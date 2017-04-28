#!/usr/bin/python2
# -*- coding: utf8 -*-


# ---------------------------------------------------------
# Author : Mathis Caristan & Aurelien Lamoureux
# Date : 22/02/17
# Class : PRecSequence -- Class to manipulate and compute
#   with p-recursive sequences in Sage/Python
# ---------------------------------------------------------


# General imports
from __future__ import print_function

# >>>> Ok pour l'instant, mais on évite généralement les "import *" dans du
# code de bibliothèque propre.
from sage.all import *
from ore_algebra import *

# >>> Généralités :
#
# - Comme discuté l'autre jour, essayez de clarifier (et documenter !) vos
# conventions sur les conditions initiales. En particulier, est-il vraiment
# nécessaire de traiter séparément les conditions initiales « de base » et les
# conditions initiales « supplémentaires » ?
#
# on a fait ZZ, 
# - Essayez de traiter des exemples de suites à valeur dans différents anneaux.
# Quelques exemples d'anneaux intéressants : les entiers ZZ, les rationnels QQ,
# les flottants réels ou complexes à différentes précisions RealField(prec),
# ComplexField(prec), les corps finis GF(q), les anneaux de polynômes en un
# paramètre différent de la variable de la suite...
#
# - (Peut-être pour le plus long terme :) l'anneau des valeurs de la suite
# n'est pas forcément le même que celui des coefficients des polynômes qui
# apparaissent dans l'opérateur. En fait, il y a au moins trois anneaux en
# jeu :
#
#   1. celui des coefficients (constants) des coefficients (polynomiaux) de
#      l'opérateur de récurrence,
#
#   2. celui des conditions initiales,
#
#   3. celui des valeurs de la suite, dans lequel il doit être possible de
#      convertir les éléments des deux précédents.
#
# Sage a un mécanisme sophistiqué pour trouver un anneau commun dans lequel
# les éléments de deux anneaux donnés peuvent se convertir. Ce mécanisme est
# invoqué automatiquement à chaque fois qu'on fait une opération du style +
# ou *, mais si nécessaire vous pouvez l'appeler explicitement comme dans
# l'exemple suivant :
#
#   sage: import sage.structure.element
#   sage: cm = sage.structure.element.get_coercion_model()
#   sage: cm.common_parent(PolynomialRing(ZZ, 'a'), CC)
#   Univariate Polynomial Ring in a over Complex Field with 53 bits of precision
#
# - Quelques exemples de méthodes ou fonctions supplémentaires que l'on
# pourrait vouloir (vous n'êtes pas obligés de tout mettre, faites votre marché
# suivant ce qui vous intéresse et ce que vous savez faire... il y a du trivial
# comme du difficile) :
#
#   - des opérations de décalage (__lshift__(), éventuellement __rshift__()
#     avec une sémantique à clarifier),
#   - un test d'égalité (__eq__(), __ne__(), éventuellement __nonzero__()),
#   - un test de si une suite est constante,  FAIT
#   - un itérateur infini, qui produit des termes de la suite à volonté
#     (__iter__()),
#   - un constructeur produisant une suite constante (pour l'instant dans une
#     fonction séparée, pourra servir par la suite pour avoir des conversions
#     automatiques constantes -> suites et ainsi des opérations constante +
#     suite, constante * suite, etc.),
#   - éventuellement la conversion inverse, d'une suite constante en élément du
#     parent de ses valeurs,
#   - la division par une suite constante,
#   - une méthode base_ring() qui renvoie le parent commun des éléments de la
#     suite,
#   - un constructeur (fonction séparée) qui fabrique une suite à partir de ses
#     premiers termes, en utilisant la fonction guess() de ore_algebra,
#   - une méthode de « minimisation » qui essaie de trouver un opérateur
#     d'ordre plus petit définissant la même suite, en combinant guess() avec
#     le test d'égalité,
#   - un constructeur (fonction séparée) qui fabrique une suite à partir d'une
#     expression sage du genre factorial(n)*2^n + n,
#   - un moyen de calculer des suites du style u(3*n+2) à partir de u(n)...

class PRecSequence(object): # >>> PRecSequence(object) (bizarrerie Python)
    """
    TODO doc
    """

    def __init__(self, cond, annihilator):
        """
        TODO doc
        """
        # TODO : init with only an int as param for constant sequences
        #   + other heuristic concerning init cond

        # Heuristic : The user can specify extra initial condition.
        # Let ̀`min` and `max` be the lowest and greatest
        # index of the initial condition, if he choses to specify extra cond
        # the dict must contain conditions for every index in [min,max]
        self.cond_init = cond.copy()
        #verification des indices de la suite
        if (Sequence(self.cond_init.keys(), use_sage_types=True).universe()
                != ZZ) :
            raise IndexError("Indices of the sequence must be integers")

        # récuperation de l'anneau des coeficient
        self.base_ring = annihilator.base_ring()
        # récuperation de l'operateur de récurence 
        self.gen = annihilator.parent().gen()
        # sauvegarde de l'annihilateur de la suite
        self.annihilator = annihilator
        #sauvegarde de l'ordre de la recurence
        self.order = annihilator.order()

        # recherche si il y a des racines du polynome "dominant" qui sont
        # superieur au plus petit element de la suite 
        for root,_ in annihilator[annihilator.order()].roots():
            if (root.parent() == ZZ # Root is in ZZ
                    and root+self.order > sorted(self.cond_init.keys())[0] # Root isnt used for recurrence
                    and root+self.order not in self.cond_init.keys()) : # Root does not appear in cond_init
                raise Exception("Initiallisation failed : Some initial value are Missing: ",root+self.order)

        # Check if there are enough initial conditions
        l = len (self.cond_init)
        if l < self.order : 
            raise Exception ("Not enough initial conditions")
        # Check if all initial cond (according to heuristic) are specified
        if self.cond_init.keys()[0] + l - 1 != self.cond_init.keys()[-1]: 
            raise Exception ("Initial condition must be on an interval")

    def to_list(self, stop, start=0):
        """
        TODO doc
        """
        if stop < self.cond_init_pos[0] : 
            err_str = str(stop) + " is too small."
            raise IndexError(err_str)
        start = max (start, sorted(self.cond_init.keys())[0])
        return self[start,stop]
        # return self.__getitem__ (slice(start, stop))

    def __getitem__(self,sl):
        # Get start, stop and step params
        if type(sl) == slice :
            start = sl.start
            step = sl.step
            stop = sl.stop
            if not step:
                step=1
        else :
            start = sl 
            stop = sl+1
            step = 1
        ret = []

        # For low values of start, recursion is faster than forward_matrix
        # TODO actual test to estimate the value at which the shift happen
        if start < 1000 :
            # Use recursive method
            vals = [self.cond_init[i] for i in sorted (self.cond_init.keys())]
            ret = (self.annihilator.to_list(vals, start+1)[-self.order:])
            # TODO check val of 'start' in case Sequence does not start at 0
        else :
            vals = [cond_init[i] for i in sorted (cond_init.keys())]
            P,Q = self.annihilator.forward_matrix_bsplit (start,0) # TODO chech params of forward_matrix too...
            if Q==0:
                # This should not happen since __init__ must look for problems !
                #   (Or does it? is it really needed?)
                raise Exception ("(THIS SHOULD NOT HAPPEN) Degenerated values in the sequence.")
            for e in (P*Matrix([[f] for f in vals[-self.order:]]))/Q :
                ret += e

        # ret[-order:] are just enough cond to do the recursion,
        #  the final [order:] is to not duplicate elements that already are in ret
        ret += self.annihilator.to_list(ret[-self.order:], stop-start)[self.order:]
        # TODO handle step so to not return every element if not needed

        return ret


    def __add__(self,other):
        #find annihilator for the add

        # >>> La conversion forcée de other.annihilator dans self.R est un peu
        # violente. Il vaut probablement mieux déclencher une erreur si les
        # deux annulateurs n'ont pas le même parent, ou à la rigueur utiliser
        # self.R.coerce().
        new_annihilator = list(self.annihilator.lclm(self.R.coerce(other.annihilator)))

        #find degenerative case
        needed_root = new_annihilator[-1].roots()
        needed_root = [elt[0] for elt in needed_root]

        #---------todo
        #regarder les indices minimau pour ajuster la somme
        #find initial condition for the add
        # cond1 = self.to_list(len(new_annihilator)-1)
        # cond2 = other.to_list(len(new_annihilator)-1)
        #do the sum pairwise
        # new_cond = [sum(x) for x in zip(cond1, cond2)]
        #---------end todo

        #create a new PRecSequence todo

        # return
        pass

    # def __mul__(self,other):
        pass #todo

    def is_const(self):
        #si la suite est d'ordre 1 et Un+1 - Un = 0 et que les conditions initiaux sont toutes egales
        if self.order == 1 and self.annihilator[0] != 0 and self.annihilator[0] == -self.annihilator[1]:
            val = self.cond.values()[0]
            for i in self.cond.values():
                if val != i:
                    return False
        return True

    #-----------todo
    def __iter__(self):
        return self

    def next(self):
        pass
    #-----------end todo
    def __repr__(self):
        _str = "recurence : "+str(self.annihilator)+"\n"
        _str += "value : "+str(self.to_list(9))+" ...\n"
        return "P-recurcive suite\n"+ _str

if __name__ == "__main__" :
    #start examples
    # condition = {-2:-2,-1:-1,0:0,1:1,2:1,3:2,4:3,8:21}
    A,n = ZZ["n"].objgen()
    R,Sn = OreAlgebra(A,"Sn").objgen()
    cond = {0:0, 1:1}
    u1 = Sn**2 - Sn - 1
    s1 = PRecSequence (cond, u1)
    print (s1[5:8])

    ###   condition = {0:0,1:1,2:7}
    ###   a1 = n*Sn**2 -Sn - 1
    ###   S1 = PRecSequence(condition,a1)

    ###   condition = {0:0,1:1,4:0}
    ###   a2 = (n-2)*Sn**2 -Sn - 1
    ###   S2 = PRecSequence(condition,a2)

    ###   condition = {0:0,1:1}
    ###   a4 = Sn**2 - Sn - 1
    ###   S4 = PRecSequence(condition,a4)
    ###   print (S4[0:10])
    ###   try :
    ###       S2.to_list(-2)
    ###   except IndexError as ie:
    ###       print ("S2.to_list(-2) correctly raises an exception.")
    ###   else :
    ###       print ("No exception : problem.")

    ###   condition = {0:0,1:1,2:2,13:100} #good initialisation
    ###   # condition = {0:0,1:1,2:2} # miss some value
    ###   a3 = (n-10)*Sn**3 + Sn**2 -Sn - 1
    ###   S3 = PRecSequence(condition,a3)
    ###   
    ###   print(S1.to_list(9))
    ###   print(S1)
    ###   print(S2.to_list(9))
    ###   print(S3.to_list(9))

    #end examples
