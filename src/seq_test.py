#!/usr/bin/python2
# -*- coding: utf8 -*-


# ---------------------------------------------------------
# Author : Mathis Caristan & Aurelien Lamoureux
# Date : 22/02/17
# Class : PRecSequence -- Class to manipulate and compute
#   with p-recursive sequences in Sage/Python
# ---------------------------------------------------------


# General imports
# TODO : sage import future print already if not mistaken
from __future__ import print_function
import sys

# Project imports
# >>> Ce n'est probablement pas une bonne idée d'avoir une exception « à
# vous » ; il vaut mieux choisir l'exception que l'on déclenche en fonction de
# la situation où on la déclenche. Souvent, une exception standard de Python
# (TypeError, ZeroDivisionError...) fait l'affaire.
from exception import ProjException

# Ore_algebra import
# Try to import ore_algebra if available
# Just used for tests at uni

# No longer needed
#IS_ORE_ALGEBRA=True
#try :
#
#    sys.path.insert(0,"../../ore_algebra-analytic/src")
#    from sage.all import *
#    from ore_algebra import *
#except ImportError :
#    PATH_TO_ORE = raw_input(("ore_algebra module was not found in working directory,\n"
#        "please provide a path to ore_algebra module : "))
#    try :
#        sys.path.insert(0,PATH_TO_ORE)
#        from ore_algebra import *
#    except ImportError :
#        IS_ORE_ALGEBRA=False

# >>>> Ok pour l'instant, mais on évite généralement les "import *" dans du
# code de bibliothèque propre.
from ore_algebra import *

# >>> Généralités :
#
# - Comme discuté l'autre jour, essayez de clarifier (et documenter !) vos
# conventions sur les conditions initiales. En particulier, est-il vraiment
# nécessaire de traiter séparément les conditions initiales « de base » et les
# conditions initiales « supplémentaires » ?
#
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
#   - un test de si une suite est constante,
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

    def __init__(self, cond, annihilator):

        # >>> Comme discuté l'autre jour, prenez plutôt en entrée un opérateur,
        # et utilisez les méthodes parent() et base_ring() pour récupérer les
        # anneaux correspondants.

        # >>> Envisagez éventuellement de passer les conditions initiales sous
        # forme de dictionnaire {indice: valeur}.
        sorted_cond = {}
        for key in sorted(cond):
            sorted_cond[key] = cond[key]

        self.cond_init_pos = Sequence(sorted_cond.keys())
        self.cond_init_val = Sequence(sorted_cond.values())

        #bug : todo correction .parent() toujours != ZZ
        if(self.cond_init_pos.parent() != ZZ):
            raise Exception("Index value error")

        # get the ring of each element
        self.base_ring = annihilator.base_ring()

        # get the operator of the recurence
        self.operator = annihilator.parent().gen()

        # store the annihilator
        self.annihilator = annihilator

        self.order = annihilator.order()

        # roots = []
        #
        for elt in annihilator[annihilator.order()].roots():
            if(elt.parent() == ZZ and elt > 0 and elt not in self.cond_init_pos): # > 0 for now but not later
                raise Exception("Some initial value are Missing")
            # if elt.parent() == ZZ:
                # roots += [elt]
        #------------


        #
        _,max = greater_concec_value(self.cond_init_pos)
        if(max < self.order):
            raise Exception("Not enough initial value")

        #------------

        # >>> Je déconseille les noms d'attribut d'une lettre, on s'y perd
        # vite -- self.order serait plus explicite. Mais vous n'avez peut-être
        # même pas besoin de cet attribut : self.annihilator.order() marche
        # aussi.
        # >>> Attention aussi à ce que le nombre de conditions initiales n'est
        # pas forcément égal à l'ordre de l'opérateur !



    # >>> Au lieu/en plus d'avoir une méthode to_list(), vous pourriez essayer
    # de gérer la syntaxe u[i:j] (ou même u[i:j:k]) dans __getitem__().
    def to_list(self,i):
        l1 = copy(self.cond_init_pos)
        l2 = copy(self.cond_init_val)
        if( i < self.cond_init_pos[0] ):
            raise Exception("Unexpected Value Index")
        rank = get_index(i,l1,self.order)
        if( rank  == -1):
            raise Exception("Can't find the ",i,"-th element")
        cond = True
        ret = []
        tmp = rank
        ret = l2[rank:rank+order]
        j = next_jump(l1[tmp:])
        while( j != -1 and i >= l1[j]):
            ret += self.annihilator.to_list(ret[-2:],j)[2:]
            j = next_jump(l1[tmp:])
        #faire un split a la fin ou moins en calculer
        return ret



    # >>> Évitez autant que possible la duplication de code. Ici, le code de
    # to_list() et celui de __getitem__() se ressemblent beaucoup : c'est le
    # signe que l'une devrait appeler l'autre ou qu'elles devraient appeler une
    # même méthode auxiliaire.
    def __getitem__(self,i):
        pass #todo
    def __add__(self,other):
        #find annihilator for the add

        # >>> La conversion forcée de other.annihilator dans self.R est un peu
        # violente. Il vaut probablement mieux déclencher une erreur si les
        # deux annulateurs n'ont pas le même parent, ou à la rigueur utiliser
        # self.R.coerce().
        new_annihilator = list(self.annihilator.lclm(self.R(other.annihilator)))
        # new_annihilator = [i for i in tmp]
        # print("coef annilator for the sum",new_annihilator)
        #find degenerative case
        needed_root = find_positive_roots(new_annihilator[-1])

        #find initial condition for the add
        #need len(annihilator)-1 cond
        cond1 = self.to_list(len(new_annihilator)-1)
        cond2 = other.to_list(len(new_annihilator)-1)
        #do the sum pairwise
        new_cond = [sum(x) for x in zip(cond1, cond2)]

        #create a new PRecSequence
        try:
            newElt = PRecSequence(new_cond,new_annihilator,self.var)
        # >>> Vous avez calculé des racines plus haut, pourquoi ne pas vous en
        # servir ? En tout cas il faut choisir entre les deux mécanismes !
        except ProjException as e :
            # print (e.text)
            #get the value needed in e.val
            more_val = [(elt,self[elt]+other[elt]) for elt in e.val ]
            newElt = PRecSequence(new_cond,new_annihilator,self.var,more_val)

        return newElt
    def __mul__(self,other):
        # #use symmetric_product to mul
        new_annihilator = list(self.annihilator.symmetric_product(self.R(other.annihilator)))
        # new_annihilator = [i for i in tmp]
        # print("coef annilator for the sum",new_annihilator)
        #find degenerative case
        needed_root = find_positive_roots(new_annihilator[-1])

        #find initial condition for the add
        #need len(annihilator)-1 cond
        cond1 = self.to_list(len(new_annihilator)-1)
        cond2 = other.to_list(len(new_annihilator)-1)
        #do the sum pairwise
        new_cond = [x*y for x,y in zip(cond1, cond2)]

        #create a new PRecSequence
        try:
            newElt = PRecSequence(new_cond,new_annihilator,self.var)
        except ProjException as e :
            # print (e.text)
            #get the value needed in e.val
            more_val = [(elt,self[elt]+other[elt]) for elt in e.val ]
            newElt = PRecSequence(new_cond,new_annihilator,self.var,more_val)

        return newElt
    def __str__(self):
        _str = "initial conditon : "+str(self.cond_init)
        _str += "\nrecurence : "+str(self.annihilator)
        return _str
    def __repr__(self):
        return "P-recurcive suite"

#retour l'index le plus petit avec lenght concecutif element 
def get_index(i,l,lenght):
    # l.reverse()
    print l
    j = 0
    m = 1
    cond = True
    try:
        while(cond):
            while i <= l[j]:
                j += 1
            prev = l[j]
            print("j",j)
            for k in range(1,lenght):
                if  prev + 1 ==  l[j + k] :
                    m += 1
                else:
                    m = 1
                prev = l[j+k]
            print("m",m)
            if m == lenght:
                cond = False
            else:
                m = 1
                j += 1
        # l.reverse()    
    except:
        # l.reverse()
        return -1
    return j
def next_jump(l):
    prev = l[0]
    for i in range(1,len(l)):
        if(prev+1 != l[i]):
            return i 
        prev = l[i]
    return -1

if __name__ == "__main__" :
    #start examples
    condition = {0:0,1:1,2:1,3:2,4:3,8:21}
    A,n = ZZ["n"].objgen()
    R,_ = Ore_algebra(A,"Sn")
    a = Sn**2 -Sn - 1
    S1 = PRecSequence(condition,a)
    #end examples
