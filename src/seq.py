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
    """
    TODO doc
    """

    def __init__(self, cond, annihilator):
        """
        TODO doc
        """
        # TODO : init with only an int as param for constant sequences
        #   + other heuristic concerning init cond

        if (type(cond) == list): # The argument is a list
             self.cond_init = {i:cond[i] for i in range(0,len(cond))}
        elif (type(cond) == dict): # The argument is a dict
            self.cond_init = cond.copy()
        else:
            raise TypeError("Illegal initial value object")


        # verification des indices de la suite
        if (Sequence(self.cond_init.keys(), use_sage_types=True).universe()
                != ZZ) :
            raise TypeError("Indices of the sequence must be integers")

        # sauvegarde de l'annihilateur de la suite
        self.annihilator = annihilator
        # sauvegarde de l'ordre de la recurence
        self.order = annihilator.order()
        # récuperation de l'anneau des coeficient
        self.base_ring = annihilator.base_ring()

        # récuperation de l'operateur de récurence
        self.gen = annihilator.parent().gen()
        # Récupération du parent
        self.parent = annihilator.parent()

        # Check if there are enough initial conditions
        l = len (self.cond_init)
        if l < self.order : 
            raise Exception ("Not enough initial conditions",l)
            # TODO verbose error exception


    def to_list(self, stop, start=0):
        """
        TODO doc
        """

        if stop < min(self.cond_init.keys()): 
            err_str = str(stop) + " is too small."
            raise IndexError(err_str)
        start = max (start, sorted(self.cond_init.keys())[0])
        return self[start:stop]
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
            if(start < len(vals) - self.order):
                ret = vals[start:]
            else:
                ret = (self.annihilator.to_list(vals, start+self.order)[-self.order:])
            # TODO check val of 'start' in case Sequence does not start at 0
        else :
            vals = [self.cond_init[i] for i in sorted (self.cond_init.keys())]
            P,Q = self.annihilator.forward_matrix_bsplit (start-(len(vals)-self.order),len(vals)-self.order) 
            # TODO chech params of forward_matrix too...
            if Q==0:
                # This should not happen since __init__ must look for problems !
                #   (Or does it? is it really needed?)
                raise Exception ("(THIS SHOULD NOT HAPPEN) Degenerated values in the sequence.")
            for e in (P*Matrix([[f] for f in vals[-self.order:]]))/Q :
                ret += e

        # ret[-order:] are just enough cond to do the recursion,
        #  the final [order:] is to not duplicate elements that already are in ret
        ret = self.annihilator.to_list(ret, stop-start,start)[:stop-start:step]
        # TODO handle step so to not return every element if not needed

        return ret


    def __add__(self,other):
        #find annihilator for the add

        # >>> La conversion forcée de other.annihilator dans self.R est un peu
        # violente. Il vaut probablement mieux déclencher une erreur si les
        # deux annulateurs n'ont pas le même parent, ou à la rigueur utiliser
        # self.R.coerce().
        #(R est devenu parent depuis)
        new_annihilator = self.annihilator.lclm(self.parent(other.annihilator))
        # print(new_annihilator)

        #find degenerative case
        try:
            needed_root = new_annihilator[order(new_annihilator)].roots()
        except AttributeError:
            needed_root = []

        #max between order and the bigest root in ZZ
        len_cond  = max(new_annihilator.order()+1,
                        max([0] + [elt[0]+new_annihilator.order()+1 for elt in needed_root if(elt[0].parent() == ZZ 
                                                                                        and elt >= 0 )]))

        #compute enough value add Sequence
        cond1 = self.to_list(max(len_cond,order(new_annihilator),len(self.cond_init.keys()) ))
        cond2 = other.to_list(max(len_cond,order(new_annihilator),len(other.cond_init.keys())))


        new_cond = [sum(x) for x in zip(cond1, cond2)]

        return PRecSequence(new_cond,new_annihilator)
        # pass

    def __mul__(self,other):
        new_annihilator = self.annihilator.symmetric_product(self.parent(other.annihilator))

        #find degenerative case
        try:
            needed_root = new_annihilator[order(new_annihilator)].roots() # BIZARRE a demander au prof
        except AttributeError:
            #if no 
            needed_root = []
        #max between order and the bigest root in ZZ
        len_cond  = max(new_annihilator.order()+1,
                        max([0] + [elt[0]+new_annihilator.order()+1 for elt in needed_root if(elt[0].parent() == ZZ 
                                                                                        and elt >= 0 )]))

        #compute enough value mult Sequence
        cond1 = self.to_list(max(len_cond,order(new_annihilator),len(self.cond_init.keys()) ))
        cond2 = other.to_list(max(len_cond,order(new_annihilator),len(other.cond_init.keys())))
        
        new_cond = [x*y for x,y in zip(cond1, cond2)]

        return PRecSequence(new_cond,new_annihilator)

    def is_const(self):
        print(self.cond_init.values())
        for i in self.cond_init.values():
            if(i != self.cond_init.values()[0]):
                return False
        #compute enough value
        tab = self.to_list(2*self.order,self.order)
        print(tab)
        for elt in tab:
            if(elt != self.cond_init.values()[0]):
                return False
        #if is const change self with a reduction????

        #------------------
        return True

    #-----------todo------------
    def __iter__(self):
        return self

    def next(self):
        pass
    #-----------end todo--------
    def __repr__(self):
        _str = "recurence : "+str(self.annihilator)+"\n"
        _str += "value : "+str(self.to_list(9))+" ...\n"
        return "P-recurcive suite\n"+ _str

def guessSequence(data,Ore):
    if not Ore.is_S():
        raise Exception("You don't use the Shift operator in OreAlgebra")
        L = guess(data,Ore)
        return -L
def ExprToSeq(expression):
    if( type(expression) != sage.symbolic.expression.Expression):
        raise TypeError("this is not an sage.symbolic.expression.Expression this is ",type(expression))
    if(len(expression.args()) > 1 ):
        raise TypeError("Can treat Expression with multiple variable")
    i = 10
    cont = True
    while(cont):
        try:
            n = (expression.args()[0])
            val = [expression(n=a) for a in range(0,i)]
            a = Sequence(val)
            base_ring = a.universe()
            print(base_ring)
            #wrong basering fo now, need some help
            A,n = base_ring["x"].objgen()
            R,Sn = OreAlgebra(A,"Sx").objgen()
            Seq = guessSequence(val,R)
            return Seq 
        except ValueError:
            i+= 10
            #maybe there is an other way to stop ?  
            #we really need to leave ? or we can continue to find a recurence
            if(i <= 100):
                continue
            else:
                cont = False






def constPRecSequence(val):
    #----until we find a best way to do that---
    a = Sequence([val],use_sage_types= True)
    base_ring = a[0].parent()
    #------------------------------------------
    A,n = base_ring["x"].objgen()
    R,Sn = OreAlgebra(A,"Sx").objgen()
    const = Sn - 1

    return PRecSequence([val],const)    




if __name__ == "__main__" :
    #start examples
    # condition = {-2:-2,-1:-1,0:0,1:1,2:1,3:2,4:3,8:21}

    A,n = ZZ["n"].objgen()
    R,Sn = OreAlgebra(A,"Sn").objgen()


    A2,x = ZZ["x"].objgen()
    R2,Sx = OreAlgebra(A2,"Sx").objgen()


    cond = {0:0, 1:1, 2:1, 3:2, 4:3, 5:5, 6:8, 7:13}
    # u1 = (n-1)*(n-2)*Sn**3 - (n-1)*(n-2)*3*Sn - (n-1)*(n-2)*8
    u1 = (n-1)*(n-2)*Sn**2 - (n-1)*(n-2)*3*Sn - (n-1)*(n-2)*8
    s1 = PRecSequence (cond, u1)

    cond2 = {0:0, 1:1, 2:1, 3:2, 4:3, 5:5, 6:8, 7:13}
    u2 = Sn**2 - Sn - 1
    # u2 = R.random_element()
    fib = PRecSequence (cond2, u2)

    cond3 = [1]
    u3 = Sn - n -1
    # u3 = R.random_element()
    fact = PRecSequence (cond3, u3)

    constS = constPRecSequence(2)
    c1 = Sn**8 - 4*Sn**7 + 6*Sn**6 - 4*Sn**5 + Sn**4
    condc = [2,2,2,2,2,2,2,2]
    const2 = PRecSequence(condc,c1)

    # print("s1:")
    # print (s1[20:23])
    # print (s1[8:10])
    a = Sequence(s1[1001:1004],cr = True)
    # print (a)
    
    print("fib:")
    print(fib[0:10])

    print("fact")
    print(fact[0:10])

    fibfact = fib + fact
    print("somme (fib+fact)")
    print(fibfact[0:15])

    print("const")
    print(constS[0:15])

    cfib = fib+constS
    print("somme (fib+2)")
    print(cfib[0:15])    

    fibFact = fib * fact
    print("mult")
    print(fibFact[0:15])

    print("fib const?",fib.is_const())
    print("constS const?",constS.is_const())
    print("const2 const?",const2.is_const())

    exp = factorial(n)
    seq = ExprToSeq(exp)
    print(seq[0:10])
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
