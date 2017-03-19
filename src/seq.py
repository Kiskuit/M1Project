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
import sys

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
from ore_algebra import *


class PRecSequence():
    def __init__(self, cond, pols,var,roots_conds=[]):

        #--Get the ring---
        # TODO : Could probably optimize this
        ring = [ZZ,QQ,RR,CC]
        i = 0
        for elt in pols:
            # print (elt,ring[i])
            while i < len(ring) and elt not in ring[i][var] :
                i +=1
            #In case element does not fit any of the base rings
            if elt not in ring[len(ring)-1][var] :
                raise ProjectException(
                    string="Element not included in base rings (ZZ,QQ,RR,CC)")
        self.var = var
        self.ring = ring[i][var]
        #-----------------

        self.cond_init = Sequence(cond)
        self.cond_roots = Sequence([(i,cond[i]) for i in range(0,len(cond))] + [elt for elt in roots_conds])
        # print(self.cond_roots)
        # self.cond_roots = Sequence(roots_conds)
        self.R,self.op = OreAlgebra(self.ring,'S'+var).objgen()

        #---Set annihilator ---
        self.annihilator = 0
        for elt,i in zip(Sequence(pols),range(0,len(Sequence(pols)))):
            self.annihilator += self.ring(elt)*self.op**i
        #----------------------

        self.n = len(cond)

        if self.n < len(pols)-1 :
            raise Exception("Not enough initial conditions")
        special_root = [elt + self.n for elt in find_positive_roots(pols[-1])]
        contain = False
        NcontainList = []
        for val in special_root:
            for elt in self.cond_roots:
                if(val == elt[0]):
                    contain = True
            if(not contain):
                NcontainList.append(val)
            contain = False
        if NcontainList:
            raise Exception("Miss some value")

    def to_list(self,i):
        if i>=self.n:
            L = []
            #find i+1 element and return the last 
            if len(self.cond_roots) <= len(self.cond_init):
                L = self.annihilator.to_list(self.cond_init,i+1)
            else:
                L = self.annihilator.to_list(self.cond_init,self.cond_roots[len(self.cond_init)][0])+[self.cond_roots[len(self.cond_init)][1]]
                inc = 1
                while len(self.cond_roots) > len(self.cond_init)+ inc and i >= self.cond_roots[len(self.cond_init)+inc][0]:
                    L = self.annihilator.to_list(L, self.cond_roots[len(self.cond_init)][0])+[self.cond_roots[len(self.cond_init)][1]]
                    inc += 1
                L = self.annihilator.to_list(L,i+1)
            return L[:i+1]
        else :
            return self.cond_init[:i+1]
    def __getitem__(self,i):
        if i>=self.n:
            L = []
            #find i+1 element and return the last 
            if len(self.cond_roots) <= len(self.cond_init):
                L = self.annihilator.to_list(self.cond_init,i+1)
            else:
                L = self.annihilator.to_list(self.cond_init,self.cond_roots[len(self.cond_init)][0])+[self.cond_roots[len(self.cond_init)][1]]
                inc = 1
                while len(self.cond_roots) > len(self.cond_init)+ inc and i >= self.cond_roots[len(self.cond_init)+inc][0]:
                    L = self.annihilator.to_list(L, self.cond_roots[len(self.cond_init)][0])+[self.cond_roots[len(self.cond_init)][1]]
                    inc += 1
                L = self.annihilator.to_list(L,i+1)
            return L[i]
        else :
            return self.cond_init[i]
    def __add__(self,other):
        #find annihilator for the add
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
        except Exception as e :
            #TODO modify to take into account new exception
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
        except Exception as e :
            #TODO modify to take into account new exception
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

def find_positive_roots(poly):
    Proot = []
    try:
        root = poly.roots()
        for elt,mult in root:
            if(elt >= 0):
                Proot.append(elt)
        # print(needed_root)
    except:
        pass

    return Proot


if __name__ == "__main__" :
    var('n')

    cond = [1]
    pols = [-n-1,1]

    cond2 = [0,1]
    pols2 = [-1,-1,1]
    try :
        s = PRecSequence(cond, pols,'n')
        print("fact")
        print(s)
        print(s.to_list(10))
        s2 = PRecSequence(cond2, pols2,'n')
        print("fib")
        print(s2)
        print(s2.to_list(10))
        s3 = s+s2
        print("sum")
        print(s3)
        print(s3.to_list(10))

        s4 = s*s2
        print("mul")
        print(s4)
        print(s4.to_list(10))
        
    except Exception as e :
        print (e)

    #test avec PRecSequence
    #factorial
    #fibonacci
