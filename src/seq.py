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

# Project imports
from exception import ProjException

# Ore_algebra import
# Try to import ore_algebra if available
# Just used for tests at uni
IS_ORE_ALGEBRA=True
try :
    from sage.all import *
    # TODO set path to ore_algebra

    from ore_algebra import *
except ImportError :
    IS_ORE_ALGEBRA=False
    PATH_TO_ORE = raw_input(("ore_algebra module was not found in working directory,\n"
        "please provide a path to ore_algebra module : "))
    # TODO import ore_algebra with provided path


class PRecSequence():
    def __init__(self, cond, pols,var):
          # TODO : coerce
        # TODO use sage sequences

        #--Get the ring---
        ring = [ZZ,QQ,RR,CC]
        i = 0
        for elt in pols:
            # print (elt,ring[i])
            while i < len(ring) and elt not in ring[i][var] :
                i +=1
        self.var = var
        self.ring = ring[i][var]
        #-----------------

        self.cond_init = Sequence(cond)
        self.R,self.op = OreAlgebra(self.ring,'S'+var).objgen()
        
        #---Set annihilator ---
        self.annihilator = 0
        for elt,i in zip(Sequence(pols),range(0,len(Sequence(pols)))):
            self.annihilator += self.ring(elt)*self.op**i
        #----------------------

        self.n = len(cond)
        if self.n < len(pols)-1 :
            raise ProjException(string="Not enough initial conditions")

    def __getitem__(self,i):
        if i>=self.n:
            #find i+1 element and return the last 
            L = self.annihilator.to_list(self.cond_init,i+1)
            return L[i]
            # return self.cond_init[self.n-1]
        else :
            return self.cond_init[i]
    def __add__(self,other):
        #find annihilator for the add
        tmp = self.annihilator.lclm(self.R(other.annihilator))
        new_annihilator = [i for i in tmp]

        #find initial condition for the add
        #need len(annihilator)-1 cond
        cond1 = self.annihilator.to_list(self.cond_init,len(new_annihilator)-1)
        cond2 = other.annihilator.to_list(other.cond_init,len(new_annihilator)-1)
        #do the sum pairwise
        new_cond = [sum(x) for x in zip(cond1, cond2)]

        #create a new PRecSequence
        newElt = PRecSequence(new_cond,new_annihilator,self.var)
        return newElt
    def __mul__(self,other):
        #use symmetric_product to mul
        pass


if __name__ == "__main__" :
	var('n')

	cond = [1]
	pols = [-(n+1),1/2.0]

	cond2 = [0,1]
	pols2 = [-1,-1,1]
	try :
		s = PRecSequence(cond, pols,'n')
		s2 = PRecSequence(cond2, pols2,'n')
		s3 = s+s2
		print(s3.annihilator)
		print(s3.cond_init)
		print(s3[4])
        
	except ProjException as e :
		print (e.text)

    #test avec PRecSequence
    #factorial
    #fibonacci
