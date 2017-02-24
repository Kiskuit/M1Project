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
    # TODO set path to ore_algebra
    import ore_algebra
except ImportError :
    IS_ORE_ALGEBRA=False
    PATH_TO_ORE = raw_input(("ore_algebra module was not found in working directory,\n"
        "please provide a path to ore_algebra module : "))
    # TODO import ore_algebra with provided path


class PRecSequence():
    def __init__(self, cond, pols):
        # TODO : coerce
        # TODO use sage sequences
        self.cond_init = cond[:]
        # TODO : use sage operators
        self.annihilator = pols[:]
        self.n = len(cond)
        if self.n < len(pols)-1 :
            raise ProjException(string="Not enough initial conditions")

    def __getitem__(self,i):
        if i>=self.n:
            #naïf : L = to_list([coef],i)
            #return L[i]
            return self.cond_init[self.n-1]
        else :
            return self.cond_init[i]
    def __add__(self,other):
        #use lclm to find the sum
        pass
    def __mul__(self,other):
        #use symmetric_product to mul
        pass


if __name__ == "__main__" :
    cond = [1,2]
    pols1 = [[1,1],[2,2]]
    pols2 = [[1,1],[2,2],[3,3],[4,4]]
    try :
        s1 = PRecSequence(cond, pols1)
        s2 = PRecSequence(cond, pols2)
    except ProjException as e :
        print (e.text)
    print (s1[3])
