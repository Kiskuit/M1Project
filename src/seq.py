#!/usr/bin/python2

# ---------------------------------------------------------
# Author : Mathis Caristan & Aurelien Lamoureux
# Date : 22/02/17
# Class : Sequence -- Class to manipulate and compute
#   with p-recursive sequences in Sage/Python
# ---------------------------------------------------------


# Try to import ore_algebra if available
# Just used for tests at uni
IS_ORE_ALGEBRA=True
try :
    import ore_algebra
except ImportError :
    IS_ORE_ALGEBRA=False

class Sequence():
    def __init__(self, cond, pols):
        # TODO check type?
        self.cond_init = cond[:] # Copy
        self.annihilator = pols[:] # Copy
        self.n = len(cond)
        if self.n < len(pols) :
            # TODO Create own exception
            raise Exception("Not enough initial conditions")

    def __getitem__(self,i):
        if i>=self.n:
            return self.cond_init[self.n-1]
        else :
            return self.cond_init[i]

if __name__ == "__main__" :
    cond = [1,2,3]
    pols1 = [[1,1],[2,2]]
    pols2 = [[1,1],[2,2],[3,3],[4,4]]
    try :
        s1 = Sequence(cond, pols1)
        s2 = Sequence(cond, pols2)
    except BaseException as e :
        print e.args[0]
    print s1[3]
