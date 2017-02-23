#!/usr/bin/python2

# ---------------------------------------------------------
# Author : Mathis Caristan & Aurelien Lamoureux
# Date : 23/02/17
# Exception : ProjException -- Exception that will be used
#   throughout the project
# ---------------------------------------------------------


class ProjException(Exception) :
    def __init__(self, string="", val=""):
        if string=="":
            self.text="Exception linked with the project"
        else :
            self.text=string

        self.text += "\nException value : ".format("No value provided" if val=="" else val)
        self.text += "No value provided" if val=="" else str(val)


if __name__ =="__main__":
    try:
        raise ProjException()
    except ProjException as e:
        print 1
        print e.text
    try:
        raise ProjException("test")
    except ProjException as e:
        print 2
        print e.text
    try:
        raise ProjException("test", 4)
    except ProjException as e:
        print 3
        print e.text


