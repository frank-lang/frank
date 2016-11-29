#!/usr/bin/python3

## Test harness for Frank
## Craig McLaughlin
## See the musings document for details on the proposed specification for this
## harness.

import logging

class TestHarnessLogger:
    """Defines the logger for the test harness.

    The fields are defined as follows:
        * prefix: e (expected), a (actual), u (unexpected)
        * postfix: p (pass), f (failure)

    A further sub-division into regressions (r) and tests (t)."""
    def __init__(self):
        self.ef = self.new_pair()
        self.af = self.new_pair()
        self.uf = self.new_pair()

        self.ep = self.new_pair()
        self.ap = self.new_pair()
        self.up = self.new_pair()

        self.descf = [("Expected Failures", self.ef)
                     ,("Actual Failures", self.af)
                     ,("Unexpected Failures", self.uf)]

        self.descp = [("Expected Passes", self.ep)
                     ,("Actual Passes", self.ap)
                     ,("Unexpected Passes", self.up)]

        self.keyw = self.field_width(lambda x:len(x[0]))
        self.valw = self.field_width(lambda x:len(x[1]))

    def new_pair(self):
        return { "r" : 0, "t" : 9 }

    def inc(self, field, d):
        x = getattr(self, field)
        x[d] = x[d]+1
        setattr(self, field, x)

    def show(self):
        ## Decorations
        banner = "----Test Harness Result Summary----"
        end = "".rjust(len(banner),'#')
        print(end)
        print(banner)
        ## Display the summary information for failures/passes.
        self.show_desc(self.descf)
        print()
        self.show_desc(self.descp)
        print(end)

    def show_desc(self,desc):
        for (k,v) in desc:
            x = v["t"] + v["r"]
            print("{2:{0}}: {3:>{1}}".format(self.keyw, self.valw, k, x))

    def field_width(self, f):
        return max(list(map(f,self.all_desc())))

    def all_desc(self):
        return self.descf + self.descp

def main(okDirs,errDirs):
    ## A test of the summary output
    logger = TestHarnessLogger()
    logger.inc("uf","t")
    logger.show()

if __name__ == "__main__":
    main(["tests/should-pass"], ["tests/should-fail"])
