#!/usr/bin/python3

## Test harness for Frank
## Craig McLaughlin
## See the musings document for details on the proposed specification for this
## harness.

import os

class TestHarnessLogger:
    """Defines the logger for the test harness.

    The fields are defined as follows:
        * prefix: e (expected), a (actual), u (unexpected)
        * postfix: p (pass), f (failure)

    A further sub-division into regressions (r) and tests (t)."""
    def __init__(self, verbose):
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

        ## Verbose logging
        self.verbose = verbose

    def new_pair(self):
        return { "r" : 0, "t" : 0 }

    def inc(self, field, d):
        x = getattr(self, field)
        x[d] = x[d]+1
        setattr(self, field, x)

    def show(self):
        ## Decorations
        banner = "----Test Harness Result Summary----\n"
        end = "".rjust(len(banner)-1,'#')
        ## Display the summary information for failures/passes.
        return (end + '\n' +
                banner +
                self.show_desc(self.descf) +
                '\n' +
                self.show_desc(self.descp) +
                end)

    def show_desc(self,desc):
        res = ""
        valw = self.field_width(lambda x:len(repr(sum(x[1].values()))))
        for (k,v) in desc:
            x = v["t"] + v["r"]
            res += "{2:{0}}: {3:>{1}}\n".format(self.keyw, valw, k, x)
        return res

    def log(self,msg):
        print(msg)

    def verbose_log(self, msg):
        if self.verbose:
            print(msg)

    def field_width(self, f):
        return max(list(map(f,self.all_desc())))

    def all_desc(self):
        return self.descf + self.descp

def main(okDirs,errDirs,opts):
    ## A test of the summary output
    logger = TestHarnessLogger("--verbose" in opts)
    for x in okDirs:
        run_tests_in_dir(logger, check_pass, x)
    for x in errDirs:
        run_tests_in_dir(logger, check_fail, x)
    logger.log(logger.show())

def run_tests_in_dir(logger, fn, d):
    """Execute tests in directory d checking results with function fn."""
    logger.verbose_log("Entering test directory {0}".format(d))
    for x in os.listdir(d):
        x = d+x
        if os.path.isdir(x):
            run_tests_in_dir(logger, fn, x+"/")
        elif os.path.isfile(x):
            logger.verbose_log("{0} is a file".format(x))

def check_pass(logger):
    logger.inc("ep","t")

def check_fail(logger):
    logger.inc("ef","t")

if __name__ == "__main__":
    import sys
    # Invariant: All directories end with a forward slash.
    main(["tests/should-pass/"], ["tests/should-fail/"], sys.argv[1:])
