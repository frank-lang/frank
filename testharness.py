#!/usr/bin/python3

## Test harness for Frank
## Craig McLaughlin
## See the musings document for details on the proposed specification for this
## harness.

import os

class TestHarnessLogger:
    """Defines the logger for the test harness.

    The fields are defined as follows:
        * prefix: e (expected), u (unexpected)
        * postfix: p (pass), f (failure)

    A further sub-division into regressions (r) and tests (t)."""
    def __init__(self):
        self.ef = self.new_pair()
        self.uf = self.new_pair()

        self.ep = self.new_pair()
        self.up = self.new_pair()

        self.descf = [("Expected Failures", self.ef)
                     ,("Unexpected Failures", self.uf)]

        self.descp = [("Expected Passes", self.ep)
                     ,("Unexpected Passes", self.up)]

        self.keyw = self.field_width(lambda x:len(x[0]))

        ## Verbose logging
        self.verbose = False
        self.verbose_on = ""

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

    def set_verbose(self, b):
        self.verbose = b

    def set_verbose_on(self, x):
        """x is a file or dir. for which verbose output is produced."""
        self.verbose_on = x

    def is_verbose_on(self, x):
        return self.verbose_on == x

    def field_width(self, f):
        return max(list(map(f,self.all_desc())))

    def all_desc(self):
        return self.descf + self.descp

class Result:
    def regression(self):
        return True

    def success(self):
        return True

def main(okDirs,errDirs,opts):
    ## A test of the summary output
    logger = TestHarnessLogger()
    ## Command line options may change the state of the logger.
    parse_opts(logger, opts)
    for x in okDirs:
        run_tests_in_dir(logger, check_pass, x)
    for x in errDirs:
        run_tests_in_dir(logger, check_fail, x)
    logger.log(logger.show())

def run_tests_in_dir(logger, fn, d):
    """Execute tests in directory d checking results with function fn."""
    if logger.is_verbose_on(d):
        logger.set_verbose(True)
    logger.verbose_log("Entering test directory {0}".format(d))
    for x in os.listdir(d):
        x = d+x
        if os.path.isdir(x):
            run_tests_in_dir(logger, fn, x+"/")
        elif os.path.isfile(x) and x.endswith(".fk"):
            if logger.is_verbose_on(x):
                logger.set_verbose(True)
            process_file(logger, fn, x)
            if logger.is_verbose_on(d):
                logger.set_verbose(False)
    if logger.is_verbose_on(d):
        logger.set_verbose(False)

def process_file(logger, fn, x):
    ## Parse the file to obtain list of directives
    ds = parse_directives(logger, x)
    res = process_directives(logger, ds, x)
    fn(logger, res)

def check_pass(logger, res):
    ttype = "r" if res.regression() else "t"
    if res.success():
        logger.inc("ep",ttype)
    else:
        logger.inc("uf",ttype)

def check_fail(logger, res):
    ttype = "r" if res.regression() else "t"
    if res.success():
        logger.inc("up",ttype)
    else:
        logger.inc("ef",ttype)

def parse_directives(logger, x):
    ds = []
    with open(x) as f:
        for line in f:
            if line.startswith("--"):
                ds += parse_line(line[2:])
    return ds

def parse_line(line):
    line = line.strip()
    return []

def process_directives(logger, ds, x):
    return Result()

def parse_opts(logger, opts):
    x = 0
    while x < len(opts):
        if opts[x] == "--verbose":
            ## Check for verbose to be set locally
            if x+1 < len(opts) and not opts[x+1].startswith("--"):
                logger.set_verbose_on(opts[x+1])
                x = x + 1 ## Move past option value.
            else:
                ## Globally verbose
                logger.set_verbose(True)
        x = x + 1

if __name__ == "__main__":
    import sys
    # Invariant: All directories end with a forward slash.
    main(["tests/should-pass/"], ["tests/should-fail/"], sys.argv[1:])
