#!/usr/bin/python3

## Test harness for Frank
## Craig McLaughlin
## See the musings document for details on the proposed specification for this
## harness.

import io
import os
from subprocess import Popen,PIPE


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
    def __init__(self,test,code,aout,eout,regression):
        self.test = test ## filename
        self.code = code
        self.aout = aout ## actual output
        self.eout = eout
        self.regression = regression

    def is_regression(self):
        return self.regression

    def success(self):
        return self.code == 0 and self.aout == self.eout

    def output(self):
        return self.aout

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
            if logger.is_verbose_on(os.path.basename(x)):
                logger.set_verbose(True)
            process_file(logger, fn, x)
            if logger.is_verbose_on(os.path.basename(x)):
                logger.set_verbose(False)
    if logger.is_verbose_on(d):
        logger.set_verbose(False)

def process_file(logger, fn, x):
    ## Parse the file to obtain list of directives
    ds = parse_file(logger, x)
    if ds:
        log_directives(logger, x, ds)
        res = process_directives(logger, x, ds)
        fn(logger, res[0])
        map(lambda r: fn(logger,r), res)

def log_directives(logger, x, ds):
    logger.verbose_log("Directives for {0}".format(x))
    for (k,v,args) in ds:
        argRep = "".join(["~{0} {1}".format(x,y) for (x,y) in args])
        logger.verbose_log("{0:>4}{1} {2} {3}".format('#',k,v,argRep))

def check_pass(logger, res):
    ttype = "r" if res.is_regression() else "t"
    if res.success():
        status = "passed"
        logger.inc("ep",ttype)
    else:
        status = "FAILED"
        logger.inc("uf",ttype)
    log_run(logger,status,res)

def check_fail(logger, res):
    ttype = "r" if res.is_regression() else "t"
    if res.success():
        status = "PASSED"
        logger.inc("up",ttype)
    else:
        status = "failed"
        logger.inc("ef",ttype)

def log_run(logger,status,res):
    rep = "{0} {1} with output:\n".format(res.test,status)
    top = "\n".rjust(len(rep),'-')
    bot = "\n".ljust(len(rep),'-')
    output = res.aout.center(len(rep)-1)
    logger.verbose_log(top + rep + output + bot)

def parse_file(logger, x):
    ds = []
    with open(x) as f:
        for line in f:
            if line.startswith("--"):
                parse_line(ds, line[2:])
    return ds

def parse_line(ds, line):
    line = line.strip()
    if line.startswith('#'):
        ds.append(parse_directive(line[1:]))

def parse_directive(line):
    args = [] ## directive arguments
    (key,value),line = parse_pair(line)
    parse_args(args,line)
    return (key,value,args)

def parse_args(args,line):
    line = line.strip()
    if line.startswith('~'):
        p,line = parse_pair(line[1:])
        args.append(p)

def parse_pair(line):
    key,value = "",""
    x = 0
    while x < len(line) and line[x].isalpha():
        key += line[x]
        x = x + 1
    while x < len(line) and line[x] != '~':
        value += line[x]
        x = x + 1
    return (key,value.strip()),line[x:]

def process_directives(logger, x, ds):
    rs = []
    for (k,v,args) in ds:
        if directive_has_result(k):
            rs.append(process_directive(logger,x,k,v,args))
    return rs

def process_directive(logger,x,k,v,args):
    isRegression = True if os.path.basename(x).startswith('r') else False
    if k == "return":
        logger.verbose_log("Running {0} against main! == {1}".format(x,v))
        p = Popen(["frank", x],stderr=PIPE,stdout=PIPE)
        p.wait()
        ret = p.returncode
        (out,err) = p.communicate()
        out = err.decode("utf-8") + out.decode("utf-8")
        res = Result(x,ret,out.strip('\n'),v,isRegression)
        return res

def directive_has_result(k):
    return k == "return"

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
