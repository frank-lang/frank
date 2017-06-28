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

    * The first 4 fields are defined as follows:
        * prefix:  e (expected), u (unexpected)
        * postfix: p (pass),     f (failure)
          (A further sub-division into regressions (r) and tests (t))

     * Verbose logging works as follows: Either
       1) Verbose for all or                    (self.verbose)
       2) Verbose only for specific dir/file    (self.verbose_on)


    """
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
        self.verbose_on = ""  ## file path to write to

    def new_pair(self):
        return { "r" : 0, "t" : 0 }

    ## field: {ef, uf, ep, up}
    ## d:     {"r", "t"}
    def inc(self, field, d):
        x = getattr(self, field)
        x[d] = x[d]+1
        setattr(self, field, x)

    def show(self):
        ## Decorations
        banner = "----Test Harness Result Summary----\n"
        end = "".rjust(len(banner)-1,'#')
        verbose_summary = '\n' + self.show_regressions() + end
        ## Display the summary information for failures/passes.
        return (end + '\n' +
                banner +
                self.show_desc(self.descf) +
                '\n' +
                self.show_desc(self.descp) +
                (verbose_summary if self.verbose else end))

    def show_desc(self,desc):
        res = ""
        valw = self.field_width(lambda x:len(repr(sum(x[1].values()))))
        for (k,v) in desc:
            x = v["t"] + v["r"]
            res += "{2:{0}}: {3:>{1}}\n".format(self.keyw, valw, k, x)
        return res

    def show_regressions(self):
        valw = self.field_width(lambda x:len(repr(sum(x[1].values()))))
        k = "Regression Failures"
        v = self.uf["r"]
        return "{2:{0}}: {3:>{1}}\n".format(len(k), valw, k, v)

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

""" Single test unit """
class Result:
    def __init__(self,test,desc,code,aout,eout,directive,regression):
        self.test = test ## filename
        self.desc = desc
        self.code = code
        self.aout = aout ## actual output
        self.eout = eout ## expected output
        self.directive = directive
        self.regression = regression

    def success(self):
        return self.code == 0 and self.aout == self.eout

    def fail(self):
        return self.code != 0 and self.aout == self.eout

def main(okDirs,errDirs,args):
    ## A test of the summary output
    logger = TestHarnessLogger()
    parse_cmd_args(logger,args)
    for x in okDirs:
        run_tests_in_dir(logger, check_pass, x)
    for x in errDirs:
        run_tests_in_dir(logger, check_fail, x)
    logger.log(logger.show())

## logger: Logger
## fn:     (Logger, result) -> Unit
## d:      dir-path
def run_tests_in_dir(logger, fn, d):
    """Execute tests in directory d checking results with function fn."""
    ## Turn on focused verbosity
    if logger.is_verbose_on(d):
        logger.set_verbose(True)
    logger.verbose_log("Entering test directory {0}".format(d))
    for x in os.listdir(d):
        x = d+x
        ## Recursively go through subdirectories
        if os.path.isdir(x):
            run_tests_in_dir(logger, fn, x+"/")
        ## Process only *.fk files
        elif os.path.isfile(x) and x.endswith(".fk"):
            ## Turn on focused verbosity
            if logger.is_verbose_on(os.path.basename(x)):
                logger.set_verbose(True)
            process_file(logger, fn, x)
            ## Turn off focused verbosity
            if logger.is_verbose_on(os.path.basename(x)):
                logger.set_verbose(False)
    ## Turn off focused verbosity
    if logger.is_verbose_on(d):
        logger.set_verbose(False)

def process_file(logger, fn, x):
    ## Parse the file to obtain list of directives
    ds = parse_file(logger, x)
    if ds:
        res = process_directives(logger, x, ds)
        ## Log
        list(map(lambda r: fn(logger,r), res))

def log_directives(logger, x, ds):
    logger.verbose_log("Directives for {0}".format(x))
    for (k,v,args) in ds:
        logger.verbose_log(show_directive(k,v,args))

def check_pass(logger, res):
    ttype = "r" if res.regression else "t"
    if res.success():
        status = "Passed"
        logger.inc("ep",ttype)
    else:
        status = "FAILED"
        logger.inc("uf",ttype)
    log_run(logger,status,res)

def check_fail(logger, res):
    ttype = "r" if res.regression else "t"
    if res.fail():
        status = "Failed"
        logger.inc("ef",ttype)
    else:
        status = "PASSED"
        logger.inc("up",ttype)
    log_run(logger,status,res)

def log_run(logger,status,res):
    log = [("File",res.test)
          ,("Description",res.desc)
          ,("Directive", show_directive(*res.directive))
          ,("Status", status)
          ,("Output", res.aout)]
    width = max(list(map(lambda x:len(x[0]),log)))
    top = "\n".rjust(width+2,'-')
    bot = "\n".ljust(width+2,'-')
    logRep = '\n'.join(["{1:{0}}: {2}".format(width,k,v) for (k,v) in log])
    rep = top + logRep + bot
    logger.verbose_log(rep)

def show_directive(k,v,args):
    argRep = "".join(["~{0} {1}".format(x,y) for (x,y) in args])
    return "#{0} {1} {2}".format(k,v,argRep)

## (Logger, File) -> [Directive]
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

def get_desc(ds):
    for (k,v,args) in ds:
        if k == "desc":
            return v
    return None

def process_directives(logger, x, ds):
    rs = []
    desc = get_desc(ds)
    for (k,v,args) in ds:
        if directive_has_result(k):
            rs.append(process_directive(logger,x,desc,k,v,args))
    return rs

def process_directive(logger,x,desc,k,v,args):
    isRegression = True if os.path.basename(x).startswith('r') else False
    if k == "return":
        p = Popen(["frank", x],stderr=PIPE,stdout=PIPE)
        p.wait()
        ret = p.returncode
        (out,err) = p.communicate()
        out = err.decode("utf-8") + out.decode("utf-8")
        res = Result(x,desc,ret,out.strip('\n'),v,(k,v,args),isRegression)
        return res

def directive_has_result(k):
    return k == "return"

def parse_cmd_args(logger, args):
    if args.verbose:
        if args.verbose == True:
            logger.set_verbose(args.verbose)
        else:
            logger.set_verbose_on(args.verbose)

if __name__ == "__main__":
    import sys
    import argparse
    desc = "Run the test suite for the Frank implementation"
    more = "PATH may be a filename or sub-directory \
    in which case verbose output is produced for PATH only."
    parser = argparse.ArgumentParser(description=desc)
    parser.add_argument("--verbose", nargs='?', const=True, default=False,
                        metavar="PATH",
                        help="Produce verbose output. {0}".format(more))
    args = parser.parse_args()
    # Invariant: All directories end with a forward slash.
    main(["tests/should-pass/", "examples/"], ["tests/should-fail/"], args)
