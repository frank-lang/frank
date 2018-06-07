#!/usr/bin/python3

## Test harness for Frank
## Craig McLaughlin
## See the musings document for details on the proposed specification for this
## harness.

import io
import os
from subprocess import Popen,PIPE,TimeoutExpired

dirs = ["tests/should-pass/", "examples/", "tests/should-fail/", "tests/still-todo/"]
showSuccesses = False
showSuccessesDetail = False
showFailures  = True
showFailuresDetail = True

stats = dict()

def main():
    for d in dirs:
        run_tests_in_dir(d)

    # Print stats
    for marking, count in sorted(stats.items()):
        print(marking + ": " + str(count))

## logger: Logger
## fn:     (Logger, result) -> Unit
## d:      dir-path
def run_tests_in_dir(d):
    """Execute tests in directory d checking results with function fn."""
    for x in sorted(os.listdir(d)):
        x = d+x
        ## Recursively go through subdirectories
        if os.path.isdir(x):
            run_tests_in_dir(x+"/")
        ## Process only *.fk files
        elif os.path.isfile(x) and x.endswith(".fk"):
            process_file(x)

def process_file(x):
    ## Parse the file to obtain list of directives
    ds = parse_file(x)
    if ds:
        out = ""
        for (k, v, args) in ds:
            out += process_directive(x, ds, k, v, args)
        if out:
            print(x)
            print(out)
            print("\n\n")

## File -> [Directive]
def parse_file(x):
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

def get_flags(ds):
    for (k,v,args) in ds:
        if k == "flags":
            return [z for (x,y) in args for z in ["--" + x,y]]
    return []

def process_directive(x,ds,k,v,args):
    if k == "return":
        flags = get_flags(ds)
        p = Popen(["frank"] + flags + [x],stderr=PIPE,stdout=PIPE)
        p.wait()
        ret = p.returncode
        try:
            #TODO: LC: Timeout does not work...
            (out,err) = p.communicate(timeout=15)
            out = (err.decode("utf-8") + out.decode("utf-8")).strip()
        except TimeoutExpired:
            p.kill()
            out = "TIMEOUT"

        isSuccess = out == v

        # Stats
        isRegression = True if os.path.basename(x).startswith('r') else False
        if isRegression:
            registerStat("regression", isSuccess)
        for d in dirs:
            if x.startswith(d):
                registerStat(d, isSuccess)

        # Output
        res = ""
        if isSuccess and showSuccesses:
            res += "PASS"
            if showSuccessesDetail:
                res += "\nOutput:   " + out

        if (not isSuccess) and showFailures:
            res += "FAIL"
            if showFailuresDetail:
                res += "\nExpected: " + v
                res += "\nOutput:   " + out

        if (len(args) > 0):
            res += str(args)
        return res
    else:
        return ""

def registerStat(marking, isSuccess):
    marking = ("successful " if isSuccess else "failing    ") + marking

    if (marking) in stats:
        stats[marking] += 1
    else:
        stats[marking] = 1

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
    main()
