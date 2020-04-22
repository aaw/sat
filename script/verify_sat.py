#!/usr/bin/python3

# Usage: python3 verify_sat.py <command line to run sat solver on sat instance>
#
# Verifies that the solver exits with return value 10 and produces an assignment
# that satisifes the input formula.

import os
import re
import subprocess
import sys

def extract_input_file(argv):
    args = iter(argv)
    for arg in args:
        if arg.startswith('--') and arg.find('=') == -1:
            next(args, None)
            continue
        if arg.startswith('-') and not arg.startswith('--') and len(arg) == 2:
            next(args, None)
            continue
        if not arg.startswith('-'):
            return arg
    raise RuntimeError("Couldn't find DIMACS input file in args: '%s'" % argv)

# Run the solver, return satisfying assignment found.
def run(argv):
    litvals = {}
    process = subprocess.Popen(argv, stdout=subprocess.PIPE)
    for line in iter(process.stdout.readline, b''):
        if line.startswith(b'v '):
            ignore = (b'v', b' ', b'0')
            cleaned = [l.strip() for l in line.split(b' ')]
            ls = [int(l) for l in cleaned if l not in ignore]
            d = dict([(l,True) for l in ls] + [(-l,False) for l in ls])
            common = litvals.items() & d.items()
            if common:
                raise RuntimeError("Repeated literal values: %s" % common)
            litvals.update(d)
    process.wait()
    if process.returncode != 10:
        raise RuntimeError("Expected exit code 10, got %s" % process.returncode)
    return litvals

def verify(litvals, fname):
    clause = []
    with open(fname) as f:
        for line in f:
            if line.startswith('c') or line.startswith('p') or line.isspace():
                continue
            cleaned = [l.strip() for l in re.split(' |\t|\n', line)]
            clause += [int(l) for l in cleaned if l not in ('', ' ', '0')]
            if cleaned[-1] == '0':
                if not any(litvals[l] for l in clause):
                    raise RuntimeError("Clause %s not satisfied." % clause)
                clause = []

if __name__ == '__main__':
    fname = extract_input_file(sys.argv[2:])
    litvals = run(sys.argv[1:])
    verify(litvals, fname)
