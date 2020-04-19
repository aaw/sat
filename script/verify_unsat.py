#!/usr/bin/python3

# Usage: python3 verify_unsat.py <command line to run solver on unsat instance>
#
# Verifies that the solver exits with return value 20 and produces a verified
# DRAT-trim proof for the input formula.
#
# This script requires the drat-trim binary in the bin directory. drat-trim is
# available at https://www.cs.utexas.edu/~marijn/drat-trim.

import os
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

def extract_proof_file(argv):
    grab_next = False
    for arg in argv:
        if grab_next:
            return arg
        if arg.startswith('-d') and len(arg) > 2:
            return arg[2:]
        elif arg.startswith('--d='):
            return arg[4:]
        elif arg == '-d' or arg == '--d':
            grab_next = True
    raise RuntimeError("Couldn't find DRAT proof file in args: '%s'" % argv)

# Run the solver, verify return code.
def run(argv):
    process = subprocess.Popen(argv, stdout=subprocess.PIPE)
    for line in iter(process.stdout.readline, b''): pass
    process.wait()
    if process.returncode != 20:
        raise RuntimeError("Expected exit code 20, got %s" % process.returncode)

def verify(fname, pname):
    process = subprocess.Popen(['bin/drat-trim', fname, pname],
                               stdout=subprocess.PIPE)
    for line in iter(process.stdout.readline, b''): pass
    process.wait()
    if process.returncode != 0:
        raise RuntimeError(
            "Expected exit code 0 from drat-trim, got %s" % process.returncode)

if __name__ == '__main__':
    fname = extract_input_file(sys.argv[2:])
    pname = extract_proof_file(sys.argv[2:])
    run(sys.argv[1:])
    verify(fname, pname)
