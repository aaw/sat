#!/usr/bin/python3

# Usage: python3 simplify_unsat.py <binary> <input_file>
#
# Given a binary SAT solver and a DIMACS input file that the SAT solver reports
# as unsatisfiable, remove the maximal number of clauses from the file such that
# the SAT solver still reports unsatisfiable.

import os
import subprocess
import sys
from tempfile import NamedTemporaryFile

def gen_file(clauses, keep):
    f = NamedTemporaryFile(mode='w',delete=False)
    contents = [clause for clause,k in zip(clauses,keep) if k]
    f.write(''.join(contents))
    f.close()
    return f.name

def run_sat(binary, fname):
    process = subprocess.run([binary, fname],
                             stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE,
                             universal_newlines=True)
    x = process.returncode
    print('Result is %s' % x)
    return int(x)

def minimize(binary, clauses):
    keep = [True for line in clauses]
    fname = None
    for i in range(1, len(clauses)):
        print('%s/%s...' % (i,len(clauses)))
        keep[i] = False
        fname = gen_file(clauses, keep)
        if run_sat(binary, fname) != 20:
            keep[i] = True
        os.unlink(fname)
    return gen_file(clauses, keep)

if __name__ == '__main__':
    try:
        assert(len(sys.argv) == 3)
        binary = sys.argv[1]
        input_file = sys.argv[2]
    except:
        print('Usage: "simplify_unsat.py binary input_file"')
        sys.exit(-1)
    assert(run_sat(binary, input_file) == 20)
    clauses = [line for line in open(input_file).readlines()
               if not line.startswith('c')]
    fname = minimize(binary, clauses)
    print("Final result stored in %s" % fname)
