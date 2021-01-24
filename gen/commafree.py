#!/usr/bin/python3

# Usage: python3 commafree.py n m d
#
# Generates clauses that are satisfiable exactly when there exists a set of
# comma-free codewords of size MAXCF(n,m) - d on words of size n using an
# alphabet of size m. MAXCF(n,m) is the maximum possible size of such a set,
# equal to the number of Lyndon words (also called "prime strings" by Knuth)
# of length n over an alphabet of size m. There's a closed-form formula for
# MAXCF(n,m) that involves the mobius function [1].
#
# A set of strings is comma-free if no concatenation of any two strings in
# the set contains another string in the set as a substring that overlaps
# both. So if '100' and '212' are in the set, '002' and '021' (and '121'
# and '210') can't be in the set. Here's an example comma-free code with
# words of length 3 over the alphabet {0,1,2} that achieves the maximum
# possible size:
#
#   {100, 101, 102, 200, 201, 202, 211, 212}
#
# If n is odd, the resulting clauses are satisfiable for any m >= 2 and
# m > d >= 0 due to results by Eastman [2].
#
# If n is even, not much is known beyond small values of n and m. Here's a
# sample of what's known:
#
# (n,m,d)  | SAT/UNSAT?
# ---------------------
# (2,2,0)  | SAT
# (2,4,0)  | UNSAT
# (2,4,1)  | SAT
# (4,3,0)  | SAT
# (4,4,0)  | UNSAT
# (4,4,3)  | SAT
# ...
# (10,2,0) | SAT
# (12,2,0) | UNSAT
# (12,2,1) | SAT
#
# [1] Golumb, S. W., B. Gordon, and L. R. Welch, Comma-free codes, Can. J.
#     Math, vol. 10, 1958, pp 202-209.
# [2] Eastman, W. L., On the Construction of Comma-Free Codes, IEEE Trans.
#     IT-11 (1965), pp 263-267.

import io
import itertools
import tempfile
import sys

# Global variable counter.
vc = 0
def new_var(): global vc; vc += 1; return vc
def num_vars(): global vc; return vc

# Global clause counter.
cc = 0
def write_clause(f, c):
    global cc
    f.write((" ".join(["{}"] * len(c)) + " 0\n").format(*c))
    cc += 1
def num_clauses(): global cc; return cc
    
# Generates all Lyndon words of length n over alphabet of size m. A Lyndon word
# is a string that is strictly lexicographically smaller than all of its
# rotations. Comma-free codes can only contain Lyndon words and their rotations.
# This method is essentially Knuth's Algorithm 7.2.1.1 F from The Art of
# Computer Programming, Volume 4A. Knuth calls these "prime strings".
def primes(n, m):
    a = [-1] + [0]*n
    j = 1
    while True:
        if j == n:
            yield tuple(a[1:])
        j = n
        while a[j] == m-1:
            j -= 1
        if j == 0: return
        a[j] += 1
        for i in range(j+1, n+1):
            a[i] = a[i-j]

# Generates all rotations of a string.
# rotations((1,2,3)) == ((1,2,3),(2,3,1),(3,1,2))
def rotations(t):
    for i in range(len(t)):
        yield t[i:]+t[:i]

# Generates clauses satisfiable iff at most one of the variables in vs is true.
def at_most_one_true(vs):
    return [(-x,-y) for x,y in itertools.combinations(vs, 2)]

# Given variables a, b, minout, and maxout, generates clauses that are
# satisfiable iff minout = min(a,b) and maxout = max(a,b).
def comparator(a, b, minout, maxout):
    return [(-maxout, a, b), (-a, maxout), (-b, maxout),
            (minout, -a, -b), (a, -minout), (b, -minout)]

# Given variables vin, returns a permutation of the values in vin such that if
# the d smallest elements of vin appear as the last d elements of vin in
# decreasing order, the d+1 smallest elements of vin appear as the last d+1
# elements of vout in decreasing order. This is essentially one round of
# bubblesort with the smallest elements appearing at the end of the output list.
def merge(cf, vin):
    vout = [0] * len(vin)
    minout = vin[0]
    for i in range(1, len(vin)):
        newmin, newmax = new_var(), new_var()
        for clause in comparator(minout, vin[i], newmin, newmax):
            write_clause(cf, clause)
        vout[i-1], vout[i] = newmax, newmin
        minout = newmin
    return vout

# Generates a variable for each non-cyclic string of length n over an alphabet
# of size m. Stores them in a map from string -> var so that we can add comments
# about the association of codewords to variables later. Also generates
# representative variables for each equivalence class of prime strings (under
# rotation) that asserts "something from this class is chosen". Returns the
# map of string -> var and the list of representative vars.
def make_vars(cf, n, m):
    var = {}
    reps = []
    for p in primes(n, m):
        rotvars = []
        for r in rotations(p):
            nv = new_var()
            var[r] = nv
            rotvars.append(nv)

        # Create a representative var and add clauses that assert "this string
        # or one of its rotations is chosen".
        nv = new_var()
        reps.append(nv)
        write_clause(cf, [-nv] + rotvars)
        for v in rotvars:
            write_clause(cf, (-v, nv))
    return (var, reps)

# Comma-free codes can't contain three strings x,y,z such that y is a substring
# of the concatentation of x and z (and has non-empty overlap with x and z).
# x,y,z can all be chosen with repetition but we're going to assert separately
# that at most one string per equivalence class (under rotations) is chosen, so
# we can consider pairs of distinct x,z here and disallow all possible y.
def disallow_forbidden_triples(cf, n, var):
    for xx in itertools.combinations(var.items(), 2):
        qx, qx_id = xx[0]
        qy, qy_id = xx[1]
        for x, x_id, y, y_id in [(qx, qx_id, qy, qy_id),
                                 (qy, qy_id, qx, qx_id)]:
            for i in range(1,n):
                z = tuple(x[i:]+y[:i])
                z_id = var.get(z)
                if z_id is None: continue
                write_clause(cf, (-x_id, -y_id, -z_id))

if __name__ == '__main__':
    if len(sys.argv) < 4:
        print('Usage: %s n m d' % sys.argv[0])
        sys.exit(1)
    n, m, d = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    assert (n > 1), "n must be greater than 1"
    assert (m > 1), "m must be greater than 1"
    
    with tempfile.TemporaryFile(mode='w+t') as cf:
        # Generate variables for all possible codewords and equivalence classes.
        var, vout = make_vars(cf, n, m)
        assert (d < len(vout)), \
            "impossible value of d=%s: only %s prime strings" % (d,len(vout))

        # Assert that at most one codeword from each equivalence class (under
        # rotations) is chosen.
        for p in primes(n, m):
            for clause in at_most_one_true([var[r] for r in rotations(p)]):
                write_clause(cf, clause)

        # Don't allow any three strings (x,y,z) in the final set of codewords
        # if y is a substring of the concatenation of x and z.
        disallow_forbidden_triples(cf, n, var)

        # Finally, we need to make an assertion about the size of the set of
        # codewords. When we created variables for each prime string and all of
        # its rotations, we also created variables that represent 'some member
        # of this equivalence class was chosen' for each prime string's
        # equivalence class. We run d+1 rounds of bubblesort over these
        # representatives now, after which the d smallest values should be false
        # and the (d+1)st smallest value should be true if we're exactly d away
        # from the maximum possible code size.
        if len(vout) > 1:
            for i in range(d+1):
                vout = merge(cf, vout)
            for i in range(d):
                write_clause(cf, [-vout[-1-i]])
            write_clause(cf, [vout[-1-d]])

        # Write the final DIMACS file. We've cached clauses in a temp file until
        # now, so we'll rewind and write those out to stdout as a final step.
        sys.stdout.write(
            "c Generated by commafree.py {0}\n".format(' '.join(sys.argv[1:])))
        sys.stdout.write(
            "c Generator source: github.com/aaw/sat/gen/commafree.py\n")
        for k,v in sorted(var.items(), key=lambda x: x[1]):
            sys.stdout.write('c var %s == %s chosen\n' %
                             (v, ''.join(str(x) for x in k)))        
        sys.stdout.write('p cnf {0} {1}\n'.format(num_vars(), num_clauses()))
        cf.seek(0)
        for line in cf:
            sys.stdout.write(line)
        sys.stdout.write('\n')
