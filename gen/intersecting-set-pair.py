#!/usr/bin/python3

# Usage: $ generate-sat.py k l i n
#
# Generates a DIMACS CNF file that's satisfiable iff there's a
# cross-intersecting set system with m(k,l,i) = n.
#
# Let {(A_i, B_i}} (1 <= i <= n) be a set pair system. An i-cross-intersecting
# system has #(A_i intersect B_j) = 1 when i != j and 0 when i = j.
#
# Kostochka, McCourt, and Nahvi have recently shown that
#
#   m(k,l,i) <= 5/6 * nCr(k + l, k). for k,l >= 2
#
# See https://blog.aaw.io/2022/04/10/intersecting-set-pair-systems.html for more
# about this generator.

import argparse
import itertools
import re
import sys
import tempfile
from collections import defaultdict

# Global variable counter.
vc = 0
def new_var(): global vc; vc += 1; return vc
def num_vars(): global vc; return vc

def ensure_vars(nv): global vc; vc = nv

# Global clause counter.
cc = 0
def write_clause(f, c):
    global cc
    f.write((" ".join(["{}"] * len(c)) + " 0\n").format(*c))
    cc += 1
def num_clauses(): global cc; return cc

# Global comment accumulator.
comments = []
def add_comment(c):
    global comments
    comments.append(c)

def all_comments():
    global comments
    for c in comments: yield c

# Makes v true iff disjunction of vars in d is true
def disjunction_witness(cf, d, v=None):
    if v is None:
        v = new_var()
    write_clause(cf, [dv for dv in d] + [-v])
    for dv in d:
        write_clause(cf, [v, -dv])
    return v

# Makes v true iff conjunction of vars in c is true
def conjunction_witness(cf, c, v=None):
    if v is None:
        v = new_var()
    write_clause(cf, [-cv for cv in c] + [v])
    for cv in c:
        write_clause(cf, [-v, cv])
    return v

# Generates clauses satisfiable iff exactly one of the variables in vs is true.
def exactly_one_true(vs):
    vvs = tuple(v for v in vs)
    return [vvs] + [(-x,-y) for x,y in itertools.combinations(vvs, 2)]

# Generates clauses satisfiable iff at most one of the variables in vs is true.
def at_most_one_true(vs):
    vvs = tuple(v for v in vs)
    return [(-x,-y) for x,y in itertools.combinations(vvs, 2)]

# Generates clauses satisfiable iff at most one of the variables in vs is false.
def at_most_one_false(vs):
    vvs = tuple(v for v in vs)
    return [(x,y) for x,y in itertools.combinations(vvs, 2)]

# Given variables a, b, minout, and maxout, generates clauses that are
# satisfiable iff minout = min(a,b) and maxout = max(a,b).
def comparator(a, b, minout, maxout):
    return [(-maxout, a, b), (-a, maxout), (-b, maxout),
            (minout, -a, -b), (a, -minout), (b, -minout)]

def apply_comparator(cf, vin, i, j):
    newmin, newmax = new_var(), new_var()
    for clause in comparator(vin[i], vin[j], newmin, newmax):
        write_clause(cf, clause)
    #vin[i], vin[j] = newmin, newmax
    vin[i], vin[j] = newmax, newmin

def pairwise_sorting_network(cf, vin, begin, end):
    n, a = end - begin, 1
    while a < n:
        b, c = a, 0
        while b < n:
            apply_comparator(cf, vin, begin+b-a, begin+b)
            b, c = b+1, (c+1) % a
            if c == 0: b += a
        a *= 2

    a //= 4
    e = 1
    while a > 0:
        d = e
        while d > 0:
            b = (d+1) * a
            c = 0
            while b < n:
                apply_comparator(cf, vin, begin+b-d*a, begin+b)
                b, c = b+1, (c+1) % a
                if c == 0: b += a
            d //= 2
        a //= 2
        e = e*2 + 1

# Filter [vin[i], vin[i+n]) with [vin[j], vin[j+n)
def filter_network(cf, vin, i, j, n):
    for x in range(n):
        apply_comparator(cf, vin, i+x, j+n-1-x)

# Assert that exactly n of the vars in vin are true.
def exactly_n_true(cf, vin, n):
    n_true(cf, vin, n, True, True)

def at_most_n_true(cf, vin, n):
    n_true(cf, vin, n, True, False)

def at_least_n_true(cf, vin, n):
    n_true(cf, vin, n, False, True)

def n_true(cf, vin, n, at_most_n_true, at_least_n_true):
    if n == 0:
        if at_least_n_true: return
        for v in vin:
            write_clause(cf, (-v,))
        return
    n = n+1  # We'll select the top n+1, verify exactly one true.
    batches = len(vin) // n
    for b in range(1, batches):
        pairwise_sorting_network(cf, vin, 0, n)
        pairwise_sorting_network(cf, vin, b*n, (b+1)*n)
        filter_network(cf, vin, 0, b*n, n)
    # Now take care of the remainder, if there is one.
    rem = len(vin) - batches * n
    if rem > 0:
        pairwise_sorting_network(cf, vin, 0, n)
        pairwise_sorting_network(cf, vin, batches*n, len(vin))
        filter_network(cf, vin, n-rem, batches*n, rem)
    if at_least_n_true:
        # Assert that at most 1 of the first n are false
        for clause in at_most_one_false(vin[:n]):
            write_clause(cf, clause)
    if at_most_n_true:
        # Assert that at least 1 of the first n are false
        write_clause(cf, [-v for v in vin[:n]])

def generate_system(cf, k, l, i, n, z, strict, verbose):
    # Must assume a ground set of size z = (k+l-2) * n + 2
    # (First pair needs k+l elements, every pair after that
    # introduces at most k+l-2 new elements.)
    if z == 0:  # Unspecified
        z = (k+l-2)*n + 2

    # Variable k(j,y) means ground set member y is in the jth lhs set
    # Variable l(j,y) means ground set member y is in the jth rhs set
    ks, ls = {}, {}
    for j in range(n):
        for y in range(z):
            v1, v2 = new_var(), new_var()
            if verbose:
                add_comment("k(%s,%s) == %s" % (j,y,v1))
                add_comment("l(%s,%s) == %s" % (j,y,v2))
            ks[(j,y)] = v1
            ls[(j,y)] = v2

    # For all j, A_j does not intersect B_j
    for j in range(n):
        for y in range(z):
            write_clause(cf, [-ks[(j,y)], -ls[(j,y)]])

    # For all j != jj, A_j intersects B_jj in i elements (at least i if strict)
    for j, jj in itertools.combinations(range(n), 2):
        vs, ws = [], []
        for y in range(z):
            vs.append(disjunction_witness(cf, [ks[(j,y)],ls[(jj,y)]]))
            ws.append(disjunction_witness(cf, [ks[(jj,y)],ls[(j,y)]]))
        if strict:
            exactly_n_true(cf, vs, k + l - i)
            exactly_n_true(cf, ws, k + l - i)
        else:
            at_most_n_true(cf, vs, k + l - i)
            at_most_n_true(cf, ws, k + l - i)

    # For all j, #(A_j) = k
    for j in range(n):
        vs = []
        for y in range(z):
            vs.append(ks[(j,y)])
        exactly_n_true(cf, vs, k)

    # For all j, #(B_j) = l
    for j in range(n):
        vs = []
        for y in range(z):
            vs.append(ls[(j,y)])
        exactly_n_true(cf, vs, l)

    # Symmetry-breaking: assume first pair is {(0,1,..,k-1),(k,...,k+l-1)}
    for i in range(k):
        write_clause(cf, [ks[(0,i)]])
    for j in range(k,k+l):
        write_clause(cf, [ls[(0,j)]])

    # Symmetry-breaking: assume second pair is {(k,...),(k-1,...)}
    write_clause(cf, [ks[(1,k)]])
    write_clause(cf, [ls[(1,k-1)]])

    # Symmetry-breaking: assume k_i < k_j for i < j
    # ks[(j,y)] means ground set member y is in the jth lhs set
    # ks[(j,0)] => ks[(i,0)]
    # ks[(j,1)] => (ks[(i,1)] OR ks[(i,0)]
    # ...
    for i,j in itertools.combinations(range(n), 2):
        for zz in range(z):
            write_clause(cf, [-ks[(j,zz)]] + [ks[(i,jj)] for jj in range(zz+1)])

    # Symmetry-breaking: assume ground set is rebased:
    # zz used => zz-1 used, etc.
    for zz in range(1,z):
        zz_anywhere = [ks[(j,zz)] for j in range(n)] + \
                      [ls[(j,zz)] for j in range(n)]
        prev_anywhere = [ks[(j,zz-1)] for j in range(n)] + \
                        [ls[(j,zz-1)] for j in range(n)]
        zz_used = disjunction_witness(cf, zz_anywhere)
        write_clause(cf, [-zz_used] + prev_anywhere)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(
        description="Encode a cross-intersecting set system as SAT")
    parser.add_argument('k', type=int, help='size of sets in left family')
    parser.add_argument('l', type=int, help='size of sets in right family')
    parser.add_argument('i', type=int, help='size of intersection')
    parser.add_argument('n', type=int,
                        help='size of cross-intersecting set system')
    parser.add_argument('--base_set', type=int, default=0,
                        help='size of base set')
    parser.add_argument('--strict', action='store_true',
                        help='(default) intersection size is exactly i')
    parser.add_argument('--no-strict', action='store_false',
                        help='intersection size is at least i')
    parser.set_defaults(strict=True)
    parser.add_argument('--verbose', action='store_true',
                        help='add verbose comments to CNF file')
    parser.add_argument('--no-verbose', action='store_false')
    parser.set_defaults(strict=True)
    args = parser.parse_args()

    with tempfile.TemporaryFile(mode='w+t') as cf:
        generate_system(cf, args.k, args.l, args.i, args.n,
                        args.base_set, args.strict, args.verbose)

        sys.stdout.write("c Generated by {0}\n".format(' '.join(sys.argv)))
        sys.stdout.write("c Generator source: " +
                         "https://github.com/aaw/sat/blob/master/gen/" +
                         "intersecting-set-pair.py\n")
        for comment in all_comments():
            sys.stdout.write('c {}\n'.format(comment))
        sys.stdout.write('p cnf {0} {1}\n'.format(num_vars(), num_clauses()))
        cf.seek(0)
        for line in cf:
            sys.stdout.write(line)
        sys.stdout.write('\n')
