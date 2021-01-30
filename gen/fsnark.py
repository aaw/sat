#!/usr/bin/python3

# Usage: python3 fsnark.py n [--exclusions]
#
# Generates the fsnark(n) clauses described in Knuth 7.2.2.2, exercise 176.
# fsnark(n) asserts that the line graph of the flower snark graph can be
# 3-colored. This formula is satisfiable iff n is even. Passing the --exclusions
# arg generates fsnark'(n), which includes Knuth's "exclusion clauses" that
# assert that every vertex has at most one color.
#
# fsnark(n) for odd n is a surprisingly easy formula for CDCL solvers.

from collections import defaultdict
import io
import sys

def flower_snark_line_graph(q):
    g = defaultdict(list)

    def add_edge(x,y):
        if x > y: x,y = y,x
        g[x].append(y)

    # a = 0..q-1, b = q..2q-1, c = 2q..3q-1, d = 3q..4q-1
    # e = 4q..5q-1, f = 5q..6q-1
    for i in range(q):
        add_edge(i, (i+1) % q)            # {a_j, a_(j+1)}
        add_edge(i, q+i)                  # {a_j, b_j}
        add_edge(i, q + (i+1) % q)        # {a_j, b_(j+1)}
        add_edge(q+i, 2*q+i)              # {b_j, c_j}
        add_edge(q+i, 3*q+i)              # {b_j, d_j}
        add_edge(2*q+i, 3*q+i)            # {c_j, d_j}
        add_edge(2*q+i, 4*q+i)            # {c_j, e_j}
        add_edge(3*q+i, 5*q+i)            # {d_j, f_j}
        add_edge(4*q+i, 3*q + (i+1) % q)  # {e_j, d_(j+1)}
        add_edge(4*q+i, 5*q + (i+1) % q)  # {e_j, f_(j+1)}
        add_edge(5*q+i, 2*q + (i+1) % q)  # {f_j, c_(j+1)}
        add_edge(5*q+i, 4*q + (i+1) % q)  # {f_j, e_(j+1)}
    return g

def fsnark(n, exclusions):
    d = 3  # Number of colors available
    g = flower_snark_line_graph(n)

    # Maps vertex indices [0..n) and color indices [0..d) onto [1..nd] for the
    # DIMACS variable encoding. Variable v(i,c) asserts vertex i is colored c.
    def v(i,c):
        return i*d + c + 1

    clauses = []
    # Assert that every vertex is colored.
    for i in range(6*n):
        clause = []
        for c in range(d):
            clause.append(v(i,c))
        clauses.append(clause)

    # Assert that edges can't connect vertexes of the same color.
    for i, js in g.items():
        for j in js:
            for c in range(d):
                clauses.append([-v(i,c), -v(j,c)])

    if exclusions:
        # Assert that a vertex can only be colored a single color.
        for i in range(6*n):
            for c2 in range(d):
                for c1 in range(c2):
                    clauses.append([-v(i,c1), -v(i,c2)])

    # Knuth defines fsnark by bootstrapping three colors:
    # b_1 = 1, c_1 = 2, d_1 = 3.
    clauses.append([v(n,0)])
    clauses.append([v(2*n,1)])
    clauses.append([v(3*n,2)])

    buffer = io.StringIO()
    vs, es = 6*n*d, len(clauses)
    for c in clauses:
        buffer.write((" ".join(["{}"] * len(c)) + " 0\n").format(*c))
    return 'p cnf {0} {1}\n'.format(vs, es) + buffer.getvalue()

if __name__ == '__main__':
    try:
        assert(2 <= len(sys.argv) <= 3)
        n = int(sys.argv[1])
        assert(n > 0)
        exclusions = (len(sys.argv) == 3 and sys.argv[2] == '--exclusions')
    except:
        print('Usage: "fsnark.py n [--exclusions]" for integer n > 0')
        sys.exit(-1)
    print("c Generated by fsnark.py {0}".format(' '.join(sys.argv[1:])))
    print("c Generator source: " +
          "https://github.com/aaw/sat/blob/master/gen/fsnark.py")
    if n % 2 == 0:
        print("c label:satisfiable")
    else:
        print("c label:unsatisfiable")
    print(fsnark(n, exclusions))
