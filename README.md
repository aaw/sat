SAT solvers
===========

This repo contains SAT solvers that are implemented following descriptions in
Donald Knuth's "The Art of Computer Programming, Volume 4, Fascicle 6:
Satisfiability".

Solvers currently implemented are:

  * 7.2.2.2 Algorithm B: Backtracking with watched literals
  * 7.2.2.2 Algorithm D: Cyclic [DPLL](https://en.wikipedia.org/wiki/DPLL_algorithm)

In contrast to Knuth's descriptions, these solvers are all implemented using
"structured programming" instead of gotos and labels and are built to accept
DIMACS input files and follow the
[output format](https://www.satcompetition.org/2004/format-solvers2004.html)
used in SAT comptetitions.

Building
--------

TODO: list build prerequisites

    make

Testing
-------

Using Instance Generators
-------------------------
