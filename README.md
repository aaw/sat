SAT solvers
===========

This repo contains SAT solvers that are implemented following descriptions in
Donald Knuth's "The Art of Computer Programming, Volume 4, Fascicle 6:
Satisfiability".

Solvers currently implemented are:

  * 7.2.2.2 Algorithm B: Backtracking with watched literals
  * 7.2.2.2 Algorithm D: Cyclic [DPLL](https://en.wikipedia.org/wiki/DPLL_algorithm)
  * 7.2.2.2 Algorithm C: [CDCL](https://en.wikipedia.org/wiki/Conflict-driven_clause_learning)
  * 7.2.2.2 Algorithm L: DPLL with lookahead
  * 7.2.2.2 Algorithm W: [WalkSAT](https://en.wikipedia.org/wiki/WalkSAT) (In progress)

These solvers are all built to accept
DIMACS input files and follow the
[output format](https://www.satcompetition.org/2004/format-solvers2004.html)
used in SAT comptetitions.

Building
--------

You'll need `git` to clone this repo, `g++` and `make` to build and `python3` to run
instance generators in the gen/ subdirectory. `bash` is used as the shell for scripts.

On a debian-based Linux distribution, you can ensure you have everything you need by
running:

    apt-get update && apt-get install bash build-essential git python3

Clone this repo:

    git clone git@github.com:aaw/sat.git

cd into the top level of the clone (`cd sat`) and run `make` to make sure everything
builds. This should build four binaries and put them in the bin/ subdirectory:

   * bin/btwl (Algorithm B)
   * bin/dpll (Algorithm D)
   * bin/cdcl (Algorithm C)
   * bin/look (Algorithm L)
   * bin/walk (Algorithm W)

To create the fastest binaries, compile out any logging, counters, or timers by adding
`OPT=1`:

    make bin/cdcl OPT=1

Running
-------

Run any of the SAT solver binaries against a DIMACS CNF input file by passing the
input file as an argument, for example:

    ./bin/dpll ./test/simple_1.cnf

You can change the verbosity of the output with the `-v` flag. By default, verbosity
is set to 0 and gives the minimal amount of output needed. Larger values of
verbosity output more. For all solvers, verbosity level 1 gives a visual
representation of the solver state during the search, so you can get some idea of
how the backtracking process works by running, for example:

     ./bin/btwl -v1 ./test/waerden_4_4_35.cnf

Testing
-------

The script/ subdirectory contains test scripts and the test/ subdirectory contains
test instances in the form of DIMACS CNF files. Instances are all annotated with
comments that tell whether the instance is satisfiable/unsatisfiable and a subjective
rating of easy/medium/hard.

The script/test.sh script can be used to test a SAT solver against all instances of a
particular difficulty class. Pass the desired binary with `-b` and the desired
difficulty with `-d` and an optional per-instance timeout with `-t`. For example, to
test the `dpll` binary against all easy instances with a timeout of 10 seconds per
instance, run the following from the top level of this repo:

    ./script/test.sh -bdpll -deasy -t10s

Using Instance Generators
-------------------------

Generators in the gen/ subdirectory are meant to be run at the command line and
output the instance to `stdout`. Each generator takes a different set of arguments
described in the header comments to the generator. To generate an instance file,
for example, just redirect the output to a file:

    ./gen/langford.py 5 > langford_5.cnf

To run a SAT solver directly against the output of a generator without an intermediate
file, use bash process substitution:

    ./bin/dpll <(./gen/langford.py 5)