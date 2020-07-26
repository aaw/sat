SAT solvers
===========

This repo contains SAT solvers that are implemented following descriptions in
Donald Knuth's "The Art of Computer Programming, Volume 4, Fascicle 6:
Satisfiability".

Solvers currently implemented are:

  * 7.2.2.2 Algorithm B: Backtracking with watched literals
  * 7.2.2.2 Algorithm D: [DPLL](https://en.wikipedia.org/wiki/DPLL_algorithm)
  * 7.2.2.2 Algorithm C: [CDCL](https://en.wikipedia.org/wiki/Conflict-driven_clause_learning)
  * 7.2.2.2 Algorithm L: DPLL with lookahead (modeled after [march](https://github.com/marijnheule/march-SAT-solver) [[1]](http://www.cs.cmu.edu/~mheule/publications/35420345.pdf) [[2]](http://www.cs.cmu.edu/~mheule/publications/JSAT2_3_Heule.pdf))
  * 7.2.2.2 Algorithm W: [WalkSAT](https://en.wikipedia.org/wiki/WalkSAT)

These solvers are all built to accept
DIMACS input files and follow the
[output format](https://www.satcompetition.org/2004/format-solvers2004.html)
used in SAT comptetitions.

Building
--------

You'll need `git` to clone this repo, `g++` and `make` to build and `python3` to run
instance generators in the gen/ subdirectory. `bash` is used as the shell for scripts.

On a debian-based Linux distribution, you can make sure you have everything you need by
running:

    apt-get update && apt-get install bash build-essential git python3

Next, clone this repo:

    git clone git@github.com:aaw/sat.git

cd into the top level of the clone (`cd sat`) and run `make` to buld everything.
This should produce five binaries and put them in the bin/ subdirectory:

   * `btwl` (Algorithm B)
   * `dpll` (Algorithm D)
   * `cdcl` (Algorithm C)
   * `look` (Algorithm L)
   * `walk` (Algorithm W)

To create the fastest binaries, compile out any logging, counters, or timers by adding
`OPT=1` and rebuilding from scratch:

    make clean bin/cdcl OPT=1

Running
-------

Run any of the SAT solver binaries against a DIMACS CNF input file by passing the
input file as an argument, for example:

    ./bin/dpll ./test/simple_1.cnf

All solvers accept a set of common flags:

   * `-sN`: Set the random seed to integer `N`.
   * `-vN`: Set the logging verbosity to a number `N` >= 0. 0 means no logging, more detail comes with higher levels.
   * `-t`: Collect timing information, dump at exit.
   * `-c`: Collect counters, dump at exit.
   * `-dF`: Output a [DRAT proof](https://www.cs.utexas.edu/~marijn/drat-trim) on unsatisfiable instances to file F. (Only works for `cdcl`.)
   * `-p[p1=v1][;pn=vn]*`: Set binary-specific parameters to floating point values.
   * `-h`: Display all flags and parameters available.

Testing
-------

The script/ subdirectory contains test scripts and the test/ subdirectory contains
test instances (DIMACS CNF files). Test files are all annotated with
comments labeling them as satisfiable/unsatisfiable and a subjective
rating of easy/medium/hard.

The `script/test.sh` script can be used to test a SAT solver against these files.
Pass the solver with `-b`, the difficulty with `-d` and an optional per-instance
timeout with `-t`. For example, to test the `dpll` solver against all easy instances
with a timeout of 10 seconds per instance, run:

    ./script/test.sh -bdpll -deasy -t10s

A full list of flags accepted by `script/test.sh`:

   * `-bX`: The solver to test, where `X` is one of `{btwl,dpll,cdcl,look,walk}`. Default: `btwl`.
   * `-dX`: Test instance difficulty, where `X` is one of `{easy,medium,hard}`. Default: easy.
   * `-lX`: Test instance label, where `X` is either `sat or `unsat`. Default: test both sat and unsat.
   * `-pX`: Binary-specific params. `X` is passed through directly as `-p` flags to the solver.
   * `-sN`: Random seed, an integer. `N` is passed through directly as `-s` flag to the solver.
   * `-tX`: Timeout. Format for `X` is a floating point duration with an optional suffix of `s`
     (seconds, default), `m` (minutes), `h` (hours), `d` (days).
   * `-v`: If set, verify results. Uses `script/verify_sat.py` to verify satisfiable results and expects
     [`bin/drat-trim`](https://github.com/marijnheule/drat-trim) to exist to verify unsatisfiable results.
     All binaries can have their satisfiable results verified, only `cdcl` can have its unsatisfiable results verified.

Using Instance Generators
-------------------------

Generators in the gen/ subdirectory are meant to be run at the command line and
output the instance to `stdout`. Read the header comments for a generator to see
the command-line arguments it expects. To generate an instance file,
for example, just redirect the output to a file:

    ./gen/langford.py 5 > langford_5.cnf

To run a SAT solver directly against the output of a generator without an intermediate
file, use bash process substitution:

    ./bin/dpll <(./gen/langford.py 5)

Fuzzing
-------

`./script/fuzz.sh` supports fuzz-testing one binary against another on randomly generated
instances. Random instances close to the sat/unsat threshold are created using the `./gen/rand.py` generator.

Flags accepted:

   * `-bX`: The experiment solver, where `X` is one of `{btwl,dpll,cdcl,look,walk}`. Default: `look`.
   * `-cX`: The control solver, where `X` is one of `{btwl,dpll,cdcl,look,walk}`. Default: `cdcl`.
   * `-dX`: The difficulty, where `X` is one of `{easy,medium,hard}`. Default: easy.
   * `-nN`: Number of tests `N` to run. Default: 20.
   * `-pX`: Parameters sent to the experiment solver.
   * `-rN`: Integer random seed `N` used by the control binary.
   * `-sN`: Integer random seed `N` used by the experiment binary.
   * `-tX`: Timeout. `X` should be in the same timeout format accepted by `./script/test.sh`.