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
  * 7.2.2.2 Algorithm W: [WalkSAT](https://en.wikipedia.org/wiki/WalkSAT)

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
builds. This should build five binaries and put them in the bin/ subdirectory:

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

All solvers accept a set of common flags:

   * `-s`: Set the random seed.
   * `-v`: Set the logging verbosity to a number >= 0. 0 means no logging, more detail comes with higher levels.
   * `-t`: Collect timing information, dump at exit.
   * `-c`: Collect counters, dump at exit.
   * `-dF`: Output a [DRAT proof](https://www.cs.utexas.edu/~marijn/drat-trim) on unsatisfiable instances to file F. (Only works for bin/cdcl.)
   * `-p[p1=v1][;pn=vn]*`: Set binary-specific parameters to floating point values.
   * `-h`: Display all flags and parameters available.

Testing
-------

The script/ subdirectory contains test scripts and the test/ subdirectory contains
test instances in the form of DIMACS CNF files. Instances are all annotated with
comments that tell whether the instance is satisfiable/unsatisfiable and a subjective
rating of easy/medium/hard.

The `script/test.sh` script can be used to test a SAT solver against all instances of a
particular difficulty class. Pass the desired binary with `-b` and the desired
difficulty with `-d` and an optional per-instance timeout with `-t`. For example, to
test the `dpll` binary against all easy instances with a timeout of 10 seconds per
instance, run the following from the top level of this repo:

    ./script/test.sh -bdpll -deasy -t10s

A full list of flags accepted by `script/test.sh`:

   * `-b`: The binary to test, one of `{btwl,dpll,cdcl,look,walk}`. Default: `btwl`.
   * `-d`: Test instance difficulty, one of `{easy,medium,hard}`. Default: easy.
   * `-l`: Test instance label, one of `{sat,unsat}`. Default: test both sat and unsat.
   * `-p`: Binary-specific params. Passed through directly as `-p` flags to the binary.
   * `-s`: Random seed. Passed through directly as `-s` flag to the binary.
   * `-t`: Timeout. Format is a floating point duration with an optional suffix of `s` (seconds, default), `m` (minutes), `h` (hours), `d` (days).
   * `-v`: If set, verify results. Uses `script/verify_sat.py` to verify satisfiable results and expects
     [`bin/drat-trim`](https://github.com/marijnheule/drat-trim) to exist to verify unsatisfiable results.
     All binaries can have their satisfiable results verified, only `cdcl` can have its unsatisfiable results verified.

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

Fuzzing
-------

`./script/fuzz.sh` supports fuzz-testing one binary against another on randomly generated
instances. Random instances close to the sat/unsat threshold are created using the `./gen/rand.py` generator.

Flags accepted:

   * `-b`: The experiment binary, one of `{btwl,dpll,cdcl,look,walk}`. Default: `look`.
   * `-c`: The control binary, one of `{btwl,dpll,cdcl,look,walk}`. Default: `cdcl`.
   * `-d`: The difficulty, one of `{easy,medium,hard}`. Default: easy.
   * `-n`: Number of tests to run. Default: 20.
   * `-p`: Parameters sent to the experiment binary.
   * `-r`: Random seed used by the control binary.
   * `-s`: Random seed used by the experiment binary.
   * `-t`: Timeout. Same format accepted by `./script/test.sh`.