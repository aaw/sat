// Algorithm W from Knuth's The Art of Computer Programming 7.2.2.2: WalkSAT.

// This program either finds a satisfying assignment or runs forever.

#include <sstream>
#include <vector>

#include "counters.h"
#include "flags.h"
#include "logging.h"
#include "timer.h"
#include "types.h"

DEFINE_PARAM(initial_bias, 0.5,
             "Probability that true is selected for each variable during "
             "initial random assignment.");

// Flips a coin that lands on heads with probability p. Return true iff heads.
static bool flip(float p) {
    return static_cast<float>(rand())/RAND_MAX <= p;
}

struct Cnf {
    // Clauses are stored as a sequential list of literals in memory with no
    // terminator between clauses. Example: (1 OR 2) AND (3 OR -2 OR -1) would
    // be stored as [1][2][3][-2][-1]. The start array (below) keeps track of
    // where each clause starts -- in the example above, start[0] = 0 and
    // start[1] = 2. The end index of each clause can be inferred from the start
    // index of the next clause.
    std::vector<lit_t> clauses;

    // Zero-indexed map of clauses. Literals in clause i run from
    // clauses[start[i]] to clauses[start[i+1]] - 1 except for the final
    // clause, where the endpoint is just clauses.size() - 1. start.size() is
    // the number of clauses.
    std::vector<clause_t> start;

    // One-indexed values of variables in the satisfying assignment.
    std::vector<bool> val;

    // One-indexed costs of variables.
    std::vector<clause_t> cost;

    // Stack of unsatisfied clauses.
    std::vector<lit_t> f;

    // Number of true literals in clause
    std::vector<lit_t> k;

    // Reverse lookup into unsatisfied clauses. if f[i] = j, w[j] = i.
    std::vector<clause_t> w;

    // Number of variables in the formula. Valid variables range from 1 to
    // nvars, inclusive.
    lit_t nvars;

    clause_t nclauses;

    Cnf(lit_t nvars, clause_t nclauses) :
        val(nvars+1),
        cost(nvars+1, 0),
        k(nclauses, 0),
        w(nclauses, 0),
        nvars(nvars),
        nclauses(nclauses) {}

    // These two methods give the begin/end index of the kth clause in the
    // clauses vector. Used for iterating over all literals in the kth clause.
    inline clause_t clause_begin(clause_t c) const { return start[c]; }
    inline clause_t clause_end(clause_t c) const {
        return (c == start.size() - 1) ? clauses.size() : start[c + 1];
    }

    inline bool is_true(lit_t l) {
        bool tv = val[var(l)];
        return (tv && l > 0) || (!tv && l < 0);
    }

    void print_assignment() {
        for (int i = 1, j = 0; i <= nvars; ++i) {
            if (j % 10 == 0) PRINT << "v";
            PRINT << (val[i] ? " -" : " ") << i;
            ++j;
            if (i == nvars) PRINT << " 0" << std::endl;
            else if (j > 0 && j % 10 == 0) PRINT << std::endl;
        }
    }
};

// Parse a DIMACS cnf input file. File starts with zero or more comments
// followed by a line declaring the number of variables and clauses in the file.
// Each subsequent line is the zero-terminated definition of a disjunction.
// Clauses are specified by integers representing literals, starting at 1.
// Negated literals are represented with a leading minus.
//
// Example: The following CNF formula:
//
//   (x_1 OR x_2) AND (x_3) AND (NOT x_2 OR NOT x_3 OR x_4)
//
// Can be represented with the following file:
//
// c Header comment
// p cnf 4 3
// 1 2 0
// 3 0
// -2 -3 4 0
Cnf parse(const char* filename) {
    int nc;
    FILE* f = fopen(filename, "r");
    CHECK(f) << "Failed to open file: " << filename;

    // Read comment lines until we see the problem line.
    long long nvars = 0, nclauses = 0;
    do {
        nc = fscanf(f, " p cnf %lld %lld \n", &nvars, &nclauses);
        if (nc > 0 && nc != EOF) break;
        nc = fscanf(f, "%*s\n");
    } while (nc != 2 && nc != EOF);
    CHECK(nvars >= 0);
    CHECK(nclauses >= 0);
    CHECK_NO_OVERFLOW(lit_t, nvars);
    CHECK_NO_OVERFLOW(clause_t, nclauses);

    Cnf c(static_cast<lit_t>(nvars), static_cast<clause_t>(nclauses));

    // Read clauses until EOF.
    int lit;
    do {
        bool read_lit = false;
        std::size_t start = c.clauses.size();
        while (true) {
            nc = fscanf(f, " %i ", &lit);
            if (nc == EOF || lit == 0) break;
            c.clauses.push_back(lit);
            read_lit = true;
        }
        if (nc != EOF && start == c.clauses.size()) {
            LOG(2) << "Empty clause in input file, unsatisfiable formula.";
            UNSAT_EXIT;
        }
        if (!read_lit) break;
        c.start.push_back(start);
    } while (nc != EOF);

    fclose(f);
    return c;
}

// Returns true exactly when a satisfying assignment exists for c.
bool solve(Cnf* c) {
    Timer t("solve");

    // W1. [Initialize.]
    for (lit_t i = 1; i <= c->nvars; ++i) {
        c->val[i] = flip(PARAM_initial_bias);
    }
    for (clause_t i = 0; i < c->nclauses; ++i) {
        clause_t end = c->clause_end(i);
        lit_t tl = lit_nil;
        for (clause_t j = c->clause_begin(i); j < end; ++j) {
            if (c->is_true(c->clauses[j])) {
                ++c->k[i];
                tl = var(c->clauses[j]);
            }
        }
        if (c->k[i] == 0) {
            c->w[i] = c->f.size();
            c->f.push_back(i);
        } else if (c->k[i] == 1) {
            ++c->cost[tl];
        }
    }

    while (true) {
        // W2. [Done?]
        if (c->f.empty()) return true;
        // TODO: terminate with UNKNOWN if num iterations is too large?

        // W3. [Choose j.]
        // TODO

        // W4. [Choose l.]
        // TODO

        // W5. [Flip l.]
        // TODO
    }
}

int main(int argc, char** argv) {
    int oidx;
    CHECK(parse_flags(argc, argv, &oidx))
        << "Usage: " << argv[0] << " <filename>";
    init_counters();
    init_timers();
    Cnf c = parse(argv[oidx]);
    if (c.clauses.empty() || solve(&c)) {
        SAT_EXIT(&c);
    }
}
