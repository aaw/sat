// Algorithm W from Knuth's The Art of Computer Programming 7.2.2.2: WalkSAT.

// This program either finds a satisfying assignment or runs forever.

#include <sstream>
#include <vector>

#include "counters.h"
#include "flags.h"
#include "logging.h"
#include "timer.h"
#include "types.h"

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

    // Number of variables in the formula. Valid variables range from 1 to
    // nvars, inclusive.
    lit_t nvars;

    Cnf(lit_t nvars, clause_t nclauses) :
        nvars(nvars) {}

    // These two methods give the begin/end index of the kth clause in the
    // clauses vector. Used for iterating over all literals in the kth clause.
    inline clause_t clause_begin(clause_t c) const { return start[c]; }
    inline clause_t clause_end(clause_t c) const {
        return (c == start.size() - 1) ? clauses.size() : start[c + 1];
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
    return true;
}

int main(int argc, char** argv) {
    int oidx;
    CHECK(parse_flags(argc, argv, &oidx))
        << "Usage: " << argv[0] << " <filename>";
    init_counters();
    init_timers();
    Cnf c = parse(argv[oidx]);
    if (/* TODO: detect no clauses || */ solve(&c)) {
        SAT_EXIT(&c);
    }
}
