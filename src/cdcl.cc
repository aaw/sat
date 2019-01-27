// Algorithm C from Knuth's The Art of Computer Programming 7.2.2.2: CDCL

#include <ctime>
#include <cstdlib>
#include <sstream>
#include <vector>

#include "flags.h"
#include "logging.h"
#include "types.h"

extern unsigned long FLAGS_seed;

enum State {
    UNSET = 0,
    FALSE = 1,           // Trying false, haven't tried true yet.
    TRUE = 2,            // Trying true, haven't tried false yet.
};

// Storage for the DPLL search and the final assignment, if one exists.
struct Cnf {
    std::vector<lit_t> clauses;

    std::vector<clause_t> start;

    std::vector<State> val;

    std::vector<State> oval;

    std::vector<unsigned long> stamp;  // TODO: what's the right type here?

    std::vector<lit_t> tloc;

    std::vector<double> act;

    std::vector<clause_t> reason_storage;
    clause_t* reason; // Keys: literals, values: clause indices

    std::vector<lit_t> hloc;

    // Heap is zero-indexed.
    std::vector<lit_t> heap;

    clause_t maxl;

    clause_t minl;

    clause_t nclauses;

    lit_t nvars;

    Cnf(lit_t nvars, clause_t nclauses) :
        val(nvars + 1, UNSET),
        oval(nvars + 1, FALSE),
        stamp(nvars + 1, 0),
        tloc(nvars + 1, lit_nil),
        act(nvars + 1, 0.0),
        reason_storage(2 * nvars + 1, clause_nil),
        reason(&reason_storage[nvars]),
        hloc(nvars + 1),
        heap(nvars + 1),
        nclauses(nclauses),
        nvars(nvars) {
        init_heap();
    }

    void init_heap() {
        if (FLAGS_seed != 1) {
            FLAGS_seed = time(NULL);
        }
        srand(FLAGS_seed);
        // Initialize hloc to a random permutation of [1,n]
        for (int i = 1; i <= nvars; ++i) {
            int r = rand() % i;
            heap[i - 1] = heap[r];
            heap[r] = i;
        }
        for (int i = 0; i < nvars; ++i) {
            hloc[heap[i]] = i;
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
    assert(nvars >= 0);
    assert(nclauses >= 0);
    ASSERT_NO_OVERFLOW(lit_t, nvars);
    ASSERT_NO_OVERFLOW(clause_t, nclauses);

    // Initialize data structures now that we know nvars and nclauses.
    Cnf c(static_cast<lit_t>(nvars), static_cast<clause_t>(nclauses));

    // Read clauses until EOF.
    int lit;
    do {
        bool read_lit = false;
        c.clauses.push_back(lit_nil);  // watch list pointer
        c.clauses.push_back(lit_nil);  // watch list pointer
        c.clauses.push_back(lit_nil);  // size of clause -- don't know this yet.
        std::size_t start = c.clauses.size();
        while (true) {
            nc = fscanf(f, " %i ", &lit);
            if (nc == EOF || lit == 0) break;
            c.clauses.push_back(lit);
            read_lit = true;
        }
        int cs = c.clauses.size() - start;
        if (cs == 0 && nc != EOF) {
            LOG(2) << "Empty clause in input file, unsatisfiable formula.";
            UNSAT_EXIT;
        } else if (cs == 1) {
            lit_t x = c.clauses[c.clauses.size() - 1];
            LOG(3) << "Found unit clause " << x;
            State s = x < 0 ? FALSE : TRUE;
            if  (c.val[abs(x)] != UNSET && c.val[abs(x)] != s) {
                LOG(2) << "Contradictory unit clauses, unsatisfiable formula.";
                UNSAT_EXIT;
            }
            c.val[abs(x)] = s;
        }
        // Record the size of the clause in offset -1.
        c.clauses[start - 1] = cs;
        if (!read_lit) break;
    } while (nc != EOF);

    c.minl = c.maxl = c.start.size() + 1;
    fclose(f);
    return c;
}


// Returns true exactly when a satisfying assignment exists for c.
bool solve(Cnf* c) {
    return false;
}

int main(int argc, char** argv) {
    int oidx;
    CHECK(parse_flags(argc, argv, &oidx)) <<
        "Usage: " << argv[0] << " <filename>";
    Cnf c = parse(argv[oidx]);
    // TODO: also check for no clauses (unsatisfiable) in the if
    // statement below.
    if (solve(&c)) {
        std::cout << "s SATISFIABLE" << std::endl;
        for (int i = 1, j = 0; i <= c.nvars; ++i) {
            if (c.val[i] == UNSET) continue;
            if (j % 10 == 0) std::cout << "v";
            std::cout << ((c.val[i] & 1) ? " -" : " ") << i;
            ++j;
            if (i == c.nvars) std::cout << " 0" << std::endl;
            else if (j > 0 && j % 10 == 0) std::cout << std::endl;
         }
        return SATISFIABLE;
    } else {
        std::cout << "s UNSATISFIABLE" << std::endl;
        return UNSATISFIABLE;
    }
}
