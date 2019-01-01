// Algorithm B from 7.2.2.2: Backtracking with a watchlist.

#include <cstdio>
#include <cstdlib>
#include <sstream>
#include <vector>

#include "flags.h"
#include "logging.h"
#include "types.h"

// States used by both the search algorithm and the final assignment. If the
// formula is satisfiable, all variables will end up in a state > UNEXAMINED.
enum State {
    UNEXAMINED = 0,
    FALSE = 1,           // Trying false, haven't tried true yet.
    TRUE = 2,            // Trying true, haven't tried false yet.
    FALSE_NOT_TRUE = 3,  // Trying false because true failed.
    TRUE_NOT_FALSE = 4   // Trying true because false failed.
};

// Storage for the backtracking search and the final variable assignment.
struct Cnf {
    // Clauses are stored as a sequential list of literals in memory with no
    // terminator between clauses. Example: (1 OR 2) AND (3 OR -2 OR -1) would
    // be stored as [1][2][3][-2][-1]. The start array (below) keeps track of
    // where each clause starts -- in the example above, start[0] = 0 and
    // start[1] = 2. The end index of each clause can be inferred from the start
    // index of the next clause. The watched literal in each clause is always
    // the first literal in the clause. We swap literals within a clause to
    // maintain this invariant throughout the algorithm.
    std::vector<lit_t> clauses;

    // Zero-indexed map of clauses. Literals in clause i run from
    // clauses[start[i]] to clauses[start[i+1]] - 1 except for the final
    // clause, where the endpoint is just clauses.size() - 1. start.size() is
    // the number of clauses.
    std::vector<clause_t> start;

    // Watch lists. watch maps a literal to the index of a clause that watches
    // that literal, or clause_nil if there is no such clause. link maps a
    // clause c to another clause that shares the same watched literal as c,
    // or clause_nil if there is no such clause. These two maps can be used to
    // iterate over all clauses that watch a particular literal. For example,
    // watch[-2], link[watch[-2]], and link[link[watch[-2]]] are all clauses
    // that watch the literal -2, assuming none are clause_nil. watch is just
    // a pointer to the middle element of watch_storage, allowing watch to
    // accept indexes that are negated variables.
    std::vector<clause_t> watch_storage;
    std::vector<clause_t> link;
    clause_t* watch;

    // One-indexed values of variables in the satisfying assignment.
    std::vector<State> vals;

    // Number of variables in the problem. Valid variables range from 1 to
    // nvars, inclusive.
    lit_t nvars;

    Cnf(lit_t nvars, clause_t nclauses) :
        watch_storage(2 * nvars + 1, clause_nil),
        link(nclauses, clause_nil),
        watch(&watch_storage[nvars]),
        vals(nvars + 1, UNEXAMINED),
        nvars(nvars) {}

    inline lit_t clause_begin(clause_t c) const { return start[c]; }
    inline lit_t clause_end(clause_t c) const {
        return (c == start.size() - 1) ? clauses.size() : start[c + 1];
    }

    // Is the literal x currently false?
    inline bool is_false(lit_t x) const {
        State s = vals[abs(x)];
        return (x > 0 && (s == FALSE || s == FALSE_NOT_TRUE)) ||
            (x < 0 && (s == TRUE || s == TRUE_NOT_FALSE));
    }

    std::string vals_debug_string() const {
        std::ostringstream oss;
        for(std::size_t i = 1; i < vals.size(); ++i) {
            oss << vals[i];
        }
        return oss.str();
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

    Cnf cnf(static_cast<lit_t>(nvars), static_cast<clause_t>(nclauses));

    // Read clauses until EOF.
    int lit;
    do {
        bool read_lit = false;
        int start = cnf.clauses.size();
        while (true) {
            nc = fscanf(f, " %i ", &lit);
            if (nc == EOF || lit == 0) break;
            cnf.clauses.push_back(lit);
            read_lit = true;
        }
        if (!read_lit) break;
        cnf.start.push_back(start);
        clause_t old = cnf.watch[cnf.clauses[cnf.start.back()]];
        cnf.watch[cnf.clauses[cnf.start.back()]] = cnf.start.size() - 1;
        cnf.link[cnf.start.size() - 1] = old;
    } while (nc != EOF);

    fclose(f);
    return cnf;
}

// Algorithm B from 7.2.2.2 (Satisfiability by watching).
bool solve(Cnf* cnf) {
    lit_t d = 1;  // Stage; Number of variables set in the partial assignment.
    lit_t l = 0;  // Current literal.
    while (0 < d && d <= cnf->nvars) {
        LOG(1) << "vals: " << cnf->vals_debug_string();
        // Choose a literal value.
        if (cnf->vals[d] == UNEXAMINED &&
            (cnf->watch[d] == clause_nil || cnf->watch[-d] != clause_nil)) {
            cnf->vals[d] = FALSE;
        } else if (cnf->vals[d] == UNEXAMINED) {
            cnf->vals[d] = TRUE;
        } else if (cnf->vals[d] == TRUE) {
            cnf->vals[d] = FALSE_NOT_TRUE;
        } else if (cnf->vals[d] == FALSE) {
            cnf->vals[d] = TRUE_NOT_FALSE;
        } else {
            // Backtrack.
            LOG(2) << "Backtracking from stage " << d;
            cnf->vals[d] = UNEXAMINED;
            d--;
            continue;
        }

        // Set current literal value based on truth value chosen for d.
        l = ((cnf->vals[d] & 1) ? -1 : 1) * d;
        LOG(3) << "Trying " << l;

        // Update watch list entries for -l if there are any.
        clause_t watcher = cnf->watch[-l];
        while (watcher != clause_nil) {
            clause_t start = cnf->clause_begin(watcher);
            clause_t end = cnf->clause_end(watcher);
            clause_t next = cnf->link[watcher];
            clause_t k = start + 1;
            while (k < end) {
                // Search for a non-false literal to watch from clause watcher
                lit_t lit = cnf->clauses[k];
                if (cnf->is_false(lit)) {
                    k++;
                    continue;
                }
                // Found a non-false literal, swap lit and -l in clauses array.
                cnf->clauses[start] = lit;
                cnf->clauses[k] = -l;
                // Splice lit into the watch list and keep going.
                cnf->link[watcher] = cnf->watch[lit];
                cnf->watch[lit] = watcher;
                watcher = next;
                LOG(3) << "Successfully updated watch list for " << lit;
                break;
            }
            if (k == end) {
                // Failed to re-assign some literal on -l's watch list. This
                // means that some clause can't be satisfied with the partial
                // assignment created by l. We need to move on to the next
                // search step for l, which could be either trying -l or
                // backtracking.
                LOG(3) << "Couldn't update watch list for " << -l;
                break;
            }
        }
        cnf->watch[-l] = watcher;
        // Move on to the next variable if watch list reassignment succeeded.
        if (watcher == clause_nil) d++;
    }
    return d != 0;
}

int main(int argc, char** argv) {
    int oidx;
    CHECK(parse_flags(argc, argv, &oidx))
        << "Usage: " << argv[0] << " <filename>";
    Cnf c = parse(argv[oidx]);
    if (!c.start.empty() && solve(&c)) {
        std::cout << "s SATISFIABLE" << std::endl;
        for (int i = 1, j = 0; i <= c.nvars; ++i) {
            if (c.vals[i] == UNEXAMINED) continue;
            if (j % 10 == 0) std::cout << "v";
            std::cout << ((c.vals[i] & 1) ? " -" : " ") << i;
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
