#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <limits>
#include <sstream>
#include <vector>

#include "logging.h"

// TODO: templatize this with lit_t, clause_t
template <typename lit_t, typename clause_t>
struct Instance {
    std::vector<lit_t> clauses;
    // Zero-indexed map of clauses. Clause i runs from clauses[start[i]]
    // to clauses[start[i+1]-1] (or clauses[clauses.size()-1]
    // if i == start.size() - 1).
    std::vector<clause_t> start;

    // Link to another clause with the same watched literal.
    std::vector<clause_t> link;
    std::vector<clause_t> watch_storage;
    clause_t* watch;
    clause_t nclauses;
    lit_t nvars;

    static const clause_t nil;
};

template <typename lit_t, typename clause_t>
clause_t const Instance<lit_t, clause_t>::nil =
    std::numeric_limits<clause_t>::max();

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
template<typename lit_t, typename clause_t>
bool parse(const char* filename, Instance<lit_t, clause_t>* cnf) {
    int nc;
    FILE* f = fopen(filename, "r");
    if (!f) {
        LOG(2) << "Failed to open file: " << filename;
        return false;
    }

    // Read comment lines until we see the problem line.
    do {
        nc = fscanf(f, " p cnf %i %i \n", &cnf->nvars, &cnf->nclauses);
        if (nc > 0 && nc != EOF) break;
        nc = fscanf(f, "%*s\n");
    } while (nc != 2 && nc != EOF);

    LOG(4) << "Problem has " << cnf->nvars << " variables and "
           << cnf->nclauses << " clauses.";

    // Initialize data structures now that we know nvars and nclauses.
    cnf->link.resize(cnf->nclauses, Instance<lit_t,clause_t>::nil);
    cnf->watch_storage.resize(2 * cnf->nvars + 1, Instance<lit_t,clause_t>::nil);
    cnf->watch = &cnf->watch_storage[cnf->nvars];

    // Read clauses until EOF.
    int lit;
    do {
        bool read_lit = false;
        int start = cnf->clauses.size();
        while (true) {
            nc = fscanf(f, " %i ", &lit);
            if (nc == EOF || lit == 0) break;
            cnf->clauses.push_back(lit);
            read_lit = true;
        }
        if (!read_lit) break;
        cnf->start.push_back(start);
        clause_t old = cnf->watch[cnf->clauses[cnf->start.back()]];
        cnf->watch[cnf->clauses[cnf->start.back()]] = cnf->start.size() - 1;
        cnf->link[cnf->start.size() - 1] = old;
    } while (nc != EOF);

    fclose(f);
    return true;
}

enum State {
    UNEXAMINED = 0,
    FALSE = 1,
    TRUE = 2,
    FALSE_NOT_TRUE = 3,
    TRUE_NOT_FALSE = 4
};

#define IS_FALSE(val, state) \
    ((val > 0 && (state == FALSE || state == FALSE_NOT_TRUE)) || \
     (val < 0 && (state == TRUE || state == TRUE_NOT_FALSE)))

#define CLAUSE_END(cnf, c) \
    ((c == cnf->start.size() - 1) ? cnf->clauses.size() : cnf->start[c+1])

#define TRUTH(x) \
    ((x == UNEXAMINED) ? "U" : ((x == TRUE || x == TRUE_NOT_FALSE) ? "T" : "F"))

template <typename lit_t, typename clause_t>
std::string dump_watchlist(Instance<lit_t, clause_t>* cnf) {
    clause_t nil = Instance<lit_t, clause_t>::nil;
    std::ostringstream oss;
    for (lit_t l = -cnf->nvars; l <= cnf->nvars; ++l) {
        if (l == 0) continue;
        clause_t x = cnf->watch[l];
        if (x != nil) {
            oss << l << ": ";
            while (x != nil) {
                oss << "[" << x << "] ";
                x = cnf->link[x];
            }
            oss << "\n";
        }
    }
    return oss.str();
}

// Algorithm B from 7.2.2.2 (Satisfiability by watching).
template <typename lit_t, typename clause_t>
bool solve(Instance<lit_t, clause_t>* cnf) {
    clause_t nil = Instance<lit_t, clause_t>::nil;
    lit_t d = 1;
    lit_t l = 0;
    std::vector<State> state(cnf->nvars + 1);  // states are 1-indexed.
    LOG(5) << "Initial watchlists:\n" << dump_watchlist(cnf);
    while (0 < d && d <= cnf->nvars) {
        LOG(3) << "Starting stage " << d;
        // Choose a literal value
        if (state[d] == UNEXAMINED) {
            if (cnf->watch[d] == nil || cnf->watch[-d] != nil) { l = -d; }
            else { l = d; }
            state[d] = (l == d) ? TRUE : FALSE;
            LOG(3) << "Choosing " << l << " but haven't tried " << -l << " yet";
        } else if (state[d] == TRUE) {
            state[d] = FALSE_NOT_TRUE;
            l = -d;
            LOG(3) << "Trying " << l << " after " << -l << " has failed.";
        } else if (state[d] == FALSE) {
            state[d] = TRUE_NOT_FALSE;
            l = d;
            LOG(3) << "Trying " << l << " after " << -l << " has failed.";
        } else {
            // Backtrack
            LOG(3) << "Tried all values for " << d << ", backtracking.";
            state[d] = UNEXAMINED;
            d--;
            continue;
        }
        // Update watch lists for NOT l
        LOG(3) << "Attempting to re-assign " << -l << "'s watchlist";
        clause_t watcher = cnf->watch[-l];
        if (watcher == nil) {
            LOG(3) << "Nevermind, it's nil";
        }
        while (watcher != nil) {
            clause_t start = cnf->start[watcher];
            clause_t end = CLAUSE_END(cnf, watcher);
            clause_t next = cnf->link[watcher];
            clause_t k = start + 1;
            LOG(3) << "start = " << start << ", end = " << end
                   << ", next = " << next << ", k = " << k;
            while (k < end) {
                lit_t lit = cnf->clauses[k];
                if (IS_FALSE(lit, state[abs(lit)])) {
                    LOG(3) << lit << " is false, continuing to k = " << k + 1;
                    k++;
                    continue;
                }
                LOG(3) << lit << " is not false, re-assigning watchlist. "
                       << "first swapping " << lit << " and " << -l;
                cnf->clauses[start] = lit;
                cnf->clauses[k] = -l;
                cnf->link[watcher] = cnf->watch[lit];
                cnf->watch[lit] = watcher;
                watcher = next;
                break;
            }
            if (k == end) {
                LOG(3) << "Failed to re-assign " << -l << "'s watchlist. "
                       << "Going to try " << l << " = false next.";
                break;
            }
            LOG(3) << "Succeeded in re-assigning " << -l << "'s watchlist.";
        }
        cnf->watch[-l] = watcher;
        if (watcher == nil) d++;
        LOG(5) << "Watchlists:\n" << dump_watchlist(cnf);
    }
    if (d != 0) {
        std::ostringstream oss;
        for (unsigned int i = 1; i < state.size(); i++) {
            oss << "[" << i << ":" << TRUTH(state[i]) << "]";
        }
        LOG(3) << "Final assignment: " << oss.str();
    }
    return d != 0;
}

int main(int argc, char** argv) {
    Instance<int, unsigned int> cnf;
    if (!parse(argv[1], &cnf)) {
        LOG(1) << "Error parsing .cnf file.";
        return -1;
    }
    bool sat = solve(&cnf);
    LOG(3) << "Satisfiable: " << sat;
    return sat ? 0 : 1;
}
