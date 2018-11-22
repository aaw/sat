// Cyclic DPLL. Algorithm D from 7.2.2.2

#include <cstdio>
#include <cstdlib>
#include <sstream>
#include <vector>

#include "logging.h"
#include "types.h"

#define CLAUSE_END(cnf, c) \
    (((c) == cnf->start.size() - 1) ? cnf->clauses.size() : cnf->start[(c)+1])

struct Cnf {
    std::vector<lit_t> clauses;

    // Zero-indexed map of clauses. Clause i runs from clauses[start[i]]
    // to CLAUSE_END(inst, i).
    std::vector<clause_t> start;

    // Link to another clause with the same watched literal.
    std::vector<clause_t> link;

    // Watch lists.
    std::vector<clause_t> watch_storage;
    clause_t* watch;

    // Active ring.
    std::vector<lit_t> next;
    lit_t head;
    lit_t tail;

    lit_t nvars;
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

    Cnf cnf;
    cnf.nvars = static_cast<lit_t>(nvars);
    cnf.head = lit_nil;
    cnf.tail = lit_nil;

    LOG(4) << "Cnf has " << cnf.nvars << " variables and "
           << nclauses << " clauses.";

    // Initialize data structures now that we know nvars and nclauses.
    cnf.link.resize(nclauses, clause_nil);
    cnf.watch_storage.resize(2 * cnf.nvars + 1, clause_nil);
    cnf.watch = &cnf.watch_storage[cnf.nvars];
    cnf.next.resize(cnf.nvars + 1, lit_nil);

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

    // Initialize active ring of literals with non-empty watchlists.
    for (lit_t k = cnf.nvars; k > 0; --k) {
        if (cnf.watch[k] != clause_nil || cnf.watch[-k] != clause_nil) {
            cnf.next[k] = cnf.head;
            cnf.head = k;
            if (cnf.tail == lit_nil) {
                cnf.tail = k;
            }
        }
    }
    if (cnf.tail != 0) {
        cnf.next[cnf.tail] = cnf.head;
    }

    fclose(f);
    return cnf;
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

#define TRUTH(x) \
    ((x == UNEXAMINED) ? "U" : ((x == TRUE || x == TRUE_NOT_FALSE) ? "T" : "F"))

std::string dump_watchlist(Cnf* cnf) {
    std::ostringstream oss;
    for (lit_t l = -cnf->nvars; l <= cnf->nvars; ++l) {
        if (l == lit_nil) continue;
        clause_t x = cnf->watch[l];
        if (x != clause_nil) {
            oss << l << ": ";
            while (x != clause_nil) {
                oss << "[" << x << "] ";
                x = cnf->link[x];
            }
            oss << "\n";
        }
    }
    return oss.str();
}

bool solve(Cnf* cnf) {
    lit_t d = 1;
    lit_t l = 0;
    std::vector<State> state(cnf->nvars + 1);  // states are 1-indexed.
    LOG(5) << "Initial watchlists:\n" << dump_watchlist(cnf);
    while (0 < d && d <= cnf->nvars) {
        LOG(3) << "Starting stage " << d;
        // Choose a literal value
        if (state[d] == UNEXAMINED) {
            if (cnf->watch[d] == clause_nil || cnf->watch[-d] != clause_nil) {
                l = -d;
            } else { l = d; }
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
        if (watcher == clause_nil) {
            LOG(3) << "Nevermind, it's nil";
        }
        while (watcher != clause_nil) {
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
        if (watcher == clause_nil) d++;
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
    CHECK(argc == 2) << "Usage: " << argv[0] << " filename.cnf";
    Cnf cnf = parse(argv[1]);
    bool sat = solve(&cnf);
    LOG(3) << "Satisfiable: " << sat;
    return sat ? 0 : 1;
}
