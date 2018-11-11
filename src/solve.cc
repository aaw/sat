#include "logging.h"
#include "solve.h"

#include <limits>
#include <sstream>

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

typedef Instance::clause_t clause_t;
typedef Instance::lit_t lit_t;
clause_t nil = Instance::nil;

std::string dump_watchlist(Instance* cnf) {
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
bool solve(Instance* cnf) {
    lit_t d = 1;
    lit_t l = 0;
    std::vector<State> state(cnf->nvars + 1);  // states are 1-indexed.
    LOG(5) << "Initial watchlists:\n" << dump_watchlist(cnf);
    while (0 < d && d <= cnf->nvars) {
        LOG(3) << "Starting stage " << d;
        l = d;
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
    return d != 0;
}
