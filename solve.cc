#include "logging.h"
#include "solve.h"

enum State {
    UNEXAMINED = 0,
    FALSE = 1,
    TRUE = 2,
    FALSE_NOT_TRUE = 3,
    TRUE_NOT_FALSE = 4
};

// Algorithm B from 7.2.2.2 (Satisfiability by watching).
bool solve(Instance* cnf) {
    Instance::lit_t d = 1;
    Instance::lit_t l = 0;
    std::vector<State> state(cnf->nvars + 1);  // states are 1-indexed.
    while (0 < d && d <= cnf->nvars) {
        LOG(3) << "Starting stage " << d;
        // Choose a literal value
        if (state[d] == UNEXAMINED) {
            if (cnf->watch[d].empty() || !cnf->watch[-d].empty()) { l = -d; }
            else { l = d; }
            state[d] = (l == d) ? TRUE : FALSE;
            LOG(3) << "Choosing " << l << " but haven't tried " << -l << " yet";
        } else if (state[d] == TRUE || state[d] == FALSE) {
            l = -l;
            state[d] = (l == d) ? TRUE_NOT_FALSE : FALSE_NOT_TRUE;
            LOG(3) << "Now trying " << l << ", final try for " << d;
        } else {
            // Backtrack
            LOG(3) << "Tried all values for " << d << ", backtracking.";
            d--;
            continue;
        }
        // Update watch lists for NOT l
        bool found_new_watch = false;
        for (const Instance::clause_t& c : cnf->watch[-l]) {
            LOG(3) << "Making clause " << c << " watch something else.";
            int end = (c == cnf->start.size() - 1) ?
                cnf->clauses.size() :
                cnf->start[c+1];
            bool seen_old_watch = false;
            found_new_watch = false;
            for (int i = cnf->start[c]; i < end; ++i) {
                if (!seen_old_watch && cnf->clauses[i] != l) continue;
                if (cnf->clauses[i] == l) { seen_old_watch = true; continue; }
                LOG(3) << "Choosing " << cnf->clauses[i]
                       << " as new watchee of clause " << c;
                cnf->watch[cnf->clauses[i]].push_back(c);
                found_new_watch = true;
                break;
            }
            if (!found_new_watch) {
                LOG(3) << "Couldn't find new watch for " << c << "!";
                break;
            }
        }
        if (found_new_watch || cnf->watch[-l].empty()) {
            cnf->watch[-l].clear();
            d++;
            LOG(3) << "Successfully updated watch lists, moving to step " << d;
        }
    }
    return d != 0;
}
