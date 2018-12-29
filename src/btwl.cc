// Algorithm B from 7.2.2.2: Backtracking with a watchlist.

#include <cstdio>
#include <cstdlib>
#include <sstream>
#include <vector>

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
    std::vector<lit_t> clauses;

    // Zero-indexed map of clauses. Clause i runs from clauses[start[i]]
    // to CLAUSE_END(inst, i).
    std::vector<clause_t> start;

    // Link to another clause with the same watched literal.
    std::vector<clause_t> link;

    // Watch lists.
    std::vector<clause_t> watch_storage;
    clause_t* watch;

    // Variable values.
    std::vector<State> vals;

    // Number of variables in the problem. Valid variables range from 1 to
    // nvars, inclusive.
    lit_t nvars;

    Cnf(lit_t nvars, clause_t nclauses) :
        link(nclauses, clause_nil),
        watch_storage(2 * nvars + 1, clause_nil),
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

std::string dump_watchlist(Cnf* cnf) {
    std::ostringstream oss;
    for (lit_t l = -cnf->nvars; l <= cnf->nvars; ++l) {
        if (l == 0) continue;
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

// Algorithm B from 7.2.2.2 (Satisfiability by watching).
bool solve(Cnf* cnf) {
    lit_t d = 1;  // Number of variables set in the partial assignment.
    lit_t l = 0;  // Current literal.
    LOG(5) << "Initial watchlists:\n" << dump_watchlist(cnf);
    while (0 < d && d <= cnf->nvars) {
        LOG(3) << "Starting stage " << d;
        // Choose a literal value
        if (cnf->vals[d] == UNEXAMINED) {
            if (cnf->watch[d] == clause_nil || cnf->watch[-d] != clause_nil) {
                l = -d;
            } else { l = d; }
            cnf->vals[d] = (l == d) ? TRUE : FALSE;
            LOG(3) << "Choosing " << l << " but haven't tried " << -l << " yet";
        } else if (cnf->vals[d] == TRUE) {
            cnf->vals[d] = FALSE_NOT_TRUE;
            l = -d;
            LOG(3) << "Trying " << l << " after " << -l << " has failed.";
        } else if (cnf->vals[d] == FALSE) {
            cnf->vals[d] = TRUE_NOT_FALSE;
            l = d;
            LOG(3) << "Trying " << l << " after " << -l << " has failed.";
        } else {
            // Backtrack
            LOG(3) << "Tried all values for " << d << ", backtracking.";
            cnf->vals[d] = UNEXAMINED;
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
            clause_t start = cnf->clause_begin(watcher);
            clause_t end = cnf->clause_end(watcher);
            clause_t next = cnf->link[watcher];
            clause_t k = start + 1;
            LOG(3) << "start = " << start << ", end = " << end
                   << ", next = " << next << ", k = " << k;
            while (k < end) {
                lit_t lit = cnf->clauses[k];
                if (cnf->is_false(lit)) {
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
    return d != 0;
}

int main(int argc, char** argv) {
    CHECK(argc == 2) << "Usage: " << argv[0] << " <filename>";
    Cnf c = parse(argv[1]);
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
