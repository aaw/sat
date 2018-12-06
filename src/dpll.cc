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
    std::vector<clause_t> start;  // use size_t instead of clause_t here

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

    // Initialize data structures now that we know nvars and nclauses.
    Cnf cnf;
    cnf.nvars = static_cast<lit_t>(nvars);
    cnf.head = lit_nil;
    cnf.tail = lit_nil;
    cnf.link.resize(nclauses, clause_nil);
    cnf.watch_storage.resize(2 * cnf.nvars + 1, clause_nil);
    cnf.watch = &cnf.watch_storage[cnf.nvars];
    cnf.next.resize(cnf.nvars + 1, lit_nil);

    LOG(4) << "Cnf has " << cnf.nvars << " variables and "
           << nclauses << " clauses.";

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
    if (cnf.tail != lit_nil) {
        cnf.next[cnf.tail] = cnf.head;
    }

    fclose(f);
    return cnf;
}

enum State {
    UNSET = 0,
    FALSE = 1,
    TRUE = 2,
    FALSE_NOT_TRUE = 3,
    TRUE_NOT_FALSE = 4,
    FALSE_FORCED = 5,
    TRUE_FORCED = 6
};

#define IS_FALSE(val, state) \
    ((val > 0 && state == FALSE) || (val < 0 && state == TRUE))

#define TRUTH(x) \
    ((x == UNEXAMINED) ? \
      "U" : \
      ((x == TRUE || x == TRUE_NOT_FALSE || x == TRUE_FORCED) ? "T" : "F"))

std::string dump_assignment(const std::vector<State>& x) {
    std::ostringstream oss;
    for (unsigned int i = 1; i < x.size(); ++i) {
        oss << "[" << i << ":";
        if (x[i] == TRUE) oss << "T]";
        if (x[i] == FALSE) oss << "F]";
        if (x[i] == UNSET) oss << "-]";
    }
    return oss.str();
}

std::string dump_moves(const std::vector<State>& x) {
    std::ostringstream oss;
    for (unsigned int i = 1; i < x.size(); ++i) {
        oss << "[" << i << ":";
        if (x[i] == TRUE) oss << "T__]";
        if (x[i] == FALSE) oss << "F__]";
        if (x[i] == TRUE_NOT_FALSE) oss << "TNF]";
        if (x[i] == FALSE_NOT_TRUE) oss << "FNT]";
        if (x[i] == TRUE_FORCED) oss << "T_U]";
        if (x[i] == FALSE_FORCED) oss << "F_U]";
        if (x[i] == UNSET) oss << "---]";
    }
    return oss.str();
}

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

std::string dump_clauses(const Cnf* cnf) {
    std::ostringstream oss;
    for (unsigned int i = 0; i < cnf->start.size(); ++i) {
        int end = CLAUSE_END(cnf, i);
        oss << "(";
        for (int itr = cnf->start[i]; itr != end; ++itr) {
            oss << cnf->clauses[itr] << " ";
        }
        oss << ")  ";
    }
    return oss.str();
}

std::string dump_active_ring(const Cnf* cnf) {
    std::ostringstream oss;
    lit_t l = cnf->head;
    do {
        oss << "[" << l << "]";
        l = cnf->next[l];
    } while (l != cnf->head);
    return oss.str();
}

bool is_unit(const Cnf* cnf, const std::vector<State>& vals, lit_t x) {
    for (clause_t w = cnf->watch[x]; w != clause_nil; w = cnf->link[w]) {
        clause_t itr = cnf->start[w] + 1;
        clause_t end = CLAUSE_END(cnf, w);
        for (; itr != end; ++itr) {
            lit_t lit = cnf->clauses[itr];
            if (!IS_FALSE(lit, vals[abs(lit)])) {
                break;
            }
        }
        if (itr == end) return true;
    }
    return false;
}

// TODO: is state[0] ever used? why does Knuth include directions for
// "an array m_0,m_1, ... m_n" of moves in summary of Algorithm D and
// start d at 0, only to update d+1 in the algorithm?

bool solve(Cnf* cnf) {
    lit_t d = 0;
    std::vector<State> state(cnf->nvars + 1, UNSET);  // states are 1-indexed.
    std::vector<lit_t> heads(cnf->nvars + 1, lit_nil);
    std::vector<State> vals(cnf->nvars + 1, UNSET);
    LOG(3) << "Clauses:\n" << dump_clauses(cnf);
    LOG(5) << "Initial watchlists:\n" << dump_watchlist(cnf);
    while (cnf->tail != lit_nil) {
        LOG(4) << "State: " << dump_assignment(vals);
        LOG(4) << "moves: " << dump_moves(state);
        lit_t k = cnf->tail;
        bool found_unit = false;
        bool backtracked = false;
        do {
            cnf->head = cnf->next[k];
            bool pos_unit = is_unit(cnf, vals, cnf->head);
            bool neg_unit = is_unit(cnf, vals, -cnf->head);
            LOG(3) << cnf->head << " a unit? " << pos_unit << ". "
                   << -cnf->head << " a unit? " << neg_unit;

            found_unit = pos_unit || neg_unit;

            if (pos_unit && neg_unit) {
                LOG(3) << "Backtracking from " << d;
                LOG(4) << "moves: " << dump_moves(state);

                backtracked = true;
                cnf->tail = k;
                while (state[d] != UNSET && state[d] != FALSE &&
                       state[d] != TRUE  && d > 0) {
                    LOG(3) << "Need to back up from " << d
                           << " since we've either been forced or already "
                           << "tried both true and false";
                    k = heads[d];
                    vals[k] = UNSET;
                    if (cnf->watch[k] != clause_nil ||
                        cnf->watch[-k] != clause_nil) {
                        LOG(3) << "Removing " << k << " from the active ring";
                        cnf->next[k] = cnf->head;
                        cnf->head = k;
                        cnf->next[cnf->tail] = cnf->head;
                    }
                    --d;
                }

                if (d <= 0) return false;
                k = heads[d];
                if (state[d] == TRUE) state[d] = FALSE_NOT_TRUE;
                else if (state[d] == FALSE) state[d] = TRUE_NOT_FALSE;
                LOG(4) << "new moves: " << dump_moves(state);
                break;
            } else if (pos_unit) {
                LOG(3) << "Found a pos unit clause";
                state[d+1] = TRUE_FORCED;
                cnf->tail = k;
                break;
            } else if (neg_unit) {
                LOG(3) << "Found a neg unit clause";
                state[d+1] = FALSE_FORCED;
                cnf->tail = k;
                break;
            } else {
                // Keep looking for unit clauses in the active ring.
                k = cnf->head;
            }
        } while (cnf->head != cnf->tail);

        if (!found_unit) {
            LOG(3) << "Couldn't find a unit clause, resorting to branching";
            cnf->head = cnf->next[cnf->tail];
            if (cnf->watch[cnf->head] == clause_nil ||
                cnf->watch[-cnf->head] != clause_nil) {
                state[d+1] = TRUE;
            } else {
                state[d+1] = FALSE;
            }
        }

        // Step D5
        if (!backtracked) {
            ++d;
            k = cnf->head; // TODO: redundant?
            heads[d] = k;
            if (cnf->tail == k) {
                // TODO: why do this here instead of just break?
                cnf->tail = lit_nil;
            } else {
                LOG(3) << "Deleting " << k << " from the active ring";
                cnf->head = cnf->next[k];
                cnf->next[cnf->tail] = cnf->head;
            }
        }

        // Step D6
        lit_t l;
        if (state[d] == TRUE || state[d] == TRUE_NOT_FALSE ||
            state[d] == TRUE_FORCED) {
            LOG(3) << "Setting " << k << " true";
            vals[k] = TRUE;
            l = -k;
        } else {
            LOG(3) << "Setting " << k << " false";
            vals[k] = FALSE;
            l = k;
        }
        // Clear l's watchlist
        LOG(3) << "Clearing " << l << "'s watchlist";
        clause_t j = cnf->watch[l];
        cnf->watch[l] = clause_nil;
        while (j != clause_nil) {
            clause_t i = cnf->start[j];
            clause_t p = i + 1;
            while (IS_FALSE(cnf->clauses[p], vals[abs(cnf->clauses[p])])) {
                ++p;
            }
            LOG(3) << "Swapping " << l << " with " << cnf->clauses[p]
                   << " so " << cnf->clauses[p] << " is watched in clause "
                   << j;
            lit_t lp = cnf->clauses[p]; // TODO: replace these lines with swap?
            cnf->clauses[p] = l;
            cnf->clauses[i] = lp;
            if (cnf->watch[lp] == clause_nil && cnf->watch[-lp] == clause_nil &&
                vals[abs(lp)] == UNSET) {
                LOG(3) << lp << " has become active now that it's watched. "
                       << "Adding it to the active ring.";
                if (cnf->tail == lit_nil) {
                    cnf->head = abs(lp);
                    cnf->tail = cnf->head;
                    cnf->next[cnf->tail] = cnf->head;
                } else {
                    cnf->next[abs(lp)] = cnf->head;
                    cnf->head = abs(lp);
                    cnf->next[cnf->tail] = cnf->head;
                }
            }
            clause_t jp = cnf->link[j];
            cnf->link[j] = cnf->watch[lp];
            cnf->watch[lp] = j;
            j = jp;
        }
        LOG(3) << "Updated watchlists:\n" << dump_watchlist(cnf);
        LOG(3) << "Active ring: " << dump_active_ring(cnf);
    }
    LOG(3) << dump_clauses(cnf);
    LOG(3) << dump_assignment(vals);
    return true;
}

int main(int argc, char** argv) {
    CHECK(argc == 2) << "Usage: " << argv[0] << " <filename>";
    Cnf cnf = parse(argv[1]);
    bool sat = solve(&cnf);
    LOG(3) << "Satisfiable: " << sat;
    return sat ? 0 : 1;
}
