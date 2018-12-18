// Cyclic DPLL. Algorithm D from 7.2.2.2

#include <cstdio>
#include <cstdlib>
#include <sstream>
#include <vector>

#include "logging.h"
#include "types.h"

// States used by both the search algorithm and the final assignment. The final
// assignment only uses UNSET, FALSE, and TRUE. The search algorithm's
// interpretation of these values is noted below.
enum State {
    UNSET = 0,
    FALSE = 1,           // Trying false, haven't tried true yet.
    TRUE = 2,            // Trying true, haven't tried false yet.
    FALSE_NOT_TRUE = 3,  // Trying false after true failed.
    TRUE_NOT_FALSE = 4,  // Trying true after false failed.
    FALSE_FORCED = 5,    // Trying false because it was forced by a unit clause.
    TRUE_FORCED = 6      // Trying true because it was forced by a unit clause.
};

// Storage for the DPLL search and the final assignment, if one exists.
struct Cnf {
    // Clauses are stored as a sequential list of literals in memory with no
    // terminator between clauses. Example: (1 or 2) and (3 or -2 or -1) would
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

    // One-indexed values of variables. Only valid if a satisfying assignment
    // has been found, in which case vals[1] through vals[nvars] will contain
    // only TRUE and FALSE values.
    std::vector<State> vals;

    // Active ring. A circular linked list that stores all of the variables v
    // that currently have a non-empty watch list for one of their literal
    // values, i.e., watch[v] != clause_nil or watch[-v] != clause_nil. Only
    // variable on the active ring can be in a unit clause. Variables on the
    // active ring with both literal values v and -v in unit clauses are used to
    // detect unsatisfiable (partial) assignment during the search. An empty
    // list has head = tail = lit_nil. A non-empty list consists of head,
    // next[head], next[next[head]], etc. until the values wrap around to head.
    std::vector<lit_t> next;
    lit_t head;
    lit_t tail;

    // Variables in the problem are 1 through nvars, inclusive.
    lit_t nvars;

    Cnf(lit_t nvars, clause_t nclauses) :
        link(nclauses, clause_nil),
        watch_storage(2 * nvars + 1, clause_nil),
        watch(&watch_storage[nvars]),
        vals(nvars + 1, UNSET),
        next(nvars + 1, lit_nil),
        head(lit_nil),
        tail(lit_nil),
        nvars(nvars) {}

    inline lit_t clause_begin(clause_t c) const { return start[c]; }
    inline lit_t clause_end(clause_t c) const {
        return (c == start.size() - 1) ? clauses.size() : start[c + 1];
    }

    // Is the literal x currently set false?
    bool is_false(lit_t x) const {
        State s = vals[abs(x)];
        return (x > 0 && s == FALSE) || (x < 0 && s == TRUE);
    }

    // Is the literal x currently in a unit clause?
    bool is_unit(lit_t x) const {
        for (clause_t w = watch[x]; w != clause_nil; w = link[w]) {
            lit_t itr = clause_begin(w) + 1;
            lit_t end = clause_end(w);
            for (; itr != end; ++itr) {
                lit_t lit = clauses[itr];
                if (!is_false(lit)) break;
            }
            if (itr == end) return true;
        }
        return false;
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
    Cnf cnf(static_cast<lit_t>(nvars),
            static_cast<clause_t>(nclauses));

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
            if (cnf.tail == lit_nil) cnf.tail = k;
        }
    }
    if (cnf.tail != lit_nil) cnf.next[cnf.tail] = cnf.head;

    fclose(f);
    return cnf;
}

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
        if (x[i] == TRUE) oss << "T1]";
        if (x[i] == FALSE) oss << "F1]";
        if (x[i] == TRUE_NOT_FALSE) oss << "T2]";
        if (x[i] == FALSE_NOT_TRUE) oss << "F2]";
        if (x[i] == TRUE_FORCED) oss << "T!]";
        if (x[i] == FALSE_FORCED) oss << "F!]";
        if (x[i] == UNSET) oss << "--]";
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
    for (clause_t i = 0; i < cnf->start.size(); ++i) {
        lit_t end = cnf->clause_end(i);
        oss << "(";
        for (lit_t itr = cnf->clause_begin(i); itr != end; ++itr) {
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

// TODO: is state[0] ever used? why does Knuth include directions for
// "an array m_0,m_1, ... m_n" of moves in summary of Algorithm D and
// start d at 0, only to update d+1 in the algorithm?

bool solve(Cnf* c) {
    lit_t d = 0;
    std::vector<State> state(c->nvars + 1, UNSET);  // states are 1-indexed.
    std::vector<lit_t> heads(c->nvars + 1, lit_nil);
    LOG(3) << "Clauses:\n" << dump_clauses(c);
    LOG(5) << "Initial watchlists:\n" << dump_watchlist(c);
    while (c->tail != lit_nil) {
        LOG(4) << "State: " << dump_assignment(c->vals);
        LOG(4) << "moves: " << dump_moves(state);
        lit_t k = c->tail;
        // Did we find a unit clause in the active ring?
        bool found_unit = false;
        // Did we find that x and -x were unit clauses, in which case we were
        // force to backtrack?
        bool backtrack = false;
        do {
            c->head = c->next[k];
            bool pos_unit = c->is_unit(c->head);
            bool neg_unit = c->is_unit(-c->head);
            LOG(3) << c->head << " a unit? " << pos_unit << ". "
                   << -c->head << " a unit? " << neg_unit;

            found_unit = pos_unit || neg_unit;
            backtrack = pos_unit && neg_unit;

            if (backtrack) {
                LOG(3) << "Backtracking from " << d;
                LOG(4) << "moves: " << dump_moves(state);
                c->tail = k;
                while (state[d] != UNSET && state[d] != FALSE &&
                       state[d] != TRUE  && d > 0) {
                    LOG(3) << "Need to back up from " << d
                           << " since we've either been forced or already "
                           << "tried both true and false";
                    k = heads[d];
                    c->vals[k] = UNSET;
                    if (c->watch[k] != clause_nil ||
                        c->watch[-k] != clause_nil) {
                        LOG(3) << "Removing " << k << " from the active ring";
                        c->next[k] = c->head;
                        c->head = k;
                        c->next[c->tail] = c->head;
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
                c->tail = k;
                break;
            } else if (neg_unit) {
                LOG(3) << "Found a neg unit clause";
                state[d+1] = FALSE_FORCED;
                c->tail = k;
                break;
            } else {
                // Keep looking for unit clauses in the active ring.
                k = c->head;
            }
        } while (c->head != c->tail);

        if (!found_unit) {
            LOG(3) << "Couldn't find a unit clause, resorting to branching";
            c->head = c->next[c->tail];
            if (c->watch[c->head] == clause_nil ||
                c->watch[-c->head] != clause_nil) {
                state[d+1] = TRUE;
            } else {
                state[d+1] = FALSE;
            }
        }

        // Step D5
        if (!backtrack) {
            ++d;
            k = c->head;
            heads[d] = k;
            if (c->tail == k) {
                // TODO: why do this here instead of just break?
                c->tail = lit_nil;
            } else {
                LOG(3) << "Deleting " << k << " from the active ring";
                c->head = c->next[k];
                c->next[c->tail] = c->head;
            }
        }

        // Step D6
        lit_t l;
        if (state[d] == TRUE || state[d] == TRUE_NOT_FALSE ||
            state[d] == TRUE_FORCED) {
            LOG(3) << "Setting " << k << " true";
            c->vals[k] = TRUE;
            l = -k;
        } else {
            LOG(3) << "Setting " << k << " false";
            c->vals[k] = FALSE;
            l = k;
        }
        // Clear l's watchlist
        LOG(3) << "Clearing " << l << "'s watchlist";
        clause_t j = c->watch[l];
        c->watch[l] = clause_nil;
        while (j != clause_nil) {
            clause_t i = c->start[j];
            clause_t p = i + 1;
            while (c->is_false(c->clauses[p])) { ++p; }
            LOG(3) << "Swapping " << l << " with " << c->clauses[p]
                   << " so " << c->clauses[p] << " is watched in clause "
                   << j;
            lit_t lp = c->clauses[p]; // TODO: replace these lines with swap?
            c->clauses[p] = l;
            c->clauses[i] = lp;
            if (c->watch[lp] == clause_nil && c->watch[-lp] == clause_nil &&
                c->vals[abs(lp)] == UNSET) {
                LOG(3) << lp << " has become active now that it's watched. "
                       << "Adding it to the active ring.";
                if (c->tail == lit_nil) {
                    c->head = abs(lp);
                    c->tail = c->head;
                    c->next[c->tail] = c->head;
                } else {
                    c->next[abs(lp)] = c->head;
                    c->head = abs(lp);
                    c->next[c->tail] = c->head;
                }
            }
            clause_t jp = c->link[j];
            c->link[j] = c->watch[lp];
            c->watch[lp] = j;
            j = jp;
        }
        LOG(3) << "Updated watchlists:\n" << dump_watchlist(c);
        LOG(3) << "Active ring: " << dump_active_ring(c);
    }
    LOG(3) << dump_clauses(c);
    LOG(3) << dump_assignment(c->vals);
    return true;
}

int main(int argc, char** argv) {
    CHECK(argc == 2) << "Usage: " << argv[0] << " <filename>";
    Cnf c = parse(argv[1]);
    bool sat = solve(&c);
    LOG(3) << "Satisfiable: " << sat;
    return sat ? 0 : 1;
}
