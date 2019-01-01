// Cyclic DPLL. Algorithm D from 7.2.2.2
//
// Significant differences:
// - No gotos
// - Dimacs format
// - watchlists indexed by negatives
// - no attempt to optimize bit-level ops
// - No separate moves + xs arrays
//
// TODO: make output consistent with SAT output
// TODO: remove debug logging

#include <cstdio>
#include <cstdlib>
#include <sstream>
#include <vector>

#include "flags.h"
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

    // One-indexed values of variables in the satisfying assignment.
    std::vector<State> vals;

    // Number of variables in the problem. Valid variables range from 1 to
    // nvars, inclusive.
    lit_t nvars;

    Cnf(lit_t nvars, clause_t nclauses) :
        watch_storage(2 * nvars + 1, clause_nil),
        link(nclauses, clause_nil),
        watch(&watch_storage[nvars]),
        next(nvars + 1, lit_nil),
        head(lit_nil),
        tail(lit_nil),
        vals(nvars + 1, UNSET),
        nvars(nvars) {}

    inline lit_t clause_begin(clause_t c) const { return start[c]; }
    inline lit_t clause_end(clause_t c) const {
        return (c == start.size() - 1) ? clauses.size() : start[c + 1];
    }

    // Is the literal x watched by any clause?
    inline bool watched(lit_t x) const {
        return watch[x] != clause_nil;
    }

    // Is the literal x currently false?
    inline bool is_false(lit_t x) const {
        State s = vals[abs(x)];
        return (x > 0 && s & 1) || (x < 0 && s > 0 && !(s & 1));
    }

    // Is the variable v currently set to a forced value, either because of a
    // unit clause or because we've already tried setting it to the other value
    // and failed?
    inline bool is_forced(lit_t v) const {
        return vals[v] > 2;
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

    std::string vals_debug_string() const {
        std::ostringstream oss;
        for(std::size_t i = 1; i < vals.size(); ++i) { oss << vals[i]; }
        return oss.str();
    }

    std::string clauses_debug_string() const {
        std::ostringstream oss;
        for (clause_t i = 0; i < start.size(); ++i) {
            lit_t end = clause_end(i);
            oss << "(";
            for (lit_t itr = clause_begin(i); itr != end; ++itr) {
                oss << clauses[itr];
                if (itr + 1 != end) oss << " ";
            }
            oss << ") ";
        }
        return oss.str();
    }

    std::string active_ring_debug_string() const {
        std::ostringstream oss;
        lit_t l = head;
        do { oss << "[" << l << "]"; l = next[l]; } while (l != head);
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

    // Initialize data structures now that we know nvars and nclauses.
    Cnf cnf(static_cast<lit_t>(nvars),
            static_cast<clause_t>(nclauses));

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

    // Initialize active ring of literals with non-empty watch lists.
    for (lit_t k = cnf.nvars; k > 0; --k) {
        if (cnf.watched(k) || cnf.watched(-k)) {
            cnf.next[k] = cnf.head;
            cnf.head = k;
            if (cnf.tail == lit_nil) cnf.tail = k;
        }
    }
    if (cnf.tail != lit_nil) cnf.next[cnf.tail] = cnf.head;

    fclose(f);
    return cnf;
}

// Returns true exactly when a satisfying assignment exists for c.
bool solve(Cnf* c) {
    // The search for a satisfying assignment proceeds in stages from d = 1 to
    // d = c->nvars. As long as a consistent partial assignment is found, d
    // is incremented. If a conflict is found, we backtrack by decrementing d.
    // heads is a 1-indexed current (partial) permutation of explored variables.
    lit_t d = 0;
    std::vector<lit_t> heads(c->nvars + 1, lit_nil);

    // As long as some literal has a non-empty watch list, continue searching
    // for a satisfying assignment.
    while (c->tail != lit_nil) {
        LOG(1) << "vals: " << c->vals_debug_string();
        LOG(3) << "clauses: " << c->clauses_debug_string();
        LOG(4) << "active ring: " << c->active_ring_debug_string();
        lit_t k = c->tail;  // Current variable being considered.
        bool pos_unit = false;  // Found a positive literal in a unit clause?
        bool neg_unit = false;  // Found a negative literal in a unit clause?

        // Iterate over the active ring looking for a literal in a unit clause.
        do {
            c->head = c->next[k];
            pos_unit = c->is_unit(c->head);
            neg_unit = c->is_unit(-c->head);

            if (pos_unit && neg_unit) {
                LOG(2) << "Backtracking from " << d;
                c->tail = k;
                while (d > 0 && c->is_forced(heads[d])) {
                    k = heads[d];
                    c->vals[k] = UNSET;
                    // If variable k was active, remove it from the active ring.
                    if (c->watched(k) || c->watched(-k)) {
                        c->next[k] = c->head;
                        c->head = k;
                        c->next[c->tail] = c->head;
                    }
                    --d;
                }

                if (d <= 0) return false;
                k = heads[d];
                if (c->vals[k] == TRUE) c->vals[k] = FALSE_NOT_TRUE;
                else if (c->vals[k] == FALSE) c->vals[k] = TRUE_NOT_FALSE;
                break;
            } else if (pos_unit) {
                c->vals[c->head] = TRUE_FORCED;
                c->tail = k;
                break;
            } else if (neg_unit) {
                c->vals[c->head] = FALSE_FORCED;
                c->tail = k;
                break;
            } else {
                // Keep looking for unit clauses in the active ring.
                k = c->head;
            }
        } while (c->head != c->tail);

        // If we couldn't find a unit clause, we may as well try setting the
        // first variable on the active ring. We guess TRUE/FALSE based on the
        // state of the watch list.
        if (!pos_unit && !neg_unit) {
            LOG(2) << "Couldn't find a unit clause, resorting to branching";
            c->head = c->next[c->tail];
            if (!c->watched(c->head) || c->watched(-c->head)) {
                c->vals[c->head] = TRUE;
            } else {
                c->vals[c->head] = FALSE;
            }
        }

        // Step D5
        // (if !backtrack) == !pos_unit || !neg_unit
        if (!pos_unit || !neg_unit) {
            ++d;
            k = c->head;
            heads[d] = k;
            if (c->tail == k) {
                // TODO: why do this here instead of just break?
                c->tail = lit_nil;
            } else {
                LOG(2) << "Deleting " << k << " from the active ring";
                c->head = c->next[k];
                c->next[c->tail] = c->head;
            }
        }

        // Step D6: TODO: explain why l is set like it is...
        // Clear l's watch list, iterate through all clauses that used to watch
        // l and make them watch some other literal.
        lit_t l = c->vals[k] & 1 ? k : -k;
        clause_t j = c->watch[l];
        c->watch[l] = clause_nil;
        while (j != clause_nil) {
            // Find the first literal in clause j that isn't false, swap it to
            // the front of clause j so that it's now watched by clause j.
            clause_t i = c->start[j];
            clause_t p = i + 1;
            while (c->is_false(c->clauses[p])) { ++p; }
            lit_t lp = c->clauses[p];
            c->clauses[p] = l;
            c->clauses[i] = lp;

            // If setting lp as the watched literal for clause j causes lp to
            // become active, add lp to the active ring.
            if (!c->watched(lp) && !c->watched(-lp) &&
                c->vals[abs(lp)] == UNSET) {
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

            // Add lp to j's watch list, move on by setting j to the next clause
            // that was originally watched by l and repeat the loop.
            clause_t jp = c->link[j];
            c->link[j] = c->watch[lp];
            c->watch[lp] = j;
            j = jp;
        }
    }
    return true;
}

int main(int argc, char** argv) {
    int oidx;
    CHECK(parse_flags(argc, argv, &oidx)) <<
        "Usage: " << argv[0] << " <filename>";
    Cnf c = parse(argv[oidx]);
    if (!c.start.empty() && solve(&c)) {
        std::cout << "s SATISFIABLE" << std::endl;
        for (int i = 1, j = 0; i <= c.nvars; ++i) {
            if (c.vals[i] == UNSET) continue;
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
