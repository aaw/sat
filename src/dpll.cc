// Algorithm D from Knuth's The Art of Computer Programming 7.2.2.2: DPLL.

#include <sstream>
#include <vector>

#include "counters.h"
#include "flags.h"
#include "logging.h"
#include "timer.h"
#include "types.h"
#include "process.h"

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
    Processor* p;

    // Number of variables in the formula. Valid variables range from 1 to
    // nvars, inclusive.
    lit_t nvars;

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
    std::vector<State> val;

    // One-indexed current (partial) permutation of explored variables.
    std::vector<lit_t> heads;

    Cnf(Processor* p) :
        p(p),
        nvars(p->nvars()),
        watch_storage(2 * nvars + 1, clause_nil),
        link(p->nclauses(), clause_nil),
        watch(&watch_storage[nvars]),
        next(nvars + 1, lit_nil),
        head(lit_nil),
        tail(lit_nil),
        val(nvars + 1, UNSET),
        heads(nvars + 1, lit_nil) {}

    // These two methods give the begin/end index of the kth clause in the
    // clauses vector. Used for iterating over all literals in the kth clause.
    inline clause_t clause_begin(clause_t k) const { return start[k]; }
    inline clause_t clause_end(clause_t k) const {
        return (k == start.size() - 1) ? clauses.size() : start[k + 1];
    }

    // Is the literal x watched by any clause?
    inline bool watched(lit_t x) const {
        return watch[x] != clause_nil;
    }

    // Is the literal x currently false?
    inline bool is_false(lit_t x) const {
        State s = val[var(x)];
        return (x > 0 && s & 1) || (x < 0 && s > 0 && !(s & 1));
    }

    // Is there any freedom to set the variable we chose at stage d to some
    // other value? The only way this is possible is if that variable hasn't
    // been explored yet or only true/false has been tried and the other value
    // hasn't yet been considered.
    inline bool freedom_at_stage(lit_t d) const {
        return val[heads[d]] <= 2;
    }

    // Is the literal x currently in a unit clause?
    bool is_unit(lit_t x) const {
        for (clause_t w = watch[x]; w != clause_nil; w = link[w]) {
            clause_t itr = clause_begin(w) + 1;
            clause_t end = clause_end(w);
            for (; itr != end; ++itr) {
                if (!is_false(clauses[itr])) break;
            }
            if (itr == end) return true;
        }
        return false;
    }

    std::string val_debug_string() const {
        std::ostringstream oss;
        for(std::size_t i = 1; i < val.size(); ++i) { oss << val[i]; }
        return oss.str();
    }

    std::string clauses_debug_string() const {
        std::ostringstream oss;
        for (clause_t i = 0; i < start.size(); ++i) {
            clause_t end = clause_end(i);
            oss << "(";
            for (clause_t itr = clause_begin(i); itr != end; ++itr) {
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

    void print_assignment() {
        p->val.resize(nvars + 1, false);  // In case preprocessing is disabled.
        for (int i = 1; i <= nvars; ++i) {
            if (val[i] == UNSET) { p->val[i] = FALSE; }
            else { p->val[i] = !(val[i] & 1); }
        }
        p->apply_rules();
        p->print_assignment();
    }
};

Cnf parse(Processor* p) {
    p->reset();
    Cnf c(p);
    while (!p->eof()) {
        std::size_t start = c.clauses.size();
        for (p->advance(); !p->eoc(); p->advance()) {
            c.clauses.push_back(p->curr());
        }
        if (p->eof() && start == c.clauses.size()) break;
        if (!p->eof() && start == c.clauses.size()) {
            LOG(2) << "Empty clause in input file, unsatisfiable formula.";
            UNSAT_EXIT;
        }
        c.start.push_back(start);
        clause_t old = c.watch[c.clauses[c.start.back()]];
        c.watch[c.clauses[c.start.back()]] = c.start.size() - 1;
        c.link[c.start.size() - 1] = old;
    }

    // Initialize active ring of literals with non-empty watch lists.
    for (lit_t k = c.nvars; k > 0; --k) {
        if (c.watched(k) || c.watched(-k)) {
            c.next[k] = c.head;
            c.head = k;
            if (c.tail == lit_nil) c.tail = k;
        }
    }
    if (c.tail != lit_nil) c.next[c.tail] = c.head;

    return c;
}

// Returns true exactly when a satisfying assignment exists for c.
bool solve(Cnf* c) {
    Timer t("solve");

    // The search for a satisfying assignment proceeds in stages from d = 1 to
    // d = c->nvars. As long as a consistent partial assignment is found, d
    // is incremented. If a conflict is found, we backtrack by decrementing d.
    lit_t d = 0;

    // As long as some literal has a non-empty watch list, continue searching
    // for a satisfying assignment. Each iteration of this main while loop
    // results in setting a value for some variable in the formula. This may
    // move the search forward towards a partial assignment or may require
    // several backtracking steps to find a feasible variable to set.
    while (c->tail != lit_nil) {
        LOG(1) << "val: " << c->val_debug_string();
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
                // Backtrack until we find a variable that has another truth
                // value we can try.
                c->tail = k;
                while (d > 0 && !c->freedom_at_stage(d)) {
                    k = c->heads[d];
                    LOG(2) << "  Unsetting " << k;
                    c->val[k] = UNSET;
                    // If variable k was active, remove it from the active ring.
                    if (c->watched(k) || c->watched(-k)) {
                        c->next[k] = c->head;
                        c->head = k;
                        c->next[c->tail] = c->head;
                    }
                    --d;
                }
                // If we've backtracked to the start, formula is unsatisfiable.
                if (d <= 0) return false;
                // Otherwise, try the other truth value for step d > 0.
                k = c->heads[d];
                if (c->val[k] == TRUE) c->val[k] = FALSE_NOT_TRUE;
                else if (c->val[k] == FALSE) c->val[k] = TRUE_NOT_FALSE;
                break;
            } else if (pos_unit) {
                // Only the positive form of the variable appears in a unit.
                c->val[c->head] = TRUE_FORCED;
                c->tail = k;
                break;
            } else if (neg_unit) {
                // Only the negated form of the variable appears in a unit.
                c->val[c->head] = FALSE_FORCED;
                c->tail = k;
                break;
            } else {
                // Keep looking for unit clauses in the active ring.
                k = c->head;
            }
        } while (c->head != c->tail);

        // If we couldn't find a unit clause, we may as well try setting the
        // first variable on the active ring. We guess TRUE/FALSE based on the
        // state of the watch list, but it's only a guess -- we may end up
        // backtracking and trying the other value later.
        if (!pos_unit && !neg_unit) {
            LOG(2) << "Couldn't find a unit clause, resorting to branching";
            c->head = c->next[c->tail];
            if (!c->watched(c->head) || c->watched(-c->head)) {
                c->val[c->head] = TRUE;
            } else {
                c->val[c->head] = FALSE;
            }
        }

        // The backtracking step above sets up d, k, and the active ring
        // appropriately for the current step. If we didn't backtrack at all
        // during this iteration, we still have some bookkeeping to do now.
        if (!pos_unit || !neg_unit) {
            ++d;
            k = c->head;
            c->heads[d] = k;
            if (c->tail == k) {
                c->tail = lit_nil;
            } else {
                LOG(2) << "Deleting " << k << " from the active ring";
                c->head = c->next[k];
                c->next[c->tail] = c->head;
            }
        }

        // Set the l to the negation of the literal we chose during this
        // iteration. Since it resolves to false, l can't be the watched literal
        // in any clauses now, so we need to clean up l's watch list. We
        // actually know at this point that l isn't in any unit clauses, since
        // at most one of l and -l are in unit clauses (we would have
        // backtracked otherwise). So we can blindly forge ahead here, assuming
        // that each clause that used to watch l has some other literal we can
        // choose to be the watched literal.
        lit_t l = c->val[k] & 1 ? k : -k;
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
                c->val[var(lp)] == UNSET) {
                if (c->tail == lit_nil) {
                    c->head = var(lp);
                    c->tail = c->head;
                    c->next[c->tail] = c->head;
                } else {
                    c->next[var(lp)] = c->head;
                    c->head = var(lp);
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
    init_counters();
    init_timers();
    Processor p(argv[oidx]);
    Cnf c = parse(&p);
    if (c.start.empty() || solve(&c)) {
        SAT_EXIT(&c);
    } else {
        PRINT << "s UNSATISFIABLE" << std::endl;
        return UNSATISFIABLE;
    }
}
