// Algorithm B from Knuth's The Art of Computer Programming 7.2.2.2:
// Enhanced backtracking using watched literals.

#include <sstream>
#include <vector>

#include "counters.h"
#include "flags.h"
#include "logging.h"
#include "timer.h"
#include "types.h"
#include "process.h"

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

    // One-indexed values of variables in the satisfying assignment.
    std::vector<State> val;

    Cnf(Processor* p) :
        p(p),
        nvars(p->nvars()),
        watch_storage(2 * nvars + 1, clause_nil),
        link(p->nclauses(), clause_nil),
        watch(&watch_storage[nvars]),
        val(nvars + 1, UNEXAMINED) {}

    // These two methods give the begin/end index of the kth clause in the
    // clauses vector. Used for iterating over all literals in the kth clause.
    inline clause_t clause_begin(clause_t c) const { return start[c]; }
    inline clause_t clause_end(clause_t c) const {
        return (c == start.size() - 1) ? clauses.size() : start[c + 1];
    }

    // Is the literal x currently false?
    inline bool is_false(lit_t x) const {
        State s = val[var(x)];
        return (x > 0 && (s == FALSE || s == FALSE_NOT_TRUE)) ||
            (x < 0 && (s == TRUE || s == TRUE_NOT_FALSE));
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

    void print_assignment() {
        p->val.resize(nvars + 1, false);  // In case preprocessing is disabled.
        for (int i = 1; i <= nvars; ++i) {
            if (val[i] == UNEXAMINED) { p->val[i] = false; }
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
    return c;
}

// Returns true exactly when a satisfying assignment exists for c.
bool solve(Cnf* c) {
    Timer t("solve");
    lit_t d = 1;  // Stage; Number of variables set in the partial assignment.
    lit_t l = 0;  // Current literal.
    while (0 < d && d <= c->nvars) {
        LOG(1) << "val: " << c->val_debug_string();
        LOG(3) << "clauses: " << c->clauses_debug_string();
        // Choose a literal value.
        if (c->val[d] == UNEXAMINED &&
            (c->watch[d] == clause_nil || c->watch[-d] != clause_nil)) {
            c->val[d] = FALSE;
        } else if (c->val[d] == UNEXAMINED) {
            c->val[d] = TRUE;
        } else if (c->val[d] == TRUE) {
            c->val[d] = FALSE_NOT_TRUE;
        } else if (c->val[d] == FALSE) {
            c->val[d] = TRUE_NOT_FALSE;
        } else {
            // Backtrack.
            LOG(2) << "Backtracking from stage " << d;
            c->val[d] = UNEXAMINED;
            d--;
            continue;
        }

        // Set current literal value based on truth value chosen for d.
        l = ((c->val[d] & 1) ? -1 : 1) * d;
        LOG(3) << "Trying " << l;

        // Update watch list entries for -l if there are any.
        LOG(3) << "Trying to make " << -l << " unwatched by all clauses";
        clause_t watcher = c->watch[-l];
        while (watcher != clause_nil) {
            clause_t start = c->clause_begin(watcher);
            clause_t end = c->clause_end(watcher);
            clause_t next = c->link[watcher];
            clause_t k = start + 1;
            while (k < end) {
                // Search for a non-false literal to watch from clause watcher
                lit_t lit = c->clauses[k];
                if (c->is_false(lit)) {
                    k++;
                    continue;
                }
                // Found a non-false literal, swap lit and -l in clauses array.
                c->clauses[start] = lit;
                c->clauses[k] = -l;
                // Splice lit into the watch list and keep going.
                c->link[watcher] = c->watch[lit];
                c->watch[lit] = watcher;
                watcher = next;
                LOG(3) << "Successfully swapped in " << lit << " as watched "
                       << "literal for " << -l << " in clause "<< c->watch[lit];
                break;
            }
            if (k == end) {
                // Failed to re-assign some literal on -l's watch list. This
                // means that some clause can't be satisfied with the partial
                // assignment created by l. We need to move on to the next
                // search step for l, which could be either trying -l or
                // backtracking.
                LOG(3) << -l << " is a unit in clause " << watcher
                       << ". Stopping attempt to update watch lists.";
                break;
            }
        }
        c->watch[-l] = watcher;
        // Move on to the next variable if watch list reassignment succeeded.
        if (watcher == clause_nil) d++;
    }
    return d != 0;
}

int main(int argc, char** argv) {
    int oidx;
    CHECK(parse_flags(argc, argv, &oidx))
        << "Usage: " << argv[0] << " <filename>";
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
