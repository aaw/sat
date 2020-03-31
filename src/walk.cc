// Algorithm W from Knuth's The Art of Computer Programming 7.2.2.2: WalkSAT.

// This program either finds a satisfying assignment or runs forever.

#include <sstream>
#include <vector>

#include "counters.h"
#include "flags.h"
#include "logging.h"
#include "timer.h"
#include "types.h"

extern unsigned long FLAGS_seed;

DEFINE_PARAM(initial_bias, 0.1,
             "Probability that true is selected for each variable during "
             "initial random assignment.");

DEFINE_PARAM(non_greedy_choice, 0.65,
             "Probability that we will choose a flip literal from all literals "
             "in a clause instead of from all minimum cost literals.");

DEFINE_PARAM(cutoff_multiplier, 10,
             "Multiplier applied to the number of iterations before restart.");

DEFINE_PARAM(quadratic_cutoff, 1,
             "If 0, length of an epoch will be linear in the number of "
             "variables. If non-zero, an epoch is quadratic in the number of "
             "variables.");

DEFINE_PARAM(move_to_front, 1,
             "If non-zero, enables a heuristic that moves some true literals "
             "to the front of clauses in hopes that they'll be quicker to find "
             "when we need to turn them off.");

// Flips a coin that lands on heads with probability p. Return true iff heads.
static bool flip(float p) {
    return static_cast<float>(rand())/RAND_MAX <= p;
}

struct Cnf {
    // Clauses are stored as a sequential list of literals in memory with no
    // terminator between clauses. Example: (1 OR 2) AND (3 OR -2 OR -1) would
    // be stored as [1][2][3][-2][-1]. The start array (below) keeps track of
    // where each clause starts -- in the example above, start[0] = 0 and
    // start[1] = 2. The end index of each clause can be inferred from the start
    // index of the next clause.
    std::vector<lit_t> clauses;

    // Zero-indexed map of clauses. Literals in clause i run from
    // clauses[start[i]] to clauses[start[i+1]] - 1 except for the final
    // clause, where the endpoint is just clauses.size() - 1. start.size() is
    // the number of clauses. "Clause indexes" refer to entries in this array.
    std::vector<clause_t> start;

    // One-indexed values of variables in the satisfying assignment.
    std::vector<bool> val;

    // Maps variables to the number of clauses that will become unsatisfied if
    // that variable's value is flipped.
    std::vector<clause_t> cost;

    // Maps literals to a list of clauses (by index) the literal is in.
    std::vector<std::vector<clause_t>> invclause_storage;
    std::vector<clause_t>* invclause;

    // Stack of unsatisfied clause indexes.
    std::vector<lit_t> unsat;

    // Reverse lookup into unsatisfied clauses. If the clause at index i is
    // satisfied (and therefore not on the unsat stack), unsat_index[i] =
    // clause_nil. Otherwise, if unsat[j] = i, then unsat_index[i] = j.
    std::vector<clause_t> unsat_index;

    // Maps clause indexes to number of true literals in clause
    std::vector<lit_t> numtrue;

    // Number of variables in the formula. Valid variables range from 1 to
    // nvars, inclusive.
    lit_t nvars;

    // Number of clauses in the formula. Valid clause indexes range from 0 to
    // nclauses - 1.
    clause_t nclauses;

    Cnf(lit_t nvars, clause_t nclauses) :
        val(nvars+1),
        cost(nvars+1, 0),
        invclause_storage(2 * nvars + 1),
        invclause(&invclause_storage[nvars]),
        unsat_index(nclauses, clause_nil),
        numtrue(nclauses, 0),
        nvars(nvars),
        nclauses(nclauses) {
        if (FLAGS_seed == 0) FLAGS_seed = time(NULL);
        srand(FLAGS_seed);
    }

    // These two methods give the begin/end index of the kth clause in the
    // clauses vector. Used for iterating over all literals in the kth clause.
    inline clause_t clause_begin(clause_t c) const { return start[c]; }
    inline clause_t clause_end(clause_t c) const {
        return (c == nclauses - 1) ? clauses.size() : start[c + 1];
    }

    inline bool is_true(lit_t l) {
        bool tv = val[var(l)];
        return (tv && l > 0) || (!tv && l < 0);
    }

    void register_satisfied(clause_t c) {
        if (unsat_index[c] == clause_nil) return;
        unsat_index[unsat[unsat.size()-1]] = unsat_index[c];
        std::swap(unsat[unsat_index[c]], unsat[unsat.size()-1]);
        unsat_index[c] = clause_nil;
        unsat.resize(unsat.size()-1);
    }

    void register_unsatisfied(clause_t c) {
        if (unsat_index[c] != clause_nil) return;
        unsat_index[c] = unsat.size();
        unsat.push_back(c);
    }

    std::string dump_clause(clause_t c) {
        std::ostringstream oss;
        clause_t end = clause_end(c);
        oss << "(";
        for (clause_t itr = clause_begin(c); itr < end; ++itr) {
            oss << clauses[itr];
            if (is_true(clauses[itr])) oss << "*";
            if (itr < end - 1) oss << " ";
        }
        oss << ")";
        return oss.str();
    }

    std::string dump_clauses() {
        std::ostringstream oss;
        for (size_t i = 0; i < start.size(); ++i) {
            oss << dump_clause(i);
        }
        return oss.str();
    }

    std::string dump_unsat() {
        std::ostringstream oss;
        for (clause_t u : unsat) {
            oss << "[" << u << "] " << dump_clause(u) << ", ";
        }
        return oss.str();
    }

    void print_assignment() {
        for (int i = 1, j = 0; i <= nvars; ++i) {
            if (j % 10 == 0) PRINT << "v";
            PRINT << (val[i] ? " -" : " ") << i;
            ++j;
            if (i == nvars) PRINT << " 0" << std::endl;
            else if (j > 0 && j % 10 == 0) PRINT << std::endl;
        }
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
    CHECK(nvars >= 0);
    CHECK(nclauses >= 0);
    CHECK_NO_OVERFLOW(lit_t, nvars);
    CHECK_NO_OVERFLOW(clause_t, nclauses);

    Cnf c(static_cast<lit_t>(nvars), static_cast<clause_t>(nclauses));

    // Read clauses until EOF.
    int lit;
    do {
        bool read_lit = false;
        std::size_t start = c.clauses.size();
        while (true) {
            nc = fscanf(f, " %i ", &lit);
            if (nc == EOF || lit == 0) break;
            c.clauses.push_back(lit);
            read_lit = true;
        }
        if (nc != EOF && start == c.clauses.size()) {
            LOG(2) << "Empty clause in input file, unsatisfiable formula.";
            UNSAT_EXIT;
        }
        if (!read_lit) break;
        c.start.push_back(start);
    } while (nc != EOF);
    CHECK(c.start.size() == c.nclauses) << "Expected nclauses == start.size()";
    fclose(f);

    for (clause_t i = 0; i < nclauses; ++i) {
        clause_t end = c.clause_end(i);
        for (clause_t j = c.clause_begin(i); j < end; ++j) {
            // Note: if a literal appears twice in a clause, the clause index
            // will appear twice in invclause.
            c.invclause[c.clauses[j]].push_back(i);
        }
    }

    return c;
}

// Returns true exactly when a satisfying assignment exists for c after
// random initialization and n iterations of WalkSAT.
bool walk(Cnf* c, int n) {

    // W1. [Initialize.]
    c->unsat.clear();
    for (lit_t i = 1; i <= c->nvars; ++i) {
        c->val[i] = flip(PARAM_initial_bias);
        c->cost[i] = 0;
    }

    for (clause_t i = 0; i < c->nclauses; ++i) {
        c->numtrue[i] = 0;
        c->unsat_index[i] = clause_nil;
        clause_t end = c->clause_end(i);
        lit_t tl = lit_nil;
        for (clause_t j = c->clause_begin(i); j < end; ++j) {
            if (c->is_true(c->clauses[j])) {
                ++c->numtrue[i];
                tl = var(c->clauses[j]);
            }
        }
        if (c->numtrue[i] == 0) {
            c->unsat_index[i] = c->unsat.size();
            c->unsat.push_back(i);
        } else if (c->numtrue[i] == 1) {
            ++c->cost[tl];
        }
    }

    for (int nn = 0; nn < n; ++nn) {
        LOG(2) << c->dump_clauses();

        // W2. [Done?]
        if (c->unsat.empty()) return true;

        // W3. [Choose j.]
        LOG(3) << "Unsat clauses: " << c->dump_unsat();
        CHECK_NO_OVERFLOW(clause_t, RAND_MAX);
        clause_t divisor =
            (static_cast<clause_t>(RAND_MAX) + 1)/c->unsat.size();
        clause_t q;
        do { q = std::rand() / divisor; } while (q >= c->unsat.size());
        LOG(2) << "Chose clause " << q << ": " << c->dump_clause(c->unsat[q]);

        // W4. [Choose l.]
        bool all = flip(PARAM_non_greedy_choice);
        clause_t end = c->clause_end(c->unsat[q]);
        lit_t choice = lit_nil;
        int k = 1;
        clause_t min_cost = std::numeric_limits<clause_t>::max();
        for (clause_t itr = c->clause_begin(c->unsat[q]); itr < end; ++itr) {
            clause_t cost = c->cost[var(c->clauses[itr])];
            CHECK(c->cost[var(c->clauses[itr])] >= 0)
                << "Cost of " << var(c->clauses[itr]) << " is negative.";
            LOG(3) << var(c->clauses[itr]) << " has cost " << cost;
            if (cost < min_cost) {
                min_cost = cost;
                if (!all || min_cost == 0) k = 1;
            }
            if ((all && min_cost > 0) || cost == min_cost) {
                if (flip(1.0/k)) { choice = c->clauses[itr]; }
                ++k;
            }
        }
        CHECK(choice != lit_nil) << "No flip literal chosen.";

        LOG(2) << "Chose " << choice << " to flip. (cost = "
               << c->cost[var(choice)] << ")";

        // W5. [Flip l.]
        lit_t pos = (c->val[var(choice)] == (choice > 0)) ? choice : -choice;
        lit_t neg = -pos;

        c->val[var(choice)] = !c->val[var(choice)];

        // Iterate over all clauses where choice was true but is now false.
        for (clause_t i : c->invclause[pos]) {
            --c->numtrue[i];
            if (c->numtrue[i] == 0) {
                // Clause is newly unsatisfied.
                c->register_unsatisfied(i);
                --c->cost[var(choice)];
            } else if (c->numtrue[i] == 1) {
                // Some other variable in the clause needs its cost incremented.
                clause_t end = c->clause_end(i);
                clause_t begin = c->clause_begin(i);
                for (clause_t itr = begin; itr < end; ++itr) {
                    if (c->is_true(c->clauses[itr])) {
                        ++c->cost[var(c->clauses[itr])];
                        if (PARAM_move_to_front) {
                            std::swap(c->clauses[begin], c->clauses[itr]);
                        }
                        break;
                    }
                }
            }
        }

        // Iterate over all clauses where choice was false but is now true.
        for (clause_t i : c->invclause[neg]) {
            ++c->numtrue[i];
            if (c->numtrue[i] == 1) {
                // Clause is newly satisfied.
                c->register_satisfied(i);
                ++c->cost[var(choice)];
            } else if (c->numtrue[i] == 2) {
                // Some other variable in the clause needs its cost decremented.
                clause_t end = c->clause_end(i);
                for (clause_t itr = c->clause_begin(i); itr < end; ++itr) {
                    if (c->clauses[itr] != neg && c->is_true(c->clauses[itr])) {
                        --c->cost[var(c->clauses[itr])];
                        break;
                    }
                }
            }
        }
    }
    return false;
}

void reluctant_double_inc(int& u, int& v) {
    if ((u & -u) == v) { ++u; v = 1; }
    else { v *= 2; }
}

bool solve(Cnf* c) {
    int u = 1, v = 1;
    int base = c->nvars;
    if (PARAM_quadratic_cutoff) base *= c->nvars;
    while (true) {
        int iters = v * base * PARAM_cutoff_multiplier;
        LOG(1) << "Running for " << iters << " iterations.";
        if (walk(c, iters)) return true;
        reluctant_double_inc(u, v);
        INC(restarts);
    }
}

int main(int argc, char** argv) {
    int oidx;
    CHECK(parse_flags(argc, argv, &oidx))
        << "Usage: " << argv[0] << " <filename>";
    init_counters();
    init_timers();
    Cnf c = parse(argv[oidx]);
    if (c.clauses.empty() || solve(&c)) {
        SAT_EXIT(&c);
    }
}