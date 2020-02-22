// Algorithm L from Knuth's The Art of Computer Programming 7.2.2.2:
// DPLL with Lookahead.
//
// This DPLL variant is modeled after Marijn Heule's March solver. When choosing
// a variable for branching, this solver efficiently simulates the choice of
// many literals that seem appealing and uses that simulation to select a single
// best candidate for branching. Surprisingly, all of this work actually makes
// the solver run faster on many problems. Even more surprisingly, sometimes
// it's a good idea to do additional work and simulate two consecutive choices.
//
// This solver implements the full lookahead solver, including Knuth's algorithm
// L, X, and Y, as well as improvements described in the following exercises:
//   - Exercise 139: Compensation resolvents
//   - Exercise 149: Efficiently identify participants
//   - Exercise 153: Use a heap to identify best candidates

#include <sstream>
#include <vector>

#include "counters.h"
#include "heap.h"
#include "flags.h"
#include "logging.h"
#include "params.h"
#include "timer.h"
#include "types.h"

DEFINE_PARAM(alpha, 3.5,
             "Multiplicative factor applied to binary clause contribution when "
             "determining lookahead candidates.");

DEFINE_PARAM(extra_heuristic_iterations, 1,
             "Number of extra iterations to run when refining lookahead "
             "candidate scores.");

DEFINE_PARAM(max_heuristic_level, 128,
             "Max search level at which we'll retain a separate set of "
             "heuristic scores for literal candidates.");

DEFINE_PARAM(max_heuristic_score, 20,
             "Max heuristic score. Scores above this value are capped.");

DEFINE_PARAM(c0, 100,
             "Defines max number of candidates considered for lookahead. See "
             "also c1: max(c0, c1/d) candidates are chosen at level d > 0.");

DEFINE_PARAM(c1, 600,
             "Defines max number of candidates considered for lookahead. See "
             "also c0: max(c0, c1/d) candidates are chosen at level d > 0.");

DEFINE_PARAM(stored_path_length, 8,
             "Length of the stored decision path used to determine whether a "
             "literal was set on the current search path. Must be <= 64.");

// Convenience macro for using the previous param.
#define SIGMA_BITS (static_cast<lit_t>(PARAM_stored_path_length))

DEFINE_PARAM(disable_lookahead, 0,
             "If 1, no lookahead (Algorithm X) will be performed.");

DEFINE_PARAM(add_windfalls, 1.0,
             "If 1, generate 'windfall' binary clauses during lookahead that "
             "are implied by consequences of the current lookahead literal.");

DEFINE_PARAM(add_double_windfalls, 1.0,
             "If 1, generate 'windfall' binary clauses during double lookahead "
             "that are implied by consequences of both the current lookahead "
             "and double lookahead literal.");

DEFINE_PARAM(cluster_during_lookahead, 1,
             "If 1, compute strongly connected components of binary "
             "implications during lookahead and only explore the best "
             "representative of each component.");

DEFINE_PARAM(disable_double_lookahead, 0,
             "If 1, no double lookahead (Algorithm Y) will be performed.");

DEFINE_PARAM(double_lookahead_frontier, 10,
             "Max number of literals we'll attempt to perform double lookahead "
             "on during a single double lookahead.");

DEFINE_PARAM(double_lookahead_damping_factor, 0.9995,
             "Damping factor that makes double lookahead more attractive the "
             "the more it's avoided. Increase this to decrease the chance of "
             "double lookahead. Should be betweeen 0 and 1, inclusive.");

DEFINE_PARAM(add_compensation_resolvents, 1,
             "Use resolution to deduce new binary clauses while exploring.");

DEFINE_PARAM(exploit_lookahead_autarkies, 1,
             "If 1, detect and exploit autarkies that occur during lookahead, "
             "resulting in either a forced literal or a new binary clause.");

// 32-bit truth stamps form the basis of the data structure used to efficiently
// set and forget truth values during lookahead. The solver always carries a
// 32-bit truth context t. Any literal with an even truth stamp >= t is true
// and any literal with an odd truth stamp >= t is false. This scheme allows
// us to quickly forget scratch work by incrementing t or to promote a truth
// value we're sure about by giving it a really high value. It also supports
// some amount of caching while computing heuristic scores by using stamps
// stamp_a < stamp_b in some cases when a => b so that we see b's heuristic
// score and truth stamp while considering a.

// Fixed constant truth values follow. Other lower values are used by the
// solver, including a floating DT (double truth) value used by double
// lookahead.

// Real truth: highest true/false stamp.
constexpr uint32_t RT = std::numeric_limits<uint32_t>::max() - 1;  // 2^32 - 2
// Near truth: all literals with this stamp will eventually end up at real truth
// unless a contradiction is found in the original formula.
constexpr uint32_t NT = std::numeric_limits<uint32_t>::max() - 3;  // 2^32 - 4
// Proto truth: the highest truth value we'll stamp during lookahead.
constexpr uint32_t PT = std::numeric_limits<uint32_t>::max() - 5;  // 2^32 - 6
// Nil truth : never used as a truth value.
constexpr uint32_t nil_truth = 0;

// Return a string with a human-readable representation of the truth stamp.
std::string tval(uint32_t t) {
    if (t == RT+1) return "RF";
    if (t == RT) return "RT";
    if (t == NT+1) return "NF";
    if (t == NT) return "NT";
    if (t == PT+1) return "PF";
    if (t == PT) return "PT";
    if (t == nil_truth) return "nil";
    std::ostringstream oss;
    oss << t;
    oss << ((t % 2) == 0 ? "T" : "F");
    return oss.str();
}

// timps and bimps: our lookahead solver only deals with 3-SAT formulas,
// converting any clause with more than three literals to a set of equivalent
// 3-SAT clauses during input processing. So our clause data structures are
// designed to be as fast as possible for iterating over all clauses that
// contain a particular literal while allowing for literals to leave/enter
// clauses as their values are fixed or unfixed. There are three cases:
//
//   * Ternary clauses: A clause (x y z) is stored in a timp map as three
//     different implications: -x => (y z), -y => (x z), and -z => (x y).
//     The structures holding (y z), (x z), (x y) also have a link field that
//     forms a circularly linked list among these three entries so that when
//     any of x, y, or z is fixed, all three clauses can be marked as disabled
//     in the timp map in constant time (or similarly, re-enabled if x, y, z
//     all become free later).
//
//   * Binary clauses: A clause (x y) is stored in a bimp map as two different
//     implications: -x => y and -y => x. Unlike timp maps, values in bimp maps
//     are just simple lists of literals. timps usually become bimps in groups,
//     as a consequence of fixing a single literal. Whenever this happens, we
//     push a record on a separate stack, keeping track of the bimp that grew
//     and its previous size, so that we can undo the bimp changes quickly if we
//     end up wanting to unfix the literal later. When bimps become unit
//     clauses, we don't actually remove them or disable them in the bimp map,
//     we just take care to always check whether a literal is fixed or free when
//     iterating over the list of bimp values.
//
//   * Unit clauses: These get pushed on special "force" list and dealt with
//     en masse during each iteration of the solver. Since we never actually
//     remove unit clauses from bimps, we don't need any special handling to
//     undo if we decide to unfix a unit clause later.

// Storage for timps (binary disjunctions implied by a single literal). timps
// exist in groups of three for every ternary disjunction: (x y z) means
// -x => (y z), -y => (x z), and -z => (x y) will all exist as timps. timps
// are stored in an array indexed by literals, so the implicant isn't stored in
// the timp. Instead we have timp[-x] = timp_t{u: y, v: z, ...}, etc. for
// (x y z) and use the link field to move to the other two timps in the group.
struct timp_t {
    lit_t u, v;

    // Use timp[-u][link] to cycle through the other two timps corresponding to
    // the original ternary clause.
    size_t link;

    // True exactly when none of the three literals in the ternary clause
    // represented by this timp are at RT.
    bool active;
};

// A record of a literal and the size of its bimp entry at some point in time.
// These live on a stack which allows us to quickly undo decisions that caused a
// literal's bimps to grow by popping the stack and shrinking the corresponding
// literal's bimp entry to its previous size.
struct istack_frame_t {
    lit_t l;
    size_t bsize;
};

// A rough signature of the state of the solver. Essentially a bitmap recording
// up to 64 of the decisions made. We need this to identify whether a literal
// has been a "participant" in the current search path by stamping each literal
// with the current solver signature whenever it's considered. This lets us
// easily focus the search in the early stages by considering only literals
// whose signatures match a prefix of the current solver signature. This focus
// becomes less important as more literals get fixed, which is why a 64-bit
// bitmap is all we keep. The stored_path_length flag can be used to set the
// effective length of a signature to a value smaller than 64 and widen the
// solver's focus even earlier.
struct psig_t {
    uint64_t path;
    lit_t length;
};

// Storage for the state of a literal according to the depth-first search (DFS)
// that we run over binary implications during lookahead. Optionally, we compute
// strongly-connected components (SCC) using Tarjan's algorithm if the
// cluster_during_lookahead flag is set.
struct dfs_t {
    dfs_t() :
        low(std::numeric_limits<size_t>::max()),
        num(std::numeric_limits<size_t>::max()),
        H(0.0),
        parent(lit_nil),
        seen(true),  // Everything starts seen, then we unset before processing.
        onstack(false),
        rep(false) {}

    size_t low;    // 'lowpoint' from the SCC algorithm.
    size_t num;    // DFS preorder stamp.
    double H;      // Second-order heuristic score, better than h.
    lit_t parent;  // parent pointer from DFS.
    bool seen;     // Has this literal been seen by DFS yet?
    bool onstack;  // Is this literal currently on the SCC stack?
    bool rep;      // Is this literal the best choice among literals in the SCC?
};

// Storage for the truth stamps assigned to candidates after the DFS during
// lookahead. These truth stamps and their ordering allow us to cache binary
// implications by arranging literal x before literal y in the ordering and
// making x's stamp greater than y's stamp in some cases when y => x.
struct lookahead_order_t {
    lit_t lit;
    uint32_t t;
};

// Storage for the DPLL search and the final assignment, if one exists.
struct Cnf {
    // Number of variables in the original problem. These are the first
    // novars variables in the value array. novars <= nvars() since extra
    // vars can be added during processing to convert to 3-SAT.
    lit_t novars;

    // Storage for bimps. bimp is a pointer into bimp_storage to allow indexing
    // by both positive and negative literals.
    std::vector<std::vector<lit_t>> bimp_storage;
    std::vector<lit_t>* bimp;

    // Storage for timps. timp is a pointer into bimp_storage to allow indexing
    // by both positive and negative literals.
    std::vector<std::vector<timp_t>> timp_storage;
    std::vector<timp_t>* timp;

    // Storage for the binary implication graph, a subset of the reverse graph
    // defined by bimp. Used to create the lookahead ordering for candidates.
    // big is a pointer that allows indexing by positive and negative literals.
    std::vector<std::vector<lit_t>> big_storage;
    std::vector<lit_t>* big;

    // Heuristic scores. h[d][l] is the score of literal l at decision level d.
    // At each new decision level, scores are bootstrapped from the previous
    // level, up to a final level defined by the flag max_decision_level.
    std::vector<std::vector<double>> h_storage;
    double* h;

    // Storage for values computed during the depth-first search of candidates.
    std::vector<dfs_t> dfs_storage;
    dfs_t* dfs;

    std::vector<lookahead_order_t> lookahead_order;

    std::vector<lit_t> windfalls;

    std::vector<lit_t> force; // list of unit literals

     // maps depth -> values of dec[depth] attempted.
    // -1 = none, 0 = dec[depth], 1 = -dec[depth].
    std::vector<uint8_t> branch;

    std::vector<lit_t> freevar;  // list of free variables
    // invfree[freevar[k]] == k, k free if this is a valid index into freevar.
    std::vector<lit_t> invfree;

    std::vector<lit_t> rstack;  // stack of literals. rstack.size() == E.

    std::vector<uint64_t> istamps_storage;  // maps literals to their istamp;
    uint64_t* istamps;

    std::vector<uint64_t> bstamps_storage;  // maps literals to their bstamp;
    uint64_t* bstamps;

    std::vector<uint64_t> dfail_storage; // dfail from Algorithm Y
    uint64_t* dfail;

    std::vector<lit_t> dec;  // maps d -> decision literal

    std::vector<lit_t> backf;  // maps d -> f at the time decision d was made.

    std::vector<uint64_t> backi;  // maps d -> istack size when dec. d was made.

    std::vector<istack_frame_t> istack;

    std::vector<uint32_t> val;  // maps variables -> truth values

    std::vector<psig_t> sig;  // to identify participants/newbies

    std::vector<lit_t> sccstack; // used for strongly connected components

    Heap cand;  // lookahead candidates

    uint64_t sigma; // branch signature, to compare against sig[var(l)] above

    lit_t d;  // current search depth

    size_t f;  // index into rstack, number of fixed variables.

    size_t g;  // really true stacked literals.

    uint64_t istamp;

    uint64_t bstamp;

    uint32_t t; // current truth level (RT, NT, PT, etc)

    double tau; // trigger for double lookahead

    Cnf(lit_t novars, lit_t nsvars) :
        novars(novars),
        bimp_storage(2 * (novars + nsvars) + 1),
        bimp(&bimp_storage[novars + nsvars]),
        timp_storage(2 * (novars + nsvars) + 1),
        timp(&timp_storage[novars + nsvars]),
        big_storage(2 * (novars + nsvars) + 1),
        big(&big_storage[novars + nsvars]),
        dfs_storage(2 * (novars + nsvars) + 1),
        dfs(&dfs_storage[novars + nsvars]),
        lookahead_order(novars + nsvars),
        branch(novars + nsvars + 1, -1),
        freevar(novars + nsvars),
        invfree(novars  + nsvars + 1),
        istamps_storage(2 * (novars + nsvars) + 1, 0),
        istamps(&istamps_storage[novars + nsvars]),
        bstamps_storage(2 * (novars + nsvars) + 1, 0),
        bstamps(&bstamps_storage[novars + nsvars]),
        dfail_storage(2 * (novars + nsvars) + 1, 0),
        dfail(&dfail_storage[novars + nsvars]),
        dec(novars + nsvars + 1),
        backf(novars + nsvars + 1),
        backi(novars + nsvars + 1),
        val(novars + nsvars + 1, 0),
        sig(novars + nsvars + 1, psig_t{path: 0, length: 0}),
        cand(novars + nsvars),
        sigma(0),
        d(0),
        f(0),
        g(0),
        istamp(1),
        bstamp(1),
        t(0),
        tau(0.0) {
        for (lit_t i = 0; i < novars + nsvars; ++i) {
            freevar[i] = i + 1;
            invfree[i + 1] = i;
        }
        CHECK(PARAM_max_heuristic_level >= 2)
            << "max_heuristic_level must be at least 2";
        h_storage.resize(PARAM_max_heuristic_level+1);
        for (int i = 0; i <= PARAM_max_heuristic_level; ++i) {
            h_storage[i].resize(2 * (novars + nsvars) + 1, 1);
        }
        h = h_ptr(0);
    }

    inline lit_t nvars() const {
        return val.size() - 1;
    }

    inline void set_true(lit_t l, uint32_t context) {
        val[var(l)] = context + (l < 0 ? 1 : 0);
    }

    inline void set_false(lit_t l, uint32_t context) {
        val[var(l)] = context + (l < 0 ? 0 : 1);
    }

    bool fixed(lit_t l, uint32_t T=nil_truth) {
        if (T == nil_truth) T = t;
        return val[var(l)] >= T;
    }

    bool fixed_true(lit_t l, uint32_t T=nil_truth) {
        if (T == nil_truth) T = t;
        uint32_t v = val[var(l)];
        if (v < T) return false;
        return (l > 0) != (v % 2 == 1);
   }

    bool fixed_false(lit_t l, uint32_t T=nil_truth) {
        if (T == nil_truth) T = t;
        uint32_t v = val[var(l)];
        if (v < T) return false;
        return (l > 0) != (v % 2 == 0);
    }

    void make_unfree(lit_t v) {
        LOG(3) << "make_unfree(" << v << ")";
        CHECK(v > 0) << "wanted var in make_unfree, got lit";
        CHECK(!freevar.empty()) << "make_unfree called on empty freevar array.";
        lit_t s = freevar[freevar.size()-1];
        std::swap(freevar[invfree[v]], freevar[freevar.size()-1]);
        freevar.pop_back();
        std::swap(invfree[v], invfree[s]);
    }

    void make_free(lit_t v) {
        LOG(3) << "make_free(" << v << ")";
        CHECK(v > 0) << "wanted var in make_free, got lit " << v;
        freevar.push_back(v);
        invfree[v] = freevar.size()-1;
    }

    // Returns true exactly when u is in bimp[v].
    bool in_bimp(lit_t u, lit_t v) {
        for (const lit_t x : bimp[v]) {
            if (x == u) return true;
        }
        return false;
    }

    // Append v to bimp[u].
    void bimp_append(lit_t u, lit_t v) {
        if (istamps[u] != istamp) {
            istamps[u] = istamp;
            istack.push_back({l: u, bsize: bimp[u].size()});
        }
        bimp[u].push_back(v);
    }

    void add_binary_clause(lit_t u, lit_t v) {
        LOG(3) << "Adding binary clause (" << u << " " << v << ")";
        bimp_append(-u, v);
        bimp_append(-v, u);
    }

    void timp_set_active(lit_t l, bool active) {
        for (lit_t x : {l, -l}) {
            for (timp_t& t : timp[x]) {
                timp_t &u = timp[-t.u][t.link];
                u.active = active;
                timp[-u.u][u.link].active = active;
            }
        }
    }

    bool participant(lit_t l) {
        psig_t p = sig[var(l)];
        return p.length > 0 && p.length <= d+1 &&
            p.path == (sigma & ((1ULL << std::min(p.length, SIGMA_BITS)) - 1));
    }

    void sigma_stamp(lit_t l) {
        if (participant(l)) return;
        sig[var(l)] = psig_t{path: sigma, length: d+1};
    }

    double* h_ptr(size_t level) {
        return &h_storage[level][nvars()];
    }

    void cascade_heuristic_scores(double* hold, double* hnew) {
        double avg = 0.0;
        for (lit_t l = 1; l <= nvars(); ++l) {
            avg += hold[l] + hold[-l];
        }
        avg /= 2 * nvars();
        for (lit_t l = -nvars(); l <= nvars(); ++l) {
            if (l == 0) continue;
            double bimpsum = 0.0;
            for (lit_t lp : bimp[l]) {
                if (fixed(lp)) continue;
                bimpsum += hold[lp];
            }
            double timpsum = 0.0;
            for (const timp_t& t : timp[l]) {
                if (!t.active) continue;
                timpsum += hold[t.u] * hold[t.v];
            }
            hnew[l] = 0.1 + PARAM_alpha*bimpsum/avg + timpsum/(avg*avg);
            hnew[l] = std::max(PARAM_max_heuristic_score, hnew[l]);
        }
    }

    void refine_heuristic_scores() {
        if (d <= 1) {
            cascade_heuristic_scores(h_ptr(0), h_ptr(1));
            for (int i = 0; i < 2 + PARAM_extra_heuristic_iterations; ++i) {
                cascade_heuristic_scores(h_ptr(1), h_ptr(2));
                cascade_heuristic_scores(h_ptr(2), h_ptr(1));
            }
            h = h_ptr(1);
        } else if (d < PARAM_max_heuristic_level) {
            cascade_heuristic_scores(h_ptr(d-1), h_ptr(d));
            for (int i = 0; i < PARAM_extra_heuristic_iterations; ++i) {
                cascade_heuristic_scores(h_ptr(d), h_ptr(d-1));
                cascade_heuristic_scores(h_ptr(d-1), h_ptr(d));
            }
            h = h_ptr(d);
        } else {
            cascade_heuristic_scores(h_ptr(PARAM_max_heuristic_level-1),
                                     h_ptr(PARAM_max_heuristic_level));
            for (int i = 0; i < PARAM_extra_heuristic_iterations; ++i) {
                cascade_heuristic_scores(h_ptr(PARAM_max_heuristic_level),
                                         h_ptr(PARAM_max_heuristic_level-1));
                cascade_heuristic_scores(h_ptr(PARAM_max_heuristic_level-1),
                                         h_ptr(PARAM_max_heuristic_level));
            }
            h = h_ptr(PARAM_max_heuristic_level);
        }
    }

    std::string val_debug_string() const {
        std::ostringstream oss;
        for(int i = 0; i < d; ++i) {
            oss << (branch[i] == 0 ? "+" : "") << dec[i];
        }
        return oss.str();
    }

    std::string dump_graph(std::vector<lit_t>* g) const {
        std::ostringstream oss;
        for(lit_t l = -nvars(); l <= nvars(); ++l) {
            if (l == 0) continue;
            if (g[l].empty()) continue;
            oss << "[" << l << "] -> ";
            for (lit_t x : g[l]) {
                oss << x << ", ";
            }
            oss << std::endl;
        }
        return oss.str();
    }

    std::string dump_bimp() const { return dump_graph(bimp); }

    std::string dump_big() const { return dump_graph(big); }

    void print_assignment() {
        for (int i = 1, j = 0; i <= novars; ++i) {
            if (!fixed(i)) { set_false(i, t); }
            if (j % 10 == 0) PRINT << "v";
            PRINT << (fixed_false(i) ? " -" : " ") << i;
            ++j;
            if (i == novars) PRINT << " 0" << std::endl;
            else if (j > 0 && j % 10 == 0) PRINT << std::endl;
        }
    }

    std::string dump_h_scores() const {
        std::ostringstream oss;
        for (lit_t l = 1; l <= nvars(); ++l) {
            oss << "[" << l << ":" << h[l] << "*" << h[-l] << "=" << h[l]*h[-l]
                << "]";
        }
        return oss.str();
    }

    std::string dump_truths() const {
        std::ostringstream oss;
        for (lit_t l = 1; l <= nvars(); ++l) {
            if (val[l] != nil_truth) {
                oss << "[" << l << ":" << tval(val[l]) << "]";
            }
        }
        return oss.str();
    }

    std::string dump_rstack() const {
        std::ostringstream oss;
        for (size_t i = 0; i < rstack.size(); ++i) {
            if (i == g) oss << "{G}";
            if (i == f) oss << "{F}";
            oss << "[" << rstack[i] << ":" << tval(val[var(rstack[i])]) << "]";
        }
        if (rstack.size() == g) oss << "{G}";
        if (rstack.size() == f) oss << "{F}";
        return oss.str();
    }
};

// Used to temporarily set truth value, then revert when scope ends.
struct truth_context {
    truth_context(Cnf* c, uint32_t t) : c_(c), saved_t_(c->t) {
        c->t = t;
    }
    ~truth_context() {
        c_->t = saved_t_;
    }
private:
    Cnf* c_;
    uint32_t saved_t_;
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

    // Read clauses until EOF.
    int lit;
    lit_t nsvars = 0;
    std::vector<std::vector<lit_t>> clauses;
    std::vector<lit_t> clause;
    do {
        clause.clear();
        bool read_lit = false;
        while (true) {
            nc = fscanf(f, " %i ", &lit);
            if (nc == EOF || lit == 0) break;
            clause.push_back(lit);
            read_lit = true;
        }
        if (clause.empty() && nc != EOF) {
            LOG(2) << "Empty clause in input file, unsatisfiable formula.";
            UNSAT_EXIT;
        }
        if (!read_lit) break;

        if (clause.size() <= 3) {
            clauses.emplace_back(std::move(clause));
        } else {
            // Convert any clause of length > 3 to an equivalent conjunction of
            // 3-clauses. Example: (x1 x2 x3 x4 x5) becomes
            // (x1 x2 z1) (-z1 x3 z2) (-z2 x4 z3) (-z3 x4 x5).
            std::ostringstream oss;
            for(const auto& x : clause) { oss << x << " "; }
            LOG(3) << "Converting clause to 3-clauses: (" << oss.str() << ")";
            clauses.push_back({});
            clauses.back().push_back(clause[0]);
            clauses.back().push_back(clause[1]);
            ++nsvars;
            clauses.back().push_back(nvars + nsvars);
            LOG(3) << "  Added (" << clauses.back()[0] << " "
                   << clauses.back()[1] << " " << clauses.back()[2] << ")";
            for (size_t i = 0; i < clause.size() - 4; ++i) {
                clauses.push_back({});
                clauses.back().push_back(-nvars - nsvars);
                clauses.back().push_back(clause[i + 2]);
                ++nsvars;
                clauses.back().push_back(nvars + nsvars);
                LOG(3) << "  Added (" << clauses.back()[0] << " "
                       << clauses.back()[1] << " " << clauses.back()[2] << ")";
            }
            clauses.push_back({});
            clauses.back().push_back(-nvars - nsvars);
            clauses.back().push_back(clause[clause.size()-2]);
            clauses.back().push_back(clause[clause.size()-1]);
            LOG(3) << "  Added (" << clauses.back()[0] << " "
                   << clauses.back()[1] << " " << clauses.back()[2] << ")";
        }
    } while (nc != EOF);
    fclose(f);

    Cnf c(nvars, nsvars);

    // L1. [Initialize.]
    std::vector<uint8_t> forced_storage(2 * nvars + 1, 0);
    uint8_t* forced = &forced_storage[nvars];
    for (const auto& cl : clauses) {
        if (cl.size() == 1) {
            if (forced[-cl[0]]) {
                LOG(2) << "Conflicting unit clauses for " << var(cl[0]);
                UNSAT_EXIT;
            } else if (!forced[cl[0]]) {
                c.force.push_back(cl[0]);
                forced[cl[0]] = 1;
            }
        } else if (cl.size() == 2) {
            c.bimp[-cl[0]].push_back(cl[1]);
            c.bimp[-cl[1]].push_back(cl[0]);
        } else /* cl.size() == 3 */ {
            CHECK(cl.size() == 3) << "Unexpected long clause.";
            size_t link = c.timp[-cl[1]].size();
            c.timp[-cl[0]].push_back({
                u: cl[1], v: cl[2], link: link, active: true});
            link = c.timp[-cl[2]].size();
            c.timp[-cl[1]].push_back({
                u: cl[2], v: cl[0], link: link, active: true});
            link = c.timp[-cl[0]].size() - 1;
            c.timp[-cl[2]].push_back({
                u: cl[0], v: cl[1], link: link, active: true});
        }
    }

    if (LOG_ENABLED(3)) { LOG(3) << "bimp: " << c.dump_bimp(); }
    return c;
}

// Returns false if a conflict was found. This is (62) in the text.
bool propagate(Cnf* c, lit_t l) {
    LOG(2) << "Propagating " << l;
    size_t h = c->rstack.size();
    if (c->fixed_false(l)) {
        LOG(2) << l << " fixed false at " << tval(c->t);
        return false;
    } else if (!c->fixed_true(l)) {
        LOG(2) << "fixing " << l << " true at " << tval(c->t);
        c->val[var(l)] = c->t + (l > 0 ? 0 : 1);
        c->rstack.push_back(l);
    }
    for(; h < c->rstack.size(); ++h) {
        l = c->rstack[h];
        for (lit_t lp : c->bimp[l]) {
            LOG(2) << "taking account of " << l << "'s bimp " << lp;
            if (c->fixed_false(lp)) {
                LOG(2) << "  " << lp << " fixed false at " << tval(c->t);
                return false;
            } else if (!c->fixed_true(lp)) {
                LOG(2) << "  fixing " << lp << " true at " << tval(c->t);
                c->val[var(lp)] = c->t + (lp > 0 ? 0 : 1);
                c->rstack.push_back(lp);
            }
        }
    }
    LOG(2) << "Successful propagation of " << l;
    return true;
}

//
// TODO: just make a member function of Cnf
lit_t resolve_conflict(Cnf* c) {
    LOG(3) << "L11: Current rstack: " << c->dump_rstack();
    // L11. [Unfix near truths.]
    while (c->g < c->rstack.size()) {
        LOG(2) << "L11: unsetting " << var(c->rstack.back())
               << " (" << tval(c->val[var(c->rstack.back())]) << ")";
        c->val[var(c->rstack.back())] = 0;
        c->rstack.pop_back();
    }
    while (true) {
        LOG(3) << "L12: Current rstack: " << c->dump_rstack();
        // L12. [Unfix real truths.]
        while (c->f < c->rstack.size()) {
            lit_t x = c->rstack.back();
            LOG(2) << "L12: unsetting " << var(x) << " ("
                   << tval(c->val[var(x)]) << ")";
            c->rstack.pop_back();
            c->timp_set_active(x, true);
            c->make_free(var(x));
            c->val[var(x)] = 0;
        }

        LOG(3) << "L13: Current rstack: " << c->dump_rstack();
        // L13. [Downdate BIMPs.]
        if (c->branch[c->d] >= 0) {
            while (c->istack.size() > c->backi[c->d]) {
                istack_frame_t f = c->istack.back();
                c->istack.pop_back();
                // debug only loop
                if (LOG_ENABLED(3)) {
                    for (size_t i = f.bsize; i < c->bimp[f.l].size(); ++i) {
                        LOG(3) << "forgetting bimp " << f.l << " -> "
                               << c->bimp[f.l][i];
                    }
                }
                c->bimp[f.l].resize(f.bsize);
            }
        }

        // L14. [Try again?]
        if (c->branch[c->d] == 0) {
            LOG(2) << "Trying again at " << c->d << " with " << -c->dec[c->d];
            c->branch[c->d] = 1;
            c->dec[c->d] = -c->dec[c->d];
            // TODO: this force->clear is inserted so that L4 will actually
            // notice the new decision. There's probably a way to communicate
            // between this stage and L4 better. Fix once everything's working.
            c->force.clear();
            return c->dec[c->d];
        }

        // L15. [Backtrack.]
        LOG(2) << "Entering L15 with d = " << c->d;
        if (c->d == 0) UNSAT_EXIT;
        --c->d;
        c->rstack.resize(c->f);
        c->f = c->backf[c->d];
    }
}

// Returns true iff there was no conflict.
bool resolve_bimps(Cnf* c, lit_t u, lit_t v) {
    c->bstamp++;
    c->bstamps[-u] = c->bstamp;
    for (lit_t w : c->bimp[-u]) { c->bstamps[w] = c->bstamp; }

    if (c->bstamps[-v] == c->bstamp || c->bstamps[v] == c->bstamp) {
        return true;
    }

    for (lit_t w : c->bimp[v]) {  // All of these ws are implied by -u
        if (c->fixed(w, NT)) {
            CHECK(c->fixed_true(w, NT)) << "Expected " << -w << " => " << -v;
            continue;
        }
        if (c->bstamps[-w] == c->bstamp) {  // -u => (-w and w), conflict.
            if (!propagate(c, u)) {
                LOG(3) << "Conflict while computing compensation resolvents.";
                return false;
            }
            break;
        } else if (c->bstamps[w] != c->bstamp) {  // -u => w, w not seen yet.
            LOG(3) << "compensation resolvent: (" << u << " " << v
                   << ") and (" << -v << " " << w  << ") => ("
                   << u << ", " << w << ")";
            INC(compensation_resolvents);
            c->add_binary_clause(u, w);
        }

    }
    return true;
}

// Does L5 - L9
// Returns lit to try if there was a conflict, lit_nil otherwise
// TODO: just make a member function of Cnf
lit_t accept_near_truths(Cnf* c) {
    // L5. [Accept near truths.]
    c->t = NT;
    c->rstack.resize(c->f);
    c->g = c->f;
    ++c->istamp;

    for(const lit_t f : c->force) {
        LOG(2) << "Taking account of forced lit " << f;
        if (!propagate(c, f)) {
            LOG(2) << "conflict with forced lit " << f;
            return resolve_conflict(c);
        }
    }
    c->force.clear();

    // L6 - L9
    while (c->g < c->rstack.size()) {
        // L6. [Choose a nearly true L.]
        lit_t l = c->rstack[c->g];
        ++c->g;

        // L7. [Promote l to real truth.]
        LOG(2) << "Promoting " << l << " to RT";
        c->set_true(l, RT);
        c->make_unfree(var(l));
        c->timp_set_active(l, false);

        LOG(2) << "considering timps of " << l;
        for (const timp_t& t : c->timp[l]) {
            if (!t.active) continue;
            LOG(2) << "  considering (" << t.u << ", " << t.v << ")";
            // L8. [Consider u OR v.]
            if (c->fixed_false(t.u) && c->fixed_false(t.v)) {
                LOG(2) << "  " << t.u << " and " << t.v << " -> conflict";
                return resolve_conflict(c);
            } else if (c->fixed_false(t.u) && !c->fixed(t.v)) {
                if (!propagate(c, t.v)) return resolve_conflict(c);
            } else if (c->fixed_false(t.v) && !c->fixed(t.u)) {
                if (!propagate(c, t.u)) return resolve_conflict(c);
            } else if (!c->fixed(t.u) && !c->fixed(t.v)) {
                // L9. [Exploit u OR v.]
                c->sigma_stamp(t.u);
                c->sigma_stamp(t.v);
                if (c->in_bimp(-t.v, -t.u)) {
                    LOG(2) << -t.v << " is in bimp[" << -t.u << "]";
                    if (!propagate(c, t.u)) return resolve_conflict(c);
                } else if (c->in_bimp(t.v, -t.u)) {
                    LOG(3) << "Already know clause (" << t.u << " " << t.v
                           << "). No need to update bimp.";
                } else if (c->in_bimp(-t.u, -t.v)) {
                    if (!propagate(c, t.v)) return resolve_conflict(c);
                } else {
                    c->add_binary_clause(t.u, t.v);
                    if (PARAM_add_compensation_resolvents) {
                        LOG(2) << "Adding compensation resolvents";
                        if (!resolve_bimps(c, t.u, t.v) ||
                            !resolve_bimps(c, t.v, t.u)) {
                            return resolve_conflict(c);
                        }
                    }
                }
                // TODO: deduce compensation resolvents (see ex. 139)
            }
        }
    }
    return lit_nil;
}

// DFS helper function.
void lookahead_dfs(Cnf* c, lit_t& count, lit_t l) {
    c->dfs[l].seen = true;
    c->dfs[l].rep = true;
    size_t i = c->lookahead_order.size();
    c->lookahead_order.push_back({lit: l});
    for (lit_t w : c->big[l]) {
        if (c->dfs[w].seen) continue;
        c->dfs[w].parent = l;
        lookahead_dfs(c, count, w);
    }
    count += 2;
    c->lookahead_order[i].t = count;
}

bool lookahead_dfs_scc(Cnf* c, lit_t& count, lit_t l) {
    c->dfs[l].seen = true;
    size_t i = c->lookahead_order.size();
    c->lookahead_order.push_back({lit: l});
    c->dfs[l].num = i;
    c->dfs[l].low = i;
    c->sccstack.push_back(l);
    c->dfs[l].onstack = true;
    for (lit_t w : c->big[l]) {
        if (c->dfs[w].seen) {
            if (c->dfs[w].num < c->dfs[l].num && c->dfs[w].onstack) {
                c->dfs[l].low = std::min(c->dfs[w].num, c->dfs[l].low);
            }
        } else {
            c->dfs[w].parent = l;
            if (!lookahead_dfs_scc(c, count, w)) return false;
            c->dfs[l].low = std::min(c->dfs[l].low, c->dfs[w].low);
        }
    }

    if (c->dfs[l].low == c->dfs[l].num) {
        lit_t x = lit_nil;
        lit_t mx = lit_nil;
        double mh = std::numeric_limits<double>::min();
        do {
            x = c->sccstack.back();
            // If -l is in the same component as l, there's a contradiciton.
            if (x == -l) {
                LOG(2) << "Found a contradiction during strongly connected "
                       << "component analysis: " << l << " <=> " << -l;
                INC(connected_components_contradiction);
                return false;
            }
            if (c->h[x] > mh) {
                mh = c->h[x];
                mx = x;
            }
            c->dfs[x].onstack = false;
            c->sccstack.pop_back();
        } while (x != l);
        CHECK(mx != lit_nil) << "Couldn't find component representative.";
        c->dfs[mx].rep = c->dfs[-mx].rep = true;
    }

    count += 2;
    c->lookahead_order[i].t = count;
    return true;
}

// Main loop of truth value propagation for Algorithm X. (72) in the text.
// Returns false iff a conflict was detected. If hh is non-null, a score
// bump is added to it.
bool propagate_lookahead(Cnf* c, lit_t l, double* hh) {
    // Set l0 <- l, i <- w <- 0, and G <- E <- F; perform (62)
    CHECK(c->rstack.size() >= c->f) << "(72) says set G <- E <- F but E > F.";
    c->rstack.resize(c->f);
    c->g = c->f;
    c->windfalls.clear();
    if (!propagate(c, l)) return false;
    for (; c->g < c->rstack.size(); ++c->g) {
        lit_t lp = c->rstack[c->g];
        for (const timp_t& t : c->timp[lp]) {
            if (!t.active) continue;
            if (c->fixed_true(t.u) || c->fixed_true(t.v)) continue;
            if (c->fixed_false(t.u) && c->fixed_false(t.v)) {
                LOG(3) << "Both " << t.u << " and " << t.v << " fixed false at "
                       << tval(c->t) << " and in timp[" << lp << "], conflict.";
                return false;
            }
            if (c->fixed_false(t.u)) { // => v not fixed
                if (PARAM_add_windfalls) c->windfalls.push_back(t.v);
                if (!propagate(c, t.v)) return false;
                continue;
            }
            if (c->fixed_false(t.v)) { // => u not fixed
                if (PARAM_add_windfalls) c->windfalls.push_back(t.u);
                if (!propagate(c, t.u)) return false;
                continue;
            }
            // Otherwise, neither u nor v are fixed.
            if (hh != nullptr) {
                *hh += c->h[t.u] * c->h[t.v];
            }
        }
    }
    if (PARAM_add_windfalls) INC(windfalls, c->windfalls.size());
    LOG(2) << "Adding " << c->windfalls.size() << " windfalls";
    for (lit_t w : c->windfalls) {
        c->add_binary_clause(-l, w);
    }
    return true;
}

// Returns false iff a conflict is found.
bool force_lookahead(Cnf* c, lit_t l) {
    // X12. [Force l.]
    LOG(3) << "X12 with " << l;
    c->force.push_back(l);
    truth_context tc(c, PT);
    return propagate_lookahead(c, l, nullptr);
}

// Returns false iff a conflict is found. This is (73) in the text.
// TODO: this can probably be merged with propagate_lookahead, they're both
// essentially the same function.
bool propagate_double_lookahead(Cnf* c, lit_t l) {
    CHECK(c->rstack.size() >= c->f) << "(73) says set G <- E <- F but E > F.";
    c->rstack.resize(c->f);
    c->g = c->f;
    if (!propagate(c, l)) return false;
    for (; c->g < c->rstack.size(); ++c->g) {
        lit_t lp = c->rstack[c->g];
        for (const timp_t& t : c->timp[lp]) {
            if (!t.active) continue;
            if (c->fixed_true(t.u) || c->fixed_true(t.v)) continue;
            if (!c->fixed(t.u) && !c->fixed(t.v)) continue;
            if (c->fixed_false(t.u) && c->fixed_false(t.v)) {
                LOG(3) << "Both " << t.u << " and " << t.v << " fixed false at "
                       << tval(c->t) << " and in timp[" << lp << "], conflict.";
                return false;
            }
            if (c->fixed_false(t.u)) { // => v not fixed
                if (!propagate(c, t.v)) return false;
                continue;
            }
            if (c->fixed_false(t.v)) { // => u not fixed
                if (!propagate(c, t.u)) return false;
                continue;
            }
            CHECK(false) << "Missing case in propagate_double_lookahead.";
        }
    }
    return true;
}

// Algorithm Y: Double lookahead for Algorithm X.
// Returns false exactly when a conflict is found.
bool double_lookahead(Cnf* c, uint32_t& base, lookahead_order_t lo, size_t bl) {
    if (PARAM_disable_double_lookahead) return true;

    Timer timer("double_lookahead");

    // Y1. [Filter.]
    if (c->dfail[lo.lit] == c->istamp) return true;
    if (c->t + 2 * bl * (PARAM_double_lookahead_frontier + 1) > PT) {
        INC(double_lookahead_exhausted);
        return true;
    }
    if (c->dfs[lo.lit].H <= c->tau) {
        c->tau *= PARAM_double_lookahead_damping_factor;
        return true;
    }
    LOG(3) << "Doing double lookahead on " << lo.lit;

    // Y2. [Initialize.]
    LOG(3) << "Initializing double lookahead";
    base = c->t - 2;
    uint32_t lbase = base + 2 * bl * PARAM_double_lookahead_frontier;
    lit_t l0 = lo.lit;
    uint32_t DT = lbase + lo.t;
    c->windfalls.clear();
    size_t jp = 0, j = 0;

    {
        truth_context tc(c, DT);
        c->rstack.resize(c->f);
        if (!propagate(c, lo.lit)) {
            // We can't get to this point unless propagate_lookahead has already
            // succeeded with lo.lit.
            CHECK(false) << "Couldn't double-propagate " << lo.lit;
        }
    }

    while (true) {
        // Y3. [Choose l for double look.]
        lit_t l = c->lookahead_order[j].lit;
        c->t = base + c->lookahead_order[j].t;
        LOG(3) << "Considering " << l << " at " << tval(c->t) << " for dlook.";
        if (c->fixed_false(l) && !c->fixed_false(l, DT)) {
            LOG(3) << l << " already false, make it double false";
            // Y7. [Make l false.]
            jp = j;
            truth_context tc(c, DT);
            if (!propagate_double_lookahead(c, -l)) {
                base = lbase;
                return false;
            }
            if (PARAM_add_double_windfalls) c->windfalls.push_back(-l);
        }

        if (!c->fixed(l)) {
            LOG(3) << l << " not fixed, we can look ahead on it";
            // Y5. [Look ahead.]
            if (!propagate_double_lookahead(c, l)) {
                LOG(3) << "Failed double lookahead on " << l;
                // Y8. [Recover from conflict.]
                // Y7. [Make lo.lit false.]
                jp = j;
                truth_context tc(c, DT);
                if (!propagate_double_lookahead(c, -l)) {
                    base = lbase;
                    return false;
                }
                if (PARAM_add_double_windfalls) c->windfalls.push_back(-l);
            }
            // -> Y4
        }

        // Y4. [Move to next.]
        LOG(3) << "On to next j";
        ++j;
        if (j == c->lookahead_order.size()) {
            LOG(3) << "Double lookahead wraparound";
            j = 0;
            base += 2 * bl;
        }
        if (jp == j || (j == 0 && base == lbase)) {
            // Y6. [Finish.]
            LOG(3) << "Successfully finished double lookahead.";
            if (PARAM_add_double_windfalls) {
                INC(double_windfalls, c->windfalls.size());
                for (lit_t w : c->windfalls) { c->add_binary_clause(-l0, w); }
            }
            base = lbase;
            c->t = DT;
            c->tau = c->dfs[l0].H;
            c->dfail[l0] = c->istamp;
            return true;
        }
        // -> Y3
    }
}

// Algorithm X:
// Returns false exactly when a conflict is found.
bool lookahead(Cnf* c) {
    Timer timer("lookahead");

    // X1. [Satisfied?]
    if (c->f == static_cast<size_t>(c->nvars())) {
        SAT_EXIT(c);
    }

    if (PARAM_disable_lookahead) return true;

    // X2. [Compile rough heuristics.]
    c->refine_heuristic_scores();
    if (LOG_ENABLED(3)) LOG(3) << "h: " << c->dump_h_scores();

    // X3. [Preselect candidates.]
    c->cand.clear();

    bool ts = true, bs = true;
    for (lit_t v : c->freevar) {
        if (c->participant(v)) c->cand.insert(v, -c->h[v]*c->h[-v]);
        c->val[v] = 0;
        // We can also use this opportunity iterating through free vars to
        // figure out if all clauses are satisfied and exit early if so. See
        // Exercise 152 for more details.
        if (!ts || !bs) continue;
        for (const lit_t l : {-v, v}) {
            for (const timp_t t : c->timp[l]) {
                if (t.active) { ts = false; break; }
            }
            for (lit_t b : c->bimp[l]) {
                if (c->val[var(b)] < RT) { bs = false; break; }
            }
        }
    }
    if (ts && bs) { SAT_EXIT(c); }

    if (c->cand.empty()) {
        LOG(2) << "No participants, flagging all vars as candidates.";
        INC(no_candidates_during_lookahead);
        for (lit_t v : c->freevar) {
            c->cand.insert(v, -c->h[v]*c->h[-v]);
        }
    }

    // Prune candidates
    size_t cmax = c->cand.size();
    if (c->d > 0) cmax = std::max(PARAM_c0, PARAM_c1/c->d);
    LOG(2) << "cmax = " << cmax << ", d = " << c->d;

    CHECK(!c->cand.empty()) << "Expected candidates but got none.";
    while (c->cand.size() > cmax) c->cand.delete_max();

    // X4. [Nest the candidates.]
    if (LOG_ENABLED(3)) { LOG(3) << "before nesting: " << c->dump_bimp(); }
    for (lit_t l = -c->nvars(); l <= c->nvars(); ++l) {
        if (l == 0) continue;
        c->dfs[l] = dfs_t();
        c->big[l].clear();
    }
    for (lit_t v : c->cand.heap) {
        c->dfs[v].seen = c->dfs[-v].seen = false;
    }
    // Copy reverse graph induced by candidates into big.
    for (lit_t u = -c->nvars(); u <= c->nvars(); ++u) {
        if (u == 0) continue;
        if (c->dfs[u].seen) continue;
        for (lit_t v : c->bimp[u]) {
            if (c->dfs[v].seen) continue;
            c->big[v].push_back(u);
        }
    }
    if (LOG_ENABLED(3)) { LOG(3) << "candidate graph: " << c->dump_big(); }

    lit_t count = 0;
    c->lookahead_order.clear();
    c->sccstack.clear();
    for(lit_t v : c->cand.heap) {
        for (lit_t l : {-v,v}) {
            if (c->dfs[l].seen) continue;
            if (PARAM_cluster_during_lookahead) {
                if (!lookahead_dfs_scc(c, count, l)) return false;
            } else {
                lookahead_dfs(c, count, l);
            }
        }
    }
    CHECK(static_cast<size_t>(count) == c->cand.heap.size() * 4)
        << "Inconsistent DFS detected.";  // we 'count += 2' for each vertex.

    size_t base_limit = c->lookahead_order.size();
    if (PARAM_cluster_during_lookahead) {
        // Remove anything from lookahead_order that isn't a representative
        // of a strongly connected component (or the complement of a rep).
        size_t n = 0;
        for(size_t i = 0; i < base_limit; ++i) {
            if (!c->dfs[c->lookahead_order[i].lit].rep) continue;
            c->lookahead_order[n++] = c->lookahead_order[i];
        }
        INC(redundant_lookahead_lits, base_limit- n);
        c->lookahead_order.resize(n);

        // Contract any parent paths that go through non-representatives.
        for (lookahead_order_t la : c->lookahead_order) {
            lit_t l = la.lit;
            while (c->dfs[l].parent != lit_nil &&
                   !c->dfs[c->dfs[l].parent].rep) {
                c->dfs[l].parent = c->dfs[c->dfs[l].parent].parent;
            }
        }
    }

    if (LOG_ENABLED(3)) {
        std::ostringstream oss;
        oss << "order: ";
        for(const auto& x : c->lookahead_order) {
            oss << "[" << x.lit << ":" << x.t << "]";
        }
        LOG(3) << oss.str();
    }

    // X5. [Prepare to explore.]
    size_t j = 0, jp = 0;
    uint32_t base = 0;
    size_t nf = c->force.size();
    CHECK(!c->lookahead_order.empty()) << "lookahead_order is empty.";

    while (true) {
        // X6. [Choose l for lookahead.]
        lookahead_order_t lo = c->lookahead_order[j];
        LOG(3) << "X6 with " << lo.lit << " at " << tval(lo.t);
        lit_t l = lo.lit;
        c->t = base + lo.t;
        c->dfs[l].H = 0.0;
        if (c->dfs[l].parent != lit_nil) {
            c->dfs[l].H = c->dfs[c->dfs[l].parent].H;
        }
        if (!c->fixed(l)) {
            // X8. [Compute sharper heuristic.]
            LOG(3) << "X8";
            LOG(2) << "Current truths: " << c->dump_truths();
            double w = 0;
            bool forced = false;
            if (!propagate_lookahead(c, l, &w)) {
                LOG(3) << "Can't propagate " << l << ", trying to force " << -l;
                INC(lookahead_propagation_failures);
                // X13. [Recover from conflict]
                if (!force_lookahead(c, -l)) {
                    LOG(3) << "Can't propagate " << l << " or force " << -l
                           << ", bailing from lookahead";
                    INC(lookahead_conflicts);
                    return false;
                } // -> X7
                forced = true;
            } else if (w > 0) {
                c->dfs[l].H += w;
                LOG(3) << l << "'s H=" << c->dfs[l].H << ", p="
                       << c->dfs[l].parent;
                // -> X10
            } else {
                // X9. [Exploit an autarky]
                if (PARAM_exploit_lookahead_autarkies) {
                    if (c->dfs[l].H == 0) {
                        if (!force_lookahead(c, l)) {
                            INC(lookahead_autarky_force_failure);
                            return false;
                        }
                    } else {
                        CHECK(c->dfs[l].parent != lit_nil)
                            << "no parent for " << l;
                        c->add_binary_clause(l, -c->dfs[l].parent);
                    } // -> X10
                }
            }
            if (!forced) {
                // X10. [Optionally look deeper.] (Algorithm Y)
                // Note: double lookahead modifies base.
                if (!double_lookahead(c, base, lo, base_limit)) {
                    CHECK(c->t < PT) << "Got stamp >= PT after double look.";
                    // X13. [Recover from conflict.]
                    if (!force_lookahead(c, -lo.lit)) {
                        INC(double_lookahead_conflict_force_failure);
                        return false;
                    }
                    LOG(3) << "dlook conflict, base now set to " << base;
                    // -> X7
                } else {
                    // X11. [Exploit necessary assignments.]
                    for (lit_t ll : c->bimp[-l]) {
                        if (!c->fixed_true(ll) ||
                            c->fixed_true(ll, PT)) continue;
                        if (!force_lookahead(c, ll)) {
                            INC(double_lookahead_force_failure);
                            return false;
                        }
                    } // -> X7
                }
            }
        } else if (c->fixed_false(l) && !c->fixed_false(l, PT)) {
            // X13. [Recover from conflict.]
            if (!force_lookahead(c, -l)) {
                LOG(3) << "Can't force " << -l << ", bailing from lookahead";
                return false;
            }
        }

        // X7. [Move to next.]
        LOG(3) << "X7";
        LOG(3) << "X7: Current rstack: " << c->dump_rstack();
        if (c->force.size() > nf) {
            nf = c->force.size();
            jp = j;
        }
        ++j;
        if (j == c->lookahead_order.size()) {
            LOG(3) << "Lookahead wraparound.";
            INC(lookahead_wraparound);
            j = 0;
            base += 2 * base_limit;
        }
        if (j == jp) {
            LOG(3) << "Bailing on lookahead, no change in j = " << j;
            return true;
        }
        if (j == 0 && base + 2 * base_limit >= PT) {
            INC(lookahead_exhausted);
            LOG(3) << "Bailing on lookahead, base counter too high.";
            return true;
        }
        // -> X6
    }

    return true;
}

lit_t choose_branch_lit(Cnf* c) {
    CHECK(!c->freevar.empty()) << "choose_best_lit called with no free vars.";
    if (PARAM_disable_lookahead) return c->freevar[0];
    double best_h = std::numeric_limits<double>::min();
    lit_t best_var = lit_nil;
    for (lookahead_order_t la : c->lookahead_order) {
        if (la.lit < 0) continue;
        double h = (c->dfs[la.lit].H + 0.001) * (c->dfs[-la.lit].H + 0.001);
        LOG(3) << la.lit << "'s H*-H = " << c->dfs[la.lit].H + 0.001
               << " * " << c->dfs[-la.lit].H + 0.001 << " = " << h;
        CHECK(!c->fixed(la.lit, RT)) << la.lit << " is fixed during choice.";
        if (h > best_h) {
            LOG(3) << "new winner is " << la.lit;
            best_h = h;
            best_var = la.lit;
        }
    }
    CHECK(best_var != lit_nil) << "no branch lit could be found.";
    if (c->dfs[best_var].H > c->dfs[-best_var].H) {
        LOG(3) << "swapping winner " << best_var << " for " << -best_var;
        best_var = -best_var;
    }
    return best_var;
}

// Returns true exactly when a satisfying assignment exists for c.
bool solve(Cnf* c) {
    Timer timer("solve");

    bool choose_new_node = true;
    while (true) {
        lit_t l = lit_nil;
        while (l == lit_nil) {
            INC(decision_level, c->d);
            // L2. [New node.]
            if (choose_new_node) {
                LOG(2) << "Current truths: " << c->dump_truths();
                LOG(2) << "Current rstack: " << c->dump_rstack();
                LOG(2) << "Choosing a new node.";
                if (c->d < SIGMA_BITS) {
                    c->sigma &= (1ULL << c->d) - 1; // trim sigma
                }
                c->branch[c->d] = -1;
                if (c->force.empty()) {
                    LOG(2) << "Calling Algorithm X for lookahead, d=" << c->d;
                    // L3.
                    if (!lookahead(c)) {
                        INC(lookahead_failure);
                        // L15. [Backtrack.]
                        if (c->d == 0) UNSAT_EXIT;
                        --c->d;
                        c->rstack.resize(c->f);
                        c->f = c->backf[c->d];
                        // (L11 - L15) -> L4
                        CHECK(c->g >= c->rstack.size())
                            << "Corner case detected: unsafe to jump to L11, "
                            << "need to jump to L12 instead from L3.";
                        l = resolve_conflict(c);
                        break;
                    }
                    INC(lookahead_success);
                } else /* !c->force.empty() */ {
                    // L5 - L9. [Accept near truths.]
                    l = accept_near_truths(c);
                    break; // -> L10 if l == lit_nil, otherwise L4
                }
            }

            // L3. [Choose l.]
            if (!c->freevar.empty()) {
                l = choose_branch_lit(c);
                INC(decisions);
                LOG(2) << "Chose " << l;
            } else {
                c->d++;
                continue;
            }

            LOG(2) << "dec[" << c->d << "] = " << l;
            c->dec[c->d] = l;
            c->backf[c->d] = c->f;
            c->backi[c->d] = c->istack.size();
            c->branch[c->d] = 0;
            choose_new_node = true;
        }

        while (l != lit_nil) {
            // L4. [Try l.]
            LOG(1) << c->val_debug_string();
            if (c->d < SIGMA_BITS && c->branch[c->d] == 1) {
                c->sigma |= 1ULL << c->d;  // append to sigma
            }
            if (c->force.empty()) {
                c->force.push_back(l);
            }

            // L5 - L9. [Accept near truths.]
            LOG(2) << "Accepting near truths";
            l = accept_near_truths(c);
        }

        // L10. [Accept real truths.]
        LOG(2) << "Accepting real truths.";
        c->f = c->rstack.size();
        if (c->branch[c->d] >= 0) {
            ++c->d;
        } else if (c->d > 0) {
            choose_new_node = false;
        }
    }  // main while loop

    return true;
}

int main(int argc, char** argv) {
    int oidx;
    CHECK(parse_flags(argc, argv, &oidx)) <<
        "Usage: " << argv[0] << " <filename>";
    CHECK(PARAM_stored_path_length >= 0) << "stored_path_length must be >= 0";
    CHECK(PARAM_stored_path_length <= 64) << "stored_path_length must be <= 64";
    CHECK(PARAM_double_lookahead_damping_factor >= 0)
        << "double_lookahead_damping factor must be >= 0";
    CHECK(PARAM_double_lookahead_damping_factor <= 1)
        << "double_lookahead_damping factor must be <= 1";
    init_counters();
    init_timers();
    Cnf c = parse(argv[oidx]);
    if (solve(&c)) SAT_EXIT(&c);
    UNSAT_EXIT;
}
