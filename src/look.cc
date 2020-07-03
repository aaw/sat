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
#include "process.h"

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

DEFINE_PARAM(disable_lookahead_wraparound, 0,
             "If 1, during lookahead, don't wait until propagation stops, only "
             "iterate through lookahead candidates at most once.");

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

DEFINE_PARAM(disable_double_lookahead_wraparound, 0,
             "If 1, during double lookahead, don't wait until propagation "
             "stops, only iterate through double lookahead candidates at most "
             "once.");

DEFINE_PARAM(double_lookahead_frontier, 7,
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

// Branching states for the solver at a decision level.
enum branch_t {
    NEED_LOOKAHEAD = 0,  // Need to perform lookahead to find best lit.
    SKIP_LOOKAHEAD= 1,   // Lookahead can be skipped for this level.
    FIRST_TRY = 2,       // Currently trying best polarity of best lit.
    SECOND_TRY = 3,      // Currently trying other polarity of best lit.
};

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
    Processor* p;

    // Number of variables in the original problem. These are the first
    // novars variables in the value array. novars <= nvars() since extra
    // vars can be added during processing to convert to 3-SAT.
    lit_t novars;

    // Storage for bimps. bimp is a pointer into bimp_storage to allow indexing
    // by both positive and negative literals. bimp maps literals to their bimp
    // list.
    std::vector<std::vector<lit_t>> bimp_storage;
    std::vector<lit_t>* bimp;

    // Storage for timps. timp is a pointer into bimp_storage to allow indexing
    // by both positive and negative literals. timp maps literals to the timp
    // list.
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

    // Ordering of literals for lookahead and double lookahead.
    std::vector<lookahead_order_t> lookahead_order;

    // Storage for windfalls (binary clauses deduced during lookahead). This
    // storage is always temporary and should be cleared before using.
    std::vector<lit_t> windfalls;

    // List of unit literals forced by the current solver state. These are
    // propagated and cleared once per iteration of the solver.
    std::vector<lit_t> force;

    // A record of decision state. Only valid up to index d (the current depth
    // of the solver).
    std::vector<branch_t> branch;

    // List of free (not fixed) variables: invfree is an index into this list so
    // that invfree[freevar[k]] == k for all 0 <= k < freevar.size().
    std::vector<lit_t> freevar;
    std::vector<size_t> invfree;

    // Stack of fixed literals. When we're propagating the consequences of a
    // literal, we also keep pointers f and g into this stack to track the
    // frontiers of RT and NT, respectively. What Knuth calls "E" is just
    // rstack.size() in our implementation.
    std::vector<lit_t> rstack;

    // Maps literals to their istamp, the last epoch where their bimps grew.
    std::vector<uint64_t> istamps_storage;
    uint64_t* istamps;

    // Maps literals to their bstamp, a counter used for computing compensation
    // resolvents.
    std::vector<uint64_t> bstamps_storage;
    uint64_t* bstamps;

    // Maps literals to the dfail value, the last istamp when they were
    // successfully considered for double lookahead.
    std::vector<uint64_t> dfail_storage;
    uint64_t* dfail;

    // Maps decision level d to the literal choice made at that level.
    std::vector<lit_t> dec;

    // Maps decision level d to the f rstack pointer when the decision was made.
    std::vector<lit_t> backf;

    // Maps decision level d to the istack value when the decision was made.
    std::vector<uint64_t> backi;

    // Maps
    std::vector<lit_t> backl;

    // A stack of literals and their bimp sizes, used to quickly undo choices
    // that caused bimps to grow.
    std::vector<istack_frame_t> istack;

    // Maps variables to their truth stamps.
    std::vector<uint32_t> val;

    // Maps variables to their bit signatures used to identify participants.
    std::vector<psig_t> sig;

    // A stack used only in strongly connected components algorithm.
    std::vector<lit_t> sccstack;

    // Heap-ordered lookahead candidates.
    Heap cand;

    // The bit signature of the current decision choices of the algorithm. Used
    // for comparing against sig[v] to see if v was considered on the current
    // search path.
    uint64_t sigma;

    lit_t d;  // Current search depth.

    size_t f;  // Index into rstack, number of RT vars from previous iterations.

    size_t g;  // Index into rstack, number of RT vars from all iterations.

    uint64_t istamp;  // Epoch counter, incremented each major solver iteration.

    uint64_t bstamp;  // Compensation resolvent counter.

    uint32_t t; // Current truth level (RT, NT, PT, etc.)

    double tau; // Trigger value for double lookahead.

    Cnf(Processor* p, lit_t nsvars) :
        p(p),
        novars(p->nvars()),
        bimp_storage(2 * (novars + nsvars) + 1),
        bimp(&bimp_storage[novars + nsvars]),
        timp_storage(2 * (novars + nsvars) + 1),
        timp(&timp_storage[novars + nsvars]),
        big_storage(2 * (novars + nsvars) + 1),
        big(&big_storage[novars + nsvars]),
        dfs_storage(2 * (novars + nsvars) + 1),
        dfs(&dfs_storage[novars + nsvars]),
        lookahead_order(novars + nsvars),
        branch(novars + nsvars + 1, NEED_LOOKAHEAD),
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
        backl(novars + nsvars + 1),
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

    // Number of variables solver is working with. Different than the number of
    // variables in the original problem because of conversion to 3-SAT.
    inline lit_t nvars() const {
        return val.size() - 1;
    }

    inline void stamp_true(lit_t l, uint32_t context) {
        val[var(l)] = context + (l < 0 ? 1 : 0);
    }

    inline void stamp_false(lit_t l, uint32_t context) {
        val[var(l)] = context + (l < 0 ? 0 : 1);
    }

    // Is literal l fixed (true or false) in a particular truth context?
    bool fixed(lit_t l, uint32_t T=nil_truth) {
        if (T == nil_truth) T = t;
        return val[var(l)] >= T;
    }

    // Is literal l fixed true in a particular truth context?
    bool fixed_true(lit_t l, uint32_t T=nil_truth) {
        if (T == nil_truth) T = t;
        uint32_t v = val[var(l)];
        if (v < T) return false;
        return (l > 0) != ((v & 1) == 1);
   }

    // Is literal l fixed false in a particular truth context?
    bool fixed_false(lit_t l, uint32_t T=nil_truth) {
        if (T == nil_truth) T = t;
        uint32_t v = val[var(l)];
        if (v < T) return false;
        return (l > 0) != ((v & 1) == 0);
    }

    // Remove var v from the free list.
    void make_unfree(lit_t v) {
        LOG(3) << "make_unfree(" << v << ")";
        CHECK(v > 0) << "wanted var in make_unfree, got lit";
        CHECK(!freevar.empty()) << "make_unfree called on empty freevar array.";
        CHECK(invfree[v] < freevar.size())
            << "make_unfree called on already unfree var: " << v;
        lit_t s = freevar[freevar.size()-1];
        std::swap(freevar[invfree[v]], freevar[freevar.size()-1]);
        freevar.pop_back();
        std::swap(invfree[v], invfree[s]);
    }

    // Add var v back to the free list.
    void make_free(lit_t v) {
        LOG(3) << "make_free(" << v << ")";
        CHECK(v > 0) << "wanted var in make_free, got lit " << v;
        CHECK(invfree[v] >= freevar.size())
            << "make_free called on already free var: " << v;
        freevar.push_back(v);
        invfree[v] = freevar.size()-1;
    }

    // Returns true exactly when u is in bimp[v].
    bool in_bimp(lit_t u, lit_t v) {
        for (const lit_t x : bimp[v]) { if (x == u) return true; }
        return false;
    }

    // Helper function: append v to bimp[u].
    void bimp_append(lit_t u, lit_t v) {
        if (istamps[u] != istamp) {
            istamps[u] = istamp;
            istack.push_back({l: u, bsize: bimp[u].size()});
        }
        bimp[u].push_back(v);
    }

    // Add the binary clause (u v), properly stamped and on the istack so that
    // it can be removed during backtracking.
    void add_binary_clause(lit_t u, lit_t v) {
        LOG(3) << "Adding binary clause (" << u << " " << v << ")";
        bimp_append(-u, v);
        bimp_append(-v, u);
    }

    // Adjust timps so that var v appears as either not active or active. This
    // should be done whenever a var is promoted to RT or demoted from RT, resp.
    void timp_set_active(lit_t v, bool active) {
        for (lit_t l : {v, -v}) {
            for (timp_t& t : timp[l]) {
                timp_t &u = timp[-t.u][t.link];
                u.active = active;
                timp[-u.u][u.link].active = active;
            }
        }
    }

    // Has sigma_stamp been called on l on the current search path? Returns
    // false if we don't know because all bits in sigma have been exhausted.
    bool participant(lit_t l) {
        psig_t p = sig[var(l)];
        return p.length > 0 && p.length <= d+1 &&
            p.path == (sigma & ((1ULL << std::min(p.length, SIGMA_BITS)) - 1));
    }

    // Mark l as a participant on the current search path.
    void sigma_stamp(lit_t l) {
        if (participant(l)) return;
        sig[var(l)] = psig_t{path: sigma, length: d+1};
    }

    // Use heuristic scores in hold to compute another iteration of heuristic
    // scores, storing them in hnew.
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

    // Helper function, returns pointer to set of heuristic scores for a level.
    double* h_ptr(size_t level) {
        return &h_storage[level][nvars()];
    }

    // Calculate heuristic scores for the current level. This should be called
    // once per decision level, and in most cases uses heuristic scores from the
    // previous level to bootstrap scores.
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

    void print_assignment() {
        p->val.resize(novars + 1, false);  // In case preprocessing is disabled.
        for (lit_t i = 1; i <= novars; ++i) {
            if (!fixed(i)) { p->val[i] = false; }
            else { p->val[i] = fixed_true(i); }
        }
        p->apply_rules();
        p->print_assignment();
    }

    std::string progress_debug_string() {
        std::ostringstream oss;
        int w = static_cast<int>(log10(nvars()) + 1);
        int rt = 0, rf = 0;
        for (lit_t v = 0; v < nvars(); ++v) {
            if (val[v] == RT) rt++;
            else if (val[v] == RT+1) rf++;
        }
        oss << "d=" << std::setw(w) << d
            << ",free=" << std::setw(w) << freevar.size()
            << ",rt=" << std::setw(w) << rt
            << ",rf=" << std::setw(w) << rf;
        return oss.str();
    }
};

// Used to temporarily set truth value of solver during lifetime of this class.
struct truth_context {
    truth_context(Cnf* c, uint32_t t) : c_(c), saved_t_(c->t) { c->t = t; }
    ~truth_context() { c_->t = saved_t_; }
private:
    Cnf* c_;
    uint32_t saved_t_;
};

Cnf parse(Processor* p) {
    p->reset();
    lit_t nsvars = 0;
    std::vector<std::vector<lit_t>> clauses;
    std::vector<lit_t> clause;
    while (!p->eof()) {
        clause.clear();
        for (p->advance(); !p->eoc(); p->advance()) {
            clause.push_back(p->curr());
        }
        if (p->eof() && clause.empty()) break;
        if (!p->eof() && clause.empty()) {
            LOG(2) << "Empty clause in input file, unsatisfiable formula.";
            UNSAT_EXIT;
        }
        if (clause.size() <= 3) {
            clauses.emplace_back(std::move(clause));
        } else {
            // Convert any clause of length > 3 to an equivalent conjunction of
            // 3-clauses by adding variables. Example: (x1 x2 x3 x4 x5) becomes
            // (x1 x2 z1) (-z1 x3 z2) (-z2 x4 z3) (-z3 x4 x5).
            LOG(3) << "Converting clause to 3-clauses.";
            clauses.push_back({});
            clauses.back().push_back(clause[0]);
            clauses.back().push_back(clause[1]);
            ++nsvars;
            clauses.back().push_back(p->nvars() + nsvars);
            LOG(3) << "  Added (" << clauses.back()[0] << " "
                   << clauses.back()[1] << " " << clauses.back()[2] << ")";
            for (size_t i = 0; i < clause.size() - 4; ++i) {
                clauses.push_back({});
                clauses.back().push_back(-p->nvars() - nsvars);
                clauses.back().push_back(clause[i + 2]);
                ++nsvars;
                clauses.back().push_back(p->nvars() + nsvars);
                LOG(3) << "  Added (" << clauses.back()[0] << " "
                       << clauses.back()[1] << " " << clauses.back()[2] << ")";
            }
            clauses.push_back({});
            clauses.back().push_back(-p->nvars() - nsvars);
            clauses.back().push_back(clause[clause.size()-2]);
            clauses.back().push_back(clause[clause.size()-1]);
            LOG(3) << "  Added (" << clauses.back()[0] << " "
                   << clauses.back()[1] << " " << clauses.back()[2] << ")";
        }
    }

    Cnf c(p, nsvars);

    // L1. [Initialize.]
    std::vector<uint8_t> forced_storage(2 * p->nvars() + 1, 0);
    uint8_t* forced = &forced_storage[p->nvars()];
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
            CHECK(cl.size() == 3) << "Unexpected clause of size " << cl.size();
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

    return c;
}

// Propagate the binary consequences of a literal l. Returns false if a conflict
// is found during propagation. This is (62) in the text.
bool propagate(Cnf* c, lit_t l) {
    size_t h = c->rstack.size();
    if (c->fixed_false(l)) {
        return false;
    } else if (!c->fixed_true(l)) {
        c->stamp_true(l, c->t);
        c->rstack.push_back(l);
    }
    for(; h < c->rstack.size(); ++h) {
        l = c->rstack[h];
        for (lit_t lp : c->bimp[l]) {
            if (c->fixed_false(lp)) {
                return false;
            } else if (!c->fixed_true(lp)) {
                c->stamp_true(lp, c->t);
                c->rstack.push_back(lp);
            }
        }
    }
    return true;
}

// Reset after a conflict has been detected. If we're trying a literal and
// haven't tried its negation yet, we'll negate and proceed. Otherwise, we'll
// backtrack. Returns next literal we should try. This is L11 - L15 in the text.
lit_t resolve_conflict(Cnf* c) {
    // L11. [Unfix near truths.]
    while (c->g < c->rstack.size()) {
        c->val[var(c->rstack.back())] = nil_truth;
        c->rstack.pop_back();
    }

    while (true) {
        // L12. [Unfix real truths.]
        while (c->f < c->rstack.size()) {
            lit_t x = c->rstack.back();
            c->rstack.pop_back();
            c->timp_set_active(var(x), true);
            c->make_free(var(x));
            c->val[var(x)] = nil_truth;
        }

        // L13. [Downdate BIMPs.]
        if (c->branch[c->d] == FIRST_TRY || c->branch[c->d] == SECOND_TRY) {
            while (c->istack.size() > c->backi[c->d]) {
                istack_frame_t f = c->istack.back();
                c->istack.pop_back();
                c->bimp[f.l].resize(f.bsize);
            }
        }

        // L14. [Try again?]
        if (c->branch[c->d] == FIRST_TRY) {
            c->branch[c->d] = SECOND_TRY;
            c->dec[c->d] = -c->dec[c->d];
            return c->dec[c->d];
        }

        // L15. [Backtrack.]
        if (c->d == 0) UNSAT_EXIT;
        --c->d;
        c->rstack.resize(c->f);
        c->f = c->backf[c->d];
    }
}

// Determine "compensation resolvents" for a learned binary clause (u v).
// Explained in Exercise 139 in the text, when (u v) is learned and w is
// in bimp[v], (u w) is also implied. All such clauses (u w) are determined
// here and added. Returns true exactly when no conflict was detected.
bool resolve_bimps(Cnf* c, lit_t u, lit_t v) {
    c->bstamps[-u] = ++c->bstamp;
    for (lit_t w : c->bimp[-u]) { c->bstamps[w] = c->bstamp; }

    if (c->bstamps[-v] == c->bstamp || c->bstamps[v] == c->bstamp) {
        return true;
    }

    for (lit_t w : c->bimp[v]) {
        if (c->fixed(w, NT)) {
            CHECK(c->fixed_true(w, NT)) << "Expected " << -w << " => " << -v;
            continue;
        }
        if (c->bstamps[-w] == c->bstamp) {  // -v => (-w and w), conflict.
            if (!propagate(c, u)) { return false; }
            break;
        } else if (c->bstamps[w] != c->bstamp) {  // -v => w, w not seen yet.
            INC(compensation_resolvents);
            c->add_binary_clause(u, w);
        }
    }
    return true;
}

// Promote all forced lits and their binary implications to NT, then promote all
// NT lits to RT by considering their ternary implications. Returns lit_nil if
// successful, otherwise backtracks and returns the literal we should try to
// propagate next. This is L5 - L9 in the text.
lit_t propagate_forced_lits(Cnf* c) {
    // L5. [Accept near truths.]
    c->t = NT;
    c->rstack.resize(c->f);
    c->g = c->f;
    ++c->istamp;

    for (lit_t f : c->force) {
        if (!propagate(c, f)) { return resolve_conflict(c); }
    }
    c->force.clear();

    // L6 - L9
    while (c->g < c->rstack.size()) {
        // L6. [Choose a nearly true L.]
        lit_t l = c->rstack[c->g];
        ++c->g;

        // L7. [Promote l to real truth.]
        c->stamp_true(l, RT);
        c->make_unfree(var(l));
        c->timp_set_active(var(l), false);

        for (const timp_t& t : c->timp[l]) {
            if (!t.active) continue;
            // L8. [Consider u OR v.]
            if (c->fixed_false(t.u) && c->fixed_false(t.v)) {
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
                    if (!propagate(c, t.u)) return resolve_conflict(c);
                } else if (c->in_bimp(t.v, -t.u)) {
                    continue;  // Already know (t.u t.v)
                } else if (c->in_bimp(-t.u, -t.v)) {
                    if (!propagate(c, t.v)) return resolve_conflict(c);
                } else {
                    c->add_binary_clause(t.u, t.v);
                    if (PARAM_add_compensation_resolvents) {
                        if (!resolve_bimps(c, t.u, t.v) ||
                            !resolve_bimps(c, t.v, t.u)) {
                            return resolve_conflict(c);
                        }
                    }
                }
            }
        }
    }
    return lit_nil;
}

// Perform depth-first search on the reversed binary implication graph to
// determine the lookahead order. Starts at the subtree rooted at l, so can
// be called on all literals in sequence, passing a reference to a running
// postorder count.
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

// Perform depth-first search on the reversed binary implication graph to
// determine the lookahead order. While doing so, compute the strongly-connected
// components (SCC) of the graph and choose the best representative of each
// component. Returns false exactly when a contradiction is discovered among any
// SCC. Like lookahead_dfs, expects to be called on all literals l in sequence
// using a running postorder count.
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

    // Process a strongly-connected component.
    if (c->dfs[l].low == c->dfs[l].num) {
        lit_t x = lit_nil;
        lit_t mx = lit_nil;
        double mh = std::numeric_limits<double>::lowest();
        do {
            x = c->sccstack.back();
            // If -l is in the same component as l, there's a contradiciton.
            if (x == -l) {
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

// Propagate the consequences of a literal l fixed during lookahead. Returns
// true exactly when there was no conflict. If hh is not null, it's incremented
// by the heuristic score update intended for the literal l's H score. This
// function is (72) in the text.
bool propagate_lookahead(Cnf* c, lit_t l, double* hh) {
    CHECK(c->rstack.size() >= c->f) << "Expected f <= rstack size";
    c->rstack.resize(c->f);
    c->g = c->f;
    c->windfalls.clear();
    if (!propagate(c, l)) return false;
    for (; c->g < c->rstack.size(); ++c->g) {
        lit_t lp = c->rstack[c->g];
        for (const timp_t& t : c->timp[lp]) {
            if (!t.active) continue;
            if (c->fixed_true(t.u) || c->fixed_true(t.v)) continue;
            if (c->fixed_false(t.u) && c->fixed_false(t.v)) { return false; }
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
    for (lit_t w : c->windfalls) { c->add_binary_clause(-l, w); }
    return true;
}

// Force a literal to be true at PT during lookahead. Returns true exactly when
// the literal could be forced without a conflict.
bool force_lookahead(Cnf* c, lit_t l) {
    // X12. [Force l.]
    c->force.push_back(l);
    truth_context tc(c, PT);
    return propagate_lookahead(c, l, nullptr);
}

// Propagate the consequences of a literal l fixed during double lookahead.
// Returns true exactly when there was no conflict. This is (73) in the text.
bool propagate_double_lookahead(Cnf* c, lit_t l) {
    CHECK(c->rstack.size() >= c->f) << "Expected f <= rstack size";
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

// Algorithm Y: Double lookahead for Algorithm X. Returns false exactly when a
// conflict is found. base is the base truth value (incremented during double
// lookahead) and bl is the size of the increment to the base truth value during
// each iteration.
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

    // Y2. [Initialize.]
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
            CHECK(false) << "Couldn't propagate " << lo.lit << " again.";
        }
    }

    while (true) {
        // Y3. [Choose l for double look.]
        lit_t l = c->lookahead_order[j].lit;
        c->t = base + c->lookahead_order[j].t;
        if (c->fixed_false(l) && !c->fixed_false(l, DT)) {
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
            // Y5. [Look ahead.]
            if (!propagate_double_lookahead(c, l)) {
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
        if (++j == c->lookahead_order.size()) {
            j = 0;
            base += 2 * bl;
        }
        bool badwrap =
            base == lbase || PARAM_disable_double_lookahead_wraparound;
        if (jp == j || (j == 0 && badwrap)) {
            // Y6. [Finish.]
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

// Algorithm X: Lookahead for Algorithm L. Returns false exactly when a conflict
// is found.
bool lookahead(Cnf* c) {
    Timer timer("lookahead");

    // X1. [Satisfied?]
    if (c->f == static_cast<size_t>(c->nvars())) {
        SAT_EXIT(c);
    }

    if (PARAM_disable_lookahead) return true;

    // X2. [Compile rough heuristics.]
    c->refine_heuristic_scores();

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
        INC(no_candidates_during_lookahead);
        for (lit_t v : c->freevar) { c->cand.insert(v, -c->h[v]*c->h[-v]); }
    }

    // Prune candidates
    size_t cmax = c->cand.size();
    if (c->d > 0) cmax = std::max(PARAM_c0, PARAM_c1/c->d);

    CHECK(!c->cand.empty()) << "Expected candidates but got none.";
    while (c->cand.size() > cmax) c->cand.delete_max();

    // X4. [Nest the candidates.]
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

    // X5. [Prepare to explore.]
    size_t j = 0, jp = 0;
    uint32_t base = 0;
    size_t nf = c->force.size();
    CHECK(!c->lookahead_order.empty()) << "lookahead_order is empty.";

    while (true) {
        // X6. [Choose l for lookahead.]
        lookahead_order_t lo = c->lookahead_order[j];
        lit_t l = lo.lit;
        c->t = base + lo.t;
        c->dfs[l].H = 0.0;
        if (c->dfs[l].parent != lit_nil) {
            c->dfs[l].H = c->dfs[c->dfs[l].parent].H;
        }
        if (!c->fixed(l)) {
            // X8. [Compute sharper heuristic.]
            double w = 0;
            bool forced = false;
            if (!propagate_lookahead(c, l, &w)) {
                INC(lookahead_propagation_failures);
                // X13. [Recover from conflict]
                if (!force_lookahead(c, -l)) {
                    INC(lookahead_conflicts);
                    return false;
                } // -> X7
                forced = true;
            } else if (w > 0) {
                c->dfs[l].H += w;
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
            if (!force_lookahead(c, -l)) { return false; }
        }

        // X7. [Move to next.]
        if (c->force.size() > nf) {
            nf = c->force.size();
            jp = j;
        }
        if (++j == c->lookahead_order.size()) {
            INC(lookahead_wraparound);
            j = 0;
            base += 2 * base_limit;
            if (PARAM_disable_lookahead_wraparound) {
                INC(lookahead_aborted);
                return true;
            }
            if (base + 2 * base_limit >= PT) {
                INC(lookahead_exhausted);
                return true;
            }
        }
        if (j == jp) { return true; }
        // -> X6
    }

    return true;
}

// Choose the best literal candidate for branching using the H scores computed
// by traversing the lookahead forest.
lit_t choose_branch_lit(Cnf* c) {
    CHECK(!c->freevar.empty()) << "choose_best_lit called with no free vars.";
    if (PARAM_disable_lookahead) return c->freevar[0];
    double best_h = std::numeric_limits<double>::lowest();
    lit_t best_var = lit_nil;
    for (lookahead_order_t la : c->lookahead_order) {
        if (la.lit < 0) continue;
        double h = (c->dfs[la.lit].H + 0.001) * (c->dfs[-la.lit].H + 0.001);
        CHECK(!c->fixed(la.lit, RT)) << la.lit << " is fixed during choice.";
        if (h > best_h) {
            best_h = h;
            best_var = la.lit;
        }
    }
    CHECK(best_var != lit_nil) << "No branch lit could be found.";
    // Using the best variable candidate, choose the least reduced literal.
    if (c->dfs[best_var].H > c->dfs[-best_var].H) { best_var = -best_var; }
    return best_var;
}

// Entry point to the solver, performs most of Algorithm L from the text.
// Returns true exactly when a satisfying assignment exists for c.
bool solve(Cnf* c) {
    Timer timer("solve");

    while (true) {
        lit_t l = lit_nil;
        while (l == lit_nil) {
            INC(decision_level, c->d);
            // L2. [New node.]
            LOG_EVERY_N_SECS(1, 1) << c->progress_debug_string();
            if (c->branch[c->d] != SKIP_LOOKAHEAD) {
                if (c->d < SIGMA_BITS) {
                    c->sigma &= (1ULL << c->d) - 1; // trim sigma
                }
                c->branch[c->d] = NEED_LOOKAHEAD;
                c->backl[c->d] = c->f;
                if (c->force.empty()) {
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
                    l = propagate_forced_lits(c);  // L5 - L9.
                    break; // -> L10 if l == lit_nil, otherwise L4
                }
            }

            // L3. [Choose l.]
            if (!c->freevar.empty()) {
                l = choose_branch_lit(c);
                INC(decisions);
            } else {
                c->d++;
                continue;
            }

            c->dec[c->d] = l;
            c->backf[c->d] = c->f;
            c->backi[c->d] = c->istack.size();
            c->branch[c->d] = FIRST_TRY;
        }

        while (l != lit_nil) {
            // L4. [Try l.]
            if (c->d < SIGMA_BITS && c->branch[c->d] == SECOND_TRY) {
                c->sigma |= 1ULL << c->d;  // append to sigma
            }
            c->force.clear();
            c->force.push_back(l);

            // L5 - L9.
            l = propagate_forced_lits(c);
        }

        // L10. [Accept real truths.]
        c->f = c->rstack.size();
        if (c->branch[c->d] == FIRST_TRY || c->branch[c->d] == SECOND_TRY) {
            ++c->d;
        } else if (c->d > 0) {
            c->branch[c->d] = SKIP_LOOKAHEAD;
            // -> L3
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
    Processor p(argv[oidx]);
    Cnf c = parse(&p);
    if (solve(&c)) SAT_EXIT(&c);
    UNSAT_EXIT;
}
