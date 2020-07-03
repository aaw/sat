// Algorithm C from Knuth's The Art of Computer Programming 7.2.2.2: CDCL
//
// This implementation also includes improvements discussed in various
// exercises, including:
//   - Ex. 257: Redundant literal detection within learned clauses
//   - Ex. 266: Infrequently forego var of max activity for random selection
//   - Ex. 268: Lazy removal of level 0 false lits from clauses
//   - Ex. 269: Learning a shorter trivial clause
//   - Ex. 270: On-the-fly subsumption
//   - Ex. 271: Subsumption of immediate predecessor learned clauses
//
// The restart scheme we use is almost exactly as Knuth describes. The clause
// purging scheme we use is a little different: although we do execute "full
// runs" before each lemma database reduction, we don't use extra storage in
// the clause array to track clause activity and a usefulness metric derived
// from literal block distance (LBD). Instead, we just compute LBD directly
// and use it to gauge clause usefulness during purging.

#include <ctime>
#include <cstdlib>
#include <functional>
#include <sstream>
#include <vector>

#include "counters.h"
#include "flags.h"
#include "heap.h"
#include "logging.h"
#include "timer.h"
#include "types.h"
#include "params.h"
#include "process.h"

extern std::string FLAGS_dratfile;

// All clauses are stored linearly in one big array using elements of this union
// type. The layout for each clause is:
//
//     [ptr_1][ptr_0][size][lit_0][lit_1]...[lit_n]
//
// The first two ptr elements are watchlist pointers for the second and first
// literals in the clause, respectively. The size element stores the length of
// the clause, and the rest of the storage for the clause consists of the
// literals themselves.
union clause_elem_t {
    lit_t lit;
    clause_t size;
    clause_t ptr;
};

// Helper macros for accessing clause components. Each clause is addressed by
// the index of its first literal.
#define LIT1(c) clauses[c+1].lit
#define LIT0(c) clauses[c].lit
#define SIZE(c) clauses[c-1].size
#define WATCH0(c) clauses[c-2].ptr
#define WATCH1(c) clauses[c-3].ptr

// During a lemma database reduction, we'll temporarily re-purpose some of the
// watchlist pointer storage to tag clauses that we want to keep and to store
// the literal block distance of the clause.
#define PIN(c) clauses[c-2].lit
#define LBD(c) clauses[c-3].lit

// Size of the header for each clause in the clause array, consisting of two
// watchlist pointers plus size info.
constexpr clause_t kHeaderSize = 3;

DEFINE_PARAM(min_purged_clause_size, 4,
             "Only clauses with at least this many literals are candidates "
             "for removal during a lemma database reduction.");

DEFINE_PARAM(max_lemmas, 1000, "Initial maximum number of lemmas to retain.");

DEFINE_PARAM(max_lemmas_delta, 500,
             "Increment to max_lemmas each time we reduce the lemma database.");

DEFINE_PARAM(reduce_db_fraction, 0.55,
             "A number between 0 and 1, the fraction of lemmas we attempt to "
             "retain during a lemma database reduction.");

DEFINE_PARAM(partial_restart_prob, 0.0,
             "When restarting, probability that we attempt to find a higher "
             "non-zero level to backjump to.");

// Setting this to a non-zero value enables the optimization described in
// Exercise 266 (Random selection of decisions).
DEFINE_PARAM(peek_prob, 0.005,
             "Probability that we'll randomly select a decision literal "
             "instead of using the one with maximum activity.");

DEFINE_PARAM(phase_flip_prob, 0.02,
             "Probability that we'll flip the phase of a decision variable "
             "to the opposite of what the saved phase suggests.");

// Optimization described in Exercise 269 (Learning the trivial clause). To
// disable this optimization, set this param to something large like 1000.
DEFINE_PARAM(trivial_clause_multiplier, 1.6,
             "If learned clauses are this many times longer than the trivial "
             "clause, we'll learn the trivial clause instead.");

DEFINE_PARAM(warm_up_runs, 10,
             "Perform this many full runs After a restart.");

DEFINE_PARAM(restart_sensitivity, 0.19,
             "Knuth's ψ parameter, a value between 0 and 1. Increasing this "
             "parameter increases the likelihood we restart.");

DEFINE_PARAM(sorted_watchlists, 0,
             "If set to 1, watchlists are kept in increasing order of clause "
             "length");

// Optimization described in Exercise 257 (Redundant literal detection).
DEFINE_PARAM(remove_redundant_literals, 1,
             "If set to 1, redundant literals in learned clauses are removed.");

DEFINE_PARAM(max_redundant_recursion, 100,
             "During checks for redundant literals, bail out after this depth "
             "of recursive exploration.");

// Optimization described in Exercise 268 (Lazy level 0 false literal removal).
DEFINE_PARAM(remove_level_0_false_lits, 1,
             "If set to 1, literals appearing on level 0 will be lazily "
             "removed from clauses.");

// Optimization described in Exercise 270 (On-the-fly subsumption).
DEFINE_PARAM(on_the_fly_subsumption, 1,
             "If set to 1, strengthen clauses while resolving when possible.");

// Optimization described in Exercise 271 (Immediate predecessor subsumption).
DEFINE_PARAM(predecessor_subsumption, 1,
             "If set to 1, check the previous clause we learned when learning "
             "a new clause to see if the new clause subsumes the older one.");

// Possible states for a literal during search.
enum State {
    UNSET = 0,
    FALSE = 1,
    TRUE = 2,
};

// Knuth's restart heuristic based on Armin Biere's agility measure. Essentially
// computes a moving average called "agility" measuring how often literals are
// assigned values that disagree with their previous values. A "reluctant
// doubling" sequence is used to gate restarts, with each restart happening only
// when agility is deemed low enough that it seems like the algorithm is stuck
// in a rut. The psi parameter can be increased / decreased to speed up / slow
// down restarts, respectively.
struct restart_oracle {
    restart_oracle(float psi) :
        u(1), v(1), m(1), M(0), agility(0), theta(1), psi(psi) {}

    // Called every time a literal is assigned a value. phase_change indicates
    // whether the new value is equal to the previous value of the literal.
    void bump(bool phase_change) {
        agility -= (agility >> 13);
        if (phase_change) agility += (1 << 19);
        INC(phase_changes, phase_change ? 0 : 1);
    }

    // Called after each new learned clause. Exception: we don't actually call
    // this if we're in the middle of a full run, which might learn multiple
    // clauses.
    bool should_restart() {
        // On the kth execution of step C5, Knuth compares M, the total number
        // of learned clauses, to M_k, the sum of the first k terms of the
        // "reluctant doubling" sequence. We take a shortcut here and, instead
        // of tracking M directly, just approximate it with the number of times
        // we've called this function in step C5.
        M += 1;
        if (M < m) return false;
        m += v;  // increment m by the reluctant doubling delta.
        if ((u & -u) == v) {
            ++u;
            v = 1;
            theta = psi * (1L << 32);
        } else {
            v *= 2;
            theta += theta >> 4;
        }
        return agility <= theta;
    }

    uint32_t u, v, m, M, agility;
    uint64_t theta;
    float psi;
};

// Flips a coin that lands on heads with probability p. Return true iff heads.
static bool flip(float p) {
    return static_cast<float>(rand())/RAND_MAX <= p;
}

// Storage for the search and the final assignment, if one exists. Variables can
// take on only positive values and literals can take on both positive and
// negative values.
struct Cnf {
    Processor* p;

    // Number of variables in the problem. [1, ..., nvars] are valid variables.
    size_t nvars;

    // Array of all clauses. Consists of both clauses in the original formula
    // and lemmas learned by CDCL. All learned lemmas appear after original
    // clauses. The comment above clause_elem_t describes the layout. Clauses
    // end with zero or more tombstoned literals which are all lit_nil. Unit
    // clauses don't have WATCH0/WATCH1 set.
    std::vector<clause_elem_t> clauses;

    // The current value of a variable: either TRUE, FALSE, or UNSET.
    std::vector<State> val;

    // The level on which a variable was set. Level 0 contains variables forced
    // by unit clauses.
    std::vector<lit_t> lev;

    // The previous value of a variable. Initialized to all FALSE. Used for
    // phase-saving.
    std::vector<State> oval;

    // Maps variables to epochs so we can figure out if a variable has been
    // processed during a given epoch.
    std::vector<uint64_t> stamp;

    // Maps levels to epochs. Used to find redundant literals in lemmas.
    std::vector<uint64_t> lstamp;

    // Maps levels to the first conflict clause discovered at that level. During
    // a full run, we may discover many conflicts on many levels, but we always
    // want to resolve the first conflict per level once we're backjumping.
    std::vector<clause_t> conflict;

    // Max heap storing variable activities. Used to select decision variables.
    Heap heap;

    // The trail: an ordered list of literals that have been set to true during
    // the current search path.
    std::vector<lit_t> trail;

    // Inverse map from variable to trail index.
    std::vector<size_t> tloc;

    // Next index in the trail that we need to process. Since processing
    // propagations during a search may force several literals, we need to add
    // literals to the trail before they've been fully processed and keep track
    // of our progress with this pointer into the trail. Knuth calls this "G".
    size_t next_trail_index;

    // Maps a level to the first trail position of that level. If
    // di[0] == di[1], there are no variables set at level 0.
    std::vector<size_t> di;

    // Maps a variable to a clause that forced the variable, or clause_nil if
    // no such clause exists because the variable was part of a decision step.
    std::vector<clause_t> reason;

    // Watchlists map a literal to the first clause in that literal's sequence
    // of watched clauses. Each subsequent clause in the literal's watchlist can
    // be found by following WATCH0/WATCH1 pointers, depending on whether the
    // literal in question is in LIT0/LIT1, respectively. See the implementation
    // of watchlist_debug_string for an example.
    std::vector<clause_t> watch_storage;
    clause_t* watch;

    // Temp storage for the learned clause, re-used each epoch.
    std::vector<lit_t> b;

    // A list of (literal, reason) pairs we've learned through conflicts at the
    // lowest backjump level. During a full run, there may be more than one
    // pair on this list.
    std::vector<std::pair<lit_t, clause_t>> trail_lits;

    // The resolution epoch. Each time we learn a clause, we bump this value by
    // 3. We use this epoch value to stamp literals as "visited" in the stamp
    // and lstamp arrays while processing the learned clause. The subroutine
    // used for redundant literal detection uses epoch values that are 1 and 2
    // (mod 3), which is why we bump by 3 each time.
    unsigned long epoch;

    // Current number of lemmas: the number of clauses we've learned through
    // resolution and are keeping in the clause database.
    size_t nlemmas;

    // Clause index of the first lemma.
    clause_t lemma_start;

    // Current decision level.
    lit_t d;

    // Number of full runs remaining. If this number is > 0, we're in the
    // middle of a full run. Otherwise, the search behaves normally and will
    // start backjumping at the first detected conflict.
    size_t full_runs;

    // A pointer into the most recent entry in the conflict array.
    lit_t confp;

    // Have we seen a conflict in the current search path? Useful in full runs.
    bool seen_conflict;

    // A black box that tells us when to restart. Every time a literal is
    // assigned a value, we tell this oracle about it. Every time we learn
    // a new lemma, we ask it if we should restart.
    restart_oracle agility;

    // The number of database purges/reductions we've performed.
    size_t npurges;

    FILE* prooflog;

    Cnf(Processor* p) :
        p(p),
        nvars(p->nvars()),
        val(nvars + 1, UNSET),
        lev(nvars + 1, -1),
        oval(nvars + 1, FALSE),
        stamp(nvars + 1, 0),
        lstamp(nvars + 1, 0),
        conflict(nvars + 1, clause_nil),
        heap(nvars),
        tloc(nvars + 1, -1),
        next_trail_index(0),
        di(nvars + 1, 0),
        reason(nvars + 1, clause_nil),
        watch_storage(2 * nvars + 1, clause_nil),
        watch(&watch_storage[nvars]),
        b(nvars, -1),
        trail_lits(nvars),
        epoch(0),
        nlemmas(0),
        d(0),
        full_runs(PARAM_warm_up_runs),
        confp(0),
        seen_conflict(false),
        agility(PARAM_restart_sensitivity),
        npurges(0),
        prooflog(0) {
        trail.reserve(nvars + 1);
        heap.shuffle_init();
        if (FLAGS_dratfile != "") prooflog = fopen(FLAGS_dratfile.c_str(), "w");
    }

    ~Cnf() { if (prooflog != 0) fclose(prooflog); }

    // Is the literal x false under the current assignment?
    inline bool is_false(lit_t x) const {
        State s = val[var(x)];
        return (x > 0 && s == FALSE) || (x < 0 && s == TRUE);
    }

    // Is the literal x true under the current assignment?
    inline bool is_true(lit_t x) const {
        State s = val[var(x)];
        return (x > 0 && s == TRUE) || (x < 0 && s == FALSE);
    }

    // Have we assigned values to all variables?
    inline bool trail_complete() const {
        return trail.size() == nvars;
    }

    // Iterates over all clauses beginning at start_index. Calls func on each
    // clause, passing the clause index and clause size, respectively.
    void for_each_clause_helper(clause_t start_index,
                                std::function<void(clause_t,clause_t)> func) {
        clause_t ts = 0;
        clause_t os = 0;
        for(clause_t i = start_index - 1; i < clauses.size();
            i += os + ts + kHeaderSize) {
            os = clauses[i].size;
            clause_t ii = i + clauses[i].size + 1;
            ts = 0;
            while (ii+ts < clauses.size() && clauses[ii+ts].lit == lit_nil) {
                ++ts;
            }
            func(i+1, clauses[i].size);
        }
    }

    void for_each_clause(std::function<void(clause_t, clause_t)> func) {
        for_each_clause_helper(kHeaderSize, func);
    }

    void for_each_lemma(std::function<void(clause_t, clause_t)> func) {
        for_each_clause_helper(lemma_start, func);
    }

    std::string clause_debug_string(clause_t c) const {
        std::ostringstream oss;
        oss << "(";
        for (size_t i = 0; i < SIZE(c); ++i) {
            oss << clauses[c+i].lit;
            if (i != SIZE(c) - 1) oss << " ";
        }
        oss << ")";
        return oss.str();
    }

    std::string trail_debug_string() {
        std::ostringstream oss;
        for (lit_t l : trail) {
            oss << "[" << l << ":" << lev[var(l)] << "]";
        }
        return oss.str();
    }

    std::string watchlist_debug_string(lit_t l) {
        std::ostringstream oss;
        for (clause_t c = watch[l]; c != clause_nil;
             clauses[c].lit == l ? (c = WATCH0(c)) : (c = WATCH1(c))) {
            oss << "[" << c << "] " << clause_debug_string(c) << " ";
        }
        return oss.str();
    }

    // Assuming l is either LIT0 or LIT1 in clause c, swap lits and watchlist
    // pointers so that l is LIT0.
    void force_lit0(lit_t l, clause_t c) {
        if (LIT0(c) != l) {
            std::swap(LIT0(c), LIT1(c));
            std::swap(WATCH0(c), WATCH1(c));
        }
        CHECK(LIT0(c) == l) << "Expected " << l << " to be LIT0 or LIT1 in "
                            << clause_debug_string(c);
    }

    // A learned clause often contains literals that can be resolved out of the
    // clause by tracing chains of reasons backward. We can discover these
    // redundant literals by running a DFS through reasons to see if we can
    // only ever derive a literals already in the current learned clause. This
    // method, devised by Niklas Sörensson for MiniSat, was improved by Knuth
    // and the full implementation is described in Exercise 257.
    //
    // This function returns true exactly when l is redundant in the current
    // learned clause. This function modifies stamp values.
    bool redundant(lit_t l, int max_recursion=PARAM_max_redundant_recursion) {
        if (max_recursion == 0) return false;
        lit_t k = var(l);
        clause_t r = reason[k];
        if (r == clause_nil) return false;
        for (size_t i = 0; i < SIZE(r); ++i) {
            lit_t a = clauses[r+i].lit;
            lit_t v = var(a);
            if (k == v) continue;
            if (lev[v] == 0) continue;
            if (stamp[v] == epoch + 2) return false;
            if (stamp[v] < epoch &&
                (lstamp[lev[v]] < epoch || !redundant(a, max_recursion-1))) {
                stamp[v] = epoch + 2;
                return false;
            }
        }
        stamp[k] = epoch + 1;
        INC(redundant_recursion_level,
            PARAM_max_redundant_recursion - max_recursion);
        return true;
    }

    // Adds clause at cindex to lit's watchlist.
    void add_to_watchlist(clause_t cindex, lit_t lit) {
        if (PARAM_sorted_watchlists != 1) {
            (LIT0(cindex) == lit ? WATCH0(cindex) : WATCH1(cindex)) =
                watch[lit];
            watch[lit] = cindex;
        } else {
            size_t cs = SIZE(cindex);
            clause_t* x = &watch[lit];
            // TODO: try sorting by LBD
            while (*x != clause_nil && SIZE(*x) < cs) {
                x = &(LIT0(*x) == lit ? WATCH0(*x) : WATCH1(*x));
            }
            (LIT0(cindex) == lit ? WATCH0(cindex) : WATCH1(cindex)) = *x;
            *x = cindex;
        }
    }

    // For a clause c = l_0 l_1 ... l_k at index cindex in the clauses array,
    // removes either l_0 (if offset is 0) or l_1 (if offset is 1) from its
    // watchlist. No-op if k == 0.
    void remove_from_watchlist(clause_t cindex, lit_t offset) {
        if (offset == 1 && SIZE(cindex) == 1) return;
        clause_t l = cindex + offset;
        clause_t* x = &watch[clauses[l].lit];
        while (*x != cindex) {
            if (LIT0(*x) == clauses[l].lit) {
                x = (clause_t*)(&WATCH0(*x));
            } else /* LIT1(*x) == clauses[l].lit */ {
                x = (clause_t*)(&WATCH1(*x));
            }
        }
        *x = LIT0(*x) == clauses[l].lit ? WATCH0(*x) : WATCH1(*x);
    }

    // Knuth's blit subroutine described in the answer to Exercise 263.
    // Processes each literal involved in resolution to learn a new clause.
    // * c is the index of the clause being processed.
    // * r is the total number of literals in the learned clause and is
    //   incremented every time we add a literal.
    // * dp is the running candidate for the level that we'll eventually
    //   backjump to after learning a clause.
    // * q is the number of level d literals we still need to resolve.
    void blit(clause_t c, clause_t* r, lit_t* dp, clause_t* q) {
        for(size_t j = 1; j < SIZE(c); ++j) {
            lit_t m = clauses[c+j].lit;
            lit_t v = var(m);
            if (stamp[v] == epoch) continue;
            stamp[v] = epoch;
            lit_t p = lev[v];
            if (p > 0) heap.bump(v);
            if (p == d) {
                (*q)++;
            } else {
                b[*r] = -m;
                (*r)++;
                *dp = std::max(*dp, p);
                lstamp[p] = (lstamp[p] == epoch) ? epoch + 1 : epoch;
            }
        }
    }

    // Adds l to the trail at level d with reason r.
    void add_to_trail(lit_t l, clause_t r) {
        lit_t k = var(l);
        tloc[k] = trail.size();
        trail.push_back(l);
        val[k] = l < 0 ? FALSE : TRUE;
        lev[k] = d;
        reason[k] = r;
        agility.bump(oval[k] == val[k]);
    }

    // Rewinds the search to the given level.
    void backjump(lit_t level) {
        while (trail.size() > di[level+1]) {
            lit_t k = var(trail.back());
            trail.pop_back();
            oval[k] = val[k];
            val[k] = UNSET;
            reason[k] = clause_nil;
            conflict[lev[k]] = clause_nil;
            heap.insert(k);
        }
        next_trail_index = trail.size();
        d = level;
    }

    // Install the new clause of length r, currently in temp storage at b,
    // as the reason for literal lp at level dp. Returns the new clause index.
    clause_t learn_clause(lit_t lp, clause_t r, lit_t dp) {
        // Initialize the new clause. All of the nils we set here will be set
        // to real values below.
        clauses.push_back({.ptr = clause_nil});  // WATCH1
        clauses.push_back({.ptr = clause_nil});  // WATCH0
        clauses.push_back({.size = r+1});  // SIZE
        clause_t lc = clauses.size();
        clauses.push_back({.lit = -lp});  // LIT0
        add_to_watchlist(lc, -lp);
        clauses.push_back({.lit = lit_nil});  // LIT1, set below.
        // Need to watch a literal at some level < dp.
        bool found_watch = false;
        for (size_t j = 0; j < r; ++j) {
            if (found_watch || lev[var(b[j])] < dp) {
                clauses.push_back({-b[j]});
            } else {
                LIT1(lc) = -b[j];
                add_to_watchlist(lc, -b[j]);
                found_watch = true;
            }
        }
        CHECK(r == 0 || found_watch) << "Didn't find watched lit in new clause";
        CHECK_NO_OVERFLOW(clause_t, clauses.size());

        if (prooflog) {
            for(size_t j = 0; j < r+1; ++j) {
                fprintf(prooflog, "%d ", clauses[lc+j].lit);
            }
            fprintf(prooflog, "0\n");
        }

        ++nlemmas;
        LOG(2) << "Learned clause: " << clause_debug_string(lc);
        INC(learned_clause_literals, r+1);
        INC(learned_clauses);
        return lc;
    }

    // Removes a large fraction of the lemmas in the clause database that we
    // don't think will be useful in the future. Returns the final clause in the
    // reduced clause database. Literal block distance (LBD) and clause length
    // are used as indicators of future clause usefulness. This function must
    // only be called after a full run so that LBD can be calculated on each
    // clause (each variable needs a level assigned for LBD). We pin all clauses
    // that are active reasons for literals on the trail so restarting is not
    // necessary after running this function. The target fraction of lemmas to
    // keep is controlled by PARAMS_reduce_db_fraction.
    clause_t reduce_db() {
        Timer t("clause database purges");
        size_t target_lemmas = nlemmas * PARAM_reduce_db_fraction;

        // We make a few passes over the clauses and keep track of anything we
        // want to keep with PIN(c). If PIN(c) > 0, we don't care to keep the
        // clause. If PIN(c) == 0, we want to keep the clause because of its
        // size or LBD. If PIN(c) < 0, we want to keep the clause because it's
        // the current reason for variable -PIN(c).
        for_each_lemma([&](clause_t c, clause_t cs) { PIN(c) = 1; });

        // Pin lemmas that are reasons.
        for (lit_t l : trail) {
            lit_t v = var(l);
            if (reason[v] == clause_nil) continue;
            if (reason[v] < lemma_start) continue;
            PIN(reason[v]) = -v;
            if (target_lemmas > 0) --target_lemmas;
        }

        // Pin any small clauses. For anything else, compute LBD. Store lemma
        // indexes of LBD candidates so we can iterate in reverse over clauses.
        std::vector<clause_t> lbds(d+2, 0);
        std::vector<clause_t> hist(d+2, 0);  // lbd histogram.
        std::vector<lit_t> lemma_indexes;
        for_each_lemma([&](clause_t c, clause_t cs) {
            if (target_lemmas == 0) return;  // continue
            if (PIN(c) < 1) return;  // continue, already pinned
            if (cs < PARAM_min_purged_clause_size && PIN(c) > 0) {
                PIN(c) = 0;
                --target_lemmas;
                return; // continue
            }
            lemma_indexes.push_back(c);
            int lbd = 0;
            for(size_t j = 0; j < cs; ++j) {
                lit_t v = var(clauses[c+j].lit);
                CHECK(val[v] != UNSET) << "reduce_db called without full run.";
                lbds[lev[v]] = c;
            }
            for(lit_t j = 0; j <= d; ++j) { if (lbds[j] == c) ++lbd; }
            LBD(c) = lbd;
            CHECK(lbd > 0 && lbd <= d+1)
                << "Computed impossible LBD: " << lbd << " (d = " << d << ")";
            hist[lbd]++;
        });

        // Figure out the max LBD we can afford to keep while staying within our
        // target eviction budget.
        int max_lbd = 1;
        size_t lbd_evictions = 0;
        while (max_lbd <= d && lbd_evictions + hist[max_lbd] <= target_lemmas) {
            lbd_evictions += hist[max_lbd];
            ++max_lbd;
        }

        // We'll keep this many of the most recently learned clauses at the
        // highest LBD value we can afford (max_lbd) as well as keep all
        // clauses with LBD < max_lbd.
        int max_lbd_budget = target_lemmas - lbd_evictions;

        // Mark clauses we want to keep because of LBD.
        for(size_t i = 0; i < lemma_indexes.size(); ++i) {
            lit_t lc = lemma_indexes[lemma_indexes.size() - i - 1];
            if (PIN(lc) < 1) continue;  // already pinned
            if (LBD(lc) == max_lbd && max_lbd_budget > 0) {
                PIN(lc) = 0;
                --max_lbd_budget;
            } else if (LBD(lc) < max_lbd) {
                PIN(lc) = 0;
            }
        }

        // Clear top-level watch pointers.
        for(size_t i = 0; i < watch_storage.size(); ++i) {
            watch_storage[i] = clause_nil;
        }

        // Compact clauses.
        lit_t tail = lemma_start;
        nlemmas = 0;
        for_each_lemma([&](clause_t c, clause_t cs) {
            if (PIN(c) > 0) return;  // continue
            if (PIN(c) < 0) {
                reason[var(PIN(c))] = tail;
            }
            // If WATCH1 isn't set to something, it might be lit_nil. If it's
            // lit_nil, it could look like a tombstoned literal instead of a
            // watch pointer. So we set it explictly here, even though we'll
            // overwrite it when we recompute watchlists in the next for loop.
            WATCH1(tail) = clause_nil;
            SIZE(tail) = cs;
            for(size_t j = 0; j < cs; ++j) {
                clauses[tail+j].lit = clauses[c+j].lit;
            }
            tail += cs + kHeaderSize;
            ++nlemmas;
        });
        clauses.resize(tail - kHeaderSize);

        // Recompute all watch lists
        clause_t last_clause = clause_nil;
        for_each_clause([&](clause_t c, clause_t cs) {
            if (cs > 1) {
                add_to_watchlist(c, LIT0(c));
                add_to_watchlist(c, LIT1(c));
            }
            last_clause = c;
        });
        return last_clause;
    }

    void print_assignment() {
        p->val.resize(nvars + 1, false);  // In case preprocessing is disabled.
        for (size_t i = 1; i <= nvars; ++i) {
            if (val[i] == UNSET) { p->val[i] = FALSE; }
            else { p->val[i] = !(val[i] & 1); }
        }
        p->apply_rules();
        p->print_assignment();
    }
};

Cnf parse(Processor* p) {
    Timer t("parse");
    p->reset();
    Cnf c(p);
    while (!p->eof()) {
        c.clauses.push_back({.ptr = clause_nil});  // watch ptr for second lit.
        c.clauses.push_back({.ptr = clause_nil});  // watch ptr for first lit.
        c.clauses.push_back({.size = 0});          // size of clause. set below.
        std::size_t start = c.clauses.size();
        for (p->advance(); !p->eoc(); p->advance()) {
            c.clauses.push_back({p->curr()});
        }
        int cs = c.clauses.size() - start;
        if (!p->eof() && cs == 0) {
            LOG(2) << "Empty clause in input file, unsatisfiable formula.";
            UNSAT_EXIT;
        } else if (p->eof() && cs == 0) {
            // Clean up from (now unnecessary) c.clauses.push_backs above.
            for(clause_t i = 0; i < kHeaderSize; ++i) { c.clauses.pop_back(); }
            break;
        } else if (cs == 1) {
            lit_t x = c.clauses[c.clauses.size() - 1].lit;
            LOG(3) << "Found unit clause " << x;
            State s = x < 0 ? FALSE : TRUE;
            lit_t v = var(x);
            if (c.val[v] != UNSET && c.val[v] != s) {
                LOG(2) << "Contradictory unit clauses, unsatisfiable formula.";
                UNSAT_EXIT;
            } else if (c.val[v] == UNSET) {
                c.val[v] = s;
                c.tloc[v] = c.trail.size();
                c.trail.push_back(x);
                c.lev[v] = 0;
            } else {
                LOG(1) << "Duplicate unit (" << x << "). Skipping from now on.";
            }
        }
        CHECK(cs > 0);
        // Record the size of the clause in offset -1.
        c.clauses[start - 1].size = cs;
        // Set watch lists for non-unit clauses.
        if (cs > 1) {
            c.add_to_watchlist(start, c.clauses[start].lit);
            c.add_to_watchlist(start, c.clauses[start+1].lit);
        }
    }

    c.lemma_start = c.clauses.size() + kHeaderSize;
    return c;
}


// Returns true exactly when a satisfying assignment exists for c.
bool solve(Cnf* c) {
    Timer t("solve");
    clause_t lc = clause_nil;  // The most recent learned clause.

    while (true) {
        // C2: [Level complete?]
        if (c->trail.size() == c->next_trail_index) {
            // C5: [New level?]

            // If we've completed the trail without a conflict, we've found a
            // satisfying assignment.
            if (!c->seen_conflict && c->trail_complete()) {
                return true;
            }

            // Is the clause database too big? If so, we need to evict some
            // lemmas. Since our eviction heuristic is based on LBD, we'd like
            // to schedule a full run before the eviction to compute levels for
            // all variables. As soon as the full run is finished, we'll hit
            // this code path again and actually reduce the database.
            size_t max_lemmas =
                PARAM_max_lemmas + c->npurges * PARAM_max_lemmas_delta;
            if (c->nlemmas >= max_lemmas && !c->trail_complete() &&
                c->full_runs == 0) {
                LOG(1) << "Clause database too big, scheduling a full run.";
                c->full_runs = 1;
            } else if (c->nlemmas >= max_lemmas && c->trail_complete()) {
                LOG(1) << "Reducing clause database at epoch " << c->epoch
                       << ", starting size = " << c->nlemmas;
                lc = c->reduce_db();
                c->npurges++;
                LOG(1) << "Clause database reduced to size = " << c->nlemmas;
                INC(clause_database_purges);
            }

            // Does our agility measure tell us that we're no longer making real
            // progress in the search? If so, restart by jumping back to the
            // lowest level that we think will allow us to explore a different
            // search path. It wouldn't make much sense to restart in the middle
            // of a full run, since full runs are used for either computing
            // levels for all variables or warming up the heap activity stats.
            if (c->agility.should_restart() && c->full_runs == 0) {
                lit_t dp = 0;
                if (flip(PARAM_partial_restart_prob)) {
                    // Find unset var of max activity.
                    lit_t vmax = c->heap.peek();
                    while (c->val[vmax] != UNSET) {
                        c->heap.delete_max();
                        vmax = c->heap.peek();
                    }
                    double amax = c->heap.act(vmax);

                    // Find lowest level where decision literals will differ.
                    while(dp < c->d &&
                          c->heap.act(var(c->trail[c->di[dp+1]])) >= amax) ++dp;
                }

                if (dp < c->d) {
                    LOG(1) << "Agility-driven restart at epoch " << c->epoch
                           << " (level " << c->d << " -> " << dp << ")";
                    c->backjump(dp);
                    c->full_runs = PARAM_warm_up_runs;
                    INC(agility_restarts);
                    continue;
                } else {
                    INC(aborted_agility_restarts);
                }
            }

            // If we're at the end of a full run that found at least one
            // conflict, clean up and reset for either another full run or
            // business as usual.
            if (c->seen_conflict && c->trail_complete()) {
                --c->full_runs;
                c->backjump(0);
                c->seen_conflict = false;
                LOG(1) << "Full run done. " << c->full_runs << " runs left.";
                INC(full_runs);
            }

            ++c->d;
            c->di[c->d] = c->trail.size();

            // C6: [Make a decision]
            INC(decisions);
            bool peek = flip(PARAM_peek_prob);
            lit_t k = peek ? c->heap.rpeek() : c->heap.delete_max();
            while (c->val[k] != UNSET) {
                k = peek ? c->heap.rpeek() : c->heap.delete_max();
            }
            CHECK(k != lit_nil) << "Got nil from heap::delete_max in step C6.";
            LOG(3) << "Decided on variable " << k;
            lit_t l = c->oval[k] == FALSE ? -k : k;
            if (flip(PARAM_phase_flip_prob)) {
                INC(forced_phase_flips);
                l = -l;
            }
            LOG(3) << "Adding " << l << " to the trail.";
            c->add_to_trail(l, clause_nil);
        }

        // C3: [Advance G]
        // We still have some literals on the trail at the current level whose
        // consequences haven't been explored. Explore them now.
        lit_t l = c->trail[c->next_trail_index++];
        LOG(3) << "Examining " << -l << "'s watch list";

        // Iterate through the clauses on -l's watchlist to see if there's a
        // conflict. -l is now false, so we need to revisit its watchlist in the
        // process: any clause on -l's watchlist that has some other non-false
        // literal needs to be moved to that non-false literal's watchlist. Any
        // clause that has no other non-false literal can stay on -l's
        // watchlist. wlp tracks w's recomputed watchlist below.
        CHECK(c->is_false(-l)) << "Expected " << -l << " to be false.";
        clause_t w = c->watch[-l];
        clause_t* wlp = &c->watch[-l];
        bool watchlist_conflict = false;
        while (w != clause_nil) {
            // C4: [Does w force a unit?]
            c->force_lit0(-l, w);
            clause_t nw = c->WATCH0(w);
            LOG(3) << "Looking at watched clause " << c->clause_debug_string(w)
                   << " to see if it forces a unit";

            bool all_false = true;
            bool tombstones = false;
            if (!c->is_true(c->LIT1(w))) {
                for(size_t i = 2; i < c->SIZE(w); ++i) {
                    // If we see a false literal from level zero, go ahead and
                    // and remove it from the clause now by replacing it with a
                    // tombstone (Ex. 268)
                    lit_t ln = c->clauses[w + i].lit;
                    if (PARAM_remove_level_0_false_lits == 1 &&
                        c->is_false(ln) && c->lev[var(ln)] == 0) {
                        c->clauses[w + i].lit = lit_nil;
                        tombstones = true;
                        continue;
                    } else if (!c->is_false(ln)) {
                        all_false = false;
                        LOG(3) << "Setting " << ln << " as the watched literal "
                               << "in " << c->clause_debug_string(w);
                        std::swap(c->LIT0(w), c->clauses[w + i].lit);
                        c->add_to_watchlist(w, ln);
                        break;
                    }
                }
                // Compact any tombstones we just added to the clause.
                if (tombstones) {
                    size_t j = 2;
                    for(size_t i = 2; i < c->SIZE(w); ++i) {
                        if (c->clauses[w+i].lit != lit_nil) {
                            c->clauses[w+j].lit = c->clauses[w+i].lit;
                            ++j;
                        }
                    }
                    for(size_t i = j; i < c->SIZE(w); ++i) {
                        c->clauses[w+i].lit = lit_nil;
                    }
                    INC(tombstoned_level_0_lits, c->SIZE(w) - j);
                    c->clauses[w-1].size = j;
                }

                // If we only saw false literals, then it's up to LIT1: if it's
                // free, it's now forced to be true so we can add it to the
                // trail. If it's false, we've got a conflict. And if it's true,
                // we can just move on.
                if (all_false) {
                    if (c->is_false(c->LIT1(w))) {
                        LOG(3) << c->LIT1(w) << " false, entire clause false.";
                        watchlist_conflict = true;
                        break;
                    } else { // l1 is free
                        LOG(3) << "Adding " << c->LIT1(w) << " to the trail, "
                               << "forced by " << c->clause_debug_string(w);
                        c->add_to_trail(c->LIT1(w), w);
                    }
                }

            }

            if (all_false) {
                // All literals in w except LIT1 are false. In this case, it's
                // okay to keep w on -l's watchlist, since we need to track the
                // clause and there's nowhere else to put it.
                *wlp = w;
                wlp = &(c->LIT0(w) == -l ? c->WATCH0(w) : c->WATCH1(w));
            }

            w = nw;
        }

        // Finish surgery on -l's watchlist.
        *wlp = w;

        if (!watchlist_conflict) {
            LOG(3) << "Didn't find conflict in " << -l << "'s watchlist.";
            continue;
        }

        // C7: [Resolve a conflict]
        LOG(3) << "Found a conflict with d = " << c->d;
        c->seen_conflict = true;
        if (c->d == 0) return false;

        // Store the first conflict clause on each level. This is overkill if
        // we're not doing a full run, since there will only be one conflict.
        if (c->conflict[c->d] == clause_nil) c->conflict[c->d] = w;
        c->confp = c->d;

        if (c->full_runs > 0) {
            LOG(2) << "Doing a full run, continuing from conflict.";
            continue;
        }

        lit_t dpmin = c->d;
        c->trail_lits.clear();
        while (c->confp > 0) {
            w = c->conflict[c->confp];
            c->d = c->confp;
            // Decrement c->confp for the next round.
            while (c->confp > 0 && c->conflict[--c->confp] == clause_nil);

            // Find the literal in the clause with the highest trail position.
            // This is the literal where the conflict happened, so we'll want
            // to temporarily move it to the front of the clause before we blit
            // and then move it right back (since we may be temporarily
            // corrupting the watchlists by moving it to LIT0).
            size_t ti = 0, t = c->tloc[var(c->LIT0(w))];
            for (size_t i = 1; i < c->SIZE(w); ++i) {
                if (c->tloc[var(c->clauses[w+i].lit)] > t) {
                    ti = i;
                    t = c->tloc[var(c->clauses[w+i].lit)];
                }
            }

            lit_t dp = 0;
            clause_t q = 0;
            clause_t r = 0;
            c->epoch += 3;

            // Move the lit with the highest trail position to LIT0, blit, then
            // move the lit back in place.
            LOG(2) << "Starting resolution, trail: " << c->trail_debug_string();
            std::swap(c->LIT0(w), c->clauses[w+ti].lit);
            c->stamp[var(c->LIT0(w))] = c->epoch;
            c->heap.bump(var(c->LIT0(w)));
            LOG(2) << "Resolving, conflict: " << c->clause_debug_string(w);
            c->blit(w, &r, &dp, &q);
            std::swap(c->LIT0(w), c->clauses[w+ti].lit);

            // Move up the trail while there are still literals to process,
            // resolving reasons to create the learned clause.
            while (q > 0) {
                lit_t l = c->trail[t];
                t--;
                if (c->stamp[var(l)] == c->epoch) {
                    q--;
                    clause_t rc = c->reason[var(l)];
                    if (rc != clause_nil) {
                        c->force_lit0(l, rc);
                        LOG(2) << "Resolving: " << c->clause_debug_string(rc);
                        c->blit(rc, &r, &dp, &q);

                        if (PARAM_on_the_fly_subsumption == 1 &&
                            q + r + 1 < c->clauses[rc-1].size && q > 0) {
                            // On-the-fly subsumption.
                            c->remove_from_watchlist(rc, 0);
                            lit_t li = lit_nil;
                            lit_t len = c->clauses[rc-1].size;
                            // Avoid j == 1 below because we'd have to do more
                            // watchlist surgery. A lit of level >= d always
                            // exists in l_2 ... l_k since q > 0.
                            for (lit_t j = len - 1; j >= 2; --j) {
                                if (c->lev[var(c->clauses[rc+j].lit)] >= c->d) {
                                    li = j;
                                    break;
                                }
                            }
                            CHECK(li != lit_nil) <<
                                "No level " << c->d << " lit for subsumption";
                            c->clauses[rc].lit = c->clauses[rc+li].lit;
                            c->clauses[rc+li].lit = c->clauses[rc+len-1].lit;
                            c->clauses[rc+len-1].lit = lit_nil;
                            c->clauses[rc-1].size--;
                            c->clauses[rc-2].ptr = c->watch[c->clauses[rc].lit];
                            c->watch[c->clauses[rc].lit] = rc;
                            if (c->prooflog) {
                                for(size_t j = 0; j < c->SIZE(rc); ++j) {
                                    fprintf(c->prooflog, "%d ",
                                            c->clauses[rc+j].lit);
                                }
                                fprintf(c->prooflog, "0\n");
                            }
                            INC(on_the_fly_subsumptions);
                        }
                    }
                }
            }

            lit_t lp = c->trail[t];
            while (c->stamp[var(lp)] != c->epoch) { t--; lp = c->trail[t]; }

            // Remove redundant literals from clause
            if (PARAM_remove_redundant_literals == 1) {
                lit_t rr = 0;
                for(size_t i = 0; i < r; ++i) {
                    if (c->lstamp[c->lev[var(c->b[i])]] == c->epoch + 1 &&
                        c->redundant(-c->b[i])) {
                        continue;
                    }
                    c->b[rr] = c->b[i];
                    ++rr;
                }
                INC(redundant_literals, r - rr);
                r = rr;
            }

            bool subsumed = false;
            if (PARAM_predecessor_subsumption == 1 && lc != clause_nil) {
                // Ex. 271: Does this clause subsume the previous learned
                // clause? If so, we can "just" overwrite it. lc is the most
                // recent learned clause from a previous iteration.
                lit_t q = r+1;
                for (int j = c->clauses[lc-1].size - 1; q > 0 && j >= q; --j) {
                    lit_t v = var(c->clauses[lc+j].lit);
                    if (c->clauses[lc + j].lit == -lp ||
                        (c->stamp[v] == c->epoch && c->val[v] != UNSET &&
                         c->lev[v] <= dp)) {
                        --q;
                    }
                }

                if (q == 0 && c->val[var(c->clauses[lc].lit)] == UNSET) {
                    subsumed = true;
                    c->remove_from_watchlist(lc, 0);
                    c->remove_from_watchlist(lc, 1);
                    c->clauses.resize(lc - kHeaderSize);
                    INC(subsumed_clauses);
                }
            }

            if (c->confp == 0 &&
                !subsumed &&
                r > PARAM_trivial_clause_multiplier * dp) {
                // Ex. 269: If dp is significantly smaller than the length of
                // the learned clause, we can learn the trivial clause that
                // asserts that all dp + 1 of the decisions we made lead to a
                // conflict, i.e., ~(d1 AND d2 AND ... AND dp AND lp).
                // If we're unwinding conflicts during a full run, we should
                // only apply this optimization to the final conflict.
                r = dp;
                for (size_t j = 0; j < r; ++j) {
                    c->b[j] = c->trail[c->di[j+1]];
                }
                INC(trivial_clauses_learned);
            }

            lc = c->learn_clause(lp, r, dp);
            c->heap.rescale_delta();

            if (dp < dpmin) { c->trail_lits.clear(); }
            if (dp <= dpmin) {
                c->trail_lits.push_back(std::make_pair(-lp, lc));
            }
            dpmin = std::min(dpmin, dp);
        }

        // C8: [Backjump]
        c->backjump(dpmin);
        c->seen_conflict = false;

        // C9: [Learn]
        // This is slightly different than Knuth's C9 becuase we've incorporated
        // "full runs". Clause learning and delta rescaling would normally
        // happen here. Look for them right before step C8 instead.
        for (const auto& tl : c->trail_lits) {
            c->add_to_trail(tl.first, tl.second);
        }

        LOG(3) << "After clause install, trail is " << c->trail_debug_string();
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
    if (c.clauses.empty() || solve(&c)) {
        SAT_EXIT(&c);
    } else {
        PRINT << "s UNSATISFIABLE" << std::endl;
        return UNSATISFIABLE;
    }
}
