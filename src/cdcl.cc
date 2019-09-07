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
#define LIT1(c) (clauses[c+1].lit)
#define LIT0(c) (clauses[c].lit)
#define SIZE(c) (clauses[c-1].size)
#define WATCH0(c) (clauses[c-2].ptr)
#define WATCH1(c) (clauses[c-3].ptr)

// During a lemma database reduction, we'll temporarily re-purpose some of the
// watchlist pointer storage to tag clauses that we want to keep and to store
// the literal block distance of the clause.
#define PIN(c) (clauses[c-2].lit)
#define LBD(c) (clauses[c-3].lit)

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

DEFINE_PARAM(partial_restart_prob, 1.0,
             "When restarting, probability that we attempt to find a higher "
             "non-zero level to backjump to.");

// Setting this to a non-zero value enables the optimization described in
// Exercise 266 (Random selection of decisions).
DEFINE_PARAM(peek_prob, 0.02,
             "Probability that we'll randomly select a decision literal "
             "instead of using the one with maximum activity.");

DEFINE_PARAM(phase_flip_prob, 0.02,
             "Probability that we'll flip the phase of a decision variable "
             "to the opposite of what the saved phase suggests.");

DEFINE_PARAM(oval_flip_on_restart_prob, 0.0,
             "Probability that we'll flip all phases of all literals when "
             "a restart happens.");

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
        INC("phase changes", phase_change ? 0 : 1);
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
    // Array of all clauses. Consists of both clauses in the original formula
    // and lemmas learned by CDCL. All learned lemmas appear after original
    // clauses. The comment above clause_elem_t describes the layout.
    std::vector<clause_elem_t> clauses;

    // The current value of a variable: either TRUE, FALSE, or UNSET.
    std::vector<State> val;

    // The level on which a variable was set. Level 0 contains variables forced
    // by unit clauses.
    std::vector<lit_t> lev;

    // The previous value of a variable. Initialized to all FALSE. Used for
    // phase-saving.
    std::vector<State> oval;

    
    std::vector<unsigned long> stamp;  // TODO: what's the right type here?

    std::vector<unsigned long> lstamp;  // maps levels to stamp values

    std::vector<clause_t> conflict;  // first conflict clause by level.
    
    Heap heap;

    std::vector<lit_t> trail;  // TODO: make sure we're not dynamically resizing during backjump
    // inverse map from literal to trail index. -1 if there's no index in trail.
    std::vector<lit_t> tloc;  // variables -> trail locations; -1 == nil
    size_t f;  // trail length
    size_t g;  // index in trail

    std::vector<size_t> di; // maps d -> first trail position of level d. if
                            // di[0] == di[1], there are no level 0 lits.
    
    std::vector<clause_t> reason;  // Keys: variables, values: clause indices

    std::vector<clause_t> watch_storage;
    clause_t* watch; // Keys: litarals, values: clause indices

    std::vector<lit_t> b;  // temp storage for learned clause

    // Used in full runs to keep track of all the lits + reasons at the
    // highest backjump level;
    std::vector<std::pair<lit_t, clause_t>> trail_lits;
    
    lit_t nvars;

    // TODO: explain epoch values here, why they're bumped by 3 each time.
    unsigned long epoch;

    size_t nlemmas;

    clause_t lemma_start;  // clause index of first learned clause.

    lit_t d; // level

    size_t full_runs;

    lit_t confp; // ptr to most recent entry in conflict array.

    bool seen_conflict; // have we seen a conflict in this search path?

    // A black box that tells us when to restart. Every time a literal is
    // assigned a value, we tell this oracle about it. Every time we learn
    // a new lemma, we ask it if we should restart.
    restart_oracle agility;

    size_t npurges;
    
    Cnf(lit_t nvars) :
        val(nvars + 1, UNSET),
        lev(nvars + 1, -1),
        oval(nvars + 1, FALSE),
        stamp(nvars + 1, 0),
        lstamp(nvars + 1, 0),
        conflict(nvars + 1, clause_nil),
        heap(nvars),
        trail(nvars + 1, -1),
        tloc(nvars + 1, -1),
        f(0),
        g(0),
        di(nvars + 1, 0),
        reason(nvars + 1, clause_nil),
        watch_storage(2 * nvars + 1, clause_nil),
        watch(&watch_storage[nvars]),
        b(nvars, -1),
        trail_lits(nvars),
        nvars(nvars),
        epoch(0),
        nlemmas(0),
        d(0),
        full_runs(PARAM_warm_up_runs),
        confp(0),
        seen_conflict(false),
        agility(PARAM_restart_sensitivity),
        npurges(0) {
    }

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

    std::string print_clause(clause_t c) const {
        std::ostringstream oss;
        oss << "(";
        for (size_t i = 0; i < SIZE(c); ++i) {
            oss << clauses[c+i].lit;
            if (i != SIZE(c) - 1) oss << " ";
        }
        oss << ")";
        return oss.str();
    }

    void for_each_clause_helper(clause_t start,
                                std::function<void(clause_t,clause_t)> func) {
        clause_t ts = 0;
        clause_t os = 0;
        for(clause_t i = start - 1; i < clauses.size();
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
    
    std::string dump_clauses() {
        std::ostringstream oss;
        for_each_clause([&](clause_t c, clause_t cs) {
            oss << print_clause(c) << " "; 
        });
        return oss.str();
    }

    std::string dump_lemmas() {
        std::ostringstream oss;
        for_each_lemma([&](clause_t c, clause_t cs) {
            oss << print_clause(c) << " ";
        });
        return oss.str();
    }    

    std::string print_trail() {
        std::ostringstream oss;
        for (size_t i = 0; i < f; ++i) {
            oss << "[" << trail[i] << ":" << lev[var(trail[i])] << "]";
        }
        return oss.str();
    }

    std::string print_watchlist(lit_t l) {
        std::ostringstream oss;
        for (clause_t c = watch[l]; c != clause_nil;
             clauses[c].lit == l ? (c = WATCH0(c)) : (c = WATCH1(c))) {
            oss << "[" << c << "] " << print_clause(c) << " ";
        }
        return oss.str();
    }

    bool redundant(lit_t l) {
        lit_t k = var(l);
        clause_t r = reason[k];
        if (r == clause_nil) {
            return false;
        }
        for (size_t i = 0; i < SIZE(r); ++i) {
            lit_t a = clauses[r+i].lit;
            lit_t v = var(a);
            if (k == v) continue;
            if (lev[v] == 0) continue;
            if (stamp[v] == epoch + 2) {
                return false;
            }
            if (stamp[v] < epoch &&
                (lstamp[lev[v]] < epoch || !redundant(a))) {
                stamp[v] = epoch + 2;
                return false;
            }
        }
        stamp[k] = epoch + 1;
        return true;
    }

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
        lit_t l = cindex + offset;
        clause_t* x = &watch[clauses[l].lit];
        while (*x != static_cast<clause_t>(cindex)) {
            if (LIT0(*x) == clauses[l].lit) {
                x = (clause_t*)(&WATCH0(*x));
            } else /* LIT1(*x) == clauses[l].lit */ {
                x = (clause_t*)(&WATCH1(*x));
            }
        }
        *x = LIT0(*x) == clauses[l].lit ? WATCH0(*x) : WATCH1(*x);
    }

    // t: if non-null, will be set to the max tloc of any var in the clause.
    void blit(clause_t c, size_t* r, lit_t* dp, size_t* q, lit_t* t) {
        if (t != nullptr) *t = tloc[var(LIT0(c))];
        for(size_t j = 1; j < SIZE(c); ++j) {
            lit_t m = clauses[c+j].lit;
            lit_t v = var(m);
            if (t != nullptr && tloc[v] >= *t) *t = tloc[v];
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
        tloc[k] = f;
        trail[f] = l;
        ++f;
        val[k] = l < 0 ? FALSE : TRUE;
        lev[k] = d;
        reason[k] = r;
        agility.bump(oval[k] == val[k]);
    }

    void backjump(lit_t level) {
        while (f > di[level+1]) {
            f--;
            lit_t k = var(trail[f]);
            oval[k] = val[k];
            val[k] = UNSET;
            reason[k] = clause_nil;
            conflict[lev[k]] = clause_nil;
            heap.insert(k);
        }
        g = f;
        d = level;
    }

    clause_t learn_clause(lit_t lp, size_t r, lit_t dp) {
        clause_elem_t nil_ptr;  // TODO: make constant
        nil_ptr.ptr = clause_nil;
        clauses.push_back(nil_ptr); // watch list for l1
        clause_elem_t wlp;
        wlp.ptr = watch[-lp];
        clauses.push_back(wlp); // watch list for l0
        clause_elem_t s;
        s.size = r+1;
        clauses.push_back(s); // size
        LOG(3) << "adding a clause of size " << r+1;
        clause_t lc = clauses.size();
        clauses.push_back({-lp});
        add_to_watchlist(lc, -lp); // watch[-lp] = lc;
        clauses.push_back({lit_nil}); // clauses[lc+1], to be set in else below
        bool found_watch = false;
        for (size_t j = 0; j < r; ++j) {
            if (found_watch || lev[var(b[j])] < dp) {
                clauses.push_back({-b[j]});
            } else {
                clauses[lc+1].lit = -b[j];
                //clauses[lc-3].ptr = watch[-b[j]];
                // watch[-b[j]] = lc;
                add_to_watchlist(lc, -b[j]); 
                found_watch = true;
            }
        }
        CHECK(r == 0 || found_watch) << "Didn't find watched lit in new clause";
        CHECK_NO_OVERFLOW(clause_t, clauses.size());

        ++nlemmas;
        LOG(2) << "Successfully added clause " << print_clause(lc);
        LOG(2) << "trail: " << print_trail();
        INC("learned clause literals", r+1);
        INC("learned clauses");
        return lc;
    }

    // Use W1(c) as LBD, use W0(c) as pin.
    // First, pin everything used as a reason.
    // Next, iterate through all clauses, computing LBD and storing in W1
    //    and computing LBD histogram.
    //    - Figure out max LBD we can keep and # clauses from max level
    // Next, iterate in reverse, pinning clauses
    // Next, clear watch_storage array
    // Next, iterate forward, compacting all pinned clauses and computing
    // watchlist
    void reduce_db() {
        Timer t("clause database purges");
        std::vector<clause_t> lbds(d+2, 0);
        std::vector<clause_t> hist(d+2, 0);  // lbd histogram.
        size_t target_lemmas = nlemmas * PARAM_reduce_db_fraction;
        
        for_each_lemma([&](clause_t c, clause_t cs) {
          PIN(c) = 2; // >= 2 == not pinned
          LBD(c) = 2;
        });
        
        // Pin learned clauses that are reasons. Note PIN(c) <= 1 means pin;
        // 1 will never be a watch pointer because 1 < kHeaderSize.
        for (size_t i = 0; i < f; ++i) {
            lit_t v = var(trail[i]);
            if (reason[v] == clause_nil) continue;
            if (reason[v] < lemma_start) continue;
            PIN(reason[v]) = -v;
            if (target_lemmas > 0) --target_lemmas;
        }

        // Pin any small clauses. For anything else,
        // Compute LBD, store in W1(c). Store lemma indexes of LBD candidates so
        // we can iterate in reverse over clauses next.        
        std::vector<lit_t> lemma_indexes;
        for_each_lemma([&](clause_t c, clause_t cs) {
            if (target_lemmas == 0) return; // continue
            if (PIN(c) < 0) return; // continue, already pinned
            if (cs < PARAM_min_purged_clause_size && PIN(c) > 1) {
                PIN(c) = 1;
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

        INC("LBD purge budget", target_lemmas);
        int max_lbd = 1;
        size_t total_lemmas = 0;
        while (max_lbd <= d && total_lemmas + hist[max_lbd] <= target_lemmas) {
            total_lemmas += hist[max_lbd];
            ++max_lbd;
        }
        int max_lbd_budget = target_lemmas - total_lemmas;
        
        // Mark clauses we want to keep because of LBD.
        for(size_t i = 0; i < lemma_indexes.size(); ++i) {
            lit_t lc = lemma_indexes[lemma_indexes.size() - i - 1];
            if (PIN(lc) < 2) continue; // already pinned
            if (LBD(lc) == max_lbd && max_lbd_budget > 0) {
                PIN(lc) = 1;
                --max_lbd_budget;
            } else if (LBD(lc) < max_lbd) {
                PIN(lc) = 1;
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
            if (PIN(c) > 1) return;  // continue
            if (PIN(c) < 0) {
                reason[var(PIN(c))] = tail;
            }
            WATCH1(tail) = 1;  // placeholder, anything != 0
            PIN(tail) = 1;  // placeholder, anything != 0
            SIZE(tail) = cs;
            for(size_t j = 0; j < cs; ++j) {
                clauses[tail+j].lit = clauses[c+j].lit;
            }
            tail += cs + kHeaderSize;
            ++nlemmas;
        });
        clauses.resize(tail - kHeaderSize);

        // Recompute all watch lists
        for_each_clause([&](clause_t c, clause_t cs) {
            if (cs > 1) {
                add_to_watchlist(c, LIT0(c));
                add_to_watchlist(c, LIT1(c));
            }
        });
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
    Timer t("parse");
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
    
    // Initialize data structures now that we know nvars.
    Cnf c(static_cast<lit_t>(nvars));

    // Read clauses until EOF.
    int lit;
    do {
        bool read_lit = false;
        clause_elem_t nil_ptr;  // TODO: make these constants
        nil_ptr.ptr = clause_nil;
        clause_elem_t zero_size;
        zero_size.size = 0;
        c.clauses.push_back(nil_ptr);  // watch ptr for clause's second lit
        c.clauses.push_back(nil_ptr);  // watch ptr for clause's first lit
        c.clauses.push_back(zero_size);  // size of clause. filled in below.
        std::size_t start = c.clauses.size();
        while (true) {
            nc = fscanf(f, " %i ", &lit);
            if (nc == EOF || lit == 0) break;
            c.clauses.push_back({lit});
            read_lit = true;
        }
        int cs = c.clauses.size() - start;
        if (cs == 0 && nc != EOF) {
            LOG(2) << "Empty clause in input file, unsatisfiable formula.";
            UNSAT_EXIT;
        } else if (cs == 0 && nc == EOF) {
            // Clean up from (now unnecessary) c.clauses.push_backs above.
            for(clause_t i = 0; i < kHeaderSize; ++i) { c.clauses.pop_back(); }
        } else if (cs == 1) {
            lit_t x = c.clauses[c.clauses.size() - 1].lit;
            LOG(3) << "Found unit clause " << x;
            State s = x < 0 ? FALSE : TRUE;
            lit_t v = var(x);
            if  (c.val[v] != UNSET && c.val[v] != s) {
                LOG(2) << "Contradictory unit clauses, unsatisfiable formula.";
                UNSAT_EXIT;
            }
            c.val[v] = s;
            c.tloc[v] = c.f;
            c.trail[c.f++] = x;
            c.lev[v] = 0;
        } 
        if (!read_lit) break;
        CHECK(cs > 0);
        // Record the size of the clause in offset -1.
        c.clauses[start - 1].size = cs;
        // Set watch lists for non-unit clauses.
        if (cs > 1) {
            c.add_to_watchlist(start, c.clauses[start].lit);
            c.add_to_watchlist(start, c.clauses[start+1].lit);
        }
    } while (nc != EOF);

    if (c.clauses.empty()) {
        LOG(2) << "No clauses, unsatisfiable.";
        UNSAT_EXIT;
    }
    fclose(f);
    c.lemma_start = c.clauses.size() + kHeaderSize;
    return c;
}


// Returns true exactly when a satisfying assignment exists for c.
bool solve(Cnf* c) {
    Timer t("solve");
    clause_t lc = clause_nil;  // The most recent learned clause

    while (true) {
        // (C2)
        LOG(3) << "C2";

        if (c->f == c->g) {
            LOG(3) << "C5";
            
            // C5
            if (!c->seen_conflict && c->f == static_cast<size_t>(c->nvars)) {
                return true;
            }

            size_t max_lemmas =
                PARAM_max_lemmas + c->npurges * PARAM_max_lemmas_delta;
            if (c->nlemmas >= max_lemmas &&
                c->f < static_cast<size_t>(c->nvars) &&
                c->full_runs == 0) {
                LOG(1) << "Clause database too big, scheduling a full run.";
                c->full_runs = 1;
            } else if (c->nlemmas >= max_lemmas &&
                       c->f == static_cast<size_t>(c->nvars)) {
                LOG(1) << "Reducing clause database at epoch " << c->epoch
                       << ", starting size = " << c->nlemmas;
                c->reduce_db();
                c->npurges++;
                LOG(1) << "Clause database reduced to size = " << c->nlemmas;
                lc = clause_nil;  // disable subsume prev clause for next iter
                INC("clause database purges");
            }

            if (c->agility.should_restart() &&
                !c->seen_conflict &&  // TODO: !seen_conflict && full_runs == 0 redundant?
                c->full_runs == 0) {
                // Find lowest level where choices will substantially differ.
                lit_t dp = 0;
                if (flip(PARAM_partial_restart_prob)) {
                    // Find unset var of max activity.
                    lit_t vmax = c->heap.peek();
                    while (c->val[vmax] != UNSET) {
                        c->heap.delete_max();
                        vmax = c->heap.peek();
                    }
                    double amax = c->heap.act(vmax);

                    while(dp < c->d &&
                          c->heap.act(c->trail[c->di[dp+1]]) >= amax) ++dp;
                }

                if (flip(PARAM_oval_flip_on_restart_prob)) {
                    for (int k = 1; k < c->nvars; ++k) {
                        c->oval[var(k)] =
                            (c->oval[var(k)] == FALSE) ? TRUE : FALSE;
                    }
                }

                if (dp < c->d) {
                    LOG(1) << "Agility-driven restart at epoch " << c->epoch
                           << " (level " << c->d << " -> " << dp << ")";
                    c->backjump(dp);
                    c->full_runs = PARAM_warm_up_runs;
                    INC("agility restarts");
                    continue;
                } else {
                    INC("aborted agility restarts");
                }
            }

            if (c->seen_conflict && c->f == static_cast<size_t>(c->nvars)) {
                INC("full runs");
                --c->full_runs;
                LOG(1) << "Full run done. " << c->full_runs << " runs left.";
                c->backjump(0);
                c->seen_conflict = false;
            }            
            
            ++c->d;
            c->di[c->d] = c->f;
            
            // C6
            INC("decisions");
            lit_t k = flip(PARAM_peek_prob) ?
                c->heap.rpeek() : c->heap.delete_max();
            while (c->val[k] != UNSET) {
                LOG(3) << k << " set, rolling again";
                k = flip(PARAM_peek_prob) ?
                    c->heap.rpeek() : c->heap.delete_max();
            }
            CHECK(k != lit_nil) << "Got nil from heap::delete_max in step C6!";
            LOG(3) << "Decided on variable " << k;
            lit_t l = c->oval[k] == FALSE ? -k : k;
            if (flip(PARAM_phase_flip_prob)) {
                INC("forced phase flips");
                l = -l;
            }
            LOG(3) << "Adding " << l << " to the trail.";
            c->add_to_trail(l, clause_nil);
        }

        // C3
        LOG(3) << "C3";
        LOG(3) << "Trail: " << c->print_trail();

        lit_t l = c->trail[c->g];
        LOG(3) << "Examining " << -l << "'s watch list";
        ++c->g;
        clause_t w = c->watch[-l];
        clause_t wll = clause_nil;
        bool found_conflict = false;
        while (w != clause_nil) {

            // C4
            LOG(3) << "C4: l = " << l << ", clause = " << c->print_clause(w);
            if (c->clauses[w].lit != -l) {
                // Make l0 first literal in the clause instead of the second.
                std::swap(c->clauses[w].lit, c->clauses[w+1].lit);
                std::swap(c->clauses[w-2].ptr, c->clauses[w-3].ptr);
            }
            clause_t nw = c->clauses[w-2].ptr;
            LOG(3) << "Looking at watched clause " << c->print_clause(w)
                   << " to see if it forces a unit";
            
            bool all_false = true;
            bool tombstones = false;
            if (!c->is_true(c->clauses[w+1].lit)) {
                for(size_t i = 2; i < c->clauses[w-1].size; ++i) {
                    // If we see a false literal from level zero, go ahead and
                    // and remove it from the clause now by replacing it with a
                    // tombstone (Ex. 268)
                    if (PARAM_remove_level_0_false_lits == 1 &&
                        c->is_false(c->clauses[w + i].lit) &&
                        c->lev[var(c->clauses[w + i].lit)] == 0) {
                        c->clauses[w + i].lit = lit_nil;
                        tombstones = true;
                        continue;
                    } else if (!c->is_false(c->clauses[w + i].lit)) {
                        all_false = false;
                        lit_t ln = c->clauses[w + i].lit;
                        LOG(3) << "Resetting " << ln
                               << " as the watched literal in " << c->print_clause(w);
                        // swap ln and l0
                        std::swap(c->clauses[w].lit, c->clauses[w + i].lit);
                        // move w onto watch list of ln
                        // TODO: clauses and watch are lit_t and clause_t, resp.
                        //       clean up so we can std::swap here.
                        LOG(4) << "Before putting " << c->print_clause(w)
                               << " on " << ln << "'s watch list: "
                               << c->print_watchlist(ln);
                        c->add_to_watchlist(w, ln);
                        break;
                    }
                }
                // Compact any tombstones we just added to the clause
                // TODO: rewrite this compaction
                if (tombstones) {
                    size_t j = 2;
                    for(size_t i = 2; i < c->clauses[w-1].size; ++i) {
                        if (c->clauses[w+i].lit != lit_nil) {
                            if (i != j) {
                                c->clauses[w+j].lit = c->clauses[w+i].lit;
                            }
                            ++j;
                        }
                    }
                    for(size_t i = j; i < c->clauses[w-1].size; ++i) {
                        c->clauses[w+i].lit = lit_nil;
                    }
                    if (j < c->clauses[w-1].size) {
                        INC("tombstoned-level-0-lits", c->clauses[w-1].size-j);
                        c->clauses[w-1].size = j;
                    }
                }
                
                if (all_false) {
                    if (c->is_false(c->clauses[w+1].lit)) {
                        LOG(3) << c->clauses[w+1].lit
                               << " false, everything false! (-> C7)";
                        found_conflict = true;
                        break;
                    } else { // l1 is free
                        lit_t l1 = c->clauses[w+1].lit;
                        LOG(3) << "Adding " << l1 << " to the trail, "
                               << "forced by " << c->print_clause(w);
                        c->add_to_trail(l1, w);
                    }
                }

            }

            if (all_false) {
                if (wll == clause_nil) {
                    LOG(4) << "Setting watch[" << -l << "] = "
                           << c->print_clause(w);
                    c->watch[-l] = w;
                }
                else {
                    LOG(4) << "Linking " << -l << "'s watchlist: "
                           << c->print_clause(wll) << " -> " << c->print_clause(w);
                    c->clauses[wll-2].ptr = w;
                }
                wll = w;
            }
                
            LOG(3) << "advancing " << w << " -> " << nw << " with wll=" << wll;
            w = nw;  // advance watch list traversal.
            
            if (w == clause_nil) { LOG(3) << "Hit clause_nil in watch list"; }
            else { LOG(3) << "Moving on to " << c->print_clause(w); }
        }

        // Finish surgery on watchlist
        if (wll == clause_nil) {
            LOG(3) << "Final: Setting watch[" << -l << "] = "
                   << ((w == clause_nil) ? "0" : c->print_clause(w));
            c->watch[-l] = w;
        }
        else {
            LOG(3) << "Final: Linking " << -l << "'s watchlist: "
                   << c->print_clause(wll)
                   << " -> " << ((w == clause_nil) ? "0" : c->print_clause(w));
            c->clauses[wll-2].ptr = w;
        }
        
        if (!found_conflict) {
            LOG(3) << "Didn't find conflict, moving on.";
            continue;
        }

        // C7
        LOG(3) << "Found a conflict with d = " << c->d;
        c->seen_conflict = true;
        if (c->d == 0) return false;

        // Store the first conflict clause on each level.
        if (c->conflict[c->d] == clause_nil) c->conflict[c->d] = w;
        c->confp = c->d;
        
        if (c->full_runs > 0) {
            // Doing a full run so keep propagating.
            LOG(2) << "doing a full run, continuing from conflict";
            continue;
        }

        lit_t dpmin = c->d;
        c->trail_lits.clear();
        while (c->confp > 0) {
            LOG(2) << "starting loop with confp = " << c->confp;
            w = c->conflict[c->confp];
            c->d = c->confp;
            // decrement c->confp for the next round.
            while (c->confp > 0 && c->conflict[--c->confp] == clause_nil);
            LOG(2) << "decremented confp to " << c->confp << " for next round";
        
            // (*) Not mentioned in Knuth's description, but we need to make sure
            // that the rightmost literal on the trail contained in the clause is
            // the first literal in the clause here. We'll undo this after the
            // first resolution step below, otherwise watchlists get corrupted.
            size_t rl = c->f - 1;
            size_t cs = c->clauses[w-1].size;
            size_t rl_pos = 0;
            for (bool done = false; !done; --rl) {
                for (rl_pos = 0; rl_pos < cs; ++rl_pos) {
                    if (var(c->trail[rl]) == var(c->clauses[w+rl_pos].lit)) {
                        done = true;
                        std::swap(c->clauses[w].lit, c->clauses[w+rl_pos].lit);
                        break;
                    }
                }
            }
            
            lit_t dp = 0;
            size_t q = 0;
            size_t r = 0;
            c->epoch += 3;
            LOG(3) << "Bumping epoch to " << c->epoch << " at "
                   << c->print_clause(w);
            LOG(3) << "Trail is " << c->print_trail();
            c->stamp[var(c->clauses[w].lit)] = c->epoch;
            c->heap.bump(var(c->clauses[w].lit));
            
            lit_t t;
            LOG(3) << "RESOLVING [A] " << c->print_clause(w);
            c->blit(w, &r, &dp, &q, &t);
            
            LOG(3) << "swapping back: " << c->print_clause(w);
            std::swap(c->clauses[w].lit, c->clauses[w+rl_pos].lit);
            LOG(3) << "now: " << c->print_clause(w);
            
            while (q > 0) {
                LOG(3) << "q=" << q << ",t=" << t;
                lit_t l = c->trail[t];
                t--;
                //LOG(3) << "New L_t = " << c->trail[t];
                if (c->stamp[var(l)] == c->epoch) {
                    LOG(3) << "Stamped this epoch: " << l;
                    q--;
                    clause_t rc = c->reason[var(l)];
                    if (rc != clause_nil) {
                        LOG(3) << "RESOLVING [B] " << c->print_clause(rc);
                        if (c->clauses[rc].lit != l) {
                            // TODO: don't swap here (or similar swap above) 
                            std::swap(c->clauses[rc].lit, c->clauses[rc+1].lit);
                            std::swap(c->clauses[rc-2].ptr, c->clauses[rc-3].ptr);
                        }                        
                        LOG(3) << "Reason for " << l << ": " << c->print_clause(rc);
                        c->blit(rc, &r, &dp, &q, nullptr);                    
                        
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
                            INC("on-the-fly subsumptions");
                        }
                    }
                }
            }
            
            lit_t lp = c->trail[t];
            while (c->stamp[var(lp)] != c->epoch) { t--; lp = c->trail[t]; }
            
            // Remove redundant literals from clause
            // TODO: move this down so that we only process learned clause once? But
            // would also have to do subsumption check in single loop...
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
                INC("redundant literals", r - rr);
                r = rr;
            }
            
            bool subsumed = false;
            if (PARAM_predecessor_subsumption == 1 && lc != clause_nil) {
                // Ex. 271: Does this clause subsume the previous learned clause? If
                // so, we can "just" overwrite it. lc is the most recent learned
                // clause from a previous iteration.
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
                    INC("subsumed clauses");
                }
            }
            
            if (c->confp == 0 &&
                !subsumed &&
                r > PARAM_trivial_clause_multiplier * static_cast<size_t>(dp)) {
                // Ex. 269: If dp is significantly smaller than the length of
                // the learned clause, we can learn the trivial clause that
                // asserts that all dp + 1 of the decisions we made lead to a
                // conflict, i.e., ~(d1 AND d2 AND ... AND dp AND lp).
                // If we're unwinding conflicts during a full run, we should
                // only apply this optimization to the final conflict.
                r = static_cast<size_t>(dp);
                for (size_t j = 0; j < r; ++j) {
                    c->b[j] = c->trail[c->di[j+1]];
                }
                INC("trivial clauses learned");
            }

            lc = c->learn_clause(lp, r, dp);
            c->heap.rescale_delta();
            
            if (dp < dpmin) { c->trail_lits.clear(); }
            if (dp <= dpmin) {
                c->trail_lits.push_back(std::make_pair(-lp, lc));
            }
            dpmin = std::min(dpmin, dp);
        }
            
        // C8: backjump
        LOG(2) << "Before backjump, trail is " << c->print_trail();        
        c->backjump(dpmin);
        c->seen_conflict = false;
        LOG(2) << "After backjump, trail is " << c->print_trail();

        // C9: learn
        // This is slightly different than Knuth's C9 becuase we've incorporated
        // "full runs". Clause learning and delta rescaling would normally
        // happen here. Look for them right before step C8 instead.
        for (const auto& tl : c->trail_lits) {
            c->add_to_trail(tl.first, tl.second);
        }
        
        LOG(3) << "After clause install, trail is " << c->print_trail();
    }

    return true;
}

int main(int argc, char** argv) {
    int oidx;
    CHECK(parse_flags(argc, argv, &oidx)) <<
        "Usage: " << argv[0] << " <filename>";
    init_counters();
    init_timers();
    Cnf c = parse(argv[oidx]);
    // TODO: also check for no clauses (unsatisfiable) in the if
    // statement below.
    if (solve(&c)) {
        std::cout << "s SATISFIABLE" << std::endl;
        for (int i = 1, j = 0; i <= c.nvars; ++i) {
            if (c.val[i] == UNSET) continue;
            if (j % 10 == 0) std::cout << "v";
            std::cout << ((c.val[i] & 1) ? " -" : " ") << i;
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
