// Algorithm L from Knuth's The Art of Computer Programming 7.2.2.2:
// DPLL with Lookahead.

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
             "Constant multiplicative factor used in computing heuristic "
             "literal scores.");

DEFINE_PARAM(c0, 30,
             "Defines maximum number of candidates considered for lookahead. "
             "See also c1, since max(c0, c1/d) is the actual bound.");

DEFINE_PARAM(c1, 600,
             "Defines maximum number of candidates considered for lookahead. "
             "See also c0, since max(c0, c1/d) is the actual bound.");

DEFINE_PARAM(disable_lookahead, 0.0,
             "If 1, no lookahead (Algorithm X) will be performed.");

DEFINE_PARAM(add_windfalls, 1.0,
             "If 1, generate 'windfall' clauses during lookahead (see (72)).");

// Real truth
constexpr uint32_t RT = std::numeric_limits<uint32_t>::max() - 1;  // 2^32 - 2
// Near truth
constexpr uint32_t NT = std::numeric_limits<uint32_t>::max() - 3;  // 2^32 - 4
// Proto truth
constexpr uint32_t PT = std::numeric_limits<uint32_t>::max() - 5;  // 2^32 - 6
// Nil truth : never used as a truth value
constexpr uint32_t nil_truth = 0;

std::string tval(uint32_t t) {
    if (t == RT+1) return "RF";
    if (t == RT) return "RT";
    if (t == NT+1) return "NF";
    if (t == NT) return "NT";
    if (t == PT+1) return "PT";
    if (t == PT) return "PT";
    if (t == nil_truth) return "nil";
    std::ostringstream oss;
    oss << t;
    oss << ((t % 2) == 0 ? "T" : "F");
    return oss.str();
}

// Bits in signature of decision path used for identifying participants/newbies.
constexpr lit_t kPathBits = 64;

struct timp_t {
    lit_t u;
    lit_t v;

    // Use c.timp[-u][link] to cycle through the other two timps corresponding
    // to the original ternary clause.
    size_t link;

    bool active;
};

struct istack_frame_t {
    lit_t l;
    size_t bsize;
};

struct psig_t {
    uint64_t path;
    lit_t length;
};

struct dfs_t {
    dfs_t() : H(0.0), parent(lit_nil), seen(false), cand(false) {}

    double H;
    lit_t parent;
    bool seen;
    bool cand;
};

struct lookahead_order_t {
    lit_t lit;
    uint32_t t;
};

// Cycles through timps corresponding to the same clause.
// c->LINK(c->LINK(c->LINK(t))) == t.
#define LINK(t) timp[-t.u][t.link]

// Storage for the DPLL search and the final assignment, if one exists.
struct Cnf {
    // Number of variables in the original problem. These are the first
    // nvars variables in the value array.
    lit_t novars;

    std::vector<std::vector<lit_t>> bimp_storage;
    std::vector<lit_t>* bimp;

    std::vector<std::vector<timp_t>> timp_storage;
    std::vector<timp_t>* timp;

    std::vector<std::vector<lit_t>> big_storage;
    std::vector<lit_t>* big; // binary implication graph, used for lookahead.

    // heuristic scores, maps lit -> score. hnew is used for scratch for
    // computing the next round of scores, then swapped.
    std::vector<double> h_storage;
    double* h;
    std::vector<double> hnew_storage;
    double* hnew;

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

    std::vector<lit_t> dec;  // maps d -> decision literal

    std::vector<lit_t> backf;  // maps d -> f at the time decision d was made.

    std::vector<uint64_t> backi;  // maps d -> istack size when dec. d was made.

    std::vector<istack_frame_t> istack;

    std::vector<uint32_t> val;  // maps variables -> truth values

    std::vector<psig_t> sig;  // to identify participants/newbies

    Heap cand;  // lookahead candidates

    uint64_t sigma; // branch signature, to compare against sig[var(l)] above

    lit_t d;  // current search depth

    size_t f;  // index into rstack, number of fixed variables.

    size_t g;  // really true stacked literals.

    uint64_t istamp;

    // TODO: do i need global t, or should it just be an arg passed
    // in to propagate?
    uint32_t t; // current truth level (RT, NT, PT, etc)

    Cnf(lit_t novars, lit_t nsvars) :
        novars(novars),
        bimp_storage(2 * (novars + nsvars) + 1),
        bimp(&bimp_storage[novars + nsvars]),
        timp_storage(2 * (novars + nsvars) + 1),
        timp(&timp_storage[novars + nsvars]),
        big_storage(2 * (novars + nsvars) + 1),
        big(&big_storage[novars + nsvars]),
        h_storage(2 * (novars + nsvars) + 1, 1),
        h(&h_storage[novars + nsvars]),
        hnew_storage(2 * (novars + nsvars) + 1),
        hnew(&hnew_storage[novars + nsvars]),
        dfs_storage(2 * (novars + nsvars) + 1),
        dfs(&dfs_storage[novars + nsvars]),
        lookahead_order(novars + nsvars),
        branch(novars + nsvars + 1, -1), // TODO: how to initialize?
        freevar(novars + nsvars),
        invfree(novars  + nsvars + 1),
        istamps_storage(2 * (novars + nsvars) + 1),
        istamps(&istamps_storage[novars + nsvars]),
        dec(novars + nsvars + 1),
        backf(novars + nsvars + 1),
        backi(novars + nsvars + 1),
        val(novars + nsvars + 1, 0),
        sig(novars + nsvars + 1, psig_t{path: 0, length: -1}),
        cand(novars + nsvars),
        sigma(0),
        d(0),
        f(0),
        g(0),
        istamp(0),
        t(0) {
        for (lit_t i = 0; i < novars + nsvars; ++i) {
            freevar[i] = i + 1;
            invfree[i + 1] = i;
        }
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
        CHECK(v > 0) << "wanted var in make_free, got lit";
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
        return p.length >= 0 && p.length <= d &&
            p.path == (sigma & ((1 << std::min(p.length, kPathBits)) - 1));
    }

    void sigma_stamp(lit_t l) {
        if (participant(l)) return;
        sig[var(l)] = psig_t{path: sigma, length: d};
    }

    // TODO: keep 2D array of h by level, use previous level to refine current.
    void refine_heuristic_scores() {
        double avg = 0.0;
        for (lit_t l = 1; l <= nvars(); ++l) {
            avg += h[l] + h[-l];
        }
        avg /= 2 * nvars();
        for (lit_t l = -nvars(); l <= nvars(); ++l) {
            if (l == 0) continue;
            double bimpsum = 0.0;
            for (lit_t lp : bimp[l]) {
                if (fixed(lp)) continue;
                bimpsum += h[lp];
            }
            double timpsum = 0.0;
            for (const timp_t& t : timp[l]) {
                if (!t.active) continue;
                timpsum += h[t.u] * h[t.v];
            }
            hnew[l] = 0.1 + PARAM_alpha*bimpsum/avg + timpsum/(avg*avg);
        }
        std::swap(h, hnew);
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

// Returns false if a conflict was found.
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

// Does L5 - L9
// Returns lit to try if there was a conflict, lit_nil otherwise
// TODO: just make a member function of Cnf
lit_t accept_near_truths(Cnf* c) {
    // L5. [Accept near truths.]
    c->t = NT;
    c->rstack.resize(c->f);  // TODO: do i need this?
    c->g = c->f;
    ++c->istamp;
    // TODO: CONFLICT = L11

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
                    if (!propagate(c, t.u)) return resolve_conflict(c);
                } else if (c->in_bimp(t.v, -t.u)) {
                    LOG(3) << "Already know clause (" << t.u << " " << t.v
                           << "). No need to update bimp.";
                } else if (c->in_bimp(-t.u, -t.v)) {
                    if (!propagate(c, t.v)) return resolve_conflict(c);
                } else {
                    LOG(2) << "    Adding bimps " << -t.u << " -> " << t.v
                           << " and " << -t.v << " -> " << t.u;
                    c->bimp_append(-t.u, t.v);
                    c->bimp_append(-t.v, t.u);
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
    size_t i = c->lookahead_order.size();
    c->lookahead_order.push_back({lit: l});
    for (lit_t w : c->big[l]) {
        // TODO: need this? if (c->fixed_false(w)) { continue; }
        if (c->dfs[w].seen) continue;
        c->dfs[w].parent = l;
        lookahead_dfs(c, count, w);
    }
    count += 2;
    c->lookahead_order[i].t = count;
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
            if (hh != nullptr) *hh += c->h[t.u] * c->h[t.v];
        }
    }
    if (PARAM_add_windfalls) INC(windfalls, c->windfalls.size());
    for (lit_t w : c->windfalls) {
        LOG(2) << "Adding windfall (" << -l << " " << w << ")";
        c->bimp_append(l, w);
        c->bimp_append(-w, -l);
    }
    return true;
}

// Returns false iff a conflict is found.
bool force_lookahead(Cnf* c, lit_t l) {
    // X12. [Force l.]
    LOG(3) << "X12 with " << l;
    c->force.push_back(l);
    uint32_t tsave = c->t;
    c->t = PT;
    bool could_propagate = propagate_lookahead(c, l, nullptr);
    c->t = tsave;
    return could_propagate;
}

// Algorithm X:
// Returns false exactly when a conflict is found.
bool lookahead(Cnf* c) {
    // X1. [Satisfied?]
    if (c->f == static_cast<size_t>(c->nvars())) {
        SAT_EXIT(c);
    }

    if (PARAM_disable_lookahead == 1.0) return true;

    // X2. [Compile rough heuristics.]
    // size_t n = static_cast<size_t>(c->nvars()) - c->f; TODO: needed?
    // TODO: tune refinement a little, Knuth mentions doing this differently
    // based on how close we are to the root of the search tree.
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
        LOG(2) << "No participants, flagging all vars as candidates.";
        INC(no_candidates_during_lookahead);
        for (lit_t v : c->freevar) {
            c->cand.insert(v, -c->h[v]*c->h[-v]);
        }
    }

    // Prune candidates
    size_t cmax = std::max(PARAM_c0, PARAM_c1 / (c->d + 1));
    LOG(2) << "cmax = " << cmax << ", d = " << c->d;
    // TODO: verify that we don't need empty check below
    while (!c->cand.empty() && c->cand.size() > cmax) c->cand.delete_max();

    // X4. [Nest the candidates.]
    if (LOG_ENABLED(3)) { LOG(3) << "before nesting: " << c->dump_bimp(); }
    for (lit_t l = -c->nvars(); l <= c->nvars(); ++l) {
        if (l == 0) continue;
        c->dfs[l] = dfs_t();
        c->big[l].clear();
    }
    for (lit_t v : c->cand.heap) {
        c->dfs[v].cand = c->dfs[-v].cand = true;
    }
    // Copy reverse graph induced by candidates into big.
    for (lit_t u = -c->nvars(); u <= c->nvars(); ++u) {
        if (u == 0) continue;
        for (lit_t v : c->bimp[u]) {
            if (!c->dfs[u].cand || !c->dfs[v].cand) continue;
            c->big[v].push_back(u);
        }
    }
    if (LOG_ENABLED(3)) { LOG(3) << "candidate graph: " << c->dump_big(); }

    // TODO: Knuth computes strongly-connected components here, which can reduce
    // the number of candidates we need to consider (all literals in the the
    // same component imply each other) as well as allow us to deduce
    // contradictions earlier (when l and -l are in the same component). But it
    // also requires a little more work and bookkeeping so we only run DFS on
    // all candidates for now.

    lit_t count = 0;
    c->lookahead_order.clear();
    for(lit_t v : c->cand.heap) {
        for (lit_t l : {-v,v}) {
            if (c->dfs[l].seen) continue;
            lookahead_dfs(c, count, l);
        }
    }
    CHECK(static_cast<size_t>(count) == c->cand.heap.size() * 4)
        << "Inconsistent DFS detected.";
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
        LOG(3) << "X6";
        lit_t l = c->lookahead_order[j].lit;
        c->t = base + c->lookahead_order[j].t;
        if (c->dfs[l].parent) {
            LOG(3) << "bootstrapping " << l << "'s H value with "
                   << c->dfs[l].parent << "'s: " << c->dfs[c->dfs[l].parent].H;
            c->dfs[l].H = c->dfs[c->dfs[l].parent].H;
        }
        if (!c->fixed(l)) {
            // X8. [Compute sharper heuristic.]
            LOG(3) << "X8";
            LOG(2) << "Current truths: " << c->dump_truths();
            double w = 0;
            if (!propagate_lookahead(c, l, &w)) {
                LOG(3) << "Can't propagate " << l << ", trying to force " << -l;
                // X13. [Recover from conflict]
                if (!force_lookahead(c, -l)) {
                    LOG(3) << "Can't propagate " << l << " or force " << -l
                           << ", bailing from lookahead";
                    return false;
                }
                // -> X7
            }
            if (w > 0) {
                c->dfs[l].H += w;
                LOG(3) << l << "'s H now " << c->dfs[l].H;
            } else {
                // X9. [Exploit an autarky]
                if (c->dfs[l].H == 0) {
                    // TODO: do X12 with l.
                } else {
                    // TODO: generate new binary clause
                }
            }
            // X10. [Optionally look deeper.] (Algorithm Y)
            // TODO
            // X11. [Exploit necessary assignments.]
            // TODO
        } else if (c->fixed_false(l) && !c->fixed_false(l, PT)) {
            // X13. [Recover from conflict]
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
        if (j == c->cand.heap.size()) {
            INC(lookahead_wraparound);
            j = 0;
            base += 2 * c->cand.heap.size();
        }
        if (j == jp) {
            return true;
        }
        if (j == 0 && base + 2 * c->cand.heap.size() >= PT) {
            INC(lookahead_exhausted);
            return true;
        }
        // -> X6
    }

    return true;
}

// Returns true exactly when a satisfying assignment exists for c.
bool solve(Cnf* c) {
    Timer t("solve");

    bool choose_new_node = true;
    while (true) {
        lit_t l = lit_nil;
        while (l == lit_nil) {
            // L2. [New node.]
            if (choose_new_node) {
                LOG(2) << "Current truths: " << c->dump_truths();
                LOG(2) << "Current rstack: " << c->dump_rstack();
                LOG(2) << "Choosing a new node.";
                if (c->d < kPathBits) c->sigma &= (1UL << c->d)-1; // trim sigma
                c->branch[c->d] = -1;
                if (c->force.empty()) {
                    LOG(2) << "Calling Algorithm X for lookahead, d=" << c->d;
                    // L3.
                    if (!lookahead(c)) {
                        // L15. [Backtrack.]
                        if (c->d == 0) UNSAT_EXIT;
                        --c->d;
                        c->rstack.resize(c->f);
                        c->f = c->backf[c->d];
                        // (L11 - L15) -> L4
                        // Note: L15 should jump to L12, but I think jumping to
                        // L11 is safe here. Verify.
                        l = resolve_conflict(c);
                        break;
                    }
                } else /* !c->force.empty() */ {
                    // L5 - L9. [Accept near truths.]
                    l = accept_near_truths(c);
                    break; // -> L10 if l == lit_nil, otherwise L4
                }
            }

            // L3. [Choose l.]
            if (!c->freevar.empty()) {
                // TODO: use heuristic scores to choose l.
                l = c->freevar[0];
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
            if (c->d < kPathBits && c->branch[c->d] == 1) {
                c->sigma |= 1UL << c->d;  // append to sigma
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
    init_counters();
    init_timers();
    Cnf c = parse(argv[oidx]);
    if (/* TODO: detect no clauses || */ solve(&c)) {
        SAT_EXIT(&c);
    } else {
        std::cout << "s UNSATISFIABLE" << std::endl;
        return UNSATISFIABLE;
    }
}
