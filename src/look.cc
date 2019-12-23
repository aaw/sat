// Algorithm L from Knuth's The Art of Computer Programming 7.2.2.2:
// DPLL with Lookahead.

#include <sstream>
#include <vector>

#include "counters.h"
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

// Real truth
constexpr uint32_t RT = std::numeric_limits<uint32_t>::max() - 1;  // 2^32 - 2
// Near truth
constexpr uint32_t NT = std::numeric_limits<uint32_t>::max() - 3;  // 2^32 - 4
// Proto truth
constexpr uint32_t PT = std::numeric_limits<uint32_t>::max() - 5;  // 2^32 - 6

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

    // heuristic scores, maps lit -> score. hnew is used for scratch for
    // computing the next round of scores, then swapped.
    std::vector<double> h_storage;
    double* h;
    std::vector<double> hnew_storage;
    double* hnew;

    std::vector<lit_t> force; // list of unit literals

     // maps depth -> values of dec[depth] attempted.
    // -1 = none, 0 = dec[depth], 1 = -dec[depth].
    std::vector<uint8_t> branch;

    std::vector<lit_t> freevar;  // list of free variables
    std::vector<lit_t> invfree;  // invfree[freevar[k]] == k
    size_t nfree;                // last valid index of freevar

    std::vector<lit_t> rstack;  // stack of literals. rstack.size() == E.

    std::vector<lit_t> cand; // list of candidates for lookahead in Alg. X.

    std::vector<uint64_t> istamps_storage;  // maps literals to their istamp;
    uint64_t* istamps;

    std::vector<lit_t> dec;  // maps d -> decision literal

    std::vector<lit_t> backf;  // maps d -> f at the time decision d was made.

    std::vector<uint64_t> backi;  // maps d -> istack size when dec. d was made.

    std::vector<istack_frame_t> istack;

    std::vector<uint32_t> val;  // maps variables -> truth values

    std::vector<psig_t> sig;  // to identify participants/newbies

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
        h_storage(2 * (novars + nsvars) + 1, 1),
        h(&h_storage[novars + nsvars]),
        hnew_storage(2 * (novars + nsvars) + 1),
        hnew(&hnew_storage[novars + nsvars]),
        branch(novars + nsvars + 1, -1), // TODO: how to initialize?
        freevar(novars + nsvars),
        invfree(novars  + nsvars + 1),
        nfree(novars + nsvars), /* TODO: is this correct? */
        istamps_storage(2 * (novars + nsvars) + 1),
        istamps(&istamps_storage[novars + nsvars]),
        dec(novars + nsvars + 1),
        backf(novars + nsvars + 1),
        backi(novars + nsvars + 1),
        val(novars + nsvars + 1, 0),
        sig(novars + nsvars + 1, psig_t{path: 0, length: -1}),
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

    bool fixed(lit_t l) {
        return val[var(l)] >= t;
    }

    bool fixed_true(lit_t l) {
        uint32_t v = val[var(l)];
        if (v < t) return false;
        return (l > 0) != (v % 2 == 1);
   }

    bool fixed_false(lit_t l) {
        uint32_t v = val[var(l)];
        if (v < t) return false;
        return (l > 0) != (v % 2 == 0);
    }

    void make_unfree(lit_t v) {
        CHECK(v > 0) << "wanted var, got lit";
        --nfree;
        lit_t s = freevar[nfree];
        std::swap(freevar[invfree[v]], freevar[nfree]);
        std::swap(invfree[v], invfree[s]);
    }

    void make_free(lit_t v) {
        CHECK(v > 0) << "wanted var, got lit";
        lit_t s = freevar[nfree];
        std::swap(freevar[invfree[v]], freevar[nfree]);
        std::swap(invfree[v], invfree[s]);
        ++nfree;
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

    void print_assignment() {
        for (int i = 1, j = 0; i <= novars; ++i) {
            if (!fixed(i)) {
                LOG_ONCE(1) << "Unset vars in solution, assuming false.";
                set_false(i, t);
            }
            if (j % 10 == 0) PRINT << "v";
            PRINT << (fixed_false(i) ? " -" : " ") << i;
            ++j;
            if (i == novars) PRINT << " 0" << std::endl;
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

    return c;
}

// Returns false if a conflict was found.
bool propagate(Cnf* c, lit_t l) {
    LOG(2) << "Propagating " << l;
    size_t h = c->rstack.size();
    if (c->fixed_false(l)) {
        LOG(2) << l << " fixed false.";
        return false;
    } else if (!c->fixed_true(l)) {
        LOG(2) << "fixing " << l << " true.";
        c->val[var(l)] = c->t + (l > 0 ? 0 : 1);
        c->rstack.push_back(l);
    }
    for(; h < c->rstack.size(); ++h) {
        l = c->rstack[h];
        for (lit_t lp : c->bimp[l]) {
            LOG(2) << "taking account of " << lp;
            if (c->fixed_false(lp)) {
                LOG(2) << "  " << lp << " fixed false.";
                return false;
            } else if (!c->fixed_true(lp)) {
                LOG(2) << "  fixing " << lp << " true.";
                c->val[var(lp)] = c->t + (lp > 0 ? 0 : 1);
                c->rstack.push_back(lp);
            }
        }
    }
    return true;
}

//
// TODO: just make a member function of Cnf
lit_t resolve_conflict(Cnf* c) {
    // L11. [Unfix near truths.]
    while (c->g < c->rstack.size()) {
        LOG(2) << "unsetting " << var(c->rstack.back()) << " (NT)";
        c->val[var(c->rstack.back())] = 0;
        c->rstack.pop_back();
    }
    while (true) {
        // L12. [Unfix real truths.]
        while (c->f < c->rstack.size()) {
            lit_t x = c->rstack.back();
            LOG(2) << "unsetting " << var(x) << " (RT)";
            c->rstack.pop_back();
            c->timp_set_active(x, true);
            c->make_free(var(x));
            c->val[var(x)] = 0;
        }

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
                    LOG(2) << "Adding " << t.v << " to " << -t.u;
                    LOG(2) << "Adding " << t.u << " to " << -t.v;
                    c->bimp_append(-t.u, t.v);
                    c->bimp_append(-t.v, t.u);
                }
            }
        }
    }
    return lit_nil;
}

// Algorithm X:
// Returns false exactly when a conflict is found.
bool lookahead(Cnf* c) {
    // X1. [Satisfied?]
    if (c->f == static_cast<size_t>(c->nvars())) {
        SAT_EXIT(c);
    }

    // TODO: add a param to disable lookahead by returning true here.

    // X2. [Compile rough heuristics.]
    // size_t n = static_cast<size_t>(c->nvars()) - c->f; TODO: needed?
    // TODO: tune refinement a little, Knuth mentions doing this differently
    // based on how close we are to the root of the search tree.
    c->refine_heuristic_scores();

    // X3. [Preselect candidates.]
    int cmax = static_cast<int>((std::max(PARAM_c0, PARAM_c1 / c->d)));
    LOG(2) << "cmax = " << cmax;
    c->cand.clear();
    for (lit_t v = 1; v <= c->nvars(); ++v) {
        if (c->participant(v)) c->cand.push_back(v);
    }
    if (c->cand.empty()) {
        LOG(2) << "No participants, flagging all vars as candidates.";
        for (lit_t v = 1; v <= c->nvars(); ++v) { c->cand.push_back(v); }
    }
    // TODO: terminate if all clauses are satisfied (ex. 152).




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
                        // L12 - L15
                        resolve_conflict(c);
                        // TODO: break to L4 from L14
                    }
                } else /* !c->force.empty() */ {
                    // L5 - L9. [Accept near truths.]
                    l = accept_near_truths(c);
                    break; // -> L10 if l == lit_nil, otherwise L4
                }
            }

            // L3. [Choose l.]
            if (c->nfree > 0) {  // TODO: c->f == nvars instead?
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
