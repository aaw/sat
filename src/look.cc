// Algorithm L from Knuth's The Art of Computer Programming 7.2.2.2:
// DPLL with Lookahead.

#include <vector>

#include "counters.h"
#include "flags.h"
#include "logging.h"
#include "timer.h"
#include "types.h"

// Real truth
constexpr uint32_t RT = std::numeric_limits<uint32_t>::max() - 1;  // 2^32 - 2
// Near truth
constexpr uint32_t NT = std::numeric_limits<uint32_t>::max() - 3;  // 2^32 - 4
// Proto truth
constexpr uint32_t PT = std::numeric_limits<uint32_t>::max() - 5;  // 2^32 - 6

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

    std::vector<lit_t> force; // list of unit literals

    std::vector<lit_t> branch; // maps depth ->

    std::vector<lit_t> freevar;  // list of free variables
    std::vector<lit_t> invfree;  // invfree[freevar[k]] == k
    size_t nfree;                // last valid index of freevar

    std::vector<lit_t> rstack;  // stack of literals. rstack.size() == E.

    std::vector<lit_t> istamps_storage;  // maps literals to their istamp;
    lit_t* istamps;

    std::vector<lit_t> dec;  // maps d -> decision literal

    std::vector<lit_t> backf;  // maps d -> f at the time decision d was made.

    std::vector<lit_t> backi;  // maps d -> istack size when dec. d was made.

    std::vector<istack_frame_t> istack;

    std::vector<uint32_t> val;  // maps variables -> truth values

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
        branch(novars + nsvars + 1, 0), // TODO: how to initialize?
        freevar(novars + nsvars),
        invfree(novars  + nsvars + 1),
        nfree(novars + nsvars), /* TODO: is this correct? */
        istamps_storage(2 * (novars + nsvars) + 1),
        istamps(&istamps_storage[novars + nsvars]),
        dec(novars + nsvars + 1),
        backf(novars + nsvars + 1),
        backi(novars + nsvars + 1),
        val(novars + nsvars + 1, 0),
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
        ++nfree;
        lit_t s = freevar[nfree];
        std::swap(freevar[invfree[v]], freevar[nfree]);
        std::swap(invfree[v], invfree[s]);
    }

    // Returns true exactly when u is in bimp[v].
    bool in_bimp(lit_t u, lit_t v) {
        for (const lit_t x : bimp[v]) {
            if (x == u) return true;
        }
        return false;
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
                LOG(1) << "Conflicting unit clauses for " << var(cl[0]);
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
    size_t h = c->rstack.size();
    if (c->fixed_false(l)) {
        return false;
    } else if (!c->fixed_true(l)) {
        c->val[var(l)] = c->t + (l > 0 ? 0 : 1);
        c->rstack.push_back(l);
    }
    for(; h < c->rstack.size(); ++h) {
        l = c->rstack[h];
        if (c->fixed_false(l)) {
            return false;
        } else if (!c->fixed_true(l)) {
            c->val[var(l)] = c->t + (l > 0 ? 0 : 1);
            c->rstack.push_back(l);
        }
    }
    return true;
}

// TODO: just make a member function of Cnf
void resolve_conflict(Cnf* c) {
    // L11. [Unfix near truths.]
    while (c->g < c->rstack.size()) {
        c->val[c->rstack.back()] = 0;
        c->rstack.pop_back();
    }
    while (true) {
        // L12. [Unfix real truths.]
        while (c->f < c->rstack.size()) {
            lit_t x = c->rstack.back();
            c->rstack.pop_back();
            c->timp_set_active(x, true);
            c->make_free(var(x));
            c->val[var(x)] = 0;
        }
        // L13. [Downdate BIMPs.]
        // TODO

        // L14. [Try again?]
        // TODO

        // L15. [Backtrack.]
        if (c->d == 0) UNSAT_EXIT;
        --c->d;
        c->rstack.resize(c->f);
        c->f = c->backf[c->d];
    }
}

// Returns true exactly when a satisfying assignment exists for c.
bool solve(Cnf* c) {
    Timer t("solve");

    lit_t l = lit_nil;
    for(; l != lit_nil; ++c->d) {
        // L2. [New node.]
        c->branch[c->d] = -1;
        if (c->force.empty()) {
            LOG(1) << "Calling Algorithm X for lookahead with d=" << c->d;
            // TODO: actually call Algorithm X, which either terminates the
            // solver or compiles heuristic scores that will help us in step L3.
        }

        if (c->force.empty()) {
            // L3. [Choose l.]
            // TODO: actually choose an l or set l = lit_nil
        }
    }

    c->dec[c->d] = l;
    c->backf[c->d] = c->f;
    c->backi[c->d] = c->istack.size();
    c->branch[c->d] = 0;

    // L4. [Try l.]
    c->force.push_back(l);

    // L5. [Accept near truths.]
    c->t = NT;
    c->rstack.resize(c->f);  // TODO: do i need this?
    c->g = c->f;
    ++c->istamp;
    // TODO: CONFLICT = L11.

    for(const lit_t l : c->force) {
        propagate(c, l);
        // TODO: go to L11 if propagate returns false
    }
    c->force.clear();

    // L6 - L9
    while (c->g < c->rstack.size()) {
        // L6. [Choose a nearly true L.]
        lit_t l = c->rstack[c->g];
        ++c->g;

        // L7. [Promote l to real truth.]
        c->set_true(l, RT);
        c->make_unfree(var(l));

        c->timp_set_active(l, false);
        for (const timp_t& t : c->timp[l]) {
            // L8. [Consider u OR v.]
            if (c->fixed_false(t.u) && c->fixed_false(t.v)) {
                // TODO: go to CONFLICT
            } else if (c->fixed_false(t.u) && !c->fixed(t.v)) {
                propagate(c, t.v);
                // TODO: go to CONFLICT if propagate returns false.
            } else if (c->fixed_false(t.v) && !c->fixed(t.u)) {
                propagate(c, t.u);
                // TODO: go to CONFLICT if propagate returns false.
            } else if (!c->fixed(t.u) && !c->fixed(t.v)) {
                // L9. [Exploit u OR v.]
                if (c->in_bimp(-t.v, -t.u)) {
                    propagate(c, t.u);
                    // TODO: go to CONFLICT if propagate returns false.
                } else if (c->in_bimp(t.v, -t.u)) {
                    LOG(3) << "Already know clause (" << t.u << " " << t.v
                           << "). No need to update bimp.";
                } else if (c->in_bimp(-t.u, -t.v)) {
                    propagate(c, t.v);
                    // TODO: go to CONFLICT if propagate returns false.
                } else {
                    // TODO: append v to bimp(u), u to bimp(v)
                }
            }
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
    Cnf c = parse(argv[oidx]);
    if (/* TODO: detect no clauses || */ solve(&c)) {
        std::cout << "s SATISFIABLE" << std::endl;
        /* TODO: output solution, something like:
        for (int i = 1, j = 0; i <= c.nvars; ++i) {
            if (c.val[i] == UNSET) {
                LOG_ONCE(1) << "Unset vars in solution, assuming false.";
                c.val[i] = FALSE;
            }
            if (j % 10 == 0) std::cout << "v";
            std::cout << ((c.val[i] & 1) ? " -" : " ") << i;
            ++j;
            if (i == c.nvars) std::cout << " 0" << std::endl;
            else if (j > 0 && j % 10 == 0) std::cout << std::endl;
         }
        */
        return SATISFIABLE;
    } else {
        std::cout << "s UNSATISFIABLE" << std::endl;
        return UNSATISFIABLE;
    }
}
