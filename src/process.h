#include <algorithm>
#include <vector>

#include "logging.h"
#include "params.h"
#include "parse.h"

DEFINE_PARAM(preprocess, 0,
             "If non-zero, pre-process the input formula, applying common "
             "simplifications.");

typedef int32_t cell_size_t;
constexpr int32_t cell_nil = std::numeric_limits<cell_size_t>::max();

struct Cell {
    lit_t lit = lit_nil;
    cell_size_t clause = cell_nil;
    cell_size_t lit_prev = cell_nil;     // B (backward)
    cell_size_t lit_next = cell_nil;     // F (forward)
    cell_size_t clause_prev = cell_nil;  // S (sinister)
    cell_size_t clause_next = cell_nil;  // D (dexter)
    uint64_t sig = 0;
};

#define TALLY(l) (cell[l].lit)
#define CSIZE(c) (cell[c].clause)

// When we eliminate a variable, we store a rule that will tell us the truth
// value of that variable as a function of other un-eliminated variables. Here,
// clauses is a sequence of lit_nil-delimited clauses. The rule tells us to set
// lit to true iff all clauses are satisfied.
struct Rule {
    lit_t lit;
    std::vector<lit_t> clauses;
};

struct Processor {
    Processor(const char* filename) : dimacs(filename) {
        if (!PARAM_preprocess) return;
        dimacs.reset();
        next_cell = cell_nil;
        nvars_ = dimacs.nvars();
        nclauses_ = dimacs.nclauses();
        val.resize(dimacs.nvars() + 1, false);
        cell_storage.resize(2*nvars_ + 1 + nclauses_);
        cell = &cell_storage[nvars_];
        std::vector<lit_t> c;

        // Initialize all cells.
        for (size_t i = 0; i < cell_storage.size(); ++i) {
            cell_size_t self = i - nvars_;
            cell_storage[i].lit_next = cell_storage[i].lit_prev = self;
            cell_storage[i].clause_next = cell_storage[i].clause_prev = self;
        }

        // Process input from DIMACS file.
        lit_end = nvars_ + 1;
        clause_end = nvars_;
        while (!dimacs.eof()) {
            c.clear();
            for (dimacs.advance(); !dimacs.eoc(); dimacs.advance()) {
                c.push_back(dimacs.curr());
            }
            if (!dimacs.eof() && c.empty()) {
                LOG(2) << "Empty clause in input file, unsatisfiable formula.";
                UNSAT_EXIT;
            }

            // Sort and remove duplicate lits. We want lits sorted by var, with
            // positive lits coming before negative: 1,2,3,-4,5,-5,6,...
            std::sort(c.begin(), c.end(), [](lit_t x, lit_t y) -> bool {
                    return abs(x) > abs(y) || (abs(x) == abs(y) && x < y);
                });
            c.erase(std::unique(c.begin(), c.end()), c.end());

            // TODO: remove tautological clauses

            // Install the clause.
            cell_size_t ptr = ++clause_end;
            cell_size_t ci = ptr;
            for (const auto& l : c) {
                cell_size_t nc = alloc_cell();
                cell[nc].lit = l;
                cell[nc].clause = ci;

                // Set clause_prev/clause_next.
                cell[nc].clause_prev = ptr;
                cell[nc].clause_next = cell[ptr].clause_next;
                cell[cell[ptr].clause_next].clause_prev = nc;
                cell[ptr].clause_next = nc;

                // Set lit_prev/lit_next.
                cell[nc].lit_prev = l;
                cell[nc].lit_next = cell[l].lit_next;
                cell[cell[l].lit_next].lit_prev = nc;
                cell[l].lit_next = nc;

                ptr = nc;
            }
        }

        // Initialize lit signatures.
        for (lit_t l = -nvars_; l <= nvars_; ++l) {
            if (l == lit_nil) continue;
            cell[l].sig = 1UL << (rand() % 64);
            cell[l].sig |= 1UL << (rand() % 64);
            calc_tally(l);
        }

        // Initialize clause signatures.
        for (cell_size_t i = lit_end; i < clause_end; ++i) {
            calc_clause_sig(i);
            calc_csize(i);
        }

        dump_clauses();
    }

    void calc_clause_sig(clause_t c) {
        cell[c].sig = 0;
        for(clause_t i = cell[c].clause_next; i != c; i = cell[i].clause_next) {
            cell[c].sig |= cell[cell[i].lit].sig;
        }
    }

    void calc_tally(lit_t l) {
        TALLY(l) = 0;
        for(cell_size_t p = cell[l].lit_next; p != l; p = cell[p].lit_next) {
            ++TALLY(l);
        }
    }

    void calc_csize(cell_size_t c) {
        CSIZE(c) = 0;
        for(cell_size_t p = cell[c].clause_next; p != c;
            p = cell[p].clause_next) {
            ++CSIZE(c);
        }
    }

    bool resolve(cell_size_t c, cell_size_t d, lit_t v) {
        return true; // TODO
    }

    void dump_clauses() {
        for (size_t i = lit_end; i < cell_storage.size(); ++i) {
            LOG(0) << "[" << i - nvars_ << "]: (" << cell_storage[i].lit << ") "
                   << " ( " << cell_storage[i].clause << ") "
                   << "<" << cell_storage[i].clause_prev << ","
                   << cell_storage[i].clause_next << "> {"
                   << cell_storage[i].lit_prev << ","
                   << cell_storage[i].lit_next << "}";
        }
    }

    void reset() {
        if (!PARAM_preprocess) {
            dimacs.reset();
            return;
        }
        cptr = lit_end;
        eof_ = cptr >= clause_end;
    }

    bool eof() {
        if (!PARAM_preprocess) return dimacs.eof();
        return eof_;
    }

    void advance() {
        if (!PARAM_preprocess) {
            dimacs.advance();
            return;
        }
        cptr = cell[cptr].clause_next;
        if (cptr < clause_end) {
            ++cptr;
            if (cptr >= clause_end) { eof_ = true; }
        }
    }

    bool eoc() {
        if (!PARAM_preprocess) return dimacs.eoc();
        return eof() || cptr < clause_end;
    }

    lit_t curr() {
        if (!PARAM_preprocess) return dimacs.curr();
        return cell[cptr].lit;
    }

    lit_t nvars() {
        if (!PARAM_preprocess) return dimacs.nvars();
        return nvars_;
    }

    clause_t nclauses() {
        if (!PARAM_preprocess) return dimacs.nclauses();
        return nclauses_;
    }

    inline cell_size_t alloc_cell() {
        // TODO: check to make sure we don't overflow cell_size_t here
        INC(cell_allocated);
        if (next_cell == cell_nil) {
            cell_storage.emplace_back(Cell());
            cell = &cell_storage[nvars_];
            return cell_storage.size() - nvars() - 1;
        } else {
            cell_size_t retval = next_cell;
            next_cell = cell[next_cell].clause_prev;
            return retval;
        }
    }

    inline cell_size_t copy(lit_t u) {
        cell_size_t i = alloc_cell();
        cell[i].lit = u;
        return i;
    }

    inline void free_cell(cell_size_t i) {
        INC(cell_freed);
        cell[i].clause_prev = next_cell;
        next_cell = i;
    }

    void apply_rules() {
        while (!rules.empty()) {
            const Rule& r = rules.back();
            bool sat = r.clauses.empty();
            for (lit_t l : r.clauses) {
                if (l == lit_nil && !sat ) break;  // nothing sat in current
                if (l == lit_nil /* && sat */) sat = false;  // reset for next
                if (val[abs(l)] == (l > 0)) sat = true;  // sat in current
            }
            val[abs(r.lit)] = (sat == (r.lit > 0));
            LOG(2) << "erp rule set " << abs(r.lit) << " = " << val[abs(r.lit)];
            rules.pop_back();
        }
    }

    void print_assignment() {
        for (std::size_t i = 1, j = 0; i < val.size(); ++i) {
            if (j % 10 == 0) PRINT << "v";
            PRINT << (val[i] ? " " : " -") << i;
            ++j;
            if (i == val.size() - 1) PRINT << " 0" << std::endl;
            else if (j > 0 && j % 10 == 0) PRINT << std::endl;
        }
    }

    DIMACS dimacs;
    std::vector<bool> val;
    std::vector<Cell> cell_storage;
    Cell* cell;
    std::vector<Rule> rules;
    cell_size_t next_cell;
    cell_size_t lit_end;
    cell_size_t clause_end;
    cell_size_t cptr;
    lit_t nvars_;
    clause_t nclauses_;
    bool eof_;
};
