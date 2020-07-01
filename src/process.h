#include <algorithm>
#include <vector>

#include "logging.h"
#include "params.h"
#include "parse.h"

DEFINE_PARAM(preprocess, 0,
             "If non-zero, pre-process the input formula, applying common "
             "simplifications.");

typedef uint32_t cell_size_t;
constexpr uint32_t cell_nil = std::numeric_limits<cell_size_t>::max();

struct Cell {
    lit_t lit = lit_nil;
    cell_size_t lit_prev = cell_nil;     // B (backward)
    cell_size_t lit_next = cell_nil;     // F (forward)
    cell_size_t clause_prev = cell_nil;  // S (sinister)
    cell_size_t clause_next = cell_nil;  // D (dexter)
};

// TODO: rework so we're not doing the 2*x+1 stuff for literals...

// Convert a positive/negative literal to a lit index. Maps lits in the range
// [-nvars, nvars] onto [2, 2*nvars+1].
static inline cell_size_t lidx(lit_t l) { return 2 * abs(l) + (l < 0 ? 1 : 0); }

// Inverse of lidx; lit(lidx(-3)) = -3
static inline lit_t lit(cell_size_t l) { return (l & 1 ? -1 : 1) * (l / 2); }

struct Processor {
    Processor(const char* filename) : dimacs(filename) {
        if (!PARAM_preprocess) return;
        dimacs.reset();
        next_cell = cell_nil;
        nvars_ = dimacs.nvars();
        nclauses_ = dimacs.nclauses();
        val.resize(dimacs.nvars() + 1, false);
        cells.resize(lidx(-dimacs.nvars()) + dimacs.nclauses() + 1);
        std::vector<lit_t> c;

        for (cell_size_t i = 2; i < cells.size(); ++i) {
            cells[i].lit_next = cells[i].lit_prev = i;
            cells[i].clause_next = cells[i].clause_prev = i;
        }

        lit_end = lidx(-dimacs.nvars()) + 1;
        clause_end = lidx(-dimacs.nvars());
        LOG(0) << "lit_end = " << lit_end;
        while (!dimacs.eof()) {
            c.clear();
            for (dimacs.advance(); !dimacs.eoc(); dimacs.advance()) {
                c.push_back(lidx(dimacs.curr()));
            }
            if (!dimacs.eof() && c.empty()) {
                LOG(2) << "Empty clause in input file, unsatisfiable formula.";
                UNSAT_EXIT;
            }

            // Sort and remove duplicate lits.
            std::sort(c.begin(), c.end());
            c.erase(std::unique(c.begin(), c.end()), c.end());

            // TODO: remove tautological clauses

            // Install the clause.
            cell_size_t ptr = ++clause_end;
            for (const auto& l : c) {
                cell_size_t nc = alloc_cell();
                cells[nc].lit = l;

                // Set clause_prev/clause_next.
                cells[nc].clause_prev = ptr;
                cells[nc].clause_next = cells[ptr].clause_next;
                cells[cells[ptr].clause_next].clause_prev = nc;
                cells[ptr].clause_next = nc;

                // Set lit_prev/lit_next.
                cells[nc].lit_prev = l;
                cells[nc].lit_next = cells[l].lit_next;
                cells[cells[l].lit_next].lit_prev = nc;
                cells[l].lit_next = nc;

                ptr = nc;
            }
        }
        dump_clauses();
    }

    void dump_clauses() {
        for (size_t i = lit_end; i < cells.size(); ++i) {
            LOG(0) << "[" << i << "]: (" << lit(cells[i].lit) << ") "
                   << "<" << cells[i].clause_prev << "," << cells[i].clause_next
                   << "> {" << cells[i].lit_prev << "," << cells[i].lit_next
                   << "}";
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
        cptr = cells[cptr].clause_next;
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
        //LOG(0) << "|" << lit(cells[cptr].lit) << "|";
        return lit(cells[cptr].lit);
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
        INC(cells_allocated);
        if (next_cell == cell_nil) {
            cells.emplace_back(Cell());
            return cells.size() - 1;
        } else {
            cell_size_t retval = next_cell;
            next_cell = cells[next_cell].clause_prev;
            return retval;
        }
    }

    inline void free_cell(cell_size_t i) {
        INC(cells_freed);
        cells[i].clause_prev = next_cell;
        next_cell = i;
    }

    void print_assignment() {
        for (std::size_t i = 1, j = 0; i < val.size(); ++i) {
            if (j % 10 == 0) PRINT << "v";
            PRINT << (val[i] ? " " : " -") << i+1;
            ++j;
            if (i == val.size() - 1) PRINT << " 0" << std::endl;
            else if (j > 0 && j % 10 == 0) PRINT << std::endl;
        }
    }

    DIMACS dimacs;
    std::vector<bool> val;
    std::vector<Cell> cells;
    cell_size_t next_cell;
    cell_size_t lit_end;
    cell_size_t clause_end;
    cell_size_t cptr;
    lit_t nvars_;
    clause_t nclauses_;
    bool eof_;
};
