#include "types.h"

// Parser for a DIMACS cnf input file. File starts with zero or more comments
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
//
// Here's an example of how to use this parser to process a DIMACS input file:
//
// DIMACS d(filename);
// d.reset();
// while (!d.eof()) {
//   /* start new clause */
//   for (d.advance(); !d.eoc(); d.advance()) {
//     /* add d.curr() to current clause */
//   }
// }
struct DIMACS {
    DIMACS(const char* filename) : filename_(filename) { }

    ~DIMACS() { fclose(f_); }

    void reset() {
        if (f_ != 0) fclose(f_);
        f_ = fopen(filename_, "r");
        CHECK(f_) << "Failed to open file: " << filename_;

        // Read comment lines until we see the problem line.
        long long nv = 0, nc = 0;
        do {
            read_ = fscanf(f_, " p cnf %lld %lld \n", &nv, &nc);
            if (read_ > 0 && read_ != EOF) break;
            read_ = fscanf(f_, "%*s\n");
        } while (read_ != 2 && read_ != EOF);
        CHECK(nv >= 0) << "Variable count must be non-negative.";
        CHECK(nc >= 0) << "Clause count must be non-negative.";
        CHECK_NO_OVERFLOW(lit_t, nv);
        CHECK_NO_OVERFLOW(clause_t, nc);
        nvars_ = nv;
        nclauses_ = nc;

    }

    inline void advance() { read_ = fscanf(f_, " %i ", &curr_); }

    inline bool eof() { return read_ == EOF; }

    inline bool eoc() { return eof() || curr_ == lit_nil; }

    inline lit_t curr() { return curr_; }

    inline lit_t nvars() { return nvars_; }

    inline lit_t nclauses() { return nclauses_; }

private:
    const char* filename_;
    FILE* f_ = 0;
    int read_ = 0;
    lit_t curr_ = lit_nil;
    lit_t nvars_;
    clause_t nclauses_;
};
