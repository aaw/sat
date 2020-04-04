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
// while (!d.eof()) {
//   /* start new clause */
//   for (d.advance(); !d.eoc(); d.advance()) {
//     /* add literal to current clause */
//   }
// }
struct DIMACS {
    DIMACS(const char* filename) {
        f = fopen(filename, "r");
        CHECK(f) << "Failed to open file: " << filename;

        // Read comment lines until we see the problem line.
        long long nv = 0, nc = 0;
        do {
            read = fscanf(f, " p cnf %lld %lld \n", &nv, &nc);
            if (read > 0 && read != EOF) break;
            read = fscanf(f, "%*s\n");
        } while (read != 2 && read != EOF);
        CHECK(nv >= 0) << "Variable count must be non-negative.";
        CHECK(nc >= 0) << "Clause count must be non-negative.";
        CHECK_NO_OVERFLOW(lit_t, nv);
        CHECK_NO_OVERFLOW(clause_t, nc);
        nvars = nv;
        nclauses = nc;
    }

    ~DIMACS() { fclose(f); }

    inline void advance() { read = fscanf(f, " %i ", &curr); }

    inline bool eof() { return read == EOF; }

    inline bool eoc() { return eof() || curr == lit_nil; }

    lit_t nvars;
    clause_t nclauses;
    lit_t curr = lit_nil;

private:
    FILE* f;
    int read = 0;
};
