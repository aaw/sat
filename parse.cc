#include "logging.h"
#include "parse.h"

#include <cstdio>

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
Instance parse(const char* filename) {
    int nc;
    FILE* f = fopen(filename, "r");
    if (!f) {
        // TODO: return an error here
        printf("Failed to open %s", filename);
    }

    // Read comment lines until we see the problem line.
    Instance cnf;
    do {
        nc = fscanf(f, " p cnf %i %i \n", &cnf.nvars, &cnf.nclauses);
        if (nc > 0 && nc != EOF) break;
        nc = fscanf(f, "%*s\n");
    } while (nc != 2 && nc != EOF);

    LOG(4) << "Problem has " << cnf.nvars << " variables and "
           << cnf.nclauses << " clauses.";

    // Initialize data structures now that we know nvars and nclauses.
    cnf.link.resize(cnf.nclauses);
    cnf.watch_storage.resize(2 * cnf.nvars + 1);
    cnf.watch = &cnf.watch_storage[cnf.nvars];

    // Read clauses until EOF.
    int lit;
    do {
        cnf.start.push_back(cnf.clauses.size());
        while (true) {
            nc = fscanf(f, " %i ", &lit);
            if (nc == EOF || lit == 0) break;
            cnf.clauses.push_back(lit);
        }
        cnf.watch[cnf.clauses[cnf.start.back()]].push_back(cnf.start.size()-1);
    } while (nc != EOF);
    LOG(4) << "Done parsing input.";

    fclose(f);
    return cnf;
}
