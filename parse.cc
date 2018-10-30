#include "parse.h"

#include <cstdio>

Instance parse(const char* filename) {
    int nc;
    FILE* f = fopen(filename, "r");
    if (!f) {
        // TODO: return an error here
        printf("Failed to open %s", filename);
    }

    // Read comment lines until we see the problem line.
    Instance inst;
    do {
        nc = fscanf(f, " p cnf %i %i \n", &inst.nvars, &inst.nclauses);
        if (nc > 0 && nc != EOF) break;
        nc = fscanf(f, "%*s\n");
    } while (nc != 2 && nc != EOF);

    // Read clauses until EOF.
    int lit;
    do {
        do { nc = fscanf(f, " %i ", &lit); } while (nc != EOF && lit != 0);
    } while (nc != EOF);

    fclose(f);
    return inst;
}
