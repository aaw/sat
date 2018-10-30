#include <cstdio>

void parse(const char* filename) {
    int nc, nvars, nclauses;
    FILE* f = fopen(filename, "r");
    if (!f) {
        // TODO: return an error here
        printf("Failed to open %s", filename);
    }

    // Read comment lines until we see the problem line.
    do {
        nc = fscanf(f, " p cnf %i %i \n", &nvars, &nclauses);
        if (nc > 0 && nc != EOF) break;
        nc = fscanf(f, "%*s\n");
    } while (nc != 2 && nc != EOF);

    // Read clauses until EOF.
    int lit;
    do {
        printf("Clause: ");
        do {
            nc = fscanf(f, " %i ", &lit);
            printf("%d ", lit);
        }
        while (nc != EOF && lit != 0);
        printf("\n");
    } while (nc != EOF);

    fclose(f);
}
