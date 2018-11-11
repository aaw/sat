#include <cstdio>

#include "logging.h"
#include "parse.h"
#include "solve.h"

int main(int argc, char** argv) {
    Instance cnf = parse(argv[1]);
    bool sat = solve(&cnf);
    LOG(1) << "Satisfiable: " << sat;
    return !sat;
}
