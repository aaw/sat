#include <cstdio>

#include "logging.h"
#include "parse.h"

int main(int argc, char** argv) {
    LOG(1) << "Hello, world!";
    parse(argv[1]);
    return 0;
}
