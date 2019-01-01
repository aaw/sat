#ifndef __FLAGS_H__
#define __FLAGS_H__

#include <cstdlib>
#include <iostream>
#include <getopt.h>

// To add and use a new flag:
// (1) Declare it and its default below globally as FLAGS_xxx = default.
// (2) Declare an extern reference to it in the module where you want to use it.
// (3) Add an entry to long_options[] and optstring[] below defining its parse.
// (4) Add a case in the switch statement below to handle setting the flag.

int FLAGS_verbosity = 0;

bool parse_flags(int argc, char* argv[], int* option_index) {
    *option_index = 0;
    int c;

    struct option long_options[] = {
        { "verbosity",      required_argument,  NULL, 'v' },
        { 0, 0, 0, 0}
    };

    char optstring[] = "v:";

    while (1) {
        c = getopt_long(argc, argv, optstring, long_options, nullptr);
        if (c == -1)
            break;

        switch (c) {
        case 'v':
            FLAGS_verbosity = atoi(optarg);
            std::cout << "c Setting verbosity = " << FLAGS_verbosity
                      << std::endl;
            break;
        default:
            return false;
        }
    }
    *option_index = optind;
    return true;
}


#endif // __FLAGS_H__
