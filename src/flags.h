#ifndef __FLAGS_H__
#define __FLAGS_H__

#include <iostream>
#include <limits>
#include <getopt.h>
#include <string>

#include "logging.h"
#include "params.h"

// To add and use a new flag:
// (1) Declare it and its default below globally as FLAGS_xxx = default.
// (2) Declare an extern reference to it in the module where you want to use it.
// (3) Add an entry to long_options[] and optstring[] below defining its parse.
// (4) Add a case in the switch statement below to handle setting the flag.
// (5) Add a sentence to the help text displayed with -h.

int FLAGS_verbosity = 0;
unsigned long FLAGS_seed = 0;
bool FLAGS_time = false;
bool FLAGS_counters = false;
std::string FLAGS_params = "";
#ifdef PROOFLOG
std::string FLAGS_dratfile = "";
#endif // PROOFLOG

bool parse_flags(int argc, char* argv[], int* option_index) {
    *option_index = 0;
    int c;

    struct option long_options[] = {
        { "verbosity",      required_argument,  NULL, 'v' },
        { "seed",           required_argument,  NULL, 's' },
        { "time",           no_argument,        NULL, 't' },
        { "counters",       no_argument,        NULL, 'c' },
        { "help",           no_argument,        NULL, 'h' },
        { "params",         required_argument,  NULL, 'p' },
#ifdef PROOFLOG
        { "drat",           required_argument,  NULL, 'd' },
#endif // PROOFLOG
        { 0, 0, 0, 0}
    };

#ifdef PROOFLOG
    char optstring[] = "v:s:p:d:tch";
#else
    char optstring[] = "v:s:p:tch";
#endif // PROOFLOG

    while (1) {
        c = getopt_long(argc, argv, optstring, long_options, nullptr);
        if (c == -1)
            break;

        switch (c) {
        case 'h':
            PRINT << "Usage: " << argv[0] << " [OPTIONS]... FILE" << std::endl;
            PRINT << std::endl;
            PRINT << "FILE must be in DIMACS cnf format. If the input formula "
                  << "is satisfiable, " << std::endl
                  << "\"c SATISFIABLE\" is written to stdout and the program "
                  << "returns 10. If the input" << std::endl
                  << "formula is unsatisfiable, \"c UNSATISFIABLE\" is written "
                  << "to stdout and the " << std::endl
                  << "program returns 20." << std::endl << std::endl;
            PRINT << "OPTIONS include:" << std::endl << std::endl;
            PRINT << "  -sN    Set the random seed to N" << std::endl
                  << std::endl;
            PRINT << "  -vN    Set the verbosity to N" << std::endl
                  << std::endl;
            PRINT << "  -t     Collect and print timing information"
                  << std::endl << std::endl;
            PRINT << "  -c     Collect and print counters" << std::endl
                  << std::endl;
#ifdef PROOFLOG
            PRINT << "  -dF    Output DRAT proof to file F." << std::endl;
#endif // PROOFLOG
            PRINT << "  -h     Display this message" << std::endl << std::endl;
            if (!Params::singleton().empty()) {
                PRINT << "  -p     Set various double-valued params. Param "
                      << "overrides must be provided as" << std::endl
                      << "         key=value pairs, separated by semicolons. "
                      << "Example: \"foo=1.0;bar=2.0\"." << std::endl
                      << "         Available params include:" << std::endl
                      << std::endl;
                PRINT << Params::singleton().help_string();
            }
            exit(0);
            break;
        case 'v':
            FLAGS_verbosity = atoi(optarg);
            PRINT << "c Setting verbosity = " << FLAGS_verbosity
                  << std::endl;
            break;
        case 's':
            FLAGS_seed = strtoul(optarg, NULL, 0);
            CHECK(FLAGS_seed <= std::numeric_limits<unsigned int>::max())
                << "Seed " << FLAGS_seed << " must be between 0 and "
                << std::numeric_limits<unsigned int>::max();
            PRINT << "c Setting random seed = " << FLAGS_seed
                  << std::endl;
            break;
        case 'p':
            FLAGS_params = optarg;
            Params::singleton().parse(FLAGS_params);
            break;
        case 't':
            PRINT << "c Timing enabled" << std::endl;
            FLAGS_time = true;
            break;
        case 'c':
            PRINT << "c Counters enabled" << std::endl;
            FLAGS_counters = true;
            break;
#ifdef PROOFLOG
        case 'd':
            PRINT << "c DRAT proof will be output to " << optarg << std::endl;
            FLAGS_dratfile = optarg;
            break;
#endif // PROOFLOG
        default:
            return false;
        }
    }
    *option_index = optind;
    return true;
}


#endif // __FLAGS_H__
