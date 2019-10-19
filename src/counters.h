// Counters: low-overhead unsigned 64-bit counters that report total and average
// increment. Usage:
//
//   INC(foo);       // Increment foo by 1. foo must be a valid variable name.
//   INC(foo, 100);  // Increment foo by 100.
//
// On program termination or SIGINT, totals are reported:
//
//   c counter: [foo] = 21225
//
// If the counter total is different than the number of calls to INC, an average
// increment is also reported:
//
//   c counter: [foo] = 21225 (avg: 12.5)

#ifndef __COUNTERS_H__
#define __COUNTERS_H__

#include "signal.h"

#include <map>
#include <string>

#include "logging.h"
#include "types.h"

#ifndef COUNTERS
#define COUNTERS 0
#endif

extern bool FLAGS_counters;

#define INC2(counter, val) \
    static uint64_t VARNAME(__count, __LINE__) = 0; \
    static uint64_t VARNAME(__sum, __LINE__) = 0; \
    static CounterRegisterer \
      VARNAME(__reg, __LINE__)(STRING(counter), \
      &VARNAME(__count, __LINE__), \
      &VARNAME(__sum, __LINE__)); \
    if (FLAGS_counters) { \
        ++VARNAME(__count, __LINE__); VARNAME(__sum, __LINE__) += val; \
    }
#define INC1(counter) INC2(counter, 1);
#define GETMACRO(_1,_2,NAME,...) NAME
#define INC(...) if (COUNTERS) {GETMACRO(__VA_ARGS__, INC2, INC1)(__VA_ARGS__)}

class Counters {
public:
    void register_counter(const char* name, uint64_t* count, uint64_t* sum) {
        counts_.insert({name, {count, sum}});
    }

    void print() {
        auto range = counts_.equal_range("");
        for(auto itr = counts_.begin(); itr != counts_.end();
            itr = range.second) {
            range = counts_.equal_range(itr->first);
            uint64_t total = 0;
            uint64_t sum = 0;
            for(auto jtr = range.first; jtr != range.second; ++jtr) {
                total += *jtr->second.first;
                sum += *jtr->second.second;
            }
            PRINT << "c counter: [" << range.first->first << "] = " << sum;
            if (total != sum) {
                PRINT << " (avg: " << ((double)sum)/total << ")";
            }
            PRINT << std::endl;
        }
    }

    void dump() {
        print();
        counts_.clear();
    }

    static Counters& singleton() {
        static Counters s;
        return s;
    }
private:
    std::multimap<const char*, std::pair<uint64_t*, uint64_t*>, cstrcmp>
        counts_;
};

struct CounterRegisterer {
    CounterRegisterer(const char* name, uint64_t* count, uint64_t* sum) {
        if (FLAGS_counters) {
            Counters::singleton().register_counter(name, count, sum);
        }
    }
};

void init_counters() {
    if (!COUNTERS) return;
    if (!FLAGS_counters) return;
    // Initialize singleton so it won't get destroyed before atexit call.
    Counters::singleton();
    std::atexit([]{ Counters::singleton().dump(); });
    struct sigaction sigbreak;
    sigbreak.sa_handler = [](int signum) {
        Counters::singleton().dump(); exit(UNKNOWN);
    };
    sigemptyset(&sigbreak.sa_mask);
    sigbreak.sa_flags = 0;
    CHECK(sigaction(SIGINT, &sigbreak, NULL) == 0);
}

#endif  // __COUNTERS_H__
