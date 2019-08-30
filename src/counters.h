#ifndef __COUNTERS_H__
#define __COUNTERS_H__

#include "signal.h"

#include <map>
#include <string>

#include "logging.h"
#include "types.h"

extern bool FLAGS_counters;

class Counters {
public:
    void inc(const char* name, uint64_t delta=1UL) {
        sums_[name] += delta;
        counts_[name] += 1;
    }

    void print() {
        for(const auto& kv : sums_) {
            PRINT << "c counter: [" << kv.first << "] = " << kv.second;
            if (counts_[kv.first] != kv.second) {
                PRINT << " (avg: " << double(kv.second) / counts_[kv.first]
                      << ")";
            }
            PRINT << std::endl;
        }
    }

    void dump() {
        print();
        sums_.clear();
        counts_.clear();
    }
    
private:
    std::map<const char*, uint64_t, cstrcmp> sums_;
    std::map<const char*, uint64_t, cstrcmp> counts_;
};

static Counters _counters;

void init_counters() {
    if (!FLAGS_counters) return;
    std::atexit([]{ _counters.dump(); });
    struct sigaction sigbreak;
    sigbreak.sa_handler = [](int signum) { _counters.dump(); exit(UNKNOWN); };
    sigemptyset(&sigbreak.sa_mask);
    sigbreak.sa_flags = 0;
    CHECK(sigaction(SIGINT, &sigbreak, NULL) == 0);
}

#define INC(...) if (FLAGS_counters) { _counters.inc(__VA_ARGS__); }

#endif  // __COUNTERS_H__
