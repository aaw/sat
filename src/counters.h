#ifndef __COUNTERS_H__
#define __COUNTERS_H__

#include <map>
#include <string>

#include "logging.h"

extern bool FLAGS_counters;

class Counters {
public:
    void inc(const char* name, uint64_t delta=1UL) {
        if (!FLAGS_counters) return;
        sums_[name] += delta;
        counts_[name] += 1;
    }

    ~Counters() {
        if (!FLAGS_counters) return;
        for(const auto& kv : sums_) {
            PRINT << "c counter:" << kv.first << " = " << kv.second;
            if (counts_[kv.first] != kv.second) {
                PRINT << " (avg: " << double(kv.second) / counts_[kv.first]
                      << ")";
            }
            PRINT << std::endl;
        }
    }
private:
    std::map<std::string, uint64_t> sums_;
    std::map<std::string, double> counts_;
};

#endif  // __COUNTERS_H__
