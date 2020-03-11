#ifndef __TIMER_H__
#define __TIMER_H__

#include "math.h"
#include "signal.h"

#include <ctime>
#include <iomanip>
#include <map>
#include <sstream>

#include "logging.h"
#include "types.h"

#ifndef TIMERS
#define TIMERS 0
#endif

extern bool FLAGS_time;

class Timers {
public:
    void start(const char* name) {
        start_[name] = clock();
    }

    void stop(const char* name) {
        clock_t start = start_[name];
        clock_t end = clock();
        sums_[name] += static_cast<double>(end - start) / CLOCKS_PER_SEC;
        counts_[name]++;
    }

    void reset(const char* name) {
        start_.erase(name);
    }

    void stop_all() {
        for (const auto& kv : start_) { stop(kv.first); }
    }

    void print() {
        for(const auto& kv : sums_) {
            PRINT << "c timer: [" << kv.first << "] = "
                  << fancy_time(kv.second);
            if (counts_[kv.first] > 1) {
                PRINT << " (avg: " << fancy_time(kv.second / counts_[kv.first])
                      << ")";
            }
            PRINT << std::endl;
        }
    }

    void dump() {
        stop_all();
        print();
        start_.clear();
        sums_.clear();
        counts_.clear();
    }

    std::string fancy_time(double t) {
        std::ostringstream oss;
        if (t < (1.0 / 1000)) {
            oss << std::fixed << std::setprecision(0) << t * 1000000 << "µs";
        } else if (t < 1) {
            oss << std::fixed << std::setprecision(0) << t * 1000 << "ms";
        } else if (t < 60) {
            oss << std::fixed << std::setprecision(1) << t << "s";
        } else {
            oss << std::fixed << std::setprecision(0) << t / 60 << "m "
                << fmod(t, 60) << "s";
        }
        return oss.str();
    }
private:
    std::map<const char*, clock_t, cstrcmp> start_;
    std::map<const char*, double, cstrcmp> sums_;
    std::map<const char*, uint64_t, cstrcmp> counts_;
};

static Timers _timers;

class Timer {
public:
    Timer(const char* name) {
        if (!TIMERS) return;
        if (!FLAGS_time) return;
        name_ = name;
        _timers.start(name_);
    }
    ~Timer() {
        if (!TIMERS) return;
        if (!FLAGS_time) return;
        _timers.stop(name_);
        _timers.reset(name_);
    }
private:
    const char* name_;
};

void init_timers() {
    if (!TIMERS) return;
    if (!FLAGS_time) return;
    std::atexit([]{ _timers.dump(); });
    struct sigaction sigbreak;
    sigbreak.sa_handler = [](int signum) { _timers.dump(); exit(UNKNOWN); };
    sigemptyset(&sigbreak.sa_mask);
    sigbreak.sa_flags = 0;
    CHECK(sigaction(SIGINT, &sigbreak, NULL) == 0);
}


#endif  // __TIMER_H__
