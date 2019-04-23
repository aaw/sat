#ifndef __LOGGING_H__
#define __LOGGING_H__

#include <iostream>

#include "types.h"

extern int FLAGS_verbosity;

#ifndef LOGGING
#define LOGGING 0
#endif

#define LOG_ENABLED(i) (LOGGING && FLAGS_verbosity >= i)
#define LOG(i) if (LOG_ENABLED(i)) Logger(__FILE__,__LINE__)
#define CHECK(expr) AbortLogger(__FILE__,__LINE__,expr)
#define CHECK_NO_OVERFLOW(x, y) \
    AbortLogger(__FILE__,__LINE__,\
                std::numeric_limits<x>::min() <= (y) &&  \
                std::numeric_limits<x>::max() >= (y)) << \
    "Overflow/underflow detected setting variable of type " << #x \
    << ": " << #y << " = " << y << ". "
#define UNSAT_EXIT UnsatExit()
#define PRINT std::cerr

struct Logger {
    Logger(const std::string& filename, int line) {
        PRINT << "c [" << filename << ":" << line << "] ";
    }

    ~Logger() { PRINT << std::endl; }

    template<class T>
    Logger& operator<<(const T& msg) {
        PRINT << msg;
        return *this;
    }
};

struct AbortLogger {
    AbortLogger(const std::string& filename, int line, bool check_passed) :
      enabled_(!check_passed) {
        if (!enabled_) return;
        PRINT << "s UNKNOWN" << std::endl;
        PRINT << "c [FATAL " << filename << ":" << line << "] ";
    }

    ~AbortLogger() {
        if (!enabled_) return;
        PRINT << std::endl;
        exit(EXIT_FAILURE);
    }

    template<class T>
    AbortLogger& operator<<(const T& msg) {
        if (enabled_) PRINT << msg;
        return *this;
    }

private:
    bool enabled_;
};

void UnsatExit() {
    PRINT << "s UNSATISFIABLE" << std::endl;
    exit(UNSATISFIABLE);
}

#endif  // __LOGGING_H__
