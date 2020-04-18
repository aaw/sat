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
#define LOG_EVERY_N(i, n) \
    static int VARNAME(__c, __LINE__) = 0; ++VARNAME(__c, __LINE__); \
    if (LOG_ENABLED(i) && (VARNAME(__c, __LINE__) % n == 0)) \
        Logger(__FILE__,__LINE__)
#define LOG_N_TIMES(i, n) \
    static int VARNAME(__c, __LINE__) = n;              \
    if (LOG_ENABLED(i) && VARNAME(__c, __LINE__)-- > 0) \
        Logger(__FILE__,__LINE__)
#define LOG_ONCE(i) LOG_N_TIMES(i, 1)
#define LOG_EVERY_N_SECS(i, n) \
    static clock_t VARNAME(__c, __LINE__) = 0; \
    bool VARNAME(__log, __LINE__) = false; \
    if (LOG_ENABLED(i) &&                                   \
        static_cast<double>(clock()-VARNAME(__c, __LINE__)) \
        /CLOCKS_PER_SEC > n) { \
        VARNAME(__log, __LINE__) = true; \
        VARNAME(__c, __LINE__) = clock(); } \
    if (VARNAME(__log, __LINE__)) Logger(__FILE__,__LINE__)
#define CHECK(expr) if (!(expr)) AbortLogger(__FILE__,__LINE__)
#define CHECK_NO_OVERFLOW(x, y) \
    CHECK(std::numeric_limits<x>::min() <= (y) &&  \
          std::numeric_limits<x>::max() >= (y)) << \
    "Overflow/underflow detected setting variable of type " << #x \
    << ": " << #y << " = " << y << ". "
#define UNSAT_EXIT UnsatExit()
#define SAT_EXIT(c) { (c)->print_assignment(); SatExit(); }
#define PRINT std::cout

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
    AbortLogger(const std::string& filename, int line) {
        PRINT << "s UNKNOWN" << std::endl;
        PRINT << "c [FATAL " << filename << ":" << line << "] ";
    }

    ~AbortLogger() {
        PRINT << std::endl;
        exit(EXIT_FAILURE);
    }

    template<class T>
    AbortLogger& operator<<(const T& msg) {
        PRINT << msg;
        return *this;
    }

private:
    bool enabled_;
};

void UnsatExit() {
    PRINT << "s UNSATISFIABLE" << std::endl;
    exit(UNSATISFIABLE);
}

void SatExit() {
    PRINT << "s SATISFIABLE" << std::endl;
    exit(SATISFIABLE);
}

#endif  // __LOGGING_H__
