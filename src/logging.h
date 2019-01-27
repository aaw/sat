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
#define UNSAT_EXIT UnsatExit()

struct Logger {
    Logger(const std::string& filename, int line) {
        std::cout << "c [" << filename << ":" << line << "] ";
    }

    ~Logger() { std::cout << std::endl; }

    template<class T>
    Logger& operator<<(const T& msg) {
        std::cout << msg;
        return *this;
    }
};

struct AbortLogger {
    AbortLogger(const std::string& filename, int line, bool check_passed) :
      enabled_(!check_passed) {
        if (!enabled_) return;
        std::cout << "s UNKNOWN" << std::endl;
        std::cout << "c [FATAL " << filename << ":" << line << "] ";
    }

    ~AbortLogger() {
        if (!enabled_) return;
        std::cout << std::endl;
        exit(EXIT_FAILURE);
    }

    template<class T>
    AbortLogger& operator<<(const T& msg) {
        if (enabled_) std::cout << msg;
        return *this;
    }

private:
    bool enabled_;
};

void UnsatExit() {
    std::cout << "s UNSATISFIABLE" << std::endl;
    exit(UNSATISFIABLE);
}

#endif  // __LOGGING_H__
