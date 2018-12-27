#ifndef __LOGGING_H__
#define __LOGGING_H__

#include <iostream>

#ifndef LOGLEVEL
#define LOGLEVEL 5
#endif  // LOGLEVEL

#define LOG(i) Logger(__FILE__,__LINE__,i)

struct Logger {
    Logger(const std::string& filename, int line, int level)
#ifdef LOGGING
      : enabled_(level <= LOGLEVEL) {
        if (enabled_) std::cout << "c [" << filename << ":" << line << "] ";
#else
    {
#endif  // LOGGING
    }

    ~Logger() {
#ifdef LOGGING
        if (enabled_) std::cout << std::endl;
#endif  // LOGGING
    }

    template<class T>
    Logger& operator<<(const T& msg) {
#ifdef LOGGING
        if (enabled_) std::cout << msg;
#endif  // LOGGING
        return *this;
    }

#ifdef LOGGING
private:
    bool enabled_;
#endif  // LOGGING
};

#define CHECK(expr) AbortLogger(__FILE__,__LINE__,expr)

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
        if (!enabled_) return *this;
        std::cout << msg;
        return *this;
    }

private:
    bool enabled_;
};

#endif  // __LOGGING_H__
