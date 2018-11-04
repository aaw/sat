#ifndef __LOGGING_H__
#define __LOGGING_H__

#include <iostream>

#ifndef LOGLEVEL
#define LOGLEVEL 4
#endif  // LOGLEVEL

#define LOG(i) logger(__FILE__,__LINE__,i)

struct logger {
    logger(const std::string& filename, int line, int level)
#ifdef LOGGING
      : enabled_(level <= LOGLEVEL) {
        if (enabled_) std::cout << "[" << filename << ":" << line << "] ";
#else
    {
#endif  // LOGGING
    }

    ~logger() {
#ifdef LOGGING
        if (enabled_) std::cout << std::endl;
#endif  // LOGGING
    }

    template<class T>
    logger& operator<<(const T& msg) {
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

#endif  // __LOGGING_H__
