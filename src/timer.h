#ifndef __TIMER_H__
#define __TIMER_H__

#include <ctime>

#include "logging.h"

extern bool FLAGS_time;

class Timer {
public:
    Timer() {
        if (!FLAGS_time) return;
        begin_ = clock();
    }
    ~Timer() {
        if (!FLAGS_time) return;        
        clock_t end = clock();
        PRINT << "c Time: "
              << static_cast<double>(end - begin_) / CLOCKS_PER_SEC
              << " seconds" << std::endl;
    }
private:
    clock_t begin_=0;  // 0-initialized to avoid gcc warning.
};

#endif  // __TIMER_H__
