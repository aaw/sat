#ifndef __TYPES_H__
#define __TYPES_H__

#include <cassert>
#include <cstdint>
#include <limits>

// TODO: add a few #ifdefs here to change types from 8 bit/16 bit/32 bit
typedef int16_t lit_t;
typedef uint16_t clause_t;

constexpr lit_t lit_nil = lit_t(0);
constexpr clause_t clause_nil = std::numeric_limits<clause_t>::max();

#define ASSERT_NO_OVERFLOW(x, y) \
    assert(std::numeric_limits<x>::min() <= (y) && \
           std::numeric_limits<x>::max() >= (y));

#endif  // __TYPES_H__
