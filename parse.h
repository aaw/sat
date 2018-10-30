#ifndef __PARSE_H__
#define __PARSE_H__

#include <vector>

// TODO: templatize this with lit_t, clause_t
struct Instance {
    int nvars;
    int nclauses;
    std::vector<int> clauses;
    std::vector<int> start;
    std::vector<int> next;
};

Instance parse(const char* filename);

#endif  // __PARSE_H__
