#ifndef __PARSE_H__
#define __PARSE_H__

#include <vector>

// TODO: templatize this with lit_t, clause_t
struct Instance {
    typedef int lit_t;
    typedef int clause_t;  // TODO: make unsigned int, start indexing at 1!

    int nvars;
    int nclauses;
    std::vector<lit_t> clauses;
    // Zero-indexed map of clauses. Clause i runs from clauses[start[i]]
    // to clauses[start[i+1]-1] (or clauses[clauses.size()-1]
    // if i == start.size() - 1).
    std::vector<clause_t> start;

    // Link to another clause with the same watched literal.
    std::vector<clause_t> link;
    std::vector<clause_t> watch_storage;
    clause_t* watch;
};

Instance parse(const char* filename);

#endif  // __PARSE_H__
