#ifndef __PARSE_H__
#define __PARSE_H__

#include <limits>
#include <vector>

// TODO: templatize this with lit_t, clause_t
struct Instance {
    typedef int lit_t;
    typedef unsigned int clause_t;

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

    static const clause_t null_clause;
};

Instance parse(const char* filename);

#endif  // __PARSE_H__
