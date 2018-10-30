#ifndef __PARSE_H__
#define __PARSE_H__

// TODO: templatize this with lit_t, clause_t
struct Instance {
    int nvars;
    int nclauses;
    int* clauses;
    int* size;
};

Instance parse(const char* filename);

#endif  // __PARSE_H__
