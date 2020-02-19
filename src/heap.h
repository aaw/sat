#ifndef __HEAP_H__
#define __HEAP_H__

#include <cmath>
#include <ctime>
#include <cstdlib>
#include <vector>

#include <sstream>

#include "counters.h"
#include "flags.h"
#include "logging.h"
#include "types.h"
#include "params.h"

extern unsigned long FLAGS_seed;

const double kMaxScore = pow(10,100);
const double kHeapNil = std::numeric_limits<size_t>::max();
const double kNegInf = std::numeric_limits<double>::min();

DEFINE_PARAM(heap_rho, 0.96,
             "Scaling factor for literal activities. The bump applied to "
             "all active literals is divided by this factor after each epoch.");

DEFINE_PARAM(heap_d, 32,
             "d-heap parameter defining the branching factor of the heap.");

// TODO: clean up and document now that this is used by both CDCL and lookahead
// in slightly different ways.

// max heap, stores variables
struct Heap {
    Heap(lit_t nvars, size_t D=PARAM_heap_d) :
    hloc(nvars + 1, kHeapNil),
      key(nvars + 1, 0.0),
      D(D),
      delta(1.0),
      max_key(kNegInf) {
    }

    // Initialize heap for CDCL by adding all vars and shuffling their order.
    void shuffle_init() {
        // TODO: set seed in some central location, not here.
        if (FLAGS_seed == 0) FLAGS_seed = time(NULL);
        srand(FLAGS_seed);
        // Initialize heap to a random permutation of [1,n]
        heap.resize(hloc.size() - 1, 0);
        for (size_t i = 1; i < hloc.size(); ++i) {
            int r = rand() % i;
            heap[i-1] = heap[r];
            heap[r] = i;
        }
        for (size_t i = 0; i < heap.size(); ++i) {
            hloc[heap[i]] = i;
        }
    }

    void clear() {
        for (lit_t h : heap) {
            hloc[h] = kHeapNil;
        }
        heap.clear();
    }

    bool empty() {
        return heap.empty();
    }

    size_t size() {
        return heap.size();
    }

    void insert(lit_t l, double val=kNegInf) {
        if (hloc[l] != kHeapNil) return;
        hloc[l] = heap.size();
        heap.push_back(l);
        if (val != kNegInf) key[l] = val;
        siftup(heap.size() - 1);
    }

    lit_t delete_max() {
        if (heap.empty()) return lit_nil;
        hloc[heap[0]] = kHeapNil;
        lit_t m = heap[0];
        heap[0] = heap[heap.size() - 1];
        heap.pop_back();
        if (heap.size() > 0) {
            hloc[heap[0]] = 0;
            siftdown(0);
        }
        return m;
    }

    lit_t peek() {
        return heap[0];
    }

    // Get a random element from the heap.
    lit_t rpeek() {
        return heap[rand() % heap.size()];
    }

    double act(lit_t l) {
        return key[l];
    }

    double avg() {
        double sum = 0;
        for (lit_t v : heap) {
            sum += key[v];
        }
        return sum / heap.size();
    }

    void bump(lit_t l) {
        key[l] += delta;
        if (key[l] > max_key) {
            max_key = key[l];
        }
        siftup(hloc[l]);
    }

    void rescale_delta() {
        delta /= PARAM_heap_rho;
        if (max_key >= kMaxScore) {
            INC(rescale_heap_delta);
            LOG(2) << "Scaling all heap scores down.";
            for (size_t i = 1; i < key.size(); ++i) {
                key[i] /= kMaxScore;
            }
            delta /= kMaxScore;
            max_key /= kMaxScore;
        }
    }

    void siftup(size_t i) {
        if (i == 0 || i == kHeapNil) return;
        lit_t v = heap[i];
        size_t p = (i - 1) / D;
        while (key[heap[p]] < key[heap[i]]) {
            heap[i] = heap[p];
            hloc[heap[i]] = i;
            i = p;
            if (p == 0) break;
            p = (p - 1) / D;
        }
        heap[i] = v;
        hloc[heap[i]] = i;
    }

    void siftdown(size_t i) {
        lit_t v = heap[i];
        size_t c = max_child(i);
        while (c != 0 && key[heap[c]] > key[v]) {
            heap[i] = heap[c];
            hloc[heap[i]] = i;
            i = c;
            c = max_child(i);
        }
        heap[i] = v;
        hloc[heap[i]] = i;
    }

    size_t max_child(size_t i) {
        size_t first_index = D * i + 1;
        if (first_index > heap.size() - 1) return 0;
        size_t max_index = first_index;
        double max_val = key[heap[first_index]];
        size_t last_index = std::min(D * (i + 1), heap.size() - 1);
        for (size_t j = first_index + 1; j <= last_index; ++j) {
            if (key[heap[j]] > max_val) {
                max_val = key[heap[j]];
                max_index = j;
            }
        }
        return max_index;
    }

    std::string debug() {
        std::ostringstream s;
        s << std::endl << "hloc: ";
        for (size_t i = 1; i < hloc.size(); ++i) {
            s << "[" << i << ":" << hloc[i] << "]";
        }
        s << std::endl << "heap: ";
        for (size_t i = 0; i < heap.size(); ++i) {
            s << "[" << heap[i] << "]";
        }
        s << std::endl << "act: ";
        for (size_t i = 1; i < key.size(); ++i) {
            s << "[" << i << ":" << key[i] << "]";
        }
        return s.str();
    }

    std::vector<size_t> hloc; // kHeapNil == nil, hloc is 1-indexed.
    std::vector<lit_t> heap;  // heap is 0-indexed.
    std::vector<double> key;  // key is 1-indexed
    const size_t D;
    double delta;
    double max_key;
};

#endif  // __HEAP_H__
