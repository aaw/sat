#ifndef __HEAP_H__
#define __HEAP_H__

#include <cmath>
#include <ctime>
#include <cstdlib>
#include <vector>

#include <sstream>

#include "flags.h"
#include "logging.h"
#include "types.h"
#include "params.h"

extern unsigned long FLAGS_seed;

const double kMaxScore = pow(10,100);

DEFINE_PARAM(heap_rho, 0.96,
             "Scaling factor for literal activities. The bump applied to "
             "all active literals is divided by this factor after each epoch.");

DEFINE_PARAM(heap_d, 8,
             "d-heap parameter defining the branching factor of the heap.");

// max heap, stores variables
// TODO: make D a param that can change at runtime, not a template parameter
struct Heap {
    Heap(lit_t nvars, size_t D=PARAM_heap_d) :
      hloc(nvars + 1),
      heap(nvars),
      key(nvars + 1, 0.0),
      D(D),
      delta(1.0),
      max_key(std::numeric_limits<double>::min()) {
        if (FLAGS_seed == 0) {
            FLAGS_seed = time(NULL);
        }
        srand(FLAGS_seed);
        // Initialize heap to a random permutation of [1,n]
        for (int i = 1; i <= nvars; ++i) {
            int r = rand() % i;
            heap[i - 1] = heap[r];
            heap[r] = i;
        }
        for (int i = 0; i < nvars; ++i) {
            hloc[heap[i]] = i;
        }
    }

    void insert(lit_t l) {
        LOG(4) << "HEAP inserting " << l;
        if (hloc[l] != std::numeric_limits<size_t>::max()) return;
        LOG(4) << "HEAP inserted " << l;
        hloc[l] = heap.size();
        heap.push_back(l);
        siftup(heap.size() - 1);
    }

    lit_t delete_max() {
        if (heap.empty()) return lit_nil;
        hloc[heap[0]] = std::numeric_limits<size_t>::max();
        lit_t m = heap[0];
        heap[0] = heap[heap.size() - 1];
        heap.pop_back();
        if (heap.size() > 0) {
            hloc[heap[0]] = 0;
            siftdown(0);
        }
        LOG(4) << "HEAP deleting " << m;
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
            INC("rescale heap delta");
            LOG(2) << "Scaling all heap scores down.";
            for (size_t i = 1; i < key.size(); ++i) {
                key[i] /= kMaxScore;
            }
            delta /= kMaxScore;
            max_key /= kMaxScore;
        }
    }
    
    void siftup(size_t i) {
        if (i == 0 || i == std::numeric_limits<size_t>::max()) return;
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

    std::vector<size_t> hloc; // std::numeric_limits<size_t>::max() == nil, hloc is 1-indexed.
    std::vector<lit_t> heap;  // heap is 0-indexed.
    std::vector<double> key;  // key is 1-indexed
    const size_t D;
    double delta;
    double max_key;
};

#endif  // __HEAP_H__
