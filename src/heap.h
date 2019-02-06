#ifndef __HEAP_H__
#define __HEAP_H__

#include <ctime>
#include <cstdlib>
#include <vector>

#include "flags.h"
#include "types.h"

extern unsigned long FLAGS_seed;

// max heap, stores variables
template <unsigned int D>
struct Heap {
    Heap(lit_t nvars) :
      hloc(nvars + 1),
      heap(nvars),
      act(nvars + 1, 0.0) {
        if (FLAGS_seed != 1) {
            FLAGS_seed = time(NULL);
        }
        srand(FLAGS_seed);
        // Initialize hloc to a random permutation of [1,n]
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
        hloc[l] = heap.size();
        heap.push_back(l);
        siftup(heap.size() - 1);
    }

    lit_t delete_max() {

    }

    void increase_key(lit_t l, double delta) {
        act[l] += delta;
        siftup(hloc[l]);
    }

    void siftup(size_t i) {
        lit_t v = heap[i];
        size_t p = (i - 1) / D;
        while (p != 0 && act[heap[p]] < act[heap[i]]) {
            heap[i] = heap[p];
            hloc[heap[i]] = i;
            i = p;
            p = (p - 1) / D;
        }
        heap[i] = v;
        hloc[heap[i]] = i;
    }

    void siftdown(size_t i) {
        lit_t v = heap[i];
        size_t c = max_child(i);
        while (c != 0 && act[heap[c]] > act[heap[i]]) {
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
        double max_val = act[heap[first_index]];
        size_t last_index = std::min(D * (i + 1), heap.size() - 1);
        for (size_t j = first_index + 1; j <= last_index; ++j) {
            if (act[heap[j]] > max_val) {
                max_val = act[heap[j]];
                max_index = j;
            }
        }
        return max_index;
    }

    std::vector<size_t> hloc;  // -1 == nil

    // Heap is zero-indexed.
    std::vector<lit_t> heap;

    std::vector<double> act;
};

#endif  // __HEAP_H__
