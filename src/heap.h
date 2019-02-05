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

    }

    void increase_key(lit_t l, double delta) {
        act[l] += delta;
        siftup(hloc[l]);
    }

    void siftup(size_t i) {
        lit_t v = heap[i];
        size_t p = (i + D - 2) / D; // ceil((i - 1) / D)
        while (p != 0 && act[heap[p]] < act[heap[i]]) {
            heap[i] = heap[p];
            hloc[heap[i]] = i;
            i = p;
            p = (p + D - 2) / D; // ceil((p - 1) / D)
        }
        heap[i] = v;
        hloc[heap[i]] = i;
    }

    void siftdown(size_t i) {

    }

    size_t min_child(size_t i) {
    }

    lit_t delete_max() {
        if (heap.empty()) return lit_nil;
        lit_t k = heap[0];
        hloc[k] = -1;
        size_t h = heap.size() - 1;
        lit_t i = heap[h];
        heap.pop_back();
        double a = act[i];
        size_t j = 0;
        for(size_t jp = 1; jp < h;) {
            double ap = act[heap[jp]];
            if (jp + 1 < h && act[heap[jp + 1]] > ap) {
                ++jp;
                ap = act[heap[jp]];
            }
            if (a >= ap) {
                jp = h;
            } else {
                heap[j] = heap[jp];
                hloc[heap[jp]] = j;
                j = jp;
                jp = 2*j + 1;
            }
            heap[j] = i;
            hloc[i] = j;
        }
        return k;
    }

    void insert(lit_t) {

    }

    std::vector<size_t> hloc;  // -1 == nil

    // Heap is zero-indexed.
    std::vector<lit_t> heap;

    std::vector<double> act;
};

#endif  // __HEAP_H__
