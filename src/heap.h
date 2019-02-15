#ifndef __HEAP_H__
#define __HEAP_H__

#include <ctime>
#include <cstdlib>
#include <vector>

#include <sstream>

#include "flags.h"
#include "logging.h"
#include "types.h"

extern unsigned long FLAGS_seed;

// max heap, stores variables
template <unsigned int D>
struct Heap {
    Heap(lit_t nvars) :
      hloc(nvars + 1),
      heap(nvars),
      key(nvars + 1, 0.0) {
        if (FLAGS_seed != 1) {
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
        if (hloc[l] == -1) return;
        hloc[l] = heap.size();
        heap.push_back(l);
        siftup(heap.size() - 1);
    }

    lit_t delete_max() {
        if (heap.empty()) return lit_nil;
        hloc[heap[0]] = -1;
        lit_t m = heap[0];
        heap[0] = heap[heap.size() - 1];
        heap.pop_back();
        hloc[heap[0]] = 0;
        siftdown(0);
        return m;
    }

    void increase_key(lit_t l, double delta) {
        CHECK(delta > 0);
        key[l] += delta;
        siftup(hloc[l]);
    }

    void siftup(size_t i) {
        if (i == 0) return;
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
        while (c != 0 && key[heap[c]] > key[heap[i]]) {
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

    std::vector<size_t> hloc; // -1 == nil, hloc is 1-indexed.
    std::vector<lit_t> heap;  // heap is 0-indexed.
    std::vector<double> key;  // key is 1-indexed
};

#endif  // __HEAP_H__
