#!/usr/bin/python3

from itertools import chain, combinations
import unittest

import langford

def powerset(x):
    return chain.from_iterable(combinations(x, r) for r in range(len(x)+1))

# Is there an assignment of free_vars along with the partial assignment that
# makes clauses satisfiable?
def satisfiable(clauses, partial, free_vars):
    for true_free in powerset(free_vars):
        false_free = free_vars - set(true_free)
        all_vars = set(partial) | set(true_free + tuple(-x for x in false_free))
        sat = True
        for clause in clauses:
            if not set(clause) & all_vars:
                sat = False
                break
        if sat:
            return True
    return False

# Given a CNF boolean formula represented by a list of tuples, verify that the
# formula returns true iff at most one of original variables is true.
def verify_clauses(c, orig_vars):
    orig_vars = set(orig_vars)
    vs = set(abs(var) for clause in c for var in clause)
    new_vars = vs - orig_vars
    for true_vars in powerset(orig_vars):
        false_vars = orig_vars - set(true_vars)
        all_vars = set(true_vars + tuple(-x for x in false_vars))
        sat = satisfiable(c, all_vars, new_vars)
        if sat and len(set(true_vars) & orig_vars) > 1:
            return False
        if not sat and len(set(true_vars) & orig_vars) <= 1:
            return False
    return True

class TestLangford(unittest.TestCase):
    def gen_at_most_one_test(self, x):
        orig_vars = [i for i in range(1,x+1)]
        c = langford.at_most_one(orig_vars)
        self.assertTrue(verify_clauses(c, orig_vars))

    def test_at_most_one_2(self):
        self.gen_at_most_one_test(2)

    def test_at_most_one_3(self):
        self.gen_at_most_one_test(3)

    def test_at_most_one_4(self):
        self.gen_at_most_one_test(4)

    def test_at_most_one_5(self):
        self.gen_at_most_one_test(5)

    def test_at_most_one_6(self):
        self.gen_at_most_one_test(6)

    def test_at_most_one_7(self):
        self.gen_at_most_one_test(7)

    def test_at_most_one_8(self):
        self.gen_at_most_one_test(8)

    def gen_compressed_at_most_one_test(self, x):
        f = langford.compressed_at_most_one(x+1)
        orig_vars = [i for i in range(1,x+1)]
        c = f(orig_vars)
        self.assertTrue(verify_clauses(c, orig_vars))

    def test_compressed_at_most_one_2(self):
        self.gen_compressed_at_most_one_test(2)

    def test_compressed_at_most_one_3(self):
        self.gen_compressed_at_most_one_test(3)

    def test_compressed_at_most_one_4(self):
        self.gen_compressed_at_most_one_test(4)

    def test_compressed_at_most_one_5(self):
        self.gen_compressed_at_most_one_test(5)

    def test_compressed_at_most_one_6(self):
        self.gen_compressed_at_most_one_test(6)

    def test_compressed_at_most_one_7(self):
        self.gen_compressed_at_most_one_test(7)

    def test_compressed_at_most_one_8(self):
        self.gen_compressed_at_most_one_test(8)

    def test_compressed_at_most_one_9(self):
        self.gen_compressed_at_most_one_test(9)

    def test_compressed_at_most_one_10(self):
        self.gen_compressed_at_most_one_test(10)

    def test_compressed_at_most_one_11(self):
        self.gen_compressed_at_most_one_test(12)

    def test_compressed_at_most_one_13(self):
        self.gen_compressed_at_most_one_test(13)

if __name__ == '__main__':
    unittest.main()
