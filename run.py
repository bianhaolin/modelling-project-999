
from functools import total_ordering
from os import umask
from nnf import Var, NNF
from lib204 import Encoding
import pprint

from nnf import true

"""
000
001
010
011 <- pre
100 <- post
101
110
111
"""



x_pre = []
pres = []
x_post = []
posts = []
BITS = 4

counts = []
count_post = []

partial_counts = {}
partial_count_vars = {}



class Bit(object):
    def __init__(self, name):
        self.name = name
    def __hash__(self):
        return hash(self.name)
    def __str__(self):
        return self.name
    def __repr__(self):
        return str(self)

for i in range(BITS):
    pre = Bit(f'pre_{i}')
    post = Bit(f'post_{i}')
    cpost = Bit(f'cpost_{i}')
    pres.append(pre)
    posts.append(post)
    counts.append(cpost)
    x_pre.append(Var(pre))
    x_post.append(Var(post))
    count_post.append(Var(cpost))

final_count = Bit(f'cpost_{BITS}')
counts.append(final_count)
count_post.append(Var(final_count))

for i in range(BITS):
    partial_counts[i] = {}
    partial_count_vars[i] = {}
    for j in range(BITS+1):
        pc = Bit(f'count_by_i{i}_is_{j}')
        pcv = Var(pc)
        partial_counts[i][j] = pc
        partial_count_vars[i][j] = pcv

def iff(left, right):
    return (left.negate() | right) & (right.negate() | left)


def display_solution(sol):
    bitvec_pre = ''
    bitvec_post = ''
    for p in pres:
        bitvec_pre += {True: '1', False: '0'}[sol.get(p, False)]
    for p in posts:
        bitvec_post += {True: '1', False: '0'}[sol.get(p, False)]

    post_count = -1
    for i in range(BITS+1):
        if sol.get(counts[i], True):
            post_count = i
    print("   Pre: "+bitvec_pre)
    print("  Post: "+bitvec_post)
    print("|Post|: %d\n" % post_count)

def extract_solution(sol):
    bitvec = ''
    for p in posts:
        bitvec += {True: '1', False: '0'}[sol.get(p, False)]
    return bitvec

def set_pre(bits):
    f = true
    for i in range(BITS):
        if bits[i] == '0':
            f = f & ~x_pre[i]
        else:
            f = f & x_pre[i]
    return f


def example_theory():
    E = Encoding()

    # Final index
    E.add_constraint(iff(x_post[-1], ~x_pre[-1]))

    # Rest of the indices
    for i in range(len(x_pre)-1):
        # Set for everything to the right
        needs_to_flip = true
        for j in range(i+1, len(x_pre)):
            needs_to_flip &= x_pre[j]
        E.add_constraint(iff(x_post[i], (needs_to_flip & ~x_pre[i]) | (x_pre[i] & needs_to_flip.negate())))

    # Final partial counts should be equal to the full count
    for c in range(BITS+1):
        E.add_constraint(iff(count_post[c], partial_count_vars[BITS-1][c]))

    # You can't have more true bits than you've already seen
    for i in range(BITS):
        for c in range(i+2, BITS+1):
            E.add_constraint(~partial_count_vars[i][c])

    # First index: only 0 or 1 could possibly be true
    E.add_constraint(iff(partial_count_vars[0][0], ~x_post[0]))
    E.add_constraint(iff(partial_count_vars[0][1], x_post[0]))

    # General pattern: look at the smaller sequence of bits to decide the current one
    for i in range(1, BITS):
        E.add_constraint(iff(partial_count_vars[i][0], partial_count_vars[i-1][0] & ~x_post[i]))
        for c in range(1,i+2):
            increased = partial_count_vars[i-1][c-1] & x_post[i]
            stay_same = partial_count_vars[i-1][c] & ~x_post[i]
            E.add_constraint(iff(partial_count_vars[i][c], increased | stay_same))
            # print("Define the constraint for index %d = %d" % (i,c))

    return E


if __name__ == "__main__":

    T = example_theory()

    # print("\nSatisfiable: %s" % T.is_satisfiable())
    # print("# Solutions: %d" % T.count_solutions())
    # print("   Solution: %s" % T.solve())

    T0 = example_theory()
    total_models = T.count_solutions()

    T = example_theory()
    # T.add_constraint(~x_pre[2] & x_post[2])
    # sol = T.solve()
    # if not sol:
    #     print("Not solvable!!")
    #     exit(1)
    # display_solution(sol)
    # print("Models: %d" % T.count_solutions())
    # print("Models as percent: %.2f" % (T.count_solutions() / total_models))

    bitvec = '0'*BITS
    for i in range(2**BITS):
        T = example_theory()
        T.add_constraint(set_pre(bitvec))
        sol = T.solve()
        display_solution(sol)
        # print(bitvec)
        bitvec = extract_solution(sol) # return '001'


    # print("\nVariable likelihoods:")
    # for v,vn in zip(x_post, '01234'):
    #     print(" %s: %.2f" % (vn, T.likelihood(v)))
    # print()
