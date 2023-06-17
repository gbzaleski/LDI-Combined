from z3 import *

S = ["001010011101", "1001010101011", "101101010101010",
    "10111011001010101010", "10110101011010101010", "10110101101010101010"]
n = 74 # tight?

# how to declare a list of n variables x0, ..., x(n-1)
x = [ Bool('x' + str(k)) for k in range(n) ]

# Solution for S: 001010011101101011010101010100101010101110110010101010101101010110101010100

# this procedure returns an assignment (as a dictionary) if any exists
def model(phi):
    
    # create a SAT instance
    s = Solver()
    s.add(phi)

    # return a satisfying assignment
    return s.model() if s.check() == sat else []

#phi = And([x[k] for k in range(n)])

x = [Bool('x_' + str(k)) for k in range(n)]

phi_main = []

for w in S:
    phi_word = [] # Or
    for i in range(n - len(w) + 1):
        phi_w_pos = [] # And
        for p, v in enumerate(w):
            if p + i < n:
                phi_w_pos.append(x[p+i] if v == '1' else Not(x[p+i]))

        phi_word.append(And(phi_w_pos))
    phi_main.append(Or(phi_word))



phi_main = And(phi_main)
solution = model(phi_main)
#print(solution)
if solution != []:
    #print([(var, solution[var]) for var in x])
    print(''.join(['1' if solution[var] else '0' for var in x]))

    print([w in ''.join(['1' if solution[var] else '0' for var in x]) for w in S])
else:
    print("No solution")


########################################################


p = Bool("p")
q = Bool("q")
r = Bool("r")
phi = Or(And(p, Not(q)), r)
#phi = Or(p,q,r)
# Pro tip 1: can enumerate all variables by looking at the keys of m
# Pro tip 2: if x is a key of m,
# the corresponding Z3 variable can be reconstructed with "Bool(str(x))"
# (it should be just "x", but so is life)

while True:
    solution = model(phi)
    if solution == []:
        break

    print(solution)
    block_clause = []
    vars = [Bool(str(x)) for x in solution]
    for v in vars:
        if solution[v]:
            block_clause.append(v)
        else:
            block_clause.append(Not(v))


    phi = And(phi, Not(And(block_clause)));
    #print(phi)

#############################################################

import matplotlib.pyplot as plt
import numpy as np
import random

# number of variables
n = 10

# size of a clause
k = 3

# number of samples per point
N = 100

variables = [Bool('x_' + str(i)) for i in range(n)]

# Hints:
# np.random.choice(list) returns a random element from list
# np.random.choice(list, k, replace=False) returns k random elements from list *without replacement*
# np.mean(list) computes the average of the numbers in the list
# plt.plot(list) generates a plot from a list of values
# plt.show() displays the plot

results = []
for m in range(1, 10*n):
    results.append(0);
    for _ in range(N):
        formula = And([Or(list(map(lambda lit: random.choice([lit, Not(lit)]) , np.random.choice(variables, k, replace=False)))) for _ in range(m)])
        if model(formula) != []:
            results[-1] += 1
    results[-1] /= N
    print(f"{(m+1)/10*n}%") # Takes ~2 mins

#phi = Or(list(map(lambda lit: random.choice([lit, Not(lit)]) , np.random.choice(variables, k, replace=False))))

print(results)
plt.plot(results)
plt.show()