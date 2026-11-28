"""Print the arm `+msg-need-ord-kept` (arm `178934` of `K`, since 2a5b618) as Lean
definitions, cut as `+msg-need-ord` is in `Compiler/CompMemOld.lean`: the gate
`[8 [1 BUNT] [1 BODY] 0 1]`, `BODY = [7 [0 1] [6 [5 [0 12] [0 26]] [0 12] REST]]`
(the `?:  =(new old)  new`), `REST` the branches after it.

    tools/capped.sh -m 3G python3 tools/gen/keptarm.py"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import slot, norm, lean

K = ('C', ('R', 'nh290d8f32435a'), ('C', ('R', 'nh15c74912d225'), ('C', ('A', 0), ('R', 'ana'))))

def full(n):
    n = norm(n)
    return n if n[0] == 'A' else ('C', full(n[1]), full(n[2]))

A = lambda v: ('A', v)
arm = full(slot(178934, K))
assert arm[1] == A(8), arm[1]
bunt = arm[2][1]; rest1 = arm[2][2]
assert bunt[1] == A(1) and rest1[1][1] == A(1) and rest1[2] == ('C', A(0), A(1)), 'gate shape'
body = rest1[1][2]
assert body[1] == A(7) and body[2][1] == ('C', A(0), A(1)), 'body = [7 [0 1] ..]'
test = body[2][2]
assert test[1] == A(6), 'a ?:'
cond, yes, rest = test[2][1], test[2][2][1], test[2][2][2]
assert cond == ('C', A(5), ('C', ('C', A(0), A(12)), ('C', A(0), A(26)))), 'the =(new old)'
assert yes == ('C', A(0), A(12)), 'new'
print('/-- The branches of `+msg-need-ord-kept` after `?:  =(new old)  new`. -/')
print('def keptRest : Noun :=\n  ' + lean(rest) + '\n')
print('/-- The gate body of `+msg-need-ord-kept`. -/')
print('def keptBody : Noun :=\n  (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 0) (A 12)) (C (A 0) (A 26)))) (C (C (A 0) (A 12)) keptRest)))))\n')
print('/-- Its sample bunt. -/')
print('def keptBunt : Noun :=\n  ' + lean(bunt[2]) + '\n')
