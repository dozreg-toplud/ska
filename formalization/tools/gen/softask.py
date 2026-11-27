"""`+soft-ask` (line 5227, battery axis 109246 of the door `comp`, core axis 0x2aabe): the gate
`[8 [1 BUNT] [1 BODY] [0 1]]`, BODY = `[6 [9 1398 0 7] [0 30] [10 [1022 JAB] [0 30]]]` (`?: dropping
gen`, else `soft` set to the `+jab:by`), the gate body of the `+jab` named `saskGB`.

    tools/capped.sh -m 3G python3 tools/gen/softask.py

prints the Lean defs `saskBunt`, `saskGB`, `saskBody`, `saskArm`."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import *

D = ('R', 'comp.door')
arm = norm(slot(109246, D))
op, bunt, rest = arm[1], norm(arm[2])[1], norm(arm[2])[2]
assert norm(op) == ('A', 8)
q1, bq = norm(rest)[1], norm(rest)[2]
assert norm(norm(q1)[1]) == ('A', 1)
body = norm(q1)[2]
assert eqn(bq, ('C', ('A', 0), ('A', 1)))
# body = [6 [9 1398 0 7] [0 30] [10 [1022 JAB] [0 30]]]
b = norm(body)
assert norm(b[1]) == ('A', 6)
t = norm(b[2])
assert eqn(t[1], ('C', ('A', 9), ('C', ('A', 1398), ('C', ('A', 0), ('A', 7)))))
t2 = norm(t[2])
assert eqn(t2[1], ('C', ('A', 0), ('A', 30)))
ed = norm(t2[2])
assert norm(ed[1]) == ('A', 10)
jab = norm(norm(norm(ed[2])[1])[2])
# find the gate body: [1 GB] inside [8 [1 BUNT2] [1 GB] 0 1]
def find_gb(n):
    n = norm(n)
    if n[0] != 'C':
        return None
    h = norm(n[1])
    if h == ('A', 10):
        t = norm(n[2])
        if norm(t[1])[0] == 'C' and norm(norm(t[1])[1]) == ('A', 4095):
            return n
    return find_gb(n[1]) or find_gb(n[2])
gb = find_gb(jab)
assert gb is not None
subs = []
print('def saskBunt : Noun :=\n  %s\n' % lean(bunt))
print('def saskGB : Noun :=\n  %s\n' % lean(gb))
subs = [('saskGB', gb)]
print('def saskBody : Noun :=\n  %s\n' % lean(body, subs))
