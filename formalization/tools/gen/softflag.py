"""The `|` side of `+soft-free` (README Gaps 21.22) for `CompSccLoopSoftTryFlag.lean`: the arm of `+soft-try`
(line 5517, battery slot 3497463 of `comp.door`, `ty_st_at` checks it by `kernel_rfl`) and the battery of the
gate `flag` (`tpYH0Bat` of `CompSccLoopSoftTryCut.lean`, line 5370), cut at their pushes with the chain
cutter of `softtrycut.py` (`tyT` the battery of `+soft-try`, `tyF` that of `flag`, `tyX` the head that makes
`[first f]`, `tyN` / `tyL` the traps of `fla` and of the tries); writes the definitions between
`-- BEGIN softflag` and `-- END softflag` of OUTFILE.

    tools/capped.sh -m 3G python3 tools/gen/softflag.py lemmas/Compiler/CompSccLoopSoftTryFlag.lean
"""
import os, re, sys
sys.setrecursionlimit(100000)
HERE = os.path.dirname(os.path.abspath(__file__))
OUT = sys.argv[1]
src = open(os.path.join(HERE, 'softtrycut.py')).read()
ns = {'__file__': os.path.join(HERE, 'softtrycut.py')}
exec(src[:src.index("v = parse_text(defs['seTryPath'])")], ns)
cut = open(os.path.join(HERE, '..', '..', 'lemmas', 'Compiler', 'CompSccLoopSoftTryCut.lean')).read()
d = dict(re.findall(r'def (\w+) : Noun :=\n  (.*)\n', cut))
parse_text, show, cells, chain = ns['parse_text'], ns['show'], ns['cells'], ns['chain']
sys.path.insert(0, HERE)
import nouns
door = nouns.get('comp.door')


def conv(n):
    n = nouns.norm(n)
    if n[0] == 'A':
        return ('a', n[1])
    return ('c', conv(n[1]), conv(n[2]))


arm = conv(nouns.slot(3497463, door))
# the gate literal [8 [1 bunt] [1 bat] [0 1]]
assert arm[1] == ('a', 8) and arm[2][1][1] == ('a', 1) and arm[2][2][1][1] == ('a', 1) and arm[2][2][2] == ('c', ('a', 0), ('a', 1))
bunt, bat = arm[2][1][2], arm[2][2][1][2]
assert cells(arm) == 1 + 2 + cells(bunt) + 1 + 1 + cells(bat) + 1, cells(arm)
ns['out'].clear(); ns['shapes'].clear()
ns['out'].append(('tyStBunt', show(bunt)))
chain('tyT', bat, 0)
ns['out'].append(('tyStArm', '(C (A 8) (C (C (A 1) tyStBunt) (C (C (A 1) tyT0) (C (A 0) (A 1)))))'))
fb = parse_text(d['tpYH0Bat'])
chain('tyF', fb, 0)
# the head of `=^  [first f]  gen` (push 5 of tyF): its own chain tyX; in it the trap of `fla`
# (tyXH4 = [7 [0 1] [8 lent [8 [1 tyNTrap] [9 2 [0 1]]]]]) and that of the tries (tyXH9 = [1 tyLTrap])
fh5 = fb
for _ in range(5):
    fh5 = fh5[2][2]
fh5 = fh5[2][1]
assert fh5[1] == ('a', 7)
x = fh5
xs = []
cur = x
while cur[0] == 'c' and cur[1][0] == 'a' and cur[1][1] in (7, 8) and cur[2][0] == 'c':
    xs.append(cur[2][1]); cur = cur[2][2]
assert len(xs) == 10 and cur == ('c', ('a', 9), ('c', ('a', 2), ('c', ('a', 0), ('a', 1))))
h4, h9 = xs[4], xs[9]
assert h9[1] == ('a', 1)
ns['out'].append(('tyLTrap', show(h9[2])))
lent_, rest = h4[2][2][2][1], h4[2][2][2][2]
assert h4[2][1] == ('c', ('a', 0), ('a', 1)) and h4[2][2][1] == ('a', 8)
assert rest[1] == ('a', 8) and rest[2][1][1] == ('a', 1) and rest[2][2] == ('c', ('a', 9), ('c', ('a', 2), ('c', ('a', 0), ('a', 1))))
ns['out'].append(('tyNTrap', show(rest[2][1][2])))
ns['out'].append(('tyNLent', show(lent_)))
ns['out'].append(('tyXH4', '(C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C tyNLent (C (A 8) (C (C (A 1) tyNTrap) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))))'))
ns['out'].append(('tyXH9', '(C (A 1) tyLTrap)'))
for i in range(9, -1, -1):
    op = 8 if i in (1, 2, 4, 7, 8, 9) else 7
    hd = 'tyXH%d' % i if i in (4, 9) else show(xs[i])
    rest_ = 'tyX%d' % (i + 1) if i < 9 else '(C (A 9) (C (A 2) (C (A 0) (A 1))))'
    ns['out'].append(('tyX%d' % i, '(C (A %d) (C %s %s))' % (op, hd, rest_)))
text = '\n'.join('def %s : Noun :=\n  %s\n' % x for x in ns['out'])
text = '/- chains:\n' + '\n'.join(ns['shapes']) + '\n-/\n\n' + text
s = open(OUT).read()
b = s.index('\n-- BEGIN softflag\n') + len('\n-- BEGIN softflag\n')
e = s.index('\n-- END softflag\n', b) + 1
open(OUT, 'w').write(s[:b] + '\n' + text + '\n' + s[e:])
print('\n'.join(ns['shapes']))
