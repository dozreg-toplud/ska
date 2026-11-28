"""The arm `+soft-cons` (line 5674 of desk/lib/nock-compilation.hoon, battery slot 12 of
`comp.door`) cut into named nouns for `lemmas/Compiler/CompSccLoopSoftTryCons.lean`
(README Gaps 21.22).  Writes the definitions into OUTFILE between `-- BEGIN softcons` and
`-- END softcons`.

    tools/capped.sh -m 3G python3 tools/gen/softcons.py lemmas/Compiler/CompSccLoopSoftTryCons.lean

The arm is the gate `[8 [1 tcBunt] [1 tcBat] [0 1]]`, `tcBat` is `=/ axe 1` and the trap
`tcTrap`: `[8 tcGet tcT1]` (`(~(get by tops) axe)`), `tcT1` the `?^ t` (`tcNC` the test, `tcMiss`
when `~`, `tcHit` `[[~ u.t] gen]`), `tcMiss` the tests `%this` (`tcThis`), `%both` (`tcBoth`),
`%none` (`tcNone`), else the cell (`tcPair`: `=/ [h t] ned`, then `tcP1` .. `tcP13`, the `=^` of
the head (`tcRecH` the recursion, `tcEdH` the edit of `gen`), the tail (`tcRecT`, `tcEdT`), `re`
(`tcRe`, `tcEdR`) and the product `tcProd`)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import nouns
from nouns import norm, lean
OUT = sys.argv[1]
door = nouns.get('comp.door')
arm = norm(nouns.slot(12, door))


def full(n):
    n = norm(n)
    if n[0] == 'A':
        return n
    return ('C', full(n[1]), full(n[2]))


arm = full(arm)


def sl(ax, n):
    for b in bin(ax)[3:]:
        assert n[0] == 'C'
        n = n[1] if b == '0' else n[2]
    return n


def isA(n, v):
    return n[0] == 'A' and n[1] == v


# arm = [8 [1 bunt] [1 bat] [0 1]]
assert isA(sl(2, arm), 8) and isA(sl(12, arm), 1) and isA(sl(28, arm), 1) and sl(15, arm) == ('C', ('A', 0), ('A', 1))
bunt = sl(13, arm)
bat = sl(29, arm)
# bat = [8 [1 1] [8 [1 trap] [9 2 [0 1]]]]
assert isA(sl(2, bat), 8) and sl(6, bat) == ('C', ('A', 1), ('A', 1))
assert isA(sl(14, bat), 8) and isA(sl(60, bat), 1)
trap = sl(61, bat)
assert sl(31, bat) == ('C', ('A', 9), ('C', ('A', 2), ('C', ('A', 0), ('A', 1))))
# trap = [8 get t1]
assert isA(sl(2, trap), 8)
get = sl(6, trap)
t1 = sl(7, trap)
assert isA(sl(2, t1), 6)
nc, miss, hit = sl(6, t1), sl(14, t1), sl(15, t1)
assert isA(sl(2, miss), 6)
isThis, this, m2 = sl(6, miss), sl(14, miss), sl(15, miss)
isBoth, both, m3 = sl(6, m2), sl(14, m2), sl(15, m2)
isNone, none, pair = sl(6, m3), sl(14, m3), sl(15, m3)
assert isA(sl(2, pair), 8)
p = [sl(7, pair)]
heads = []
while isA(sl(2, p[-1]), 7) or isA(sl(2, p[-1]), 8):
    heads.append((sl(2, p[-1])[1], sl(6, p[-1])))
    p.append(sl(7, p[-1]))
assert len(p) == 13, len(p)
names = {1: None, 2: 'tcRecH', 3: 'tcEdH', 4: None, 5: None, 6: 'tcRecT', 7: 'tcEdT', 8: None,
         9: None, 10: 'tcRe', 11: 'tcEdR', 12: None}
defs = []
defs.append(('tcProd', lean(p[12])))
for i in range(12, 0, -1):
    op, h = heads[i - 1]
    hn = names[i]
    if hn:
        defs.append((hn, lean(h)))
        ht = hn
    else:
        ht = lean(h)
    rest = 'tcProd' if i == 12 else 'tcP%d' % (i + 1)
    defs.append(('tcP%d' % i, '(C (A %d) (C %s %s))' % (op, ht, rest)))
defs.append(('tcPair', '(C (A 8) (C %s tcP1))' % lean(sl(6, pair))))
for nm, v in [('tcNone', none), ('tcBoth', both), ('tcThis', this), ('tcIsNone', isNone), ('tcIsBoth', isBoth),
              ('tcIsThis', isThis), ('tcHit', hit), ('tcNC', nc), ('tcGet', get)]:
    defs.append((nm, lean(v)))
defs.append(('tcM3', '(C (A 6) (C tcIsNone (C tcNone tcPair)))'))
defs.append(('tcM2', '(C (A 6) (C tcIsBoth (C tcBoth tcM3)))'))
defs.append(('tcMiss', '(C (A 6) (C tcIsThis (C tcThis tcM2)))'))
defs.append(('tcT1', '(C (A 6) (C tcNC (C tcMiss tcHit)))'))
defs.append(('tcTrap', '(C (A 8) (C tcGet tcT1))'))
defs.append(('tcBunt', lean(bunt)))
defs.append(('tcBat', '(C (A 8) (C (C (A 1) (A 1)) (C (A 8) (C (C (A 1) tcTrap) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))'))
defs.append(('tcArm', '(C (A 8) (C (C (A 1) tcBunt) (C (C (A 1) tcBat) (C (A 0) (A 1)))))'))
text = '\n'.join('def %s : Noun :=\n  %s\n' % d for d in defs)
src = open(OUT).read()
b = src.index('-- BEGIN softcons\n') + len('-- BEGIN softcons\n')
e = src.index('-- END softcons')
open(OUT, 'w').write(src[:b] + '\n' + text + '\n' + src[e:])
print('wrote', len(defs), 'definitions')
