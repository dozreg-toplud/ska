"""The arms +soft-new (door axis 254, 71 cells) and +soft-bond (door axis 442, 296 cells) of
the door of +comp as Lean literals: each arm is [8 [1 bunt] [1 battery] 0 1].  Prints the defs
snArm, snBat, sbArm, sbBat for lemmas/Compiler/CompRunSoftArms.lean.  Run from formalization/
under tools/capped.sh -m 4G."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import *
def cells(n):
    n = norm(n)
    return 0 if n[0] == 'A' else 1 + cells(n[1]) + cells(n[2])
for ax, nm, want in ((254, 'sn', 71), (442, 'sb', 296)):
    f = slot(ax, ('R', 'comp.door'))
    assert cells(f) == want, (ax, cells(f))
    f = norm(f)
    assert norm(f[1]) == ('A', 8)
    r = norm(f[2]); bat = norm(norm(norm(r[2])[1])[2])
    assert norm(norm(norm(r[2])[1])[1]) == ('A', 1)
    print('def %sBat : Noun :=\n  %s\n' % (nm, lean(bat)))
    print('def %sArm : Noun :=\n  %s\n' % (nm, lean(f, sub=[('%sBat' % nm, bat)])))
