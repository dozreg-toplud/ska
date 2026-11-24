"""Writes the cases of the gate +run of the door of +comp (door axis 2047) as
Lean definitions: `python3 runcases.py 0,1,7` writes the bodies of the cases
%0, %1, %7 out as literals and the others as `(slot? k comp.door).getD (A 0)`
(names c, 0, 1, 2, 3, 4, 5, 6, 7, 10, 11, mean; see Compiler/CompRunLink.lean)."""
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import *
def comp(a, b):
    k = b.bit_length() - 1
    return (a << k) | (b - (1 << k))
door = ('R','comp.door')
AARM = 2047
arm = slot(AARM, door)
AB = comp(comp(AARM, 6), 29)
B = slot(AB, door)
ABAT = comp(AB, 13)
BAT = slot(ABAT, door)
ASN = comp(ABAT, 2); ADOL = comp(ABAT, 3)
assert eqn(slot(ASN, door), slot(2, BAT))
names = ['c', '0', '1', '2', '3', '4', '5', '6', '7', '10', '11', 'mean']
explicit = set(sys.argv[1].split(',')) if len(sys.argv) > 1 else set()
out = []
out.append('def crSn : Noun :=\n  ' + lean(slot(2, BAT)) + '\n')
ax = ADOL
rest_axes = []
for i, nm in enumerate(names):
    body_ax = comp(ax, 14)
    body = slot(body_ax, door)
    if nm in explicit:
        out.append('def crK%s : Noun :=\n  %s\n' % (nm, lean(body)))
    else:
        out.append('def crK%s : Noun := (slot? %d comp.door).getD (A 0)\n' % (nm, body_ax))
    ax = comp(ax, 15)
out.append('def crLast : Noun := (slot? %d comp.door).getD (A 0)\n' % ax)
print('\n'.join(out))
print('-- axes: arm', AARM, 'B', AB, 'BAT', ABAT, 'sn', ASN, 'dol', ADOL)
print('-- bunt', lean(slot(6, slot(6, arm))))
print('-- hint', lean(slot(7, arm)))
