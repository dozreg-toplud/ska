"""The map of `+compiled-mono` (arm `10` of axis `3` of `cor`, README Gaps 19 (g), track K):
the arm, its gate battery cut into pushes, the cells and calls of each part.

    tools/capped.sh -m 3G python3 tools/gen/monolink.py tools/gen
"""
import sys
sys.path.insert(0, sys.argv[1])
from nouns import *
cor = ('R', 'cor')
c3 = slot(3, cor)
arm = slot(10, c3)
def cells(n):
    n = norm(n)
    if n[0] == 'A': return 0
    return 1 + cells(n[1]) + cells(n[2])
print('arm 10 of axis 3: cells', cells(arm))
print(show(arm, maxd=40)[:6000])
def full(n, d=0):
    n = norm(n)
    if n[0] == 'A':
        return str(n[1])
    return '[' + full(n[1], d+1) + ' ' + full(n[2], d+1) + ']'
print(full(arm))
def L(n):
    n = norm(n)
    if n[0] == 'A': return '(A %d)' % n[1]
    return '(C %s %s)' % (L(n[1]), L(n[2]))
bunt = slot(6, arm)   # [8 [1 bunt] ...]: axis 6 is [1 bunt]
bat = slot(14, arm)   # axis 14: [1 BAT]
print('BUNT', L(slot(3, bunt)))
B = slot(3, bat)
print('GET', L(slot(6, B)))
print('TEST', L(slot(14, B)))
print('MISS', L(slot(30, B)))
print('HIT', L(slot(31, B)))
print('MISSF', L(slot(62, B)))
print('SAMF', L(slot(6, slot(30, slot(15, slot(7, slot(62, B)))))) if False else '')
