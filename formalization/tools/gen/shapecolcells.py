"""Cell counts of the arms of `+shape-collapse` in the pill (README Gaps 9).

    tools/capped.sh -m 3G python3 tools/gen/shapecolcells.py

For each arm of `K` that `+shape-collapse` runs on a lazy need with forks:
its axis, its `%fast` name if any, and the cells of the arm (shared
subnouns counted at each occurrence)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import *

K = ('C', ('R', 'nh5592f9d7750f'), ('C', ('R', 'nh15c74912d225'), ('C', ('A', 0), ('R', 'ana'))))
memo = {}
def cells(n):
    n = norm(n)
    if n[0] == 'A':
        return 0
    k = id(n)
    if k in memo:
        return memo[k]
    r = 1 + cells(n[1]) + cells(n[2])
    memo[k] = r
    return r

ARMS = [(682, 'shape-collapse'), (6006, 'lazy-to-inter1'), (0xbbbb, 'inter1-to-inter2'),
        (1406, 'inter2-collapse'), (0xaebdf, 'inter2-fix-round'), (1367, 'inter2-orig'),
        (2794, 'uni-need-ord'), (20, 'msg-need-ord'), (350, 'cons-need')]
for ax, nm in ARMS:
    a = slot(ax, K)
    print('%-24s axis %-8s cells %6d' % (nm, hex(ax) if ax > 9999 else ax, cells(a)))
# the other arms, found by their `%fast` names
for nm in ['msg-need-ord-fix-aware', 'need-to-ordered', 'inter2-collapse-nested']:
    c = ('A', int.from_bytes(nm.encode(), 'little'))
    for ax, arm in arms(K):
        a = norm(arm)
        if a[0] == 'C' and norm(a[2]) and contains_atom(norm(a[2]), c[1]) and cells(arm) < 3000:
            print('%-24s axis %-8s cells %6d' % (nm, hex(ax) if ax > 9999 else ax, cells(arm)))
