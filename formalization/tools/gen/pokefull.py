"""The %full branch of the pill's inner +poke, cut at its calls (track P,
lemmas/Compiler/PokeLinkFull.lean).  Matches a template of the glue against
the branch and prints each named call formula as a Lean literal, and the
other branches of the dispatch.  Run: python3 tools/gen/pokefull.py"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import *

cor = ('R', 'cor')
arm = slot(23, cor)
bat = slot(29, arm)          # [8 [1 0] [1 bat] [0 1]]
R = slot(7, bat)             # [8 ipokeB ipokeR]

def P(x):
    """template: int -> atom, str -> name, tuple -> cell (right-assoc list)"""
    if isinstance(x, int): return ('A', x)
    if isinstance(x, str): return ('V', x)
    if len(x) == 1: return P(x[0])
    return ('C', P(x[0]), P(x[1:]))

def match(t, n, env):
    n = norm(n)
    if t[0] == 'V':
        if t[1] in env:
            assert eqn(env[t[1]], n), t[1]
        env[t[1]] = n; return True
    if t[0] == 'A':
        return n[0] == 'A' and n[1] == t[1]
    if n[0] != 'C': return False
    return match(t[1], n[1], env) and match(t[2], n[2], env)

full, fast, jets, ska = 0x6c6c7566, 0x74736166, 0x7374656a, 0x616b73
# ipokeR = [6 [5 [1 %jets] 0 4] bJ [6 [5 [1 %fast] 0 4] bF [6 [5 [1 %full] 0 4] fullF bD]]]
disp = P((6, (5, (1, jets), (0, 4)), 'bJ', (6, (5, (1, fast), (0, 4)), 'bF', (6, (5, (1, full), (0, 4)), 'fullF', 'bD'))))
env = {}
assert match(disp, R, env), 'dispatch'
FB = env['fullF']
glue = P((7, (0, 1), (8, 'skaF',
  (7, (10, (1018, 0, 5), 0, 1), (7, ((0, 4), 0, 3), (8, 'getF',
  (6, (6, (3, 0, 2), (6, 'hasF', (1, 0), 1, 1), 1, 1),
     (8, ((1, 0x73696874, 0), (1, 1), 'putF'), ((1, 0x7269), (0, 28), (0, 2), 0, 29), 0, 127),
     (7, (0, 1), (8, 'sccF', (7, (10, (0xffbe, 0, 5), 0, 1), (7, ((0, 4), 0, 3),
       (7, (0, 1), (8, 'monoF', (7, (10, (0x3ff7, 0, 5), 0, 1), (7, ((0, 4), 0, 3),
         (8, 'optF', ((1, 0x7269), (0, 124), (0, 2), 0, 125), 0, 511))))))))))))))))
env2 = {}
assert match(glue, FB, env2), 'glue'
def cells(n):
    n = norm(n)
    return 0 if n[0] == 'A' else 1 + cells(n[1]) + cells(n[2])
for k in ['skaF', 'getF', 'hasF', 'putF', 'sccF', 'monoF', 'optF']:
    print('-- %s: %d cells' % (k, cells(env2[k])))
    print('def %sP : Noun :=\n  %s\n' % (k, lean(env2[k])))
print('-- fullF %d cells, ipokeR %d cells' % (cells(FB), cells(R)))
