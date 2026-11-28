"""The cut of `+uni-ju` (arm `1404` of `ana`, 134 cells, README Gaps 23,
track P) into named parts, as Lean definitions: each part a `getD` slot of
its parent, its shape (with the names of its own parts) checked by
`kernel_rfl`.

    tools/capped.sh -m 3G python3 tools/gen/ujcut.py lemmas/Compiler/PokeLinkTailJets.lean

    ++  uni-ju                                   ujArm: [8 [1 0] [[1 ujBatA] [0 1]]]
      |*  a=(jug)                                ujBatA: [8 [0 6] [[1 ujBatB] [0 1]]]
      |*  b=_a                                   ujBatB: [6 [5 [1 0] [0 6]] [0 30] ujRep]
      ?:  =(~ b)  a                              ujRep: the `+rep:by` of `b`, its gate
      %-  ~(rep by b)                              [8 ujSam [[1 ujStep] [0 1]]]
      |=  [[p q] =_a]                            ujStep: the battery of the gate
      (~(put by a) p (~(uni in (~(get ju a) p)) q))

Writes the definitions between `-- BEGIN ujcut` and `-- END ujcut` of
OUTFILE and prints the cells."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import *
OUT = sys.argv[1]
def cells(n):
    n = norm(n)
    if n[0] == 'A': return 0
    return 1 + cells(n[1]) + cells(n[2])
def full(n):
    n = norm(n)
    if n[0] == 'A': return n
    return ('C', full(n[1]), full(n[2]))
def ax(path):
    a = 1
    for c in path:
        a = 2 * a + (0 if c == 'h' else 1)
    return a
def at(n, path):
    for c in path:
        assert n[0] == 'C', path
        n = n[1] if c == 'h' else n[2]
    return n
ana = ('R', 'ana')
PARTS = [
    ('ujArm', None, None, 'the arm `+uni-ju`: the wet gate on `a`'),
    ('ujBatA', 'ujArm', 'ttht', 'the battery of the gate on `a`: the wet gate on `b`'),
    ('ujBatB', 'ujBatA', 'ttht', 'the battery of the gate on `b`'),
    ('ujRep', 'ujBatB', 'ttt', 'the `+rep:by` of `b`'),
    ('ujSam', 'ujRep', 'tttttht' + 'ttth', 'the bunt of the sample of the step gate'),
    ('ujStep', 'ujRep', 'tttttht' + 'ttttht', 'the battery of the step gate'),
]
N = {}
N['ujArm'] = full(slot(1404, ana))
assert cells(N['ujArm']) == 134, cells(N['ujArm'])
for nm, par, path, doc in PARTS[1:]:
    N[nm] = at(N[par], path)
txt_of = {}
for nm, par, path, doc in PARTS:
    kids = [x[0] for x in PARTS if x[1] == nm]
    txt_of[nm] = lean(N[nm], [(k, N[k]) for k in kids])
lines = []
for nm, par, path, doc in PARTS:
    if par is None:
        lines.append(f'/-- {doc}, {cells(N[nm])} cells: axis `1404` of `ana`. -/\n'
                     f'def {nm} : Noun := (slot? 1404 ana).getD (A 0)')
    else:
        lines.append(f'/-- {doc}, {cells(N[nm])} cells: axis `{ax(path)}` of `{par}`. -/\n'
                     f'def {nm} : Noun := (slot? {ax(path)} {par}).getD (A 0)')
    print(f'{nm:10} cells {cells(N[nm])}')
lines.append('')
for nm, par, path, doc in PARTS:
    lines.append(f'theorem {nm}_eq : {nm} = {txt_of[nm]} := by kernel_rfl')
lines.append('')
lines.append('/-- `+uni-ju` is the arm `1404` of `ana`. -/\n'
             'theorem ana_ujArm : slot? 1404 ana = some ujArm := by kernel_rfl')
text = '\n'.join(lines) + '\n'
src = open(OUT).read()
b = src.index('-- BEGIN ujcut\n') + len('-- BEGIN ujcut\n')
e = src.index('-- END ujcut')
open(OUT, 'w').write(src[:b] + text + src[e:])
print('wrote', OUT, len(text), 'chars')
