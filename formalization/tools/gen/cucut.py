"""The cut of `+ska-cole-update` (arm `2746` of `ana`, 150 cells) and of
`+cole-put` (arm `2814` of `ana`, 60 cells), README Gaps 23, track P, into
named parts, as Lean definitions: each part a `getD` slot of its parent, its
shape (with the names of its own parts) checked by `kernel_rfl`.  Modelled
on `ujcut.py`.

    tools/capped.sh -m 3G python3 tools/gen/cucut.py lemmas/Compiler/PokeLinkColeUpd.lean

    ++  ska-cole-update                     couArm: [7 [8 [1 bunt] [1 couBat] 0 1] 11 %fast 0 1]
      |=  [lon=long-ska new-bells=(set bell) hot=(set ring)]
      =*  cole  cole.jets.lon               couBat: [7 [0 1] 7 [10 [799 couRep] 0 1] 0 12]
      =.  cole
        %-  ~(rep in new-bells)             couRep: [8 rep:in [9 2 10 [6 7 [0 3] 8 couSam [1 couStep] 0 1] 0 2]]
        |=  [b=bell c=_cole]                couStep: got:by of seek (%mean), +cole-match, +cole-put
        =/  sek=cape  ~|(%ska-seek (~(got by seek.lon) b))
        ?~  r=(cole-match b sek core.jets.lon arms.jets.lon hot)  c
        (cole-put b u.r c)
      lon
    ++  cole-put                            cputArm: [8 [1 bunt] [1 cputBat] 0 1]
      |=  [b=bell r=ring c=[call=(map bell ring) back=(jug ring bell)]]
      [(~(put by call.c) b r) (~(put ju back.c) r b)]

Writes the definitions between `-- BEGIN cucut` and `-- END cucut` of
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
ROOTS = {'couArm': (2746, 150), 'cputArm': (2814, 60)}
PARTS = [
    ('couArm', None, None, 'the arm `+ska-cole-update`: the gate with its `%fast` hint'),
    ('couBat', 'couArm', 'thttht', 'the battery of the gate'),
    ('couRep', 'couBat', 'ttththt', 'the `+rep:in` of `new-bells` with its step gate'),
    ('couSam', 'couRep', 'tttttht' + 'ttth', 'the bunt of the sample of the step gate'),
    ('couBunt', 'couSam', 'h', 'the bunt of `bell`'),
    ('couStep', 'couRep', 'tttttht' + 'ttttht', 'the battery of the step gate'),
    ('couGot', 'couStep', 'th', 'the push of `sek`: `got:by` of `seek.lon` under `%mean`'),
    ('couCm', 'couStep', 'ttth', 'the push of the call of `+cole-match`'),
    ('couTl', 'couStep', 'tttt', 'the test of the match and the call of `+cole-put`'),
    ('cputArm', None, None, 'the arm `+cole-put`: the gate'),
    ('cputBat', 'cputArm', 'ttht', 'the battery of `+cole-put`'),
]
N = {}
for nm, (a, c) in ROOTS.items():
    N[nm] = full(slot(a, ana))
    assert cells(N[nm]) == c, (nm, cells(N[nm]))
for nm, par, path, doc in PARTS:
    if par is not None:
        N[nm] = at(N[par], path)
txt_of = {}
for nm, par, path, doc in PARTS:
    kids = [x[0] for x in PARTS if x[1] == nm]
    txt_of[nm] = lean(N[nm], [(k, N[k]) for k in kids])
lines = []
for nm, par, path, doc in PARTS:
    if par is None:
        a = ROOTS[nm][0]
        lines.append(f'/-- {doc}, {cells(N[nm])} cells: axis `{a}` of `ana`. -/\n'
                     f'def {nm} : Noun := (slot? {a} ana).getD (A 0)')
    else:
        lines.append(f'/-- {doc}, {cells(N[nm])} cells: axis `{ax(path)}` of `{par}`. -/\n'
                     f'def {nm} : Noun := (slot? {ax(path)} {par}).getD (A 0)')
    print(f'{nm:10} cells {cells(N[nm])}')
lines.append('')
for nm, par, path, doc in PARTS:
    lines.append(f'theorem {nm}_eq : {nm} = {txt_of[nm]} := by kernel_rfl')
lines.append('')
for nm, (a, c) in ROOTS.items():
    lines.append(f'theorem ana_{nm} : slot? {a} ana = some {nm} := by kernel_rfl')
text = '\n'.join(lines) + '\n'
src = open(OUT).read()
b = src.index('-- BEGIN cucut\n') + len('-- BEGIN cucut\n')
e = src.index('-- END cucut')
open(OUT, 'w').write(src[:b] + text + src[e:])
print('wrote', OUT, len(text), 'chars')
