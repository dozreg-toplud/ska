"""The cut of `+eval-finalized` (arm `0x57de` of `ana`, 1,066 cells, README
Gaps 23, track P) into named parts, as Lean definitions: each part a `getD`
slot of its parent, its shape (with the names of its own parts) checked by
`kernel_rfl`.

    tools/capped.sh -m 3G python3 tools/gen/efcut.py lemmas/Compiler/PokeLinkEvalCut.lean

The parts, by the Hoon:

    ++  eval-finalized  ~%  %eval-finalized  ..ride  ~
      |=  [b=bell code=(map bell code-entry)]       efArm: [7 [0 1] [7 [8 [1 bunt] [[1 efBat] [0 1]]] [11 ..]]]
      =/  sub=sock  less.b                           efBat: [8 [0 24] [8 efGot [7 [8 [1 [efHave efLoop]] [9 5 0 1]] [0 3]]]]
      =/  =nomm  nomm:(~(got by code) b)             efGot
      =<  +  |^  ?-  nomm ..  ==                     efLoop ($): [7 [0 1] [6 T efCcons [6 T efC0 ..]]]
      ++  have  |=  [=sock axe=@]  ?<  =(0 axe)  |-  efHave, efHGate, efHTrap

Writes the definitions between `-- BEGIN efcut` and `-- END efcut` of
OUTFILE and prints the cells."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import *
OUT = sys.argv[1]
memo = {}
def cells(n):
    if n[0] == 'R':
        k = n[1]
        if k not in memo: memo[k] = cells(get(k))
        return memo[k]
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
# (name, parent, path in parent, doc)
PARTS = [
    ('efArm', None, None, 'the arm `+eval-finalized`: the gate, built and hinted `%fast`'),
    ('efBat', 'efArm', 'ttthttht', 'the battery of the gate'),
    ('efGot', 'efBat', 'ttth', '`nomm:(~(got by code) b)`'),
    ('efHave', 'efBat', 'ttttththt' + 'h', 'the arm `+have` of the `|^` core: the gate'),
    ('efLoop', 'efBat', 'ttttththt' + 't', 'the arm `$` of the `|^` core: the trap `nomm-loop`'),
    ('efHGate', 'efHave', 'ttht', 'the battery of the gate `+have`: `?<  =(0 axe)` then the `|-`'),
    ('efHTrap', 'efHGate', 'ttttht', 'the battery of the `|-` trap of `+have`'),
]
CASES = ['efCcons', 'efC0', 'efC1', 'efC2', 'efC3', 'efC4', 'efC5', 'efC6', 'efC7', 'efC10',
         'efC11', 'efCmean']
TAGS = ['`[p=^ q=*]`', '`%0`', '`%1`', '`%2`', '`%3`', '`%4`', '`%5`', '`%6`', '`%7`', '`%10`',
        '`%11`', '`%mean`']
N = {}
N['efArm'] = full(slot(0x57de, ana))
assert cells(N['efArm']) == 1066, cells(N['efArm'])
for nm, par, path, doc in PARTS[1:]:
    N[nm] = at(N[par], path)
p = 'tt'
for nm, tg in zip(CASES, TAGS):
    PARTS.append((nm, 'efLoop', p + 'tth', f'the case {tg} of `nomm-loop`'))
    N[nm] = at(N['efLoop'], p + 'tth')
    p = p + 'ttt'
PARTS.append(('efC12', 'efLoop', p, 'the last case `%12` of `nomm-loop`, under the `%toss` of `?-`'))
N['efC12'] = at(N['efLoop'], p)
assert cells(N['efHave']) == 150
# leaves first, for the substitution
order = list(reversed([x[0] for x in PARTS]))
out = []
subs = []
done = []
for nm in order:
    kids = [x[0] for x in PARTS if x[1] == nm]
    txt = lean(N[nm], [(k, N[k]) for k in kids])
    done.append(nm)
    out.append((nm, txt))
txt_of = dict(out)
lines = []
for nm, par, path, doc in PARTS:
    if par is None:
        lines.append(f'/-- {doc}, {cells(N[nm])} cells: axis `0x57de` of `ana`. -/\n'
                     f'def {nm} : Noun := (slot? 0x57de ana).getD (A 0)')
    else:
        lines.append(f'/-- {doc}, {cells(N[nm])} cells: axis `{ax(path)}` of `{par}`. -/\n'
                     f'def {nm} : Noun := (slot? {ax(path)} {par}).getD (A 0)')
    print(f'{nm:10} cells {cells(N[nm])}')
lines.append('')
for nm, par, path, doc in PARTS:
    lines.append(f'theorem {nm}_eq : {nm} = {txt_of[nm]} := by kernel_rfl')
lines.append('')
lines.append('/-- `+eval-finalized` is the arm `0x57de` of `ana`. -/\n'
             'theorem ana_efArm : slot? 0x57de ana = some efArm := by kernel_rfl')
text = '\n'.join(lines) + '\n'
src = open(OUT).read()
b = src.index('-- BEGIN efcut\n') + len('-- BEGIN efcut\n')
e = src.index('-- END efcut')
open(OUT, 'w').write(src[:b] + text + src[e:])
print('wrote', OUT, len(text), 'chars')
