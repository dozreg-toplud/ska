"""The cut of `spRest` (the baking half of `+ska-poke`, 1,120 cells, README
Gaps 23, track P) into the chain of its 14 pushes and the rest, as Lean
definitions.

    tools/capped.sh -m 3G python3 tools/gen/sprestcut.py lemmas/Compiler/PokeLinkRestCut.lean

`spRest` is `[op_0 P_0 [op_1 P_1 ... [op_13 P_13 END]]]` with `op_i` `7` or
`8`.  Each pushed part `P_i` gets the name of its Hoon part (`srDat` the gate
`dat`, ..., `srCalls` the write of `calls`), the rest after push `i` is
`srK<i+1>` (`srK0` is `spRest` itself, `srK14` is `srEnd`), so that
`srK<i> = [op_i P_i srK<i+1>]` holds by `rfl` and `spRest = srK0` by
`kernel_rfl`.  Writes the definitions between `-- BEGIN sprestcut` and
`-- END sprestcut` of OUTFILE and prints the parts with their cells."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nouns import *
OUT = sys.argv[1]
NAMES = ['srDat', 'srRoot', 'srJet', 'srBakeId', 'srBake', 'srVarsEd', 'srSwap', 'srNew',
         'srSccs', 'srLoop', 'srCores', 'srJets', 'srSeek', 'srCalls']
HOON = ['the gate `dat`', '`root-bell`', 'the gate `jetted`', 'the `[0 1]` of `=^  [baked vars.lon]`',
        'the call of `+bake-graph`', 'the write of `vars.lon`', 'the swap `[[0 4] [0 3]]` of `=^`',
        '`new-code` (`~(rep by baked)`)', '`sccs`: `+tarjan` under `%poke-tarjan`, flopped',
        'the SCC loop under `%poke-scc-loop` with `+eval-finalized`', '`new-cores`',
        'the edit of `jets.lon`', 'the write of `seek.lon`', 'the write of `calls.lon`']
memo = {}
def cells(n):
    def go(n):
        if n[0] == 'R':
            k = n[1]
            if k not in memo: memo[k] = go(get(k))
            return memo[k]
        if n[0] == 'A': return 0
        return 1 + go(n[1]) + go(n[2])
    return go(n)
sp = slot(44826492927, ('R', 'ana'))
parts = []
n = norm(sp)
while True:
    h = norm(n[1]); t = norm(n[2])
    if n[0] == 'C' and h[0] == 'A' and h[1] in (7, 8) and t[0] == 'C' and len(parts) < len(NAMES):
        parts.append((h[1], t[1]))
        n = norm(t[2])
    else:
        break
assert len(parts) == len(NAMES), len(parts)
out = []
for i, (op, p) in enumerate(parts):
    print(f'{i:2} op{op} {NAMES[i]:9} cells {cells(p)}')
    q = norm(p)
    gate = None
    if q[0] == 'C' and norm(q[1]) == ('A', 8):
        r = norm(q[2]); bu = norm(r[1]); rr = norm(r[2])
        if bu[0] == 'C' and norm(bu[1]) == ('A', 1) and rr[0] == 'C' and eqn(rr[2], ('C', ('A', 0), ('A', 1))):
            ba = norm(rr[1])
            if ba[0] == 'C' and norm(ba[1]) == ('A', 1):
                gate = (bu[2], ba[2])
    if gate:
        nm = NAMES[i]
        out.append(f'/-- The bunt of the sample of the gate of push {i}. -/\ndef {nm}Bunt : Noun :=\n  {lean(gate[0])}')
        out.append(f'/-- The battery of the gate of push {i}. -/\ndef {nm}Bat : Noun :=\n  {lean(gate[1])}')
        out.append(f'/-- Push {i} of `spRest` (`%{op}`): {HOON[i]}, {cells(p)} cells: a gate `[8 [1 bunt] [1 bat] [0 1]]`. -/\n'
                   f'def {nm} : Noun :=\n  C (A 8) (C (C (A 1) {nm}Bunt) (C (C (A 1) {nm}Bat) (C (A 0) (A 1))))')
    else:
        out.append(f'/-- Push {i} of `spRest` (`%{op}`): {HOON[i]}, {cells(p)} cells. -/\n'
                   f'def {NAMES[i]} : Noun :=\n  {lean(p)}')
print(f'   end srEnd cells {cells(n)}')
out.append(f'/-- The end of `spRest`: `+ska-cole-update` and the product, {cells(n)} cells. -/\n'
           f'def srEnd : Noun :=\n  {lean(n)}')
out.append(f'/-- The rest of `spRest` after its 14 pushes. -/\ndef srK{len(parts)} : Noun := srEnd')
for i in range(len(parts) - 1, -1, -1):
    op = parts[i][0]
    out.append(f'/-- The rest of `spRest` from push {i}. -/\n'
               f'def srK{i} : Noun := C (A {op}) (C {NAMES[i]} srK{i + 1})')
text = '\n\n'.join(out) + '\n'
src = open(OUT).read()
b = src.index('-- BEGIN sprestcut\n') + len('-- BEGIN sprestcut\n')
e = src.index('-- END sprestcut')
open(OUT, 'w').write(src[:b] + text + src[e:])
print('wrote', OUT, len(text), 'chars')
