"""The cut of `srLoop` (push 9 of `spRest`, the SCC loop of `+ska-poke` under
`%poke-scc-loop`, 243 cells, README Gaps 23, track P) into named parts, as
Lean definitions, and the size of `+eval-finalized` (arm `0x57de` of `ana`).

    tools/capped.sh -m 3G python3 tools/gen/loopcut.py lemmas/Compiler/PokeLinkLoopCut.lean

The parts, by the Hoon of the loop:

    =.  lon
      =<  $  ~%  %poke-scc-loop  ..ride  ~  |.        lpBat   (the |. trap)
      |-  ^-  long-ska                                lpBat2  (the |- trap)
      ?~  sccs  lon                                   lpNo    (the ?~ no branch)
      =/  scc  i.sccs
      =/  loc1  (~(rep in scc) |=([b acc] (~(put by acc) b [nomm:(got new-code) | |])))
                                                      lpLoc1 = [8 lpDoor1 [9 2 [10 [6 [7 [0 3] [8 lpBunt1 [[1 lpG1] [0 1]]]]] [0 2]]]]
      =;  loc2  (=.  code.lon  loc2  scc-loop(sccs t.sccs))
                                                      lpTail
      (~(rep in scc) |=([b acc] (~(jab by acc) b ..(eval-finalized b acc)..)))
                                                      lpLoc2 (lpDoor2, lpBunt2, lpG2)

Each name is defined by the names below it, so that `srLoop = lpTop` is one
`kernel_rfl` and the parts are `rfl` facts.  Writes the definitions between
`-- BEGIN loopcut` and `-- END loopcut` of OUTFILE and prints the cells."""
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
def at(n, path):
    for c in path:
        assert n[0] == 'C', path
        n = n[1] if c == 'h' else n[2]
    return n
sp = full(slot(44826492927, ('R', 'ana')))
n = sp
for i in range(9):
    n = n[2][2]
loop = n[2][1]
assert cells(loop) == 243, cells(loop)
F = at(loop, 'tht')
bat = at(F, 'ththt')
clue = at(F, 'thttthtt')
bat2 = at(bat, 'tht')
no = at(bat2, 'ttttt')
loc1 = at(no, 'ttth')
r2 = at(no, 'tttt')
loc2 = at(r2, 'th')
tail = at(r2, 'tt')
def gate(L):
    G = at(L, 'tttttht')
    return at(L, 'th'), at(G, 'ttth'), at(G, 'ttttht')
door1, bunt1, g1 = gate(loc1)
door2, bunt2, g2 = gate(loc2)
# the call of +eval-finalized in lpG2 and the jab after it
efCall = at(g2, 'th')
jab = at(g2, 'tt')
parts = [  # (name, noun, doc), leaves first
    ('lpClue', clue, 'the clue of `~%  %poke-scc-loop  ..ride  ~`'),
    ('lpDoor1', door1, 'the door `~(rep in scc)` of `loc1`'),
    ('lpBunt1', bunt1, 'the sample bunt of the gate of `loc1`: `[*bell code.lon]`'),
    ('lpG1', g1, 'the gate of `loc1`: `(~(put by acc) b [nomm:(~(got by new-code) b) | |])`'),
    ('lpDoor2', door2, 'the door `~(rep in scc)` of `loc2`'),
    ('lpBunt2', bunt2, 'the sample bunt of the gate of `loc2`: `[*bell loc1]`'),
    ('lpEf', efCall, 'the call `(eval-finalized b acc)` (arm `0x57de` of the core at `0x1fffff`)'),
    ('lpJab', jab, 'the `~(jab by acc)` that writes the flags'),
    ('lpG2', g2, 'the gate of `loc2`: `=/  [pure total]  (eval-finalized b acc)` then `+jab:by`'),
    ('lpLoc1', loc1, '`loc1`: the members of the SCC put with `[| |]`'),
    ('lpLoc2', loc2, '`loc2`: each member set to `+eval-finalized`'),
    ('lpTail', tail, '`=.  code.lon  loc2` and the recursion `scc-loop(sccs t.sccs)`'),
    ('lpNo', no, 'the branch of a nonempty `sccs`'),
    ('lpBat2', bat2, 'the battery of the `|-` trap `scc-loop`'),
    ('lpBat', bat, 'the battery of the `|.` trap under `%poke-scc-loop`'),
    ('lpF', F, 'the trap: built, hinted, run'),
]
subs = []
out = []
for nm, nn, doc in parts:
    txt = lean(nn, subs)
    out.append(f'/-- {doc}, {cells(nn)} cells. -/\ndef {nm} : Noun :=\n  {txt}')
    print(f'{nm:8} cells {cells(nn)}')
    subs.insert(0, (nm, nn))
top = lean(loop, subs)
out.append(f'/-- `srLoop` from its parts. -/\ndef lpTop : Noun :=\n  {top}')
ef = slot(0x57de, ('R', 'ana'))
print('eval-finalized (arm 0x57de of ana) cells', cells(ef))
text = '\n\n'.join(out) + '\n'
src = open(OUT).read()
b = src.index('-- BEGIN loopcut\n') + len('-- BEGIN loopcut\n')
e = src.index('-- END loopcut')
open(OUT, 'w').write(src[:b] + text + src[e:])
print('wrote', OUT, len(text), 'chars')
