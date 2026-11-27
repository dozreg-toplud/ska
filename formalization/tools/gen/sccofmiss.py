"""The cut of the cache miss of `+scc-of` (track Q): `sccMiss`, axis `62` of
the battery `sccBat` of arm `96127` of `sccCore` (axis `7` of the library),
373 cells, cut into its parts by axis, each with its cells and the arms it
calls; `lean` prints the Lean definitions (each part a `getD` slot of its
parent) and their shapes (`kernel_rfl`) for
`lemmas/Compiler/CompSccOfMissCut.lean`.

    tools/capped.sh -m 3G python3 tools/gen/sccofmiss.py tools/gen [lean]
"""
import sys, os
sys.path.insert(0, sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__)))
import tarjancut as T
from nouns import *

cor = ('R', 'cor'); lib = slot(15, cor); sc = slot(7, lib)
arm = slot(96127, sc); bat = slot(109, arm); miss = slot(62, bat)
# (name, parent, axis in the parent)
PARTS = [
  ('smSub', 'sccMiss', 6),      # =/ sub: [8 [1 0] [8 [[0 60] [1 0]] [8 [1 smTrap] [9 2 0 1]]]]
  ('smRest', 'sccMiss', 7),     # [7 smRollE smGot]
  ('smTrap', 'smSub', 253),     # the trap: [6 ?~(q) [0 14] smTrapNo]
  ('smTrapNo', 'smTrap', 15),   # [6 smHasQ $(q t.q) smMain]
  ('smHasQ', 'smTrapNo', 6),    # (~(has by sub) i.q)
  ('smMain', 'smTrapNo', 15),   # [8 smCs smRec]
  ('smCs', 'smMain', 6),        # cs: ~(rep in (~(gut by calls) i.q ~)) gate
  ('smGut', 'smCs', 3575),      # (~(gut by calls) i.q ~)
  ('smCsG', 'smCs', 16253),     # the gate: ?:((~(has by sccs) c) acc (~(put in acc) c))
  ('smRec', 'smMain', 7),       # $(q (weld ~(tap in cs) t.q), sub (~(put by sub) i.q cs))
  ('smRollE', 'smRest', 6),     # [10 [123 smRoll] [0 1]]: =. sccs
  ('smRoll', 'smRollE', 13),    # (roll (tarjan sub) gate)
  ('smTj', 'smRoll', 2027),     # (tarjan sub)
  ('smB1', 'smRoll', 16252),    # the bunt of s=(set bell): the mold set (arm 6098) on bell (382)
  ('smGBat', 'smRoll', 32509),  # the roll's gate: (~(rep in s) inner gate)
  ('smB2', 'smGBat', 8124),     # the bunt of m=bell (arm 382)
  ('smIBat', 'smGBat', 16253),  # the inner gate: (~(put by acc) m s)
  ('smGot', 'smRest', 7),       # [(~(got by sccs) b) sccs]
]
OPAQUE = set()
def part_nouns():
    N = {'sccMiss': miss}
    for nm_, par, ax in PARTS:
        N[nm_] = slot(ax, N[par])
    return N
def gen_lean():
    N = part_nouns()
    out = []
    for nm_, par, ax in PARTS:
        out.append(f'/-- axis `{ax}` of `{par}`, {T.cells(N[nm_])} cells. -/')
        out.append(f'def {nm_} : Noun := (slot? {ax} {par}).getD (A 0)')
    out.append('')
    for nm_ in ['sccMiss'] + [p[0] for p in PARTS]:
        if nm_ in OPAQUE: continue
        kids = [(k, N[k]) for k, p, a in PARTS if p == nm_]
        out.append(f'theorem {nm_}_eq : {nm_} = {lean(N[nm_], kids)} := by kernel_rfl')
    return '\n'.join(out)
if __name__ == '__main__':
    if len(sys.argv) > 2 and sys.argv[2] == 'lean':
        print(gen_lean()); sys.exit(0)
    N = part_nouns()
    T.row('sccMiss', '62@sccBat', miss)
    for nm_, par, ax in PARTS:
        T.row(nm_, f'{ax}@{par}', N[nm_])
