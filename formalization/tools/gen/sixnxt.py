#!/usr/bin/env python3
"""Write lemmas/Ska/CompSixNxTop.lean: a `%6` under `%next` as the operand of
`[4 p]` and `[3 p]` under `%done`, and the top (README Gaps 12.36, steps 3
and 4).  `four_doneT` and `three_doneT` are the text of `four_doneB` and
`three_doneB` (CompFourTop.lean) with `RunTE` of the operand (`RunOKLT` at a
goal with no entry) in place of `LOKSF`, read on the unwrapped need, and the
conclusion of `SixDW` (`RunOKGB` of the unwrapped need, `WalkEq` to the
real one) in place of `DoneOK`."""
import os
root = os.path.join(os.path.dirname(__file__), '..', '..')
s = open(os.path.join(root, 'lemmas/Ska/CompFourTop.lean')).read()

def grab(start, stop):
    a = s.index(start); b = s.index(stop, a)
    return s[a:b].rstrip() + '\n'

common = [
 ('(Sp : LOKSF (S := S) (Map := Map) lib N env P fb p)', '(Sp : RunTE (S := S) (Map := Map) lib N env P fb p)'),
 ('    DoneOK lib N P f g0 g1 nex := by',
  '    ∃ nexU : NextL S, nexU.th = nex.th ∧ WalkEq (Map := Map) nex.laz nexU.laz ∧\n'
  '      RunOKGB lib N P f (CGoal.done : CGoal S) g0 g1 nexU := by'),
 ('  obtain ⟨⟨Qp, Rp⟩, pne, -, pfl, pec⟩ := Sp.run (L := ofSure (lazyReg _)) (th := jmp0 _) (Or.inr (e0 _)) hcount',
  '  obtain ⟨Qp, nexU, eth, unw, -, Rp⟩ := Sp (sur := lazyReg _) (th := jmp0 _) hcount'),
 ('rfl (by rw [e0]; simp) trivial', 'rfl trivial'),
 ('    (fun e he => by rw [e0] at he; cases he) (by rw [e0]; simp) (fun e he => by rw [e0] at he; cases he)\n'
  '    (flat_ofSure _) trivial (fun e he => by rw [e0] at he; cases he) h',
  '    trivial h'),
 ('  refine ⟨?_, pne, pfl, Sp.clean (L := ofSure (lazyReg _)) trivial h, pec⟩',
  '  refine ⟨nexU, eth, unw.walkEq, ?_⟩'),
]

four = grab('theorem four_doneB', '/-- **`unaryGT_ok` for `RunOKGB`**')
for x, y in [('theorem four_doneB', 'theorem four_doneT')] + common:
    assert four.count(x) == 1, x
    four = four.replace(x, y)
three = grab('theorem three_doneB', '/-- **`LOKSF` at the goal a compile starts from**')
for x, y in [('theorem three_doneB', 'theorem three_doneT')] + common:
    assert three.count(x) == 1, x
    three = three.replace(x, y)

head = open(os.path.join(root, 'tools/gen/sixnxt_head.lean')).read()
tail = open(os.path.join(root, 'tools/gen/sixnxt_tail.lean')).read()
out = (head
  + '/-- (Generated from `four_doneB`.) **`[4 p]` under `%done` with an operand of `RunTE`**: the operand\'s\n'
  + '`RunOKLT` read on its unwrapped need, `RunOKLB.toGB`, `unaryGB_ok`. -/\n' + four + '\n'
  + '/-- (Generated from `three_doneB`.) **`[3 p]` under `%done` with an operand of `RunTE`**. -/\n'
  + three + '\n' + tail)
open(os.path.join(root, 'lemmas/Ska/CompSixNxTop.lean'), 'w').write(out)
