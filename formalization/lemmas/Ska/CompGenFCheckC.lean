import lemmas.Ska.CompGenFCheck

/-!
# famC phase 1 of the check of `FrontRG`, explained

README Gaps 12.39, item 9.  `CompGenFCheck.lean` left famC (the 245 `%6`
and the 7 branches under the goals `goalsP` that runs of other nomms leave)
unfrozen: phase 1 (`sem`: from the run's jump with the subject in the
result's sure registers to the goal's jump, the goal's sure registers hold
`+mink`'s product) failed on 10,800 of 1,619,400 pairs.  `p1` reruns phase 1
on one (nomm, goal, subject) and returns how the walk ended, whether the
product fits the goal's sure need, and whether it is held at the goal's jump,
when that is a failure; `fixed` starts the walk as a jump to the run's jump
from the registers holding the subject (`walk` on `[] [hop nex.th]`), the
committed harness entered `nex.th`'s block and ran its body.

The explanation (a harness artifact).  All 10,800 failures are the two
leaves `[0 2]` and `[0 3]` of the 7 branches, under all 300 goals of
`goalsP` (all well-formed), on the 18 subjects of each run whose product
exists and fits the result (a scratch run of the whole family, 8 min:
10,800 failures, 2 distinct nomms).  A leaf puts no block, so its jump is the
goal's (`nex.th = th`), and the harness, entering the jump's block before
testing for the stop, ran the GOAL's continuation (the generator's code at
`th`), which crashes or jumps into a marked entry `5000+a` (no block): it
never reaches `th` again.  The smallest witness: `[0 2]` under goal 0
(labels `[10 10 11 11]`, `th = 16`, `bo = 17`, `re = 11`), subject
`[[1 0] 0]`, product `[1 0]`, walk `crash`.  Started as a jump, every one
of them reaches `th` with the goal's sure registers holding the product.
For every other run the two starts agree (the jump is not to the stop), so
famC phase 1 has no failure.  No clause of `RunOKGen` is false here, and the
model computes the right value.
-/

namespace Formalization
namespace SkaModel
namespace Comp
namespace GenFCheck

open Nock Lazy SixCheck GenCheck

def endS : WEnd → String | .reach _ => "reach" | .crash => "crash" | .other => "other" | .fail => "fail"

/-- Phase 1 of one (nomm, goal, subject), when it fails: `(end, product fits
the goal's sure need, held at the goal's jump, product)`. -/
def p1 (fixed : Bool) (run : GenCheck.Runner) (nm : Nomm) (L : Lazy LS) (th : Jmp) (g : Gen FM) (s : Noun) :
    Option (String × Bool × Bool × Noun × Bool) :=
  let g0 := markGoal L g
  match run nm (CGoalL.next L th) g0 with
  | Option.none => Option.none
  | some (nex, g1) =>
    match putS nex.laz.sure s, minkF libT (A 0) 500 [] s (fol nm) with
    | some ps, some (Tone.zero v) =>
      let bl := codeOf g1 nex s
      let w := if fixed then walk bl th.there 4000 (regsL ps) [] (Termin.hop nex.th) else
        match bl nex.th.there with
        | some b => match evalPass nex.th.args b.par (regsL ps) with
          | some R0 => walk bl th.there 4000 R0 b.body b.fin
          | Option.none => WEnd.fail
        | Option.none => WEnd.fail
      let ok := match w with | .reach R => holdsSB L.sure R v | _ => false
      let fit := (putS L.sure v).isSome
      if (fit && !ok) || (!fit && !w.isCrash) then some (endS w, fit, ok, v, nex.th == th) else Option.none
    | _, _ => Option.none

/-- The failures of phase 1 among the 7 branches under the well-formed goals
of `goalsP`: `(branch, goal, subject, end, fits, held, product, jump is the goal's)`. -/
def brsFails (fixed : Bool) : List (Nat × Nat × Nat × String × Bool × Bool × Noun × Bool) :=
  ((List.range brs.length).zip brs).flatMap fun (k, nm) =>
    ((List.range GenCheck.goalsP.length).zip GenCheck.goalsP).flatMap fun (i, L, th, g) =>
      if th.there < g.bo then ((List.range SixCheck.subjects.length).zip SixCheck.subjects).filterMap fun (j, s) =>
        (p1 fixed GenCheck.runP nm L th g s).map fun r => (k, i, j, r) else []

/-! The committed harness: 10,800 failures, all of `[0 2]` and `[0 3]` (branches
`0` and `1`), every one at a run whose jump is the goal's; started as a jump,
none. -/
#guard (wellFormed GenCheck.goalsP).length == 300
#guard (brsFails false).length == 10800
#guard ((brsFails false).map (·.1)).eraseDups == [0, 1]
#guard ((brsFails false).map fun w => (w.1, w.2.1)).eraseDups.length == 600
#guard (brsFails false).all fun w => w.2.2.2.2.2.2.2
#guard (brsFails true).length == 0

/-! The smallest witness. -/
#guard match GenCheck.goalsP[0]? with
  | some (L, th, g) => GenCheck.labels L == [10, 10, 11, 11] && th.there == 16 && g.bo == 17 && g.re == 11 &&
      p1 false GenCheck.runP (Nomm.n0 2) L th g (C (C (A 1) (A 0)) (A 0)) == some ("crash", true, false, C (A 1) (A 0), true) &&
      (p1 true GenCheck.runP (Nomm.n0 2) L th g (C (C (A 1) (A 0)) (A 0))).isNone
  | Option.none => false

end GenFCheck
end Comp
end SkaModel
end Formalization
