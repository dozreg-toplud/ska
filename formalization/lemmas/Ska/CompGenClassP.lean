import lemmas.Ska.CompGenClassH

/-!
# The widened class `NextGX` (for `%6` under `%next`, `[3 p]`, `[4 p]`, `[5 p q]`)

README Gaps 12.39, item 12.  `NextGCS` with three clauses widened:

* `x` is chosen by the run (`∃ Q x`), and the state-level fronts read the
  goal's sure registers when it is `true` (`E = gsE x L = L.sure.ned`):
  under a goal with an entry, `+collapse-lazy-atom` of `[3 p]`, `[4 p]`,
  `[5 p q]` takes the goal's sure register as the product's, and the front at
  the entry's label reads it (`[4 [0 2]]` under the sure need `[0]`, entry
  `(1, [2])`: front `[mov 0 2]`);
* `GrowG` for `GrowU` (a goal entry's block may be re-pointed by `+fork`);
* at a goal label: ops in front with a `FrontSG` at `E = gsE x L`, OR
  re-pointed (`RepointG`) with `FrontRG` at the same `E` (`FrontsSGX`).

Checked before any proof (a scratch copy of `CompGenClassCheck.lean`'s
`chk`, widened to `chkX`: every clause at every sub-run through the cons,
`%7`, `%5`, `%4`, `%3`, the parts' premises (`premB`), the copies'
`CopyPreAt`, the reassembly against `runLC`), on the goals meeting `premB`:
no clause fails on famB (154,350 runs), famC (75,600), famD (72,000 under
`goalsP`, 21,600 under the flat goals), famA (22,050), the `%3`/`%4`/`%5`
family `fam345` (5,040 flat, 16,800 `goalsP`) and the composites with a
`%3`/`%4`/`%5` part `famX` (19,440 flat, 64,800 `goalsP`).  The clauses: the
frame (`oneG`'s, `GrowG` included, but `jumpNoEnt`, which is `OutG` and not
in the class: it fails where the goal's own jump is at one of its entries'
labels, e.g. `[7 [4 [0 2]] [0 2]]` under the sure need none, entry
`(1, [2])`, jump 1), `ResG`, and per goal label: an old result register at
the label is a goal entry's there (`FrontSG.loc`; never the goal's sure
one), the front ops read only the result's needs at the label, fresh
registers and (with `x`) the goal's sure ones, and write only the goal's
needs at the label and fresh registers; with `x` the goal's sure registers
are apart from the result's needs at every goal label (`FrontSG.toLG`'s
`hE`); a label with no ops in front is re-pointed (`RepointG`).  The runs
that need `x` are `%3`, `%4`, `%5` and the `%7` above them (famB, call-free:
192, 96, 96, 96 runs); `%6` and the cons never need it (re-points: 3,102
call-free runs of famB, 7,056 of famC, 20,768 of famD).  When a part of a
cons or a `%7` needs `x`, the registers its fronts read are the whole's goal's
sure ones (never fresh in the run before it), so `x` composes as `x` of the
whole.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The state-level fronts of the widened class**: at every goal label,
ops in front of the block whose renamed form is a `FrontSG` with the goal's
sure registers `gsE x L`, or the block re-pointed with `FrontRG`. -/
def FrontsSGX (Q : Wit) (x : Bool) (g0 g1 : Gen Map) (L : Lazy S) (nex : NextL S) : Prop :=
  ∀ a ∈ (entries L).map Prod.fst,
    (∃ F : List Pole, FrontBlk g0 g1 a F ∧
      ∀ cf : Map (Nat × List Nat), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
        FrontSG (Map := Map) Q (gsE x L) g0.re g1.re (suresAt nex.laz a) (F.map (renPole (unproxy cf)))
          (suresAt L a)) ∨
    (RepointG g0 g1 a ∧ FrontRG (Map := Map) Q (gsE x L) g0 g1 nex a (suresAt L a))

/-- **The widened class `NextGX`**: under every goal of the class, some
witness and `x` with `RunOKGen`, `GrowG`, `ResG` and `FrontsSGX`. -/
abbrev NextGX (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop) (f : Noun) (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {L : Lazy S} {th : Jmp} {nex : NextL S},
    PremG (Map := Map) L th g0 →
    runLC env sup nm (CGoalL.next L th) region g0 = some (nex, g1) →
    ∃ (Q : Wit) (x : Bool), RunOKGen lib N P f L th Q x g0 g1 nex ∧ GrowG L g0 g1 ∧
      ResG (Map := Map) L g0 g1 nex.laz ∧ FrontsSGX (Map := Map) Q x g0 g1 L nex

/-- `NextGCS` is the case `x = false`, no re-pointing. -/
theorem NextGCS.toGX {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (h : NextGCS (S := S) (Map := Map) lib N env P f nm) : NextGX (S := S) (Map := Map) lib N env P f nm :=
  fun H hr =>
    let ⟨Q, R, g, _, r, fs⟩ := h H hr
    ⟨Q, false, R, g.toG, r, fun a ha => Or.inl (fs a ha)⟩

end Comp
end SkaModel
end Formalization
