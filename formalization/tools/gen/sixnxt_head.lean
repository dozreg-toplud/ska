import lemmas.Ska.CompSixNxRun

/-!
# A `%6` under `%next` inside a parent, and the top

README Gaps 12.36, steps 3 and 4.  Written by `tools/gen/sixnxt.py` (with
`sixnxt_head.lean`, `sixnxt_tail.lean`); do not edit by hand.

* `RunTE` (every run under `%next sur th`, a goal with no entry, from a
  state with the premises of `LOKSE.run`, meets `RunOKLT`), `six_nextT`
  (phase S: the `%6` meets `RunTE`, from `six_nextGB`).
* `four_doneT`, `three_doneT` (generated from `four_doneB`, `three_doneB`):
  `[4 p]` and `[3 p]` under `%done` run their operand under `%next
  (lazy-from-reg r)`, a goal with no entry; from `RunTE` of the operand they
  meet `RunOKGB` of the operand's unwrapped need, with `WalkEq` to the real
  one, which `finishLUC_contractGBW` reads at the top.
* `fourSix_contract`, `threeSix_contract`: the whole-subject code of
  `[4 [6 [3 [0 2]] [0 3] [1 0]]]` and `[3 [6 [3 [0 2]] [0 3] [1 0]]]` meets
  both halves of the contract, with `#guard`s that the code exists and
  agrees with `+mink` on the 24 subjects of `CompSixLSCheck.lean`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

local macro "romega" : tactic =>
  `(tactic| first | omega | (simp only [emitted_re, emitted_bo] at *; omega) | (dsimp only at *; omega))

/-- **Every run at a goal with no entry meets `RunOKLT`**, from a state
with the premises of `LOKSE.run`. -/
abbrev RunTE (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop) (f : Noun) (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    1 ≤ th.there → th.there < g0.bo → th.args = [] → Distinct sur.ned →
    (∀ x, NMem sur.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) → Clean sur.ned →
    runLC env sup nm (CGoalL.next (ofSure sur) th) region g0 = some (nex, g1) →
    ∃ Q, RunOKLT (Map := Map) lib N P f (ofSure sur) th Q false g0 g1 nex

/-- **Phase S: `[6 c a b]` meets `RunTE`** (`six_nextGB`, `RunOKGB.toLS`). -/
theorem six_nextT (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {fc fa fb : Noun} {c a b : Nomm}
    {kc ka kb : Nat} (Hc : PickD (S := S) (Map := Map) lib N env P fc c kc) (Fc : PickF (S := S) (Map := Map) env c)
    (Ha : SixN (S := S) (Map := Map) lib N env P fa a ka) (Hb : SixN (S := S) (Map := Map) lib N env P fb b kb)
    (hk : 5 + ka + kb ≤ lazyMax) :
    RunTE (S := S) (Map := Map) lib N env P (n4 (A 6) fc fa fb) (Nomm.n6 c a b) := by
  intro sup sur th region g0 g1 nex hcount b0 d0 hu hcl hcb h1 h2 hta hsd hsl hcs hr
  obtain ⟨nexU, eth, unw, t1, R⟩ := six_nextGB lib env Hc Fc Ha Hb hk hcount b0 d0 hu hcl hcb h1 h2 hta hsd hsl
    hcs hr
  exact ⟨noWit, nexU, eth, unw, t1, R.toLS⟩

