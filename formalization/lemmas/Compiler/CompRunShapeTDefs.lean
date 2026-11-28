import lemmas.Compiler.CompRunShapeTwo

/-!
# `+run-shape` threading the rest of `gen` (track A, 2026-11-28)

`+callee-need` on a callee `b` outside the SCC with no entry in `nary.cache` runs `+scc-of` and
`+compile-scc-in` and returns `gen` with a bigger `cache` (`+callee-compiled`).  That is the normal
case in the first `%may` sweep, where the callees outside the SCC are met first.  So the run of
`+run-shape` does not keep the rest `y` of `gen`: `RsAtE` (the rest kept) is restated on a rest
relation `Rl` (track K's `CompRunAtXT` for `+run`).

* `RlPre Rl`: `Rl` is reflexive and transitive (the cache grows).
* **`RsAtT ctx env E Rl`**: from every rest `y` of `E`, the gate returns the model's result with some
  rest `y'` of `E` with `Rl y y'`.
* `rsAtT_of_E`: a run that keeps the rest is threaded; `rsAtE_of_T`: a threaded run at `Rl = Eq` keeps it.
* **`ShapeCallT`**: `ShapeCall` with the need push moving the rest from `y` to `y'` (a miss), and
  `+callee-sure` read at `y'` (it runs after the push); on a cell key (no need push) `+callee-sure`
  returns some `need-ordered` at `y` (its value is not used: the soft test is `|` there).
* `shapeCallT_of`: `ShapeCall` (no miss) is `ShapeCallT` with `y' = y`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun}

/-- A rest relation that is reflexive and transitive. -/
structure RlPre (Rl : RsRest → RsRest → Prop) : Prop where
  refl : ∀ y, Rl y y
  trans : ∀ {a b c : RsRest}, Rl a b → Rl b c → Rl a c

/-- **`RsAt` threading the rest**: from every rest `y` of `E` the gate of `+run-shape` returns the
model's result with some rest `y'` of `E` that `Rl` relates to `y`. -/
def RsAtT (ctx : Noun) (env : ShapeEnv) (E : RsRest → Prop) (Rl : RsRest → RsRest → Prop) (n : Nomm)
    (sup : Option Nomm) (goal : GoalS CSet) (st : RSt CSet) : Prop :=
  ∀ y : RsRest, E y → ∃ y', Rl y y' ∧ E y' ∧
    nock (rsCoreG n.toNoun goal.toNoun (supNoun sup) (rsDoor st y ctx)) rsGate
      = (runShape env sup n goal st).map fun p => C p.1.toNoun (rsGenNoun p.2 y')

theorem rsAtT_of_E {env : ShapeEnv} {E : RsRest → Prop} {Rl : RsRest → RsRest → Prop} (hR : RlPre Rl)
    {n : Nomm} {sup : Option Nomm} {goal : GoalS CSet} {st : RSt CSet} (h : RsAtE ctx env E n sup goal st) :
    RsAtT ctx env E Rl n sup goal st :=
  fun y hy => ⟨y, hR.refl y, hy, h y hy⟩

theorem rsAtT_of {env : ShapeEnv} {E : RsRest → Prop} {Rl : RsRest → RsRest → Prop} (hR : RlPre Rl)
    {n : Nomm} {sup : Option Nomm} {goal : GoalS CSet} {st : RSt CSet} (h : RsAt ctx env n sup goal st) :
    RsAtT ctx env E Rl n sup goal st :=
  rsAtT_of_E hR (rsAtE_of h)

theorem rsAtE_of_T {env : ShapeEnv} {E : RsRest → Prop} {n : Nomm} {sup : Option Nomm} {goal : GoalS CSet}
    {st : RSt CSet} (h : RsAtT ctx env E (· = ·) n sup goal st) : RsAtE ctx env E n sup goal st := by
  intro y hy
  obtain ⟨y', rfl, -, e⟩ := h y hy
  exact e

/-- A model result that is `none` is the pill's at every rest. -/
theorem rsT_none {α : Type} {o : Option α} (h : o = Option.none) (f : α → Noun) : o.map f = Option.none := by
  rw [h]; rfl

/-- **What the direct call reads of the door, threading the rest**: the need push (`+callee-need`)
returns `env.need b` and moves the rest from `y` to some `y'` of `E` (a miss compiles the callee and
returns the bigger cache; a hit keeps `y`), after which `+callee-sure` returns `env.sure b`; on a
cell key there is no need push and `+callee-sure` returns some `need-ordered` at `y`. -/
structure ShapeCallT (ctx : Noun) (env : ShapeEnv) (E : RsRest → Prop) (Rl : RsRest → RsRest → Prop)
    (p q : Nomm) (b : Bell) (k : Option Noun) (sup : Option Nomm) (y : RsRest) : Prop where
  need : konstCell k = false → ∃ nb, env.need b = some nb ∧ ∀ st : RSt CSet, ∃ y', Rl y y' ∧ E y' ∧
    nock (C cneBat (C b.toNoun (rsDoor st y ctx))) cneBat = some (C nb.toNoun (rsGenNoun st y')) ∧
    ∀ st' : RSt CSet, nock (C csuBat (C b.toNoun (rsDoor st' y' ctx))) csuBat = some (env.sure b).toNoun
  sureK : konstCell k = true → ∃ sur : NeedOrd, ∀ st : RSt CSet,
    nock (C csuBat (C b.toNoun (rsDoor st y ctx))) csuBat = some sur.toNoun
  cole : ∃ cole, slot? 6846 ctx = some cole ∧ getF mugF b.toNoun cole = some (A 0)
  hot : ∃ jh, slot? 54 ctx = some jh
  jet : env.jet b = false
  soft : ∀ ned : NeedOrd, (konstCell k = true → ned = NeedOrd.this) →
    (konstCell k = false → env.need b = some ned) → softTest env p q b k ned (env.sure b) sup ≠ Option.none

/-- **A call with no miss is a threaded call with `y' = y`.** -/
theorem shapeCallT_of {env : ShapeEnv} {E : RsRest → Prop} {Rl : RsRest → RsRest → Prop} (hR : RlPre Rl)
    {p q : Nomm} {b : Bell} {k : Option Noun} {sup : Option Nomm} {y : RsRest} (hy : E y)
    (h : ShapeCall ctx env p q b k sup y) : ShapeCallT ctx env E Rl p q b k sup y where
  need hk := by
    obtain ⟨nb, e, hn⟩ := h.need hk
    exact ⟨nb, e, fun st => ⟨y, hR.refl y, hy, hn st, h.sure⟩⟩
  sureK _ := ⟨env.sure b, h.sure⟩
  cole := h.cole
  hot := h.hot
  jet := h.jet
  soft := h.soft

/-- **`ShapeOK` threading the rest**: `ShapeCallT` at every rest of `E`, for every direct call of `n`,
with the `sup` it runs under. -/
def ShapeOKT (ctx : Noun) (env : ShapeEnv) (E : RsRest → Prop) (Rl : RsRest → RsRest → Prop) :
    Option Nomm → Nomm → Prop
  | sup, Nomm.n2 p q (some (b, k)) =>
    (∀ y, E y → ShapeCallT ctx env E Rl p q b k sup y) ∧ ShapeOKT ctx env E Rl sup p ∧ ShapeOKT ctx env E Rl sup q
  | sup, Nomm.n2 p q Option.none => ShapeOKT ctx env E Rl sup p ∧ ShapeOKT ctx env E Rl sup q
  | sup, Nomm.n7 p q => ShapeOKT ctx env E Rl sup p ∧ ShapeOKT ctx env E Rl (some p) q
  | sup, Nomm.n6 p q r => ShapeOKT ctx env E Rl sup p ∧ ShapeOKT ctx env E Rl sup q ∧ ShapeOKT ctx env E Rl sup r
  | sup, Nomm.n3 p => ShapeOKT ctx env E Rl sup p
  | sup, Nomm.n4 p => ShapeOKT ctx env E Rl sup p
  | sup, Nomm.cons p q => ShapeOKT ctx env E Rl sup p ∧ ShapeOKT ctx env E Rl sup q
  | sup, Nomm.n5 p q => ShapeOKT ctx env E Rl sup p ∧ ShapeOKT ctx env E Rl sup q
  | sup, Nomm.n10 _ v q => ShapeOKT ctx env E Rl sup v ∧ ShapeOKT ctx env E Rl sup q
  | _, _ => True

end Compiler
end Formalization
