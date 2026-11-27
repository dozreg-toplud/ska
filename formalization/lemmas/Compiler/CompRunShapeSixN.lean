import lemmas.Compiler.CompRunShapeSixNTail
import lemmas.Compiler.CompRunShapeLeaps
import lemmas.Compiler.CompRunShapeThisOnly
import lemmas.Compiler.CompRunShapeWhole
import lemmas.Compiler.CompRunShapeSoftFork
import lemmas.Compiler.CompRunShapeBranch

/-!
# `+run-shape`: the case `[6 p q r]` under `[%next laz]` (track A, 2026-11-28)

The case runs `+laze-leaps` (`lls_all`); on a leap it runs itself on `[%next rest]` and rolls
`+laze-copy` over the `bys`; with no leap and `laz` none-equivalent but for its sure need it is
the tail on `goal-branch` (`six_br`); else, if the kerf test holds (`+whole` of both branches,
`+laze-this-only`, `+laze-big`, `+laze-soft-fork`), it runs itself on `[%next this]`, and if it
does not, it is the fork (`+laze-branch`, then the tail on the two halves).  The model is
`sixShape` at the fuel `sixFuel`: a run on the same nomm costs one unit.

**The fuel.**  `sixShape` at fuel `f` returns `none` when the chain of runs on the same nomm is
longer than `f`, where the pill may return.  The chain is a run of leaps, then at most one kerf
(`this` has neither forks nor bonds, so the run on it is the tail).  `SixDeep q r f laz` says the
fuel `f` covers the chain from `laz`: at most `f - 2` leaps in a row.  At `sixFuel = 4` this is
two leaps in a row (`sixDeep_of_idem`: it holds when a leap's `rest` never leaps again).

* `roll_gateO`: `+roll` with a gate that may crash is `List.foldlM`.
* `six_lep`, `six_tk`, `six_ktest`: the three tests; `six_br` (the tail on `goal-branch`),
  `six_this` (the run on `[%next this]`), `six_fork` (the fork), `six_leap` (the leap).
* **`six_fuel`**: at every fuel `f` and `laz` of `LzNZ` with `SixDeep q r f laz`, the gate is
  `sixShape .. f laz`.
* **`rs_n6NE`**: the case on `RsAtE`, at `sixFuel`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun} {E : RsRest → Prop}

/-! ## The fuel -/

/-- **The fuel `f` covers the runs on the same nomm from `laz`**: a kerf needs one unit beyond the
current one, a leap one unit for its `rest`. -/
def SixDeep (q r : Nomm) : Nat → Laze CSet → Prop
  | 0, _ => False
  | f + 1, laz => 1 ≤ f ∧ ∀ rest bys, lazeLeaps laz q r = some (some (rest, bys)) → SixDeep q r f rest

/-- At `sixFuel`, when a leap's `rest` never leaps again. -/
theorem sixDeep_of_idem (q r : Nomm)
    (hid : ∀ (laz rest : Laze CSet) bys, lazeLeaps laz q r = some (some (rest, bys)) →
      ∀ (rest' : Laze CSet) bys', lazeLeaps rest q r ≠ some (some (rest', bys'))) (laz : Laze CSet) :
    SixDeep q r sixFuel laz := by
  simp only [sixFuel, SixDeep]
  exact ⟨by omega, fun rest bys h => ⟨by omega, fun rest' bys' h' => absurd h' (hid _ _ _ h _ _)⟩⟩

/-! ## `+roll` with a gate that may crash -/

theorem roll_loopO {α σ : Type} (toE : α → Noun) (toS : σ → Noun) (c bp e bc : Noun)
    (f : σ → α → Option σ) : ∀ (l : List α) (acc : σ),
    (∀ x ∈ l, ∀ acc, nock (C bp (C (C (toE x) (toS acc)) bc)) bp = (f acc x).map toS) →
    nock (C roll.loop (C roll.battery (C (C (listN (l.map toE)) (C bp (C (C e (toS acc)) bc))) c)))
      roll.loop = (l.foldlM f acc).map toS := by
  intro l
  induction l with
  | nil =>
    intro acc _
    nock_open roll.loop
    simp [nock_exec]
  | cons x xs ih =>
    intro acc hf
    have hx := hf x (by simp) acc
    nock_open roll.loop
    cases e1 : f acc x with
    | none =>
      rw [e1] at hx
      simp [nock_exec, hx, e1]
    | some a =>
      rw [e1] at hx
      have hxs := ih a (fun y hy => hf y (by simp [hy]))
      simp [nock_exec, hx, hxs, e1]

/-- **`+roll`** slammed on a list and a gate that may crash. -/
theorem roll_gateO {α σ : Type} (toE : α → Noun) (toS : σ → Noun) (c bp e bc : Noun)
    (f : σ → α → Option σ) (l : List α) (acc : σ)
    (hf : ∀ x ∈ l, ∀ acc, nock (C bp (C (C (toE x) (toS acc)) bc)) bp = (f acc x).map toS) :
    nock (C roll.battery (C (C (listN (l.map toE)) (C bp (C (C e (toS acc)) bc))) c)) roll.battery
      = (l.foldlM f acc).map toS := by
  nock_open roll.battery
  simp only [nock_exec, roll_loopO toE toS c bp e bc f l acc hf]

/-! ## The entry and the tests -/

/-- The subject of the case under `[%next laz]`. -/
noncomputable def sixS (ctx : Noun) (p q r : Nomm) (sup : Option Nomm) (laz : Laze CSet) (st : RSt CSet)
    (y : RsRest) : Noun :=
  rsS (GoalS.next laz).toNoun (C (A 6) (C p.toNoun (C q.toNoun r.toNoun))) (GoalS.next laz).toNoun
    (supNoun sup) (rsDoor st y ctx)

/-- After the push of `lep`: `?^  lep` and the rest. -/
def sixDisp : Noun :=
  C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 1) (A 1)) (C (A 1) (A 0)))))
    (C (C (A 6) (C rs6Tk (C rs6Kerf (C (A 8) (C rs6Gb rs6Rest))))) rs6Leap))

theorem rs6Arm_disp : rs6Arm = C (A 8) (C rs6Lep sixDisp) := rfl

theorem n6_noun (p q r : Nomm) : (Nomm.n6 p q r).toNoun = C (A 6) (C p.toNoun (C q.toNoun r.toNoun)) := rfl

/-- **The entry**: the pushes, the `?-`, the push of `lep`. -/
theorem six_entry (p q r : Nomm) (sup : Option Nomm) (laz : Laze CSet) (st : RSt CSet) (y : RsRest) :
    nock (rsCoreG (Nomm.n6 p q r).toNoun (GoalS.next laz).toNoun (supNoun sup) (rsDoor st y ctx)) rsGate
      = (nock (sixS ctx p q r sup laz st y) rs6Lep).bind fun LEP =>
          nock (C LEP (sixS ctx p q r sup laz st y)) sixDisp := by
  rw [n6_noun, rs_push, rs_disp_n6, rsK6_eq, rs6Arm_disp]
  simp only [rsSimpleN, simpleS]
  unfold sixS
  generalize rs6Lep = LP
  generalize sixDisp = SD
  simp [nock_exec]

/-- **`lep`**: `+laze-leaps` of the goal's `laze` over `q` and `r`. -/
theorem six_lep (h7 : slot? 7 ctx = some compK) (p q r : Nomm) (sup : Option Nomm) (laz : Laze CSet)
    (st : RSt CSet) (y : RsRest) (hl : LzNZ laz) (hq0 : Bake.NoAx0 q) (hr0 : Bake.NoAx0 r) :
    nock (sixS ctx p q r sup laz st y) rs6Lep = (lazeLeaps laz q r).map llsN := by
  have hlls := lls_all h7 (rsGenNoun st y) laz q r hl hq0 hr0
  unfold rs6Lep sixS
  simp [nock_exec, rsS, rsCoreG, rsDoor, GoalS.toNoun, lls_at', lls_arm, hlls]

/-- `goal-branch`: `[%next [sure.laz ~ ~]]`. -/
theorem six_gb (p q r : Nomm) (sup : Option Nomm) (sur : SureO CSet) (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet)))
    (bd : List (Nat × Laze CSet)) (st : RSt CSet) (y : RsRest) :
    nock (C (A 0) (sixS ctx p q r sup (Laze.mk sur fk bd) st y)) rs6Gb
      = some (GoalS.next (Laze.mk sur [] [] : Laze CSet)).toNoun := by
  unfold rs6Gb sixS
  simp [nock_exec, rsS, rsCoreG, GoalS.toNoun, Laze.toNoun, Laze.forksNoun, Laze.bondsNoun]

/-- The recursion `$(goal [%next this])` of the kerf. -/
theorem six_rec (LEP : Noun) (p q r : Nomm) (sup : Option Nomm) (laz : Laze CSet) (st : RSt CSet) (y : RsRest) :
    nock (C LEP (sixS ctx p q r sup laz st y)) rs6KRec
      = nock (rsCoreG (Nomm.n6 p q r).toNoun (GoalS.next (thisL : Laze CSet)).toNoun (supNoun sup) (rsDoor st y ctx)) rsGate := by
  unfold rs6KRec sixS
  simp [nock_exec, rsS, rsCoreG, GoalS.toNoun, thisL_noun, n6_noun]

section
variable (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
include hc

/-- **The test of the kerf** (`?.  ?=(%next -.goal)  |  !(laze-none-equivalent ..)`). -/
theorem six_tk (p q r : Nomm) (sup : Option Nomm) (sur : SureO CSet)
    (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet))) (bd : List (Nat × Laze CSet)) (st : RSt CSet) (y : RsRest) :
    nock (C (A 0) (sixS ctx p q r sup (Laze.mk sur fk bd) st y)) rs6Tk
      = some (loob (!noneEq (Laze.mk SureO.bunt fk bd : Laze CSet))) := by
  have hl := lne_all hc (rsGenNoun st y) (Laze.mk SureO.bunt fk bd)
  unfold rs6Tk sixS
  cases e : noneEq (Laze.mk SureO.bunt fk bd : Laze CSet) <;> rw [e] at hl <;>
    simp only [Laze.toNoun, SureO.bunt, SureO.toNoun, NeedOrd.toNoun, Tag.none, HoonSet.toNoun_empty] at hl <;>
    simp [nock_exec, rsS, rsCoreG, rsDoor, GoalS.toNoun, Laze.toNoun, lne_at', lneArm, hl, e, loob]

include h7 hcode

/-- **The tail on `goal-branch`**: `laz` none-equivalent but for its sure need. -/
theorem six_br (env : ShapeEnv) (p q r : Nomm) (sup : Option Nomm) (sur : SureO CSet)
    (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet))) (bd : List (Nat × Laze CSet)) (st : RSt CSet)
    (y : RsRest) (hy : E y) (hcp : CallCode cod (shapeCE env) p)
    (hne : noneEq (Laze.mk SureO.bunt fk bd : Laze CSet) = true)
    (hr : ∀ st1, RsAtE ctx env E r sup (GoalS.next (Laze.mk sur [] [])) st1)
    (hq : ∀ st1, RsAtE ctx env E q sup (GoalS.next (Laze.mk sur [] [])) st1)
    (hp : ∀ st1, RsAtE ctx env E p sup GoalS.pick st1) :
    nock (C (A 0) (sixS ctx p q r sup (Laze.mk sur fk bd) st y)) sixDisp
      = (sixBranch env (runShape env sup p) (runShape env sup q) (runShape env sup r) p
          (GoalS.next (Laze.mk sur [] [])) st).map fun p => C p.1.toNoun (rsGenNoun p.2 y) := by
  have htk := six_tk hc p q r sup sur fk bd st y
  rw [hne] at htk
  have hgb := six_gb (ctx := ctx) p q r sup sur fk bd st y
  have ht := six_tail hc h7 hcode env p q r sup (GoalS.next (Laze.mk sur [] [])) (GoalS.next (Laze.mk sur [] []))
    GoalS.pick st y hy hcp hr hq hp (GoalS.next (Laze.mk sur [] [] : Laze CSet)).toNoun (A 0)
    (GoalS.next (Laze.mk sur fk bd)).toNoun (GoalS.next (Laze.mk sur fk bd)).toNoun
    (C (A 0) (A 2)) (C (A 0) (A 6)) (C (A 1) (C (A 0x6b636970) (A 0)))
    (fun Z => by simp [nock_exec]) (fun a Z => by simp [nock_exec])
    (fun a b c Z => by simp [nock_exec, GoalS.toNoun])
  rw [← rs6Rest_tail, n6_noun] at ht
  change nock (C _ (C (A 0) (sixS ctx p q r sup (Laze.mk sur fk bd) st y))) rs6Rest = _ at ht
  rw [sixBranch_tail]
  unfold sixDisp
  generalize sixS ctx p q r sup (Laze.mk sur fk bd) st y = T at htk hgb ht
  generalize rs6Tk = TK at htk
  generalize rs6Gb = GB at hgb
  generalize rs6Rest = RR at ht
  generalize rs6Kerf = KF
  generalize rs6Leap = LP
  simp [nock_exec, htk, hgb, ht, loob]

/-- **The run on `[%next this]`** is the tail on `[%next [this ~ ~]]`, at every fuel. -/
theorem six_this (env : ShapeEnv) (p q r : Nomm) (sup : Option Nomm) (f : Nat) (st : RSt CSet)
    (y : RsRest) (hy : E y) (hcp : CallCode cod (shapeCE env) p) (hq0 : Bake.NoAx0 q) (hr0 : Bake.NoAx0 r)
    (hr : ∀ st1, RsAtE ctx env E r sup (GoalS.next (Laze.mk (thisL : Laze CSet).sure [] [])) st1)
    (hq : ∀ st1, RsAtE ctx env E q sup (GoalS.next (Laze.mk (thisL : Laze CSet).sure [] [])) st1)
    (hp : ∀ st1, RsAtE ctx env E p sup GoalS.pick st1) :
    nock (rsCoreG (Nomm.n6 p q r).toNoun (GoalS.next (thisL : Laze CSet)).toNoun (supNoun sup) (rsDoor st y ctx)) rsGate
      = (sixShape env (runShape env sup p) (runShape env sup q) (runShape env sup r) p q r (f + 1) thisL st).map
          fun p => C p.1.toNoun (rsGenNoun p.2 y) := by
  have hleap : lazeLeaps (thisL : Laze CSet) q r = some Option.none := by simp [lazeLeaps, thisL, Laze.fork, Laze.bond]
  have hsm : HoonSet.small (HoonSet.empty : CSet) = true :=
    (HoonSet.small_iff _).2 fun x hx => absurd hx (HoonSet.mem_empty x)
  have hne : noneEq (Laze.mk SureO.bunt [] [] : Laze CSet) = true := by
    simp [noneEq, noneEqF, noneEqB, SureO.bunt, hsm]
  have hleap' : lazeLeaps (Laze.mk ⟨NeedOrd.this, HoonSet.empty⟩ [] [] : Laze CSet) q r = some Option.none := hleap
  rw [six_entry, six_lep h7 p q r sup thisL st y lzNZ_thisL hq0 hr0, hleap]
  have hb := six_br hc h7 hcode env p q r sup thisL.sure [] [] st y hy hcp hne hr hq hp
  have hm : sixShape env (runShape env sup p) (runShape env sup q) (runShape env sup r) p q r (f + 1) thisL
      = sixBranch env (runShape env sup p) (runShape env sup q) (runShape env sup r) p
          (GoalS.next (Laze.mk (thisL : Laze CSet).sure [] [])) := by
    funext st0
    simp [sixShape, shLiftS, hleap', bind, StateT.bind, thisL, Laze.fork, Laze.bond, hne, pure, StateT.pure]
  rw [hm]
  simpa [llsN, unitNoun, thisL, Laze.sure] using hb

end

end Compiler
end Formalization
