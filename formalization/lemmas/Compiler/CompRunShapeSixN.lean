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

/-! ## `+laze-soft-fork` returns when `!&((sound q ned) (sound r ned))` does -/

theorem orB_isSome {a b : Option Bool} (ha : ∃ x, a = some x) (hb : ∃ y, b = some y) : ∃ z, orB a b = some z := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  cases x <;> simp [orB]

section
variable (soft : Nat → Bool) (uns : NeedOrd → Option Bool) (hu : ∀ ned, ∃ b, uns ned = some b)
include hu

mutual
theorem sfk_some : ∀ laz : Laze CSet, ∃ t, softForkS soft uns laz = some t
  | Laze.mk _ f b => by
    simp only [softForkS]
    exact orB_isSome (sfkB_some b) (sfkF_some f)
theorem sfkB_some : ∀ bd : List (Nat × Laze CSet), ∃ t, softForkSB soft uns bd = some t
  | [] => ⟨false, rfl⟩
  | (o, l) :: rest => by
    simp only [softForkSB]
    refine orB_isSome (orB_isSome ?_ (sfk_some l)) (sfkB_some rest)
    split
    · exact hu _
    · exact ⟨false, rfl⟩
theorem sfkF_some : ∀ fk : List ((Nat × Laze CSet) × (Nat × Laze CSet)), ∃ t, softForkSF soft uns fk = some t
  | [] => ⟨false, rfl⟩
  | ((_, a), (_, b)) :: rest => by
    simp only [softForkSF]
    exact orB_isSome (orB_isSome (sfk_some a) (sfk_some b)) (sfkF_some rest)
end

end

/-! ## The kerf, the fork, the leap -/

/-- The fork of the kerf: `+laze-branch`, its `=^`, the tail on the halves. -/
def sixForkN : Noun :=
  C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C rs6KLbr
    (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3)))
    (sixTailN (C (C (A 1) (A 0x7478656e)) (C (A 0) (A 5))) (C (C (A 1) (A 0x7478656e)) (C (A 0) (A 12)))
      (C (C (A 1) (A 0x7478656e)) (C (A 0) (A 254)))))))))))

theorem rs6Kerf_fork : rs6Kerf = C (A 6) (C rs6KTest (C rs6KRec sixForkN)) := rs6Kerf_eq

/-- The body of the gate that `+roll` slams over the `bys`: `(laze-copy acc by)`. -/
def sixRollB : Noun :=
  C (A 8) (C (C (A 9) (C (A 43958) (C (A 0) (A 1023)))) (C (A 9) (C (A 2) (C (A 10)
    (C (C (A 6) (C (C (A 0) (A 29)) (C (A 0) (A 28)))) (C (A 0) (A 2)))))))

section
variable (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
include hc h7 hcode

/-- **The kerf test**, where `+laze-soft-fork` returns. -/
theorem six_ktest (env : ShapeEnv) (hcn : CodeNomms env.cod cod) (p q r : Nomm) (sup : Option Nomm)
    (laz : Laze CSet) (st : RSt CSet) (y : RsRest) (t : Bool)
    (ht : softForkS (sofsHas st.sofs) (unsS env q r) laz = some t) :
    nock (C (A 0) (sixS ctx p q r sup laz st y)) rs6KTest
      = some (loob ((whole q && whole r) || thisOnlyS laz || lazeBig (sofsHas st.sofs) laz || t)) := by
  have hana := whl_ana h7
  have hw1 := wh_gate ana q
  have hw2 := wh_gate ana r
  have hlto := lto_all hc (rsGenNoun st y) laz
  have hlbg := lbg_gate hc h7 st y laz
  simp only [rsDoor] at hlbg
  have hlsf := lsf_all hc h7 hcode env hcn q r st y laz t ht
  simp only [rsDoor] at hlsf
  unfold rs6KTest sixS
  cases e1 : whole q <;> cases e2 : whole r <;> cases e3 : thisOnlyS laz <;>
    cases e4 : lazeBig (sofsHas st.sofs) laz <;> cases t <;>
    simp [nock_exec, rsS, rsCoreG, rsDoor, GoalS.toNoun, hana, wh_at, wh_arm, hw1, hw2, e1, e2, e3, e4,
      lto_at', lto_arm, hlto, lbg_at', lbg_arm, hlbg, lsf_at', lsf_arm, hlsf, loob]

/-- **The fork**: `+laze-branch`, then the tail on `[%next goal-1]`, `[%next goal-0]`, `[%next this]`. -/
theorem six_fork (env : ShapeEnv) (p q r : Nomm) (sup : Option Nomm) (laz : Laze CSet) (hl : LzNZ laz)
    (st : RSt CSet) (y : RsRest) (hy : E y) (hcp : CallCode cod (shapeCE env) p)
    (hr : ∀ g st1, GoalNZ g → RsAtE ctx env E r sup g st1)
    (hq : ∀ g st1, GoalNZ g → RsAtE ctx env E q sup g st1)
    (hp : ∀ g st1, GoalNZ g → RsAtE ctx env E p sup g st1) :
    nock (C (A 0) (sixS ctx p q r sup laz st y)) sixForkN
      = (sixFork env (runShape env sup p) (runShape env sup q) (runShape env sup r) p laz st).map
          fun p => C p.1.toNoun (rsGenNoun p.2 y) := by
  rw [sixFork_tail]
  have hlb := lbr_call hc h7 (C (A 0) (sixS ctx p q r sup laz st y)) laz st y
    (by simp [sixS, rsS, rsCoreG, nock_exec]) (by simp [sixS, rsS, rsCoreG, GoalS.toNoun, nock_exec])
  change nock _ rs6KLbr = _ at hlb
  have hstep : nock (C (A 0) (sixS ctx p q r sup laz st y)) sixForkN
      = (lazeBranch laz st).bind fun w => nock (C (C w.1.1.toNoun w.1.2.toNoun) (C (A 0) (sixS ctx p q r sup laz w.2 y)))
          (sixTailN (C (C (A 1) (A 0x7478656e)) (C (A 0) (A 5))) (C (C (A 1) (A 0x7478656e)) (C (A 0) (A 12)))
            (C (C (A 1) (A 0x7478656e)) (C (A 0) (A 254)))) := by
    unfold sixForkN
    generalize sixTailN _ _ _ = TL
    simp only [sixS, rsS, rsCoreG, rsDoor] at hlb ⊢
    generalize rs6KLbr = LB at hlb ⊢
    cases e1 : lazeBranch laz st with
    | none => rw [e1] at hlb; simp [nock_exec, hlb]
    | some r1 =>
      rw [e1] at hlb
      simp [nock_exec, hlb]
  rw [hstep]
  cases e1 : lazeBranch laz st with
  | none => rfl
  | some r1 =>
    obtain ⟨⟨g0, g1⟩, st1⟩ := r1
    have hnz := lazeBranch_nz laz st (g0, g1) st1 hl e1
    have ht := six_tail hc h7 hcode env p q r sup (GoalS.next g1) (GoalS.next g0) (GoalS.next thisL) st1 y hy hcp
      (fun st2 => hr _ st2 hnz.2) (fun st2 => hq _ st2 hnz.1) (fun st2 => hp _ st2 lzNZ_thisL)
      (C g0.toNoun g1.toNoun) (A 0) (GoalS.next laz).toNoun (GoalS.next laz).toNoun
      (C (C (A 1) (A 0x7478656e)) (C (A 0) (A 5))) (C (C (A 1) (A 0x7478656e)) (C (A 0) (A 12)))
      (C (C (A 1) (A 0x7478656e)) (C (A 0) (A 254)))
      (fun Z => by simp [nock_exec, GoalS.toNoun]) (fun a Z => by simp [nock_exec, GoalS.toNoun])
      (fun a b c Z => by simp [nock_exec, GoalS.toNoun, thisL_noun])
    rw [n6_noun] at ht
    simp only [Option.bind_some]
    exact ht

/-- **The leap**: the run on `[%next rest]`, then `+roll` of `+laze-copy` over the `bys`. -/
theorem six_leap (p q r : Nomm) (sup : Option Nomm) (laz rest : Laze CSet) (bys : List (Laze CSet))
    (st : RSt CSet) (y : RsRest) (R : Option (Laze CSet × RSt CSet))
    (hrec : nock (rsCoreG (Nomm.n6 p q r).toNoun (GoalS.next rest).toNoun (supNoun sup) (rsDoor st y ctx)) rsGate
      = R.map fun p => C p.1.toNoun (rsGenNoun p.2 y)) :
    nock (C (llsN (some (rest, bys))) (sixS ctx p q r sup laz st y)) sixDisp
      = (R.bind fun pr => (bys.foldlM (fun acc b => lazeCopy acc b) pr.1).map fun l => (l, pr.2)).map
          fun p => C p.1.toNoun (rsGenNoun p.2 y) := by
  have hrec' := hrec
  simp only [rsCoreG, rsDoor, GoalS.toNoun, n6_noun] at hrec'
  unfold sixDisp rs6Leap
  cases R with
  | none =>
    rw [Option.map_none] at hrec'
    generalize rs6Tk = TK
    generalize rs6Kerf = KF
    generalize rs6Gb = GB
    generalize rs6Rest = RR
    simp [nock_exec, llsN, unitNoun, sixS, rsS, rsCoreG, rsDoor, GoalS.toNoun, hrec']
  | some pr =>
    obtain ⟨l, st1⟩ := pr
    simp only [Option.map_some] at hrec'
    have hroll := roll_gateO Laze.toNoun Laze.toNoun layer2 sixRollB (noneL : Laze CSet).toNoun
      (C l.toNoun (C (llsN (some (rest, bys))) (sixS ctx p q r sup laz st1 y)))
      (fun acc b => lazeCopy acc b) bys l (by
        intro x _ acc
        have hlc := lc_all hc h7 (rsGenNoun st1 y) acc x
        unfold sixRollB
        simp [nock_exec, sixS, rsS, rsCoreG, rsDoor, lc_at', lc_arm, hlc])
    rw [noneL_noun] at hroll
    simp only [llsN, unitNoun, sixS, rsS, rsCoreG, rsDoor, sixRollB, GoalS.toNoun] at hroll
    have hl2 : slot? 262143 ctx = some layer2 := hc
    generalize rs6Tk = TK
    generalize rs6Kerf = KF
    generalize rs6Gb = GB
    generalize rs6Rest = RR
    cases e : bys.foldlM (fun acc b => lazeCopy acc b) l with
    | none =>
      rw [e] at hroll
      simp [nock_exec, llsN, unitNoun, sixS, rsS, rsCoreG, rsDoor, GoalS.toNoun, hrec', hl2, roll.arm_at,
        roll_arm, hroll, e]
    | some l' =>
      rw [e] at hroll
      simp [nock_exec, llsN, unitNoun, sixS, rsS, rsCoreG, rsDoor, GoalS.toNoun, hrec', hl2, roll.arm_at,
        roll_arm, hroll, e, sixRollB]

end

/-- The dispatch with no leap and the kerf test passed (`rs6Tk` is `&`): the kerf. -/
theorem six_kerf_disp (T : Noun) (kb : Bool) (htk : nock (C (A 0) T) rs6Tk = some (A 0))
    (hkt : nock (C (A 0) T) rs6KTest = some (loob kb)) :
    nock (C (A 0) T) sixDisp = if kb then nock (C (A 0) T) rs6KRec else nock (C (A 0) T) sixForkN := by
  unfold sixDisp
  rw [rs6Kerf_fork]
  generalize rs6Tk = TK at htk
  generalize rs6KTest = KT at hkt
  generalize rs6KRec = KR
  generalize sixForkN = FN
  generalize rs6Gb = GB
  generalize rs6Rest = RR
  generalize rs6Leap = LP
  cases kb <;> simp [nock_exec, htk, hkt, loob]

section
variable (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
include hc h7 hcode

/-- **The case `%6` under `[%next laz]` at every fuel that covers it** (`SixDeep`). -/
theorem six_fuel (env : ShapeEnv) (hcn : CodeNomms env.cod cod) (p q r : Nomm) (sup : Option Nomm)
    (y : RsRest) (hy : E y) (hcp : CallCode cod (shapeCE env) p) (hq0 : Bake.NoAx0 q) (hr0 : Bake.NoAx0 r)
    (hun : ∀ ned, unsS env q r ned ≠ Option.none)
    (hr : ∀ g st1, GoalNZ g → RsAtE ctx env E r sup g st1)
    (hq : ∀ g st1, GoalNZ g → RsAtE ctx env E q sup g st1)
    (hp : ∀ g st1, GoalNZ g → RsAtE ctx env E p sup g st1) :
    ∀ (f : Nat) (laz : Laze CSet) (st : RSt CSet), LzNZ laz → SixDeep q r f laz →
      nock (rsCoreG (Nomm.n6 p q r).toNoun (GoalS.next laz).toNoun (supNoun sup) (rsDoor st y ctx)) rsGate
        = (sixShape env (runShape env sup p) (runShape env sup q) (runShape env sup r) p q r f laz st).map
            fun p => C p.1.toNoun (rsGenNoun p.2 y)
  | 0, _, _, _, h => h.elim
  | f + 1, laz, st, hl, ⟨hf1, hd⟩ => by
    rw [six_entry, six_lep h7 p q r sup laz st y hl hq0 hr0]
    cases e : lazeLeaps laz q r with
    | none => simp [sixShape, shLiftS, e, bind, StateT.bind]
    | some x =>
      cases x with
      | some rb =>
        obtain ⟨rest, bys⟩ := rb
        have hnz := (lazeLeaps_nz hl hq0 hr0 e).1
        have hrec := six_fuel env hcn p q r sup y hy hcp hq0 hr0 hun hr hq hp f rest st hnz (hd rest bys e)
        simp only [Option.map_some, Option.bind_some]
        rw [six_leap hc h7 hcode p q r sup laz rest bys st y _ hrec]
        congr 1
        cases e2 : sixShape env (runShape env sup p) (runShape env sup q) (runShape env sup r) p q r f rest st with
        | none => simp [sixShape, shLiftS, e, e2, bind, StateT.bind]
        | some pr =>
          obtain ⟨l0, st0⟩ := pr
          cases e3 : bys.foldlM (fun acc b => lazeCopy acc b) l0 <;>
            simp [sixShape, shLiftS, e, e2, e3, bind, StateT.bind]
      | none =>
        obtain ⟨sur, fk, bd⟩ := laz
        have hl0 : LzNZ (Laze.mk sur [] [] : Laze CSet) := ⟨hl.1, trivial, trivial⟩
        simp only [Option.map_some, Option.bind_some]
        have hA : llsN Option.none = A 0 := rfl
        rw [hA]
        cases hne : noneEq (Laze.mk SureO.bunt fk bd : Laze CSet) with
        | true =>
          rw [six_br hc h7 hcode env p q r sup sur fk bd st y hy hcp hne (fun st1 => hr _ st1 hl0)
            (fun st1 => hq _ st1 hl0) (fun st1 => hp _ st1 trivial)]
          congr 1
          simp [sixShape, shLiftS, e, hne, bind, StateT.bind, Laze.fork, Laze.bond, Laze.sure]
        | false =>
          obtain ⟨t, ht⟩ := sfk_some (sofsHas st.sofs) (unsS env q r)
            (fun ned => Option.ne_none_iff_exists'.mp (hun ned)) (Laze.mk sur fk bd)
          have htk := six_tk hc p q r sup sur fk bd st y
          rw [hne] at htk
          have hkt := six_ktest hc h7 hcode env hcn p q r sup (Laze.mk sur fk bd) st y t ht
          have hm : sixShape env (runShape env sup p) (runShape env sup q) (runShape env sup r) p q r (f + 1)
              (Laze.mk sur fk bd) st
              = if ((whole q && whole r) || thisOnlyS (Laze.mk sur fk bd : Laze CSet)
                  || lazeBig (sofsHas st.sofs) (Laze.mk sur fk bd) || t) = true
                then sixShape env (runShape env sup p) (runShape env sup q) (runShape env sup r) p q r f thisL st
                else sixFork env (runShape env sup p) (runShape env sup q) (runShape env sup r) p (Laze.mk sur fk bd) st := by
            cases h1 : whole q <;> cases h2 : whole r <;> cases h3 : thisOnlyS (Laze.mk sur fk bd : Laze CSet) <;>
              cases h4 : lazeBig (sofsHas st.sofs) (Laze.mk sur fk bd) <;>
              simp [sixShape, shLiftS, e, hne, ht, h1, h2, h3, h4, bind, StateT.bind, get, getThe, MonadState.get,
                StateT.get, rs6_get, pure, StateT.pure, Laze.fork, Laze.bond] <;> cases t <;> rfl
          rw [hm, six_kerf_disp _ _ (by simpa [loob] using htk) hkt]
          generalize ((whole q && whole r) || thisOnlyS (Laze.mk sur fk bd : Laze CSet)
            || lazeBig (sofsHas st.sofs) (Laze.mk sur fk bd) || t) = kb
          cases kb with
          | true =>
            simp only [if_true]
            rw [six_rec]
            obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
            exact six_this hc h7 hcode env p q r sup f' st y hy hcp hq0 hr0 (fun st1 => hr _ st1 lzNZ_thisL)
              (fun st1 => hq _ st1 lzNZ_thisL) (fun st1 => hp _ st1 trivial)
          | false =>
            simp only [Bool.false_eq_true, if_false]
            exact six_fork hc h7 hcode env p q r sup (Laze.mk sur fk bd) hl st y hy hcp hr hq hp

/-- **The case `[6 p q r]` under `[%next laz]`** on `RsAtE`, at `sixFuel`, where the fuel covers the
runs on the same nomm (`SixDeep`). -/
theorem rs_n6NE (env : ShapeEnv) (hcn : CodeNomms env.cod cod) (p q r : Nomm) (sup : Option Nomm)
    (laz : Laze CSet) (hl : LzNZ laz) (st : RSt CSet) (hcp : CallCode cod (shapeCE env) p)
    (hq0 : Bake.NoAx0 q) (hr0 : Bake.NoAx0 r) (hun : ∀ ned, unsS env q r ned ≠ Option.none)
    (hdeep : SixDeep q r sixFuel laz)
    (hr : ∀ g st1, GoalNZ g → RsAtE ctx env E r sup g st1)
    (hq : ∀ g st1, GoalNZ g → RsAtE ctx env E q sup g st1)
    (hp : ∀ g st1, GoalNZ g → RsAtE ctx env E p sup g st1) :
    RsAtE ctx env E (Nomm.n6 p q r) sup (GoalS.next laz) st := by
  intro y hy
  rw [six_fuel hc h7 hcode env hcn p q r sup y hy hcp hq0 hr0 hun hr hq hp sixFuel laz st hl hdeep]
  rfl

end

/-! ## `LzNZ` is kept -/

theorem sixTailM_nz (env : ShapeEnv) (rp rq rr : GoalS CSet → SM CSet (Laze CSet)) (p : Nomm) (gr gq gp : GoalS CSet)
    (hrp : ∀ st l st1, rp gp st = some (l, st1) → LzNZ l)
    (hrq : ∀ st l st1, rq gq st = some (l, st1) → LzNZ l)
    (hrr : ∀ st l st1, rr gr st = some (l, st1) → LzNZ l)
    (st : RSt CSet) (l : Laze CSet) (st1 : RSt CSet) (e : sixTailM env rp rq rr p gr gq gp st = some (l, st1)) :
    LzNZ l := by
  unfold sixTailM at e
  obtain ⟨l1, s1, e1, k1⟩ := sm_bind_some e
  obtain ⟨l0, s2, e2, k2⟩ := sm_bind_some k1
  obtain ⟨lz, s3, e3, k3⟩ := sm_bind_some k2
  obtain ⟨lz', s4, e4, k4⟩ := sm_bind_some k3
  obtain ⟨st', s5, e5, k5⟩ := sm_bind_some k4
  obtain ⟨lc, s6, e6, k6⟩ := sm_bind_some k5
  have h3 := lazeSect_nz l0 l1 s2 lz s3 (hrq _ _ _ e2) (hrr _ _ _ e1) e3
  obtain ⟨a, ea, ra⟩ := shLiftS_some e4
  simp only [Prod.mk.injEq] at ra
  have h4 : LzNZ lz' := by rw [ra.1]; exact lazePastFork_nz env lz p a h3 ea
  have hbig : LzNZ (if lazeBig (sofsHas st'.sofs) lz' = true then thisL else lz') := by
    split
    · exact lzNZ_thisL
    · exact h4
  exact lazeCopyEnd_nz (hrp _ _ _ e6) hbig k6

theorem foldCopy_nz : ∀ (bys : List (Laze CSet)) (l r : Laze CSet), LzNZ l → (∀ b ∈ bys, LzNZ b) →
    bys.foldlM (fun acc b => lazeCopy acc b) l = some r → LzNZ r
  | [], l, r, hl, _, e => by simp at e; subst e; exact hl
  | b :: bs, l, r, hl, hb, e => by
    simp only [List.foldlM_cons] at e
    cases e1 : lazeCopy l b with
    | none => rw [e1] at e; cases e
    | some c =>
      rw [e1] at e
      exact foldCopy_nz bs c r (lazeCopy_nz l b c hl (hb b (by simp)) e1) (fun x hx => hb x (by simp [hx])) e

/-- **`sixShape` keeps `LzNZ`**, given that the runs of `p`, `q`, `r` do on goals of `GoalNZ`. -/
theorem sixShape_nz (env : ShapeEnv) (rp rq rr : GoalS CSet → SM CSet (Laze CSet)) (p q r : Nomm)
    (hq0 : Bake.NoAx0 q) (hr0 : Bake.NoAx0 r)
    (hrp : ∀ g st l st1, GoalNZ g → rp g st = some (l, st1) → LzNZ l)
    (hrq : ∀ g st l st1, GoalNZ g → rq g st = some (l, st1) → LzNZ l)
    (hrr : ∀ g st l st1, GoalNZ g → rr g st = some (l, st1) → LzNZ l) :
    ∀ (f : Nat) (laz : Laze CSet) (st : RSt CSet) (l : Laze CSet) (st1 : RSt CSet), LzNZ laz →
      sixShape env rp rq rr p q r f laz st = some (l, st1) → LzNZ l
  | 0, _, _, _, _, _, e => by simp [sixShape] at e
  | f + 1, laz, st, l, st1, hl, e => by
    simp only [sixShape] at e
    obtain ⟨lep, s1, e1, e⟩ := sm_bind_some e
    obtain ⟨a, ea, ra⟩ := shLiftS_some e1
    simp only [Prod.mk.injEq] at ra
    obtain ⟨ra1, ra2⟩ := ra
    simp only [ra1] at e
    clear e1
    cases a with
    | some rb =>
      obtain ⟨rest, bys⟩ := rb
      obtain ⟨hrest, hbys⟩ := lazeLeaps_nz hl hq0 hr0 ea
      obtain ⟨l0, s2, e2, e⟩ := sm_bind_some e
      have h0 := sixShape_nz env rp rq rr p q r hq0 hr0 hrp hrq hrr f rest _ l0 s2 hrest e2
      obtain ⟨c, ec, rc⟩ := shLiftS_some e
      simp only [Prod.mk.injEq] at rc
      have hlc : l = c := by first | exact rc.1.symm | exact rc.1
      rw [hlc]
      exact foldCopy_nz bys l0 c h0 hbys ec
    | none =>
      obtain ⟨sur, fk, bd⟩ := laz
      simp only [Laze.fork, Laze.bond, Laze.sure] at e
      cases hne : noneEq (Laze.mk SureO.bunt fk bd : Laze CSet) with
      | false =>
        simp only [hne, Bool.not_false, ↓reduceIte] at e
        obtain ⟨st', s2, e2, e⟩ := sm_bind_some e
        obtain ⟨kerf, s3, e3, e⟩ := sm_bind_some e
        cases kerf with
        | true =>
          simp only [↓reduceIte] at e
          exact sixShape_nz env rp rq rr p q r hq0 hr0 hrp hrq hrr f thisL _ l st1 lzNZ_thisL e
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at e
          unfold sixFork at e
          obtain ⟨gs, s4, e4, e⟩ := sm_bind_some e
          have hnz := lazeBranch_nz (Laze.mk sur fk bd) s3 gs s4 hl e4
          have e' : sixTailM env rp rq rr p (GoalS.next gs.2) (GoalS.next gs.1) (GoalS.next thisL) s4
              = some (l, st1) := by
            obtain ⟨g0, g1⟩ := gs
            exact e
          exact sixTailM_nz env rp rq rr p _ _ _ (fun st l st1 e => hrp (GoalS.next thisL) st l st1 lzNZ_thisL e)
            (fun st l st1 e => hrq (GoalS.next gs.1) st l st1 hnz.1 e)
            (fun st l st1 e => hrr (GoalS.next gs.2) st l st1 hnz.2 e) s4 l st1 e'
      | true =>
        simp only [hne, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at e
        have hl0 : LzNZ (Laze.mk sur [] [] : Laze CSet) := ⟨hl.1, trivial, trivial⟩
        exact sixBranch_nz env rp rq rr p _ (fun st l st1 e => hrp GoalS.pick st l st1 trivial e)
          (fun st l st1 e => hrq (GoalS.next (Laze.mk sur [] [])) st l st1 hl0 e)
          (fun st l st1 e => hrr (GoalS.next (Laze.mk sur [] [])) st l st1 hl0 e) _ l st1 e

end Compiler
end Formalization
