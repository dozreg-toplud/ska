import lemmas.Compiler.CompRunShapeTSixTail
import lemmas.Compiler.CompRunShapeSixN

/-!
# `+run-shape`: the case `[6 p q r]` under `[%next laz]`, threading the rest (track A, 2026-11-28)

`CompRunShapeSixN.lean` on `RsAtT`: the runs of `p`, `q`, `r` and the runs on the same nomm (the leap,
the kerf) may move the rest of `gen` (a miss of `+callee-need`), so every arm after a run reads the
rest that run returned.  The tests (`six_lep`, `six_tk`, `six_ktest`) run before any run, at the rest
the case was given.

* `six_brT` (the tail on `goal-branch`), `six_thisT` (the run on `[%next this]`), `six_forkT` (the
  fork), `six_leapT` (the leap: the run on `[%next rest]` moves the rest from `y` to `y'`, the
  `+roll` of `+laze-copy` runs at `y'`).
* **`six_fuelT`**: at every fuel `f` and `laz` of `LzNZ` with `SixDeep q r f laz`, the gate is
  `sixShape .. f laz` with some rest `y'` of `E` that `Rl` relates to `y`.
* **`rs_n6NT`**: the case on `RsAtT`, at `sixFuel`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun} {E : RsRest → Prop} {Rl : RsRest → RsRest → Prop}

section
variable (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
include hc h7 hcode

/-- **The tail on `goal-branch`, threading the rest**: `laz` none-equivalent but for its sure need. -/
theorem six_brT (env : ShapeEnv) (hR : RlPre Rl) (p q r : Nomm) (sup : Option Nomm) (sur : SureO CSet)
    (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet))) (bd : List (Nat × Laze CSet)) (st : RSt CSet)
    (y : RsRest) (hy : E y) (hcp : CallCode cod (shapeCE env) p)
    (hne : noneEq (Laze.mk SureO.bunt fk bd : Laze CSet) = true)
    (hr : ∀ st1, RsAtT ctx env E Rl r sup (GoalS.next (Laze.mk sur [] [])) st1)
    (hq : ∀ st1, RsAtT ctx env E Rl q sup (GoalS.next (Laze.mk sur [] [])) st1)
    (hp : ∀ st1, RsAtT ctx env E Rl p sup GoalS.pick st1) :
    ∃ y', Rl y y' ∧ E y' ∧
      nock (C (A 0) (sixS ctx p q r sup (Laze.mk sur fk bd) st y)) sixDisp
        = (sixBranch env (runShape env sup p) (runShape env sup q) (runShape env sup r) p
            (GoalS.next (Laze.mk sur [] [])) st).map fun p => C p.1.toNoun (rsGenNoun p.2 y') := by
  have htk := six_tk hc p q r sup sur fk bd st y
  rw [hne] at htk
  have hgb := six_gb (ctx := ctx) p q r sup sur fk bd st y
  obtain ⟨y', hR', hy', ht⟩ := six_tailT hc h7 hcode env hR p q r sup (GoalS.next (Laze.mk sur [] []))
    (GoalS.next (Laze.mk sur [] [])) GoalS.pick st y hy hcp hr hq hp (GoalS.next (Laze.mk sur [] [] : Laze CSet)).toNoun
    (A 0) (GoalS.next (Laze.mk sur fk bd)).toNoun (GoalS.next (Laze.mk sur fk bd)).toNoun
    (C (A 0) (A 2)) (C (A 0) (A 6)) (C (A 1) (C (A 0x6b636970) (A 0)))
    (fun Z => by simp [nock_exec]) (fun a Z => by simp [nock_exec])
    (fun a b c Z => by simp [nock_exec, GoalS.toNoun])
  refine ⟨y', hR', hy', ?_⟩
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

/-- **The run on `[%next this]`, threading the rest**: the tail on `[%next [this ~ ~]]`, at every fuel. -/
theorem six_thisT (env : ShapeEnv) (hR : RlPre Rl) (p q r : Nomm) (sup : Option Nomm) (f : Nat) (st : RSt CSet)
    (y : RsRest) (hy : E y) (hcp : CallCode cod (shapeCE env) p) (hq0 : Bake.NoAx0 q) (hr0 : Bake.NoAx0 r)
    (hr : ∀ st1, RsAtT ctx env E Rl r sup (GoalS.next (Laze.mk (thisL : Laze CSet).sure [] [])) st1)
    (hq : ∀ st1, RsAtT ctx env E Rl q sup (GoalS.next (Laze.mk (thisL : Laze CSet).sure [] [])) st1)
    (hp : ∀ st1, RsAtT ctx env E Rl p sup GoalS.pick st1) :
    ∃ y', Rl y y' ∧ E y' ∧
      nock (rsCoreG (Nomm.n6 p q r).toNoun (GoalS.next (thisL : Laze CSet)).toNoun (supNoun sup) (rsDoor st y ctx)) rsGate
        = (sixShape env (runShape env sup p) (runShape env sup q) (runShape env sup r) p q r (f + 1) thisL st).map
            fun p => C p.1.toNoun (rsGenNoun p.2 y') := by
  have hleap : lazeLeaps (thisL : Laze CSet) q r = some Option.none := by simp [lazeLeaps, thisL, Laze.fork, Laze.bond]
  have hsm : HoonSet.small (HoonSet.empty : CSet) = true :=
    (HoonSet.small_iff _).2 fun x hx => absurd hx (HoonSet.mem_empty x)
  have hne : noneEq (Laze.mk SureO.bunt [] [] : Laze CSet) = true := by
    simp [noneEq, noneEqF, noneEqB, SureO.bunt, hsm]
  have hleap' : lazeLeaps (Laze.mk ⟨NeedOrd.this, HoonSet.empty⟩ [] [] : Laze CSet) q r = some Option.none := hleap
  obtain ⟨y', hR', hy', hb⟩ := six_brT hc h7 hcode env hR p q r sup thisL.sure [] [] st y hy hcp hne hr hq hp
  refine ⟨y', hR', hy', ?_⟩
  rw [six_entry, six_lep h7 p q r sup thisL st y lzNZ_thisL hq0 hr0, hleap]
  have hm : sixShape env (runShape env sup p) (runShape env sup q) (runShape env sup r) p q r (f + 1) thisL
      = sixBranch env (runShape env sup p) (runShape env sup q) (runShape env sup r) p
          (GoalS.next (Laze.mk (thisL : Laze CSet).sure [] [])) := by
    funext st0
    simp [sixShape, shLiftS, hleap', bind, StateT.bind, thisL, Laze.fork, Laze.bond, hne, pure, StateT.pure]
  rw [hm]
  simpa [llsN, unitNoun, thisL, Laze.sure] using hb

/-- **The fork, threading the rest**: `+laze-branch`, then the tail on `[%next goal-1]`,
`[%next goal-0]`, `[%next this]`. -/
theorem six_forkT (env : ShapeEnv) (hR : RlPre Rl) (p q r : Nomm) (sup : Option Nomm) (laz : Laze CSet)
    (hl : LzNZ laz) (st : RSt CSet) (y : RsRest) (hy : E y) (hcp : CallCode cod (shapeCE env) p)
    (hr : ∀ g st1, GoalNZ g → RsAtT ctx env E Rl r sup g st1)
    (hq : ∀ g st1, GoalNZ g → RsAtT ctx env E Rl q sup g st1)
    (hp : ∀ g st1, GoalNZ g → RsAtT ctx env E Rl p sup g st1) :
    ∃ y', Rl y y' ∧ E y' ∧
      nock (C (A 0) (sixS ctx p q r sup laz st y)) sixForkN
        = (sixFork env (runShape env sup p) (runShape env sup q) (runShape env sup r) p laz st).map
            fun p => C p.1.toNoun (rsGenNoun p.2 y') := by
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
  | none => exact ⟨y, hR.refl y, hy, rfl⟩
  | some r1 =>
    obtain ⟨⟨g0, g1⟩, st1⟩ := r1
    have hnz := lazeBranch_nz laz st (g0, g1) st1 hl e1
    obtain ⟨y', hR', hy', ht⟩ := six_tailT hc h7 hcode env hR p q r sup (GoalS.next g1) (GoalS.next g0)
      (GoalS.next thisL) st1 y hy hcp
      (fun st2 => hr _ st2 hnz.2) (fun st2 => hq _ st2 hnz.1) (fun st2 => hp _ st2 lzNZ_thisL)
      (C g0.toNoun g1.toNoun) (A 0) (GoalS.next laz).toNoun (GoalS.next laz).toNoun
      (C (C (A 1) (A 0x7478656e)) (C (A 0) (A 5))) (C (C (A 1) (A 0x7478656e)) (C (A 0) (A 12)))
      (C (C (A 1) (A 0x7478656e)) (C (A 0) (A 254)))
      (fun Z => by simp [nock_exec, GoalS.toNoun]) (fun a Z => by simp [nock_exec, GoalS.toNoun])
      (fun a b c Z => by simp [nock_exec, GoalS.toNoun, thisL_noun])
    refine ⟨y', hR', hy', ?_⟩
    rw [n6_noun] at ht
    simp only [Option.bind_some]
    exact ht

/-- **The leap, threading the rest**: the run on `[%next rest]` from the rest `y` returns at `y'`,
then `+roll` of `+laze-copy` over the `bys` runs at `y'`. -/
theorem six_leapT (p q r : Nomm) (sup : Option Nomm) (laz rest : Laze CSet) (bys : List (Laze CSet))
    (st : RSt CSet) (y y' : RsRest) (R : Option (Laze CSet × RSt CSet))
    (hrec : nock (rsCoreG (Nomm.n6 p q r).toNoun (GoalS.next rest).toNoun (supNoun sup) (rsDoor st y ctx)) rsGate
      = R.map fun p => C p.1.toNoun (rsGenNoun p.2 y')) :
    nock (C (llsN (some (rest, bys))) (sixS ctx p q r sup laz st y)) sixDisp
      = (R.bind fun pr => (bys.foldlM (fun acc b => lazeCopy acc b) pr.1).map fun l => (l, pr.2)).map
          fun p => C p.1.toNoun (rsGenNoun p.2 y') := by
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
      (C l.toNoun (C (llsN (some (rest, bys))) (sixS ctx p q r sup laz st1 y')))
      (fun acc b => lazeCopy acc b) bys l (by
        intro x _ acc
        have hlc := lc_all hc h7 (rsGenNoun st1 y') acc x
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

/-- **The case `%6` under `[%next laz]` at every fuel that covers it** (`SixDeep`), threading the rest. -/
theorem six_fuelT (env : ShapeEnv) (hR : RlPre Rl) (hcn : CodeNomms env.cod cod) (p q r : Nomm)
    (sup : Option Nomm) (y : RsRest) (hy : E y) (hcp : CallCode cod (shapeCE env) p) (hq0 : Bake.NoAx0 q)
    (hr0 : Bake.NoAx0 r) (hun : ∀ ned, unsS env q r ned ≠ Option.none)
    (hr : ∀ g st1, GoalNZ g → RsAtT ctx env E Rl r sup g st1)
    (hq : ∀ g st1, GoalNZ g → RsAtT ctx env E Rl q sup g st1)
    (hp : ∀ g st1, GoalNZ g → RsAtT ctx env E Rl p sup g st1) :
    ∀ (f : Nat) (laz : Laze CSet) (st : RSt CSet), LzNZ laz → SixDeep q r f laz →
      ∃ y', Rl y y' ∧ E y' ∧
        nock (rsCoreG (Nomm.n6 p q r).toNoun (GoalS.next laz).toNoun (supNoun sup) (rsDoor st y ctx)) rsGate
          = (sixShape env (runShape env sup p) (runShape env sup q) (runShape env sup r) p q r f laz st).map
              fun p => C p.1.toNoun (rsGenNoun p.2 y')
  | 0, _, _, _, h => h.elim
  | f + 1, laz, st, hl, ⟨hf1, hd⟩ => by
    rw [six_entry, six_lep h7 p q r sup laz st y hl hq0 hr0]
    cases e : lazeLeaps laz q r with
    | none => exact ⟨y, hR.refl y, hy, by simp [sixShape, shLiftS, e, bind, StateT.bind]⟩
    | some x =>
      cases x with
      | some rb =>
        obtain ⟨rest, bys⟩ := rb
        have hnz := (lazeLeaps_nz hl hq0 hr0 e).1
        obtain ⟨y', hR', hy', hrec⟩ :=
          six_fuelT env hR hcn p q r sup y hy hcp hq0 hr0 hun hr hq hp f rest st hnz (hd rest bys e)
        refine ⟨y', hR', hy', ?_⟩
        simp only [Option.map_some, Option.bind_some]
        rw [six_leapT hc h7 hcode p q r sup laz rest bys st y y' _ hrec]
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
          obtain ⟨y', hR', hy', hb⟩ := six_brT hc h7 hcode env hR p q r sup sur fk bd st y hy hcp hne
            (fun st1 => hr _ st1 hl0) (fun st1 => hq _ st1 hl0) (fun st1 => hp _ st1 trivial)
          refine ⟨y', hR', hy', ?_⟩
          rw [hb]
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
            exact six_thisT hc h7 hcode env hR p q r sup f' st y hy hcp hq0 hr0 (fun st1 => hr _ st1 lzNZ_thisL)
              (fun st1 => hq _ st1 lzNZ_thisL) (fun st1 => hp _ st1 trivial)
          | false =>
            simp only [Bool.false_eq_true, if_false]
            exact six_forkT hc h7 hcode env hR p q r sup (Laze.mk sur fk bd) hl st y hy hcp hr hq hp

/-- **The case `[6 p q r]` under `[%next laz]`** on `RsAtT`, at `sixFuel`, where the fuel covers the
runs on the same nomm (`SixDeep`). -/
theorem rs_n6NT (env : ShapeEnv) (hR : RlPre Rl) (hcn : CodeNomms env.cod cod) (p q r : Nomm)
    (sup : Option Nomm) (laz : Laze CSet) (hl : LzNZ laz) (st : RSt CSet) (hcp : CallCode cod (shapeCE env) p)
    (hq0 : Bake.NoAx0 q) (hr0 : Bake.NoAx0 r) (hun : ∀ ned, unsS env q r ned ≠ Option.none)
    (hdeep : SixDeep q r sixFuel laz)
    (hr : ∀ g st1, GoalNZ g → RsAtT ctx env E Rl r sup g st1)
    (hq : ∀ g st1, GoalNZ g → RsAtT ctx env E Rl q sup g st1)
    (hp : ∀ g st1, GoalNZ g → RsAtT ctx env E Rl p sup g st1) :
    RsAtT ctx env E Rl (Nomm.n6 p q r) sup (GoalS.next laz) st := by
  intro y hy
  obtain ⟨y', hR', hy', h⟩ :=
    six_fuelT hc h7 hcode env hR hcn p q r sup y hy hcp hq0 hr0 hun hr hq hp sixFuel laz st hl hdeep
  refine ⟨y', hR', hy', ?_⟩
  rw [h]
  rfl

end

end Compiler
end Formalization
