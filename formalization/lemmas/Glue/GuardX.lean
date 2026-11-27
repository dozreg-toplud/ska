import lemmas.Glue.GuardArmsL
import lemmas.Ska.RawInvATX

/-!
# `BlocksOK` kept by `runL` on `FragX` (track G, step 3 of `GuardMonoX`)

**`runX_kp`**: on every nomm of `FragX` with at most 255 `%6`, every run of
`runL` for a fork-free goal whose `%next` jump passes no `~` and whose
`%pick` jumps pass nothing (`GJX`) keeps `Inv` (`BlocksOK`, not dropping)
and returns a jump that passes no `~`.

* The first fragment by `run_kp` (`runL_frag`); `[7 p q]` and `[7 [0 axe] q]`
  by `runL_n7`, `runL_seven_from`.
* `%3`, `%4`, cons, `%5`, `%10`: the code of `runL` on a fork-free goal,
  whose lazy arms are the sure ones mapped (`splitL_mk`, `intoL_mk`,
  `collapseLazyAtomL_mk`, `simpleNextL_toL`, `pastL_pure`), and `+copy` of a
  lazy need with forks (`kp_copyL`).
* `%6` (`rkx_sixP`, `rkx_sixN`): taken apart by track C's `sixBody_apart`
  and `sixNextSimple_apart`.  `+fork-sure`'s blocks pass registers
  (`kp_forkSure`); `+sect` leaves the blocks of its two hop blocks
  (`sect_spec`: the branches leave `cond` as it is, `KeepR.cnd`, so the
  threading, the one place that passes `~`, threads nothing); the fork is
  not big (`KeepR.size`), so `+lazy-shut` does not run `+kern`.  The facts
  of `KeepX` ask the goal's registers to be below `re`: the sub-goals are
  `jmp0`s and fork-fresh registers (`forkSure_spec`), so no hypothesis on
  the parent's goal beyond `GJX` is needed.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt Comp Raw Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- The jumps of a goal of `FragX`: a `%next` jump passes no `~`, a
`%pick` jump passes nothing. -/
def GJX : CGoal S → Prop
  | CGoal.next _ th => JOK th
  | CGoal.pick z o => z.args = [] ∧ o.args = []
  | CGoal.done => True

theorem jok_of_nil {j : Jmp} (h : j.args = []) : JOK j := by simp [JOK, h]

theorem gjk_of_gjx {goal : CGoal S} (h : GJX goal) : GJK goal := by
  cases goal with
  | next _ _ => exact h
  | pick z o => exact ⟨jok_of_nil h.1, jok_of_nil h.2⟩
  | done => trivial

theorem goalIn_gjx {goal : CGoal S} (hn : NotNext goal) (h : GJX goal) (n : Nat) : GoalIn n goal := by
  cases goal with
  | next => exact hn.elim
  | pick z o => exact ⟨fun x hx => (by rw [h.1] at hx; cases hx), fun x hx => (by rw [h.2] at hx; cases hx)⟩
  | done => trivial

/-- **What the induction proves of one nomm.** -/
def RKX (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (nm : Nomm) : Prop :=
  ∀ (goal : CGoal S) (region : List Nat), GJX goal → sixCount nm ≤ 255 →
    KP (fun n : NextL S => JOK n.th) (runL nm (CGoal.toL goal) region : CM Map (NextL S))

/-! ## States -/

theorem inv_emitted {g : Comp.Gen Map} {b : Blob} (h : Inv g) (hb : BlockOK b) : Inv (g.emitted b) :=
  ⟨blocksOK_emitted h.1 hb, by simp only [Gen.emitted]; exact h.2⟩

theorem inv_tagged {g : Comp.Gen Map} (h : Inv g) (o : Nat) (region : List Nat) : Inv (g.tagged o region) := by
  unfold Gen.tagged; split
  · exact h
  · exact h

theorem inv_sixGenL {g : Comp.Gen Map} {t0 t1 : Jmp} (h : Inv g) (j0 : JOK t0) (j1 : JOK t1) (region : List Nat) :
    Inv (sixGenL g t0 t1 region) := by
  unfold sixGenL
  refine inv_tagged (inv_tagged (inv_emitted (inv_emitted h ?_) ?_) _ _) _ _
  · exact blockOK_of (by simpa [getJmps] using j0) noSplit_nil
  · exact blockOK_of (by simpa [getJmps] using j1) noSplit_nil

theorem inv_same {g g' : Comp.Gen Map} (hs : SameBlocks g g') (h : Inv g) : Inv g' :=
  ⟨fun k x hx => h.1 k x (by rw [← hs.2.2.2.2.2.2 k]; exact hx), by rw [hs.2.2.2.1]; exact h.2⟩

/-! ## The lazy arms on a fork-free need -/

theorem kp_pastLP (cod : Bell → Option Bool) (nex : NextL S) {nom : Nomm} (h : nom.pure = true)
    (region : List Nat) : KP (fun x : NextL S => x = nex) (pastL cod nex nom region : CM Map (NextL S)) := by
  rw [pastL_pure cod nex h region]; exact KP.pure' rfl

theorem kp_splitL_mk {laz : Sure S} {th : Jmp} (hth : JOK th) :
    KP (fun x => ∃ y : Sure S × Sure S × Nat, True ∧ x = (ofSure y.1, ofSure y.2.1, y.2.2))
      (splitL ⟨ofSure laz, th⟩ : CM Map (Lazy S × Lazy S × Nat)) := by
  rw [splitL_mk]; exact KP.map' _ (kp_split hth)

theorem kp_intoL_mk {laz : Sure S} {th : Jmp} (hth : JOK th) (axe : Nat) :
    KP (fun x => ∃ y : Sure S × Sure S × Nat, True ∧ x = (ofSure y.1, ofSure y.2.1, y.2.2))
      (intoL ⟨ofSure laz, th⟩ axe : CM Map (Lazy S × Lazy S × Nat)) := by
  rw [intoL_mk]; exact KP.map' _ (kp_into hth axe)

theorem kp_simpleNextL_toL {goal : CGoal S} (hg : GJK goal) :
    KP (fun x => ∃ n : Next S, JOK n.th ∧ x = Next.toL n) (simpleNextL (CGoal.toL goal) : CM Map (NextL S)) := by
  rw [simpleNextL_toL]; exact KP.map' _ (kp_simpleNext hg)

/-! ## The cases outside `%6` -/

theorem rkx_frag {nm : Nomm} (hf : ∀ goal : CGoal S, Frag nm goal) : RKX S Map nm := by
  intro goal region hg hc
  constructor
  intro g0 nex g1 hI h
  rw [runL_frag (hf goal)] at h
  obtain ⟨⟨n, g'⟩, hr, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact (run_kp nm goal (gjk_of_gjx hg)).k _ _ _ hI hr

theorem rkx_seven {p q : Nomm} (hq : ∀ goal : CGoal S, Frag q goal) (ihp : RKX S Map p) :
    RKX S Map (Nomm.n7 p q) := by
  intro goal region hg hc
  constructor
  intro g0 nex g1 hI h
  rw [runL_n7] at h
  obtain ⟨nx, g, h2, h3⟩ := bind_some h
  rw [runL_frag (hq goal)] at h2
  obtain ⟨⟨n, g'⟩, hr, e⟩ := Option.map_eq_some_iff.mp h2
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨I1, j1⟩ := (run_kp q goal (gjk_of_gjx hg)).k _ _ _ hI hr
  exact (ihp n.goal region j1 (by simp only [sixCount] at hc; omega)).k _ _ _ I1 h3

theorem rkx_sevenFrom {axe : Nat} {q : Nomm} (ha : 2 ≤ axe) (ihq : RKX S Map q) :
    RKX S Map (Nomm.n7 (Nomm.n0 axe) q) := by
  intro goal region hg hc
  constructor
  intro g0 nex g1 hI h
  obtain ⟨nx, laz', h2, hl, rfl⟩ := runL_seven_from ha h
  have R := (ihq goal region hg (by simp only [sixCount] at hc; omega)).k g0 nx g1 hI h2
  exact R

theorem rkx_four {p : Nomm} (ih : RKX S Map p) : RKX S Map (Nomm.n4 p) := by
  intro goal region hg hc
  have hcp : sixCount p ≤ 255 := by simpa only [sixCount] using hc
  cases goal with
  | done =>
    show KP _ (runL (Nomm.n4 p) CGoalL.done region)
    unfold runL
    exact KP.bind' KP.re' fun _ _ => KP.bind' KP.re' fun _ _ => KP.bind' (KP.emit' (by kpblk)) fun o _ =>
      ih (CGoal.next (lazyReg _) (jmp0 o)) region (jok_jmp0 o) hcp
  | pick z o =>
    obtain ⟨hz, ho⟩ := hg
    show KP _ (runL (Nomm.n4 p) (CGoalL.pick z o) region)
    unfold runL
    exact KP.bind' KP.re' fun _ _ => KP.bind' KP.re' fun _ _ => KP.bind' (KP.emit' (by kpblk)) fun o _ =>
      ih (CGoal.next (lazyReg _) (jmp0 o)) region (jok_jmp0 o) hcp
  | next sur th =>
    show KP _ (runL (Nomm.n4 p) (CGoalL.next (ofSure sur) th) region)
    unfold runL
    dsimp only
    rw [collapseLazyAtomL_mk]
    refine KP.bind' (kp_collapseLazyAtom (nex := ⟨sur, th⟩) hg) fun a _ => ?_
    refine KP.bind' (P := fun _ => True) ?_ fun x _ => ?_
    · split
      · exact KP.pure' trivial
      · exact KP.bind' KP.re' fun r _ => KP.ite' _ (KP.pure' trivial) KP.fail
    · obtain ⟨pro, th'⟩ := x
      exact KP.bind' KP.re' fun _ _ => KP.bind' (KP.emit' (by kpblk)) fun o _ =>
        ih (CGoal.next (lazyReg _) (jmp0 o)) region (jok_jmp0 o) hcp

theorem rkx_three {p : Nomm} (ih : RKX S Map p) : RKX S Map (Nomm.n3 p) := by
  intro goal region hg hc
  have hcp : sixCount p ≤ 255 := by simpa only [sixCount] using hc
  cases goal with
  | done =>
    show KP _ (runL (Nomm.n3 p) CGoalL.done region)
    unfold runL
    refine KP.bind' kp_doneBlocks fun x _ => ?_
    obtain ⟨o0, o1⟩ := x
    exact KP.bind' KP.re' fun _ _ => KP.bind' (KP.emit' (by kpblk)) fun o _ =>
      ih (CGoal.next (lazyReg _) (jmp0 o)) region (jok_jmp0 o) hcp
  | pick z o =>
    obtain ⟨hz, ho⟩ := hg
    show KP _ (runL (Nomm.n3 p) (CGoalL.pick z o) region)
    unfold runL
    exact KP.bind' KP.re' fun _ _ => KP.bind' (KP.emit' (by kpblk)) fun o _ =>
      ih (CGoal.next (lazyReg _) (jmp0 o)) region (jok_jmp0 o) hcp
  | next sur th =>
    show KP _ (runL (Nomm.n3 p) (CGoalL.next (ofSure sur) th) region)
    unfold runL
    dsimp only
    refine KP.ite' _ (ih (CGoal.next sur th) region hg hcp) ?_
    rw [collapseLazyAtomL_mk]
    refine KP.bind' (kp_collapseLazyAtom (nex := ⟨sur, th⟩) hg) fun a _ => ?_
    split
    · exact KP.fail
    · refine KP.bind' (kp_forl _ _) fun x _ => ?_
      obtain ⟨z, o'⟩ := x
      exact KP.bind' KP.re' fun _ _ => KP.bind' (KP.emit' (by kpblk)) fun o _ =>
        ih (CGoal.next (lazyReg _) (jmp0 o)) region (jok_jmp0 o) hcp

/-- The two runs and the copy of cons, `%5`, `%10`. -/
theorem kp_binTail {p q : Nomm} (ihp : RKX S Map p) (ihq : RKX S Map q) (hp : p.pure = true)
    (hcp : sixCount p ≤ 255) (hcq : sixCount q ≤ 255) {hs ts : Sure S} {j : Jmp} (hj : JOK j)
    (region : List Nat) :
    KP (fun n : NextL S => JOK n.th) (do
      let nex2 ← runL q (CGoalL.next (ofSure ts) j) region
      let nex2 ← pastL noCode nex2 p region
      let nex1 ← runL p (CGoalL.next (ofSure hs) nex2.th) region
      copyL nex1 nex2.laz : CM Map (NextL S)) := by
  refine KP.bind' (ihq (CGoal.next ts j) region hj hcq) fun nex2 h2 => ?_
  refine KP.bind' (kp_pastLP _ _ hp _) fun nex2' e => ?_
  subst e
  exact KP.bind' (ihp (CGoal.next hs nex2'.th) region h2 hcp) fun nex1 h1 => kp_copyL h1 _

theorem rkx_consNext {p q : Nomm} (ihp : RKX S Map p) (ihq : RKX S Map q) (hp : p.pure = true)
    (hq : q.pure = true) (hcp : sixCount p ≤ 255) (hcq : sixCount q ≤ 255) {sur : Sure S} {th : Jmp}
    (hth : JOK th) (region : List Nat) :
    KP (fun n : NextL S => JOK n.th) (runL (Nomm.cons p q) (CGoalL.next (ofSure sur) th) region :
      CM Map (NextL S)) := by
  rw [runL_cons_next]
  refine KP.bind' (kp_splitL_mk hth) fun x hx => ?_
  obtain ⟨y, -, rfl⟩ := hx
  obtain ⟨hs, ts, o⟩ := y
  refine KP.bind' (kp_pastLP _ _ hq _) fun nexh e => ?_
  subst e
  exact kp_binTail ihp ihq hp hcp hcq (jok_jmp0 o) region

theorem rkx_cons {p q : Nomm} (hp : p.pure = true) (hq : q.pure = true) (ihp : RKX S Map p)
    (ihq : RKX S Map q) : RKX S Map (Nomm.cons p q) := by
  intro goal region hg hc
  have hcp : sixCount p ≤ 255 := by simp only [sixCount] at hc; omega
  have hcq : sixCount q ≤ 255 := by simp only [sixCount] at hc; omega
  cases goal with
  | done =>
    show KP _ (runL (Nomm.cons p q) CGoalL.done region)
    rw [runL_cons_done]
    exact KP.bind' KP.re' fun _ _ => KP.bind' (KP.emit' (by kpblk)) fun o _ =>
      rkx_consNext ihp ihq hp hq hcp hcq (jok_jmp0 o) region
  | next sur th => exact rkx_consNext ihp ihq hp hq hcp hcq hg region
  | pick z o =>
    show KP _ (runL (Nomm.cons p q) (CGoalL.pick z o) region)
    rw [runL_cons_pick]
    exact KP.bind' (KP.emit' (by kpblk)) fun o _ => kp_binTail ihp ihq hp hcp hcq (jok_jmp0 o) region

theorem rkx_five {p q : Nomm} (hp : p.pure = true) (ihp : RKX S Map p) (ihq : RKX S Map q) :
    RKX S Map (Nomm.n5 p q) := by
  intro goal region hg hc
  have hcp : sixCount p ≤ 255 := by simp only [sixCount] at hc; omega
  have hcq : sixCount q ≤ 255 := by simp only [sixCount] at hc; omega
  rw [runL_n5_toL]
  refine KP.bind' KP.re' fun rp _ => KP.bind' KP.re' fun rq _ => KP.bind' (P := fun _ => True) ?_ fun o _ =>
    kp_binTail ihp ihq hp hcp hcq (jok_jmp0 o) region
  cases goal with
  | pick z o =>
    obtain ⟨hz, ho⟩ := hg
    exact KP.emit' (by kpblk)
  | done =>
    unfold n5Pre
    refine KP.bind' kp_doneBlocks fun x _ => ?_
    obtain ⟨o0, o1⟩ := x
    exact KP.emit' (by kpblk)
  | next laz th =>
    unfold n5Pre
    refine KP.bind' (kp_collapseLazyAtom (nex := ⟨laz, th⟩) hg) fun a _ => ?_
    split
    · exact KP.ite' _ (KP.emit' (by kpblk)) KP.fail
    · refine KP.bind' (kp_forl _ _) fun x _ => ?_
      obtain ⟨z, o'⟩ := x
      exact KP.emit' (by kpblk)

theorem rkx_ten {a : Nat} {v q : Nomm} (hv : v.pure = true) (hq : q.pure = true) (ihv : RKX S Map v)
    (ihq : RKX S Map q) : RKX S Map (Nomm.n10 a v q) := by
  intro goal region hg hc
  have hcv : sixCount v ≤ 255 := by simp only [sixCount] at hc; omega
  have hcq : sixCount q ≤ 255 := by simp only [sixCount] at hc; omega
  rw [runL_n10_body]
  refine KP.bind' (kp_simpleNextL_toL (gjk_of_gjx hg)) fun x hx => ?_
  obtain ⟨n, hn, rfl⟩ := hx
  unfold n10Body
  refine KP.bind' (kp_intoL_mk (laz := n.laz) hn a) fun x hx => ?_
  obtain ⟨y, -, rfl⟩ := hx
  obtain ⟨d, r, o⟩ := y
  refine KP.bind' (kp_pastLP _ _ hv _) fun nexR e => ?_
  subst e
  exact kp_binTail ihq ihv hq hcq hcv (jok_jmp0 o) region

/-! ## `%6` -/

theorem rkx_sixP {c a b : Nomm} (hcp : c.pure = true) (ihc : RKX S Map c) (iha : RKX S Map a)
    (ihb : RKX S Map b) (ka : KeepX S Map a) (kb : KeepX S Map b) {goal : CGoal S}
    (hg' : NotNext goal) (hg : GJX goal) {region : List Nat} (hc : sixCount c + sixCount a + sixCount b + 1 ≤ 255) :
    KP (fun n : NextL S => JOK n.th) (runL (Nomm.n6 c a b) (CGoal.toL goal) region : CM Map (NextL S)) := by
  constructor
  intro g0 nex g4 hI h
  rw [runL_n6_body _ _ _ hg'] at h
  obtain ⟨x1, x0, xc, g1, g2, g3, hb1, hb2, _, _, h3, hrest⟩ := sixBody_apart hcp h
  obtain ⟨I1, j1⟩ := (ihb goal region hg (by omega)).k _ _ _ hI hb1
  have Rb := kb hI.2 (goalIn_gjx hg' hg _) (by omega) hb1
  obtain ⟨I2, j0⟩ := (iha goal region hg (by omega)).k _ _ _ I1 hb2
  have Ra := ka I1.2 (goalIn_gjx hg' hg _) (by omega) hb2
  obtain ⟨I3, jc⟩ := (ihc (CGoal.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1))) region ⟨rfl, rfl⟩ (by omega)).k _ _ _
    (inv_sixGenL I2 j0 j1 region) h3
  have hbig : lazyBig (mk (Sure.bunt : Sure S) [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))] []) = false := by
    apply lazyBig_entries
    rw [entries_six]; simp only [List.length_append, List.length_cons]
    have := Ra.size; have := Rb.size; simp only [lazyMax]; omega
  exact (kp_copyL jc _).k _ _ _ I3 (hrest hbig)

theorem rkx_sixN {c a b : Nomm} (hcp : c.pure = true) (ihc : RKX S Map c) (iha : RKX S Map a)
    (ihb : RKX S Map b) (ka : KeepX S Map a) (kb : KeepX S Map b) {sur : Sure S} {th : Jmp} (hth : JOK th)
    {region : List Nat} (hc : sixCount c + sixCount a + sixCount b + 1 ≤ 255) :
    KP (fun n : NextL S => JOK n.th) (runL (Nomm.n6 c a b) (CGoal.toL (CGoal.next sur th)) region :
      CM Map (NextL S)) := by
  constructor
  intro g0 nex g9 hI h
  simp only [CGoal.toL] at h
  rw [runL_n6_next, sixNextL_ofSure] at h
  obtain ⟨s0, s1, x1, x0, xc, lz, yes, nuh, gF, gR, gQ, gS, gC, hFk, hR, hQ, hS, hC, hrest⟩ :=
    sixNextSimple_apart hcp h
  obtain ⟨_, _, _, _, d0, d1, j01, hreg, hle, hbo, hdrop, hcond, _, hb0, hb1, hb2, hold⟩ := forkSure_spec hFk hI.2
  obtain ⟨IF, -⟩ := (kp_forkSure _ _ _ _).k _ _ _ (show Inv ({ g0 with bo := g0.bo + 1 + 1 } : Comp.Gen Map) from hI) hFk
  have gb : GoalIn ({ gF with id := gF.id + 1 } : Comp.Gen Map).re (CGoal.next s1 (jmp0 (g0.bo + 1))) :=
    ⟨fun x hx => (hreg x (Or.inr hx)).2, jmpIn_jmp0 _ _⟩
  obtain ⟨IR, jR⟩ := (ihb (CGoal.next s1 (jmp0 (g0.bo + 1))) (gF.id :: region) (jok_jmp0 _) (by omega)).k
    { gF with id := gF.id + 1 } _ _ IF hR
  have Rb := kb (goal := CGoal.next s1 (jmp0 (g0.bo + 1))) (g0 := { gF with id := gF.id + 1 }) IF.2 gb
    (by omega) hR
  have lR : gF.re ≤ gR.re := Rb.keeps.le
  have ga' : GoalIn gR.re (CGoal.next s0 (jmp0 g0.bo)) :=
    ⟨fun x hx => Nat.lt_of_lt_of_le (hreg x (Or.inl hx)).2 lR, jmpIn_jmp0 _ _⟩
  obtain ⟨IQ, jQ⟩ := (iha (CGoal.next s0 (jmp0 g0.bo)) (gF.id :: region) (jok_jmp0 _) (by omega)).k _ _ _ IR hQ
  have Ra := ka (goal := CGoal.next s0 (jmp0 g0.bo)) IR.2 ga' (by omega) hQ
  have cR : gR.cond = gF.cond := Rb.cnd
  rw [cR] at hS
  obtain ⟨ey, en, _, _, el, hsb⟩ := sect_spec IQ.2 (Ra.cnd.trans cR) hS
  have IS : Inv gS := inv_same hsb (inv_sixGenL IQ jQ jR _)
  subst ey en el
  obtain ⟨IC, jC⟩ := (ihc (CGoal.pick (jmp0 gQ.bo) (jmp0 (gQ.bo + 1))) region ⟨rfl, rfl⟩ (by omega)).k _ _ _ IS hC
  have hbig : lazyBig (mk (Sure.bunt : Sure S) [((gQ.bo, x0.laz), (gQ.bo + 1, x1.laz))] []) = false := by
    apply lazyBig_entries
    rw [entries_six]; simp only [List.length_append, List.length_cons]
    have := Ra.size; have := Rb.size; simp only [lazyMax]; omega
  exact (kp_copyL jC _).k _ _ _ IC (hrest hbig)

/-! ## The induction -/

/-- **On `FragX`, every run of `runL` for a fork-free goal whose jumps pass
no `~` keeps `BlocksOK` and returns a jump that passes no `~`.** -/
theorem runX_kp {nm : Nomm} (hf : FragX (S := S) nm) : RKX S Map nm := by
  induction hf with
  | frag hf => exact rkx_frag hf
  | @six c a b hc ha hb ihc iha ihb =>
    intro goal region hg hcount
    have hc'' : sixCount c + sixCount a + sixCount b + 1 ≤ 255 := by simpa only [sixCount] using hcount
    cases goal with
    | next sur th =>
      exact rkx_sixN (fragX_pure hc) ihc iha ihb (runX_keeps ha) (runX_keeps hb) hg hc''
    | done =>
      exact rkx_sixP (goal := CGoal.done) (fragX_pure hc) ihc iha ihb (runX_keeps ha) (runX_keeps hb) trivial
        hg hc''
    | pick z o =>
      exact rkx_sixP (goal := CGoal.pick z o) (fragX_pure hc) ihc iha ihb (runX_keeps ha) (runX_keeps hb)
        trivial hg hc''
  | four hp ih => exact rkx_four ih
  | three hp ih => exact rkx_three ih
  | seven hq hp ih => exact rkx_seven hq ih
  | cons hp hq ihp ihq => exact rkx_cons (fragX_pure hp) (fragX_pure hq) ihp ihq
  | five hp hq ihp ihq => exact rkx_five (fragX_pure hp) ihp ihq
  | ten hv hq ihv ihq => exact rkx_ten (fragX_pure hv) (fragX_pure hq) ihv ihq
  | sevenFrom ha _ ihq => exact rkx_sevenFrom ha ihq

/-- **The raw blocks of the top run of `FragX`**: from the empty state for
`%done`, `BlocksOK` and a result jump with no `~`. -/
theorem runX_blocksOK {nm : Nomm} (hf : FragX (S := S) nm) (hc : sixCount nm ≤ 255) {nex : NextL S}
    {g1 : Comp.Gen Map} (h : runL nm (CGoalL.done : CGoalL S) [] gen0 = some (nex, g1)) :
    Inv g1 ∧ JOK nex.th :=
  (runX_kp hf CGoal.done [] trivial hc).k gen0 nex g1
    ⟨fun k b hb => by simp [gen0, HoonMap.get_empty] at hb, by simp [gen0]⟩ h

end Glue
end SkaModel
end Formalization
