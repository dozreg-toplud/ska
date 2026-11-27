import lemmas.Ska.RawInvAT

/-!
# Raw `+comp` output on `FragX`: `ArityOK` and `TwoNA` of the run

README Gaps 14, track D.  The run-level induction over `FragX` for `RunAT`
(`RawInvStX.lean`), in the shape of `runX_eap`: from a state whose goal
jumps are `Fresh` (no arguments, a target with no parameter), a run of
`runL` is a `GA` (`RawInvAT.lean`) and its result jump is `Fresh`
(`ATR`).  The first fragment by `run_at` (and `run_down` of track C for the
result), the unary cases by the helpers of `RawInvAT.lean` on the sure
needs (`collapseLazyAtomL_mk`), the binary ones with `copyL_apart_some`
(the entries of the two results lie apart, `KeepR.labs` of track C).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **What a run on `FragX` gives**: a `GA`, and a `Fresh` result jump in
`[1, g1.bo)`. -/
structure ATR (g0 g1 : Comp.Gen Map) (nex : NextL S) : Prop where
  ga : GA g0 g1
  lo : 1 ≤ nex.th.there
  hi : nex.th.there < g1.bo
  fresh : Fresh g1 nex.th

/-- **What the induction proves of one nomm of `FragX`.** -/
abbrev ATX (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (nm : Nomm) : Prop :=
  ∀ {goal : CGoal S} {region : List Nat} {g0 g1 : Comp.Gen Map} {nex : NextL S},
    g0.drop = false → 1 ≤ g0.bo → GJ g0.bo goal → GFresh g0 goal → GoalIn g0.re goal → sixCount nm ≤ 255 →
    runL nm (CGoal.toL goal) region g0 = some (nex, g1) → ATR g0 g1 nex

theorem ga_re {g g' : Comp.Gen Map} {r : Nat} (h : (re : CM Map Nat) g = some (r, g')) : GA g g' := by
  rw [re_apply] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ga_quiet (quiet_re g)

theorem atx_frag {nm : Nomm} (hf : ∀ goal : CGoal S, Frag nm goal) : ATX S Map nm := by
  intro goal region g0 g1 nex hd h1 hj hF hg _ h
  rw [runL_frag (hf goal)] at h
  obtain ⟨⟨n, g⟩, hr, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have D := run_down nm goal g0 g n hj h1 hd hr
  have A := run_at nm goal g0 g n hj h1 hd hF hr
  exact ⟨A, D.lo, D.hi, entry_fresh D.entry hF hj A⟩

theorem atx_seven {p q : Nomm} (hq : ∀ goal : CGoal S, Frag q goal) (ihp : ATX S Map p) :
    ATX S Map (Nomm.n7 p q) := by
  intro goal region g0 g1 nex hd h1 hj hF hg hc h
  rw [runL_n7] at h
  obtain ⟨nx, g, h2, h3⟩ := bind_some h
  rw [runL_frag (hq goal)] at h2
  obtain ⟨⟨n, g'⟩, hr, e⟩ := Option.map_eq_some_iff.mp h2
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨k1, n1⟩ := run_keeps q goal g0 g' n hd hg hr
  have D := run_down q goal g0 g' n hj h1 hd hr
  have A := run_at q goal g0 g' n hj h1 hd hF hr
  have P := ihp (goal := CGoal.next n.laz n.th) (A.drop.trans hd) (Nat.le_trans h1 A.bo) ⟨D.lo, D.hi⟩
    (entry_fresh D.entry hF hj A) n1 (by simp only [sixCount] at hc; omega) h3
  exact ⟨A.trans P.ga, P.lo, P.hi, P.fresh⟩

theorem atx_sevenFrom {axe : Nat} {q : Nomm} (ha : 2 ≤ axe) (ihq : ATX S Map q) :
    ATX S Map (Nomm.n7 (Nomm.n0 axe) q) := by
  intro goal region g0 g1 nex hd h1 hj hF hg hc h
  obtain ⟨nx, laz', h2, hl, rfl⟩ := runL_seven_from ha h
  have Q := ihq hd h1 hj hF hg (by simp only [sixCount] at hc; omega) h2
  exact ⟨Q.ga, Q.lo, Q.hi, Q.fresh⟩

/-- A run for the goal of a block just emitted. -/
theorem atx_tail {p : Nomm} (ih : ATX S Map p) {b : Blob} {arg : Nat} {region : List Nat}
    {g0 g g1 g2 : Comp.Gen Map} {o : Nat} {nex : NextL S} (h0 : GA g0 g) (hd : g0.drop = false)
    (h1 : 1 ≤ g0.bo) (hb : ∀ j ∈ finJumps b.fin, Fresh g j ∧ j.there < g.bo) (hp : b.par = [])
    (ha : arg < g.re) (hc : sixCount p ≤ 255) (he : (emit b : CM Map Nat) g = some (o, g1))
    (h : runL p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region g1 = some (nex, g2)) : ATR g0 g2 nex := by
  rw [emit_apply] at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hd' : g.drop = false := h0.drop.trans hd
  have hb1 : 1 ≤ g.bo := Nat.le_trans h1 h0.bo
  have R := ih (goal := CGoal.next (lazyReg arg) (jmp0 g.bo)) ((emitted_drop g b).trans hd')
    (by simp only [emitted_bo]; omega) ⟨hb1, by simp [jmp0, emitted_bo]⟩ (fresh_emitted hd' hp rfl)
    ⟨nb_this (by simp only [emitted_re]; omega), jmpIn_jmp0 _ _⟩ hc h
  exact ⟨h0.trans ((ga_emitF hd' hb).trans R.ga), R.lo, R.hi, R.fresh⟩

theorem jumps_two {g g' : Comp.Gen Map} {fin : Termin} {z o : Jmp} (hf : finJumps fin = [z, o]) (hz : Fresh g z)
    (ho : Fresh g o) (hzl : z.there < g.bo) (hol : o.there < g.bo) (a : GA g g') :
    ∀ j' ∈ finJumps fin, Fresh g' j' ∧ j'.there < g'.bo :=
  fresh_two hf (fresh_ga hz hzl a) (fresh_ga ho hol a) (Nat.lt_of_lt_of_le hzl a.bo) (Nat.lt_of_lt_of_le hol a.bo)

theorem atx_four {p : Nomm} (ih : ATX S Map p) : ATX S Map (Nomm.n4 p) := by
  intro goal region g0 g1 nex hd h1 hj hF hg hc h
  have hcp : sixCount p ≤ 255 := by simpa only [sixCount] using hc
  cases goal with
  | done =>
    simp only [CGoal.toL] at h
    unfold runL at h
    obtain ⟨pro, ga, h2, h⟩ := bind_some h
    obtain ⟨e1, q1, k1⟩ := keeps_re h2
    obtain ⟨arg, gb, h3, h⟩ := bind_some h
    obtain ⟨e2, q2, k2⟩ := keeps_re h3
    obtain ⟨o, gc, h4, h⟩ := bind_some h
    exact atx_tail ih ((ga_re h2).trans (ga_re h3)) hd h1 (nil_jumps rfl) rfl (show arg < gb.re by omega) hcp h4 h
  | pick z o =>
    simp only [CGoal.toL] at h
    unfold runL at h
    obtain ⟨pro, ga, h2, h⟩ := bind_some h
    obtain ⟨e1, q1, k1⟩ := keeps_re h2
    obtain ⟨arg, gb, h3, h⟩ := bind_some h
    obtain ⟨e2, q2, k2⟩ := keeps_re h3
    obtain ⟨o', gc, h4, h⟩ := bind_some h
    have A := (ga_re h2).trans (ga_re h3)
    exact atx_tail ih A hd h1 (jumps_two rfl hF.1 hF.2 hj.1.2 hj.2.2 A) rfl (show arg < gb.re by omega) hcp h4 h
  | next sur th =>
    simp only [CGoal.toL] at h
    unfold runL at h
    obtain ⟨a, ga, h2, h⟩ := bind_some h
    rw [collapseLazyAtomL_mk] at h2
    obtain ⟨k1, r1⟩ := keeps_collapseLazyAtom (nex := ⟨sur, th⟩) hd hg.1 h2
    have C := ga_collapse (nex := ⟨sur, th⟩) h2 hF hj.2 hd
    obtain ⟨⟨pro, th'⟩, gb, h3, h⟩ := bind_some h
    have T : GA ga gb ∧ Fresh gb (jmp0 th') ∧ th' < gb.bo ∧ pro < gb.re := by
      cases a with
      | some x =>
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
        obtain ⟨rfl, rfl⟩ := h3
        exact ⟨GA.refl _, (C.2 _ _ rfl).1, (C.2 _ _ rfl).2, r1 _ _ rfl⟩
      | none =>
        simp only at h3
        obtain ⟨r, g3, h4, h3⟩ := bind_some h3
        obtain ⟨e3, q3, k3⟩ := keeps_re h4
        by_cases ht : th.args = []
        · rw [if_pos ht] at h3
          simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h3
          have A3 := ga_re h4
          have l1 : th.there < ga.bo := Nat.lt_of_lt_of_le hj.2 C.1.bo
          exact ⟨A3, fresh_ga (fresh_ga (fresh_jmp0 hF) hj.2 C.1) l1 A3, Nat.lt_of_lt_of_le l1 A3.bo,
            by omega⟩
        · rw [if_neg ht] at h3; cases h3
    obtain ⟨arg, gc, h4, h⟩ := bind_some h
    obtain ⟨e3, q3, k3⟩ := keeps_re h4
    obtain ⟨o, gd, h5, h⟩ := bind_some h
    have A4 := ga_re h4
    exact atx_tail ih (C.1.trans (T.1.trans A4)) hd h1
      (fresh_one (fresh_ga T.2.1 T.2.2.1 A4) (Nat.lt_of_lt_of_le T.2.2.1 A4.bo)) rfl
      (show arg < gc.re by omega) hcp h5 h

theorem atx_three {p : Nomm} (ih : ATX S Map p) : ATX S Map (Nomm.n3 p) := by
  intro goal region g0 g1 nex hd h1 hj hF hg hc h
  have hcp : sixCount p ≤ 255 := by simpa only [sixCount] using hc
  cases goal with
  | done =>
    simp only [CGoal.toL] at h
    unfold runL at h
    obtain ⟨⟨o0, o1⟩, ga, h2, h⟩ := bind_some h
    have B := ga_doneBlocks h2 hd
    obtain ⟨r, gb, h3, h⟩ := bind_some h
    obtain ⟨e2, q2, k2⟩ := keeps_re h3
    obtain ⟨oc, gc, h4, h⟩ := bind_some h
    have A3 := ga_re h3
    exact atx_tail ih (B.1.trans A3) hd h1 (jumps_two rfl B.2.1 B.2.2.1 B.2.2.2.1 B.2.2.2.2 A3) rfl
      (show r < gb.re by omega) hcp h4 h
  | pick z o =>
    simp only [CGoal.toL] at h
    unfold runL at h
    obtain ⟨r, gb, h3, h⟩ := bind_some h
    obtain ⟨e2, q2, k2⟩ := keeps_re h3
    obtain ⟨oc, gc, h4, h⟩ := bind_some h
    have A3 := ga_re h3
    exact atx_tail ih A3 hd h1 (jumps_two rfl hF.1 hF.2 hj.1.2 hj.2.2 A3) rfl (show r < gb.re by omega) hcp h4 h
  | next sur th =>
    simp only [CGoal.toL] at h
    unfold runL at h
    dsimp only at h
    revert h; split
    · exact fun h => ih (goal := CGoal.next sur th) hd h1 hj hF hg hcp h
    intro h
    obtain ⟨a, ga, h2, h⟩ := bind_some h
    rw [collapseLazyAtomL_mk] at h2
    have C := ga_collapse (nex := ⟨sur, th⟩) h2 hF hj.2 hd
    rcases a with _ | ⟨r, o⟩
    · cases h
    simp only at h
    obtain ⟨⟨z, o'⟩, gb, h3, h⟩ := bind_some h
    have Co := C.2 r o rfl
    have F := ga_forl h3 Co.1 Co.2 (C.1.drop.trans hd)
    obtain ⟨r', gc, h4, h⟩ := bind_some h
    obtain ⟨e3, q3, k3⟩ := keeps_re h4
    obtain ⟨oc, gd, h5, h⟩ := bind_some h
    have A4 := ga_re h4
    exact atx_tail ih (C.1.trans (F.1.trans A4)) hd h1 (jumps_two rfl F.2.1 F.2.2.1 F.2.2.2.1 F.2.2.2.2 A4) rfl
      (show r' < gc.re by omega) hcp h5 h

/-! ## The binary cases -/

/-- **Two runs and the `+copy`.** -/
theorem atx_binary {p q : Nomm} (ihp : ATX S Map p) (ihq : ATX S Map q) (kp : KeepX S Map p)
    (kq : KeepX S Map q) {region : List Nat} {g0 g1 g2 g3 : Comp.Gen Map} {nq np : Sure S} {th : Jmp}
    {nex2 nex1 nex : NextL S} (hd : g0.drop = false) (hl : 1 ≤ th.there) (hh : th.there < g0.bo)
    (hf : Fresh g0 th) (hc : sixCount p + sixCount q ≤ 255) (hnq : NB g0.re nq.ned) (hnp : NB g0.re np.ned)
    (hj : JmpIn (· < g0.re) th)
    (h2 : runL q (CGoalL.next (ofSure nq) th) region g0 = some (nex2, g1))
    (h3 : runL p (CGoalL.next (ofSure np) nex2.th) region g1 = some (nex1, g2))
    (h4 : copyL nex1 nex2.laz g2 = some (nex, g3)) : ATR g0 g3 nex := by
  have Q := ihq (goal := CGoal.next nq th) hd (by omega) ⟨hl, hh⟩ hf ⟨hnq, hj⟩ (by omega) h2
  have Rq := kq (goal := CGoal.next nq th) hd ⟨hnq, hj⟩ (by omega) h2
  have d1 : g1.drop = false := Q.ga.drop.trans hd
  have gp : GoalIn g1.re (CGoal.next np nex2.th) := ⟨hnp.mono Rq.keeps.le, Rq.out.2⟩
  have P := ihp (goal := CGoal.next np nex2.th) d1 (by have := Q.lo; have := Q.hi; omega) ⟨Q.lo, Q.hi⟩
    Q.fresh gp (by omega) h3
  have Rp := kp (goal := CGoal.next np nex2.th) d1 gp (by omega) h3
  have l1 := Rq.keeps.le
  obtain ⟨n, hcp, rfl⟩ := copyL_apart_some
    (fun e he e' he' => by
      have a := (Rp.labs _ (fork_in_entries he)).1
      have b := (Rq.labs _ (fork_in_entries he')).2
      omega)
    (fun e he e' he' => by
      have a := (Rp.labs _ (bond_in_entries he)).1
      have b := (Rq.labs _ (bond_in_entries he')).2
      omega) h4
  have d2 : g2.drop = false := P.ga.drop.trans d1
  have C := ga_copy hcp P.fresh P.hi d2
  have D := copy_down (goal := (CGoal.done : CGoal S)) hcp P.lo P.hi d2 (by have := P.lo; have := P.hi; omega)
  exact ⟨Q.ga.trans (P.ga.trans C), D.lo, D.hi, D.entry.elim id fun e => e.elim⟩

theorem atx_consBody {p q : Nomm} (ihp : ATX S Map p) (ihq : ATX S Map q) (kp : KeepX S Map p)
    (kq : KeepX S Map q) (hpp : p.pure = true) (hqp : q.pure = true)
    {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Comp.Gen Map} {nex : NextL S} (hd : g0.drop = false)
    (hl : 1 ≤ th.there) (hh : th.there < g0.bo) (hf : Fresh g0 th)
    (hg : GoalIn g0.re (CGoal.next sur th)) (hc : sixCount p + sixCount q ≤ 255)
    (h : (do
      let (hed, tel, o) ← splitL ⟨ofSure sur, th⟩
      let nexh ← pastL noCode ⟨hed, jmp0 o⟩ q region
      let nex2 ← runL q (CGoalL.next tel nexh.th) region
      let nex2 ← pastL noCode nex2 p region
      let nex1 ← runL p (CGoalL.next nexh.laz nex2.th) region
      copyL nex1 nex2.laz : CM Map (NextL S)) g0 = some (nex, g1)) : ATR g0 g1 nex := by
  obtain ⟨⟨hed', tel', o⟩, g2x, h2, h⟩ := bind_some h
  rw [splitL_mk, map_apply] at h2
  obtain ⟨⟨⟨hed, tel, o'⟩, g2⟩, hs2, e2⟩ := Option.map_eq_some_iff.mp h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e2
  obtain ⟨k2, nh, nt⟩ := keeps_split hd hg.1 hg.2 hs2
  obtain ⟨G2, eo, lt2, F2⟩ := split_down hs2 hl hh hd
  have A2 := ga_split hs2 hf hh hd
  simp only at nh nt eo F2
  obtain ⟨nexh, g2', hph, h⟩ := bind_some h
  rw [pastL_mk _ _ _ hqp, pure_apply] at hph
  simp only [Option.some.injEq, Prod.mk.injEq] at hph
  obtain ⟨rfl, rfl⟩ := hph
  obtain ⟨nex2, g3, h3, h⟩ := bind_some h
  obtain ⟨nex2', g3', hp2, h⟩ := bind_some h
  rw [pastL_pure _ _ hpp, pure_apply] at hp2
  simp only [Option.some.injEq, Prod.mk.injEq] at hp2
  obtain ⟨rfl, rfl⟩ := hp2
  obtain ⟨nex1, g4, h4, hcp⟩ := bind_some h
  have R := atx_binary ihp ihq kp kq (G2.drop.trans hd) (th := jmp0 o') (by simp only [jmp0]; omega)
    (by simp only [jmp0]; omega) F2 hc nt nh (jmpIn_jmp0 _ _) h3 h4 hcp
  exact ⟨A2.trans R.ga, R.lo, R.hi, R.fresh⟩

theorem atx_cons {p q : Nomm} (ihp : ATX S Map p) (ihq : ATX S Map q) (kp : KeepX S Map p)
    (kq : KeepX S Map q) (hpp : p.pure = true) (hqp : q.pure = true) : ATX S Map (Nomm.cons p q) := by
  intro goal region g0 g1 nex hd h1 hj hF hg hc h
  have hc' : sixCount p + sixCount q ≤ 255 := by simpa only [sixCount] using hc
  cases goal with
  | next sur th =>
    simp only [CGoal.toL] at h
    rw [runL_cons_next] at h
    exact atx_consBody ihp ihq kp kq hpp hqp hd hj.1 hj.2 hF hg hc' h
  | done =>
    simp only [CGoal.toL] at h
    rw [runL_cons_done] at h
    obtain ⟨r, ga, h2, h⟩ := bind_some h
    obtain ⟨e1, q1, k1⟩ := keeps_re h2
    obtain ⟨o, gb, h3, h⟩ := bind_some h
    rw [emit_apply] at h3
    simp only [Option.some.injEq, Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    have A2 := ga_re h2
    have da : ga.drop = false := A2.drop.trans hd
    rw [runL_cons_next] at h
    have R := atx_consBody (sur := lazyReg r) ihp ihq kp kq hpp hqp ((emitted_drop _ _).trans da)
      (th := jmp0 ga.bo) (by simp only [jmp0]; have := A2.bo; omega) (by simp [jmp0, emitted_bo])
      (fresh_emitted da rfl rfl) ⟨nb_this (by simp only [emitted_re]; omega), jmpIn_jmp0 _ _⟩ hc' h
    exact ⟨A2.trans ((ga_emitN da rfl).trans R.ga), R.lo, R.hi, R.fresh⟩
  | pick z o =>
    simp only [CGoal.toL] at h
    rw [runL_cons_pick] at h
    obtain ⟨o', ga, h2, h⟩ := bind_some h
    rw [emit_apply] at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    obtain ⟨nex2, gb, h3, h⟩ := bind_some h
    obtain ⟨nex2', gb', hp2, h⟩ := bind_some h
    rw [pastL_pure _ _ hpp, pure_apply] at hp2
    simp only [Option.some.injEq, Prod.mk.injEq] at hp2
    obtain ⟨rfl, rfl⟩ := hp2
    obtain ⟨nex1, gc, h4, h⟩ := bind_some h
    have R := atx_binary (nq := Sure.bunt) (np := Sure.bunt) ihp ihq kp kq ((emitted_drop _ _).trans hd)
      (th := jmp0 g0.bo) h1 (by simp [jmp0, emitted_bo]) (fresh_emitted hd rfl rfl) hc' (nb_none _) (nb_none _)
      (jmpIn_jmp0 _ _) h3 h4 h
    exact ⟨(ga_emitN hd rfl).trans R.ga, R.lo, R.hi, R.fresh⟩

/-- The block of `[5 p q]` that compares `rp` and `rq`. -/
theorem ga_n5Pre {rp rq : Nat} {goal : CGoal S} {g g' : Comp.Gen Map} {o : Nat}
    (h : n5Pre rp rq goal g = some (o, g')) (hj : GJ g.bo goal) (hf : GFresh g goal) (hd : g.drop = false)
    (h1 : 1 ≤ g.bo) : GA g g' ∧ Fresh g' (jmp0 o) ∧ 1 ≤ o ∧ o < g'.bo := by
  cases goal with
  | pick z o' =>
    simp only [n5Pre, emit_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ga_emitF hd (fresh_two rfl hf.1 hf.2 hj.1.2 hj.2.2), fresh_emitted hd rfl rfl, h1,
      by simp [emitted_bo]⟩
  | done =>
    simp only [n5Pre] at h
    obtain ⟨⟨o0, o1⟩, g3, h3, h2⟩ := bind_some h
    have B := ga_doneBlocks h3 hd
    rw [emit_apply] at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    have hd3 : g3.drop = false := B.1.drop.trans hd
    exact ⟨B.1.trans (ga_emitF hd3 (fresh_two rfl B.2.1 B.2.2.1 B.2.2.2.1 B.2.2.2.2)),
      fresh_emitted hd3 rfl rfl, Nat.le_trans h1 B.1.bo, by simp [emitted_bo]⟩
  | next laz th =>
    simp only [n5Pre] at h
    obtain ⟨a, g3, h3, h2⟩ := bind_some h
    have C := ga_collapse (nex := ⟨laz, th⟩) h3 hf hj.2 hd
    have hd3 : g3.drop = false := C.1.drop.trans hd
    cases a with
    | none =>
      simp only at h2
      by_cases ea : th.args = []
      · rw [if_pos ea, emit_apply] at h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        exact ⟨C.1.trans (ga_emitF hd3 (fresh_one (fresh_ga (fresh_jmp0 hf) hj.2 C.1)
          (Nat.lt_of_lt_of_le hj.2 C.1.bo))), fresh_emitted hd3 rfl rfl, Nat.le_trans h1 C.1.bo,
          by simp [emitted_bo]⟩
      · rw [if_neg ea] at h2; cases h2
    | some x =>
      obtain ⟨r, o''⟩ := x
      have Co := C.2 r o'' rfl
      simp only at h2
      obtain ⟨⟨z, o'⟩, g4, h4, h2⟩ := bind_some h2
      have F := ga_forl h4 Co.1 Co.2 hd3
      rw [emit_apply] at h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      have hd4 : g4.drop = false := F.1.drop.trans hd3
      exact ⟨C.1.trans (F.1.trans (ga_emitF hd4 (fresh_two rfl F.2.1 F.2.2.1 F.2.2.2.1 F.2.2.2.2))),
        fresh_emitted hd4 rfl rfl, Nat.le_trans h1 (Nat.le_trans C.1.bo F.1.bo), by simp [emitted_bo]⟩

theorem atx_five {p q : Nomm} (ihp : ATX S Map p) (ihq : ATX S Map q) (kp : KeepX S Map p)
    (kq : KeepX S Map q) (hpp : p.pure = true) : ATX S Map (Nomm.n5 p q) := by
  intro goal region g0 g1 nex hd h1 hj hF hg hc h
  have hc' : sixCount p + sixCount q ≤ 255 := by simpa only [sixCount] using hc
  rw [runL_n5_toL] at h
  obtain ⟨rp, ga, h2, h⟩ := bind_some h
  obtain ⟨e1, q1, k1⟩ := keeps_re h2
  obtain ⟨rq, gb, h3, h⟩ := bind_some h
  obtain ⟨e2, q2, k2⟩ := keeps_re h3
  obtain ⟨o, gc, h4, h⟩ := bind_some h
  have A0 := (ga_re h2).trans (ga_re h3)
  have k3 := keeps_n5Pre ((k1.trans k2).dropF hd) (hg.mono (by omega)) (by omega) (by omega) h4
  have O := ga_n5Pre h4 (hj.mono A0.bo) (by
      cases goal with
      | next laz th => exact fresh_ga hF hj.2 A0
      | pick z o' => exact ⟨fresh_ga hF.1 hj.1.2 A0, fresh_ga hF.2 hj.2.2 A0⟩
      | done => trivial) (A0.drop.trans hd) (Nat.le_trans h1 A0.bo)
  obtain ⟨nexq, gd, h5, h⟩ := bind_some h
  obtain ⟨nexq', gd', hp2, h⟩ := bind_some h
  rw [pastL_pure _ _ hpp, pure_apply] at hp2
  simp only [Option.some.injEq, Prod.mk.injEq] at hp2
  obtain ⟨rfl, rfl⟩ := hp2
  obtain ⟨nexp, ge, h6, h⟩ := bind_some h
  have l3 := k3.le
  have R := atx_binary (nq := lazyReg rq) (np := lazyReg rp) ihp ihq kp kq (O.1.drop.trans (A0.drop.trans hd))
    (th := jmp0 o) O.2.2.1 O.2.2.2 O.2.1 hc' (nb_this (by omega)) (nb_this (by omega)) (jmpIn_jmp0 _ _) h5 h6 h
  exact ⟨A0.trans (O.1.trans R.ga), R.lo, R.hi, R.fresh⟩

theorem atx_ten {a : Nat} {v q : Nomm} (ihv : ATX S Map v) (ihq : ATX S Map q) (kv : KeepX S Map v)
    (kq : KeepX S Map q) (hvp : v.pure = true) (hqp : q.pure = true) : ATX S Map (Nomm.n10 a v q) := by
  intro goal region g0 g1 nex hd h1 hj hF hg hc h
  have hc' : sixCount q + sixCount v ≤ 255 := by simp only [sixCount] at hc; omega
  rw [runL_n10_body] at h
  obtain ⟨next, gs, hs, h⟩ := bind_some h
  rw [simpleNextL_toL, map_apply] at hs
  obtain ⟨⟨n, gs'⟩, hs', e⟩ := Option.map_eq_some_iff.mp hs
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨k1, n1⟩ := keeps_simpleNext hd hg hs'
  have D0 := simpleNext_down hs' hj hd h1
  have A0 := ga_simpleNext hs' hj hF hd
  have F0 : Fresh gs' n.th := entry_fresh D0.entry hF hj A0
  unfold n10Body at h
  obtain ⟨⟨don', rec', o⟩, g2x, h2, h⟩ := bind_some h
  rw [show (Next.toL n : NextL S) = ⟨ofSure n.laz, n.th⟩ from rfl, intoL_mk, map_apply] at h2
  obtain ⟨⟨⟨don, rec, o'⟩, g2⟩, hs2, e2⟩ := Option.map_eq_some_iff.mp h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e2
  obtain ⟨k2, nd, nr⟩ := keeps_into (k1.dropF hd) n1 hs2
  have hd2 : gs'.drop = false := A0.drop.trans hd
  obtain ⟨G3, eo, lt3, F3⟩ := into_down hs2 D0.lo D0.hi hd2
  have A3 := ga_into hs2 F0 D0.hi hd2
  simp only at eo F3 nd nr
  obtain ⟨nexR, g2', hpr, h⟩ := bind_some h
  rw [pastL_mk _ _ _ hvp, pure_apply] at hpr
  simp only [Option.some.injEq, Prod.mk.injEq] at hpr
  obtain ⟨rfl, rfl⟩ := hpr
  obtain ⟨nexDon, g3, h3, h⟩ := bind_some h
  obtain ⟨nexDon', g3', hpd, h⟩ := bind_some h
  rw [pastL_pure _ _ hqp, pure_apply] at hpd
  simp only [Option.some.injEq, Prod.mk.injEq] at hpd
  obtain ⟨rfl, rfl⟩ := hpd
  obtain ⟨nexRec, g4, h4, hcp⟩ := bind_some h
  have lo := D0.lo
  have hi := D0.hi
  have R := atx_binary ihq ihv kq kv (G3.drop.trans hd2) (th := jmp0 o') (by simp only [jmp0]; omega)
    (by simp only [jmp0]; omega) F3 hc' nd nr (jmpIn_jmp0 _ _) h3 h4 hcp
  exact ⟨A0.trans (A3.trans R.ga), R.lo, R.hi, R.fresh⟩

end Raw
end SkaModel
end Formalization
