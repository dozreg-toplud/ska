import lemmas.Ska.CompFootTen
import lemmas.Ska.CompBelowX

/-!
# Fact (i) over `FragX`, case by case

The write footprint of `CompFootRun.lean` for the runs of `runL` on
`FragX`, with the lazy entries of the result (facts (iii) and (iv) of
`CompUnproxyRegs.lean`): `FootR g0 g1 goal nex` says that the code of the
run writes only registers below its end that it allocated or that its goal
needs, none of the result's sure need and none of its entries' needs
(`wr`); the sure need and each entry's need lie in those registers (`sure`,
`esure`), are distinct (`dist`, `edist`), and the sure need shares no
register with an entry's need (`apart`).  `FootX nm` is the case of the
induction, in the shape of `KeepX` of `CompBelowX.lean`.

The cases, in the order of `runX_keeps`: `footX_frag` (through `run_foot`),
`footX_four`, `footX_three` (through `footX_tail`), `footX_seven`,
`footX_cons`, `footX_five`, `footX_ten` (through `footX_binary` and
`foot_copy`), `footX_sevenFrom`, `footX_sixP` (`%6` under `%done` and
`%pick`), `footX_sixN` (`%6` under a fork-free `%next`, through
`wroteIn_forkSure` and `wroteIn_sameBlocks`), and so `runX_foot`, every case.
`FootR.pre` puts code in front of a run and widens its goal.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **Fact (i) of one run of `runL`, with the lazy entries of its result.** -/
structure FootR (g g' : Gen Map) (goal : CGoal S) (nex : NextL S) : Prop where
  wr : WroteIn (fun x => x < g'.re ∧ (g.re ≤ x ∨ GMem goal x) ∧ ¬ NMem nex.laz.sure.ned x ∧
    ∀ e ∈ entries nex.laz, ¬ NMem e.2.sure.ned x) g g'
  sure : ∀ x, NMem nex.laz.sure.ned x → g.re ≤ x ∨ GMem goal x
  dist : Distinct nex.laz.sure.ned
  esure : ∀ e ∈ entries nex.laz, ∀ x, NMem e.2.sure.ned x → g.re ≤ x ∨ GMem goal x
  edist : ∀ e ∈ entries nex.laz, Distinct e.2.sure.ned
  apart : ∀ e ∈ entries nex.laz, ∀ x, NMem nex.laz.sure.ned x → ¬ NMem e.2.sure.ned x

/-- What the induction proves of one nomm of `FragX`. -/
abbrev FootX (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (nm : Nomm) : Prop :=
  ∀ {goal : CGoal S} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    g0.drop = false → GoalIn g0.re goal → GDist goal → sixCount nm ≤ 255 →
    runL nm (CGoal.toL goal) region g0 = some (nex, g1) → FootR g0 g1 goal nex

/-- A fork-free result. -/
theorem footR_toL {g g' : Gen Map} {goal : CGoal S} {n : Next S} (F : Foot g g' goal n) :
    FootR g g' goal (Next.toL n) := by
  have ne : ∀ e, e ∉ entries (Next.toL n).laz := fun e he => by simp [Next.toL, entries_ofSure] at he
  exact ⟨F.wr.mono fun x hx => ⟨hx.1, hx.2.1, hx.2.2, fun e he => absurd he (ne e)⟩, F.sure, F.dist,
    fun e he => absurd he (ne e), fun e he => absurd he (ne e), fun e he => absurd he (ne e)⟩

/-- **Code in front of a run, and a wider goal**: the code before writes
registers that the run's goal does not need and that it did not allocate. -/
theorem FootR.pre {g0 g g1 : Gen Map} {goal goal' : CGoal S} {nex : NextL S} (F : FootR g g1 goal nex)
    (W : WroteIn (fun x => x < g1.re ∧ (g0.re ≤ x ∨ GMem goal' x) ∧ ¬ (g.re ≤ x ∨ GMem goal x)) g0 g)
    (a : ∀ x, (g.re ≤ x ∨ GMem goal x) → g0.re ≤ x ∨ GMem goal' x) : FootR g0 g1 goal' nex :=
  ⟨(W.mono fun x hx => ⟨hx.1, hx.2.1, fun e => hx.2.2 (F.sure x e), fun e he h => hx.2.2 (F.esure e he x h)⟩).trans
    (F.wr.mono fun x hx => ⟨hx.1, a x hx.2.1, hx.2.2⟩), fun x hx => a x (F.sure x hx), F.dist,
    fun e he x hx => a x (F.esure e he x hx), F.edist, F.apart⟩

/-! ## The leaves and `[7 p q]` -/

theorem footX_frag {nm : Nomm} (hf : ∀ goal : CGoal S, Frag nm goal) : FootX S Map nm := by
  intro goal region g0 g1 nex hd hg hD _ h
  rw [runL_frag (hf goal)] at h
  obtain ⟨⟨n, g⟩, hr, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact footR_toL (run_foot nm goal g0 g n hd hg hD hr)

theorem footX_seven {p q : Nomm} (hq : ∀ goal : CGoal S, Frag q goal) (ihp : FootX S Map p)
    (kp : KeepX S Map p) : FootX S Map (Nomm.n7 p q) := by
  intro goal region g0 g1 nex hd hg hD hc h
  rw [runL_n7] at h
  obtain ⟨nx, g, h1, h2⟩ := bind_some h
  rw [runL_frag (hq goal)] at h1
  obtain ⟨⟨n, g'⟩, hr, e⟩ := Option.map_eq_some_iff.mp h1
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨k1, n1⟩ := run_keeps q goal g0 g' n hd hg hr
  have Fq := run_foot q goal g0 g' n hd hg hD hr
  have hcp : sixCount p ≤ 255 := by simp only [sixCount] at hc; omega
  have Fp := ihp (goal := CGoal.next n.laz n.th) (k1.dropF hd) n1 Fq.dist hcp h2
  have l2 := (kp (goal := CGoal.next n.laz n.th) (k1.dropF hd) n1 hcp h2).keeps.le
  have l1 := k1.le
  refine Fp.pre (Fq.wr.mono fun x hx => ⟨by omega, hx.2.1, fun e => ?ne⟩) fun x hx => ?a
  case ne =>
    rcases e with e | e
    · omega
    · exact hx.2.2 e
  case a =>
    rcases hx with e | e
    · exact Or.inl (by omega)
    · exact Fq.sure x e

theorem footX_sevenFrom {axe : Nat} {q : Nomm} (ha : 2 ≤ axe) (ihq : FootX S Map q) :
    FootX S Map (Nomm.n7 (Nomm.n0 axe) q) := by
  intro goal region g0 g1 nex hd hg hD hc h
  obtain ⟨nx, laz', h1, hl, rfl⟩ := runL_seven_from ha h
  have F := ihq hd hg hD (by simp only [sixCount] at hc; omega) h1
  have E := fromL_ent axe _ _ hl
  have fs := fromL_sure hl
  have ent : ∀ e ∈ entries laz', ∃ l : Lazy S, fromSure axe l.sure = some e.2.sure ∧ (e.1, l) ∈ entries nx.laz :=
    fun e he => by
      obtain ⟨l, hl', he'⟩ := E.mem_right he
      exact ⟨l, fromL_sure hl', he'⟩
  have w : ∀ x, ¬ NMem nx.laz.sure.ned x → (∀ e ∈ entries nx.laz, ¬ NMem e.2.sure.ned x) →
      ¬ NMem laz'.sure.ned x ∧ ∀ e ∈ entries laz', ¬ NMem e.2.sure.ned x := fun x h1 h2 => by
    refine ⟨fun e => h1 (nmem_fromSure fs e), fun e he h => ?_⟩
    obtain ⟨l, fl, ml⟩ := ent e he
    exact h2 _ ml (nmem_fromSure fl h)
  have es : ∀ e ∈ entries laz', ∀ x, NMem e.2.sure.ned x → g0.re ≤ x ∨ GMem goal x := fun e he x hx => by
    obtain ⟨l, fl, ml⟩ := ent e he
    exact F.esure _ ml x (nmem_fromSure fl hx)
  have ed : ∀ e ∈ entries laz', Distinct e.2.sure.ned := fun e he => by
    obtain ⟨l, fl, ml⟩ := ent e he
    exact fromSure_dist fl (F.edist _ ml)
  have ea : ∀ e ∈ entries laz', ∀ x, NMem laz'.sure.ned x → ¬ NMem e.2.sure.ned x := fun e he x hx h => by
    obtain ⟨l, fl, ml⟩ := ent e he
    exact F.apart _ ml x (nmem_fromSure fs hx) (nmem_fromSure fl h)
  exact ⟨F.wr.mono fun x hx => ⟨hx.1, hx.2.1, w x hx.2.2.1 hx.2.2.2⟩, fun x hx => F.sure x (nmem_fromSure fs hx),
    fromSure_dist fs F.dist, es, ed, ea⟩

/-! ## `%4` and `%3` -/

/-- The block of a unary op that reads the fresh register `arg`, then the run
of the operand for `arg`. -/
theorem footX_tail {p : Nomm} (ihp : FootX S Map p) (kp : KeepX S Map p) {goal : CGoal S} {b : Blob} {arg : Nat}
    {region : List Nat} {g0 g g1 g2 : Gen Map} {o : Nat} {nex : NextL S} (hd : g.drop = false)
    (hb : BlobIn (· < g.re) b) (ha : arg + 1 = g.re) (h0 : g0.re ≤ arg) (hc : sixCount p ≤ 255)
    (W : WroteIn (fun x => x < arg ∧ (g0.re ≤ x ∨ GMem goal x)) g0 g)
    (hbw : BlobWr (fun x => x < arg ∧ (g0.re ≤ x ∨ GMem goal x)) b) (h1 : (emit b : CM Map Nat) g = some (o, g1))
    (h : runL p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region g1 = some (nex, g2)) : FootR g0 g2 goal nex := by
  obtain ⟨k1, q1⟩ := keeps_emit hd hb h1
  have hg : GoalIn g1.re (CGoal.next (lazyReg arg : Sure S) (jmp0 o)) := ⟨nb_this (by omega), jmpIn_jmp0 _ _⟩
  have F := ihp (goal := CGoal.next (lazyReg arg) (jmp0 o)) (k1.dropF hd) hg trivial hc h
  have l2 := (kp (goal := CGoal.next (lazyReg arg) (jmp0 o)) (k1.dropF hd) hg hc h).keeps.le
  refine F.pre ((W.trans (wroteIn_emit hbw h1)).mono fun x hx => ⟨by omega, hx.2, fun e => ?ne⟩) fun x hx => ?a
  case ne =>
    rcases e with e | e
    · omega
    · have : x = arg := e
      omega
  case a =>
    rcases hx with e | e
    · exact Or.inl (by omega)
    · have : x = arg := e
      exact Or.inl (by omega)

theorem footX_four {p : Nomm} (ih : FootX S Map p) (kp : KeepX S Map p) : FootX S Map (Nomm.n4 p) := by
  intro goal region g g' nex hd hg hD hc h
  have hcp : sixCount p ≤ 255 := by simpa only [sixCount] using hc
  cases goal with
  | done =>
    simp only [CGoal.toL] at h
    unfold runL at h
    obtain ⟨pro, g1, h1, h⟩ := bind_some h
    obtain ⟨e1, q1, k1⟩ := keeps_re h1
    obtain ⟨arg, g2, h2, h⟩ := bind_some h
    obtain ⟨e2, q2, k2⟩ := keeps_re h2
    obtain ⟨o, g3, h3, h⟩ := bind_some h
    exact footX_tail ih kp ((k1.trans k2).dropF hd) (blobIn_one (p := Pole.inc arg pro) (f := Termin.don pro)
      (fun x hx => by simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; omega)
      (show pro < g2.re by omega)) (by omega) (by omega) hcp ((wroteIn_re h1).trans (wroteIn_re h2))
      (blobWr_inc _ ⟨by omega, Or.inl (by omega)⟩) h3 h
  | pick z o =>
    simp only [CGoal.toL] at h
    unfold runL at h
    obtain ⟨pro, g1, h1, h⟩ := bind_some h
    obtain ⟨e1, q1, k1⟩ := keeps_re h1
    obtain ⟨arg, g2, h2, h⟩ := bind_some h
    obtain ⟨e2, q2, k2⟩ := keeps_re h2
    obtain ⟨o', g3, h3, h⟩ := bind_some h
    have kk : ∀ x, x < g.re → x < g2.re := fun x hx => by omega
    exact footX_tail ih kp ((k1.trans k2).dropF hd) (blobIn_one (p := Pole.inc arg pro) (f := Termin.brn pro z o)
      (fun x hx => by simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; omega)
      ⟨show pro < g2.re by omega, hg.1.mono kk, hg.2.mono kk⟩) (by omega) (by omega) hcp
      ((wroteIn_re h1).trans (wroteIn_re h2)) (blobWr_inc _ ⟨by omega, Or.inl (by omega)⟩) h3 h
  | next laz th =>
    simp only [CGoal.toL] at h
    unfold runL at h
    obtain ⟨a, g1, h1, h⟩ := bind_some h
    rw [collapseLazyAtomL_mk] at h1
    obtain ⟨k1, r1⟩ := keeps_collapseLazyAtom (nex := ⟨laz, th⟩) hd hg.1 h1
    obtain ⟨w1, rr1⟩ := wr_collapseLazyAtom (nex := ⟨laz, th⟩) hd hg.1 h1
    obtain ⟨⟨pro, th'⟩, g2, h2, h⟩ := bind_some h
    have hp : Keeps g1 g2 ∧ pro < g2.re ∧ WroteIn (fun _ => False) g1 g2 ∧ (NewOr laz.ned g g1 pro ∨ g1.re ≤ pro) := by
      cases a with
      | some x =>
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        exact ⟨Keeps.refl _, r1 _ _ rfl, WroteIn.refl _ _, Or.inl (rr1 _ _ rfl)⟩
      | none =>
        simp only at h2
        obtain ⟨r, g3, h3, h2⟩ := bind_some h2
        obtain ⟨e3, q3, k3⟩ := keeps_re h3
        by_cases ht : th.args = []
        · rw [if_pos ht] at h2
          simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
          exact ⟨k3, by omega, wroteIn_re h3, Or.inr (by omega)⟩
        · rw [if_neg ht] at h2; cases h2
    obtain ⟨k2, p2, w2, pp⟩ := hp
    obtain ⟨arg, g3, h3, h⟩ := bind_some h
    obtain ⟨e3, q3, k3⟩ := keeps_re h3
    obtain ⟨o, g4, h4, h⟩ := bind_some h
    have l1 := k1.le
    have l2 := k2.le
    have bnd : ∀ x, NewOr laz.ned g g1 x → x < arg ∧ (g.re ≤ x ∨ GMem (CGoal.next laz th) x) := fun x hx => by
      rcases hx with e | e
      · exact ⟨by have := hg.1 x e; omega, Or.inr e⟩
      · exact ⟨by omega, Or.inl e.1⟩
    exact footX_tail ih kp ((k1.trans (k2.trans k3)).dropF hd)
      (blobIn_one (p := Pole.inc arg pro) (f := Termin.hop (jmp0 th'))
        (fun x hx => by simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; omega)
        (jmpIn_jmp0 _ _)) (by omega) (by omega) hcp
      (((w1.mono bnd).trans (w2.mono fun _ e => e.elim)).trans (wroteIn_re h3))
      (blobWr_inc _ (by
        rcases pp with e | e
        · exact bnd pro e
        · exact ⟨by omega, Or.inl (by omega)⟩)) h4 h

theorem footX_three {p : Nomm} (ih : FootX S Map p) (kp : KeepX S Map p) : FootX S Map (Nomm.n3 p) := by
  intro goal region g g' nex hd hg hD hc h
  have hcp : sixCount p ≤ 255 := by simpa only [sixCount] using hc
  cases goal with
  | done =>
    simp only [CGoal.toL] at h
    unfold runL at h
    obtain ⟨⟨o0, o1⟩, g1, h1, h⟩ := bind_some h
    have k1 := keeps_doneBlocks hd h1
    obtain ⟨r, g2, h2, h⟩ := bind_some h
    obtain ⟨e2, q2, k2⟩ := keeps_re h2
    obtain ⟨oc, g3, h3, h⟩ := bind_some h
    have l1 := k1.le
    exact footX_tail ih kp ((k1.trans k2).dropF hd)
      (blobIn_fin (f := Termin.clq r (jmp0 o0) (jmp0 o1)) ⟨show r < g2.re by omega, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩)
      (by omega) (by omega) hcp (((wr_doneBlocks h1).mono fun x hx => by
        rcases hx with e | e
        · exact e.elim
        · exact ⟨by omega, Or.inl e.1⟩).trans (wroteIn_re h2)) (blobWr_fin _ _) h3 h
  | pick z o =>
    simp only [CGoal.toL] at h
    unfold runL at h
    obtain ⟨r, g2, h2, h⟩ := bind_some h
    obtain ⟨e2, q2, k2⟩ := keeps_re h2
    obtain ⟨oc, g3, h3, h⟩ := bind_some h
    have kk : ∀ x, x < g.re → x < g2.re := fun x hx => by omega
    exact footX_tail ih kp (k2.dropF hd)
      (blobIn_fin (f := Termin.clq r z o) ⟨show r < g2.re by omega, hg.1.mono kk, hg.2.mono kk⟩) (by omega) (by omega)
      hcp (wroteIn_re h2) (blobWr_fin _ _) h3 h
  | next laz th =>
    simp only [CGoal.toL] at h
    unfold runL at h
    dsimp only at h
    revert h; split
    · exact fun h => ih (goal := CGoal.next laz th) hd hg hD hcp h
    intro h
    obtain ⟨a, g1, h1, h⟩ := bind_some h
    rw [collapseLazyAtomL_mk] at h1
    obtain ⟨k1, r1⟩ := keeps_collapseLazyAtom (nex := ⟨laz, th⟩) hd hg.1 h1
    obtain ⟨w1, rr1⟩ := wr_collapseLazyAtom (nex := ⟨laz, th⟩) hd hg.1 h1
    rcases a with _ | ⟨r, o⟩
    · cases h
    simp only at h
    obtain ⟨⟨z, o'⟩, g2, h2, h⟩ := bind_some h
    have k2 := keeps_forl (k1.dropF hd) (r1 r o rfl) h2
    obtain ⟨r', g3, h3, h⟩ := bind_some h
    obtain ⟨e3, q3, k3⟩ := keeps_re h3
    obtain ⟨oc, g4, h4, h⟩ := bind_some h
    have l1 := k1.le
    have l2 := k2.le
    have bnd : ∀ x, NewOr laz.ned g g1 x → x < r' ∧ (g.re ≤ x ∨ GMem (CGoal.next laz th) x) := fun x hx => by
      rcases hx with e | e
      · exact ⟨by have := hg.1 x e; omega, Or.inr e⟩
      · exact ⟨by omega, Or.inl e.1⟩
    have bnd2 : ∀ x, NewOr (Need.this r) g1 g2 x → x < r' ∧ (g.re ≤ x ∨ GMem (CGoal.next laz th) x) :=
      fun x hx => by
        rcases hx with e | e
        · simp only [NMem] at e; rw [e]; exact bnd r (rr1 r o rfl)
        · exact ⟨by omega, Or.inl (by omega)⟩
    exact footX_tail ih kp ((k1.trans (k2.trans k3)).dropF hd)
      (blobIn_fin (f := Termin.clq r' (jmp0 z) (jmp0 o')) ⟨show r' < g3.re by omega, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩)
      (by omega) (by omega) hcp (((w1.mono bnd).trans ((wr_forl h2).mono bnd2)).trans (wroteIn_re h3))
      (blobWr_fin _ _) h4 h

/-! ## `+copy` and the binary cases -/

/-- **The `+copy` of two distinct sure needs apart and below `re`** writes
registers of the two needs and none of the copy, which is distinct and made
of their registers and fresh ones. -/
theorem foot_copy {a b : Sure S} {th : Jmp} {g g' : Gen Map} {n : Next S} (hd : g.drop = false)
    (hj : JmpIn (· < g.re) th) (da : Distinct a.ned) (db : Distinct b.ned) (ab : ∀ y, NMem a.ned y → ¬ NMem b.ned y)
    (na : NB g.re a.ned) (nb : NB g.re b.ned) (h : copy ⟨a, th⟩ b g = some (n, g')) :
    WroteIn (fun y => y < g.re ∧ (NMem a.ned y ∨ NMem b.ned y) ∧ ¬ NMem n.laz.ned y) g g' ∧
    (∀ y, NMem n.laz.ned y → NMem a.ned y ∨ NMem b.ned y ∨ g.re ≤ y) ∧ Distinct n.laz.ned ∧ g.re ≤ g'.re := by
  simp only [copy] at h
  obtain ⟨o, g5, h50, h5⟩ := bind_some h
  obtain ⟨k5, q5⟩ := keeps_emit hd (blobIn_fin (f := Termin.hop th) hj) h50
  obtain ⟨laz, g6, h6, h5⟩ := bind_some h5
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h5
  obtain ⟨rfl, rfl⟩ := h5
  simp only [copyLazy] at h6
  obtain ⟨⟨n1, o1⟩, g7, h7, h6⟩ := bind_some h6
  obtain ⟨u, g8, h8, h6⟩ := bind_some h6
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h6
  obtain ⟨rfl, rfl⟩ := h6
  have dpair : Distinct (Need.pair a.ned b.ned) := ⟨da, db, ab⟩
  have nb1 : NB g5.re a.ned := by rw [q5]; exact na
  have nb2 : NB g5.re b.ned := by rw [q5]; exact nb
  obtain ⟨A, eA, wA⟩ := wr_copyNeed _ _ _ _ _ _ h7 dpair nb1 nb2
  have dres := copyNeed_dist _ _ _ _ _ _ h7 dpair nb1 nb2
  obtain ⟨_, _, c7⟩ := copyNeed_spec _ _ _ _ _ _ h7
  have m7 := c7.mem
  have l7 := c7.le
  have q8 := (addOps_re h8).1
  simp only at eA wA dres m7
  have wC : OpsWr (fun y => y < g.re ∧ (NMem a.ned y ∨ NMem b.ned y) ∧ ¬ NMem n1 y) o1 := by
    rw [eA, List.append_nil]
    refine wA.mono fun y hy => ⟨?_, hy.1, hy.2⟩
    rcases hy.1 with e | e
    · exact na y e
    · exact nb y e
  refine ⟨(wroteIn_emit (blobWr_fin _ _) h50).trans ((wroteIn_of_gen c7.gen).trans (wroteIn_addOps wC h8)),
    fun y hy => ?_, dres, by omega⟩
  rcases m7 y hy with (e | e) | e
  · exact Or.inl e
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr (by omega))

/-- **The two runs and the `+copy` of cons, `%5` and `%10`**, from the
footprints of the two runs: `q` first for `nq`, `p` second for `np`, the
two needs distinct and apart.  The footprint is stated for the goal whose
need is the pair of the two. -/
theorem footX_binary {p q : Nomm} (ihp : FootX S Map p) (ihq : FootX S Map q) (kp : KeepX S Map p)
    (kq : KeepX S Map q) {region : List Nat} {g0 g1 g2 g3 : Gen Map} {nq np : Sure S} {th : Jmp}
    {nex2 nex1 nex : NextL S} (hd : g0.drop = false) (hc : sixCount p + sixCount q ≤ 255) (hnq : NB g0.re nq.ned)
    (hnp : NB g0.re np.ned) (dq : Distinct nq.ned) (dp : Distinct np.ned) (ap : ∀ x, NMem np.ned x → ¬ NMem nq.ned x)
    (hj : JmpIn (· < g0.re) th)
    (h2 : runL q (CGoalL.next (ofSure nq) th) region g0 = some (nex2, g1))
    (h3 : runL p (CGoalL.next (ofSure np) nex2.th) region g1 = some (nex1, g2))
    (h4 : copyL nex1 nex2.laz g2 = some (nex, g3)) :
    FootR g0 g3 (CGoal.next ⟨Need.pair np.ned nq.ned, HoonSet.empty⟩ th) nex := by
  have Rq := kq (goal := CGoal.next nq th) hd ⟨hnq, hj⟩ (by omega) h2
  have Fq := ihq (goal := CGoal.next nq th) hd ⟨hnq, hj⟩ dq (by omega) h2
  have d1 := Rq.keeps.dropF hd
  have gp : GoalIn g1.re (CGoal.next np nex2.th) := ⟨hnp.mono Rq.keeps.le, Rq.out.2⟩
  have Rp := kp (goal := CGoal.next np nex2.th) d1 gp (by omega) h3
  have Fp := ihp (goal := CGoal.next np nex2.th) d1 gp dp (by omega) h3
  have d2 := Rp.keeps.dropF d1
  have l1 := Rq.keeps.le
  have l2 := Rp.keeps.le
  obtain ⟨n, hcp, rfl⟩ := copyL_apart_some
    (fun e he e' he' => by
      have a := (Rp.labs _ (fork_in_entries he)).1
      have b := (Rq.labs _ (fork_in_entries he')).2
      omega)
    (fun e he e' he' => by
      have a := (Rp.labs _ (bond_in_entries he)).1
      have b := (Rq.labs _ (bond_in_entries he')).2
      omega) h4
  have me : ∀ e ∈ entries (mk n.laz (nex1.laz.fork ++ nex2.laz.fork) (nex1.laz.bond ++ nex2.laz.bond)),
      e ∈ entries nex1.laz ∨ e ∈ entries nex2.laz := fun e he =>
    List.mem_append.mp ((entries_side_perm _ _ _).mem_iff.mp he)
  -- where the registers lie
  have s2 : ∀ y, NMem nex2.laz.sure.ned y → g0.re ≤ y ∨ NMem nq.ned y := Fq.sure
  have s1 : ∀ y, NMem nex1.laz.sure.ned y → g1.re ≤ y ∨ NMem np.ned y := Fp.sure
  have e2 : ∀ e ∈ entries nex2.laz, ∀ y, NMem e.2.sure.ned y → g0.re ≤ y ∨ NMem nq.ned y := Fq.esure
  have e1 : ∀ e ∈ entries nex1.laz, ∀ y, NMem e.2.sure.ned y → g1.re ≤ y ∨ NMem np.ned y := Fp.esure
  have b2 : ∀ y, NMem nex2.laz.sure.ned y → y < g1.re := Rq.out.1.1
  have b1 : ∀ y, NMem nex1.laz.sure.ned y → y < g2.re := Rp.out.1.1
  have be2 : ∀ e ∈ entries nex2.laz, ∀ y, NMem e.2.sure.ned y → y < g1.re := Rq.out.1.2
  have be1 : ∀ e ∈ entries nex1.laz, ∀ y, NMem e.2.sure.ned y → y < g2.re := Rp.out.1.2
  -- a register of `q`'s side below `g1.re` is no register of `p`'s side
  have qp : ∀ y, y < g1.re → (g0.re ≤ y ∨ NMem nq.ned y) → ¬ (g1.re ≤ y ∨ NMem np.ned y) := fun y hy hq hp => by
    rcases hp with e | e
    · omega
    · rcases hq with e' | e'
      · have := hnp y e; omega
      · exact ap y e e'
  have A12 : ∀ y, NMem nex1.laz.sure.ned y → ¬ NMem nex2.laz.sure.ned y := fun y a b => qp y (b2 y b) (s2 y b) (s1 y a)
  have X12 : ∀ y, NMem nex1.laz.sure.ned y → ∀ e ∈ entries nex2.laz, ¬ NMem e.2.sure.ned y := fun y a e he b =>
    qp y (be2 e he y b) (e2 e he y b) (s1 y a)
  have X21 : ∀ y, NMem nex2.laz.sure.ned y → ∀ e ∈ entries nex1.laz, ¬ NMem e.2.sure.ned y := fun y a e he b =>
    qp y (b2 y a) (s2 y a) (e1 e he y b)
  have nb1 : NB g2.re nex1.laz.sure.ned := b1
  have nb2 : NB g2.re nex2.laz.sure.ned := fun y hy => by have := b2 y hy; omega
  obtain ⟨WC, sC, dC, lC⟩ := foot_copy d2 Rp.out.2 Fp.dist Fq.dist A12 nb1 nb2 hcp
  -- the result's needs
  have rs : ∀ y, NMem n.laz.ned y → NMem nex1.laz.sure.ned y ∨ NMem nex2.laz.sure.ned y ∨ g2.re ≤ y := sC
  have G : ∀ y, (g0.re ≤ y ∨ NMem np.ned y ∨ NMem nq.ned y) →
      g0.re ≤ y ∨ GMem (CGoal.next (⟨Need.pair np.ned nq.ned, HoonSet.empty⟩ : Sure S) th) y := fun y hy => hy
  -- `q`'s writes
  have Wq : ∀ y, (y < g1.re ∧ (g0.re ≤ y ∨ NMem nq.ned y) ∧ ¬ NMem nex2.laz.sure.ned y ∧
      ∀ e ∈ entries nex2.laz, ¬ NMem e.2.sure.ned y) →
      ¬ NMem n.laz.ned y ∧ ∀ e ∈ entries (mk n.laz (nex1.laz.fork ++ nex2.laz.fork) (nex1.laz.bond ++ nex2.laz.bond)),
        ¬ NMem e.2.sure.ned y := fun y hy => by
    refine ⟨fun e => ?_, fun e he h => ?_⟩
    · rcases rs y e with e' | e' | e'
      · exact qp y hy.1 hy.2.1 (s1 y e')
      · exact hy.2.2.1 e'
      · omega
    · rcases me e he with e' | e'
      · exact qp y hy.1 hy.2.1 (e1 e e' y h)
      · exact hy.2.2.2 e e' h
  -- `p`'s writes
  have Wp : ∀ y, (y < g2.re ∧ (g1.re ≤ y ∨ NMem np.ned y) ∧ ¬ NMem nex1.laz.sure.ned y ∧
      ∀ e ∈ entries nex1.laz, ¬ NMem e.2.sure.ned y) →
      ¬ NMem n.laz.ned y ∧ ∀ e ∈ entries (mk n.laz (nex1.laz.fork ++ nex2.laz.fork) (nex1.laz.bond ++ nex2.laz.bond)),
        ¬ NMem e.2.sure.ned y := fun y hy => by
    refine ⟨fun e => ?_, fun e he h => ?_⟩
    · rcases rs y e with e' | e' | e'
      · exact hy.2.2.1 e'
      · exact qp y (b2 y e') (s2 y e') hy.2.1
      · omega
    · rcases me e he with e' | e'
      · exact hy.2.2.2 e e' h
      · exact qp y (be2 e e' y h) (e2 e e' y h) hy.2.1
  -- the copy's writes
  have Wc : ∀ y, (y < g2.re ∧ (NMem nex1.laz.sure.ned y ∨ NMem nex2.laz.sure.ned y) ∧ ¬ NMem n.laz.ned y) →
      ∀ e ∈ entries (mk n.laz (nex1.laz.fork ++ nex2.laz.fork) (nex1.laz.bond ++ nex2.laz.bond)),
        ¬ NMem e.2.sure.ned y := fun y hy e he h => by
    rcases me e he with e' | e' <;> rcases hy.2.1 with a | a
    · exact Fp.apart e e' y a h
    · exact X21 y a e e' h
    · exact X12 y a e e' h
    · exact Fq.apart e e' y a h
  have pa : ∀ y, (NMem nex1.laz.sure.ned y ∨ NMem nex2.laz.sure.ned y) → g0.re ≤ y ∨ NMem np.ned y ∨ NMem nq.ned y :=
    fun y hy => by
      rcases hy with a | a
      · rcases s1 y a with e | e
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl e)
      · exact (s2 y a).imp id Or.inr
  refine ⟨(Fq.wr.mono fun y hy => ⟨by omega, G y (hy.2.1.imp id Or.inr), (Wq y hy).1, (Wq y hy).2⟩).trans
    ((Fp.wr.mono fun y hy => ⟨by omega, G y (hy.2.1.elim (fun e => Or.inl (by omega)) (fun e => Or.inr (Or.inl e))),
      (Wp y hy).1, (Wp y hy).2⟩).trans
    (WC.mono fun y hy => ⟨by omega, G y (pa y hy.2.1), hy.2.2, Wc y hy⟩)), fun y hy => ?_, dC, fun e he y hy => ?_,
    fun e he => ?_, fun e he y hy h => ?_⟩
  · rcases rs y hy with e | e | e
    · exact G y (pa y (Or.inl e))
    · exact G y (pa y (Or.inr e))
    · exact Or.inl (by omega)
  · rcases me e he with e' | e'
    · rcases e1 e e' y hy with a | a
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl a)
    · exact G y ((e2 e e' y hy).imp id Or.inr)
  · rcases me e he with e' | e'
    · exact Fp.edist e e'
    · exact Fq.edist e e'
  · rcases rs y hy with a | a | a
    · rcases me e he with e' | e'
      · exact Fp.apart e e' y a h
      · exact X12 y a e e' h
    · rcases me e he with e' | e'
      · exact X21 y a e e' h
      · exact Fq.apart e e' y a h
    · rcases me e he with e' | e'
      · have := be1 e e' y h; omega
      · have := be2 e e' y h; omega

theorem footX_consBody {p q : Nomm} (ihp : FootX S Map p) (ihq : FootX S Map q) (kp : KeepX S Map p)
    (kq : KeepX S Map q) (hpp : p.pure = true) (hqp : q.pure = true) {sur : Sure S} {th : Jmp} {region : List Nat}
    {g0 g1 : Gen Map} {nex : NextL S} (hd : g0.drop = false) (hg : GoalIn g0.re (CGoal.next sur th))
    (hD : Distinct sur.ned) (hc : sixCount p + sixCount q ≤ 255)
    (h : (do
      let (hed, tel, o) ← splitL ⟨ofSure sur, th⟩
      let nexh ← pastL noCode ⟨hed, jmp0 o⟩ q region
      let nex2 ← runL q (CGoalL.next tel nexh.th) region
      let nex2 ← pastL noCode nex2 p region
      let nex1 ← runL p (CGoalL.next nexh.laz nex2.th) region
      copyL nex1 nex2.laz : CM Map (NextL S)) g0 = some (nex, g1)) : FootR g0 g1 (CGoal.next sur th) nex := by
  obtain ⟨⟨hed', tel', o⟩, g2x, h2, h⟩ := bind_some h
  rw [splitL_mk, map_apply] at h2
  obtain ⟨⟨⟨hed, tel, o'⟩, g2⟩, hs2, e2⟩ := Option.map_eq_some_iff.mp h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e2
  obtain ⟨k2, nh, nt⟩ := keeps_split hd hg.1 hg.2 hs2
  obtain ⟨W2, dh, dt, ap, mh, mt⟩ := split_foot hd hD hg.1 hg.2 hs2
  simp only at W2 dh dt ap mh mt nh nt
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
  have F := footX_binary ihp ihq kp kq (k2.dropF hd) hc nt nh dt dh ap (jmpIn_jmp0 _ _) h3 h4 hcp
  have lF := (keepX_binary kp kq (k2.dropF hd) hc nt nh (jmpIn_jmp0 _ _) h3 h4 hcp).keeps.le
  have l2 := k2.le
  refine F.pre (W2.mono fun y hy => ⟨?hlt, Or.inr hy.1, ?hng⟩) fun y hy => ?hA
  case hlt => have := hg.1 y hy.1; omega
  case hng =>
    rintro (e | e | e)
    · have := hg.1 y hy.1; omega
    · exact hy.2.1 e
    · exact hy.2.2 e
  case hA =>
    rcases hy with e | e | e
    · exact Or.inl (by omega)
    · exact (mh y e).symm
    · exact (mt y e).symm

theorem footX_cons {p q : Nomm} (ihp : FootX S Map p) (ihq : FootX S Map q) (kp : KeepX S Map p)
    (kq : KeepX S Map q) (hpp : p.pure = true) (hqp : q.pure = true) : FootX S Map (Nomm.cons p q) := by
  intro goal region g0 g1 nex hd hg hD hc h
  have hc' : sixCount p + sixCount q ≤ 255 := by simpa only [sixCount] using hc
  cases goal with
  | next sur th =>
    simp only [CGoal.toL] at h
    rw [runL_cons_next] at h
    exact footX_consBody ihp ihq kp kq hpp hqp hd hg hD hc' h
  | done =>
    simp only [CGoal.toL] at h
    rw [runL_cons_done] at h
    obtain ⟨r, ga, h1, h⟩ := bind_some h
    obtain ⟨e1, q1, k1⟩ := keeps_re h1
    obtain ⟨o, gb, h2, h⟩ := bind_some h
    obtain ⟨k2, q2⟩ := keeps_emit (k1.dropF hd) (blobIn_fin (f := Termin.don r) (show r < ga.re by omega)) h2
    rw [runL_cons_next] at h
    have F := footX_consBody (sur := lazyReg r) ihp ihq kp kq hpp hqp ((k1.trans k2).dropF hd)
      ⟨nb_this (by omega), jmpIn_jmp0 _ _⟩ trivial hc' h
    refine F.pre ((wroteIn_re h1).trans (wroteIn_emit (blobWr_fin _ _) h2)) fun y hy => ?_
    rcases hy with e | e
    · exact Or.inl (by omega)
    · have : y = r := e
      exact Or.inl (by omega)
  | pick z o =>
    simp only [CGoal.toL] at h
    rw [runL_cons_pick] at h
    obtain ⟨o', ga, h1, h⟩ := bind_some h
    obtain ⟨k1, q1⟩ := keeps_emit hd (blobIn_fin (f := Termin.bom Option.none) trivial) h1
    obtain ⟨nex2, gb, h3, h⟩ := bind_some h
    obtain ⟨nex2', gb', hp2, h⟩ := bind_some h
    rw [pastL_pure _ _ hpp, pure_apply] at hp2
    simp only [Option.some.injEq, Prod.mk.injEq] at hp2
    obtain ⟨rfl, rfl⟩ := hp2
    obtain ⟨nex1, gc, h4, h⟩ := bind_some h
    have F := footX_binary (nq := Sure.bunt) (np := Sure.bunt) ihp ihq kp kq (k1.dropF hd) hc' (nb_none _)
      (nb_none _) trivial trivial (fun _ e => e.elim) (jmpIn_jmp0 _ _) h3 h4 h
    refine F.pre (wroteIn_emit (blobWr_fin _ _) h1) fun y hy => ?_
    rcases hy with e | e | e
    · exact Or.inl (by omega)
    · exact e.elim
    · exact e.elim

theorem footX_five {p q : Nomm} (ihp : FootX S Map p) (ihq : FootX S Map q) (kp : KeepX S Map p)
    (kq : KeepX S Map q) (hpp : p.pure = true) : FootX S Map (Nomm.n5 p q) := by
  intro goal region g g' nex hd hg hD hc h
  have hc' : sixCount p + sixCount q ≤ 255 := by simpa only [sixCount] using hc
  rw [runL_n5_toL] at h
  obtain ⟨rp, g1, h1, h⟩ := bind_some h
  obtain ⟨e1, q1, k1⟩ := keeps_re h1
  obtain ⟨rq, g2, h2, h⟩ := bind_some h
  obtain ⟨e2, q2, k2⟩ := keeps_re h2
  have d2 := (k1.trans k2).dropF hd
  have kk : ∀ x, x < g.re → x < g2.re := fun x hx => by omega
  obtain ⟨o, g3, h3, h⟩ := bind_some h
  have k3 := keeps_n5Pre d2 (hg.mono (by omega)) (by omega) (by omega) h3
  have W3 : WroteIn (fun x => x < g3.re ∧ (g2.re ≤ x ∨ GMem goal x)) g2 g3 := by
    cases goal with
    | pick z o =>
      exact wroteIn_emit (blobWr_fin _ _) h3
    | done =>
      simp only [n5Pre] at h3
      obtain ⟨⟨o0, o1⟩, g4, h4, h3⟩ := bind_some h3
      have k4 := keeps_doneBlocks d2 h4
      have k5 := (keeps_emit (k4.dropF d2) (blobIn_fin (f := Termin.eqq rp rq (jmp0 o0) (jmp0 o1))
          ⟨show rp < g4.re by have := k4.le; omega, show rq < g4.re by have := k4.le; omega,
            jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩) h3).1
      have l5 := k5.le
      exact ((wr_doneBlocks h4).mono fun x hx => by
        rcases hx with e | e
        · exact e.elim
        · exact ⟨by omega, Or.inl e.1⟩).trans (wroteIn_emit (blobWr_fin _ _) h3)
    | next laz th =>
      simp only [n5Pre] at h3
      obtain ⟨a, g4, h4, h3⟩ := bind_some h3
      obtain ⟨k4, r4⟩ := keeps_collapseLazyAtom (nex := ⟨laz, th⟩) d2 (hg.1.mono (by omega)) h4
      obtain ⟨w4, rr4⟩ := wr_collapseLazyAtom (nex := ⟨laz, th⟩) d2 (hg.1.mono (by omega)) h4
      have l4 := k4.le
      cases a with
      | none =>
        simp only at h3
        by_cases ht : th.args = []
        · rw [if_pos ht] at h3
          have k5 := (keeps_emit (k4.dropF d2) (blobIn_one (p := Pole.equ rp rq) (f := Termin.hop (jmp0 th.there))
            (fun x hx => by simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; omega)
            (jmpIn_jmp0 _ _)) h3).1
          have l5 := k5.le
          exact (w4.mono fun x hx => by
            rcases hx with e | e
            · exact ⟨by have := hg.1 x e; omega, Or.inr e⟩
            · exact ⟨by omega, Or.inl e.1⟩).trans (wroteIn_emit (blobWr_one (p := Pole.equ rp rq) _
              (fun x hx => by simp [poleWr] at hx)) h3)
        · rw [if_neg ht] at h3; cases h3
      | some x =>
        obtain ⟨r, o⟩ := x
        simp only at h3
        obtain ⟨⟨z, o'⟩, g5, h5, h3⟩ := bind_some h3
        have k5 := keeps_forl (k4.dropF d2) (r4 r o rfl) h5
        have l5 := k5.le
        have k6 := (keeps_emit ((k4.trans k5).dropF d2) (blobIn_fin (f := Termin.eqq rp rq (jmp0 z) (jmp0 o'))
          ⟨show rp < g5.re by omega, show rq < g5.re by omega, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩) h3).1
        have l6 := k6.le
        have bnd : ∀ x, NewOr laz.ned g2 g4 x → x < g3.re ∧ (g2.re ≤ x ∨ GMem (CGoal.next laz th) x) :=
          fun x hx => by
            rcases hx with e | e
            · exact ⟨by have := hg.1 x e; omega, Or.inr e⟩
            · exact ⟨by omega, Or.inl e.1⟩
        refine ((w4.mono bnd).trans ((wr_forl h5).mono fun x hx => ?_)).trans (wroteIn_emit (blobWr_fin _ _) h3)
        rcases hx with e | e
        · simp only [NMem] at e; rw [e]; exact bnd r (rr4 r o rfl)
        · exact ⟨by omega, Or.inl (by omega)⟩
  have l3 := k3.le
  have d3 := k3.dropF d2
  obtain ⟨nexq, g4, h4, h⟩ := bind_some h
  obtain ⟨nexq', g4', hp, h⟩ := bind_some h
  rw [pastL_pure _ _ hpp, pure_apply] at hp
  simp only [Option.some.injEq, Prod.mk.injEq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  obtain ⟨nexp, g5, h5, h⟩ := bind_some h
  have F := footX_binary (nq := lazyReg rq) (np := lazyReg rp) ihp ihq kp kq d3 hc' (nb_this (by omega))
    (nb_this (by omega)) trivial trivial (fun x e e' => by simp only [lazyReg, NMem] at e e'; omega) (jmpIn_jmp0 _ _)
    h4 h5 h
  have lF := (keepX_binary (nq := lazyReg rq) (np := lazyReg rp) kp kq d3 hc' (nb_this (by omega))
    (nb_this (by omega)) (jmpIn_jmp0 _ _) h4 h5 h).keeps.le
  have gl : ∀ x, GMem goal x → x < g.re := fun x hx => by
    cases goal with
    | next laz th => exact hg.1 x hx
    | pick => exact hx.elim
    | done => exact hx.elim
  have a : ∀ x, (g3.re ≤ x ∨ GMem (CGoal.next (⟨Need.pair (Need.this rp) (Need.this rq), HoonSet.empty⟩ : Sure S)
      (jmp0 o)) x) → g.re ≤ x := fun x hx => by
    rcases hx with e | e | e
    · omega
    · have : x = rp := e
      omega
    · have : x = rq := e
      omega
  refine F.pre (((wroteIn_re h1).trans (wroteIn_re h2)).trans (W3.mono fun x hx => ⟨by omega, ?hw, ?hn⟩))
    fun x hx => Or.inl (a x hx)
  case hw =>
    rcases hx.2 with e | e
    · exact Or.inl (by omega)
    · exact Or.inr e
  case hn =>
    intro e
    have := a x e
    rcases hx.2 with e' | e'
    · rcases e with e | e | e
      · omega
      · have : x = rp := e
        omega
      · have : x = rq := e
        omega
    · have := gl x e'; omega

theorem footX_ten {a : Nat} {v q : Nomm} (ihv : FootX S Map v) (ihq : FootX S Map q) (kv : KeepX S Map v)
    (kq : KeepX S Map q) (hvp : v.pure = true) (hqp : q.pure = true) : FootX S Map (Nomm.n10 a v q) := by
  intro goal region g g' nex hd hg hD hc h
  have hc' : sixCount q + sixCount v ≤ 255 := by simp only [sixCount] at hc; omega
  rw [runL_n10_body] at h
  obtain ⟨next, gs, hs, h⟩ := bind_some h
  rw [simpleNextL_toL, map_apply] at hs
  obtain ⟨⟨n, gs'⟩, hs', e⟩ := Option.map_eq_some_iff.mp hs
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨k1, n1⟩ := keeps_simpleNext hd hg hs'
  have F0 : (∀ x, NMem n.laz.ned x → g.re ≤ x ∨ GMem goal x) ∧ Distinct n.laz.ned := by
    cases goal with
    | next laz th =>
      simp only [simpleNext, pure_apply, Option.some.injEq, Prod.mk.injEq] at hs'
      obtain ⟨rfl, rfl⟩ := hs'
      exact ⟨fun x hx => Or.inr hx, hD⟩
    | done =>
      simp only [simpleNext] at hs'
      obtain ⟨r, g5, h5, hs'⟩ := bind_some hs'
      obtain ⟨e5, _, _⟩ := keeps_re h5
      obtain ⟨o, g6, h6, hs'⟩ := bind_some hs'
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs'
      obtain ⟨rfl, rfl⟩ := hs'
      exact ⟨fun x hx => Or.inl (by simp only [lazyReg, NMem] at hx; omega), trivial⟩
    | pick z o =>
      simp only [simpleNext] at hs'
      obtain ⟨r, g5, h5, hs'⟩ := bind_some hs'
      obtain ⟨e5, _, _⟩ := keeps_re h5
      obtain ⟨o', g6, h6, hs'⟩ := bind_some hs'
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs'
      obtain ⟨rfl, rfl⟩ := hs'
      exact ⟨fun x hx => Or.inl (by simp only [lazyReg, NMem] at hx; omega), trivial⟩
  unfold n10Body at h
  obtain ⟨⟨don', rec', o⟩, g2x, h2, h⟩ := bind_some h
  rw [show (Next.toL n : NextL S) = ⟨ofSure n.laz, n.th⟩ from rfl, intoL_mk, map_apply] at h2
  obtain ⟨⟨⟨don, rec, o'⟩, g2⟩, hs2, e2⟩ := Option.map_eq_some_iff.mp h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e2
  obtain ⟨k2, nd, nr⟩ := keeps_into (k1.dropF hd) n1 hs2
  have W2 := into_wr F0.2 n1.1 hs2
  obtain ⟨_, _, _, _, md, mr, _, Sm⟩ := into_ok hs2
  obtain ⟨Dd, Dr, Ddr, _, _⟩ := Sm F0.2 n1.1
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
  have d2 := (k1.trans k2).dropF hd
  have F := footX_binary ihq ihv kq kv d2 hc' nd nr Dd Dr (fun x e e' => Ddr x e' e) (jmpIn_jmp0 _ _) h3 h4 hcp
  have lF := (keepX_binary kq kv d2 hc' nd nr (jmpIn_jmp0 _ _) h3 h4 hcp).keeps.le
  have l1 := k1.le
  have l2 := k2.le
  have A : ∀ x, (g2.re ≤ x ∨ GMem (CGoal.next (⟨Need.pair rec.ned don.ned, HoonSet.empty⟩ : Sure S) (jmp0 o')) x) →
      g.re ≤ x ∨ GMem goal x := fun x hx => by
    rcases hx with e | e | e
    · exact Or.inl (by omega)
    · rcases mr x e with e' | e'
      · exact F0.1 x e'
      · exact Or.inl (by omega)
    · rcases md x e with e' | e'
      · exact F0.1 x e'
      · exact Or.inl (by omega)
  refine F.pre ((wr_simpleNext _ hs').trans (W2.mono fun x hx => ⟨?hlt, ?hg2, ?hn⟩)) A
  case hlt =>
    rcases hx.1 with e | e
    · have := n1.1 x e; omega
    · omega
  case hg2 =>
    rcases hx.1 with e | e
    · exact F0.1 x e
    · exact Or.inl (by omega)
  case hn =>
    rintro (e | e | e)
    · rcases hx.1 with e' | e'
      · have := n1.1 x e'; omega
      · omega
    · exact hx.2.2 e
    · exact hx.2.1 e

/-! ## `%6` under `%done` and `%pick` -/

theorem wroteIn_sixGenL {Q : Nat → Prop} (g2 : Gen Map) (t0 t1 : Jmp) (region : List Nat) :
    WroteIn Q g2 (sixGenL g2 t0 t1 region) := by
  intro o b' hb
  simp only [sixGenL, tagged_blocks] at hb
  exact ((wroteIn_emitted (blobWr_fin Q _)).trans (wroteIn_emitted (blobWr_fin Q _))) o b' hb

/-- **`%6` for `%done` or `%pick`**: the branches `b` and `a` write
registers they allocate, the test `c` registers above both, `sixGenL`
nothing, and the `+copy` of the test's need with the two lazy blocks the
registers of the test's need.  The entries of the result are the test's,
the two branches' lazy needs and their entries. -/
theorem footX_sixP {c a b : Nomm} (hcp : c.pure = true) (ihc : FootX S Map c) (iha : FootX S Map a)
    (ihb : FootX S Map b) (kc : KeepX S Map c) (ka : KeepX S Map a) (kb : KeepX S Map b)
    {goal : CGoal S} (hg' : NotNext goal) {region : List Nat} {g0 g4 : Gen Map} {nex : NextL S}
    (hd : g0.drop = false) (hg : GoalIn g0.re goal) (hD : GDist goal)
    (hc : sixCount c + sixCount a + sixCount b + 1 ≤ 255)
    (h : runL (Nomm.n6 c a b) (CGoal.toL goal) region g0 = some (nex, g4)) : FootR g0 g4 goal nex := by
  have ng : ∀ x, ¬ GMem goal x := fun x hx => by
    cases goal with
    | next => exact hg'
    | done => exact hx
    | pick => exact hx
  rw [runL_n6_body _ _ _ hg'] at h
  obtain ⟨x1, x0, xc, g1, g2, g3, h1, h2, _, _, h3, hrest⟩ := sixBody_apart hcp h
  have Rb := kb hd hg (by omega) h1
  have Fb := ihb hd hg hD (by omega) h1
  have d1 := Rb.keeps.dropF hd
  have Ra := ka d1 (hg.mono Rb.keeps.le) (by omega) h2
  have Fa := iha d1 (hg.mono Rb.keeps.le) hD (by omega) h2
  have d2 := Ra.keeps.dropF d1
  obtain ⟨kG, cG⟩ := keeps_sixGenL (region := region) d2 Ra.out.2
    (Rb.out.2.mono fun _ e => Nat.lt_of_lt_of_le e Ra.keeps.le)
  have gc : GoalIn (sixGenL g2 x0.th x1.th region).re (CGoal.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1)) : CGoal S) :=
    ⟨jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩
  have Rc := kc (goal := CGoal.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1))) (kG.dropF d2) gc (by omega) h3
  have Fc := ihc (goal := CGoal.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1))) (kG.dropF d2) gc trivial (by omega) h3
  have hbig : lazyBig (mk (Sure.bunt : Sure S) [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))] []) = false := by
    apply lazyBig_entries
    rw [entries_six]; simp only [List.length_append, List.length_cons]
    have := Ra.size; have := Rb.size; simp only [lazyMax]; omega
  have h4 := hrest hbig
  have d3 := Rc.keeps.dropF (kG.dropF d2)
  have l1 := Rb.keeps.le
  have l2 := Ra.keeps.le
  have l3 := Rc.keeps.le
  simp only [sixGenL_re] at l3
  obtain ⟨n, hcp', rfl⟩ := copyL_apart_some
    (fun e he e' he' => by
      have := (Rc.labs _ (fork_in_entries he)).1
      simp only [sixGenL_bo] at this
      rw [fork_mk, List.mem_singleton] at he'
      subst he'
      simp only
      omega)
    (fun e he e' he' => by rw [bond_mk] at he'; cases he') h4
  obtain ⟨WC, sC, dC, lC⟩ := foot_copy (b := (Sure.bunt : Sure S)) d3 Rc.out.2 Fc.dist trivial
    (fun _ _ e => e.elim) Rc.out.1.1 (nb_none _) hcp'
  -- the ranges of the registers
  have rcs : ∀ y, NMem xc.laz.sure.ned y → g2.re ≤ y ∧ y < g3.re := fun y hy => by
    have e := Fc.sure y hy
    simp only [sixGenL_re] at e
    exact ⟨e.resolve_right (fun e => e), Rc.out.1.1 y hy⟩
  have rce : ∀ e ∈ entries xc.laz, ∀ y, NMem e.2.sure.ned y → g2.re ≤ y ∧ y < g3.re := fun e he y hy => by
    have e' := Fc.esure e he y hy
    simp only [sixGenL_re] at e'
    exact ⟨e'.resolve_right (fun e => e), Rc.out.1.2 e he y hy⟩
  have ra : ∀ y, NMem x0.laz.sure.ned y → g1.re ≤ y ∧ y < g2.re := fun y hy =>
    ⟨(Fa.sure y hy).resolve_right (ng y), Ra.out.1.1 y hy⟩
  have rae : ∀ e ∈ entries x0.laz, ∀ y, NMem e.2.sure.ned y → g1.re ≤ y ∧ y < g2.re := fun e he y hy =>
    ⟨(Fa.esure e he y hy).resolve_right (ng y), Ra.out.1.2 e he y hy⟩
  have rb : ∀ y, NMem x1.laz.sure.ned y → g0.re ≤ y ∧ y < g1.re := fun y hy =>
    ⟨(Fb.sure y hy).resolve_right (ng y), Rb.out.1.1 y hy⟩
  have rbe : ∀ e ∈ entries x1.laz, ∀ y, NMem e.2.sure.ned y → g0.re ≤ y ∧ y < g1.re := fun e he y hy =>
    ⟨(Fb.esure e he y hy).resolve_right (ng y), Rb.out.1.2 e he y hy⟩
  have rs : ∀ y, NMem n.laz.ned y → NMem xc.laz.sure.ned y ∨ g3.re ≤ y := fun y hy => by
    rcases sC y hy with e | e | e
    · exact Or.inl e
    · exact e.elim
    · exact Or.inr e
  -- the five kinds of entries
  have K : ∀ e ∈ entries (mk n.laz (xc.laz.fork ++ [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))]) (xc.laz.bond ++ [])),
      e ∈ entries xc.laz ∨ e = (g2.bo, x0.laz) ∨ e ∈ entries x0.laz ∨ e = (g2.bo + 1, x1.laz) ∨ e ∈ entries x1.laz :=
    fun e he => by
      have := (entries_side_perm n.laz xc.laz (mk (Sure.bunt : Sure S) [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))] [])).mem_iff.mp
        (by simpa only [fork_mk, bond_mk] using he)
      rw [entries_six] at this
      simp only [List.mem_append, List.mem_cons] at this
      rcases this with e1 | (e1 | e1) | (e1 | e1)
      · exact Or.inl e1
      · exact Or.inr (Or.inl e1)
      · exact Or.inr (Or.inr (Or.inl e1))
      · exact Or.inr (Or.inr (Or.inr (Or.inl e1)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr e1)))
  -- every register of an entry lies in one of the three ranges, with its kind
  have R : ∀ e ∈ entries (mk n.laz (xc.laz.fork ++ [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))]) (xc.laz.bond ++ [])),
      ∀ y, NMem e.2.sure.ned y → (e ∈ entries xc.laz ∧ g2.re ≤ y ∧ y < g3.re) ∨
        ((NMem x0.laz.sure.ned y ∨ ∃ e' ∈ entries x0.laz, NMem e'.2.sure.ned y) ∧ g1.re ≤ y ∧ y < g2.re) ∨
        ((NMem x1.laz.sure.ned y ∨ ∃ e' ∈ entries x1.laz, NMem e'.2.sure.ned y) ∧ g0.re ≤ y ∧ y < g1.re) :=
    fun e he y hy => by
      rcases K e he with k | k | k | k | k
      · exact Or.inl ⟨k, rce e k y hy⟩
      · subst k; exact Or.inr (Or.inl ⟨Or.inl hy, ra y hy⟩)
      · exact Or.inr (Or.inl ⟨Or.inr ⟨e, k, hy⟩, rae e k y hy⟩)
      · subst k; exact Or.inr (Or.inr ⟨Or.inl hy, rb y hy⟩)
      · exact Or.inr (Or.inr ⟨Or.inr ⟨e, k, hy⟩, rbe e k y hy⟩)
  refine ⟨(Fb.wr.mono fun y hy => ⟨by omega, hy.2.1, ?b1, ?b2⟩).trans ((Fa.wr.mono fun y hy => ⟨by omega,
    Or.inl (by have := hy.2.1.resolve_right (ng y); omega), ?a1, ?a2⟩).trans ((wroteIn_sixGenL _ _ _ _).trans
    ((Fc.wr.mono fun y hy => ⟨by omega, Or.inl ?c0, ?c1, ?c2⟩).trans
    (WC.mono fun y hy => ⟨by omega, Or.inl ?w0, hy.2.2, ?w2⟩)))), fun y hy => ?hsure, dC, fun e he y hy => ?es,
    fun e he => ?ed, fun e he y hy h => ?ap⟩
  case b1 =>
    intro e
    rcases rs y e with e' | e'
    · have := rcs y e'; omega
    · omega
  case b2 =>
    intro e he h
    rcases R e he y h with ⟨_, r⟩ | ⟨_, r⟩ | ⟨k, _⟩
    · omega
    · omega
    · rcases k with k | ⟨e', he', k⟩
      · exact hy.2.2.1 k
      · exact hy.2.2.2 e' he' k
  case a1 =>
    intro e
    rcases rs y e with e' | e'
    · have := rcs y e'; omega
    · omega
  case a2 =>
    intro e he h
    have := hy.2.1.resolve_right (ng y)
    rcases R e he y h with ⟨_, r⟩ | ⟨k, _⟩ | ⟨_, r⟩
    · omega
    · rcases k with k | ⟨e', he', k⟩
      · exact hy.2.2.1 k
      · exact hy.2.2.2 e' he' k
    · omega
  case c0 =>
    have := hy.2.1
    simp only [sixGenL_re] at this
    rcases this with e | e
    · omega
    · exact e.elim
  case c1 =>
    intro e
    rcases rs y e with e' | e'
    · exact hy.2.2.1 e'
    · omega
  case c2 =>
    intro e he h
    have := hy.2.1
    simp only [sixGenL_re] at this
    have hy2 : g2.re ≤ y := this.resolve_right (fun e => e)
    rcases R e he y h with ⟨k, _⟩ | ⟨_, r⟩ | ⟨_, r⟩
    · exact hy.2.2.2 e k h
    · omega
    · omega
  case w0 =>
    rcases hy.2.1 with e | e
    · have := rcs y e; omega
    · exact e.elim
  case w2 =>
    intro e he h
    have hx : NMem xc.laz.sure.ned y := hy.2.1.resolve_right (fun e => e)
    have := rcs y hx
    rcases R e he y h with ⟨k, _⟩ | ⟨_, r⟩ | ⟨_, r⟩
    · exact Fc.apart e k y hx h
    · omega
    · omega
  case hsure =>
    rcases rs y hy with e | e
    · have := rcs y e; exact Or.inl (by omega)
    · exact Or.inl (by omega)
  case es =>
    rcases R e he y hy with ⟨_, r⟩ | ⟨_, r⟩ | ⟨_, r⟩
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inl r.1
  case ed =>
    rcases K e he with k | k | k | k | k
    · exact Fc.edist e k
    · subst k; exact Fa.dist
    · exact Fa.edist e k
    · subst k; exact Fb.dist
    · exact Fb.edist e k
  case ap =>
    rcases rs y hy with e' | e'
    · have := rcs y e'
      rcases R e he y h with ⟨k, _⟩ | ⟨_, r⟩ | ⟨_, r⟩
      · exact Fc.apart e k y e' h
      · omega
      · omega
    · rcases R e he y h with ⟨_, r⟩ | ⟨_, r⟩ | ⟨_, r⟩
      · omega
      · omega
      · omega

/-! ## `%6` under a fork-free `%next` -/

/-- **`+fork-sure` writes the parameters of the join**, which are the
registers of the sure need forked; the two fork blocks write nothing. -/
theorem wroteIn_forkSure {Q : Nat → Prop} {sur : Sure S} {o : Nat} {g g' : Gen Map} {s0 s1 : Sure S}
    (h : forkSure sur o g.bo (g.bo + 1) { g with bo := g.bo + 2 } = some ((s0, s1), g')) (hd : g.drop = false)
    (hq : ∀ x, NMem sur.ned x → Q x) : WroteIn Q g g' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hb0, hb1, hb2, hold⟩ := forkSure_spec h hd
  have oth := forkSure_other h hd
  intro k b' hb
  by_cases h0 : k < g.bo
  · rw [hold k h0] at hb; exact WroteIn.refl Q g k b' hb
  by_cases e0 : k = g.bo
  · rw [e0, hb0] at hb; cases hb; exact Or.inr (blobWr_fin _ _)
  by_cases e1 : k = g.bo + 1
  · rw [e1, hb1] at hb; cases hb; exact Or.inr (blobWr_fin _ _)
  by_cases e2 : k = g.bo + 2
  · rw [e2, hb2] at hb; cases hb
    exact Or.inr ⟨fun x hx => hq x ((mem_flatten _ x).mp hx), opsWr_nil Q⟩
  · rw [oth k (by omega)] at hb; exact WroteIn.refl Q g k b' hb

/-- A state with the same blocks writes nothing. -/
theorem wroteIn_sameBlocks {Q : Nat → Prop} {g g' : Gen Map} (h : SameBlocks g g') : WroteIn Q g g' :=
  fun o b' hb => by rw [h.2.2.2.2.2.2 o] at hb; exact WroteIn.refl Q g o b' hb

/-- **`%6` for a fork-free `%next`**: `+fork-sure` writes the join's
parameters, the goal's need, which the result needs nowhere; the branches
`b` and `a` write registers they allocate or the copies `s1` and `s0`,
which lie in registers fresh for the run and apart; `+sect` changes no
block; the test `c` and the `+copy` write as in `footX_sixP`. -/
theorem footX_sixN {c a b : Nomm} (hcp : c.pure = true) (ihc : FootX S Map c) (iha : FootX S Map a)
    (ihb : FootX S Map b) (kc : KeepX S Map c) (ka : KeepX S Map a) (kb : KeepX S Map b)
    {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g9 : Gen Map} {nex : NextL S}
    (hd : g0.drop = false) (hg : GoalIn g0.re (CGoal.next sur th))
    (hc : sixCount c + sixCount a + sixCount b + 1 ≤ 255)
    (h : runL (Nomm.n6 c a b) (CGoal.toL (CGoal.next sur th)) region g0 = some (nex, g9)) :
    FootR g0 g9 (CGoal.next sur th) nex := by
  simp only [CGoal.toL] at h
  rw [runL_n6_next, sixNextL_ofSure] at h
  obtain ⟨s0, s1, x1, x0, xc, lz, yes, nuh, gF, gR, gQ, gS, gC, hF, hR, hQ, hS, hC, hrest⟩ :=
    sixNextSimple_apart hcp h
  obtain ⟨_, _, _, _, d0, d1, j01, hreg, hle, hbo, hdrop, hcond, _, hb0, hb1, hb2, hold⟩ := forkSure_spec hF hd
  have kF : Keeps g0 gF := by
    refine ⟨fun lo hl o b' l u hb' => ?_, hle, hdrop, by omega⟩
    by_cases h0 : o < g0.bo
    · rw [hold o h0] at hb'
      exact (hl o b' l h0 hb').mono fun _ e => Nat.lt_of_lt_of_le e hle
    by_cases e0 : o = g0.bo
    · rw [e0, hb0] at hb'; cases hb'
      exact blobIn_fin (f := Termin.hop _) (jmpIn_flatten fun x hx => (hreg x (Or.inl hx)).2)
    by_cases e1 : o = g0.bo + 1
    · rw [e1, hb1] at hb'; cases hb'
      exact blobIn_fin (f := Termin.hop _) (jmpIn_flatten fun x hx => (hreg x (Or.inr hx)).2)
    by_cases e2 : o = g0.bo + 2
    · rw [e2, hb2] at hb'; cases hb'
      exact ⟨fun x hx => Nat.lt_of_lt_of_le (hg.1 x ((mem_flatten _ x).mp hx)) hle, RegsIn.nil _, jmpIn_jmp0 _ _⟩
    · omega
  have dF := kF.dropF hd
  have gb : GoalIn ({ gF with id := gF.id + 1 } : Gen Map).re (CGoal.next s1 (jmp0 (g0.bo + 1))) :=
    ⟨fun x hx => (hreg x (Or.inr hx)).2, jmpIn_jmp0 _ _⟩
  have Rb := kb (goal := CGoal.next s1 (jmp0 (g0.bo + 1))) (g0 := { gF with id := gF.id + 1 }) dF gb
    (by omega) hR
  have Fb := ihb (goal := CGoal.next s1 (jmp0 (g0.bo + 1))) (g0 := { gF with id := gF.id + 1 }) dF gb d1
    (by omega) hR
  have d1' := Rb.keeps.dropF dF
  have lR : gF.re ≤ gR.re := Rb.keeps.le
  have ga : GoalIn gR.re (CGoal.next s0 (jmp0 g0.bo)) :=
    ⟨fun x hx => Nat.lt_of_lt_of_le (hreg x (Or.inl hx)).2 lR, jmpIn_jmp0 _ _⟩
  have Ra := ka (goal := CGoal.next s0 (jmp0 g0.bo)) d1' ga (by omega) hQ
  have Fa := iha (goal := CGoal.next s0 (jmp0 g0.bo)) d1' ga d0 (by omega) hQ
  have d2 := Ra.keeps.dropF d1'
  have cR : gR.cond = gF.cond := Rb.cnd
  rw [cR] at hS
  obtain ⟨ey, en, _, _, el, hsb⟩ := sect_spec d2 (Ra.cnd.trans cR) hS
  obtain ⟨kG, _⟩ := keeps_sixGenL (region := gF.id :: region) d2 Ra.out.2
    (Rb.out.2.mono fun _ e => Nat.lt_of_lt_of_le e Ra.keeps.le)
  have kS := kG.trans (keeps_same hsb)
  have bS : gS.bo = gQ.bo + 2 := by rw [hsb.2.1]; simp
  have reS : gS.re = gQ.re := by rw [hsb.1]; simp
  have gc : GoalIn gS.re (CGoal.pick (jmp0 yes) (jmp0 nuh) : CGoal S) := ⟨jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩
  have Rc := kc (goal := CGoal.pick (jmp0 yes) (jmp0 nuh)) (kS.dropF d2) gc (by omega) hC
  have Fc := ihc (goal := CGoal.pick (jmp0 yes) (jmp0 nuh)) (kS.dropF d2) gc trivial (by omega) hC
  subst el
  have hbig : lazyBig (mk (Sure.bunt : Sure S) [((gQ.bo, x0.laz), (gQ.bo + 1, x1.laz))] []) = false := by
    apply lazyBig_entries
    rw [entries_six]; simp only [List.length_append, List.length_cons]
    have := Ra.size; have := Rb.size; simp only [lazyMax]; omega
  subst ey en
  have h4 := hrest hbig
  have d3 := Rc.keeps.dropF (kS.dropF d2)
  have lQ := Ra.keeps.le
  have lC := Rc.keeps.le
  obtain ⟨n, hcp', rfl⟩ := copyL_apart_some
    (fun e he e' he' => by
      have := (Rc.labs _ (fork_in_entries he)).1
      rw [fork_mk, List.mem_singleton] at he'
      subst he'
      simp only
      omega)
    (fun e he e' he' => by rw [bond_mk] at he'; cases he') h4
  obtain ⟨WC, sC, dC, l9⟩ := foot_copy (b := (Sure.bunt : Sure S)) d3 Rc.out.2 Fc.dist trivial
    (fun _ _ e => e.elim) Rc.out.1.1 (nb_none _) hcp'
  -- the ranges of the registers
  have rcs : ∀ y, NMem xc.laz.sure.ned y → gS.re ≤ y ∧ y < gC.re := fun y hy =>
    ⟨(Fc.sure y hy).resolve_right (fun e => e), Rc.out.1.1 y hy⟩
  have rce : ∀ e ∈ entries xc.laz, ∀ y, NMem e.2.sure.ned y → gS.re ≤ y ∧ y < gC.re := fun e he y hy =>
    ⟨(Fc.esure e he y hy).resolve_right (fun e => e), Rc.out.1.2 e he y hy⟩
  have ra : ∀ y, NMem x0.laz.sure.ned y → (gR.re ≤ y ∨ NMem s0.ned y) ∧ y < gQ.re := fun y hy =>
    ⟨Fa.sure y hy, Ra.out.1.1 y hy⟩
  have rae : ∀ e ∈ entries x0.laz, ∀ y, NMem e.2.sure.ned y → (gR.re ≤ y ∨ NMem s0.ned y) ∧ y < gQ.re :=
    fun e he y hy => ⟨Fa.esure e he y hy, Ra.out.1.2 e he y hy⟩
  have rb : ∀ y, NMem x1.laz.sure.ned y → (gF.re ≤ y ∨ NMem s1.ned y) ∧ y < gR.re := fun y hy =>
    ⟨Fb.sure y hy, Rb.out.1.1 y hy⟩
  have rbe : ∀ e ∈ entries x1.laz, ∀ y, NMem e.2.sure.ned y → (gF.re ≤ y ∨ NMem s1.ned y) ∧ y < gR.re :=
    fun e he y hy => ⟨Fb.esure e he y hy, Rb.out.1.2 e he y hy⟩
  have rs : ∀ y, NMem n.laz.ned y → NMem xc.laz.sure.ned y ∨ gC.re ≤ y := fun y hy => by
    rcases sC y hy with e | e | e
    · exact Or.inl e
    · exact e.elim
    · exact Or.inr e
  -- the five kinds of entries
  have K : ∀ e ∈ entries (mk n.laz (xc.laz.fork ++ [((gQ.bo, x0.laz), (gQ.bo + 1, x1.laz))]) (xc.laz.bond ++ [])),
      e ∈ entries xc.laz ∨ e = (gQ.bo, x0.laz) ∨ e ∈ entries x0.laz ∨ e = (gQ.bo + 1, x1.laz) ∨
        e ∈ entries x1.laz :=
    fun e he => by
      have := (entries_side_perm n.laz xc.laz
        (mk (Sure.bunt : Sure S) [((gQ.bo, x0.laz), (gQ.bo + 1, x1.laz))] [])).mem_iff.mp
        (by simpa only [fork_mk, bond_mk] using he)
      rw [entries_six] at this
      simp only [List.mem_append, List.mem_cons] at this
      rcases this with e1 | (e1 | e1) | (e1 | e1)
      · exact Or.inl e1
      · exact Or.inr (Or.inl e1)
      · exact Or.inr (Or.inr (Or.inl e1))
      · exact Or.inr (Or.inr (Or.inr (Or.inl e1)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr e1)))
  -- every register of an entry lies in one of the three ranges, with its kind
  have R : ∀ e ∈ entries (mk n.laz (xc.laz.fork ++ [((gQ.bo, x0.laz), (gQ.bo + 1, x1.laz))]) (xc.laz.bond ++ [])),
      ∀ y, NMem e.2.sure.ned y → (e ∈ entries xc.laz ∧ gS.re ≤ y ∧ y < gC.re) ∨
        ((NMem x0.laz.sure.ned y ∨ ∃ e' ∈ entries x0.laz, NMem e'.2.sure.ned y) ∧
          (gR.re ≤ y ∨ NMem s0.ned y) ∧ y < gQ.re) ∨
        ((NMem x1.laz.sure.ned y ∨ ∃ e' ∈ entries x1.laz, NMem e'.2.sure.ned y) ∧
          (gF.re ≤ y ∨ NMem s1.ned y) ∧ y < gR.re) :=
    fun e he y hy => by
      rcases K e he with k | k | k | k | k
      · exact Or.inl ⟨k, rce e k y hy⟩
      · subst k; exact Or.inr (Or.inl ⟨Or.inl hy, ra y hy⟩)
      · exact Or.inr (Or.inl ⟨Or.inr ⟨e, k, hy⟩, rae e k y hy⟩)
      · subst k; exact Or.inr (Or.inr ⟨Or.inl hy, rb y hy⟩)
      · exact Or.inr (Or.inr ⟨Or.inr ⟨e, k, hy⟩, rbe e k y hy⟩)
  -- every register of an entry is at or above `g0.re`, and those of the branches' below `gS.re`
  have R0 : ∀ e ∈ entries (mk n.laz (xc.laz.fork ++ [((gQ.bo, x0.laz), (gQ.bo + 1, x1.laz))]) (xc.laz.bond ++ [])),
      ∀ y, NMem e.2.sure.ned y → g0.re ≤ y := fun e he y hy => by
    rcases R e he y hy with ⟨_, r, _⟩ | ⟨_, r | r, _⟩ | ⟨_, r | r, _⟩
    · omega
    · omega
    · exact (hreg y (Or.inl r)).1
    · omega
    · exact (hreg y (Or.inr r)).1
  refine ⟨(wroteIn_forkSure hF hd fun x hx => ?fk).trans ((wroteIn_same (g := gF) rfl).trans
    ((Fb.wr.mono fun y hy => ⟨by omega, Or.inl ?b0, ?b1, ?b2⟩).trans
    ((Fa.wr.mono fun y hy => ⟨by omega, Or.inl ?a0, ?a1, ?a2⟩).trans
    ((wroteIn_sixGenL _ _ _ _).trans ((wroteIn_sameBlocks hsb).trans
    ((Fc.wr.mono fun y hy => ⟨by omega, Or.inl ?c0, ?c1, ?c2⟩).trans
    (WC.mono fun y hy => ⟨by omega, Or.inl ?w0, hy.2.2, ?w2⟩))))))), fun y hy => ?hsure, dC,
    fun e he y hy => Or.inl (R0 e he y hy), fun e he => ?ed, fun e he y hy h => ?ap⟩
  case fk =>
    have := hg.1 x hx
    refine ⟨by omega, Or.inr hx, fun e => ?_, fun e he h => ?_⟩
    · rcases rs x e with e' | e'
      · have := rcs x e'; omega
      · omega
    · have := R0 e he x h; omega
  case b0 =>
    rcases hy.2.1 with e | e
    · exact Nat.le_trans hle e
    · exact (hreg y (Or.inr e)).1
  case b1 =>
    intro e
    rcases rs y e with e' | e'
    · have := rcs y e'; have := hy.1; omega
    · have := hy.1; omega
  case b2 =>
    intro e he h
    have hy1 := hy.1
    rcases R e he y h with ⟨_, r, _⟩ | ⟨_, r | r, _⟩ | ⟨k, _⟩
    · omega
    · omega
    · rcases hy.2.1 with e' | e'
      · have e'' : gF.re ≤ y := e'
        have := (hreg y (Or.inl r)).2; omega
      · exact j01 y r e'
    · rcases k with k | ⟨e', he', k⟩
      · exact hy.2.2.1 k
      · exact hy.2.2.2 e' he' k
  case a0 =>
    rcases hy.2.1 with e | e
    · omega
    · exact (hreg y (Or.inl e)).1
  case a1 =>
    intro e
    rcases rs y e with e' | e'
    · have := rcs y e'; have := hy.1; omega
    · have := hy.1; omega
  case a2 =>
    intro e he h
    have hy1 := hy.1
    rcases R e he y h with ⟨_, r, _⟩ | ⟨k, _⟩ | ⟨_, r, r'⟩
    · omega
    · rcases k with k | ⟨e', he', k⟩
      · exact hy.2.2.1 k
      · exact hy.2.2.2 e' he' k
    · rcases hy.2.1 with e' | e'
      · omega
      · have := (hreg y (Or.inl e')).2
        rcases r with r | r
        · omega
        · exact j01 y e' r
  case c0 =>
    have := hy.2.1
    rcases this with e | e
    · omega
    · exact e.elim
  case c1 =>
    intro e
    rcases rs y e with e' | e'
    · exact hy.2.2.1 e'
    · have := hy.1; omega
  case c2 =>
    intro e he h
    have hy2 : gS.re ≤ y := hy.2.1.resolve_right (fun e => e)
    rcases R e he y h with ⟨k, _⟩ | ⟨_, _, r⟩ | ⟨_, _, r⟩
    · exact hy.2.2.2 e k h
    · omega
    · omega
  case w0 =>
    rcases hy.2.1 with e | e
    · have := rcs y e; omega
    · exact e.elim
  case w2 =>
    intro e he h
    have hx : NMem xc.laz.sure.ned y := hy.2.1.resolve_right (fun e => e)
    have := rcs y hx
    rcases R e he y h with ⟨k, _⟩ | ⟨_, _, r⟩ | ⟨_, _, r⟩
    · exact Fc.apart e k y hx h
    · omega
    · omega
  case hsure =>
    rcases rs y hy with e | e
    · have := rcs y e; exact Or.inl (by omega)
    · exact Or.inl (by omega)
  case ed =>
    rcases K e he with k | k | k | k | k
    · exact Fc.edist e k
    · subst k; exact Fa.dist
    · exact Fa.edist e k
    · subst k; exact Fb.dist
    · exact Fb.edist e k
  case ap =>
    rcases rs y hy with e' | e'
    · have := rcs y e'
      rcases R e he y h with ⟨k, _⟩ | ⟨_, _, r⟩ | ⟨_, _, r⟩
      · exact Fc.apart e k y e' h
      · omega
      · omega
    · rcases R e he y h with ⟨_, _, r⟩ | ⟨_, _, r⟩ | ⟨_, _, r⟩
      · omega
      · omega
      · omega

/-! ## The induction -/

/-- **Fact (i) on `FragX`, given the case `%6` under a fork-free `%next`**:
every run of a nomm of `FragX` with at most 255 `%6` for a fork-free goal
whose registers are below `re` and whose need is distinct, from a state that
does not drop, meets `FootR`, when every `%6` of `FragX` whose parts meet it
does under a `%next`.  The cases `%done` and `%pick` of `%6` are
`footX_sixP`. -/
theorem runX_foot_of
    (h6 : ∀ {c a b : Nomm}, FragX (S := S) c → FragX (S := S) a → FragX (S := S) b →
      FootX S Map c → FootX S Map a → FootX S Map b →
      ∀ {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
        g0.drop = false → GoalIn g0.re (CGoal.next sur th) → Distinct sur.ned →
        sixCount (Nomm.n6 c a b) ≤ 255 →
        runL (Nomm.n6 c a b) (CGoal.toL (CGoal.next sur th)) region g0 = some (nex, g1) →
        FootR g0 g1 (CGoal.next sur th) nex)
    {nm : Nomm} (hf : FragX (S := S) nm) : FootX S Map nm := by
  induction hf with
  | frag hf => exact footX_frag hf
  | @six c a b hc ha hb ihc iha ihb =>
    intro goal region g0 g1 nex hd hg hD hcount h
    have hcp := fragX_pure hc
    have hc'' : sixCount c + sixCount a + sixCount b + 1 ≤ 255 := by simpa only [sixCount] using hcount
    have kc : KeepX S Map c := runX_keeps hc
    have ka : KeepX S Map a := runX_keeps ha
    have kb : KeepX S Map b := runX_keeps hb
    cases goal with
    | next sur th => exact h6 hc ha hb ihc iha ihb hd hg hD hcount h
    | done => exact footX_sixP (goal := CGoal.done) hcp ihc iha ihb kc ka kb trivial hd hg hD hc'' h
    | pick z o => exact footX_sixP (goal := CGoal.pick z o) hcp ihc iha ihb kc ka kb trivial hd hg hD hc'' h
  | four hp ih => exact footX_four ih (runX_keeps hp)
  | three hp ih => exact footX_three ih (runX_keeps hp)
  | seven hq hp ih => exact footX_seven hq ih (runX_keeps hp)
  | cons hp hq ihp ihq => exact footX_cons ihp ihq (runX_keeps hp) (runX_keeps hq) (fragX_pure hp) (fragX_pure hq)
  | five hp hq ihp ihq => exact footX_five ihp ihq (runX_keeps hp) (runX_keeps hq) (fragX_pure hp)
  | ten hv hq ihv ihq => exact footX_ten ihv ihq (runX_keeps hv) (runX_keeps hq) (fragX_pure hv) (fragX_pure hq)
  | sevenFrom ha _ ihq => exact footX_sevenFrom ha ihq

/-- **Fact (i) on `FragX`**: every run of a nomm of `FragX` with at most 255
`%6` for a fork-free goal whose registers are below `re` and whose need is
distinct, from a state that does not drop, meets `FootR`. -/
theorem runX_foot {nm : Nomm} (hf : FragX (S := S) nm) : FootX S Map nm :=
  runX_foot_of (fun hc ha hb ihc iha ihb => fun hd hg _ hcount h =>
    footX_sixN (fragX_pure hc) ihc iha ihb (runX_keeps hc) (runX_keeps ha) (runX_keeps hb) hd hg
      (by simpa only [sixCount] using hcount) h) hf

end Comp
end SkaModel
end Formalization
