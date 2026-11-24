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
`foot_copy`), `footX_sevenFrom`.  `FootR.pre` puts code in front of a run
and widens its goal.
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

end Comp
end SkaModel
end Formalization
