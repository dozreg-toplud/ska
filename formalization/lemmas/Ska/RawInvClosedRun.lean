import lemmas.Ska.RawInvClosed

/-!
# Raw `+comp` output: `run_closed`, case by case

README Gaps 14.  `ClosedIH` for every nomm (`run_closed`): the blocks a run
of `run` makes jump only to blocks it made or to its goal's targets, and its
entry is one of them.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

theorem closed_of {goal : CGoal S} {g0 g1 : Comp.Gen Map} {nex : Next S} (C : CS g0.bo (GTgt goal) g1)
    (he : g0.bo ≤ nex.th.there ∨ GTgt goal nex.th.there) :
    ClosedR g0.bo (GTgt goal) g1.blocks ∧ (g0.bo ≤ nex.th.there ∨ GTgt goal nex.th.there) := ⟨C.cl, he⟩

theorem closed_n0 (ax : Nat) : ClosedIH S Map (Nomm.n0 ax) := by
  intro goal g0 g1 nex hd h1 hj hc hr
  have C0 : CS g0.bo (GTgt goal) g0 := cs_start hc hd h1
  simp only [run] at hr
  by_cases a0 : ax = 0
  · rw [if_pos a0] at hr
    obtain ⟨C, e⟩ := cs_bomb C0 hr
    exact closed_of C (Or.inl e)
  rw [if_neg a0] at hr
  obtain ⟨nx, g2, h2, hr⟩ := bind_some hr
  obtain ⟨C2, e2⟩ := cs_simpleNext C0 h2
  by_cases a1 : ax = 1
  · rw [if_pos a1] at hr
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact closed_of C2 e2
  rw [if_neg a1] at hr
  cases ef : «from» ax nx.laz with
  | none => rw [ef] at hr; cases hr
  | some laz =>
    rw [ef] at hr
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact closed_of C2 e2

theorem closed_n1 (k : Noun) : ClosedIH S Map (Nomm.n1 k) := by
  intro goal g0 g1 nex hd h1 hj hc hr
  have C0 : CS g0.bo (GTgt goal) g0 := cs_start hc hd h1
  cases goal with
  | done =>
    simp only [run] at hr
    obtain ⟨r, g2, h2, hr⟩ := bind_some hr
    obtain ⟨q2, b2, -, -⟩ := quiet_of_re h2
    obtain ⟨o, g3, h3, hr⟩ := bind_some hr
    obtain ⟨C3, rfl, -, -⟩ := cs_emit (cs_quiet C0 q2) (none_ok rfl) h3
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact closed_of C3 (Or.inl (by simp [jmp0]; omega))
  | pick z o =>
    simp only [run] at hr
    by_cases e0 : k = A 0
    · rw [if_pos e0] at hr
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact closed_of C0 (Or.inr (Or.inl rfl))
    rw [if_neg e0] at hr
    by_cases e1 : k = A 1
    · rw [if_pos e1] at hr
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact closed_of C0 (Or.inr (Or.inr rfl))
    rw [if_neg e1] at hr
    obtain ⟨C, e⟩ := cs_bomb C0 hr
    exact closed_of C (Or.inl e)
  | next laz th =>
    simp only [run] at hr
    obtain ⟨o, g2, h2, hr⟩ := bind_some hr
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨C2, e2⟩ := cs_mede C0 (Or.inr rfl) h2
    exact closed_of C2 (Or.inl (by simpa [jmp0] using e2))

theorem closed_n7 {p q : Nomm} (ihp : ClosedIH S Map p) (ihq : ClosedIH S Map q) : ClosedIH S Map (Nomm.n7 p q) := by
  intro goal g0 g1 nex hd h1 hj hc hr
  have C0 : CS g0.bo (GTgt goal) g0 := cs_start hc hd h1
  simp only [run] at hr
  obtain ⟨nq, g2, h2, hr⟩ := bind_some hr
  obtain ⟨C2, e2, l2, u2⟩ := cs_run ihq C0 hj (fun t e => Or.inr e) h2
  obtain ⟨C1, e1, -, -⟩ := cs_run (goal := CGoal.next nq.laz nq.th) ihp C2 (gj_next l2 u2) (gtgt_next e2) hr
  exact closed_of C1 e1

/-- The tail of `%3` and `%4`: a block, then the operand for a fresh register. -/
theorem cs_tail {lo : Nat} {T : Nat → Prop} {p : Nomm} (ihp : ClosedIH S Map p) {g g1 g2 : Comp.Gen Map} {b : Blob}
    {o x : Nat} {nex : Next S} (h : CS lo T g) (hb : ∀ j ∈ getJmps b.fin, lo ≤ j.there ∨ T j.there)
    (he : (emit b : CM Map Nat) g = some (o, g1))
    (hr : run p (CGoal.next (lazyReg x) (jmp0 o)) g1 = some (nex, g2)) :
    CS lo T g2 ∧ (lo ≤ nex.th.there ∨ T nex.th.there) := by
  obtain ⟨C1, rfl, b1, -⟩ := cs_emit h hb he
  obtain ⟨C2, e2, -, -⟩ := cs_run ihp C1 (gj_next (by simp [jmp0]; exact h.bo1) (by simp [jmp0]; omega))
    (gtgt_next (Or.inl (by simp [jmp0]; exact h.le))) hr
  exact ⟨C2, e2⟩

theorem two_ok {lo : Nat} {T : Nat → Prop} {f : Termin} {z o : Jmp} (hf : getJmps f = [z, o])
    (hz : lo ≤ z.there ∨ T z.there) (ho : lo ≤ o.there ∨ T o.there) :
    ∀ j ∈ getJmps f, lo ≤ j.there ∨ T j.there := by
  intro j hj; rw [hf] at hj; simp at hj; rcases hj with rfl | rfl
  · exact hz
  · exact ho

theorem closed_n4 {p : Nomm} (ihp : ClosedIH S Map p) : ClosedIH S Map (Nomm.n4 p) := by
  intro goal g0 g1 nex hd h1 hj hc hr
  have C0 : CS g0.bo (GTgt goal) g0 := cs_start hc hd h1
  cases goal with
  | done =>
    simp only [run] at hr
    obtain ⟨pro, g2, h2, hr⟩ := bind_some hr
    obtain ⟨q2, -, -, -⟩ := quiet_of_re h2
    obtain ⟨arg, g3, h3, hr⟩ := bind_some hr
    obtain ⟨q3, -, -, -⟩ := quiet_of_re h3
    obtain ⟨o, g4, h4, hr⟩ := bind_some hr
    obtain ⟨C, e⟩ := cs_tail ihp (cs_quiet (cs_quiet C0 q2) q3) (none_ok rfl) h4 hr
    exact closed_of C e
  | pick z o =>
    simp only [run] at hr
    obtain ⟨pro, g2, h2, hr⟩ := bind_some hr
    obtain ⟨q2, -, -, -⟩ := quiet_of_re h2
    obtain ⟨arg, g3, h3, hr⟩ := bind_some hr
    obtain ⟨q3, -, -, -⟩ := quiet_of_re h3
    obtain ⟨o', g4, h4, hr⟩ := bind_some hr
    obtain ⟨C, e⟩ := cs_tail ihp (cs_quiet (cs_quiet C0 q2) q3) (two_ok rfl (Or.inr (Or.inl rfl))
      (Or.inr (Or.inr rfl))) h4 hr
    exact closed_of C e
  | next laz th =>
    simp only [run] at hr
    obtain ⟨a, g2, h2, hr⟩ := bind_some hr
    obtain ⟨C2, ta⟩ := cs_collapse C0 (Or.inr rfl) h2
    obtain ⟨⟨pro, th'⟩, g3, h3, hr⟩ := bind_some hr
    have P : CS g0.bo (GTgt (CGoal.next laz th)) g3 ∧ (g0.bo ≤ th' ∨ GTgt (CGoal.next laz th) th') := by
      cases a with
      | some x =>
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
        obtain ⟨rfl, rfl⟩ := h3
        exact ⟨C2, ta _ _ rfl⟩
      | none =>
        simp only at h3
        obtain ⟨r, g4, h4, h3⟩ := bind_some h3
        obtain ⟨q4, -, -, -⟩ := quiet_of_re h4
        split at h3
        · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h3
          exact ⟨cs_quiet C2 q4, Or.inr rfl⟩
        · cases h3
    obtain ⟨C3, t3⟩ := P
    obtain ⟨arg, g4, h4, hr⟩ := bind_some hr
    obtain ⟨q4, -, -, -⟩ := quiet_of_re h4
    obtain ⟨o, g5, h5, hr⟩ := bind_some hr
    obtain ⟨C, e⟩ := cs_tail ihp (cs_quiet C3 q4) (hop_ok (t := jmp0 th') (by simpa [jmp0] using t3)) h5 hr
    exact closed_of C e

theorem closed_n3 {p : Nomm} (ihp : ClosedIH S Map p) : ClosedIH S Map (Nomm.n3 p) := by
  intro goal g0 g1 nex hd h1 hj hc hr
  have C0 : CS g0.bo (GTgt goal) g0 := cs_start hc hd h1
  cases goal with
  | done =>
    simp only [run] at hr
    obtain ⟨⟨o0, o1⟩, g2, h2, hr⟩ := bind_some hr
    obtain ⟨C2, l0, l1, -, -⟩ := cs_doneBlocks C0 h2
    obtain ⟨r, g3, h3, hr⟩ := bind_some hr
    obtain ⟨q3, -, -, -⟩ := quiet_of_re h3
    obtain ⟨oc, g4, h4, hr⟩ := bind_some hr
    obtain ⟨C, e⟩ := cs_tail ihp (cs_quiet C2 q3) (two_ok rfl (Or.inl (by simpa [jmp0] using l0))
      (Or.inl (by simpa [jmp0] using l1))) h4 hr
    exact closed_of C e
  | pick z o =>
    simp only [run] at hr
    obtain ⟨r, g3, h3, hr⟩ := bind_some hr
    obtain ⟨q3, -, -, -⟩ := quiet_of_re h3
    obtain ⟨oc, g4, h4, hr⟩ := bind_some hr
    obtain ⟨C, e⟩ := cs_tail ihp (cs_quiet C0 q3) (two_ok rfl (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))) h4 hr
    exact closed_of C e
  | next laz th =>
    simp only [run] at hr
    by_cases hne : noneEquivalent laz = true
    · rw [if_pos hne] at hr
      exact ihp _ g0 g1 nex hd h1 hj hc hr
    rw [if_neg hne] at hr
    obtain ⟨a, g2, h2, hr⟩ := bind_some hr
    obtain ⟨C2, ta⟩ := cs_collapse C0 (Or.inr rfl) h2
    cases a with
    | none => cases hr
    | some x =>
      obtain ⟨r, o⟩ := x
      simp only at hr
      obtain ⟨⟨z, o'⟩, g3, h3, hr⟩ := bind_some hr
      obtain ⟨C3, lz, lo', -, -⟩ := cs_forl C2 (ta r o rfl) h3
      obtain ⟨r', g4, h4, hr⟩ := bind_some hr
      obtain ⟨q4, -, -, -⟩ := quiet_of_re h4
      obtain ⟨oc, g5, h5, hr⟩ := bind_some hr
      obtain ⟨C, e⟩ := cs_tail ihp (cs_quiet C3 q4) (two_ok rfl (Or.inl (by simpa [jmp0] using lz))
        (Or.inl (by simpa [jmp0] using lo'))) h5 hr
      exact closed_of C e

/-- The two runs and the copy of cons, `%5`, `%10`. -/
theorem cs_bin {lo : Nat} {T : Nat → Prop} {p q : Nomm} (ihp : ClosedIH S Map p) (ihq : ClosedIH S Map q)
    {hs ts : Sure S} {j : Jmp} {g2 g3 g4 g1 : Comp.Gen Map} {nex2 nex1 nex : Next S} (h : CS lo T g2)
    (hj1 : 1 ≤ j.there) (hj : j.there < g2.bo) (ht : lo ≤ j.there ∨ T j.there)
    (h3 : run q (CGoal.next ts j) g2 = some (nex2, g3))
    (h4 : run p (CGoal.next hs nex2.th) g3 = some (nex1, g4))
    (h5 : copy nex1 nex2.laz g4 = some (nex, g1)) : CS lo T g1 ∧ (lo ≤ nex.th.there ∨ T nex.th.there) := by
  obtain ⟨C3, e3, l3, u3⟩ := cs_run ihq h (gj_next hj1 hj) (gtgt_next ht) h3
  obtain ⟨C4, e4, -, -⟩ := cs_run ihp C3 (gj_next l3 u3) (gtgt_next e3) h4
  obtain ⟨C1, e1, -⟩ := cs_copy C4 e4 h5
  exact ⟨C1, Or.inl e1⟩

theorem closed_consNext {lo : Nat} {T : Nat → Prop} {p q : Nomm} (ihp : ClosedIH S Map p)
    (ihq : ClosedIH S Map q) {laz : Sure S} {th : Jmp} {g0 g1 : Comp.Gen Map} {nex : Next S} (h : CS lo T g0)
    (ht : lo ≤ th.there ∨ T th.there)
    (hr : (do
      let (hed, tel, o) ← Comp.split ⟨laz, th⟩
      let nexh ← past noCode ⟨hed, jmp0 o⟩ q
      let nex2 ← run q (CGoal.next tel nexh.th)
      let nex2 ← past noCode nex2 p
      let nex1 ← run p (CGoal.next nexh.laz nex2.th)
      copy nex1 nex2.laz : CM Map (Next S)) g0 = some (nex, g1)) :
    CS lo T g1 ∧ (lo ≤ nex.th.there ∨ T nex.th.there) := by
  obtain ⟨⟨hed, tel, o⟩, g2, h2, hr⟩ := bind_some hr
  obtain ⟨C2, eo, b2⟩ := cs_split h ht h2
  simp only at eo; subst eo
  obtain ⟨nexh, g2', hph, hr⟩ := bind_some hr
  obtain ⟨rfl, rfl⟩ := past_some hph
  obtain ⟨nex2, g3, h3, hr⟩ := bind_some hr
  obtain ⟨nex2', g3', hp2, hr⟩ := bind_some hr
  obtain ⟨rfl, rfl⟩ := past_some hp2
  obtain ⟨nex1, g4, h4, hr⟩ := bind_some hr
  exact cs_bin ihp ihq C2 (by simp [jmp0]; exact h.bo1) (by simp [jmp0]; omega)
    (Or.inl (by simp [jmp0]; exact h.le)) h3 h4 hr

theorem closed_cons {p q : Nomm} (ihp : ClosedIH S Map p) (ihq : ClosedIH S Map q) :
    ClosedIH S Map (Nomm.cons p q) := by
  intro goal g0 g1 nex hd h1 hj hc hr
  have C0 : CS g0.bo (GTgt goal) g0 := cs_start hc hd h1
  cases goal with
  | done =>
    simp only [run] at hr
    obtain ⟨gl, g2, h2, hr⟩ := bind_some hr
    obtain ⟨r, g3, h3, h2⟩ := bind_some h2
    obtain ⟨q3, -, -, -⟩ := quiet_of_re h3
    obtain ⟨o, g4, h4, h2⟩ := bind_some h2
    obtain ⟨C4, rfl, b4, -⟩ := cs_emit (cs_quiet C0 q3) (none_ok rfl) h4
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    simp only at hr
    obtain ⟨C, e⟩ := closed_consNext (th := jmp0 g3.bo) ihp ihq C4 (Or.inl (by simp [jmp0]; have := q3.2; omega)) hr
    exact closed_of C e
  | next laz th =>
    simp only [run, bind_apply, pure_apply, Option.bind_some] at hr
    obtain ⟨C, e⟩ := closed_consNext ihp ihq C0 (Or.inr rfl) hr
    exact closed_of C e
  | pick z o =>
    simp only [run, bind_apply, pure_apply, Option.bind_some] at hr
    obtain ⟨⟨o', g2⟩, h2, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨C2, rfl, b2, -⟩ := cs_emit C0 (none_ok rfl) h2
    obtain ⟨⟨nex2, g3⟩, h3, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨⟨nex2', g3'⟩, hp, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨rfl, rfl⟩ := past_some hp
    obtain ⟨⟨nex1, g4⟩, h4, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨C, e⟩ := cs_bin (j := jmp0 g0.bo) ihp ihq C2 (by simp [jmp0]; exact h1) (by simp [jmp0]; omega)
      (Or.inl (by simp [jmp0])) h3 h4 hr
    exact closed_of C e

theorem closed_n5 {p q : Nomm} (ihp : ClosedIH S Map p) (ihq : ClosedIH S Map q) :
    ClosedIH S Map (Nomm.n5 p q) := by
  intro goal g0 g1 nex hd h1 hj hc hr
  have C0 : CS g0.bo (GTgt goal) g0 := cs_start hc hd h1
  simp only [run] at hr
  obtain ⟨rp, g2, h2, hr⟩ := bind_some hr
  obtain ⟨q2, -, -, -⟩ := quiet_of_re h2
  obtain ⟨rq, g3, h3, hr⟩ := bind_some hr
  obtain ⟨q3, -, -, -⟩ := quiet_of_re h3
  have C3 := cs_quiet (cs_quiet C0 q2) q3
  obtain ⟨o, g4, h4, hr⟩ := bind_some hr
  have H : CS g0.bo (GTgt goal) g4 ∧ g0.bo ≤ o ∧ o < g4.bo := by
    cases goal with
    | pick z o' =>
      simp only at h4
      obtain ⟨C4, rfl, b4, -⟩ := cs_emit C3 (two_ok rfl (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))) h4
      exact ⟨C4, C3.le, by omega⟩
    | done =>
      simp only at h4
      obtain ⟨⟨o0, o1⟩, g5, h5, h4⟩ := bind_some h4
      obtain ⟨C5, l0, l1, -, -⟩ := cs_doneBlocks C3 h5
      obtain ⟨C4, rfl, b4, -⟩ := cs_emit C5 (two_ok rfl (Or.inl (by simpa [jmp0] using l0))
        (Or.inl (by simpa [jmp0] using l1))) h4
      exact ⟨C4, C5.le, by omega⟩
    | next laz th =>
      simp only at h4
      obtain ⟨a, g5, h5, h4⟩ := bind_some h4
      obtain ⟨C5, ta⟩ := cs_collapse C3 (Or.inr rfl) h5
      cases a with
      | none =>
        simp only at h4
        split at h4
        · obtain ⟨C4, rfl, b4, -⟩ := cs_emit C5 (hop_ok (T := GTgt (CGoal.next laz th)) (t := jmp0 th.there)
            (Or.inr (show GTgt (CGoal.next laz th) (jmp0 th.there).there from rfl))) h4
          exact ⟨C4, C5.le, by omega⟩
        · cases h4
      | some x =>
        obtain ⟨r, o'⟩ := x
        simp only at h4
        obtain ⟨⟨z, o''⟩, g6, h6, h4⟩ := bind_some h4
        obtain ⟨C6, lz, lo', -, -⟩ := cs_forl C5 (ta r o' rfl) h6
        obtain ⟨C4, rfl, b4, -⟩ := cs_emit C6 (two_ok rfl (Or.inl (by simpa [jmp0] using lz))
          (Or.inl (by simpa [jmp0] using lo'))) h4
        exact ⟨C4, C6.le, by omega⟩
  obtain ⟨C4, lo4, hi4⟩ := H
  obtain ⟨nexq, g5, h5, hr⟩ := bind_some hr
  obtain ⟨nexq', g5', hp, hr⟩ := bind_some hr
  obtain ⟨rfl, rfl⟩ := past_some hp
  obtain ⟨nexp, g6, h6, hr⟩ := bind_some hr
  obtain ⟨C, e⟩ := cs_bin (j := jmp0 o) ihp ihq C4 (by simp [jmp0]; omega) (by simp [jmp0]; omega)
    (Or.inl (by simpa [jmp0] using lo4)) h5 h6 hr
  exact closed_of C e

theorem closed_n10 (a : Nat) {v q : Nomm} (ihv : ClosedIH S Map v) (ihq : ClosedIH S Map q) :
    ClosedIH S Map (Nomm.n10 a v q) := by
  intro goal g0 g1 nex hd h1 hj hc hr
  have C0 : CS g0.bo (GTgt goal) g0 := cs_start hc hd h1
  simp only [run] at hr
  obtain ⟨nx, g2, h2, hr⟩ := bind_some hr
  obtain ⟨C2, e2⟩ := cs_simpleNext C0 h2
  obtain ⟨⟨don, rec, o⟩, g3, h3, hr⟩ := bind_some hr
  obtain ⟨C3, eo, b3⟩ := cs_into C2 e2 h3
  simp only at eo; subst eo
  obtain ⟨nexR, g3', hpr, hr⟩ := bind_some hr
  obtain ⟨rfl, rfl⟩ := past_some hpr
  obtain ⟨nexDon, g4, h4, hr⟩ := bind_some hr
  obtain ⟨nexDon', g4', hpd, hr⟩ := bind_some hr
  obtain ⟨rfl, rfl⟩ := past_some hpd
  obtain ⟨nexRec, g5, h5, hr⟩ := bind_some hr
  obtain ⟨C, e⟩ := cs_bin (j := jmp0 g2.bo) ihq ihv C3 (by simp [jmp0]; exact C2.bo1) (by simp [jmp0]; omega)
    (Or.inl (by simp [jmp0]; exact C2.le)) h4 h5 hr
  exact closed_of C e

/-- **`run_closed`**: every run's code jumps only into itself or to its
goal's targets. -/
theorem run_closed : ∀ nm : Nomm, ClosedIH S Map nm := by
  intro nm
  induction nm with
  | n0 ax => exact closed_n0 ax
  | n1 k => exact closed_n1 k
  | n7 p q ihp ihq => exact closed_n7 ihp ihq
  | n4 p ih => exact closed_n4 ih
  | n3 p ih => exact closed_n3 ih
  | n5 p q ihp ihq => exact closed_n5 ihp ihq
  | cons p q ihp ihq => exact closed_cons ihp ihq
  | n10 a v q ihv ihq => exact closed_n10 a ihv ihq
  | n2 => intro goal g0 g1 nex _ _ _ _ h; simp only [run] at h; cases h
  | n6 => intro goal g0 g1 nex _ _ _ _ h; simp only [run] at h; cases h
  | n11s => intro goal g0 g1 nex _ _ _ _ h; simp only [run] at h; cases h
  | n11d => intro goal g0 g1 nex _ _ _ _ h; simp only [run] at h; cases h
  | n12 => intro goal g0 g1 nex _ _ _ _ h; simp only [run] at h; cases h
  | mean => intro goal g0 g1 nex _ _ _ _ h; simp only [run] at h; cases h

end Raw
end SkaModel
end Formalization
