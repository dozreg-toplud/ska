import lemmas.Ska.CompFootRun

/-!
# Fact (i) for `run`: the case cons

The footprint of cons (`Foot`, `CompFootRun.lean`), for every goal.

* `copyNeed_dist`: the copy of two distinct needs that are apart and below
  `re` is distinct (no `Clean` needed, unlike `CopyOK.sem`).
* `wr_splitNeedS`: `+split-need` writes only registers of the need it splits
  that are in neither half (the top register of a `%this` or `%both`).
* `foot_copyTail`: the two runs and the `+copy` of a cons, from the
  footprints of the two runs: the code of `p` writes no register of `q`'s
  result, since those were allocated before `p` ran or are `q`'s goal's,
  which is apart from `p`'s goal's.
* `foot_cons`: the case cons of `run_foot_of`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

theorem distinct_consNeed {a b : Need} (da : Distinct a) (db : Distinct b) (ab : ∀ y, NMem a y → ¬ NMem b y) :
    Distinct (consNeed a b) := by
  unfold consNeed; split
  · trivial
  · exact ⟨da, db, ab⟩

/-- Two results apart: the first in `P1` or fresh in `[lo, mid)`, the second
in `P2` or fresh from `mid` on. -/
theorem apart_two {res1 res2 P1 P2 : Nat → Prop} {lo mid : Nat} (hlm : lo ≤ mid)
    (m1 : ∀ y, res1 y → P1 y ∨ (lo ≤ y ∧ y < mid)) (m2 : ∀ y, res2 y → P2 y ∨ mid ≤ y)
    (l1 : ∀ y, P1 y → y < lo) (l2 : ∀ y, P2 y → y < lo) (d : ∀ y, P1 y → ¬ P2 y) : ∀ y, res1 y → ¬ res2 y := by
  intro y h1 h2
  rcases m1 y h1 with e1 | e1 <;> rcases m2 y h2 with e2 | e2
  · exact d y e1 e2
  · have := l1 y e1; omega
  · have := l2 y e2; omega
  · omega

theorem copy_mem {l r : Need} {ops : List Pole} {g g' : Gen Map} {x : Need × List Pole}
    (h : copyNeed l r ops g = some (x, g')) :
    g.re ≤ g'.re ∧ ∀ y, NMem x.1 y → (NMem l y ∨ NMem r y) ∨ (g.re ≤ y ∧ y < g'.re) := by
  obtain ⟨_, _, c⟩ := copyNeed_spec _ _ _ _ _ _ h
  exact ⟨c.le, c.mem⟩

/-- **The copy of two distinct needs apart and below `re` is distinct.** -/
theorem copyNeed_dist : ∀ (a b : Need) (ops : List Pole) (g g' : Gen Map) (x : Need × List Pole),
    copyNeed a b ops g = some (x, g') → Distinct (Need.pair a b) → NB g.re a → NB g.re b → Distinct x.1 := by
  intro a
  induction a with
  | none =>
    intro b ops g g' x h dab _ _
    simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact dab.2.1
  | this rl =>
    intro b ops g g' x h dab ha hb
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; trivial
    | this rr =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; trivial
    | both xr hr tr =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact dab.2.1
    | pair p q =>
      simp only [copyNeed, bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨dp, dq, apq⟩ := dab.2.1
      exact ⟨dp, dq, apq, fun e => Nat.lt_irrefl _ (hb _ (Or.inl e)), fun e => Nat.lt_irrefl _ (hb _ (Or.inr e))⟩
  | pair pl ql ihp ihq =>
    intro b ops g g' x h dab ha hb
    obtain ⟨⟨dpl, dql, apq⟩, db, ab⟩ := dab
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨dpl, dql, apq⟩
    | this rr =>
      simp only [copyNeed, bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨dpl, dql, apq, fun e => Nat.lt_irrefl _ (ha _ (Or.inl e)), fun e => Nat.lt_irrefl _ (ha _ (Or.inr e))⟩
    | pair pr qr =>
      obtain ⟨dpr, dqr, apr⟩ := db
      simp only [copyNeed] at h
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨l1, m1⟩ := copy_mem h1
      obtain ⟨_, m2⟩ := copy_mem h2
      have d1 := ihp _ _ _ _ _ h1 ⟨dpl, dpr, fun y hy => ab y (Or.inl hy) ∘ Or.inl⟩
        (fun y hy => ha y (Or.inl hy)) (fun y hy => hb y (Or.inl hy))
      have d2 := ihq _ _ _ _ _ h2 ⟨dql, dqr, fun y hy => ab y (Or.inr hy) ∘ Or.inr⟩
        (fun y hy => Nat.lt_of_lt_of_le (ha y (Or.inr hy)) l1) (fun y hy => Nat.lt_of_lt_of_le (hb y (Or.inr hy)) l1)
      refine distinct_consNeed d1 d2 (apart_two (lo := g.re) (mid := g1.re) l1 m1
        (fun y hy => (m2 y hy).imp id (fun e => e.1)) (fun y hy => hy.elim (fun e => ha y (Or.inl e)) (fun e => hb y (Or.inl e)))
        (fun y hy => hy.elim (fun e => ha y (Or.inr e)) (fun e => hb y (Or.inr e))) ?_)
      rintro y (e | e) (e' | e')
      · exact apq y e e'
      · exact ab y (Or.inl e) (Or.inr e')
      · exact ab y (Or.inr e') (Or.inl e)
      · exact apr y e e'
    | both xr hr tr =>
      obtain ⟨dhr, dtr, aht, nh, nt⟩ := db
      simp only [copyNeed] at h
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨l1, m1⟩ := copy_mem h1
      obtain ⟨_, m2⟩ := copy_mem h2
      have hx : xr < g.re := hb xr (Or.inl rfl)
      have d1 := ihp _ _ _ _ _ h1 ⟨dpl, dhr, fun y hy => ab y (Or.inl hy) ∘ Or.inr ∘ Or.inl⟩
        (fun y hy => ha y (Or.inl hy)) (fun y hy => hb y (Or.inr (Or.inl hy)))
      have d2 := ihq _ _ _ _ _ h2 ⟨dql, dtr, fun y hy => ab y (Or.inr hy) ∘ Or.inr ∘ Or.inr⟩
        (fun y hy => Nat.lt_of_lt_of_le (ha y (Or.inr hy)) l1)
        (fun y hy => Nat.lt_of_lt_of_le (hb y (Or.inr (Or.inr hy))) l1)
      refine ⟨d1, d2, apart_two (lo := g.re) (mid := g1.re) l1 m1 (fun y hy => (m2 y hy).imp id (fun e => e.1))
        (fun y hy => hy.elim (fun e => ha y (Or.inl e)) (fun e => hb y (Or.inr (Or.inl e))))
        (fun y hy => hy.elim (fun e => ha y (Or.inr e)) (fun e => hb y (Or.inr (Or.inr e)))) ?_, fun e => ?_, fun e => ?_⟩
      · rintro y (e | e) (e' | e')
        · exact apq y e e'
        · exact ab y (Or.inl e) (Or.inr (Or.inr e'))
        · exact ab y (Or.inr e') (Or.inr (Or.inl e))
        · exact aht y e e'
      · rcases m1 xr e with (e' | e') | e'
        · exact ab xr (Or.inl e') (Or.inl rfl)
        · exact nh e'
        · omega
      · rcases m2 xr e with (e' | e') | e'
        · exact ab xr (Or.inr e') (Or.inl rfl)
        · exact nt e'
        · omega
  | both rl hl tl ihh iht =>
    intro b ops g g' x h dab ha hb
    obtain ⟨⟨dhl, dtl, ahl, nhl, ntl⟩, db, ab⟩ := dab
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨dhl, dtl, ahl, nhl, ntl⟩
    | this rr =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨dhl, dtl, ahl, nhl, ntl⟩
    | pair pr qr =>
      obtain ⟨dpr, dqr, apr⟩ := db
      simp only [copyNeed] at h
      obtain ⟨xr, g0', h0, h⟩ := bind_some h
      simp only [re_apply, Option.some.injEq, Prod.mk.injEq] at h0
      obtain ⟨rfl, rfl⟩ := h0
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have s : ∀ y, y < g.re → y < g.re + 1 := fun _ e => Nat.lt_succ_of_lt e
      obtain ⟨l1, m1⟩ := copy_mem h1
      obtain ⟨_, m2⟩ := copy_mem h2
      simp only at l1 m1
      have d1 := ihh _ _ _ _ _ h1 ⟨dhl, dpr, fun y hy => ab y (Or.inr (Or.inl hy)) ∘ Or.inl⟩
        (fun y hy => s _ (ha y (Or.inr (Or.inl hy)))) (fun y hy => s _ (hb y (Or.inl hy)))
      have d2 := iht _ _ _ _ _ h2 ⟨dtl, dqr, fun y hy => ab y (Or.inr (Or.inr hy)) ∘ Or.inr⟩
        (fun y hy => Nat.lt_of_lt_of_le (s _ (ha y (Or.inr (Or.inr hy)))) l1)
        (fun y hy => Nat.lt_of_lt_of_le (s _ (hb y (Or.inr hy))) l1)
      refine ⟨d1, d2, apart_two (lo := g.re + 1) (mid := g1.re) l1 m1 (fun y hy => (m2 y hy).imp id (fun e => e.1))
        (fun y hy => hy.elim (fun e => s _ (ha y (Or.inr (Or.inl e)))) (fun e => s _ (hb y (Or.inl e))))
        (fun y hy => hy.elim (fun e => s _ (ha y (Or.inr (Or.inr e)))) (fun e => s _ (hb y (Or.inr e)))) ?_,
        fun e => ?_, fun e => ?_⟩
      · rintro y (e | e) (e' | e')
        · exact ahl y e e'
        · exact ab y (Or.inr (Or.inl e)) (Or.inr e')
        · exact ab y (Or.inr (Or.inr e')) (Or.inl e)
        · exact apr y e e'
      · rcases m1 _ e with (e' | e') | e'
        · have := ha _ (Or.inr (Or.inl e')); omega
        · have := hb _ (Or.inl e'); omega
        · omega
      · rcases m2 _ e with (e' | e') | e'
        · have := ha _ (Or.inr (Or.inr e')); omega
        · have := hb _ (Or.inr e'); omega
        · omega
    | both xr hr tr =>
      obtain ⟨dhr, dtr, aht, nh, nt⟩ := db
      simp only [copyNeed] at h
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨l1, m1⟩ := copy_mem h1
      obtain ⟨_, m2⟩ := copy_mem h2
      have hx : xr < g.re := hb xr (Or.inl rfl)
      have d1 := ihh _ _ _ _ _ h1 ⟨dhl, dhr, fun y hy => ab y (Or.inr (Or.inl hy)) ∘ Or.inr ∘ Or.inl⟩
        (fun y hy => ha y (Or.inr (Or.inl hy))) (fun y hy => hb y (Or.inr (Or.inl hy)))
      have d2 := iht _ _ _ _ _ h2 ⟨dtl, dtr, fun y hy => ab y (Or.inr (Or.inr hy)) ∘ Or.inr ∘ Or.inr⟩
        (fun y hy => Nat.lt_of_lt_of_le (ha y (Or.inr (Or.inr hy))) l1)
        (fun y hy => Nat.lt_of_lt_of_le (hb y (Or.inr (Or.inr hy))) l1)
      refine ⟨d1, d2, apart_two (lo := g.re) (mid := g1.re) l1 m1 (fun y hy => (m2 y hy).imp id (fun e => e.1))
        (fun y hy => hy.elim (fun e => ha y (Or.inr (Or.inl e))) (fun e => hb y (Or.inr (Or.inl e))))
        (fun y hy => hy.elim (fun e => ha y (Or.inr (Or.inr e))) (fun e => hb y (Or.inr (Or.inr e)))) ?_,
        fun e => ?_, fun e => ?_⟩
      · rintro y (e | e) (e' | e')
        · exact ahl y e e'
        · exact ab y (Or.inr (Or.inl e)) (Or.inr (Or.inr e'))
        · exact ab y (Or.inr (Or.inr e')) (Or.inr (Or.inl e))
        · exact aht y e e'
      · rcases m1 xr e with (e' | e') | e'
        · exact ab xr (Or.inr (Or.inl e')) (Or.inl rfl)
        · exact nh e'
        · omega
      · rcases m2 xr e with (e' | e') | e'
        · exact ab xr (Or.inr (Or.inr e')) (Or.inl rfl)
        · exact nt e'
        · omega

/-- **`+split-need` writes only registers of its need in neither half.** -/
theorem wr_splitNeedS {ned : Need} {o : Nat} {g g' : Gen Map} {x : Need × Need} (dn : Distinct ned)
    (hn : NB g.re ned) (h : splitNeed ned o g = some (x, g')) :
    WroteIn (fun y => NMem ned y ∧ ¬ NMem x.1 y ∧ ¬ NMem x.2 y) g g' := by
  cases ned with
  | pair p q =>
    simp only [splitNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact WroteIn.refl _ _
  | none =>
    simp only [splitNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact WroteIn.refl _ _
  | this r =>
    simp only [splitNeed] at h
    obtain ⟨hh, g1, h1, h⟩ := bind_some h
    obtain ⟨e1, q1, _⟩ := keeps_re h1
    obtain ⟨t, g2, h2, h⟩ := bind_some h
    obtain ⟨e2, q2, _⟩ := keeps_re h2
    obtain ⟨u, g3, h3, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hr : r < g.re := hn r rfl
    exact (wroteIn_re h1).trans ((wroteIn_re h2).trans (wroteIn_addOps (opsWr_one (p := Pole.con hh t r)
      (fun y hy => by
        simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hy
        subst hy
        refine ⟨rfl, ?_, ?_⟩ <;> simp only [NMem] <;> omega)) h3))
  | both r hd tl =>
    obtain ⟨_, _, _, nh, nt⟩ := dn
    simp only [splitNeed] at h
    obtain ⟨⟨r1, n1⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨⟨r2, n2⟩, g2, h2, h⟩ := bind_some h
    obtain ⟨u, g3, h3, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hr : r < g.re := hn r (Or.inl rfl)
    obtain ⟨_, l1, m1, _⟩ := must_spec h1
    obtain ⟨_, _, m2, _⟩ := must_spec h2
    exact (wr_must _ h1).trans ((wr_must _ h2).trans (wroteIn_addOps (opsWr_one (p := Pole.con r1 r2 r)
      (fun y hy => by
        simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hy
        subst hy
        refine ⟨Or.inl rfl, fun e => ?_, fun e => ?_⟩
        · rcases m1 _ e with e' | e'
          · exact nh e'
          · omega
        · rcases m2 _ e with e' | e'
          · exact nt e'
          · omega)) h3))

/-- **The two runs and the `+copy` of a cons** (and of `%5`, `%10`): `q`
runs first for `ts`, `p` second for `hs`, and `+copy` joins the two results.
The footprint lies in the registers allocated from `g2` on and those of the
two needs, which are apart and below `g2.re`. -/
theorem foot_copyTail {p q : Nomm} (ihp : FootIH S Map p) (ihq : FootIH S Map q) {hs ts : Sure S} {j : Jmp}
    {g2 g3 g4 g1 : Gen Map} {nex2 nex1 nex : Next S}
    (hd : g2.drop = false) (nh : NB g2.re hs.ned) (nt : NB g2.re ts.ned) (dh : Distinct hs.ned)
    (dt : Distinct ts.ned) (ap : ∀ x, NMem hs.ned x → ¬ NMem ts.ned x) (hj : JmpIn (· < g2.re) j)
    (h3 : run q (CGoal.next ts j) g2 = some (nex2, g3))
    (h4 : run p (CGoal.next hs nex2.th) g3 = some (nex1, g4))
    (h5 : copy nex1 nex2.laz g4 = some (nex, g1)) :
    WroteIn (fun x => x < g1.re ∧ (g2.re ≤ x ∨ NMem hs.ned x ∨ NMem ts.ned x) ∧ ¬ NMem nex.laz.ned x) g2 g1 ∧
    (∀ x, NMem nex.laz.ned x → g2.re ≤ x ∨ NMem hs.ned x ∨ NMem ts.ned x) ∧ Distinct nex.laz.ned ∧
    g2.re ≤ g1.re ∧ g1.drop = false := by
  have gq : GoalIn g2.re (CGoal.next ts j) := ⟨nt, hj⟩
  obtain ⟨k3, n3⟩ := run_keeps q _ _ _ _ hd gq h3
  have Fq := ihq _ _ _ _ hd gq dt h3
  have d3 := k3.dropF hd
  have gp : GoalIn g3.re (CGoal.next hs nex2.th) := ⟨nh.mono k3.le, n3.2⟩
  obtain ⟨k4, n4⟩ := run_keeps p _ _ _ _ d3 gp h4
  have Fp := ihp _ _ _ _ d3 gp dh h4
  have d4 := k4.dropF d3
  have l3 := k3.le
  have l4 := k4.le
  simp only [copy] at h5
  obtain ⟨o, g5, h50, h5⟩ := bind_some h5
  obtain ⟨k5, q5⟩ := keeps_emit d4 (blobIn_fin (f := Termin.hop nex1.th) n4.2) h50
  obtain ⟨laz, g6, h6, h5⟩ := bind_some h5
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h5
  obtain ⟨rfl, rfl⟩ := h5
  simp only [copyLazy] at h6
  obtain ⟨⟨n1, o1⟩, g7, h7, h6⟩ := bind_some h6
  obtain ⟨u, g8, h8, h6⟩ := bind_some h6
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h6
  obtain ⟨rfl, rfl⟩ := h6
  have s2 : ∀ y, NMem nex2.laz.ned y → g2.re ≤ y ∨ NMem ts.ned y := Fq.sure
  have s1 : ∀ y, NMem nex1.laz.ned y → g3.re ≤ y ∨ NMem hs.ned y := Fp.sure
  have a12 : ∀ y, NMem nex1.laz.ned y → ¬ NMem nex2.laz.ned y := fun y e1 e2 => by
    have := n3.1 y e2
    rcases s1 y e1 with e | e
    · omega
    · rcases s2 y e2 with e' | e'
      · have := nh y e; omega
      · exact ap y e e'
  have dpair : Distinct (Need.pair nex1.laz.ned nex2.laz.ned) := ⟨Fp.dist, Fq.dist, a12⟩
  have nb1 : NB g5.re nex1.laz.ned := by rw [q5]; exact n4.1
  have nb2 : NB g5.re nex2.laz.ned := by rw [q5]; exact n3.1.mono k4.le
  obtain ⟨A, eA, wA⟩ := wr_copyNeed _ _ _ _ _ _ h7 dpair nb1 nb2
  have dres := copyNeed_dist _ _ _ _ _ _ h7 dpair nb1 nb2
  obtain ⟨_, _, c7⟩ := copyNeed_spec _ _ _ _ _ _ h7
  have m7 := c7.mem
  have l7 := c7.le
  have q8 := (addOps_re h8).1
  have d8 : g8.drop = false := by rw [(addOps_re h8).2.1, c7.gen]; exact (k5.dropF d4)
  simp only at eA wA dres m7
  have no1 : ∀ y, y < g3.re → (g2.re ≤ y ∨ NMem ts.ned y) → ¬ NMem nex2.laz.ned y → ¬ NMem n1 y := fun y hy hm hn e => by
    rcases m7 y e with (e' | e') | e'
    · rcases s1 y e' with e'' | e''
      · omega
      · rcases hm with hm | hm
        · have := nh y e''; omega
        · exact ap y e'' hm
    · exact hn e'
    · omega
  have no2 : ∀ y, y < g4.re → (g3.re ≤ y ∨ NMem hs.ned y) → ¬ NMem nex1.laz.ned y → ¬ NMem n1 y := fun y hy hm hn e => by
    rcases m7 y e with (e' | e') | e'
    · exact hn e'
    · have := n3.1 y e'
      rcases hm with hm | hm
      · omega
      · rcases s2 y e' with e'' | e''
        · have := nh y hm; omega
        · exact ap y hm e''
    · omega
  have wC : OpsWr (fun y => y < g8.re ∧ (g2.re ≤ y ∨ NMem hs.ned y ∨ NMem ts.ned y) ∧ ¬ NMem n1 y) o1 := by
    rw [eA, List.append_nil]
    refine wA.mono fun y hy => ⟨?_, ?_, hy.2⟩
    · rcases hy.1 with e | e
      · have := n4.1 y e; omega
      · have := n3.1 y e; omega
    · rcases hy.1 with e | e
      · exact (s1 y e).elim (fun e => Or.inl (by omega)) (fun e => Or.inr (Or.inl e))
      · exact (s2 y e).imp id Or.inr
  have sure : ∀ x, NMem n1 x → g2.re ≤ x ∨ NMem hs.ned x ∨ NMem ts.ned x := fun x hx => by
    rcases m7 x hx with (e | e) | e
    · exact (s1 x e).elim (fun e => Or.inl (by omega)) (fun e => Or.inr (Or.inl e))
    · exact (s2 x e).imp id Or.inr
    · exact Or.inl (by omega)
  exact ⟨(Fq.wr.mono fun x hx => ⟨by omega, hx.2.1.imp id Or.inr, no1 x hx.1 hx.2.1 hx.2.2⟩).trans
    ((Fp.wr.mono fun x hx => ⟨by omega, hx.2.1.elim (fun e => Or.inl (by omega)) (fun e => Or.inr (Or.inl e)),
      no2 x hx.1 hx.2.1 hx.2.2⟩).trans ((wroteIn_emit (blobWr_fin _ _) h50).trans
      ((wroteIn_of_gen c7.gen).trans (wroteIn_addOps wC h8)))),
    sure, dres, by omega, d8⟩
/-- **`+split` writes only registers of the goal's need in neither half**,
and returns two distinct halves apart, of the goal's registers and fresh
ones. -/
theorem split_foot {laz : Sure S} {th : Jmp} {g g' : Gen Map} {x : Sure S × Sure S × Nat} (hd : g.drop = false)
    (dn : Distinct laz.ned) (hn : NB g.re laz.ned) (hj : JmpIn (· < g.re) th)
    (h : Comp.split ⟨laz, th⟩ g = some (x, g')) :
    WroteIn (fun y => NMem laz.ned y ∧ ¬ NMem x.1.ned y ∧ ¬ NMem x.2.1.ned y) g g' ∧
    Distinct x.1.ned ∧ Distinct x.2.1.ned ∧ (∀ y, NMem x.1.ned y → ¬ NMem x.2.1.ned y) ∧
    (∀ y, NMem x.1.ned y → NMem laz.ned y ∨ g.re ≤ y) ∧ (∀ y, NMem x.2.1.ned y → NMem laz.ned y ∨ g.re ≤ y) := by
  simp only [Comp.split] at h
  obtain ⟨o, g0, h0, h⟩ := bind_some h
  obtain ⟨k0, q0⟩ := keeps_emit hd (blobIn_fin (f := Termin.hop th) hj) h0
  obtain ⟨⟨sh, st⟩, g1, h2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [splitSure] at h2
  obtain ⟨⟨lh, lt⟩, _, h2⟩ := Option.bind_eq_some_iff.mp h2
  obtain ⟨⟨⟨nh, nt⟩, g2⟩, h3, h4⟩ := Option.map_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
  have hn0 : NB g0.re laz.ned := by rw [q0]; exact hn
  obtain ⟨_, _, _, _, m1, m2, D, _⟩ := splitNeed_spec h3
  obtain ⟨d1, d2, a12, _⟩ := D dn hn0
  refine ⟨(wroteIn_emit (blobWr_fin _ _) h0).trans (wr_splitNeedS dn hn0 h3), d1, d2, a12,
    fun y hy => (m1 y hy).imp id fun e => by omega, fun y hy => (m2 y hy).imp id fun e => by omega⟩

/-- **The case cons for a goal `%next`.** -/
theorem foot_consNext {p q : Nomm} (ihp : FootIH S Map p) (ihq : FootIH S Map q)
    {laz : Sure S} {th : Jmp} {g0 g1 : Gen Map} {nex : Next S} (hd : g0.drop = false) (hg : NB g0.re laz.ned)
    (hj : JmpIn (· < g0.re) th) (hD : Distinct laz.ned)
    (h : (do
      let (hed, tel, o) ← Comp.split ⟨laz, th⟩
      let nexh ← past noCode ⟨hed, jmp0 o⟩ q
      let nex2 ← run q (CGoal.next tel nexh.th)
      let nex2 ← past noCode nex2 p
      let nex1 ← run p (CGoal.next nexh.laz nex2.th)
      copy nex1 nex2.laz : CM Map (Next S)) g0 = some (nex, g1)) : Foot g0 g1 (CGoal.next laz th) nex := by
  obtain ⟨⟨hed, tel, o⟩, g2, h2, h⟩ := bind_some h
  obtain ⟨k2, nh, nt⟩ := keeps_split hd hg hj h2
  obtain ⟨W2, dh, dt, ap, mh, mt⟩ := split_foot hd hD hg hj h2
  simp only at W2 dh dt ap mh mt nh nt
  obtain ⟨nexh, g2', hph, h⟩ := bind_some h
  obtain ⟨rfl, rfl⟩ := past_some hph
  obtain ⟨nex2, g3, h3, h⟩ := bind_some h
  obtain ⟨nex2', g3', hp2, h⟩ := bind_some h
  obtain ⟨rfl, rfl⟩ := past_some hp2
  obtain ⟨nex1, g4, h4, h⟩ := bind_some h
  obtain ⟨WT, sT, dT, lT, _⟩ := foot_copyTail ihp ihq (k2.dropF hd) nh nt dh dt ap (jmpIn_jmp0 _ _) h3 h4 h
  have l2 := k2.le
  have A1 : ∀ y, NMem laz.ned y ∧ ¬ NMem hed.ned y ∧ ¬ NMem tel.ned y → ¬ NMem nex.laz.ned y := fun y hy e => by
    rcases sT y e with e' | e' | e'
    · have := hg y hy.1; omega
    · exact hy.2.1 e'
    · exact hy.2.2 e'
  have A2 : ∀ y, (g2.re ≤ y ∨ NMem hed.ned y ∨ NMem tel.ned y) → g0.re ≤ y ∨ NMem laz.ned y := fun y hy => by
    rcases hy with e | e | e
    · exact Or.inl (by omega)
    · exact (mh y e).symm
    · exact (mt y e).symm
  exact ⟨(W2.mono fun y hy => ⟨by have := hg y hy.1; omega, Or.inr hy.1, A1 y hy⟩).trans
    (WT.mono fun y hy => ⟨hy.1, A2 y hy.2.1, hy.2.2⟩), fun y hy => A2 y (sT y hy), dT⟩

/-- **Fact (i) of cons**, for every goal. -/
theorem foot_cons {p q : Nomm} (ihp : FootIH S Map p) (ihq : FootIH S Map q) : FootIH S Map (Nomm.cons p q) := by
  intro goal g g' nex hd hg hD h
  cases goal with
  | done =>
    simp only [run] at h
    obtain ⟨gl, g1, h1, h⟩ := bind_some h
    obtain ⟨r, g2, h2, h1⟩ := bind_some h1
    obtain ⟨e2, q2, k2⟩ := keeps_re h2
    obtain ⟨o, g3, h3, h1⟩ := bind_some h1
    obtain ⟨k3, q3⟩ := keeps_emit (k2.dropF hd) (blobIn_fin (f := Termin.don r) (show r < g2.re by omega)) h3
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    simp only at h
    have F := foot_consNext (laz := lazyReg r) ihp ihq ((k2.trans k3).dropF hd) (nb_this (by omega))
      (jmpIn_jmp0 _ _) trivial h
    have a : ∀ x, (g3.re ≤ x ∨ GMem (CGoal.next (lazyReg r : Sure S) (jmp0 o)) x) → g.re ≤ x ∨ GMem (CGoal.done : CGoal S) x :=
      fun x hx => by
        rcases hx with e | e
        · exact Or.inl (by omega)
        · exact Or.inl (by simp only [GMem, lazyReg, NMem] at e; omega)
    exact ⟨((wroteIn_re h2).trans (wroteIn_emit (blobWr_fin _ _) h3)).trans
      (F.wr.mono fun x hx => ⟨hx.1, a x hx.2.1, hx.2.2⟩), fun x hx => a x (F.sure x hx), F.dist⟩
  | next laz th =>
    simp only [run, bind_apply, pure_apply, Option.bind_some] at h
    exact foot_consNext ihp ihq hd hg.1 hg.2 hD h
  | pick z o =>
    simp only [run, bind_apply, pure_apply, Option.bind_some] at h
    obtain ⟨⟨o', g1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨k1, q1⟩ := keeps_emit hd (blobIn_fin (f := Termin.bom Option.none) trivial) h1
    have d1 := k1.dropF hd
    obtain ⟨⟨nex2, g3⟩, h3, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨nex2', g3'⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rfl, rfl⟩ := past_some hp
    obtain ⟨⟨nex1, g4⟩, h4, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨WT, sT, dT, lT, _⟩ := foot_copyTail (hs := Sure.bunt) (ts := Sure.bunt) ihp ihq d1 (nb_none _) (nb_none _)
      trivial trivial (fun _ e => e.elim) (jmpIn_jmp0 _ _) h3 h4 h
    have a : ∀ x, (g1.re ≤ x ∨ NMem (Sure.bunt : Sure S).ned x ∨ NMem (Sure.bunt : Sure S).ned x) →
        g.re ≤ x ∨ GMem (CGoal.pick z o : CGoal S) x := fun x hx => by
      rcases hx with e | e | e
      · exact Or.inl (by omega)
      · exact e.elim
      · exact e.elim
    exact ⟨(wroteIn_emit (blobWr_fin _ _) h1).trans (WT.mono fun x hx => ⟨hx.1, a x hx.2.1, hx.2.2⟩),
      fun x hx => a x (sT x hx), dT⟩

/-- **Fact (i) of `[5 p q]`**, for every goal: the block that compares the
two fresh registers writes fresh registers and the goal's need (through
`+collapse-lazy-atom` and `+forl` under `%next`), then the two runs and the
copy as for cons. -/
theorem foot_n5 {p q : Nomm} (ihp : FootIH S Map p) (ihq : FootIH S Map q) : FootIH S Map (Nomm.n5 p q) := by
  intro goal g g' nex hd hg hD h
  simp only [run] at h
  obtain ⟨rp, g1, h1, h⟩ := bind_some h
  obtain ⟨e1, q1, k1⟩ := keeps_re h1
  obtain ⟨rq, g2, h2, h⟩ := bind_some h
  obtain ⟨e2, q2, k2⟩ := keeps_re h2
  have d2 := (k1.trans k2).dropF hd
  have kk : ∀ x, x < g.re → x < g2.re := fun x hx => by omega
  obtain ⟨o, g3, h3, h⟩ := bind_some h
  have P : Keeps g2 g3 ∧ WroteIn (fun x => x < g3.re ∧ (g2.re ≤ x ∨ GMem goal x)) g2 g3 := by
    cases goal with
    | pick z o =>
      exact ⟨(keeps_emit d2 (blobIn_fin (f := Termin.eqq rp rq z o)
        ⟨show rp < g2.re by omega, show rq < g2.re by omega, hg.1.mono kk, hg.2.mono kk⟩) h3).1,
        wroteIn_emit (blobWr_fin _ _) h3⟩
    | done =>
      obtain ⟨⟨o0, o1⟩, g4, h4, h3⟩ := bind_some h3
      have k4 := keeps_doneBlocks d2 h4
      have k5 := (keeps_emit (k4.dropF d2) (blobIn_fin (f := Termin.eqq rp rq (jmp0 o0) (jmp0 o1))
          ⟨show rp < g4.re by have := k4.le; omega, show rq < g4.re by have := k4.le; omega,
            jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩) h3).1
      have l5 := k5.le
      exact ⟨k4.trans k5, ((wr_doneBlocks h4).mono fun x hx => by
        rcases hx with e | e
        · exact e.elim
        · exact ⟨by omega, Or.inl e.1⟩).trans (wroteIn_emit (blobWr_fin _ _) h3)⟩
    | next laz th =>
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
          exact ⟨k4.trans k5, (w4.mono fun x hx => by
            rcases hx with e | e
            · exact ⟨by have := hg.1 x e; omega, Or.inr e⟩
            · exact ⟨by omega, Or.inl e.1⟩).trans (wroteIn_emit (blobWr_one (p := Pole.equ rp rq) _
              (fun x hx => by simp [poleWr] at hx)) h3)⟩
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
        refine ⟨k4.trans (k5.trans k6), ((w4.mono bnd).trans ((wr_forl h5).mono fun x hx => ?_)).trans
          (wroteIn_emit (blobWr_fin _ _) h3)⟩
        rcases hx with e | e
        · simp only [NMem] at e; rw [e]; exact bnd r (rr4 r o rfl)
        · exact ⟨by omega, Or.inl (by omega)⟩
  obtain ⟨k3, W3⟩ := P
  have l3 := k3.le
  have d3 := k3.dropF d2
  obtain ⟨nexq, g4, h4, h⟩ := bind_some h
  obtain ⟨nexq', g4', hp, h⟩ := bind_some h
  obtain ⟨rfl, rfl⟩ := past_some hp
  obtain ⟨nexp, g5, h5, h⟩ := bind_some h
  obtain ⟨WT, sT, dT, lT, _⟩ := foot_copyTail (hs := lazyReg rp) (ts := lazyReg rq) ihp ihq d3
    (nb_this (by omega)) (nb_this (by omega)) trivial trivial
    (fun x e e' => by simp only [lazyReg, NMem] at e e'; omega) (jmpIn_jmp0 _ _) h4 h5 h
  have gl : ∀ x, GMem goal x → x < g.re := fun x hx => by
    cases goal with
    | next laz th => exact hg.1 x hx
    | pick => exact hx.elim
    | done => exact hx.elim
  have a : ∀ x, (g3.re ≤ x ∨ NMem (lazyReg rp : Sure S).ned x ∨ NMem (lazyReg rq : Sure S).ned x) → g.re ≤ x :=
    fun x hx => by
      rcases hx with e | e | e
      · omega
      · simp only [lazyReg, NMem] at e; omega
      · simp only [lazyReg, NMem] at e; omega
  refine ⟨((wroteIn_re h1).trans (wroteIn_re h2)).trans ((W3.mono fun x hx => ⟨by omega, ?_, fun e => ?_⟩).trans
    (WT.mono fun x hx => ⟨hx.1, Or.inl (a x hx.2.1), hx.2.2⟩)), fun x hx => Or.inl (a x (sT x hx)), dT⟩
  · rcases hx.2 with e | e
    · exact Or.inl (by omega)
    · exact Or.inr e
  · rcases sT x e with e' | e' | e'
    · omega
    · simp only [lazyReg, NMem] at e'
      rcases hx.2 with e'' | e''
      · omega
      · have := gl x e''; omega
    · simp only [lazyReg, NMem] at e'
      rcases hx.2 with e'' | e''
      · omega
      · have := gl x e''; omega

end Comp
end SkaModel
end Formalization
