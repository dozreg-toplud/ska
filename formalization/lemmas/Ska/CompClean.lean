import lemmas.Ska.CompForl

/-!
# No need of `run` has a subterm `pair none none`

`+cons-need` turns `[none none]` into `none`, which drops the requirement
that the noun be a cell.  If a need `[[%none ~] [%none ~]]` could reach
`+copy`, the copy of two such needs would be `none`, and a cell check would
be lost.  `run_clean`: when the need of the goal has no such subterm
(`Clean`), neither has the need that `run` returns, for every nomm of the
model.  The helpers keep it: `+from-sure` treats `none` apart and
`+from-sure`'s loop wraps a need that is not `none`; `+split-need` and
`+must` take a need apart or name it; `+copy-need-make-ops` conses through
`+cons-need`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

theorem clean_consNeed {a b : Need} (ha : Clean a) (hb : Clean b) : Clean (consNeed a b) := by
  unfold consNeed
  split
  · trivial
  · exact ⟨by assumption, ha, hb⟩

theorem clean_fromPath {ned : Need} (hc : Clean ned) (hn : ned ≠ Need.none) :
    ∀ axe, Clean (fromPath ned axe) ∧ fromPath ned axe ≠ Need.none := by
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
    by_cases h1 : axe ≤ 1
    · rw [fromPath]; simp only [h1, dif_pos]; exact ⟨hc, hn⟩
    · rw [fromPath_step ned (by omega)]
      have ihm := ih (mas axe) (mas_lt axe (by omega))
      split
      · exact ⟨⟨fun e => ihm.2 e.1, ihm.1, trivial⟩, by simp⟩
      · exact ⟨⟨fun e => ihm.2 e.2, trivial, ihm.1⟩, by simp⟩

theorem clean_fromSure {axe : Nat} {sur sur' : Sure S} (h : fromSure axe sur = some sur')
    (hc : Clean sur.ned) : Clean sur'.ned := by
  unfold fromSure at h
  by_cases h0 : axe = 0
  · simp [h0] at h
  simp only [h0, if_false] at h
  by_cases hn : sur.ned = Need.none
  · simp only [hn, if_true] at h
    by_cases h1 : axe = 1
    · simp [h1] at h
    simp only [h1, if_false, Option.some.injEq] at h
    subst h; trivial
  · simp only [hn, if_false, Option.some.injEq] at h
    subst h; exact (clean_fromPath hc hn axe).1

theorem clean_must {ned : Need} {g g' : Gen Map} {x : Nat × Need} (h : must ned g = some (x, g'))
    (hc : Clean ned) : Clean x.2 := by
  cases ned <;> simp only [must, bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq,
    Prod.mk.injEq] at h <;> rw [← h.1]
  · exact ⟨hc.2.1, hc.2.2⟩
  · exact hc
  · exact hc
  · trivial

theorem clean_splitNeed {ned : Need} {o : Nat} {g g' : Gen Map} {x : Need × Need}
    (h : splitNeed ned o g = some (x, g')) (hc : Clean ned) : Clean x.1 ∧ Clean x.2 := by
  cases ned with
  | pair p q =>
    simp only [splitNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact ⟨hc.2.1, hc.2.2⟩
  | none =>
    simp only [splitNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact ⟨trivial, trivial⟩
  | this r =>
    simp only [splitNeed, bind_apply, re_apply, Option.bind_some] at h
    obtain ⟨⟨_, g1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact ⟨trivial, trivial⟩
  | both r hh t =>
    simp only [splitNeed] at h
    obtain ⟨m1, g1, h1, h⟩ := bind_some h
    obtain ⟨m2, g2, h2, h⟩ := bind_some h
    obtain ⟨_, g3, h3, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact ⟨clean_must h1 hc.1, clean_must h2 hc.2⟩

theorem clean_split {nex : Next S} {g g' : Gen Map} {x : Sure S × Sure S × Nat}
    (h : Comp.split nex g = some (x, g')) (hc : Clean nex.laz.ned) : Clean x.1.ned ∧ Clean x.2.1.ned := by
  simp only [Comp.split] at h
  obtain ⟨o, g0, h0, h⟩ := bind_some h
  obtain ⟨⟨sh, st⟩, g1, h2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [splitSure] at h2
  obtain ⟨⟨lh, lt⟩, _, h2⟩ := Option.bind_eq_some_iff.mp h2
  obtain ⟨⟨⟨nh, nt⟩, g2⟩, h3, h4⟩ := Option.map_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
  exact clean_splitNeed h3 hc

theorem clean_copyNeed : ∀ (a b : Need) (ops : List Pole) (g g' : Gen Map) (x : Need × List Pole),
    copyNeed a b ops g = some (x, g') → Clean a → Clean b → Clean x.1 := by
  intro a
  induction a with
  | none =>
    intro b ops g g' x h _ hb
    simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact hb
  | this rl =>
    intro b ops g g' x h _ hb
    cases b <;> simp only [copyNeed, bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq,
      Prod.mk.injEq] at h <;> rw [← h.1]
    · exact ⟨hb.2.1, hb.2.2⟩
    · exact hb
    · trivial
    · trivial
  | pair pl ql ihp ihq =>
    intro b ops g g' x h ha hb
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]; exact ha
    | this rr =>
      simp only [copyNeed, bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h
      rw [← h.1]; exact ⟨ha.2.1, ha.2.2⟩
    | pair pr qr =>
      simp only [copyNeed] at h
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact clean_consNeed (ihp _ _ _ _ _ h1 ha.2.1 hb.2.1) (ihq _ _ _ _ _ h2 ha.2.2 hb.2.2)
    | both xr hr tr =>
      simp only [copyNeed] at h
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact ⟨ihp _ _ _ _ _ h1 ha.2.1 hb.1, ihq _ _ _ _ _ h2 ha.2.2 hb.2⟩
  | both rl hl tl ihh iht =>
    intro b ops g g' x h ha hb
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]; exact ha
    | this rr =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]; exact ha
    | pair pr qr =>
      simp only [copyNeed] at h
      obtain ⟨xr, g0', h0, h⟩ := bind_some h
      simp only [re_apply, Option.some.injEq, Prod.mk.injEq] at h0
      obtain ⟨rfl, rfl⟩ := h0
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact ⟨ihh _ _ _ _ _ h1 ha.1 hb.2.1, iht _ _ _ _ _ h2 ha.2 hb.2.2⟩
    | both xr hr tr =>
      simp only [copyNeed] at h
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact ⟨ihh _ _ _ _ _ h1 ha.1 hb.1, iht _ _ _ _ _ h2 ha.2 hb.2⟩

theorem clean_copy {first : Next S} {second : Sure S} {g g' : Gen Map} {nex : Next S}
    (h : copy first second g = some (nex, g')) (ha : Clean first.laz.ned) (hb : Clean second.ned) :
    Clean nex.laz.ned := by
  simp only [copy] at h
  obtain ⟨o, g0, h0, h⟩ := bind_some h
  obtain ⟨laz, g1, h1', h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [copyLazy] at h1'
  obtain ⟨⟨n1, o1⟩, g2, h2, h1'⟩ := bind_some h1'
  obtain ⟨_, g3, h3, h1'⟩ := bind_some h1'
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1'
  obtain ⟨rfl, rfl⟩ := h1'
  exact clean_copyNeed _ _ _ _ _ _ h2 ha hb

theorem clean_simpleNext {goal : CGoal S} {g g' : Gen Map} {nex : Next S}
    (h : simpleNext goal g = some (nex, g')) (hc : GClean goal) : Clean nex.laz.ned := by
  cases goal with
  | next laz th =>
    simp only [simpleNext, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact hc
  | done =>
    simp only [simpleNext, bind_apply, re_apply, emit_apply, pure_apply, Option.bind_some,
      Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; trivial
  | pick z o =>
    simp only [simpleNext, bind_apply, re_apply, emit_apply, pure_apply, Option.bind_some,
      Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; trivial

theorem clean_bomb {miss : Option Nat} {g g' : Gen Map} {nex : Next S}
    (h : (bomb miss : CM Map (Next S)) g = some (nex, g')) : Clean nex.laz.ned := by
  rw [bomb_eq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.1]; trivial

theorem clean_side {h : Bool} {a b : Need} (ha : Clean a) (hb : Clean b) : Clean (side h a b) := by
  unfold side; split
  · exact clean_consNeed ha hb
  · exact clean_consNeed hb ha

theorem clean_rollTack : ∀ (tack : List (Bool × Need)) (acc : Need), Clean acc → (∀ e ∈ tack, Clean e.2) →
    Clean (tack.foldl (fun acc e => side e.1 acc e.2) acc)
  | [], _, ha, _ => ha
  | e :: tack, acc, ha, ht => clean_rollTack tack _ (clean_side ha (ht e (List.mem_cons_self ..)))
      (fun x hx => ht x (List.mem_cons_of_mem _ hx))

theorem clean_intoLoop {o : Nat} : ∀ (axe : Nat) (ned : Need) (tack : List (Bool × Need)) (ops : List Pole)
    (g g' : Gen Map) (x : Need × Need), intoLoop o axe ned tack ops g = some (x, g') →
    Clean ned → (∀ e ∈ tack, Clean e.2) → Clean x.1 ∧ Clean x.2 := by
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
  intro ned tack ops g g' x h hc ht
  rw [intoLoop] at h
  by_cases h1 : axe ≤ 1
  · rw [dif_pos h1] at h
    obtain ⟨_, g1, _, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact ⟨hc, clean_rollTack tack _ trivial ht⟩
  rw [dif_neg h1] at h
  have lt := mas_lt axe (by omega)
  cases ned with
  | none => exact ih _ lt _ _ _ _ _ _ h trivial (by
      intro e he; rcases List.mem_cons.mp he with rfl | he
      · trivial
      · exact ht e he)
  | this r =>
    simp only [bind_apply, re_apply, Option.bind_some] at h
    refine ih _ lt _ _ _ _ _ _ h trivial ?_
    intro e he; rcases List.mem_cons.mp he with rfl | he
    · trivial
    · exact ht e he
  | pair p q =>
    simp only at h
    refine ih _ lt _ _ _ _ _ _ h (by split <;> first | exact hc.2.1 | exact hc.2.2) ?_
    intro e he; rcases List.mem_cons.mp he with rfl | he
    · show Clean (if _ then _ else _); split
      · exact hc.2.2
      · exact hc.2.1
    · exact ht e he
  | both r hh t =>
    simp only at h
    obtain ⟨l, g1, h1, h⟩ := bind_some h
    obtain ⟨l', g2, h2, h⟩ := bind_some h
    have c1 := clean_must h1 hc.1
    have c2 := clean_must h2 hc.2
    refine ih _ lt _ _ _ _ _ _ h (by split <;> assumption) ?_
    intro e he; rcases List.mem_cons.mp he with rfl | he
    · show Clean (if _ then _ else _); split <;> assumption
    · exact ht e he

theorem clean_into {nex : Next S} {axe : Nat} {g g' : Gen Map} {x : Sure S × Sure S × Nat}
    (h : into nex axe g = some (x, g')) (hc : Clean nex.laz.ned) : Clean x.1.ned ∧ Clean x.2.1.ned := by
  simp only [into] at h
  obtain ⟨o, g0, _, h⟩ := bind_some h
  obtain ⟨⟨sd, sr⟩, g1, h2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [intoSure] at h2
  obtain ⟨⟨ld, lr⟩, _, h2⟩ := Option.bind_eq_some_iff.mp h2
  obtain ⟨⟨⟨nd, nr⟩, g2⟩, h3, h4⟩ := Option.map_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
  simp only [intoNeed] at h3
  by_cases a0 : axe = 0
  · simp [a0] at h3
  rw [if_neg a0] at h3
  by_cases a1 : axe = 1
  · rw [if_pos a1] at h3
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h3
    exact ⟨hc, trivial⟩
  rw [if_neg a1] at h3
  exact clean_intoLoop _ _ _ _ _ _ _ h3 hc (fun e he => by simp at he)

/-- What `run_clean` proves of one nomm. -/
def CleanIH (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] (p : Nomm) : Prop :=
  ∀ (goal : CGoal S) (g g' : Gen Map) (nex : Next S), GClean goal → run p goal g = some (nex, g') →
    Clean nex.laz.ned

/-- The two runs and the copy of a cons, for a goal `%next`. -/
theorem cons_next_clean {p q : Nomm} (ihp : CleanIH S Map p) (ihq : CleanIH S Map q)
    {laz : Sure S} {th : Jmp} {g0 g1 : Gen Map} {nex : Next S}
    (h : (do
      let (hed, tel, o) ← Comp.split ⟨laz, th⟩
      let nexh : Next S := ⟨hed, jmp0 o⟩
      let nex2 ← run q (CGoal.next tel nexh.th)
      let nex1 ← run p (CGoal.next nexh.laz nex2.th)
      copy nex1 nex2.laz : CM Map (Next S)) g0 = some (nex, g1))
    (hc : Clean laz.ned) : Clean nex.laz.ned := by
  obtain ⟨⟨hed, tel, o⟩, g2, h2, h⟩ := bind_some h
  have Sp := clean_split h2 hc
  simp only at Sp
  obtain ⟨nex2, g3, h3, h⟩ := bind_some h
  have Cq := ihq (CGoal.next _ _) g2 g3 nex2 Sp.2 h3
  obtain ⟨nex1, g4, h4, h⟩ := bind_some h
  have Cp := ihp (CGoal.next _ _) g3 g4 nex1 Sp.1 h4
  exact clean_copy h Cp Cq

/-- **No need that `run` returns has a subterm `pair none none`**, when the
goal's need has none, for every nomm. -/
theorem run_clean : ∀ (nm : Nomm), CleanIH S Map nm := by
  intro nm
  induction nm with
  | n0 ax =>
    intro goal g g' nex hc h
    simp only [run] at h
    by_cases h0 : ax = 0
    · rw [if_pos h0] at h; exact clean_bomb h
    rw [if_neg h0] at h
    obtain ⟨nex0, g1, h1, h⟩ := bind_some h
    have C0 := clean_simpleNext h1 hc
    by_cases ha : ax = 1
    · rw [if_pos ha] at h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]; exact C0
    rw [if_neg ha] at h
    cases e : «from» ax nex0.laz with
    | none => rw [e] at h; cases h
    | some laz =>
      rw [e] at h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]; exact clean_fromSure e C0
  | n1 k =>
    intro goal g g' nex hc h
    cases goal with
    | done =>
      simp only [run, bind_apply, re_apply, emit_apply, Option.bind_some, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h
      rw [← h.1]; trivial
    | pick z o =>
      simp only [run] at h
      by_cases h0 : k = A 0
      · rw [if_pos h0] at h
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]; trivial
      rw [if_neg h0] at h
      by_cases h1 : k = A 1
      · rw [if_pos h1] at h
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]; trivial
      rw [if_neg h1] at h
      exact clean_bomb h
    | next laz th =>
      simp only [run] at h
      obtain ⟨o, g1, _, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]; trivial
  | n7 p q ihp ihq =>
    intro goal g g' nex hc h
    simp only [run] at h
    obtain ⟨nexq, g1, h1, h⟩ := bind_some h
    exact ihp _ _ _ _ (by exact ihq goal g g1 nexq hc h1) h
  | n4 p ih =>
    intro goal g g' nex hc h
    cases goal with
    | done =>
      simp only [run, bind_apply, re_apply, emit_apply, Option.bind_some] at h
      refine ih _ _ _ _ ?_ h; trivial
    | pick z o =>
      simp only [run, bind_apply, re_apply, emit_apply, Option.bind_some] at h
      refine ih _ _ _ _ ?_ h; trivial
    | next laz th =>
      simp only [run] at h
      obtain ⟨a, g2, h2, h⟩ := bind_some h
      obtain ⟨⟨pro, th'⟩, g3, h3, h⟩ := bind_some h
      simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
      refine ih _ _ _ _ ?_ h; trivial
  | n3 p ih =>
    intro goal g g' nex hc h
    cases goal with
    | done =>
      simp only [run] at h
      obtain ⟨⟨o0, o1⟩, g2, h2, h⟩ := bind_some h
      simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
      refine ih _ _ _ _ ?_ h; trivial
    | pick z o =>
      simp only [run, bind_apply, re_apply, emit_apply, Option.bind_some] at h
      refine ih _ _ _ _ ?_ h; trivial
    | next laz th =>
      simp only [run] at h
      by_cases en : noneEquivalent laz = true
      · rw [if_pos en] at h; exact ih _ _ _ _ hc h
      rw [if_neg en] at h
      obtain ⟨a, g2, h2, h⟩ := bind_some h
      cases a with
      | none => cases h
      | some x =>
        obtain ⟨r, o⟩ := x
        simp only at h
        obtain ⟨⟨z, o'⟩, g3, h3, h⟩ := bind_some h
        simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
        refine ih _ _ _ _ ?_ h; trivial
  | n5 p q ihp ihq =>
    intro goal g0 g1 nex hc h
    simp only [run, bind_apply, re_apply, Option.bind_some] at h
    obtain ⟨⟨o, g2⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨nexq, g3⟩, h3, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨nexp, g4⟩, h4, h⟩ := Option.bind_eq_some_iff.mp h
    exact clean_copy h (ihp _ _ _ _ (by trivial) h4) (ihq _ _ _ _ (by trivial) h3)
  | cons p q ihp ihq =>
    intro goal g0 g1 nex hc h
    cases goal with
    | done =>
      simp only [run, bind_apply, re_apply, emit_apply, Option.bind_some, pure_apply] at h
      exact cons_next_clean ihp ihq h trivial
    | next laz th =>
      simp only [run, bind_apply, pure_apply, Option.bind_some] at h
      exact cons_next_clean ihp ihq h hc
    | pick z o =>
      simp only [run, bind_apply, pure_apply, emit_apply, Option.bind_some] at h
      obtain ⟨⟨nex2, g3⟩, h3, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨nex1, g4⟩, h4, h⟩ := Option.bind_eq_some_iff.mp h
      exact clean_copy h (ihp _ _ _ _ (by trivial) h4) (ihq _ _ _ _ (by trivial) h3)
  | n2 => intro goal g0 g1 nex _ h; simp only [run] at h; cases h
  | n6 => intro goal g0 g1 nex _ h; simp only [run] at h; cases h
  | n10 a v q ihv ihq =>
    intro goal g0 g1 nex hc h
    simp only [run] at h
    obtain ⟨nex0, g2, h2, h⟩ := bind_some h
    have C0 := clean_simpleNext h2 hc
    obtain ⟨⟨don, rec, o⟩, g3, h3, h⟩ := bind_some h
    have CI := clean_into h3 C0
    simp only at h
    obtain ⟨nexRec, g4, h4, h⟩ := bind_some h
    obtain ⟨nexDon, g5, h5, h⟩ := bind_some h
    exact clean_copy h (ihv _ _ _ _ (by exact CI.1) h5) (ihq _ _ _ _ (by exact CI.2) h4)
  | n11s => intro goal g0 g1 nex _ h; simp only [run] at h; cases h
  | n11d => intro goal g0 g1 nex _ h; simp only [run] at h; cases h
  | n12 => intro goal g0 g1 nex _ h; simp only [run] at h; cases h
  | mean => intro goal g0 g1 nex _ h; simp only [run] at h; cases h

end Comp
end SkaModel
end Formalization
