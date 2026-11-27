import lemmas.Compiler.PokeLinkEvalBase

/-!
# `+eval-finalized`: the cases that call the trap and `+so` only (track P, README Gaps 23)

The cases `%3`, `%7`, the cell, `%5`, `%6`, `%11` (static and dynamic) and
`%mean` of `nomm-loop` against `efGo`, each from `EfLoopAt` of the sub-nomms
it runs (`PokeLinkEvalBase.lean`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF SkaModel.PokeM

set_option linter.unusedSimpArgs false

section Cases

variable (b : Bell) (M : FinMap Bell Noun)

theorem ef_3 (p : Nomm) (ih : EfLoopAt b M p) : EfLoopAt b M (Nomm.n3 p) := by
  intro sub r h
  simp only [efGo] at h
  cases e : efGo (accFt M) sub p with
  | none => simp [e] at h
  | some rp =>
    simp only [e, Option.map_some, Option.some.injEq] at h; subst h
    have hp := ih sub rp e
    rw [ef_disp_3, efC3_eq]
    unfold efK at hp ⊢
    obtain ⟨sp, pp, tp⟩ := rp
    simp only [efRes] at hp ⊢
    simp [nock_exec, Nomm.toNoun, hp]
    simp [Sock.toNoun, Cape.toNoun, Sock.dunno, flagNoun]

theorem ef_7 (p q : Nomm) (ihp : EfLoopAt b M p) (ihq : EfLoopAt b M q) : EfLoopAt b M (Nomm.n7 p q) := by
  intro sub r h
  simp only [efGo] at h
  cases e : efGo (accFt M) sub p with
  | none => simp [e] at h
  | some rp =>
    cases e2 : efGo (accFt M) rp.1 q with
    | none => simp [e, e2] at h
    | some rq =>
      simp only [e, e2, Option.bind_some, Option.map_some, Option.some.injEq] at h; subst h
      have hp := ihp sub rp e
      have hq := ihq rp.1 rq e2
      rw [ef_disp_7, efC7_eq]
      unfold efK at hp hq ⊢
      obtain ⟨sp, pp, tp⟩ := rp
      obtain ⟨sq, pq, tq⟩ := rq
      simp only [efRes, flagNoun] at hp hq ⊢
      cases pp <;> cases tp <;> cases pq <;> cases tq <;>
        simp [nock_exec, Nomm.toNoun, hp, hq]

/-- The two runs of a two-part case. -/
theorem efGo_two {α : Type} {o1 o2 : Option (Sock × Bool × Bool)} {f : (Sock × Bool × Bool) → (Sock × Bool × Bool) → α} {r : α}
    (h : (o1.bind fun a => o2.map fun c => f a c) = some r) :
    ∃ a c, o1 = some a ∧ o2 = some c ∧ r = f a c := by
  cases o1 <;> cases o2 <;> simp_all

theorem ef_cons (p q : Nomm) (ihp : EfLoopAt b M p) (ihq : EfLoopAt b M q) : EfLoopAt b M (Nomm.cons p q) := by
  intro sub r h
  simp only [efGo] at h
  obtain ⟨rp, rq, e, e2, rfl⟩ := efGo_two h
  have hp := ihp sub rp e
  have hq := ihq sub rq e2
  have hk := so_knit_pill rp.1 rq.1
  rw [ef_disp_cons, efCcons_eq]
  unfold efK at hp hq ⊢
  obtain ⟨sp, pp, tp⟩ := rp
  obtain ⟨sq, pq, tq⟩ := rq
  simp only [efRes, flagNoun] at hp hq hk ⊢
  cases pp <;> cases tp <;> cases pq <;> cases tq <;>
    simp [nock_exec, Nomm.toNoun, hp, hq, ana_lib7, so.lib.arm_at, so_lib_arm, so.knit.arm_at, so_knit_arm, hk]

theorem ef_6 (p q r : Nomm) (ihq : EfLoopAt b M q) (ihr : EfLoopAt b M r) : EfLoopAt b M (Nomm.n6 p q r) := by
  intro sub o h
  simp only [efGo] at h
  obtain ⟨rq, rr, e, e2, rfl⟩ := efGo_two h
  have hq := ihq sub rq e
  have hr := ihr sub rr e2
  have hk := so_purr_pill rq.1 rr.1
  rw [ef_disp_6, efC6_eq]
  unfold efK at hq hr ⊢
  obtain ⟨sq, pq, tq⟩ := rq
  obtain ⟨sr, pr, tr⟩ := rr
  simp only [efRes, flagNoun] at hq hr hk ⊢
  simp [nock_exec, Nomm.toNoun, hq, hr, ana_lib7, so.lib.arm_at, so_lib_arm, so.purr.arm_at, so_purr_arm, hk]

theorem ef_mean (p : Nomm) (c : Bell) (q : Nomm) (bd : Noun) (k : Option Noun)
    (ihp : EfLoopAt b M p) (ihq : EfLoopAt b M q) : EfLoopAt b M (Nomm.mean p c q bd k) := by
  intro sub r h
  simp only [efGo] at h
  obtain ⟨rp, rq, e, e2, rfl⟩ := efGo_two h
  have hp := ihp sub rp e
  have hq := ihq sub rq e2
  rw [ef_disp_mean, efCmean_eq]
  unfold efK at hp hq ⊢
  obtain ⟨sp, pp, tp⟩ := rp
  obtain ⟨sq, pq, tq⟩ := rq
  simp only [efRes, flagNoun] at hp hq ⊢
  cases pp <;> cases tp <;> cases pq <;> cases tq <;>
    simp [nock_exec, Nomm.toNoun, hp, hq]

theorem ef_11s (t : Nat) (q : Nomm) (bd : Noun) (ihq : EfLoopAt b M q) : EfLoopAt b M (Nomm.n11s t q bd) := by
  intro sub r h
  simp only [efGo] at h
  cases e : efGo (accFt M) sub q with
  | none => simp [e] at h
  | some rq =>
    simp only [e, Option.map_some, Option.some.injEq] at h; subst h
    have hq := ihq sub rq e
    rw [ef_disp_11s, efC11_eq]
    unfold efK at hq ⊢
    obtain ⟨sq, pq, tq⟩ := rq
    simp only [efRes, flagNoun] at hq ⊢
    cases tq <;> simp [nock_exec, Nomm.toNoun, hq]

theorem ef_11d (t : Nat) (hh q : Nomm) (bd : Noun) (ihh : EfLoopAt b M hh) (ihq : EfLoopAt b M q) :
    EfLoopAt b M (Nomm.n11d t hh q bd) := by
  intro sub r h
  simp only [efGo] at h
  obtain ⟨rh, rq, e, e2, rfl⟩ := efGo_two h
  have hp := ihh sub rh e
  have hq := ihq sub rq e2
  rw [ef_disp_11d, efC11_eq]
  unfold efK at hp hq ⊢
  obtain ⟨sp, pp, tp⟩ := rh
  obtain ⟨sq, pq, tq⟩ := rq
  simp only [efRes, flagNoun] at hp hq ⊢
  by_cases h1 : t = Tag.fast
  · subst h1; cases pp <;> cases tp <;> cases pq <;> cases tq <;>
      simp [nock_exec, Nomm.toNoun, hp, hq, hintFree, hintSafe, stopTag, Tag.fast, Tag.memo, Tag.hunk, Tag.hand,
        Tag.mean, Tag.lose, Tag.spot]
  by_cases h2 : t = Tag.hunk
  · subst h2; cases pp <;> cases tp <;> cases pq <;> cases tq <;>
      simp [nock_exec, Nomm.toNoun, hp, hq, hintFree, hintSafe, stopTag, Tag.fast, Tag.memo, Tag.hunk, Tag.hand,
        Tag.mean, Tag.lose, Tag.spot]
  by_cases h3 : t = Tag.hand
  · subst h3; cases pp <;> cases tp <;> cases pq <;> cases tq <;>
      simp [nock_exec, Nomm.toNoun, hp, hq, hintFree, hintSafe, stopTag, Tag.fast, Tag.memo, Tag.hunk, Tag.hand,
        Tag.mean, Tag.lose, Tag.spot]
  by_cases h4 : t = Tag.mean
  · subst h4; cases pp <;> cases tp <;> cases pq <;> cases tq <;>
      simp [nock_exec, Nomm.toNoun, hp, hq, hintFree, hintSafe, stopTag, Tag.fast, Tag.memo, Tag.hunk, Tag.hand,
        Tag.mean, Tag.lose, Tag.spot]
  by_cases h5 : t = Tag.lose
  · subst h5; cases pp <;> cases tp <;> cases pq <;> cases tq <;>
      simp [nock_exec, Nomm.toNoun, hp, hq, hintFree, hintSafe, stopTag, Tag.fast, Tag.memo, Tag.hunk, Tag.hand,
        Tag.mean, Tag.lose, Tag.spot]
  by_cases h6 : t = Tag.spot
  · subst h6; cases pp <;> cases tp <;> cases pq <;> cases tq <;>
      simp [nock_exec, Nomm.toNoun, hp, hq, hintFree, hintSafe, stopTag, Tag.fast, Tag.memo, Tag.hunk, Tag.hand,
        Tag.mean, Tag.lose, Tag.spot]
  by_cases h7 : t = Tag.memo
  · subst h7; cases pp <;> cases tp <;> cases pq <;> cases tq <;>
      simp [nock_exec, Nomm.toNoun, hp, hq, hintFree, hintSafe, stopTag, Tag.fast, Tag.memo, Tag.hunk, Tag.hand,
        Tag.mean, Tag.lose, Tag.spot]
  have hf : hintFree t = false := by
    simp [hintFree, hintSafe, stopTag, h1, h2, h3, h4, h5, h6, h7]
  simp only [Tag.fast, Tag.memo, Tag.hunk, Tag.hand, Tag.mean, Tag.lose, Tag.spot] at h1 h2 h3 h4 h5 h6 h7
  rw [hf]
  cases pp <;> cases tp <;> cases pq <;> cases tq <;>
    simp [nock_exec, Nomm.toNoun, hp, hq, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5,
      Ne.symm h6, Ne.symm h7, h1, h2, h3, h4, h5, h6, h7]

theorem ef_5 (p q : Nomm) (ihp : EfLoopAt b M p) (ihq : EfLoopAt b M q) : EfLoopAt b M (Nomm.n5 p q) := by
  intro sub r h
  cases e : efGo (accFt M) sub p with
  | none => simp [efGo, e, andS] at h
  | some rp =>
    have hp := ihp sub rp e
    obtain ⟨sp, pp, tp⟩ := rp
    rw [ef_disp_5, efC5_eq]
    unfold efK at hp ⊢
    simp only [efRes, flagNoun] at hp ⊢
    cases pp <;> cases tp <;> simp only [Bool.false_eq_true, ↓reduceIte] at hp
    · simp [efGo, e, andS] at h; subst h
      simp [nock_exec, Nomm.toNoun, hp]
      simp [Sock.toNoun, Cape.toNoun, Sock.dunno]
    all_goals
      cases e2 : efGo (accFt M) sub q with
      | none => simp [efGo, e, e2, andS] at h
      | some rq =>
        have hq := ihq sub rq e2
        obtain ⟨sq, pq, tq⟩ := rq
        unfold efK at hq
        simp only [efRes, flagNoun] at hq
        simp [efGo, e, e2, andS] at h; subst h
        cases pq <;> cases tq <;> simp only [Bool.false_eq_true, ↓reduceIte] at hq <;>
          simp [nock_exec, Nomm.toNoun, hp, hq] <;>
          simp [Sock.toNoun, Cape.toNoun, Sock.dunno]

end Cases

end Compiler
end Formalization
