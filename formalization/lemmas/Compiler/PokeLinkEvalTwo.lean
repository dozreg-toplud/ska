import lemmas.Compiler.PokeLinkEvalBase

/-!
# `+eval-finalized`: the case `%2` (track P, README Gaps 23)

`[%2 p q info]`: `?&(pure:loop(p) pure:loop(q) &(?=(^ info) pure:(~(got by code) b.u.info)))`
and the same for `total`.  The `?&` stops at the first `|`, as `andS` of
`efGo`; `+got:by` on the accumulator crashes on a bell it does not hold, as
`accFt M` gives `none` there; and `decF` reads the entry's flags.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF SkaModel.PokeM

set_option linter.unusedSimpArgs false

/-- An entry whose flags `decF` reads is `[nomm flags]`. -/
theorem decF_some {v : Noun} {f : Bool × Bool} (h : decF v = some f) : ∃ x, v = C x (flagNoun f) := by
  match v, h with
  | Noun.cell x (Noun.cell (Noun.atom a) (Noun.atom t)), h =>
    simp only [decF] at h
    split at h
    · rename_i hle
      simp only [Option.some.injEq] at h; subst h
      refine ⟨x, ?_⟩
      rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;>
        rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl <;> rfl
    · cases h

section Cases

variable (b : Bell) (M : FinMap Bell Noun)

set_option maxHeartbeats 4000000 in
theorem ef_2 (p q : Nomm) (i : Option (Bell × Option Noun)) (ihp : EfLoopAt b M p) (ihq : EfLoopAt b M q) :
    EfLoopAt b M (Nomm.n2 p q i) := by
  intro sub r h
  have hgc : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
    ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
  cases e : efGo (accFt M) sub p with
  | none => simp [efGo, e, andS] at h
  | some rp =>
  have hp := ihp sub rp e
  obtain ⟨sp, pp, tp⟩ := rp
  rw [ef_disp_2, efC2_eq]
  unfold efK at hp ⊢
  simp only [efRes, flagNoun] at hp ⊢
  cases pp <;> cases tp <;> simp only [Bool.false_eq_true, ↓reduceIte] at hp
  -- `pure.p` and `total.p` both `|`: nothing else runs
  · simp [efGo, e, andS] at h; subst h
    simp [nock_exec, Nomm.toNoun, hp]
    simp [Sock.toNoun, Cape.toNoun, Sock.dunno]
  all_goals
    cases e2 : efGo (accFt M) sub q with
    | none => simp [efGo, e, e2, andS] at h
    | some rq =>
      have hq := ihq sub rq e2
      unfold efK at hq
      obtain ⟨sq, pq, tq⟩ := rq
      simp only [efRes, flagNoun] at hq
      cases pq <;> cases tq <;> simp only [Bool.false_eq_true, ↓reduceIte] at hq
      all_goals
        cases i with
        | none =>
          simp [efGo, e, e2, andS] at h; subst h
          simp [nock_exec, Nomm.toNoun, unitNoun, hp, hq]
          simp [Sock.toNoun, Cape.toNoun, Sock.dunno]
        | some ic =>
          obtain ⟨c, k⟩ := ic
          cases hv : M.get c with
          | none =>
            have hget : getF mugF (TKey.enc c) (M.toNoun id) = some (A 0) := by
              rw [FinMap.getF_toNoun, hv]; rfl
            have hgot := got_gate_nil layer2 hgc (TKey.enc c) _ hget
            simp only [show TKey.enc c = c.toNoun from rfl] at hgot
            first
              | (simp [efGo, e, e2, andS, accFt, hv] at h; done)
              | (simp [efGo, e, e2, andS, accFt, hv] at h; subst h
                 simp [nock_exec, Nomm.toNoun, unitNoun, hp, hq, ana_l2e, by.arm_at, by_arm, by.got.arm_at,
                   got_arm, hgot]
                 simp [Sock.toNoun, Cape.toNoun, Sock.dunno])
          | some v =>
            have hget : getF mugF (TKey.enc c) (M.toNoun id) = some (C (A 0) v) := by
              rw [FinMap.getF_toNoun, hv]; rfl
            have hgot := got_gate layer2 hgc (TKey.enc c) _ _ hget
            simp only [show TKey.enc c = c.toNoun from rfl] at hgot
            cases hd : decF v with
            | none =>
              first
                | (simp [efGo, e, e2, andS, accFt, hv, hd] at h; done)
                | (simp [efGo, e, e2, andS, accFt, hv, hd] at h; subst h
                   simp [nock_exec, Nomm.toNoun, unitNoun, hp, hq]
                   simp [Sock.toNoun, Cape.toNoun, Sock.dunno])
            | some fl =>
              obtain ⟨x, rfl⟩ := decF_some hd
              obtain ⟨fa, fb⟩ := fl
              simp only [flagNoun] at hgot
              cases fa <;> cases fb <;> simp only [Bool.false_eq_true, ↓reduceIte] at hgot <;>
                simp [efGo, e, e2, andS, accFt, hv, hd] at h <;> subst h <;>
                simp [nock_exec, Nomm.toNoun, unitNoun, hp, hq, ana_l2e, by.arm_at, by_arm, by.got.arm_at,
                  got_arm, hgot] <;>
                simp [Sock.toNoun, Cape.toNoun, Sock.dunno]

end Cases

end Compiler
end Formalization
