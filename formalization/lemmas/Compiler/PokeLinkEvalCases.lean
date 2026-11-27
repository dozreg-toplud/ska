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

end Cases

end Compiler
end Formalization
