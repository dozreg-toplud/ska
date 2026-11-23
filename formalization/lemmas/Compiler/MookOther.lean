import lemmas.Compiler.EvalRend

/-!
# `+eval-mook` on nouns that are no tone

`Reach` of `core/Statement.lean` runs `+eval-mook` on any noun, the model only
on tones.  On a noun that is not `[%2 *]` the pill's `+eval-mook` returns the
noun and the core unchanged (`eval_mook_not2`), which it also does on the tone
`[%0 0]`; so `MookOther` of `Assembly.lean` reduces to the nouns `[%2 x]`
(`MookOtherTwo`, `mookOther_of_two`).
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon

/-- On a noun that is not `[%2 *]`, `+eval-mook` returns the noun and the
compiler's core.  It reads nothing from its context. -/
theorem eval_mook_not2 (cr ton : Noun) (h : ∀ x, ton ≠ C (A 2) x) :
    nock (C eval_mook.battery (C ton (icore cr))) eval_mook.battery = some (C ton cr) := by
  nock_open eval_mook.battery
  rcases ton with a | ⟨hd, tl⟩
  · simp [nock_exec, icore]
  · rcases hd with b | ⟨h₁, h₂⟩
    · have hb : ¬ (2 = b) := fun e => h tl (by rw [← e])
      simp [nock_exec, icore, hb]
    · simp [nock_exec, icore]

/-- What is left of `MookOther` of `Assembly.lean`: the nouns `[%2 x]`. -/
def MookOtherTwo : Prop :=
  ∀ cr, CorIn cr → ∀ tr x,
    nock (C eval_mook.battery (C (C (A 2) tr) (icore cr))) eval_mook.battery = some x →
    ∃ (t : Tone) (y z cr' : Noun), x = C y cr' ∧
      nock (mookS cr t) eval_mook.battery = some (C z cr')

/-- `MookOther` of `Assembly.lean`, from its case `[%2 x]`. -/
theorem mookOther_of_two (h2 : MookOtherTwo) :
    ∀ cr, CorIn cr → ∀ ton x,
      nock (C eval_mook.battery (C ton (icore cr))) eval_mook.battery = some x →
      ∃ (t : Tone) (y z cr' : Noun), x = C y cr' ∧
        nock (mookS cr t) eval_mook.battery = some (C z cr') := by
  intro cr hc ton x hx
  by_cases h : ∃ tr, ton = C (A 2) tr
  · obtain ⟨tr, rfl⟩ := h
    exact h2 cr hc tr x hx
  · have h' : ∀ tr, ton ≠ C (A 2) tr := fun tr e => h ⟨tr, e⟩
    rw [eval_mook_not2 cr ton h', Option.some.injEq] at hx
    subst hx
    refine ⟨Tone.zero (A 0), ton, C (A 0) (A 0), cr, rfl, ?_⟩
    have := eval_mook_not2 cr (C (A 0) (A 0)) (fun x e => by simp at e)
    simpa [mookS, Tone.toNoun] using this

end Compiler
end Formalization
