import lemmas.Compiler.TreapKey

/-!
# `+cole-put` and the coherence of `cole` (track P, README Gaps 23)

The maps of `cole.jets`: `call` (bell to ring) and `back` (ring to the set of
its bells), at the level of `FinMap` (`ColeM`), with `+cole-put`
(`colePutM`: `+put:by` on `call`, `+put:ju` on `back`) and the coherence
`ColeCohM` (`call` maps `b` to `r` iff `b` is in `back` of `r`; the noun form
is `ColeCoh` of `PokeLinkGood5.lean`).

* `coleCohM_put`: `+cole-put` of a bell that has no ring keeps coherence.
* `coleCohM_put_bad`: of a bell that has another ring, it breaks it (the old
  ring's set keeps the bell): so the `ColeCoh` step of `+ska-cole-update`
  needs the new bells to have no ring, which holds when the keys of `call`
  are keys of `code` (`new-code` holds no key of `code`).
* `coleCohM_fold`: the fold of `+ska-cole-update` over distinct bells with
  no ring, each put with the ring a matcher gives (any matcher), keeps it.
-/

namespace Formalization
namespace Compiler

variable {κ ρ : Type} [DecidableEq κ] [DecidableEq ρ]

/-- `cole` at the map level. -/
structure ColeM (κ ρ : Type) where
  call : FinMap κ ρ
  back : FinMap ρ (FinMap κ Unit)

/-- `call` maps `b` to `r` iff `b` is in `back` of `r`. -/
def ColeCohM (c : ColeM κ ρ) : Prop :=
  ∀ b r, c.call.get b = some r ↔ ∃ S, c.back.get r = some S ∧ S.get b = some ()

/-- `+cole-put`: `[(~(put by call.c) b r) (~(put ju back.c) r b)]`. -/
def colePutM (b : κ) (r : ρ) (c : ColeM κ ρ) : ColeM κ ρ :=
  ⟨c.call.put b r, c.back.put r (((c.back.get r).getD FinMap.empty).put b ())⟩

theorem coleCohM_put {c : ColeM κ ρ} {b : κ} (r : ρ) (h : ColeCohM c) (hb : c.call.get b = none) :
    ColeCohM (colePutM b r c) := by
  intro b' r'
  simp only [colePutM, FinMap.get, FinMap.put]
  by_cases e : b' = b
  · subst e
    by_cases er : r' = r
    · subst er; simp only [if_true, true_iff]; exact ⟨_, rfl, by simp⟩
    · have h1 := h b' r'
      simp only [FinMap.get] at hb h1
      rw [hb] at h1
      simp only [er, if_false, if_true, Option.some.injEq]
      constructor
      · intro hh; exact absurd hh.symm er
      · intro hh; exact absurd (h1.2 hh) (by simp)
  · by_cases er : r' = r
    · subst er
      have h1 := h b' r'
      simp only [FinMap.get] at h1
      simp only [e, if_false, if_true]
      constructor
      · intro hc
        obtain ⟨S, hS, hSb⟩ := h1.1 hc
        refine ⟨_, rfl, ?_⟩
        simp [e, hS, hSb]
      · rintro ⟨S, hS, hSb⟩
        cases hS
        simp only [e, if_false] at hSb
        rcases hbk : c.back.1 r' with _ | S0
        · rw [hbk] at hSb; exact absurd hSb (by show (none : Option Unit) ≠ some (); simp)
        · rw [hbk] at hSb; exact h1.2 ⟨S0, hbk, hSb⟩
    · have h1 := h b' r'
      simp only [FinMap.get] at h1
      simp only [e, er, if_false]
      exact h1

/-- **The finding**: `+cole-put` of a bell with another ring breaks coherence. -/
theorem coleCohM_put_bad {c : ColeM κ ρ} {b : κ} {r r0 : ρ} (h : ColeCohM c) (hb : c.call.get b = some r0)
    (hr : r ≠ r0) : ¬ ColeCohM (colePutM b r c) := by
  intro h'
  obtain ⟨S, hS, hSb⟩ := (h b r0).1 hb
  have := (h' b r0).2 ⟨S, by simp only [colePutM, FinMap.get, FinMap.put, Ne.symm hr, if_false]; exact hS, hSb⟩
  simp only [colePutM, FinMap.get, FinMap.put, if_true, Option.some.injEq] at this
  exact hr this

/-- The fold of `+ska-cole-update`: each bell put with its match, if any. -/
def coleUpdM (m : κ → Option ρ) : List κ → ColeM κ ρ → ColeM κ ρ
  | [], c => c
  | b :: l, c => coleUpdM m l (match m b with
    | none => c
    | some r => colePutM b r c)

/-- **`+ska-cole-update` keeps coherence** on distinct bells with no ring. -/
theorem coleCohM_fold (m : κ → Option ρ) :
    ∀ (l : List κ) (c : ColeM κ ρ), l.Nodup → (∀ b ∈ l, c.call.get b = none) → ColeCohM c →
      ColeCohM (coleUpdM m l c)
  | [], c, _, _, h => h
  | b :: l, c, hn, hf, h => by
    simp only [coleUpdM]
    have hn' := (List.nodup_cons.1 hn)
    cases e : m b with
    | none => exact coleCohM_fold m l c hn'.2 (fun x hx => hf x (List.mem_cons_of_mem _ hx)) h
    | some r =>
      refine coleCohM_fold m l _ hn'.2 (fun x hx => ?_) (coleCohM_put r h (hf b List.mem_cons_self))
      have hxb : x ≠ b := fun e => hn'.1 (e ▸ hx)
      simp only [colePutM, FinMap.get, FinMap.put, hxb, if_false]
      exact hf x (List.mem_cons_of_mem _ hx)

end Compiler
end Formalization
