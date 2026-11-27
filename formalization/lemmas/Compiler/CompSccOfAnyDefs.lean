import lemmas.Compiler.CompSccOfOneGate

/-!
# The invariants of the gate with callees of any SCC: the definitions (README Gaps 19 (g))

Split from `CompSccOfAny.lean` so that `CompMonoLink.lean` (which imports track P's
`PokeLinkGood`) can state `PGoodK` without importing track I's loop files (their
`CompSccLoopStep.swG` clashes with `OptLinkSwNouns.swG`).

* `AgreeIP env P` (`AgreeE` with the bells in progress `P`), `agreeIP_of_E`, `agreeE_of_IP`,
  `agreeIP_mono`;
* `SccsGood`, `SccClosed`, `NaryClosed`, `RK`, `members_miss`, `sccClosed_put`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## The invariant with bells in progress -/

/-- **`AgreeE` with bells in progress `P`**: the clause on `sure.cache` (the value is `env.sure`
and the key is a key of `nary.cache`) only for keys outside `P`. -/
def AgreeIP (env : CallEnv) (P : Noun → Prop) (x : GenRest) : Prop :=
  x.NoSoft ∧ ∃ NR MO SC INL SU, x.cache = cacheN NR MO SC INL SU ∧ IsMap mugF NR ∧ IsMap mugF SU ∧
    (∀ (b : Bell) u, getF mugF b.toNoun NR = some (C (A 0) u) →
      (∃ nb, env.need b = some nb ∧ slot? 2 u = some nb.toNoun) ∧ ∃ v, getF mugF b.toNoun SU = some (C (A 0) v)) ∧
    (∀ (b : Bell) v, getF mugF b.toNoun SU = some (C (A 0) v) → ¬ P b.toNoun →
      v = (env.sure b).toNoun ∧ ∃ u, getF mugF b.toNoun NR = some (C (A 0) u))

theorem agreeIP_of_E {env : CallEnv} {x : GenRest} (P : Noun → Prop) (h : AgreeE env x) : AgreeIP env P x := by
  obtain ⟨hs, NR, MO, SC, INL, SU, hc, h1, h2, h3, h4⟩ := h
  exact ⟨hs, NR, MO, SC, INL, SU, hc, h1, h2, h3, fun b v hv _ => h4 b v hv⟩

theorem agreeE_of_IP {env : CallEnv} {x : GenRest} (h : AgreeIP env (fun _ => False) x) : AgreeE env x := by
  obtain ⟨hs, NR, MO, SC, INL, SU, hc, h1, h2, h3, h4⟩ := h
  exact ⟨hs, NR, MO, SC, INL, SU, hc, h1, h2, h3, fun b v hv => h4 b v hv id⟩

theorem agreeIP_mono {env : CallEnv} {x : GenRest} {P P' : Noun → Prop} (hP : ∀ k, P k → P' k)
    (h : AgreeIP env P x) : AgreeIP env P' x := by
  obtain ⟨hs, NR, MO, SC, INL, SU, hc, h1, h2, h3, h4⟩ := h
  exact ⟨hs, NR, MO, SC, INL, SU, hc, h1, h2, h3, fun b v hv hn => h4 b v hv fun h => hn (hP _ h)⟩

/-! ## `sccs` and `nary` -/

/-- **The meaning of `sccs.cache`** (track P: the product of `+tarjan`, beyond `SccImage`'s
shape): an entry `S` of `k` is a set holding `k`, and every member of `S` is a bell whose
entry is `S`. -/
def SccsGood (SC0 : Noun) : Prop :=
  ∀ k S, getF mugF k SC0 = some (C (A 0) S) → IsSet mugF S ∧ k ∈ tapList S ∧
    ∀ k' ∈ tapList S, getF mugF k' SC0 = some (C (A 0) S) ∧ ∃ b' : Bell, b'.toNoun = k'

/-- The keys of `NR` are a union of whole SCCs of `SC0`. -/
def SccClosed (SC0 NR : Noun) : Prop :=
  ∀ k u, getF mugF k NR = some (C (A 0) u) →
    ∃ S, getF mugF k SC0 = some (C (A 0) S) ∧ ∀ k' ∈ tapList S, ∃ u', getF mugF k' NR = some (C (A 0) u')

/-- `nary.cache` of the rest is `SccClosed`. -/
def NaryClosed (SC0 : Noun) (x : GenRest) : Prop := ∃ NR, slot? 2 x.cache = some NR ∧ SccClosed SC0 NR

/-- **The rest predicate of the gate**: `sccs` fixed, `inl` entries known, `nary` closed. -/
def RK (SC0 : Noun) (inl : Noun → Option Nomm) (x : GenRest) : Prop := RInl SC0 inl x ∧ NaryClosed SC0 x

/-- **Every member of the SCC misses when one does**, on a closed map. -/
theorem members_miss {SC0 NR k0 S : Noun} (hsg : SccsGood SC0) (hsc : getF mugF k0 SC0 = some (C (A 0) S))
    (hcl : SccClosed SC0 NR) (hm : IsMap mugF NR) (h0 : getF mugF k0 NR = some (A 0)) :
    ∀ k ∈ tapList S, getF mugF k NR = some (A 0) := by
  intro k hk
  rcases getF_cases (k := k) hm with h | ⟨u, hu⟩
  · exact h
  · obtain ⟨S', hS', hall⟩ := hcl k u hu
    rw [((hsg k0 S hsc).2.2 k hk).1] at hS'
    simp only [Option.some.injEq, Noun.cell.injEq, true_and] at hS'
    subst hS'
    obtain ⟨u', hu'⟩ := hall k0 (hsg k0 S hsc).2.1
    rw [hu'] at h0
    cases h0

/-- After `+put:by` of a bell whose SCC is itself, the map stays closed. -/
theorem sccClosed_put {SC0 NR NRU B v : Noun} (hnr : IsMap mugF NR) (h0 : getF mugF B NR = some (A 0))
    (hpn : putF mugF B v NR = some NRU) (hsc : getF mugF B SC0 = some (C (A 0) (setOne B)))
    (hcl : SccClosed SC0 NR) : SccClosed SC0 NRU := by
  intro k u hu
  rcases getF_put_cases hnr hpn hu with ⟨e, -⟩ | ⟨-, hu'⟩
  · subst e
    refine ⟨_, hsc, fun k' hk' => ?_⟩
    simp [setOne, tapList] at hk'
    subst hk'
    exact ⟨_, (getF_put_self hnr hpn).2⟩
  · obtain ⟨S, hS, hall⟩ := hcl k u hu'
    refine ⟨S, hS, fun k' hk' => ?_⟩
    obtain ⟨u', h'⟩ := hall k' hk'
    exact ⟨u', mapSub_put hnr h0 hpn _ _ h'⟩

end Compiler
end Formalization
