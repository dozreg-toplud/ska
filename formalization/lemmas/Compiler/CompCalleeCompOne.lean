import lemmas.Compiler.CompUnaryDirE
import lemmas.Compiler.CompSccGate

/-!
# `CccMiss` for a callee whose SCC is one bell (README Gaps 19 (g))

* `ccc_csi_eq`: the push of `+compile-scc-in` in the miss branch is the gate
  body `csiBody` on `[new-scc long-ska jets-hot cache]` (as `cu_csi_eq` is in
  the trap of `+compile-unary`).
* `getF_one`: the lookup in the map `[[B st] ~ ~]` of `+compile-scc-in`.
* **`cccMiss_one`**: `CccMiss` from the gate of `+scc-of` returning the
  singleton `[b ~ ~]` (named, `hscc`: not linked) and the gate body of
  `+compile-scc-in` on it returning `[[[b st] ~ ~] CA']` (the shape of track
  A's `csi_gate_scc_one_f_six_L`, `hcsi1`), with the need `nb` at the head of
  `st`.
* `get_of_getF`, **`mapSub_put`**: `+put:by` of a key the map lacks keeps every
  entry; **`ext_one`**: so the one-bell compile's cache
  `[(put b st NR) MO SC' INL' (put b sur SU)]` is an `Ext` step.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-- **The push of `+compile-scc-in` in the miss branch** is the gate body on
`[NS long-ska jets-hot cache]` (axes `26`, `54` of the context, `cache` of
the rest). -/
theorem ccc_csi_eq {ctx LONG JH : Noun} (h7 : slot? 7 ctx = some compK) (hl : slot? 26 ctx = some LONG)
    (hj : slot? 54 ctx = some JH) (NS : Noun) (b : Bell) (g : Gen (TreapMap mugF)) (x : GenRest) :
    nock (C NS (cccS0 b g x ctx)) cccCsiF = nock (C csiBody (C (csiSam NS LONG JH x.cache) compK)) csiBody := by
  have ha := csi_at
  unfold cccS0 cccCsiF csiSam
  simp only [compCore, genNoun]
  generalize compK = KC at ha h7 ⊢
  simp [nock_exec, ha, csi_arm, h7, hl, hj]

/-- The lookup of the key in a map of one entry. -/
theorem getF_one (B st : Noun) : getF mugF B (C (C B st) (C (A 0) (A 0))) = some (C (A 0) st) := by
  simp [getF]

/-- **`CccMiss` for a one-bell callee SCC**: the gate of `+scc-of` on the
subject of the miss returns the singleton `[b ~ ~]` with `sccs` `SC'`
(`hscc`, named), and the gate body of `+compile-scc-in` on `[[b ~ ~]
long-ska jets-hot cache]` with `sccs` set to `SC'` returns `[[[b st] ~ ~]
CA']` (`hcsi1`, the shape of `csi_gate_scc_one_f_six_L`), with the need `nb`
at axis `2` of `st`. -/
theorem cccMiss_one {ctx LONG JH : Noun} (h7 : slot? 7 ctx = some compK) (hl : slot? 26 ctx = some LONG)
    (hj : slot? 54 ctx = some JH) (b : Bell) (nb : NeedOrd) {NR MO SC RS SO SS SC' st CA' : Noun}
    (hscc : ∀ g, nock (cccS0 b g (ccRest NR MO SC RS SO SS) ctx) cccSccF = some (C (setOne b.toNoun) SC'))
    (hcsi1 : nock (C csiBody (C (csiSam (setOne b.toNoun) LONG JH (C NR (C MO (C SC' RS)))) compK)) csiBody
      = some (C (C (C b.toNoun st) (C (A 0) (A 0))) CA'))
    (hst : slot? 2 st = some nb.toNoun) :
    CccMiss ctx b nb NR MO SC RS SO SS CA' :=
  ⟨setOne b.toNoun, SC', C (C b.toNoun st) (C (A 0) (A 0)), st, hscc,
    fun g => (ccc_csi_eq h7 hl hj _ b g _).trans hcsi1, getF_one _ _, hst⟩

/-- On a map, a hit of `getF` is an entry. -/
theorem get_of_getF {M k u : Noun} (hm : IsMap mugF M) (h : getF mugF k M = some (C (A 0) u)) : Get M k u := by
  by_cases hx : ∃ v, Get M k v
  · obtain ⟨v, hg⟩ := hx
    rw [getF_some hm hg] at h
    cases h
    exact hg
  · rw [getF_none hm fun v hg => hx ⟨v, hg⟩] at h
    cases h

/-- **`+put:by` of a key the map lacks keeps every entry.** -/
theorem mapSub_put {M M' k v : Noun} (hm : IsMap mugF M) (hk : getF mugF k M = some (A 0))
    (hp : putF mugF k v M = some M') : MapSub M M' := by
  obtain ⟨out, hput, hmo, hget⟩ := putF_spec mugF M k v hm
  rw [hp] at hput
  cases hput
  intro k' u h
  have hg := get_of_getF hm h
  have hne : k' ≠ k := by
    rintro rfl
    rw [hk] at h
    cases h
  exact getF_some hmo ((hget k' u).2 (Or.inr ⟨hne, hg⟩))

/-- **The one-bell compile's cache is an `Ext` step**: `nary.cache` and
`sure.cache` gain the key `B` (absent in both before), the rest of the cache
may change (`sccs`, `inl`), `soft` and `sofs` stay. -/
theorem ext_one {NR MO SC INL SU MO' SC' INL' NRU SUU B st sur : Noun} {so ss : Noun}
    (hnr : IsMap mugF NR) (hsu : IsMap mugF SU) (hkn : getF mugF B NR = some (A 0))
    (hks : getF mugF B SU = some (A 0)) (hpn : putF mugF B st NR = some NRU) (hps : putF mugF B sur SU = some SUU) :
    Ext ⟨cacheN NR MO SC INL SU, so, ss⟩ ⟨cacheN NRU MO' SC' INL' SUU, so, ss⟩ := by
  refine ⟨rfl, rfl, fun N hN => ?_, fun S hS => ?_⟩
  · have : N = NR := by simpa [cacheN, nock_exec] using hN.symm
    subst this
    exact ⟨NRU, by simp [cacheN, nock_exec], mapSub_put hnr hkn hpn⟩
  · have : S = SU := by simpa [cacheN, nock_exec] using hS.symm
    subst this
    exact ⟨SUU, by simp [cacheN, nock_exec], mapSub_put hsu hks hps⟩

end Compiler
end Formalization
