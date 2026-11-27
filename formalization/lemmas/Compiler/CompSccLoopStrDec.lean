import lemmas.Compiler.CompSccLoopStrGen

/-! # The loop's product decoded (README Gaps 21.17)

* **`csi_gate_ranked_dec`**: `csi_gate_rankedStr` with `PrintId` discharged (`printId_pill`) and
  the members bells: the gate's `M` is `FinMap.toNoun Straight.toNoun m` for a map of straights
  `m` whose needs are the model's final `ml` (the shape `unaryImageAt_of_gate` asks of `NM`).
* `finUni`, **`uni_decode`**: the `+uni:by` of two maps of straights (`UniSpec`, as the loop's
  `NARYU`) is the noun of their union, the second's pairs winning: so `nary` after the loop
  decodes once the `nary` the last member run leaves decodes (track K's decoding (b)). -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop SkaModel.Ana

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- **The loop's gate with its `M` decoded.** -/
theorem csi_gate_ranked_dec (c : Cfg Noun NeedOrd) (r : Ranked c) (bs : List Noun)
    (outC : Noun → List Noun) (nout : Noun → NeedOrd) (Q : Noun → Prop)
    (SCC CODE JETS CALLS JH NARY CR : Noun) (hsam : SamOK SCC CALLS NARY)
    (hmiss : ∃ b ∈ tapList SCC, getF mugF b NARY = some (A 0))
    (hnd : (∀ n, SCC ≠ C n (C (A 0) (A 0))) ∨ ∃ n, SCC = C n (C (A 0) (A 0)) ∧ CalleeIn CALLS n n)
    (hcfg : CfgOf c SCC (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR)))
    (hbell : ∀ k ∈ tapList SCC, ∃ b' : Bell, b'.toNoun = k)
    (hmay : MemGate c (LoopRS bs outC nout Q) (csiCtx (A 1) (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR))
      SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) (fun _ => c.none) (A 0) Mode.may (A 0x79616d))
    (hdone : MemGate c (LoopRS bs outC nout Q) (csiCtx (A 1) (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR))
      SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) (fun _ => c.none) (A 0) Mode.done (A 0x656e6f64))
    (st0 : St Noun NeedOrd)
    (hmust : ∀ TOP, TopN (maySweep c st0).ml TOP → MemGate c (LoopRS bs outC nout Q)
      (csiCtx (A 1) (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) SCC (C CODE (C JETS CALLS)) JH (C NARY CR))
      (topOf c (maySweep c st0)) TOP Mode.must (A 0x7473756d))
    (hQ : ∀ CA, Q CA → ∃ NR REST, CA = C NR REST ∧ IsMap mugF NR)
    (hml0 : ∀ b, st0.ml b = none) (hsu0 : SureHolds bs st0.sure (C NARY CR)) (hq0 : Q (C NARY CR)) :
    ∃ s, compileSccIn c false (4 * c.scc.length + c.order.length * (r.H + 1) + 2) st0 = some s ∧
      (∀ b ∈ c.scc, (s.ml b).isSome) ∧ (∀ k, k ∉ c.scc → s.ml k = none) ∧
      ∃ M NR REST NARYU, LoopRS bs outC nout Q s.ml s.sure M (C NR REST) ∧ IsMap mugF NR ∧
        IsMap mugF NARYU ∧ UniSpec NR M NARYU ∧
        nock (C csiBody (C (csiSam SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) compK)) csiBody
          = some (C M (C NARYU REST)) ∧
        ∃ m : FinMap Bell (Straight (TreapMap mugF)), M = m.toNoun Straight.toNoun ∧
          ∀ b : Bell, (m.1 b).map Straight.need = s.ml b.toNoun := by
  obtain ⟨s, hs, hin, hout, M, NR, REST, NARYU, hR, hNR, hU, hus, hgo⟩ :=
    csi_gate_rankedStr c r bs outC nout Q SCC CODE JETS CALLS JH NARY CR hsam hmiss hnd hcfg hmay hdone st0
      hmust hQ (fun _ _ => printId_pill _) hml0 hsu0 hq0
  refine ⟨s, hs, hin, hout, M, NR, REST, NARYU, hR, hNR, hU, hus, hgo, ml_decode hR.1.1 hR.2 fun k hk => ?_⟩
  have hk' : k ∈ c.scc := Classical.byContradiction fun h => by rw [hout k h] at hk; cases hk
  rw [hcfg.scc] at hk'
  exact hbell k hk'

/-- The union of two maps with the pairs of `m` over those of `n` (`(~(uni by n) m)`). -/
def finUni {κ ν : Type} (m n : FinMap κ ν) : FinMap κ ν :=
  ⟨fun k => match m.1 k with
    | some v => some v
    | none => n.1 k, by
    obtain ⟨l1, h1⟩ := m.2
    obtain ⟨l2, h2⟩ := n.2
    exact ⟨l1 ++ l2, fun k h => by
      cases e : m.1 k with
      | some v => exact List.mem_append_left _ (h1 k (by rw [e]; simp))
      | none => simp only [e] at h; exact List.mem_append_right _ (h2 k h)⟩⟩

/-- **`+uni:by` of two maps of straights decoded**: a map `NARYU` with the pairs `UniSpec` gives
for `NR` and `M` (as at the end of the loop) is the noun of `finUni m n`. -/
theorem uni_decode {n m : FinMap Bell (Straight (TreapMap mugF))} {NARYU : Noun} (hu : IsMap mugF NARYU)
    (hs : UniSpec (n.toNoun Straight.toNoun) (m.toNoun Straight.toNoun) NARYU) :
    NARYU = (finUni m n).toNoun Straight.toNoun := by
  refine isMap_ext hu (FinMap.isMap_toNoun _ _) (fun kn vn => ?_)
  rw [hs, FinMap.get_toNoun, FinMap.get_toNoun, FinMap.get_toNoun]
  constructor
  · rintro (⟨k, v, h1, rfl, rfl⟩ | ⟨⟨k, v, h1, rfl, rfl⟩, hn⟩)
    · exact ⟨k, v, by simp [finUni, h1], rfl, rfl⟩
    · refine ⟨k, v, ?_, rfl, rfl⟩
      cases e : m.1 k with
      | some w => exact absurd ⟨w.toNoun, (FinMap.get_toNoun _ m _ _).2 ⟨k, w, e, rfl, rfl⟩⟩ hn
      | none => simp [finUni, e, h1]
  · rintro ⟨k, v, h1, rfl, rfl⟩
    cases e : m.1 k with
    | some w =>
      simp only [finUni, e, Option.some.injEq] at h1
      subst h1
      exact Or.inl ⟨k, w, e, rfl, rfl⟩
    | none =>
      simp only [finUni, e] at h1
      refine Or.inr ⟨⟨k, v, h1, rfl, rfl⟩, ?_⟩
      rintro ⟨w, hw⟩
      obtain ⟨k', w', h2, h3, -⟩ := (FinMap.get_toNoun _ m _ _).1 hw
      obtain rfl := TKey.enc_inj _ _ h3
      rw [e] at h2; cases h2

end Compiler
end Formalization
