import lemmas.Compiler.OptLinkTotalN
import lemmas.Ska.OptAliasSSAMid
import lemmas.Ska.OptAliasSSARub
import lemmas.Ska.RawInvBase

/-!
# The passes keep `ReadsIn N`: the passes that keep every definition

`readsIn_of_lift`: `ReadsIn N` passes from `bl` to `bl'` when every read of
a reachable block of `bl'` of a register that `bl'` does not define is a read
of a reachable block of `bl`, and `bl'` keeps every definition of `bl` of
such a register.  `+remove-useless-branching` (`rub_reads`),
`+remove-empty-middle` (`mid_reads`: a substituted argument is read at the end
of the bypassed block, which is reachable) and `+trim-trace-hints`
(`trim_reads`: it drops hints, which define nothing) keep the definitions of
every block.
-/

namespace Formalization
namespace Compiler

open Nock SkaModel Opt

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

section
variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

theorem allDefs_iff {bl : Map Blob} {r : Nat} :
    r ∈ allDefs bl ↔ ∃ o b, HoonMap.get bl o = some b ∧ r ∈ blockDefs b :=
  Raw.mem_allDefs.trans Raw.defd_iff

/-- **`ReadsIn N` from a lift of the reads.** -/
theorem readsIn_of_lift {N : Nat} {bl bl' : Map Blob} (hR : ReadsIn N bl)
    (hl : ∀ o' b' i r, Reach bl' o' → HoonMap.get bl' o' = some b' → ReadAt b' i r → r ∉ allDefs bl' →
      (∃ o b i', Reach bl o ∧ HoonMap.get bl o = some b ∧ ReadAt b i' r) ∧ (r ∈ allDefs bl → r ∈ allDefs bl')) :
    ReadsIn N bl' := by
  intro o' b' i r hr hb hrd
  by_cases hd : r ∈ allDefs bl'
  · exact Or.inl hd
  · obtain ⟨⟨o, b, i', hro, hbo, hrd'⟩, hk⟩ := hl o' b' i r hr hb hrd hd
    rcases hR o b i' r hro hbo hrd' with h | h
    · exact absurd (hk h) hd
    · exact Or.inr h

/-- A map whose blocks keep the definitions of the blocks of `bl` keeps
`allDefs`. -/
theorem allDefs_mono {bl bl' : Map Blob}
    (h : ∀ o b, HoonMap.get bl o = some b → ∃ b', HoonMap.get bl' o = some b' ∧ blockDefs b' = blockDefs b)
    {r : Nat} (hr : r ∈ allDefs bl) : r ∈ allDefs bl' := by
  obtain ⟨o, b, hb, hm⟩ := allDefs_iff.mp hr
  obtain ⟨b', hb', he⟩ := h o b hb
  exact allDefs_iff.mpr ⟨o, b', hb', he ▸ hm⟩

/-- **`+remove-useless-branching` keeps `ReadsIn N`.** -/
theorem rub_reads {N : Nat} {bl bl' : Map Blob} {ch : Bool} (h : removeUselessBranching bl = some (ch, bl'))
    (hR : ReadsIn N bl) : ReadsIn N bl' := by
  have hB := rub_blocks h
  refine readsIn_of_lift hR fun o' b' i r hr hb hrd _ => ⟨?_, allDefs_mono fun o b hb0 => ?_⟩
  · obtain ⟨b, e, hb0, he, rfl⟩ := hB.back hb
    exact ⟨o', b, _, ssk_rub_reach hB hr, hb0, ssk_rub_read he hrd⟩
  · obtain ⟨e, he, hb'⟩ := (hB o).2 b hb0
    exact ⟨_, hb', ssk_rub_defs he⟩

/-- **`+remove-empty-middle` keeps `ReadsIn N`.** -/
theorem mid_reads {N fuel : Nat} {bl bl' : Map Blob} {ch : Bool} (h : removeEmptyMiddle fuel bl = some (ch, bl'))
    (hR : ReadsIn N bl) : ReadsIn N bl' := by
  have hM := mid_blocks h
  refine readsIn_of_lift hR fun o' b' i r hr hb hrd _ => ⟨?_, allDefs_mono fun o b hb0 => ?_⟩
  · obtain ⟨b, f', hb0, hf, rfl⟩ := hM.back hb
    have hro := ssk_mid_reach hM hr
    rcases hrd with hrd | ⟨hi, hrf⟩
    · exact ⟨o', b, i, hro, hb0, Or.inl hrd⟩
    · rcases (ssk_mfin hf).2 r hrf with hrf | ⟨j, hj, l, m, bm, hc, hbm, hbe, hrm, -⟩
      · exact ⟨o', b, i, hro, hb0, Or.inr ⟨hi, hrf⟩⟩
      · exact ⟨m, bm, 0, ssk_chain_reach hc (Reach.jump hro hb0 hj), hbm, Or.inr ⟨by rw [hbe]; rfl, hrm⟩⟩
  · obtain ⟨f', -, hb'⟩ := (hM o).2 b hb0
    exact ⟨_, hb', rfl⟩

/-- **Filtering bodies by a test that keeps every op writing a register keeps
`ReadsIn N`.** -/
theorem filt_reads {N : Nat} {bl bl' : Map Blob} {p : Pole → Bool}
    (hg : ∀ o, HoonMap.get bl' o = (HoonMap.get bl o).map fun b => { b with body := b.body.filter p })
    (hp : ∀ op, p op = false → aliasDst op = none) (hR : ReadsIn N bl) : ReadsIn N bl' := by
  refine readsIn_of_lift hR fun o' b' i r hr hb hrd _ => ⟨?_, allDefs_mono fun o b hb0 => ?_⟩
  · rw [hg] at hb
    obtain ⟨b, hb0, rfl⟩ := Option.map_eq_some_iff.mp hb
    exact ⟨o', b, _, reach_filt hg hr, hb0, readAt_filt hg hrd⟩
  · refine ⟨_, by rw [hg, hb0]; rfl, ?_⟩
    simp only [blockDefs, filt_defs p hp]

/-- **`+trim-trace-hints` keeps `ReadsIn N`.** -/
theorem trim_reads {N : Nat} {bl : Map Blob} {topo : List Nat} {rev : Map (List Nat)} {bl' : Map Blob}
    (h : trimTraceHints bl topo rev = some bl') (hR : ReadsIn N bl) : ReadsIn N bl' := by
  unfold trimTraceHints at h
  obtain ⟨uns, -, rfl⟩ := Option.map_eq_some_iff.mp h
  refine filt_reads (p := tkeep uns (trimOpened bl)) (trimRun_get bl uns (trimOpened bl)) (fun op hop => ?_) hR
  have hd : trimDrop uns (trimOpened bl) op = true := by simpa [tkeep] using hop
  obtain ⟨_, _, hk, -⟩ := trimDrop_true hd
  cases op <;> first | rfl | simp [traceKey] at hk

end

end Compiler
end Formalization
