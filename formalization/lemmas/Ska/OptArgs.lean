import lemmas.Ska.OptHopsSim
import lemmas.Ska.OptBranch

/-!
# `ArgsOK` through the proved passes

`+remove-empty-middle` keeps the code only on entries with `ArgsOK`
(`OptMiddleSim.lean`), so `Keeps` must carry `ArgsOK` beside `ReadsOK` before
the driver can use it.  The two other proved passes keep `ArgsOK` (given
`ReadsOK`, which their backward simulations use): `+remove-useless-branching`
because its relation has the same arguments and registers (`rub_argsOK`),
`+remove-hops` because `HopI` has the same arguments with registers in
`RegLe`, which are there together (`RegLe.get_none`), and `HopII` has none
pending after (`hops_argsOK_of`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock Path

variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

/-- **`+remove-useless-branching` keeps `ArgsOK`.** -/
theorem rub_argsOK (c : Straight Map) {ch : Bool} {bl' : Map Blob}
    (h : removeUselessBranching c.blocks = some (ch, bl')) (lib : Lib) (σ : Type) (O : Oracle σ) (gul : Noun)
    (st : σ) (vals : List Noun) (t : Trace) (hok : ReadsOK lib O c gul st vals t)
    (ha : ArgsOK lib O c gul st vals t) : ArgsOK lib O (withBlocks c bl') gul st vals t := by
  have hbl' : RubBlocks c.blocks (withBlocks c bl').blocks := rub_blocks h
  rintro es' y' k ⟨b0'', hb0'', hs'⟩ hk
  cases hb0 : HoonMap.get c.blocks 0 with
  | none => rw [(hbl' 0).1 hb0] at hb0''; cases hb0''
  | some b0 =>
    obtain ⟨e0, he0, hb0'⟩ := (hbl' 0).2 b0 hb0
    rw [hb0'] at hb0''; cases hb0''
    have hr0 : RubRel c.blocks (⟨0, b0, [], regsOf vals, t, st⟩ : Path.Cfg σ Map)
        ⟨0, rubBlob b0 e0, [], regsOf vals, t, st⟩ := ⟨rfl, rfl, rfl, rfl, e0, he0, Or.inl rfl⟩
    have hok' : ∀ es y k, Steps lib O c gul ⟨0, b0, [], regsOf vals, t, st⟩ es y → ReadsAt gul y k →
        ∃ v, read k y.regs = some v := fun es y k hs hk => hok es y k ⟨b0, hb0, hs⟩ hk
    obtain ⟨es, y, hs, hr⟩ := rub_bwd (c' := withBlocks c bl') hbl' hok' hs' (Steps.refl _) hr0
    rw [hr.2.1]
    rw [hr.1] at hk
    exact ha es y k ⟨b0, hb0, hs⟩ hk

/-- **`+remove-hops` keeps `ArgsOK`.** -/
theorem hops_argsOK_of {fuel : Nat} (c : Straight Map) {rev : Map (List Nat)} {topo : List Nat} {ch : Bool}
    {bl' : Map Blob} (HH : HopsHyp c.blocks rev topo) (hn : topo.Nodup) (h0 : topo.head? = some 0)
    (h : removeHops fuel c.blocks rev topo = some (ch, bl')) (lib : Lib) (σ : Type) (O : Oracle σ) (gul : Noun)
    (st : σ) (vals : List Noun) (t : Trace) (hok : ReadsOK lib O c gul st vals t)
    (ha : ArgsOK lib O c gul st vals t) : ArgsOK lib O (withBlocks c bl') gul st vals t := by
  have H : HopsBlocks c.blocks rev topo (withBlocks c bl').blocks := hops_blocks hn h0 h
  obtain ⟨m0, hm0, b0, T, F, hb0, hmt, rfl⟩ := H.zero
  rintro es' y' k ⟨b0'', hb0'', hs'⟩ hk
  rw [hm0] at hb0''; cases hb0''
  have hr0 : HopRel c.blocks rev (⟨0, b0, [], regsOf vals, t, st⟩ : Path.Cfg σ Map)
      ⟨0, merge b0 T F, [], regsOf vals, t, st⟩ :=
    Or.inl ⟨b0, T, F, rfl, rfl, Reach.zero, hb0, hmt, rfl, RegLe.refl _, rfl, rfl⟩
  have hok' : ∀ es y k, Steps lib O c gul ⟨0, b0, [], regsOf vals, t, st⟩ es y → ReadsAt gul y k →
      ∃ v, read k y.regs = some v := fun es y k hs hk => hok es y k ⟨b0, hb0, hs⟩ hk
  obtain ⟨es, y, hs, hn'⟩ := hop_bwd (c' := withBlocks c bl') HH H hok' hs' (Steps.refl _) hr0
  rcases hn' with ⟨-, -, -, b1, T1, F1, ops, -, -, -, -, hp', -⟩ | ⟨b1, T1, F1, hI, -⟩
  · rw [hp'] at hk; simp at hk
  · obtain ⟨-, -, -, -, -, hp', hR, -, -⟩ := hI
    rw [hp'] at hk
    have hy := ha es y k ⟨b0, hb0, hs⟩ hk
    cases e : HoonMap.get y'.regs k with
    | none => rw [(hR.get_none k).mp e] at hy; simp at hy
    | some _ => rfl

end Opt
end SkaModel
end Formalization
