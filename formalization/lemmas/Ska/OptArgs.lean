import lemmas.Ska.OptHopsSim
import lemmas.Ska.OptBranch
import lemmas.Ska.OptMiddleSim

/-!
# `ArgsOK` through the proved passes, and `Keeps` of the three

`+remove-empty-middle` keeps the code only on entries with `ArgsOK`
(`OptMiddleSim.lean`), so `Keeps` carries `ArgsOK` beside `ReadsOK`
(`EntryOK`).  The two other proved passes keep `ArgsOK` (given `ReadsOK`,
which their backward simulations use): `+remove-useless-branching` because
its relation has the same arguments and registers (`rub_argsOK`),
`+remove-hops` because `HopI` has the same arguments with registers in
`RegLe`, which are there together (`RegLe.get_none`), and `HopII` has none
pending after (`hops_argsOK_of`).

With them, `Keeps` of each proved pass: `rub_keeps` (no hypothesis),
`hops_keeps_of` and `hops_keeps` (the hypotheses of `hops_keepsR_of`),
`hopsKeeps` (the statement `HopsKeeps`), and `middle_keeps` (`PassOK` of the
input and of the result, from `middle_keeps_of`).
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

/-- **`+remove-useless-branching` keeps the code.** -/
theorem rub_keeps (c : Straight Map) {ch : Bool} {bl' : Map Blob}
    (h : removeUselessBranching c.blocks = some (ch, bl')) : Keeps c (withBlocks c bl') :=
  keeps_of_R (rub_keepsR c h) fun lib σ O gul st vals t hok ha => rub_argsOK c h lib σ O gul st vals t hok ha

/-- **`+remove-hops` keeps the code**, given what the simulation needs of
`rev` and `topo` (`HopsHyp`), `topo` without duplicates and `0` first. -/
theorem hops_keeps_of {fuel : Nat} (c : Straight Map) {rev : Map (List Nat)} {topo : List Nat} {ch : Bool}
    {bl' : Map Blob} (HH : HopsHyp c.blocks rev topo) (hn : topo.Nodup) (h0 : topo.head? = some 0)
    (h : removeHops fuel c.blocks rev topo = some (ch, bl')) : Keeps c (withBlocks c bl') :=
  keeps_of_R (hops_keepsR_of c HH hn h0 h) fun lib σ O gul st vals t hok ha =>
    hops_argsOK_of c HH hn h0 h lib σ O gul st vals t hok ha

/-- **`+remove-hops` keeps the code**, on a `topo` with `TopoOK`, its
`+rev-cfg`, distinct parameters and jumps that pass the check of
`+eval-pass`. -/
theorem hops_keeps {fuel : Nat} (c : Straight Map) {topo : List Nat} {ch : Bool} {bl' : Map Blob}
    (ht : TopoOK c.blocks topo) (hnd : ParNodup c.blocks) (hpc : PassOK c.blocks)
    (h : removeHops fuel c.blocks (revCfg c.blocks topo) topo = some (ch, bl')) : Keeps c (withBlocks c bl') :=
  hops_keeps_of c ⟨ht.2.2.2.1, fun _ _ _ ho hb hj => revCfg_mem ho hb hj, hnd, hpc⟩ ht.1 ht.2.1 h

/-- **The preservation statement of `+remove-hops` holds.** -/
theorem hopsKeeps (fuel : Nat) : HopsKeeps (Map := Map) fuel :=
  fun c _ _ _ ht hnd hpc h => hops_keeps c ht hnd hpc h

/-- **`+remove-empty-middle` keeps the code**, given `PassOK` of its input
and of its result. -/
theorem middle_keeps {fuel : Nat} (c : Straight Map) {ch : Bool} {bl' : Map Blob}
    (h : removeEmptyMiddle fuel c.blocks = some (ch, bl')) (hpc : PassOK c.blocks) (hpc' : PassOK bl') :
    Keeps c (withBlocks c bl') := by
  obtain ⟨hp, hs⟩ := middle_keeps_of c h hpc hpc'
  refine ⟨rfl, rfl, hp, fun lib σ O gul st vals t ⟨hr, ha⟩ => ?_⟩
  obtain ⟨e, r, a⟩ := hs lib σ O gul st vals t ha
  exact ⟨e, r hr, a⟩

end Opt
end SkaModel
end Formalization
