import lemmas.Ska.OptAliasPlain
import lemmas.Ska.OptAliasWitness

/-!
# The driver under plain single assignment

**`driverHypR_of`**: with the model of `+alias` (any `pick` that picks a
member of its list), the real `+trim-trace-hints` and the model of
`+switch-chains`, every field of `DriverHyp` holds at the block invariant
`DInvR` (`OptAliasPlain.lean`) and `TopoInvR`: each pass keeps `DInvS` by the
theorems stated at `DInvS` (`DInvR` implies it), and `DefOnceR` by
`hops_onceR`, `rub_onceR`, `mid_onceR`, `alias_onceR`, `trim_onceR`,
`dead_onceR`; for `+alias`, `DefOnceB` of the result is `alias_onceB` with
`FillFresh` from `DefOnceR` (`alias_fieldR`).

**`optimize_keeps_plain`**: `optimizeF` keeps the code (`Keeps`) on blocks
with `DInvR`, given only `hpick`; **`optimize_keeps_plain_pickR`** is the
same for the passes of the Hoon (`pickR`, the first key of `rap` of a
`+silt`), with no hypothesis but `DInvR` of the input blocks.  It replaces
`optimize_keeps_aliasO`, whose hypothesis `AliasOnceB` is false.

**`OptIn`**: the invariant of raw `+comp` output that the optimizer needs,
written out field by field (`optIn_iff`: it is `DInvR`), for track C.

The witnesses of `OptAliasWitness.lean` violate it: in `vBlocks` and in
`wBlocks` register `2` has two definitions in reachable blocks, the `%inc`
of block `0` and the fill of `+crash-need` (`not_defOnceR_v`,
`not_defOnceR_w`), and neither has `FillFresh` (`not_fillFresh_v`,
`not_fillFresh_w`).

The two passes that turn an ordinary `%imm` into a dead fill, on the
examples of the header of `OptAliasPlain.lean`, evaluated on `LM`:
`ex_hops` (`+remove-hops` merges the block `[%bom ~]` into
`[%imm 5 1]`, `[%hop [~ 1]]`) and `ex_alias` (`+alias` turns
`[%brn 1 [~ 1] [~ 2]]` into `[%bom ~]` after `[%imm 5 1]`, and drops blocks
`1` and `2`).
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock

section
variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

set_option linter.unusedSectionVars false

/-- **The field `alias` at `DInvR`** for the model: it keeps the code,
`DInvR`, and `TopoInvR` of the filtered `topo` with its `+rev-cfg`. -/
theorem alias_fieldR {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) {n : Nat}
    {bl : Map Blob} {topo : List Nat} {rev : Map (List Nat)} {f : Bool} {bl' : Map Blob} (hD : DInvR bl)
    (hT : TopoInvR bl topo rev) (h : aliasM pick n bl rev topo = some (f, bl')) :
    KeepsB bl bl' ∧ DInvR bl' ∧
      TopoInvR bl' (topo.filter fun o => (HoonMap.get bl' o).isSome)
        (revCfg bl' (topo.filter fun o => (HoonMap.get bl' o).isSome)) := by
  have hS := dInvR_dInvS hD
  have hk := alias_keepsB hpick hS hT h
  unfold aliasM at h
  obtain ⟨g, hg, he⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at he
  obtain ⟨-, rfl⟩ := he
  obtain ⟨hpo, hdp, hK, hss⟩ := alias_restSSAB_fresh hpick hS hT hg (fillFresh_of_R hD.2.2.2)
  have hdt := hD.1
  exact ⟨hk, dInvR_of ⟨⟨⟨⟨alias_parNodup hT hdt.1.1.1 hg, hpo⟩, alias_acyclic hT hdt.1.2.1 hg, hdp⟩, hK⟩, hss,
    alias_nolti hT hD.2.2.1 hg⟩ (alias_onceR hT hg hD.2.2.2), alias_topoInvR hT hg⟩

/-- **Every field of `DriverHyp` at `DInvR`**, with the model of `+alias`,
the real trim pass and the model switch pass. -/
theorem driverHypR_of {fuel sfuel : Nat} {P : Passes Map} {pick : List Nat → Nat}
    (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (ha : P.alias = aliasM pick) (ht : P.trim = trimTraceHints)
    (hsw : P.switch = switchChains sfuel) : DriverHyp fuel P DInvR TopoInvR where
  topo := fun bl topo hb h => ⟨topo_field hb.1.1 h, revCfg_sound bl topo⟩
  hops := fun bl topo rev ch bl' hb hi h => by
    have hS := dInvR_dInvS hb
    obtain ⟨k, d, t⟩ := hops_fieldD hb.1.1 hi.1 h
    obtain ⟨Kt, hK⟩ := hb.1.2
    have hss : AliasSSAB bl' := hopsSSA_of hopsOnce_proved bl topo rev ch bl' hb.1 hi.1 hS.2.1 h
    refine ⟨k, dInvR_of ⟨⟨d, Kt, hops_trimBr hi.1.1.1 hi.1.1.2.1 h hK⟩, hss,
      nolti_hops hb.2.2.1 hi.1.1.1 hi.1.1.2.1 h⟩ (hops_onceR hb.1 hi.1 h hb.2.2.2), fun e => ⟨t e, ?_⟩⟩
    subst e
    exact rvs_eq hi.2 (hops_same hi.1.1.1 h).1
  rub := fun bl topo rev ch bl' hb h => by
    have hS := dInvR_dInvS hb
    obtain ⟨k, d, t⟩ := rub_fieldD hb.1.1 h
    obtain ⟨Kt, hK⟩ := hb.1.2
    refine ⟨k, dInvR_of ⟨⟨d, Kt, rub_trimBr h hK⟩, ssk_rub h hS.2.1, nolti_rub hb.2.2.1 h⟩
      (rub_onceR h hb.2.2.2), fun hi e => ⟨t hi.1 e, ?_⟩⟩
    subst e
    exact rvs_rub hi.2 h
  middle := fun bl topo rev ch bl' hb h => by
    have hS := dInvR_dInvS hb
    obtain ⟨k, d, t⟩ := middle_fieldD hb.1.1 h
    obtain ⟨Kt, hK⟩ := hb.1.2
    refine ⟨k, dInvR_of ⟨⟨d, Kt, mid_trimBr h hK⟩, ssk_mid h hS.2.1, nolti_mid hb.2.2.1 h⟩
      (mid_onceR h hb.2.2.2), fun hi e => ⟨t hi.1 e, ?_⟩⟩
    subst e
    exact rvs_eq hi.2 fun k _ => mid_same h k
  alias := fun n bl topo rev f bl' hb hi h => by
    rw [ha] at h
    exact alias_fieldR hpick hb hi h
  trim := fun bl topo rev bl' hb hi h => by
    rw [ht] at h
    obtain ⟨k, d, t⟩ := trim_fieldT hb.1 hi.1 h
    have hs := trim_shape h
    exact ⟨k, ⟨d, (trim_ssa h (dInvR_dInvS hb).2.1).2, nolti_shape hb.2.2.1 hs.1,
      trim_onceR h hb.2.2.2⟩, t, rvs_shape hi.2 hs.1 fun k hk => by rw [hs.2 k]; exact hi.1.1.2.2.1 k hk⟩
  dead := fun bl topo rev bl' hb hi h => by
    obtain ⟨Kt, hK⟩ := hb.1.2
    obtain ⟨d, t⟩ := dead_inv hb.1.1 hi.1 h
    have hs := dead_shape h
    exact ⟨fun c hc => by subst hc; exact dead_keeps c hi.1.1 h,
      ⟨⟨d, Kt, dead_trimBr hi.1.1 h hK⟩, (ssk_dead hi.1.1 h (dInvR_dInvS hb).2.1).2, nolti_shape hb.2.2.1 hs.1,
        dead_onceR hi.1.1 h hb.2.2.2⟩, t,
      rvs_shape hi.2 hs.1 fun k hk => hs.2 k (List.mem_reverse.mpr hk)⟩
  switch := fun bl bl' hb h => by rw [hsw] at h; exact switch_fieldT _ hb.1 h

/-- **`+optimize` with the model of `+alias` keeps the code** on blocks with
`DInvR`, given only that `pick` picks a member of its list. -/
theorem optimize_keeps_plain {fuel sfuel : Nat} {P : Passes Map} {pick : List Nat → Nat}
    (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (ha : P.alias = aliasM pick) (ht : P.trim = trimTraceHints)
    (hsw : P.switch = switchChains sfuel) {s s' : Straight Map} (hb : DInvR s.blocks)
    (h : optimizeF fuel P s = some s') : Keeps s s' :=
  optimize_keeps (driverHypR_of hpick ha ht hsw) hb h

/-- **`+optimize` with the passes of the Hoon keeps the code** on blocks with
`DInvR`: `+alias` with `pickR`, the real `+trim-trace-hints`, the model of
`+switch-chains`; no hypothesis but `DInvR` of the input blocks. -/
theorem optimize_keeps_plain_pickR (M : Type → Type → Type) [Ana.Treap M] {fuel sfuel : Nat}
    {s s' : Straight Map} (hb : DInvR s.blocks)
    (h : optimizeF fuel ⟨aliasM (Ana.pickR M), trimTraceHints, switchChains sfuel⟩ s = some s') : Keeps s s' :=
  optimize_keeps_plain (fun l hl => Ana.pickR_mem l hl) rfl rfl rfl hb h

/-! ## What raw `+comp` output owes the optimizer -/

/-- **The invariant of raw `+comp` output that `+optimize` needs** (for
track C), field by field; `optIn_iff`: it is `DInvR`. -/
structure OptIn (bl : Map Blob) : Prop where
  /-- The parameters of each block are distinct. -/
  parNodup : ParNodup bl
  /-- Every jump passes the check of `+eval-pass`: as many arguments as
  parameters, each argument register a register the block may read. -/
  passOK : PassOK bl
  /-- No cycle: a rank that falls along every jump. -/
  acyclic : Acyclic bl
  /-- The parameters of a block are written by no op of a block below it. -/
  downPar : DownPar bl
  /-- Trace hints are bracketed: every block opens and closes the hints that a
  key list says (`TrimBr`). -/
  trimBr : ∃ K, TrimBr bl K
  /-- Every read of a register with a definition is preceded, along every path
  of blocks from `0`, by a definition of it. -/
  defFirst : DefFirst bl
  /-- No end is `%lti` (only `+switch-chains`, after the loop, makes one). -/
  noLti : NoLti bl
  /-- Every register has at most one definition (parameter or op) in the blocks
  reachable from `0`. -/
  defOnce : DefOnceR bl

theorem optIn_iff {bl : Map Blob} : OptIn bl ↔ DInvR bl :=
  ⟨fun h => ⟨⟨⟨⟨h.parNodup, h.passOK⟩, h.acyclic, h.downPar⟩, h.trimBr⟩, h.defFirst, h.noLti, h.defOnce⟩,
    fun h => ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2.1, h.1.1.2.2, h.1.2, h.2.1, h.2.2.1, h.2.2.2⟩⟩

/-- `optimize_keeps_plain_pickR` on blocks with `OptIn`. -/
theorem optimize_keeps_optIn (M : Type → Type → Type) [Ana.Treap M] {fuel sfuel : Nat}
    {s s' : Straight Map} (hb : OptIn s.blocks)
    (h : optimizeF fuel ⟨aliasM (Ana.pickR M), trimTraceHints, switchChains sfuel⟩ s = some s') : Keeps s s' :=
  optimize_keeps_plain_pickR M (optIn_iff.mp hb) h

end

/-! ## The witnesses violate the invariant -/

theorem v_reach1 : Reach vBlocks 1 := Reach.jump (j := ⟨[], 1⟩) Reach.zero v_get0 (by simp [V0, getJmps])

/-- In `vBlocks` register `2` is written by the `%inc` of block `0` and by the
fill of block `1`. -/
theorem not_defOnceR_v : ¬ DefOnceR vBlocks := by
  intro H
  have := H 2 (0, some 0) (1, some 1) Reach.zero ⟨V0, Pole.inc 0 2, v_get0, rfl, rfl⟩ v_reach1
    ⟨V1, Pole.imm (A 0) 2, v_get1, rfl, rfl⟩
  simp at this

theorem not_fillFresh_v : ¬ FillFresh vBlocks := by
  intro H
  refine H 2 1 1 v_reach1 v_fill (0, some 0) ⟨Reach.zero, ⟨V0, Pole.inc 0 2, v_get0, rfl, rfl⟩, fun i _ hdf => ?_⟩
  obtain ⟨b, hb, ⟨u, hu⟩, -⟩ := hdf
  rw [v_get0] at hb; cases hb; cases hu

theorem w_reach4 : Reach wBlocks 4 :=
  Reach.jump (j := ⟨[], 4⟩)
    (Reach.jump (j := ⟨[none], 3⟩) (Reach.jump (j := ⟨[], 2⟩) Reach.zero w_get0 (by simp [W0, getJmps]))
      (b := W2) rfl (by simp [W2, getJmps]))
    w_get3 (by simp [W3, getJmps])

/-- In `wBlocks` register `2` is written by the `%inc` of block `0` and by the
fill of block `4`. -/
theorem not_defOnceR_w : ¬ DefOnceR wBlocks := by
  intro H
  have := H 2 (0, some 0) (4, some 1) Reach.zero ⟨W0, Pole.inc 0 2, w_get0, rfl, rfl⟩ w_reach4
    ⟨W4, Pole.imm (A 0) 2, w_get4, rfl, rfl⟩
  simp at this

theorem not_fillFresh_w : ¬ FillFresh wBlocks := by
  intro H
  refine H 2 4 1 w_reach4 w_fill (0, some 0) ⟨Reach.zero, ⟨W0, Pole.inc 0 2, w_get0, rfl, rfl⟩, fun i _ hdf => ?_⟩
  obtain ⟨b, hb, ⟨u, hu⟩, -⟩ := hdf
  rw [w_get0] at hb; cases hb; cases hu

/-- **The witness blocks violate `DInvR`.** -/
theorem not_dInvR_w : ¬ DInvR wBlocks := fun h => not_defOnceR_w h.2.2.2

theorem not_dInvR_v : ¬ DInvR vBlocks := fun h => not_defOnceR_v h.2.2.2

/-! ## The two passes that make dead fills, on examples -/

/-- `+remove-hops` merges the `[%bom ~]` block `1` into block `0`, whose
`[%imm 5 1]` is then a dead fill. -/
def xhBlocks : LM Blob :=
  ⟨[(0, ⟨[], [Pole.imm (A 5) 1], Termin.hop ⟨[], 1⟩⟩), (1, ⟨[], [], Termin.bom none⟩)]⟩

theorem ex_hops : (removeHops 10 xhBlocks (revCfg xhBlocks [0, 1]) [0, 1]).map
    (fun r => (HoonMap.get r.2 0, HoonMap.get r.2 1)) =
    some (some ⟨[], [Pole.imm (A 5) 1], Termin.bom none⟩, none) := by decide

/-- `+alias` turns the `%brn` on the known immediate `5` into `[%bom ~]` and
drops blocks `1` and `2`; `[%imm 7 2]` is then a dead fill. -/
def xaBlocks : LM Blob :=
  ⟨[(0, ⟨[], [Pole.imm (A 5) 1, Pole.imm (A 7) 2], Termin.brn 1 ⟨[], 1⟩ ⟨[], 2⟩⟩),
    (1, ⟨[], [], Termin.don 2⟩), (2, ⟨[], [], Termin.don 2⟩)]⟩

theorem ex_alias : (aliasM (fun l => l.headD 0) 1 xaBlocks (revCfg xaBlocks [0, 1, 2]) [0, 1, 2]).map
    (fun r => (HoonMap.get r.2 0, HoonMap.get r.2 1, HoonMap.get r.2 2)) =
    some (some ⟨[], [Pole.imm (A 5) 1, Pole.imm (A 7) 2], Termin.bom none⟩, none, none) := by decide

end Opt
end SkaModel
end Formalization
