import lemmas.Ska.OptDriver
import lemmas.Ska.OptArgs

/-!
# The fields of `DriverHyp` for the proved passes

The two invariants meant for `DriverHyp`: `BlkInv` (distinct parameters and
the check of `+eval-pass`, of the blocks alone) and `TopoInv` (`TopoOK`, and
`rev` lists every member of `topo` that jumps to a block, the `rev` field of
`HopsHyp`).  `+bb-topo` with `+rev-cfg` gives `TopoInv` from `TopoOK`
(`topoInv_revCfg`); that `+bb-topo` gives `TopoOK` is open.

Discharged here, for the fields of `DriverHyp` at these invariants: the
semantic half (`Keeps`, with `ReadsOK` and `ArgsOK`) and `BlkInv` for
`+remove-hops` (`hops_field`) and for `+remove-useless-branching`
(`rub_field`, with no hypothesis), and both for `+remove-empty-middle` under
its own hypothesis, `PassOK` of its result (`middle_field`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock

variable {Map : Type → Type} [HoonMap Map]

/-- The block invariant: distinct parameters, jumps that pass the check of
`+eval-pass`. -/
def BlkInv (bl : Map Blob) : Prop := ParNodup bl ∧ PassOK bl

/-- The invariant of `topo` and `rev`. -/
def TopoInv (bl : Map Blob) (topo : List Nat) (rev : Map (List Nat)) : Prop :=
  TopoOK bl topo ∧
    ∀ o b j, o ∈ topo → HoonMap.get bl o = some b → j ∈ getJmps b.fin → o ∈ getJa rev j.there

section
variable [MapKeys Map]

theorem topoInv_revCfg {bl : Map Blob} {topo : List Nat} (ht : TopoOK bl topo) :
    TopoInv bl topo (revCfg bl topo) :=
  ⟨ht, fun _ _ _ ho hb hj => revCfg_mem ho hb hj⟩

/-- The semantic half of the field `rub` holds. -/
theorem rub_keepsB {bl bl' : Map Blob} {ch : Bool} (h : removeUselessBranching bl = some (ch, bl')) :
    KeepsB bl bl' := by
  intro c hc; subst hc; exact rub_keeps c h

/-- **The field `hops` of `DriverHyp`, but for `TopoInv` after no change.** -/
theorem hops_field {fuel : Nat} {bl : Map Blob} {topo : List Nat} {rev : Map (List Nat)} {ch : Bool}
    {bl' : Map Blob} (hb : BlkInv bl) (hi : TopoInv bl topo rev) (h : removeHops fuel bl rev topo = some (ch, bl')) :
    KeepsB bl bl' ∧ BlkInv bl' := by
  refine ⟨fun c hc => ?_, hops_parNodup hi.1.1 hi.1.2.1 h hb.1, hops_passOK hi.1.1 hi.1.2.1 h hb.2⟩
  subst hc
  exact hops_keeps_of c ⟨hi.1.2.2.2.1, hi.2, hb.1, hb.2⟩ hi.1.1 hi.1.2.1 h

/-- **The field `rub` of `DriverHyp`, but for `TopoInv` after no change.** -/
theorem rub_field {bl : Map Blob} {ch : Bool} {bl' : Map Blob} (hb : BlkInv bl)
    (h : removeUselessBranching bl = some (ch, bl')) : KeepsB bl bl' ∧ BlkInv bl' :=
  ⟨rub_keepsB h, rub_parNodup h hb.1, rub_passOK h hb.2⟩

/-- **`BlkInv` after `+remove-empty-middle`**, under its hypothesis. -/
theorem middle_blkInv {fuel : Nat} {bl : Map Blob} {ch : Bool} {bl' : Map Blob} (hb : BlkInv bl)
    (h : removeEmptyMiddle fuel bl = some (ch, bl')) (hyp : PassOK bl') : BlkInv bl' :=
  ⟨mid_parNodup h hb.1, hyp⟩

/-- **The field `middle` of `DriverHyp`, but for `TopoInv` after no
change**, under the pass's own hypothesis (`PassOK` of its result); `PassOK`
of its input is that of `BlkInv`. -/
theorem middle_field {fuel : Nat} {bl : Map Blob} {ch : Bool} {bl' : Map Blob} (hb : BlkInv bl)
    (h : removeEmptyMiddle fuel bl = some (ch, bl')) (hyp : PassOK bl') : KeepsB bl bl' ∧ BlkInv bl' := by
  refine ⟨fun c hc => ?_, middle_blkInv hb h hyp⟩
  subst hc
  exact middle_keeps c h hb.2 hyp

end

end Opt
end SkaModel
end Formalization
