import lemmas.Ska.OptAliasStatic

/-!
# `PassOK` and `DownPar` of the blocks `+alias` returns

The end after of a walked block `o` reads only registers of `DefW` at the
point right after `o` (`SInv.ends` through `sst_at`): the end before reads
registers defined before it, and `old` maps them into `DefW`.  A parameter of
a block reachable from a target of `o` is defined only there (`DefOnceB`),
after `o` in `topo`, so it is outside `DefW` (`awi_par_notDefW`).  Hence no
argument of a jump after is a parameter of a block below its target:
**`alias_downPar`**, and its case of the target itself **`alias_passOK`**.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map]

set_option linter.unusedSectionVars false

/-- Reachability from a label along forward jumps stays forward in `topo`. -/
theorem rfrom_idx [MapKeys Map] {bl : Map Blob} {T : List Nat} (ht : TopoOK bl T) {x z : Nat} (h : RFrom bl x z) :
    x ∈ T → z ∈ T ∧ T.idxOf x ≤ T.idxOf z := by
  induction h with
  | refl => exact fun hx => ⟨hx, Nat.le_refl _⟩
  | step hb hj _ ih =>
    intro hx
    obtain ⟨hjT, hlt⟩ := awi_fwd ht hx hb hj
    obtain ⟨hz, hle⟩ := ih hjT
    exact ⟨hz, by omega⟩

theorem rfrom_reach {bl : Map Blob} {x z : Nat} (h : RFrom bl x z) : Reach bl x → Reach bl z := by
  induction h with
  | refl => exact id
  | step hb hj _ ih => exact fun hx => ih (Reach.jump hx hb hj)

/-- A path of a map whose jumps go to targets of `bl` is a path of `bl`. -/
theorem rfrom_sub {bl bl' : Map Blob} (hs : TargetsSub bl bl') {x z : Nat} (h : RFrom bl' x z) : RFrom bl x z := by
  induction h with
  | refl => exact RFrom.refl _
  | step hb hj _ ih =>
    obtain ⟨b, hb0, hjs⟩ := hs _ _ hb
    obtain ⟨j0, hj0, he⟩ := hjs _ hj
    exact RFrom.step hb0 hj0 (he ▸ ih)

section
variable [MapKeys Map] {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} {topo : List Nat}
  {rev : Map (List Nat)} {g : AGen Map}

/-- **The end after of a walked jumping block reads only `DefW` registers** at
the point right after the block. -/
theorem alias_fin_defW (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (hD : DInvS bl) (hT : TopoInvR bl topo rev)
    (h : aliasWalk pick nargs bl topo (aliasInit rev) = some g) {o : Nat} {b' : Blob} {j' : Jmp}
    (hb' : HoonMap.get g.new o = some b') (hj' : j' ∈ getJmps b'.fin) :
    ∃ pre l b j, topo = pre ++ o :: l ∧ HoonMap.get bl o = some b ∧ j ∈ getJmps b.fin ∧ j.there = j'.there ∧
      ∀ x ∈ finRegs b'.fin, DefW bl (pre ++ [o]) x := by
  have ht := hT.1.1
  obtain ⟨pre, l, g1, g2, b, st0, rb, rf, hto, h1, h2, h3, _e5, hb, _e7, _e8, hrf, _e10, hbe⟩ := aw_new ht hT.2 h hb'
  obtain ⟨⟨j, hj, hjt⟩, -⟩ := afin_jmps hrf (hbe ▸ hj')
  have hI := sst_at hpick hD hT hto h1 h2
  have hnd := ht.1
  rw [hto] at hnd
  have hol : o ∉ l := fun h' => ((List.nodup_append.mp hnd).2.1 |> List.nodup_cons.mp).1 h'
  have hg2 : HoonMap.get g2.new o = some b' := by rw [← ((awk_walk l g2 g h3).2 o hol).2.2]; exact hb'
  obtain ⟨-, -, -, -, hfr, -, -⟩ := hI.ends o b j b' (List.mem_append_right _ (List.mem_singleton.mpr rfl)) hb hj hg2
  exact ⟨pre, l, b, j, hto, hb, hj, hjt, hfr⟩

/-- **`DownPar` of the result**: no argument of a jump after is a parameter of
a block reachable from its target. -/
theorem alias_downPar (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (hD : DInvS bl) (hT : TopoInvR bl topo rev)
    (h : aliasWalk pick nargs bl topo (aliasInit rev) = some g) : DownPar g.new := by
  have ht := hT.1.1
  intro y b' j' hb' hj' r hr z bz' hz hbz'
  obtain ⟨pre, l, b, j, hto, hb, hj, hjt, hfr⟩ := alias_fin_defW hpick hD hT h hb' hj'
  have hdef : DefW bl (pre ++ [y]) r := hfr r (jmp_finRegs hj' hr)
  have hzb : RFrom bl j.there z := hjt ▸ rfrom_sub (alias_targetsSub hT h) hz
  have hyT : y ∈ topo := by rw [hto]; simp
  obtain ⟨hjT, hlt⟩ := awi_fwd ht hyT hb hj
  obtain ⟨hzT, hle⟩ := rfrom_idx ht hzb hjT
  have hRz : Reach bl z := aliasWalk_reach ht hT.2 h z (by rw [hbz']; rfl)
  obtain ⟨_pre, _l, _g1, _g2, bz, _st0, _rb, _rf, _e1, _e2, _e3, _e4, _e5, hbz, _e7, _e8, _e9, _e10, hbze⟩ :=
    aw_new ht hT.2 h hbz'
  intro hrp
  rw [hbze] at hrp
  have hzpre : z ∉ pre ++ [y] := by
    rw [hto] at hlt hle
    exact sst_not_pre (hto ▸ ht.1) (by omega)
  exact awi_par_notDefW hD.2.1.1 hRz hbz hrp hzpre hdef

/-- **`PassOK` of the result**: no argument of a jump after is a parameter of
its target. -/
theorem alias_passOK (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (hD : DInvS bl) (hT : TopoInvR bl topo rev)
    (h : aliasWalk pick nargs bl topo (aliasInit rev) = some g) : PassOK g.new :=
  downPar_passOK (alias_downPar hpick hD hT h)

end

end Opt
end SkaModel
end Formalization
