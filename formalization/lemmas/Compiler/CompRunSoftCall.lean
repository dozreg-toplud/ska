import lemmas.Compiler.CompRunSoftDefs
import lemmas.Compiler.CompRunTNCall

/-! # The soft direct call in the pill: the blocks (README Gaps 19 (g), track K)

The soft branch of a direct call at `mono` `|` under `%done` with no key (lines 4004 to 4047):
the push of `sof` gives `&` (`A 0`), step `7` emits `[~ ~ (jump-op ~)]` and then runs
`+soft-new` (the `=?  gen  sof (soft-new ..)` of `crD7Ur1`), so the entry of the call's block is
in `soft.gen` when step `9` asks `~(has by soft.gen) call-block` (yes, `crn_hasS`) and runs
`+soft-bond`.

* `sn_arm`, `sb_arm`: the arms of `+soft-new` / `+soft-bond` build their gates;
* **`crn_hasS`**: `+has:by` of `softMapNoun (put sm o c)` at `o` is yes;
* **`crd_blk_doneS`**: step `7` on `%done` with `sof` `&`: the `+emit` of `crd_blk_done`, then
  `+soft-new` (`comp_soft_new`) at the emitted block with `kin` `%tail` (`1`), no ring, the
  call's `sub-ned` and `b-sur`, `pro` and `out` `0`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun}

/-- The arm of `+soft-new` builds its gate (sample the bunt). -/
theorem sn_arm (d : Noun) : ∃ U, nock d snArm = some (C snBat (C U d)) := by
  unfold snArm; generalize snBat = B; simp [nock_exec]

/-- The arm of `+soft-bond` builds its gate (sample the bunt). -/
theorem sb_arm (d : Noun) : ∃ U, nock d sbArm = some (C sbBat (C U d)) := by
  unfold sbArm; generalize sbBat = B; simp [nock_exec]

/-- **`+has:by` on `soft` at the key just put**: yes (`A 0`). -/
theorem crn_hasS (sm : TreapMap mugF SoftCall) (o : Nat) (c : SoftCall) :
    nock (C by.has.battery (C (A o) (C by.battery (C (softMapNoun (HoonMap.put sm o c)) layer2)))) by.has.battery
      = some (A 0) := by
  have hg := getF_hoonMap SoftCall.toNoun (HoonMap.put sm o c) o
  rw [HoonMap.get_put] at hg
  simp only [if_true] at hg
  rw [softMapNoun, has_gate layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ (A o) _ _ hg]
  simp [unitNoun, loob]

/-- The entry `+soft-new` puts for a soft tail call at the block `o`. -/
abbrev softTailEntry (o : Nat) (b : Bell) (subNed : Need) (sur : NeedOrd) : SoftCall :=
  ⟨1, b, Option.none, subNed, sur, o, o, o, 0, 0, []⟩

/-- **Step `7` on `%done` with `sof` `&`**: one `+emit` of `[~ ~ (jump-op ~)]`, then `+soft-new`
at the emitted block `o = g.bo` (the model's `emit` then `softNew o 1 b ~ sub-ned b-sur 0 0`). -/
theorem crd_blk_doneS (hc : CompIn ctx) (gs : GenSf (TreapMap mugF)) (x : GenRest)
    (hx : x.soft = softMapNoun gs.soft) (sur : NeedOrd) (V2 PV : Noun) (subNed : Need) (p q : Nomm) (b : Bell)
    (region : List Nat) (sup : Noun) :
    nock (crdS6m (A 0) sur.toNoun (listNoun A (flattenNeed subNed)) subNed.toNoun V2 PV
      (crSubj (A 1) (crdN p q b) (CGoalL.done : CGoalL CSet).toNoun (listNoun A region) sup (compCore gs.g x ctx)))
      crDKc7
      = some (C (A gs.g.bo) (genNoun (cfEmitG ⟨[], [], Termin.jmp b (flattenNeed subNed)⟩ gs.g)
          { x with soft := softMapNoun (HoonMap.put gs.soft gs.g.bo (softTailEntry gs.g.bo b subNed sur)) })) := by
  have he := cf_emit (x := x) hc gs.g ⟨[], [], Termin.jmp b (flattenNeed subNed)⟩
  simp only [Blob.toNoun, listNoun, Termin.toNoun, Tag.jmp] at he
  have hD := comp_emit_at
  have hsn := comp_soft_new hc ⟨cfEmitG ⟨[], [], Termin.jmp b (flattenNeed subNed)⟩ gs.g, gs.soft⟩ x hx gs.g.bo 1 b
    Option.none subNed sur 0 0 (A 0x6c696174) b.toNoun (A 0) subNed.toNoun sur.toNoun rfl
  simp only [softNew, Option.map_some] at hsn
  have hD2 := comp_sn_at
  have hU := sn_arm
  simp only [crSubj, compCore, snSample] at he hsn ⊢
  generalize comp.door = Dr at he hD hsn hD2 ⊢
  generalize snArm = SA at hD2 hU
  obtain ⟨U, hU⟩ := hU (C Dr (C (genNoun (cfEmitG ⟨[], [], Termin.jmp b (flattenNeed subNed)⟩ gs.g) x) ctx))
  unfold crDKc7 crD7 crD7Op crD7Jop crD7T crD7D crD7Ur0 crD7Uc0 crD7Ur1
  simp [nock_exec, CGoalL.toNoun, hD, comp_emit_arm, he, hD2, hU, hsn]

end Compiler
end Formalization
