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

/-- The model's state after step `7` of a soft tail call. -/
abbrev softGs1 (gs : GenSf (TreapMap mugF)) (b : Bell) (subNed : Need) (sur : NeedOrd) : GenSf (TreapMap mugF) :=
  ⟨cfEmitG ⟨[], [], Termin.jmp b (flattenNeed subNed)⟩ gs.g,
    HoonMap.put gs.soft gs.g.bo (softTailEntry gs.g.bo b subNed sur)⟩

/-- **Steps `7` to `14` of a soft tail call at `mono` `|`** (`crd_from7NT` with `sof` `&`): the
block and `+soft-new` (`crd_blk_doneS`), `call-blocks` an atom, `~(has by soft.gen) call-block`
yes (`crn_hasS`), `+soft-bond` (`comp_soft_bond`), then the tail (`crd_ctailRT`) from the rest
whose `soft` is the noun of the map `+soft-bond` leaves. -/
theorem crd_from7NTS (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)) (cd : Bell → Option Bool) (p q : Nomm)
    (hpn : PastAt ctx cd p) (region : List Nat) (gs : GenSf (TreapMap mugF)) (x : GenRest)
    (hx : x.soft = softMapNoun gs.soft) (sur : NeedOrd) (V2 PV sup : Noun) (subNed : Need) (b : Bell)
    {Y : GenRest → GenRest → Prop} (hr : ∀ x, Y x x) (ht : ∀ {x y z : GenRest}, Y x y → Y y z → Y x z)
    (hq : ∀ nexB gs2, softBond (crdArg subNed gs.g.bo) region (softGs1 gs b subNed sur) = some (nexB, gs2) →
      RunAtRT R ctx Y { x with soft := softMapNoun gs2.soft } (A 1) sup q
        (CGoalL.next (Lazy.ofSure Sure.bunt) nexB.th) region gs2.g)
    (hp : ∀ nexB gs2, softBond (crdArg subNed gs.g.bo) region (softGs1 gs b subNed sur) = some (nexB, gs2) →
      ∀ x1, Y { x with soft := softMapNoun gs2.soft } x1 → ∀ nexF g2 nexF' g3,
      crdFqR R q nexB.th region gs2.g = some (nexF, g2) → pastL cd nexF p region g2 = some (nexF', g3) →
      RunAtRT R ctx Y x1 (A 1) sup p (CGoalL.next nexB.laz nexF'.th) region g3)
    (hcp : ∀ nexB gs2, softBond (crdArg subNed gs.g.bo) region (softGs1 gs b subNed sur) = some (nexB, gs2) →
      ∀ nexF g2 nexF' g3 nexS g4, crdFqR R q nexB.th region gs2.g = some (nexF, g2) →
      pastL cd nexF p region g2 = some (nexF', g3) →
      R p (CGoalL.next nexB.laz nexF'.th) region g3 = some (nexS, g4) → CopyH g4.re nexS.laz nexF'.laz) :
    ∃ x', (∀ nexB gs2, softBond (crdArg subNed gs.g.bo) region (softGs1 gs b subNed sur) = some (nexB, gs2) →
        Y { x with soft := softMapNoun gs2.soft } x') ∧
      nock (crdS6m (A 0) sur.toNoun (listNoun A (flattenNeed subNed)) subNed.toNoun V2 PV
        (crSubj (A 1) (crdN p q b) (CGoalL.done : CGoalL CSet).toNoun (listNoun A region) sup (compCore gs.g x ctx)))
        crDKr7
      = (softBond (crdArg subNed gs.g.bo) region (softGs1 gs b subNed sur)).bind fun r =>
          (crdTailMR R cd p q r.1 region r.2.g).map fun t => C t.1.goal.toNoun (genNoun t.2 x') := by
  have h15 := cr_ctx15 h7
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  have hblk := crd_blk_doneS hc gs x hx sur V2 PV subNed p q b region sup
  have hs := crn_hasS gs.soft gs.g.bo (softTailEntry gs.g.bo b subNed sur)
  have hsb := comp_soft_bond hc (softGs1 gs b subNed sur)
    { x with soft := softMapNoun (softGs1 gs b subNed sur).soft } rfl (crdArg subNed gs.g.bo) region
  have hD2 := comp_sb_at
  have hU := sb_arm
  rw [crd_arg_noun] at hsb
  cases eb : softBond (crdArg subNed gs.g.bo) region (softGs1 gs b subNed sur) with
  | none =>
    rw [eb] at hsb
    refine ⟨x, (fun _ _ h => by cases h), ?_⟩
    simp only [crSubj, compCore, crdS6m] at hblk hsb ⊢
    generalize comp.door = Dr at hblk hsb hD2 ⊢
    generalize sbArm = SA at hD2 hU
    obtain ⟨U, hU⟩ := hU (C Dr (C (genNoun (softGs1 gs b subNed sur).g
      { x with soft := softMapNoun (softGs1 gs b subNed sur).soft }) ctx))
    unfold crDKr7 crDKr8 crDKc8 crDKr9 crDKc9
    simp [nock_exec, hblk, h15, hc, ct_lfn_at, ct_lfn_arm, ct_lfn_gate, by_arm, by.arm_at, by.has.arm_at, has_arm,
      hs, hD2, hU, hsb]
  | some r =>
    obtain ⟨nexB, gs2⟩ := r
    rw [eb] at hsb
    simp only [Option.map_some] at hsb
    obtain ⟨x', hy, ht'⟩ := crd_ctailRT h7 hcode R cd p q hpn region { x with soft := softMapNoun gs2.soft } (A 1)
      (C (A 0) (C b.toNoun (A 0))) sup (CGoalL.done : CGoalL CSet).toNoun nexB (C subNed.toNoun (A gs.g.bo))
      (A gs.g.bo) (A 0) sur.toNoun (listNoun A (flattenNeed subNed)) subNed.toNoun V2 (A 0) PV gs2.g hr ht
      (hq nexB gs2 eb) (hp nexB gs2 eb) (hcp nexB gs2 eb)
    refine ⟨x', (fun n' g' h => by cases h; exact hy), ?_⟩
    simp only [Option.bind_some]
    simp only [crSubj, compCore, crdS9, crdS6m] at hblk hsb ht' ⊢
    generalize comp.door = Dr at hblk hsb hD2 ht' ⊢
    generalize sbArm = SA at hD2 hU
    obtain ⟨U, hU⟩ := hU (C Dr (C (genNoun (softGs1 gs b subNed sur).g
      { x with soft := softMapNoun (softGs1 gs b subNed sur).soft }) ctx))
    unfold crDKr7 crDKr8 crDKc8 crDKr9 crDKc9
    simp [nock_exec, hblk, h15, hc, ct_lfn_at, ct_lfn_arm, ct_lfn_gate, by_arm, by.arm_at, by.has.arm_at, has_arm,
      hs, hD2, hU, hsb, ht']

end Compiler
end Formalization
