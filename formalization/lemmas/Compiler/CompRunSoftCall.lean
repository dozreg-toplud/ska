import lemmas.Compiler.CompRunSoftDefs
import lemmas.Compiler.CompRunTNCall
import lemmas.Compiler.CompRunTCallQ

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
    (hq : safeFolFol q = false → ∀ nexB gs2,
      softBond (crdArg subNed gs.g.bo) region (softGs1 gs b subNed sur) = some (nexB, gs2) →
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
    obtain ⟨x', hy, ht'⟩ := crd_ctailRTQ h7 hcode R cd p q hpn region { x with soft := softMapNoun gs2.soft } (A 1)
      (C (A 0) (C b.toNoun (A 0))) sup (CGoalL.done : CGoalL CSet).toNoun nexB (C subNed.toNoun (A gs.g.bo))
      (A gs.g.bo) (A 0) sur.toNoun (listNoun A (flattenNeed subNed)) subNed.toNoun V2 (A 0) PV gs2.g hr ht
      (fun hs => hq hs nexB gs2 eb) (hp nexB gs2 eb) (hcp nexB gs2 eb)
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

/-- **A soft tail call at `mono` `|`, steps `0` to `14`** (`crd_head6M` with the push of `sof`
giving `&`, then `crd_from7NTS`). -/
theorem crd_callNTS (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)) (cd : Bell → Option Bool)
    (msup : Option Nomm) (p q : Nomm) (hpn : PastAt ctx cd p) (b : Bell) (nb sur : NeedOrd)
    (gs : GenSf (TreapMap mugF)) (x : GenRest) (hx : x.soft = softMapNoun gs.soft)
    (hn : CallNounM msup ctx p q b nb sur.toNoun x (A 1) (A 0)) (PV : Noun) (region : List Nat)
    {Y : GenRest → GenRest → Prop} (hr : ∀ x, Y x x) (ht : ∀ {x y z : GenRest}, Y x y → Y y z → Y x z)
    (hq : safeFolFol q = false → ∀ subNed g1 nexB gs2, needOrdAllocRegs nb gs.g = some (subNed, g1) →
      softBond (crdArg subNed g1.bo) region (softGs1 ⟨g1, gs.soft⟩ b subNed sur) = some (nexB, gs2) →
      RunAtRT R ctx Y { x with soft := softMapNoun gs2.soft } (A 1) (unitNoun Nomm.toNoun msup) q
        (CGoalL.next (Lazy.ofSure Sure.bunt) nexB.th) region gs2.g)
    (hp : ∀ subNed g1 nexB gs2, needOrdAllocRegs nb gs.g = some (subNed, g1) →
      softBond (crdArg subNed g1.bo) region (softGs1 ⟨g1, gs.soft⟩ b subNed sur) = some (nexB, gs2) →
      ∀ x1, Y { x with soft := softMapNoun gs2.soft } x1 → ∀ nexF g2 nexF' g3,
      crdFqR R q nexB.th region gs2.g = some (nexF, g2) → pastL cd nexF p region g2 = some (nexF', g3) →
      RunAtRT R ctx Y x1 (A 1) (unitNoun Nomm.toNoun msup) p (CGoalL.next nexB.laz nexF'.th) region g3)
    (hcp : ∀ subNed g1 nexB gs2, needOrdAllocRegs nb gs.g = some (subNed, g1) →
      softBond (crdArg subNed g1.bo) region (softGs1 ⟨g1, gs.soft⟩ b subNed sur) = some (nexB, gs2) →
      ∀ nexF g2 nexF' g3 nexS g4, crdFqR R q nexB.th region gs2.g = some (nexF, g2) →
      pastL cd nexF p region g2 = some (nexF', g3) →
      R p (CGoalL.next nexB.laz nexF'.th) region g3 = some (nexS, g4) → CopyH g4.re nexS.laz nexF'.laz) :
    ∃ x', (∀ subNed g1 nexB gs2, needOrdAllocRegs nb gs.g = some (subNed, g1) →
        softBond (crdArg subNed g1.bo) region (softGs1 ⟨g1, gs.soft⟩ b subNed sur) = some (nexB, gs2) →
        Y { x with soft := softMapNoun gs2.soft } x') ∧
      nock (C PV (crSubj (A 1) (crdN p q b) (CGoalL.done : CGoalL CSet).toNoun (listNoun A region)
        (unitNoun Nomm.toNoun msup) (compCore gs.g x ctx))) crDCall
      = (needOrdAllocRegs nb gs.g).bind fun r =>
          (softBond (crdArg r.1 r.2.bo) region (softGs1 ⟨r.2, gs.soft⟩ b r.1 sur)).bind fun s =>
            (crdTailMR R cd p q s.1 region s.2.g).map fun t => C t.1.goal.toNoun (genNoun t.2 x') := by
  rw [crd_head6M h7 msup p q b nb sur.toNoun x (A 1) (A 0) hn PV (CGoalL.done : CGoalL CSet).toNoun region gs.g]
  cases e : needOrdAllocRegs nb gs.g with
  | none => exact ⟨x, (fun _ _ _ _ h => by cases h), rfl⟩
  | some r =>
    obtain ⟨subNed, g1⟩ := r
    obtain ⟨x', hy, hc⟩ := crd_from7NTS h7 hcode R cd p q hpn region ⟨g1, gs.soft⟩ x hx sur nb.toNoun PV
      (unitNoun Nomm.toNoun msup) subNed b hr ht (fun hs nB g2 h => hq hs subNed g1 nB g2 e h) (hp subNed g1 · · e) (hcp subNed g1 · · e)
    refine ⟨x', (fun s' g' nB g2 h h2 => by cases h; exact hy nB g2 h2), ?_⟩
    simpa only [Option.bind_some] using hc

/-- **The model on a soft tail call whose formula is skipped** (`safe-fol-fol`) and whose subject
runs as a lifted `R` (no read of `soft.gen`): `needOrdAllocRegs`, `+soft-new` and `+soft-bond`
(`softGs1`, `crdArg`), then `crdTailMR R` with the soft map kept. -/
theorem callLS_soft_tailK (env : CallEnv) (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet))
    (rq : CGoalL CSet → List Nat → CMS (TreapMap mugF) (NextL CSet)) (p q : Nomm) (b : Bell) (sup : Option Nomm)
    (region : List Nat) (bNed : NeedOrd) (hri : env.ring b = Option.none) (hnb : env.need b = some bNed)
    (hsof : env.sof (made p sup) p q b bNed = true) (hsq : safeFolFol q = true) (s : GenSf (TreapMap mugF)) :
    callLS env (fun g r => liftS (R p g r)) rq p q (some (b, Option.none)) sup CGoalL.done region s =
      (needOrdAllocRegs bNed s.g).bind fun r =>
        (softBond (crdArg r.1 r.2.bo) region (softGs1 ⟨r.2, s.soft⟩ b r.1 (env.sure b))).bind fun t =>
          (crdTailMR R env.cod p q t.1 region t.2.g).map fun u => (u.1, (⟨u.2, t.2.soft⟩ : GenSf (TreapMap mugF))) := by
  rw [callLS_soft_tail (S := CSet) (Map := TreapMap mugF) env _ rq p q b sup region bNed hri hnb hsof s]
  cases h1 : needOrdAllocRegs bNed s.g with
  | none => simp [bind, StateT.bind, liftS, h1]
  | some r =>
    obtain ⟨subNed, g1⟩ := r
    have he := cf_emit_g ⟨[], [], Termin.jmp b (flattenNeed subNed)⟩ g1
    simp only [Option.bind_some]
    cases h2 : softBond (crdArg subNed g1.bo) region (softGs1 ⟨g1, s.soft⟩ b subNed (env.sure b)) with
    | none =>
      simp only [crdArg, softGs1] at h2
      simp [bind, StateT.bind, liftS, h1, he, softNew, h2]
    | some r2 =>
      obtain ⟨nexB, gs2⟩ := r2
      simp only [crdArg, softGs1] at h2
      simp only [Option.bind_some]
      unfold crdTailMR crdFqR
      simp only [hsq, if_true]
      cases h3 : pastL env.cod (⟨Lazy.ofSure Sure.bunt, nexB.th⟩ : NextL CSet) p region gs2.g with
      | none => simp [bind, StateT.bind, liftS, h1, he, softNew, h2, hsq, pure, StateT.pure, h3]
      | some r3 =>
        obtain ⟨nexF, g3⟩ := r3
        cases h4 : R p (CGoalL.next nexB.laz nexF.th) region g3 with
        | none => simp [bind, StateT.bind, liftS, h1, he, softNew, h2, hsq, pure, StateT.pure, h3, h4]
        | some r4 =>
          obtain ⟨nexS, g4⟩ := r4
          cases h5 : copyL nexS nexF.laz g4 with
          | none => simp [bind, StateT.bind, liftS, h1, he, softNew, h2, hsq, pure, StateT.pure, h3, h4, h5]
          | some r5 => simp [bind, StateT.bind, liftS, h1, he, softNew, h2, hsq, pure, StateT.pure, h3, h4, h5]

/-- **The case `%2` on a soft tail call at `mono` `|`** (README Gaps 19 (g), the corpus shape:
`safe-fol-fol` holds of the formula `q`, the run of the subject `p` is a lifted `R` that does not
read `soft.gen`): from a rest whose `soft` is the noun of the model's map, the pill's `$` of
`+run` is `runLCS env snd msup` on `[2 p q [~ b ~]]` under `%done` (`callLS_soft_tailK`), the
run of `p` threading the rest at `Y` with `soft` kept (the run of `q` is skipped), the rest returned related
to `x` by `Y` (blind to `soft`). -/
theorem comp_run_n2_softNT (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (msup : Option Nomm) (p q : Nomm)
    (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet))
    (hrp : ∀ goal region, runLCS (S := CSet) (Map := TreapMap mugF) env snd msup p goal region
      = liftS (R p goal region))
    (hsq : safeFolFol q = true) (hpn : PastAt ctx env.cod p) (b : Bell) (hcd : CodePure cod env b) (nb : NeedOrd)
    (region : List Nat) (gs : GenSf (TreapMap mugF))
    (hri : env.ring b = Option.none) (hnb : env.need b = some nb) (hsof : env.sof (made p msup) p q b nb = true)
    {Y : GenRest → GenRest → Prop} (hr : ∀ x, Y x x) (ht : ∀ {x y z : GenRest}, Y x y → Y y z → Y x z)
    (hsY : ∀ {x y : GenRest} (s : Noun), Y x y → Y x { y with soft := s })
    (x : GenRest) (hx : x.soft = softMapNoun gs.soft)
    (hn : CallNounM msup ctx p q b nb (env.sure b).toNoun x (A 1) (A 0))
    (hp : ∀ subNed g1 nexB gs2, needOrdAllocRegs nb gs.g = some (subNed, g1) →
      softBond (crdArg subNed g1.bo) region (softGs1 ⟨g1, gs.soft⟩ b subNed (env.sure b)) = some (nexB, gs2) →
      ∀ x1, (Y { x with soft := softMapNoun gs2.soft } x1 ∧ x1.soft = softMapNoun gs2.soft) →
      ∀ nexF g2 nexF' g3, crdFqR R q nexB.th region gs2.g = some (nexF, g2) →
      pastL env.cod nexF p region g2 = some (nexF', g3) →
      RunAtRT R ctx (fun a c => Y a c ∧ c.soft = a.soft) x1 (A 1) (unitNoun Nomm.toNoun msup) p
        (CGoalL.next nexB.laz nexF'.th) region g3)
    (hcp : ∀ subNed g1 nexB gs2, needOrdAllocRegs nb gs.g = some (subNed, g1) →
      softBond (crdArg subNed g1.bo) region (softGs1 ⟨g1, gs.soft⟩ b subNed (env.sure b)) = some (nexB, gs2) →
      ∀ nexF g2 nexF' g3 nexS g4, crdFqR R q nexB.th region gs2.g = some (nexF, g2) →
      pastL env.cod nexF p region g2 = some (nexF', g3) →
      R p (CGoalL.next nexB.laz nexF'.th) region g3 = some (nexS, g4) → CopyH g4.re nexS.laz nexF'.laz) :
    ∃ x', Y x x' ∧
      nock (crSubj (A 1) (Nomm.n2 p q (some (b, Option.none))).toNoun (CGoalL.done : CGoalL CSet).toNoun
        (listNoun A region) (unitNoun Nomm.toNoun msup) (compCore gs.g x ctx)) crDol
      = (runLCS (S := CSet) env snd msup (Nomm.n2 p q (some (b, Option.none))) CGoalL.done region gs).map
          fun r => C r.1.goal.toNoun (genNoun r.2.g { x' with soft := softMapNoun r.2.soft }) := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  obtain ⟨V, hgot, hv⟩ := hcd
  obtain ⟨x', hy, hcall⟩ := crd_callNTS (Y := fun a c => Y a c ∧ c.soft = a.soft) h7 hcode R env.cod msup p q hpn b
    nb (env.sure b) gs x hx hn (loob (env.pure b)) region (fun a => ⟨hr a, rfl⟩)
    (fun h1 h2 => ⟨ht h1.1 h2.1, h2.2.trans h1.2⟩) (fun h => absurd (hsq.symm.trans h) (by decide))
    (fun s g n g2 h h2 x1 hx1 => hp s g n g2 h h2 x1 hx1) hcp
  have hmod : runLCS (S := CSet) (Map := TreapMap mugF) env snd msup (Nomm.n2 p q (some (b, Option.none)))
      CGoalL.done region gs = callLS env (fun g r => liftS (R p g r)) (runLCS env snd msup q) p q
        (some (b, Option.none)) msup (CGoalL.done : CGoalL CSet) region gs := by
    simp only [runLCS]
    have : runLCS (S := CSet) (Map := TreapMap mugF) env snd msup p = fun g r => liftS (R p g r) := by
      funext g r; exact hrp g r
    rw [this]
  rw [hmod, callLS_soft_tailK env R _ p q b msup region nb hri hnb hsof hsq gs]
  have hpure := crd_pure hc hcode p.toNoun q.toNoun b.toNoun (unitNoun id Option.none) V _ (A 1)
    (CGoalL.done : CGoalL CSet).toNoun (listNoun A region) (unitNoun Nomm.toNoun msup) gs.g x hgot hv
  have ht0 := crd_test_all h7 (C (A 2) (C p.toNoun (C q.toNoun (C (A 0) (C b.toNoun (unitNoun id Option.none))))))
    (A 1) (listNoun A region) (unitNoun Nomm.toNoun msup) (env.pure b) CGoalL.done gs.g x
  have hu : unitNoun (id : Noun → Noun) Option.none = A 0 := rfl
  have hl : loob false = A 1 := rfl
  simp only [crdDrop] at ht0
  rw [hu] at hpure ht0
  rw [hl] at ht0
  simp only [crdN] at hcall
  have hstep : nock (crSubj (A 1) (Nomm.n2 p q (some (b, Option.none))).toNoun (CGoalL.done : CGoalL CSet).toNoun
      (listNoun A region) (unitNoun Nomm.toNoun msup) (compCore gs.g x ctx)) crDol
      = nock (C (loob (env.pure b)) (crSubj (A 1) (C (A 2) (C p.toNoun (C q.toNoun (C (A 0) (C b.toNoun (A 0))))))
        (CGoalL.done : CGoalL CSet).toNoun (listNoun A region) (unitNoun Nomm.toNoun msup) (compCore gs.g x ctx)))
        crDCall := by
    rw [crd_noun, cr_disp_n2, cr2_dir, crd_eq, hu]
    unfold crDHead
    simp [nock_exec, hpure, ht0]
  rw [hstep, hcall]
  cases e1 : needOrdAllocRegs nb gs.g with
  | none => exact ⟨x, hr x, rfl⟩
  | some r =>
    obtain ⟨subNed, g1⟩ := r
    cases e2 : softBond (crdArg subNed g1.bo) region (softGs1 ⟨g1, gs.soft⟩ b subNed (env.sure b)) with
    | none => exact ⟨x, hr x, by simp [e2]⟩
    | some r2 =>
      obtain ⟨nexB, gs2⟩ := r2
      obtain ⟨hy1, hs1⟩ := hy subNed g1 nexB gs2 e1 e2
      refine ⟨x', ht (hsY _ (hr x)) hy1, ?_⟩
      have hx' : { x' with soft := softMapNoun gs2.soft } = x' := by
        obtain ⟨c', s', f'⟩ := x'
        simp only at hs1 ⊢
        rw [hs1]
      simp only [Option.bind_some, e2, Option.map_map, Function.comp_def, hx']

/-- **The case `%0` on a `%next` goal at any `soft`**: `comp_run_n0_next` (copied from
`CompRunLeafL.lean` with the `NoSoft` binder dropped: the proof never reads `soft`). -/
theorem comp_run_n0_nextS (h7 : slot? 7 ctx = some compK) (ax : Nat) (laz : Lazy CSet) (th : Jmp)
    (region : List Nat) (g : Gen (TreapMap mugF)) (hlok : WalkP lok0 0 laz) (x : GenRest) (mono sup : Noun) :
    nock (crSubj mono (Nomm.n0 ax).toNoun (CGoalL.next laz th).toNoun (listNoun A region) sup (compCore g x ctx)) crDol
      = (runL (Nomm.n0 ax) (CGoalL.next laz th) region g).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  simp only [Nomm.toNoun]
  rw [cr_disp_n0]
  by_cases h0 : ax = 0
  · subst h0
    have hD := comp_bomb_at
    simp only [compCore]
    have hb := comp_bomb (S := CSet) x hc g (some th.there)
    simp [compCore, bomb, cd_emit_eq, bind, StateT.bind, pure, StateT.pure, unitNoun, Next.goal,
      CGoal.toNoun, Jmp.toNoun, jmp0, lazyNoun, Sure.toNoun, Sure.bunt, Need.toNoun, HoonSet.toNoun_empty,
      listNoun] at hb
    generalize comp.door = Dr at hb hD ⊢
    nock_open crK0
    simp [nock_exec, crSubj, hD, comp_bomb_arm, CGoalL.toNoun, Jmp.toNoun, unitNoun, hb,
      runL, bombL, cd_emit_eq, NextL.goal, Next.goal, CGoal.toNoun, Lazy.toNoun_ofSure, Functor.map,
      StateT.map, jmp0, lazyNoun, Sure.toNoun, Sure.bunt, Need.toNoun, HoonSet.toNoun_empty, listNoun]
  · have h0' : ¬ (0 = ax) := fun h => h0 h.symm
    have hD2 := comp_from_at
    have hsn := comp_simple_next hc x g (CGoalL.next laz th) mono (C (A 0) (A ax)) (listNoun A region) sup
    have e : simpleNextL (CGoalL.next laz th) g = some (⟨laz, th⟩, g) := rfl
    rw [e] at hsn
    simp only [crSubj, compCore, Option.map_some] at hsn
    have hng : (NextL.goal ⟨laz, th⟩ : CGoalL CSet).toNoun = C (A 0x7478656e) (C laz.toNoun th.toNoun) := rfl
    rw [hng] at hsn
    have hf := cfr_all hc (genNoun g x) ax laz 0 hlok
    simp only [compCore]
    generalize comp.door = Dr at hsn hD2 hf ⊢
    nock_open crK0
    by_cases h1 : ax = 1
    · subst h1
      simp [nock_exec, crSubj, hsn, cr_bat_sn, runL, e, hng, pure, StateT.pure, bind, StateT.bind]
    · have h1' : ¬ (1 = ax) := fun h => h1 h.symm
      cases ef : Lazy.fromL ax laz with
      | none =>
        rw [ef] at hf
        simp [nock_exec, crSubj, h0, h0', h1, h1', hsn, cr_bat_sn, runL, e, hng, pure, StateT.pure, bind,
          StateT.bind, hD2, comp_from_arm, hf, ef, simpleNextL]
      | some laz' =>
        rw [ef] at hf
        simp [nock_exec, crSubj, h0, h0', h1, h1', hsn, cr_bat_sn, runL, e, hng, pure, StateT.pure, bind,
          StateT.bind, hD2, comp_from_arm, hf, ef, simpleNextL]
        simp [NextL.goal, CGoalL.toNoun]

theorem runLC_n0 (env : CallEnv) (sup : Option Nomm) (ax : Nat) (goal : CGoalL CSet) (region : List Nat) :
    (runLC env sup (Nomm.n0 ax) goal region : CM (TreapMap mugF) (NextL CSet)) = runL (Nomm.n0 ax) goal region := rfl

/-- **The soft tail call of the corpus** (`[2 [0 1] [1 f] [~ b ~]]` under `%done`, `sof` `&`):
`comp_run_n2_softNT` with `R := runLC env msup`, the run of `[0 1]` by `comp_run_n0_nextS` (it
returns its goal; the rest kept), `[1 f]` skipped by `+safe-fol-fol`.  Left: `CallNounM` at `x`
with the push of `sof` giving `&`, the lock walk of the lazy need `+soft-bond` returns, and the
`+copy` side condition. -/
theorem comp_run_n2_softTail (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (msup : Option Nomm) (f : Noun)
    (hpn : PastAt ctx env.cod (Nomm.n0 1)) (b : Bell) (hcd : CodePure cod env b) (nb : NeedOrd)
    (region : List Nat) (gs : GenSf (TreapMap mugF))
    (hri : env.ring b = Option.none) (hnb : env.need b = some nb)
    (hsof : env.sof (made (Nomm.n0 1) msup) (Nomm.n0 1) (Nomm.n1 f) b nb = true)
    {Y : GenRest → GenRest → Prop} (hr : ∀ x, Y x x) (ht : ∀ {x y z : GenRest}, Y x y → Y y z → Y x z)
    (hsY : ∀ {x y : GenRest} (s : Noun), Y x y → Y x { y with soft := s })
    (x : GenRest) (hx : x.soft = softMapNoun gs.soft)
    (hn : CallNounM msup ctx (Nomm.n0 1) (Nomm.n1 f) b nb (env.sure b).toNoun x (A 1) (A 0))
    (hlok : ∀ subNed g1 nexB gs2, needOrdAllocRegs nb gs.g = some (subNed, g1) →
      softBond (crdArg subNed g1.bo) region (softGs1 ⟨g1, gs.soft⟩ b subNed (env.sure b)) = some (nexB, gs2) →
      WalkP lok0 0 nexB.laz)
    (hcp : ∀ subNed g1 nexB gs2, needOrdAllocRegs nb gs.g = some (subNed, g1) →
      softBond (crdArg subNed g1.bo) region (softGs1 ⟨g1, gs.soft⟩ b subNed (env.sure b)) = some (nexB, gs2) →
      ∀ nexF g2 nexF' g3 nexS g4, crdFqR (runLC env msup) (Nomm.n1 f) nexB.th region gs2.g = some (nexF, g2) →
      pastL env.cod nexF (Nomm.n0 1) region g2 = some (nexF', g3) →
      runLC env msup (Nomm.n0 1) (CGoalL.next nexB.laz nexF'.th) region g3 = some (nexS, g4) →
      CopyH g4.re nexS.laz nexF'.laz) :
    ∃ x', Y x x' ∧
      nock (crSubj (A 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n1 f) (some (b, Option.none))).toNoun
        (CGoalL.done : CGoalL CSet).toNoun (listNoun A region) (unitNoun Nomm.toNoun msup) (compCore gs.g x ctx)) crDol
      = (runLCS (S := CSet) env snd msup (Nomm.n2 (Nomm.n0 1) (Nomm.n1 f) (some (b, Option.none))) CGoalL.done
          region gs).map
          fun r => C r.1.goal.toNoun (genNoun r.2.g { x' with soft := softMapNoun r.2.soft }) :=
  comp_run_n2_softNT h7 hcode env snd msup (Nomm.n0 1) (Nomm.n1 f) (runLC env msup) (fun _ _ => rfl) rfl hpn b hcd
    nb region gs hri hnb hsof hr ht hsY x hx hn
    (fun subNed g1 nexB gs2 e1 e2 x1 hx1 nexF g2 nexF' g3 h3 h4 => ⟨x1, ⟨hr x1, rfl⟩, by
      rw [runLC_n0]; exact comp_run_n0_nextS h7 1 nexB.laz nexF'.th region g3 (hlok subNed g1 nexB gs2 e1 e2) x1 _ _⟩)
    hcp

end Compiler
end Formalization
