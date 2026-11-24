import lemmas.Compiler.CompBakeNeed

/-!
# The gate `finish` of `+compile-scc-in`

The gate `finish` (`%compile-scc-finish`, axis `0x2ab2dffd6fbffffffffe` of
`K`, inside `member` of `+compile-scc-in`, `fin_at`) is built on the subject
of `member` after its final pass, `[finBody [pessimized CTX]]`.  Its
`?:  done` branch (`done` at axis `2046`) edits `gen` (axis `254`) three times
and calls `+to-straight`:

1. `+coerce-lazy` of the door `comp` (axis `1022`) with `gen`, on
   `[ned-final o laz cape.less.b]` (axes `1014`, `4062`, `506`, `65520`);
2. `+soft-done` (door battery axis `54644`);
3. `+add-ops` at `o` of `(turn imm.bak |=([r v] [%imm v r]))` (`imm.bak` at
   `4061`);
4. `res = [%next [[ned.bak ~] ~ ~] ~ o]` (`ned.bak` at `4060`), then on
   `pessimized = ~` `+to-straight` of `res` (door arm `6892`), otherwise
   `+coerce-soft` first.

`CTX` is the subject of `member` at the definition of `finish`: here it is
`finCtx`, explicit on the path to `gen` and to the tuple `res` of the
final pass (`[need-new laz ned-final bak o sur]`, axis `30` of `CTX`), with
the rest `REST` (axis `63`) read only at `6` (the door `comp`), `14`
(`done`), `496` (`cape.less.b`) and `0x3ffffff` (`layer2`).

`fin_gate`: on `pessimized = ~`, `done`, a fork-free `laz`, `soft` empty,
`cond` empty, nothing baked (`bak = [ned-final ~]`) and the registers of
`ned-final` a run, the gate returns the noun of `finTail`, the part of the
model's final pass `finishLF` after `+need-ord-alloc-regs`
(`finishLF_tail`).  `fin_gate_finishLF` states it against `finishLF` itself,
given the run and the shape that the final pass computed before `finish`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The nouns -/

/-- The body of the gate `finish`. -/
def finBody : Noun :=
  (C (A 6) (C (C (A 0) (A 2046)) (C (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 8) (C (C (A 8) (C (C (A 0) (A 1022)) (C (A 9) (C (A 5628) (C (A 10) (C (C (A 6) (C (A 0) (A 510))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 2038)) (C (C (A 0) (A 8158)) (C (C (A 0) (A 1018)) (C (A 0) (A 0x1fff0)))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 8) (C (C (A 0) (A 1022)) (C (A 9) (C (A 0x15574) (C (A 10) (C (C (A 6) (C (A 0) (A 510))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 8) (C (C (A 8) (C (C (A 0) (A 1022)) (C (A 9) (C (A 0x2aee) (C (A 10) (C (C (A 6) (C (A 0) (A 510))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 8158)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x1ffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 8157)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) (C (C (A 1) (A 0x6d6d69)) (C (C (A 0) (A 13)) (C (A 0) (A 12))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 8) (C (C (C (A 1) (A 0x7478656e)) (C (C (C (C (A 0) (A 4060)) (C (A 1) (A 0))) (C (A 1) (C (A 0) (A 0)))) (C (C (A 1) (A 0)) (C (A 0) (A 4062))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 14)))) (C (C (A 8) (C (C (A 8) (C (C (A 0) (A 2046)) (C (A 9) (C (A 0x2aec) (C (A 10) (C (C (A 6) (C (A 0) (A 1022))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 8) (C (C (A 0) (A 2046)) (C (A 9) (C (A 766) (C (A 10) (C (C (A 6) (C (A 0) (A 1022))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 61)) (C (A 0) (A 6)))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 8) (C (C (A 0) (A 4094)) (C (A 9) (C (A 0x2aec) (C (A 10) (C (C (A 6) (C (A 0) (A 2046))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2))))))))))))))))))))))))))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 6)))) (C (C (A 0) (A 252)) (C (A 0) (A 13))))) (C (A 1) (C (A 0) (A 0)))))))

def finHint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x6873696e69662d6363732d656c69706d6f63) (C (C (A 0) (A 0x3fffffff)) (A 0))))) (C (A 0) (A 1))))

/-- The formula that builds `finish` in `member`. -/
def finArm : Noun := C (A 7) (C (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) finBody) (C (A 0) (A 1))))) finHint)

/-- `finish` in `K`, inside the arm `+compile-scc-in` (arm `2732`). -/
theorem fin_at : slot? 0x2ab2dffd6fbffffffffe compK = some finArm := by kernel_rfl

/-- The formula builds the gate on any subject. -/
theorem fin_arm (d : Noun) : nock d finArm = some (C finBody (C (A 0) d)) := by
  unfold finArm finHint; generalize finBody = B; simp [nock_exec]

/-- The subject of `member` at the definition of `finish`: explicit on the
path to `gen` (axis `62`) and to the tuple of the final pass (axis `30`). -/
def finCtx (c2 c6 c14 NEWN LAZ NEDF NEDB IMM : Noun) (o : Nat) (SUR G REST : Noun) : Noun :=
  C c2 (C c6 (C c14 (C (C NEWN (C LAZ (C NEDF (C (C NEDB IMM) (C (A o) SUR))))) (C G REST))))

/-! ## The model -/

/-- The part of `finishLF` after `+need-ord-alloc-regs`: the bake,
`+coerce-lazy`, the baked immediates at `o`, `+to-straight`. -/
noncomputable def finTail (nedF : Need) (less : Cape) (o : Nat) (laz : Lazy CSet)
    (bake : Need → Need × List (Nat × Noun)) (g2 : Gen (TreapMap mugF)) : Option (Straight (TreapMap mugF)) :=
  let bak := bake nedF
  (coerceLazyL nedF less o laz g2).bind fun (_, g3) =>
    (addOps o (bak.2.map fun (r, v) => Pole.imm v r) g3).bind fun (_, g4) =>
      toStraightF g4.cond g4.blocks bak.1 o

/-- **`finishLF` is the run, the check of `args`, `+need-ord-alloc-regs`,
then `finTail`.** -/
theorem finishLF_tail (nm : Nomm) (ord : NeedOrd) (less : Cape) (bake : Need → Need × List (Nat × Noun)) :
    finishLF (S := CSet) (Map := TreapMap mugF) nm ord less bake
      = (runL nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))).bind fun (nex, g1) =>
          if nex.th.args ≠ [] then Option.none else
          (needOrdAllocRegs ord g1).bind fun (nedF, g2) => finTail nedF less nex.th.there nex.laz bake g2 := rfl

/-- `soft` empty leaves every block out of `soft`. -/
theorem fin_softOut (x : GenRest) (hs : x.soft = A 0) (o : Nat) : x.SoftOut o := by
  unfold GenRest.SoftOut; rw [hs]; rfl

/-! ## The gate -/

/-- `+turn` of `~` is `~`. -/
theorem fin_turn_nil (bp bs bc : Noun) :
    nock (C turn.battery (C (C (A 0) (C bp (C bs bc))) layer2)) turn.battery = some (A 0) := by
  have h := turn_gate layer2 homoIn_layer2 bp bs bc id [] (by intro x hx; cases hx)
  simpa [listN, appendN] using h

/-- **The gate `finish`** on `~` in the subject of the final pass of
`member`, with `done`, a fork-free `laz`, `soft` and `cond` empty, nothing
baked (`bak` is `[ned-final ~]`) and the registers of `ned-final` a run:
the noun of `finTail` with the bake that bakes nothing. -/
theorem fin_gate {ctx : Noun} (h7 : slot? 7 ctx = some compK) (c2 c6 c14 NEWN SUR REST G0 : Noun)
    (less : Cape) (hcomp : slot? 6 REST = some (C comp.door (C G0 ctx))) (hdone : slot? 14 REST = some (A 0))
    (hless : slot? 496 REST = some less.toNoun) (hl2 : slot? 0x3ffffff REST = some layer2)
    (g : Gen (TreapMap mugF)) (x : GenRest) (hs0 : x.soft = A 0) (hcond : ∀ k, HoonMap.get g.cond k = Option.none)
    (nedF : Need) (hrun : isRun (flattenNeed nedF) ((flattenNeed nedF).headD 0) 0 = true)
    (o : Nat) (s : Sure CSet) :
    nock (C finBody (C (A 0) (finCtx c2 c6 c14 NEWN (Lazy.ofSure s).toNoun nedF.toNoun nedF.toNoun (A 0) o SUR
        (genNoun g x) REST))) finBody
      = (finTail nedF less o (Lazy.ofSure s) (fun n => (n, [])) g).map Straight.toNoun := by
  have hc := (comp_ctx_pill ctx h7).1
  have hcz := cz_gate_L h7 x o (fin_softOut x hs0 o) nedF s less g
  have hczat := comp_cz_at
  have hsdat := sd_at
  have haoat := comp_add_ops_at
  have htsat := comp_ts_at
  unfold finTail
  simp only [List.map_nil]
  cases e1 : coerceLazyL nedF less o (Lazy.ofSure s) g with
  | none =>
    rw [e1] at hcz
    simp only [compCore] at hcz
    conv => { lhs; arg 2; unfold finBody }
    simp only [finCtx]
    generalize comp.door = Dr at hcz hczat hsdat haoat htsat hcomp
    simp [nock_exec, hcomp, hdone, hless, hczat, comp_cz_arm, hcz]
  | some r1 =>
    obtain ⟨u1, g3⟩ := r1
    rw [e1] at hcz
    have hsd := sd_empty ctx hc g3 x hs0
    have hao := comp_add_ops x hc g3 o []
    have kc3 := (kc_coerceLazyL nedF less o (Lazy.ofSure s)).keep g u1 g3 e1
    simp only [listNoun] at hao
    cases e2 : addOps o [] g3 with
    | none =>
      rw [e2] at hao
      simp only [compCore, Option.map_some] at hcz hsd hao
      conv => { lhs; arg 2; unfold finBody }
      simp only [finCtx, Option.bind_some]
      generalize comp.door = Dr at hcz hczat hsdat haoat htsat hcomp hsd hao
      generalize sdArm = SD at hsdat hsd
      simp [nock_exec, hcomp, hdone, hless, hl2, hczat, comp_cz_arm, hcz, hsdat, hsd, haoat, comp_add_ops_arm,
        turn.arm_at, turn_arm, fin_turn_nil, hao, e2]
    | some r2 =>
      obtain ⟨u2, g4⟩ := r2
      rw [e2] at hao
      have kc4 := (KC.addOps' o []).keep g3 u2 g4 e2
      have hts := tsn_at h7 g4 x o nedF (fun k => by rw [kc4, kc3]; exact hcond k) hrun
      simp only [compCore, Option.map_some, tsSampleN] at hcz hsd hao hts
      conv => { lhs; arg 2; unfold finBody }
      simp only [finCtx, Option.bind_some]
      generalize comp.door = Dr at hcz hczat hsdat haoat htsat hcomp hsd hao hts
      generalize sdArm = SD at hsdat hsd
      simp [nock_exec, hcomp, hdone, hless, hl2, hczat, comp_cz_arm, hcz, hsdat, hsd, haoat, comp_add_ops_arm,
        turn.arm_at, turn_arm, fin_turn_nil, hao, htsat, comp_ts_arm, hts, e2]
      all_goals exact hts

/-! ## Against `finishLF` -/

/-- **The gate `finish` returns the noun of `finishLF`**, the model of the
final pass for a bell alone in its SCC, with the bake that bakes nothing:
given the run of the final pass (`runL` from `gen0` gives `nex` and `g1`,
with `args.then.nex = ~`, a fork-free `laz`, `cond` empty) and the shape
`ord` that `+need-ord-alloc-regs` allocates from `g1` (`ned-final` and
`g2`), the gate on the subject that holds them returns
`finishLF nm ord less (fun n => (n, []))`. -/
theorem fin_gate_finishLF {ctx : Noun} (h7 : slot? 7 ctx = some compK) (c2 c6 c14 NEWN SUR REST G0 : Noun)
    (less : Cape) (hcomp : slot? 6 REST = some (C comp.door (C G0 ctx))) (hdone : slot? 14 REST = some (A 0))
    (hless : slot? 496 REST = some less.toNoun) (hl2 : slot? 0x3ffffff REST = some layer2)
    (x : GenRest) (hs0 : x.soft = A 0)
    (nm : Nomm) (ord : NeedOrd) (nex : NextL CSet) (g1 g2 : Gen (TreapMap mugF)) (nedF : Need) (s : Sure CSet)
    (hrunL : runL nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
    (hargs : nex.th.args = []) (hlaz : nex.laz = Lazy.ofSure s)
    (hcond1 : ∀ k, HoonMap.get g1.cond k = Option.none)
    (hnoar : needOrdAllocRegs ord g1 = some (nedF, g2)) :
    nock (C finBody (C (A 0) (finCtx c2 c6 c14 NEWN nex.laz.toNoun nedF.toNoun nedF.toNoun (A 0) nex.th.there SUR
        (genNoun g2 x) REST))) finBody
      = (finishLF (S := CSet) (Map := TreapMap mugF) nm ord less (fun n => (n, []))).map Straight.toNoun := by
  have kc2 := (kc_needOrdAllocRegs (Map := TreapMap mugF) ord).keep g1 nedF g2 hnoar
  have hrun := isRun_needOrdAllocRegs hnoar
  rw [finishLF_tail, hrunL]
  simp only [Option.bind_some, hargs, ne_eq, not_true_eq_false, if_false, hnoar]
  rw [hlaz]
  exact fin_gate h7 c2 c6 c14 NEWN SUR REST G0 less hcomp hdone hless hl2 g2 x hs0
    (fun k => by rw [kc2]; exact hcond1 k) nedF hrun nex.th.there s

/-- **The bake of the final pass bakes nothing** under `NoBake`: the gate of
`+bake-need` on the need of `+need-ord-alloc-regs` returns the `bak` that
`fin_gate_finishLF` assumes, `[ned-final ~]`. -/
theorem fin_bak (ord : NeedOrd) (g1 g2 : Gen (TreapMap mugF)) (nedF : Need) (know : Sock)
    (hnoar : needOrdAllocRegs ord g1 = some (nedF, g2)) (hb : NoBake nedF know) :
    nock (C bnBody (C (C nedF.toNoun know.toNoun) compK)) bnBody = some (C nedF.toNoun (A 0)) :=
  bn_gate nedF know (needNorm_noar ord g1 g2 nedF hnoar) hb

/-- **After `+collapse-shape`**: if the gate of `+shape-collapse` gives the
shape `ord` (`hsc`, as in `cs_gate`) and the gate of `+collapse-shape` on
the `next` of the run returns `[[NF LZ O] G2]`, then `NF`, `LZ`, `O`, `G2`
are the nouns of `ned-final`, `laz.nex`, `there.then.nex` and the state of
`+need-ord-alloc-regs` of `ord`, and the gate `finish` on the subject that
holds them returns the noun of `finishLF nm ord less (fun n => (n, []))`. -/
theorem fin_after_cs {ctx : Noun} (h7 : slot? 7 ctx = some compK) (c2 c6 c14 NEWN SUR REST G0 : Noun)
    (less : Cape) (hcomp : slot? 6 REST = some (C comp.door (C G0 ctx))) (hdone : slot? 14 REST = some (A 0))
    (hless : slot? 496 REST = some less.toNoun) (hl2 : slot? 0x3ffffff REST = some layer2)
    (x : GenRest) (hs0 : x.soft = A 0)
    (nm : Nomm) (ord : NeedOrd) (nex : NextL CSet) (g1 : Gen (TreapMap mugF)) (s : Sure CSet) (LESS : Noun)
    (hrunL : runL nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
    (hlaz : nex.laz = Lazy.ofSure s) (hcond1 : ∀ k, HoonMap.get g1.cond k = Option.none)
    (hsc : nock (C scBody (C (C nex.laz.toNoun LESS) compK)) scBody = some ord.toNoun)
    (NF LZ G2 : Noun) (O : Nat)
    (hcs : nock (C csBody (C (C nex.goal.toNoun LESS) (compCore g1 x ctx))) csBody
      = some (C (C NF (C LZ (A O))) G2)) :
    ∃ (nedF : Need) (g2 : Gen (TreapMap mugF)), needOrdAllocRegs ord g1 = some (nedF, g2) ∧
      NF = nedF.toNoun ∧ LZ = nex.laz.toNoun ∧ O = nex.th.there ∧ G2 = genNoun g2 x ∧
      nock (C finBody (C (A 0) (finCtx c2 c6 c14 NEWN LZ NF NF (A 0) O SUR G2 REST))) finBody
        = (finishLF (S := CSet) (Map := TreapMap mugF) nm ord less (fun n => (n, []))).map Straight.toNoun := by
  rw [cs_gate ctx h7 x g1 nex LESS ord hsc] at hcs
  by_cases ha : nex.th.args ≠ []
  · simp [ha] at hcs
  · simp only [ha, if_false] at hcs
    have ha' : nex.th.args = [] := by simpa using ha
    cases e : needOrdAllocRegs ord g1 with
    | none => rw [e] at hcs; cases hcs
    | some p =>
      obtain ⟨nedF, g2⟩ := p
      rw [e] at hcs
      simp only [Option.map_some, Option.some.injEq, Noun.cell.injEq] at hcs
      obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hcs
      refine ⟨nedF, g2, rfl, h1.symm, h2.symm, ?_, h4.symm, ?_⟩
      · cases h3; rfl
      · rw [← h1, ← h2, ← h4]
        cases h3
        exact fin_gate_finishLF h7 c2 c6 c14 NEWN SUR REST G0 less hcomp hdone hless hl2 x hs0 nm ord nex g1 g2
          nedF s hrunL ha' hlaz hcond1 e
