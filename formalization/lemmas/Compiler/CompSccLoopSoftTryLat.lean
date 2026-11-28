import lemmas.Compiler.CompSccLoopSoftTryS
import lemmas.Compiler.CompSccLoopSoftEmitOps
import lemmas.Compiler.CompCopyLib

/-! # The try path of `+soft-emit`: `lat`, `flag`, `tom` (README Gaps 21.22)

On the subject `tpS0` of `seTryPath` (`tp0`, cut in `CompSccLoopSoftTryCut.lean`):

* **`tl_lat`**: `tpH0` is `(~(got by blocks.gen) last.s)` (a crash on a missing block), and the
  `?>  ?=([~ ~ %hop ~ *] lat)` of `tp1` goes on to `tpY0` with `lat` in front, or crashes;
* **`tl_flag`**: `tpY0` pushes the gate `flag` (`tpFlagN`, its bunt `0`);
* **`tl_tom`**: `tpY1` pushes `tom`, `(malt (turn tops.cut |=([q r ned] [q r])))`: a map noun
  whose pairs are the `[q r]` of `tops`, the last one of each `q` (`AxsRel` on the reversed list,
  as `softEmit`'s `tom` has it). -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## `lat` and the `?>` -/

/-- `tpH0`: `(~(got by blocks.gen) last.s)`, then `tp1` with it in front. -/
theorem tl_got (ctx : Noun) (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (x : GenRest) (o : Nat) (s : SoftCall)
    (HD TR OPS CUT AXS : Noun) :
    nock (tpS0 HD TR OPS CUT AXS o s g x ctx) tp0 =
      (HoonMap.get g.blocks s.last).bind fun b => nock (C b.toNoun (tpS0 HD TR OPS CUT AXS o s g x ctx)) tp1 := by
  have hget := getF_hoonMap Blob.toNoun g.blocks s.last
  have hgc : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
    ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
  conv => { lhs; arg 2; unfold tp0 }
  simp only [tpS0, seS0, compCore]
  generalize tp1 = T1
  generalize comp.door = Dr
  cases e : HoonMap.get g.blocks s.last with
  | none =>
    rw [e] at hget
    have hgot := got_gate_nil layer2 hgc (A s.last) _ hget
    simp [tpH0, nock_exec, genNoun, hc, by_arm, by.arm_at, by.got.arm_at, got_arm, hgot,
      Compiler.SoftCall.toNoun]
  | some b =>
    rw [e] at hget
    have hgot := got_gate layer2 hgc (A s.last) _ _ hget
    simp [tpH0, nock_exec, genNoun, hc, by_arm, by.arm_at, by.got.arm_at, got_arm, hgot,
      Compiler.SoftCall.toNoun]

/-- The `?>  ?=([~ ~ %hop ~ *] lat)` of `tp1` on a block of that form goes on to `tpY0`. -/
theorem tl_test_yes (t : Nat) (S : Noun) :
    nock (C (Blob.toNoun ⟨[], [], Termin.hop ⟨[], t⟩⟩) S) tp1
      = nock (C (Blob.toNoun ⟨[], [], Termin.hop ⟨[], t⟩⟩) S) tpY0 := by
  conv => { lhs; arg 2; unfold tp1 }
  generalize tpY0 = Y
  simp [tpT, tpN0, nock_exec, seHedT, Blob.toNoun, listNoun, Termin.toNoun, Jmp.toNoun, Tag.hop]

/-- **`lat`**: `(~(got by blocks.gen) last.s)` and the `?>  ?=([~ ~ %hop ~ *] lat)`, as `hopOf`
has them (a crash on a missing block or one of another form). -/
theorem tl_lat (ctx : Noun) (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (x : GenRest) (o : Nat) (s : SoftCall)
    (HD TR OPS CUT AXS : Noun) :
    nock (tpS0 HD TR OPS CUT AXS o s g x ctx) tp0 =
      (hopOf s.last g).bind fun p => nock (C p.1.1.toNoun (tpS0 HD TR OPS CUT AXS o s g x ctx)) tpY0 := by
  rw [tl_got ctx hc g x o s HD TR OPS CUT AXS]
  generalize tpS0 HD TR OPS CUT AXS o s g x ctx = S
  unfold hopOf
  cases e : HoonMap.get g.blocks s.last with
  | none => rfl
  | some b =>
    simp only [Option.bind_some]
    by_cases hs : b.par = [] ∧ b.body = [] ∧ ∃ t, b.fin = Termin.hop t ∧ t.args = []
    · obtain ⟨hp, hb, t, hf, ht⟩ := hs
      obtain ⟨par, body, fin⟩ := b
      simp only at hp hb hf
      subst hp hb hf
      obtain ⟨args, there⟩ := t
      simp only at ht
      subst ht
      rw [tl_test_yes]
      simp
    · rw [show tp1 = C (A 6) (C seHedT (C tpY0 (C (A 0) (A 0)))) from rfl, se_bad b hs S tpY0]
      by_cases h1 : b.par = [] ∧ b.body = []
      · rw [if_pos h1]
        cases hf : b.fin with
        | hop t =>
          have : t.args ≠ [] := fun e => hs ⟨h1.1, h1.2, t, hf, e⟩
          simp [this]
        | _ => rfl
      · rw [if_neg h1]; rfl

/-! ## `flag` -/

/-- **`flag`**: `tpY0` pushes the gate core `tpFlagN` of its subject. -/
theorem tl_flag (LAT S : Noun) : nock (C LAT S) tpY0 = nock (C (tpFlagN (C LAT S)) (C LAT S)) tpY1 := by
  conv => { lhs; arg 2; unfold tpY0 }
  generalize tpY1 = Y
  simp [nock_exec, tpYH0, tpFlagN]

/-! ## `tom` -/

/-- `+gas:by` of `[q r]` pairs on a map of `acc`: the map of the reversed list in front of `acc`. -/
theorem tl_gas : ∀ (l : List (Nat × Nat)) (M : Noun) (acc : List (Nat × Nat)), AxsRel M acc →
    ∃ M', gasF mugF M (l.map fun p => (A p.1, A p.2)) = some M' ∧ AxsRel M' (l.reverse ++ acc)
  | [], M, acc, h => ⟨M, rfl, by simpa using h⟩
  | (q, r) :: l, M, acc, h => by
    obtain ⟨M1, hp, h1⟩ := axsRel_put h q r
    obtain ⟨M2, hg, h2⟩ := tl_gas l M1 ((q, r) :: acc) h1
    refine ⟨M2, ?_, by simpa using h2⟩
    simp only [List.map_cons, gasF, hp]
    exact hg

/-- The gate of the `+turn`: `[q r ned]` to `[q r]`. -/
theorem tl_turn (bs bc : Noun) (tops : List (Nat × Nat × Need)) :
    nock (C turn.battery (C (C (listN (tops.map seTopN)) (C (C (C (A 0) (A 12)) (C (A 0) (A 26))) (C bs bc)))
      layer2)) turn.battery
      = some (listN ((tops.map fun t => (A t.1, A t.2.1)).map pairNoun)) := by
  rw [turn_gate layer2 homoIn_layer2 _ bs bc
    (fun y => match y with | Noun.cell a (Noun.cell b _) => C a b | _ => A 0) (tops.map seTopN)
    (fun y hy => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hy
      simp [nock_exec, seTopN])]
  simp [List.map_map, Function.comp_def, seTopN, pairNoun]

/-- **`tom`**: `tpY1` pushes `(malt (turn tops.cut |=([q r ned] [q r])))`, a map noun of the
`[q r]` of `tops` (the last of each `q` wins: `AxsRel` on the reversed list). -/
theorem tl_tom (ctx : Noun) (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (x : GenRest) (o : Nat) (s : SoftCall)
    (HD TR OPS AXS : Noun) (ops : List Pole) (tops : List (Nat × Nat × Need)) :
    ∃ TOM, AxsRel TOM ((tops.map fun t => (t.1, t.2.1)).reverse) ∧ ∀ FLAG LAT : Noun,
      nock (C FLAG (C LAT (tpS0 HD TR OPS (seCutN (ops, tops)) AXS o s g x ctx))) tpY1
        = nock (C TOM (C FLAG (C LAT (tpS0 HD TR OPS (seCutN (ops, tops)) AXS o s g x ctx)))) tpY2 := by
  obtain ⟨TOM, hG, hR⟩ := tl_gas (tops.map fun t => (t.1, t.2.1)) (A 0) [] axsRel_nil
  simp only [List.append_nil, List.map_map] at hG hR
  refine ⟨TOM, hR, fun FLAG LAT => ?_⟩
  have hM := malt_gate _ _ hG
  have hm1 := malt_at
  have ht1 := turn.arm_at
  have hc' : slot? 262143 ctx = some layer2 := hc
  conv => { lhs; arg 2; unfold tpY1 }
  simp only [tpS0, seS0, compCore, seCutN, cd_listNoun_listN] at hM ⊢
  generalize tpY2 = Y
  generalize comp.door = Dr
  have hT : ∀ bs bc, nock (C turn.battery (C (C (listN (tops.map seTopN))
      (C (C (C (A 0) (A 12)) (C (A 0) (A 26))) (C bs bc))) layer2)) turn.battery
      = some (listN ((tops.map fun t => (A t.1, A t.2.1)).map pairNoun)) := fun bs bc => tl_turn bs bc tops
  simp only [List.map_map, Function.comp_def] at hT hM
  generalize layer2 = L2 at hc' hm1 ht1 hT hM ⊢
  simp [tpYH1, nock_exec, hc', hm1, maltArm, ht1, turn_arm, hT, hM, genNoun]

end Compiler
end Formalization
