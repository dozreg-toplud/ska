import lemmas.Compiler.OptLinkHelpers

/-!
# `+remove-dead-code` linked

```hoon
++  remove-dead-code
  ~%  %remove-dead-code  ..ride  ~
  |=  [blocks=(map @uwoo blob) rev-topo=(list @uwoo)]
  ^+  blocks
  =|  new=(map @uwoo blob)
  =|  saw=(set @uvre)
  |-  ^+  new
  ?~  rev-topo  new
  =/  b  (~(got by blocks) i.rev-topo)
  =;  [new-body=(list pole) saw1=(set @uvre)]
    =.  new  (~(put by new) i.rev-topo b(body new-body))
    $(rev-topo t.rev-topo, saw saw1)
  =/  old-body=(list pole)  (flop body.b)
  =.  saw  (~(gas in saw) (get-regs fin.b))
  =|  new-body=(list pole)
  |-  ^+  [new-body saw]
  ?~  old-body  [new-body saw]
  =/  dest=(unit @uvre)  (get-reg-safe-assignment i.old-body)
  ?:  &(?=(^ dest) !(~(has in saw) u.dest))  $(old-body t.old-body)
  %=  $
    old-body  t.old-body
    new-body  [i.old-body new-body]
    saw       (~(gas in saw) (get-regs i.old-body))
  ==
```

The arm is `724` of `optC` (`rdc_at`, nouns by `tools/gen/optlink.py
rdc`): the body pushes `new` and `saw` and kicks the outer trap `rdcTrap`
over `rev-topo`, whose turn takes the block (`rdcGot`), flops its body, adds
the registers of its terminator to `saw` (`rdcGasFin`, `+get-regs`) and runs
the inner trap `rdcInner` over the reversed body, then puts the new block and
turns again (`rdcCont`).

The model `removeDeadCode` (`Ska/OptDead.lean`) keeps `saw` as a list; the
Hoon's is a set.  `SawRel S l`: the noun `S` is a set whose atoms are the
members of `l`.  Only membership is read (`+has:in`), so the outcome of the
Hoon is the model's whatever set the `+gas:in` builds (`saw_gas` gives one,
`saw_has` reads it).

* `rdc_inner`: the inner trap from `[new-body saw]` with `SawRel` is
  `deadBody`, with a set related to the model's `saw`.
* `rdc_trap`: the outer trap is the fold `rdcStep` over `rev-topo`, on blocks
  with no `%lti` (`NoLti`, for `+get-regs` of the terminators).
* `rdc_gate`: **the gate of `+remove-dead-code` on the nouns of a treap of
  blocks with no `%lti` and of a list `rev-topo` is `removeDeadCode`**,
  crashes (a label of `rev-topo` with no block) included.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The nouns -/

/-- The inner trap of `+remove-dead-code`, over the reversed body. -/
def rdcInner : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 14)))) (C (C (C (A 0) (A 6)) (C (A 0) (A 126))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 750) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 60))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 6) (C (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 381) (C (A 10) (C (C (A 6) (C (A 0) (A 510))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 13))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (A 0) (A 61))) (C (A 0) (A 3)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 126) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 187) (C (A 10) (C (C (A 6) (C (A 0) (A 510))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 84) (C (A 0) (A 8191)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 124))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2))))))))) (C (A 10) (C (C (A 14) (C (A 0) (A 61))) (C (A 10) (C (C (A 6) (C (C (A 0) (A 60)) (C (A 0) (A 14)))) (C (A 0) (A 3))))))))))))))))))

/-- `(~(gas in saw) (get-regs fin.b))`. -/
def rdcGasFin : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 187) (C (A 10) (C (C (A 6) (C (A 0) (A 62))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 84) (C (A 0) (A 1023)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2))))))))

/-- The put of the new block and the next turn of the outer trap. -/
def rdcCont : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 126))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 2042)) (C (A 7) (C (C (A 0) (A 3)) (C (A 10) (C (C (A 6) (C (A 0) (A 4))) (C (A 0) (A 6)))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 125) (C (A 0) (A 1019))) (C (A 10) (C (C (A 6) (C (A 0) (A 5))) (C (A 0) (A 7))))))))))

/-- `(~(got by blocks) i.rev-topo)`. -/
def rdcGot : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 252))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 506))) (C (A 0) (A 2))))))))

/-- The outer trap of `+remove-dead-code`, over `rev-topo`. -/
def rdcTrap : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 125)))) (C (C (A 0) (A 14)) (C (A 8) (C rdcGot (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0x2fbd7f) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 26))) (C (A 0) (A 2)))))))) (C (A 7) (C (C (A 10) (C (C (A 30) rdcGasFin) (C (A 0) (A 1)))) (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) rdcInner) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))))))) rdcCont)))))))

/-- The gate body of `+remove-dead-code`. -/
def rdcBody : Noun :=
  (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) rdcTrap) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))))

/-- Its sample bunt. -/
def rdcBunt : Noun :=
  (C (A 0) (A 0))

/-- Its `%fast` hint. -/
def rdcHint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x65646f632d646165642d65766f6d6572) (C (C (A 0) (A 0xffff)) (A 0))))) (C (A 0) (A 1))))

/-- The arm `+remove-dead-code`. -/
def rdcArm : Noun := C (A 7) (C (C (A 8) (C (C (A 1) rdcBunt) (C (C (A 1) rdcBody) (C (A 0) (A 1))))) rdcHint)

/-- `+remove-dead-code` is arm `724` of `optC`. -/
theorem rdc_at : slot? 724 optC = some rdcArm := by kernel_rfl

@[nock_exec] theorem rdc_arm (d : Noun) : nock d rdcArm = some (C rdcBody (C rdcBunt d)) := by
  unfold rdcArm rdcHint; generalize rdcBody = B; generalize rdcBunt = U; simp [nock_exec]

/-! ## The inner trap -/

/-- The subject of the inner trap: `[rdcInner [new-body [old-body [b T]]]]`
with `T = [rdcTrap [saw [new REST]]]`. -/
def rdcI (nb old bN S newN REST : Noun) : Noun :=
  C rdcInner (C nb (C old (C bN (C rdcTrap (C S (C newN REST))))))

/-- **The inner trap** is `deadBody`. -/
theorem rdc_inner (SMP : Noun) :
    ∀ (old nb : List Pole) (sawl : List Nat) (S bN newN : Noun), SawRel S sawl →
    ∃ S', nock (rdcI (listNoun Pole.toNoun nb) (listNoun Pole.toNoun old) bN S newN (C rdcBody (C SMP optC)))
        rdcInner = some (C (listNoun Pole.toNoun (Opt.deadBody old nb sawl).1) S') ∧
      SawRel S' (Opt.deadBody old nb sawl).2 := by
  have hL := optC_layer2
  have hT := optC_types
  have hgs := gs_at
  have hgr := gr_at
  have hgsg := fun p => gs_gate compTypes p
  have hgrg := gr_gate_pole
  generalize optC = OC at hL hT
  generalize compTypes = CT at hT hgs hgr hgsg hgrg
  intro old
  induction old with
  | nil =>
    intro nb sawl S bN newN hS
    refine ⟨S, ?_, hS⟩
    unfold rdcI
    conv => lhs; arg 2; unfold rdcInner
    simp [nock_exec, listNoun, Opt.deadBody]
  | cons op rest ih =>
    intro nb sawl S bN newN hS
    have hh := saw_has hS
    cases hd : Opt.safeAssign op with
    | some d =>
      by_cases hm : d ∈ sawl
      · obtain ⟨S1, hg1, hS1⟩ := saw_gas hS (Opt.poleRegs op)
        obtain ⟨S2, hn2, hS2⟩ := ih (op :: nb) (Opt.poleRegs op ++ sawl) S1 bN newN hS1
        refine ⟨S2, ?_, by simp only [Opt.deadBody, hd, hm, if_true]; exact hS2⟩
        unfold rdcI at hn2 ⊢
        conv => lhs; arg 2; unfold rdcInner
        simp [nock_exec, listNoun, Opt.deadBody, hd, hm, hL, hT, hgs, hgr, gs_arm, gr_arm, hgsg, hgrg, unitNoun,
          in_arm, in.arm_at, has_in_arm, in.has.arm_at, hh, loob, in.gas.arm_at, gas_in_arm, hg1]
        simpa [listNoun] using hn2
      · obtain ⟨S2, hn2, hS2⟩ := ih nb sawl S bN newN hS
        refine ⟨S2, ?_, by simp only [Opt.deadBody, hd, hm, if_false]; exact hS2⟩
        unfold rdcI at hn2 ⊢
        conv => lhs; arg 2; unfold rdcInner
        simp [nock_exec, listNoun, Opt.deadBody, hd, hm, hL, hT, hgs, hgr, gs_arm, gr_arm, hgsg, hgrg, unitNoun,
          in_arm, in.arm_at, has_in_arm, in.has.arm_at, hh, loob]
        simpa [listNoun] using hn2
    | none =>
      obtain ⟨S1, hg1, hS1⟩ := saw_gas hS (Opt.poleRegs op)
      obtain ⟨S2, hn2, hS2⟩ := ih (op :: nb) (Opt.poleRegs op ++ sawl) S1 bN newN hS1
      refine ⟨S2, ?_, by simp only [Opt.deadBody, hd]; exact hS2⟩
      unfold rdcI at hn2 ⊢
      conv => lhs; arg 2; unfold rdcInner
      simp [nock_exec, listNoun, Opt.deadBody, hd, hL, hT, hgs, hgr, gs_arm, gr_arm, hgsg, hgrg, unitNoun,
        in_arm, in.arm_at, in.gas.arm_at, gas_in_arm, hg1]
      simpa [listNoun] using hn2

/-! ## The outer trap -/

/-- One turn of the model's walk over `rev-topo`. -/
def rdcStep (bl : TreapMap mugF Blob) (acc : TreapMap mugF Blob × List Nat) (o : Nat) :
    Option (TreapMap mugF Blob × List Nat) :=
  (HoonMap.get bl o).map fun b =>
    let r := Opt.deadBody b.body.reverse [] (Opt.finRegs b.fin ++ acc.2)
    (HoonMap.put acc.1 o { b with body := r.1 }, r.2)

/-- The subject of the outer trap: `[rdcTrap [saw [new [rdcBody [[blocks rev-topo] optC]]]]]`. -/
def rdcT (S newN BL RT : Noun) : Noun := C rdcTrap (C S (C newN (C rdcBody (C (C BL RT) optC))))

theorem flop_poles (body : List Pole) :
    nock (C flop.battery (C (listNoun Pole.toNoun body) layer2)) flop.battery
      = some (listNoun Pole.toNoun body.reverse) := by
  rw [listNoun_map_listN, listNoun_map_listN, flop_gate layer2 homoIn_layer2, List.map_reverse]

/-- **The outer trap** is the fold of `rdcStep` over `rev-topo`. -/
theorem rdc_trap (bl : TreapMap mugF Blob) (hl : NoLti bl) :
    ∀ (rt : List Nat) (new : TreapMap mugF Blob) (sawl : List Nat) (S : Noun), SawRel S sawl →
    nock (rdcT S (HoonMap.toNoun Blob.toNoun new) (HoonMap.toNoun Blob.toNoun bl) (listNoun A rt)) rdcTrap
      = (rt.foldlM (rdcStep bl) (new, sawl)).map fun r => HoonMap.toNoun Blob.toNoun r.1 := by
  intro rt
  induction rt with
  | nil =>
    intro new sawl S hS
    unfold rdcT
    conv => lhs; arg 2; unfold rdcTrap
    simp [nock_exec, listNoun]
  | cons o rt ih =>
    intro new sawl S hS
    have hL := optC_layer2
    have hT := optC_types
    have hgr := gr_at
    have hg := blocks_got bl
    have hf := flop_poles
    cases hb : HoonMap.get bl o with
    | none =>
      unfold rdcT
      conv => lhs; arg 2; unfold rdcTrap
      generalize optC = OC at hL hT
      generalize HoonMap.toNoun Blob.toNoun bl = BL at hg
      simp [nock_exec, listNoun, rdcGot, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg, hb, rdcStep]
    | some b =>
      obtain ⟨par, body, fin⟩ := b
      have hfp : finPlain fin = true := hl o _ hb
      have hgf := gr_gate_fin fin hfp
      obtain ⟨S1, hg1, hS1⟩ := saw_gas hS (Opt.finRegs fin)
      obtain ⟨S2, hn2, hS2⟩ := rdc_inner (C (HoonMap.toNoun Blob.toNoun bl) (listNoun A (o :: rt)))
        body.reverse [] _ S1 (Blob.toNoun ⟨par, body, fin⟩) (HoonMap.toNoun Blob.toNoun new) hS1
      have hp := putF_hoonMap Blob.toNoun new o ⟨par, (Opt.deadBody body.reverse [] (Opt.finRegs fin ++ sawl)).1, fin⟩
      have hput := put_gate (mug := mugF) layer2 gorIn_morIn_layer2 (A o) _ _ _ hp
      have ih' := ih (HoonMap.put new o ⟨par, (Opt.deadBody body.reverse [] (Opt.finRegs fin ++ sawl)).1, fin⟩)
        (Opt.deadBody body.reverse [] (Opt.finRegs fin ++ sawl)).2 S2 hS2
      unfold rdcT at ih' ⊢
      unfold rdcI at hn2
      conv => lhs; arg 2; unfold rdcTrap
      simp only [Blob.toNoun, listNoun] at hn2 hput ih' ⊢
      generalize optC = OC at hL hT hn2 ih' ⊢
      generalize compTypes = CT at hT hgr hgf
      generalize HoonMap.toNoun Blob.toNoun bl = BL at hg hn2 ih' ⊢
      simp [nock_exec, listNoun, rdcGot, rdcGasFin, rdcCont, hL, hT, hgr, gr_arm, hgf, by.arm_at, by_arm,
        by.got.arm_at, got_arm, hg, hb, flop.arm_at, flop_arm, hf, in_arm, in.arm_at, in.gas.arm_at,
        gas_in_arm, hg1, hn2, by.put.arm_at, put_arm, hput, ih', rdcStep, Blob.toNoun]

/-! ## The gate -/

/-- **`+remove-dead-code`** on the nouns of a treap of blocks with no `%lti`
and of the list `rev-topo`: the noun of `removeDeadCode`, and a crash where
the model is `none`. -/
theorem rdc_gate (bl : TreapMap mugF Blob) (hl : NoLti bl) (rt : List Nat) :
    nock (C rdcBody (C (C (HoonMap.toNoun Blob.toNoun bl) (listNoun A rt)) optC)) rdcBody
      = (Opt.removeDeadCode bl rt).map (HoonMap.toNoun Blob.toNoun) := by
  have ht := rdc_trap bl hl rt HoonMap.empty [] (A 0) sawRel_nil
  rw [HoonMap.toNoun_empty] at ht
  unfold rdcT at ht
  have hm : Opt.removeDeadCode bl rt = (rt.foldlM (rdcStep bl) (HoonMap.empty, [])).map Prod.fst := rfl
  rw [hm, Option.map_map]
  conv => lhs; arg 2; unfold rdcBody
  simp only [nock_exec] at ht ⊢
  exact ht

end Compiler
end Formalization
