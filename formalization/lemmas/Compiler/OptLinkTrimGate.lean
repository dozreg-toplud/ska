import lemmas.Compiler.OptLinkTrimOuter
import lemmas.Hoon.RunByP

/-!
# `+trim-trace-hints` linked

```hoon
  =/  opened=(set key)
    %-  ~(rep by blocks)
    |=  [[* b=blob] acc=(set key)]
    %+  roll  body.b
    |=  [op=pole acc=_acc]
    ?~  hint=(trace op)  acc
    ?.  open.u.hint  acc
    (~(put in acc) key.u.hint)
  ::
  %-  ~(run by blocks)
  |=  b=blob
  %_    b
      body
    %+  skip  body.b
    |=  op=pole
    ?~  hint=(trace op)  |
    ?&  !(~(has in unsafe) key.u.hint)
        (~(has in opened) key.u.hint)
    ==
  ==
```

* `tr_opened`: `opened` is a set of key nouns with the keys of
  `trimOpened` (`OpRel`), by `rep_gate_rel` over the pairs of `rap` and
  `roll_gate_rel` over each body.
* `tr_sgate`: the test of the `+skip` is `trimDrop`.
* `tr_rngate`: the gate of the `+run:by` on the noun of a block is the
  noun of the block with its body filtered.
* `tr_gate`: **where `trimTraceHints` returns, the gate of
  `+trim-trace-hints` on the nouns of the blocks, `topo` and `rev` returns
  the noun of the result** (`run_by_P` and `isMap_ext` against the
  `TreapMap` of the model, `get_trimRun`).
* `trimLink`: `TrimLink P` for every `P` whose `trim` is `trimTraceHints`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## `opened` -/

/-- The noun `N` is the set of the keys of `l`. -/
def OpRel (N : Noun) (l : List Opt.TKey) : Prop := IsSet mugF N ∧ ∀ x, Has N x ↔ ∃ k ∈ l, x = keyN k

theorem opRel_nil : OpRel (A 0) [] := ⟨isSet_nil, fun x => by simp [uni_has_nil]⟩

/-- The model's step of `opened` on an op. -/
def opStep (l : List Opt.TKey) (op : Pole) : List Opt.TKey :=
  match Opt.traceKey op with
  | some (true, k) => k :: l
  | _ => l

/-- The subject after `unsafe`: `[unsafe [trace gate]]`. -/
def trS2 (U TC BL TOPO REV : Noun) : Noun := C U (C (C trTraceB (C trSBunt TC)) (trG BL TOPO REV))

/-- The subject of the gate of the `+rep:by` of `opened`. -/
def trGS (o : Nat) (bN N U TC BL TOPO REV : Noun) : Noun := C trOGate (C (C (C (A o) bN) N) (trS2 U TC BL TOPO REV))

/-- **The gate of the `+roll` over the body in `opened`**. -/
theorem tr_opg (op : Pole) (N : Noun) (l : List Opt.TKey) (hN : OpRel N l) (bN ACC U TC BL TOPO REV : Noun)
    (o : Nat) :
    ∃ N', nock (C trOpg (C (C op.toNoun N) (trGS o bN ACC U TC BL TOPO REV))) trOpg = some N' ∧
      OpRel N' (opStep l op) := by
  have hL := optC_layer2
  have htr := tr_trace op TC
  unfold trGS trS2 trG
  cases e : Opt.traceKey op with
  | none =>
    have ht : traceN op = A 0 := by simp [traceN, e]
    rw [ht] at htr
    refine ⟨N, ?_, by simpa [opStep, e] using hN⟩
    conv => lhs; arg 2; unfold trOpg
    generalize optC = OC at hL htr
    simp [nock_exec, htr]
  | some p =>
    obtain ⟨b, k⟩ := p
    have ht : traceN op = C (A 0) (C (flag b) (keyN k)) := by simp [traceN, e]
    rw [ht] at htr
    cases b with
    | false =>
      refine ⟨N, ?_, by simpa [opStep, e] using hN⟩
      conv => lhs; arg 2; unfold trOpg
      generalize optC = OC at hL htr
      simp [nock_exec, htr, flag]
    | true =>
      obtain ⟨out, hp, hs, hh⟩ := putInF_spec mugF N (keyN k) hN.1
      refine ⟨out, ?_, hs, fun x => ?_⟩
      · have hpg := put_in_gate (mug := mugF) layer2 gorIn_morIn_layer2 _ _ _ hp
        conv => lhs; arg 2; unfold trOpg
        generalize optC = OC at hL htr
        simp [nock_exec, htr, flag, hL, in.arm_at, in_arm, in.put.arm_at, put_in_arm, hpg]
      · rw [hh, hN.2]
        simp only [opStep, e, List.mem_cons]
        constructor
        · rintro (rfl | ⟨k', hk', rfl⟩)
          · exact ⟨k, Or.inl rfl, rfl⟩
          · exact ⟨k', Or.inr hk', rfl⟩
        · rintro ⟨k', rfl | hk', rfl⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨k', hk', rfl⟩

/-- **The gate of the `+rep:by` of `opened`** on a block. -/
theorem tr_ogate (o : Nat) (b : Blob) (N : Noun) (l : List Opt.TKey) (hN : OpRel N l) (U TC BL TOPO REV : Noun) :
    ∃ N', nock (trGS o b.toNoun N U TC BL TOPO REV) trOGate = some N' ∧ OpRel N' (b.body.foldl opStep l) := by
  have hroll := roll_gate_rel Pole.toNoun OpRel (fun op l => some (opStep l op)) layer2 trOpg poleBunt
    (trGS o b.toNoun N U TC BL TOPO REV) b.body l N (b.body.foldl opStep l)
    (fun op _ l M l' hR hf => by
      cases hf
      exact tr_opg op M l hR b.toNoun N U TC BL TOPO REV o) hN (by rw [foldlM_some])
  obtain ⟨N', hn, hO⟩ := hroll
  refine ⟨N', ?_, hO⟩
  rw [← listNoun_map_listN] at hn
  have hL := optC_layer2
  have hT := optC_types
  have hpm := pole_mold_at
  have hpg := pole_gate
  have hps := pole_gate_bat
  have hpb := pole_bunt'
  unfold trGS trS2 trG at hn ⊢
  obtain ⟨par, body, fin⟩ := b
  simp only [Blob.toNoun] at hn ⊢
  conv => lhs; arg 2; unfold trOGate
  generalize optC = OC at hL hT hn
  generalize compTypes = CT at hT hpm hpg
  generalize poleGateBat = PB at hps hpb
  generalize poleGate = PG at hpg hps hpb
  simp [nock_exec, hL, hT, roll.arm_at, roll_arm, hn, hpm, hpg, hps, hpb, trOBuntF]

theorem trimOpened_rap (bl : TreapMap mugF Blob) :
    Opt.trimOpened bl = (TreapMap.rap bl).foldl (fun l p => p.2.body.foldl opStep l) [] := by
  unfold Opt.trimOpened
  rw [optKeys_eq]
  refine foldl_keys_rap' _ (fun acc (k : Nat) (v : Blob) => v.body.foldl opStep acc) _ (fun p hp acc => ?_) _
  rw [rap_get bl p hp]
  rfl

/-- **`opened`**: the `+rep:by` over the blocks is a set of key nouns with
the keys of `trimOpened`. -/
theorem tr_opened (bl : TreapMap mugF Blob) (U TC TOPO REV : Noun) :
    ∃ N, nock (C by.rep.battery (C (C trOGate (C trOBunt (trS2 U TC (HoonMap.toNoun Blob.toNoun bl) TOPO REV)))
        (C by.battery (C (HoonMap.toNoun Blob.toNoun bl) layer2)))) by.rep.battery = some N ∧
      OpRel N (Opt.trimOpened bl) := by
  have ha : Tree (HoonMap.toNoun Blob.toNoun bl) := by
    rw [hoonMap_toNoun]; exact Tree.of_isMap (bl.2 Blob.toNoun)
  have hP : preorder (HoonMap.toNoun Blob.toNoun bl) = (TreapMap.rap bl).map (Tr.pairNoun Blob.toNoun) := by
    rw [hoonMap_toNoun]; exact TreapMap.preorder_toNoun Blob.toNoun bl
  have h := rep_gate_rel (Tr.pairNoun Blob.toNoun) OpRel (fun p l => some (p.2.body.foldl opStep l)) by.battery
    layer2 trOGate (C (A 0) (C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0)))))
    (trS2 U TC (HoonMap.toNoun Blob.toNoun bl) TOPO REV) _ ha _ hP [] _ (A 0) (by rw [foldlM_some]) opRel_nil
    (fun p hp l N l' hR hf => by
      cases hf
      obtain ⟨o, b⟩ := p
      exact tr_ogate o b N l hR U TC _ TOPO REV)
  rw [← trimOpened_rap] at h
  exact h

/-! ## The `+run:by` -/

/-- **The test of the `+skip`** is `trimDrop`. -/
theorem tr_sgate (op : Pole) (U OPD : Noun) (uns : Opt.Uns) (opened : List Opt.TKey) (hU : UnsRel U uns)
    (hO : OpRel OPD opened) (x TC BL TOPO REV : Noun) :
    nock (C trSGate (C op.toNoun (C trRnGate (C x (C OPD (trS2 U TC BL TOPO REV)))))) trSGate
      = some (loob (Opt.trimDrop uns opened op)) := by
  have hL := optC_layer2
  have htr := tr_trace op TC
  unfold trS2 trG
  cases e : Opt.traceKey op with
  | none =>
    have ht : traceN op = A 0 := by simp [traceN, e]
    rw [ht] at htr
    conv => lhs; arg 2; unfold trSGate
    generalize optC = OC at hL
    simp [nock_exec, htr, Opt.trimDrop, e, loob]
  | some p =>
    obtain ⟨b, k⟩ := p
    have ht : traceN op = C (A 0) (C (flag b) (keyN k)) := by simp [traceN, e]
    rw [ht] at htr
    obtain ⟨t1, h1, e1⟩ := hasInF_spec mugF U (keyN k) hU.1
    obtain ⟨t2, h2, e2⟩ := hasInF_spec mugF OPD (keyN k) hO.1
    have g1 := has_in_gate (mug := mugF) layer2 gorIn_morIn_layer2.1 _ _ _ h1
    have g2 := has_in_gate (mug := mugF) layer2 gorIn_morIn_layer2.1 _ _ _ h2
    have f1 : t1 = uns k := by
      rw [hU.2] at e1
      cases t1 <;> cases hk : uns k <;> simp_all [keyN_inj]
    have f2 : t2 = decide (k ∈ opened) := by
      rw [hO.2] at e2
      by_cases hk : k ∈ opened
      · have : t2 = true := e2.2 ⟨k, hk, rfl⟩
        simp [this, hk]
      · have : t2 = false := by
          cases t2
          · rfl
          · obtain ⟨k', hk', e'⟩ := e2.1 rfl
            rw [keyN_inj] at e'
            subst e'; exact absurd hk' hk
        simp [this, hk]
    subst f1 f2
    conv => lhs; arg 2; unfold trSGate
    generalize optC = OC at hL
    cases b <;> cases hu : uns k <;> by_cases hk : k ∈ opened <;>
      simp [nock_exec, htr, Opt.trimDrop, e, loob, flag, hL, in.arm_at, in_arm, in.has.arm_at, has_in_arm, g1, g2, hk,
        hu]

/-- A block with its body filtered by `trimDrop`. -/
def dropB (uns : Opt.Uns) (opened : List Opt.TKey) (b : Blob) : Blob :=
  { b with body := b.body.filter fun op => !Opt.trimDrop uns opened op }

/-- **The gate of the `+run:by`** on the noun of a block. -/
theorem tr_rngate (b : Blob) (U OPD : Noun) (uns : Opt.Uns) (opened : List Opt.TKey) (hU : UnsRel U uns)
    (hO : OpRel OPD opened) (TC BL TOPO REV : Noun) :
    nock (C trRnGate (C b.toNoun (C OPD (trS2 U TC BL TOPO REV)))) trRnGate
      = some (dropB uns opened b).toNoun := by
  have hL := optC_layer2
  have hsk := skip_gate layer2 trSGate trSBunt (C trRnGate (C b.toNoun (C OPD (trS2 U TC BL TOPO REV))))
    (fun y => Opt.trimDrop uns opened (OptDec.poleDec y)) (b.body.map Pole.toNoun) (fun y hy => by
      obtain ⟨op, -, rfl⟩ := List.mem_map.1 hy
      rw [OptDec.poleDec_toNoun]
      exact tr_sgate op U OPD uns opened hU hO _ TC BL TOPO REV)
  rw [List.filter_map] at hsk
  have hf : (fun op => !Opt.trimDrop uns opened (OptDec.poleDec (Pole.toNoun op)))
      = fun op => !Opt.trimDrop uns opened op := by
    funext op; rw [OptDec.poleDec_toNoun]
  simp only [Function.comp_def, hf] at hsk
  rw [← listNoun_map_listN, ← listNoun_map_listN] at hsk
  unfold trS2 trG at hsk ⊢
  obtain ⟨par, body, fin⟩ := b
  simp only [Blob.toNoun, dropB] at hsk ⊢
  conv => lhs; arg 2; unfold trRnGate
  generalize optC = OC at hL hsk
  simp [nock_exec, hL, skip.arm_at, skip_arm, hsk]

end Compiler
end Formalization
