import lemmas.Compiler.OptLinkHelpers

/-!
# `+rev-cfg` linked

```hoon
++  rev-cfg
  ~%  %rev-cfg  ..ride  ~
  |=  [blocks=(map @uwoo blob) topo-set=(set @uwoo)]
  ^-  (jar @uwoo @uwoo)
  %-  ~(rep by blocks)
  |=  [[o=@uwoo v=blob] acc=(jar @uwoo @uwoo)]
  ?.  (~(has in topo-set) o)  acc
  %+  roll  (get-jmps fin.v)
  |=  [[* o1=@uwoo] =_acc]
  (~(add ja acc) o1 o)
```

The arm is `732` of `optC` (`rev_at`, nouns by `tools/gen/optlink.py
rev`): the `+rep:by` over the blocks with the gate `revGate`, which runs
`+roll` over `+get-jmps` of the terminator with the gate `revRGate`.

The model `revCfg` (`Ska/OptTopo.lean`) takes `topo` as a list; the Hoon
takes a set (`(sy topo)` in `+optimize-once`).  The link takes any set
noun whose atoms are the members of the list (`SawRel`).

* `rev_rgate`: the gate of the `+roll` is `addJa` (`jar_add`).
* `rev_step`: the gate of the `+rep:by` on a pair `(o, v)` is `revStepP`.
* `rev_gate`: **the gate of `+rev-cfg` on the noun of a treap of blocks with
  no `%lti` and a set of labels is the noun of `revCfg`**, the jar laid out
  by `listNoun A`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The nouns -/

/-- The gate of the `+roll` over the jumps: `(~(add ja acc) o1 o)`. -/
def revRGate : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 761) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 4) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 57)) (C (A 0) (A 248)))) (C (A 0) (A 2))))))))

/-- The gate of the `+rep:by` of `+rev-cfg`. -/
def revGate : Noun :=
  (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 381) (C (A 10) (C (C (A 6) (C (A 0) (A 125))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 56))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 1502) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 231))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (A 1) (C (A 0) (A 0))) (C (A 0) (A 13))) (C (C (A 1) revRGate) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (A 0) (A 13)))))

/-- The gate body of `+rev-cfg`. -/
def revBody : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffff)))) (C (A 9) (C (A 767) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (A 0) (C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0))))) (A 0))) (C (C (A 1) revGate) (C (A 0) (A 1)))))))) (C (A 0) (A 2))))))))

/-- Its sample bunt. -/
def revBunt : Noun :=
  (C (A 0) (A 0))

/-- Its `%fast` hint. -/
def revHint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x6766632d766572) (C (C (A 0) (A 0xffff)) (A 0))))) (C (A 0) (A 1))))

/-- The arm `+rev-cfg`. -/
def revArm : Noun := C (A 7) (C (C (A 8) (C (C (A 1) revBunt) (C (C (A 1) revBody) (C (A 0) (A 1))))) revHint)

/-- `+rev-cfg` is arm `732` of `optC`. -/
theorem rev_at : slot? 732 optC = some revArm := by kernel_rfl

@[nock_exec] theorem rev_arm (d : Noun) : nock d revArm = some (C revBody (C revBunt d)) := by
  unfold revArm revHint; generalize revBody = B; generalize revBunt = U; simp [nock_exec]

/-- The noun of a jar of labels. -/
abbrev jarN (m : TreapMap mugF (List Nat)) : Noun := HoonMap.toNoun (listNoun A) m

/-- The subject of the gate of the `+rep:by`. -/
def revG (o : Nat) (v : Blob) (ACC BL TS : Noun) : Noun :=
  C revGate (C (C (C (A o) v.toNoun) ACC) (C revBody (C (C BL TS) optC)))

/-- **The gate of the `+roll`**: `(~(add ja acc) o1 o)`. -/
theorem rev_rgate (o : Nat) (v : Blob) (ACC BL TS : Noun) (j : Jmp) (acc : TreapMap mugF (List Nat)) :
    nock (C revRGate (C (C j.toNoun (jarN acc)) (revG o v ACC BL TS))) revRGate
      = some (jarN (Opt.addJa acc j.there o)) := by
  have hL := optC_layer2
  have hj := jar_add acc j.there o
  unfold revG
  generalize optC = OC at hL
  simp [nock_exec, revRGate, Jmp.toNoun, hL, ja.arm_at, ja_arm, ja.add.arm_at, ja_add_arm, hj]

/-- The step of the model on a pair of `rap`. -/
def revStepP (topo : List Nat) (acc : TreapMap mugF (List Nat)) (p : Nat × Blob) : TreapMap mugF (List Nat) :=
  if p.1 ∈ topo then (Opt.getJmps p.2.fin).foldl (fun acc j => Opt.addJa acc j.there p.1) acc else acc

/-- **The gate of the `+rep:by`** on a pair `(o, v)` whose terminator is not
`%lti`: `revStepP`. -/
theorem rev_step (BL TS : Noun) (topo : List Nat) (hS : SawRel TS topo) (p : Nat × Blob)
    (hp : finPlain p.2.fin = true) (acc : TreapMap mugF (List Nat)) :
    nock (C revGate (C (C (Tr.pairNoun Blob.toNoun p) (jarN acc)) (C revBody (C (C BL TS) optC)))) revGate
      = some (jarN (revStepP topo acc p)) := by
  obtain ⟨o, v⟩ := p
  have hL := optC_layer2
  have hT := optC_types
  have hh := saw_has hS o
  have hgj := gj_gate compTypes v.fin hp
  have hgja := gj_at
  have hroll := roll_gate_list Jmp.toNoun jarN (fun j acc => some (Opt.addJa acc j.there o)) layer2 revRGate
    (C (A 0) (A 0)) (revG o v (jarN acc) BL TS) (Opt.getJmps v.fin) acc
    (fun j _ s => by rw [rev_rgate]; rfl)
  rw [foldlM_some, ← listNoun_map_listN] at hroll
  unfold revG at hroll
  simp only [Tr.pairNoun]
  generalize optC = OC at hL hT hroll
  generalize compTypes = CT at hT hgj hgja
  conv => lhs; arg 2; unfold revGate
  by_cases ho : o ∈ topo
  · simp [nock_exec, revStepP, ho, hL, hT, in_arm, in.arm_at, has_in_arm, in.has.arm_at, hh, loob,
      roll.arm_at, roll_arm, hgja, gj_arm, hgj, hroll]
  · simp [nock_exec, revStepP, ho, hL, hT, in_arm, in.arm_at, has_in_arm, in.has.arm_at, hh, loob]

/-- The model's fold in the order of `rap`. -/
theorem rev_fold (bl : TreapMap mugF Blob) (topo : List Nat) :
    Opt.revCfg bl topo = (TreapMap.rap bl).foldl (revStepP topo) HoonMap.empty := by
  unfold Opt.revCfg
  rw [optKeys_eq]
  exact foldl_keys_rap' (Opt.revStep bl topo) (fun acc k v => revStepP topo acc (k, v)) _
    (fun p hp acc => by simp [Opt.revStep, rap_get bl p hp, revStepP]) _

/-- **`+rev-cfg`** on the noun of a treap of blocks with no `%lti` and a set
`TS` of the labels of `topo`: the noun of `revCfg`. -/
theorem rev_gate (bl : TreapMap mugF Blob) (hl : NoLti bl) (topo : List Nat) (TS : Noun)
    (hS : SawRel TS topo) :
    nock (C revBody (C (C (HoonMap.toNoun Blob.toNoun bl) TS) optC)) revBody
      = some (jarN (Opt.revCfg bl topo)) := by
  have hL := optC_layer2
  have ha : Tree (HoonMap.toNoun Blob.toNoun bl) := by
    rw [hoonMap_toNoun]; exact Tree.of_isMap (bl.2 Blob.toNoun)
  have hP : preorder (HoonMap.toNoun Blob.toNoun bl) = (TreapMap.rap bl).map (Tr.pairNoun Blob.toNoun) := by
    rw [hoonMap_toNoun]; exact TreapMap.preorder_toNoun Blob.toNoun bl
  have hrep := rep_gate_list (Tr.pairNoun Blob.toNoun) jarN (fun p s => some (revStepP topo s p)) by.battery
    layer2 revGate (C (A 0) (C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0)))))
    (C revBody (C (C (HoonMap.toNoun Blob.toNoun bl) TS) optC)) _ ha _ hP HoonMap.empty
    (fun p hp s => by rw [rev_step _ _ topo hS p (hl p.1 p.2 (rap_get bl p hp))]; rfl)
  rw [foldlM_some] at hrep
  simp only [Option.map_some, jarN, HoonMap.toNoun_empty] at hrep
  rw [rev_fold]
  rw [← hrep]
  conv => lhs; arg 2; unfold revBody
  generalize HoonMap.toNoun Blob.toNoun bl = BL
  generalize revGate = G
  generalize optC = OC at hL
  simp [nock_exec, hL, by.arm_at, by_arm, by.rep.arm_at, rep_arm]

end Compiler
end Formalization
