import lemmas.Compiler.OptLinkSwTree

/-!
# `+switch-chains`: `nex` and the subjects of the walk

```hoon
  =/  out=(map @uwoo blob-out)  blocks
  =|  done=(set @uwoo)
  =/  nex=@uwoo
    %+  roll  ~(tap in ~(key by blocks))
    |=([o=@uwoo m=@uwoo] ?:((gte o m) `@uwoo`+(o) m))
```

* `nexF`: the fold of `nex` is one more than the largest member, so it is the
  same on two lists with the same members (`nexF_le`, `nexF_congr`).
* `sw_nex`: **`nex` is `nexOf`**: the `+roll` runs over `~(tap in ~(key by
  blocks))`, whose members are the keys of the model's treap, in another
  order than `rap`.
* The walk changes `topo` in its subject, which the gate cores pushed before
  it hold as it was: `swSp BL T0 TOPO REV USES` is the subject after `tree`
  with the gates' `topo` `T0` and the walk's `TOPO` (`swS9 = swSp` at `T0 =
  TOPO`, `swS9_eq`), and `swWk` the core of the walk on it.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The fold of `nex` -/

/-- The step of `nex`. -/
def nexStep (m o : Nat) : Nat := if o ≥ m then o + 1 else m

theorem nexStep_le (m o x : Nat) : nexStep m o ≤ x ↔ m ≤ x ∧ o + 1 ≤ x := by
  unfold nexStep
  by_cases h : o ≥ m
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

theorem nexF_le : ∀ (l : List Nat) (m x : Nat), l.foldl nexStep m ≤ x ↔ m ≤ x ∧ ∀ o ∈ l, o + 1 ≤ x
  | [], m, x => by simp
  | o :: l, m, x => by
    rw [List.foldl_cons, nexF_le l (nexStep m o) x, nexStep_le]
    simp only [List.mem_cons, forall_eq_or_imp, and_assoc]

theorem nexF_congr (l1 l2 : List Nat) (h : ∀ x, x ∈ l1 ↔ x ∈ l2) (m : Nat) :
    l1.foldl nexStep m = l2.foldl nexStep m := by
  apply Nat.le_antisymm
  · rw [nexF_le]
    have := (nexF_le l2 m (l2.foldl nexStep m)).1 (Nat.le_refl _)
    exact ⟨this.1, fun o ho => this.2 o ((h o).1 ho)⟩
  · rw [nexF_le]
    have := (nexF_le l1 m (l1.foldl nexStep m)).1 (Nat.le_refl _)
    exact ⟨this.1, fun o ho => this.2 o ((h o).2 ho)⟩

theorem nexOf_eq (bl : TreapMap mugF Blob) : Opt.nexOf bl = (Opt.MapKeys.keys bl).foldl nexStep 0 := rfl

/-! ## `nex` -/

theorem gteIn_layer1 : LthIn layer1 := arith_layer1.2.2.2.1

/-- **`nex`** on the noun of a treap of blocks: `nexOf`. -/
theorem sw_nex (bl : TreapMap mugF Blob) (TOPO REV USES : Noun) :
    nock (C (A 0) (C (HoonMap.toNoun Blob.toNoun bl) (swS9 (HoonMap.toNoun Blob.toNoun bl) TOPO REV USES))) swNex
      = some (A (Opt.nexOf bl)) := by
  have hm := isMap_hoonMap Blob.toNoun bl
  obtain ⟨K, hk, hs, hh⟩ := keyF_spec hm (A 0) isSet_nil
  have hkey : nock (C by.battery (C (HoonMap.toNoun Blob.toNoun bl) layer2)) by.key.arm = some K := by
    rw [key_arm, key_loop layer2 cs_inIn_layer2 by.battery _ (A 0) K hk]
  have htap : nock (C in.battery (C K layer2)) by.tap.arm = some (listN (tapList K)) := by
    rw [tap_arm, tap_loop, show A 0 = listN [] from rfl, tapF_list (Tree.of_isSet hs), List.append_nil]
  have hmem : ∀ x, x ∈ tapList K ↔ ∃ o, x = A o ∧ o ∈ Opt.MapKeys.keys bl := by
    intro x
    rw [mem_tapList_set hs, hh]
    simp only [uni_has_nil, false_or]
    constructor
    · rintro ⟨v, hv⟩
      obtain ⟨o, b, rfl, hb, rfl⟩ := (get_hoonMap Blob.toNoun bl x v).1 hv
      exact ⟨o, rfl, (Opt.MapKeys.mem_keys bl o).2 (by simp [hb])⟩
    · rintro ⟨o, rfl, ho⟩
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 ((Opt.MapKeys.mem_keys bl o).1 ho)
      exact ⟨Blob.toNoun b, (get_hoonMap Blob.toNoun bl _ _).2 ⟨o, b, rfl, hb, rfl⟩⟩
  have hks : tapList K = ((tapList K).map OptDec.atomOf).map A := by
    rw [List.map_map]
    conv => lhs; rw [← List.map_id (tapList K)]
    apply List.map_congr_left
    intro x hx
    obtain ⟨o, rfl, -⟩ := (hmem x).1 hx
    rfl
  generalize hks' : (tapList K).map OptDec.atomOf = ks at hks
  have hkm : ∀ o, o ∈ ks ↔ o ∈ Opt.MapKeys.keys bl := by
    intro o
    have := hmem (A o)
    rw [hks] at this
    simpa [List.mem_map] using this
  have hroll := roll_gate_list A A (fun o m => some (nexStep m o)) layer2 swNexG (A 0)
    (C (A 0) (C (HoonMap.toNoun Blob.toNoun bl) (swS9 (HoonMap.toNoun Blob.toNoun bl) TOPO REV USES))) ks 0
    (fun o _ m => by
      have hg := gte_gate layer1 gteIn_layer1 o m
      have hL1 := optC_layer1
      unfold swS9 swS8 swS7 swS6 swS5 swS4 swS3 swG
      generalize optC = OC at hL1
      generalize HoonMap.toNoun Blob.toNoun bl = BL
      by_cases e : m ≤ o
      · simp [nock_exec, swNexG, hL1, gte.arm_at, gte_arm, hg, e, nexStep, loob]
      · simp [nock_exec, swNexG, hL1, gte.arm_at, gte_arm, hg, e, nexStep, loob])
  rw [foldlM_some] at hroll
  simp only [Option.map_some] at hroll
  rw [nexOf_eq, ← nexF_congr ks _ hkm]
  rw [hks] at htap
  have hL := optC_layer2
  unfold swS9 swS8 swS7 swS6 swS5 swS4 swS3 swG at *
  generalize optC = OC at hL hroll
  generalize HoonMap.toNoun Blob.toNoun bl = BL at hkey htap hroll
  simp [nock_exec, swNex, hL, roll.arm_at, roll_arm, in.arm_at, in_arm, in.tap.arm_at, htap, by.arm_at, by_arm,
    by.key.arm_at, hkey, hroll]

/-! ## The subjects of the walk -/

/-- The core of `test-of` as the gates after it hold it. -/
def swK4 (BL T0 REV USES : Noun) : Noun := C swTOB (C (A 0) (swS3 BL T0 REV USES))
/-- The core of `chain-of`. -/
def swK5 (BL T0 REV USES : Noun) : Noun := C swCHB (C (A 0) (swS4 BL T0 REV USES))
/-- The core of `plain-of`. -/
def swK6 (BL T0 REV USES : Noun) : Noun := C swPOB (C (A 0) (swS5 BL T0 REV USES))
/-- The core of `plains-of`. -/
def swK7 (BL T0 REV USES : Noun) : Noun := C swPSB (C (A 0) (swS6 BL T0 REV USES))
/-- The core of `cases`. -/
def swK8 (BL T0 REV USES : Noun) : Noun := C swCSB (C (A 0) (swS7 BL T0 REV USES))
/-- The core of `tree`. -/
def swK9 (BL T0 REV USES : Noun) : Noun := C swTRB (C swTRBunt (swS8 BL T0 REV USES))

/-- The subject after `tree`, the gates holding `T0`, the spine `TOPO`. -/
def swSp (BL T0 TOPO REV USES : Noun) : Noun :=
  C (swK9 BL T0 REV USES) (C (swK8 BL T0 REV USES) (C (swK7 BL T0 REV USES) (C (swK6 BL T0 REV USES)
    (C (swK5 BL T0 REV USES) (C (swK4 BL T0 REV USES) (swS3 BL TOPO REV USES))))))

theorem swS9_eq (BL TOPO REV USES : Noun) : swS9 BL TOPO REV USES = swSp BL TOPO TOPO REV USES := rfl

/-- The core of the walk: `[swWalk [nex [done [out spine]]]]`. -/
def swWk (BL T0 TOPO REV USES OUT DONE NEX : Noun) : Noun :=
  C swWalk (C NEX (C DONE (C OUT (swSp BL T0 TOPO REV USES))))

end Compiler
end Formalization
