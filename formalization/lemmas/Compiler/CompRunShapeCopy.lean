import lemmas.Compiler.CompRunShapeFrom
import lemmas.Compiler.CompRunShapeCopyCut
import lemmas.Compiler.CompRunShapeNoneCut
import lemmas.Compiler.CompCopyMerge
import lemmas.Compiler.CompShapeColUni

/-!
# The link of `+laze-copy` (track A, 2026-11-27)

`+laze-copy` (door arm `0xabb6`, cut in `CompRunShapeCopyCut.lean`) against `lazeCopy` of
`Ska/RunShape.lean`, on every pair of `laze`s (forks and bonds to any depth) and every noun `G`
of `gen` (the arm reads none of it), under `CompIn ctx` and `K` at axis `7` of `ctx` (for
`+uni-need-ord`).  The proof of `copy_all` (`CompCopyAll.lean`) without registers and without
`gen`: the merge is a `+turn` (not a `+spin`), so the gates are `turn_gate_mapT`.  The index of
the merge is the model's `lastF` / `lastB` (`lc_get_index`: `+get:by` of the `+malt` is the last
entry under the key), the seen set its `any` (`lc_any`).  No departure.

* `lc_arm`, **`lc_door`**: the arm builds the gate.
* `lc_sure`: the sure need (`uno_gate`, `cs_uni_is`).
* `lc_fgate`, `lc_bgate`: the merge gates; `lc_fpart`, `lc_bpart`: the fork and bond parts.
* **`lc_all`** (with `lc_forks`, `lc_bonds`): the gate is `lazeCopy`.
* **`lazeCopy_nz`**: `LzNZ` is kept (the looks of the product are those of the two).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-! ## The model, as the Hoon computes it -/

/-- The merge gate over the forks of `first`, in the model. -/
noncomputable def lcFG (sec : List ((Nat × Laze CSet) × (Nat × Laze CSet)))
    (e : (Nat × Laze CSet) × (Nat × Laze CSet)) : Option ((Nat × Laze CSet) × (Nat × Laze CSet)) :=
  match lastF sec e.1.1 with
  | Option.none => some e
  | some ((_, my), (mon, mn)) =>
    if e.2.1 = mon then
      (lazeCopy e.1.2 my).bind fun y => (lazeCopy e.2.2 mn).map fun n => ((e.1.1, y), (e.2.1, n))
    else Option.none

/-- The merge gate over the bonds of `first`, in the model. -/
noncomputable def lcBG (sec : List (Nat × Laze CSet)) (e : Nat × Laze CSet) : Option (Nat × Laze CSet) :=
  match lastB sec e.1 with
  | Option.none => some e
  | some (_, m) => (lazeCopy e.2 m).map fun c => (e.1, c)

theorem lc_copyF (sec : List ((Nat × Laze CSet) × (Nat × Laze CSet))) :
    ∀ fk : List ((Nat × Laze CSet) × (Nat × Laze CSet)), copyF fk sec = fk.mapM (lcFG sec)
  | [] => rfl
  | ((oy, y), (on, n)) :: rest => by
    simp only [copyF, List.mapM_cons, lcFG, lc_copyF sec rest]
    cases lastF sec oy with
    | none => simp only; cases rest.mapM (lcFG sec) <;> rfl
    | some v =>
      obtain ⟨⟨_, my⟩, ⟨mon, mn⟩⟩ := v
      simp only
      by_cases h : on = mon
      · simp only [h, ne_eq, not_true_eq_false, if_false, if_true]
        cases lazeCopy y my <;> cases lazeCopy n mn <;> cases rest.mapM (lcFG sec) <;> rfl
      · simp [h]

theorem lc_copyB (sec : List (Nat × Laze CSet)) :
    ∀ bd : List (Nat × Laze CSet), copyB bd sec = bd.mapM (lcBG sec)
  | [] => rfl
  | (o, l) :: rest => by
    simp only [copyB, List.mapM_cons, lcBG, lc_copyB sec rest]
    cases lastB sec o with
    | none => simp only; cases rest.mapM (lcBG sec) <;> rfl
    | some v =>
      obtain ⟨_, m⟩ := v
      simp only
      cases lazeCopy l m <;> cases rest.mapM (lcBG sec) <;> rfl

/-- The fork part of `lazeCopy`. -/
noncomputable def lcFP (ff fs : List ((Nat × Laze CSet) × (Nat × Laze CSet))) :
    Option (List ((Nat × Laze CSet) × (Nat × Laze CSet))) :=
  if fs.isEmpty then some ff else if ff.isEmpty then some fs else
    (copyF ff fs).map fun m => m ++ fs.filter fun e => !(ff.any fun x => x.1.1 == e.1.1)

/-- The bond part of `lazeCopy`. -/
noncomputable def lcBP (bf bs : List (Nat × Laze CSet)) : Option (List (Nat × Laze CSet)) :=
  if bs.isEmpty then some bf else if bf.isEmpty then some bs else
    (copyB bf bs).map fun m => m ++ bs.filter fun e => !(bf.any fun x => x.1 == e.1)

theorem lazeCopy_eq (sf ss : SureO CSet) (ff fs bf bs) :
    lazeCopy (Laze.mk sf ff bf) (Laze.mk ss fs bs)
      = (lcFP ff fs).bind fun fk => (lcBP bf bs).map fun bd =>
          Laze.mk ⟨uniOrd sf.ned ss.ned, HoonSet.uni sf.lok ss.lok⟩ fk bd := by
  rw [lazeCopy]; rfl

/-! ## The index and the seen set -/

theorem lc_get_foldl {α : Type} (key : α → Nat) : ∀ (l : List α) (m : TreapMap mugF α) (k : Nat),
    HoonMap.get (l.foldl (fun m e => HoonMap.put m (key e) e) m) k
      = ((l.filter fun e => key e == k).getLast?).or (HoonMap.get m k)
  | [], m, k => by simp
  | e :: rest, m, k => by
    rw [List.foldl_cons, lc_get_foldl key rest _ k, HoonMap.get_put]
    by_cases h : key e = k
    · subst h
      simp only [List.filter_cons, beq_self_eq_true, if_true, if_pos rfl, List.getLast?_cons]
      cases (rest.filter fun x => key x == key e).getLast? <;> rfl
    · have h' : ¬ k = key e := fun x => h x.symm
      simp only [List.filter_cons, h', if_false]
      have hb : (key e == k) = false := by simp [h]
      simp only [hb, Bool.false_eq_true, if_false]

/-- **`+get:by` of the index** (`+malt` of the pairs) is the last entry under the key. -/
theorem lc_get_index {α : Type} (key : α → Nat) (l : List α) (k : Nat) :
    HoonMap.get (Lazy.index (Map := TreapMap mugF) key l) k = (l.filter fun e => key e == k).getLast? := by
  unfold Lazy.index
  rw [lc_get_foldl, HoonMap.get_empty]
  cases (l.filter fun e => key e == k).getLast? <;> rfl

theorem lc_any {α : Type} (key : α → Nat) (k : Nat) :
    ∀ l : List α, (l.any fun x => key x == k) = decide (k ∈ l.map key)
  | [] => rfl
  | a :: l => by
    rw [List.any_cons, lc_any key k l]
    by_cases h : key a = k
    · simp [h]
    · have h' : ¬ k = key a := fun x => h x.symm
      simp [h, h']

/-! ## The arm, the sure need -/

/-- The arm builds its gate. -/
theorem lc_arm (d : Noun) : nock d lcArm = some (C lcGate (C lcBunt d)) := by
  unfold lcArm lcHint; simp only [nock_exec]

/-- **The arm `+laze-copy` on the door gives the gate `lcGate`**. -/
theorem lc_door (y : Noun) : nock (C comp.door y) (C (A 9) (C (A 0xabb6) (C (A 0) (A 1))))
    = some (C lcGate (C lcBunt (C comp.door y))) := by
  simp [nock_exec, lc_at', lc_arm]

/-- The gate is the cons of its three parts. -/
theorem lc_gate_cons (S : Noun) : nock S lcGate
    = (nock S lcSure).bind fun a => (nock S lcFX).bind fun b => (nock S lcBX).bind fun c => some (C a (C b c)) := by
  obtain ⟨b1, c1, h1⟩ : ∃ b c, lcSure = C b c := ⟨_, _, rfl⟩
  obtain ⟨b2, c2, h2⟩ : ∃ b c, lcFX = C b c := ⟨_, _, rfl⟩
  unfold lcGate
  rw [h1, nock_cell, ← h1, h2, nock_cell, ← h2]
  cases nock S lcSure <;> cases nock S lcFX <;> cases nock S lcBX <;> rfl

/-- The sure need: `+uni-need-ord` of the needs and `+uni:in` of the looks. -/
theorem lc_sure (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) (G : Noun) (sf ss : SureO CSet)
    (Ff Fs : Noun) :
    nock (C lcGate (C (C (C sf.toNoun Ff) (C ss.toNoun Fs)) (C comp.door (C G ctx)))) lcSure
      = some (SureO.toNoun (⟨uniOrd sf.ned ss.ned, HoonSet.uni sf.lok ss.lok⟩ : SureO CSet)) := by
  obtain ⟨n1, l1⟩ := sf
  obtain ⟨n2, l2⟩ := ss
  have hu := uno_gate compK compK_cn n1 n2
  have huni := cs_uni_is l1 l2
  unfold lcSure
  simp [nock_exec, SureO.toNoun, h7, uno_at, uno_arm, hu, hc, in_arm, in.arm_at, in.uni.arm_at,
    cl_uni_arm, huni]

/-! ## The merge gates -/

/-- The pair `[key e]` of a fork's noun, through the inline gate `[[0 24] 0 6]`. -/
theorem lc_turn_pairs (bs bc : Noun) (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet))) :
    nock (C turn.battery (C (C (listN (fk.map lzfE)) (C (C (C (A 0) (A 24)) (C (A 0) (A 6))) (C bs bc))) layer2))
      turn.battery = some (listN ((fk.map fun e => (A e.1.1, lzfE e)).map pairNoun)) := by
  rw [turn_gate layer2 homoIn_layer2 _ bs bc pairOf (fk.map lzfE) (fun y hy => by
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hy
    simp [nock_exec, lzfE, pairOf])]
  simp [List.map_map, Function.comp_def, lzfE, pairOf, pairNoun]

theorem lc_turn_keys (bs bc : Noun) (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet))) :
    nock (C turn.battery (C (C (listN (fk.map lzfE)) (C (C (A 0) (A 24)) (C bs bc))) layer2))
      turn.battery = some (listN ((fk.map fun e => e.1.1).map A)) := by
  rw [turn_gate layer2 homoIn_layer2 _ bs bc keyOf (fk.map lzfE) (fun y hy => by
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hy
    simp [nock_exec, lzfE, keyOf])]
  simp [List.map_map, Function.comp_def, lzfE, keyOf]

theorem lc_turn_pairsB (bs bc : Noun) (bd : List (Nat × Laze CSet)) :
    nock (C turn.battery (C (C (listN (bd.map lzbE)) (C (C (C (A 0) (A 12)) (C (A 0) (A 6))) (C bs bc))) layer2))
      turn.battery = some (listN ((bd.map fun e => (A e.1, lzbE e)).map pairNoun)) := by
  rw [turn_gate layer2 homoIn_layer2 _ bs bc pairOfB (bd.map lzbE) (fun y hy => by
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hy
    simp [nock_exec, lzbE, pairOfB])]
  simp [List.map_map, Function.comp_def, lzbE, pairOfB, pairNoun]

theorem lc_turn_keysB (bs bc : Noun) (bd : List (Nat × Laze CSet)) :
    nock (C turn.battery (C (C (listN (bd.map lzbE)) (C (C (A 0) (A 12)) (C bs bc))) layer2))
      turn.battery = some (listN ((bd.map fun e => e.1).map A)) := by
  rw [turn_gate layer2 homoIn_layer2 _ bs bc keyOfB (bd.map lzbE) (fun y hy => by
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hy
    simp [nock_exec, lzbE, keyOfB])]
  simp [List.map_map, Function.comp_def, lzbE, keyOfB]

section
variable (hc : CompIn ctx) (G : Noun)
include hc

/-- **The merge gate over the forks**: the lookup in the index, `e` itself without an entry,
the `?>` on the no blocks, then `+laze-copy` of the yes needs and of the no needs. -/
theorem lc_fgate (sec : List ((Nat × Laze CSet) × (Nat × Laze CSet))) (e : (Nat × Laze CSet) × (Nat × Laze CSet))
    (X : Noun)
    (ihy : ∀ m : Laze CSet, nock (C lcGate (C (C e.1.2.toNoun m.toNoun) (C comp.door (C G ctx)))) lcGate
      = (lazeCopy e.1.2 m).map Laze.toNoun)
    (ihn : ∀ m : Laze CSet, nock (C lcGate (C (C e.2.2.toNoun m.toNoun) (C comp.door (C G ctx)))) lcGate
      = (lazeCopy e.2.2 m).map Laze.toNoun) :
    nock (C lcMF (C (lzfE e) (C (HoonMap.toNoun lzfE (Lazy.index (Map := TreapMap mugF)
      (fun e : (Nat × Laze CSet) × (Nat × Laze CSet) => e.1.1) sec))
      (C lcGate (C X (C comp.door (C G ctx))))))) lcMF
      = (lcFG sec e).map lzfE := by
  obtain ⟨⟨oy, y⟩, ⟨on, n⟩⟩ := e
  have hget := getF_hoonMap lzfE (Lazy.index (Map := TreapMap mugF)
    (fun e : (Nat × Laze CSet) × (Nat × Laze CSet) => e.1.1) sec) oy
  rw [lc_get_index] at hget
  have hgg := get_gate layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ (A oy) _ _ hget
  have hl : lastF sec oy = (sec.filter fun e => e.1.1 == oy).getLast? := rfl
  rw [← hl] at hgg
  unfold lcMF
  simp only at ihy ihn
  cases ev : lastF sec oy with
  | none =>
    rw [ev] at hgg
    simp [nock_exec, hc, by_arm, by.arm_at, get_arm, by.get.arm_at, hgg, unitNoun, lcFG, ev, lzfE]
  | some v =>
    obtain ⟨⟨oy', my⟩, ⟨mon, mn⟩⟩ := v
    rw [ev] at hgg
    by_cases hon : on = mon
    · subst hon
      have hy := ihy my
      have hn := ihn mn
      cases e1 : lazeCopy y my with
      | none =>
        rw [e1] at hy
        simp [nock_exec, hc, by_arm, by.arm_at, get_arm, by.get.arm_at, hgg, unitNoun, lcFG, ev, lzfE,
          hy, e1, lc_at', lc_arm]
      | some y' =>
        rw [e1] at hy
        cases e2 : lazeCopy n mn with
        | none =>
          rw [e2] at hn
          simp [nock_exec, hc, by_arm, by.arm_at, get_arm, by.get.arm_at, hgg, unitNoun, lcFG, ev, lzfE,
            hy, e1, hn, e2, lc_at', lc_arm]
        | some n' =>
          rw [e2] at hn
          simp [nock_exec, hc, by_arm, by.arm_at, get_arm, by.get.arm_at, hgg, unitNoun, lcFG, ev, lzfE,
            hy, e1, hn, e2, lc_at', lc_arm]
    · simp [nock_exec, hc, by_arm, by.arm_at, get_arm, by.get.arm_at, hgg, unitNoun, lcFG, ev, lzfE, hon,
        eqCode_atom]

/-- **The merge gate over the bonds**: the lookup, `e` itself without an entry, else
`+laze-copy` of the two needs of the block. -/
theorem lc_bgate (sec : List (Nat × Laze CSet)) (e : Nat × Laze CSet) (X : Noun)
    (ih : ∀ m : Laze CSet, nock (C lcGate (C (C e.2.toNoun m.toNoun) (C comp.door (C G ctx)))) lcGate
      = (lazeCopy e.2 m).map Laze.toNoun) :
    nock (C lcMB (C (lzbE e) (C (HoonMap.toNoun lzbE (Lazy.index (Map := TreapMap mugF)
      (fun e : Nat × Laze CSet => e.1) sec))
      (C lcGate (C X (C comp.door (C G ctx))))))) lcMB
      = (lcBG sec e).map lzbE := by
  obtain ⟨ob, l⟩ := e
  have hget := getF_hoonMap lzbE (Lazy.index (Map := TreapMap mugF) (fun e : Nat × Laze CSet => e.1) sec) ob
  rw [lc_get_index] at hget
  have hgg := get_gate layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ (A ob) _ _ hget
  have hl : lastB sec ob = (sec.filter fun e => e.1 == ob).getLast? := rfl
  rw [← hl] at hgg
  unfold lcMB
  simp only at ih
  cases ev : lastB sec ob with
  | none =>
    rw [ev] at hgg
    simp [nock_exec, hc, by_arm, by.arm_at, get_arm, by.get.arm_at, hgg, unitNoun, lcBG, ev, lzbE]
  | some v =>
    obtain ⟨ob', m⟩ := v
    rw [ev] at hgg
    have hm := ih m
    cases e1 : lazeCopy l m with
    | none =>
      rw [e1] at hm
      simp [nock_exec, hc, by_arm, by.arm_at, get_arm, by.get.arm_at, hgg, unitNoun, lcBG, ev, lzbE,
        hm, e1, lc_at', lc_arm]
    | some l' =>
      rw [e1] at hm
      simp [nock_exec, hc, by_arm, by.arm_at, get_arm, by.get.arm_at, hgg, unitNoun, lcBG, ev, lzbE,
        hm, e1, lc_at', lc_arm]

end

/-! ## The fork and bond parts -/

section
variable (hc : CompIn ctx) (G : Noun)
include hc

/-- **The fork part** (`lcFX`): `lcFP`, given the merge gate at every fork of `first`. -/
theorem lc_fpart (sf ss : SureO CSet) (ff fs : List ((Nat × Laze CSet) × (Nat × Laze CSet)))
    (bf bs : List (Nat × Laze CSet))
    (hgate : ∀ e ∈ ff, ∀ X : Noun,
      nock (C lcMF (C (lzfE e) (C (HoonMap.toNoun lzfE (Lazy.index (Map := TreapMap mugF)
        (fun e : (Nat × Laze CSet) × (Nat × Laze CSet) => e.1.1) fs))
        (C lcGate (C X (C comp.door (C G ctx))))))) lcMF = (lcFG fs e).map lzfE) :
    nock (C lcGate (C (C (C sf.toNoun (C (listN (ff.map lzfE)) (listN (bf.map lzbE))))
      (C ss.toNoun (C (listN (fs.map lzfE)) (listN (bs.map lzbE))))) (C comp.door (C G ctx)))) lcFX
      = (lcFP ff fs).map fun r => listN (r.map lzfE) := by
  have tF := lz_test lzfE ff
  have tS := lz_test lzfE fs
  unfold lcFX
  rcases tS with ⟨s1, s2, s3⟩ | ⟨s1, s2, s3⟩
  · subst s1
    simp [nock_exec, s2, s3, lcFP]
  rcases tF with ⟨f1, f2, f3⟩ | ⟨f1, f2, f3⟩
  · subst f1
    simp [nock_exec, s2, s3, f2, f3, lcFP, s1]
  have hT0 := lc_turn_pairs (C (C (A 0) lneBunt) (C (A 0) lneBunt))
    (C lcGate (C (C (C sf.toNoun (C (listN (ff.map lzfE)) (listN (bf.map lzbE))))
      (C ss.toNoun (C (listN (fs.map lzfE)) (listN (bs.map lzbE))))) (C comp.door (C G ctx)))) fs
  have hIdx := malt_gate _ _ (malt_index lzfE (fun e : (Nat × Laze CSet) × (Nat × Laze CSet) => e.1.1) fs)
  unfold lneBunt at hT0
  simp only [lcFP, s1, f1, List.isEmpty_iff, if_false, lc_copyF]
  generalize hidx : Lazy.index (Map := TreapMap mugF)
    (fun e : (Nat × Laze CSet) × (Nat × Laze CSet) => e.1.1) fs = idx at hIdx hgate
  have hM := turn_gate_mapT lzfE lzfE layer2 homoIn_layer2 lcMF (C (C (A 0) lneBunt) (C (A 0) lneBunt))
    (C (HoonMap.toNoun lzfE idx) (C lcGate (C (C (C sf.toNoun (C (listN (ff.map lzfE)) (listN (bf.map lzbE))))
      (C ss.toNoun (C (listN (fs.map lzfE)) (listN (bs.map lzbE))))) (C comp.door (C G ctx)))))
    (lcFG fs) ff (fun e he => hgate e he _)
  unfold lneBunt at hM
  simp only [List.map_map] at hT0 hIdx
  have hm1 := malt_at
  have ht1 := turn.arm_at
  have hc' : slot? 262143 ctx = some layer2 := hc
  cases eS : ff.mapM (lcFG fs) with
  | none =>
    rw [eS] at hM
    generalize layer2 = L2 at hc' hm1 ht1 hT0 hIdx hM ⊢
    simp [nock_exec, s2, s3, f2, f3, hc', ht1, turn_arm, hT0, hm1, maltArm, hIdx, hM, eS]
  | some merged =>
    rw [eS] at hM
    have hTk := lc_turn_keys (C (C (A 0) lneBunt) (C (A 0) lneBunt))
      (C (listN (merged.map lzfE)) (C (HoonMap.toNoun lzfE idx) (C lcGate (C (C (C sf.toNoun
        (C (listN (ff.map lzfE)) (listN (bf.map lzbE))))
        (C ss.toNoun (C (listN (fs.map lzfE)) (listN (bs.map lzbE))))) (C comp.door (C G ctx)))))) ff
    unfold lneBunt at hTk
    simp only [List.map_map] at hTk
    obtain ⟨S0, hS0, hhas⟩ := seen_set (ff.map fun e => e.1.1)
    have hSilt := cm_silt_gate _ S0 hS0
    simp only [List.map_map] at hSilt
    have hSkip := skip_gate_map lzfE layer2 lcSF (C (C (A 0) lneBunt) (C (A 0) lneBunt))
      (C S0 (C (listN (merged.map lzfE)) (C (HoonMap.toNoun lzfE idx) (C lcGate (C (C (C sf.toNoun
        (C (listN (ff.map lzfE)) (listN (bf.map lzbE))))
        (C ss.toNoun (C (listN (fs.map lzfE)) (listN (bs.map lzbE))))) (C comp.door (C G ctx)))))))
      (fun e => decide (e.1.1 ∈ ff.map fun e => e.1.1)) fs (fun e _ => by
        have := hhas e.1.1
        unfold lcSF
        simp [nock_exec, hc, in_arm, in.arm_at, in.has.arm_at, has_in_arm, this, lzfE])
    unfold lneBunt at hSkip
    have hW := weld_gate_list layer2 (merged.map lzfE)
      ((fs.filter fun a => !decide (a.1.1 ∈ ff.map fun e => e.1.1)).map lzfE)
    have hfil : (fs.filter fun e => !(ff.any fun x => x.1.1 == e.1.1))
        = fs.filter fun a => !decide (a.1.1 ∈ ff.map fun e => e.1.1) := by
      congr 1; funext a; rw [lc_any (fun x : (Nat × Laze CSet) × (Nat × Laze CSet) => x.1.1)]
    rw [hfil]
    have hsl := silt.arm_at
    have hsk := skip.arm_at
    have hwl := weld.arm_at
    generalize layer2 = L2 at hc' hm1 ht1 hT0 hIdx hM hTk hSilt hSkip hW hsl hsk hwl ⊢
    simp [nock_exec, s2, s3, f2, f3, hc', ht1, turn_arm, hT0, hm1, maltArm, hIdx, hM, eS, hTk, hsl,
      cm_silt_arm, hSilt, hsk, lp_skip_arm, hSkip, hwl, weld_arm, hW]

/-- **The bond part** (`lcBX`): `lcBP`, given the merge gate at every bond of `first`. -/
theorem lc_bpart (sf ss : SureO CSet) (ff fs : List ((Nat × Laze CSet) × (Nat × Laze CSet)))
    (bf bs : List (Nat × Laze CSet))
    (hgate : ∀ e ∈ bf, ∀ X : Noun,
      nock (C lcMB (C (lzbE e) (C (HoonMap.toNoun lzbE (Lazy.index (Map := TreapMap mugF)
        (fun e : Nat × Laze CSet => e.1) bs))
        (C lcGate (C X (C comp.door (C G ctx))))))) lcMB = (lcBG bs e).map lzbE) :
    nock (C lcGate (C (C (C sf.toNoun (C (listN (ff.map lzfE)) (listN (bf.map lzbE))))
      (C ss.toNoun (C (listN (fs.map lzfE)) (listN (bs.map lzbE))))) (C comp.door (C G ctx)))) lcBX
      = (lcBP bf bs).map fun r => listN (r.map lzbE) := by
  have tF := lz_test lzbE bf
  have tS := lz_test lzbE bs
  unfold lcBX
  rcases tS with ⟨s1, s2, s3⟩ | ⟨s1, s2, s3⟩
  · subst s1
    simp [nock_exec, s2, s3, lcBP]
  rcases tF with ⟨f1, f2, f3⟩ | ⟨f1, f2, f3⟩
  · subst f1
    simp [nock_exec, s2, s3, f2, f3, lcBP, s1]
  have hT0 := lc_turn_pairsB (C (A 0) lneBunt)
    (C lcGate (C (C (C sf.toNoun (C (listN (ff.map lzfE)) (listN (bf.map lzbE))))
      (C ss.toNoun (C (listN (fs.map lzfE)) (listN (bs.map lzbE))))) (C comp.door (C G ctx)))) bs
  have hIdx := malt_gate _ _ (malt_index lzbE (fun e : Nat × Laze CSet => e.1) bs)
  unfold lneBunt at hT0
  simp only [lcBP, s1, f1, List.isEmpty_iff, if_false, lc_copyB]
  generalize hidx : Lazy.index (Map := TreapMap mugF) (fun e : Nat × Laze CSet => e.1) bs = idx at hIdx hgate
  have hM := turn_gate_mapT lzbE lzbE layer2 homoIn_layer2 lcMB (C (A 0) lneBunt)
    (C (HoonMap.toNoun lzbE idx) (C lcGate (C (C (C sf.toNoun (C (listN (ff.map lzfE)) (listN (bf.map lzbE))))
      (C ss.toNoun (C (listN (fs.map lzfE)) (listN (bs.map lzbE))))) (C comp.door (C G ctx)))))
    (lcBG bs) bf (fun e he => hgate e he _)
  unfold lneBunt at hM
  simp only [List.map_map] at hT0 hIdx
  have hm1 := malt_at
  have ht1 := turn.arm_at
  have hc' : slot? 262143 ctx = some layer2 := hc
  cases eS : bf.mapM (lcBG bs) with
  | none =>
    rw [eS] at hM
    generalize layer2 = L2 at hc' hm1 ht1 hT0 hIdx hM ⊢
    simp [nock_exec, s2, s3, f2, f3, hc', ht1, turn_arm, hT0, hm1, maltArm, hIdx, hM, eS]
  | some merged =>
    rw [eS] at hM
    have hTk := lc_turn_keysB (C (A 0) lneBunt)
      (C (listN (merged.map lzbE)) (C (HoonMap.toNoun lzbE idx) (C lcGate (C (C (C sf.toNoun
        (C (listN (ff.map lzfE)) (listN (bf.map lzbE))))
        (C ss.toNoun (C (listN (fs.map lzfE)) (listN (bs.map lzbE))))) (C comp.door (C G ctx)))))) bf
    unfold lneBunt at hTk
    simp only [List.map_map] at hTk
    obtain ⟨S0, hS0, hhas⟩ := seen_set (bf.map fun e => e.1)
    have hSilt := cm_silt_gate _ S0 hS0
    simp only [List.map_map] at hSilt
    have hSkip := skip_gate_map lzbE layer2 lcSB (C (A 0) lneBunt)
      (C S0 (C (listN (merged.map lzbE)) (C (HoonMap.toNoun lzbE idx) (C lcGate (C (C (C sf.toNoun
        (C (listN (ff.map lzfE)) (listN (bf.map lzbE))))
        (C ss.toNoun (C (listN (fs.map lzfE)) (listN (bs.map lzbE))))) (C comp.door (C G ctx)))))))
      (fun e => decide (e.1 ∈ bf.map fun e => e.1)) bs (fun e _ => by
        have := hhas e.1
        unfold lcSB
        simp [nock_exec, hc, in_arm, in.arm_at, in.has.arm_at, has_in_arm, this, lzbE])
    unfold lneBunt at hSkip
    have hW := weld_gate_list layer2 (merged.map lzbE)
      ((bs.filter fun a => !decide (a.1 ∈ bf.map fun e => e.1)).map lzbE)
    have hfil : (bs.filter fun e => !(bf.any fun x => x.1 == e.1))
        = bs.filter fun a => !decide (a.1 ∈ bf.map fun e => e.1) := by
      congr 1; funext a; rw [lc_any (fun x : Nat × Laze CSet => x.1)]
    rw [hfil]
    have hsl := silt.arm_at
    have hsk := skip.arm_at
    have hwl := weld.arm_at
    generalize layer2 = L2 at hc' hm1 ht1 hT0 hIdx hM hTk hSilt hSkip hW hsl hsk hwl ⊢
    simp [nock_exec, s2, s3, f2, f3, hc', ht1, turn_arm, hT0, hm1, maltArm, hIdx, hM, eS, hTk, hsl,
      cm_silt_arm, hSilt, hsk, lp_skip_arm, hSkip, hwl, weld_arm, hW]

end

/-! ## The whole gate -/

section
variable (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) (G : Noun)
include hc h7

mutual
/-- **`+laze-copy` is `lazeCopy`** on every pair of `laze`s (forks and bonds to any depth), on
every noun `G` of `gen`. -/
theorem lc_all : ∀ (f s : Laze CSet),
    nock (C lcGate (C (C f.toNoun s.toNoun) (C comp.door (C G ctx)))) lcGate
      = (lazeCopy f s).map Laze.toNoun
  | Laze.mk sf ff bf, Laze.mk ss fs bs => by
    have hS := lc_sure hc h7 G sf ss (C (listN (ff.map lzfE)) (listN (bf.map lzbE)))
      (C (listN (fs.map lzfE)) (listN (bs.map lzbE)))
    have hF := lc_fpart hc G sf ss ff fs bf bs (fun e he X => lc_forks ff e he fs X)
    have hB := lc_bpart hc G sf ss ff fs bf bs (fun e he X => lc_bonds bf e he bs X)
    rw [lz_toNoun_mk sf ff bf, lz_toNoun_mk ss fs bs, lc_gate_cons, hS, hF, hB, lazeCopy_eq]
    cases lcFP ff fs <;> cases lcBP bf bs <;> simp [lz_toNoun_mk]

theorem lc_forks : ∀ (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet))), ∀ e ∈ fk,
    ∀ (sec : List ((Nat × Laze CSet) × (Nat × Laze CSet))) (X : Noun),
    nock (C lcMF (C (lzfE e) (C (HoonMap.toNoun lzfE (Lazy.index (Map := TreapMap mugF)
      (fun e : (Nat × Laze CSet) × (Nat × Laze CSet) => e.1.1) sec))
      (C lcGate (C X (C comp.door (C G ctx))))))) lcMF = (lcFG sec e).map lzfE
  | [], e, he => absurd he List.not_mem_nil
  | ((oy, y), (on, n)) :: rest, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro sec X
      exact lc_fgate hc G sec _ X (fun m => lc_all y m) (fun m => lc_all n m)
    · exact lc_forks rest e he'

theorem lc_bonds : ∀ (bd : List (Nat × Laze CSet)), ∀ e ∈ bd,
    ∀ (sec : List (Nat × Laze CSet)) (X : Noun),
    nock (C lcMB (C (lzbE e) (C (HoonMap.toNoun lzbE (Lazy.index (Map := TreapMap mugF)
      (fun e : Nat × Laze CSet => e.1) sec))
      (C lcGate (C X (C comp.door (C G ctx))))))) lcMB = (lcBG sec e).map lzbE
  | [], e, he => absurd he List.not_mem_nil
  | (ob, l) :: rest, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro sec X
      exact lc_bgate hc G sec _ X (fun m => lc_all l m)
    · exact lc_bonds rest e he'
end

end

/-! ## `LzNZ` is kept -/

theorem lzNZF_iff : ∀ l : List ((Nat × Laze CSet) × (Nat × Laze CSet)),
    LzNZF l ↔ ∀ e ∈ l, LzNZ e.1.2 ∧ LzNZ e.2.2
  | [] => by simp [LzNZF]
  | ((oy, y), (on, n)) :: r => by simp [LzNZF, lzNZF_iff r, and_assoc]

theorem lzNZB_iff : ∀ l : List (Nat × Laze CSet), LzNZB l ↔ ∀ e ∈ l, LzNZ e.2
  | [] => by simp [LzNZB]
  | (o, x) :: r => by simp [LzNZB, lzNZB_iff r]

theorem lastF_mem {sec : List ((Nat × Laze CSet) × (Nat × Laze CSet))} {o : Nat} {v}
    (h : lastF sec o = some v) : v ∈ sec :=
  (List.mem_filter.1 (List.mem_of_getLast? h)).1

theorem lastB_mem {sec : List (Nat × Laze CSet)} {o : Nat} {v} (h : lastB sec o = some v) : v ∈ sec :=
  (List.mem_filter.1 (List.mem_of_getLast? h)).1

mutual
/-- **`+laze-copy` keeps `LzNZ`**: its looks are those of its two `laze`s. -/
theorem lazeCopy_nz : ∀ (f s r : Laze CSet), LzNZ f → LzNZ s → lazeCopy f s = some r → LzNZ r
  | Laze.mk sf ff bf, Laze.mk ss fs bs, r, ⟨h1, h2, h3⟩, ⟨k1, k2, k3⟩, e => by
    rw [lazeCopy_eq] at e
    obtain ⟨fk, eF, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨bd, eB, rfl⟩ := Option.map_eq_some_iff.1 e
    refine ⟨?_, ?_, ?_⟩
    · intro y hy
      rcases (HoonSet.mem_uni _ _ y).1 hy with h | h
      · exact h1 y h
      · exact k1 y h
    · unfold lcFP at eF
      split at eF
      · cases eF; exact h2
      split at eF
      · cases eF; exact k2
      obtain ⟨m, eM, rfl⟩ := Option.map_eq_some_iff.1 eF
      have hm := (lzNZF_iff m).1 (copyF_nz ff h2 fs k2 m eM)
      have hk := (lzNZF_iff fs).1 k2
      refine (lzNZF_iff _).2 fun x hx => ?_
      rcases List.mem_append.1 hx with hx | hx
      · exact hm x hx
      · exact hk x (List.mem_filter.1 hx).1
    · unfold lcBP at eB
      split at eB
      · cases eB; exact h3
      split at eB
      · cases eB; exact k3
      obtain ⟨m, eM, rfl⟩ := Option.map_eq_some_iff.1 eB
      have hm := (lzNZB_iff m).1 (copyB_nz bf h3 bs k3 m eM)
      have hk := (lzNZB_iff bs).1 k3
      refine (lzNZB_iff _).2 fun x hx => ?_
      rcases List.mem_append.1 hx with hx | hx
      · exact hm x hx
      · exact hk x (List.mem_filter.1 hx).1

theorem copyF_nz : ∀ (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet))), LzNZF fk →
    ∀ (sec : List ((Nat × Laze CSet) × (Nat × Laze CSet))), LzNZF sec → ∀ m, copyF fk sec = some m → LzNZF m
  | [], _, sec, _, m, e => by
    simp only [copyF, Option.some.injEq] at e; subst e; trivial
  | ((oy, y), (on, n)) :: rest, ⟨hy, hn, hr⟩, sec, hs, m, e => by
    simp only [copyF] at e
    cases el : lastF sec oy with
    | none =>
      rw [el] at e
      obtain ⟨r, er, rfl⟩ := Option.map_eq_some_iff.1 e
      exact ⟨hy, hn, copyF_nz rest hr sec hs r er⟩
    | some v =>
      obtain ⟨⟨oy', my⟩, ⟨mon, mn⟩⟩ := v
      rw [el] at e
      have hv := (lzNZF_iff sec).1 hs _ (lastF_mem el)
      simp only at e hv
      split at e
      · cases e
      obtain ⟨y', ey, e⟩ := Option.bind_eq_some_iff.1 e
      obtain ⟨n', en, e⟩ := Option.bind_eq_some_iff.1 e
      obtain ⟨r, er, rfl⟩ := Option.map_eq_some_iff.1 e
      exact ⟨lazeCopy_nz y my y' hy hv.1 ey, lazeCopy_nz n mn n' hn hv.2 en, copyF_nz rest hr sec hs r er⟩

theorem copyB_nz : ∀ (bd : List (Nat × Laze CSet)), LzNZB bd →
    ∀ (sec : List (Nat × Laze CSet)), LzNZB sec → ∀ m, copyB bd sec = some m → LzNZB m
  | [], _, sec, _, m, e => by
    simp only [copyB, Option.some.injEq] at e; subst e; trivial
  | (o, l) :: rest, ⟨hl, hr⟩, sec, hs, m, e => by
    simp only [copyB] at e
    cases el : lastB sec o with
    | none =>
      rw [el] at e
      obtain ⟨r, er, rfl⟩ := Option.map_eq_some_iff.1 e
      exact ⟨hl, copyB_nz rest hr sec hs r er⟩
    | some v =>
      obtain ⟨o', mm⟩ := v
      rw [el] at e
      have hv := (lzNZB_iff sec).1 hs _ (lastB_mem el)
      simp only at e hv
      obtain ⟨c, ec, e⟩ := Option.bind_eq_some_iff.1 e
      obtain ⟨r, er, rfl⟩ := Option.map_eq_some_iff.1 e
      exact ⟨lazeCopy_nz l mm c hl hv ec, copyB_nz rest hr sec hs r er⟩
end

end Compiler
end Formalization
