import lemmas.Compiler.CompSectN
import lemmas.Compiler.CompRunSixS
import lemmas.Compiler.DifMap
import lemmas.Compiler.ListMold
import lemmas.Hoon.JabBy
import lemmas.Hoon.RepBy
import lemmas.Compiler.CompStraightCore

/-!
# `+sect` against the model's `sect`

The Nock is cut by `tools/gen/sect.py` (`CompSectN.lean`).  The gate runs on
`[scBat [sample [comp.door [gen ctx]]]]`.

* `sc_g0`, `sc_g1`: the gates of the two `~(rep by made-i)`, on a pair
  `[k v]` of `made-i` and the whole core `dot` (`scDot`: `args`, `tars`,
  `inside-branch`, the other pushes and the door), are `sectStep`.
* `jab_gate_at`: `+jab:by` with a gate that need only work on the value at
  the key (`lens-hop` asserts `%hop`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun} (x : GenRest)

/-! ## The gates of the two `+rep:by` -/

/-- The noun of `args`: the arguments of the yes and no ends and the
parameters of the join. -/
def scArgsN (acc : SectAcc (TreapMap mugF)) : Noun :=
  C (listNoun (unitNoun A) acc.2.1) (C (listNoun (unitNoun A) acc.2.2.1) (listNoun A acc.2.2.2))

/-- The core `dot` of the `=>` of `+sect`: `args`, `tars`, the gate
`inside-branch`, seven pushes and nouns of the gate (`o-target`, `made-1`,
`made-0`, the two block labels, the battery and the sample), the door. -/
def scDot (c : Noun) (acc : SectAcc (TreapMap mugF)) (INS Y1 Y2 Y3 Y4 Y5 Y6 Y7 : Noun) (g : Gen (TreapMap mugF)) :
    Noun :=
  C (scArgsN acc) (C (HoonMap.toNoun A acc.1) (C INS (C Y1 (C Y2 (C Y3 (C Y4 (C Y5 (C Y6 (C Y7
    (compCore g x c))))))))))

theorem sectStep_some {rid : Nat} {yes : Bool} {made : TreapMap mugF (Nat × List Nat)} {k df : Nat}
    {tag : List Nat} (hk : HoonMap.get made k = some (df, tag)) (acc : SectAcc (TreapMap mugF))
    (g : Gen (TreapMap mugF)) :
    sectStep rid yes made acc k g =
      if tag.any (· == rid) then some (acc, g) else
      match HoonMap.get acc.1 df with
      | some t => some (acc, { g with cond := HoonMap.put g.cond k (t, tag) })
      | Option.none =>
        some (if yes
          then (HoonMap.put acc.1 df g.re, some df :: acc.2.1, Option.none :: acc.2.2.1, g.re :: acc.2.2.2)
          else (HoonMap.put acc.1 df g.re, Option.none :: acc.2.1, some df :: acc.2.2.1, g.re :: acc.2.2.2),
          { g with re := g.re + 1, cond := HoonMap.put g.cond k (g.re, tag) }) := by
  unfold sectStep
  rw [hk]
  rfl

theorem unitNoun_some' (y : Nat) : unitNoun A (some y) = C (A 0) (A y) := rfl
theorem unitNoun_none' : unitNoun A (Option.none : Option Nat) = A 0 := rfl

/-- **The gate of `~(rep by made-0)`** is `sectStep rid true made`. -/
theorem sc_g0 (hc : CompIn ctx) (rid : Nat) (IB IS IC Y1 Y2 Y3 Y4 Y5 Y6 Y7 bc : Noun)
    (hins : ∀ tag : List Nat, nock (C IB (C (listNoun A tag) IC)) IB = some (loob (tag.any (· == rid))))
    (made : TreapMap mugF (Nat × List Nat)) (k df : Nat) (tag : List Nat)
    (hk : HoonMap.get made k = some (df, tag)) (acc : SectAcc (TreapMap mugF)) (g : Gen (TreapMap mugF)) :
    nock (C scG0 (C (C (C (A k) (condValNoun (df, tag))) (scDot x ctx acc (C IB (C IS IC)) Y1 Y2 Y3 Y4 Y5 Y6 Y7 g))
      bc)) scG0
      = (sectStep rid true made acc k g).map fun s => scDot x ctx s.1 (C IB (C IS IC)) Y1 Y2 Y3 Y4 Y5 Y6 Y7 s.2 := by
  rw [sectStep_some hk]
  have hi := hins tag
  have hget := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ (A df)
    (HoonMap.toNoun A acc.1) _ (getF_hoonMap A acc.1 df)
  have hpt := put_gate layer2 gorIn_morIn_layer2 (A df) (A g.re) _ _ (putF_hoonMap A acc.1 df g.re)
  have hpc := fun (t : Nat) (g' : Gen (TreapMap mugF)) => put_gate layer2 gorIn_morIn_layer2 (A k)
    (condValNoun (t, tag)) _ _ (putF_hoonMap condValNoun g'.cond k (t, tag))
  have hD := comp_re_at
  have h1 := comp_re' (ctx := ctx) x g
  simp only [scDot, compCore] at h1 ⊢
  generalize comp.door = Dr at h1 hD ⊢
  simp only [genNoun] at h1
  simp only [condValNoun] at hpc
  unfold scG0 scG0Y scGS
  cases ha : tag.any (· == rid)
  · rw [ha] at hi
    cases hg : HoonMap.get acc.1 df with
    | none =>
      simp [nock_exec, hi, hc, by_arm, by.arm_at, by.get.arm_at, get_arm, hget, hg, by.put.arm_at, put_arm,
        hpt, hpc, hD, h1, scArgsN, listNoun, unitNoun, genNoun, condValNoun]
    | some t =>
      simp [nock_exec, hi, hc, by_arm, by.arm_at, by.get.arm_at, get_arm, hget, hg, by.put.arm_at, put_arm,
        hpt, hpc, hD, h1, scArgsN, listNoun, unitNoun, genNoun, condValNoun]
  · rw [ha] at hi
    simp [nock_exec, hi, scArgsN, listNoun]

/-- **The gate of `~(rep by made-1)`** is `sectStep rid false made`. -/
theorem sc_g1 (hc : CompIn ctx) (rid : Nat) (IB IS IC Y1 Y2 Y3 Y4 Y5 Y6 Y7 bc : Noun)
    (hins : ∀ tag : List Nat, nock (C IB (C (listNoun A tag) IC)) IB = some (loob (tag.any (· == rid))))
    (made : TreapMap mugF (Nat × List Nat)) (k df : Nat) (tag : List Nat)
    (hk : HoonMap.get made k = some (df, tag)) (acc : SectAcc (TreapMap mugF)) (g : Gen (TreapMap mugF)) :
    nock (C scG1 (C (C (C (A k) (condValNoun (df, tag))) (scDot x ctx acc (C IB (C IS IC)) Y1 Y2 Y3 Y4 Y5 Y6 Y7 g))
      bc)) scG1
      = (sectStep rid false made acc k g).map fun s => scDot x ctx s.1 (C IB (C IS IC)) Y1 Y2 Y3 Y4 Y5 Y6 Y7 s.2 := by
  rw [sectStep_some hk]
  have hi := hins tag
  have hget := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ (A df)
    (HoonMap.toNoun A acc.1) _ (getF_hoonMap A acc.1 df)
  have hpt := put_gate layer2 gorIn_morIn_layer2 (A df) (A g.re) _ _ (putF_hoonMap A acc.1 df g.re)
  have hpc := fun (t : Nat) (g' : Gen (TreapMap mugF)) => put_gate layer2 gorIn_morIn_layer2 (A k)
    (condValNoun (t, tag)) _ _ (putF_hoonMap condValNoun g'.cond k (t, tag))
  have hD := comp_re_at
  have h1 := comp_re' (ctx := ctx) x g
  simp only [scDot, compCore] at h1 ⊢
  generalize comp.door = Dr at h1 hD ⊢
  simp only [genNoun] at h1
  simp only [condValNoun] at hpc
  unfold scG1 scG1Y scGS
  cases ha : tag.any (· == rid)
  · rw [ha] at hi
    cases hg : HoonMap.get acc.1 df with
    | none =>
      simp [nock_exec, hi, hc, by_arm, by.arm_at, by.get.arm_at, get_arm, hget, hg, by.put.arm_at, put_arm,
        hpt, hpc, hD, h1, scArgsN, listNoun, unitNoun, genNoun, condValNoun]
    | some t =>
      simp [nock_exec, hi, hc, by_arm, by.arm_at, by.get.arm_at, get_arm, hget, hg, by.put.arm_at, put_arm,
        hpt, hpc, hD, h1, scArgsN, listNoun, unitNoun, genNoun, condValNoun]
  · rw [ha] at hi
    simp [nock_exec, hi, scArgsN, listNoun]


/-! ## The folds -/

theorem ctx_layer1 (hc : CompIn ctx) : slot? 524287 ctx = some layer1 := by
  have h := slot_bit 262143 (by decide) 1 (by decide) ctx
  rw [hc] at h
  rw [show (524287 : Nat) = 2 * 262143 + 1 from rfl, h]
  exact (slot_three layer2).symm.trans layer2_layer1

/-- The mold `(list item)` on its default sample `0` is `~`, whatever its context. -/
theorem mold_nil (c : Noun) : nock (C moldBat (C (A 0) c)) moldBat = some (A 0) := by
  nock_open moldBat; simp [nock_exec]

/-- The bunt `(list @uxid)` of the sample of the gates. -/
theorem sc_lb (hc : CompIn ctx) (acc : SectAcc (TreapMap mugF)) (INS Y1 Y2 Y3 Y4 Y5 Y6 Y7 : Noun)
    (g : Gen (TreapMap mugF)) : nock (scDot x ctx acc INS Y1 Y2 Y3 Y4 Y5 Y6 Y7 g) scLB = some (A 0) := by
  have h1 := ctx_layer1 hc
  simp only [scDot, compCore]
  generalize comp.door = Dr
  unfold scLB
  simp [nock_exec, h1, layer1_list, list_arm_run, builder_run, mold_nil]

/-- `foldlM` in `CM` over the keys of a list of pairs is `foldlM` in `Option`
over the pairs, with the state in the accumulator. -/
theorem foldlM_cm {σ ν : Type} (f : σ → Nat → CM (TreapMap mugF) σ) :
    ∀ (L : List (Nat × ν)) (s : σ) (g : Gen (TreapMap mugF)),
    ((L.map Prod.fst).foldlM f s : CM (TreapMap mugF) σ) g
      = L.foldlM (fun sg p => f sg.1 p.1 sg.2) (s, g)
  | [], s, g => rfl
  | p :: L, s, g => by
    simp only [List.map_cons, List.foldlM_cons, bind_apply]
    cases e : f s p.1 g with
    | none => rfl
    | some r => exact foldlM_cm f L r.1 r.2

/-- **The `=>` of `~(rep by made-0)`**: the fold of `sectStep rid true made`
over the pairs of `made` in the order of `+rep:by`. -/
theorem sc_rep0 (hc : CompIn ctx) (rid : Nat) (IB IS IC Y1 Y2 Y4 Y5 Y6 Y7 : Noun)
    (hins : ∀ tag : List Nat, nock (C IB (C (listNoun A tag) IC)) IB = some (loob (tag.any (· == rid))))
    (made : TreapMap mugF (Nat × List Nat)) (acc : SectAcc (TreapMap mugF)) (g : Gen (TreapMap mugF)) :
    nock (scDot x ctx acc (C IB (C IS IC)) Y1 Y2 (HoonMap.toNoun condValNoun made) Y4 Y5 Y6 Y7 g) scRep0
      = (((HoonMapKeys.keys made).foldlM (sectStep rid true made) acc : CM (TreapMap mugF) _) g).map
          fun s => scDot x ctx s.1 (C IB (C IS IC)) Y1 Y2 (HoonMap.toNoun condValNoun made) Y4 Y5 Y6 Y7 s.2 := by
  rw [treapMap_keys, foldlM_cm]
  have ha : Tree (HoonMap.toNoun condValNoun made) := by
    rw [hoonMap_toNoun]; exact Tree.of_isMap (made.2 condValNoun)
  have hL : preorder (HoonMap.toNoun condValNoun made) = (TreapMap.rap made).map (Tr.pairNoun condValNoun) :=
    TreapMap.preorder_toNoun condValNoun made
  have hlb := sc_lb x hc acc (C IB (C IS IC)) Y1 Y2 (HoonMap.toNoun condValNoun made) Y4 Y5 Y6 Y7 g
  have hrep := rep_gate_list (Tr.pairNoun condValNoun)
    (fun s : SectAcc (TreapMap mugF) × Gen (TreapMap mugF) =>
      scDot x ctx s.1 (C IB (C IS IC)) Y1 Y2 (HoonMap.toNoun condValNoun made) Y4 Y5 Y6 Y7 s.2)
    (fun p s => sectStep rid true made s.1 p.1 s.2) by.battery layer2 scG0 (C (A 0) (C (A 0) (A 0)))
    (scDot x ctx acc (C IB (C IS IC)) Y1 Y2 (HoonMap.toNoun condValNoun made) Y4 Y5 Y6 Y7 g)
    _ ha _ hL (acc, g) (fun p hp s => by
      obtain ⟨k, df, tag⟩ := p
      have hk : HoonMap.get made k = some (df, tag) := by
        rw [hoonMap_get]; exact (TreapMap.mem_rap made k (df, tag)).1 hp
      exact sc_g0 x hc rid IB IS IC Y1 Y2 (HoonMap.toNoun condValNoun made) Y4 Y5 Y6 Y7 _ hins made k df tag hk
        s.1 s.2)
  simp only [scDot, compCore] at hlb hrep ⊢
  generalize comp.door = Dr at hlb hrep ⊢
  unfold scRep0
  simp [nock_exec, hc, by_arm, by.arm_at, by.rep.arm_at, rep_arm, hlb, hrep]

/-- **The `=>` of `~(rep by made-1)`**: the fold of `sectStep rid false made`
over the pairs of `made` in the order of `+rep:by`. -/
theorem sc_rep1 (hc : CompIn ctx) (rid : Nat) (IB IS IC Y1 Y3 Y4 Y5 Y6 Y7 : Noun)
    (hins : ∀ tag : List Nat, nock (C IB (C (listNoun A tag) IC)) IB = some (loob (tag.any (· == rid))))
    (made : TreapMap mugF (Nat × List Nat)) (acc : SectAcc (TreapMap mugF)) (g : Gen (TreapMap mugF)) :
    nock (scDot x ctx acc (C IB (C IS IC)) Y1 (HoonMap.toNoun condValNoun made) Y3 Y4 Y5 Y6 Y7 g) scRep1
      = (((HoonMapKeys.keys made).foldlM (sectStep rid false made) acc : CM (TreapMap mugF) _) g).map
          fun s => scDot x ctx s.1 (C IB (C IS IC)) Y1 (HoonMap.toNoun condValNoun made) Y3 Y4 Y5 Y6 Y7 s.2 := by
  rw [treapMap_keys, foldlM_cm]
  have ha : Tree (HoonMap.toNoun condValNoun made) := by
    rw [hoonMap_toNoun]; exact Tree.of_isMap (made.2 condValNoun)
  have hL : preorder (HoonMap.toNoun condValNoun made) = (TreapMap.rap made).map (Tr.pairNoun condValNoun) :=
    TreapMap.preorder_toNoun condValNoun made
  have hlb := sc_lb x hc acc (C IB (C IS IC)) Y1 (HoonMap.toNoun condValNoun made) Y3 Y4 Y5 Y6 Y7 g
  have hrep := rep_gate_list (Tr.pairNoun condValNoun)
    (fun s : SectAcc (TreapMap mugF) × Gen (TreapMap mugF) =>
      scDot x ctx s.1 (C IB (C IS IC)) Y1 (HoonMap.toNoun condValNoun made) Y3 Y4 Y5 Y6 Y7 s.2)
    (fun p s => sectStep rid false made s.1 p.1 s.2) by.battery layer2 scG1 (C (A 0) (C (A 0) (A 0)))
    (scDot x ctx acc (C IB (C IS IC)) Y1 (HoonMap.toNoun condValNoun made) Y3 Y4 Y5 Y6 Y7 g)
    _ ha _ hL (acc, g) (fun p hp s => by
      obtain ⟨k, df, tag⟩ := p
      have hk : HoonMap.get made k = some (df, tag) := by
        rw [hoonMap_get]; exact (TreapMap.mem_rap made k (df, tag)).1 hp
      exact sc_g1 x hc rid IB IS IC Y1 (HoonMap.toNoun condValNoun made) Y3 Y4 Y5 Y6 Y7 _ hins made k df tag hk
        s.1 s.2)
  simp only [scDot, compCore] at hlb hrep ⊢
  generalize comp.door = Dr at hlb hrep ⊢
  unfold scRep1
  simp [nock_exec, hc, by_arm, by.arm_at, by.rep.arm_at, rep_arm, hlb, hrep]

end Compiler
end Formalization
