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

/-! ## `+jab:by` on the blocks -/

/-- `+jab:by` with a gate that need only work on the value `v` at the key. -/
theorem jab_gate_at {mug : Noun → Nat} (c : Noun) (hc : GorIn mug c) (B key fp fs fc : Noun)
    (g : Noun → Noun) (v : Noun) (hg : nock (C fp (C v fc)) fp = some (g v)) :
    ∀ (a out : Noun), getF mug key a = some (C (A 0) v) → jabF mug key g a = some out →
      nock (C by.jab.battery (C (C key (C fp (C fs fc))) (C B (C a c)))) by.jab.battery = some out := by
  intro a
  have hgor := gor_gate (mug := mug) c hc.2
  have hgo := hc.1
  fun_induction jabF mug key g a
  all_goals intro out hv h
  all_goals first
    | (simp at h; done)
    | skip
  all_goals simp [getF, *] at hv
  all_goals first
    | (cases h
       subst hv
       nock_open by.jab.battery
       simp [nock_exec, *]
       done)
    | (nock_open by.jab.battery
       simp_all [nock_exec])

/-- **`+jab:by` on the blocks**: at a block `b` that the gate maps to `b'`,
the noun of the blocks with `b'` put at the key. -/
theorem jab_blocks (fp fs fc : Noun) (bs : TreapMap mugF Blob) (o : Nat) (b b' : Blob)
    (hb : HoonMap.get bs o = some b) (hg : nock (C fp (C b.toNoun fc)) fp = some b'.toNoun) :
    nock (C by.jab.battery (C (C (A o) (C fp (C fs fc))) (C by.battery (C (HoonMap.toNoun Blob.toNoun bs)
      layer2)))) by.jab.battery = some (HoonMap.toNoun Blob.toNoun (HoonMap.put bs o b')) := by
  have hm := isMap_hoonMap Blob.toNoun bs
  have hv : Get (HoonMap.toNoun Blob.toNoun bs) (A o) b.toNoun := by
    rw [hoonMap_toNoun] at hm ⊢
    exact (Tr.Get_toNoun_iff Blob.toNoun _ hm _ _).2 ⟨o, b, rfl, hb, rfl⟩
  obtain ⟨out, hj, hmo, hget⟩ := jabF_spec (A o) (fun _ => b'.toNoun) hm hv
  obtain ⟨out', hp, hmp, hgp⟩ := putF_spec mugF (HoonMap.toNoun Blob.toNoun bs) (A o) b'.toNoun hm
  rw [jab_gate_at layer2 gorIn_morIn_layer2.1 by.battery (A o) fp fs fc (fun _ => b'.toNoun) b.toNoun hg _ out
    (getF_some hm hv) hj]
  rw [putF_hoonMap] at hp
  cases hp
  congr 1
  exact isMap_ext hmo hmp (fun k w => by rw [hget, hgp])

/-- The block after `|=(blob +<(par tar.args))`. -/
theorem sc_parg (b : Blob) (par : List Nat) (D : Noun) (yes nuh : Noun) (Z : Noun) :
    nock (C scParG (C b.toNoun (C (C yes (C nuh (listNoun A par))) Z))) scParG
      = some ({ b with par := par } : Blob).toNoun := by
  unfold scParG; simp [nock_exec, Blob.toNoun]

/-- The gate that `lens-hop` builds, on a block whose end is `%hop`. -/
theorem sc_inner (b : Blob) (t : Jmp) (hb : b.fin = Termin.hop t) (args : List (Option Nat)) (D : Noun) :
    nock (C scInner (C b.toNoun (C scLensB (C (listNoun (unitNoun A) args) D)))) scInner
      = (lensHop args b).map Blob.toNoun := by
  obtain ⟨par, body, fin⟩ := b
  simp only at hb
  subst hb
  unfold scInner
  simp [nock_exec, Blob.toNoun, Termin.toNoun, Tag.hop, lensHop, Jmp.toNoun]

theorem sc_lensB (a D : Noun) : nock (C scLensB (C a D)) scLensB
    = some (C scInner (C (C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0)))) (C scLensB (C a D)))) := by
  conv => lhs; arg 2; unfold scLensB
  simp [nock_exec]

theorem get_put_hop {bs : TreapMap mugF Blob} {o tgt : Nat} {b v : Blob} {t : Jmp}
    (h : HoonMap.get bs o = some b) (hf : b.fin = Termin.hop t) (hv : o = tgt → ∃ t', v.fin = Termin.hop t') :
    ∃ c t2, HoonMap.get (HoonMap.put bs tgt v) o = some c ∧ c.fin = Termin.hop t2 := by
  rw [hoonMap_get] at h ⊢
  show ∃ c t2, TreapMap.get (TreapMap.put bs tgt v) o = some c ∧ _
  rw [TreapMap.get_put]
  by_cases e : o = tgt
  · obtain ⟨t', ht'⟩ := hv e
    exact ⟨v, t', if_pos e, ht'⟩
  · exact ⟨b, t, by rw [if_neg e]; exact h, hf⟩

/-- The arm `jab` of the door on a map that holds a key: its gate, whose
sample the call replaces. -/
theorem jab_arm_map (B c : Noun) (bs : TreapMap mugF Blob) (o : Nat) (b : Blob)
    (h : HoonMap.get bs o = some b) :
    ∃ S, nock (C B (C (HoonMap.toNoun Blob.toNoun bs) c)) by.jab.arm
      = some (C by.jab.battery (C S (C B (C (HoonMap.toNoun Blob.toNoun bs) c)))) := by
  rw [hoonMap_get] at h
  rw [hoonMap_toNoun]
  obtain ⟨t, ht⟩ := bs
  cases t with
  | nil => simp [TreapMap.get, Tr.get] at h
  | node k v l r =>
    simp only [TreapMap.toNoun, Tr.toNoun]
    exact ⟨C (A k) (C (C (A 0) (A 15)) (C (Blob.toNoun v) (C (Blob.toNoun v) (Blob.toNoun v)))), by
      nock_open by.jab.arm; simp [nock_exec]⟩

/-- **The three `+jab:by` of `+sect`**: the parameters of the join, then the
arguments of the two ends, then `gen`. -/
theorem sc_jabs (hc : CompIn ctx) (acc : SectAcc (TreapMap mugF)) (INS Y2 Y3 Y4 Y5 Y6 N0 N1 R : Noun) (tgt o0 o1 : Nat)
    (g : Gen (TreapMap mugF)) (bt b0 b1 : Blob) (t0 t1 : Jmp)
    (hbt : HoonMap.get g.blocks tgt = some bt) (h0 : HoonMap.get g.blocks o0 = some b0)
    (hf0 : b0.fin = Termin.hop t0) (h1 : HoonMap.get g.blocks o1 = some b1) (hf1 : b1.fin = Termin.hop t1) :
    nock (scDot x ctx acc INS (A tgt) Y2 Y3 Y4 Y5 Y6 (C N0 (C N1 (C (A o0) (C (A o1) R)))) g) scJabs
      = ((do
          jabBlock tgt (fun b => some { b with par := acc.2.2.2 })
          jabBlock o0 (lensHop acc.2.1)
          jabBlock o1 (lensHop acc.2.2.1) : CM (TreapMap mugF) Unit) g).map fun p => genNoun p.2 x := by
  -- the first jab: the parameters of the join
  have hv0 : o0 = tgt → ∃ t', ({ bt with par := acc.2.2.2 } : Blob).fin = Termin.hop t' := fun e => by
    subst e; rw [hbt] at h0; cases h0; exact ⟨t0, hf0⟩
  obtain ⟨c0, u0, hc0, hfc0⟩ := get_put_hop (tgt := tgt) (v := { bt with par := acc.2.2.2 }) h0 hf0 hv0
  have hv1 : o1 = tgt → ∃ t', ({ bt with par := acc.2.2.2 } : Blob).fin = Termin.hop t' := fun e => by
    subst e; rw [hbt] at h1; cases h1; exact ⟨t1, hf1⟩
  obtain ⟨d1, w1, hd1, hfd1⟩ := get_put_hop (tgt := tgt) (v := { bt with par := acc.2.2.2 }) h1 hf1 hv1
  -- the second: the arguments of the yes end
  have hv2 : o1 = o0 → ∃ t', ({ c0 with fin := Termin.hop { u0 with args := acc.2.1 } } : Blob).fin
      = Termin.hop t' := fun _ => ⟨_, rfl⟩
  obtain ⟨c1, u1, hc1, hfc1⟩ := get_put_hop (tgt := o0) hd1 hfd1 hv2
  have hl0 : lensHop acc.2.1 c0 = some { c0 with fin := Termin.hop { u0 with args := acc.2.1 } } := by
    simp [lensHop, hfc0]
  have hl1 : lensHop acc.2.2.1 c1 = some { c1 with fin := Termin.hop { u1 with args := acc.2.2.1 } } := by
    simp [lensHop, hfc1]
  have hm : ((do
          jabBlock tgt (fun b => some { b with par := acc.2.2.2 })
          jabBlock o0 (lensHop acc.2.1)
          jabBlock o1 (lensHop acc.2.2.1) : CM (TreapMap mugF) Unit) g)
      = some ((), { g with blocks := (HoonMap.put (HoonMap.put (HoonMap.put g.blocks tgt { bt with par := acc.2.2.2 })
          o0 { c0 with fin := Termin.hop { u0 with args := acc.2.1 } })
          o1 { c1 with fin := Termin.hop { u1 with args := acc.2.2.1 } }) }) := by
    simp only [bind_apply, jabBlock, hbt, Option.bind_some, Option.map_some]
    simp only [hc0, Option.bind_some, hl0, Option.map_some, hc1, hl1]
  rw [hm, Option.map_some]
  have hj0 := jab_blocks scParG (C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0))))
    (scDot x ctx acc INS (A tgt) Y2 Y3 Y4 Y5 Y6 (C N0 (C N1 (C (A o0) (C (A o1) R)))) g) g.blocks tgt bt
    { bt with par := acc.2.2.2 } hbt (by simp only [scDot, scArgsN]; exact sc_parg _ _ (A 0) _ _ _)
  have hj1 := fun D => jab_blocks scInner (C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0))))
    (C scLensB (C (listNoun (unitNoun A) acc.2.1) D)) _ o0 c0 _ hc0
    (by rw [sc_inner c0 u0 hfc0, hl0]; rfl)
  have hj2 := fun D => jab_blocks scInner (C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0))))
    (C scLensB (C (listNoun (unitNoun A) acc.2.2.1) D)) _ o1 c1 _ hc1
    (by rw [sc_inner c1 u1 hfc1, hl1]; rfl)
  obtain ⟨S0, hS0⟩ := jab_arm_map by.battery layer2 g.blocks tgt bt hbt
  obtain ⟨S1, hS1⟩ := jab_arm_map by.battery layer2 _ o0 c0 hc0
  obtain ⟨S2, hS2⟩ := jab_arm_map by.battery layer2 _ o1 c1 hc1
  simp only [scDot, scArgsN, compCore, genNoun] at hj0 hj1 hj2 ⊢
  generalize comp.door = Dr at hj0 hj1 hj2 ⊢
  unfold scJabs
  simp [nock_exec, hc, by_arm, by.arm_at, by.jab.arm_at, hS0, hS1, hS2, hj0, hj1, hj2, sc_lensB]

end Compiler
end Formalization
