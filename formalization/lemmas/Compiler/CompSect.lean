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

/-! ## The pushes of the threading -/

theorem dif_arm (B a c : Noun) :
    nock (C B (C a c)) by.dif.arm = some (C by.dif.battery (C a (C B (C a c)))) := by
  nock_open by.dif.arm; simp only [nock_exec]

/-- The subject of the threading: the two block labels, the battery, the
sample (with `region-branch` `rid :: rest`, `cond-before`, `cond-between`)
and the door. -/
def scT (o1b o0b : Nat) (Y6 N0 N1 : Noun) (o0 o1 rid : Nat) (rest : List Nat)
    (cb cbw : TreapMap mugF (Nat × List Nat)) (g : Gen (TreapMap mugF)) : Noun :=
  C (A o1b) (C (A o0b) (C Y6 (C (C N0 (C N1 (C (A o0) (C (A o1) (C (listNoun A (rid :: rest))
    (C (HoonMap.toNoun condValNoun cb) (HoonMap.toNoun condValNoun cbw))))))) (compCore g x ctx))))

/-- `inside-branch`: whether a tag holds the region's identifier. -/
theorem sc_ins (hc : CompIn ctx) (o1b o0b : Nat) (Y6 N0 N1 : Noun) (o0 o1 rid : Nat) (rest : List Nat)
    (cb cbw : TreapMap mugF (Nat × List Nat)) (g : Gen (TreapMap mugF)) (Z1 Z2 Z3 : Noun) (tag : List Nat) :
    nock (C scIns (C (listNoun A tag) (C Z1 (C Z2 (C Z3 (scT (ctx := ctx) x o1b o0b Y6 N0 N1 o0 o1 rid rest cb cbw g))))))
      scIns = some (loob (tag.any (· == rid))) := by
  have hl := lien_gate layer2 (C (A 5) (C (C (A 0) (A 6)) (C (A 0) (A 0x3ffbc)))) (A 0)
    (C scIns (C (listNoun A tag) (C Z1 (C Z2 (C Z3 (scT (ctx := ctx) x o1b o0b Y6 N0 N1 o0 o1 rid rest cb cbw g))))))
    (fun n => decide (n = A rid)) (tag.map A) (fun y _ => by
      simp only [scT, compCore]
      generalize comp.door = Dr
      simp [nock_exec, eqCode_atom, loob]
      by_cases e : y = A rid <;> simp [e, eqCode, loob])
  rw [← cd_listNoun_listN] at hl
  have he : (tag.map A).any (fun n => decide (n = A rid)) = tag.any (· == rid) := by
    simp only [List.any_map, Function.comp_def]
    congr 1; funext y; by_cases e : y = rid <;> simp [e]
  rw [he] at hl
  simp only [scT, compCore] at hl ⊢
  generalize comp.door = Dr at hl ⊢
  conv => lhs; arg 2; unfold scIns
  simp [nock_exec, hc, lien.arm_at, lien_arm, hl]

theorem sectStep_blocks {rid : Nat} {yes : Bool} {made : TreapMap mugF (Nat × List Nat)}
    {acc acc' : SectAcc (TreapMap mugF)} {k : Nat} {g g' : Gen (TreapMap mugF)}
    (h : sectStep rid yes made acc k g = some (acc', g')) : g'.blocks = g.blocks := by
  unfold sectStep at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · split at h
      · cases h; rfl
      · cases h; rfl

theorem foldlM_sectStep_blocks {rid : Nat} {yes : Bool} {made : TreapMap mugF (Nat × List Nat)} :
    ∀ (ks : List Nat) (acc acc' : SectAcc (TreapMap mugF)) (g g' : Gen (TreapMap mugF)),
    (ks.foldlM (sectStep rid yes made) acc : CM (TreapMap mugF) _) g = some (acc', g') → g'.blocks = g.blocks
  | [], acc, acc', g, g', h => by cases h; rfl
  | k :: ks, acc, acc', g, g', h => by
    rw [List.foldlM_cons, bind_apply] at h
    cases e : sectStep rid yes made acc k g with
    | none => rw [e] at h; cases h
    | some r =>
      rw [e, Option.bind_some] at h
      rw [foldlM_sectStep_blocks ks r.1 acc' r.2 g' h, sectStep_blocks e]

/-- **The threading of `+sect`** (`scND`, when not dropping) is `sectThread`. -/
theorem sc_nd (hc : CompIn ctx) (o1b o0b : Nat) (Y6 N0 N1 : Noun) (o0 o1 rid : Nat) (rest : List Nat)
    (cb cbw : TreapMap mugF (Nat × List Nat)) (g : Gen (TreapMap mugF)) :
    nock (scT (ctx := ctx) x o1b o0b Y6 N0 N1 o0 o1 rid rest cb cbw g) scND
      = (sectThread rid o0 o1 cb cbw g).map fun p => genNoun p.2 x := by
  have hgc : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
    ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
  have hd0 := dif_by_hoonMap layer2 gorIn_morIn_layer2 condValNoun g.cond cbw
  have hd1 := dif_by_hoonMap layer2 gorIn_morIn_layer2 condValNoun cbw cb
  have gotN : ∀ o, HoonMap.get g.blocks o = Option.none →
      nock (C by.got.battery (C (A o) (C by.battery (C (HoonMap.toNoun Blob.toNoun g.blocks) layer2))))
        by.got.battery = Option.none := fun o e =>
    got_gate_nil layer2 hgc _ _ (by rw [getF_hoonMap, e]; rfl)
  have gotS : ∀ o b, HoonMap.get g.blocks o = some b →
      nock (C by.got.battery (C (A o) (C by.battery (C (HoonMap.toNoun Blob.toNoun g.blocks) layer2))))
        by.got.battery = some b.toNoun := fun o b e =>
    got_gate layer2 hgc _ _ _ (by rw [getF_hoonMap, e]; rfl)
  unfold sectThread
  cases e0 : HoonMap.get g.blocks o0 with
  | none =>
    have h := gotN o0 e0
    simp only [scT, compCore, genNoun] at h ⊢
    generalize comp.door = Dr
    unfold scND scOt
    simp [nock_exec, hc, by_arm, by.arm_at, by.dif.arm_at, dif_arm, hd0, hd1, by.got.arm_at, got_arm, h]
  | some b0 =>
  have g0 := gotS o0 b0 e0
  cases e1 : HoonMap.get g.blocks o1 with
  | none =>
    have h := gotN o1 e1
    simp only [scT, compCore, genNoun] at h g0 ⊢
    generalize comp.door = Dr
    unfold scND scOt
    simp [nock_exec, hc, by_arm, by.arm_at, by.dif.arm_at, dif_arm, hd0, hd1, by.got.arm_at, got_arm, h, g0]
  | some b1 =>
  have g1 := gotS o1 b1 e1
  obtain ⟨p0, bd0, f0⟩ := b0
  obtain ⟨p1, bd1, f1⟩ := b1
  cases f0
  case hop t0 =>
    cases f1
    case hop t1 =>
      obtain ⟨a0, th0⟩ := t0
      obtain ⟨a1, th1⟩ := t1
      by_cases ht : th0 = th1
      · subst ht
        cases et : HoonMap.get g.blocks th0 with
        | none =>
          have h := gotN th0 et
          simp only [scT, compCore, genNoun] at g0 g1 h ⊢
          generalize comp.door = Dr
          unfold scND scOt scArgs
          simp [nock_exec, hc, by_arm, by.arm_at, by.dif.arm_at, dif_arm, hd0, hd1, by.got.arm_at, got_arm, g0, g1,
            h, Blob.toNoun, Termin.toNoun, Jmp.toNoun, Tag.hop, et]
        | some bt =>
        have gt := gotS th0 bt et
        have hins := fun tag => sc_ins x hc o1b o0b Y6 N0 N1 o0 o1 rid rest cb cbw g (A th0)
          (HoonMap.toNoun condValNoun (difM cbw cb)) (HoonMap.toNoun condValNoun (difM g.cond cbw)) tag
        have hemp : HoonMap.toNoun A (HoonMap.empty : TreapMap mugF Nat) = A 0 := rfl
        have hrep0 := sc_rep0 x hc rid scIns (A 0) _ (A th0) (HoonMap.toNoun condValNoun (difM cbw cb)) (A o1b)
          (A o0b) Y6 (C N0 (C N1 (C (A o0) (C (A o1) (C (listNoun A (rid :: rest)) (C (HoonMap.toNoun condValNoun cb) (HoonMap.toNoun condValNoun cbw))))))) hins (difM g.cond cbw) ((HoonMap.empty, a0, a1, bt.par) : SectAcc (TreapMap mugF)) g
        cases e2 : ((HoonMapKeys.keys (difM g.cond cbw)).foldlM (sectStep rid true (difM g.cond cbw))
            ((HoonMap.empty, a0, a1, bt.par) : SectAcc (TreapMap mugF)) : CM (TreapMap mugF) _) g with
        | none =>
          rw [e2] at hrep0
          simp only [scDot, scArgsN, scT, compCore, genNoun, Option.map_none, hemp] at g0 g1 gt hrep0 ⊢
          generalize comp.door = Dr at hrep0 ⊢
          unfold scND scOt scArgs
          simp [nock_exec, hc, by_arm, by.arm_at, by.dif.arm_at, dif_arm, hd0, hd1, by.got.arm_at, got_arm, g0, g1,
            gt, Blob.toNoun, Termin.toNoun, Jmp.toNoun, Tag.hop, et, bind_apply, e2, hrep0]
        | some r1 =>
        obtain ⟨acc1, g1'⟩ := r1
        have hb1 := foldlM_sectStep_blocks _ _ _ _ _ e2
        rw [e2] at hrep0
        have hrep1 := sc_rep1 x hc rid scIns (A 0) _ (A th0) (HoonMap.toNoun condValNoun (difM g.cond cbw)) (A o1b)
          (A o0b) Y6 (C N0 (C N1 (C (A o0) (C (A o1) (C (listNoun A (rid :: rest)) (C (HoonMap.toNoun condValNoun cb) (HoonMap.toNoun condValNoun cbw))))))) hins (difM cbw cb) acc1 g1'
        cases e3 : ((HoonMapKeys.keys (difM cbw cb)).foldlM (sectStep rid false (difM cbw cb)) acc1
            : CM (TreapMap mugF) _) g1' with
        | none =>
          rw [e3] at hrep1
          simp only [scDot, scArgsN, scT, compCore, genNoun, Option.map_none, Option.map_some, hemp] at g0 g1 gt hrep0 hrep1 ⊢
          generalize comp.door = Dr at hrep0 hrep1 ⊢
          unfold scND scOt scArgs
          simp [nock_exec, hc, by_arm, by.arm_at, by.dif.arm_at, dif_arm, hd0, hd1, by.got.arm_at, got_arm, g0, g1,
            gt, Blob.toNoun, Termin.toNoun, Jmp.toNoun, Tag.hop, et, bind_apply, e2, e3, hrep0, hrep1]
        | some r2 =>
        obtain ⟨acc2, g2⟩ := r2
        have hb2 := foldlM_sectStep_blocks _ _ _ _ _ e3
        rw [e3] at hrep1
        have hbl : g2.blocks = g.blocks := hb2.trans hb1
        have hj := sc_jabs x hc acc2 (C scIns (C (A 0) (C (A th0) (C (HoonMap.toNoun condValNoun (difM cbw cb))
          (C (HoonMap.toNoun condValNoun (difM g.cond cbw))
            (scT (ctx := ctx) x o1b o0b Y6 N0 N1 o0 o1 rid rest cb cbw g))))))
          (HoonMap.toNoun condValNoun (difM cbw cb)) (HoonMap.toNoun condValNoun (difM g.cond cbw)) (A o1b) (A o0b) Y6
          N0 N1 (C (listNoun A (rid :: rest)) (C (HoonMap.toNoun condValNoun cb) (HoonMap.toNoun condValNoun cbw)))
          th0 o0 o1 g2 bt _ _ ⟨a0, th0⟩ ⟨a1, th0⟩ (by rw [hbl]; exact et) (by rw [hbl]; exact e0) rfl
          (by rw [hbl]; exact e1) rfl
        simp only [scDot, scArgsN, scT, compCore, genNoun, Option.map_some, hemp] at g0 g1 gt hrep0 hrep1 hj ⊢
        generalize comp.door = Dr at hrep0 hrep1 hj ⊢
        unfold scND scOt scArgs
        simp [nock_exec, hc, by_arm, by.arm_at, by.dif.arm_at, dif_arm, hd0, hd1, by.got.arm_at, got_arm, g0, g1,
          gt, Blob.toNoun, Termin.toNoun, Jmp.toNoun, Tag.hop, et, bind_apply, e2, e3, hrep0, hrep1, hj]
      · have ht' : ¬ th1 = th0 := fun e => ht e.symm
        simp only [scT, compCore, genNoun] at g0 g1 ⊢
        generalize comp.door = Dr
        unfold scND scOt
        simp [nock_exec, hc, by_arm, by.arm_at, by.dif.arm_at, dif_arm, hd0, hd1, by.got.arm_at, got_arm, g0, g1,
          Blob.toNoun, Termin.toNoun, Jmp.toNoun, Tag.hop, ht, ht']
    all_goals
      simp only [scT, compCore, genNoun] at g0 g1 ⊢
      generalize comp.door = Dr
      unfold scND scOt
      simp [nock_exec, hc, by_arm, by.arm_at, by.dif.arm_at, dif_arm, hd0, hd1, by.got.arm_at, got_arm, g0, g1,
        Blob.toNoun, Termin.toNoun, Jmp.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti]
  all_goals
    simp only [scT, compCore, genNoun] at g0 g1 ⊢
    generalize comp.door = Dr
    unfold scND scOt
    simp [nock_exec, hc, by_arm, by.arm_at, by.dif.arm_at, dif_arm, hd0, hd1, by.got.arm_at, got_arm, g0, g1,
      Blob.toNoun, Termin.toNoun, Jmp.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti]

end Compiler
end Formalization
