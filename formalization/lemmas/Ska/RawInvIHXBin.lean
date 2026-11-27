import lemmas.Ska.RawInvIHX
import lemmas.Ska.CompFootX

/-!
# Raw `+comp` output on `FragX`: cons, `%5` and `%10`

README Gaps 14, track D, step 2 of the class `FragX`.  The three binary
cases of `RawIHX`: two runs, `q` first into the block before, `p` into
`q`'s code, then `+copy` of their lazy needs.

* `LiveK.monoB`: kills compared at one register and only at labels with a
  block.  `p` runs with `q`'s kills cut at `q`'s end (so they vanish there,
  `KVan`), which is no change on `q`'s blocks.
* **`rawX_binTail`**: the two runs and the copy.  The entries of the two
  results lie apart (`labs` of `runX_keeps`), so the copy is that of the sure
  needs with the entries side by side (`copyL_apart_some` of track C) and
  `raw_copy` applies; the moves of the copy block define every register of
  the two sure needs that the merged need does not keep, so a register live
  after the copy is in neither, and the kills of the two results' roots,
  which are not entries of the copy's result, do not touch it.  The facts of
  `sub_facts` come from `runX_keeps`, `runX_foot` (track C) and the jump
  facts of `RawIHX`.
* The cases: **`rawX_cons`** (`rawX_consBody`: `+split` first, as
  `raw_consNext`), **`rawX_five`** (the block of `n5Pre`, as `raw_n5`),
  **`rawX_ten`** (`+simple-next` and `+into`, as `raw_n10`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]
variable {X : Map Blob → Prop} [XOK X]

/-- **Kills compared at one register, at the labels with a block.** -/
theorem LiveK.monoB {bl : Map Blob} {K K' : Nat → Nat → Prop} {k r : Nat} (h : LiveK bl K k r)
    (hK : ∀ x b, HoonMap.get bl x = some b → K' x r → K x r) : LiveK bl K' k r := by
  induction h with
  | here hb hr hk => exact LiveK.here hb hr fun e => hk (hK _ _ hb e)
  | next hb hj _ hd hk ih => exact LiveK.next hb hj (ih hK) hd fun e => hk (hK _ _ hb e)

theorem lazK_cases {o : Nat} {l : Lazy S} {x r : Nat} (h : lazK o l x r) :
    NMem l.sure.ned r ∨ ∃ e ∈ entries l, e.1 = x ∧ NMem e.2.sure.ned r := by
  obtain ⟨e, he, h1, h2⟩ := h
  rcases List.mem_cons.mp he with rfl | he
  · exact Or.inl h2
  · exact Or.inr ⟨e, he, h1, h2⟩

theorem lazK_root {o : Nat} {l : Lazy S} {r : Nat} (h : NMem l.sure.ned r) : lazK o l o r :=
  ⟨(o, l), List.mem_cons_self, rfl, h⟩

theorem lazK_ent {o : Nat} {l : Lazy S} {e : Nat × Lazy S} (he : e ∈ entries l) {r : Nat}
    (h : NMem e.2.sure.ned r) : lazK o l e.1 r :=
  ⟨e, List.mem_cons_of_mem _ he, rfl, h⟩

/-- The kills of a result with the entries of two side by side, at a
register in neither root's sure need. -/
theorem lazK_side {o o1 o2 : Nat} {s : Sure S} {l1 l2 : Lazy S} {x r : Nat} (n1 : ¬ NMem l1.sure.ned r)
    (n2 : ¬ NMem l2.sure.ned r) (h : lazK o1 l1 x r ∨ lazK o2 l2 x r) :
    lazK o (mk s (l1.fork ++ l2.fork) (l1.bond ++ l2.bond)) x r := by
  have P := entries_side_perm s l1 l2
  rcases h with h | h
  · rcases lazK_cases h with e | ⟨e, he, rfl, hr⟩
    · exact absurd e n1
    · exact lazK_ent (P.mem_iff.mpr (List.mem_append_left _ he)) hr
  · rcases lazK_cases h with e | ⟨e, he, rfl, hr⟩
    · exact absurd e n2
    · exact lazK_ent (P.mem_iff.mpr (List.mem_append_right _ he)) hr

/-! ## The two runs and the copy -/

/-- **The two runs and the `+copy` of cons, `%5` and `%10` on `FragX`**:
`q` for `ts` into `j`, `p` for `hs` into `q`'s code, the copy of their lazy
needs. -/
theorem rawX_binTail {p q : Nomm} (xp : FragX (S := S) p) (xq : FragX (S := S) q)
    (ihp : RawIHX S Map X p) (ihq : RawIHX S Map X q) (hc : sixCount p + sixCount q ≤ 255)
    {hs ts : Sure S} {j : Jmp} {region : List Nat} {g2 g3 g4 g1 : Comp.Gen Map} {nex2 nex1 nex : NextL S}
    {K : Nat → Nat → Prop} (hK : KVan K g2.bo)
    (h : SIP X (upRk g2.blocks) g2.bo g2) (nh : NB g2.re hs.ned) (nt : NB g2.re ts.ned) (dh : Distinct hs.ned)
    (dt : Distinct ts.ned) (ap : ∀ x, NMem hs.ned x → ¬ NMem ts.ned x) (ha : j.args = []) (hj1 : 1 ≤ j.there)
    (hj : j.there < g2.bo) (hf : ∀ x, Defd g2.blocks x → ¬ NMem hs.ned x ∧ ¬ NMem ts.ned x)
    (h3 : runL q (CGoalL.next (ofSure ts) j) region g2 = some (nex2, g3))
    (h4 : runL p (CGoalL.next (ofSure hs) nex2.th) region g3 = some (nex1, g4))
    (h5 : copyL nex1 nex2.laz g4 = some (nex, g1)) :
    SIP X (upRk g1.blocks) g1.bo g1 ∧ nex.th.args = [] ∧ 1 ≤ nex.th.there ∧ nex.th.there < g1.bo ∧
      ∀ x, LiveK g1.blocks (fun a c => K a c ∨ lazK nex.th.there nex.laz a c) nex.th.there x →
        LiveK g2.blocks K j.there x ∧ ¬ NMem hs.ned x ∧ ¬ NMem ts.ned x := by
  have hcq : sixCount q ≤ 255 := by omega
  have hcp : sixCount p ≤ 255 := by omega
  -- the run of `q`
  have gq : GoalIn g2.re (CGoal.next ts j : CGoal S) := ⟨nt, fun x hx => by rw [ha] at hx; cases hx⟩
  obtain ⟨S3, a3, lo3, hi3, L3⟩ := ihq (CGoal.next ts j) region g2 g3 nex2 K hK h gq dt ⟨hj1, hj⟩ ha
    (fun r d hm => (hf r d).2 hm) hcq h3
  have Rq := runX_keeps xq (goal := CGoal.next ts j) h.drop gq hcq h3
  have Fq := runX_foot xq (goal := CGoal.next ts j) h.drop gq dt hcq h3
  have l3 := Rq.keeps.le
  have nb3 : NB g3.re nex2.laz.sure.ned := Rq.out.1.1
  have s3 : ∀ x, NMem nex2.laz.sure.ned x → g2.re ≤ x ∨ NMem ts.ned x := Fq.sure
  have dd3 : ∀ x, Defd g3.blocks x → Defd g2.blocks x ∨
      (x < g3.re ∧ (g2.re ≤ x ∨ NMem ts.ned x) ∧ ¬ NMem nex2.laz.sure.ned x) := fun x d =>
    (defd_of_wroteIn Fq.wr d).imp_right fun e => ⟨e.1, e.2.1, e.2.2.1⟩
  -- the run of `p`, with `q`'s kills cut at `q`'s end
  have gp : GoalIn g3.re (CGoal.next hs nex2.th : CGoal S) :=
    ⟨nh.mono l3, fun x hx => by rw [a3] at hx; cases hx⟩
  have fp : ∀ r, Defd g3.blocks r → ¬ GMem (CGoal.next hs nex2.th : CGoal S) r := fun r d hm => by
    rcases dd3 r d with d | ⟨_, e, _⟩
    · exact (hf r d).1 hm
    · rcases e with e | e
      · have := nh r hm; omega
      · exact ap r hm e
  have hK3 : KVan (fun a c => a < g3.bo ∧ (K a c ∨ lazK nex2.th.there nex2.laz a c)) g3.bo :=
    ⟨fun k r hk e => by have := e.1; omega⟩
  obtain ⟨S4, a4, lo4, hi4, L4⟩ := ihp (CGoal.next hs nex2.th) region g3 g4 nex1 _ hK3 S3 gp dh ⟨lo3, hi3⟩ a3 fp
    hcp h4
  have Rp := runX_keeps xp (goal := CGoal.next hs nex2.th) S3.drop gp hcp h4
  have Fp := runX_foot xp (goal := CGoal.next hs nex2.th) S3.drop gp dh hcp h4
  have l4 := Rp.keeps.le
  have nb4 : NB g4.re nex1.laz.sure.ned := Rp.out.1.1
  have s4 : ∀ x, NMem nex1.laz.sure.ned x → g3.re ≤ x ∨ NMem hs.ned x := Fp.sure
  have dd4 : ∀ x, Defd g4.blocks x → Defd g3.blocks x ∨
      (x < g4.re ∧ (g3.re ≤ x ∨ NMem hs.ned x) ∧ ¬ NMem nex1.laz.sure.ned x) := fun x d =>
    (defd_of_wroteIn Fp.wr d).imp_right fun e => ⟨e.1, e.2.1, e.2.2.1⟩
  -- the copy: the entries lie apart
  obtain ⟨n, hcp', rfl⟩ := copyL_apart_some
    (fun e he e' he' => by
      have a := (Rp.labs _ (fork_in_entries he)).1
      have b := (Rq.labs _ (fork_in_entries he')).2
      omega)
    (fun e he e' he' => by
      have a := (Rp.labs _ (bond_in_entries he)).1
      have b := (Rq.labs _ (bond_in_entries he')).2
      omega) h5
  have m2 : ∀ x, NMem nex2.laz.sure.ned x → (g2.re ≤ x ∨ NMem ts.ned x) ∧ x < g3.re :=
    fun x hx => ⟨s3 x hx, nb3 x hx⟩
  have dab : Distinct (Need.pair nex1.laz.sure.ned nex2.laz.sure.ned) := ⟨Fp.dist, Fq.dist, fun x h1 h2 => by
    obtain ⟨e2, lt2⟩ := m2 x h2
    rcases s4 x h1 with e1 | e1
    · omega
    · rcases e2 with e2 | e2
      · have := nh x e1; omega
      · exact ap x e1 e2⟩
  have hfc : ∀ y, NMem nex1.laz.sure.ned y ∨ NMem nex2.laz.sure.ned y → ¬ Defd g4.blocks y := fun y hy d => by
    rcases dd4 y d with d | ⟨_, e4, n4⟩
    · rcases dd3 y d with d | ⟨_, e3, n3⟩
      · have lt := h.defd_lt d
        obtain ⟨fh, ft⟩ := hf y d
        rcases hy with hy | hy
        · rcases s4 y hy with e | e
          · omega
          · exact fh e
        · rcases (m2 y hy).1 with e | e
          · omega
          · exact ft e
      · rcases hy with hy | hy
        · rcases s4 y hy with e | e
          · omega
          · rcases e3 with e3 | e3
            · have := nh y e; omega
            · exact ap y e e3
        · exact n3 hy
    · rcases hy with hy | hy
      · exact n4 hy
      · obtain ⟨e2, lt2⟩ := m2 y hy
        rcases e4 with e4 | e4
        · omega
        · rcases e2 with e2 | e2
          · have := nh y e4; omega
          · exact ap y e4 e2
  have hKc : KVan (fun a c => a < g4.bo ∧ (K a c ∨
      lazK g4.bo (mk n.laz (nex1.laz.fork ++ nex2.laz.fork) (nex1.laz.bond ++ nex2.laz.bond)) a c)) g4.bo :=
    ⟨fun k r hk e => by have := e.1; omega⟩
  obtain ⟨S1, eth, bo1, -, below, L1, -⟩ := raw_copy (first := ⟨nex1.laz.sure, nex1.th⟩)
    (K := fun a c => a < g4.bo ∧ (K a c ∨
      lazK g4.bo (mk n.laz (nex1.laz.fork ++ nex2.laz.fork) (nex1.laz.bond ++ nex2.laz.bond)) a c)) S4 a4 hi4 dab nb4
    (nb3.mono l4) hfc hcp'
  have hb4 := S4.bo1
  refine ⟨sip_reRank S1 (fun k hk => S4.none hk) (finKeep_of_eq below), by rw [eth]; rfl,
    by rw [eth]; simp [jmp0]; omega, by rw [eth]; simp [jmp0]; omega, fun x hx => ?_⟩
  have hnk := hx.nk
  simp only at hx hnk
  rw [eth] at hx hnk
  simp only [jmp0] at hx hnk
  have nn : ¬ NMem n.laz.ned x := fun e => hnk (Or.inr (lazK_root e))
  rcases L1 x (hx.mono fun a c e => e.2) with e | ⟨hl, n1, n2⟩
  · exact absurd e nn
  have hl' := hl.monoB (K' := fun a c => (a < g3.bo ∧ (K a c ∨ lazK nex2.th.there nex2.laz a c)) ∨
      lazK nex1.th.there nex1.laz a c) fun a b hb e => by
    refine ⟨S4.lab a b hb, ?_⟩
    rcases e with ⟨-, e | e⟩ | e
    · exact Or.inl e
    · exact Or.inr (lazK_side (o1 := nex1.th.there) (o2 := nex2.th.there) n1 n2 (Or.inr e))
    · exact Or.inr (lazK_side (o1 := nex1.th.there) (o2 := nex2.th.there) n1 n2 (Or.inl e))
  obtain ⟨hl2, nh'⟩ := L4 x hl'
  have hl3 := hl2.monoB (K' := fun a c => K a c ∨ lazK nex2.th.there nex2.laz a c) fun a b hb e => ⟨S3.lab a b hb, e⟩
  obtain ⟨hl4, nt'⟩ := L3 x hl3
  exact ⟨hl4, nh', nt'⟩

end Raw
end SkaModel
end Formalization
