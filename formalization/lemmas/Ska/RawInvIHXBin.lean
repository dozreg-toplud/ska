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
    (ch : Clean hs.ned) (ct : Clean ts.ned)
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
    (fun r d hm => (hf r d).2 hm) hcq ct h3
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
    hcp ch h4
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

/-! ## Cons -/

theorem rawX_consBody {p q : Nomm} (xp : FragX (S := S) p) (xq : FragX (S := S) q)
    (ihp : RawIHX S Map X p) (ihq : RawIHX S Map X q) (hc : sixCount p + sixCount q ≤ 255)
    {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Comp.Gen Map} {nex : NextL S}
    {K : Nat → Nat → Prop} (hK : KVan K g0.bo) (h : SIP X (upRk g0.blocks) g0.bo g0) (hn : NB g0.re sur.ned)
    (dn : Distinct sur.ned) (ha : th.args = []) (hj1 : 1 ≤ th.there) (hj : th.there < g0.bo)
    (hf : ∀ y, NMem sur.ned y → ¬ Defd g0.blocks y) (hcl : Clean sur.ned)
    (hr : (do
      let (hed, tel, o) ← splitL ⟨ofSure sur, th⟩
      let nexh ← pastL noCode ⟨hed, jmp0 o⟩ q region
      let nex2 ← runL q (CGoalL.next tel nexh.th) region
      let nex2 ← pastL noCode nex2 p region
      let nex1 ← runL p (CGoalL.next nexh.laz nex2.th) region
      copyL nex1 nex2.laz : CM Map (NextL S)) g0 = some (nex, g1)) :
    SIP X (upRk g1.blocks) g1.bo g1 ∧ nex.th.args = [] ∧ 1 ≤ nex.th.there ∧ nex.th.there < g1.bo ∧
      ∀ x, LiveK g1.blocks (fun a c => K a c ∨ lazK nex.th.there nex.laz a c) nex.th.there x →
        LiveK g0.blocks K th.there x ∧ ¬ NMem sur.ned x := by
  obtain ⟨⟨hed', tel', o⟩, g2x, h2, hr⟩ := bind_some hr
  rw [splitL_mk, map_apply] at h2
  obtain ⟨⟨⟨hed, tel, o'⟩, g2⟩, hs2, e2⟩ := Option.map_eq_some_iff.mp h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e2
  have CS := clean_split hs2 hcl
  obtain ⟨S2, eo, bo2, l2, fr2, Ls, Ds⟩ := raw_split (K := K) h dn hn ha hj hf hs2
  simp only at eo; subst eo
  obtain ⟨-, nh, nt⟩ := keeps_split h.drop hn (fun x hx => by rw [ha] at hx; cases hx) hs2
  obtain ⟨-, dh, dt, ap, mh, mt⟩ := split_foot h.drop dn hn (fun x hx => by rw [ha] at hx; cases hx) hs2
  simp only at nh nt dh dt ap mh mt Ls Ds
  obtain ⟨nexh, g2', hph, hr⟩ := bind_some hr
  rw [pastL_mk _ _ _ (fragX_pure xq), pure_apply] at hph
  simp only [Option.some.injEq, Prod.mk.injEq] at hph
  obtain ⟨rfl, rfl⟩ := hph
  obtain ⟨nex2, g3, h3, hr⟩ := bind_some hr
  obtain ⟨nex2', g3', hp2, hr⟩ := bind_some hr
  rw [pastL_pure _ _ (fragX_pure xp), pure_apply] at hp2
  simp only [Option.some.injEq, Prod.mk.injEq] at hp2
  obtain ⟨rfl, rfl⟩ := hp2
  obtain ⟨nex1, g4, h4, hr⟩ := bind_some hr
  obtain ⟨S1, a1, lo1, hi1, L1⟩ := rawX_binTail xp xq ihp ihq hc (hK.mono (by omega))
    (sip_reRank S2 (fun k hk => h.none hk) (finKeep_of_eq fr2)) nh nt dh dt ap rfl
    (by simp [jmp0]; have := h.bo1; omega) (by simp [jmp0]; omega)
    (fun x d => by
      rcases Ds x d with d | ⟨_, e1, e2⟩
      · have := h.defd_lt d
        refine ⟨fun e => ?_, fun e => ?_⟩
        · rcases mh x e with e' | e'
          · exact hf x e' d
          · omega
        · rcases mt x e with e' | e'
          · exact hf x e' d
          · omega
      · exact ⟨e1, e2⟩) (ch := CS.1) (ct := CS.2) h3 h4 hr
  refine ⟨S1, a1, lo1, hi1, fun x hx => ?_⟩
  obtain ⟨hl, n1, n2⟩ := L1 x hx
  rcases Ls x hl with e | e | e
  · exact absurd e n1
  · exact absurd e n2
  · exact e

/-- **The case cons**: `%done` makes the block `don` and runs as `%next`,
`%pick` makes a `%bom` block and runs both operands for an empty need, as
`raw_cons`. -/
theorem rawX_cons {p q : Nomm} (xp : FragX (S := S) p) (xq : FragX (S := S) q) (ihp : RawIHX S Map X p)
    (ihq : RawIHX S Map X q) : RawIHX S Map X (Nomm.cons p q) := by
  intro goal region g0 g1 nex K hK h hg hD hj ha hf hc hcl hr
  have hc' : sixCount p + sixCount q ≤ 255 := by simpa only [sixCount] using hc
  cases goal with
  | next sur th =>
    simp only [CGoal.toL] at hr
    rw [runL_cons_next] at hr
    exact rawX_consBody xp xq ihp ihq hc' hK h hg.1 hD ha hj.1 hj.2 (fun y hy d => hf y d hy) hcl hr
  | done =>
    simp only [CGoal.toL] at hr
    rw [runL_cons_done] at hr
    obtain ⟨r, g3, h3, hr⟩ := bind_some hr
    obtain ⟨S3, rfl, q3, b3, o3⟩ := sip_re h h3
    obtain ⟨o, g4, h4, hr⟩ := bind_some hr
    obtain ⟨S4, rfl, e4, q4, bo4⟩ := sip_emit S3 (emitOK_don (by omega)) h4
    rw [runL_cons_next] at hr
    obtain ⟨S1, a1, lo1, hi1, L1⟩ := rawX_consBody (sur := lazyReg g0.re) xp xq ihp ihq hc'
      (hK.mono (by omega)) (sip_reRank S4 (fun k hk => h.none hk) (finKeep_put (by rw [e4, b3, o3])))
      (nb_this (by omega)) trivial rfl (by simp [jmp0]; have := h.bo1; omega) (by simp [jmp0]; omega)
      (fun y hy d => by
        simp only [lazyReg, NMem] at hy; subst hy
        rw [e4, defd_put (S3.none (Nat.le_refl _)), b3] at d
        rcases d with d | d
        · have := h.defd_lt d; omega
        · simp [blockDefs, defsOf] at d) trivial hr
    refine ⟨S1, a1, lo1, hi1, fun x hx => ?_⟩
    obtain ⟨hl, hn⟩ := L1 x hx
    exact hn (by simp only [lazyReg, NMem]; exact not_liveK_don (by rw [e4]; exact get_put_self) hl)
  | pick z o =>
    simp only [CGoal.toL] at hr
    rw [runL_cons_pick] at hr
    obtain ⟨o', g2, h2, hr⟩ := bind_some hr
    obtain ⟨S2, rfl, e2, q2, bo2⟩ := sip_emit h (emitOK_bom Option.none) h2
    obtain ⟨nex2, g3, h3, hr⟩ := bind_some hr
    obtain ⟨nex2', g3', hp2, hr⟩ := bind_some hr
    rw [pastL_pure _ _ (fragX_pure xp), pure_apply] at hp2
    simp only [Option.some.injEq, Prod.mk.injEq] at hp2
    obtain ⟨rfl, rfl⟩ := hp2
    obtain ⟨nex1, g4, h4, hr⟩ := bind_some hr
    obtain ⟨S1, a1, lo1, hi1, L1⟩ := rawX_binTail (hs := Sure.bunt) (ts := Sure.bunt) xp xq ihp ihq hc'
      (hK.mono (by omega)) (sip_reRank S2 (fun k hk => h.none hk) (finKeep_put e2)) (nb_none _) (nb_none _)
      trivial trivial (fun _ e => e.elim) rfl (by simp [jmp0]; have := h.bo1; omega) (by simp [jmp0]; omega)
      (fun _ _ => ⟨fun e => e.elim, fun e => e.elim⟩) (ch := trivial) (ct := trivial) h3 h4 hr
    refine ⟨S1, a1, lo1, hi1, fun x hx => ?_⟩
    obtain ⟨hl, -⟩ := L1 x hx
    exact absurd hl (not_liveK_bom (by rw [e2]; exact get_put_self))

/-! ## `%5` -/

/-- **The case `%5`**: the block of `n5Pre` that compares the two
registers, then the two runs and the copy, as `raw_n5`. -/
theorem rawX_five {p q : Nomm} (xp : FragX (S := S) p) (xq : FragX (S := S) q) (ihp : RawIHX S Map X p)
    (ihq : RawIHX S Map X q) : RawIHX S Map X (Nomm.n5 p q) := by
  intro goal region g0 g1 nex K hK h hg hD hj ha hf hc _ hr
  have hc' : sixCount p + sixCount q ≤ 255 := by simpa only [sixCount] using hc
  rw [runL_n5_toL] at hr
  obtain ⟨rp, g2, h2, hr⟩ := bind_some hr
  obtain ⟨S2, rfl, q2, b2, o2⟩ := sip_re h h2
  obtain ⟨rq, g3, h3, hr⟩ := bind_some hr
  obtain ⟨S3, rfl, q3, b3, o3⟩ := sip_re S2 h3
  obtain ⟨o, g4, h4, hr⟩ := bind_some hr
  have b30 : g3.blocks = g0.blocks := by rw [b3, b2]
  have bo30 : g3.bo = g0.bo := by rw [o3, o2]
  have F3 : FinKeep g0 g3 := finKeep_blocks b30
  have H : SIP X (upRk g0.blocks) g0.bo g4 ∧ FinKeep g0 g4 ∧ 1 ≤ o ∧ o < g4.bo ∧ g3.re ≤ g4.re ∧
      (∀ x, Defd g4.blocks x → Defd g0.blocks x ∨ g3.re ≤ x ∨ GMem goal x) ∧
      (∀ x, LiveK g4.blocks K o x → x = g0.re ∨ x = g2.re ∨ GLiveK g0.blocks K goal x) := by
    cases goal with
    | pick z o' =>
      simp only [GJ] at hj
      simp only [n5Pre] at h4
      obtain ⟨S4, rfl, e4, q4, bo4⟩ := sip_emit S3 (emitOK_eqq (by omega) (by omega) ha.1 ha.2 (by omega) (by omega)) h4
      refine ⟨S4, F3.trans (finKeep_put e4) (by omega), by have := h.bo1; omega, by omega, by omega,
        fun x d => ?_, fun x hl => ?_⟩
      · rw [e4, defd_put (S3.none (Nat.le_refl _)), b30] at d
        rcases d with d | d
        · exact Or.inl d
        · simp [blockDefs, defsOf] at d
      · rcases liveK_unfoldP (by rw [e4]; exact get_put_self) (S3.below g3.bo)
          (fun k hk => by rw [e4, get_put_ne (by omega)])
          (fun j hj' => by simp [getJmps] at hj'; rcases hj' with rfl | rfl <;> omega) hl with
          e | ⟨j, hj', hl', -⟩
        · rcases blockRF_eqq ha.1 ha.2 e with e | e
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
        · rw [b30] at hl'
          simp [getJmps] at hj'
          rcases hj' with rfl | rfl
          · exact Or.inr (Or.inr (Or.inl hl'))
          · exact Or.inr (Or.inr (Or.inr hl'))
    | done =>
      simp only [n5Pre] at h4
      obtain ⟨⟨o0, o1⟩, g5, h5, h4⟩ := bind_some h4
      obtain ⟨S5, l5, rfl, rfl, bo5, fr5, n0, n1, dd5⟩ := raw_doneBlocks (K := K) S3 h5
      obtain ⟨S4, rfl, e4, q4, bo4⟩ := sip_emit S5 (emitOK_eqq (by omega) (by omega) rfl rfl
        (by simp [jmp0]; omega) (by simp [jmp0]; omega)) h4
      refine ⟨S4, (F3.trans (finKeep_of_eq fr5) (by omega)).trans (finKeep_put e4) (by omega),
        by have := h.bo1; omega, by omega, by omega, fun x d => ?_, fun x hl => ?_⟩
      · rw [e4, defd_put (S5.none (Nat.le_refl _))] at d
        rcases d with d | d
        · rcases dd5 x d with d | d
          · rw [b30] at d; exact Or.inl d
          · exact Or.inr (Or.inl d.1)
        · simp [blockDefs, defsOf] at d
      · rcases liveK_unfoldP (by rw [e4]; exact get_put_self) (S5.below g5.bo)
          (fun k hk => by rw [e4, get_put_ne (by omega)])
          (fun j hj' => by simp [getJmps] at hj'; rcases hj' with rfl | rfl <;> simp [jmp0] <;> omega) hl with
          e | ⟨j, hj', hl', -⟩
        · rcases blockRF_eqq rfl rfl e with e | e
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
        · simp [getJmps] at hj'
          rcases hj' with rfl | rfl
          · exact absurd hl' (n0 x)
          · exact absurd hl' (n1 x)
    | next laz th =>
      have hjt : th.there < g0.bo := hj.2
      simp only [n5Pre] at h4
      obtain ⟨a, g5, h5, h4⟩ := bind_some h4
      obtain ⟨S5, l5, bo5, ha5, fr5, cn, cs⟩ := raw_collapse (K := K) S3 (hg.1.mono (by omega)) (by omega)
        (fun y hy d => by rw [b30] at d; exact hf y d hy) h5
      have F5 : FinKeep g0 g5 := F3.trans (finKeep_of_grow (collapse_down h5 hj.1 (show th.there < g3.bo by omega) S3.bo1).1) (by omega)
      cases a with
      | none =>
        obtain ⟨hn0, e5⟩ := cn rfl
        rw [e5] at h4
        rw [if_pos ha5] at h4
        have E : EmitOK g3 ⟨[], [Pole.equ g0.re g2.re], Termin.hop (jmp0 th.there)⟩ :=
          emitOK_of rfl (fun j hj' => by simp [getJmps] at hj'; rw [hj']; rfl)
            (fun j hj' => by simp [getJmps] at hj'; rw [hj']; simp [jmp0]; omega)
            (regsIn_one (fun x hx => by simp [Comp.poleRegs] at hx; omega)) (by simp [FinIn, JmpIn, jmp0])
            (by simp [defsOf, aliasDst, List.filterMap_cons]) (fun y hy => by simp [defsOf, aliasDst] at hy)
            (fun op hop => by simp at hop; subst hop; rfl)
        obtain ⟨S4, rfl, e4, q4, bo4⟩ := sip_emit S3 E h4
        refine ⟨S4, F3.trans (finKeep_put e4) (by omega), by have := h.bo1; omega, by omega, by omega,
          fun x d => ?_, fun x hl => ?_⟩
        · rw [e4, defd_put (S3.none (Nat.le_refl _)), b30] at d
          rcases d with d | d
          · exact Or.inl d
          · simp [blockDefs, defsOf, aliasDst] at d
        · rcases liveK_unfoldP (by rw [e4]; exact get_put_self) (S3.below g3.bo)
            (fun k hk => by rw [e4, get_put_ne (by omega)])
            (fun j hj' => by simp [getJmps] at hj'; rw [hj']; simp [jmp0]; omega) hl with
            ⟨-, e⟩ | ⟨j, hj', hl', -⟩
          · rcases e with e | ⟨-, e⟩
            · simp only [OpsRF, reads_equ] at e
              rcases e with (e | e) | ⟨-, e⟩
              · exact Or.inl e
              · exact Or.inr (Or.inl e)
              · exact e.elim
            · simp [finRegs, jmpRegs, jmp0] at e
          · simp [getJmps] at hj'; subst hj'
            rw [b30] at hl'
            exact Or.inr (Or.inr ⟨hl', by rw [hn0]; exact id⟩)
      | some x =>
        obtain ⟨r, o'⟩ := x
        obtain ⟨rm, rl, nd, tl, dd, lv⟩ := cs r o' rfl
        simp only at h4
        obtain ⟨⟨z, o''⟩, g6, h6, h4⟩ := bind_some h4
        obtain ⟨S6, q6, bo6, rfl, rfl, fr6, lz, lo', dd6⟩ := raw_forl (K := K) S5 rl nd tl h6
        obtain ⟨S4, rfl, e4, q4, bo4⟩ := sip_emit S6 (emitOK_eqq (by omega) (by omega) rfl rfl
          (by simp [jmp0]; omega) (by simp [jmp0]; omega)) h4
        refine ⟨S4, (F5.trans (finKeep_of_eq fr6) (by omega)).trans (finKeep_put e4) (by omega),
          by have := h.bo1; omega, by omega, by omega, fun x d => ?_, fun x hl => ?_⟩
        · rw [e4, defd_put (S6.none (Nat.le_refl _))] at d
          rcases d with d | d
          · rcases dd6 x d with d | rfl | d
            · rcases dd x d with d | d
              · rw [b30] at d; exact Or.inl d
              · exact Or.inr (Or.inl d.1)
            · rcases rm with e | e
              · exact Or.inr (Or.inr e)
              · exact Or.inr (Or.inl e.1)
            · exact Or.inr (Or.inl (by omega))
          · simp [blockDefs, defsOf] at d
        · rcases liveK_unfoldP (by rw [e4]; exact get_put_self) (S6.below g6.bo)
            (fun k hk => by rw [e4, get_put_ne (by omega)])
            (fun j hj' => by simp [getJmps] at hj'; rcases hj' with rfl | rfl <;> simp [jmp0] <;> omega) hl with
            e | ⟨j, hj', hl', -⟩
          · rcases blockRF_eqq rfl rfl e with e | e
            · exact Or.inl e
            · exact Or.inr (Or.inl e)
          · simp [getJmps] at hj'
            have hl'' : x ≠ r ∧ LiveK g5.blocks K o' x := by
              rcases hj' with rfl | rfl
              · exact lz x hl'
              · exact lo' x hl'
            rcases lv x hl''.2 with e | ⟨e1, e2⟩
            · exact absurd e hl''.1
            · rw [b30] at e1; exact Or.inr (Or.inr ⟨e1, e2⟩)
  obtain ⟨S4, F4, lo4, hi4, l4, dd4, lv4⟩ := H
  obtain ⟨nexq, g5, h5, hr⟩ := bind_some hr
  obtain ⟨nexq', g5', hp, hr⟩ := bind_some hr
  rw [pastL_pure _ _ (fragX_pure xp), pure_apply] at hp
  simp only [Option.some.injEq, Prod.mk.injEq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  obtain ⟨nexp, g6, h6, hr⟩ := bind_some hr
  have hgm : ∀ x, GMem goal x → x < g0.re := fun x hx => by
    cases goal with
    | next laz th => exact hg.1 x hx
    | _ => exact hx.elim
  obtain ⟨S1, a1, lo1, hi1, L1⟩ := rawX_binTail (hs := lazyReg g0.re) (ts := lazyReg g2.re) xp xq ihp ihq hc'
    (hK.mono S4.lob) (sip_reRank S4 (fun k hk => h.none hk) F4) (nb_this (by omega))
    (nb_this (by omega)) trivial trivial
    (fun x e1 e2 => by simp only [lazyReg, NMem] at e1 e2; omega) rfl (by simp [jmp0]; exact lo4)
    (by simp [jmp0]; exact hi4)
    (fun x d => by
      simp only [lazyReg, NMem]
      rcases dd4 x d with d | d | d
      · have := h.defd_lt d; omega
      · omega
      · have := hgm x d; omega) (ch := trivial) (ct := trivial) h5 h6 hr
  refine ⟨S1, a1, lo1, hi1, fun x hx => ?_⟩
  obtain ⟨hl, n1, n2⟩ := L1 x hx
  simp only [lazyReg, NMem] at n1 n2
  rcases lv4 x hl with e | e | e
  · exact absurd e n1
  · exact absurd e n2
  · exact e

/-! ## `%10` -/

/-- **The case `%10`**: `+simple-next`, `+into` of its need, then the run
of the value `v` for the donor's need and of the target `q` for the
recipient's, and the copy, as `raw_n10`. -/
theorem rawX_ten (a : Nat) {v q : Nomm} (xv : FragX (S := S) v) (xq : FragX (S := S) q) (ihv : RawIHX S Map X v)
    (ihq : RawIHX S Map X q) : RawIHX S Map X (Nomm.n10 a v q) := by
  intro goal region g0 g1 nex K hK h hg hD hj ha hf hc hcl hr
  have hc' : sixCount q + sixCount v ≤ 255 := by simp only [sixCount] at hc; omega
  rw [runL_n10_body] at hr
  obtain ⟨next, gs, hs, hr⟩ := bind_some hr
  rw [simpleNextL_toL, map_apply] at hs
  obtain ⟨⟨nx, g2⟩, hs', e⟩ := Option.map_eq_some_iff.mp hs
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨S2, l2, bo2, a2, t2, fr2, dd2, L2, m2, -⟩ := raw_simpleNext (K := K) h hj ha hg hs'
  have D2 := simpleNext_dist hD hs'
  have hgm : ∀ x, GMem goal x → x < g0.re := fun x hx => by
    cases goal with
    | next laz th => exact hg.1 x hx
    | _ => exact hx.elim
  have nb2 : NB g2.re nx.laz.ned := fun y hy => by
    rcases m2 y hy with e | e
    · have := hgm y e; omega
    · exact e.2
  have nf2 : ∀ y, NMem nx.laz.ned y → ¬ Defd g2.blocks y := fun y hy d => by
    rw [dd2] at d
    rcases m2 y hy with e | e
    · exact hf y d e
    · have := h.defd_lt d; omega
  unfold n10Body at hr
  obtain ⟨⟨don', rec', o⟩, g3x, h3, hr⟩ := bind_some hr
  rw [show (Next.toL nx : NextL S) = ⟨ofSure nx.laz, nx.th⟩ from rfl, intoL_mk, map_apply] at h3
  obtain ⟨⟨⟨don, rec, o'⟩, g3⟩, hs3, e3⟩ := Option.map_eq_some_iff.mp h3
  simp only [Prod.mk.injEq] at e3
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e3
  have CI := clean_into hs3 (clean_simpleNext hs' hcl)
  obtain ⟨S3, eo, bo3, l3, fr3, L3, dd3, Dd, Dr, Ap, md, mr⟩ := raw_into (K := K) S2 D2 nb2 a2 t2 nf2 hs3
  subst eo
  obtain ⟨-, nd3, nr3⟩ := keeps_into S2.drop ⟨nb2, fun x hx => by rw [a2] at hx; cases hx⟩ hs3
  simp only at nd3 nr3
  obtain ⟨nexR, g3', hpr, hr⟩ := bind_some hr
  rw [pastL_mk _ _ _ (fragX_pure xv), pure_apply] at hpr
  simp only [Option.some.injEq, Prod.mk.injEq] at hpr
  obtain ⟨rfl, rfl⟩ := hpr
  obtain ⟨nexDon, g4, h4, hr⟩ := bind_some hr
  obtain ⟨nexDon', g4', hpd, hr⟩ := bind_some hr
  rw [pastL_pure _ _ (fragX_pure xq), pure_apply] at hpd
  simp only [Option.some.injEq, Prod.mk.injEq] at hpd
  obtain ⟨rfl, rfl⟩ := hpd
  obtain ⟨nexRec, g5, h5, hr⟩ := bind_some hr
  have F3 : FinKeep g0 g3 := (finKeep_of_eq fr2).trans (finKeep_of_eq fr3) bo2
  obtain ⟨S1, a1, lo1, hi1, L1⟩ := rawX_binTail (hs := rec) (ts := don) (j := jmp0 g2.bo) xq xv ihq ihv hc'
    (hK.mono S3.lob) (sip_reRank S3 (fun k hk => h.none hk) F3) nr3 nd3 Dr Dd (fun x e1 e2 => Ap x e2 e1) rfl
    (by simp [jmp0]; have := S2.bo1; omega) (by simp [jmp0]; omega)
    (fun x d => by
      rcases dd3 x d with d | ⟨-, n1, n2⟩
      · have lt := S2.defd_lt d
        refine ⟨fun e => ?_, fun e => ?_⟩
        · rcases mr x e with e' | e'
          · exact nf2 x e' d
          · omega
        · rcases md x e with e' | e'
          · exact nf2 x e' d
          · omega
      · exact ⟨n2, n1⟩) (ch := CI.2) (ct := CI.1) h4 h5 hr
  refine ⟨S1, a1, lo1, hi1, fun x hx => ?_⟩
  obtain ⟨hl, n1, n2⟩ := L1 x hx
  rcases L3 x hl with e | e | ⟨hl', hn'⟩
  · exact absurd e n2
  · exact absurd e n1
  · rcases L2 x hl' with e | e
    · exact absurd e hn'
    · exact e

end Raw
end SkaModel
end Formalization
