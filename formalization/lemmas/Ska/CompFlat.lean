import lemmas.Ska.CompFrontS

/-!
# Flat lazy needs: `+split` and `+copy` over their bonds

README Gaps 12.24.  In the plain class (no `%6`, no direct call, no hint)
every lazy need is flat: no fork, and every bond's need is itself fork- and
bond-free (`+past` lifts a need's bonds to the top, the leaves return
fork-free needs).  On flat needs the arms that walk the bonds are short:

* `Flat`, `entries_flat` (the entries are the bonds).
* `preBody`, `Pref` (the state grew only by registers and by ops put in
  front of some blocks), `Pref.trans`, `pref_addOps`, `pref_re`.
* `splitSure_ok`: `+split-sure` with the ops it puts at its block, the
  halves' registers, cleanliness, shape and semantics.
* `SplitBs`, `splitBonds_flat`, `SplitBs.spec`: `+split`'s loop over flat
  bonds splits each bond's need at its own block.
* `splitLoop_flat`, `splitL_flat`: `+split` of a flat need.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Flat needs -/

/-- **A flat lazy need**: no fork, every bond's need fork- and bond-free. -/
def Flat (l : Lazy S) : Prop := l.fork = [] ∧ ∀ e ∈ l.bond, e.2 = ofSure e.2.sure

/-- Flat bonds. -/
def FlatB (b : List (Nat × Lazy S)) : Prop := ∀ e ∈ b, e.2 = ofSure e.2.sure

theorem flatB_nil : FlatB ([] : List (Nat × Lazy S)) := fun e he => by cases he

theorem bondEntries_flat : ∀ (b : List (Nat × Lazy S)), FlatB b → bondEntries b = b
  | [], _ => rfl
  | (o, l) :: rest, h => by
    have e : entries l = [] := by
      have h0 := h (o, l) List.mem_cons_self
      simp only at h0
      rw [h0]; exact entries_ofSure _
    simp only [bondEntries, e, List.cons_append, List.nil_append]
    rw [bondEntries_flat rest (fun e he => h e (List.mem_cons_of_mem _ he))]

theorem entries_flat {l : Lazy S} (h : Flat l) : entries l = l.bond := by
  rcases l with ⟨s, f, b⟩
  simp only [Flat, fork_mk, bond_mk] at h
  obtain ⟨rfl, hb⟩ := h
  simp [entries, forkEntries, bondEntries_flat b hb]

theorem flat_ofSure (s : Sure S) : Flat (ofSure s) := ⟨rfl, fun e he => by cases he⟩

theorem flat_mk {s : Sure S} {b : List (Nat × Lazy S)} (h : FlatB b) : Flat (mk s [] b) := ⟨rfl, h⟩

/-! ## The state grew by ops in front of blocks -/

/-- The block `b` with the ops `A` in front of its body. -/
def preBody (A : List Pole) (b : Blob) : Blob := { b with body := A ++ b.body }

@[simp] theorem preBody_nil (b : Blob) : preBody [] b = b := by cases b; rfl

theorem preBody_preBody (A B : List Pole) (b : Blob) : preBody A (preBody B b) = preBody (A ++ B) b := by
  cases b; simp [preBody]

theorem preBody_mk (A B : List Pole) (fin : Termin) : preBody A ⟨[], B, fin⟩ = ⟨[], A ++ B, fin⟩ := rfl

/-- **The state grew only by registers and by the ops `P k` in front of the
block at each label `k`.** -/
structure Pref (g g' : Gen Map) (P : Nat → List Pole) : Prop where
  bo : g'.bo = g.bo
  drop : g'.drop = g.drop
  re : g.re ≤ g'.re
  cond : g'.cond = g.cond
  get : ∀ k, HoonMap.get g'.blocks k = (HoonMap.get g.blocks k).map (preBody (P k))

theorem Pref.refl (g : Gen Map) : Pref g g (fun _ => []) :=
  ⟨rfl, rfl, Nat.le_refl _, rfl, fun k => by cases HoonMap.get g.blocks k <;> simp⟩

theorem Pref.trans {g1 g2 g3 : Gen Map} {P P' : Nat → List Pole} (a : Pref g1 g2 P) (b : Pref g2 g3 P') :
    Pref g1 g3 (fun k => P' k ++ P k) :=
  ⟨b.bo.trans a.bo, b.drop.trans a.drop, Nat.le_trans a.re b.re, b.cond.trans a.cond, fun k => by
    rw [b.get k, a.get k]; cases HoonMap.get g1.blocks k <;> simp [preBody_preBody]⟩

theorem Pref.congr {g g' : Gen Map} {P P' : Nat → List Pole} (a : Pref g g' P) (h : ∀ k, P k = P' k) :
    Pref g g' P' := ⟨a.bo, a.drop, a.re, a.cond, fun k => by rw [a.get k, h k]⟩

theorem pref_re {g g' : Gen Map} (h : g' = { g with re := g'.re }) (hl : g.re ≤ g'.re) : Pref g g' (fun _ => []) := by
  rw [h]; exact ⟨rfl, rfl, hl, rfl, fun k => by cases HoonMap.get g.blocks k <;> simp⟩

theorem pref_addOps {o : Nat} {ops : List Pole} {g g' : Gen Map} {u : Unit} (h : addOps o ops g = some (u, g'))
    (hd : g.drop = false) : Pref g g' (fun k => if k = o then ops else []) := by
  obtain ⟨b, hb, rfl⟩ := addOps_spec h hd
  refine ⟨rfl, rfl, Nat.le_refl _, rfl, fun k => ?_⟩
  simp only [HoonMap.get_put]
  by_cases e : k = o
  · subst e; simp [hb, preBody]
  · simp only [e, if_false]; cases HoonMap.get g.blocks k <;> simp

theorem Pref.blk {g g' : Gen Map} {P : Nat → List Pole} (h : Pref g g' P) {k : Nat} {B : List Pole} {fin : Termin}
    (hb : HoonMap.get g.blocks k = some ⟨[], B, fin⟩) : HoonMap.get g'.blocks k = some ⟨[], P k ++ B, fin⟩ := by
  rw [h.get k, hb]; rfl

theorem Pref.same {g g' : Gen Map} {P : Nat → List Pole} (h : Pref g g' P) {k : Nat} (hk : P k = []) :
    HoonMap.get g'.blocks k = HoonMap.get g.blocks k := by
  rw [h.get k, hk]; cases HoonMap.get g.blocks k <;> simp

theorem Pref.ext {g g' : Gen Map} {P : Nat → List Pole} (h : Pref g g' P) (hP : ∀ k, k < g.bo → P k = []) :
    Ext g g' :=
  ⟨h.re, by have := h.bo; omega, h.drop, fun o ho => h.same (hP o ho)⟩

theorem Pref.growU {g g' : Gen Map} {P : Nat → List Pole} (h : Pref g g' P) : GrowU g g' := by
  refine ⟨by have := h.bo; omega, h.drop, fun k b _ hb => ⟨preBody (P k) b, by rw [h.get k, hb]; rfl, rfl, rfl⟩,
    fun k b' hb' => ?_⟩
  rw [h.get k] at hb'
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hb'
  exact Or.inl ⟨b, hb, rfl, rfl⟩

theorem Pref.condFresh {g g' : Gen Map} {P : Nat → List Pole} (h : Pref g g' P) : CondFresh g g' :=
  ⟨h.re, fun k => Or.inl (by rw [h.cond])⟩

theorem Pref.upAt {g g' : Gen Map} {P : Nat → List Pole} (h : Pref g g' P) (u t : Nat) :
    UpAt g'.blocks u t ↔ UpAt g.blocks u t := by
  constructor
  · rintro ⟨b', j, hb', hf, ht, hl⟩
    rw [h.get u] at hb'
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hb'
    exact ⟨b, j, hb, hf, ht, hl⟩
  · rintro ⟨b, j, hb, hf, ht, hl⟩
    exact ⟨preBody (P u) b, j, by rw [h.get u, hb]; rfl, hf, ht, hl⟩

theorem Pref.upBelow {g g' : Gen Map} {P : Nat → List Pole} (h : Pref g g' P) (hu : UpBelow g) : UpBelow g' :=
  fun u t hut => by rw [h.bo]; exact hu u t ((h.upAt u t).mp hut)

theorem Pref.clear {g g' : Gen Map} {P : Nat → List Pole} (h : Pref g g' P) (hc : Clear g) : Clear g' :=
  fun k hk => by rw [h.get k, hc k (by rw [← h.bo]; exact hk)]; rfl

theorem Pref.condBelow {g g' : Gen Map} {P : Nat → List Pole} (h : Pref g g' P) (hc : CondBelow g) : CondBelow g' :=
  h.condFresh.below hc

theorem Pref.fresh {g g' : Gen Map} {P : Nat → List Pole} (h : Pref g g' P) {j : Jmp} (hj : Fresh g j) : Fresh g' j := by
  obtain ⟨b, hb, hp, ha⟩ := hj
  exact ⟨preBody (P j.there) b, by rw [h.get, hb]; rfl, hp, ha⟩

theorem Pref.entry {g g' : Gen Map} {P : Nat → List Pole} (h : Pref g g' P) {goal : CGoal S} {j : Jmp}
    (hj : Entry g goal j) : Entry g' goal j := hj.imp h.fresh id

/-! ## `+split-sure` -/

theorem splitNeed_pref {ned : Need} {o : Nat} {g g' : Gen Map} {x : Need × Need}
    (h : splitNeed ned o g = some (x, g')) (hd : g.drop = false) :
    ∃ A, Pref g g' (fun k => if k = o then A else []) ∧
      ∀ (Pr : Nat → Prop), NA Pr ned → Ple Pr g.re → RegsIn Pr A := by
  cases ned with
  | pair p q =>
    simp only [splitNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], (Pref.refl g).congr (fun k => by split <;> rfl), fun _ _ _ => RegsIn.nil _⟩
  | none =>
    simp only [splitNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], (Pref.refl g).congr (fun k => by split <;> rfl), fun _ _ _ => RegsIn.nil _⟩
  | this r =>
    simp only [splitNeed, bind_apply, re_apply, Option.bind_some] at h
    obtain ⟨⟨_, g1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have P0 : Pref g { { g with re := g.re + 1 } with re := g.re + 1 + 1 } (fun _ => []) :=
      pref_re rfl (by simp only; omega)
    exact ⟨[Pole.con g.re (g.re + 1) r], (P0.trans (pref_addOps h1 hd)).congr (fun k => by simp),
      fun Pr hn hm => regsIn_con (hm _ (Nat.le_refl _)) (hm _ (Nat.le_succ _)) (hn r rfl) (RegsIn.nil _)⟩
  | both r hh t =>
    simp only [splitNeed] at h
    obtain ⟨⟨r1, n1⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨⟨r2, n2⟩, g2, h2, h⟩ := bind_some h
    obtain ⟨_, g3, h3, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨G1, L1, -⟩ := must_spec h1
    obtain ⟨G2, L2, -⟩ := must_spec h2
    have d2 : g2.drop = false := by rw [G2, G1]; exact hd
    refine ⟨[Pole.con r1 r2 r], (((pref_re G1 L1).trans (pref_re G2 L2)).trans (pref_addOps h3 d2)).congr
      (fun k => by simp), fun Pr hn hm => ?_⟩
    obtain ⟨-, -, p1⟩ := keepsA_must (fun y hy => hn y (Or.inr (Or.inl hy))) hm h1
    obtain ⟨-, -, p2⟩ := keepsA_must (fun y hy => hn y (Or.inr (Or.inr hy))) (ple_trans hm L1) h2
    exact regsIn_con p1 p2 (hn r (Or.inl rfl)) (RegsIn.nil _)

/-- **`+split-sure`**: the ops `A` it puts at its block `o`, the halves'
registers, their cleanliness, and, for a distinct need allocated before,
the halves' shape and the ops' semantics. -/
theorem splitSure_ok {s : Sure S} {o : Nat} {g g' : Gen Map} {sh st : Sure S}
    (h : splitSure s o g = some ((sh, st), g')) (hd : g.drop = false) {B0 : List Pole} {fin0 : Termin}
    (hb : HoonMap.get g.blocks o = some ⟨[], B0, fin0⟩) :
    ∃ A, Pref g g' (fun k => if k = o then A else []) ∧
      (∀ y, NMem sh.ned y → NMem s.ned y ∨ (g.re ≤ y ∧ y < g'.re)) ∧
      (∀ y, NMem st.ned y → NMem s.ned y ∨ (g.re ≤ y ∧ y < g'.re)) ∧
      (Clean s.ned → Clean sh.ned ∧ Clean st.ned) ∧
      (∀ (Pr : Nat → Prop), NA Pr s.ned → Ple Pr g.re → RegsIn Pr A) ∧
      (Distinct s.ned → (∀ y, NMem s.ned y → y < g.re) →
        Distinct sh.ned ∧ Distinct st.ned ∧ (∀ y, NMem sh.ned y → ¬ NMem st.ned y) ∧
        (∀ a b, FitsS s (C a b) ↔ FitsS sh a ∧ FitsS st b) ∧
        ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st' : σ) (t : Trace)
          (R : Map (Option Noun)) (a b : Noun), HoldsN sh.ned R a → HoldsN st.ned R b →
          ∃ R', Runs lib O c gul st' t A R R' ∧ HoldsN s.ned R' (C a b) ∧
            ∀ y, ¬ NMem s.ned y → SkaModel.read y R' = SkaModel.read y R) := by
  have hc : g'.cond = g.cond := (kc_splitSure s o).keep g _ g' h
  simp only [splitSure] at h
  obtain ⟨⟨lh, lt⟩, hl, h2⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨⟨nh, nt⟩, g2⟩, h3, h4⟩ := Option.map_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
  obtain ⟨eb, ed, er, eo, M1, M2, D, SB⟩ := splitNeed_spec h3
  obtain ⟨A', P', RA⟩ := splitNeed_pref h3 hd
  obtain ⟨A, Fr, Sm⟩ := SB hd
  have eA : A' = A := by
    have h1 := P'.blk hb
    have h2 := Fr.blk B0 fin0 hb
    simp only [if_true] at h1
    rw [h1] at h2
    simp only [Option.some.injEq, Blob.mk.injEq, true_and] at h2
    exact List.append_cancel_right h2.1
  subst eA
  refine ⟨A', P', M1, M2, fun hcl => clean_splitNeed h3 hcl, RA, fun d lo => ?_⟩
  obtain ⟨Dh, Dt, Dht, F⟩ := D d lo
  refine ⟨Dh, Dt, Dht, fun a b => ?_, fun lib σ O c gul st' t R a b ha hb' => Sm d lo lib σ O c gul st' t R a b ha hb'⟩
  simp only [FitsS, F a b, splitLok_looks hl a b]
  exact ⟨fun ⟨⟨x, y⟩, z, w⟩ => ⟨⟨x, z⟩, y, w⟩, fun ⟨⟨x, z⟩, y, w⟩ => ⟨⟨x, y⟩, z, w⟩⟩

/-! ## The loop of `+split` over flat bonds -/

/-- **`+split`'s loop over flat bonds**: each bond's need split at its own
block, the states threaded. -/
inductive SplitBs : List (Nat × Lazy S) → List (Nat × Lazy S) → List (Nat × Lazy S) → Gen Map → Gen Map → Prop
  | nil (g : Gen Map) : SplitBs [] [] [] g g
  | cons {o : Nat} {s sh st : Sure S} {rest rh rt : List (Nat × Lazy S)} {g g1 g2 : Gen Map} :
      splitSure s o g = some ((sh, st), g1) → SplitBs rest rh rt g1 g2 →
      SplitBs ((o, ofSure s) :: rest) ((o, ofSure sh) :: rh) ((o, ofSure st) :: rt) g g2

theorem splitBonds_flat : ∀ (b : List (Nat × Lazy S)) (g g' : Gen Map) (r : List (Nat × Lazy S) × List (Nat × Lazy S)),
    FlatB b → splitBonds b g = some (r, g') → SplitBs b r.1 r.2 g g'
  | [], g, g', r, _, h => by
    simp only [splitBonds, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact SplitBs.nil g
  | (o, l) :: rest, g, g', r, hf, h => by
    have el : l = ofSure l.sure := hf (o, l) List.mem_cons_self
    rw [splitBonds] at h
    obtain ⟨⟨lh, lt⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨⟨rh, rt⟩, g2, h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [el, splitLoop_ofSure] at h1
    obtain ⟨⟨sh, st⟩, g3, h3, h1⟩ := bind_some h1
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h1
    have ih := splitBonds_flat rest _ _ (rh, rt) (fun e he => hf e (List.mem_cons_of_mem _ he)) h2
    rw [el]
    exact SplitBs.cons h3 ih

/-- **What `+split`'s loop over flat bonds does**: the same labels on both
halves; at each bond's block, the ops of `+split-sure` of its need in
front, from a state between the two; nothing else but registers. -/
theorem SplitBs.spec {b bh bt : List (Nat × Lazy S)} {g g' : Gen Map} (h : SplitBs b bh bt g g')
    (hd : g.drop = false) (hn : (b.map Prod.fst).Nodup)
    (hb : ∀ e ∈ b, ∃ B fin, HoonMap.get g.blocks e.1 = some ⟨[], B, fin⟩) :
    bh.map Prod.fst = b.map Prod.fst ∧ bt.map Prod.fst = b.map Prod.fst ∧ FlatB bh ∧ FlatB bt ∧
    ∃ P : Nat → List Pole, Pref g g' P ∧ (∀ k, k ∉ b.map Prod.fst → P k = []) ∧
      ∀ e ∈ b, ∃ (s sh st : Sure S) (g1 g2 : Gen Map), e.2 = ofSure s ∧ (e.1, ofSure sh) ∈ bh ∧ (e.1, ofSure st) ∈ bt ∧
        g.re ≤ g1.re ∧ g2.re ≤ g'.re ∧ g1.drop = false ∧
        (∀ B fin, HoonMap.get g.blocks e.1 = some ⟨[], B, fin⟩ → HoonMap.get g1.blocks e.1 = some ⟨[], B, fin⟩) ∧
        splitSure s e.1 g1 = some ((sh, st), g2) ∧
        (∀ A, Pref g1 g2 (fun k => if k = e.1 then A else []) → P e.1 = A) := by
  induction h with
  | nil g =>
    exact ⟨rfl, rfl, flatB_nil, flatB_nil, fun _ => [], Pref.refl g, fun _ _ => rfl, fun e he => by cases he⟩
  | @cons o s sh st rest rh rt g g1 g2 h1 hr ih =>
    have hn' : (rest.map Prod.fst).Nodup := (List.nodup_cons.mp hn).2
    have ho : o ∉ rest.map Prod.fst := (List.nodup_cons.mp hn).1
    obtain ⟨B0, fin0, hb0⟩ := hb (o, ofSure s) List.mem_cons_self
    obtain ⟨A, P1, -⟩ := splitSure_ok h1 hd hb0
    have d1 : g1.drop = false := P1.drop.trans hd
    have hb1 : ∀ e ∈ rest, ∃ B fin, HoonMap.get g1.blocks e.1 = some ⟨[], B, fin⟩ := fun e he => by
      obtain ⟨B, fin, hbe⟩ := hb e (List.mem_cons_of_mem _ he)
      exact ⟨_, fin, P1.blk hbe⟩
    obtain ⟨eh, et, fh, ft, P, PP, Pout, Pin⟩ := ih d1 hn' hb1
    refine ⟨by simp [eh], by simp [et], ?_, ?_, fun k => P k ++ (if k = o then A else []), P1.trans PP,
      fun k hk => ?_, fun e he => ?_⟩
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · rfl
      · exact fh e he
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · rfl
      · exact ft e he
    · simp only [List.map_cons, List.mem_cons, not_or] at hk
      show P k ++ (if k = o then A else []) = []
      rw [Pout k hk.2, if_neg hk.1]; rfl
    · rcases List.mem_cons.mp he with rfl | he
      · refine ⟨s, sh, st, g, g1, rfl, List.mem_cons_self, List.mem_cons_self, Nat.le_refl _,
          PP.re, hd, fun B fin h => h, h1, fun A' PA' => ?_⟩
        dsimp only
        rw [Pout o ho, List.nil_append]
        simp only [if_true]
        have a1 := PA'.blk hb0
        have a2 := P1.blk hb0
        simp only [if_true] at a1 a2
        rw [a1] at a2
        simp only [Option.some.injEq, Blob.mk.injEq, true_and] at a2
        exact (List.append_cancel_right a2.1).symm
      · obtain ⟨s', sh', st', g1', g2', es, mh, mt, l1, l2, dd, bb, sp, pp⟩ := Pin e he
        have hne : e.1 ≠ o := fun x => ho (x ▸ List.mem_map_of_mem he)
        refine ⟨s', sh', st', g1', g2', es, List.mem_cons_of_mem _ mh, List.mem_cons_of_mem _ mt,
          Nat.le_trans P1.re l1, l2, dd, fun B fin hB => bb B fin (by rw [P1.same (by simp [hne])]; exact hB), sp,
          fun A' PA' => by dsimp only; rw [pp A' PA', if_neg hne, List.append_nil]⟩

/-! ## `+split` of a flat need -/

theorem lazyPrune_flat {s : Sure S} {b : List (Nat × Lazy S)} :
    lazyPrune (mk s [] b) = mk s [] (b.filter fun e => !(lazyEmpty e.2)) := by
  simp [lazyPrune]

theorem splitLoop_flat {s : Sure S} {b : List (Nat × Lazy S)} (hf : FlatB b) {o : Nat} {g g' : Gen Map}
    {x : Lazy S × Lazy S} (h : splitLoop (mk s [] b) o g = some (x, g')) :
    ∃ (sh st : Sure S) (g1 : Gen Map) (bh bt : List (Nat × Lazy S)), splitSure s o g = some ((sh, st), g1) ∧ SplitBs b bh bt g1 g' ∧
      x = (mk sh [] (bh.filter fun e => !(lazyEmpty e.2)), mk st [] (bt.filter fun e => !(lazyEmpty e.2))) := by
  rw [splitLoop] at h
  obtain ⟨⟨sh, st⟩, g1, h1, h⟩ := bind_some h
  by_cases e : b = []
  · subst e
    simp only [List.isEmpty_nil, Bool.and_self, if_true, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨sh, st, g1, [], [], h1, SplitBs.nil g1, by simp [ofSure]⟩
  · have e' : (List.isEmpty ([] : List (ForkE S)) && b.isEmpty) = false := by
      simp only [List.isEmpty_nil, Bool.true_and]; exact List.isEmpty_eq_false_iff.mpr e
    simp only [fork_mk, bond_mk, e', Bool.false_eq_true, if_false] at h
    obtain ⟨⟨fh, ft⟩, g2, h2, h⟩ := bind_some h
    rw [splitForks, pure_apply] at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
    obtain ⟨⟨bh, bt⟩, g3, h3, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨sh, st, g1, bh, bt, h1, splitBonds_flat b g1 _ (bh, bt) hf h3, by simp [lazyPrune]⟩

end Comp
end SkaModel
end Formalization
