import lemmas.Ska.CompGenLeaf
import lemmas.Ska.CompConsCall

/-!
# The cons in `RunOKGen`: `+split` per label

README Gaps 12.39, item 10.  The cons `[p q]` under `%next L th` begins with
`+split` (`splitL`): a fresh block `o` hopping to `th`, then `splitLoop` of
the goal's need at `o`, each fork's and bond's need split at its own label
(`+split-sure` puts the ops of `+split-need` in front of that block), the
halves pruned (`+lazy-prune` drops the children that ask nothing).  At a goal
with repeated labels several entries share one block, so the spec is stated
per label, in the pattern of `WalkOKL` (`CompGenTop.lean`): at every label
the ops in front are one piece per entry there (up to a permutation), and the
halves' needs there are the pieces' halves, some trivial ones dropped.

* `TrivS`, `DropT` (a list with trivial needs dropped, up to a permutation),
  `DropA` (the same at every label), with `refl`, `append`, `trans`, `perm`.
* `prune_dropA`: `+lazy-prune` drops only trivial entries.
* `SplitP` (one piece: the need, its halves, the ops, `splitSure_ok`'s
  conclusions), `SplitP.mono`.
* `SplitOKL` (the split per label) with `nil`, `trans`, `perm`, `dropH`,
  `dropT`, `drop`, `blk`, `base`; **`splitLoop_okL`** (mutual with
  `splitForks_okL`, `splitBonds_okL`), **`splitL_okL`**.
* `splitPieces_run`, **`SplitOKL.runAt`**: at one label, from the halves'
  needs held by `a` and `b`, the ops in front build every goal need there
  for `[a b]` and keep every other register (no `Nodup`: the needs at a
  label are apart, `LabDisj`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Trivial needs and dropped lists -/

/-- A need that asks nothing: what `+lazy-prune` drops. -/
def TrivS (s : Sure S) : Prop := s.ned = Need.none ∧ HoonSet.small s.lok = true

/-- `l'` is `l` with some trivial needs dropped, up to a permutation. -/
def DropT (l l' : List (Sure S)) : Prop := ∃ k : List (Sure S), (l' ++ k).Perm l ∧ ∀ s ∈ k, TrivS s

theorem DropT.refl (l : List (Sure S)) : DropT l l := ⟨[], by simp, fun _ h => by simp at h⟩

theorem DropT.ofPerm {l l' : List (Sure S)} (h : l'.Perm l) : DropT l l' := ⟨[], by simpa using h, fun _ h => by simp at h⟩

theorem DropT.append {a a' b b' : List (Sure S)} (ha : DropT a a') (hb : DropT b b') : DropT (a ++ b) (a' ++ b') := by
  obtain ⟨k1, p1, t1⟩ := ha
  obtain ⟨k2, p2, t2⟩ := hb
  refine ⟨k1 ++ k2, ?_, fun s hs => (List.mem_append.mp hs).elim (t1 s) (t2 s)⟩
  have q : List.Perm ((b' ++ k1) ++ k2) (k1 ++ (b' ++ k2)) := by
    rw [← List.append_assoc]; exact List.perm_append_comm.append_right k2
  have e1 : (a' ++ b') ++ (k1 ++ k2) = a' ++ ((b' ++ k1) ++ k2) := by simp
  have e2 : a' ++ (k1 ++ (b' ++ k2)) = (a' ++ k1) ++ (b' ++ k2) := by simp
  rw [e1]
  exact ((q.append_left a').trans (by rw [e2])).trans (p1.append p2)

theorem DropT.trans {a b c : List (Sure S)} (h1 : DropT a b) (h2 : DropT b c) : DropT a c := by
  obtain ⟨k1, p1, t1⟩ := h1
  obtain ⟨k2, p2, t2⟩ := h2
  refine ⟨k2 ++ k1, ?_, fun s hs => (List.mem_append.mp hs).elim (t2 s) (t1 s)⟩
  rw [← List.append_assoc]
  exact (p2.append_right k1).trans p1

theorem DropT.perm_left {a a' b : List (Sure S)} (h : DropT a b) (hp : a.Perm a') : DropT a' b :=
  let ⟨k, p, t⟩ := h; ⟨k, p.trans hp, t⟩

theorem DropT.perm_right {a b b' : List (Sure S)} (h : DropT a b) (hp : b.Perm b') : DropT a b' :=
  let ⟨k, p, t⟩ := h; ⟨k, (hp.symm.append_right k).trans p, t⟩

/-- **`DropT` at every label.** -/
def DropA (es es' : List (Nat × Lazy S)) : Prop := ∀ k, DropT (atL es k) (atL es' k)

theorem atL_perm {es es' : List (Nat × Lazy S)} (h : es.Perm es') (k : Nat) : (atL es k).Perm (atL es' k) :=
  (h.filter _).map _

theorem atL_cons_sure (o : Nat) (l l' : Lazy S) (hs : l.sure = l'.sure) (es : List (Nat × Lazy S)) (k : Nat) :
    atL ((o, l) :: es) k = atL ((o, l') :: es) k := by
  by_cases h : o = k <;> simp [atL, List.filter_cons, h, hs]

theorem atL_single (o : Nat) (l : Lazy S) (k : Nat) : atL [(o, l)] k = if o = k then [l.sure] else [] := by
  by_cases h : o = k <;> simp [atL, List.filter_cons, h]

theorem DropA.refl (es : List (Nat × Lazy S)) : DropA es es := fun _ => DropT.refl _

theorem DropA.ofPerm {es es' : List (Nat × Lazy S)} (h : es'.Perm es) : DropA es es' :=
  fun k => DropT.ofPerm (atL_perm h k)

theorem DropA.append {a a' b b' : List (Nat × Lazy S)} (ha : DropA a a') (hb : DropA b b') :
    DropA (a ++ b) (a' ++ b') := fun k => by
  rw [atL_append, atL_append]; exact (ha k).append (hb k)

theorem DropA.trans {a b c : List (Nat × Lazy S)} (h1 : DropA a b) (h2 : DropA b c) : DropA a c :=
  fun k => (h1 k).trans (h2 k)

theorem DropA.cons {o : Nat} {l l' : Lazy S} (hs : l.sure = l'.sure) {es es' : List (Nat × Lazy S)}
    (h : DropA es es') : DropA ((o, l) :: es) ((o, l') :: es') := by
  intro k
  have := (DropA.refl [(o, l)]).append h k
  rw [atL_cons_sure o l' l hs.symm]
  exact this

/-- Entries dropped by `DropA` are trivial: an entry list with only trivial
entries appended. -/
theorem DropA.ofTriv {es es' k : List (Nat × Lazy S)} (hp : (es' ++ k).Perm es) (ht : ∀ e ∈ k, TrivS e.2.sure) :
    DropA es es' := by
  intro o
  refine ⟨atL k o, ?_, fun s hs => ?_⟩
  · rw [← atL_append]; exact atL_perm hp o
  · unfold atL at hs
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hs
    exact ht e (List.mem_filter.mp he).1

theorem lazyEmpty_spec {l : Lazy S} (h : lazyEmpty l = true) : TrivS l.sure ∧ entries l = [] := by
  rcases l with ⟨s, f, b⟩
  simp only [lazyEmpty, Bool.and_eq_true, List.isEmpty_iff, sure_mk, fork_mk, bond_mk] at h
  obtain ⟨⟨⟨h1, h2⟩, rfl⟩, rfl⟩ := h
  exact ⟨⟨of_decide_eq_true h1, h2⟩, by simp [entries, bondEntries, forkEntries]⟩

theorem prune_bonds : ∀ (b : List (Nat × Lazy S)), ∃ k : List (Nat × Lazy S),
    (bondEntries (b.filter fun e => !(lazyEmpty e.2)) ++ k).Perm (bondEntries b) ∧ ∀ e ∈ k, TrivS e.2.sure
  | [] => ⟨[], by simp [bondEntries], fun _ h => by simp at h⟩
  | (o, l) :: rest => by
    obtain ⟨k, p, t⟩ := prune_bonds rest
    cases hl : lazyEmpty l with
    | true =>
      obtain ⟨tl, el⟩ := lazyEmpty_spec hl
      refine ⟨(o, l) :: k, ?_, fun e he => ?_⟩
      · simp only [List.filter_cons, hl, Bool.not_true, Bool.false_eq_true, if_false, bondEntries, el,
          List.singleton_append, List.cons_append]
        exact List.perm_middle.trans (p.cons _)
      · rcases List.mem_cons.mp he with rfl | he
        · exact tl
        · exact t e he
    | false =>
      refine ⟨k, ?_, t⟩
      simp only [List.filter_cons, hl, Bool.not_false, if_true, bondEntries, List.append_assoc]
      exact p.append_left _

theorem prune_forks : ∀ (f : List (ForkE S)), ∃ k : List (Nat × Lazy S),
    (forkEntries (f.filter fun e => !(lazyEmpty e.1.2 && lazyEmpty e.2.2)) ++ k).Perm (forkEntries f) ∧
      ∀ e ∈ k, TrivS e.2.sure
  | [] => ⟨[], by simp [forkEntries], fun _ h => by simp at h⟩
  | ((oy, y), (on, n)) :: rest => by
    obtain ⟨k, p, t⟩ := prune_forks rest
    cases hl : (lazyEmpty y && lazyEmpty n) with
    | true =>
      simp only [Bool.and_eq_true] at hl
      obtain ⟨ty, ey⟩ := lazyEmpty_spec hl.1
      obtain ⟨tn, en⟩ := lazyEmpty_spec hl.2
      have hl' : (lazyEmpty y && lazyEmpty n) = true := by simp [hl.1, hl.2]
      refine ⟨(oy, y) :: (on, n) :: k, ?_, fun e he => ?_⟩
      · simp only [List.filter_cons, hl', Bool.not_true, Bool.false_eq_true, if_false, forkEntries, ey, en,
          List.singleton_append, List.cons_append, List.nil_append]
        exact List.perm_middle.trans ((List.perm_middle.trans (p.cons _)).cons _)
      · rcases List.mem_cons.mp he with rfl | he
        · exact ty
        · rcases List.mem_cons.mp he with rfl | he
          · exact tn
          · exact t e he
    | false =>
      refine ⟨k, ?_, t⟩
      simp only [List.filter_cons, hl, Bool.not_false, if_true, forkEntries, List.append_assoc]
      exact List.Perm.append_left _ (List.Perm.append_left _ p)

/-- **`+lazy-prune` drops only trivial entries.** -/
theorem prune_dropA (l : Lazy S) : DropA (entries l) (entries (lazyPrune l)) := by
  rcases l with ⟨s, f, b⟩
  obtain ⟨kb, pb, tb⟩ := prune_bonds b
  obtain ⟨kf, pf, tf⟩ := prune_forks f
  refine DropA.ofTriv (k := kb ++ kf) ?_ (fun e he => (List.mem_append.mp he).elim (tb e) (tf e))
  simp only [lazyPrune, entries, sure_mk, fork_mk, bond_mk]
  have q : List.Perm ((bondEntries (b.filter fun e => !(lazyEmpty e.2)) ++
      forkEntries (f.filter fun e => !(lazyEmpty e.1.2 && lazyEmpty e.2.2))) ++ (kb ++ kf))
      ((bondEntries (b.filter fun e => !(lazyEmpty e.2)) ++ kb) ++
      (forkEntries (f.filter fun e => !(lazyEmpty e.1.2 && lazyEmpty e.2.2)) ++ kf)) := by
    simp only [List.append_assoc]
    exact List.Perm.append_left _ (by
      rw [← List.append_assoc, ← List.append_assoc]
      exact List.perm_append_comm.append_right kf)
  exact q.trans (pb.append pf)

/-! ## One piece of `+split` -/

/-- A piece: the need, its head and tail halves, and the ops in front. -/
abbrev SplitE (S : Type) := Sure S × Sure S × Sure S × List Pole

/-- **What `+split-sure` did for one need** (`splitSure_ok`), its fresh
registers in `[lo, hi)`. -/
structure SplitP (lo hi : Nat) (p : SplitE S) : Prop where
  mh : ∀ y, NMem p.2.1.ned y → NMem p.1.ned y ∨ (lo ≤ y ∧ y < hi)
  mt : ∀ y, NMem p.2.2.1.ned y → NMem p.1.ned y ∨ (lo ≤ y ∧ y < hi)
  ra : ∀ (Pr : Nat → Prop), NA Pr p.1.ned → Ple Pr lo → RegsIn Pr p.2.2.2
  rb : NB lo p.1.ned → RegsIn (· < hi) p.2.2.2
  sem : Distinct p.1.ned → (∀ y, NMem p.1.ned y → y < lo) →
    Distinct p.2.1.ned ∧ Distinct p.2.2.1.ned ∧ (∀ y, NMem p.2.1.ned y → ¬ NMem p.2.2.1.ned y) ∧
    (∀ a b, FitsS p.1 (C a b) ↔ FitsS p.2.1 a ∧ FitsS p.2.2.1 b) ∧
    ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st' : σ) (t : Trace)
      (R : Map (Option Noun)) (a b : Noun), HoldsN p.2.1.ned R a → HoldsN p.2.2.1.ned R b →
      ∃ R', Runs lib O c gul st' t p.2.2.2 R R' ∧ HoldsN p.1.ned R' (C a b) ∧
        ∀ y, ¬ NMem p.1.ned y → SkaModel.read y R' = SkaModel.read y R
  cl : Clean p.1.ned → Clean p.2.1.ned ∧ Clean p.2.2.1.ned

theorem SplitP.mono {lo hi lo' hi' : Nat} {p : SplitE S} (h : SplitP (Map := Map) lo hi p) (e1 : lo' ≤ lo)
    (e2 : hi ≤ hi') : SplitP (Map := Map) lo' hi' p := by
  refine ⟨fun y hy => ?_, fun y hy => ?_, fun Pr hn hm => h.ra Pr hn (ple_trans hm e1),
    fun hb q hq x hx => Nat.lt_of_lt_of_le (h.rb (fun r hr => Nat.lt_of_lt_of_le (hb r hr) e1) q hq x hx) e2,
    fun d l => h.sem d (fun y hy => Nat.lt_of_lt_of_le (l y hy) e1), h.cl⟩
  · rcases h.mh y hy with a | a
    · exact Or.inl a
    · exact Or.inr ⟨by omega, by omega⟩
  · rcases h.mt y hy with a | a
    · exact Or.inl a
    · exact Or.inr ⟨by omega, by omega⟩

/-! ## `+split` per label -/

/-- **`+split` per label**: the state grew by registers and by ops `P k` in
front of the block at each label of `es`; at every label they are one piece
per entry of `es` there (up to a permutation), whose halves are the needs of
`hs` and `ts` there, some trivial ones dropped. -/
def SplitOKL (g g' : Gen Map) (es hs ts : List (Nat × Lazy S)) : Prop :=
  ∃ P : Nat → List Pole, Pref g g' P ∧ (∀ k, k ∉ es.map Prod.fst → P k = []) ∧
    ∀ k, ∃ ps : List (SplitE S), P k = (ps.map fun p => p.2.2.2).flatten ∧
      (ps.map fun p => p.1).Perm (atL es k) ∧ DropT (ps.map fun p => p.2.1) (atL hs k) ∧
      DropT (ps.map fun p => p.2.2.1) (atL ts k) ∧ ∀ p ∈ ps, SplitP (Map := Map) g.re g'.re p

theorem SplitOKL.nil (g : Gen Map) : SplitOKL (S := S) g g [] [] [] :=
  ⟨fun _ => [], Pref.refl g, fun _ _ => rfl, fun k => ⟨[], rfl, by simp [atL], by simp [atL, DropT.refl],
    by simp [atL, DropT.refl], fun _ h => by simp at h⟩⟩

theorem SplitOKL.drop {g g' : Gen Map} {es hs ts : List (Nat × Lazy S)} (h : SplitOKL g g' es hs ts) :
    g'.drop = g.drop := let ⟨_, P, _⟩ := h; P.drop

theorem SplitOKL.re {g g' : Gen Map} {es hs ts : List (Nat × Lazy S)} (h : SplitOKL g g' es hs ts) :
    g.re ≤ g'.re := let ⟨_, P, _⟩ := h; P.re

theorem SplitOKL.blk {g g' : Gen Map} {es hs ts : List (Nat × Lazy S)} (h : SplitOKL g g' es hs ts) {k : Nat}
    {B : List Pole} {fin : Termin} (hb : HoonMap.get g.blocks k = some ⟨[], B, fin⟩) :
    ∃ B', HoonMap.get g'.blocks k = some ⟨[], B', fin⟩ := let ⟨P, PP, _⟩ := h; ⟨_, PP.blk hb⟩

theorem SplitOKL.trans {g g1 g2 : Gen Map} {es1 hs1 ts1 es2 hs2 ts2 : List (Nat × Lazy S)}
    (a : SplitOKL g g1 es1 hs1 ts1) (b : SplitOKL g1 g2 es2 hs2 ts2) :
    SplitOKL g g2 (es1 ++ es2) (hs1 ++ hs2) (ts1 ++ ts2) := by
  obtain ⟨P1, PP1, O1, A1⟩ := a
  obtain ⟨P2, PP2, O2, A2⟩ := b
  have r1 := PP1.re
  have r2 := PP2.re
  refine ⟨fun k => P2 k ++ P1 k, PP1.trans PP2, fun k hk => ?_, fun k => ?_⟩
  · simp only [List.map_append, List.mem_append, not_or] at hk
    simp only [O1 k hk.1, O2 k hk.2, List.append_nil]
  · obtain ⟨ps1, e1, p1, h1, t1, s1⟩ := A1 k
    obtain ⟨ps2, e2, p2, h2, t2, s2⟩ := A2 k
    refine ⟨ps2 ++ ps1, by simp [e1, e2], ?_, ?_, ?_, fun p hp => ?_⟩
    · rw [List.map_append, atL_append]; exact (p2.append p1).trans List.perm_append_comm
    · rw [List.map_append, atL_append]; exact (h2.append h1).perm_right List.perm_append_comm
    · rw [List.map_append, atL_append]; exact (t2.append t1).perm_right List.perm_append_comm
    · rcases List.mem_append.mp hp with h | h
      · exact (s2 p h).mono r1 (Nat.le_refl _)
      · exact (s1 p h).mono (Nat.le_refl _) r2

theorem SplitOKL.perm {g g' : Gen Map} {es hs ts es' hs' ts' : List (Nat × Lazy S)} (W : SplitOKL g g' es hs ts)
    (he : es.Perm es') (hh : hs.Perm hs') (ht : ts.Perm ts') : SplitOKL g g' es' hs' ts' := by
  obtain ⟨P, PP, O, A⟩ := W
  refine ⟨P, PP, fun k hk => O k fun hm => hk ((he.map Prod.fst).mem_iff.mp hm), fun k => ?_⟩
  obtain ⟨ps, e, p, h, t, s⟩ := A k
  exact ⟨ps, e, p.trans (atL_perm he k), h.perm_right (atL_perm hh k), t.perm_right (atL_perm ht k), s⟩

theorem SplitOKL.dropH {g g' : Gen Map} {es hs ts hs' : List (Nat × Lazy S)} (W : SplitOKL g g' es hs ts)
    (hd : DropA hs hs') : SplitOKL g g' es hs' ts := by
  obtain ⟨P, PP, O, A⟩ := W
  refine ⟨P, PP, O, fun k => ?_⟩
  obtain ⟨ps, e, p, h, t, s⟩ := A k
  exact ⟨ps, e, p, h.trans (hd k), t, s⟩

theorem SplitOKL.dropT {g g' : Gen Map} {es hs ts ts' : List (Nat × Lazy S)} (W : SplitOKL g g' es hs ts)
    (hd : DropA ts ts') : SplitOKL g g' es hs ts' := by
  obtain ⟨P, PP, O, A⟩ := W
  refine ⟨P, PP, O, fun k => ?_⟩
  obtain ⟨ps, e, p, h, t, s⟩ := A k
  exact ⟨ps, e, p, h, t.trans (hd k), s⟩

/-- **One `+split-sure`** is the split per label of one entry. -/
theorem SplitOKL.base {s sh st : Sure S} {o : Nat} {g g1 : Gen Map} (h : splitSure s o g = some ((sh, st), g1))
    (hd : g.drop = false) {B0 : List Pole} {fin0 : Termin} (hb : HoonMap.get g.blocks o = some ⟨[], B0, fin0⟩)
    (l hl tl : Lazy S) (es : l.sure = s) (eh : hl.sure = sh) (et : tl.sure = st) :
    SplitOKL g g1 [(o, l)] [(o, hl)] [(o, tl)] := by
  obtain ⟨A, PA, M1, M2, CL, RA, RB, SD⟩ := splitSure_ok h hd hb
  refine ⟨fun k => if k = o then A else [], PA, fun k hk => ?_, fun k => ?_⟩
  · have : k ≠ o := fun e => hk (by simp [e])
    simp [this]
  · by_cases e : k = o
    · subst e
      refine ⟨[(s, sh, st, A)], by simp, by simp [atL_single, es], by simp [atL_single, eh, DropT.refl],
        by simp [atL_single, et, DropT.refl], fun p hp => ?_⟩
      rw [List.mem_singleton.mp hp]
      exact ⟨M1, M2, RA, RB, SD, CL⟩
    · have e' : o ≠ k := fun x => e x.symm
      refine ⟨[], by simp [e], by simp [atL_single, e'], by simp [atL_single, e', DropT.refl],
        by simp [atL_single, e', DropT.refl], fun _ h => by simp at h⟩

theorem fe_mem_y {oy on : Nat} {y n : Lazy S} {rest : List (ForkE S)} {e : Nat × Lazy S}
    (h : e ∈ (oy, y) :: entries y) : e ∈ forkEntries (((oy, y), (on, n)) :: rest) := by
  simp only [forkEntries]; exact List.mem_append_left _ (List.mem_append_left _ h)

theorem fe_mem_n {oy on : Nat} {y n : Lazy S} {rest : List (ForkE S)} {e : Nat × Lazy S}
    (h : e ∈ (on, n) :: entries n) : e ∈ forkEntries (((oy, y), (on, n)) :: rest) := by
  simp only [forkEntries]; exact List.mem_append_left _ (List.mem_append_right _ h)

theorem fe_mem_r {oy on : Nat} {y n : Lazy S} {rest : List (ForkE S)} {e : Nat × Lazy S}
    (h : e ∈ forkEntries rest) : e ∈ forkEntries (((oy, y), (on, n)) :: rest) := by
  simp only [forkEntries]; exact List.mem_append_right _ h

theorem be_mem_l {o : Nat} {l : Lazy S} {rest : List (Nat × Lazy S)} {e : Nat × Lazy S}
    (h : e ∈ (o, l) :: entries l) : e ∈ bondEntries ((o, l) :: rest) := by
  simp only [bondEntries]; exact List.mem_append_left _ h

theorem be_mem_r {o : Nat} {l : Lazy S} {rest : List (Nat × Lazy S)} {e : Nat × Lazy S}
    (h : e ∈ bondEntries rest) : e ∈ bondEntries ((o, l) :: rest) := by
  simp only [bondEntries]; exact List.mem_append_right _ h

mutual
/-- **`+split`'s loop per label**: every entry's need split at its label. -/
theorem splitLoop_okL : ∀ (o : Nat) (l : Lazy S) (g g' : Gen Map) (x : Lazy S × Lazy S),
    splitLoop l o g = some (x, g') → g.drop = false →
    (∀ e ∈ (o, l) :: entries l, ∃ B fin, HoonMap.get g.blocks e.1 = some ⟨[], B, fin⟩) →
    SplitOKL g g' ((o, l) :: entries l) ((o, x.1) :: entries x.1) ((o, x.2) :: entries x.2)
  | o, mk s fk bd, g, g', x, h, hd, hb => by
    rw [splitLoop] at h
    obtain ⟨⟨sh, st⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨B0, fin0, hb0⟩ := hb (o, mk s fk bd) List.mem_cons_self
    by_cases hfb : (fk.isEmpty && bd.isEmpty) = true
    · have hfb2 := hfb
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hfb2
      simp only [hfb, ↓reduceIte, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have e0 : entries (mk s fk bd : Lazy S) = [] := by
        rw [hfb2.1, hfb2.2]; simp [entries, bondEntries, forkEntries]
      simp only [e0, entries_ofSure]
      exact SplitOKL.base h1 hd hb0 _ _ _ rfl rfl rfl
    · have hfb' : (fk.isEmpty && bd.isEmpty) = false := by simpa using hfb
      simp only [hfb', Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨⟨fh, ft⟩, g2, h2, h⟩ := bind_some h
      obtain ⟨⟨bh, bt⟩, g3, h3, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have W1 := SplitOKL.base h1 hd hb0 (mk s fk bd) (mk sh fh bh) (mk st ft bt) rfl rfl rfl
      have d1 : g1.drop = false := W1.drop.trans hd
      have WF := splitForks_okL fk g1 g2 (fh, ft) h2 d1 (fun e he => by
        obtain ⟨B, fin, hb'⟩ := hb e (List.mem_cons_of_mem _ (by simp only [entries]; exact List.mem_append_right _ he))
        obtain ⟨B', hb''⟩ := W1.blk hb'
        exact ⟨B', fin, hb''⟩)
      have d2 : g2.drop = false := WF.drop.trans d1
      have WB := splitBonds_okL bd g2 g3 (bh, bt) h3 d2 (fun e he => by
        obtain ⟨B, fin, hb'⟩ := hb e (List.mem_cons_of_mem _ (by simp only [entries]; exact List.mem_append_left _ he))
        obtain ⟨B', hb''⟩ := W1.blk hb'
        obtain ⟨B'', hb'''⟩ := WF.blk hb''
        exact ⟨B'', fin, hb'''⟩)
      have W := (W1.trans WF).trans WB
      have pe : ∀ (s' : Sure S) (f' : List (ForkE S)) (b' : List (Nat × Lazy S)),
          ([(o, mk s' f' b')] ++ forkEntries f' ++ bondEntries b').Perm ((o, mk s' f' b') :: entries (mk s' f' b')) :=
        fun s' f' b' => by
          simp only [entries, List.singleton_append, List.cons_append]
          exact List.Perm.cons _ List.perm_append_comm
      refine ((W.perm (pe s fk bd) (pe sh fh bh) (pe st ft bt)).dropH ?_).dropT ?_
      · exact DropA.cons (o := o) (l := mk sh fh bh) (l' := lazyPrune (mk sh fh bh)) rfl (prune_dropA (mk sh fh bh))
      · exact DropA.cons (o := o) (l := mk st ft bt) (l' := lazyPrune (mk st ft bt)) rfl (prune_dropA (mk st ft bt))

/-- Its spin over the forks. -/
theorem splitForks_okL : ∀ (fk : List (ForkE S)) (g g' : Gen Map) (x : List (ForkE S) × List (ForkE S)),
    splitForks fk g = some (x, g') → g.drop = false →
    (∀ e ∈ forkEntries fk, ∃ B fin, HoonMap.get g.blocks e.1 = some ⟨[], B, fin⟩) →
    SplitOKL g g' (forkEntries fk) (forkEntries x.1) (forkEntries x.2)
  | [], g, g', x, h, _, _ => by
    simp only [splitForks, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact SplitOKL.nil g
  | ((oy, y), (on, n)) :: rest, g, g', x, h, hd, hb => by
    unfold splitForks at h
    obtain ⟨⟨yh, yt⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨⟨nh, nt⟩, g2, h2, h⟩ := bind_some h
    obtain ⟨⟨rh, rt⟩, g3, h3, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have Wy := splitLoop_okL oy y g g1 (yh, yt) h1 hd (fun e he => hb e (fe_mem_y he))
    have d1 : g1.drop = false := Wy.drop.trans hd
    have Wn := splitLoop_okL on n g1 g2 (nh, nt) h2 d1 (fun e he => by
      obtain ⟨B, fin, hb'⟩ := hb e (fe_mem_n he)
      obtain ⟨B', hb''⟩ := Wy.blk hb'
      exact ⟨B', fin, hb''⟩)
    have d2 : g2.drop = false := Wn.drop.trans d1
    have Wr := splitForks_okL rest g2 g3 (rh, rt) h3 d2 (fun e he => by
      obtain ⟨B, fin, hb'⟩ := hb e (fe_mem_r he)
      obtain ⟨B', hb''⟩ := Wy.blk hb'
      obtain ⟨B'', hb'''⟩ := Wn.blk hb''
      exact ⟨B'', fin, hb'''⟩)
    simp only [forkEntries]
    exact (Wy.trans Wn).trans Wr

/-- Its spin over the bonds. -/
theorem splitBonds_okL : ∀ (bd : List (Nat × Lazy S)) (g g' : Gen Map)
    (x : List (Nat × Lazy S) × List (Nat × Lazy S)),
    splitBonds bd g = some (x, g') → g.drop = false →
    (∀ e ∈ bondEntries bd, ∃ B fin, HoonMap.get g.blocks e.1 = some ⟨[], B, fin⟩) →
    SplitOKL g g' (bondEntries bd) (bondEntries x.1) (bondEntries x.2)
  | [], g, g', x, h, _, _ => by
    simp only [splitBonds, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact SplitOKL.nil g
  | (o, l) :: rest, g, g', x, h, hd, hb => by
    unfold splitBonds at h
    obtain ⟨⟨lh, lt⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨⟨rh, rt⟩, g2, h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have Wl := splitLoop_okL o l g g1 (lh, lt) h1 hd (fun e he => hb e (be_mem_l he))
    have d1 : g1.drop = false := Wl.drop.trans hd
    have Wr := splitBonds_okL rest g1 g2 (rh, rt) h2 d1 (fun e he => by
      obtain ⟨B, fin, hb'⟩ := hb e (be_mem_r he)
      obtain ⟨B', hb''⟩ := Wl.blk hb'
      exact ⟨B', fin, hb''⟩)
    simp only [bondEntries]
    exact Wl.trans Wr
end

/-- **`+split` per label**: the fresh block `g.bo` hopping to `th`, then the
loop on the goal's need at it (the root entry `(g.bo, L)`, the sure need). -/
theorem splitL_okL {L : Lazy S} {th : Jmp} {g g' : Gen Map} {hed tel : Lazy S} {o : Nat}
    (h : splitL ⟨L, th⟩ g = some ((hed, tel, o), g')) (hd : g.drop = false)
    (hb : ∀ e ∈ entries L, e.1 < g.bo ∧ ∃ B fin, HoonMap.get g.blocks e.1 = some ⟨[], B, fin⟩) :
    o = g.bo ∧ HoonMap.get (g.emitted ⟨[], [], Termin.hop th⟩).blocks g.bo = some ⟨[], [], Termin.hop th⟩ ∧
      SplitOKL (g.emitted ⟨[], [], Termin.hop th⟩) g' ((o, L) :: entries L) ((o, hed) :: entries hed)
        ((o, tel) :: entries tel) := by
  unfold splitL at h
  obtain ⟨o', g1, h1, h⟩ := bind_some h
  rw [emit_apply] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  obtain ⟨⟨hd', tl⟩, g2, h2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
  have eo := emitted_get g ⟨[], [], Termin.hop th⟩ hd
  refine ⟨rfl, eo, splitLoop_okL g.bo L _ g2 _ h2 hd (fun e he => ?_)⟩
  rcases List.mem_cons.mp he with rfl | he
  · exact ⟨[], _, eo⟩
  · obtain ⟨hlt, B, fin, hb'⟩ := hb e he
    exact ⟨B, fin, by rw [get_emitted_ne (by omega)]; exact hb'⟩

/-! ## The ops at one label -/

/-- **The pieces at one label run in sequence**: from the halves' needs held
by `a` and `b`, each need is built for `[a b]`; no register outside them
changes.  The needs are apart and below `lo`, the halves' registers theirs or
from `lo`, so no piece clobbers another's. -/
theorem splitPieces_run {lo hi : Nat} : ∀ (ps : List (SplitE S)), (∀ p ∈ ps, SplitP (Map := Map) lo hi p) →
    (∀ p ∈ ps, Distinct p.1.ned ∧ ∀ y, NMem p.1.ned y → y < lo) →
    (ps.map fun p => p.1).Pairwise (fun L L' => ∀ r, NMem L.ned r → ¬ NMem L'.ned r) →
    ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st' : σ) (t : Trace)
      (R : Map (Option Noun)) (a b : Noun), (∀ p ∈ ps, HoldsN p.2.1.ned R a) → (∀ p ∈ ps, HoldsN p.2.2.1.ned R b) →
      ∃ R', Runs lib O c gul st' t (ps.map fun p => p.2.2.2).flatten R R' ∧ (∀ p ∈ ps, HoldsN p.1.ned R' (C a b)) ∧
        ∀ y, (∀ p ∈ ps, ¬ NMem p.1.ned y) → SkaModel.read y R' = SkaModel.read y R
  | [], _, _, _, lib, σ, O, c, gul, st', t, R, a, b, _, _ =>
    ⟨R, Runs.nil R, fun _ h => by simp at h, fun _ _ => rfl⟩
  | p :: ps, hP, hD, hA, lib, σ, O, c, gul, st', t, R, a, b, ha, hb => by
    rw [List.map_cons, List.pairwise_cons] at hA
    have Pp := hP p List.mem_cons_self
    obtain ⟨dp, lp⟩ := hD p List.mem_cons_self
    obtain ⟨-, -, -, -, Sm⟩ := Pp.sem dp lp
    obtain ⟨R1, r1, h1, k1⟩ := Sm lib σ O c gul st' t R a b (ha p List.mem_cons_self) (hb p List.mem_cons_self)
    have apart : ∀ q ∈ ps, ∀ y, NMem q.1.ned y → ¬ NMem p.1.ned y := fun q hq y hy hp =>
      hA.1 q.1 (List.mem_map_of_mem hq) y hp hy
    have low : ∀ y, lo ≤ y → ¬ NMem p.1.ned y := fun y hy hp => by have := lp y hp; omega
    have keep1 : ∀ q ∈ ps, ∀ y, (NMem q.1.ned y ∨ (lo ≤ y ∧ y < hi)) → SkaModel.read y R1 = SkaModel.read y R :=
      fun q hq y hy => k1 y (hy.elim (apart q hq y) (fun h => low y h.1))
    obtain ⟨R2, r2, h2, k2⟩ := splitPieces_run ps (fun q hq => hP q (List.mem_cons_of_mem _ hq))
      (fun q hq => hD q (List.mem_cons_of_mem _ hq)) hA.2 lib σ O c gul st' t R1 a b
      (fun q hq => HoldsN.agree _ (fun y hy => keep1 q hq y ((hP q (List.mem_cons_of_mem _ hq)).mh y hy))
        (ha q (List.mem_cons_of_mem _ hq)))
      (fun q hq => HoldsN.agree _ (fun y hy => keep1 q hq y ((hP q (List.mem_cons_of_mem _ hq)).mt y hy))
        (hb q (List.mem_cons_of_mem _ hq)))
    refine ⟨R2, by simpa using r1.append r2, fun q hq => ?_, fun y hy => ?_⟩
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact HoldsN.agree _ (fun y hy => k2 y (fun q' hq' hq'' => apart q' hq' y hq'' hy)) h1
      · exact h2 q hq
    · rw [k2 y (fun q hq => hy q (List.mem_cons_of_mem _ hq)), k1 y (hy p List.mem_cons_self)]

/-- **The fits of the pieces at one label.** -/
theorem splitPieces_fits {lo hi : Nat} (ps : List (SplitE S)) (hP : ∀ p ∈ ps, SplitP (Map := Map) lo hi p)
    (hD : ∀ p ∈ ps, Distinct p.1.ned ∧ ∀ y, NMem p.1.ned y → y < lo) (a b : Noun) :
    (∀ p ∈ ps, FitsS p.1 (C a b)) ↔ (∀ p ∈ ps, FitsS p.2.1 a) ∧ (∀ p ∈ ps, FitsS p.2.2.1 b) := by
  have F : ∀ p ∈ ps, (FitsS p.1 (C a b) ↔ FitsS p.2.1 a ∧ FitsS p.2.2.1 b) := fun p hp =>
    ((hP p hp).sem (hD p hp).1 (hD p hp).2).2.2.2.1 a b
  exact ⟨fun h => ⟨fun p hp => ((F p hp).mp (h p hp)).1, fun p hp => ((F p hp).mp (h p hp)).2⟩,
    fun ⟨h1, h2⟩ p hp => (F p hp).mpr ⟨h1 p hp, h2 p hp⟩⟩

/-! ## The split at one label, in the needs of the entries -/

/-- **The needs at one label of an entry list are apart**, from `LabDisj`'s
form on the list. -/
theorem atL_apart {es : List (Nat × Lazy S)}
    (h : es.Pairwise fun e e' => e.1 = e'.1 → ∀ r, NMem e.2.sure.ned r → ¬ NMem e'.2.sure.ned r) (k : Nat) :
    (atL es k).Pairwise fun L L' => ∀ r, NMem L.ned r → ¬ NMem L'.ned r := by
  unfold atL
  rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ (List.Pairwise.filter (fun e => decide (e.1 = k)) h)
  intro a b ha hb hab
  exact hab ((of_decide_eq_true (List.mem_filter.mp ha).2).trans (of_decide_eq_true (List.mem_filter.mp hb).2).symm)

theorem mem_atL {es : List (Nat × Lazy S)} {k : Nat} {L : Sure S} (h : L ∈ atL es k) :
    ∃ e ∈ es, e.1 = k ∧ e.2.sure = L := by
  unfold atL at h
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
  exact ⟨e, (List.mem_filter.mp he).1, of_decide_eq_true (List.mem_filter.mp he).2, rfl⟩

/-- A list with trivial needs dropped: what holds of the kept ones holds of
all, for a property that every trivial need has. -/
theorem DropT.all {l l' : List (Sure S)} (h : DropT l l') {Q : Sure S → Prop} (ht : ∀ s, TrivS s → Q s)
    (h' : ∀ s ∈ l', Q s) : ∀ s ∈ l, Q s := by
  obtain ⟨k, p, t⟩ := h
  intro s hs
  rcases List.mem_append.mp (p.mem_iff.mpr hs) with a | a
  · exact h' s a
  · exact ht s (t s a)

theorem DropT.sub {l l' : List (Sure S)} (h : DropT l l') : ∀ s ∈ l', s ∈ l := by
  obtain ⟨k, p, t⟩ := h
  exact fun s hs => p.mem_iff.mp (List.mem_append_left _ hs)

/-- **`+split` at one label, in the needs of the entries**: the ops `P k`
in front of the block at `k` build every need of `es` at `k` for `[a b]`
from the needs of `hs` at `k` held by `a` and those of `ts` by `b`, and keep
every other register; the halves' registers are the entries' at `k` or
fresh; the fits split alike.  No `Nodup`: the needs at one label are apart. -/
theorem SplitOKL.runAt {g g' : Gen Map} {es hs ts : List (Nat × Lazy S)} (W : SplitOKL g g' es hs ts)
    (hdj : es.Pairwise fun e e' => e.1 = e'.1 → ∀ r, NMem e.2.sure.ned r → ¬ NMem e'.2.sure.ned r)
    (hreg : ∀ e ∈ es, Distinct e.2.sure.ned ∧ ∀ y, NMem e.2.sure.ned y → y < g.re) :
    ∃ P : Nat → List Pole, Pref g g' P ∧ (∀ k, k ∉ es.map Prod.fst → P k = []) ∧ ∀ k,
      (∀ a b, (∀ L ∈ atL es k, FitsS L (C a b)) ↔ (∀ H ∈ atL hs k, FitsS H a) ∧ (∀ T ∈ atL ts k, FitsS T b)) ∧
      (∀ H ∈ atL hs k, ∀ y, NMem H.ned y → (∃ L ∈ atL es k, NMem L.ned y) ∨ (g.re ≤ y ∧ y < g'.re)) ∧
      (∀ T ∈ atL ts k, ∀ y, NMem T.ned y → (∃ L ∈ atL es k, NMem L.ned y) ∨ (g.re ≤ y ∧ y < g'.re)) ∧
      ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st' : σ) (t : Trace)
        (R : Map (Option Noun)) (a b : Noun), (∀ H ∈ atL hs k, HoldsN H.ned R a) → (∀ T ∈ atL ts k, HoldsN T.ned R b) →
        ∃ R', Runs lib O c gul st' t (P k) R R' ∧ (∀ L ∈ atL es k, HoldsN L.ned R' (C a b)) ∧
          ∀ y, (∀ L ∈ atL es k, ¬ NMem L.ned y) → SkaModel.read y R' = SkaModel.read y R := by
  obtain ⟨P, PP, O, A⟩ := W
  refine ⟨P, PP, O, fun k => ?_⟩
  obtain ⟨ps, eP, pE, dH, dT, sP⟩ := A k
  have hD : ∀ p ∈ ps, Distinct p.1.ned ∧ ∀ y, NMem p.1.ned y → y < g.re := fun p hp => by
    obtain ⟨e, he, -, es'⟩ := mem_atL (pE.mem_iff.mp (List.mem_map_of_mem hp))
    rw [← es']; exact hreg e he
  have pw : (ps.map fun p => p.1).Pairwise fun L L' => ∀ r, NMem L.ned r → ¬ NMem L'.ned r :=
    (pE.pairwise_iff (fun h r hr hr' => h r hr' hr)).mpr (atL_apart hdj k)
  have memE : ∀ L, L ∈ atL es k ↔ ∃ p ∈ ps, p.1 = L := fun L => by
    rw [← pE.mem_iff, List.mem_map]
  have fitP := splitPieces_fits (Map := Map) ps sP hD
  refine ⟨fun a b => ?_, fun H hH y hy => ?_, fun T hT y hy => ?_, fun lib σ O' c gul st' t R a b ha hb => ?_⟩
  · have e1 : (∀ L ∈ atL es k, FitsS L (C a b)) ↔ ∀ p ∈ ps, FitsS p.1 (C a b) :=
      ⟨fun h p hp => h _ ((memE _).mpr ⟨p, hp, rfl⟩), fun h L hL => by
        obtain ⟨p, hp, rfl⟩ := (memE L).mp hL; exact h p hp⟩
    have e2 : ∀ (l : List (Sure S)) (l' : List (Sure S)), DropT l l' → ∀ v : Noun,
        ((∀ H ∈ l', FitsS H v) ↔ ∀ H ∈ l, FitsS H v) := fun l l' d v =>
      ⟨fun h => d.all (fun s ts => fitsS_trivial ts.1 ts.2 v) h, fun h H hH => h H (d.sub H hH)⟩
    rw [e1, fitP a b, e2 _ _ dH a, e2 _ _ dT b]
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (dH.sub H hH)
    rcases (sP p hp).mh y hy with h | h
    · exact Or.inl ⟨p.1, (memE _).mpr ⟨p, hp, rfl⟩, h⟩
    · exact Or.inr h
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (dT.sub T hT)
    rcases (sP p hp).mt y hy with h | h
    · exact Or.inl ⟨p.1, (memE _).mpr ⟨p, hp, rfl⟩, h⟩
    · exact Or.inr h
  · have ha' : ∀ p ∈ ps, HoldsN p.2.1.ned R a := fun p hp =>
      dH.all (Q := fun s => HoldsN s.ned R a) (fun s ts => by rw [ts.1]; trivial) ha _ (List.mem_map_of_mem hp)
    have hb' : ∀ p ∈ ps, HoldsN p.2.2.1.ned R b := fun p hp =>
      dT.all (Q := fun s => HoldsN s.ned R b) (fun s ts => by rw [ts.1]; trivial) hb _ (List.mem_map_of_mem hp)
    obtain ⟨R', r, h1, k1⟩ := splitPieces_run ps sP hD pw lib σ O' c gul st' t R a b ha' hb'
    refine ⟨R', by rw [eP]; exact r, fun L hL => ?_, fun y hy => k1 y (fun p hp => hy p.1 ((memE _).mpr ⟨p, hp, rfl⟩))⟩
    obtain ⟨p, hp, rfl⟩ := (memE L).mp hL
    exact h1 p hp

end Comp
end SkaModel
end Formalization
