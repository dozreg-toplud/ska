import lemmas.Ska.CompGenConsC


/-!
# The cons in `RunOKGen`: `+split` per label with apart halves

README Gaps 12.39, item 10.  `SplitOKL` (`CompGenCons.lean`) keeps each
piece's fresh registers only in the common range of the whole split, so it
cannot say that two goal entries at one label got apart halves; the copy's
pieces at that label need it (`copyPieces_run`).  `SplitOKD` is `SplitOKL`
with `PiecesApart`: the halves of the pieces at a label are apart when the
pieces' needs are apart and below the start.  The proofs are those of
`CompGenCons.lean` (`trans` adds the disjoint ranges of its two parts).

* `PiecesApart`, `SplitOKD` with `nil`, `drop`, `re`, `blk`, `trans`,
  `perm`, `dropH`, `dropT`, `base`; `splitLoop_okD` (mutual with
  `splitForks_okD`, `splitBonds_okD`), `splitL_okD`; `SplitOKD.toL`;
  **`SplitOKD.apartAt`**: the halves' needs at a label are pairwise apart.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The halves of the pieces are apart** when their needs are apart and
below `lo`. -/
def PiecesApart (lo : Nat) (ps : List (SplitE S)) : Prop :=
  (ps.map fun p => p.1).Pairwise (fun L L' => ∀ r, NMem L.ned r → ¬ NMem L'.ned r) →
    (∀ p ∈ ps, ∀ y, NMem p.1.ned y → y < lo) →
    ps.Pairwise fun p q => ∀ r, NMem (Need.pair p.2.1.ned p.2.2.1.ned) r → ¬ NMem (Need.pair q.2.1.ned q.2.2.1.ned) r

/-- **`+split` per label**: the state grew by registers and by ops `P k` in
front of the block at each label of `es`; at every label they are one piece
per entry of `es` there (up to a permutation), whose halves are the needs of
`hs` and `ts` there, some trivial ones dropped. -/
def SplitOKD (g g' : Gen Map) (es hs ts : List (Nat × Lazy S)) : Prop :=
  ∃ P : Nat → List Pole, Pref g g' P ∧ (∀ k, k ∉ es.map Prod.fst → P k = []) ∧
    ∀ k, ∃ ps : List (SplitE S), P k = (ps.map fun p => p.2.2.2).flatten ∧
      (ps.map fun p => p.1).Perm (atL es k) ∧ DropT (ps.map fun p => p.2.1) (atL hs k) ∧
      DropT (ps.map fun p => p.2.2.1) (atL ts k) ∧ (∀ p ∈ ps, SplitP (Map := Map) g.re g'.re p) ∧
      PiecesApart g.re ps

theorem SplitOKD.nil (g : Gen Map) : SplitOKD (S := S) g g [] [] [] :=
  ⟨fun _ => [], Pref.refl g, fun _ _ => rfl, fun k => ⟨[], rfl, by simp [atL], by simp [atL, DropT.refl],
    by simp [atL, DropT.refl], fun _ h => by simp at h, fun _ _ => List.Pairwise.nil⟩⟩

theorem SplitOKD.drop {g g' : Gen Map} {es hs ts : List (Nat × Lazy S)} (h : SplitOKD g g' es hs ts) :
    g'.drop = g.drop := let ⟨_, P, _⟩ := h; P.drop

theorem SplitOKD.re {g g' : Gen Map} {es hs ts : List (Nat × Lazy S)} (h : SplitOKD g g' es hs ts) :
    g.re ≤ g'.re := let ⟨_, P, _⟩ := h; P.re

theorem SplitOKD.blk {g g' : Gen Map} {es hs ts : List (Nat × Lazy S)} (h : SplitOKD g g' es hs ts) {k : Nat}
    {B : List Pole} {fin : Termin} (hb : HoonMap.get g.blocks k = some ⟨[], B, fin⟩) :
    ∃ B', HoonMap.get g'.blocks k = some ⟨[], B', fin⟩ := let ⟨P, PP, _⟩ := h; ⟨_, PP.blk hb⟩

theorem SplitOKD.trans {g g1 g2 : Gen Map} {es1 hs1 ts1 es2 hs2 ts2 : List (Nat × Lazy S)}
    (a : SplitOKD g g1 es1 hs1 ts1) (b : SplitOKD g1 g2 es2 hs2 ts2) :
    SplitOKD g g2 (es1 ++ es2) (hs1 ++ hs2) (ts1 ++ ts2) := by
  obtain ⟨P1, PP1, O1, A1⟩ := a
  obtain ⟨P2, PP2, O2, A2⟩ := b
  have r1 := PP1.re
  have r2 := PP2.re
  refine ⟨fun k => P2 k ++ P1 k, PP1.trans PP2, fun k hk => ?_, fun k => ?_⟩
  · simp only [List.map_append, List.mem_append, not_or] at hk
    simp only [O1 k hk.1, O2 k hk.2, List.append_nil]
  · obtain ⟨ps1, e1, p1, h1, t1, s1, a1⟩ := A1 k
    obtain ⟨ps2, e2, p2, h2, t2, s2, a2⟩ := A2 k
    refine ⟨ps2 ++ ps1, by simp [e1, e2], ?_, ?_, ?_, fun p hp => ?_, fun hpw hlo => ?_⟩
    · rw [List.map_append, atL_append]; exact (p2.append p1).trans List.perm_append_comm
    · rw [List.map_append, atL_append]; exact (h2.append h1).perm_right List.perm_append_comm
    · rw [List.map_append, atL_append]; exact (t2.append t1).perm_right List.perm_append_comm
    · rcases List.mem_append.mp hp with h | h
      · exact (s2 p h).mono r1 (Nat.le_refl _)
      · exact (s1 p h).mono (Nat.le_refl _) r2
    · rw [List.map_append, List.pairwise_append] at hpw
      rw [List.pairwise_append]
      refine ⟨a2 hpw.1 (fun p hp y hy => by have := hlo p (List.mem_append_left _ hp) y hy; omega),
        a1 hpw.2.1 (fun p hp y hy => hlo p (List.mem_append_right _ hp) y hy), fun p hp q hq r hr hr' => ?_⟩
      have sp := hlo p (List.mem_append_left _ hp)
      have sq := hlo q (List.mem_append_right _ hq)
      have m1 : NMem p.1.ned r ∨ (g1.re ≤ r ∧ r < g2.re) := by
        rcases hr with h | h
        · exact (s2 p hp).mh r h
        · exact (s2 p hp).mt r h
      have m2 : NMem q.1.ned r ∨ (g.re ≤ r ∧ r < g1.re) := by
        rcases hr' with h | h
        · exact (s1 q hq).mh r h
        · exact (s1 q hq).mt r h
      rcases m1 with m1 | m1 <;> rcases m2 with m2 | m2
      · exact hpw.2.2 p.1 (List.mem_map_of_mem hp) q.1 (List.mem_map_of_mem hq) r m1 m2
      · have := sp r m1; omega
      · have := sq r m2; omega
      · omega

theorem SplitOKD.perm {g g' : Gen Map} {es hs ts es' hs' ts' : List (Nat × Lazy S)} (W : SplitOKD g g' es hs ts)
    (he : es.Perm es') (hh : hs.Perm hs') (ht : ts.Perm ts') : SplitOKD g g' es' hs' ts' := by
  obtain ⟨P, PP, O, A⟩ := W
  refine ⟨P, PP, fun k hk => O k fun hm => hk ((he.map Prod.fst).mem_iff.mp hm), fun k => ?_⟩
  obtain ⟨ps, e, p, h, t, s, ap⟩ := A k
  exact ⟨ps, e, p.trans (atL_perm he k), h.perm_right (atL_perm hh k), t.perm_right (atL_perm ht k), s, ap⟩

theorem SplitOKD.dropH {g g' : Gen Map} {es hs ts hs' : List (Nat × Lazy S)} (W : SplitOKD g g' es hs ts)
    (hd : DropA hs hs') : SplitOKD g g' es hs' ts := by
  obtain ⟨P, PP, O, A⟩ := W
  refine ⟨P, PP, O, fun k => ?_⟩
  obtain ⟨ps, e, p, h, t, s, ap⟩ := A k
  exact ⟨ps, e, p, h.trans (hd k), t, s, ap⟩

theorem SplitOKD.dropT {g g' : Gen Map} {es hs ts ts' : List (Nat × Lazy S)} (W : SplitOKD g g' es hs ts)
    (hd : DropA ts ts') : SplitOKD g g' es hs ts' := by
  obtain ⟨P, PP, O, A⟩ := W
  refine ⟨P, PP, O, fun k => ?_⟩
  obtain ⟨ps, e, p, h, t, s, ap⟩ := A k
  exact ⟨ps, e, p, h, t.trans (hd k), s, ap⟩

/-- **One `+split-sure`** is the split per label of one entry. -/
theorem SplitOKD.base {s sh st : Sure S} {o : Nat} {g g1 : Gen Map} (h : splitSure s o g = some ((sh, st), g1))
    (hd : g.drop = false) {B0 : List Pole} {fin0 : Termin} (hb : HoonMap.get g.blocks o = some ⟨[], B0, fin0⟩)
    (l hl tl : Lazy S) (es : l.sure = s) (eh : hl.sure = sh) (et : tl.sure = st) :
    SplitOKD g g1 [(o, l)] [(o, hl)] [(o, tl)] := by
  obtain ⟨A, PA, M1, M2, CL, RA, RB, SD⟩ := splitSure_ok h hd hb
  refine ⟨fun k => if k = o then A else [], PA, fun k hk => ?_, fun k => ?_⟩
  · have : k ≠ o := fun e => hk (by simp [e])
    simp [this]
  · by_cases e : k = o
    · subst e
      refine ⟨[(s, sh, st, A)], by simp, by simp [atL_single, es], by simp [atL_single, eh, DropT.refl],
        by simp [atL_single, et, DropT.refl], fun p hp => ?_, ?_⟩
      · rw [List.mem_singleton.mp hp]
        exact ⟨M1, M2, RA, RB, SD, CL⟩
      · exact fun _ _ => List.pairwise_singleton _ _
    · have e' : o ≠ k := fun x => e x.symm
      refine ⟨[], by simp [e], by simp [atL_single, e'], by simp [atL_single, e', DropT.refl],
        by simp [atL_single, e', DropT.refl], fun _ h => by simp at h, fun _ _ => List.Pairwise.nil⟩

mutual
/-- **`+split`'s loop per label**: every entry's need split at its label. -/
theorem splitLoop_okD : ∀ (o : Nat) (l : Lazy S) (g g' : Gen Map) (x : Lazy S × Lazy S),
    splitLoop l o g = some (x, g') → g.drop = false →
    (∀ e ∈ (o, l) :: entries l, ∃ B fin, HoonMap.get g.blocks e.1 = some ⟨[], B, fin⟩) →
    SplitOKD g g' ((o, l) :: entries l) ((o, x.1) :: entries x.1) ((o, x.2) :: entries x.2)
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
      exact SplitOKD.base h1 hd hb0 _ _ _ rfl rfl rfl
    · have hfb' : (fk.isEmpty && bd.isEmpty) = false := by simpa using hfb
      simp only [hfb', Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨⟨fh, ft⟩, g2, h2, h⟩ := bind_some h
      obtain ⟨⟨bh, bt⟩, g3, h3, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have W1 := SplitOKD.base h1 hd hb0 (mk s fk bd) (mk sh fh bh) (mk st ft bt) rfl rfl rfl
      have d1 : g1.drop = false := W1.drop.trans hd
      have WF := splitForks_okD fk g1 g2 (fh, ft) h2 d1 (fun e he => by
        obtain ⟨B, fin, hb'⟩ := hb e (List.mem_cons_of_mem _ (by simp only [entries]; exact List.mem_append_right _ he))
        obtain ⟨B', hb''⟩ := W1.blk hb'
        exact ⟨B', fin, hb''⟩)
      have d2 : g2.drop = false := WF.drop.trans d1
      have WB := splitBonds_okD bd g2 g3 (bh, bt) h3 d2 (fun e he => by
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
theorem splitForks_okD : ∀ (fk : List (ForkE S)) (g g' : Gen Map) (x : List (ForkE S) × List (ForkE S)),
    splitForks fk g = some (x, g') → g.drop = false →
    (∀ e ∈ forkEntries fk, ∃ B fin, HoonMap.get g.blocks e.1 = some ⟨[], B, fin⟩) →
    SplitOKD g g' (forkEntries fk) (forkEntries x.1) (forkEntries x.2)
  | [], g, g', x, h, _, _ => by
    simp only [splitForks, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact SplitOKD.nil g
  | ((oy, y), (on, n)) :: rest, g, g', x, h, hd, hb => by
    unfold splitForks at h
    obtain ⟨⟨yh, yt⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨⟨nh, nt⟩, g2, h2, h⟩ := bind_some h
    obtain ⟨⟨rh, rt⟩, g3, h3, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have Wy := splitLoop_okD oy y g g1 (yh, yt) h1 hd (fun e he => hb e (fe_mem_y he))
    have d1 : g1.drop = false := Wy.drop.trans hd
    have Wn := splitLoop_okD on n g1 g2 (nh, nt) h2 d1 (fun e he => by
      obtain ⟨B, fin, hb'⟩ := hb e (fe_mem_n he)
      obtain ⟨B', hb''⟩ := Wy.blk hb'
      exact ⟨B', fin, hb''⟩)
    have d2 : g2.drop = false := Wn.drop.trans d1
    have Wr := splitForks_okD rest g2 g3 (rh, rt) h3 d2 (fun e he => by
      obtain ⟨B, fin, hb'⟩ := hb e (fe_mem_r he)
      obtain ⟨B', hb''⟩ := Wy.blk hb'
      obtain ⟨B'', hb'''⟩ := Wn.blk hb''
      exact ⟨B'', fin, hb'''⟩)
    simp only [forkEntries]
    exact (Wy.trans Wn).trans Wr

/-- Its spin over the bonds. -/
theorem splitBonds_okD : ∀ (bd : List (Nat × Lazy S)) (g g' : Gen Map)
    (x : List (Nat × Lazy S) × List (Nat × Lazy S)),
    splitBonds bd g = some (x, g') → g.drop = false →
    (∀ e ∈ bondEntries bd, ∃ B fin, HoonMap.get g.blocks e.1 = some ⟨[], B, fin⟩) →
    SplitOKD g g' (bondEntries bd) (bondEntries x.1) (bondEntries x.2)
  | [], g, g', x, h, _, _ => by
    simp only [splitBonds, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact SplitOKD.nil g
  | (o, l) :: rest, g, g', x, h, hd, hb => by
    unfold splitBonds at h
    obtain ⟨⟨lh, lt⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨⟨rh, rt⟩, g2, h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have Wl := splitLoop_okD o l g g1 (lh, lt) h1 hd (fun e he => hb e (be_mem_l he))
    have d1 : g1.drop = false := Wl.drop.trans hd
    have Wr := splitBonds_okD rest g1 g2 (rh, rt) h2 d1 (fun e he => by
      obtain ⟨B, fin, hb'⟩ := hb e (be_mem_r he)
      obtain ⟨B', hb''⟩ := Wl.blk hb'
      exact ⟨B', fin, hb''⟩)
    simp only [bondEntries]
    exact Wl.trans Wr
end

/-- **`+split` per label**: the fresh block `g.bo` hopping to `th`, then the
loop on the goal's need at it (the root entry `(g.bo, L)`, the sure need). -/
theorem splitL_okD {L : Lazy S} {th : Jmp} {g g' : Gen Map} {hed tel : Lazy S} {o : Nat}
    (h : splitL ⟨L, th⟩ g = some ((hed, tel, o), g')) (hd : g.drop = false)
    (hb : ∀ e ∈ entries L, e.1 < g.bo ∧ ∃ B fin, HoonMap.get g.blocks e.1 = some ⟨[], B, fin⟩) :
    o = g.bo ∧ HoonMap.get (g.emitted ⟨[], [], Termin.hop th⟩).blocks g.bo = some ⟨[], [], Termin.hop th⟩ ∧
      SplitOKD (g.emitted ⟨[], [], Termin.hop th⟩) g' ((o, L) :: entries L) ((o, hed) :: entries hed)
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
  refine ⟨rfl, eo, splitLoop_okD g.bo L _ g2 _ h2 hd (fun e he => ?_)⟩
  rcases List.mem_cons.mp he with rfl | he
  · exact ⟨[], _, eo⟩
  · obtain ⟨hlt, B, fin, hb'⟩ := hb e he
    exact ⟨B, fin, by rw [get_emitted_ne (by omega)]; exact hb'⟩


/-- `SplitOKD` forgets to `SplitOKL`. -/
theorem SplitOKD.toL {g g' : Gen Map} {es hs ts : List (Nat × Lazy S)} (W : SplitOKD g g' es hs ts) :
    SplitOKL g g' es hs ts := by
  obtain ⟨P, PP, O, A⟩ := W
  exact ⟨P, PP, O, fun k => let ⟨ps, e, p, h, t, s, _⟩ := A k; ⟨ps, e, p, h, t, s⟩⟩

theorem flatMap_pair_perm (ps : List (SplitE S)) :
    (ps.flatMap fun p => [p.2.1, p.2.2.1]).Perm ((ps.map fun p => p.2.1) ++ ps.map fun p => p.2.2.1) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.flatMap_cons, List.map_cons, List.cons_append, List.singleton_append, List.nil_append]
    exact List.Perm.cons _ ((ih.cons _).trans List.perm_middle.symm)

/-- **The halves' needs at one label are pairwise apart**, the goal's needs
there being apart (`LabDisj`'s form on `es`) and distinct below the start. -/
theorem SplitOKD.apartAt {g g' : Gen Map} {es hs ts : List (Nat × Lazy S)} (W : SplitOKD g g' es hs ts)
    (hdj : es.Pairwise fun e e' => e.1 = e'.1 → ∀ r, NMem e.2.sure.ned r → ¬ NMem e'.2.sure.ned r)
    (hreg : ∀ e ∈ es, Distinct e.2.sure.ned ∧ ∀ y, NMem e.2.sure.ned y → y < g.re) (k : Nat) :
    (atL hs k ++ atL ts k).Pairwise fun L L' => ∀ r, NMem L.ned r → ¬ NMem L'.ned r := by
  obtain ⟨P, PP, O, A⟩ := W
  obtain ⟨ps, eP, pE, dH, dT, sP, aP⟩ := A k
  have hD : ∀ p ∈ ps, Distinct p.1.ned ∧ ∀ y, NMem p.1.ned y → y < g.re := fun p hp => by
    obtain ⟨e, he, -, es'⟩ := mem_atL (pE.mem_iff.mp (List.mem_map_of_mem hp))
    rw [← es']; exact hreg e he
  have pw : (ps.map fun p => p.1).Pairwise fun L L' => ∀ r, NMem L.ned r → ¬ NMem L'.ned r :=
    (pE.pairwise_iff (fun h r hr hr' => h r hr' hr)).mpr (atL_apart hdj k)
  have ap := aP pw (fun p hp => (hD p hp).2)
  have big : (ps.flatMap fun p => [p.2.1, p.2.2.1]).Pairwise fun L L' => ∀ r, NMem L.ned r → ¬ NMem L'.ned r := by
    rw [List.pairwise_flatMap]
    refine ⟨fun p hp => ?_, ap.imp fun h x hx y hy r hr hr' => ?_⟩
    · have ht := ((sP p hp).sem (hD p hp).1 (hD p hp).2).2.2.1
      simp only [List.pairwise_cons, List.mem_singleton, forall_eq, List.not_mem_nil, false_imp_iff, implies_true,
        List.Pairwise.nil, and_true]
      exact ht
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
      refine h r ?_ ?_
      · rcases hx with rfl | rfl
        · exact Or.inl hr
        · exact Or.inr hr
      · rcases hy with rfl | rfl
        · exact Or.inl hr'
        · exact Or.inr hr'
  have big' := ((flatMap_pair_perm ps).pairwise_iff (fun h r hr hr' => h r hr' hr)).mp big
  obtain ⟨jh, ph, th⟩ := dH
  obtain ⟨jt, pt, tt⟩ := dT
  have pp : ((atL hs k ++ atL ts k) ++ (jh ++ jt)).Perm
      ((ps.map fun p => p.2.1) ++ ps.map fun p => p.2.2.1) := by
    refine List.Perm.trans ?_ (ph.append pt)
    simp only [List.append_assoc]
    refine List.Perm.append_left _ ?_
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.perm_append_comm.append_right _
  exact ((pp.pairwise_iff (fun h r hr hr' => h r hr' hr)).mpr big').sublist (List.sublist_append_left _ _)

end Comp
end SkaModel
end Formalization
