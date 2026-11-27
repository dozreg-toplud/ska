import lemmas.Ska.CompGenCons

/-!
# The cons in `RunOKGen`: `+copy` per label, the relation and its pieces

README Gaps 12.39, item 10.  The cons ends with `copyL nex1 nex2.laz`: a
fresh block `o'` hopping to the head's jump, then `copyLazyL o'` of the two
halves: the sure needs merged by `+copy-need-make-ops` with the moves in
front of `o'`, and the forks and bonds of the two needs that name the same
lazy block merged the same way at that block (`mergeForks`,
`mergeBonds`), the others kept.  As for `+split` (`SplitOKL`,
`CompGenCons.lean`) the spec is per label: at every label the ops in front
are one piece per entry of the result there, each a copy of a need of the
first and one of the second (one of them `bunt` for an entry kept as it
was).

* `CopyE`, `CopyP` (one piece: `copyLazy_ok`'s conclusions), `CopyP.mono`,
  `copyP_root` (the merge of two sure needs at a block), `copyP_left`,
  `copyP_right` (an entry kept, its partner `bunt`).
* `CopyOKL` (the copy per label) with `nil`, `trans`, `perm`.
* `copyPieces_run`: the pieces at one label run in sequence, from the
  merged needs held by `z` to both halves' needs held by `z`, no register
  outside them changed, when the halves of different pieces are apart.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## One piece of `+copy` -/

/-- A piece of `+copy`: the need of the first, the need of the second, the
merged need, the ops in front. -/
abbrev CopyE (S : Type) := Sure S × Sure S × Sure S × List Pole

/-- **What `+copy-need-make-ops` did for two needs** (`copyLazy_ok`), its
fresh registers in `[lo, hi)`. -/
structure CopyP (lo hi : Nat) (p : CopyE S) : Prop where
  mem : ∀ y, NMem p.2.2.1.ned y → NMem p.1.ned y ∨ NMem p.2.1.ned y ∨ (lo ≤ y ∧ y < hi)
  ra : ∀ (Pr : Nat → Prop), NA Pr p.1.ned → NA Pr p.2.1.ned → Ple Pr lo → RegsIn Pr p.2.2.2
  rb : NB lo p.1.ned → NB lo p.2.1.ned → RegsIn (· < hi) p.2.2.2
  sem : CopyPre p.1.ned p.2.1.ned lo → Distinct p.2.2.1.ned ∧
    (∀ s, FitsS p.2.2.1 s ↔ FitsS p.1 s ∧ FitsS p.2.1 s) ∧ CopySem Map p.1.ned p.2.1.ned p.2.2.1.ned p.2.2.2

theorem CopyPre.mono {l r : Need} {lo lo' : Nat} (h : CopyPre l r lo) (e : lo ≤ lo') : CopyPre l r lo' :=
  ⟨h.cl, h.cr, h.d, fun y hy => Nat.lt_of_lt_of_le (h.lo y hy) e⟩

theorem CopyP.mono {lo hi lo' hi' : Nat} {p : CopyE S} (h : CopyP (Map := Map) lo hi p) (e1 : lo' ≤ lo)
    (e2 : hi ≤ hi') : CopyP (Map := Map) lo' hi' p := by
  refine ⟨fun y hy => ?_, fun Pr h1 h2 hm => h.ra Pr h1 h2 (ple_trans hm e1),
    fun h1 h2 q hq x hx => Nat.lt_of_lt_of_le (h.rb (fun r hr => Nat.lt_of_lt_of_le (h1 r hr) e1)
      (fun r hr => Nat.lt_of_lt_of_le (h2 r hr) e1) q hq x hx) e2,
    fun P => h.sem (P.mono e1)⟩
  rcases h.mem y hy with a | a | a
  · exact Or.inl a
  · exact Or.inr (Or.inl a)
  · exact Or.inr (Or.inr ⟨by omega, by omega⟩)

/-- **The merge of two sure needs at a block** (the root of `copyLazyL`). -/
theorem copyP_root {o : Nat} {s1 s2 s' : Sure S} {g g' : Gen Map} (h : copyLazy o s1 s2 g = some (s', g'))
    (hd : g.drop = false) :
    ∃ A, Pref g g' (fun k => if k = o then A else []) ∧ CopyP (Map := Map) g.re g'.re (s1, s2, s', A) := by
  obtain ⟨A, g1, PA, O, e1, el, RA, RB⟩ := copyLazy_ok h hd
  refine ⟨A, PA, ⟨fun y hy => ?_, RA, RB, fun P => ?_⟩⟩
  · rcases O.mem y hy with a | a
    · rcases a with a | a
      · exact Or.inl a
      · exact Or.inr (Or.inl a)
    · exact Or.inr (Or.inr ⟨a.1, by rw [← e1]; exact a.2⟩)
  · obtain ⟨d, -, F, CS⟩ := O.sem P
    refine ⟨d, fun s => ?_, CS⟩
    simp only [FitsS, F s, el, looks_uni]
    exact ⟨fun ⟨⟨a, b⟩, c, e⟩ => ⟨⟨a, c⟩, b, e⟩, fun ⟨⟨a, c⟩, b, e⟩ => ⟨⟨a, b⟩, c, e⟩⟩

/-- **An entry of the first kept as it was**: its partner `bunt`, no op. -/
theorem copyP_left (lo hi : Nat) (L : Sure S) : CopyP (Map := Map) lo hi (L, Sure.bunt, L, []) := by
  refine ⟨fun y hy => Or.inl hy, fun _ _ _ _ => RegsIn.nil _, fun _ _ => RegsIn.nil _, fun P => ?_⟩
  obtain ⟨d, -, -, CS⟩ := (copyOK_left (Map := Map) L.ned ({ (gen0 : Gen Map) with re := lo })).sem
    (by simpa [Sure.bunt] using P)
  refine ⟨d, fun s => ⟨fun f => ⟨f, fitsS_bunt s⟩, fun f => f.1⟩, ?_⟩
  simpa [Sure.bunt] using CS

/-- **An entry of the second kept as it was**: its partner `bunt`, no op. -/
theorem copyP_right (lo hi : Nat) (L : Sure S) : CopyP (Map := Map) lo hi (Sure.bunt, L, L, []) := by
  refine ⟨fun y hy => Or.inr (Or.inl hy), fun _ _ _ _ => RegsIn.nil _, fun _ _ => RegsIn.nil _, fun P => ?_⟩
  obtain ⟨d, -, -, CS⟩ := (copyOK_right (Map := Map) L.ned ({ (gen0 : Gen Map) with re := lo })).sem
    (by simpa [Sure.bunt] using P)
  refine ⟨d, fun s => ⟨fun f => ⟨fitsS_bunt s, f⟩, fun f => f.2⟩, ?_⟩
  simpa [Sure.bunt] using CS

/-! ## `+copy` per label -/

/-- **`+copy` per label**: the state grew by registers and by ops `P k` in
front of the block at each label of `fs` or `ss`; at every label they are
one piece per entry of the result `rs` there (up to a permutation), whose
first and second needs are those of `fs` and `ss` there, with `bunt`s
added for the entries kept as they were. -/
def CopyOKL (g g' : Gen Map) (fs ss rs : List (Nat × Lazy S)) : Prop :=
  ∃ P : Nat → List Pole, Pref g g' P ∧ (∀ k, k ∉ (fs ++ ss).map Prod.fst → P k = []) ∧
    ∀ k, ∃ cs : List (CopyE S), P k = (cs.map fun p => p.2.2.2).flatten ∧
      DropT (cs.map fun p => p.1) (atL fs k) ∧ DropT (cs.map fun p => p.2.1) (atL ss k) ∧
      (cs.map fun p => p.2.2.1).Perm (atL rs k) ∧ ∀ p ∈ cs, CopyP (Map := Map) g.re g'.re p

theorem CopyOKL.nil (g : Gen Map) : CopyOKL (S := S) g g [] [] [] :=
  ⟨fun _ => [], Pref.refl g, fun _ _ => rfl, fun k => ⟨[], rfl, by simp [atL, DropT.refl],
    by simp [atL, DropT.refl], by simp [atL], fun _ h => by simp at h⟩⟩

theorem CopyOKL.drop {g g' : Gen Map} {fs ss rs : List (Nat × Lazy S)} (h : CopyOKL g g' fs ss rs) :
    g'.drop = g.drop := let ⟨_, P, _⟩ := h; P.drop

theorem CopyOKL.blk {g g' : Gen Map} {fs ss rs : List (Nat × Lazy S)} (h : CopyOKL g g' fs ss rs) {k : Nat}
    {B : List Pole} {fin : Termin} (hb : HoonMap.get g.blocks k = some ⟨[], B, fin⟩) :
    ∃ B', HoonMap.get g'.blocks k = some ⟨[], B', fin⟩ := let ⟨P, PP, _⟩ := h; ⟨_, PP.blk hb⟩

theorem CopyOKL.trans {g g1 g2 : Gen Map} {fs1 ss1 rs1 fs2 ss2 rs2 : List (Nat × Lazy S)}
    (a : CopyOKL g g1 fs1 ss1 rs1) (b : CopyOKL g1 g2 fs2 ss2 rs2) :
    CopyOKL g g2 (fs1 ++ fs2) (ss1 ++ ss2) (rs1 ++ rs2) := by
  obtain ⟨P1, PP1, O1, A1⟩ := a
  obtain ⟨P2, PP2, O2, A2⟩ := b
  have r1 := PP1.re
  have r2 := PP2.re
  refine ⟨fun k => P2 k ++ P1 k, PP1.trans PP2, fun k hk => ?_, fun k => ?_⟩
  · simp only [List.map_append, List.mem_append, not_or] at hk
    show P2 k ++ P1 k = []
    rw [O1 k (by simp only [List.map_append, List.mem_append, not_or]; exact ⟨hk.1.1, hk.2.1⟩),
      O2 k (by simp only [List.map_append, List.mem_append, not_or]; exact ⟨hk.1.2, hk.2.2⟩)]
    rfl
  · obtain ⟨cs1, e1, f1, s1, p1, q1⟩ := A1 k
    obtain ⟨cs2, e2, f2, s2, p2, q2⟩ := A2 k
    refine ⟨cs2 ++ cs1, by simp [e1, e2], ?_, ?_, ?_, fun p hp => ?_⟩
    · rw [List.map_append, atL_append]; exact (f2.append f1).perm_right List.perm_append_comm
    · rw [List.map_append, atL_append]; exact (s2.append s1).perm_right List.perm_append_comm
    · rw [List.map_append, atL_append]; exact (p2.append p1).trans List.perm_append_comm
    · rcases List.mem_append.mp hp with h | h
      · exact (q2 p h).mono r1 (Nat.le_refl _)
      · exact (q1 p h).mono (Nat.le_refl _) r2

theorem CopyOKL.perm {g g' : Gen Map} {fs ss rs fs' ss' rs' : List (Nat × Lazy S)} (W : CopyOKL g g' fs ss rs)
    (hf : fs.Perm fs') (hs : ss.Perm ss') (hr : rs.Perm rs') : CopyOKL g g' fs' ss' rs' := by
  obtain ⟨P, PP, O, A⟩ := W
  refine ⟨P, PP, fun k hk => O k fun hm => hk (((hf.append hs).map Prod.fst).mem_iff.mp hm), fun k => ?_⟩
  obtain ⟨cs, e, f, s, p, q⟩ := A k
  exact ⟨cs, e, f.perm_right (atL_perm hf k), s.perm_right (atL_perm hs k), p.trans (atL_perm hr k), q⟩

/-! ## The ops at one label -/

/-- **The pieces of `+copy` at one label run in sequence**: from every
merged need held by `z`, both halves' needs of every piece hold `z`; no
register outside the halves changes.  The halves of two pieces are apart,
those of one piece apart and below `lo` (`CopyPre`), and the fresh
registers of the merged needs from `lo`. -/
theorem copyPieces_run {lo hi : Nat} : ∀ (cs : List (CopyE S)), (∀ p ∈ cs, CopyP (Map := Map) lo hi p) →
    (∀ p ∈ cs, CopyPre p.1.ned p.2.1.ned lo) →
    cs.Pairwise (fun p q => ∀ r, NMem (Need.pair p.1.ned p.2.1.ned) r → ¬ NMem (Need.pair q.1.ned q.2.1.ned) r) →
    ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st' : σ) (t : Trace)
      (R : Map (Option Noun)) (z : Noun), (∀ p ∈ cs, HoldsN p.2.2.1.ned R z) →
      ∃ R', Runs lib O c gul st' t (cs.map fun p => p.2.2.2).flatten R R' ∧
        (∀ p ∈ cs, HoldsN p.1.ned R' z ∧ HoldsN p.2.1.ned R' z) ∧
        ∀ y, (∀ p ∈ cs, ¬ NMem (Need.pair p.1.ned p.2.1.ned) y) → SkaModel.read y R' = SkaModel.read y R
  | [], _, _, _, lib, σ, O, c, gul, st', t, R, z, _ =>
    ⟨R, Runs.nil R, fun _ h => by simp at h, fun _ _ => rfl⟩
  | p :: cs, hP, hC, hA, lib, σ, O, c, gul, st', t, R, z, hz => by
    rw [List.pairwise_cons] at hA
    have Pp := hP p List.mem_cons_self
    have Cp := hC p List.mem_cons_self
    obtain ⟨-, -, CS⟩ := Pp.sem Cp
    obtain ⟨R1, r1, h1l, h1r, k1⟩ := CS lib σ O c gul st' t R z (hz p List.mem_cons_self)
    have apart : ∀ q ∈ cs, ∀ y, NMem (Need.pair q.1.ned q.2.1.ned) y → ¬ NMem (Need.pair p.1.ned p.2.1.ned) y :=
      fun q hq y hy hp => hA.1 q hq y hp hy
    have keep1 : ∀ q ∈ cs, ∀ y, NMem q.2.2.1.ned y → SkaModel.read y R1 = SkaModel.read y R := by
      intro q hq y hy
      refine k1 y ?_
      rcases (hP q (List.mem_cons_of_mem _ hq)).mem y hy with a | a | a
      · exact apart q hq y (Or.inl a)
      · exact apart q hq y (Or.inr a)
      · intro hp; have := Cp.lo y hp; omega
    obtain ⟨R2, r2, h2, k2⟩ := copyPieces_run cs (fun q hq => hP q (List.mem_cons_of_mem _ hq))
      (fun q hq => hC q (List.mem_cons_of_mem _ hq)) hA.2 lib σ O c gul st' t R1 z
      (fun q hq => HoldsN.agree _ (fun y hy => keep1 q hq y hy) (hz q (List.mem_cons_of_mem _ hq)))
    have k2p : ∀ y, NMem (Need.pair p.1.ned p.2.1.ned) y → SkaModel.read y R2 = SkaModel.read y R1 :=
      fun y hy => k2 y (fun q hq hq' => apart q hq y hq' hy)
    refine ⟨R2, by simpa using r1.append r2, fun q hq => ?_, fun y hy => ?_⟩
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨HoldsN.agree _ (fun y hy => k2p y (Or.inl hy)) h1l, HoldsN.agree _ (fun y hy => k2p y (Or.inr hy)) h1r⟩
      · exact h2 q hq
    · rw [k2 y (fun q hq => hy q (List.mem_cons_of_mem _ hq)), k1 y (hy p List.mem_cons_self)]

end Comp
end SkaModel
end Formalization
