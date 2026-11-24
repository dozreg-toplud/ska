import lemmas.Ska.OptAliasSSAMid
import lemmas.Ska.OptDeadSim

/-!
# `+remove-dead-code` keeps single assignment

**`ssk_dead`** (the field `dead` of `SSAKeepR`), on a `topo` with `TopoOK`.
The pass keeps labels, parameters and ends, and keeps a sublist of each body
(`deadF`); the `j`-th op kept sits at `didx l S j` before (`ssk_dd_head`,
`ssk_dd_len`, `ssk_dd_mono`, `ssk_dd_lt`, `ssk_dd_mem`), as `fidx` does for
`filt_ssa`.  A read after is a read before, and a definition that counts after
is one before.  For `DefFirst` the definition found before must be one the pass
kept: the live set of `deadF` only grows backwards (`ssk_dd_live`: it never
removes a register an op writes), a register read at place `i` is in the live
set there (`ssk_dd_read`, and the end's registers are in `Sf o`), and along a
path the live set at a block's start is in `Sf` of every block before it
(`DeadW.jmp`).  So every op before the read that writes the register is kept
(`ssk_dd_def`), in the same block or in an earlier block of the path.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

set_option linter.unusedSectionVars false

/-- Whether `deadF` keeps the head `p` of `p :: rest`. -/
def dkeep (p : Pole) (rest : List Pole) (S : List Nat) : Bool :=
  match safeAssign p with
  | some d => decide (d ∈ (deadF rest S).2)
  | none => true

/-- The place in `l` of the `j`-th op that `deadF l S` keeps (`|l|` past the
last). -/
def didx : List Pole → List Nat → Nat → Nat
  | [], _, _ => 0
  | p :: rest, S, 0 => if dkeep p rest S then 0 else didx rest S 0 + 1
  | p :: rest, S, j + 1 => if dkeep p rest S then didx rest S j + 1 else didx rest S (j + 1) + 1

theorem ssk_sa_dst {op : Pole} {d : Nat} (h : safeAssign op = some d) : aliasDst op = some d := by
  cases op <;> simp_all [safeAssign, aliasDst]

theorem ssk_reads_regs {op : Pole} {x : Nat} (h : x ∈ aliasReads op) : x ∈ poleRegs op := by
  unfold aliasReads at h
  split at h
  · exact List.mem_of_mem_erase h
  · exact h

theorem ssk_dd_cons (p : Pole) (rest : List Pole) (S : List Nat) :
    (deadF (p :: rest) S = (p :: (deadF rest S).1, poleRegs p ++ (deadF rest S).2) ∧
      didx (p :: rest) S 0 = 0 ∧ ∀ j, didx (p :: rest) S (j + 1) = didx rest S j + 1) ∨
    (∃ d, safeAssign p = some d ∧ d ∉ (deadF rest S).2 ∧ deadF (p :: rest) S = deadF rest S ∧
      ∀ j, didx (p :: rest) S j = didx rest S j + 1) := by
  cases e : safeAssign p with
  | none => left; exact ⟨by simp [deadF, e], by simp [didx, dkeep, e], fun j => by simp [didx, dkeep, e]⟩
  | some d =>
    by_cases hd : d ∈ (deadF rest S).2
    · left; exact ⟨by simp [deadF, e, hd], by simp [didx, dkeep, e, hd], fun j => by simp [didx, dkeep, e, hd]⟩
    · right; exact ⟨d, rfl, hd, by simp [deadF, e, hd], fun j => by cases j <;> simp [didx, dkeep, e, hd]⟩

theorem ssk_dd_sub (S : List Nat) : ∀ l : List Pole, List.Sublist (deadF l S).1 l
  | [] => by simp [deadF]
  | p :: rest => by
    rcases ssk_dd_cons p rest S with ⟨hF, -, -⟩ | ⟨d, -, -, hF, -⟩
    · rw [hF]; exact List.Sublist.cons_cons p (ssk_dd_sub S rest)
    · rw [hF]; exact List.Sublist.cons p (ssk_dd_sub S rest)

theorem ssk_dd_len (S : List Nat) : ∀ (l : List Pole) (j : Nat), (deadF l S).1.length ≤ j → didx l S j = l.length
  | [], _, _ => rfl
  | p :: rest, j, h => by
    rcases ssk_dd_cons p rest S with ⟨hF, -, hs⟩ | ⟨d, -, -, hF, hI⟩
    · rw [hF] at h
      simp only [List.length_cons] at h
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [hs, ssk_dd_len S rest j (by omega)]; rfl
    · rw [hF] at h
      rw [hI, ssk_dd_len S rest j h]; rfl

theorem ssk_dd_head (S : List Nat) : ∀ (l : List Pole) (j : Nat),
    ((deadF l S).1.drop j).head? = (l.drop (didx l S j)).head?
  | [], _ => by simp [deadF, didx]
  | p :: rest, j => by
    rcases ssk_dd_cons p rest S with ⟨hF, h0, hs⟩ | ⟨d, -, -, hF, hI⟩
    · rw [hF]
      cases j with
      | zero => rw [h0]; rfl
      | succ j => rw [hs]; simp only [List.drop_succ_cons]; exact ssk_dd_head S rest j
    · rw [hF, hI]; simp only [List.drop_succ_cons]; exact ssk_dd_head S rest j

theorem ssk_dd_mem (S : List Nat) : ∀ (l : List Pole) (j : Nat) (op : Pole),
    op ∈ (deadF l S).1.drop j → op ∈ l.drop (didx l S j)
  | [], _, _, h => by simp [deadF] at h
  | p :: rest, j, op, h => by
    rcases ssk_dd_cons p rest S with ⟨hF, h0, hs⟩ | ⟨d, -, -, hF, hI⟩
    · rw [hF] at h
      cases j with
      | zero =>
        rw [h0]
        simp only [List.drop_zero, List.mem_cons] at h ⊢
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr ((ssk_dd_sub S rest).subset h)
      | succ j => rw [hs]; simp only [List.drop_succ_cons] at h ⊢; exact ssk_dd_mem S rest j op h
    · rw [hF] at h; rw [hI]; simp only [List.drop_succ_cons]; exact ssk_dd_mem S rest j op h

theorem ssk_dd_mono (S : List Nat) : ∀ (l : List Pole) (j₁ j₂ : Nat), j₁ ≤ j₂ → didx l S j₁ ≤ didx l S j₂
  | [], _, _, _ => Nat.le_refl _
  | p :: rest, j₁, j₂, h => by
    rcases ssk_dd_cons p rest S with ⟨-, h0, hs⟩ | ⟨d, -, -, -, hI⟩
    · cases j₁ with
      | zero => rw [h0]; exact Nat.zero_le _
      | succ j₁ =>
        cases j₂ with
        | zero => omega
        | succ j₂ => simp only [hs]; have := ssk_dd_mono S rest j₁ j₂ (by omega); omega
    · simp only [hI]; have := ssk_dd_mono S rest j₁ j₂ h; omega

theorem ssk_dd_lt (S : List Nat) : ∀ (l : List Pole) (j₁ j₂ : Nat), j₁ < j₂ → j₁ < (deadF l S).1.length →
    didx l S j₁ < didx l S j₂
  | [], _, _, _, h => by simp [deadF] at h
  | p :: rest, j₁, j₂, h, hl => by
    rcases ssk_dd_cons p rest S with ⟨hF, h0, hs⟩ | ⟨d, -, -, hF, hI⟩
    · rw [hF] at hl; simp only [List.length_cons] at hl
      cases j₁ with
      | zero =>
        cases j₂ with
        | zero => omega
        | succ j₂ => simp only [h0, hs]; omega
      | succ j₁ =>
        cases j₂ with
        | zero => omega
        | succ j₂ => simp only [hs]; have := ssk_dd_lt S rest j₁ j₂ (by omega) (by omega); omega
    · rw [hF] at hl; simp only [hI]; have := ssk_dd_lt S rest j₁ j₂ h hl; omega

/-- **An op before the `j`-th kept one whose register is live after it is
kept**, before the `j`-th. -/
theorem ssk_dd_def (S : List Nat) : ∀ (l : List Pole) (i' j r : Nat) (op : Pole), l[i']? = some op →
    aliasDst op = some r → r ∈ (deadF (l.drop (i' + 1)) S).2 → i' < didx l S j →
    r ∈ ((deadF l S).1.take j).filterMap aliasDst
  | [], _, _, _, _, h, _, _, _ => by simp at h
  | p :: rest, i', j, r, op, hop, hd, hl, hlt => by
    rcases ssk_dd_cons p rest S with ⟨hF, h0, hs⟩ | ⟨d, hsd, hdn, hF, hI⟩
    · rw [hF]
      cases j with
      | zero => rw [h0] at hlt; omega
      | succ j =>
        rw [hs] at hlt
        simp only [List.take_succ_cons]
        cases i' with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hop
          subst hop
          exact List.mem_filterMap.mpr ⟨p, List.mem_cons_self, hd⟩
        | succ i0 =>
          simp only [List.getElem?_cons_succ] at hop
          simp only [List.drop_succ_cons] at hl
          have := ssk_dd_def S rest i0 j r op hop hd hl (by omega)
          obtain ⟨a, ha, hfa⟩ := List.mem_filterMap.mp this
          exact List.mem_filterMap.mpr ⟨a, List.mem_cons_of_mem _ ha, hfa⟩
    · rw [hF]
      rw [hI] at hlt
      cases i' with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hop
        subst hop
        have := ssk_sa_dst hsd
        rw [hd] at this; cases this
        simp only [List.drop_succ_cons, List.drop_zero] at hl
        exact absurd hl hdn
      | succ i0 =>
        simp only [List.getElem?_cons_succ] at hop
        simp only [List.drop_succ_cons] at hl
        exact ssk_dd_def S rest i0 j r op hop hd hl (by omega)

/-- The registers of the `j`-th kept op are live before it. -/
theorem ssk_dd_read (S : List Nat) : ∀ (l : List Pole) (j : Nat) (op : Pole), ((deadF l S).1.drop j).head? = some op →
    ∀ x ∈ poleRegs op, x ∈ (deadF (l.drop (didx l S j)) S).2
  | [], _, _, h => by simp [deadF] at h
  | p :: rest, j, op, h => by
    rcases ssk_dd_cons p rest S with ⟨hF, h0, hs⟩ | ⟨d, -, -, hF, hI⟩
    · rw [hF] at h
      cases j with
      | zero =>
        simp only [List.drop_zero, List.head?_cons, Option.some.injEq] at h
        subst h
        rw [h0, List.drop_zero, hF]
        intro x hx; exact List.mem_append_left _ hx
      | succ j =>
        simp only [List.drop_succ_cons] at h
        rw [hs]; simp only [List.drop_succ_cons]
        exact ssk_dd_read S rest j op h
    · rw [hF] at h; rw [hI]; simp only [List.drop_succ_cons]
      exact ssk_dd_read S rest j op h

theorem ssk_dd_step (S : List Nat) (x : Nat) : ∀ (l : List Pole) (i : Nat),
    x ∈ (deadF (l.drop (i + 1)) S).2 → x ∈ (deadF (l.drop i) S).2
  | [], _, h => by simpa using h
  | p :: rest, 0, h => by
    simp only [List.drop_succ_cons, List.drop_zero] at h ⊢
    rcases deadF_cons p rest S with hF | ⟨d, -, -, hF⟩ <;> rw [hF]
    · exact List.mem_append_right _ h
    · exact h
  | p :: rest, i + 1, h => by
    simp only [List.drop_succ_cons] at h ⊢
    exact ssk_dd_step S x rest i h

/-- **The live set only grows backwards.** -/
theorem ssk_dd_live (S : List Nat) (l : List Pole) {i i' : Nat} (h : i ≤ i') {x : Nat}
    (hx : x ∈ (deadF (l.drop i') S).2) : x ∈ (deadF (l.drop i) S).2 := by
  revert hx
  induction h with
  | refl => exact id
  | step _ ih => exact fun hx => ih (ssk_dd_step S x l _ hx)

theorem ssk_bpath_reach {bl : Map Blob} {L : List Nat} (h : BPath bl L) : ∀ x ∈ L, Reach bl x := by
  induction h with
  | start => intro x hx; rw [List.mem_singleton.mp hx]; exact Reach.zero
  | @step p0 o0 b j _ hb hj ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Reach.jump (j := j) (ih o0 List.mem_cons_self) hb hj
    · exact ih x hx

/-- `dead_walk`, with the labels outside `topo` absent after. -/
theorem ssk_dead_walk {bl bl' : Map Blob} {topo : List Nat} (ht : TopoOK bl topo)
    (h : removeDeadCode bl topo.reverse = some bl') :
    ∃ Sf, DeadW bl bl' topo Sf ∧ ∀ k, k ∉ topo → HoonMap.get bl' k = none := by
  unfold removeDeadCode at h
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨Sf, A, B, -, E⟩ := deadFold_spec bl topo.reverse _ r (List.pairwise_reverse.mpr (ht.1.imp fun h e => h e.symm)) hr
  refine ⟨Sf, ⟨ht, fun o ho => ?_, fun o b j bt ho hb hj hbt x hx => ?_⟩, fun k hk => ?_⟩
  · obtain ⟨b, hb, i1, i2, -⟩ := A o (List.mem_reverse.mpr ho)
    exact ⟨b, hb, i1, i2⟩
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ho
    obtain ⟨k, hik, hk⟩ := ht.2.2.2.2 i o b j hi hb hj
    have hk' : k < topo.length := (List.getElem?_eq_some_iff.mp hk).1
    refine E (topo.length - 1 - k) (topo.length - 1 - i) j.there o bt (by omega) ?_ ?_ hbt x hx
    · rw [List.getElem?_reverse (l := topo) (by omega),
        show topo.length - 1 - (topo.length - 1 - k) = k by omega]
      exact hk
    · have hi' : i < topo.length := (List.getElem?_eq_some_iff.mp hi).1
      rw [List.getElem?_reverse (l := topo) (by omega),
        show topo.length - 1 - (topo.length - 1 - i) = i by omega]
      exact hi
  · rw [B k (fun h => hk (List.mem_reverse.mp h))]; exact HoonMap.get_empty k

/-- **`+remove-dead-code` keeps `AliasSSAB`** (the field `dead` of
`SSAKeepR`), on a `topo` with `TopoOK`. -/
theorem ssk_dead {bl bl' : Map Blob} {topo : List Nat} (ht : TopoOK bl topo)
    (h : removeDeadCode bl topo.reverse = some bl') (hs : AliasSSAB bl) : AliasSSAB bl' := by
  obtain ⟨Sf, W, hout⟩ := ssk_dead_walk ht h
  obtain ⟨h1, h2⟩ := hs
  have hback : ∀ o b', HoonMap.get bl' o = some b' → o ∈ topo ∧ ∃ b, HoonMap.get bl o = some b ∧
      b' = { b with body := (deadF b.body (Sf o)).1 } := by
    intro o b' hb'
    by_cases ho : o ∈ topo
    · obtain ⟨b, hb, hb2, -⟩ := W.blk o ho
      rw [hb2] at hb'; cases hb'
      exact ⟨ho, b, hb, rfl⟩
    · rw [hout o ho] at hb'; cases hb'
  have hreach : ∀ o, Reach bl' o → Reach bl o := by
    intro o hr
    induction hr with
    | zero => exact Reach.zero
    | jump _ hb hj ih =>
      obtain ⟨-, b, hb0, rfl⟩ := hback _ _ hb
      exact Reach.jump (j := _) ih hb0 hj
  have hbpath : ∀ L, BPath bl' L → BPath bl L := by
    intro L hL
    induction hL with
    | start => exact BPath.start
    | step _ hb hj ih =>
      obtain ⟨-, b, hb0, rfl⟩ := hback _ _ hb
      exact BPath.step ih hb0 hj
  -- a read after is a read before, of a live register
  have hrm : ∀ o b j r, HoonMap.get bl o = some b → ReadAt { b with body := (deadF b.body (Sf o)).1 } j r →
      o ∈ topo → ReadAt b (didx b.body (Sf o) j) r ∧ r ∈ (deadF (b.body.drop (didx b.body (Sf o) j)) (Sf o)).2 := by
    intro o b j r hb h ho
    rcases h with h | ⟨hj, h⟩
    · simp only at h
      cases e : ((deadF b.body (Sf o)).1.drop j).head? with
      | none => rw [e] at h; simp at h
      | some op =>
        rw [e] at h
        simp only [Option.map_some, Option.getD_some] at h
        refine ⟨Or.inl ?_, ssk_dd_read (Sf o) b.body j op e r (ssk_reads_regs h)⟩
        rw [← ssk_dd_head, e]
        simp only [Option.map_some, Option.getD_some]
        exact h
    · simp only at hj
      have hd : didx b.body (Sf o) j = b.body.length := ssk_dd_len _ _ _ (by omega)
      rw [hd]
      refine ⟨Or.inr ⟨rfl, h⟩, ?_⟩
      rw [List.drop_length]
      obtain ⟨b2, hb2, -, hfin⟩ := W.blk o ho
      rw [hb] at hb2; cases hb2
      exact hfin r h
  -- along a path, the live set at a block's start is in `Sf` of every block before
  have hlivep : ∀ L, BPath bl L → ∀ o p b, L = o :: p → HoonMap.get bl o = some b →
      ∀ x ∈ (deadF b.body (Sf o)).2, ∀ o' ∈ p, x ∈ Sf o' := by
    intro L hL
    induction hL with
    | start => intro o p b e; cases e; intro _ _ _ _ h; cases h
    | @step p0 o0 b0 j hp hb0 hj ih =>
      intro o p b e hb x hx o' ho'
      cases e
      have ho0 : o0 ∈ topo := ht.2.2.2.1 o0 (ssk_bpath_reach hp o0 List.mem_cons_self)
      have hx0 : x ∈ Sf o0 := W.jmp o0 b0 j b ho0 hb0 hj hb x hx
      rcases List.mem_cons.mp ho' with rfl | ho'
      · exact hx0
      · exact ih o0 p0 b0 rfl hb0 x (deadF_sup _ _ x hx0) o' ho'
  -- the place before of a definition after
  let sm : Nat × Option Nat → Nat × Option Nat := fun s =>
    match s.2 with
    | none => s
    | some i => (s.1, some (((HoonMap.get bl s.1).map fun b => didx b.body (Sf s.1) i).getD i))
  have live : ∀ r s, LiveDef bl' r s → LiveDef bl r (sm s) ∧
      (∀ i, s.2 = some i → ∃ b, HoonMap.get bl s.1 = some b ∧ i < (deadF b.body (Sf s.1)).1.length ∧
        sm s = (s.1, some (didx b.body (Sf s.1) i))) := by
    rintro r ⟨o, _ | i⟩ ⟨hr, hd, hf⟩
    · obtain ⟨b', hb', hm⟩ := hd
      obtain ⟨-, b, hb, rfl⟩ := hback _ _ hb'
      exact ⟨⟨hreach _ hr, ⟨b, hb, hm⟩, fun _ h => by cases h⟩, fun _ h => by cases h⟩
    · obtain ⟨b', op, hb', hop, hdst⟩ := hd
      obtain ⟨ho, b, hb, rfl⟩ := hback _ _ hb'
      have hlt : i < (deadF b.body (Sf o)).1.length := (List.getElem?_eq_some_iff.mp hop).1
      have hop0 : b.body[didx b.body (Sf o) i]? = some op := by
        rw [← List.head?_drop, ← ssk_dd_head, List.head?_drop]; exact hop
      have hsm : sm (o, some i) = (o, some (didx b.body (Sf o) i)) := by
        simp only [sm, hb, Option.map_some, Option.getD_some]
      refine ⟨?_, fun i2 h => by cases h; exact ⟨b, hb, hlt, hsm⟩⟩
      rw [hsm]
      refine ⟨hreach _ hr, ⟨b, op, hb, hop0, hdst⟩, fun i0 hi0 hdf => ?_⟩
      cases hi0
      apply hf i rfl
      obtain ⟨b1, hb1, hbom, ⟨n, hn⟩, himm, hrd⟩ := hdf
      rw [hb] at hb1; cases hb1
      refine ⟨_, hb', hbom, ⟨n, ?_⟩, fun op' hop' => ?_, fun o' b'' j hr' hb'' hj => ?_⟩
      · rw [hop]; rw [hop0] at hn; exact hn
      · exact himm op' (ssk_dd_mem _ _ _ _ hop')
      · obtain ⟨ho', b2, hb2, rfl⟩ := hback _ _ hb''
        obtain ⟨hrd1, -⟩ := hrm o' b2 j r hb2 hj ho'
        obtain ⟨ho'', hlt'⟩ := hrd o' b2 _ (hreach _ hr') hb2 hrd1
        rw [ho''] at hb2 hlt'
        rw [hb] at hb2; cases hb2
        refine ⟨ho'', Classical.byContradiction fun hn' => ?_⟩
        have := ssk_dd_mono (Sf o) b.body i j (by omega)
        dsimp only at hlt'
        omega
  refine ⟨fun r s s' hs hs' => ?_, fun o pth b' hpath hb' i r hread hr => ?_⟩
  · obtain ⟨l1, e1⟩ := live r s hs
    obtain ⟨l2, e2⟩ := live r s' hs'
    have heq := h1 r _ _ l1 l2
    obtain ⟨o, _ | i⟩ := s <;> obtain ⟨o', _ | i'⟩ := s'
    · exact heq
    · obtain ⟨b, -, -, hsm⟩ := e2 i' rfl
      rw [hsm] at heq; cases heq
    · obtain ⟨b, -, -, hsm⟩ := e1 i rfl
      rw [hsm] at heq; cases heq
    · obtain ⟨b, hb, hlt, hsm⟩ := e1 i rfl
      obtain ⟨b2, hb2, hlt2, hsm2⟩ := e2 i' rfl
      rw [hsm, hsm2] at heq
      simp only [Prod.mk.injEq, Option.some.injEq] at heq
      obtain ⟨rfl, hfi⟩ := heq
      rw [hb] at hb2; cases hb2
      rcases Nat.lt_trichotomy i i' with hc | hc | hc
      · have := ssk_dd_lt (Sf o) b.body i i' hc hlt; omega
      · rw [hc]
      · have := ssk_dd_lt (Sf o) b.body i' i hc hlt2; omega
  · obtain ⟨ho, b, hb, rfl⟩ := hback _ _ hb'
    have hr0 : r ∈ allDefs bl := by
      unfold allDefs at hr ⊢
      obtain ⟨k, hk, hmem⟩ := List.mem_flatMap.mp hr
      have hks : (HoonMap.get bl' k).isSome := (MapKeys.mem_keys bl' k).mp hk
      obtain ⟨bk', hbk'⟩ := Option.isSome_iff_exists.mp hks
      obtain ⟨-, bk, hbk, rfl⟩ := hback _ _ hbk'
      rw [hbk'] at hmem
      refine List.mem_flatMap.mpr ⟨k, (MapKeys.mem_keys bl k).mpr (by rw [hbk]; rfl), ?_⟩
      rw [hbk]
      simp only [Option.map_some, Option.getD_some, blockDefs, List.mem_append] at hmem ⊢
      rcases hmem with hm | hm
      · exact Or.inl hm
      · exact Or.inr (((ssk_dd_sub _ _).filterMap aliasDst).subset hm)
    obtain ⟨hrd, hlv⟩ := hrm o b i r hb hread ho
    have hpb := hbpath _ hpath
    rcases h2 o pth b hpb hb _ r hrd hr0 with h | h | ⟨o', ho', b2, hb2, hm⟩
    · exact Or.inl h
    · right; left
      obtain ⟨op, hop, hd⟩ := List.mem_filterMap.mp h
      obtain ⟨i', hi'⟩ := List.mem_iff_getElem?.mp hop
      rw [List.getElem?_take] at hi'
      split at hi'
      · rename_i hlt
        exact ssk_dd_def (Sf o) b.body i' i r op hi' hd (ssk_dd_live (Sf o) b.body (by omega) hlv) hlt
      · cases hi'
    · right; right
      have ho2 : o' ∈ topo := ht.2.2.2.1 o' (ssk_bpath_reach hpb o' (List.mem_cons_of_mem _ ho'))
      obtain ⟨b3, hb3, hb3', -⟩ := W.blk o' ho2
      rw [hb2] at hb3; cases hb3
      refine ⟨o', ho', _, hb3', ?_⟩
      have hS : r ∈ Sf o' := hlivep _ hpb o pth b rfl hb r (ssk_dd_live (Sf o) b.body (Nat.zero_le _) hlv) o' ho'
      simp only [blockDefs, List.mem_append] at hm ⊢
      rcases hm with hm | hm
      · exact Or.inl hm
      · right
        obtain ⟨op, hop, hd⟩ := List.mem_filterMap.mp hm
        obtain ⟨i', hi'⟩ := List.mem_iff_getElem?.mp hop
        have hlen := ssk_dd_len (Sf o') b2.body _ (Nat.le_refl _)
        have := ssk_dd_def (Sf o') b2.body i' _ r op hi' hd (deadF_sup _ _ r hS)
          (by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hi').1)
        rwa [List.take_length] at this

end Opt
end SkaModel
end Formalization
