import lemmas.Ska.RawInvCLCopy

/-!
# The run-level liveness with calls: the structure of the merge of `+copy`

README Gaps 14 (b), track D.  What `copyLazyL t a b` does to the state, as
the bricks of `CopySpecL` (`RawInvCLCopy.lean`).

* `copyNeed_mv`: the moves of `+copy-need-make-ops` read only registers of
  the merged need, and every register of either need is the merged need's
  or a move's destination.
* `MergeR Src La Lc P g g'`: the state changes only by `re` and by ops `P`
  in front (`Prep`), `cond`, `bo`, `drop` kept; the ops at `k` write
  registers of source entries at `k` and read registers of result entries
  at `k`; every register of an input entry of `La` is defined by the ops at
  its label or is a register of a result entry there (`cov`); every result
  entry of `Lc` sits at the label of a source entry, its registers those of
  source entries at that label or fresh (`ent`).
* **`mr_copyLazyL`** (mutual with `mr_mergeForks`, `mr_mergeBonds`): the
  merge of `a` and `b` at `t` meets `MergeR` with the inputs
  `(t, a) :: entries a ++ (t, b) :: entries b` and the result
  `(t, c) :: entries c`, when `b` is `LabUniq` (the witness `gD` of
  `RawInvCLCheckCopy.lean` shows `cov` fails without it).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The moves of `+copy-need-make-ops` -/

theorem cm_mov {R : Nat → Prop} {s d : Nat} {ops : List Pole} (hs : R s) :
    ∀ op ∈ Pole.mov s d :: ops, op ∈ ops ∨ ∀ y ∈ aliasReads op, R y := fun op hop => by
  rcases List.mem_cons.mp hop with rfl | h
  · exact Or.inr fun y hy => by rw [reads_mov.mp hy]; exact hs
  · exact Or.inl h

theorem cm_dst {s d : Nat} {ops : List Pole} : d ∈ defsOf (Pole.mov s d :: ops) := by
  rw [defsOf_cons]; simp [aliasDst]

theorem cm_defs_cons {op : Pole} {ops : List Pole} {y : Nat} (h : y ∈ defsOf ops) : y ∈ defsOf (op :: ops) := by
  rw [defsOf_cons]; exact List.mem_append_right _ h

theorem copyNeed_defs_mono {a b : Need} {ops : List Pole} {g g' : Comp.Gen Map} {x : Need × List Pole}
    (h : copyNeed a b ops g = some (x, g')) {y : Nat} (hy : y ∈ defsOf ops) : y ∈ defsOf x.2 := by
  obtain ⟨A, hA, -⟩ := copyNeed_spec _ _ _ _ _ _ h
  rw [hA, defsOf_append]; exact List.mem_append_right _ hy

/-- **The moves of `+copy-need-make-ops`**: each new op reads only registers
of the merged need; every register of either need is a destination or in
the merged need. -/
theorem copyNeed_mv : ∀ (a b : Need) (ops : List Pole) (g g' : Comp.Gen Map) (x : Need × List Pole),
    copyNeed a b ops g = some (x, g') →
    (∀ op ∈ x.2, op ∈ ops ∨ ∀ y ∈ aliasReads op, NMem x.1 y) ∧
    (∀ y, NMem a y ∨ NMem b y → y ∈ defsOf x.2 ∨ NMem x.1 y) := by
  intro a
  induction a with
  | none =>
    intro b ops g g' x h
    simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun op hop => Or.inl hop, fun y hy => Or.inr (hy.elim (fun e => e.elim) id)⟩
  | this rl =>
    intro b ops g g' x h
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨fun op hop => Or.inl hop, fun y hy => Or.inr (hy.elim id fun e => e.elim)⟩
    | this rr =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨cm_mov (show NMem (Need.this rl) rl from rfl), fun y hy => ?_⟩
      rcases hy with hy | hy
      · exact Or.inr hy
      · have e : y = rr := hy
        subst e; exact Or.inl cm_dst
    | both x' hh tt =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨cm_mov (show NMem (Need.both x' hh tt) x' from Or.inl rfl), fun y hy => ?_⟩
      rcases hy with hy | hy
      · have e : y = rl := hy
        subst e; exact Or.inl cm_dst
      · exact Or.inr hy
    | pair p q =>
      simp only [copyNeed, bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨cm_mov (show NMem (Need.both g.re p q) g.re from Or.inl rfl), fun y hy => ?_⟩
      rcases hy with hy | hy
      · have e : y = rl := hy
        subst e; exact Or.inl cm_dst
      · exact Or.inr (Or.inr hy)
  | pair pl ql ihp ihq =>
    intro b ops g g' x h
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨fun op hop => Or.inl hop, fun y hy => Or.inr (hy.elim id fun e => e.elim)⟩
    | this rr =>
      simp only [copyNeed, bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨cm_mov (show NMem (Need.both g.re pl ql) g.re from Or.inl rfl), fun y hy => ?_⟩
      rcases hy with hy | hy
      · exact Or.inr (Or.inr hy)
      · have e : y = rr := hy
        subst e; exact Or.inl cm_dst
    | both x' hr tr =>
      simp only [copyNeed] at h
      obtain ⟨⟨a', ops1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨b', ops2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨R1, C1⟩ := ihp hr _ g g1 _ h1
      obtain ⟨R2, C2⟩ := ihq tr _ g1 g2 _ h2
      refine ⟨fun op hop => ?_, fun y hy => ?_⟩
      · rcases R2 op hop with h | h
        · rcases R1 op h with h | h
          · exact Or.inl h
          · exact Or.inr fun y hy => Or.inr (Or.inl (h y hy))
        · exact Or.inr fun y hy => Or.inr (Or.inr (h y hy))
      · rcases hy with (hy | hy) | (hy | hy | hy)
        · rcases C1 y (Or.inl hy) with h | h
          · exact Or.inl (copyNeed_defs_mono h2 h)
          · exact Or.inr (Or.inr (Or.inl h))
        · rcases C2 y (Or.inl hy) with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inr (Or.inl hy)
        · rcases C1 y (Or.inr hy) with h | h
          · exact Or.inl (copyNeed_defs_mono h2 h)
          · exact Or.inr (Or.inr (Or.inl h))
        · rcases C2 y (Or.inr hy) with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inr h))
    | pair pr qr =>
      simp only [copyNeed] at h
      obtain ⟨⟨a', ops1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨b', ops2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨R1, C1⟩ := ihp pr _ g g1 _ h1
      obtain ⟨R2, C2⟩ := ihq qr _ g1 g2 _ h2
      refine ⟨fun op hop => ?_, fun y hy => ?_⟩
      · rcases R2 op hop with h | h
        · rcases R1 op h with h | h
          · exact Or.inl h
          · exact Or.inr fun y hy => nmem_consNeed_iff.mpr (Or.inl (h y hy))
        · exact Or.inr fun y hy => nmem_consNeed_iff.mpr (Or.inr (h y hy))
      · rcases hy with (hy | hy) | (hy | hy)
        · rcases C1 y (Or.inl hy) with h | h
          · exact Or.inl (copyNeed_defs_mono h2 h)
          · exact Or.inr (nmem_consNeed_iff.mpr (Or.inl h))
        · rcases C2 y (Or.inl hy) with h | h
          · exact Or.inl h
          · exact Or.inr (nmem_consNeed_iff.mpr (Or.inr h))
        · rcases C1 y (Or.inr hy) with h | h
          · exact Or.inl (copyNeed_defs_mono h2 h)
          · exact Or.inr (nmem_consNeed_iff.mpr (Or.inl h))
        · rcases C2 y (Or.inr hy) with h | h
          · exact Or.inl h
          · exact Or.inr (nmem_consNeed_iff.mpr (Or.inr h))
  | both rl hl tl ihh iht =>
    intro b ops g g' x h
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨fun op hop => Or.inl hop, fun y hy => Or.inr (hy.elim id fun e => e.elim)⟩
    | this rr =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨cm_mov (show NMem (Need.both rl hl tl) rl from Or.inl rfl), fun y hy => ?_⟩
      rcases hy with hy | hy
      · exact Or.inr hy
      · have e : y = rr := hy
        subst e; exact Or.inl cm_dst
    | both x' hr tr =>
      simp only [copyNeed] at h
      obtain ⟨⟨a', ops1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨b', ops2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨R1, C1⟩ := ihh hr _ g g1 _ h1
      obtain ⟨R2, C2⟩ := iht tr _ g1 g2 _ h2
      refine ⟨fun op hop => ?_, fun y hy => ?_⟩
      · rcases R2 op hop with h | h
        · rcases R1 op h with h | h
          · rcases List.mem_cons.mp h with rfl | h
            · exact Or.inr fun y hy => Or.inl (reads_mov.mp hy)
            · exact Or.inl h
          · exact Or.inr fun y hy => Or.inr (Or.inl (h y hy))
        · exact Or.inr fun y hy => Or.inr (Or.inr (h y hy))
      · rcases hy with (hy | hy | hy) | (hy | hy | hy)
        · have e : y = rl := hy
          subst e
          exact Or.inl (copyNeed_defs_mono h2 (copyNeed_defs_mono h1 cm_dst))
        · rcases C1 y (Or.inl hy) with h | h
          · exact Or.inl (copyNeed_defs_mono h2 h)
          · exact Or.inr (Or.inr (Or.inl h))
        · rcases C2 y (Or.inl hy) with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inr (Or.inl hy)
        · rcases C1 y (Or.inr hy) with h | h
          · exact Or.inl (copyNeed_defs_mono h2 h)
          · exact Or.inr (Or.inr (Or.inl h))
        · rcases C2 y (Or.inr hy) with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inr h))
    | pair p q =>
      simp only [copyNeed] at h
      obtain ⟨x0, g0', h0, h⟩ := bind_some h
      simp only [re_apply, Option.some.injEq, Prod.mk.injEq] at h0
      obtain ⟨rfl, rfl⟩ := h0
      obtain ⟨⟨a', ops1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨b', ops2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨R1, C1⟩ := ihh p _ _ g1 _ h1
      obtain ⟨R2, C2⟩ := iht q _ g1 g2 _ h2
      refine ⟨fun op hop => ?_, fun y hy => ?_⟩
      · rcases R2 op hop with h | h
        · rcases R1 op h with h | h
          · rcases List.mem_cons.mp h with rfl | h
            · exact Or.inr fun y hy => Or.inl (reads_mov.mp hy)
            · exact Or.inl h
          · exact Or.inr fun y hy => Or.inr (Or.inl (h y hy))
        · exact Or.inr fun y hy => Or.inr (Or.inr (h y hy))
      · rcases hy with (hy | hy | hy) | (hy | hy)
        · have e : y = rl := hy
          subst e
          exact Or.inl (copyNeed_defs_mono h2 (copyNeed_defs_mono h1 cm_dst))
        · rcases C1 y (Or.inl hy) with h | h
          · exact Or.inl (copyNeed_defs_mono h2 h)
          · exact Or.inr (Or.inr (Or.inl h))
        · rcases C2 y (Or.inl hy) with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inr h))
        · rcases C1 y (Or.inr hy) with h | h
          · exact Or.inl (copyNeed_defs_mono h2 h)
          · exact Or.inr (Or.inr (Or.inl h))
        · rcases C2 y (Or.inr hy) with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inr h))


/-! ## Lists of entries, the index -/

/-- `y` is a register of the need of an entry of `L` at label `k`. -/
def LK (L : List (Nat × Lazy S)) (k y : Nat) : Prop := ∃ e ∈ L, e.1 = k ∧ NMem e.2.sure.ned y

theorem LK.mono {L L' : List (Nat × Lazy S)} (h : ∀ e ∈ L, e ∈ L') {k y : Nat} (hl : LK L k y) : LK L' k y :=
  let ⟨e, he, h1, h2⟩ := hl; ⟨e, h e he, h1, h2⟩

theorem lazK_iff_LK {o : Nat} {laz : Lazy S} {x r : Nat} : lazK o laz x r ↔ LK ((o, laz) :: entries laz) x r :=
  Iff.rfl

theorem fe_append : ∀ (f1 f2 : List (ForkE S)), forkEntries (f1 ++ f2) = forkEntries f1 ++ forkEntries f2
  | [], _ => rfl
  | ((oy, y), (on, n)) :: rest, f2 => by
    simp only [List.cons_append, forkEntries, fe_append rest f2, List.append_assoc]

theorem be_append : ∀ (b1 b2 : List (Nat × Lazy S)), bondEntries (b1 ++ b2) = bondEntries b1 ++ bondEntries b2
  | [], _ => rfl
  | (o, l) :: rest, b2 => by
    simp only [List.cons_append, bondEntries, be_append rest b2, List.append_assoc]

theorem fe_single (v : ForkE S) :
    forkEntries [v] = ((v.1.1, v.1.2) :: entries v.1.2) ++ ((v.2.1, v.2.2) :: entries v.2.2) := by
  rcases v with ⟨⟨oy, y⟩, ⟨on, n⟩⟩
  simp [forkEntries]

theorem be_single (v : Nat × Lazy S) : bondEntries [v] = (v.1, v.2) :: entries v.2 := by
  rcases v with ⟨o, l⟩
  simp [bondEntries]

theorem fe_sub {f : List (ForkE S)} {v : ForkE S} (hv : v ∈ f) : ∀ e ∈ forkEntries [v], e ∈ forkEntries f := by
  induction f with
  | nil => cases hv
  | cons w rest ih =>
    intro e he
    rw [show w :: rest = [w] ++ rest from rfl, fe_append]
    rcases List.mem_cons.mp hv with rfl | hv
    · exact List.mem_append_left _ he
    · exact List.mem_append_right _ (ih hv e he)

theorem be_sub {b : List (Nat × Lazy S)} {v : Nat × Lazy S} (hv : v ∈ b) : ∀ e ∈ bondEntries [v], e ∈ bondEntries b := by
  induction b with
  | nil => cases hv
  | cons w rest ih =>
    intro e he
    rw [show w :: rest = [w] ++ rest from rfl, be_append]
    rcases List.mem_cons.mp hv with rfl | hv
    · exact List.mem_append_left _ he
    · exact List.mem_append_right _ (ih hv e he)

theorem fe_split {f : List (ForkE S)} {e : Nat × Lazy S} (he : e ∈ forkEntries f) : ∃ v ∈ f, e ∈ forkEntries [v] := by
  induction f with
  | nil => simp [forkEntries] at he
  | cons w rest ih =>
    rw [show w :: rest = [w] ++ rest from rfl, fe_append] at he
    rcases List.mem_append.mp he with he | he
    · exact ⟨w, List.mem_cons_self, he⟩
    · obtain ⟨v, hv, h⟩ := ih he
      exact ⟨v, List.mem_cons_of_mem _ hv, h⟩

theorem be_split {b : List (Nat × Lazy S)} {e : Nat × Lazy S} (he : e ∈ bondEntries b) : ∃ v ∈ b, e ∈ bondEntries [v] := by
  induction b with
  | nil => simp [bondEntries] at he
  | cons w rest ih =>
    rw [show w :: rest = [w] ++ rest from rfl, be_append] at he
    rcases List.mem_append.mp he with he | he
    · exact ⟨w, List.mem_cons_self, he⟩
    · obtain ⟨v, hv, h⟩ := ih he
      exact ⟨v, List.mem_cons_of_mem _ hv, h⟩

theorem entries_parts (l : Lazy S) : entries l = bondEntries l.bond ++ forkEntries l.fork := by
  cases l; rfl

theorem labUniq_of {l l' : Lazy S} {o : Nat} (h : LabUniq l) (hm : ∀ e ∈ (o, l') :: entries l', e ∈ entries l) :
    LabUniq l' := by
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · exact h (o, l') (List.mem_cons_of_mem _ (hm _ List.mem_cons_self))
  · exact h e (List.mem_cons_of_mem _ (hm e (List.mem_cons_of_mem _ he)))

theorem filterMap_cons_toList {α β : Type} (f : α → Option β) (a : α) (l : List α) :
    (a :: l).filterMap f = (f a).toList ++ l.filterMap f := by
  cases h : f a <;> simp [List.filterMap_cons, h]

theorem gm_foldl_get {α : Type} (key : α → Nat) (k : Nat) : ∀ (l : List α) (m : Map α) (e : α),
    HoonMap.get (l.foldl (fun m e => HoonMap.put m (key e) e) m) k = some e →
      (e ∈ l ∧ key e = k) ∨ HoonMap.get m k = some e
  | [], _, _, h => Or.inr h
  | x :: l, m, e, h => by
    simp only [List.foldl_cons] at h
    rcases gm_foldl_get key k l _ e h with ⟨h1, h2⟩ | h'
    · exact Or.inl ⟨List.mem_cons_of_mem _ h1, h2⟩
    · rw [HoonMap.get_put] at h'
      by_cases e1 : k = key x
      · rw [if_pos e1] at h'
        cases h'
        exact Or.inl ⟨List.mem_cons_self, e1.symm⟩
      · rw [if_neg e1] at h'; exact Or.inr h'

theorem gm_index_get {α : Type} (key : α → Nat) {l : List α} {k : Nat} {e : α}
    (h : HoonMap.get (index (Map := Map) key l) k = some e) : e ∈ l ∧ key e = k := by
  unfold index at h
  rcases gm_foldl_get key k l _ e h with h | h
  · exact h
  · rw [HoonMap.get_empty] at h; cases h

theorem gm_foldl_none {α : Type} (key : α → Nat) (k : Nat) : ∀ (l : List α) (m : Map α), (∀ e ∈ l, key e ≠ k) →
    HoonMap.get (l.foldl (fun m e => HoonMap.put m (key e) e) m) k = HoonMap.get m k
  | [], _, _ => rfl
  | x :: l, m, h => by
    simp only [List.foldl_cons]
    rw [gm_foldl_none key k l _ (fun e he => h e (List.mem_cons_of_mem _ he)), HoonMap.get_put,
      if_neg (fun e => h x List.mem_cons_self e.symm)]

theorem gm_index_mem {α : Type} (key : α → Nat) : ∀ {l : List α}, (l.map key).Nodup → ∀ {e : α}, e ∈ l →
    HoonMap.get (index (Map := Map) key l) (key e) = some e := by
  intro l hn e he
  unfold index
  suffices H : ∀ (l : List α) (m : Map α), (l.map key).Nodup → e ∈ l →
      HoonMap.get (l.foldl (fun m e => HoonMap.put m (key e) e) m) (key e) = some e from H l _ hn he
  intro l
  induction l with
  | nil => intro _ _ h; cases h
  | cons a rest ih =>
    intro m hn he
    simp only [List.foldl_cons]
    have hn' := List.nodup_cons.mp (by simpa using hn : (key a :: rest.map key).Nodup)
    rcases List.mem_cons.mp he with rfl | he
    · rw [gm_foldl_none key _ rest _ (fun e' he' x => hn'.1 (by rw [← x]; exact List.mem_map_of_mem he')),
        HoonMap.get_put, if_pos rfl]
    · exact ih _ hn'.2 he

theorem gm_mem_foldl (k : Nat) : ∀ (xs : List Nat) (s : S),
    k ∈ HoonSet.toList (xs.foldl HoonSet.put s) ↔ k ∈ xs ∨ k ∈ HoonSet.toList s
  | [], s => by simp
  | x :: xs, s => by
    simp only [List.foldl_cons]
    rw [gm_mem_foldl k xs, HoonSet.mem_put, List.mem_cons]
    constructor
    · rintro (h | h | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rintro ((h | h) | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

theorem gm_seen {α : Type} (key : α → Nat) (l : List α) (k : Nat) :
    seen (S := S) key l k = true ↔ k ∈ l.map key := by
  unfold seen
  rw [decide_eq_true_iff, gm_mem_foldl]
  exact ⟨fun h => h.elim id (fun h => absurd h (HoonSet.mem_empty k)), Or.inl⟩

/-! ## The relation of a merge -/

/-- **What a merge does to the state.** -/
structure MergeR (Src : Nat × Lazy S → Prop) (La Lc : List (Nat × Lazy S)) (P : Nat → List Pole)
    (g g' : Comp.Gen Map) : Prop where
  le : g.re ≤ g'.re
  cond : g'.cond = g.cond
  bo : g'.bo = g.bo
  drop : g'.drop = g.drop
  prep : Prep P g.blocks g'.blocks
  wr : ∀ k, OpsWr (fun y => ∃ e, Src e ∧ e.1 = k ∧ NMem e.2.sure.ned y) (P k)
  rd : ∀ k, ∀ op ∈ P k, ∀ y ∈ aliasReads op, LK Lc k y
  cov : ∀ e ∈ La, ∀ y, NMem e.2.sure.ned y → y ∈ defsOf (P e.1) ∨ LK Lc e.1 y
  ent : ∀ e ∈ Lc, (∃ e', Src e' ∧ e'.1 = e.1) ∧ ∀ y, NMem e.2.sure.ned y →
    (∃ e', Src e' ∧ e'.1 = e.1 ∧ NMem e'.2.sure.ned y) ∨ (g.re ≤ y ∧ y < g'.re)

theorem MergeR.keep {Src : Nat × Lazy S → Prop} {L : List (Nat × Lazy S)} (hS : ∀ e ∈ L, Src e)
    (g : Comp.Gen Map) : MergeR Src L L (fun _ => []) g g :=
  ⟨Nat.le_refl _, rfl, rfl, rfl, prep_nil _, fun _ => opsWr_nil _, fun _ op hop => absurd hop List.not_mem_nil,
    fun e he _ hy => Or.inr ⟨e, he, rfl, hy⟩, fun e he => ⟨⟨e, hS e he, rfl⟩, fun _ hy => Or.inl ⟨e, hS e he, rfl, hy⟩⟩⟩

theorem MergeR.seq {Src : Nat × Lazy S → Prop} {La1 Lc1 La2 Lc2 : List (Nat × Lazy S)} {P1 P2 : Nat → List Pole}
    {g g1 g2 : Comp.Gen Map} (h1 : MergeR Src La1 Lc1 P1 g g1) (h2 : MergeR Src La2 Lc2 P2 g1 g2) :
    MergeR Src (La1 ++ La2) (Lc1 ++ Lc2) (fun k => P2 k ++ P1 k) g g2 where
  le := Nat.le_trans h1.le h2.le
  cond := h2.cond.trans h1.cond
  bo := h2.bo.trans h1.bo
  drop := h2.drop.trans h1.drop
  prep := prep_trans h1.prep h2.prep
  wr k p hp := (List.mem_append.mp hp).elim (h2.wr k p) (h1.wr k p)
  rd k op hop y hy := (List.mem_append.mp hop).elim
    (fun h => (h2.rd k op h y hy).mono fun _ he => List.mem_append_right _ he)
    (fun h => (h1.rd k op h y hy).mono fun _ he => List.mem_append_left _ he)
  cov e he y hy := by
    rcases List.mem_append.mp he with he | he
    · rcases h1.cov e he y hy with h | h
      · exact Or.inl (by rw [defsOf_append]; exact List.mem_append_right _ h)
      · exact Or.inr (h.mono fun _ he => List.mem_append_left _ he)
    · rcases h2.cov e he y hy with h | h
      · exact Or.inl (by rw [defsOf_append]; exact List.mem_append_left _ h)
      · exact Or.inr (h.mono fun _ he => List.mem_append_right _ he)
  ent e he := by
    rcases List.mem_append.mp he with he | he
    · obtain ⟨l1, l2⟩ := h1.ent e he
      exact ⟨l1, fun y hy => (l2 y hy).imp_right fun h => ⟨h.1, Nat.lt_of_lt_of_le h.2 h2.le⟩⟩
    · obtain ⟨l1, l2⟩ := h2.ent e he
      exact ⟨l1, fun y hy => (l2 y hy).imp_right fun h => ⟨Nat.le_trans h1.le h.1, h.2⟩⟩

theorem MergeR.congr {Src : Nat × Lazy S → Prop} {La Lc La' Lc' : List (Nat × Lazy S)} {P : Nat → List Pole}
    {g g' : Comp.Gen Map} (h : MergeR Src La Lc P g g') (ha : ∀ e ∈ La', e ∈ La) (hc : ∀ e, e ∈ Lc ↔ e ∈ Lc') :
    MergeR Src La' Lc' P g g' where
  le := h.le
  cond := h.cond
  bo := h.bo
  drop := h.drop
  prep := h.prep
  wr := h.wr
  rd k op hop y hy := (h.rd k op hop y hy).mono fun e he => (hc e).mp he
  cov e he y hy := (h.cov e (ha e he) y hy).imp_right fun l => l.mono fun e he => (hc e).mp he
  ent e he := h.ent e ((hc e).mpr he)


/-! ## The merge -/

theorem mr_root {Src : Nat × Lazy S → Prop} {t : Nat} {a b c : Lazy S} {ned : Need} {ops : List Pole}
    {g g1 g2 : Comp.Gen Map} (hc : c.sure.ned = ned)
    (h1 : copyNeed a.sure.ned b.sure.ned [] g = some ((ned, ops), g1)) (hd : g.drop = false)
    (h2 : addOps t ops g1 = some ((), g2)) (hSa : Src (t, a)) (hSb : Src (t, b)) :
    MergeR Src [(t, a), (t, b)] [(t, c)] (fun k => if k = t then ops else []) g g2 := by
  obtain ⟨A, -, C⟩ := copyNeed_spec _ _ _ _ _ _ h1
  have MV := copyNeed_mv _ _ _ _ _ _ h1
  have e1 : g1.cond = g.cond ∧ g1.bo = g.bo ∧ g1.drop = g.drop ∧ g1.blocks = g.blocks := by
    rw [C.gen]; exact ⟨rfl, rfl, rfl, rfl⟩
  have hd1 : g1.drop = false := e1.2.2.1.trans hd
  obtain ⟨AS, hc2, pr2⟩ := addOps_step hd1 h2
  refine ⟨Nat.le_trans C.le AS.2.2.2.1, hc2.trans e1.1, AS.1.trans e1.2.1, AS.2.1.trans e1.2.2.1,
    by rw [← e1.2.2.2]; exact pr2, fun k => ?_, fun k op hop y hy => ?_, fun e he y hy => ?_, fun e he => ?_⟩
  · by_cases hk : k = t
    · rw [if_pos hk]
      exact fc_copyNeed_wr _ _ _ _ _ _ h1 (fun y hy => ⟨(t, a), hSa, hk.symm, hy⟩)
        (fun y hy => ⟨(t, b), hSb, hk.symm, hy⟩) (opsWr_nil _)
    · rw [if_neg hk]; exact opsWr_nil _
  · by_cases hk : k = t
    · rw [if_pos hk] at hop
      rcases MV.1 op hop with h | h
      · exact absurd h List.not_mem_nil
      · exact ⟨(t, c), List.mem_singleton_self _, hk.symm, by rw [hc]; exact h y hy⟩
    · rw [if_neg hk] at hop; exact absurd hop List.not_mem_nil
  · have et : e.1 = t := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
      rcases he with rfl | rfl <;> rfl
    rw [et, if_pos rfl]
    have hy' : NMem a.sure.ned y ∨ NMem b.sure.ned y := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
      rcases he with rfl | rfl
      · exact Or.inl hy
      · exact Or.inr hy
    rcases MV.2 y hy' with h | h
    · exact Or.inl h
    · exact Or.inr ⟨(t, c), List.mem_singleton_self _, rfl, by rw [hc]; exact h⟩
  · rw [List.mem_singleton] at he
    subst he
    refine ⟨⟨(t, a), hSa, rfl⟩, fun y hy => ?_⟩
    rw [hc] at hy
    rcases C.mem y hy with (h | h) | h
    · exact Or.inl ⟨(t, a), hSa, rfl, h⟩
    · exact Or.inl ⟨(t, b), hSb, rfl, h⟩
    · exact Or.inr ⟨h.1, Nat.lt_of_lt_of_le h.2 AS.2.2.2.1⟩

mutual
/-- **The structure of the merge of two lazy trees at `t`.** -/
theorem mr_copyLazyL (Src : Nat × Lazy S → Prop) (t : Nat) : ∀ (a b : Lazy S) (g g' : Comp.Gen Map) (c : Lazy S),
    copyLazyL t a b g = some (c, g') → g.drop = false →
    (∀ e ∈ (t, a) :: entries a, Src e) → (∀ e ∈ (t, b) :: entries b, Src e) → LabUniq b →
    ∃ P, MergeR Src (((t, a) :: entries a) ++ ((t, b) :: entries b)) ((t, c) :: entries c) P g g'
  | mk s1 f1 b1, second, g, g', c, h, hd, hSa, hSb, hU => by
    rw [copyLazyL] at h
    obtain ⟨⟨ned, ops⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨u, g2, h2, h⟩ := bind_some h
    obtain ⟨fork, g3, h3, h⟩ := bind_some h
    obtain ⟨bond, g4, h4, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hea : entries (mk s1 f1 b1) = bondEntries b1 ++ forkEntries f1 := rfl
    have heb := entries_parts second
    have hSaE : ∀ e ∈ bondEntries b1 ++ forkEntries f1, Src e := fun e he => hSa e (List.mem_cons_of_mem _ he)
    have hSbE : ∀ e ∈ bondEntries second.bond ++ forkEntries second.fork, Src e := fun e he =>
      hSb e (List.mem_cons_of_mem _ (by rw [heb]; exact he))
    have hU0 := hU (0, second) List.mem_cons_self
    have R1 := mr_root (Src := Src) (t := t) (c := mk ⟨ned, HoonSet.uni s1.lok second.sure.lok⟩ fork bond)
      (a := mk s1 f1 b1) rfl h1 hd (by cases u; exact h2) (hSa _ List.mem_cons_self) (hSb _ List.mem_cons_self)
    have hd2 : g2.drop = false := R1.drop.trans hd
    -- the forks
    have R2 : ∃ P, MergeR Src (forkEntries f1 ++ forkEntries second.fork) (forkEntries fork) P g2 g3 := by
      have hSf1 : ∀ e ∈ forkEntries f1, Src e := fun e he => hSaE e (List.mem_append_right _ he)
      have hSf2 : ∀ e ∈ forkEntries second.fork, Src e := fun e he => hSbE e (List.mem_append_right _ he)
      by_cases c1 : second.fork.isEmpty = true
      · rw [if_pos c1] at h3
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
        obtain ⟨rfl, rfl⟩ := h3
        have e0 : second.fork = [] := List.isEmpty_iff.mp c1
        refine ⟨_, (MergeR.keep hSf1 g2).congr (fun e he => ?_) (fun _ => Iff.rfl)⟩
        rw [e0] at he; simpa [forkEntries] using he
      rw [if_neg c1] at h3
      by_cases c2 : f1.isEmpty = true
      · rw [if_pos c2] at h3
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
        obtain ⟨rfl, rfl⟩ := h3
        have e0 : f1 = [] := List.isEmpty_iff.mp c2
        refine ⟨_, (MergeR.keep hSf2 g2).congr (fun e he => ?_) (fun _ => Iff.rfl)⟩
        rw [e0] at he; simpa [forkEntries] using he
      rw [if_neg c2] at h3
      obtain ⟨merged, g3', hm, h3⟩ := bind_some h3
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
      obtain ⟨rfl, rfl⟩ := h3
      obtain ⟨P3, M⟩ := mr_mergeForks Src (index (Map := Map) (fun e : ForkE S => e.1.1) second.fork) f1 g2 g3' merged
        hm hd2 hSf1 (fun k v hk => by
          obtain ⟨hv, hkv⟩ := gm_index_get _ hk
          have hsub := fe_sub hv
          rw [fe_single] at hsub
          refine ⟨fun e he => hSf2 e (fe_sub hv e he), labUniq_of hU (o := v.1.1) fun e he => ?_,
            labUniq_of hU (o := v.2.1) fun e he => ?_, hkv⟩
          · rw [heb]; exact List.mem_append_right _ (hsub e (List.mem_append_left _ he))
          · rw [heb]; exact List.mem_append_right _ (hsub e (List.mem_append_right _ he)))
      refine ⟨_, (M.seq (MergeR.keep (L := forkEntries (second.fork.filter fun e =>
        !(seen (S := S) (fun e : ForkE S => e.1.1) f1 e.1.1))) (fun e he => hSf2 e ?_) g3')).congr
        (fun e he => ?_) (fun e => by rw [fe_append])⟩
      · obtain ⟨v, hv, he'⟩ := fe_split he
        exact fe_sub (List.mem_filter.mp hv).1 e he'
      · rcases List.mem_append.mp he with he | he
        · exact List.mem_append_left _ (List.mem_append_left _ he)
        · obtain ⟨v, hv, he'⟩ := fe_split he
          cases hs : seen (S := S) (fun e : ForkE S => e.1.1) f1 v.1.1
          · exact List.mem_append_right _ (fe_sub (List.mem_filter.mpr ⟨hv, by simp [hs]⟩) e he')
          · obtain ⟨fa, hfa, hfe⟩ := List.mem_map.mp ((gm_seen _ _ _).mp hs)
            have hg := gm_index_mem (Map := Map) (fun e : ForkE S => e.1.1) hU0.2 hv
            refine List.mem_append_left _ (List.mem_append_right _ (fe_sub (List.mem_filterMap.mpr
              ⟨fa, hfa, ?_⟩) e he'))
            rw [hfe]; exact hg
    obtain ⟨P3, R2⟩ := R2
    have hd3 : g3.drop = false := R2.drop.trans hd2
    -- the bonds
    have R3 : ∃ P, MergeR Src (bondEntries b1 ++ bondEntries second.bond) (bondEntries bond) P g3 g4 := by
      have hSb1 : ∀ e ∈ bondEntries b1, Src e := fun e he => hSaE e (List.mem_append_left _ he)
      have hSb2 : ∀ e ∈ bondEntries second.bond, Src e := fun e he => hSbE e (List.mem_append_left _ he)
      by_cases c1 : second.bond.isEmpty = true
      · rw [if_pos c1] at h4
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
        obtain ⟨rfl, rfl⟩ := h4
        have e0 : second.bond = [] := List.isEmpty_iff.mp c1
        refine ⟨_, (MergeR.keep hSb1 g3).congr (fun e he => ?_) (fun _ => Iff.rfl)⟩
        rw [e0] at he; simpa [bondEntries] using he
      rw [if_neg c1] at h4
      by_cases c2 : b1.isEmpty = true
      · rw [if_pos c2] at h4
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
        obtain ⟨rfl, rfl⟩ := h4
        have e0 : b1 = [] := List.isEmpty_iff.mp c2
        refine ⟨_, (MergeR.keep hSb2 g3).congr (fun e he => ?_) (fun _ => Iff.rfl)⟩
        rw [e0] at he; simpa [bondEntries] using he
      rw [if_neg c2] at h4
      obtain ⟨merged, g4', hm, h4⟩ := bind_some h4
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
      obtain ⟨rfl, rfl⟩ := h4
      obtain ⟨P4, M⟩ := mr_mergeBonds Src (index (Map := Map) (fun e : Nat × Lazy S => e.1) second.bond) b1 g3 g4'
        merged hm hd3 hSb1 (fun k v hk => by
          obtain ⟨hv, hkv⟩ := gm_index_get _ hk
          have hsub := be_sub hv
          rw [be_single] at hsub
          refine ⟨fun e he => hSb2 e (be_sub hv e he), labUniq_of hU (o := v.1) fun e he => ?_, hkv⟩
          rw [heb]; exact List.mem_append_left _ (hsub e he))
      refine ⟨_, (M.seq (MergeR.keep (L := bondEntries (second.bond.filter fun e =>
        !(seen (S := S) (fun e : Nat × Lazy S => e.1) b1 e.1))) (fun e he => hSb2 e ?_) g4')).congr
        (fun e he => ?_) (fun e => by rw [be_append])⟩
      · obtain ⟨v, hv, he'⟩ := be_split he
        exact be_sub (List.mem_filter.mp hv).1 e he'
      · rcases List.mem_append.mp he with he | he
        · exact List.mem_append_left _ (List.mem_append_left _ he)
        · obtain ⟨v, hv, he'⟩ := be_split he
          cases hs : seen (S := S) (fun e : Nat × Lazy S => e.1) b1 v.1
          · exact List.mem_append_right _ (be_sub (List.mem_filter.mpr ⟨hv, by simp [hs]⟩) e he')
          · obtain ⟨fa, hfa, hfe⟩ := List.mem_map.mp ((gm_seen _ _ _).mp hs)
            have hg := gm_index_mem (Map := Map) (fun e : Nat × Lazy S => e.1) hU0.1 hv
            refine List.mem_append_left _ (List.mem_append_right _ (be_sub (List.mem_filterMap.mpr
              ⟨fa, hfa, ?_⟩) e he'))
            rw [hfe]; exact hg
    obtain ⟨P4, R3⟩ := R3
    refine ⟨_, ((R1.seq R2).seq R3).congr (fun e he => ?_) (fun e => ?_)⟩
    · rw [hea, heb] at he
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at he ⊢
      rcases he with (h | h | h) | (h | h | h)
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inr (Or.inr h)
      · exact Or.inl (Or.inr (Or.inr h))
    · show _ ↔ e ∈ (t, _) :: (bondEntries bond ++ forkEntries fork)
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
        · exact Or.inl (Or.inr h)

/-- The forks of the merge. -/
theorem mr_mergeForks (Src : Nat × Lazy S → Prop) (idx : Map (ForkE S)) :
    ∀ (l : List (ForkE S)) (g g' : Comp.Gen Map) (l' : List (ForkE S)),
    mergeForks idx l g = some (l', g') → g.drop = false → (∀ e ∈ forkEntries l, Src e) →
    (∀ k v, HoonMap.get idx k = some v → (∀ e ∈ forkEntries [v], Src e) ∧ LabUniq v.1.2 ∧ LabUniq v.2.2 ∧
      v.1.1 = k) →
    ∃ P, MergeR Src (forkEntries l ++ forkEntries (l.filterMap fun fe => HoonMap.get idx fe.1.1))
      (forkEntries l') P g g'
  | [], g, g', l', h, _, _, _ => by
    rw [mergeForks] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, (MergeR.keep (L := []) (fun e he => absurd he List.not_mem_nil) g).congr
      (fun e he => by simp [forkEntries] at he) (fun e => by simp [forkEntries])⟩
  | ((oy, y), (on, n)) :: rest, g, g', l', h, hd, hS, hidx => by
    rw [mergeForks] at h
    obtain ⟨e, g1, h1, h⟩ := bind_some h
    obtain ⟨r, g2, h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hcons : ∀ (w : ForkE S) (ws : List (ForkE S)), forkEntries (w :: ws) = forkEntries [w] ++ forkEntries ws :=
      fun w ws => fe_append [w] ws
    have hS0 : ∀ x ∈ forkEntries [((oy, y), (on, n))], Src x := fun x hx =>
      hS x (by rw [hcons]; exact List.mem_append_left _ hx)
    have hSr : ∀ x ∈ forkEntries rest, Src x := fun x hx => hS x (by rw [hcons]; exact List.mem_append_right _ hx)
    have E : ∃ P, MergeR Src (forkEntries [((oy, y), (on, n))] ++ forkEntries (HoonMap.get idx oy).toList)
        (forkEntries [e]) P g g1 := by
      rcases hk : HoonMap.get idx oy with _ | ⟨⟨z, my⟩, ⟨mon, mn⟩⟩
      · rw [hk] at h1
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact ⟨_, (MergeR.keep hS0 g).congr (fun x hx => by simpa [forkEntries] using hx) (fun _ => Iff.rfl)⟩
      · rw [hk] at h1
        obtain ⟨hSv, hU1, hU2, hz⟩ := hidx oy _ hk
        dsimp only at hz
        subst hz
        dsimp only at h1
        by_cases ce : on = mon
        · rw [if_pos ce] at h1
          subst ce
          obtain ⟨y', ga, hya, h1⟩ := bind_some h1
          obtain ⟨n', gb, hnb, h1⟩ := bind_some h1
          simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
          obtain ⟨rfl, rfl⟩ := h1
          rw [fe_single] at hS0 hSv
          obtain ⟨PA, A⟩ := mr_copyLazyL Src z y my g ga y' hya hd
            (fun x hx => hS0 x (List.mem_append_left _ hx)) (fun x hx => hSv x (List.mem_append_left _ hx)) hU1
          obtain ⟨PB, B⟩ := mr_copyLazyL Src on n mn ga gb n' hnb (A.drop.trans hd)
            (fun x hx => hS0 x (List.mem_append_right _ hx)) (fun x hx => hSv x (List.mem_append_right _ hx)) hU2
          refine ⟨_, (A.seq B).congr (fun x hx => ?_) (fun x => ?_)⟩
          · simp only [Option.toList, fe_single, List.mem_append, List.mem_cons] at hx ⊢
            rcases hx with (h | h) | (h | h)
            · exact Or.inl (Or.inl h)
            · exact Or.inr (Or.inl h)
            · exact Or.inl (Or.inr h)
            · exact Or.inr (Or.inr h)
          · simp only [fe_single, List.mem_append, List.mem_cons]
        · rw [if_neg ce] at h1
          cases h1
    obtain ⟨P1, E⟩ := E
    obtain ⟨P2, R⟩ := mr_mergeForks Src idx rest g1 g2 r h2 (E.drop.trans hd) hSr hidx
    refine ⟨_, (E.seq R).congr (fun x hx => ?_) (fun x => by rw [hcons e r])⟩
    rw [hcons, filterMap_cons_toList, fe_append] at hx
    simp only [List.mem_append] at hx ⊢
    rcases hx with (h | h) | (h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)

/-- The bonds of the merge. -/
theorem mr_mergeBonds (Src : Nat × Lazy S → Prop) (idx : Map (Nat × Lazy S)) :
    ∀ (l : List (Nat × Lazy S)) (g g' : Comp.Gen Map) (l' : List (Nat × Lazy S)),
    mergeBonds idx l g = some (l', g') → g.drop = false → (∀ e ∈ bondEntries l, Src e) →
    (∀ k v, HoonMap.get idx k = some v → (∀ e ∈ bondEntries [v], Src e) ∧ LabUniq v.2 ∧ v.1 = k) →
    ∃ P, MergeR Src (bondEntries l ++ bondEntries (l.filterMap fun e => HoonMap.get idx e.1))
      (bondEntries l') P g g'
  | [], g, g', l', h, _, _, _ => by
    rw [mergeBonds] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, (MergeR.keep (L := []) (fun e he => absurd he List.not_mem_nil) g).congr
      (fun e he => by simp [bondEntries] at he) (fun e => by simp [bondEntries])⟩
  | (ob, lb) :: rest, g, g', l', h, hd, hS, hidx => by
    rw [mergeBonds] at h
    obtain ⟨e, g1, h1, h⟩ := bind_some h
    obtain ⟨r, g2, h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hcons : ∀ (w : Nat × Lazy S) (ws : List (Nat × Lazy S)), bondEntries (w :: ws) = bondEntries [w] ++ bondEntries ws :=
      fun w ws => be_append [w] ws
    have hS0 : ∀ x ∈ bondEntries [(ob, lb)], Src x := fun x hx =>
      hS x (by rw [hcons]; exact List.mem_append_left _ hx)
    have hSr : ∀ x ∈ bondEntries rest, Src x := fun x hx => hS x (by rw [hcons]; exact List.mem_append_right _ hx)
    have E : ∃ P, MergeR Src (bondEntries [(ob, lb)] ++ bondEntries (HoonMap.get idx ob).toList)
        (bondEntries [e]) P g g1 := by
      rcases hk : HoonMap.get idx ob with _ | ⟨z, m⟩
      · rw [hk] at h1
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact ⟨_, (MergeR.keep hS0 g).congr (fun x hx => by simpa [bondEntries] using hx) (fun _ => Iff.rfl)⟩
      · rw [hk] at h1
        obtain ⟨hSv, hU1, hz⟩ := hidx ob _ hk
        dsimp only at hz
        subst hz
        dsimp only at h1
        obtain ⟨l2, ga, hla, h1⟩ := bind_some h1
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        rw [be_single] at hS0 hSv
        obtain ⟨PA, A⟩ := mr_copyLazyL Src z lb m g ga l2 hla hd hS0 hSv hU1
        refine ⟨_, A.congr (fun x hx => ?_) (fun x => ?_)⟩
        · simpa [Option.toList, be_single] using hx
        · simp only [be_single]
    obtain ⟨P1, E⟩ := E
    obtain ⟨P2, R⟩ := mr_mergeBonds Src idx rest g1 g2 r h2 (E.drop.trans hd) hSr hidx
    refine ⟨_, (E.seq R).congr (fun x hx => ?_) (fun x => by rw [hcons e r])⟩
    rw [hcons, filterMap_cons_toList, be_append] at hx
    simp only [List.mem_append] at hx ⊢
    rcases hx with (h | h) | (h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)
end

end Raw
end SkaModel
end Formalization
