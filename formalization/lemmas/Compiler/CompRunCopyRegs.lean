import lemmas.Compiler.CompRunRegs

/-!
# `+copy-lazy` keeps no register twice, the keys and the labels

`copy_regs`: on two lazy needs with their keys (`LKeys`), whose registers
are below the counter and occur once in the two together, `+copy-lazy`
returns a lazy need made of their registers and fresh ones, each once
(`Sub`), with its keys, whose labels are theirs.  The merge (`mergeForks`,
`mergeBonds`) copies the entry of the second need under a label of the first
into that entry: the keys of the first need have no duplicate, so each entry
of the second is used at most once (`index_get_key`, `filter_key_single`),
and the entries the merge uses and those it appends (`seen`) cut the second
need's list in two (`bregs_filter_split`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## The index of the merge -/

theorem index_get_key' {α : Type} (key : α → Nat) :
    ∀ (l : List α) (m : TreapMap mugF α) (k : Nat) (v : α),
    HoonMap.get (l.foldl (fun m e => HoonMap.put m (key e) e) m) k = some v →
      (v ∈ l ∧ key v = k) ∨ HoonMap.get m k = some v
  | [], m, k, v, h => Or.inr h
  | e :: rest, m, k, v, h => by
    rw [List.foldl_cons] at h
    rcases index_get_key' key rest _ k v h with ⟨h1, h2⟩ | h1
    · exact Or.inl ⟨List.mem_cons_of_mem _ h1, h2⟩
    · rw [HoonMap.get_put] at h1
      split at h1
      · rename_i hk
        simp only [Option.some.injEq] at h1; subst h1; exact Or.inl ⟨List.mem_cons_self, hk.symm⟩
      · exact Or.inr h1

theorem index_get_key {α : Type} (key : α → Nat) (l : List α) (k : Nat) (v : α)
    (h : HoonMap.get (Lazy.index (Map := TreapMap mugF) key l) k = some v) : v ∈ l ∧ key v = k := by
  rcases index_get_key' key l HoonMap.empty k v h with h1 | h1
  · exact h1
  · rw [HoonMap.get_empty] at h1; cases h1

theorem index_get_none' {α : Type} (key : α → Nat) :
    ∀ (l : List α) (m : TreapMap mugF α) (k : Nat),
    HoonMap.get (l.foldl (fun m e => HoonMap.put m (key e) e) m) k = Option.none → ∀ e ∈ l, key e ≠ k
  | [], m, k, h, e, he => absurd he List.not_mem_nil
  | e :: rest, m, k, h, e', he' => by
    rw [List.foldl_cons] at h
    rcases List.mem_cons.1 he' with rfl | he'
    · intro hk
      -- the entry put at its key stays found
      have : ∀ (l : List α) (m : TreapMap mugF α), (HoonMap.get m k).isSome →
          (HoonMap.get (l.foldl (fun m e => HoonMap.put m (key e) e) m) k).isSome := by
        intro l
        induction l with
        | nil => intro m hm; exact hm
        | cons a t ih =>
          intro m hm
          rw [List.foldl_cons]
          apply ih
          rw [HoonMap.get_put]
          split
          · rfl
          · exact hm
      have h2 := this rest (HoonMap.put m (key e') e') (by rw [HoonMap.get_put, if_pos hk.symm]; rfl)
      rw [h] at h2; cases h2
    · exact index_get_none' key rest _ k h e' he'

theorem index_get_none {α : Type} (key : α → Nat) (l : List α) (k : Nat)
    (h : HoonMap.get (Lazy.index (Map := TreapMap mugF) key l) k = Option.none) : ∀ e ∈ l, key e ≠ k :=
  index_get_none' key l HoonMap.empty k h

/-- With no duplicate key, the entries under a key are the one found. -/
theorem filter_key_single {α : Type} (key : α → Nat) {k : Nat} {v : α} :
    ∀ (l : List α), (l.map key).Nodup → v ∈ l → key v = k → l.filter (fun e => decide (key e = k)) = [v]
  | [], _, hv, _ => absurd hv List.not_mem_nil
  | e :: rest, hn, hv, hk => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    rw [List.filter_cons]
    rcases List.mem_cons.1 hv with rfl | hv
    · rw [if_pos (by simp [hk])]
      congr 1
      rw [List.filter_eq_nil_iff]
      intro a ha hka
      exact hn.1 ⟨a, ha, by simpa [hk] using hka⟩
    · rw [if_neg (by simp only [decide_eq_true_eq]; intro he; exact hn.1 ⟨v, hv, hk.trans he.symm⟩)]
      exact filter_key_single key rest hn.2 hv hk

theorem filter_key_none {α : Type} (key : α → Nat) {k : Nat} (l : List α) (h : ∀ e ∈ l, key e ≠ k) :
    l.filter (fun e => decide (key e = k)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro a ha hka
  exact h a ha (by simpa using hka)

/-! ## Counting over the lists of entries -/

theorem count_lregs_bmem {v : Nat × Lazy CSet} (x : Nat) :
    ∀ (b : List (Nat × Lazy CSet)), v ∈ b → (lregs v.2).count x ≤ (bregs b).count x
  | [], hv => absurd hv List.not_mem_nil
  | (o, l) :: rest, hv => by
    simp only [bregs, List.count_append]
    rcases List.mem_cons.1 hv with rfl | hv
    · dsimp only; omega
    · have := count_lregs_bmem x rest hv; omega

theorem count_lregs_fmem {v : Lazy.ForkE CSet} (x : Nat) :
    ∀ (f : List (Lazy.ForkE CSet)), v ∈ f → (lregs v.1.2 ++ lregs v.2.2).count x ≤ (fregs f).count x
  | [], hv => absurd hv List.not_mem_nil
  | ((oy, y), (on, n)) :: rest, hv => by
    simp only [fregs, List.count_append]
    rcases List.mem_cons.1 hv with rfl | hv
    · simp only [List.count_append]; omega
    · have := count_lregs_fmem x rest hv; simp only [List.count_append] at this; omega

theorem bregs_filter_one (x : Nat) (k : Nat) (v : Nat × Lazy CSet) (b : List (Nat × Lazy CSet))
    (h : b.filter (fun e => decide (e.1 = k)) = [v]) :
    (bregs (b.filter (fun e => decide (e.1 = k)))).count x = (lregs v.2).count x := by
  rw [h]; simp [bregs]

/-- Cutting off one key from a list of keys. -/
theorem bregs_filter_cons (x ob : Nat) (K : List Nat) (hk : ob ∉ K) : ∀ b : List (Nat × Lazy CSet),
    (bregs (b.filter fun e => decide (e.1 ∈ ob :: K))).count x =
      (bregs (b.filter fun e => decide (e.1 = ob))).count x + (bregs (b.filter fun e => decide (e.1 ∈ K))).count x
  | [] => by simp [bregs]
  | (o, l) :: rest => by
    have ih := bregs_filter_cons x ob K hk rest
    simp only [List.filter_cons]
    by_cases h1 : o = ob
    · subst h1
      have h2 : o ∉ K := hk
      simp [h2, bregs, List.count_append] at ih ⊢; omega
    · by_cases h2 : o ∈ K
      · simp [h1, h2, bregs, List.count_append] at ih ⊢; omega
      · simp [h1, h2] at ih ⊢; omega

theorem fregs_filter_cons (x ob : Nat) (K : List Nat) (hk : ob ∉ K) : ∀ f : List (Lazy.ForkE CSet),
    (fregs (f.filter fun e => decide (e.1.1 ∈ ob :: K))).count x =
      (fregs (f.filter fun e => decide (e.1.1 = ob))).count x + (fregs (f.filter fun e => decide (e.1.1 ∈ K))).count x
  | [] => by simp [fregs]
  | ((oy, y), (on, n)) :: rest => by
    have ih := fregs_filter_cons x ob K hk rest
    simp only [List.filter_cons]
    by_cases h1 : oy = ob
    · subst h1
      have h2 : oy ∉ K := hk
      simp [h2, fregs, List.count_append] at ih ⊢; omega
    · by_cases h2 : oy ∈ K
      · simp [h1, h2, fregs, List.count_append] at ih ⊢; omega
      · simp [h1, h2] at ih ⊢; omega

theorem bkeys_mem {v : Nat × Lazy CSet} : ∀ (b : List (Nat × Lazy CSet)), BKeys b → v ∈ b → LKeys v.2
  | [], _, hv => absurd hv List.not_mem_nil
  | (o, l) :: rest, ⟨hl, hr⟩, hv => by
    rcases List.mem_cons.1 hv with rfl | hv
    · exact hl
    · exact bkeys_mem rest hr hv

theorem fkeys_mem {v : Lazy.ForkE CSet} : ∀ (f : List (Lazy.ForkE CSet)), FKeys f → v ∈ f → LKeys v.1.2 ∧ LKeys v.2.2
  | [], _, hv => absurd hv List.not_mem_nil
  | ((oy, y), (on, n)) :: rest, ⟨hy, hn, hr⟩, hv => by
    rcases List.mem_cons.1 hv with rfl | hv
    · exact ⟨hy, hn⟩
    · exact fkeys_mem rest hr hv

theorem blabs_mem {v : Nat × Lazy CSet} {o : Nat} : ∀ (b : List (Nat × Lazy CSet)), v ∈ b →
    (o = v.1 ∨ o ∈ llabs v.2) → o ∈ blabs b
  | [], hv, _ => absurd hv List.not_mem_nil
  | (ob, l) :: rest, hv, ho => by
    simp only [blabs, List.mem_cons, List.mem_append]
    rcases List.mem_cons.1 hv with rfl | hv
    · rcases ho with ho | ho
      · exact Or.inl ho
      · exact Or.inr (Or.inl ho)
    · exact Or.inr (Or.inr (blabs_mem rest hv ho))

theorem flabs_mem {v : Lazy.ForkE CSet} {o : Nat} : ∀ (f : List (Lazy.ForkE CSet)), v ∈ f →
    (o = v.1.1 ∨ o = v.2.1 ∨ o ∈ llabs v.1.2 ∨ o ∈ llabs v.2.2) → o ∈ flabs f
  | [], hv, _ => absurd hv List.not_mem_nil
  | ((oy, y), (on, n)) :: rest, hv, ho => by
    simp only [flabs, List.mem_cons, List.mem_append]
    rcases List.mem_cons.1 hv with rfl | hv
    · rcases ho with ho | ho | ho | ho
      · exact Or.inl ho
      · exact Or.inr (Or.inl ho)
      · exact Or.inr (Or.inr (Or.inl ho))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ho)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (flabs_mem rest hv ho))))

/-- Two lists together with no register twice: the counts. -/
theorem nodup_of_count_le {A B : List Nat} (hB : B.Nodup) (h : ∀ x, A.count x ≤ B.count x) : A.Nodup := by
  rw [List.nodup_iff_count] at hB ⊢
  intro x; have := h x; have := hB x; omega

theorem below_of_count_le {A B : List Nat} {k : Nat} (hB : ∀ x ∈ B, x < k) (h : ∀ x, A.count x ≤ B.count x) :
    ∀ x ∈ A, x < k := fun x hx => hB x (List.count_pos_iff.1 (Nat.lt_of_lt_of_le (List.count_pos_iff.2 hx) (h x)))

/-! ## The root -/

theorem copyNeed_sub {a b : Need} {ops : List Pole} {g g' : Gen (TreapMap mugF)} {x : Need × List Pole}
    (hn : (flattenNeed a ++ flattenNeed b).Nodup) (hb : ∀ y ∈ flattenNeed a ++ flattenNeed b, y < g.re)
    (h : copyNeed a b ops g = some (x, g')) :
    g.re ≤ g'.re ∧ Sub (flattenNeed a ++ flattenNeed b) g.re g'.re (flattenNeed x.1) := by
  obtain ⟨le, mem⟩ := copy_mem h
  have dab : Distinct (Need.pair a b) := by
    rw [distinct_iff_nodup]; exact hn
  have na : NB g.re a := fun y hy => hb y (List.mem_append_left _ ((mem_flat a y).2 hy))
  have nb : NB g.re b := fun y hy => hb y (List.mem_append_right _ ((mem_flat b y).2 hy))
  have dx := copyNeed_dist a b ops g g' x h dab na nb
  refine ⟨le, sub_of_nodup ((distinct_iff_nodup _).1 dx) fun y hy => ?_⟩
  rcases mem y ((mem_flat _ y).1 hy) with (e | e) | e
  · exact Or.inl (List.mem_append_left _ ((mem_flat a y).2 e))
  · exact Or.inl (List.mem_append_right _ ((mem_flat b y).2 e))
  · exact Or.inr e

/-! ## The merge -/

/-- What the merge returns. -/
structure MergeB (bf bs r : List (Nat × Lazy CSet)) (a c : Nat) : Prop where
  le : a ≤ c
  sub : Sub (bregs bf ++ bregs (bs.filter fun e => decide (e.1 ∈ bf.map (fun e => e.1)))) a c (bregs r)
  keys : BKeys r
  map : r.map (fun e => e.1) = bf.map (fun e => e.1)
  labs : ∀ o ∈ blabs r, o ∈ blabs bf ∨ o ∈ blabs bs

structure MergeF (ff fs r : List (Lazy.ForkE CSet)) (a c : Nat) : Prop where
  le : a ≤ c
  sub : Sub (fregs ff ++ fregs (fs.filter fun e => decide (e.1.1 ∈ ff.map (fun e => e.1.1)))) a c (fregs r)
  keys : FKeys r
  map : r.map (fun e => e.1.1) = ff.map (fun e => e.1.1)
  labs : ∀ o ∈ flabs r, o ∈ flabs ff ∨ o ∈ flabs fs

/-- What `+copy-lazy` returns. -/
structure CopyR (f s r : Lazy CSet) (a c : Nat) : Prop where
  le : a ≤ c
  sub : Sub (lregs f ++ lregs s) a c (lregs r)
  keys : LKeys r
  labs : ∀ o ∈ llabs r, o ∈ llabs f ∨ o ∈ llabs s

/-- What the fork part and the bond part of `+copy-lazy` return. -/
structure PartF (ff fs r : List (Lazy.ForkE CSet)) (a c : Nat) : Prop where
  le : a ≤ c
  sub : Sub (fregs ff ++ fregs fs) a c (fregs r)
  keys : FKeys r
  nd : (r.map fun e => e.1.1).Nodup
  labs : ∀ o ∈ flabs r, o ∈ flabs ff ∨ o ∈ flabs fs

structure PartB (bf bs r : List (Nat × Lazy CSet)) (a c : Nat) : Prop where
  le : a ≤ c
  sub : Sub (bregs bf ++ bregs bs) a c (bregs r)
  keys : BKeys r
  nd : (r.map fun e => e.1).Nodup
  labs : ∀ o ∈ blabs r, o ∈ blabs bf ∨ o ∈ blabs bs

/-- The keys of the merged list and of the entries it appends. -/
theorem nodup_keys_merge {β : Type} (key : β → Nat) (A B : List β) (hA : (A.map key).Nodup) (hB : (B.map key).Nodup) :
    ((A.map key) ++ ((B.filter fun e => !decide (key e ∈ A.map key)).map key)).Nodup := by
  rw [List.nodup_append]
  refine ⟨hA, ((List.filter_sublist).map _).nodup hB, fun a ha b hb e => ?_⟩
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hb
  have := (List.mem_filter.1 hv).2
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
  exact this (e ▸ ha)

/-- **The fork part of `+copy-lazy`**, given what the merge returns. -/
theorem forkPart_of {ff fs r : List (Lazy.ForkE CSet)} {g g' : Gen (TreapMap mugF)}
    (kf1 : (ff.map fun e => e.1.1).Nodup) (ks1 : (fs.map fun e => e.1.1).Nodup) (kf3 : FKeys ff) (ks3 : FKeys fs)
    (hM : ∀ m g'', Lazy.mergeForks (Lazy.index (Map := TreapMap mugF) (fun e : Lazy.ForkE CSet => e.1.1) fs) ff g
      = some (m, g'') → MergeF ff fs m g.re g''.re)
    (e : forkPart ff fs g = some (r, g')) : PartF ff fs r g.re g'.re := by
  unfold forkPart at e
  split at e
  · rename_i hfs
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    simp only [List.isEmpty_iff] at hfs; subst hfs
    exact ⟨Nat.le_refl _, by simpa [fregs] using sub_refl (fregs ff) g.re g.re, kf3, kf1, fun o ho => Or.inl ho⟩
  · split at e
    · rename_i _ hff
      simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      simp only [List.isEmpty_iff] at hff; subst hff
      exact ⟨Nat.le_refl _, by simpa [fregs] using sub_refl (fregs fs) g.re g.re, ks3, ks1, fun o ho => Or.inr ho⟩
    · obtain ⟨m, g5, e5, e⟩ := bind_some e
      simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      have M := hM m g5 e5
      have hu : (fs.filter fun e => !(Lazy.seen (S := CSet) (fun e : Lazy.ForkE CSet => e.1.1) ff e.1.1))
          = fs.filter fun e => !decide (e.1.1 ∈ ff.map fun e => e.1.1) := by
        apply List.filter_congr; intro e _; rw [seen_iff]
      rw [hu]
      refine ⟨M.le, fun x => ?_, fkeys_append _ _ M.keys (fkeys_filter _ fs ks3), ?_, fun o ho => ?_⟩
      · have h1 := M.sub x
        have h2 := fregs_filter_split (fun e : Lazy.ForkE CSet => decide (e.1.1 ∈ ff.map fun e => e.1.1)) x fs
        simp only [fregs_append, List.count_append] at h1 h2 ⊢
        omega
      · rw [List.map_append, M.map]; exact nodup_keys_merge (fun e : Lazy.ForkE CSet => e.1.1) ff fs kf1 ks1
      · rw [flabs_append, List.mem_append] at ho
        rcases ho with ho | ho
        · exact M.labs o ho
        · exact Or.inr (flabs_filter _ fs o ho)

/-- **The bond part of `+copy-lazy`**, given what the merge returns. -/
theorem bondPart_of {bf bs r : List (Nat × Lazy CSet)} {g g' : Gen (TreapMap mugF)}
    (kf2 : (bf.map fun e => e.1).Nodup) (ks2 : (bs.map fun e => e.1).Nodup) (kf4 : BKeys bf) (ks4 : BKeys bs)
    (hM : ∀ m g'', Lazy.mergeBonds (Lazy.index (Map := TreapMap mugF) (fun e : Nat × Lazy CSet => e.1) bs) bf g
      = some (m, g'') → MergeB bf bs m g.re g''.re)
    (e : bondPart bf bs g = some (r, g')) : PartB bf bs r g.re g'.re := by
  unfold bondPart at e
  split at e
  · rename_i hbs
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    simp only [List.isEmpty_iff] at hbs; subst hbs
    exact ⟨Nat.le_refl _, by simpa [bregs] using sub_refl (bregs bf) g.re g.re, kf4, kf2, fun o ho => Or.inl ho⟩
  · split at e
    · rename_i _ hbf
      simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      simp only [List.isEmpty_iff] at hbf; subst hbf
      exact ⟨Nat.le_refl _, by simpa [bregs] using sub_refl (bregs bs) g.re g.re, ks4, ks2, fun o ho => Or.inr ho⟩
    · obtain ⟨m, g5, e5, e⟩ := bind_some e
      simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      have M := hM m g5 e5
      have hu : (bs.filter fun e => !(Lazy.seen (S := CSet) (fun e : Nat × Lazy CSet => e.1) bf e.1))
          = bs.filter fun e => !decide (e.1 ∈ bf.map fun e => e.1) := by
        apply List.filter_congr; intro e _; rw [seen_iff]
      rw [hu]
      refine ⟨M.le, fun x => ?_, bkeys_append _ _ M.keys (bkeys_filter _ bs ks4), ?_, fun o ho => ?_⟩
      · have h1 := M.sub x
        have h2 := bregs_filter_split (fun e : Nat × Lazy CSet => decide (e.1 ∈ bf.map fun e => e.1)) x bs
        simp only [bregs_append, List.count_append] at h1 h2 ⊢
        omega
      · rw [List.map_append, M.map]; exact nodup_keys_merge (fun e : Nat × Lazy CSet => e.1) bf bs kf2 ks2
      · rw [blabs_append, List.mem_append] at ho
        rcases ho with ho | ho
        · exact M.labs o ho
        · exact Or.inr (blabs_filter _ bs o ho)

theorem mem_fregs_tail {x : Nat} {e : Lazy.ForkE CSet} {rest fs : List (Lazy.ForkE CSet)}
    (h : x ∈ fregs rest ++ fregs fs) : x ∈ fregs (e :: rest) ++ fregs fs := by
  obtain ⟨⟨oy, y⟩, ⟨on, n⟩⟩ := e
  simp only [fregs, List.mem_append] at h ⊢
  rcases h with h | h
  · exact Or.inl (Or.inr (Or.inr h))
  · exact Or.inr h

theorem mem_bregs_tail {x : Nat} {e : Nat × Lazy CSet} {rest bs : List (Nat × Lazy CSet)}
    (h : x ∈ bregs rest ++ bregs bs) : x ∈ bregs (e :: rest) ++ bregs bs := by
  obtain ⟨o, l⟩ := e
  simp only [bregs, List.mem_append] at h ⊢
  rcases h with h | h
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

mutual
/-- **`+copy-lazy` on two lazy needs with their keys, no register twice in
the two and below the counter.** -/
theorem copy_regs : ∀ (f : Lazy CSet) (o : Nat) (s : Lazy CSet) (g g' : Gen (TreapMap mugF)) (r : Lazy CSet),
    LKeys f → LKeys s → (lregs f ++ lregs s).Nodup → (∀ x ∈ lregs f ++ lregs s, x < g.re) →
    Lazy.copyLazyL o f s g = some (r, g') → CopyR f s r g.re g'.re
  | Lazy.mk sf ff bf, o, Lazy.mk ss fs bs, g, g', r, kf, ks, hn, hb, h => by
    rw [copyLazyL_eq] at h
    obtain ⟨kf1, kf2, kf3, kf4⟩ := kf
    obtain ⟨ks1, ks2, ks3, ks4⟩ := ks
    have cnt : ∀ x, (lregs (Lazy.mk sf ff bf) ++ lregs (Lazy.mk ss fs bs)).count x =
        (flattenNeed sf.ned ++ flattenNeed ss.ned).count x + (fregs ff ++ fregs fs).count x +
          (bregs bf ++ bregs bs).count x := fun x => by
      simp only [lregs, List.count_append]; omega
    have nd : ∀ (A : List Nat), (∀ x, A.count x ≤ (lregs (Lazy.mk sf ff bf) ++ lregs (Lazy.mk ss fs bs)).count x) →
        A.Nodup ∧ ∀ x ∈ A, x < g.re :=
      fun A hA => ⟨nodup_of_count_le hn hA, below_of_count_le hb hA⟩
    obtain ⟨⟨ned, ops⟩, g1, e1, h⟩ := bind_some h
    obtain ⟨n1, b1⟩ := nd (flattenNeed sf.ned ++ flattenNeed ss.ned) fun x => by rw [cnt]; omega
    obtain ⟨l1, S1⟩ := copyNeed_sub n1 b1 e1
    obtain ⟨u, g2, e2, h⟩ := bind_some h
    have r2 := addOps_re e2
    obtain ⟨fk, g3, e3, h⟩ := bind_some h
    obtain ⟨bd, g4, e4, h⟩ := bind_some h
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨nF, bF⟩ := nd (fregs ff ++ fregs fs) fun x => by rw [cnt]; omega
    obtain ⟨nB, bB⟩ := nd (bregs bf ++ bregs bs) fun x => by rw [cnt]; omega
    have F := forkPart_of kf1 ks1 kf3 ks3 (fun m g'' e5 => mforks_regs ff fs g2 g'' m kf1 ks1 kf3 ks3 nF
      (fun x hx => Nat.lt_of_lt_of_le (bF x hx) (by omega)) e5) e3
    have B := bondPart_of kf2 ks2 kf4 ks4 (fun m g'' e5 => mbonds_regs bf bs g3 g'' m kf2 ks2 kf4 ks4 nB
      (fun x hx => Nat.lt_of_lt_of_le (bB x hx) (by have := F.le; omega)) e5) e4
    refine ⟨by have := F.le; have := B.le; omega, fun x => ?_, ⟨F.nd, B.nd, F.keys, B.keys⟩, fun o ho => ?_⟩
    · have h1 := S1 x; have h2 := F.sub x; have h3 := B.sub x; have h4 := cnt x
      have := fr_add (x := x) l1 (show g1.re ≤ g3.re by have := F.le; omega)
      have := fr_add (x := x) (show g.re ≤ g3.re by have := F.le; omega) B.le
      rw [r2] at h2
      simp only [lregs, List.count_append] at h1 h2 h3 h4 ⊢
      omega
    · simp only [llabs, List.mem_append] at ho ⊢
      rcases ho with ho | ho
      · rcases F.labs o ho with e | e
        · exact Or.inl (Or.inl e)
        · exact Or.inr (Or.inl e)
      · rcases B.labs o ho with e | e
        · exact Or.inl (Or.inr e)
        · exact Or.inr (Or.inr e)

theorem mforks_regs : ∀ (ff fs : List (Lazy.ForkE CSet)) (g g' : Gen (TreapMap mugF)) (r : List (Lazy.ForkE CSet)),
    (ff.map fun e => e.1.1).Nodup → (fs.map fun e => e.1.1).Nodup → FKeys ff → FKeys fs →
    (fregs ff ++ fregs fs).Nodup → (∀ x ∈ fregs ff ++ fregs fs, x < g.re) →
    Lazy.mergeForks (Lazy.index (Map := TreapMap mugF) (fun e : Lazy.ForkE CSet => e.1.1) fs) ff g = some (r, g') →
    MergeF ff fs r g.re g'.re
  | [], fs, g, g', r, _, _, _, _, _, _, h => by
    simp only [Lazy.mergeForks, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Nat.le_refl _, fun x => by simp [fregs], trivial, rfl, fun o ho => by simp [flabs] at ho⟩
  | ((oy, y), (on, n)) :: rest, fs, g, g', r, kf1, ks1, ⟨ky, kn, kr⟩, ks3, hn, hb, h => by
    simp only [Lazy.mergeForks] at h
    obtain ⟨e', g1, e1, h⟩ := bind_some h
    obtain ⟨r', g2, e2, h⟩ := bind_some h
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [List.map_cons, List.nodup_cons] at kf1
    obtain ⟨hoy, kf1⟩ := kf1
    -- the counts of the first list against the two together
    have cff : ∀ x, (fregs (((oy, y), (on, n)) :: rest)).count x =
        (lregs y).count x + (lregs n).count x + (fregs rest).count x := fun x => by
      simp only [fregs, List.count_append]; omega
    have ncr : (fregs rest ++ fregs fs).Nodup := nodup_of_count_le hn fun x => by
      have := cff x; simp only [List.count_append] at this ⊢; omega
    have hfl := fregs_filter_cons (ob := oy) (K := rest.map fun e => e.1.1) (hk := hoy)
    cases hg : (HoonMap.get (Lazy.index (Map := TreapMap mugF) (fun e : Lazy.ForkE CSet => e.1.1) fs) oy
        : Option (Lazy.ForkE CSet)) with
    | none =>
      simp only [hg, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e1
      obtain ⟨rfl, rfl⟩ := e1
      have hnone := filter_key_none (fun e : Lazy.ForkE CSet => e.1.1) fs (index_get_none _ fs oy hg)
      have R := mforks_regs rest fs g g2 r' kf1 ks1 kr ks3 ncr
        (fun x hx => hb x (mem_fregs_tail hx)) e2
      refine ⟨R.le, fun x => ?_, ⟨ky, kn, R.keys⟩, by simp [R.map], fun o ho => ?_⟩
      · have h1 := R.sub x; have h2 := hfl x fs; have h3 := cff x
        rw [hnone] at h2
        simp only [List.map_cons, fregs, List.count_append, List.count_nil] at h1 h2 h3 ⊢
        omega
      · simp only [flabs, List.mem_cons, List.mem_append] at ho
        rcases ho with ho | ho | ho | ho | ho
        · exact Or.inl (by simp [flabs, ho])
        · exact Or.inl (by simp [flabs, ho])
        · exact Or.inl (by simp [flabs, ho])
        · exact Or.inl (by simp [flabs, ho])
        · rcases R.labs o ho with e | e
          · exact Or.inl (by simp [flabs, e])
          · exact Or.inr e
    | some v =>
      obtain ⟨⟨oy', my⟩, ⟨mon, mn⟩⟩ := v
      obtain ⟨hv, hvk⟩ := index_get_key _ fs oy _ hg
      simp only at hvk
      subst hvk
      have hone := filter_key_single (fun e : Lazy.ForkE CSet => e.1.1) fs ks1 hv rfl
      simp only [hg] at e1
      split at e1
      · rename_i hon
        subst hon
        obtain ⟨y', g3, e3, e1⟩ := bind_some e1
        obtain ⟨n', g4, e4, e1⟩ := bind_some e1
        simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e1
        obtain ⟨rfl, rfl⟩ := e1
        have cm := fun x => count_lregs_fmem (v := ((oy', my), (on, mn))) x fs hv
        obtain ⟨kmy, kmn⟩ := fkeys_mem fs ks3 hv
        have Y := copy_regs y oy' my g g3 y' ky kmy
          (nodup_of_count_le hn fun x => by
            have := cff x; have := cm x; simp only [List.count_append] at this ⊢; omega)
          (below_of_count_le hb fun x => by
            have := cff x; have := cm x; simp only [List.count_append] at this ⊢; omega) e3
        have N := copy_regs n on mn g3 g4 n' kn kmn
          (nodup_of_count_le hn fun x => by
            have := cff x; have := cm x; simp only [List.count_append] at this ⊢; omega)
          (fun x hx => Nat.lt_of_lt_of_le (below_of_count_le hb (fun x => by
            have := cff x; have := cm x; simp only [List.count_append] at this ⊢; omega) x hx) Y.le) e4
        have R := mforks_regs rest fs g4 g2 r' kf1 ks1 kr ks3 ncr
          (fun x hx => Nat.lt_of_lt_of_le (hb x (mem_fregs_tail hx)) (Nat.le_trans Y.le N.le)) e2
        refine ⟨by have := Y.le; have := N.le; have := R.le; omega, fun x => ?_, ⟨Y.keys, N.keys, R.keys⟩,
          by simp [R.map], fun o ho => ?_⟩
        · have h1 := Y.sub x; have h2 := N.sub x; have h3 := R.sub x; have h4 := hfl x fs; have h5 := cff x
          rw [hone] at h4
          have := fr_add (x := x) Y.le N.le
          have := fr_add (x := x) (Nat.le_trans Y.le N.le) R.le
          simp only [List.map_cons, fregs, List.count_append, List.count_nil] at h1 h2 h3 h4 h5 ⊢
          omega
        · simp only [flabs, List.mem_cons, List.mem_append] at ho
          rcases ho with ho | ho | ho | ho | ho
          · exact Or.inl (by simp [flabs, ho])
          · exact Or.inl (by simp [flabs, ho])
          · rcases Y.labs o ho with e | e
            · exact Or.inl (by simp [flabs, e])
            · exact Or.inr (flabs_mem fs hv (Or.inr (Or.inr (Or.inl e))))
          · rcases N.labs o ho with e | e
            · exact Or.inl (by simp [flabs, e])
            · exact Or.inr (flabs_mem fs hv (Or.inr (Or.inr (Or.inr e))))
          · rcases R.labs o ho with e | e
            · exact Or.inl (by simp [flabs, e])
            · exact Or.inr e
      · cases e1

theorem mbonds_regs : ∀ (bf bs : List (Nat × Lazy CSet)) (g g' : Gen (TreapMap mugF)) (r : List (Nat × Lazy CSet)),
    (bf.map fun e => e.1).Nodup → (bs.map fun e => e.1).Nodup → BKeys bf → BKeys bs →
    (bregs bf ++ bregs bs).Nodup → (∀ x ∈ bregs bf ++ bregs bs, x < g.re) →
    Lazy.mergeBonds (Lazy.index (Map := TreapMap mugF) (fun e : Nat × Lazy CSet => e.1) bs) bf g = some (r, g') →
    MergeB bf bs r g.re g'.re
  | [], bs, g, g', r, _, _, _, _, _, _, h => by
    simp only [Lazy.mergeBonds, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Nat.le_refl _, fun x => by simp [bregs], trivial, rfl, fun o ho => by simp [blabs] at ho⟩
  | (ob, l) :: rest, bs, g, g', r, kf1, ks1, ⟨kl, kr⟩, ks3, hn, hb, h => by
    simp only [Lazy.mergeBonds] at h
    obtain ⟨e', g1, e1, h⟩ := bind_some h
    obtain ⟨r', g2, e2, h⟩ := bind_some h
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [List.map_cons, List.nodup_cons] at kf1
    obtain ⟨hob, kf1⟩ := kf1
    have cbf : ∀ x, (bregs ((ob, l) :: rest)).count x = (lregs l).count x + (bregs rest).count x := fun x => by
      simp only [bregs, List.count_append]
    have ncr : (bregs rest ++ bregs bs).Nodup := nodup_of_count_le hn fun x => by
      have := cbf x; simp only [List.count_append] at this ⊢; omega
    have hfl := bregs_filter_cons (ob := ob) (K := rest.map fun e => e.1) (hk := hob)
    cases hg : (HoonMap.get (Lazy.index (Map := TreapMap mugF) (fun e : Nat × Lazy CSet => e.1) bs) ob
        : Option (Nat × Lazy CSet)) with
    | none =>
      simp only [hg, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e1
      obtain ⟨rfl, rfl⟩ := e1
      have hnone := filter_key_none (fun e : Nat × Lazy CSet => e.1) bs (index_get_none _ bs ob hg)
      have R := mbonds_regs rest bs g g2 r' kf1 ks1 kr ks3 ncr
        (fun x hx => hb x (mem_bregs_tail hx)) e2
      refine ⟨R.le, fun x => ?_, ⟨kl, R.keys⟩, by simp [R.map], fun o ho => ?_⟩
      · have h1 := R.sub x; have h2 := hfl x bs; have h3 := cbf x
        rw [hnone] at h2
        simp only [List.map_cons, bregs, List.count_append, List.count_nil] at h1 h2 h3 ⊢
        omega
      · simp only [blabs, List.mem_cons, List.mem_append] at ho
        rcases ho with ho | ho | ho
        · exact Or.inl (by simp [blabs, ho])
        · exact Or.inl (by simp [blabs, ho])
        · rcases R.labs o ho with e | e
          · exact Or.inl (by simp [blabs, e])
          · exact Or.inr e
    | some v =>
      obtain ⟨ob', m⟩ := v
      obtain ⟨hv, hvk⟩ := index_get_key _ bs ob _ hg
      simp only at hvk
      subst hvk
      have hone := filter_key_single (fun e : Nat × Lazy CSet => e.1) bs ks1 hv rfl
      simp only [hg] at e1
      obtain ⟨l', g3, e3, e1⟩ := bind_some e1
      simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e1
      obtain ⟨rfl, rfl⟩ := e1
      have cm := fun x => count_lregs_bmem (v := (ob', m)) x bs hv
      have km := bkeys_mem bs ks3 hv
      have L := copy_regs l ob' m g g3 l' kl km
        (nodup_of_count_le hn fun x => by
          have := cbf x; have := cm x; simp only [List.count_append] at this ⊢; omega)
        (below_of_count_le hb fun x => by
          have := cbf x; have := cm x; simp only [List.count_append] at this ⊢; omega) e3
      have R := mbonds_regs rest bs g3 g2 r' kf1 ks1 kr ks3 ncr
        (fun x hx => Nat.lt_of_lt_of_le (hb x (mem_bregs_tail hx)) L.le) e2
      refine ⟨by have := L.le; have := R.le; omega, fun x => ?_, ⟨L.keys, R.keys⟩, by simp [R.map], fun o ho => ?_⟩
      · have h1 := L.sub x; have h3 := R.sub x; have h4 := hfl x bs; have h5 := cbf x
        rw [hone] at h4
        have := fr_add (x := x) L.le R.le
        simp only [List.map_cons, bregs, List.count_append, List.count_nil] at h1 h3 h4 h5 ⊢
        omega
      · simp only [blabs, List.mem_cons, List.mem_append] at ho
        rcases ho with ho | ho | ho
        · exact Or.inl (by simp [blabs, ho])
        · rcases L.labs o ho with e | e
          · exact Or.inl (by simp [blabs, e])
          · exact Or.inr (blabs_mem bs hv (Or.inr e))
        · rcases R.labs o ho with e | e
          · exact Or.inl (by simp [blabs, e])
          · exact Or.inr e
end

end Compiler
end Formalization
