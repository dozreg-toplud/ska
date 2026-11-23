import lemmas.Ska.Bridge

/-!
# The construction invariant of the state-passing analysis

What every arm of `Analysis.lean` keeps: the graph is well formed, the memo
of the poke has well-formed products, the keys of `order` are the members of
the stack, each in the graph, and the stack has no duplicates (`SInv`).  Each
arm changes the graph only by the abstract writes of `GStepR`, and leaves
alone the entries and the `order` of the functions below it on the stack
(`Keep`).  So the identity a run is about keeps its entry during its own
`fol-loop` (`hold`), the answers of `resolve` on a well-formed subject sock
have well-formed products, and `resolve` keeps the invariant (`ResOK` for
`P_wf`), which discharges the hypotheses of `run_folTopR` and
`runEnd_gStepR`.
-/

namespace Formalization
namespace SkaModel
namespace Ana

open Nock

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-! ## Maps and sets -/

namespace Treap

theorem get_ins {κ : Type} [DecidableEq κ] (s : M κ Unit) (k k' : κ) :
    get (ins s k) k' = if k' = k then some () else get s k' := get_put _ _ _ _

theorem has_iff {κ ν : Type} [DecidableEq κ] (m : M κ ν) (k : κ) : has m k = true ↔ ∃ v, get m k = some v := by
  unfold has; cases get m k <;> simp

theorem has_ins {κ : Type} [DecidableEq κ] (s : M κ Unit) (k k' : κ) :
    has (ins s k) k' = true ↔ k' = k ∨ has s k' = true := by
  simp only [has_iff, get_ins]
  split <;> simp_all

theorem has_silt_aux {κ : Type} [DecidableEq κ] : ∀ (l : List κ) (s : M κ Unit) (k : κ),
    has (l.foldl ins s) k = true ↔ k ∈ l ∨ has s k = true
  | [], s, k => by simp
  | x :: l, s, k => by
    simp only [List.foldl_cons, has_silt_aux l (ins s x) k, has_ins, List.mem_cons]
    constructor
    · rintro (h | h | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rintro ((h | h) | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

theorem has_silt {κ : Type} [DecidableEq κ] (l : List κ) (k : κ) :
    has (silt l : M κ Unit) k = true ↔ k ∈ l := by
  unfold silt
  rw [has_silt_aux]
  simp [has, get_empty]

theorem get_foldl_del {κ ν μ : Type} [DecidableEq κ] : ∀ (l : List (κ × μ)) (a : M κ ν) (k : κ),
    get (l.foldl (fun s k => del s k.1) a) k = if k ∈ l.map (·.1) then none else get a k
  | [], a, k => by simp
  | x :: l, a, k => by
    simp only [List.foldl_cons, get_foldl_del l (del a x.1) k, get_del, List.map_cons, List.mem_cons]
    by_cases h1 : k ∈ l.map (·.1) <;> by_cases h2 : k = x.1 <;> simp [h1, h2]

theorem get_dif {κ ν μ : Type} [DecidableEq κ] (a : M κ ν) (b : M κ μ) (k : κ) :
    get (dif a b) k = if has b k = true then none else get a k := by
  unfold dif
  rw [get_foldl_del]
  have e : (k ∈ (tap b).map (·.1)) ↔ has b k = true := by
    rw [has_iff]
    constructor
    · intro h
      obtain ⟨⟨k', v⟩, hm, rfl⟩ := List.mem_map.mp h
      exact ⟨v, (mem_tap b k' v).mp hm⟩
    · rintro ⟨v, hv⟩
      exact List.mem_map.mpr ⟨(k, v), (mem_tap b k v).mpr hv, rfl⟩
  by_cases h : has b k = true
  · rw [if_pos (e.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (e.mp h')), if_neg h]

end Treap

/-! ## The stack -/

theorem above_eq {id : Ident} : ∀ {stk : List Ident} {ab : List Ident}, above id stk = some ab →
    ∃ ab0 rest, ab = ab0 ++ [id] ∧ stk = ab0 ++ id :: rest ∧ id ∉ ab0
  | [], _, h => by simp [above] at h
  | i :: stk, ab, h => by
    unfold above at h
    by_cases e : id = i
    · rw [if_pos e] at h
      cases h; subst e
      exact ⟨[], stk, rfl, rfl, by simp⟩
    · rw [if_neg e] at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨ab', h', rfl⟩ := h
      obtain ⟨ab0, rest, rfl, rfl, hn⟩ := above_eq h'
      exact ⟨i :: ab0, rest, rfl, rfl, by simp only [List.mem_cons, not_or]; exact ⟨e, hn⟩⟩

theorem above_of_mem {id : Ident} : ∀ {stk : List Ident}, id ∈ stk → ∃ ab, above id stk = some ab
  | [], h => by simp at h
  | i :: stk, h => by
    unfold above
    by_cases e : id = i
    · rw [if_pos e]; exact ⟨_, rfl⟩
    · rw [if_neg e]
      have : id ∈ stk := by simp [e] at h; exact h
      obtain ⟨ab, hab⟩ := above_of_mem this
      exact ⟨_, by rw [hab]; rfl⟩

/-! ## `+recursive-call` -/

theorem recLoop_cases {he : Sock → Sock → Bool} {heOn : Bool} {g : Sock × Noun → Option Datum}
    {kid : Sock × Noun} : ∀ {stk : List (Sock × Noun)} {b : Bool} {i : Sock × Noun},
    recLoop he heOn g kid stk = some (some (b, i)) →
    (b = true ∧ i ∈ stk) ∨ (b = false ∧ ∃ j ∈ stk, msgSock kid.1 j.1 = some i.1 ∧ i.2 = kid.2)
  | [], _, _, h => by simp [recLoop] at h
  | j :: stk, b, i, h => by
    unfold recLoop at h
    split at h
    · rcases recLoop_cases h with ⟨hb, hi⟩ | ⟨hb, j', hj', hm, he'⟩
      · exact Or.inl ⟨hb, List.mem_cons_of_mem _ hi⟩
      · exact Or.inr ⟨hb, j', List.mem_cons_of_mem _ hj', hm, he'⟩
    · split at h
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Or.inl ⟨rfl, List.mem_cons_self⟩
      · split at h
        · simp only [Option.map_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨m, hm, rfl, rfl⟩ := h
          exact Or.inr ⟨rfl, j, List.mem_cons_self, hm, rfl⟩
        · rcases recLoop_cases h with ⟨hb, hi⟩ | ⟨hb, j', hj', hm, he'⟩
          · exact Or.inl ⟨hb, List.mem_cons_of_mem _ hi⟩
          · exact Or.inr ⟨hb, j', List.mem_cons_of_mem _ hj', hm, he'⟩

theorem recursiveCall_cases {he : Sock → Sock → Bool} {th : Nat} {kid : Sock × Noun}
    {stk : List (Sock × Noun)} {g : Sock × Noun → Option Datum} {b : Bool} {i : Sock × Noun}
    (h : recursiveCall he th kid stk g = some (some (b, i))) :
    (b = true ∧ i ∈ stk) ∨ (b = false ∧ ∃ j ∈ stk, msgSock kid.1 j.1 = some i.1 ∧ i.2 = kid.2) :=
  recLoop_cases h

/-! ## `+git:mi` -/

/-- The memo has well-formed products. -/
def MemoWF (m : Memo M) : Prop :=
  ∀ f ms s e, Treap.get m f = some ms → Treap.get ms s = some e → WellFormed e.2.prod

/-- A hit of `+git:mi` is a memo entry patched for the subject sock. -/
theorem gitLoop_hit {s : Sock} : ∀ {l : List (Sock × (Ident × FDatum M))} {i : Ident} {d : FDatum M},
    gitLoop s l = some (some (i, d)) →
    ∃ k d0, (k, (i, d0)) ∈ l ∧ hitTest ⟨i.1, i.2, d0.core⟩ s = some true ∧
      d = { d0 with prod := (patchProd d0.prod d0.map s).sock, map := (patchProd d0.prod d0.map s).src }
  | [], _, _, h => by simp [gitLoop] at h
  | (k, (i0, d0)) :: l, i, d, h => by
    unfold gitLoop at h
    split at h
    · cases h
    · rename_i ht
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨k, d0, List.mem_cons_self, ht, rfl⟩
    · obtain ⟨k', d1, hm, ht, hd⟩ := gitLoop_hit h
      exact ⟨k', d1, List.mem_cons_of_mem _ hm, ht, hd⟩

theorem gitMi_hit {m : Memo M} {f : Noun} {s : Sock} {i : Ident} {d : FDatum M}
    (h : gitMi m f s = some (some (i, d))) :
    ∃ k d0, Treap.get (gutMi m f) k = some (i, d0) ∧ hitTest ⟨i.1, i.2, d0.core⟩ s = some true ∧
      d.core = patchDatum d0.core s ∧ d.prod = (patchDatum d0.core s).prod := by
  obtain ⟨k, d0, hm, ht, rfl⟩ := gitLoop_hit h
  exact ⟨k, d0, (Treap.mem_tap _ _ _).mp hm, ht, rfl, rfl⟩

theorem gitMi_wf {m : Memo M} (hm : MemoWF m) {f : Noun} {s : Sock} {i : Ident} {d : FDatum M}
    (hs : WellFormed s) (h : gitMi m f s = some (some (i, d))) : WellFormed d.prod := by
  obtain ⟨k, d0, hg, _, hc, hp⟩ := gitMi_hit h
  rw [hp]
  have hg' : Treap.get m f = some (gutMi m f) ∨ gutMi m f = Treap.empty := by
    unfold gutMi Treap.gut
    cases e : Treap.get m f <;> simp
  rcases hg' with hg' | hg'
  · exact wf_patchDatum (hm f _ k _ hg' hg) hs
  · rw [hg', Treap.get_empty] at hg; cases hg

theorem MemoWF.putMi {m : Memo M} (hm : MemoWF m) {i : Ident} {d : FDatum M} (hd : WellFormed d.prod) :
    MemoWF (putMi m i d) := by
  intro f ms s e h1 h2
  unfold Ana.putMi at h1
  rw [Treap.get_put] at h1
  split at h1
  · cases h1
    rw [Treap.get_put] at h2
    split at h2
    · cases h2; exact hd
    · unfold gutMi Treap.gut at h2
      rename_i hf _
      subst hf
      cases e' : Treap.get m i.2 with
      | none => rw [e'] at h2; simp [Treap.get_empty] at h2
      | some ms' => rw [e'] at h2; exact hm _ _ _ _ e' h2
  · exact hm _ _ _ _ h1 h2

theorem MemoWF.empty : MemoWF (Treap.empty : Memo M) := by
  intro f ms s e h; rw [Treap.get_empty] at h; cases h

/-! ## The invariant and the frame -/

/-- **The construction invariant of the state.** -/
structure SInv (st : SkaState M R) : Prop where
  g_wf : GraphWF (gCore st.g)
  done_wf : MemoWF st.done
  ord_g : ∀ i o, Treap.get st.order i = some o → ∃ d, Treap.get st.g i = some d
  ord_stk : ∀ i, (∃ o, Treap.get st.order i = some o) ↔ i ∈ st.stk
  nodup : st.stk.Nodup

theorem SInv.init (reg : R) : SInv (SkaState.init reg : SkaState M R) where
  g_wf := by
    intro i d h
    simp [gCore, SkaState.init, Treap.get_empty] at h
  done_wf := MemoWF.empty
  ord_g := by intro i o h; simp [SkaState.init, Treap.get_empty] at h
  ord_stk := by intro i; simp [SkaState.init, Treap.get_empty]
  nodup := List.nodup_nil

theorem SInv.mem_g {st : SkaState M R} (h : SInv st) {i : Ident} (hi : i ∈ st.stk) :
    ∃ d, Treap.get st.g i = some d := by
  obtain ⟨o, ho⟩ := (h.ord_stk i).mpr hi
  exact h.ord_g i o ho

theorem SInv.not_mem {st : SkaState M R} (h : SInv st) {i : Ident} (hg : Treap.get st.g i = none) :
    i ∉ st.stk := fun hi => by
  obtain ⟨d, hd⟩ := h.mem_g hi
  rw [hg] at hd; cases hd

theorem SInv.wf_stk {st : SkaState M R} (h : SInv st) {i : Ident} (hi : i ∈ st.stk) : WellFormed i.1 := by
  obtain ⟨d, hd⟩ := h.mem_g hi
  exact (h.g_wf i d.core (by simp [gCore, hd])).1

theorem SInv.wf_get {st : SkaState M R} (h : SInv st) {i : Ident} {d : FDatum M}
    (hd : Treap.get st.g i = some d) : WellFormed i.1 ∧ WellFormed d.prod :=
  h.g_wf i d.core (by simp [gCore, hd])

theorem SInv.wf_gitG {st : SkaState M R} (h : SInv st) (i : Ident) : WellFormed (gitG st.g i).prod := by
  unfold gitG Treap.gut
  cases e : Treap.get st.g i with
  | none => exact wf_void
  | some d => exact (h.wf_get e).2

/-- **What an arm leaves alone**: the stack `bo` stays at the bottom of the
stack with its `order`, and the graph is the same at the identities `bg`. -/
def Keep (bo : List Ident) (bg : Ident → Prop) (st st' : SkaState M R) : Prop :=
  (∃ l, st'.stk = l ++ bo) ∧ (∀ j ∈ bo, Treap.get st'.order j = Treap.get st.order j) ∧
    ∀ j, bg j → Treap.get st'.g j = Treap.get st.g j

theorem Keep.trans {bo : List Ident} {bg : Ident → Prop} {st st' st'' : SkaState M R}
    (h1 : Keep bo bg st st') (h2 : Keep bo bg st' st'') : Keep bo bg st st'' :=
  ⟨h2.1, fun j hj => (h2.2.1 j hj).trans (h1.2.1 j hj), fun j hj => (h2.2.2 j hj).trans (h1.2.2 j hj)⟩

theorem Keep.mono {bo : List Ident} {bg bg' : Ident → Prop} {st st' : SkaState M R}
    (h : Keep bo bg st st') (hb : ∀ j, bg' j → bg j) : Keep bo bg' st st' :=
  ⟨h.1, h.2.1, fun j hj => h.2.2 j (hb j hj)⟩

theorem gStepsR_trans {g g' g'' : Graph} (h1 : GStepsR g g') (h2 : GStepsR g' g'') : GStepsR g g'' := by
  induction h2 with
  | refl => exact h1
  | tail _ h ih => exact ih.tail h

theorem gStepsR_one {g g' : Graph} (h : GStepR g g') : GStepsR g g' := (GStepsR.refl g).tail h

/-! ## The writes of `+analyze` -/

/-- The write of a memo hit from an earlier poke. -/
theorem hit_ok {memoF : Memo M} (hmF : MemoWF memoF) {st : SkaState M R} (hi : SInv st) {id : Ident}
    {hit : Ident × FDatum M} (hw : WellFormed id.1) (hg : Treap.get st.g id = none)
    (h : gitMi memoF id.2 id.1 = some (some hit)) :
    let st' := { st with g := Treap.put st.g id hit.2, done := putMi st.done id hit.2 }
    SInv st' ∧ GStepsR (gCore st.g) (gCore st'.g) ∧ Keep st.stk (· ∈ st.stk) st st' := by
  obtain ⟨k, d0, hk, _, hc, hp⟩ := gitMi_hit (s := id.1) (i := hit.1) (d := hit.2) h
  have hwd : WellFormed hit.2.prod := gitMi_wf hmF hw h
  have hstep : GStepR (gCore st.g) (gCore (Treap.put st.g id hit.2)) := by
    rw [gCore_put, hc]
    obtain ⟨k', d1, hk1, _, _, _⟩ := gitMi_hit (s := id.1) (i := hit.1) (d := hit.2) h
    have hwd0 : WellFormed d0.prod := by
      have hg' : Treap.get memoF id.2 = some (gutMi memoF id.2) ∨ gutMi memoF id.2 = Treap.empty := by
        unfold gutMi Treap.gut
        cases e : Treap.get memoF id.2 <;> simp
      rcases hg' with hg' | hg'
      · exact hmF _ _ _ _ hg' hk
      · rw [hg', Treap.get_empty] at hk; cases hk
    exact GStepR.memo hw hwd0
  refine ⟨⟨hstep.wf hi.g_wf, hi.done_wf.putMi hwd, fun i o ho => ?_, hi.ord_stk, hi.nodup⟩,
    gStepsR_one hstep, ⟨⟨[], rfl⟩, fun _ _ => rfl, fun j hj => ?_⟩⟩
  · obtain ⟨d, hd⟩ := hi.ord_g i o ho
    simp only [Treap.get_put]
    split
    · exact ⟨_, rfl⟩
    · exact ⟨d, hd⟩
  · simp only [Treap.get_put]
    rw [if_neg]
    rintro rfl
    exact hi.not_mem hg hj

/-- The push of a new function. -/
theorem push_ok {st : SkaState M R} (hi : SInv st) {id : Ident} (hw : WellFormed id.1)
    (hg : Treap.get st.g id = none) (index : Nat) :
    let st' := { st with next := index + 1, order := Treap.put st.order id index, stk := id :: st.stk,
                         g := Treap.put st.g id FDatum.bunt }
    SInv st' ∧ GStepsR (gCore st.g) (gCore st'.g) ∧ Keep st.stk (· ∈ st.stk) st st' := by
  have hstep : GStepR (gCore st.g) (gCore (Treap.put st.g id FDatum.bunt)) := by
    rw [gCore_put, FDatum.bunt_core]; exact GStepR.start hw
  have hn := hi.not_mem hg
  refine ⟨⟨hstep.wf hi.g_wf, hi.done_wf, fun i o ho => ?_, fun i => ?_, List.nodup_cons.mpr ⟨hn, hi.nodup⟩⟩,
    gStepsR_one hstep, ⟨⟨[id], rfl⟩, fun j hj => ?_, fun j hj => ?_⟩⟩
  · simp only [Treap.get_put]
    split
    · exact ⟨_, rfl⟩
    · rw [Treap.get_put, if_neg ‹_›] at ho; exact hi.ord_g i o ho
  · simp only [Treap.get_put, List.mem_cons]
    split
    · rename_i e; exact ⟨fun _ => Or.inl e, fun _ => ⟨_, rfl⟩⟩
    · rename_i e; rw [hi.ord_stk i]; exact ⟨Or.inr, fun h => h.resolve_left e⟩
  · simp only [Treap.get_put]; rw [if_neg]; rintro rfl; exact hn hj
  · simp only [Treap.get_put]; rw [if_neg]; rintro rfl; exact hn hj

end Ana
end SkaModel
end Formalization
