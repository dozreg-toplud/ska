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

/-! ## The write of `+run` -/

theorem runEnd_fields (id : Ident) (data : FDatum M) (out : FolOut) (gs : GenS M R) :
    (runEnd id data out gs).2.order = gs.st.order ∧ (runEnd id data out gs).2.stk = gs.st.stk ∧
    (runEnd id data out gs).2.done = gs.st.done ∧
    (∃ dn, (runEnd id data out gs).2.g = Treap.put gs.st.g id dn) := by
  unfold runEnd
  simp only
  split <;> exact ⟨rfl, rfl, rfl, _, rfl⟩

/-- The write at the end of `+run` keeps the invariant. -/
theorem runEnd_ok {gs : GenS M R} (hi : SInv gs.st) {id : Ident} {data : FDatum M} {out : FolOut}
    (hstep : GStepR (gCore gs.st.g) (gCore (runEnd id data out gs).2.g)) :
    SInv (runEnd id data out gs).2 ∧ Keep gs.st.stk (· ≠ id) gs.st (runEnd id data out gs).2 := by
  obtain ⟨ho, hs, hd, dn, hg⟩ := runEnd_fields id data out gs
  refine ⟨⟨hstep.wf hi.g_wf, hd ▸ hi.done_wf, fun i o h => ?_, fun i => ?_, hs ▸ hi.nodup⟩,
    ⟨⟨[], by rw [hs]; rfl⟩, fun j _ => by rw [ho], fun j hj => by rw [hg, Treap.get_put, if_neg hj]⟩⟩
  · rw [ho] at h
    obtain ⟨d, e⟩ := hi.ord_g i o h
    rw [hg, Treap.get_put]
    split
    · exact ⟨_, rfl⟩
    · exact ⟨d, e⟩
  · rw [ho, hs]; exact hi.ord_stk i

/-! ## `+pop` -/

theorem FDatum.pop_core (d : FDatum M) :
    (if d.prod = Sock.void then { d with prod := Sock.dunno } else d).core =
      if d.core.prod = Sock.void then { d.core with prod := Sock.dunno } else d.core := by
  unfold FDatum.core; split <;> rfl

theorem popGo_ok {id : Ident} : ∀ (l : List Ident) (st st' : SkaState M R), st.stk = l → SInv st →
    popGo id l st = some st' →
    SInv st' ∧ GStepsR (gCore st.g) (gCore st'.g) ∧ (∃ pre, l = pre ++ id :: st'.stk) ∧
    ∀ j ∈ st'.stk, Treap.get st'.order j = Treap.get st.order j ∧ Treap.get st'.g j = Treap.get st.g j
  | [], _, _, _, _, h => by simp [popGo] at h
  | top :: rest, st, st', hl, hi, h => by
    unfold popGo at h
    simp only at h
    have htop : top ∈ st.stk := by rw [hl]; exact List.mem_cons_self
    obtain ⟨d0, hd0⟩ := hi.mem_g htop
    have hnd : (top :: rest).Nodup := hl ▸ hi.nodup
    have hnr : top ∉ rest := (List.nodup_cons.mp hnd).1
    have hgit : gitG st.g top = d0 := by simp [gitG, Treap.gut, hd0]
    simp only [hgit] at h
    let d' : FDatum M := if d0.prod = Sock.void then { d0 with prod := Sock.dunno } else d0
    have hstep : GStepR (gCore st.g) (gCore (Treap.put st.g top d')) := by
      rw [gCore_put, FDatum.pop_core]
      exact GStepR.pop (by simp [gCore, hd0])
    have hwd : WellFormed d'.prod := by
      show WellFormed (if d0.prod = Sock.void then { d0 with prod := Sock.dunno } else d0).prod
      split
      · exact wf_dunno
      · exact (hi.wf_get hd0).2
    let st2 : SkaState M R :=
      { st with stk := rest, order := Treap.del st.order top, ticks := Treap.del st.ticks top, g := Treap.put st.g top d', done := putMi st.done top d' }
    have i2 : SInv st2 := by
      refine ⟨hstep.wf hi.g_wf, hi.done_wf.putMi hwd, fun i o ho => ?_, fun i => ?_, (List.nodup_cons.mp hnd).2⟩
      · simp only [st2, Treap.get_del] at ho
        split at ho
        · cases ho
        · obtain ⟨d, e⟩ := hi.ord_g i o ho
          simp only [st2, Treap.get_put]
          split
          · exact ⟨_, rfl⟩
          · exact ⟨d, e⟩
      · simp only [st2, Treap.get_del]
        split
        · rename_i e; subst e; simp [hnr]
        · rename_i e; rw [hi.ord_stk i, hl]; simp [e]
    have k2 : ∀ j ∈ rest, Treap.get st2.order j = Treap.get st.order j ∧ Treap.get st2.g j = Treap.get st.g j := by
      intro j hj
      have hne : j ≠ top := fun e => hnr (e ▸ hj)
      simp [st2, Treap.get_del, Treap.get_put, hne]
    by_cases e : top = id
    · rw [if_pos e] at h
      cases h
      exact ⟨i2, gStepsR_one hstep, ⟨[], by rw [e]; rfl⟩, k2⟩
    · rw [if_neg e] at h
      obtain ⟨i', s', ⟨pre, hpre⟩, k'⟩ := popGo_ok rest st2 st' rfl i2 h
      refine ⟨i', gStepsR_trans (gStepsR_one hstep) s', ⟨top :: pre, by rw [hpre]; rfl⟩, fun j hj => ?_⟩
      have hjr : j ∈ rest := by rw [hpre]; simp [hj]
      obtain ⟨a1, a2⟩ := k' j hj
      obtain ⟨b1, b2⟩ := k2 j hjr
      exact ⟨a1.trans b1, a2.trans b2⟩

theorem nodup_split_unique {α : Type} {x : α} : ∀ {a a' b b' : List α}, (a ++ x :: b).Nodup →
    a ++ x :: b = a' ++ x :: b' → a = a' ∧ b = b'
  | [], [], _, _, _, h => by simp at h; exact ⟨rfl, h⟩
  | [], y :: a', b, b', hn, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp at hn
  | y :: a, [], b, b', hn, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp at hn
  | y :: a, z :: a', b, b', hn, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨e1, e2⟩ := nodup_split_unique (List.nodup_cons.mp hn).2 h
    exact ⟨by rw [e1], e2⟩

/-- **`+pop` keeps the invariant**: it writes the graph by `GStepR.pop`, and
leaves the stack below `id` alone. -/
theorem pop_ok {id : Ident} {st st' : SkaState M R} (hi : SInv st) (h : pop id st = some st')
    {ab0 rest : List Ident} (hs : st.stk = ab0 ++ id :: rest) :
    SInv st' ∧ GStepsR (gCore st.g) (gCore st'.g) ∧ Keep rest (· ∈ rest) st st' := by
  obtain ⟨i', s', ⟨pre, hpre⟩, k'⟩ := popGo_ok st.stk st st' rfl hi h
  have hu := nodup_split_unique (hs ▸ hi.nodup) (hs.symm.trans hpre)
  refine ⟨i', s', ⟨⟨[], by rw [← hu.2]; rfl⟩, fun j hj => (k' j (hu.2 ▸ hj)).1, fun j hj => (k' j (hu.2 ▸ hj)).2⟩⟩

/-! ## `+cull` -/

theorem liveLoop_mono {st : SkaState M R} {members : M Ident Unit} : ∀ (n : Nat) (q : List Ident)
    (live live' : M Ident Unit), liveLoop st members n q live = some live' →
    ∀ k, Treap.has live k = true → Treap.has live' k = true
  | 0, _, _, _, h => by simp [liveLoop] at h
  | n + 1, [], live, live', h => by
    simp only [liveLoop, Option.some.injEq] at h; subst h; exact fun _ h => h
  | n + 1, i :: q, live, live', h => by
    unfold liveLoop at h
    split at h
    · exact liveLoop_mono n q live live' h
    · intro k hk; exact liveLoop_mono n _ _ live' h k ((Treap.has_ins _ _ _).mpr (Or.inr hk))

theorem liveLoop_head {st : SkaState M R} {members : M Ident Unit} {n : Nat} {i : Ident} {q : List Ident}
    {live live' : M Ident Unit} (h : liveLoop st members n (i :: q) live = some live')
    (hm : Treap.has members i = true) : Treap.has live' i = true := by
  cases n with
  | zero => simp [liveLoop] at h
  | succ n =>
    unfold liveLoop at h
    split at h
    · rename_i hc
      rcases hc with hc | hc
      · exact liveLoop_mono n q live live' h i hc
      · rw [hm] at hc; cases hc
    · exact liveLoop_mono n _ _ live' h i ((Treap.has_ins _ _ _).mpr (Or.inl rfl))

theorem gCore_del (g : Callgraph M) (i : Ident) : gCore (Treap.del g i) = Graph.del (gCore g) i := by
  funext j
  simp only [gCore, Graph.del, Treap.get_del]
  split <;> rfl

/-- One deletion of `+cull`. -/
def cullStep (st : SkaState M R) (i : Ident × Unit) : SkaState M R :=
  { st with order := Treap.del st.order i.1, ticks := Treap.del st.ticks i.1, g := Treap.del st.g i.1 }

theorem cullFold_ok : ∀ (l : List (Ident × Unit)) (st : SkaState M R),
    (l.foldl cullStep st).stk = st.stk ∧ (l.foldl cullStep st).done = st.done ∧
    (∀ k, Treap.get (l.foldl cullStep st).order k = if k ∈ l.map (·.1) then none else Treap.get st.order k) ∧
    (∀ k, Treap.get (l.foldl cullStep st).g k = if k ∈ l.map (·.1) then none else Treap.get st.g k) ∧
    GStepsR (gCore st.g) (gCore (l.foldl cullStep st).g)
  | [], st => ⟨rfl, rfl, fun k => by simp, fun k => by simp, GStepsR.refl _⟩
  | x :: l, st => by
    obtain ⟨a1, a2, a3, a4, a5⟩ := cullFold_ok l (cullStep st x)
    refine ⟨a1, a2, fun k => ?_, fun k => ?_, gStepsR_trans (gStepsR_one ?_) a5⟩
    · rw [List.foldl_cons, a3]
      simp only [cullStep, Treap.get_del, List.map_cons, List.mem_cons]
      by_cases h1 : k ∈ l.map (·.1) <;> by_cases h2 : k = x.1 <;> simp [h1, h2]
    · rw [List.foldl_cons, a4]
      simp only [cullStep, Treap.get_del, List.map_cons, List.mem_cons]
      by_cases h1 : k ∈ l.map (·.1) <;> by_cases h2 : k = x.1 <;> simp [h1, h2]
    · simp only [cullStep]; rw [gCore_del]; exact GStepR.cull

theorem mem_rap_keys {κ : Type} [DecidableEq κ] (m : M κ Unit) (k : κ) :
    k ∈ (Treap.rap m).map (·.1) ↔ Treap.has m k = true := by
  rw [Treap.has_iff]
  constructor
  · intro h
    obtain ⟨⟨k', v⟩, hm, rfl⟩ := List.mem_map.mp h
    exact ⟨v, (Treap.mem_rap m k' v).mp hm⟩
  · rintro ⟨v, hv⟩
    exact List.mem_map.mpr ⟨(k, v), (Treap.mem_rap m k v).mpr hv, rfl⟩

/-- `+cull` with its deletions as `cullStep`. -/
theorem cull_eq (n : Nat) (id : Ident) (st : SkaState M R) : cull n id st =
    (above id st.stk).bind fun ab =>
    (liveLoop st (Treap.silt ab) n [id] Treap.empty).map fun live =>
    if Treap.tap (Treap.dif (Treap.silt ab : M Ident Unit) live) = [] then st else
    (Treap.rap (Treap.dif (Treap.silt ab : M Ident Unit) live)).foldl cullStep
      { st with stats := { st.stats with culled := st.stats.culled + Treap.wyt (Treap.dif (Treap.silt ab : M Ident Unit) live) },
                stk := st.stk.filter (fun i => !Treap.has (Treap.dif (Treap.silt ab : M Ident Unit) live) i),
                moved := Treap.dif st.moved (Treap.dif (Treap.silt ab : M Ident Unit) live) } := rfl

/-- **`+cull` keeps the invariant**: it deletes from the graph (`GStepR.cull`)
members above `id` only, and keeps `id` and the stack below it. -/
theorem cull_ok {n : Nat} {id : Ident} {st st' : SkaState M R} (hi : SInv st) (h : cull n id st = some st')
    {ab0 rest : List Ident} (hs : st.stk = ab0 ++ id :: rest) :
    SInv st' ∧ GStepsR (gCore st.g) (gCore st'.g) ∧ Keep (id :: rest) (· ∈ id :: rest) st st' := by
  rw [cull_eq] at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨ab, hab, live, hlive, hst⟩ := h
  obtain ⟨ab0', rest', rfl, hs', _⟩ := above_eq hab
  obtain ⟨rfl, rfl⟩ := nodup_split_unique (hs ▸ hi.nodup) (hs.symm.trans hs')
  have hnd := hs ▸ hi.nodup
  have hmem : ∀ k, Treap.has (Treap.silt (ab0 ++ [id]) : M Ident Unit) k = true ↔ k ∈ ab0 ++ [id] :=
    fun k => Treap.has_silt _ k
  have hid : Treap.has live id = true := liveLoop_head hlive ((hmem id).mpr (by simp))
  generalize hdd : (Treap.dif (Treap.silt (ab0 ++ [id])) live : M Ident Unit) = dead at hst
  have hdead : ∀ k, Treap.has dead k = true → Treap.has live k ≠ true ∧ k ∈ ab0 ++ [id] := by
    intro k hk
    rw [← hdd] at hk
    rw [← hmem k]
    have e : Treap.has (Treap.dif (Treap.silt (ab0 ++ [id]) : M Ident Unit) live) k =
        (Treap.get (Treap.dif (Treap.silt (ab0 ++ [id]) : M Ident Unit) live) k).isSome := rfl
    rw [e, Treap.get_dif] at hk
    by_cases hl : Treap.has live k = true
    · rw [if_pos hl] at hk; cases hk
    · rw [if_neg hl] at hk; exact ⟨hl, hk⟩
  have hnd2 : ((ab0 ++ [id]) ++ rest).Nodup := by simpa using hnd
  have hkeep : ∀ j ∈ id :: rest, Treap.has dead j ≠ true := by
    intro j hj hd
    obtain ⟨hl, hm⟩ := hdead j hd
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hl hid
    · exact (List.nodup_append.mp hnd2).2.2 j hm j hj rfl
  split at hst
  · subst hst
    exact ⟨hi, GStepsR.refl _, ⟨⟨ab0, hs⟩, fun _ _ => rfl, fun _ _ => rfl⟩⟩
  · subst hst
    obtain ⟨a1, a2, a3, a4, a5⟩ := cullFold_ok (Treap.rap dead)
      { st with stats := { st.stats with culled := st.stats.culled + Treap.wyt dead },
                stk := st.stk.filter (fun i => !Treap.has dead i), moved := Treap.dif st.moved dead }
    have hL : ∀ k, k ∈ (Treap.rap dead).map (·.1) ↔ Treap.has dead k = true := mem_rap_keys dead
    refine ⟨⟨graphWF_stepsR a5 hi.g_wf, by rw [a2]; exact hi.done_wf, fun i o ho => ?_, fun i => ?_, ?_⟩, a5, ⟨⟨ab0.filter (fun i => !Treap.has dead i), ?_⟩, fun j hj => ?_, fun j hj => ?_⟩⟩
    · rw [a3] at ho
      split at ho
      · cases ho
      · rename_i hn
        obtain ⟨d, hd⟩ := hi.ord_g i o ho
        exact ⟨d, by rw [a4, if_neg hn]; exact hd⟩
    · rw [a3, a1]
      simp only [List.mem_filter, Bool.not_eq_true', ← hi.ord_stk i]
      by_cases hd : Treap.has dead i = true
      · simp [(hL i).mpr hd, hd]
      · have : Treap.has dead i = false := by simpa using hd
        simp only [this, Bool.false_eq_true, not_false_eq_true, and_true]
        rw [if_neg (fun h => hd ((hL i).mp h))]
    · rw [a1]; exact hi.nodup.filter _
    · rw [a1, hs, List.filter_append, List.filter_cons]
      have hid' : Treap.has dead id ≠ true := hkeep id (by simp)
      have hr : rest.filter (fun i => !Treap.has dead i) = rest := by
        apply List.filter_eq_self.mpr
        intro j hj
        have := hkeep j (List.mem_cons_of_mem _ hj)
        simpa using this
      simp only [show (!Treap.has dead id) = true by simpa using hid', if_true, hr]
    · rw [a3, if_neg (fun h => hkeep j hj ((hL j).mp h))]
    · rw [a4, if_neg (fun h => hkeep j hj ((hL j).mp h))]

/-! ## `+sweep` -/

theorem sweepLoop_mem {st : SkaState M R} {was : M Ident Unit} {id : Ident} : ∀ (n : Nat)
    (seen : M Ident Unit) (stack : List (Ident × List Ident)) (out res : List Ident),
    sweepLoop st was n seen stack out = some res → (∀ x ∈ out, x = id ∨ Treap.has was x = true) →
    (∀ e ∈ stack, e.1 = id ∨ Treap.has was e.1 = true) → ∀ x ∈ res, x = id ∨ Treap.has was x = true
  | 0, _, _, _, _, h, _, _ => by simp [sweepLoop] at h
  | n + 1, seen, [], out, res, h, ho, _ => by
    simp only [sweepLoop, Option.some.injEq] at h
    subst h; intro x hx; exact ho x (List.mem_reverse.mp hx)
  | n + 1, seen, (i, []) :: rest, out, res, h, ho, hs => by
    simp only [sweepLoop] at h
    refine sweepLoop_mem n seen rest (i :: out) res h ?_ (fun e he => hs e (List.mem_cons_of_mem _ he))
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hs (x, []) List.mem_cons_self
    · exact ho x hx
  | n + 1, seen, (i, k :: ks) :: rest, out, res, h, ho, hs => by
    simp only [sweepLoop] at h
    split at h
    · refine sweepLoop_mem n seen ((i, ks) :: rest) out res h ho ?_
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hs (i, k :: ks) List.mem_cons_self
      · exact hs e (List.mem_cons_of_mem _ he)
    · rename_i hc
      refine sweepLoop_mem n _ _ out res h ho ?_
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · refine Or.inr ?_
        cases hw : Treap.has was k
        · exact absurd (Or.inr hw) hc
        · rfl
      · rcases List.mem_cons.mp he with rfl | he
        · exact hs (i, k :: ks) List.mem_cons_self
        · exact hs e (List.mem_cons_of_mem _ he)

theorem sweep_mem {n : Nat} {id : Ident} {was : M Ident Unit} {st : SkaState M R} {res : List Ident}
    (h : sweep n id was st = some res) : ∀ x ∈ res, x = id ∨ Treap.has was x = true :=
  sweepLoop_mem n _ _ [] res h (by simp) (by simp)

/-! ## The arms, by induction on the fuel -/

/-- The answers of `resolve` at a well-formed subject sock have well-formed
products. -/
def PWF : Sock → Noun → TabEntry → Prop := fun s _ a => WellFormed s → WellFormed a.prod

theorem pwf_tab : ∀ tab, TabIn PWF tab → TabWF tab := fun _ ht s f a hs h => ht s f a h hs

theorem SInv.congr {st st' : SkaState M R} (h : SInv st) (h1 : st'.g = st.g) (h2 : st'.done = st.done)
    (h3 : st'.order = st.order) (h4 : st'.stk = st.stk) : SInv st' := by
  obtain ⟨a, b, c, d, e⟩ := h
  exact ⟨h1 ▸ a, h2 ▸ b, h3 ▸ h1 ▸ c, h3 ▸ h4 ▸ d, h4 ▸ e⟩

theorem Keep.refl' {st st' : SkaState M R} (bg : Ident → Prop) (h1 : st'.g = st.g)
    (h3 : st'.order = st.order) (h4 : st'.stk = st.stk) : Keep st.stk bg st st' :=
  ⟨⟨[], by rw [h4]; rfl⟩, fun j _ => by rw [h3], fun j _ => by rw [h1]⟩

theorem Keep.weaken {bo bo' : List Ident} {bg bg' : Ident → Prop} {st st' : SkaState M R}
    (h : Keep bo bg st st') (hb : ∃ l, bo = l ++ bo') (hg : ∀ j, bg' j → bg j) : Keep bo' bg' st st' := by
  obtain ⟨⟨l1, e1⟩, h2, h3⟩ := h
  obtain ⟨l, rfl⟩ := hb
  exact ⟨⟨l1 ++ l, by rw [e1, List.append_assoc]⟩, fun j hj => h2 j (List.mem_append_right _ hj),
    fun j hj => h3 j (hg j hj)⟩

/-- What `resolve` keeps. -/
def ResP (res : ResGo M R) : Prop :=
  ∀ idT gs r gs', SInv gs.st → WellFormed idT.1 → res idT gs = some (r, gs') →
    SInv gs'.st ∧ GStepsR (gCore gs.st.g) (gCore gs'.st.g) ∧ Keep gs.st.stk (· ∈ gs.st.stk) gs.st gs'.st ∧
      gs'.gen = gs.gen ∧ WellFormed r.2.prod

/-- What `+analyze` keeps. -/
def AnaP (ana : AnaGo M R) : Prop :=
  ∀ id st low st', SInv st → WellFormed id.1 → Treap.get st.g id = none → ana id st = some (low, st') →
    SInv st' ∧ GStepsR (gCore st.g) (gCore st'.g) ∧ Keep st.stk (· ∈ st.stk) st st'

/-- What `+run` keeps. -/
def RunP (run : RunGo M R) : Prop :=
  ∀ id index st r st', SInv st → id ∈ st.stk → run id index st = some (r, st') →
    SInv st' ∧ GStepsR (gCore st.g) (gCore st'.g) ∧ Keep st.stk (fun j => j ∈ st.stk ∧ j ≠ id) st st'

/-- What the member loop keeps. -/
def MemP (mem : MemGo M R) : Prop :=
  ∀ index pass ms st r st' (bo : List Ident) (bg : Ident → Prop), SInv st → (∃ l, st.stk = l ++ bo) →
    (∀ j, bg j → j ∈ bo) → (∀ m ∈ ms, ¬ bg m) → mem index pass ms st = some (r, st') →
    SInv st' ∧ GStepsR (gCore st.g) (gCore st'.g) ∧ Keep bo bg st st'

/-- What the pass loop keeps. -/
def PassP (pass : PassGo M R) : Prop :=
  ∀ id index p st low st' (ab0 rest : List Ident), SInv st → st.stk = ab0 ++ id :: rest →
    pass id index p st = some (low, st') →
    SInv st' ∧ GStepsR (gCore st.g) (gCore st'.g) ∧ Keep rest (· ∈ rest) st st'

/-- The invariant of a run of `fol-loop` that began in the state `st0`. -/
def RInv (st0 : SkaState M R) (gs : GenS M R) : Prop :=
  SInv gs.st ∧ GStepsR (gCore st0.g) (gCore gs.st.g) ∧ Keep st0.stk (· ∈ st0.stk) st0 gs.st

theorem rInv_stable (st0 : SkaState M R) : LocalStable (RInv (M := M) st0) := by
  intro gs gs' h _ _ e1 e2 e3 e4 _ _ _ _
  obtain ⟨a, b, c⟩ := h
  refine ⟨a.congr e1 e2 e3 e4, by rw [e1]; exact b, ?_⟩
  obtain ⟨⟨l, el⟩, c2, c3⟩ := c
  exact ⟨⟨l, by rw [e4]; exact el⟩, fun j hj => by rw [e3]; exact c2 j hj, fun j hj => by rw [e1]; exact c3 j hj⟩

theorem resOK_of_resP {res : ResGo M R} (h : ResP res) (st0 : SkaState M R) : ResOK PWF (RInv st0) res := by
  intro idT gs r gs' hi hw e
  obtain ⟨i1, s1, k1⟩ := hi
  obtain ⟨i2, s2, k2, g2, w2⟩ := h idT gs r gs' i1 hw e
  refine ⟨fun _ => w2, ⟨i2, gStepsR_trans s1 s2, k1.trans (k2.weaken k1.1 (fun j hj => ?_))⟩, g2⟩
  obtain ⟨l, el⟩ := k1.1
  rw [el]; exact List.mem_append_right _ hj

theorem resolveStep_ok (env : Env R) {resolve : ResGo M R} {analyze : AnaGo M R}
    (hres : ResP resolve) (hana : AnaP analyze) : ResP (resolveStep env resolve analyze) := by
  intro idT gs r gs' hi hw e
  unfold resolveStep at e
  cases hg : Treap.get gs.st.g idT with
  | some d =>
    simp only [hg] at e
    have hwd := (hi.wf_get hg).2
    cases ho : Treap.get gs.st.order idT with
    | none =>
      simp only [ho, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨hi, GStepsR.refl _, Keep.refl' _ rfl rfl rfl, rfl, hwd⟩
    | some o =>
      simp only [ho, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨hi, GStepsR.refl _, Keep.refl' _ rfl rfl rfl, rfl, hwd⟩
  | none =>
    rw [hg] at e
    simp only at e
    split at e
    · cases e
    · rename_i m hm
      cases e
      exact ⟨hi, GStepsR.refl _, Keep.refl' _ rfl rfl rfl, rfl, gitMi_wf hi.done_wf hw hm⟩
    · split at e
      · cases e
      · rename_i i hrc
        have hwi : WellFormed i.1 := by
          rcases recursiveCall_cases hrc with ⟨hb, _⟩ | ⟨_, j, hj, hm, _⟩
          · cases hb
          · exact wf_msgSock hw (hi.wf_stk hj) hm
        exact hres i gs r gs' hi hwi e
      · rename_i i hrc
        simp only [Option.map_eq_some_iff] at e
        obtain ⟨o, _, e⟩ := e
        cases e
        refine ⟨hi, GStepsR.refl _, Keep.refl' _ rfl rfl rfl, rfl, ?_⟩
        exact wf_patchDatum (d := (gitG gs.st.g i).core) (hi.wf_gitG i) hw
      · simp only [Option.map_eq_some_iff] at e
        obtain ⟨⟨low, st'⟩, ha, e⟩ := e
        cases e
        obtain ⟨i', s', k'⟩ := hana idT gs.st low st' hi hw hg ha
        exact ⟨i', s', k', rfl, i'.wf_gitG idT⟩

theorem runStep_ok (env : Env R) (memoF : Memo M) {n : Nat}
    (hres : ∀ k, k < n → ResP (resolve env memoF k)) : RunP (runStep (folLoop env memoF n)) := by
  intro id index st r st' hi hid e
  unfold runStep at e
  simp only [Option.map_eq_some_iff] at e
  obtain ⟨⟨out, gs⟩, hf, e⟩ := e
  cases e
  let st0 : SkaState M R := { st with stats := { st.stats with runs := st.stats.runs + 1 } }
  have i0 : SInv st0 := hi.congr rfl rfl rfl rfl
  have r0 : RInv st0 (genInit index st0) := ⟨i0, GStepsR.refl _, Keep.refl' _ rfl rfl rfl⟩
  obtain ⟨⟨i1, s1, k1⟩, hF⟩ := run_folTopR env memoF pwf_tab (rInv_stable st0)
    (fun k hk => resOK_of_resP (hres k hk) st0) r0 (hi.wf_stk hid) hf
  obtain ⟨d0, hd0⟩ := hi.mem_g hid
  have hold : gCore gs.st.g id = some (gitG st0.g id).core := by
    have e1 : Treap.get gs.st.g id = Treap.get st0.g id := k1.2.2 id hid
    simp only [gCore, e1]
    show Option.map FDatum.core (Treap.get st.g id) = some (gitG st.g id).core
    simp [hd0, gitG, Treap.gut]
  have hstep := runEnd_gStepR pwf_tab hF hold
  obtain ⟨i2, k2⟩ := runEnd_ok i1 hstep
  refine ⟨i2, gStepsR_trans s1 (gStepsR_one hstep), ?_⟩
  refine (k1.mono (fun j hj => hj.1)).trans (k2.weaken k1.1 (fun j hj => hj.2))

end Ana
end SkaModel
end Formalization
