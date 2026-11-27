import lemmas.Ska.PassStabM
import lemmas.Ska.ConvPass

/-!
# What is left of the freezing argument (track F, Gaps 16)

Until dab8478 the pass loop dropped, after every pass, the members that the
root no longer reached (`+cull`), and a later pass could push such a member
again from the bunt.  The freezing argument (R, `EvFrozen`: a member that
stays has an eventually constant callee set; C, `PassMoves`; and
`freeze_no_chain`, `finPushes_of_freeze`) answered that.  Since dab8478 the
loop culls only once it is stable, so a member keeps its entry for the whole
loop, and R, C and the argument on chains are no longer needed: they are
deleted, with `passOn_cull` (a pass that goes on has no `+cull` now).

Kept, because they still hold and the halting argument of the new loop uses
them: `MembR`, `memberLoop_clean`, `passOn_dirty` (a pass that goes on with a
change had a member dirty at its start), `cull_keeps_kid` and `cull_reach`
(what the final `+cull` keeps: every member left is reached from the root),
`FinIdents` ((i): the members of a chain of passes lie in a finite list) and
`KruskalBT` (section 5, what (i) rests on).
-/

namespace Formalization
namespace SkaModel
namespace Ana

open Nock

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-- A member of the component: on the stack, above the fixed bottom `rest`. -/
def MembR (rest : List Ident) (st : SkaState M R) (x : Ident) : Prop := x ∈ st.stk ∧ x ∉ rest

/-! ## 1. A pass that goes on had a dirty member -/

/-- **A member loop over clean members runs nothing.** -/
theorem memberLoop_clean (env : Env R) (memoF : Memo M) :
    ∀ n index pass (ms : List Ident) (st : SkaState M R) r st',
      (∀ m ∈ ms, dirty m st = false) → memberLoop env memoF n index pass ms st = some (r, st') →
      r = (index, false) ∧ st' = st
  | 0 => by
    intro index pass ms st r st' _ h
    rw [memberLoop_zero] at h; cases h
  | n + 1 => by
    intro index pass ms st r st' hc h
    rw [memberLoop_succ] at h
    cases ms with
    | nil =>
      simp only [memberStep, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨h.1.symm, h.2.symm⟩
    | cons m ms =>
      simp only [memberStep, hc m List.mem_cons_self, if_true] at h
      exact memberLoop_clean env memoF n index pass ms st r st' (fun x hx => hc x (List.mem_cons_of_mem _ hx)) h

/-- **A pass that goes on had a member dirty at its start**: if every member
were clean, the member loop would run nothing, report no change and push
nothing, and the pass would stop. -/
theorem passOn_dirty {env : Env R} {memoF : Memo M} {n : Nat} {id : Ident} {index pass : Nat}
    {st st' : SkaState M R} (h : PassOn env memoF n id index pass st st') :
    ∃ ab, above id st.stk = some ab ∧ ∃ m ∈ ab, dirty m st = true := by
  obtain ⟨ab, members, r, h1, h2, h3, _, h6⟩ := h
  refine ⟨ab, h1, Classical.byContradiction fun hn => ?_⟩
  have hc : ∀ m ∈ members,
      dirty m ({ st with stats := { st.stats with passes := st.stats.passes + 1 } } : SkaState M R) = false := by
    intro m hm
    have hab : m ∈ ab := by
      obtain ⟨ab0, rest, rfl, _, _⟩ := above_eq h1
      rcases sweep_mem h2 m hm with rfl | hm'
      · exact List.mem_append_right _ List.mem_cons_self
      · exact (Treap.has_silt _ m).mp hm'
    cases e : dirty m st with
    | false => exact e
    | true => exact absurd ⟨m, hab, e⟩ hn
  obtain ⟨rfl, rfl⟩ := memberLoop_clean env memoF n index pass members _ r st' hc h3
  exact h6 ⟨rfl, rfl⟩

/-! ## 2. What `+cull` keeps -/

theorem kids_of_get {st st' : SkaState M R} {m : Ident} (h : Treap.get st'.g m = Treap.get st.g m) :
    kids st' m = kids st m := by
  unfold kids gitG Treap.gut; rw [h]

/-- **A callee of a member that `+cull` keeps is kept**, if it was a member. -/
theorem cull_keeps_kid {n : Nat} {id : Ident} {st st' : SkaState M R} {ab0 rest : List Ident} (hi : SInv st)
    (hs : st.stk = ab0 ++ id :: rest) (h : cull n id st = some st') {m c : Ident}
    (hm : MembR rest st' m) (hc : c ∈ kids st' m) (hc2 : MembR rest st c) : MembR rest st' c := by
  obtain ⟨live, hlive, -, hg, -, hstk, -⟩ := cull_eff hi hs h
  have hcl := liveLoop_closed n [id] Treap.empty live hlive
    (fun x hx => by simp [Treap.has, Treap.get_empty] at hx)
  have hin : ∀ x, x ∈ st.stk → x ∉ rest → x ∈ ab0 ++ [id] := by
    intro x hx hxr
    rw [hs] at hx
    rcases List.mem_append.mp hx with h' | h'
    · exact List.mem_append_left _ h'
    · rcases List.mem_cons.mp h' with rfl | h''
      · exact List.mem_append_right _ List.mem_cons_self
      · exact absurd h'' hxr
  have hm1 : m ∈ st.stk := by
    have := hm.1; rw [hstk] at this; exact (List.mem_filter.mp this).1
  have hm2 : ¬ (m ∈ ab0 ++ [id] ∧ Treap.has live m = false) := by
    have := hm.1; rw [hstk] at this
    have := (List.mem_filter.mp this).2
    intro ⟨a, b⟩; simp [a, b] at this
  have hml : Treap.has live m = true := by
    cases e : Treap.has live m with
    | true => rfl
    | false => exact absurd ⟨hin m hm1 hm.2, e⟩ hm2
  have hk : kids st' m = kids st m := kids_of_get (by rw [hg]; exact if_neg hm2)
  have hcm : Treap.has (Treap.silt (ab0 ++ [id]) : M Ident Unit) c = true :=
    (Treap.has_silt _ c).mpr (hin c hc2.1 hc2.2)
  have hcl' := hcl m hml c (hk ▸ hc) hcm
  refine ⟨?_, hc2.2⟩
  rw [hstk]
  refine List.mem_filter.mpr ⟨hc2.1, ?_⟩
  simp [hcl']

/-- **Every member after `+cull` is reached from the root**, over callees
through members. -/
theorem cull_reach {n : Nat} {id : Ident} {st st' : SkaState M R} {ab0 rest : List Ident} (hi : SInv st)
    (hs : st.stk = ab0 ++ id :: rest) (h : cull n id st = some st') {x : Ident}
    (hx : MembR rest st' x) : Reach st' (MembR rest st') id x := by
  obtain ⟨live, hlive, -, hg, -, hstk, -⟩ := cull_eff hi hs h
  have hnd : (ab0 ++ id :: rest).Nodup := hs ▸ hi.nodup
  have hidr : id ∉ rest := ((List.nodup_append.mp hnd).2.1 |> List.nodup_cons.mp).1
  have hcl := liveLoop_closed n [id] Treap.empty live hlive
    (fun x hx => by simp [Treap.has, Treap.get_empty] at hx)
  have hso := liveLoop_sound (a := id) n [id] Treap.empty live hlive
    (fun x hx => by simp [Treap.has, Treap.get_empty] at hx) (fun x hx => by
      rw [List.mem_singleton.mp hx]; exact Or.inl Reach.refl)
  have hin : ∀ x, x ∈ st.stk → x ∉ rest → x ∈ ab0 ++ [id] := by
    intro x hx hxr
    rw [hs] at hx
    rcases List.mem_append.mp hx with h' | h'
    · exact List.mem_append_left _ h'
    · rcases List.mem_cons.mp h' with rfl | h''
      · exact List.mem_append_right _ List.mem_cons_self
      · exact absurd h'' hxr
  let W : Ident → Prop := fun y => Treap.has (Treap.silt (ab0 ++ [id]) : M Ident Unit) y = true
  have hmemW : ∀ y, W y → y ∈ ab0 ++ [id] := fun y hy => (Treap.has_silt _ y).mp hy
  -- every live identity is kept, with its callees, and is a member after
  have hkeep : ∀ y, Treap.has live y = true → MembR rest st' y ∧ kids st' y = kids st y := by
    intro y hy
    have hnd' : ¬ (y ∈ ab0 ++ [id] ∧ Treap.has live y = false) := fun ⟨_, b⟩ => by simp [hy] at b
    refine ⟨⟨?_, ?_⟩, kids_of_get (by rw [hg]; exact if_neg hnd')⟩
    · have hyW : W y := by
        refine Classical.byContradiction fun hw => ?_
        -- a live identity is a member: liveLoop only marks members
        have := hso y hy
        cases this with
        | refl => exact hw ((Treap.has_silt _ _).mpr (List.mem_append_right _ List.mem_cons_self))
        | step _ _ hc => exact hw hc
      rw [hstk]
      refine List.mem_filter.mpr ⟨?_, by simp [hy]⟩
      rw [hs]
      rcases List.mem_append.mp (hmemW y hyW) with h' | h'
      · exact List.mem_append_left _ h'
      · rw [List.mem_singleton.mp h']; exact List.mem_append_right _ List.mem_cons_self
    · intro hr
      have hyW : y ∈ ab0 ++ [id] := by
        have := hso y hy
        cases this with
        | refl => exact List.mem_append_right _ List.mem_cons_self
        | step _ _ hc => exact hmemW _ hc
      rcases List.mem_append.mp hyW with h' | h'
      · exact (List.nodup_append.mp hnd).2.2 y h' y (List.mem_cons_of_mem _ hr) rfl
      · rw [List.mem_singleton.mp h'] at hr; exact hidr hr
  -- the reach of `liveLoop_sound` goes through live identities
  have hlv : ∀ y, Reach st W id y → Treap.has live y = true := by
    intro y hy
    induction hy with
    | refl => exact liveLoop_head hlive ((Treap.has_silt _ id).mpr (List.mem_append_right _ List.mem_cons_self))
    | step _ hk hw ih => exact hcl _ ih _ hk hw
  have hxl : Treap.has live x = true := by
    have hx1 : x ∈ st.stk := by have := hx.1; rw [hstk] at this; exact (List.mem_filter.mp this).1
    have hx2 := hx.1; rw [hstk] at hx2
    have := (List.mem_filter.mp hx2).2
    cases e : Treap.has live x with
    | true => rfl
    | false => simp [hin x hx1 hx.2, e] at this
  have hr := hso x hxl
  have : ∀ y, Reach st W id y → Reach st' (MembR rest st') id y := by
    intro y hy
    induction hy with
    | refl => exact Reach.refl
    | @step b c hb hk hw ih =>
      have hbl := hlv b hb
      have hcl2 := hlv c (Reach.step hb hk hw)
      exact Reach.step ih ((hkeep b hbl).2 ▸ hk) (hkeep c hcl2).1
  exact this x hr

/-! ## 4. On the model -/

/-- (i) along a chain: its members are among a finite list. -/
def FinIdents (rest : List Ident) (f : Nat → SkaState M R) : Prop :=
  ∃ I : List Ident, ∀ k x, MembR rest (f k) x → x ∈ I

/-! ## 5. What (i) rests on

`FinIdents` is what the argument uses: along one chain, the members of all its
passes lie in one finite list.  The argument of `AnaEnds.lean` for (i) is
Kruskal's theorem for the embedding `+he-sock` (a sock embeds in another when
it is a part of it, or the two are cells whose halves embed, a leaf only in an
equal leaf) over finitely many leaves.  It can be stated in Lean core, as
below (`KruskalBT`), with no Mathlib; it is not proved here.  What it gives is
less than `FinIdents`: past `he-threshold` frames of one formula the subjects
along one stack form a bad sequence, so no stack is infinite (one descent).
`FinIdents` speaks of the union of the stacks of infinitely many passes, and
needs besides that the identities a run can push be finitely many at each
frame (finite branching, then König's lemma), which `HeBound.lean` does not
give either: it bounds the `%he` turns of one `resolve`. -/

/-- Binary trees with leaves in `L` (the shape of a sock: a leaf `|`, or `&`
over a noun). -/
inductive BT (L : Type) where
  | leaf : L → BT L
  | node : BT L → BT L → BT L

/-- The homeomorphic embedding of `+he-sock`: a part of the bigger tree, or
cells whose halves embed, or equal leaves. -/
inductive BTEmb {L : Type} : BT L → BT L → Prop where
  | leaf (a : L) : BTEmb (.leaf a) (.leaf a)
  | left {s t₁ t₂ : BT L} : BTEmb s t₁ → BTEmb s (.node t₁ t₂)
  | right {s t₁ t₂ : BT L} : BTEmb s t₂ → BTEmb s (.node t₁ t₂)
  | node {s₁ s₂ t₁ t₂ : BT L} : BTEmb s₁ t₁ → BTEmb s₂ t₂ → BTEmb (.node s₁ s₂) (.node t₁ t₂)

/-- **Kruskal's theorem for binary trees over finitely many leaves** (stated,
not proved): every infinite sequence has an earlier tree that embeds in a
later one. -/
def KruskalBT : Prop :=
  ∀ (L : Type) (ls : List L), (∀ a : L, a ∈ ls) → ∀ t : Nat → BT L, ∃ i j, i < j ∧ BTEmb (t i) (t j)

end Ana
end SkaModel
end Formalization
