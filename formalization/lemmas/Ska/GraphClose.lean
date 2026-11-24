import lemmas.Ska.ConvPass

/-!
# Toward `GraphClosed`: the graph is closed under callees

`GraphClosed` of `AnaEnds.lean` asks that the final graph hold the root and
be closed under callees.  Checked on the real compiler (2026-11-24): over the
26 pokes of `sitesmeet4.hoon`, `he2.hoon`, `voidscc.hoon` and
`prodsame.hoon`, run in sequence with the memo threaded, the graphs that
`+ska-callgraph` returned had 1760 entries and 4052 callee edges, every
callee an entry, and every root an entry.

`Closed st`: every callee of an entry of the graph is an entry.  The pieces
proved here, each for one arm, are the ones that do not need the convergence
invariant `CInv` to be extended:

* `closed_put_new`: putting an entry with no callees (the bunt of `+analyze`,
  a memo hit when the memo's entries have none, `MemoNoCallees`) keeps it.
* `closed_put_callees`: putting an entry whose callees are entries keeps it (the end of a run, `runEnd`).
* `inG_frame`: an identity in the graph stays in it across an arm that keeps
  the stack's entries (`Keep`) and the finalized ones (`Frame.fin`), which is
  how the callees a run collects stay entries until the run ends.
* `cull_closed`, the argument of `+cull`: a culled member is called only by
  culled members.  A live member calls only live members or identities
  outside the component (`liveLoop_closed`), and an entry outside the
  component, by hypothesis, calls nothing in it.

What is left for `GraphClosed`: a field of `CInv` (under `MemoNoCallees` of
the memo) carrying `Closed` and "a finalized entry calls only finalized
identities", the second kept by `+pop` through its `hready` (the popped
members' callees on the stack are popped with them); the run invariant
`RunInv` carrying "the callees of `gen` are entries" (by `inG_frame` across
each `resolve`, whose answer is an entry); and, for `cull_closed`, the fact
that during the `+analyze` of a root no member below it calls a member above
it, which holds when the root is pushed (every callee is then numbered below
`next`) and is kept because the members below do not run during that
`+analyze`.
-/

namespace Formalization
namespace SkaModel

open Nock

namespace Ana

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-- **The graph is closed under callees.** -/
def Closed (st : SkaState M R) : Prop :=
  ∀ i d, Treap.get st.g i = some d → ∀ c, InCallees d.callees c → Treap.get st.g c ≠ none

/-- Putting an entry with no callees keeps `Closed`. -/
theorem closed_put_new {st st' : SkaState M R} {i : Ident} {d : FDatum M} (hc : Closed st)
    (hg : st'.g = Treap.put st.g i d) (hd : ∀ c, ¬ InCallees d.callees c) : Closed st' := by
  intro j e hj c hce
  rw [hg, Treap.get_put] at hj ⊢
  split at hj
  · cases hj; exact absurd hce (hd c)
  · split
    · simp
    · exact hc j e hj c hce

/-- Putting an entry whose callees are entries keeps `Closed`. -/
theorem closed_put_callees {st st' : SkaState M R} {i : Ident} {d : FDatum M} (hc : Closed st)
    (hg : st'.g = Treap.put st.g i d)
    (hd : ∀ c, InCallees d.callees c → Treap.get st.g c ≠ none) : Closed st' := by
  have keep : ∀ c, Treap.get st.g c ≠ none → Treap.get st'.g c ≠ none := by
    intro c h
    rw [hg, Treap.get_put]
    split
    · simp
    · exact h
  intro j e hj c hce
  rw [hg, Treap.get_put] at hj
  split at hj
  · cases hj; exact keep c (hd c hce)
  · exact keep c (hc j e hj c hce)

/-- **An entry stays an entry** across an arm that keeps the entries of the
stack and the finalized entries. -/
theorem inG_frame {st st' : SkaState M R} {bt : Ident → Prop} (hi : SInv st)
    (hk : Keep st.stk (· ∈ st.stk) st st') (hf : Frame bt st st') {c : Ident}
    (h : Treap.get st.g c ≠ none) : Treap.get st'.g c ≠ none := by
  cases ho : Treap.get st.order c with
  | some o =>
    have hcs : c ∈ st.stk := (hi.ord_stk c).mp ⟨o, ho⟩
    rw [hk.2.2 c hcs]; exact h
  | none =>
    obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp h
    rw [(hf.fin c d hd ho).1]; simp

/-- **`+cull` keeps the graph closed**: a culled member is called only by
culled members, given that no entry outside the component of `id` calls a
member of it. -/
theorem cull_closed {n : Nat} {id : Ident} {st st' : SkaState M R} {ab0 rest : List Ident} (hi : SInv st)
    (hs : st.stk = ab0 ++ id :: rest) (h : cull n id st = some st') (hc : Closed st)
    (hout : ∀ x d, Treap.get st.g x = some d → x ∉ ab0 ++ [id] → ∀ c, InCallees d.callees c → c ∉ ab0 ++ [id]) :
    Closed st' := by
  obtain ⟨live, hlive, -, hg, -⟩ := cull_eff hi hs h
  have hcl := liveLoop_closed n [id] Treap.empty live hlive (fun x hx => by simp [Treap.has, Treap.get_empty] at hx)
  intro x d hx c hce
  rw [hg] at hx ⊢
  by_cases hdx : x ∈ ab0 ++ [id] ∧ Treap.has live x = false
  · rw [if_pos hdx] at hx; cases hx
  rw [if_neg hdx] at hx
  have hcg := hc x d hx c hce
  by_cases hdc : c ∈ ab0 ++ [id] ∧ Treap.has live c = false
  · exfalso
    by_cases hxm : x ∈ ab0 ++ [id]
    · have hxl : Treap.has live x = true := by
        cases e : Treap.has live x
        · exact absurd ⟨hxm, e⟩ hdx
        · rfl
      have hk : c ∈ kids st x := kids_of_inCallees (by simpa only [calleesOf, gitG, Treap.gut, hx, Option.getD_some] using hce)
      have := hcl x hxl c hk ((Treap.has_silt _ _).mpr hdc.1)
      rw [hdc.2] at this; cases this
    · exact hout x d hx hxm c hce hdc.1
  · rw [if_neg hdc]; exact hcg

end Ana

end SkaModel
end Formalization
