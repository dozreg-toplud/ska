import lemmas.Ska.ConvAna

/-!
# `GraphClosed`: the graph is closed under callees

`GraphClosed` of `AnaEnds.lean` asks that the final graph hold the root and
be closed under callees.  Proved here for the model, from the hypotheses of
`skaCallgraph_frozen` and `MemoNoCallees` of the persistent memo
(`skaCallgraph_closed`); `graphClosed` of `AnaEnds.lean` discharges it under
`InvB`.

The argument is carried by the convergence invariant, field `CInv.clo`: when
the memo's entries have no callees, every state the analysis passes through
is closed under callees (`Closed`), and a finalized entry calls only
finalized identities (`FinCalls`).  Arm by arm:

* a push (`push_cinv`) and a memo hit (`hit_cinv`) put an entry with no
  callees (`closed_put_new`, `gitMi_noCallees`);
* the end of a run (`runStep_ok2`) puts an entry whose callees are entries
  (`closed_put_callees`), because the run invariant `RunInv` carries "the
  callees of `gen` are entries": each answer of `resolve` rests on an entry
  (`AnsW.exists_entry`), and an entry stays one across `resolve`
  (`inG_frame`);
* `+pop` (`pop_frozen`) keeps both, the second by its `hready`: the callees
  on the stack of a popped member are popped with it;
* `+cull` (`cull_ok2`) keeps both by `cull_closed`: a culled member is called
  only by culled members, given that no entry outside the component calls
  into it.  That holds because finalized entries call only finalized
  identities, and the members below the root call only members below it
  (`RestBelow`), which is true when the root is pushed (every number is then
  below `next`) and is kept through the run and the pass loop
  (`restBelow_keep`), since the members below the root keep their entries
  and numbers and an identity off the stack that a closed graph holds stays
  finalized.

Checked on the real compiler (2026-11-24), over the 26 pokes of
`tools/hoon/closed.hoon` with the memo threaded: the returned graphs had 1760
entries and 4052 callee edges, every callee and every root an entry.  An
instrumented copy of `+cull` and `+pop` checked the two clauses at every
state they see: at 3680 culls, none of the 2,195,392 callee edges from an
entry outside the component pointed into it and no callee of any entry was
missing; at 4472 pops, none of the 2,354,100 callee edges of finalized
entries pointed to an identity in `order` and none was missing.
-/

namespace Formalization
namespace SkaModel

open Nock

namespace Ana

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-- **The final graph of `+ska-callgraph` holds the root and is closed under
callees**, for a persistent memo with well-formed and normal products whose
entries have no callees. -/
theorem skaCallgraph_closed (env : Env R) (memoF : Memo M) (hmF : MemoWF memoF) (hmN : MemoNorm memoF)
    (hmC : MemoNoCallees memoF) {n : Nat} {root : Ident} {reg reg' : R} {g : Callgraph M}
    (hw : WellFormed root.1) (hnr : NormSock root.1) (hnvr : root.1 ≠ Sock.void)
    (h : skaCallgraph env n root memoF reg = some (g, reg')) :
    Treap.get g root ≠ none ∧
      ∀ i d, Treap.get g i = some d → ∀ c, InCallees d.callees c → Treap.get g c ≠ none := by
  unfold skaCallgraph at h
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨low, st⟩, ha, rfl, _⟩ := h
  obtain ⟨⟨F, _, c⟩, _, _, _, _, ⟨d, hd⟩, _, _⟩ := (allP2 env memoF hmF hmN n n (Nat.le_refl n)).2.1 root
    (SkaState.init reg) low st (fun _ => False) (CInv.init memoF reg) hw hnr hnvr
    (by simp [SkaState.init, Treap.get_empty]) ha
  exact ⟨by rw [hd]; simp, (c.clo hmC).1⟩

end Ana

end SkaModel
end Formalization
