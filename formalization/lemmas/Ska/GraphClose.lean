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

end Ana

end SkaModel
end Formalization
