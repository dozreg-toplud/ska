import lemmas.Ska.OptTopo

/-!
# `+remove-dead-code`

`safeAssign`: `+get-reg-safe-assignment`, the register an op of `%imm`,
`%mov`, `%con`, `%hed`, `%tal` writes.  `deadBody`: the inner `|-` over the
reversed body, with the set `saw` (a list here; only membership is used).
`removeDeadCode`: the walk over `rev-topo`, one `saw` for the whole walk,
whose order matters (`+optimize-once` passes `(flop topo)`).

The preservation statement (`DeadKeeps`, not proved yet) needs `TopoOK`
(every successor of a block is walked before it, so `saw` holds every
register read later on any path) and `LocalOK`: no dropped op crashes on an
execution.  The ops `+get-reg-safe-assignment` names can crash in the
interpreter: `%hed`/`%tal` of an atom, `%con` of a missing or poisoned
register, `%mov` of a missing one.  For example the block
`[[%hed 0v0 0v1] ~] [%don 0v0]` returns its argument after the pass even
when that argument is an atom, where the interpreter crashes before.  So
the pass is sound only on code whose ops of these kinds never crash, which
`+comp` must guarantee (it emits `%hed` and `%tal` where the subject is known
to be a cell, or after a `%cel`).
-/

namespace Formalization
namespace SkaModel
namespace Opt

open Nock

variable {Map : Type → Type} [HoonMap Map]

/-- The inner loop over the reversed body. -/
def deadBody : List Pole → List Pole → List Nat → List Pole × List Nat
  | [], nb, saw => (nb, saw)
  | op :: rest, nb, saw =>
    match safeAssign op with
    | some d => if d ∈ saw then deadBody rest (op :: nb) (poleRegs op ++ saw) else deadBody rest nb saw
    | none => deadBody rest (op :: nb) (poleRegs op ++ saw)

/-- `+remove-dead-code`. -/
def removeDeadCode (bl : Map Blob) (revTopo : List Nat) : Option (Map Blob) :=
  (revTopo.foldlM (fun (acc : Map Blob × List Nat) o =>
      (HoonMap.get bl o).map fun b =>
        let r := deadBody b.body.reverse [] (finRegs b.fin ++ acc.2)
        (HoonMap.put acc.1 o { b with body := r.1 }, r.2))
    (HoonMap.empty, [])).map Prod.fst

/-- **The preservation statement of `+remove-dead-code`** (proved:
`deadKeeps` in `OptDeadSim.lean`): `Keeps`, on a `topo` with `TopoOK`. -/
def DeadKeeps : Prop :=
  ∀ (c : Straight Map) topo bl', TopoOK c.blocks topo →
    removeDeadCode c.blocks topo.reverse = some bl' → Keeps c (withBlocks c bl')

end Opt
end SkaModel
end Formalization
