import lemmas.Ska.OptTopo

/-!
# `+remove-hops`

`hopSeg`: the inner `|-` that turns the hop's arguments into ops in front of
the merged block's body: `[%mov a p]` for an argument `a`, `[%imm 0 p]` for
an argument `~`, each consed in front of the ops so far, so the ops come in
the reverse order of the arguments (harmless when the parameters are
distinct, since `+eval-pass` checks that no argument is a parameter: no op
then reads what another writes).  Different counts are `!!`, here `none`.

`hopChain`: the `|-` at one block of `topo`: while the block being built ends
in a `%hop` to `o1` whose list in `rev` is exactly `~[o]` (`o` the current
end of the chain), put `o1` in `saw` and append its segment; `?<  =(~ pre-o1)`
is `none`.  `done` appends the segments, oldest first.  The fuel bounds the
length of the chain (the Hoon has none).

`removeHops`: the `+roll` over `topo` (its order matters: a block merged into
an earlier one is skipped), with the flag `!=(~ saw)`.

The preservation statement (`HopsKeeps`, not proved yet): with `TopoOK bl topo`
and `rev = revCfg bl topo`, the parameters of every merged block distinct and
no hop argument one of them (what `+eval-pass` checks in the code before),
the result keeps the code (`Keeps`).  The poison case: an argument `~` writes
`0` where the code before poisons, which `ReadsOK` makes invisible (see
`Opt.lean`); the simulation relation on registers is then "the code after
holds a value wherever the code before does, the same value, and is defined
wherever the code before is".
-/

namespace Formalization
namespace SkaModel
namespace Opt

open Nock

variable {Map : Type → Type} [HoonMap Map]

/-- The segment of a merged block. -/
def hopSeg : List (Option Nat) → List Nat → List Pole → Option (List Pole)
  | [], [], ops => some ops
  | [], _ :: _, _ => none
  | _ :: _, [], _ => none
  | a :: as, p :: ps, ops =>
      hopSeg as ps ((match a with | none => Pole.imm (A 0) p | some r => Pole.mov r p) :: ops)

/-- `done`: the block with the segments appended, oldest first. -/
def hopDone (bnew : Blob) (segs : List (List Pole)) : Blob :=
  { bnew with body := bnew.body ++ segs.reverse.flatten }

/-- The chain of merges at one block. -/
def hopChain (bl : Map Blob) (rev : Map (List Nat)) :
    Nat → Nat → Blob → List (List Pole) → List Nat → Option (Blob × List Nat)
  | 0, _, _, _, _ => none
  | n + 1, o, bnew, segs, saw =>
    match bnew.fin with
    | Termin.hop t =>
      let pre := getJa rev t.there
      if pre = [] then none
      else if pre ≠ [o] then some (hopDone bnew segs, saw)
      else (HoonMap.get bl t.there).bind fun b1 =>
        (hopSeg t.args b1.par b1.body).bind fun seg =>
          hopChain bl rev n t.there { bnew with fin := b1.fin } (seg :: segs) (t.there :: saw)
    | _ => some (hopDone bnew segs, saw)

/-- `+remove-hops`. -/
def removeHops (fuel : Nat) (bl : Map Blob) (rev : Map (List Nat)) (topo : List Nat) :
    Option (Bool × Map Blob) :=
  (topo.foldlM (fun (acc : Map Blob × List Nat) o =>
      if o ∈ acc.2 then some acc
      else (HoonMap.get bl o).bind fun b =>
        (hopChain bl rev fuel o b [] acc.2).map fun r => (HoonMap.put acc.1 o r.1, r.2))
    (HoonMap.empty, [])).map fun r => (decide (r.2 ≠ []), r.1)

/-- **The preservation statement of `+remove-hops`** (open). -/
def HopsKeeps [MapKeys Map] (fuel : Nat) : Prop :=
  ∀ (c : Straight Map) topo ch bl', TopoOK c.blocks topo →
    (∀ o b, HoonMap.get c.blocks o = some b → b.par.Nodup) →
    removeHops fuel c.blocks (revCfg c.blocks topo) topo = some (ch, bl') →
    Keeps c (withBlocks c bl')

end Opt
end SkaModel
end Formalization
