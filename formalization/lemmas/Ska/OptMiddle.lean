import lemmas.Ska.OptHops

/-!
# `+remove-empty-middle`

`readersOf bl p`: the labels of the blocks whose `+get-regs` (of an op or of
the terminator) mention `p`.  The Hoon builds a jug by a `+rep:by`; it is used
only through `=(~ (~(del in readers-of-p) there.j))`, which depends on the set
alone, so a filter over `MapKeys.keys` stands for it (a simplification of
the construction, not of the result).  The Hoon computes the jug only when
some block is empty with parameters and a `%hop`, and consults it only for
such a block, so computing it always gives the same result.

`rewriteJump` and `rewriteHop`: the two arms, with fuel (the Hoon's loops end
only when the chains of empty blocks are not cycles).  `mkSub` is the map
`sub` (a later parameter of the same name wins, as with `+put:by`), and
`passArg` is `pass`: `~` stays `~`, a register is replaced by what `sub`
gives (a unit), or kept.

`removeEmptyMiddle`: the `+rep:by` over the blocks, each new value depending
only on the old map and `readers`, so its order does not matter.

The preservation statement (`MiddleKeeps`, proved in `OptMiddleSim.lean`)
needs the check of `+eval-pass` before and after the pass (`PassOK` of the
input and of the result) and, on the entry, `ArgsOK` in place of `ReadsOK`
(see `MiddleKeeps`).
-/

namespace Formalization
namespace SkaModel
namespace Opt

open Nock

variable {Map : Type → Type} [HoonMap Map]

/-- The registers a block mentions. -/
def blobRegs (b : Blob) : List Nat := finRegs b.fin ++ b.body.flatMap poleRegs

/-- The readers of `p`, as a list of labels. -/
def readersOf [MapKeys Map] (bl : Map Blob) (p : Nat) : List Nat :=
  (MapKeys.keys bl).filter fun o =>
    match HoonMap.get bl o with
    | some b => decide (p ∈ blobRegs b)
    | none => false

/-- `rewrite-jump`. -/
def rewriteJump (bl : Map Blob) : Nat → Jmp → Option Jmp
  | 0, _ => none
  | n + 1, j =>
    if j.args ≠ [] then some j else
    (HoonMap.get bl j.there).bind fun nex =>
      if nex.par ≠ [] then none else
      if nex.body ≠ [] then some j else
      match nex.fin with
      | Termin.hop t => if t.args ≠ [] then some j else rewriteJump bl n t
      | _ => some j

/-- The map `sub` of `rewrite-hop`. -/
def mkSub : List Nat → List (Option Nat) → (Nat → Option (Option Nat)) → Option (Nat → Option (Option Nat))
  | [], [], s => some s
  | [], _ :: _, _ => none
  | _ :: _, [], _ => none
  | p :: ps, a :: as, s => mkSub ps as (fun q => if q = p then some a else s q)

/-- `pass` of `rewrite-hop`. -/
def passArg (s : Nat → Option (Option Nat)) : Option Nat → Option Nat
  | none => none
  | some a => (s a).getD (some a)

/-- `rewrite-hop`, with the readers as a function. -/
def rewriteHop (bl : Map Blob) (rd : Nat → List Nat) : Nat → Jmp → Option Jmp
  | 0, _ => none
  | n + 1, j =>
    (HoonMap.get bl j.there).bind fun nex =>
      if nex.body ≠ [] then some j else
      match nex.fin with
      | Termin.hop t =>
        if !(nex.par.all fun p => (rd p).all (· = j.there)) then some j else
        (mkSub nex.par j.args (fun _ => none)).bind fun s =>
          rewriteHop bl rd n ⟨t.args.map (passArg s), t.there⟩
      | _ => some j

/-- The new terminator of one block. -/
def middleFin (bl : Map Blob) (rd : Nat → List Nat) (fuel : Nat) : Termin → Option Termin
  | Termin.clq s z o => (rewriteJump bl fuel z).bind fun z' => (rewriteJump bl fuel o).map fun o' => Termin.clq s z' o'
  | Termin.eqq l r z o => (rewriteJump bl fuel z).bind fun z' => (rewriteJump bl fuel o).map fun o' => Termin.eqq l r z' o'
  | Termin.brn s z o => (rewriteJump bl fuel z).bind fun z' => (rewriteJump bl fuel o).map fun o' => Termin.brn s z' o'
  | Termin.brz s z o => (rewriteJump bl fuel z).bind fun z' => (rewriteJump bl fuel o).map fun o' => Termin.brz s z' o'
  | Termin.hop t => (rewriteHop bl rd fuel t).map Termin.hop
  | f => some f

/-- `+remove-empty-middle`. -/
def removeEmptyMiddle [MapKeys Map] (fuel : Nat) (bl : Map Blob) : Option (Bool × Map Blob) :=
  (MapKeys.keys bl).foldl (fun acc o =>
    acc.bind fun (ch, nw) => (HoonMap.get bl o).bind fun b =>
      (middleFin bl (readersOf bl) fuel b.fin).map fun f' =>
        (ch || decide (f' ≠ b.fin), HoonMap.put nw o { b with fin := f' }))
    (some (false, HoonMap.empty))

/-- **The preservation statement of `+remove-empty-middle`** (proved:
`middleKeeps`, `OptMiddleSim.lean`).  It is not `Keeps`: the code before
moves the arguments of a bypassed hop into parameters nothing reads, and
crashes there when an argument register is not in the file, where the code
after goes on; so the entry must also satisfy `ArgsOK`, which the pass keeps.
It needs the check of `+eval-pass` before (`PassOK` of the input, the check at
each bypassed block) and after (`PassOK` of the result, the check of the
substituted arguments at the new target). -/
def MiddleKeeps [MapKeys Map] (fuel : Nat) : Prop :=
  ∀ (c : Straight Map) ch bl', removeEmptyMiddle fuel c.blocks = some (ch, bl') →
    PassOK c.blocks → PassOK bl' →
    (HoonMap.get bl' 0).map Blob.par = (HoonMap.get c.blocks 0).map Blob.par ∧
    ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ) (vals : List Noun) (t : Trace),
      ArgsOK lib O c gul st vals t →
        execEntry lib O st (withBlocks c bl') vals t gul = execEntry lib O st c vals t gul ∧
        (ReadsOK lib O c gul st vals t → ReadsOK lib O (withBlocks c bl') gul st vals t) ∧
        ArgsOK lib O (withBlocks c bl') gul st vals t

end Opt
end SkaModel
end Formalization
