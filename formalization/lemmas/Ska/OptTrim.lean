import lemmas.Ska.OptTopo

/-!
# `+trim-trace-hints`

The pass (`nock-compilation.hoon`, about line 8902) drops trace hints whose
frame nothing can observe.  Line by line:

1. `key` and `trace` (`TKey`, `traceKey`): a `%hdp` or `%hde` with the tag
   `%spot` or `%mean` has the key `[%clue n p]`, a `%hmp` or `%hme` the key
   `[%defer a v f]`, a `%hcp` or `%hce` the key `[%konst n f]`; the `p`, `m`,
   `c` ops open their key, the `e` ops close it.  Other ops have no key (a
   `%hdp` of another tag among them).
2. `unsafe` (`trimWalk`, `trimBody`): a walk over `topo` with a map `out`
   from each walked block to the keys open at its end.  At a block, the keys
   open at its start are the union of `out` over its predecessors in `rev`
   (`+roll` over `(~(get ja rev) o)`, `~(get ju out) p`, empty for a
   predecessor not walked yet).  Along the body an opening op puts its key,
   a closing op deletes it, and any other op that is not
   `pole-not-crashing` (`%imm %mov %con %hed %tal %hsp %hse %hdp %hde %hmp
   %hme %hcp %hce %equ`) makes every open key unsafe.  At the end, a
   terminator that is not `%clq`, `%eqq`, `%brz`, `%hop` makes every open key
   unsafe.  Then `out` of the block is the keys open at its end.
3. `opened` (`trimOpened`): the keys that some op of some block opens
   (`+rep:by`, a union, so its order does not matter).
4. The result (`trimTraceHints`): `+run:by` over the blocks, each body
   without the hint ops whose key is not unsafe and is opened.  Every block
   is kept with its parameters and end.

The model returns `none` where the Hoon crashes (`got` of a label of `topo`
that is not a block).  Sets are lists here; only membership is used.

## What preservation needs

`TrimKeeps` states it in the form `Keeps`, on a `topo` with `TopoOK` and its
`+rev-cfg`, which is how `+optimize-once` calls it (after `+alias`, with
`topo` filtered by the blocks that remain).  It is not proved.  A proof must
use, beyond `ReadsOK` (a dropped `%hdp` or `%hmp` reads its registers for
real) and `LocalOK` (`%con %hed %tal %mov` count as not crashing), that
pushes and pops are bracketed on every path: a dropped `%hde`, `%hme` or
`%hce` pops the frame its dropped prologue pushed.  `pole-not-crashing`
counts the pops as not crashing, while `popTrace` crashes on an empty trace,
and the walk unions the open keys of the predecessors, so an epilogue reached
on a path that did not pass its prologue (its key opened on another path)
is dropped too.  Whether raw `+comp` output can reach an epilogue that way is
open; `+comp` keys a `%spot`/`%mean` frame by the register of its clue, which
is defined once, before the prologue.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock

variable {Map : Type → Type} [HoonMap Map]

/-- `key` of `+trim-trace-hints`. -/
inductive TKey
  | clue (hint : Nat) (reg : Nat)
  | defer (a : Bell) (v : List Nat) (f : Noun)
  | konst (n : Noun) (f : Noun)
  deriving DecidableEq

/-- `trace`: the key of a trace hint op, and whether it opens the hint. -/
def traceKey : Pole → Option (Bool × TKey)
  | Pole.hdp n p _ => if n = Tag.spot ∨ n = Tag.mean then some (true, TKey.clue n p) else none
  | Pole.hde n p _ => if n = Tag.spot ∨ n = Tag.mean then some (false, TKey.clue n p) else none
  | Pole.hmp a v f => some (true, TKey.defer a v f)
  | Pole.hme a v f => some (false, TKey.defer a v f)
  | Pole.hcp n f => some (true, TKey.konst n f)
  | Pole.hce n f => some (false, TKey.konst n f)
  | _ => none

/-- `pole-not-crashing`. -/
def notCrashing : Pole → Bool
  | Pole.imm _ _ | Pole.mov _ _ | Pole.con _ _ _ | Pole.hed _ _ | Pole.tal _ _ | Pole.hsp _ _
  | Pole.hse _ _ | Pole.hdp _ _ _ | Pole.hde _ _ _ | Pole.hmp _ _ _ | Pole.hme _ _ _ | Pole.hcp _ _
  | Pole.hce _ _ | Pole.equ _ _ => true
  | _ => false

/-- The terminators after which open keys stay safe: `?(%clq %eqq %brz %hop)`. -/
def finQuiet : Termin → Bool
  | Termin.clq _ _ _ | Termin.eqq _ _ _ _ | Termin.brz _ _ _ | Termin.hop _ => true
  | _ => false

/-- The inner `|-` over the body: the keys open and the unsafe keys. -/
def trimBody : List Pole → List TKey → List TKey → List TKey × List TKey
  | [], opn, uns => (opn, uns)
  | op :: body, opn, uns =>
    match traceKey op with
    | some (true, k) => trimBody body (k :: opn) uns
    | some (false, k) => trimBody body (opn.filter (· ≠ k)) uns
    | none => if notCrashing op then trimBody body opn uns else trimBody body opn (opn ++ uns)

/-- The keys open at the start of `o`: the union of `out` over its
predecessors. -/
def trimOpen (rev : Map (List Nat)) (out : Map (List TKey)) (o : Nat) : List TKey :=
  (getJa rev o).foldl (fun acc p => acc ++ (HoonMap.get out p).getD []) []

/-- The walk over `topo` that makes `unsafe`. -/
def trimWalk (bl : Map Blob) (rev : Map (List Nat)) : List Nat → Map (List TKey) → List TKey → Option (List TKey)
  | [], _, uns => some uns
  | o :: topo, out, uns => (HoonMap.get bl o).bind fun b =>
      let r := trimBody b.body (trimOpen rev out o) uns
      trimWalk bl rev topo (HoonMap.put out o r.1) (if finQuiet b.fin then r.2 else r.1 ++ r.2)

/-- `opened`: the keys some op of some block opens. -/
def trimOpened [MapKeys Map] (bl : Map Blob) : List TKey :=
  (MapKeys.keys bl).foldl (fun acc o =>
    match HoonMap.get bl o with
    | some b => b.body.foldl (fun acc op =>
        match traceKey op with
        | some (true, k) => k :: acc
        | _ => acc) acc
    | none => acc) []

/-- The test of the `+skip`: a hint op whose key is not unsafe and is
opened. -/
def trimDrop (uns opened : List TKey) (op : Pole) : Bool :=
  match traceKey op with
  | some (_, k) => decide (k ∉ uns) && decide (k ∈ opened)
  | none => false

/-- `+run:by`: every block with the body skipped. -/
def trimRun [MapKeys Map] (bl : Map Blob) (uns opened : List TKey) : Map Blob :=
  (MapKeys.keys bl).foldl (fun acc o =>
    match HoonMap.get bl o with
    | some b => HoonMap.put acc o { b with body := b.body.filter fun op => !trimDrop uns opened op }
    | none => acc) bl

/-- `+trim-trace-hints`. -/
def trimTraceHints [MapKeys Map] (bl : Map Blob) (topo : List Nat) (rev : Map (List Nat)) : Option (Map Blob) :=
  (trimWalk bl rev topo HoonMap.empty []).map fun uns => trimRun bl uns (trimOpened bl)

/-- **The preservation statement of `+trim-trace-hints`** (open): `Keeps`,
on a `topo` with `TopoOK` and its `+rev-cfg`. -/
def TrimKeeps [MapKeys Map] : Prop :=
  ∀ (c : Straight Map) topo bl', TopoOK c.blocks topo →
    trimTraceHints c.blocks topo (revCfg c.blocks topo) = some bl' → Keeps c (withBlocks c bl')

end Opt
end SkaModel
end Formalization
