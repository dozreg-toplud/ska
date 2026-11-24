import lemmas.Ska.OptDriverTopo

/-!
# `+switch-chains`: what it does, and its preservation statement

`+switch-chains` (`nock-compilation.hoon`, about line 9135) runs once, after
the loop of `+optimize`, and is the only pass that makes `%lti` (the
interpreter model has it: `execBlob` of `Interp.lean` takes `z` when the
register holds an atom below `n`, else `o`, as `+eval-blob` does).  It is
modelled below (`switchChains`), line by line, and the model is checked on
the real compiler by `tools/hoon/switchcheck.hoon` (formulas made to have
chains) and `switchcheck2.hoon` (the 143 cases of `optcheck.hoon`), which
write the model again in Hoon and compare it with the pass.  The ends it
makes are `%lti`, `%eqq` and `%clq`, with jumps that pass nothing.  Line by
line:

1. `topo` by `+bb-topo`, `rev` by `+rev-cfg`, and `uses`: how many times each
   register is mentioned (parameters, `+get-regs` of every op and end).
2. `test-of p`: the block `p` ends in a `%clq s` whose yes side `y` has `p` as
   its only predecessor, no parameters, a body of exactly a `%hed s d` and an
   `%imm c r` (in either order), and an `%eqq` of `d` and `r` whose no side
   is the no side of the `%clq`; `c` an atom below `2^31`, `d` and `r`
   mentioned twice each.  `chain-of p`: the tests chained through the no
   sides, each an empty block reached from the two blocks of the test before
   only, on the same `s`.
3. `plain-of p`: the block ends in an `%eqq` of a register `d` and a register
   `r` its body sets by an `%imm c r` (`c` an atom below `2^31`, `r` mentioned
   twice, `l ≠ r`).  `plains-of p`: the chain through the no sides, each a
   block with no parameters, a body of one `%imm`, reached from the test
   before only, on the same `d`.
4. `cases`: the first case of each constant, sorted.  `tree`: a binary
   search over the cases, a leaf an `%imm c r` with an `%eqq d r` to its hit
   or to the miss, an inner node an `%lti` on the constant of the first case
   of its upper half.
5. The walk over `topo` (blocks of a chain done are skipped): a chain of
   four tests or more replaces its blocks by the tree under the yes side of
   the first test, which does the `%hed` first, and the first block's end
   becomes the `%clq` to it and to the final miss; else a chain of four plain
   tests or more puts the root of the tree at the end of the first block
   (without its `%imm` of the first constant) and the other nodes in the
   blocks of the chain and new labels from `nex`, the first label no block
   has.

## What preservation needs

The search takes the hit of the first case of the constant the register
holds, and the miss otherwise, as the chain does: the chain tests the cases in
order, the first equal one wins, and `cases` keeps the first of each constant.
The `%hed` moves to the root, where the chain did it after the `%clq`, so on
the yes side only.  The `%imm` ops of the chain are dropped from blocks the
search no longer passes (`uses = 2` makes sure nothing else reads them).  The
dropped blocks are reached only from the chain (`rev`), so no other jump
changes.  `ReadsOK` is needed where the chain read `d` or `r` and the tree
reads it in another place; `%lti` reads its register and compares an atom.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Opt

variable {Map : Type → Type} [HoonMap Map]

open Nock

/-! ## The model, line by line

A crash of the Hoon (`got:by` of a missing block, a failed `?>`) is `none`;
the recursions (`chain-of`, `plains-of`, `sort`, `tree`, the walk) take fuel,
`none` when it runs out. -/

/-- The registers a block mentions, as `uses` counts them: the parameters,
`+get-regs` of the end, `+get-regs` of every op. -/
def blobMentions (b : Blob) : List Nat := b.par ++ finRegs b.fin ++ b.body.flatMap poleRegs

/-- `uses`: how many times the register `r` is mentioned (a `+rep:by`, whose
order a count does not see). -/
def usesOf [MapKeys Map] (bl : Map Blob) (r : Nat) : Nat :=
  ((MapKeys.keys bl).flatMap fun o => ((HoonMap.get bl o).map blobMentions).getD []).count r

/-- `test`: the head `d` of `s` against the constant `c` in `r`, to `hit` or
`miss`, in the block `y`. -/
structure STest where
  s : Nat
  c : Nat
  hit : Nat
  miss : Nat
  y : Nat
  d : Nat
  r : Nat
  deriving DecidableEq, Repr

/-- A direct atom: an atom below `2^31`. -/
def smallAtom : Noun → Option Nat
  | Noun.atom a => if a < 2 ^ 31 then some a else none
  | _ => none

/-- The `h` of `test-of`: the first of two ops that is a `%hed`. -/
def hedOf2 (i0 i1 : Pole) : Option (Nat × Nat) :=
  match i0, i1 with
  | Pole.hed s d, _ => some (s, d)
  | _, Pole.hed s d => some (s, d)
  | _, _ => none

/-- The `m` of `test-of`: the first of two ops that is an `%imm`. -/
def immOf2 (i0 i1 : Pole) : Option (Noun × Nat) :=
  match i0, i1 with
  | Pole.imm n d, _ => some (n, d)
  | _, Pole.imm n d => some (n, d)
  | _, _ => none

/-- `test-of p`: the outer `none` a crash, the inner one no test. -/
def testOf [MapKeys Map] (bl : Map Blob) (rev : Map (List Nat)) (p : Nat) : Option (Option STest) :=
  (HoonMap.get bl p).bind fun b =>
  match b.fin with
  | Termin.clq s ⟨[], y⟩ ⟨[], n⟩ =>
    if getJa rev y ≠ [p] then some none else
    (HoonMap.get bl y).bind fun yb =>
    if yb.par ≠ [] then some none else
    match yb.fin with
    | Termin.eqq l r ⟨[], hit⟩ ⟨[], n'⟩ =>
      if n ≠ n' then some none else
      match yb.body with
      | [i0, i1] =>
        match hedOf2 i0 i1, immOf2 i0 i1 with
        | some (hs, hd), some (mn, md) =>
          if hs ≠ s then some none else
          match smallAtom mn with
          | some c =>
            if ¬ ((l, r) = (hd, md) ∨ (l, r) = (md, hd)) then some none else
            if ¬ (usesOf bl hd = 2 ∧ usesOf bl md = 2) then some none else
            some (some ⟨s, c, hit, n, y, hd, md⟩)
          | none => some none
        | _, _ => some none
      | _ => some none
    | _ => some none
  | _ => some none

/-- `chain-of p`, with fuel. -/
def chainOf [MapKeys Map] (bl : Map Blob) (rev : Map (List Nat)) : Nat → Nat → Option (List STest)
  | 0, _ => none
  | n + 1, p =>
    (testOf bl rev p).bind fun t =>
    match t with
    | none => some []
    | some t =>
      ((HoonMap.get bl t.miss).bind fun nb =>
        if ¬ (nb.par = [] ∧ nb.body = []) then some [] else
        let rm := getJa rev t.miss
        if ¬ (rm = [p, t.y] ∨ rm = [t.y, p]) then some [] else
        (testOf bl rev t.miss).bind fun t2 =>
        match t2 with
        | none => some []
        | some t2 => if t2.s ≠ t.s then some [] else chainOf bl rev n t.miss).map (t :: ·)

/-- `plain`: the register `d` against the constant `c`, put in `r` by the
block, to `hit` or `miss`. -/
structure SPlain where
  d : Nat
  c : Nat
  hit : Nat
  miss : Nat
  r : Nat
  deriving DecidableEq, Repr

/-- The `m` of `plain-of`: the first `%imm` of the body into `l` or `r`. -/
def immInto (l r : Nat) : List Pole → Option (Noun × Nat)
  | [] => none
  | Pole.imm n d :: t => if d = l ∨ d = r then some (n, d) else immInto l r t
  | _ :: t => immInto l r t

/-- `plain-of p`. -/
def plainOf [MapKeys Map] (bl : Map Blob) (p : Nat) : Option (Option SPlain) :=
  (HoonMap.get bl p).bind fun b =>
  match b.fin with
  | Termin.eqq l r ⟨[], hit⟩ ⟨[], miss⟩ =>
    match immInto l r b.body with
    | none => some none
    | some (mn, md) =>
      match smallAtom mn with
      | none => some none
      | some c =>
        if l = r then some none else
        if usesOf bl md ≠ 2 then some none else
        some (some ⟨if md = l then r else l, c, hit, miss, md⟩)
  | _ => some none

/-- `plains-of p`, with fuel. -/
def plainsOf [MapKeys Map] (bl : Map Blob) (rev : Map (List Nat)) : Nat → Nat → Option (List (Nat × SPlain))
  | 0, _ => none
  | n + 1, p =>
    (plainOf bl p).bind fun t =>
    match t with
    | none => some []
    | some t =>
      ((HoonMap.get bl t.miss).bind fun nb =>
        if nb.par ≠ [] then some [] else
        match nb.body with
        | [Pole.imm _ _] =>
          if getJa rev t.miss ≠ [p] then some [] else
          (plainOf bl t.miss).bind fun t2 =>
          match t2 with
          | none => some []
          | some t2 => if t2.d ≠ t.d then some [] else plainsOf bl rev n t.miss
        | _ => some []).map ((p, t) :: ·)

/-- `case`: a constant, its hit, its register. -/
structure SCase where
  c : Nat
  hit : Nat
  r : Nat
  deriving DecidableEq, Repr

/-- `+sort` of hoon.hoon (a quicksort: the head, then the rest split by
`+skid` into those before it and the others), with fuel. -/
def hsort {α : Type} (lt : α → α → Bool) : Nat → List α → Option (List α)
  | _, [] => some []
  | 0, _ :: _ => none
  | n + 1, a :: t =>
    let s := t.partition fun c => lt c a
    (hsort lt n s.1).bind fun p => (hsort lt n s.2).map fun q => p ++ a :: q

/-- The loop of `cases`: the first case of each constant, in the reverse
order. -/
def casesAcc : List SCase → List Nat → List SCase → List SCase
  | [], _, acc => acc
  | x :: t, saw, acc => if x.c ∈ saw then casesAcc t saw acc else casesAcc t (x.c :: saw) (x :: acc)

/-- `cases`: the first case of each constant, by the constants. -/
def casesOf (ces : List SCase) : Option (List SCase) :=
  let acc := casesAcc ces [] []
  hsort (fun a b => decide (a.c < b.c)) acc.length acc

/-- `tree`: the body and end of the root of a binary search over `cas` of
the register `d`, `mis` where no case leads; the other nodes are put in `out`
under labels taken from `ids`.  With fuel. -/
def stree (d mis : Nat) : Nat → List SCase → List Nat → Map Blob →
    Option (List Pole × Termin × List Nat × Map Blob)
  | 0, _, _, _ => none
  | _, [], _, _ => none
  | _, [x], ids, out => some ([Pole.imm (A x.c) x.r], Termin.eqq d x.r ⟨[], x.hit⟩ ⟨[], mis⟩, ids, out)
  | n + 1, all@(_ :: _ :: _), ids, out =>
    let haf := all.length / 2
    let hi := all.drop haf
    match hi, ids with
    | h :: _, lid :: rid :: rest =>
      (stree d mis n (all.take haf) rest out).bind fun (lb, lf, lids, lout) =>
      let lout := HoonMap.put lout lid ⟨[], lb, lf⟩
      (stree d mis n hi lids lout).map fun (rb, rf, rids, rout) =>
      ([], Termin.lti h.c d ⟨[], lid⟩ ⟨[], rid⟩, rids, HoonMap.put rout rid ⟨[], rb, rf⟩)
    | _, _ => none

/-- `nex`: the first label no block has (the `+roll` over the keys). -/
def nexOf [MapKeys Map] (bl : Map Blob) : Nat :=
  (MapKeys.keys bl).foldl (fun m o => if o ≥ m then o + 1 else m) 0

/-- The labels of the plain case: the first `ned` of `old`, then new ones
from `nex` put in front, with the next `nex`. -/
def freshIds : Nat → List Nat → Nat → Nat → List Nat × Nat
  | 0, ids, _, nex => (ids, nex)
  | f + 1, ids, ned, nex => if ids.length ≥ ned then (ids, nex) else freshIds f (nex :: ids) ned (nex + 1)

/-- The tagged chain `cs` (four tests or more) at the block `o`. -/
def switchTag (bl out : Map Blob) (fuel : Nat) (o : Nat) (cs : List STest) (done : List Nat) :
    Option (Map Blob × List Nat) :=
  match cs with
  | [] => none
  | t0 :: tl =>
    let s := t0.s
    let d := t0.d
    let top := t0.y
    let mis := ((t0 :: tl).getLast (List.cons_ne_nil _ _)).miss
    let ids := tl.map STest.y ++ (t0 :: tl).dropLast.map STest.miss
    let done := ids ++ done
    let out := ids.foldl HoonMap.del out
    (casesOf ((t0 :: tl).map fun t => ⟨t.c, t.hit, t.r⟩)).bind fun cas =>
    (stree d mis fuel cas ids out).bind fun (nb, nf, _, nout) =>
    let out := HoonMap.put nout top ⟨[], Pole.hed s d :: nb, nf⟩
    (HoonMap.get bl o).map fun b =>
    (HoonMap.put out o { b with fin := Termin.clq s ⟨[], top⟩ ⟨[], mis⟩ }, done)

/-- The plain chain `ps` (four tests or more) at the block `o`. -/
def switchPlain (bl out : Map Blob) (fuel : Nat) (o : Nat) (ps : List (Nat × SPlain)) (done : List Nat)
    (nex : Nat) : Option (Map Blob × List Nat × Nat) :=
  match ps with
  | [] => none
  | p0 :: pl =>
    let d := p0.2.d
    let mis := ((p0 :: pl).getLast (List.cons_ne_nil _ _)).2.miss
    let old := pl.map Prod.fst
    let done := old ++ done
    let out := old.foldl HoonMap.del out
    (casesOf ((p0 :: pl).map fun t => ⟨t.2.c, t.2.hit, t.2.r⟩)).bind fun cas =>
    let ned := 2 * cas.length - 2
    let (ids, nex) := freshIds (ned + 1) (old.take ned) ned nex
    (stree d mis fuel cas ids out).bind fun (nb, nf, _, nout) =>
    (HoonMap.get bl o).map fun b =>
    let bod := b.body.filter fun op => match op with
      | Pole.imm _ dd => !(dd = p0.2.r)
      | _ => true
    (HoonMap.put nout o ⟨b.par, bod ++ nb, nf⟩, done, nex)

/-- The walk of `+switch-chains` over `topo`. -/
def switchWalk [MapKeys Map] (bl : Map Blob) (rev : Map (List Nat)) (fuel : Nat) :
    List Nat → Map Blob → List Nat → Nat → Option (Map Blob)
  | [], out, _, _ => some out
  | o :: rest, out, done, nex =>
    if o ∈ done then switchWalk bl rev fuel rest out done nex else
    (chainOf bl rev fuel o).bind fun cs =>
    if cs.length ≥ 4 then
      (switchTag bl out fuel o cs done).bind fun (out, done) => switchWalk bl rev fuel rest out done nex
    else
    (plainsOf bl rev fuel o).bind fun ps =>
    if ps.length < 4 then switchWalk bl rev fuel rest out done nex else
    (switchPlain bl out fuel o ps done nex).bind fun (out, done, nex) =>
      switchWalk bl rev fuel rest out done nex

/-- **`+switch-chains`**, with fuel for `+bb-topo` and the recursions. -/
def switchChains [MapKeys Map] (fuel : Nat) (bl : Map Blob) : Option (Map Blob) :=
  (bbTopo fuel bl).bind fun topo =>
  switchWalk bl (revCfg bl topo) fuel topo bl [] (nexOf bl)

/-- **The preservation statement of `+switch-chains`** (open), for the pass
as a function on blocks: `Keeps` on blocks with `DInv`.  It is the field
`switch` of `DriverRest`. -/
def SwitchKeeps (switch : Map Blob → Option (Map Blob)) : Prop :=
  ∀ (c : Straight Map) bl', DInv c.blocks → switch c.blocks = some bl' → Keeps c (withBlocks c bl')

/-- `SwitchKeeps` gives the field `switch` of `DriverRest`. -/
theorem switch_field {switch : Map Blob → Option (Map Blob)} (h : SwitchKeeps switch) :
    ∀ (bl : Map Blob) bl', DInv bl → switch bl = some bl' → KeepsB bl bl' :=
  fun bl bl' hb hs c hc => by subst hc; exact h c bl' hb hs

/-- The statement for the model. -/
def SwitchKeepsM [MapKeys Map] (fuel : Nat) : Prop := SwitchKeeps (Map := Map) (switchChains fuel)

end Opt
end SkaModel
end Formalization
