import lemmas.Ska.KnowSound
import lemmas.Ska.Analysis

/-!
# `+bake-graph`: the worklist and its fixed point

A model of `+bake-graph` (`nock-compilation.hoon`), arm by arm: `+pick`
(`pick`), one evaluation of the worklist (`bakeStep`, with the `roll` of the
sites `newStep` and the `roll` of the touched callees `touchStep`), the
worklist (`bakeLoop`, with fuel: `none` is a crash or too little fuel), the
final pass (`finalStep`, with the `res` of the final pass `bakeRes`), and
`bakeGraph`.  Maps and sets are the treaps of `Analysis.lean`; `~(rep in ..)`
and `~(rep by ..)` visit in `rap` order, `~(tap in ..)` and `~(val by ..)` in
`tap` order, and `~(key by ..)`, `~(uni in ..)` and `~(gas in ..)` are folds
of `put` (a treap is its contents, `Treap.ext`).

`bakeLoop_sound`: when the worklist ends, every site `[b k]` of every
function `c` of the bakes, as `+know` lists it under `c`'s bake, that `+pick`
does not send to an existing variant, has a bake for `b` that every subject
fitting both `less.b` and `k` fits (`Fits`).  So the `res` of the final pass
sends every subject of a site to a variant whose bell it fits
(`bakeRes_fits`).
-/

namespace Formalization
namespace SkaModel

open Nock Ana

namespace Bake

variable {M : Type → Type → Type} [Treap M]

/-- The parameters of `+bake-graph`, and the two flags of `bake-mode` it
reads: `fold` (`!@(off:bake-mode & |)`, for `+know`) and `frozen`. -/
structure BEnv (M : Type → Type → Type) where
  root : Bell
  dat : Bell → Option Datum
  jetted : Bell → Bool
  vars : M Bell (M Bell Unit)
  fold : Bool
  frozen : Bool

/-- The state of the worklist. -/
structure BSt (M : Type → Type → Type) where
  bak : M Bell Sock
  fix : M Bell Unit
  out : M Bell (M Bell Unit)
  inn : M Bell (M Bell (List Sock))
  evals : Nat
  grew : Nat

/-- The gate of the `~(rep in ..)` of `+pick`: the variant that knows the
most among those fit for `k`.  `none` is a crash of `+huge:so`. -/
def pickGate (k : Sock) (acc : Option (Option Bell)) (v : Bell) : Option (Option Bell) :=
  acc.bind fun best => (So.huge v.less k).bind fun hv =>
    if hv then
      match best with
      | none => some (some v)
      | some u => (So.huge u.less v.less).map fun h => if h then some v else some u
    else some best

/-- `+pick`: an existing variant of the code bell `c` fit for a site that
knows `k`, if `k` provides `less.c`. -/
def pick (vars : M Bell (M Bell Unit)) (c : Bell) (k : Sock) : Option (Option Bell) :=
  (So.huge c.less k).bind fun h =>
    if h then ((Treap.rap (Treap.gut vars c Treap.empty)).map Prod.fst).foldl (pickGate k) (some none)
    else some none

/-- `idc`: the `res` of the worklist's `+know`. -/
def idc : Bell → Sock → Option Bell := fun c _ => some c

/-- The gate of the `roll` over the sites: a site that `+pick` sends to no
variant adds what it knows to its callee's list. -/
def newStep (vars : M Bell (M Bell Unit)) (acc : Option (M Bell (List Sock))) (s : Site) :
    Option (M Bell (List Sock)) :=
  acc.bind fun new => (pick vars s.1 s.2).map fun p =>
    match p with
    | some _ => new
    | none => Treap.put new s.1 (s.2 :: Treap.gut new s.1 [])

/-- `~(key by m)`. -/
def keySet {ν : Type} (m : M Bell ν) : M Bell Unit :=
  (Treap.tap m).foldl (fun acc e => Treap.put acc e.1 ()) Treap.empty

/-- `~(uni in a b)`. -/
def uniIn (a b : M Bell Unit) : M Bell Unit :=
  (Treap.tap b).foldl (fun acc e => Treap.put acc e.1 ()) a

/-- `~(gas in s l)`. -/
def gasIn (s : M Bell Unit) (l : List Bell) : M Bell Unit :=
  l.foldl (fun acc c => Treap.put acc c ()) s

/-- What `cur` now tells its callee `c`: `inn` of `c` with `cur`'s list
replaced, or dropped when `cur` no longer calls `c`. -/
def innUpd (new : M Bell (List Sock)) (cur c : Bell) (m : M Bell (List Sock)) : M Bell (List Sock) :=
  match Treap.get new c with
  | none => Treap.del m cur
  | some ks => Treap.put m cur ks

/-- The bake of a callee against its old one, with the count of bakes that
would have grown: `+norm-sock` of the `+purr:so` when the new one is not a
loss. -/
def rebakeG (bake : Sock) (old : Option Sock) (grew : Nat) : Option (Sock × Nat) :=
  match old with
  | none => some (bake, grew)
  | some o => (So.huge bake o).bind fun h =>
      if h then some (bake, grew) else (normSockH (So.purr bake o)).map fun b => (b, grew + 1)

/-- The gate of the `roll` over the touched callees. -/
def touchStep (E : BEnv M) (cur : Bell) (new : M Bell (List Sock))
    (acc : Option (List Bell × BSt M)) (c : Bell) : Option (List Bell × BSt M) :=
  acc.bind fun ⟨changed, st⟩ =>
  let m := innUpd new cur c (Treap.gut st.inn c Treap.empty)
  let st := { st with inn := Treap.put st.inn c m }
  if c = E.root then some (changed, st) else
  let st := if E.jetted c then { st with fix := Treap.put st.fix c () } else st
  let ks := ((Treap.tap m).map Prod.snd).flatten
  (bakeOf (E.frozen || Treap.has st.fix c) c.less ks).bind fun bake =>
  let old := Treap.get st.bak c
  (rebakeG bake old st.grew).bind fun ⟨bake, grew⟩ =>
  let st := { st with grew := grew }
  if some bake = old then some (changed, st) else
  some (c :: changed, { st with bak := Treap.put st.bak c bake })

/-- The sites of `c` under its bake, as the worklist's `+know` lists them. -/
def sitesOf (E : BEnv M) (st : BSt M) (c : Bell) : Option (List Site) :=
  (E.dat c).bind fun d => (Treap.get st.bak c).bind fun s =>
    (know E.fold d.nomm s E.dat idc).map Prod.snd

/-- One evaluation of the worklist: `cur` under its bake, what it tells its
callees, their bakes again, and the callees whose bake changed queued. -/
def bakeStep (E : BEnv M) (cur : Bell) (rest : List Bell) (qs : M Bell Unit) (st : BSt M) :
    Option (List Bell × M Bell Unit × BSt M) :=
  let qs := Treap.del qs cur
  (sitesOf E st cur).bind fun sites =>
  let st := { st with evals := st.evals + 1 }
  (sites.foldl (newStep E.vars) (some Treap.empty)).bind fun new =>
  let newBells := keySet new
  let prev := Treap.gut st.out cur Treap.empty
  let st := { st with out := Treap.put st.out cur newBells }
  let touched := uniIn prev newBells
  ((Treap.tap touched).map Prod.fst |>.foldl (touchStep E cur new) (some ([], st))).map fun ⟨changed, st⟩ =>
  let fresh := changed.filter fun c => !Treap.has qs c
  (rest ++ fresh, gasIn qs fresh, st)

/-- The worklist, with fuel. -/
def bakeLoop (E : BEnv M) : Nat → List Bell → M Bell Unit → BSt M → Option (BSt M)
  | 0, _, _, _ => none
  | _ + 1, [], _, st => some st
  | n + 1, cur :: rest, qs, st => (bakeStep E cur rest qs st).bind fun ⟨q, qs, st⟩ => bakeLoop E n q qs st

/-- The state the worklist starts from: the root's bake is its code
requirement, and it is fixed. -/
def bakeInit (E : BEnv M) : BSt M :=
  ⟨Treap.put Treap.empty E.root E.root.less, Treap.put Treap.empty E.root (), Treap.empty, Treap.empty, 0, 0⟩

/-- The `res` of the final pass: an existing variant `+pick` finds, or the
bake of the callee. -/
def bakeRes (E : BEnv M) (st : BSt M) : Bell → Sock → Option Bell := fun c k =>
  (pick E.vars c k).bind fun p =>
    match p with
    | some v => some v
    | none => (Treap.get st.bak c).map fun s => ⟨s, c.fol⟩

/-- An entry of the variants to compile: the folded nomm, the variants it
calls and the `.seek` of its function. -/
structure VarEntry (M : Type → Type → Type) where
  nomm : Nomm
  calls : M Bell Unit
  seek : Cape

/-- The gate of the final `~(rep by bak.st)`. -/
def finalStep (E : BEnv M) (st : BSt M) (acc : Option (M Bell (VarEntry M) × M Bell (M Bell Unit)))
    (e : Bell × Sock) : Option (M Bell (VarEntry M) × M Bell (M Bell Unit)) :=
  acc.bind fun ⟨out, vars⟩ =>
  (E.dat e.1).bind fun d =>
  (know E.fold d.nomm e.2 E.dat (bakeRes E st)).bind fun ⟨nomm, sites⟩ =>
  let v : Bell := ⟨e.2, e.1.fol⟩
  (sites.mapM fun s => bakeRes E st s.1 s.2).map fun vs =>
  (Treap.put out v ⟨nomm, Treap.silt vs, d.seek⟩,
    Treap.put vars e.1 (Treap.put (Treap.gut vars e.1 Treap.empty) v ()))

/-- `+bake-graph`: the variants to compile and the code bell -> variants
index with them. -/
def bakeGraph (E : BEnv M) (n : Nat) : Option (M Bell (VarEntry M) × M Bell (M Bell Unit)) :=
  (bakeLoop E n [E.root] (Treap.put Treap.empty E.root ()) (bakeInit E)).bind fun st =>
    (Treap.rap st.bak).foldl (finalStep E st) (some (Treap.empty, E.vars))

end Bake

end SkaModel
end Formalization
