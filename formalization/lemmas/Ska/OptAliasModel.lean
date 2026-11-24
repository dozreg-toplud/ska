import lemmas.Ska.OptAlias

/-!
# The model of `+alias`, line by line

`+alias` (`nock-compilation.hoon`, line 8310) as a function of the blocks,
`rev` and `topo`.  A Hoon crash (`got` or `jab` of a missing key, a `?>`
that fails) is `none`.  The walk is structural on `topo` and the parameter
loop on the parameters, so no fuel is needed.

## Representations, and where the model departs from the Hoon

1. The register maps (`info-local`, the `info` of a block) are functions
   `Nat → Option InfoReg` (`AInfo`), the immediates (`imms-local`, a
   `(jug * @uvre)`) functions `Noun → List Nat` (`AImms`, an absent key the
   empty list), `old` a function `Nat → Nat` that starts as the identity (so
   `rn` is `old` itself), and the reversed CFG `rev.gen` (a `jug`) a function
   `Nat → List Nat` without duplicates (`+silt` of each list, then `del ju`
   an `erase`).  The per-block stores `info.gen`, `imms.gen` are functions
   `Nat → Option _`, `new.gen` is a `Map Blob`.
2. **The join of facts is pointwise** (`joinInfoA`): at a key of both maps it
   is `joinRegE`, which keeps an equal value as it is and is `joinReg`
   otherwise.  The Hoon's `join-info` follows the treaps and returns an equal
   subtree as it is, so at a key with equal values it gives either the value
   or `joinReg x x`, which differ only in `isLoob` where `hasImm` is a
   loobean.  `isLoob` is read only beside `hasImm` (`%lob`, `%clq`, `%brn`
   read `hasImm` first or together; `join-reg` takes `isLoob ∨ loobImm`; the
   refinement after a `%brz` reads it only for a remaining `%brz`, whose test
   register has no `hasImm`), so the blocks and the flag the pass returns do
   not depend on that choice; `aliascheck2.hoon` checks this on every call.
   `join-imms` is pointwise too (`joinImmsA`, an empty set is absent).
3. **The choice of a member of a set** (`n.res` for `%imm`, `n.intersect` for
   `%con`) is a parameter `pick : List Nat → Nat`.  In the Hoon it is the
   root of the set's treap, which depends only on the set; the soundness of
   the pass needs only that it is a member.  The sets of registers
   (`hed-of`, `tel-of`, the entries of `imms`) are lists without duplicates
   (`insN` puts a register in only once).
4. The order of `pre` (`~(tap in …)` in the Hoon, the order of `rev.gen` in
   the model) changes nothing but the order of the lists of the joined sets:
   `joinRegE` is commutative and associative up to that order.
5. `%lti` (absent from the Hoon's `termin`) is kept as it is, as the Hoon's
   last case `%bom` would.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock

variable {Map : Type → Type} [HoonMap Map]

/-- A register map of facts. -/
abbrev AInfo := Nat → Option InfoReg
/-- The immediates: the registers known to hold each noun. -/
abbrev AImms := Noun → List Nat

/-- `+put:in` on a list without duplicates. -/
def insN (l : List Nat) (x : Nat) : List Nat := if x ∈ l then l else x :: l

/-- A function update. -/
def updA {α : Type} (f : Nat → α) (k : Nat) (v : α) : Nat → α := fun k' => if k' = k then v else f k'

/-- `+jab:by`: crashes on a missing key. -/
def jabA (m : AInfo) (k : Nat) (g : InfoReg → InfoReg) : Option AInfo :=
  (m k).map fun v => updA m k (some (g v))

/-- `join-reg`, with an equal value kept as it is (see the header, 2). -/
def joinRegE (a b : InfoReg) : InfoReg := if a = b then a else joinReg a b

/-- `join-info`, pointwise. -/
def joinInfoA (a b : AInfo) : AInfo := fun k =>
  match a k, b k with
  | some x, some y => some (joinRegE x y)
  | _, _ => none

/-- `join-imms`, pointwise. -/
def joinImmsA (a b : AImms) : AImms := fun n => (a n).filter (· ∈ b n)

/-- `?=([~ ^] has-imm)`. -/
def InfoReg.cellImm (a : InfoReg) : Bool :=
  match a.hasImm with
  | some (Noun.cell _ _) => true
  | _ => false

/-- `?=([~ @] has-imm)`. -/
def InfoReg.atomImm (a : InfoReg) : Bool :=
  match a.hasImm with
  | some (Noun.atom _) => true
  | _ => false

/-- The state `gen` of the walk. -/
structure AGen (Map : Type → Type) where
  new : Map Blob
  old : Nat → Nat
  info : Nat → Option AInfo
  imms : Nat → Option AImms
  rev : Nat → List Nat
  folded : Bool

/-- The part of the state that the body changes. -/
structure ABody where
  old : Nat → Nat
  loc : AInfo
  imml : AImms

/-- `del:ju`. -/
def delJu (rev : Nat → List Nat) (k o : Nat) : Nat → List Nat := updA rev k ((rev k).erase o)

/-- `+silt` of a list, as a list without duplicates. -/
def dedupN : List Nat → List Nat
  | [] => []
  | x :: l => let r := dedupN l; if x ∈ r then r else x :: r

/-- The facts at the start of a block with predecessors `pre` (step 3 of
`OptAlias.lean`): the join, then the refinement after a one-predecessor
`%brn`, `%brz`, `%clq`. -/
def aliasStart (g : AGen Map) (o : Nat) : List Nat → Option AInfo
  | [] => none
  | p :: t =>
    (g.info p).bind fun i0 =>
    (t.foldlM (fun acc o1 => (g.info o1).map fun i1 => joinInfoA acc i1) i0).bind fun info =>
    if t ≠ [] then some info else
    (HoonMap.get g.new p).bind fun pb =>
    match pb.fin with
    | Termin.brn s z o' =>
      if z.there = o ∧ o'.there ≠ o then jabA info s fun i => { i with hasImm := some (Noun.atom 0) }
      else if o'.there = o ∧ z.there ≠ o then jabA info s fun i => { i with hasImm := some (Noun.atom 1) }
      else if z.there = o'.there ∧ z.there = o then jabA info s fun i => { i with isLoob := true }
      else none
    | Termin.brz s z o' =>
      if z.there = o ∧ o'.there ≠ o then jabA info s fun i => { i with hasImm := some (Noun.atom 0) }
      else if o'.there = o ∧ z.there ≠ o then
        (info s).bind fun si => if si.isLoob then jabA info s fun i => { i with hasImm := some (Noun.atom 1) }
          else some info
      else some info
    | Termin.clq s z o' =>
      if z.there = o ∧ o'.there ≠ o then jabA info s fun i => { i with isCell := true }
      else if o'.there = o then some info else none
    | _ => some info

/-- The immediates at the start of a block. -/
def aliasStartImms (g : AGen Map) : List Nat → Option AImms
  | [] => some fun _ => []
  | p :: t => (g.imms p).bind fun m0 => t.foldlM (fun acc o1 => (g.imms o1).map fun m1 => joinImmsA acc m1) m0

/-- The edges into `o`: each predecessor with the arguments of each of its
jumps to `o`. -/
def aliasEdges (g : AGen Map) (o : Nat) (pre : List Nat) : Option (List (Nat × List (Option Nat))) :=
  (pre.mapM fun p => (HoonMap.get g.new p).map fun pb =>
    (getJmps pb.fin).filterMap fun j => if j.there = o then some (p, j.args) else none).map List.flatten

/-- The facts of the argument of one edge (step 4): `?>  ?=(^ args)`. -/
def aliasIn (g : AGen Map) : Nat × List (Option Nat) → Option (Option InfoReg)
  | (_, []) => none
  | (_, none :: _) => some none
  | (p, some u :: _) => ((g.info p).bind fun ip => ip u).map some

/-- The parameter loop: each parameter gets `param-info` of the arguments
passed to it. -/
def aliasPars (g : AGen Map) : List Nat → List (Nat × List (Option Nat)) → AInfo → Option AInfo
  | [], _, loc => some loc
  | x :: ps, edges, loc =>
    (edges.mapM (aliasIn g)).bind fun ins =>
    aliasPars g ps (edges.map fun e => (e.1, e.2.tail)) (updA loc x (some (paramInfo ins)))

/-- One op of the body: the op kept (renamed) or `none` if dropped, and the
new state. -/
def aliasOp (pick : List Nat → Nat) (st : ABody) : Pole → Option (Option Pole × ABody)
  | Pole.imm n d =>
    if st.imml n ≠ [] then some (none, { st with old := updA st.old d (pick (st.imml n)) })
    else some (some (Pole.imm n d), { st with loc := updA st.loc d (some { hasImm := some n }),
                                              imml := fun m => if m = n then insN (st.imml m) d else st.imml m })
  | Pole.mov s d => some (none, { st with old := updA st.old d (st.old s) })
  | Pole.inc s d =>
    let arg := st.old s
    (st.loc arg).bind fun ai =>
    match ai.decOf with
    | some x => some (none, { st with old := updA st.old d x })
    | none =>
      (jabA (updA st.loc d (some {})) arg fun i => { i with decOf := some d }).map fun loc =>
        (some (Pole.inc arg d), { st with loc := loc })
  | Pole.con h t d =>
    let h' := st.old h
    let t' := st.old t
    (st.loc h').bind fun hi => (st.loc t').bind fun ti =>
    let inter := hi.hedOf.filter (· ∈ ti.telOf)
    if inter ≠ [] then some (none, { st with old := updA st.old d (pick inter) })
    else
      (jabA (updA st.loc d (some { hasHed := some h', hasTel := some t', isCell := true })) h'
          fun i => { i with hedOf := insN i.hedOf d }).bind fun l1 =>
      (jabA l1 t' fun i => { i with telOf := insN i.telOf d }).map fun l2 =>
        (some (Pole.con h' t' d), { st with loc := l2 })
  | Pole.hed s d =>
    let arg := st.old s
    (st.loc arg).bind fun ai =>
    match ai.hasHed with
    | some x => some (none, { st with old := updA st.old d x })
    | none =>
      (jabA (updA st.loc d (some { hedOf := [arg] })) arg fun i => { i with hasHed := some d }).map fun loc =>
        (some (Pole.hed arg d), { st with loc := loc })
  | Pole.tal s d =>
    let arg := st.old s
    (st.loc arg).bind fun ai =>
    match ai.hasTel with
    | some x => some (none, { st with old := updA st.old d x })
    | none =>
      (jabA (updA st.loc d (some { telOf := [arg] })) arg fun i => { i with hasTel := some d }).map fun loc =>
        (some (Pole.tal arg d), { st with loc := loc })
  | Pole.cel p =>
    let arg := st.old p
    (st.loc arg).bind fun ai =>
    if ai.isCell then some (none, st)
    else (jabA st.loc arg fun i => { i with isCell := true }).map fun loc => (some (Pole.cel arg), { st with loc := loc })
  | Pole.lob p =>
    let arg := st.old p
    (st.loc arg).bind fun ai =>
    if ai.isLoob || ai.loobImm then some (none, st)
    else (jabA st.loc arg fun i => { i with isLoob := true }).map fun loc => (some (Pole.lob arg), { st with loc := loc })
  | Pole.equ l r => if st.old l = st.old r then some (none, st) else some (some (Pole.equ (st.old l) (st.old r)), st)
  | Pole.hsp n f => some (some (Pole.hsp n f), st)
  | Pole.hse n f => some (some (Pole.hse n f), st)
  | Pole.hdp n p f => some (some (Pole.hdp n (st.old p) f), st)
  | Pole.hde n p f => some (some (Pole.hde n (st.old p) f), st)
  | Pole.hmp a v f => some (some (Pole.hmp a (v.map st.old) f), st)
  | Pole.hme a v f => some (some (Pole.hme a (v.map st.old) f), st)
  | Pole.hcp n f => some (some (Pole.hcp n f), st)
  | Pole.hce n f => some (some (Pole.hce n f), st)
  | Pole.spy e p d => some (some (Pole.spy (st.old e) (st.old p) d), { st with loc := updA st.loc d (some {}) })
  | Pole.nok u f d => some (some (Pole.nok (st.old u) (st.old f) d), { st with loc := updA st.loc d (some {}) })
  | Pole.cal a v d => some (some (Pole.cal a (v.map st.old) d), { st with loc := updA st.loc d (some {}) })
  | Pole.caf a v d n => some (some (Pole.caf a (v.map st.old) d n), { st with loc := updA st.loc d (some {}) })
  | Pole.cam a v d k => some (some (Pole.cam a (v.map st.old) d k), { st with loc := updA st.loc d (some {}) })
  | Pole.csl a s d => some (some (Pole.csl a (st.old s) d), { st with loc := updA st.loc d (some {}) })
  | Pole.csf a s d n => some (some (Pole.csf a (st.old s) d n), { st with loc := updA st.loc d (some {}) })
  | Pole.csm a s d k => some (some (Pole.csm a (st.old s) d k), { st with loc := updA st.loc d (some {}) })

/-- The body (`+roll`): the ops kept, in order. -/
def aliasBody (pick : List Nat → Nat) : List Pole → ABody → Option (List Pole × ABody)
  | [], st => some ([], st)
  | op :: l, st =>
    (aliasOp pick st op).bind fun r =>
    (aliasBody pick l r.2).map fun r2 => (r.1.toList ++ r2.1, r2.2)

/-- A two-way end folded to a hop to `go`, the edge to `cut` deleted unless
it is `go`. -/
def aliasFold (rev : Nat → List Nat) (o go cut : Nat) : Termin × (Nat → List Nat) × Bool :=
  (Termin.hop { args := [], there := go }, if go = cut then rev else delJu rev cut o, true)

/-- The end (step 6): the new end, `rev.gen` and `folded`. -/
def aliasFin (old : Nat → Nat) (loc : AInfo) (rev : Nat → List Nat) (f : Bool) (o : Nat) :
    Termin → Option (Termin × (Nat → List Nat) × Bool)
  | Termin.clq s z o' =>
    if z.args ≠ [] ∨ o'.args ≠ [] then none else
    let c := old s
    (loc c).map fun ic =>
    if ic.isCell || ic.cellImm then aliasFold rev o z.there o'.there
    else if ic.isLoob || ic.atomImm then aliasFold rev o o'.there z.there
    else (Termin.clq c z o', rev, f)
  | Termin.eqq l r z o' =>
    if z.args ≠ [] ∨ o'.args ≠ [] then none else
    if old l ≠ old r then some (Termin.eqq (old l) (old r) z o', rev, f)
    else some (aliasFold rev o z.there o'.there)
  | Termin.brn s z o' =>
    if z.args ≠ [] ∨ o'.args ≠ [] then none else
    let c := old s
    (loc c).map fun ic =>
    match ic.hasImm with
    | none => if ic.isLoob then (Termin.brz c z o', rev, true) else (Termin.brn c z o', rev, f)
    | some (Noun.atom 0) => aliasFold rev o z.there o'.there
    | some (Noun.atom 1) => aliasFold rev o o'.there z.there
    | some _ => (Termin.bom none, delJu (delJu rev o'.there o) z.there o, f)
  | Termin.brz s z o' =>
    if z.args ≠ [] ∨ o'.args ≠ [] then none else
    let c := old s
    (loc c).map fun ic =>
    let zero : Option Bool := match ic.hasImm with
      | some v => some (decide (v = Noun.atom 0))
      | none => if ic.isCell then some false else none
    match zero with
    | none => (Termin.brz c z o', rev, f)
    | some true => aliasFold rev o z.there o'.there
    | some false => aliasFold rev o o'.there z.there
  | Termin.hop t => some (Termin.hop { t with args := t.args.map (Option.map old) }, rev, f)
  | Termin.jmp a v => some (Termin.jmp a (v.map old), rev, f)
  | Termin.jmf a v n => some (Termin.jmf a (v.map old) n, rev, f)
  | Termin.jsp a s => some (Termin.jsp a (old s), rev, f)
  | Termin.jsf a s n => some (Termin.jsf a (old s) n, rev, f)
  | Termin.don s => some (Termin.don (old s), rev, f)
  | Termin.bom b => some (Termin.bom b, rev, f)
  | Termin.lti n s z o' => some (Termin.lti n s z o', rev, f)

/-- The facts of the entry block: `*info-reg` for `0 .. n-args - 1`. -/
def entryInfo (nargs : Nat) : AInfo := fun r => if r < nargs then some {} else none

/-- One block of `topo` (steps 2 to 7). -/
def aliasBlock (pick : List Nat → Nat) (nargs : Nat) (bl : Map Blob) (g : AGen Map) (o : Nat) : Option (AGen Map) :=
  let pre := g.rev o
  if pre = [] ∧ o ≠ 0 then
    (HoonMap.get bl o).map fun b =>
      { g with folded := true, rev := (getJmps b.fin).foldl (fun acc j => delJu acc j.there o) g.rev }
  else
  (if pre = [] then some (entryInfo nargs) else aliasStart g o pre).bind fun info =>
  (aliasStartImms g pre).bind fun imms =>
  (HoonMap.get bl o).bind fun b =>
  (aliasEdges g o pre).bind fun edges =>
  (aliasPars g b.par edges info).bind fun loc0 =>
  (aliasBody pick b.body { old := g.old, loc := loc0, imml := imms }).bind fun rb =>
  (aliasFin rb.2.old rb.2.loc g.rev g.folded o b.fin).map fun rf =>
  { new := HoonMap.put g.new o { par := b.par, body := rb.1, fin := rf.1 }
    old := rb.2.old
    info := updA g.info o (some rb.2.loc)
    imms := updA g.imms o (some rb.2.imml)
    rev := rf.2.1
    folded := rf.2.2 }

/-- The walk over `topo`. -/
def aliasWalk (pick : List Nat → Nat) (nargs : Nat) (bl : Map Blob) : List Nat → AGen Map → Option (AGen Map)
  | [], g => some g
  | o :: topo, g => (aliasBlock pick nargs bl g o).bind fun g' => aliasWalk pick nargs bl topo g'

/-- **The model of `+alias`**: `[folded new]`. -/
def aliasM (pick : List Nat → Nat) (nargs : Nat) (bl : Map Blob) (rev : Map (List Nat)) (topo : List Nat) :
    Option (Bool × Map Blob) :=
  (aliasWalk pick nargs bl topo
    { new := HoonMap.empty, old := id, info := fun _ => none, imms := fun _ => none,
      rev := fun o => dedupN ((HoonMap.get rev o).getD []), folded := false }).map fun g => (g.folded, g.new)

end Opt
end SkaModel
end Formalization
