import lemmas.Ska.RunStep

/-!
# The analysis with its state: `+ska-callgraph` and `+ska-poke`, arm by arm

A state-passing model of the analysis of `nock-compilation.hoon`: the trap
`fol-loop` with the whole `gen` of `+run` threaded through it (the call graph,
the memo of finished functions, `order`, `stk`, `next`, `moved`, `tick`,
`ticks`, the `%fast` registrations and the statistics), the `resolve` loop of
a direct call, `+analyze`, `+run`, the pass loop over a component and its
member loop, `+dirty`, `+sweep`, `+above`, `+cull`, `+pop`, `+ska-callgraph`,
`+prune-callgraph`, `+memo-final-entry`, and the part of `+ska-poke` that
writes the persistent memo and indexes the datums by code bell.  The rest of
`+ska-poke` (baking, the code table, `+eval-finalized`, the `+ska-cole-*`
arms) is not modelled here.

Each arm has the Hoon's name (in `lowerCamelCase`) and its branches in the
Hoon's order.  The recursion between `fol-loop`, `resolve`, `+analyze`,
`+run`, the pass loop and the member loop is fuelled: every call from one of
them to another, or to itself, takes one unit, and every loop that is not
structural (`+sweep`, `+cull`, `+prune-callgraph`) takes the fuel of the
arm it runs in.  `none` is a crash of the Hoon or too little fuel.  A
theorem about a result that the model returns holds of the Hoon whenever the
Hoon returns; that some fuel is enough is the termination of the Hoon.

Maps and sets are a parameter, `Treap`: Hoon's treaps of `+by` and `+in`,
with `get`, `put`, `del`, and two listings, `tap` (the order of
`~(tap by ...)`) and `rap` (the order in which `~(rep by ...)` visits).  Both
orders come from `+mug` of the keys, which is not modelled; the laws say what
the analysis needs: lookups after `put` and `del`, the listings list the map,
and a treap is determined by its contents (`ext`, which holds of the treaps
that `+put:by` and `+del:by` build).  So `+silt`, `+dif:in` and the other
operations on whole sets are given by `put` and `del`, and give the treap that
the Hoon's arm gives.

Three arms are parameters too (`Env`): `+he-sock` (the homeomorphic embedding,
which only chooses between two sound answers), `+soft-spot` (which reads a
`spot` out of a `%spot` hint, and feeds only the location of the code) and
`+register-fast` (which reads the products of a `%fast` hint and changes only
the registrations); `he-threshold` is `32`.

The fixed-table model of `FolLoop.lean` is the projection of this one
(`Bridge.lean`).
-/

namespace Formalization
namespace SkaModel
namespace Ana

open Nock

/-! ## Maps and sets -/

/-- The key types of the treaps, with their noun encoding.  `+put:by` and
`+tap:by` order a map by `+gor` and `+mor` of the key nouns, so the treap
operations are over keys with an injective encoding, and may depend on it. -/
class TKey (κ : Type) where
  enc : κ → Noun
  enc_inj : ∀ a b, enc a = enc b → a = b

/-- The treaps of `+by` (a map from `κ` to `ν`) and of `+in` (a set, `ν` the
unit type), over keys with their noun encoding (`TKey`), with the laws the
analysis uses.  `tap` lists a map in the order of `~(tap by ...)`, `rap` in
the order in which `~(rep by ...)` visits it.  `toNoun` and `setNoun` are the
treaps as nouns, the keys encoded by `TKey.enc`.

`get_put` and `get_del` have proved counterparts for atom keys in
`Compiler/TreapMap.lean` (`TreapMap.get_put`, `TreapMap.get_del`, from
`putF_spec` and `delF_spec`), and the listings in `Hoon/TapBy.lean`
(`mem_tapList`) and `Hoon/RepBy.lean` (the pre-order of `+rep`).  `ext`
(a treap is determined by its contents) rests on treaps ordered by `+gor` and
`+mor` being canonical, which is not proved yet. -/
class Treap (M : Type → Type → Type) where
  empty {κ ν : Type} : M κ ν
  get {κ ν : Type} [DecidableEq κ] [TKey κ] : M κ ν → κ → Option ν
  put {κ ν : Type} [DecidableEq κ] [TKey κ] : M κ ν → κ → ν → M κ ν
  del {κ ν : Type} [DecidableEq κ] [TKey κ] : M κ ν → κ → M κ ν
  tap {κ ν : Type} [TKey κ] : M κ ν → List (κ × ν)
  rap {κ ν : Type} [TKey κ] : M κ ν → List (κ × ν)
  toNoun {κ ν : Type} [TKey κ] : (ν → Noun) → M κ ν → Noun
  setNoun {κ : Type} [TKey κ] : M κ Unit → Noun
  get_empty {κ ν : Type} [DecidableEq κ] [TKey κ] (k : κ) : get (empty : M κ ν) k = none
  get_put {κ ν : Type} [DecidableEq κ] [TKey κ] (m : M κ ν) (k : κ) (v : ν) (k' : κ) :
    get (put m k v) k' = if k' = k then some v else get m k'
  get_del {κ ν : Type} [DecidableEq κ] [TKey κ] (m : M κ ν) (k k' : κ) :
    get (del m k) k' = if k' = k then none else get m k'
  mem_tap {κ ν : Type} [DecidableEq κ] [TKey κ] (m : M κ ν) (k : κ) (v : ν) :
    (k, v) ∈ tap m ↔ get m k = some v
  mem_rap {κ ν : Type} [DecidableEq κ] [TKey κ] (m : M κ ν) (k : κ) (v : ν) :
    (k, v) ∈ rap m ↔ get m k = some v
  ext {κ ν : Type} [DecidableEq κ] [TKey κ] (a b : M κ ν) : (∀ k, get a k = get b k) → a = b

variable {M : Type → Type → Type} [Treap M] {R : Type}

namespace Treap

/-- `+has:by`, `+has:in`. -/
def has {κ ν : Type} [DecidableEq κ] [TKey κ] (m : M κ ν) (k : κ) : Bool := (get m k).isSome

/-- `+gut:by`. -/
def gut {κ ν : Type} [DecidableEq κ] [TKey κ] (m : M κ ν) (k : κ) (d : ν) : ν := (get m k).getD d

/-- `+put:in`. -/
def ins {κ : Type} [DecidableEq κ] [TKey κ] (s : M κ Unit) (k : κ) : M κ Unit := put s k ()

/-- `+silt`: the set of a list. -/
def silt {κ : Type} [DecidableEq κ] [TKey κ] (l : List κ) : M κ Unit := l.foldl ins empty

/-- `+dif:in`: `a` without the members of `b`. -/
def dif {κ ν μ : Type} [DecidableEq κ] [TKey κ] (a : M κ ν) (b : M κ μ) : M κ ν :=
  (tap b).foldl (fun s k => del s k.1) a

/-- `+wyt:in`. -/
def wyt {κ ν : Type} [TKey κ] (m : M κ ν) : Nat := (tap m).length

end Treap

/-! ## The types, with their nouns -/

/-- `+$identity`: `[more=sock fol=^]`. -/
abbrev Ident := Sock × Noun

def identNoun (i : Ident) : Noun := C i.1.toNoun i.2

/-- `+$callee-entry`: `[seat=(unit spot) id=identity]`; a spot is kept as its
noun. -/
structure CalleeEntry where
  seat : Option Noun
  id : Ident
  deriving DecidableEq

def CalleeEntry.toNoun (c : CalleeEntry) : Noun := C (unitNoun (fun x => x) c.seat) (identNoun c.id)

theorem Cape.toNoun_inj : ∀ a b : Cape, a.toNoun = b.toNoun → a = b
  | Cape.yes, Cape.yes, _ => rfl
  | Cape.no, Cape.no, _ => rfl
  | Cape.cell a1 a2, Cape.cell b1 b2, h => by
    simp only [Cape.toNoun, Noun.cell.injEq] at h
    rw [Cape.toNoun_inj a1 b1 h.1, Cape.toNoun_inj a2 b2 h.2]
  | Cape.yes, Cape.no, h | Cape.no, Cape.yes, h => by simp [Cape.toNoun] at h
  | Cape.yes, Cape.cell _ _, h | Cape.no, Cape.cell _ _, h => by simp [Cape.toNoun] at h
  | Cape.cell _ _, Cape.yes, h | Cape.cell _ _, Cape.no, h => by simp [Cape.toNoun] at h

theorem Sock.toNoun_inj : ∀ a b : Sock, a.toNoun = b.toNoun → a = b
  | Sock.void, Sock.void, _ => rfl
  | Sock.mk c d, Sock.mk c' d', h => by
    simp only [Sock.toNoun, Noun.cell.injEq] at h
    rw [Cape.toNoun_inj c c' h.1, h.2]
  | Sock.void, Sock.mk _ _, h | Sock.mk _ _, Sock.void, h => by simp [Sock.toNoun] at h

instance : TKey Noun := ⟨fun x => x, fun _ _ h => h⟩
instance : TKey Sock := ⟨Sock.toNoun, Sock.toNoun_inj⟩
instance : TKey Ident := ⟨identNoun, fun a b h => by
  simp only [identNoun, Noun.cell.injEq] at h
  exact Prod.ext (Sock.toNoun_inj _ _ h.1) h.2⟩
instance : TKey Bell := ⟨Bell.toNoun, fun a b h => by
  cases a; cases b
  simp only [Bell.toNoun, Noun.cell.injEq] at h
  rw [Sock.toNoun_inj _ _ h.1, h.2]⟩
instance : TKey CalleeEntry := ⟨CalleeEntry.toNoun, fun a b h => by
  cases a with | mk sa ia => cases b with | mk sb ib =>
  simp only [CalleeEntry.toNoun, identNoun, Noun.cell.injEq] at h
  have hs : sa = sb := by
    cases sa <;> cases sb <;> simp_all [unitNoun]
  rw [hs, Prod.ext (Sock.toNoun_inj _ _ h.2.1) h.2.2]⟩

/-- `+$datum`, with all its fields. -/
structure FDatum (M : Type → Type → Type) where
  callees : M CalleeEntry Unit
  nomm : Nomm
  less : Sock
  indi : Cape
  seek : Cape
  prod : Sock
  map : Noun
  area : Option Noun

def FDatum.toNoun (d : FDatum M) : Noun :=
  C (Treap.setNoun d.callees)
    (C d.nomm.toNoun (C d.less.toNoun (C d.indi.toNoun (C d.seek.toNoun
      (C (C d.prod.toNoun d.map) (unitNoun (fun x => x) d.area))))))

/-- `*datum`: a function in progress not analysed yet. -/
def FDatum.bunt : FDatum M :=
  ⟨Treap.empty, Nomm.n0 0, Sock.dunno, Cape.no, Cape.no, Sock.void, A 0, none⟩

/-- The fields that `Datum` keeps. -/
def FDatum.core (d : FDatum M) : Datum := ⟨d.nomm, d.less, d.indi, d.seek, d.prod, d.map⟩

theorem FDatum.bunt_core : (FDatum.bunt : FDatum M).core = Datum.bunt := rfl

/-- `+$callgraph`. -/
abbrev Callgraph (M : Type → Type → Type) := M Ident (FDatum M)

/-- `+$memo`: formula, then code requirement, to the entry. -/
abbrev Memo (M : Type → Type → Type) := M Noun (M Sock (Ident × FDatum M))

def entryNoun (e : Ident × FDatum M) : Noun := C (identNoun e.1) e.2.toNoun

def memoNoun (m : Memo M) : Noun :=
  Treap.toNoun (Treap.toNoun entryNoun) m

/-- `stats` of `+$ska-state`. -/
structure Stats where
  runs : Nat
  passes : Nat
  lateRuns : Nat
  misses : Nat
  culled : Nat

def Stats.toNoun (s : Stats) : Noun := C (A s.runs) (C (A s.passes) (C (A s.lateRuns) (C (A s.misses) (A s.culled))))

/-- `+$ska-state`; the `%fast` registrations `regs` are of a type `R`. -/
structure SkaState (M : Type → Type → Type) (R : Type) where
  g : Callgraph M
  done : Memo M
  order : M Ident Nat
  stk : List Ident
  next : Nat
  moved : M Ident Unit
  tick : Nat
  ticks : M Ident (Nat × Nat)
  regs : R
  stats : Stats

def SkaState.toNoun (regsNoun : R → Noun) (st : SkaState M R) : Noun :=
  C (Treap.toNoun FDatum.toNoun st.g)
    (C (memoNoun st.done)
      (C (Treap.toNoun A st.order)
        (C (listNoun identNoun st.stk)
          (C (A st.next)
            (C (Treap.setNoun st.moved)
              (C (A st.tick)
                (C (Treap.toNoun (fun p => C (A p.1) (A p.2)) st.ticks)
                  (C (regsNoun st.regs) st.stats.toNoun))))))))

/-- `=|  st=ska-state` with `regs` set, as `+ska-callgraph` starts. -/
def SkaState.init (reg : R) : SkaState M R :=
  ⟨Treap.empty, Treap.empty, Treap.empty, [], 0, Treap.empty, 0, Treap.empty, reg, ⟨0, 0, 0, 0, 0⟩⟩

/-- `gen` of `+run`: `[want indi seek callees area low back st]`. -/
structure GenS (M : Type → Type → Type) (R : Type) where
  want : Cape
  indi : Cape
  seek : Cape
  callees : M CalleeEntry Unit
  area : Option Noun
  low : Nat
  back : Bool
  st : SkaState M R

def GenS.toNoun (regsNoun : R → Noun) (g : GenS M R) : Noun :=
  C g.want.toNoun (C g.indi.toNoun (C g.seek.toNoun
    (C (Treap.setNoun g.callees) (C (unitNoun (fun x => x) g.area)
      (C (A g.low) (C (flag g.back) (g.st.toNoun regsNoun)))))))

/-- The capes of `gen` that the fixed-table model keeps. -/
def GenS.gen (g : GenS M R) : Gen := { want := g.want, indi := g.indi, seek := g.seek }

/-- The arms that are parameters. -/
structure Env (R : Type) where
  /-- `+he-sock` -/
  he : Sock → Sock → Bool
  /-- `+soft-spot`, the spot as its noun -/
  softSpot : Noun → Option Noun
  /-- `+register-fast` on the products of the hint and its formula:
  whether the registration missed its parent, and the registrations -/
  registerFast : Sock → Sock → R → Option (Bool × R)
  /-- `he-threshold` -/
  threshold : Nat

/-! ## The memo and the graph -/

/-- `+gut:mi`. -/
def gutMi (m : Memo M) (f : Noun) : M Sock (Ident × FDatum M) := Treap.gut m f Treap.empty

/-- The loop of `+git:mi` over `~(tap by (gut m f))`. -/
def gitLoop (s : Sock) : List (Sock × (Ident × FDatum M)) → Option (Option (Ident × FDatum M))
  | [] => some none
  | (_, (i, d)) :: es =>
    match hitTest ⟨i.1, i.2, d.core⟩ s with
    | none => none
    | some true =>
      let p := patchProd d.prod d.map s
      some (some (i, { d with prod := p.sock, map := p.src }))
    | some false => gitLoop s es

/-- `+git:mi`: a hit for the formula `f` on the subject sock `s`, with its own
identity and its datum patched for `s`. -/
def gitMi (m : Memo M) (f : Noun) (s : Sock) : Option (Option (Ident × FDatum M)) :=
  gitLoop s (Treap.tap (gutMi m f))

/-- `+put:mi`. -/
def putMi (m : Memo M) (i : Ident) (d : FDatum M) : Memo M :=
  Treap.put m i.2 (Treap.put (gutMi m i.2) d.less (i, d))

/-- `+git-g`. -/
def gitG (g : Callgraph M) (i : Ident) : FDatum M := Treap.gut g i FDatum.bunt

/-- The graph as `+recursive-call` reads it, through `+git-g`. -/
def gCore (g : Callgraph M) : Ident → Option Datum := fun i => (Treap.get g i).map FDatum.core

/-- `+memo-final-entry`. -/
def memoFinalEntry (id : Ident) (d : FDatum M) : Ident × FDatum M :=
  ((Ca.app d.indi id.1, id.2), { d with callees := Treap.empty })

/-! ## `fol-loop` -/

/-- The recursion of `fol-loop`: `fol-loop(fol, sub, seat, memo-key,
bare-call, defer)` from `gen`. -/
abbrev FolGoS (M : Type → Type → Type) (R : Type) :=
  Noun → Anno → Option Noun → Option Noun → Bool → Bool → GenS M R → Option (FolOut × GenS M R)

/-- `resolve`: the callee's identity and datum, from `gen`. -/
abbrev ResGo (M : Type → Type → Type) (R : Type) :=
  Ident → GenS M R → Option ((Ident × FDatum M) × GenS M R)

/-- The `%2` case once both operands are analysed. -/
def callStep (res : ResGo M R) (go : FolGoS M R) (seat mk : Option Noun) (bc df : Bool)
    (s f : FolOut) (gen : GenS M R) : Option (FolOut × GenS M R) :=
  if s.prod.sock = Sock.void ∨ f.prod.sock = Sock.void then
    some (⟨Nomm.n2 s.nomm f.nomm none, ⟨Sock.void, A 0⟩, false⟩, gen)
  else
  match f.prod.sock, bc with
  | Sock.mk Cape.yes (Noun.cell fa fb), false =>
    if mk = none ∧ df = false ∧ inlineable (C fa fb) = true ∧ safeFolFol f.nomm = true then
      (go (C fa fb) s.prod seat mk bc df
          { gen with want := Ca.uni gen.want (distribute Cape.yes f.prod.src) }).bind fun i =>
      some (⟨Nomm.n7 s.nomm i.1.nomm, i.1.prod, false⟩, i.2)
    else
      (res (s.prod.sock, C fa fb) gen).bind fun r =>
      match r.1.2.less with
      | Sock.void => none
      | Sock.mk lc _ =>
        some (⟨Nomm.n2 s.nomm f.nomm (some (⟨r.1.2.less, C fa fb⟩, mk)),
            ⟨r.1.2.prod, Pi.compose r.1.2.map s.prod.src⟩, false⟩,
          { r.2 with
            want := Ca.uni r.2.want (Ca.uni (distribute Cape.yes f.prod.src)
              (distribute lc s.prod.src)),
            indi := Ca.uni r.2.indi (distribute r.1.2.indi s.prod.src),
            seek := Ca.uni r.2.seek (distribute r.1.2.seek s.prod.src),
            callees := Treap.ins r.2.callees ⟨seat, r.1.1⟩ })
  | _, _ =>
    some (⟨Nomm.n2 s.nomm f.nomm none, Anno.dunno, false⟩,
      { gen with indi := Ca.uni gen.indi (distribute Cape.yes f.prod.src),
                 seek := Ca.uni gen.seek (distribute Cape.yes f.prod.src) })

/-- The arm of a `%mean` hint whose trap has a known battery. -/
def meanArm (go : FolGoS M R) (tag : Nat) (h : FolOut) (seat mk : Option Noun) (bc : Bool)
    (gen : GenS M R) : Option (Option (Bell × Option Noun) × GenS M R) :=
  if ¬ (tag = Tag.mean ∧ h.saf = false ∧ h.prod.sock ≠ Sock.void) then some (none, gen) else
  (So.pull h.prod.sock 2).bind fun bat =>
  match bat with
  | Sock.mk Cape.yes (Noun.cell _ _) =>
    (go (n3 (A 2) (slot 1) (slot 2)) h.prod seat mk bc true gen).bind fun cg =>
    match cg.1.nomm with
    | Nomm.n2 _ _ (some (b, _)) =>
      some (some (b, match cg.1.prod.sock with
                     | Sock.mk c d => if Ca.all c = true then some d else none
                     | Sock.void => none), cg.2)
    | _ => none
  | _ => some (none, gen)

/-- The `=?  .` of a `%spot` hint with a constant spot: the location of the
code (`area`, if not set yet) and of the calls below (`seat`). -/
def spotHint (env : Env R) (tag : Nat) (h1 h2 : Noun) (seat : Option Noun) (gen : GenS M R) :
    Option Noun × GenS M R :=
  if tag = Tag.spot ∧ h1 = A 1 then
    match env.softSpot h2 with
    | none => (seat, gen)
    | some pot => (some pot, if gen.area = none then { gen with area := some pot } else gen)
  else (seat, gen)

/-- The `=?  gen` of a `%fast` hint: `+register-fast`. -/
def fastHint (env : Env R) (tag : Nat) (h f : FolOut) (gen : GenS M R) : Option (GenS M R) :=
  if tag = Tag.fast then
    (env.registerFast h.prod.sock f.prod.sock gen.st.regs).map fun r =>
      let gen := { gen with st := { gen.st with regs := r.2 } }
      if r.1 then { gen with st := { gen.st with stats := { gen.st.stats with misses := gen.st.stats.misses + 1 } } }
      else gen
  else some gen

/-- One level of `fol-loop`, the cases of its `?+` in the Hoon's order. -/
def folStep (env : Env R) (res : ResGo M R) (go : FolGoS M R) (fol : Noun) (sub : Anno)
    (seat mk : Option Noun) (bc df : Bool) (gen : GenS M R) : Option (FolOut × GenS M R) :=
  match shape fol with
  | Shape.cons a b q =>
    (go (C a b) sub seat mk bc df gen).bind fun l =>
    (go q sub seat mk bc df l.2).bind fun r =>
    let pr := consProd l.1 r.1
    some (⟨Nomm.cons l.1.nomm r.1.nomm, pr.1, pr.2⟩, r.2)
  | Shape.op0 p =>
    let pr : Option Anno :=
      if p = 0 then some Anno.dunno
      else if p = 1 then some sub
      else (So.pull sub.sock p).map fun s => ⟨s, Pi.slot sub.src p⟩
    pr.map fun pr => (⟨Nomm.n0 p, pr, false⟩, gen)
  | Shape.op1 p => some (⟨Nomm.n1 p, ⟨Sock.mk Cape.yes p, A 0⟩, true⟩, gen)
  | Shape.op2 a b q =>
    (go (C a b) sub seat mk bc df gen).bind fun s =>
    (go q sub seat mk bc df s.2).bind fun f =>
    callStep res go seat mk bc df s.1 f.1 f.2
  | Shape.op3 a b =>
    (go (C a b) sub seat mk bc df gen).bind fun p =>
    some (⟨Nomm.n3 p.1.nomm, Anno.dunno, false⟩, p.2)
  | Shape.op4 a b =>
    (go (C a b) sub seat mk bc df gen).bind fun p =>
    some (⟨Nomm.n4 p.1.nomm, Anno.dunno, false⟩, p.2)
  | Shape.op5 a b q =>
    (go (C a b) sub seat mk bc df gen).bind fun p =>
    (go q sub seat mk bc df p.2).bind fun q =>
    some (⟨Nomm.n5 p.1.nomm q.1.nomm, Anno.dunno, false⟩, q.2)
  | Shape.op6 a b q r =>
    (go (C a b) sub seat mk bc df gen).bind fun p =>
    (go q sub seat mk bc df p.2).bind fun q =>
    (go r sub seat mk bc df q.2).bind fun r =>
    some (⟨Nomm.n6 p.1.nomm q.1.nomm r.1.nomm, doubleInt q.1.prod r.1.prod, false⟩, r.2)
  | Shape.op7 a b q =>
    (go (C a b) sub seat mk bc df gen).bind fun p =>
    (go q p.1.prod seat mk bc df p.2).bind fun q =>
    some (⟨Nomm.n7 p.1.nomm q.1.nomm, q.1.prod, false⟩, q.2)
  | Shape.op8 a b q => go (n3 (A 7) (C (C a b) (slot 1)) q) sub seat mk bc df gen
  | Shape.op9 p a b => go (n3 (A 7) (C a b) (n3 (A 2) (slot 1) (slot p))) sub seat mk bc df gen
  | Shape.op10 ax don r1 r2 =>
    if ax = 0 then some (⟨Nomm.n0 0, Anno.dunno, false⟩, gen) else
    (go don sub seat mk bc df gen).bind fun dn =>
    (go (C r1 r2) sub seat mk bc df dn.2).bind fun rc =>
    (So.darn rc.1.prod.sock ax dn.1.prod.sock).map fun s =>
      (⟨Nomm.n10 ax dn.1.nomm rc.1.nomm, ⟨s, Pi.edit rc.1.prod.src ax dn.1.prod.src⟩, false⟩, rc.2)
  | Shape.op11s p a b =>
    if p = Tag.bare then
      go (n3 (A 2) (slot 1) (quote (C (A 11) (C (A p) (C a b))))) sub seat mk true df gen
    else
    (go (C a b) sub seat mk bc df gen).bind fun q =>
    some (⟨Nomm.n11s p q.1.nomm (C a b), q.1.prod, false⟩, q.2)
  | Shape.op11d tag h1 h2 f =>
    let sg := spotHint env tag h1 h2 seat gen
    (go (C h1 h2) sub sg.1 mk bc df sg.2).bind fun h =>
    if tag = Tag.memo ∧ h.1.saf = true ∧ h.1.prod.sock ≠ Sock.void then
      go (n3 (A 2) (slot 1) (quote f)) sub sg.1 (some h.1.prod.sock.data) bc df h.2
    else
    (meanArm go tag h.1 sg.1 mk bc h.2).bind fun arm =>
    (go f sub sg.1 mk bc df arm.2).bind fun fr =>
    (fastHint env tag h.1 fr.1 fr.2).bind fun gen =>
    some (⟨match arm.1 with
           | some (bl, k) => Nomm.mean h.1.nomm bl fr.1.nomm f k
           | none => Nomm.n11d tag h.1.nomm fr.1.nomm f,
         fr.1.prod,
         decide ((tag = Tag.spot ∨ tag = Tag.mean) ∧ h.1.saf = true ∧ fr.1.saf = true)⟩, gen)
  | Shape.op12 a b q =>
    (go (C a b) sub seat mk bc df gen).bind fun p =>
    (go q sub seat mk bc df p.2).bind fun q =>
    some (⟨Nomm.n12 p.1.nomm q.1.nomm, Anno.dunno, false⟩, q.2)
  | Shape.other => some (⟨Nomm.n0 0, Anno.dunno, false⟩, gen)

/-! ## `resolve` -/

/-- `+analyze`: the lowlink and the state. -/
abbrev AnaGo (M : Type → Type → Type) (R : Type) := Ident → SkaState M R → Option (Nat × SkaState M R)

/-- One turn of the `resolve` loop of a direct call to `idT`: an exact
identity in the graph (a recursive call if in `order`), a finished function
of this poke (`done`), a recursive call to a function in progress (`%rec`,
its product patched) or a generalized identity (`%he`, resolved again), or a
new function, analysed now.

`orig` is the identity the loop began with, the site sock and formula of the
call (`[sock.prod.s fol-new]` of the trap around the loop): the Hoon asks
`+git:mi` with these, not with `id-there`, so after a `%he` step the lookup
is the one that just missed, on the same `done`.  The loop `resolve` passed
in is the loop for the same `orig`. -/
def resolveStep (env : Env R) (resolve : ResGo M R) (analyze : AnaGo M R) (orig idT : Ident)
    (gen : GenS M R) : Option ((Ident × FDatum M) × GenS M R) :=
  match Treap.get gen.st.g idT with
  | some d =>
    match Treap.get gen.st.order idT with
    | none => some ((idT, d), gen)
    | some o => some ((idT, d), { gen with low := min gen.low o, back := true })
  | none =>
  match gitMi gen.st.done orig.2 orig.1 with
  | none => none
  | some (some m) => some (m, gen)
  | some none =>
  match recursiveCall env.he env.threshold idT gen.st.stk (gCore gen.st.g) with
  | none => none
  | some (some (false, i)) => resolve i gen
  | some (some (true, i)) =>
    let d := gitG gen.st.g i
    let m := patchProd d.prod d.map idT.1
    (Treap.get gen.st.order i).map fun o =>
      ((i, { d with prod := m.sock, map := m.src }), { gen with low := min gen.low o, back := true })
  | some none =>
    (analyze idT gen.st).map fun r =>
      ((idT, gitG r.2.g idT), { gen with st := r.2, low := min gen.low r.1 })

/-! ## `+run` -/

/-- `+run`: `[low back changed]` and the state. -/
abbrev RunGo (M : Type → Type → Type) (R : Type) :=
  Ident → Nat → SkaState M R → Option ((Nat × Bool × Bool) × SkaState M R)

/-- The `gen` that `+run` starts `fol-loop` with. -/
def genInit (index : Nat) (st : SkaState M R) : GenS M R :=
  ⟨Cape.no, Cape.no, Cape.no, Treap.empty, none, index, false, st⟩

/-- What `+run` makes of the result of `fol-loop` on the identity `id`, whose
datum was `data` when the run began: `[low back changed]` and the state. -/
def runEnd (id : Ident) (data : FDatum M) (out : FolOut) (gen : GenS M R) :
    (Nat × Bool × Bool) × SkaState M R :=
  let rd := runDatum (Treap.has gen.st.moved id) id.1 out gen.gen data.core
  let dn : FDatum M := ⟨gen.callees, rd.1.nomm, rd.1.less, rd.1.indi, rd.1.seek, rd.1.prod, rd.1.map, gen.area⟩
  let st := gen.st
  -- when `id` is in `moved` already, the `put` changes nothing (`Treap.ext`)
  let st := if rd.2.1 then { st with moved := Treap.ins st.moved id } else st
  let tk := st.tick + 1
  let st := { st with tick := tk,
                      ticks := Treap.put st.ticks id
                        (tk, if rd.2.2 then tk else (Treap.gut st.ticks id (0, 0)).2) }
  ((gen.low, gen.back, rd.2.2), { st with g := Treap.put st.g id dn })

/-- One run of `+run`. -/
def runStep (fol : FolGoS M R) (id : Ident) (index : Nat) (st : SkaState M R) :
    Option ((Nat × Bool × Bool) × SkaState M R) :=
  let st := { st with stats := { st.stats with runs := st.stats.runs + 1 } }
  let data := gitG st.g id
  (fol id.2 ⟨id.1, A 1⟩ none none false false (genInit index st)).map fun r =>
    runEnd id data r.1 r.2

/-! ## The arms around a component -/

/-- `+above`: the functions on the stack above and including `id`, latest
first.  `none` is the crash when `id` is not on the stack. -/
def above (id : Ident) : List Ident → Option (List Ident)
  | [] => none
  | i :: stk => if id = i then some [id] else (above id stk).map (i :: ·)

/-- The immediate callees of `i`, in the order of `~(tap in callees)`. -/
def kids (st : SkaState M R) (i : Ident) : List Ident :=
  (Treap.tap (gitG st.g i).callees).map (·.1.id)

/-- `+dirty`: did the entry of a callee of `m` change since `m` last ran (or
in that run)? -/
def dirty (m : Ident) (st : SkaState M R) : Bool :=
  let ran := (Treap.gut st.ticks m (0, 0)).1
  (Treap.tap (gitG st.g m).callees).any fun ce => decide (ran ≤ (Treap.gut st.ticks ce.1.id (0, 0)).2)

/-- The loop of `+sweep`, with fuel. -/
def sweepLoop (st : SkaState M R) (was : M Ident Unit) :
    Nat → M Ident Unit → List (Ident × List Ident) → List Ident → Option (List Ident)
  | 0, _, _, _ => none
  | _ + 1, _, [], out => some out.reverse
  | n + 1, seen, (i, []) :: rest, out => sweepLoop st was n seen rest (i :: out)
  | n + 1, seen, (i, k :: ks) :: rest, out =>
    if Treap.has seen k = true ∨ Treap.has was k = false then sweepLoop st was n seen ((i, ks) :: rest) out
    else sweepLoop st was n (Treap.ins seen k) ((k, kids st k) :: (i, ks) :: rest) out

/-- `+sweep`: the members `was` of the component of `id` that `id` reaches,
callees before callers. -/
def sweep (n : Nat) (id : Ident) (was : M Ident Unit) (st : SkaState M R) : Option (List Ident) :=
  sweepLoop st was n (Treap.ins Treap.empty id) [(id, kids st id)] []

/-- The loop of `+cull` that finds the members `id` still reaches. -/
def liveLoop (st : SkaState M R) (members : M Ident Unit) :
    Nat → List Ident → M Ident Unit → Option (M Ident Unit)
  | 0, _, _ => none
  | _ + 1, [], live => some live
  | n + 1, i :: q, live =>
    if Treap.has live i = true ∨ Treap.has members i = false then liveLoop st members n q live
    else liveLoop st members n (q ++ kids st i) (Treap.ins live i)

/-- `+cull`: forget the members of the component of `id` that it does not
reach anymore. -/
def cull (n : Nat) (id : Ident) (st : SkaState M R) : Option (SkaState M R) :=
  (above id st.stk).bind fun ab =>
  let members : M Ident Unit := Treap.silt ab
  (liveLoop st members n [id] Treap.empty).map fun live =>
  let dead := Treap.dif members live
  if Treap.tap dead = [] then st else
  let st := { st with stats := { st.stats with culled := st.stats.culled + Treap.wyt dead },
                      stk := st.stk.filter (fun i => !Treap.has dead i),
                      moved := Treap.dif st.moved dead }
  (Treap.rap dead).foldl (fun st i =>
    { st with order := Treap.del st.order i.1, ticks := Treap.del st.ticks i.1,
              g := Treap.del st.g i.1 }) st

/-- The loop of `+pop` over the stack. -/
def popGo (id : Ident) : List Ident → SkaState M R → Option (SkaState M R)
  | [], _ => none
  | top :: rest, st =>
    let st := { st with stk := rest, order := Treap.del st.order top, ticks := Treap.del st.ticks top }
    let d := gitG st.g top
    let d := if d.prod = Sock.void then { d with prod := Sock.dunno } else d
    let st := { st with g := Treap.put st.g top d, done := putMi st.done top d }
    if top = id then some st else popGo id rest st

/-- `+pop`: pop a finished component off the stack, memoizing its members. -/
def pop (id : Ident) (st : SkaState M R) : Option (SkaState M R) := popGo id st.stk st

/-! ## The pass loop, the member loop, `+analyze` -/

/-- The member loop of a pass: `[low changed]` and the state. -/
abbrev MemGo (M : Type → Type → Type) (R : Type) :=
  Nat → Nat → List Ident → SkaState M R → Option ((Nat × Bool) × SkaState M R)

/-- The pass loop over the component of `id`. -/
abbrev PassGo (M : Type → Type → Type) (R : Type) :=
  Ident → Nat → Nat → SkaState M R → Option (Nat × SkaState M R)

/-- One turn of the member loop (`index`, `pass`, the members left). -/
def memberStep (run : RunGo M R) (memberLoop : MemGo M R) (index pass : Nat) :
    List Ident → SkaState M R → Option ((Nat × Bool) × SkaState M R)
  | [], st => some ((index, false), st)
  | m :: ms, st =>
    if dirty m st = false then memberLoop index pass ms st else
    let st := if pass > 1 then { st with stats := { st.stats with lateRuns := st.stats.lateRuns + 1 } } else st
    (Treap.get st.order m).bind fun o =>
    (run m o st).bind fun r =>
    if r.1.1 < index then some ((r.1.1, r.1.2.2), r.2) else
    (memberLoop index pass ms r.2).map fun t => ((min r.1.1 t.1.1, r.1.2.2 || t.1.2), t.2)

/-- One pass over the component of `id` (`index` its DFS number, `pass` the
number of the pass), with the fuel `n` of `+sweep` and `+cull`. -/
def passStep (n : Nat) (memberLoop : MemGo M R) (passLoop : PassGo M R) (id : Ident)
    (index pass : Nat) (st : SkaState M R) : Option (Nat × SkaState M R) :=
  (above id st.stk).bind fun ab =>
  (sweep n id (Treap.silt ab) st).bind fun members =>
  let st := { st with stats := { st.stats with passes := st.stats.passes + 1 } }
  let nextBefore := st.next
  (memberLoop index pass members st).bind fun r =>
  let st := r.2
  if r.1.1 ≠ index then some (r.1.1, st) else
  (cull n id st).bind fun st =>
  if r.1.2 = false ∧ st.next = nextBefore then (pop id st).map fun st' => (st.next, st')
  else passLoop id index (pass + 1) st

/-- The `=.  st  (cull id st)` before the first pass, then the pass loop. -/
def cullPass (n : Nat) (passLoop : PassGo M R) (id : Ident) (index : Nat) (st : SkaState M R) :
    Option (Nat × SkaState M R) :=
  (cull n id st).bind fun st => passLoop id index 1 st

/-- One `+analyze` of `id` with the persistent memo `memoF`: a hit from an
earlier poke, or a new function: number it, push it, run it, and if it is
the root of a component, pop it (trivial) or drop the members it does not
reach (`+cull`) and iterate the component.  `n` is the fuel of that
`+cull`. -/
def analyzeStep (n : Nat) (memoF : Memo M) (run : RunGo M R) (passLoop : PassGo M R) (id : Ident)
    (st : SkaState M R) : Option (Nat × SkaState M R) :=
  match gitMi memoF id.2 id.1 with
  | none => none
  | some (some hit) => some (st.next, { st with g := Treap.put st.g id hit.2, done := putMi st.done id hit.2 })
  | some none =>
  let index := st.next
  let st := { st with next := index + 1, order := Treap.put st.order id index, stk := id :: st.stk,
                      g := Treap.put st.g id FDatum.bunt }
  (run id index st).bind fun r =>
  let st := r.2
  if r.1.1 ≠ index then some (r.1.1, st) else
  if r.1.2.1 = true then cullPass n passLoop id index st else
  (above id st.stk).bind fun ab =>
  if ab.length ≠ 1 then cullPass n passLoop id index st else
  (pop id st).map fun st' => (st.next, st')

/-! ## The recursion, fuelled -/

mutual

/-- `fol-loop`, with fuel.  A direct call starts the `resolve` loop with
its own identity as `orig`. -/
def folLoop (env : Env R) (memoF : Memo M) : Nat → FolGoS M R
  | 0 => fun _ _ _ _ _ _ _ => none
  | n + 1 => folStep env (fun i => resolve env memoF n i i) (folLoop env memoF n)

/-- The `resolve` loop, with fuel, for the identity `orig` it began with. -/
def resolve (env : Env R) (memoF : Memo M) : Nat → Ident → ResGo M R
  | 0 => fun _ _ _ => none
  | n + 1 => fun orig => resolveStep env (resolve env memoF n orig) (analyze env memoF n) orig

/-- `+analyze`, with fuel. -/
def analyze (env : Env R) (memoF : Memo M) : Nat → AnaGo M R
  | 0 => fun _ _ => none
  | n + 1 => analyzeStep n memoF (run env memoF n) (passLoop env memoF n)

/-- `+run`, with fuel. -/
def run (env : Env R) (memoF : Memo M) : Nat → RunGo M R
  | 0 => fun _ _ _ => none
  | n + 1 => runStep (folLoop env memoF n)

/-- The pass loop of `+analyze`, with fuel. -/
def passLoop (env : Env R) (memoF : Memo M) : Nat → PassGo M R
  | 0 => fun _ _ _ _ => none
  | n + 1 => passStep n (memberLoop env memoF n) (passLoop env memoF n)

/-- The member loop of a pass, with fuel. -/
def memberLoop (env : Env R) (memoF : Memo M) : Nat → MemGo M R
  | 0 => fun _ _ _ _ => none
  | n + 1 => memberStep (run env memoF n) (memberLoop env memoF n)

end

/-- The `resolve` of a direct call: the loop begun with the call's own
identity. -/
def resolveR (env : Env R) (memoF : Memo M) (n : Nat) : ResGo M R := fun i => resolve env memoF n i i

/-! ## `+ska-callgraph`, `+prune-callgraph`, `+ska-poke` -/

/-- `+ska-callgraph` on the root `root`, with the persistent memo `memoF`
and the registrations `reg`: the graph and the registrations. -/
def skaCallgraph (env : Env R) (n : Nat) (root : Ident) (memoF : Memo M) (reg : R) :
    Option (Callgraph M × R) :=
  (analyze env memoF n root (SkaState.init reg)).map fun r => (r.2.g, r.2.regs)

/-- The loop of `+prune-callgraph`, with fuel. -/
def pruneLoop (g : Callgraph M) : Nat → List Ident → Callgraph M → Option (Callgraph M)
  | 0, _, _ => none
  | _ + 1, [], out => some out
  | n + 1, i :: q, out =>
    if Treap.has out i = true then pruneLoop g n q out else
    (Treap.get g i).bind fun d =>
    pruneLoop g n (q ++ (Treap.tap d.callees).map (·.1.id)) (Treap.put out i d)

/-- `+prune-callgraph`: the functions the root reaches. -/
def pruneCallgraph (n : Nat) (g : Callgraph M) (root : Ident) : Option (Callgraph M) :=
  pruneLoop g n [root] Treap.empty

/-- The `~(rep by pruned)` of `+ska-poke`: the datums by code bell, and the
persistent memo with the finished functions. -/
def pokeMemo (pruned : Callgraph M) (memo : Memo M) : M Bell (FDatum M) × Memo M :=
  (Treap.rap pruned).foldl (fun acc e =>
    (Treap.put acc.1 ⟨e.2.less, e.1.2⟩ e.2,
     let me := memoFinalEntry e.1 e.2
     putMi acc.2 me.1 me.2)) (Treap.empty, memo)

/-- The analysis part of `+ska-poke` on the identity `root` with the
persistent memo `memo` and the registrations `reg`: the pruned graph, the
datums by code bell (`dats`), the new persistent memo, the root's datum and
the registrations.  The rest of `+ska-poke` (baking, the code table, the
`+ska-cole-*` arms) works on these. -/
def skaPoke (env : Env R) (n : Nat) (root : Ident) (memo : Memo M) (reg : R) :
    Option (Callgraph M × M Bell (FDatum M) × Memo M × FDatum M × R) :=
  (skaCallgraph env n root memo reg).bind fun gr =>
  (pruneCallgraph n gr.1 root).bind fun pruned =>
  (Treap.get pruned root).map fun rd =>
  let dm := pokeMemo pruned memo
  (pruned, dm.1, dm.2, rd, gr.2)

end Ana
end SkaModel
end Formalization
