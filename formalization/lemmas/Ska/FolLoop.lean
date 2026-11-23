import lemmas.Ska.Pi
import lemmas.Ska.NommSem

/-!
# `fol-loop`, for one function, with its callees answered by a table

A Lean model of the trap `fol-loop` inside `+run:ska-callgraph` of
`nock-compilation.hoon` (the analysis of one formula, about lines 2375 to
2725), as it is after the commits that made operands any noun, analysed an
atom operand as `[%0 0]` in its place, and inlined a call only under
`+safe-fol-fol`.

What is modelled, and what is not:

* `fol-loop` turns a formula into `[nomm prod saf]` and threads `gen`.  The
  model returns the same triple (`FolOut`) and threads the parts of `gen`
  that feed it or the entry of the function: `want`, `indi`, `seek` (`Gen`).
  The parts left out (`callees`, `area`, `low`, `back`, `st`, and `seat`) only
  record the call graph, the location of the code, and Tarjan's numbering;
  nothing of the nomm, the product or the three capes depends on them.  The
  `%fast` registration (`+register-fast`) only changes `regs.st`, and the
  `%spot` hint only `area` and `seat`; both are left out.
* A direct call looks its callee up in the call graph, the memo, or by a
  recursive analysis (`resolve`, with `+recursive-call`, `+patch-prod` and
  `+analyze`).  Here a table `Tab` answers it instead: for the subject sock of
  the call and the callee's formula, the parts of the callee's `datum` that
  `fol-loop` reads (`TabEntry`), or `none` where the Hoon would crash or not
  return.  `FolLoopSound.lean` states what the proofs assume of the table.
* `fol-loop` recurses on formulas that are not subformulas (the inlined
  callee, and the rewrites of `%8`, `%9`, `%bare`, `%memo`), so the model is
  fuelled, as `minkF` is: `folLoopF tab n` with `n` levels, and `none` when
  that is not enough.  A theorem about a result that the model returns holds
  of the Hoon whenever the Hoon returns.

The cases of the `?+` are `shape`, in the Hoon's order; `folStep` is one level
of `fol-loop` on them.  `inlineable`, `safeNomm` and `safeFolFol` are the arms
`+inlineable`, `+safe-nomm` and `+safe-fol-fol`.
-/

namespace Formalization
namespace SkaModel

open Nock

/-! ## The arms that guard inlining -/

/-- `+$hint-safe`: `?(%hunk %hand %lose %mean %spot)`, the tags that
`+mink` keeps on its trace. -/
def hintSafe (tag : Nat) : Bool := stopTag tag

/-- `?(hint-safe %memo)`. -/
def hintSafeMemo (tag : Nat) : Bool := hintSafe tag || tag == Tag.memo

/-- `+inlineable`: a formula without a Nock 2 or 9 anywhere, whose operands are
all cells. -/
def inlineable : Noun → Bool
  | Noun.cell (Noun.cell a b) (Noun.cell c d) => inlineable (C a b) && inlineable (C c d)
  | Noun.cell (Noun.atom 0) (Noun.atom _) => true
  | Noun.cell (Noun.atom 1) _ => true
  | Noun.cell (Noun.atom 2) _ => false
  | Noun.cell (Noun.atom 9) _ => false
  | Noun.cell (Noun.atom 3) (Noun.cell a b) => inlineable (C a b)
  | Noun.cell (Noun.atom 4) (Noun.cell a b) => inlineable (C a b)
  | Noun.cell (Noun.atom 5) (Noun.cell (Noun.cell a b) (Noun.cell c d)) =>
      inlineable (C a b) && inlineable (C c d)
  | Noun.cell (Noun.atom 6)
      (Noun.cell (Noun.cell a b) (Noun.cell (Noun.cell c d) (Noun.cell e f))) =>
      inlineable (C a b) && inlineable (C c d) && inlineable (C e f)
  | Noun.cell (Noun.atom 7) (Noun.cell (Noun.cell a b) (Noun.cell c d)) =>
      inlineable (C a b) && inlineable (C c d)
  | Noun.cell (Noun.atom 8) (Noun.cell (Noun.cell a b) (Noun.cell c d)) =>
      inlineable (C a b) && inlineable (C c d)
  | Noun.cell (Noun.atom 10) (Noun.cell (Noun.cell (Noun.atom _) (Noun.cell a b)) (Noun.cell c d)) =>
      inlineable (C a b) && inlineable (C c d)
  | Noun.cell (Noun.atom 11) (Noun.cell (Noun.atom _) (Noun.cell a b)) => inlineable (C a b)
  | Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom _) (Noun.cell c d)) (Noun.cell a b)) =>
      inlineable (C a b) && inlineable (C c d)
  | Noun.cell (Noun.atom 12) (Noun.cell (Noun.cell a b) (Noun.cell c d)) =>
      inlineable (C a b) && inlineable (C c d)
  | _ => false

/-- `+safe-nomm`: a nomm of constants and safe hints, which cannot crash. -/
def safeNomm : Nomm → Bool
  | Nomm.cons p q => safeNomm p && safeNomm q
  | Nomm.n1 _ => true
  | Nomm.n11s tag q _ => hintSafeMemo tag && safeNomm q
  | Nomm.n11d tag h q _ => hintSafeMemo tag && safeNomm h && safeNomm q
  | Nomm.mean p _ q _ _ => safeNomm p && safeNomm q
  | _ => false

/-- `+safe-fol-fol`: may the formula of a formula, with this nomm, be dropped?
As `+safe-nomm`, and a Nock 0 is allowed, since the code it reads is known. -/
def safeFolFol : Nomm → Bool
  | Nomm.n0 _ => true
  | Nomm.cons p q => safeFolFol p && safeFolFol q
  | Nomm.n1 _ => true
  | Nomm.n11s tag q _ => hintSafeMemo tag && safeFolFol q
  | Nomm.n11d tag h q _ => hintSafeMemo tag && safeNomm h && safeFolFol q
  | Nomm.mean p _ q _ _ => safeNomm p && safeFolFol q
  | _ => false

/-! ## The state, the table, the result -/

/-- The parts of `gen` that the model threads: what the function uses of its
subject as code (`want`), as code it could not find (`indi`), and where an
indirect call sought its formula (`seek`). -/
structure Gen where
  want : Cape
  indi : Cape
  seek : Cape

/-- `gen` at the start of `+run`: `[| | | ~ ~ index | st]`, its capes. -/
def Gen.init : Gen := ⟨Cape.no, Cape.no, Cape.no⟩

/-- The parts of the callee's `datum` that a direct call reads:
`less-code`, `indi`, `seek`, `prod` and `map`. -/
structure TabEntry where
  less : Sock
  indi : Cape
  seek : Cape
  prod : Sock
  map : Noun

/-- The table of callees: for the subject sock of a call and the callee's
formula, its entry.  `none` is a crash or a loop of the Hoon's `resolve`. -/
abbrev Tab := Sock → Noun → Option TabEntry

/-- `[=nomm prod=sock-anno saf=?]`. -/
structure FolOut where
  nomm : Nomm
  prod : Anno
  saf : Bool

def FolOut.toNoun (o : FolOut) : Noun := C o.nomm.toNoun (C o.prod.toNoun (flag o.saf))

abbrev FolRes := Option (FolOut × Gen)

/-- The data of a sock that is not `%void`. -/
def Sock.data : Sock → Noun
  | Sock.void => A 0
  | Sock.mk _ d => d

/-! ## The cases of the `?+` -/

/-- The cases of `fol-loop`'s `?+`, in its order, with the parts of each
pattern.  A part that the pattern says is a cell is given as its head and
tail. -/
inductive Shape where
  /-- `[p=^ q=*]` -/
  | cons (a b q : Noun)
  /-- `[%0 p=@]` -/
  | op0 (p : Nat)
  /-- `[%1 p=*]` -/
  | op1 (p : Noun)
  /-- `[%2 p=^ q=*]` -/
  | op2 (a b q : Noun)
  /-- `[%3 p=^]` -/
  | op3 (a b : Noun)
  /-- `[%4 p=^]` -/
  | op4 (a b : Noun)
  /-- `[%5 p=^ q=*]` -/
  | op5 (a b q : Noun)
  /-- `[%6 p=^ q=* r=*]` -/
  | op6 (a b q r : Noun)
  /-- `[%7 p=^ q=*]` -/
  | op7 (a b q : Noun)
  /-- `[%8 p=^ q=*]` -/
  | op8 (a b q : Noun)
  /-- `[%9 p=@ q=^]` -/
  | op9 (p : Nat) (a b : Noun)
  /-- `[%10 [a=@ don=*] rec=^]` -/
  | op10 (ax : Nat) (don r1 r2 : Noun)
  /-- `[%11 p=@ q=^]` -/
  | op11s (p : Nat) (a b : Noun)
  /-- `[%11 [a=@ h=^] f=*]` -/
  | op11d (tag : Nat) (h1 h2 f : Noun)
  /-- `[%12 p=^ q=*]` -/
  | op12 (a b q : Noun)
  /-- the default -/
  | other

def shape : Noun → Shape
  | Noun.cell (Noun.cell a b) q => Shape.cons a b q
  | Noun.cell (Noun.atom 0) (Noun.atom p) => Shape.op0 p
  | Noun.cell (Noun.atom 1) p => Shape.op1 p
  | Noun.cell (Noun.atom 2) (Noun.cell (Noun.cell a b) q) => Shape.op2 a b q
  | Noun.cell (Noun.atom 3) (Noun.cell a b) => Shape.op3 a b
  | Noun.cell (Noun.atom 4) (Noun.cell a b) => Shape.op4 a b
  | Noun.cell (Noun.atom 5) (Noun.cell (Noun.cell a b) q) => Shape.op5 a b q
  | Noun.cell (Noun.atom 6) (Noun.cell (Noun.cell a b) (Noun.cell q r)) => Shape.op6 a b q r
  | Noun.cell (Noun.atom 7) (Noun.cell (Noun.cell a b) q) => Shape.op7 a b q
  | Noun.cell (Noun.atom 8) (Noun.cell (Noun.cell a b) q) => Shape.op8 a b q
  | Noun.cell (Noun.atom 9) (Noun.cell (Noun.atom p) (Noun.cell a b)) => Shape.op9 p a b
  | Noun.cell (Noun.atom 10) (Noun.cell (Noun.cell (Noun.atom ax) don) (Noun.cell r1 r2)) =>
      Shape.op10 ax don r1 r2
  | Noun.cell (Noun.atom 11) (Noun.cell (Noun.atom p) (Noun.cell a b)) => Shape.op11s p a b
  | Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom tag) (Noun.cell h1 h2)) f) =>
      Shape.op11d tag h1 h2 f
  | Noun.cell (Noun.atom 12) (Noun.cell (Noun.cell a b) q) => Shape.op12 a b q
  | _ => Shape.other

/-- The formula of a case. -/
def Shape.fol : Shape → Noun
  | cons a b q => C (C a b) q
  | op0 p => C (A 0) (A p)
  | op1 p => C (A 1) p
  | op2 a b q => C (A 2) (C (C a b) q)
  | op3 a b => C (A 3) (C a b)
  | op4 a b => C (A 4) (C a b)
  | op5 a b q => C (A 5) (C (C a b) q)
  | op6 a b q r => C (A 6) (C (C a b) (C q r))
  | op7 a b q => C (A 7) (C (C a b) q)
  | op8 a b q => C (A 8) (C (C a b) q)
  | op9 p a b => C (A 9) (C (A p) (C a b))
  | op10 ax don r1 r2 => C (A 10) (C (C (A ax) don) (C r1 r2))
  | op11s p a b => C (A 11) (C (A p) (C a b))
  | op11d tag h1 h2 f => C (A 11) (C (C (A tag) (C h1 h2)) f)
  | op12 a b q => C (A 12) (C (C a b) q)
  | other => A 0

/-! ## One level of `fol-loop` -/

/-- The recursion of `fol-loop`: `fol-loop(fol f, sub s, memo-key m,
bare-call b, defer d)` from `gen`. -/
abbrev FolGo := Noun → Anno → Option Noun → Bool → Bool → Gen → FolRes

/-- The product of a cons: a constant if both sides are safe, else the knit. -/
def consProd (l r : FolOut) : Anno × Bool :=
  if l.saf = true ∧ r.saf = true ∧ l.prod.sock ≠ Sock.void ∧ r.prod.sock ≠ Sock.void then
    (⟨Sock.mk Cape.yes (C l.prod.sock.data r.prod.sock.data), A 0⟩, true)
  else
    (⟨So.knit l.prod.sock r.prod.sock, Pi.cons l.prod.src r.prod.src⟩, false)

/-- The `%2` case once both operands are analysed (`s` the subject's, `f`
the formula's). -/
def callStep (tab : Tab) (go : FolGo) (mk : Option Noun) (bc df : Bool) (s f : FolOut)
    (gen : Gen) : FolRes :=
  if s.prod.sock = Sock.void ∨ f.prod.sock = Sock.void then
    some (⟨Nomm.n2 s.nomm f.nomm none, ⟨Sock.void, A 0⟩, false⟩, gen)
  else
  match f.prod.sock, bc with
  | Sock.mk Cape.yes (Noun.cell fa fb), false =>
    if mk = none ∧ df = false ∧ inlineable (C fa fb) = true ∧ safeFolFol f.nomm = true then
      (go (C fa fb) s.prod mk bc df
          { gen with want := Ca.uni gen.want (distribute Cape.yes f.prod.src) }).bind fun i =>
      some (⟨Nomm.n7 s.nomm i.1.nomm, i.1.prod, false⟩, i.2)
    else
      (tab s.prod.sock (C fa fb)).bind fun d =>
      match d.less with
      | Sock.void => none
      | Sock.mk lc _ =>
        some (⟨Nomm.n2 s.nomm f.nomm (some (⟨d.less, C fa fb⟩, mk)),
            ⟨d.prod, Pi.compose d.map s.prod.src⟩, false⟩,
          { want := Ca.uni gen.want (Ca.uni (distribute Cape.yes f.prod.src)
              (distribute lc s.prod.src)),
            indi := Ca.uni gen.indi (distribute d.indi s.prod.src),
            seek := Ca.uni gen.seek (distribute d.seek s.prod.src) })
  | _, _ =>
    some (⟨Nomm.n2 s.nomm f.nomm none, Anno.dunno, false⟩,
      { gen with indi := Ca.uni gen.indi (distribute Cape.yes f.prod.src),
                 seek := Ca.uni gen.seek (distribute Cape.yes f.prod.src) })

/-- The arm of a `%mean` hint whose trap has a known battery: the bell of the
call `[%2 [%0 1] %0 2]` on the trap, and its product if all known. -/
def meanArm (go : FolGo) (tag : Nat) (h : FolOut) (mk : Option Noun) (bc : Bool) (gen : Gen) :
    Option (Option (Bell × Option Noun) × Gen) :=
  if ¬ (tag = Tag.mean ∧ h.saf = false ∧ h.prod.sock ≠ Sock.void) then some (none, gen) else
  (So.pull h.prod.sock 2).bind fun bat =>
  match bat with
  | Sock.mk Cape.yes (Noun.cell _ _) =>
    (go (n3 (A 2) (slot 1) (slot 2)) h.prod mk bc true gen).bind fun cg =>
    match cg.1.nomm with
    | Nomm.n2 _ _ (some (b, _)) =>
      some (some (b, match cg.1.prod.sock with
                     | Sock.mk c d => if Ca.all c = true then some d else none
                     | Sock.void => none), cg.2)
    | _ => none
  | _ => some (none, gen)

/-- One level of `fol-loop`: `go` is the recursion. -/
def folStep (tab : Tab) (go : FolGo) (fol : Noun) (sub : Anno) (mk : Option Noun)
    (bc df : Bool) (gen : Gen) : FolRes :=
  match shape fol with
  | Shape.cons a b q =>
    (go (C a b) sub mk bc df gen).bind fun l =>
    (go q sub mk bc df l.2).bind fun r =>
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
    (go (C a b) sub mk bc df gen).bind fun s =>
    (go q sub mk bc df s.2).bind fun f =>
    callStep tab go mk bc df s.1 f.1 f.2
  | Shape.op3 a b =>
    (go (C a b) sub mk bc df gen).bind fun p =>
    some (⟨Nomm.n3 p.1.nomm, Anno.dunno, false⟩, p.2)
  | Shape.op4 a b =>
    (go (C a b) sub mk bc df gen).bind fun p =>
    some (⟨Nomm.n4 p.1.nomm, Anno.dunno, false⟩, p.2)
  | Shape.op5 a b q =>
    (go (C a b) sub mk bc df gen).bind fun p =>
    (go q sub mk bc df p.2).bind fun q =>
    some (⟨Nomm.n5 p.1.nomm q.1.nomm, Anno.dunno, false⟩, q.2)
  | Shape.op6 a b q r =>
    (go (C a b) sub mk bc df gen).bind fun p =>
    (go q sub mk bc df p.2).bind fun q =>
    (go r sub mk bc df q.2).bind fun r =>
    some (⟨Nomm.n6 p.1.nomm q.1.nomm r.1.nomm, doubleInt q.1.prod r.1.prod, false⟩, r.2)
  | Shape.op7 a b q =>
    (go (C a b) sub mk bc df gen).bind fun p =>
    (go q p.1.prod mk bc df p.2).bind fun q =>
    some (⟨Nomm.n7 p.1.nomm q.1.nomm, q.1.prod, false⟩, q.2)
  | Shape.op8 a b q => go (n3 (A 7) (C (C a b) (slot 1)) q) sub mk bc df gen
  | Shape.op9 p a b => go (n3 (A 7) (C a b) (n3 (A 2) (slot 1) (slot p))) sub mk bc df gen
  | Shape.op10 ax don r1 r2 =>
    if ax = 0 then some (⟨Nomm.n0 0, Anno.dunno, false⟩, gen) else
    (go don sub mk bc df gen).bind fun dn =>
    (go (C r1 r2) sub mk bc df dn.2).bind fun rc =>
    (So.darn rc.1.prod.sock ax dn.1.prod.sock).map fun s =>
      (⟨Nomm.n10 ax dn.1.nomm rc.1.nomm, ⟨s, Pi.edit rc.1.prod.src ax dn.1.prod.src⟩, false⟩, rc.2)
  | Shape.op11s p a b =>
    if p = Tag.bare then go (n3 (A 2) (slot 1) (quote (C (A 11) (C (A p) (C a b))))) sub mk true df gen
    else
    (go (C a b) sub mk bc df gen).bind fun q =>
    some (⟨Nomm.n11s p q.1.nomm (C a b), q.1.prod, false⟩, q.2)
  | Shape.op11d tag h1 h2 f =>
    (go (C h1 h2) sub mk bc df gen).bind fun h =>
    if tag = Tag.memo ∧ h.1.saf = true ∧ h.1.prod.sock ≠ Sock.void then
      go (n3 (A 2) (slot 1) (quote f)) sub (some h.1.prod.sock.data) bc df h.2
    else
    (meanArm go tag h.1 mk bc h.2).bind fun arm =>
    (go f sub mk bc df arm.2).bind fun fr =>
    some (⟨match arm.1 with
           | some (bl, k) => Nomm.mean h.1.nomm bl fr.1.nomm f k
           | none => Nomm.n11d tag h.1.nomm fr.1.nomm f,
         fr.1.prod,
         decide ((tag = Tag.spot ∨ tag = Tag.mean) ∧ h.1.saf = true ∧ fr.1.saf = true)⟩, fr.2)
  | Shape.op12 a b q =>
    (go (C a b) sub mk bc df gen).bind fun p =>
    (go q sub mk bc df p.2).bind fun q =>
    some (⟨Nomm.n12 p.1.nomm q.1.nomm, Anno.dunno, false⟩, q.2)
  | Shape.other => some (⟨Nomm.n0 0, Anno.dunno, false⟩, gen)

/-- `fol-loop` with fuel. -/
def folLoopF (tab : Tab) : Nat → FolGo
  | 0 => fun _ _ _ _ _ _ => none
  | n + 1 => folStep tab (folLoopF tab n)

theorem folLoopF_succ (tab : Tab) (n : Nat) :
    folLoopF tab (n + 1) = folStep tab (folLoopF tab n) := rfl

/-- `fol-loop` as `+run` starts it on the formula of the identity
`[bus fol]`: the subject is `[bus 1]`, no memo key, no `%bare`, no deferral. -/
def folLoopTop (tab : Tab) (n : Nat) (bus : Sock) (fol : Noun) : FolRes :=
  folLoopF tab n fol ⟨bus, A 1⟩ none false false Gen.init

end SkaModel
end Formalization
