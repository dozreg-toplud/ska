import lemmas.Run

/-!
# The types of SKA's IR, as Lean types with their noun layouts

Each type here is a Hoon type of `desk/lib/nock-compilation.hoon` (or of
`desk/sys/hoon.hoon`), and each comes with `toNoun`, the noun that Hoon lays
the value out as.  The Lean models of the arms work on these types; a proof
that an arm's Nock computes its model is about the arm on `toNoun` of the
arguments.

Tags are cords: the letters as bytes, the first letter lowest.  A Hoon flag
`?` is `0` for `&` (yes) and `1` for `|` (no); a list is `~` or `[i t]`; a
unit is `~` or `[~ u]`.

Maps are a parameter, `HoonMap`: the interpreter only looks values up, puts
them and deletes them, and the noun of a map is the treap of `+by`, which the
instance gives.
-/

namespace Formalization
namespace SkaModel

open Nock

/-! ## Tags -/

namespace Tag
-- pole
def imm : Nat := 0x6d6d69
def mov : Nat := 0x766f6d
def inc : Nat := 0x636e69
def con : Nat := 0x6e6f63
def hed : Nat := 0x646568
def tal : Nat := 0x6c6174
def cel : Nat := 0x6c6563
def lob : Nat := 0x626f6c
def equ : Nat := 0x757165
def hsp : Nat := 0x707368
def hse : Nat := 0x657368
def hdp : Nat := 0x706468
def hde : Nat := 0x656468
def hmp : Nat := 0x706d68
def hme : Nat := 0x656d68
def hcp : Nat := 0x706368
def hce : Nat := 0x656368
def spy : Nat := 0x797073
def nok : Nat := 0x6b6f6e
def cal : Nat := 0x6c6163
def caf : Nat := 0x666163
def cam : Nat := 0x6d6163
def csl : Nat := 0x6c7363
def csf : Nat := 0x667363
def csm : Nat := 0x6d7363
-- termin-out
def clq : Nat := 0x716c63
def eqq : Nat := 0x717165
def brn : Nat := 0x6e7262
def brz : Nat := 0x7a7262
def hop : Nat := 0x706f68
def jmp : Nat := 0x706d6a
def jmf : Nat := 0x666d6a
def jsp : Nat := 0x70736a
def jsf : Nat := 0x66736a
def don : Nat := 0x6e6f64
def bom : Nat := 0x6d6f62
def lti : Nat := 0x69746c
-- need-ordered
def both : Nat := 0x68746f62
def this : Nat := 0x73696874
def none : Nat := 0x656e6f6e
-- prod and ovum
def ir : Nat := 0x7269
def drop : Nat := 0x706f7264
def full : Nat := 0x6c6c7566
def jets : Nat := 0x7374656a
def dire : Nat := 0x65726964
def fast : Nat := 0x74736166
-- sock
def void : Nat := 0x64696f76
-- frames of a trace
def hunk : Nat := 0x6b6e7568
def hand : Nat := 0x646e6168
def lose : Nat := 0x65736f6c
def mean : Nat := 0x6e61656d
def spot : Nat := 0x746f7073
def meaf : Nat := 0x6661656d
def meac : Nat := 0x6361656d
-- tank
def leaf : Nat := 0x6661656c
-- the hint that keeps a formula out of compiled Nock
def bare : Nat := 0x65726162
end Tag

/-! ## Generic layouts -/

/-- A Hoon flag: `&` is `0`, `|` is `1`. -/
def flag (b : Bool) : Noun := if b then A 0 else A 1

/-- A Hoon list. -/
def listNoun {α : Type} (f : α → Noun) : List α → Noun
  | [] => A 0
  | x :: xs => C (f x) (listNoun f xs)

/-- A Hoon unit. -/
def unitNoun {α : Type} (f : α → Noun) : Option α → Noun
  | Option.none => A 0
  | Option.some x => C (A 0) (f x)

/-- `;;((list) n)`: the elements of a noun that is a list, and `none` (a
crash) for one that does not end in `~`. -/
def nounList? : Noun → Option (List Noun)
  | Noun.atom 0 => some []
  | Noun.atom _ => Option.none
  | Noun.cell i t => (nounList? t).map (i :: ·)

theorem nounList?_listNoun (xs : List Noun) : nounList? (listNoun id xs) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [listNoun, nounList?, ih]

/-! ## Maps -/

/-- The operations of `+by` on a `(map @ v)` that the interpreter uses, and
the laws they satisfy on maps that pass `+apt:by`.  An instance is a model of
Hoon's treaps: `toNoun` is the treap, and `get`, `put`, `del` are `+get:by`,
`+put:by` and `+del:by`. -/
class HoonMap (Map : Type → Type) where
  empty : Map ν
  get : Map ν → Nat → Option ν
  put : Map ν → Nat → ν → Map ν
  del : Map ν → Nat → Map ν
  toNoun : (ν → Noun) → Map ν → Noun
  get_empty (k : Nat) : get (empty : Map ν) k = Option.none
  get_put (m : Map ν) (k : Nat) (v : ν) (k' : Nat) :
    get (put m k v) k' = if k' = k then some v else get m k'
  get_del (m : Map ν) (k k' : Nat) :
    get (del m k) k' = if k' = k then Option.none else get m k'
  toNoun_empty (f : ν → Noun) : toNoun f (empty : Map ν) = A 0

/-! ## Capes, socks, bells

    +$  cape  $~(| $@(? [cape cape]))
    +$  sock  $~(|+~ $@(%void [=cape data=*]))
    +$  bell  [less=sock fol=^]
-/

/-- `cape`: `yes` is `&` (known), `no` is `|` (not known). -/
inductive Cape where
  | yes : Cape
  | no : Cape
  | cell : Cape → Cape → Cape
  deriving DecidableEq, Repr

def Cape.toNoun : Cape → Noun
  | yes => A 0
  | no => A 1
  | cell h t => C h.toNoun t.toNoun

/-- `+validate-cape`, which `+validate-bell` runs on a bell of a `%dire`
ovum: `none` is its crash. -/
def Cape.ofNoun? : Noun → Option Cape
  | Noun.atom 0 => some yes
  | Noun.atom 1 => some no
  | Noun.atom _ => Option.none
  | Noun.cell h t => do
      let h' ← Cape.ofNoun? h
      let t' ← Cape.ofNoun? t
      pure (cell h' t')

theorem Cape.ofNoun?_toNoun (c : Cape) : Cape.ofNoun? c.toNoun = some c := by
  induction c with
  | yes => rfl
  | no => rfl
  | cell h t ih ih' => simp [Cape.toNoun, Cape.ofNoun?, ih, ih']

/-- `sock`: `void` is the empty set of nouns. -/
inductive Sock where
  | void : Sock
  | mk : Cape → Noun → Sock
  deriving DecidableEq, Repr

def Sock.toNoun : Sock → Noun
  | void => A Tag.void
  | mk c d => C c.toNoun d

/-- `bell`: a function, as the subject it is compiled for and its formula.
The type says `fol=^`: a formula that is a cell. -/
structure Bell where
  less : Sock
  fol : Noun
  deriving DecidableEq, Repr

def Bell.toNoun (b : Bell) : Noun := C b.less.toNoun b.fol

/-- `+validate-bell`: a bell from a noun, as `+poke` checks the bell of a
`%dire` ovum.  `none` is its crash. -/
def Bell.ofNoun? : Noun → Option Bell
  | Noun.cell (Noun.cell c d) (Noun.cell f g) => do
      let c' ← Cape.ofNoun? c
      pure ⟨Sock.mk c' d, C f g⟩
  | _ => Option.none

theorem Bell.ofNoun?_toNoun (c : Cape) (d f g : Noun) :
    Bell.ofNoun? (Bell.toNoun ⟨Sock.mk c d, C f g⟩) = some ⟨Sock.mk c d, C f g⟩ := by
  simp [Bell.toNoun, Sock.toNoun, Bell.ofNoun?, Cape.ofNoun?_toNoun]

/-- `ring`: `[=path axe=@]`, a path of knots and an axis. -/
structure Ring where
  path : List Nat
  axe : Nat
  deriving DecidableEq, Repr

def Ring.toNoun (r : Ring) : Noun := C (listNoun A r.path) (A r.axe)

/-! ## Needs

    +$  need-ordered
      $~  [%none ~]
      $^  [p=need-ordered q=need-ordered]
      $%  [%both h=need-ordered t=need-ordered]
          [%this ~]
          [%none ~]
      ==
-/

inductive NeedOrd where
  | pair : NeedOrd → NeedOrd → NeedOrd
  | both : NeedOrd → NeedOrd → NeedOrd
  | this : NeedOrd
  | none : NeedOrd
  deriving DecidableEq, Repr

def NeedOrd.toNoun : NeedOrd → Noun
  | pair p q => C p.toNoun q.toNoun
  | both h t => C (A Tag.both) (C h.toNoun t.toNoun)
  | this => C (A Tag.this) (A 0)
  | none => C (A Tag.none) (A 0)

/-! ## The IR

    +$  jmp  [args=(list (unit @uvre)) there=@uwoo]
    +$  pole  $%  [%imm n=* d=@uvre] ... ==
    +$  termin-out  $%  termin  [%lti n=@ s=@uvre z=jmp o=jmp]  ==
    +$  blob-out  [par=(list @uvre) body=(list pole) fin=termin-out]
    +$  straight-out  [need=need-ordered n-args=@ud blocks=(map @uwoo blob-out)]

Registers (`@uvre`) and block labels (`@uwoo`) are atoms.  The hint names of
`%hsp`, `%hse`, `%hdp`, `%hde` are atoms of the types `hint-static` and
`hint-dynamic`.
-/

structure Jmp where
  args : List (Option Nat)
  there : Nat
  deriving DecidableEq, Repr

def Jmp.toNoun (j : Jmp) : Noun := C (listNoun (unitNoun A) j.args) (A j.there)

inductive Pole where
  | imm (n : Noun) (d : Nat)
  | mov (s d : Nat)
  | inc (s d : Nat)
  | con (h t d : Nat)
  | hed (s d : Nat)
  | tal (s d : Nat)
  | cel (p : Nat)
  | lob (p : Nat)
  | equ (l r : Nat)
  | hsp (n : Nat) (f : Noun)
  | hse (n : Nat) (f : Noun)
  | hdp (n : Nat) (p : Nat) (f : Noun)
  | hde (n : Nat) (p : Nat) (f : Noun)
  | hmp (a : Bell) (v : List Nat) (f : Noun)
  | hme (a : Bell) (v : List Nat) (f : Noun)
  | hcp (n : Noun) (f : Noun)
  | hce (n : Noun) (f : Noun)
  | spy (e p d : Nat)
  | nok (u f d : Nat)
  | cal (a : Bell) (v : List Nat) (d : Nat)
  | caf (a : Bell) (v : List Nat) (d : Nat) (n : Ring)
  | cam (a : Bell) (v : List Nat) (d : Nat) (k : Noun)
  | csl (a : Bell) (s d : Nat)
  | csf (a : Bell) (s d : Nat) (n : Ring)
  | csm (a : Bell) (s d : Nat) (k : Noun)
  deriving DecidableEq, Repr

def Pole.toNoun : Pole → Noun
  | imm n d => C (A Tag.imm) (C n (A d))
  | mov s d => C (A Tag.mov) (C (A s) (A d))
  | inc s d => C (A Tag.inc) (C (A s) (A d))
  | con h t d => C (A Tag.con) (C (A h) (C (A t) (A d)))
  | hed s d => C (A Tag.hed) (C (A s) (A d))
  | tal s d => C (A Tag.tal) (C (A s) (A d))
  | cel p => C (A Tag.cel) (A p)
  | lob p => C (A Tag.lob) (A p)
  | equ l r => C (A Tag.equ) (C (A l) (A r))
  | hsp n f => C (A Tag.hsp) (C (A n) f)
  | hse n f => C (A Tag.hse) (C (A n) f)
  | hdp n p f => C (A Tag.hdp) (C (A n) (C (A p) f))
  | hde n p f => C (A Tag.hde) (C (A n) (C (A p) f))
  | hmp a v f => C (A Tag.hmp) (C a.toNoun (C (listNoun A v) f))
  | hme a v f => C (A Tag.hme) (C a.toNoun (C (listNoun A v) f))
  | hcp n f => C (A Tag.hcp) (C n f)
  | hce n f => C (A Tag.hce) (C n f)
  | spy e p d => C (A Tag.spy) (C (A e) (C (A p) (A d)))
  | nok u f d => C (A Tag.nok) (C (A u) (C (A f) (A d)))
  | cal a v d => C (A Tag.cal) (C a.toNoun (C (listNoun A v) (A d)))
  | caf a v d n => C (A Tag.caf) (C a.toNoun (C (listNoun A v) (C (A d) n.toNoun)))
  | cam a v d k => C (A Tag.cam) (C a.toNoun (C (listNoun A v) (C (A d) k)))
  | csl a s d => C (A Tag.csl) (C a.toNoun (C (A s) (A d)))
  | csf a s d n => C (A Tag.csf) (C a.toNoun (C (A s) (C (A d) n.toNoun)))
  | csm a s d k => C (A Tag.csm) (C a.toNoun (C (A s) (C (A d) k)))

/-- `termin-out`: `termin` and `%lti`. -/
inductive Termin where
  | clq (s : Nat) (z o : Jmp)
  | eqq (l r : Nat) (z o : Jmp)
  | brn (s : Nat) (z o : Jmp)
  | brz (s : Nat) (z o : Jmp)
  | hop (t : Jmp)
  | jmp (a : Bell) (v : List Nat)
  | jmf (a : Bell) (v : List Nat) (n : Ring)
  | jsp (a : Bell) (s : Nat)
  | jsf (a : Bell) (s : Nat) (n : Ring)
  | don (s : Nat)
  | bom (o : Option Nat)
  | lti (n : Nat) (s : Nat) (z o : Jmp)
  deriving DecidableEq, Repr

def Termin.toNoun : Termin → Noun
  | clq s z o => C (A Tag.clq) (C (A s) (C z.toNoun o.toNoun))
  | eqq l r z o => C (A Tag.eqq) (C (A l) (C (A r) (C z.toNoun o.toNoun)))
  | brn s z o => C (A Tag.brn) (C (A s) (C z.toNoun o.toNoun))
  | brz s z o => C (A Tag.brz) (C (A s) (C z.toNoun o.toNoun))
  | hop t => C (A Tag.hop) t.toNoun
  | jmp a v => C (A Tag.jmp) (C a.toNoun (listNoun A v))
  | jmf a v n => C (A Tag.jmf) (C a.toNoun (C (listNoun A v) n.toNoun))
  | jsp a s => C (A Tag.jsp) (C a.toNoun (A s))
  | jsf a s n => C (A Tag.jsf) (C a.toNoun (C (A s) n.toNoun))
  | don s => C (A Tag.don) (A s)
  | bom o => C (A Tag.bom) (unitNoun A o)
  | lti n s z o => C (A Tag.lti) (C (A n) (C (A s) (C z.toNoun o.toNoun)))

/-- `blob-out`: a basic block. -/
structure Blob where
  par : List Nat
  body : List Pole
  fin : Termin
  deriving DecidableEq, Repr

def Blob.toNoun (b : Blob) : Noun :=
  C (listNoun A b.par) (C (listNoun Pole.toNoun b.body) b.fin.toNoun)

/-- `straight-out`: a compiled function. -/
structure Straight (Map : Type → Type) where
  need : NeedOrd
  nargs : Nat
  blocks : Map Blob

def Straight.toNoun {Map : Type → Type} [HoonMap Map] (s : Straight Map) : Noun :=
  C s.need.toNoun (C (A s.nargs) (HoonMap.toNoun Blob.toNoun s.blocks))

/-! ## The core's interface

    +$  ovum
      $%  [%full sub=* fol=^]
          [%jets p=(list (pair ring jets-comp-info))]
          [%dire b=bell mono=?]
          [%fast reset=? p=(list [pax=path =sock])]
      ==
    +$  prod
      $@  ~
      $%  [%ir b=bell p=straight-out new=(list [pax=path tem=sock clue=*])]
          [%drop p=(list bell)]
      ==

The payloads that the interpreter never makes or reads are left as nouns.
-/

inductive Ovum where
  | full (sub fol : Noun)
  | jets (p : Noun)
  | dire (b : Bell) (mono : Bool)
  | fast (reset : Bool) (p : Noun)

def Ovum.toNoun : Ovum → Noun
  | full s f => C (A Tag.full) (C s f)
  | jets p => C (A Tag.jets) p
  | dire b m => C (A Tag.dire) (C b.toNoun (flag m))
  | fast r p => C (A Tag.fast) (C (flag r) p)

inductive Prod (Map : Type → Type) where
  | nil : Prod Map
  | ir (b : Bell) (p : Straight Map) (new : Noun) : Prod Map
  | drop (p : List Bell) : Prod Map

def Prod.toNoun {Map : Type → Type} [HoonMap Map] : Prod Map → Noun
  | nil => A 0
  | ir b p new => C (A Tag.ir) (C b.toNoun (C p.toNoun new))
  | drop p => C (A Tag.drop) (listNoun Bell.toNoun p)

/-! ## Results of virtual Nock (`hoon.hoon`)

    +$  tone  $%  [%0 product=*]  [%1 block=*]  [%2 trace=(list [@ta *])]  ==
    +$  toon  $%  [%0 p=*]  [%1 p=*]  [%2 p=(list tank)]  ==
-/

/-- A frame of a trace: its tag and its datum. -/
abbrev Frame := Nat × Noun

abbrev Trace := List Frame

def Frame.toNoun (fr : Frame) : Noun := C (A fr.1) fr.2

inductive Tone where
  | zero (product : Noun)
  | one (block : Noun)
  | two (trace : Trace)
  deriving DecidableEq, Repr

def Tone.toNoun : Tone → Noun
  | zero p => C (A 0) p
  | one b => C (A 1) b
  | two t => C (A 2) (listNoun Frame.toNoun t)

/-- `toon`; the tanks are nouns. -/
inductive Toon where
  | zero (p : Noun)
  | one (p : Noun)
  | two (p : List Noun)
  deriving DecidableEq, Repr

def Toon.toNoun : Toon → Noun
  | zero p => C (A 0) p
  | one p => C (A 1) p
  | two p => C (A 2) (listNoun id p)

/-- The frames that `+mink` pushes for a dynamic hint, and that `%hdp` and
`%hde` push and pop: `?(%hunk %hand %lose %mean %spot)`. -/
def stopTag (n : Nat) : Bool :=
  n = Tag.hunk || n = Tag.hand || n = Tag.lose || n = Tag.mean || n = Tag.spot

/-- The product of a scry gate, `(unit (unit))`, as `+mink` and `%spy` take
it apart: `~` is a block, `[~ ~]` a failure, `[~ ~ v]` a value.  The heads
of the cells are not looked at; any other noun is a crash (`none`). -/
inductive ScryRes where
  | block : ScryRes
  | hunk : ScryRes
  | val (v : Noun) : ScryRes

def scryDecode : Noun → Option ScryRes
  | Noun.atom 0 => some ScryRes.block
  | Noun.cell _ (Noun.atom 0) => some ScryRes.hunk
  | Noun.cell _ (Noun.cell _ v) => some (ScryRes.val v)
  | _ => Option.none

end SkaModel
end Formalization
