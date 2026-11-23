import lemmas.Ska.Interp

/-!
# The contract between the compiler and the interpreter

What the code that the compiler returns must do, for the interpreter to agree
with `+mink`.  It is stated about the code alone: a function's code is run by
`execEntry` against an arbitrary `Oracle` that answers its calls, and the
contract says that the run agrees with `+mink` on the function's formula
whenever the oracle agrees with `+mink` on the calls.  The interpreter's own
oracle is one such oracle (`Theorems.lean`), so the contract for every piece
of code the compiler returns is all that the interpreter needs.

## The pieces

* `Fits sock n`: the noun `n` is one of the nouns the sock describes.  A bell
  `[less fol]` is compiled for the subjects that fit `less`.
* `split need n`: the arguments of a function whose subject shape is `need`,
  on the subject `n`.  The registers of a `need-ordered` are its leaves in
  preorder, the whole of a `%both` before its parts (`+flatten-need`,
  `+need-ord-alloc-regs`).
* `Needs`: what the compiler says the subject shape of each bell is, as a
  partial map.  A call `%cal a v` passes the values of `v` as the split of the
  callee's subject by the callee's need, which the caller was compiled with.
* `FrameRel N fi fm`: the frame `fi` of an interpreter trace stands for the
  frame `fm` of a `+mink` trace.  Frames that both push are equal; the
  interpreter's `[%meaf a vals]` stands for `[%mean trap]` when `vals` is the
  split of `trap` and `trap` fits `a`; `[%meac n]` stands for `[%mean trap]`
  when the trap computes `n`.  `ToneRel` lifts it to tones.
* `OracleFwd`, `OracleBwd`, `OracleSteps`: an oracle answers calls as
  `+mink` runs them, in the two directions, and its answers keep an invariant.
* `ContractFwd`, `ContractBwd`: the contract of a piece of code on a subject.
* `Sound`: every answer of the compiler satisfies the contract.
-/

namespace Formalization
namespace SkaModel

open Nock

/-! ## Socks -/

/-- A cape that knows nothing: `|`, or cells of such. -/
def Cape.isNo : Cape → Bool
  | Cape.yes => false
  | Cape.no => true
  | Cape.cell h t => h.isNo && t.isNo

/-- The noun `n` agrees with the data `d` wherever the cape knows.  A cell
of capes that knows nothing is `|` (the normalization `[| |] -> |`); one that
knows something says that the noun is a cell. -/
def FitsCape : Cape → Noun → Noun → Prop
  | Cape.yes, d, n => n = d
  | Cape.no, _, _ => True
  | Cape.cell h t, d, n =>
      (h.isNo && t.isNo) = true ∨
      ∃ dh dt nh nt, d = C dh dt ∧ n = C nh nt ∧ FitsCape h dh nh ∧ FitsCape t dt nt

/-- The noun `n` is one of the nouns of the sock.  `%void` has none. -/
def Fits : Sock → Noun → Prop
  | Sock.void, _ => False
  | Sock.mk c d, n => FitsCape c d n

/-! ## Arguments -/

/-- The arguments of a function with the subject shape `need`, on the subject
`n`: the leaves of the need in preorder.  A pair or a `%both` needs a cell. -/
def split : NeedOrd → Noun → Option (List Noun)
  | NeedOrd.none, _ => some []
  | NeedOrd.this, n => some [n]
  | NeedOrd.pair p q, Noun.cell h t =>
      (split p h).bind fun a => (split q t).bind fun b => some (a ++ b)
  | NeedOrd.both p q, Noun.cell h t =>
      (split p h).bind fun a => (split q t).bind fun b => some (C h t :: (a ++ b))
  | NeedOrd.pair _ _, Noun.atom _ => none
  | NeedOrd.both _ _, Noun.atom _ => none

/-- The subject shape of each bell, as the compiler answers `%dire` with it
(for `mono`, whether there is an answer at all). -/
abbrev Needs := Bell → Bool → Option NeedOrd

/-- `N'` answers whatever `N` answers, the same way. -/
def Needs.le (N N' : Needs) : Prop := ∀ b m x, N b m = some x → N' b m = some x

instance : LE Needs := ⟨Needs.le⟩

theorem Needs.le_refl (N : Needs) : N ≤ N := fun _ _ _ h => h

theorem Needs.le_trans {N N' N'' : Needs} (h : N ≤ N') (h' : N' ≤ N'') : N ≤ N'' :=
  fun b m x hx => h' b m x (h b m x hx)

/-- The argument values of a call of `b` on the subject `s`: the subject
itself for a call by subject (`mono`), else its split by the callee's need.
`none` if the compiler has no answer for the callee. -/
def argsFor (N : Needs) (b : Bell) (mono : Bool) (s : Noun) : Option (List Noun) :=
  (N b mono).bind fun nd => if mono then some [s] else split nd s

/-! ## Lists in step -/

inductive Forall2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : Forall2 R [] []
  | cons {a b as bs} : R a b → Forall2 R as bs → Forall2 R (a :: as) (b :: bs)

namespace Forall2

theorem imp {α β : Type} {R R' : α → β → Prop} (h : ∀ a b, R a b → R' a b) :
    ∀ {as bs}, Forall2 R as bs → Forall2 R' as bs
  | _, _, nil => nil
  | _, _, cons hab rest => cons (h _ _ hab) (imp h rest)

theorem length_eq {α β : Type} {R : α → β → Prop} :
    ∀ {as bs}, Forall2 R as bs → as.length = bs.length
  | _, _, nil => rfl
  | _, _, cons _ rest => by simp [length_eq rest]

theorem append {α β : Type} {R : α → β → Prop} :
    ∀ {as bs cs ds}, Forall2 R as bs → Forall2 R cs ds → Forall2 R (as ++ cs) (bs ++ ds)
  | _, _, _, _, nil, h => h
  | _, _, _, _, cons hab rest, h => cons hab (append rest h)

theorem take {α β : Type} {R : α → β → Prop} :
    ∀ (n : Nat) {as bs}, Forall2 R as bs → Forall2 R (as.take n) (bs.take n)
  | 0, _, _, _ => by simp; exact nil
  | _ + 1, _, _, nil => nil
  | n + 1, _, _, cons hab rest => cons hab (take n rest)

theorem drop {α β : Type} {R : α → β → Prop} :
    ∀ (n : Nat) {as bs}, Forall2 R as bs → Forall2 R (as.drop n) (bs.drop n)
  | 0, _, _, h => h
  | _ + 1, _, _, nil => nil
  | n + 1, _, _, cons _ rest => drop n rest

theorem reverse {α β : Type} {R : α → β → Prop} :
    ∀ {as bs}, Forall2 R as bs → Forall2 R as.reverse bs.reverse
  | _, _, nil => nil
  | _, _, cons hab rest => by
    simp only [List.reverse_cons]
    exact append (reverse rest) (cons hab nil)

end Forall2

theorem skip_forall2 (lib : Lib) {α β : Type} {R : α → β → Prop} {la : Noun → α} {lb : Noun → β}
    (hl : ∀ m, R (la m) (lb m)) {as : List α} {bs : List β} (h : Forall2 R as bs) :
    Forall2 R (skip lib la as) (skip lib lb bs) := by
  have hlen := h.length_eq
  unfold skip
  rw [hlen]
  split
  · exact Forall2.append (Forall2.take 512 h)
      (Forall2.cons (hl _) (Forall2.drop _ h))
  · exact h

/-! ## Traces -/

/-- `+mack` of a trap: `+mink` on the trap with its head as the formula and
no scry gate returns `[%0 n]`. -/
def MackRel (lib : Lib) (trap n : Noun) : Prop :=
  ∃ h t, trap = C h t ∧ Mink lib (A 0) [] trap h (Tone.zero n)

/-- The frame `fi` of an interpreter trace stands for the frame `fm` of a
`+mink` trace: both render to the same tank. -/
inductive FrameRel (lib : Lib) (N : Needs) : Frame → Frame → Prop where
  /-- A frame of a dynamic hint that `+mink` keeps, pushed by `%hdp` or by a
  failed scry. -/
  | same {tag : Nat} {d : Noun} : stopTag tag = true → FrameRel lib N (tag, d) (tag, d)
  /-- A deferred `%mean`: the arm `a` of the trap, on the split of the trap.
  The bell is one that `+poke` takes (`+validate-bell`). -/
  | meaf {a : Bell} {vals : List Noun} {h t : Noun} {nd : NeedOrd} :
      Bell.ofNoun? a.toNoun = some a → Fits a.less (C h t) → a.fol = h →
      N a false = some nd → split nd (C h t) = some vals →
      FrameRel lib N (Tag.meaf, C a.toNoun (listNoun id vals)) (Tag.mean, C h t)
  /-- A constant `%mean`: the product of the trap. -/
  | meac {n trap : Noun} : MackRel lib trap n → FrameRel lib N (Tag.meac, n) (Tag.mean, trap)

/-- The tone `ti` of the interpreter stands for the tone `tm` of `+mink`. -/
inductive ToneRel (lib : Lib) (N : Needs) : Tone → Tone → Prop where
  | zero (p : Noun) : ToneRel lib N (Tone.zero p) (Tone.zero p)
  | one (p : Noun) : ToneRel lib N (Tone.one p) (Tone.one p)
  | two {ti tm : Trace} : Forall2 (FrameRel lib N) ti tm → ToneRel lib N (Tone.two ti) (Tone.two tm)

theorem FrameRel.mono {lib : Lib} {N N' : Needs} (hN : N ≤ N') {fi fm : Frame}
    (h : FrameRel lib N fi fm) : FrameRel lib N' fi fm := by
  cases h with
  | same ht => exact FrameRel.same ht
  | meaf hv hf hfol hn hs => exact FrameRel.meaf hv hf hfol (hN _ _ _ hn) hs
  | meac hm => exact FrameRel.meac hm

theorem ToneRel.mono {lib : Lib} {N N' : Needs} (hN : N ≤ N') {ti tm : Tone}
    (h : ToneRel lib N ti tm) : ToneRel lib N' ti tm := by
  cases h with
  | zero p => exact ToneRel.zero p
  | one p => exact ToneRel.one p
  | two hl => exact ToneRel.two (hl.imp fun _ _ => FrameRel.mono hN)

theorem ToneRel.zero_right {lib : Lib} {N : Needs} {ti : Tone} {p : Noun}
    (h : ToneRel lib N ti (Tone.zero p)) : ti = Tone.zero p := by
  cases h; rfl

/-! ## Oracles -/

section
variable {σ : Type}

/-- The answers of `O` from states where `Inv` holds lead to states where it
holds, and the needs only grow. -/
structure OracleSteps (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) : Prop where
  call : ∀ st b m vals t gul ton st', Inv st → O.call st b m vals t gul = some (ton, st') →
    Inv st' ∧ ν st ≤ ν st'
  nok : ∀ st u f gul ton st', Inv st → O.nok st u f gul = some (ton, st') →
    Inv st' ∧ ν st ≤ ν st'

/-- `O` answers, as `+mink` does, every call and every indirect call that
`+mink` runs with less than `n` fuel, from states where `Inv` holds.  A call of
`b` stands for a run of `b`'s formula on a subject that fits `b` and whose
split the argument values are; the trace passed stands for the trace of
`+mink`. -/
structure OracleFwd (lib : Lib) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) (n : Nat) :
    Prop where
  call : ∀ st b m vals ti tm gul s j r, Inv st → j < n → Fits b.less s →
    argsFor (ν st) b m s = some vals → Forall2 (FrameRel lib (ν st)) ti tm →
    minkF lib gul j tm s b.fol = some r →
    ∃ ton st', O.call st b m vals ti gul = some (ton, st') ∧ ToneRel lib (ν st') ton r
  nok : ∀ st u f gul j r, Inv st → j < n → minkF lib gul j [] u f = some r →
    ∃ ton st', O.nok st u f gul = some (ton, st') ∧ ToneRel lib (ν st') ton r

/-- What `O` answers, `+mink` returns, from states where `Inv` holds. -/
structure OracleBwd (lib : Lib) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) : Prop where
  call : ∀ st b m vals ti gul ton st', Inv st → O.call st b m vals ti gul = some (ton, st') →
    ∀ s tm, Fits b.less s → argsFor (ν st) b m s = some vals →
      Forall2 (FrameRel lib (ν st)) ti tm →
      ∃ r, Mink lib gul tm s b.fol r ∧ ToneRel lib (ν st') ton r
  nok : ∀ st u f gul ton st', Inv st → O.nok st u f gul = some (ton, st') →
    ∃ r, Mink lib gul [] u f r ∧ ToneRel lib (ν st') ton r

end

/-! ## The contract -/

section
variable {Map : Type → Type} [HoonMap Map]

/-- The forward half of the contract of the code `c` on the subject `s` and
the formula `f`, entered with the argument values `args`.  `N` is what the
code was compiled against: the needs of its callees.

For every oracle that answers the calls below `n` as `+mink` does, and from
every state where its invariant holds and the needs include `N`: if `+mink`
returns `r` on `[s f]` with `n` fuel from the trace `tm`, then the code,
entered with a trace `ti` that stands for `tm`, returns a tone that stands
for `r`. -/
def ContractFwd (lib : Lib) (N : Needs) (s f : Noun) (args : List Noun) (c : Straight Map) :
    Prop :=
  ∀ (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) (n : Nat) (gul : Noun)
    (ti tm : Trace) (r : Tone),
    (∀ st, Inv st → N ≤ ν st) → OracleSteps Inv ν O → OracleFwd lib Inv ν O n →
    minkF lib gul n tm s f = some r →
    ∀ st, Inv st → Forall2 (FrameRel lib (ν st)) ti tm →
    ∃ ton st', execEntry lib O st c args ti gul = some (ton, st') ∧ ToneRel lib (ν st') ton r

/-- The backward half: for every oracle whose answers `+mink` returns, what
the code returns, `+mink` returns. -/
def ContractBwd (lib : Lib) (N : Needs) (s f : Noun) (args : List Noun) (c : Straight Map) :
    Prop :=
  ∀ (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) (gul : Noun) (ti tm : Trace),
    (∀ st, Inv st → N ≤ ν st) → OracleSteps Inv ν O → OracleBwd lib Inv ν O →
    ∀ st ton st', Inv st → Forall2 (FrameRel lib (ν st)) ti tm →
    execEntry lib O st c args ti gul = some (ton, st') →
    ∃ r, Mink lib gul tm s f r ∧ ToneRel lib (ν st') ton r

/-- The contract of the code `c` that the compiler returns for the bell `b`:
both halves, on every subject that fits the bell, with the subject whole as
the argument of a function by subject, else split by the code's need. -/
def BellContract (lib : Lib) (N : Needs) (b : Bell) (mono : Bool) (c : Straight Map) : Prop :=
  ∀ s, Fits b.less s → ∀ args, (if mono then some [s] else split c.need s) = some args →
    ContractFwd lib N s b.fol args c ∧ ContractBwd lib N s b.fol args c

variable {σ : Type}

/-- The needs that the compiler in the state `st` answers `%dire` with. -/
def needOf (poke : σ → Ovum → Option (Prod Map × σ)) (st : σ) : Needs := fun b m =>
  match poke st (Ovum.dire b m) with
  | some (Prod.ir _ c _, _) => some c.need
  | _ => none

omit [HoonMap Map] in
theorem needOf_some {poke : σ → Ovum → Option (Prod Map × σ)} {st : σ} {b : Bell} {m : Bool}
    {nd : NeedOrd} (h : needOf poke st b m = some nd) :
    ∃ b' c new st', poke st (Ovum.dire b m) = some (Prod.ir b' c new, st') ∧ c.need = nd := by
  unfold needOf at h
  split at h
  · rename_i b' c new st' heq
    exact ⟨b', c, new, st', heq, Option.some.inj h⟩
  · simp at h

omit [HoonMap Map] in
theorem needOf_of_poke {poke : σ → Ovum → Option (Prod Map × σ)} {st st' : σ} {b b' : Bell}
    {m : Bool} {c : Straight Map} {new : Noun}
    (h : poke st (Ovum.dire b m) = some (Prod.ir b' c new, st')) :
    needOf poke st b m = some c.need := by
  simp [needOf, h]

/-- The compiler keeps the invariant `InvC`: a poke from a state where it
holds leads to one where it holds, and the needs it answers with only grow
(what is compiled holds). -/
structure PokeSteps (poke : σ → Ovum → Option (Prod Map × σ)) (InvC : σ → Prop) : Prop where
  dire : ∀ st b m p st', InvC st → poke st (Ovum.dire b m) = some (p, st') →
    InvC st' ∧ needOf poke st ≤ needOf poke st'
  full : ∀ st s f p st', InvC st → poke st (Ovum.full s f) = some (p, st') →
    InvC st' ∧ needOf poke st ≤ needOf poke st'

/-- **The contract.**  From a state where `InvC` holds, the compiler answers
`%dire` with code that satisfies the contract of its bell against the needs
of the state it leaves, and `%full s f` with code of one argument, the whole
subject, that satisfies the contract on `s` and `f`. -/
structure Sound (lib : Lib) (poke : σ → Ovum → Option (Prod Map × σ)) (InvC : σ → Prop) :
    Prop extends PokeSteps poke InvC where
  dire_code : ∀ st b m p st', InvC st → poke st (Ovum.dire b m) = some (p, st') →
    ∃ b' c new, p = Prod.ir b' c new ∧ BellContract lib (needOf poke st') b m c
  full_code : ∀ st s f p st', InvC st → poke st (Ovum.full s f) = some (p, st') →
    ∃ b c new, p = Prod.ir b c new ∧ c.nargs = 1 ∧ c.need = NeedOrd.this ∧
      ContractFwd lib (needOf poke st') s f [s] c ∧ ContractBwd lib (needOf poke st') s f [s] c

/-- `%full` returns on every subject and every formula that is a cell, from
states where `InvC` holds: the model's `Halts`. -/
def FullAnswers (poke : σ → Ovum → Option (Prod Map × σ)) (InvC : σ → Prop) : Prop :=
  ∀ st s f₁ f₂, InvC st → ∃ r, poke st (Ovum.full s (C f₁ f₂)) = some r

end

end SkaModel
end Formalization
