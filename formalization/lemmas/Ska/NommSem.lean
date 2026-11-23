import lemmas.Ska.Contract

/-!
# `nomm`: its type, a semantics, and the invariant the analysis must give it

The start of stage 3.  `Nomm` is `+$nomm` of `nock-compilation.hoon`, with
its noun layout.  `nommF` runs a nomm as the compiled code means it: as
`+mink` would run the formula, except that a direct call (`%2` with a bell)
runs the callee's nomm from a code table on the subject, and the formula that
`q` computes is evaluated and dropped.

`Annot code P f n` is the invariant: the nomm `n` is a faithful annotation of
the formula `f` for every subject in `P` (what the analysis knows of the
subject, read as a set of nouns), given the nomms of the callees in `code`.
It follows the cases of `fol-loop` in `+run:ska-callgraph`, and states as side
conditions what the analysis must ensure:

* at a direct call, every subject in `P` gives a product of `p` that fits the
  callee's sock and a formula from `q` that is the callee's formula;
* at an inlined call, the formula-formula `q`, which the nomm drops, returns
  the inlined formula on every subject in `P`, from any scry gate: it neither
  crashes, nor loops, nor blocks (the fixed `+fol-loop` inlines only when
  `+safe-fol-fol` holds of its nomm, which should imply this);
* the default case, a crash, only for formulas on which `+mink` crashes with
  the trace as it is (the fixed `+fol-loop` analyses an atom operand as
  `[%0 0]` in its place, which is this case for the atom).

The table of callees is a separate invariant, `CodeOK`: an inductive `Annot`
cannot hold the callee's annotation, which for a recursive function would hold
the caller's again.

`%bare` is an indirect call of the hinted formula itself, which the fixed
`+eval-top` gives to `+mink`; `%memo` is the memoized call `[2 [0 1] 1 f]`
with the clue dropped.

`NommAgree.lean` proves that `Annot` and `CodeOK` make `nommF` agree with
`minkF`.
-/

namespace Formalization
namespace SkaModel

open Nock

/-- `+$nomm`.  `info` is `info-2`: the callee and a memoization key. -/
inductive Nomm where
  | cons (p q : Nomm)
  | n0 (p : Nat)
  | n1 (p : Noun)
  | n2 (p q : Nomm) (info : Option (Bell × Option Noun))
  | n3 (p : Nomm)
  | n4 (p : Nomm)
  | n5 (p q : Nomm)
  | n6 (p q r : Nomm)
  | n7 (p q : Nomm)
  | n10 (a : Nat) (v q : Nomm)
  | n11s (tag : Nat) (q : Nomm) (body : Noun)
  | n11d (tag : Nat) (h q : Nomm) (body : Noun)
  | n12 (p q : Nomm)
  | mean (p : Nomm) (b : Bell) (q : Nomm) (body : Noun) (k : Option Noun)

def Nomm.toNoun : Nomm → Noun
  | cons p q => C p.toNoun q.toNoun
  | n0 p => C (A 0) (A p)
  | n1 p => C (A 1) p
  | n2 p q info =>
      C (A 2) (C p.toNoun (C q.toNoun (unitNoun (fun i => C i.1.toNoun (unitNoun id i.2)) info)))
  | n3 p => C (A 3) p.toNoun
  | n4 p => C (A 4) p.toNoun
  | n5 p q => C (A 5) (C p.toNoun q.toNoun)
  | n6 p q r => C (A 6) (C p.toNoun (C q.toNoun r.toNoun))
  | n7 p q => C (A 7) (C p.toNoun q.toNoun)
  | n10 a v q => C (A 10) (C (C (A a) v.toNoun) q.toNoun)
  | n11s tag q body => C (A 11) (C (A tag) (C q.toNoun body))
  | n11d tag h q body => C (A 11) (C (C (A tag) h.toNoun) (C q.toNoun body))
  | n12 p q => C (A 12) (C p.toNoun q.toNoun)
  | mean p b q body k =>
      C (A Tag.mean) (C p.toNoun (C b.toNoun (C q.toNoun (C body (unitNoun id k)))))

/-- One level of the semantics of a nomm: `go` runs a sub-nomm, `mk` runs
plain Nock (an indirect call). -/
def nommStep (lib : Lib) (gul : Noun) (code : Bell → Option Nomm)
    (go : Trace → Noun → Nomm → Option Tone) (mk : Trace → Noun → Noun → Option Tone)
    (trace : Trace) (s : Noun) : Nomm → Option Tone
  | Nomm.cons p q =>
      tbind (go trace s p) fun a => tbind (go trace s q) fun b => some (Tone.zero (C a b))
  | Nomm.n0 axis =>
      match slot? axis s with
      | none => some (Tone.two trace)
      | some p => some (Tone.zero p)
  | Nomm.n1 k => some (Tone.zero k)
  | Nomm.n2 p q none =>
      tbind (go trace s p) fun s' => tbind (go trace s q) fun f' => mk trace s' f'
  | Nomm.n2 p q (some (b, _)) =>
      tbind (go trace s p) fun s' => tbind (go trace s q) fun _ =>
        (code b).bind fun nb => go trace s' nb
  | Nomm.n3 p => tbind (go trace s p) fun x => some (Tone.zero (wut x))
  | Nomm.n4 p => tbind (go trace s p) fun x =>
      match x with
      | Noun.cell _ _ => some (Tone.two trace)
      | Noun.atom a => some (Tone.zero (A (a + 1)))
  | Nomm.n5 p q => tbind (go trace s p) fun x => tbind (go trace s q) fun y =>
      some (Tone.zero (eqCode x y))
  | Nomm.n6 p q r => tbind (go trace s p) fun t =>
      match t with
      | Noun.atom 0 => go trace s q
      | Noun.atom 1 => go trace s r
      | _ => some (Tone.two trace)
  | Nomm.n7 p q => tbind (go trace s p) fun s' => go trace s' q
  | Nomm.n10 a v q =>
      if a = 0 then some (Tone.two trace) else
      tbind (go trace s q) fun t => tbind (go trace s v) fun x =>
        match edit? a x t with
        | none => some (Tone.two trace)
        | some r => some (Tone.zero r)
  | Nomm.n11s _ q _ => tbind (go trace s q) fun p => some (Tone.zero p)
  | Nomm.n11d tag h q _ => tbind (go trace s h) fun c =>
      tbind (go (if stopTag tag then (tag, c) :: trace else trace) s q) fun p =>
        some (Tone.zero p)
  | Nomm.n12 p q =>
      tbind (go trace s p) fun r => tbind (go trace s q) fun path =>
        if gul = A 0 then some (Tone.two trace) else
        (lib.slam gul (C r path)).bind fun res => (scryDecode res).bind fun d =>
          match d with
          | ScryRes.block => some (Tone.one path)
          | ScryRes.hunk => some (Tone.two ((Tag.hunk, C r path) :: trace))
          | ScryRes.val v => some (Tone.zero v)
  | Nomm.mean p _ q _ _ => tbind (go trace s p) fun trap =>
      tbind (go ((Tag.mean, trap) :: trace) s q) fun x => some (Tone.zero x)

/-- The semantics of a nomm, with fuel. -/
def nommF (lib : Lib) (gul : Noun) (code : Bell → Option Nomm) :
    Nat → Trace → Noun → Nomm → Option Tone
  | 0 => fun _ _ _ => none
  | n + 1 => nommStep lib gul code (nommF lib gul code n) (minkF lib gul n)

/-- The products of the formula `b` on the subjects of `P`, from any scry gate. -/
def Img (lib : Lib) (P : Noun → Prop) (b : Noun) : Noun → Prop :=
  fun y => ∃ x gul, P x ∧ Mink lib gul [] x b (Tone.zero y)

/-- The subjects `[*[x b] x]` of the body of `[8 b c]`. -/
def Img8 (lib : Lib) (P : Noun → Prop) (b : Noun) : Noun → Prop :=
  fun z => ∃ x y gul, P x ∧ Mink lib gul [] x b (Tone.zero y) ∧ z = C y x

/-- `+mink` crashes on `f` with the trace as it is, on every subject: an atom,
or a formula whose first operand is no formula. -/
def CrashesAtOnce (lib : Lib) (f : Noun) : Prop :=
  ∀ gul t s, Mink lib gul t s f (Tone.two t)

/-- **The invariant of nomm.**  `Annot lib code P f n`: the nomm `n` stands
for the formula `f` on the subjects of `P`, with the callees' nomms in
`code`. -/
inductive Annot (lib : Lib) (code : Bell → Option Nomm) : (Noun → Prop) → Noun → Nomm → Prop where
  | cons {P a1 a2 b p q} : Annot lib code P (C a1 a2) p → Annot lib code P b q →
      Annot lib code P (C (C a1 a2) b) (Nomm.cons p q)
  | n0 {P axis} : Annot lib code P (slot axis) (Nomm.n0 axis)
  | n1 {P k} : Annot lib code P (quote k) (Nomm.n1 k)
  /-- An indirect call. -/
  | indirect {P b c p q} : Annot lib code P b p → Annot lib code P c q →
      Annot lib code P (n3 (A 2) b c) (Nomm.n2 p q none)
  /-- A direct call of the bell `bl`, which has a nomm in the table (`CodeOK`
  says what it is). -/
  | direct {P b c p q bl k nb} : Annot lib code P b p → Annot lib code P c q →
      code bl = some nb →
      (∀ x gul y, P x → Mink lib gul [] x b (Tone.zero y) → Fits bl.less y) →
      (∀ x gul g, P x → Mink lib gul [] x c (Tone.zero g) → g = bl.fol) →
      Annot lib code P (n3 (A 2) b c) (Nomm.n2 p q (some (bl, k)))
  /-- An inlined call of the formula `g`: the formula-formula `c` is dropped,
  so it must return `g` on every subject. -/
  | inline {P b c g p q} : Annot lib code P b p →
      (∀ x gul, P x → Mink lib gul [] x c (Tone.zero g)) →
      Annot lib code (Img lib P b) g q →
      Annot lib code P (n3 (A 2) b c) (Nomm.n7 p q)
  | n3 {P b p} : Annot lib code P b p → Annot lib code P (n2 (A 3) b) (Nomm.n3 p)
  | n4 {P b p} : Annot lib code P b p → Annot lib code P (n2 (A 4) b) (Nomm.n4 p)
  | n5 {P b c p q} : Annot lib code P b p → Annot lib code P c q →
      Annot lib code P (n3 (A 5) b c) (Nomm.n5 p q)
  | n6 {P b c d p q r} : Annot lib code P b p → Annot lib code P c q → Annot lib code P d r →
      Annot lib code P (n4 (A 6) b c d) (Nomm.n6 p q r)
  | n7 {P b c p q} : Annot lib code P b p → Annot lib code (Img lib P b) c q →
      Annot lib code P (n3 (A 7) b c) (Nomm.n7 p q)
  /-- `[8 b c]` as `[7 [b 0 1] c]`. -/
  | n8 {P b c p q} : Annot lib code P b p → Annot lib code (Img8 lib P b) c q →
      Annot lib code P (n3 (A 8) b c) (Nomm.n7 (Nomm.cons p (Nomm.n0 1)) q)
  /-- `[9 a c]` as `[7 c 2 [0 1] 0 a]`. -/
  | n9 {P axis c q r} : Annot lib code P c q →
      Annot lib code (Img lib P c) (n3 (A 2) (slot 1) (slot axis)) r →
      Annot lib code P (n3 (A 9) (A axis) c) (Nomm.n7 q r)
  | n10 {P axis v t p q} : axis ≠ 0 → Annot lib code P v p → Annot lib code P t q →
      Annot lib code P (n3 (A 10) (n2 (A axis) v) t) (Nomm.n10 axis p q)
  | n11s {P tag q f} : Annot lib code P f q →
      Annot lib code P (n3 (A 11) (A tag) f) (Nomm.n11s tag q f)
  | n11d {P tag h f p q} : Annot lib code P h p → Annot lib code P f q →
      Annot lib code P (n3 (A 11) (C (A tag) h) f) (Nomm.n11d tag p q f)
  | mean {P h f p q b k} : Annot lib code P h p → Annot lib code P f q →
      Annot lib code P (n3 (A 11) (C (A Tag.mean) h) f) (Nomm.mean p b q f k)
  | n12 {P b c p q} : Annot lib code P b p → Annot lib code P c q →
      Annot lib code P (n3 (A 12) b c) (Nomm.n12 p q)
  /-- `%bare` inside a formula: an indirect call of the hinted formula itself,
  which `+eval-top` gives to `+mink`. -/
  | bare {P f} : isBare f = true → Annot lib code P f (Nomm.n2 (Nomm.n0 1) (Nomm.n1 f) none)
  /-- `[11 [%memo h] f]` with a safe clue: the call of `f` on the subject,
  `[2 [0 1] 1 f]`, memoized.  The clue is dropped, so it must return. -/
  | memo {P h f nm} : (∀ x gul, P x → ∃ c, Mink lib gul [] x h (Tone.zero c)) →
      Annot lib code P (n3 (A 2) (slot 1) (quote f)) nm →
      Annot lib code P (n3 (A 11) (C (A Tag.memo) h) f) nm
  /-- The default case of `fol-loop`: a crash, for formulas on which `+mink`
  crashes at once. -/
  | crash {P f} : CrashesAtOnce lib f → Annot lib code P f (Nomm.n0 0)

/-- Every nomm of the table stands for its bell's formula on the bell's sock. -/
def CodeOK (lib : Lib) (code : Bell → Option Nomm) : Prop :=
  ∀ bl nb, code bl = some nb → Annot lib code (Fits bl.less) bl.fol nb

end SkaModel
end Formalization
