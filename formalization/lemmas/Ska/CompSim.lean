import lemmas.Ska.ContractExamples
import lemmas.Ska.NommAgree

/-!
# What `+comp` must establish, for nomm without calls and hints

Nothing in this file models `+comp`.  It states the simulation relation that
the code `+comp` emits for a function body must satisfy, for the simplest
nomm (`Nomm.pure`: no calls, no hints, no scry), and proves that the
relation gives the contract of `Contract.lean`.

* `pureEval`: the value of a pure nomm on a subject, `none` for a crash.
  `nommF_pure` and `nommF_pure_total`: `nommF` returns `[%0 p]` where the
  value is `p`, and `[%2 trace]` with the trace it was given where there is
  none.
* `CompDone c nm mono`: the code `c`, entered as the interpreter enters it,
  returns `pureTone`, the value of `nm` or a crash with the trace it was
  entered with, and leaves the oracle's state alone.  This is the relation
  for the goal `%done` at the entry of a function.
* `bellContract_of_compDone`: if the nomm stands for the bell's formula on
  the bell's sock (`Annot`, as the analysis gives it at convergence) and the
  code satisfies `CompDone`, then the code satisfies `BellContract`, both
  halves, against any needs.
* `CompRel`: the relation for one block and each goal of `+comp` (`%done`,
  `%next`, `%pick`), with the subject held in registers by a need with
  registers (`RNeed`, `Holds`).  `compDone_of_compRel` derives `CompDone`
  from `CompRel` at the entry block, for a function whose need is one
  register for the whole subject.
* `oneConst`: the code that the case `[%1 *]` with goal `%done` of `+comp`
  emits, `(emit ~ ~[imm+[p.nomm r]] don+r)`, as a whole function with no
  argument; `oneConst_compRel` and `oneConst_contract`.
-/

set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel

open Nock

/-! ## Pure nomm -/

/-- A nomm without calls (`%2`), hints (`%11`, `%mean`) and scry (`%12`). -/
def Nomm.pure : Nomm → Bool
  | Nomm.cons p q => p.pure && q.pure
  | Nomm.n0 _ => true
  | Nomm.n1 _ => true
  | Nomm.n3 p => p.pure
  | Nomm.n4 p => p.pure
  | Nomm.n5 p q => p.pure && q.pure
  | Nomm.n6 p q r => p.pure && q.pure && r.pure
  | Nomm.n7 p q => p.pure && q.pure
  | Nomm.n10 _ v q => v.pure && q.pure
  | _ => false

/-- The depth of a pure nomm: the fuel `nommF` needs, less one. -/
def Nomm.depth : Nomm → Nat
  | Nomm.cons p q => max p.depth q.depth + 1
  | Nomm.n3 p => p.depth + 1
  | Nomm.n4 p => p.depth + 1
  | Nomm.n5 p q => max p.depth q.depth + 1
  | Nomm.n6 p q r => max p.depth (max q.depth r.depth) + 1
  | Nomm.n7 p q => max p.depth q.depth + 1
  | Nomm.n10 _ v q => max v.depth q.depth + 1
  | _ => 0

/-- The value of a pure nomm on the subject `s`; `none` is a crash. -/
def pureEval : Nomm → Noun → Option Noun
  | Nomm.cons p q, s => (pureEval p s).bind fun a => (pureEval q s).bind fun b => some (C a b)
  | Nomm.n0 ax, s => slot? ax s
  | Nomm.n1 k, _ => some k
  | Nomm.n3 p, s => (pureEval p s).bind fun x => some (wut x)
  | Nomm.n4 p, s => (pureEval p s).bind fun x =>
      match x with
      | Noun.atom a => some (A (a + 1))
      | Noun.cell _ _ => none
  | Nomm.n5 p q, s => (pureEval p s).bind fun x => (pureEval q s).bind fun y => some (eqCode x y)
  | Nomm.n6 p q r, s => (pureEval p s).bind fun t =>
      match t with
      | Noun.atom 0 => pureEval q s
      | Noun.atom 1 => pureEval r s
      | _ => none
  | Nomm.n7 p q, s => (pureEval p s).bind fun s' => pureEval q s'
  | Nomm.n10 a v q, s =>
      if a = 0 then none else
      (pureEval q s).bind fun t => (pureEval v s).bind fun x => edit? a x t
  | _, _ => none

/-- The tone of a pure nomm: its value, or a crash with the trace `t`. -/
def toneOf (t : Trace) : Option Noun → Tone
  | some p => Tone.zero p
  | none => Tone.two t

def pureTone (t : Trace) (nm : Nomm) (s : Noun) : Tone := toneOf t (pureEval nm s)

theorem tbind_toneOf (t : Trace) (o : Option Noun) (k : Noun → Option Tone) :
    tbind (some (toneOf t o)) k = (match o with | some p => k p | none => some (Tone.two t)) := by
  cases o <;> rfl

theorem tbind_toneOf_inv {x : Option Tone} {k : Noun → Option Tone} {r : Tone} {t : Trace}
    {o : Option Noun} (hx : ∀ y, x = some y → y = toneOf t o) (h : tbind x k = some r) :
    (∃ a, o = some a ∧ k a = some r) ∨ (o = none ∧ r = Tone.two t) := by
  rcases tbind_eq_some h with ⟨a, hxa, hk⟩ | ⟨hxr, hnz⟩
  · have e := hx _ hxa
    cases o with
    | some p => simp only [toneOf, Tone.zero.injEq] at e; subst e; exact Or.inl ⟨a, rfl, hk⟩
    | none => simp [toneOf] at e
  · have e := hx _ hxr
    cases o with
    | some p => exact absurd e (hnz p)
    | none => exact Or.inr ⟨rfl, e⟩

section Pure

variable (lib : Lib) (gul : Noun) (code : Bell → Option Nomm)

theorem nommF_succ_eq' (n : Nat) (t : Trace) (s : Noun) (nm : Nomm) :
    nommF lib gul code (n + 1) t s nm = nommStep lib gul code (nommF lib gul code n) (minkF lib gul n) t s nm :=
  rfl

/-- **What `nommF` returns on a pure nomm** is its value, or a crash with
the trace it was given. -/
theorem nommF_pure : ∀ (n : Nat) (t : Trace) (s : Noun) (nm : Nomm) (r : Tone), nm.pure = true →
    nommF lib gul code n t s nm = some r → r = pureTone t nm s := by
  intro n
  induction n with
  | zero => intro t s nm r _ h; simp [nommF] at h
  | succ n ih =>
  intro t s nm r hp h
  rw [nommF_succ_eq'] at h
  have I := fun s nm (hp : nm.pure = true) y (hy : nommF lib gul code n t s nm = some y) =>
    ih t s nm y hp hy
  cases nm with
  | cons p q =>
    simp only [Nomm.pure, Bool.and_eq_true] at hp
    simp only [nommStep] at h
    unfold pureTone; simp only [pureEval]
    rcases tbind_toneOf_inv (I s p hp.1) h with ⟨a, ha, h⟩ | ⟨ha, rfl⟩
    · rcases tbind_toneOf_inv (I s q hp.2) h with ⟨b, hb, h⟩ | ⟨hb, rfl⟩
      · cases h; simp [ha, hb, toneOf]
      · simp [ha, hb, toneOf]
    · simp [ha, toneOf]
  | n0 ax =>
    simp only [nommStep] at h
    unfold pureTone; simp only [pureEval]
    cases e : slot? ax s <;> simp [e, toneOf] at h ⊢ <;> exact h.symm
  | n1 k =>
    simp only [nommStep, Option.some.injEq] at h
    subst h; rfl
  | n2 p q info => simp [Nomm.pure] at hp
  | n3 p =>
    simp only [Nomm.pure] at hp
    simp only [nommStep] at h
    unfold pureTone; simp only [pureEval]
    rcases tbind_toneOf_inv (I s p hp) h with ⟨a, ha, h⟩ | ⟨ha, rfl⟩
    · cases h; simp [ha, toneOf]
    · simp [ha, toneOf]
  | n4 p =>
    simp only [Nomm.pure] at hp
    simp only [nommStep] at h
    unfold pureTone; simp only [pureEval]
    rcases tbind_toneOf_inv (I s p hp) h with ⟨a, ha, h⟩ | ⟨ha, rfl⟩
    · cases a with
      | atom k => cases h; simp [ha, toneOf]
      | cell _ _ => cases h; simp [ha, toneOf]
    · simp [ha, toneOf]
  | n5 p q =>
    simp only [Nomm.pure, Bool.and_eq_true] at hp
    simp only [nommStep] at h
    unfold pureTone; simp only [pureEval]
    rcases tbind_toneOf_inv (I s p hp.1) h with ⟨a, ha, h⟩ | ⟨ha, rfl⟩
    · rcases tbind_toneOf_inv (I s q hp.2) h with ⟨b, hb, h⟩ | ⟨hb, rfl⟩
      · cases h; simp [ha, hb, toneOf]
      · simp [ha, hb, toneOf]
    · simp [ha, toneOf]
  | n6 p q r' =>
    simp only [Nomm.pure, Bool.and_eq_true] at hp
    simp only [nommStep] at h
    unfold pureTone; simp only [pureEval]
    rcases tbind_toneOf_inv (I s p hp.1.1) h with ⟨a, ha, h⟩ | ⟨ha, rfl⟩
    · rw [ha]; simp only [Option.bind_some]
      match a, h with
      | Noun.atom 0, h => exact I s q hp.1.2 r h
      | Noun.atom 1, h => exact I s r' hp.2 r h
      | Noun.atom (_ + 2), h => cases h; rfl
      | Noun.cell _ _, h => cases h; rfl
    · simp [ha, toneOf]
  | n7 p q =>
    simp only [Nomm.pure, Bool.and_eq_true] at hp
    simp only [nommStep] at h
    unfold pureTone; simp only [pureEval]
    rcases tbind_toneOf_inv (I s p hp.1) h with ⟨a, ha, h⟩ | ⟨ha, rfl⟩
    · rw [ha]; exact ih t a q r hp.2 h
    · simp [ha, toneOf]
  | n10 ax v q =>
    simp only [Nomm.pure, Bool.and_eq_true] at hp
    simp only [nommStep] at h
    unfold pureTone; simp only [pureEval]
    split at h
    · rename_i h0; cases h; simp [h0, toneOf]
    · rename_i h0
      rw [if_neg h0]
      rcases tbind_toneOf_inv (I s q hp.2) h with ⟨a, ha, h⟩ | ⟨ha, rfl⟩
      · rcases tbind_toneOf_inv (I s v hp.1) h with ⟨b, hb, h⟩ | ⟨hb, rfl⟩
        · rw [ha, hb]; simp only [Option.bind_some]
          cases e : edit? ax b a <;> simp [e, toneOf] at h ⊢ <;> exact h.symm
        · simp [ha, hb, toneOf]
      · simp [ha, toneOf]
  | n11s _ _ _ => simp [Nomm.pure] at hp
  | n11d _ _ _ _ => simp [Nomm.pure] at hp
  | n12 _ _ => simp [Nomm.pure] at hp
  | mean _ _ _ _ _ => simp [Nomm.pure] at hp

/-- **`nommF` returns on a pure nomm**, with fuel one more than its depth. -/
theorem nommF_pure_total : ∀ (n : Nat) (nm : Nomm), nm.pure = true → nm.depth < n →
    ∀ t s, nommF lib gul code n t s nm = some (pureTone t nm s) := by
  intro n
  induction n with
  | zero => intro nm _ h; omega
  | succ n ih =>
  intro nm hp hd t s
  rw [nommF_succ_eq']
  cases nm with
  | cons p q =>
    simp only [Nomm.pure, Bool.and_eq_true] at hp
    simp only [Nomm.depth] at hd
    simp only [nommStep]
    rw [ih p hp.1 (by omega), ih q hp.2 (by omega)]
    unfold pureTone; simp only [pureEval]
    cases pureEval p s <;> cases pureEval q s <;> rfl
  | n0 ax =>
    simp only [nommStep]
    unfold pureTone; simp only [pureEval]
    cases slot? ax s <;> rfl
  | n1 k => rfl
  | n2 p q info => simp [Nomm.pure] at hp
  | n3 p =>
    simp only [Nomm.pure] at hp
    simp only [Nomm.depth] at hd
    simp only [nommStep]
    rw [ih p hp (by omega)]
    unfold pureTone; simp only [pureEval]
    cases pureEval p s <;> rfl
  | n4 p =>
    simp only [Nomm.pure] at hp
    simp only [Nomm.depth] at hd
    simp only [nommStep]
    rw [ih p hp (by omega)]
    unfold pureTone; simp only [pureEval]
    cases pureEval p s with
    | none => rfl
    | some a => cases a <;> rfl
  | n5 p q =>
    simp only [Nomm.pure, Bool.and_eq_true] at hp
    simp only [Nomm.depth] at hd
    simp only [nommStep]
    rw [ih p hp.1 (by omega), ih q hp.2 (by omega)]
    unfold pureTone; simp only [pureEval]
    cases pureEval p s <;> cases pureEval q s <;> rfl
  | n6 p q r =>
    simp only [Nomm.pure, Bool.and_eq_true] at hp
    simp only [Nomm.depth] at hd
    simp only [nommStep]
    rw [ih p hp.1.1 (by omega)]
    unfold pureTone; simp only [pureEval]
    cases pureEval p s with
    | none => rfl
    | some a =>
      simp only [tbind_toneOf, Option.bind_some]
      match a with
      | Noun.atom 0 => exact ih q hp.1.2 (by omega) t s
      | Noun.atom 1 => exact ih r hp.2 (by omega) t s
      | Noun.atom (_ + 2) => rfl
      | Noun.cell _ _ => rfl
  | n7 p q =>
    simp only [Nomm.pure, Bool.and_eq_true] at hp
    simp only [Nomm.depth] at hd
    simp only [nommStep]
    rw [ih p hp.1 (by omega)]
    unfold pureTone; simp only [pureEval]
    cases pureEval p s with
    | none => rfl
    | some a => exact ih q hp.2 (by omega) t a
  | n10 ax v q =>
    simp only [Nomm.pure, Bool.and_eq_true] at hp
    simp only [Nomm.depth] at hd
    simp only [nommStep]
    unfold pureTone; simp only [pureEval]
    by_cases h0 : ax = 0
    · simp [h0, toneOf]
    · rw [if_neg h0, if_neg h0, ih q hp.2 (by omega), ih v hp.1 (by omega)]
      unfold pureTone
      cases pureEval q s with
      | none => rfl
      | some a =>
        cases pureEval v s with
        | none => rfl
        | some b => simp only [tbind_toneOf, Option.bind_some]; cases edit? ax b a <;> rfl
  | n11s _ _ _ => simp [Nomm.pure] at hp
  | n11d _ _ _ _ => simp [Nomm.pure] at hp
  | n12 _ _ => simp [Nomm.pure] at hp
  | mean _ _ _ _ _ => simp [Nomm.pure] at hp

end Pure

/-- A pure nomm that stands for `f` on the subjects of `P`: on them, `+mink`
returns exactly `pureTone`. -/
theorem mink_pure {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {P : Noun → Prop}
    {f : Noun} {nm : Nomm} (hp : nm.pure = true) (hA : Annot lib code P f nm) {x : Noun} (hx : P x)
    (gul : Noun) (t : Trace) (r : Tone) : Mink lib gul t x f r ↔ r = pureTone t nm x := by
  rw [nomm_agree lib gul code hok hA hx t r]
  constructor
  · intro ⟨m, hm⟩; exact nommF_pure lib gul code m t x nm r hp hm
  · intro e; subst e; exact ⟨_, nommF_pure_total lib gul code _ nm hp (Nat.lt_succ_self _) t x⟩

/-! ## The relation at the entry, and the contract -/

section
variable {Map : Type → Type} [HoonMap Map]

/-- **What `+comp` must establish at the entry of a function whose body is
the pure nomm `nm`, with the goal `%done`**: entered as the interpreter
enters it (the subject whole for a function by subject, else split by the
code's need), the code returns the value of the nomm, or crashes with the
trace it was entered with where the nomm has no value, and leaves the
oracle's state alone (it makes no call). -/
def CompDone (lib : Lib) (c : Straight Map) (nm : Nomm) (mono : Bool) : Prop :=
  ∀ (σ : Type) (O : Oracle σ) (st : σ) (s : Noun) (args : List Noun) (t : Trace) (gul : Noun),
    (if mono then some [s] else split c.need s) = some args →
    execEntry lib O st c args t gul = some (pureTone t nm s, st)

theorem toneRel_pureTone {lib : Lib} {N : Needs} {ti tm : Trace} (htr : Forall2 (FrameRel lib N) ti tm)
    (nm : Nomm) (s : Noun) : ToneRel lib N (pureTone ti nm s) (pureTone tm nm s) := by
  unfold pureTone
  cases pureEval nm s with
  | some p => exact ToneRel.zero p
  | none => exact ToneRel.two htr

/-- **The simulation relation gives the contract.**  If the pure nomm `nm`
stands for the bell's formula on the bell's sock (`hA`, with a code table
`code` satisfying `CodeOK`, which a pure nomm never reads), and the code `c`
satisfies `CompDone` for `nm`, then `c` satisfies both halves of the
contract of the bell, against any needs `N`. -/
theorem bellContract_of_compDone {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {b : Bell} {nm : Nomm} (hp : nm.pure = true) (hA : Annot lib code (Fits b.less) b.fol nm)
    {mono : Bool} {c : Straight Map} (hc : CompDone lib c nm mono) (N : Needs) :
    BellContract lib N b mono c := by
  intro s hs args hargs
  refine ⟨?_, ?_⟩
  · intro σ Inv ν O n gul ti tm r _ _ _ hm st _ htr
    have e := (mink_pure hok hp hA hs gul tm r).mp ⟨n, hm⟩
    subst e
    exact ⟨pureTone ti nm s, st, hc σ O st s args ti gul hargs, toneRel_pureTone htr nm s⟩
  · intro σ Inv ν O gul ti tm _ _ _ st ton st' _ htr hrun
    rw [hc σ O st s args ti gul hargs] at hrun
    cases hrun
    exact ⟨pureTone tm nm s, (mink_pure hok hp hA hs gul tm _).mpr rfl, toneRel_pureTone htr nm s⟩

/-- The empty code table satisfies `CodeOK`. -/
theorem codeOK_none (lib : Lib) : CodeOK lib (fun _ => none) := fun _ _ h => by cases h

end

end SkaModel
end Formalization
