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
  from `CompRel` at the entry block, given that the registers the
  interpreter enters with hold the subject as the entry block's need asks.
* `compRel_done_of_next`, `compRel_n7`, `compRel_n6`: the relation composes
  as `+comp` composes goals: `%done` from `%next` into a block `[%don r]`,
  `[7 p q]` through `%next`, `[6 p q r]` through `%pick`.
* `const_contract`, `slot1_contract`, `bomb_contract`: the blocks that the
  cases `[%1 *]` and `[%0 *]` of `run` emit for the goal `%done`
  (`(emit ~ ~[imm+[p.nomm r]] don+r)`, `simple-next`, `bomb`), as whole
  functions, satisfy the contract of every bell with that formula.
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

/-! ## The relation for one block and one goal -/

/-- A need with registers, as `+comp` builds them: `%none`, the whole in a
register, a pair of needs, or a `%both`, the whole in a register and its
halves by needs. -/
inductive RNeed where
  | none
  | this (r : Nat)
  | pair (p q : RNeed)
  | both (r : Nat) (p q : RNeed)

/-- The registers `regs` hold the noun `n` as the need asks: a pair or a
`%both` asks for a cell. -/
def Holds : RNeed → Map Noun → Noun → Prop
  | RNeed.none, _, _ => True
  | RNeed.this r, regs, n => SkaModel.read r regs = some n
  | RNeed.pair p q, regs, Noun.cell h t => Holds p regs h ∧ Holds q regs t
  | RNeed.both r p q, regs, Noun.cell h t =>
      SkaModel.read r regs = some (C h t) ∧ Holds p regs h ∧ Holds q regs t
  | _, _, _ => False

/-- The goals of `+comp`'s `run`: return the product (`%done`); put the
product in registers as the need `nd` asks and go on in the block `k`
(`%next`, without parameters here); branch to `z` on `0` and to `o` on `1`
(`%pick`). -/
inductive Goal where
  | done
  | next (nd : RNeed) (k : Nat)
  | pick (z o : Nat)

/-- What the block `b` of `c`, entered with the registers `regs`, does for
the goal `g` when the value of the nomm is `v`.  A crash is `[%2 t]` with
the trace the block was entered with.  On `%next` and `%pick` the block goes
on in the target block with registers that agree with `regs` on the
registers `keep` that the code after it reads. -/
def GoalRel (lib : Lib) (c : Straight Map) (keep : Nat → Prop) {σ : Type} (O : Oracle σ) (st : σ)
    (regs : Map Noun) (t : Trace) (gul : Noun) (b : Blob) : Goal → Option Noun → Prop
  | Goal.done, v => execBlob lib O c gul st regs t b [] = some (toneOf t v, st)
  | Goal.next nd k, some p => ∃ regs' bk, HoonMap.get c.blocks k = some bk ∧ Holds nd regs' p ∧
      (∀ r, keep r → SkaModel.read r regs' = SkaModel.read r regs) ∧
      execBlob lib O c gul st regs t b [] = execBlob lib O c gul st regs' t bk []
  | Goal.pick z _, some (Noun.atom 0) => ∃ regs' bz, HoonMap.get c.blocks z = some bz ∧
      (∀ r, keep r → SkaModel.read r regs' = SkaModel.read r regs) ∧
      execBlob lib O c gul st regs t b [] = execBlob lib O c gul st regs' t bz []
  | Goal.pick _ o, some (Noun.atom 1) => ∃ regs' bo, HoonMap.get c.blocks o = some bo ∧
      (∀ r, keep r → SkaModel.read r regs' = SkaModel.read r regs) ∧
      execBlob lib O c gul st regs t b [] = execBlob lib O c gul st regs' t bo []
  | _, _ => execBlob lib O c gul st regs t b [] = some (Tone.two t, st)

/-- **The simulation relation of `+comp` for one block**: the block `b` of
`c`, entered with registers that hold the subject as the need `nd` asks,
does for the goal `g` what the value of the pure nomm `nm` says, against
every oracle. -/
def CompRel (lib : Lib) (c : Straight Map) (nm : Nomm) (g : Goal) (b : Blob) (nd : RNeed)
    (keep : Nat → Prop) : Prop :=
  ∀ (σ : Type) (O : Oracle σ) (st : σ) (s : Noun) (regs : Map Noun) (t : Trace) (gul : Noun),
    Holds nd regs s → GoalRel lib c keep O st regs t gul b g (pureEval nm s)

/-- **`CompDone` from the relation at the entry block**: block `0` is `b`,
the registers the interpreter enters with hold the subject as `nd` asks,
and `b` satisfies the relation for `%done`. -/
theorem compDone_of_compRel {lib : Lib} {c : Straight Map} {nm : Nomm} {b : Blob} {nd : RNeed}
    {keep : Nat → Prop} {mono : Bool} (hb : HoonMap.get c.blocks 0 = some b)
    (hhold : ∀ s args, (if mono then some [s] else split c.need s) = some args →
      Holds nd (regsOf (Map := Map) args) s)
    (hr : CompRel lib c nm Goal.done b nd keep) : CompDone lib c nm mono := by
  intro σ O st s args t gul hargs
  have := hr σ O st s (regsOf args) t gul (hhold s args hargs)
  simp only [GoalRel] at this
  simp only [execEntry, hb, Option.bind_some]
  exact this

theorem execBlob_don {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ}
    {regs : Map Noun} {t : Trace} (r : Nat) :
    execBlob lib O c gul st regs t ⟨[], [], Termin.don r⟩ [] =
      (SkaModel.read r regs).bind fun v => some (Tone.zero v, st) := by
  rw [execBlob]; simp

theorem execBlob_bom {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ}
    {regs : Map Noun} {t : Trace} (o : Option Nat) :
    execBlob lib O c gul st regs t ⟨[], [], Termin.bom o⟩ [] = some (Tone.two t, st) := by
  rw [execBlob]; simp

/-- **`%done` from `%next`**, as `+comp` makes it for a cell of formulas: a
fresh register `r`, a block `[%don r]`, and the goal `%next` that puts the
product in `r` and goes on in that block. -/
theorem compRel_done_of_next {lib : Lib} {c : Straight Map} {nm : Nomm} {b : Blob} {nd : RNeed}
    {keep : Nat → Prop} {r k : Nat} (hk : HoonMap.get c.blocks k = some ⟨[], [], Termin.don r⟩)
    (h : CompRel lib c nm (Goal.next (RNeed.this r) k) b nd keep) :
    CompRel lib c nm Goal.done b nd keep := by
  intro σ O st s regs t gul hs
  have H := h σ O st s regs t gul hs
  simp only [GoalRel]
  revert H
  cases pureEval nm s with
  | none => intro H; exact H
  | some p =>
    intro ⟨regs', bk, hbk, hh, _, he⟩
    rw [hk] at hbk; cases hbk
    rw [he, execBlob_don]
    simp only [Holds] at hh
    simp [hh, toneOf]

/-! ## Composition: `%7` through `%next`, `%6` through `%pick`

`+comp` compiles `[7 p q]` for a goal by compiling `q` for the goal, then
`p` for the goal `%next` into the need and block of `q`; and `[6 p q r]`
by compiling `q` and `r` for the goal, then `p` for the goal `%pick` into
their blocks.  The relation composes the same way, provided the registers
that the code after a block reads are kept by the code before it. -/

/-- The registers of a need. -/
def RNeed.Mem : RNeed → Nat → Prop
  | RNeed.none, _ => False
  | RNeed.this r, x => x = r
  | RNeed.pair p q, x => p.Mem x ∨ q.Mem x
  | RNeed.both r p q, x => x = r ∨ p.Mem x ∨ q.Mem x

/-- Registers that agree on a need's registers hold what it holds. -/
theorem Holds.agree : ∀ (nd : RNeed) {regs regs' : Map Noun} {n : Noun},
    (∀ x, nd.Mem x → SkaModel.read x regs' = SkaModel.read x regs) → Holds nd regs n → Holds nd regs' n
  | RNeed.none, _, _, _, _, h => h
  | RNeed.this r, _, _, _, ha, h => by
    simp only [Holds] at h ⊢; rw [ha r (by simp [RNeed.Mem])]; exact h
  | RNeed.pair p q, _, _, Noun.cell a b, ha, h =>
    ⟨Holds.agree p (fun x hx => ha x (Or.inl hx)) h.1, Holds.agree q (fun x hx => ha x (Or.inr hx)) h.2⟩
  | RNeed.pair _ _, _, _, Noun.atom _, _, h => by simp [Holds] at h
  | RNeed.both r p q, _, _, Noun.cell a b, ha, h =>
    ⟨by rw [ha r (Or.inl rfl)]; exact h.1, Holds.agree p (fun x hx => ha x (Or.inr (Or.inl hx))) h.2.1,
      Holds.agree q (fun x hx => ha x (Or.inr (Or.inr hx))) h.2.2⟩
  | RNeed.both _ _ _, _, _, Noun.atom _, _, h => by simp [Holds] at h

section
variable {lib : Lib} {c : Straight Map} {K : Nat → Prop} {σ : Type} {O : Oracle σ} {st : σ}
  {t : Trace} {gul : Noun}

/-- A block that crashes does what every goal asks where there is no value. -/
theorem goalRel_crash {regs : Map Noun} {b : Blob} (g : Goal)
    (h : execBlob lib O c gul st regs t b [] = some (Tone.two t, st)) :
    GoalRel lib c K O st regs t gul b g none := by
  cases g <;> simp only [GoalRel, toneOf] <;> exact h

/-- What a block does for a goal, a block that runs as it does does too. -/
theorem GoalRel.transfer {regs regs' : Map Noun} {b b' : Blob} {g : Goal} {v : Option Noun}
    (he : execBlob lib O c gul st regs t b [] = execBlob lib O c gul st regs' t b' [])
    (hk : ∀ r, K r → SkaModel.read r regs' = SkaModel.read r regs)
    (h : GoalRel lib c K O st regs' t gul b' g v) : GoalRel lib c K O st regs t gul b g v := by
  cases g with
  | done => simp only [GoalRel] at h ⊢; rw [he]; exact h
  | next nd k =>
    cases v with
    | none => simp only [GoalRel] at h ⊢; rw [he]; exact h
    | some p =>
      obtain ⟨r2, bk, hbk, hh, hk2, he2⟩ := h
      exact ⟨r2, bk, hbk, hh, fun r hr => (hk2 r hr).trans (hk r hr), he.trans he2⟩
  | pick z o =>
    rcases v with _ | ⟨⟨_ | _ | k⟩ | ⟨a, b⟩⟩
    · simp only [GoalRel] at h ⊢; rw [he]; exact h
    · obtain ⟨r2, bk, hbk, hk2, he2⟩ := h
      exact ⟨r2, bk, hbk, fun r hr => (hk2 r hr).trans (hk r hr), he.trans he2⟩
    · obtain ⟨r2, bk, hbk, hk2, he2⟩ := h
      exact ⟨r2, bk, hbk, fun r hr => (hk2 r hr).trans (hk r hr), he.trans he2⟩
    · simp only [GoalRel] at h ⊢; rw [he]; exact h
    · simp only [GoalRel] at h ⊢; rw [he]; exact h

end

/-- **`[7 p q]`**: `p` for the goal `%next` into the need and block of `q`,
`q` for the goal. -/
theorem compRel_n7 {lib : Lib} {c : Straight Map} {p q : Nomm} {g : Goal} {bp bq : Blob}
    {nd ndq : RNeed} {K Kp : Nat → Prop} {kq : Nat} (hkq : HoonMap.get c.blocks kq = some bq)
    (hp : CompRel lib c p (Goal.next ndq kq) bp nd Kp) (hq : CompRel lib c q g bq ndq K)
    (hK : ∀ r, K r → Kp r) : CompRel lib c (Nomm.n7 p q) g bp nd K := by
  intro σ O st s regs t gul hs
  have Hp := hp σ O st s regs t gul hs
  simp only [pureEval]
  cases e : pureEval p s with
  | none =>
    rw [e] at Hp
    exact goalRel_crash g Hp
  | some s' =>
    rw [e] at Hp
    obtain ⟨regs', bk, hbk, hh, hk, he⟩ := Hp
    rw [hkq] at hbk; cases hbk
    exact GoalRel.transfer he (fun r hr => hk r (hK r hr)) (hq σ O st s' regs' t gul hh)

/-- **`[6 p q r]`**: `p` for the goal `%pick` into the blocks of `q` and
`r`, both for the goal, with the subject's registers kept by `p`. -/
theorem compRel_n6 {lib : Lib} {c : Straight Map} {p q r : Nomm} {g : Goal} {bp bq br : Blob}
    {nd : RNeed} {K Kp : Nat → Prop} {kq kr : Nat} (hkq : HoonMap.get c.blocks kq = some bq)
    (hkr : HoonMap.get c.blocks kr = some br)
    (hp : CompRel lib c p (Goal.pick kq kr) bp nd Kp) (hq : CompRel lib c q g bq nd K)
    (hr : CompRel lib c r g br nd K) (hK : ∀ x, K x → Kp x) (hnd : ∀ x, nd.Mem x → Kp x) :
    CompRel lib c (Nomm.n6 p q r) g bp nd K := by
  intro σ O st s regs t gul hs
  have Hp := hp σ O st s regs t gul hs
  simp only [pureEval]
  cases e : pureEval p s with
  | none =>
    rw [e] at Hp
    exact goalRel_crash g Hp
  | some v =>
    rw [e] at Hp
    simp only [Option.bind_some]
    rcases v with ⟨_ | _ | k⟩ | ⟨a, b⟩
    · obtain ⟨regs', bz, hbz, hk, he⟩ := Hp
      rw [hkq] at hbz; cases hbz
      exact GoalRel.transfer he (fun x hx => hk x (hK x hx))
        (hq σ O st s regs' t gul (Holds.agree nd (fun x hx => hk x (hnd x hx)) hs))
    · obtain ⟨regs', bo, hbo, hk, he⟩ := Hp
      rw [hkr] at hbo; cases hbo
      exact GoalRel.transfer he (fun x hx => hk x (hK x hx))
        (hr σ O st s regs' t gul (Holds.agree nd (fun x hx => hk x (hnd x hx)) hs))
    · simp only [GoalRel] at Hp; exact goalRel_crash g Hp
    · simp only [GoalRel] at Hp; exact goalRel_crash g Hp

/-! ## The leaves of `+comp` with the goal `%done`

From the cases `[%0 *]` and `[%1 *]` of `run`: `[%1 k]` emits a block
`(emit ~ ~[imm+[k r]] don+r)` with a fresh register `r` and needs nothing of
the subject; `[%0 1]` is `simple-next`, a block `[%don r]` with the need
`this+r`; `[%0 0]` is `bomb`, a block `[%bom ~]` that needs nothing. -/

theorem compRel_const (lib : Lib) (c : Straight Map) (k : Noun) (r : Nat) (nd : RNeed)
    (keep : Nat → Prop) :
    CompRel lib c (Nomm.n1 k) Goal.done ⟨[], [Pole.imm k r], Termin.don r⟩ nd keep := by
  intro σ O st s regs t gul _
  simp only [GoalRel, pureEval, toneOf]
  rw [execBlob_body]
  simp only [execPole_imm, Option.bind_some]
  rw [execBlob_don]
  simp [store, SkaModel.read, HoonMap.get_put]

theorem compRel_slot1 (lib : Lib) (c : Straight Map) (r : Nat) (keep : Nat → Prop) :
    CompRel lib c (Nomm.n0 1) Goal.done ⟨[], [], Termin.don r⟩ (RNeed.this r) keep := by
  intro σ O st s regs t gul hs
  simp only [Holds] at hs
  simp only [GoalRel, pureEval, slot?_one, toneOf]
  rw [execBlob_don, hs]; rfl

theorem compRel_bomb (lib : Lib) (c : Straight Map) (nd : RNeed) (keep : Nat → Prop) :
    CompRel lib c (Nomm.n0 0) Goal.done ⟨[], [], Termin.bom none⟩ nd keep := by
  intro σ O st s regs t gul _
  simp only [GoalRel]
  rw [execBlob_bom]
  have : slot? 0 s = none := slot?_zero s
  simp [pureEval, this, toneOf]

/-- A function of one block that needs nothing of its subject. -/
def noArgBlock (b : Blob) : Straight Map := ⟨NeedOrd.none, 0, HoonMap.put HoonMap.empty 0 b⟩

theorem holds_none (s : Noun) (args : List Noun) : Holds (Map := Map) RNeed.none (regsOf args) s :=
  trivial

/-- **The code of `[1 k]`**: as a function by need, or by subject, the
block that `+comp` emits satisfies the contract of every bell whose formula
is `[1 k]`. -/
theorem const_contract (lib : Lib) (N : Needs) (k : Noun) (r : Nat) (b : Bell) (hf : b.fol = quote k)
    (mono : Bool) :
    BellContract lib N b mono (noArgBlock (Map := Map) ⟨[], [Pole.imm k r], Termin.don r⟩) := by
  refine bellContract_of_compDone (codeOK_none lib) (nm := Nomm.n1 k) rfl
    (by rw [hf]; exact Annot.n1) ?_ N
  exact compDone_of_compRel (nd := RNeed.none) (keep := fun _ => False)
    (by simp [noArgBlock, HoonMap.get_put]) (fun s args _ => holds_none s args)
    (compRel_const lib _ k r RNeed.none _)

/-- **The code of `[0 1]`**: the block `[%don 0]` with the whole subject in
register `0` satisfies the contract of every bell whose formula is `[0 1]`. -/
theorem slot1_contract (lib : Lib) (N : Needs) (b : Bell) (hf : b.fol = slot 1) (mono : Bool) :
    BellContract lib N b mono (oneBlock (Map := Map) ⟨[], [], Termin.don 0⟩) := by
  refine bellContract_of_compDone (codeOK_none lib) (nm := Nomm.n0 1) rfl
    (by rw [hf]; exact Annot.n0) ?_ N
  refine compDone_of_compRel (nd := RNeed.this 0) (keep := fun _ => False)
    (by simp [oneBlock, HoonMap.get_put]) ?_ (compRel_slot1 lib _ 0 _)
  intro s args h
  have e : args = [s] := by
    cases mono <;> simp [oneBlock, split] at h <;> exact h.symm
  subst e
  simp [Holds, regsOf, regsFrom, SkaModel.read, HoonMap.get_put]

/-- **The code of `[0 0]`**: the block `[%bom ~]` satisfies the contract of
every bell whose formula is `[0 0]`. -/
theorem bomb_contract (lib : Lib) (N : Needs) (b : Bell) (hf : b.fol = slot 0) (mono : Bool) :
    BellContract lib N b mono (noArgBlock (Map := Map) ⟨[], [], Termin.bom none⟩) := by
  refine bellContract_of_compDone (codeOK_none lib) (nm := Nomm.n0 0) rfl
    (by rw [hf]; exact Annot.n0) ?_ N
  exact compDone_of_compRel (nd := RNeed.none) (keep := fun _ => False)
    (by simp [noArgBlock, HoonMap.get_put]) (fun s args _ => holds_none s args)
    (compRel_bomb lib _ RNeed.none _)


end

end SkaModel
end Formalization
