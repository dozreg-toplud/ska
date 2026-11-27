import lemmas.Compiler.OptLinkTotalAlias
import lemmas.Ska.CompEntry

/-!
# `EntryOK` of raw code from four static facts

`Opt.Keeps` assumes `EntryOK` of every entry (`ReadsOK`, `ArgsOK`,
`LocalOK`; `bellContract_of_keeps`), and LEDGER 2.c names it the leaf
`rawEntry`.  Here it follows, for every oracle, scry gate, state and trace,
from four facts of the blocks, none of them about executions:

* `DefFirst` (a field of track D's `OptIn`): on every path of blocks from
  `0`, a register with a definition is read only after one;
* `Compiler.ReadsIn n` (track D's `optInput_*`): a register a reachable
  block reads is defined in the map or is below `n`;
* `NoPoison`: no reachable jump passes `~` (so no register is ever
  poisoned, and a real read fails only on a register that is not there);
* `CelGuard`: every `%hed s` / `%tal s` of a reachable block comes after a
  `%cel s` of the same body with no op between them that writes `s`.

`entryOK_of`: with these and at least `n` entry values, `EntryOK` holds.
The proof is one invariant of the configurations of a path from the entry
(`EInv`): the path's blocks are a `BPath`, the registers hold no poison,
every register below `n` or defined by an earlier block of the path, by a
parameter or by an op already run of the current block is in the file, and
a register that a `%cel` already run checked, with no write since, holds a
cell.  `einv_step` keeps it along every `Step`.

`NoPoison` and `CelGuard` are checked on the raw output of `FragX`
(`Glue/EntryCheck.lean`); they are the two new leaves of `rawEntry` on that
class (`Glue/EntryFragX.lean`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt Path

section
variable {Map : Type → Type} [HoonMap Map] [Opt.MapKeys Map] {σ : Type}

/-! ## The two new static facts -/

/-- **No reachable jump passes `~`.** -/
def NoPoison (bl : Map Blob) : Prop :=
  ∀ o b j, Reach bl o → HoonMap.get bl o = some b → j ∈ getJmps b.fin → Option.none ∉ j.args

/-- The register a `%hed` or `%tal` takes apart. -/
def splitReg : Pole → Option Nat
  | Pole.hed s _ => some s
  | Pole.tal s _ => some s
  | _ => Option.none

/-- **The `%cel` guard**: every `%hed s` / `%tal s` of a reachable block
comes after a `%cel s` of the same body, and no op between them writes
`s`. -/
def CelGuard (bl : Map Blob) : Prop :=
  ∀ o b i p s, Reach bl o → HoonMap.get bl o = some b → b.body[i]? = some p → splitReg p = some s →
    ∃ j : Nat, j < i ∧ b.body[j]? = some (Pole.cel s) ∧
      ∀ l, j < l → l < i → ∀ q, b.body[l]? = some q → aliasDst q ≠ some s

/-! ## Small facts -/

theorem bpath_reach {bl : Map Blob} : ∀ {l : List Nat}, BPath bl l → ∀ {o p}, l = o :: p → Reach bl o := by
  intro l h
  induction h with
  | start => intro o p e; cases e; exact Reach.zero
  | step _ hb hj ih => intro o p e; cases e; exact Reach.jump (ih rfl) hb hj

theorem taken_mem {regs : Map (Option Noun)} {f : Termin} {j : Jmp} (h : taken regs f = some j) :
    j ∈ getJmps f := by
  cases f with
  | lti n r z o =>
    simp only [taken, Option.map_eq_some_iff] at h; obtain ⟨v, _, rfl⟩ := h
    have key : ∀ c : Bool, (if c = true then z else o) ∈ [z, o] := fun c => by cases c <;> simp
    exact key _
  | clq r z o =>
    simp only [taken, Option.map_eq_some_iff] at h; obtain ⟨v, _, rfl⟩ := h; split <;> simp [getJmps]
  | eqq l r z o =>
    simp only [taken, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, rfl⟩ := h; split <;> simp [getJmps]
  | brn r z o =>
    simp only [taken, Option.bind_eq_some_iff] at h
    obtain ⟨v, _, h⟩ := h
    split at h
    · cases h; simp [getJmps]
    · split at h
      · cases h; simp [getJmps]
      · cases h
  | brz r z o =>
    simp only [taken, Option.map_eq_some_iff] at h; obtain ⟨v, _, rfl⟩ := h; split <;> simp [getJmps]
  | hop t => simp only [taken, Option.some.injEq] at h; subst h; simp [getJmps]
  | jmp => simp [taken] at h
  | jmf => simp [taken] at h
  | jsp => simp [taken] at h
  | jsf => simp [taken] at h
  | don => simp [taken] at h
  | bom => simp [taken] at h

/-- No register holds poison. -/
def Pure (regs : Map (Option Noun)) : Prop := ∀ r, HoonMap.get regs r ≠ some Option.none

/-- The register is in the file. -/
def Present (regs : Map (Option Noun)) (r : Nat) : Prop := (HoonMap.get regs r).isSome

theorem read_of_present {regs : Map (Option Noun)} {r : Nat} (hp : Pure regs) (h : Present regs r) :
    ∃ v, read r regs = some v := by
  unfold Present at h; unfold read
  cases e : HoonMap.get regs r with
  | none => rw [e] at h; cases h
  | some u => cases u with
    | none => exact absurd e (hp r)
    | some v => exact ⟨v, rfl⟩

theorem present_put {regs : Map (Option Noun)} {r d : Nat} {u : Option Noun} (h : Present regs r) :
    Present (HoonMap.put regs d u) r := by
  unfold Present at *; rw [HoonMap.get_put]; split <;> simp_all

theorem pure_put {regs : Map (Option Noun)} {d : Nat} {v : Noun} (h : Pure regs) :
    Pure (HoonMap.put regs d (some v)) := by
  intro r; rw [HoonMap.get_put]; split
  · simp
  · exact h r

theorem pure_regsOf (vals : List Noun) : Pure (regsOf (Map := Map) vals) := by
  intro r
  unfold regsOf
  rw [Comp.get_regsFrom]
  split
  · cases vals[r - 0]? <;> simp
  · rw [HoonMap.get_empty]; simp

theorem present_regsOf {vals : List Noun} {r : Nat} (h : r < vals.length) : Present (regsOf (Map := Map) vals) r := by
  unfold Present regsOf
  rw [Comp.get_regsFrom, if_pos (by omega)]
  simp [List.getElem?_eq_getElem h]

/-! ## One op -/

/-- **An op that steps changes only the register it writes**, to a value or,
for a `%mov`, to what its source holds. -/
theorem execPole_zero {lib : Lib} {O : Oracle σ} {gul : Noun} {st st' : σ} {p : Pole}
    {regs R : Map (Option Noun)} {t t' : Trace} {n : Noun}
    (h : execPole lib O gul st p regs t = some (Tone.zero n, R, t', st')) :
    (∀ r, aliasDst p ≠ some r → HoonMap.get R r = HoonMap.get regs r) ∧
    (∀ d, aliasDst p = some d →
      (∃ v, HoonMap.get R d = some (some v)) ∨
        ∃ s, p = Pole.mov s d ∧ HoonMap.get R d = HoonMap.get regs s ∧ (HoonMap.get regs s).isSome) := by
  have hst : ∀ d v, (∀ r, some d ≠ some r → HoonMap.get (store d v regs) r = HoonMap.get regs r) ∧
      (∃ w, HoonMap.get (store d v regs) d = some (some w)) := fun d v =>
    ⟨fun r hr => by simp only [store, HoonMap.get_put]; rw [if_neg (fun e => hr (by rw [e]))],
     ⟨v, by simp [store, HoonMap.get_put]⟩⟩
  cases p with
  | imm a d =>
    simp only [execPole, localPole, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -, -⟩ := h
    exact ⟨(hst d a).1, fun d' e => by cases e; exact Or.inl (hst d a).2⟩
  | mov s d =>
    simp only [execPole, localPole, Option.map_eq_some_iff, Option.bind_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨_, _, _⟩, ⟨R0, hm, hR⟩, he⟩ := h
    simp only [Option.some.injEq, Prod.mk.injEq] at hR he
    obtain ⟨rfl, rfl, rfl⟩ := hR
    obtain ⟨-, rfl, -, -⟩ := he
    unfold move at hm
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp hm
    refine ⟨fun r hr => ?_, fun d' e => ?_⟩
    · simp only [HoonMap.get_put]; rw [if_neg (fun e => hr (by simp [aliasDst, e]))]
    · cases e; exact Or.inr ⟨s, rfl, by simp [HoonMap.get_put, hu], by simp [hu]⟩
  | inc s d =>
    simp only [execPole, localPole, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
    obtain ⟨⟨_, _, _⟩, ⟨v, _, hv⟩, he⟩ := h
    cases v with
    | cell => simp at hv; obtain ⟨rfl, -⟩ := hv; simp at he
    | atom a =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hv he
      obtain ⟨-, rfl, -⟩ := hv; obtain ⟨-, rfl, -, -⟩ := he
      exact ⟨(hst d _).1, fun d' e => by cases e; exact Or.inl (hst d _).2⟩
  | con a b d =>
    simp only [execPole, localPole, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
    obtain ⟨⟨_, _, _⟩, ⟨_, _, _, _, hv⟩, he⟩ := h
    simp only [Option.some.injEq, Prod.mk.injEq] at hv he
    obtain ⟨-, rfl, -⟩ := hv; obtain ⟨-, rfl, -, -⟩ := he
    exact ⟨(hst d _).1, fun d' e => by cases e; exact Or.inl (hst d _).2⟩
  | hed s d =>
    simp only [execPole, localPole, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
    obtain ⟨⟨_, _, _⟩, ⟨v, _, hv⟩, he⟩ := h
    cases v with
    | atom => simp at hv
    | cell x y =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hv he
      obtain ⟨-, rfl, -⟩ := hv; obtain ⟨-, rfl, -, -⟩ := he
      exact ⟨(hst d _).1, fun d' e => by cases e; exact Or.inl (hst d _).2⟩
  | tal s d =>
    simp only [execPole, localPole, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
    obtain ⟨⟨_, _, _⟩, ⟨v, _, hv⟩, he⟩ := h
    cases v with
    | atom => simp at hv
    | cell x y =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hv he
      obtain ⟨-, rfl, -⟩ := hv; obtain ⟨-, rfl, -, -⟩ := he
      exact ⟨(hst d _).1, fun d' e => by cases e; exact Or.inl (hst d _).2⟩
  | spy e q d =>
    simp only [execPole, localPole, Option.map_eq_some_iff] at h
    obtain ⟨⟨ton, R0, t0⟩, hl, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, -, -⟩ := he
    split at hl
    · simp at hl
    · simp only [Option.bind_eq_some_iff] at hl
      obtain ⟨_, _, _, _, _, _, dr, _, hl⟩ := hl
      cases dr with
      | block => simp at hl
      | hunk => simp at hl
      | val v =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hl
        obtain ⟨-, rfl, -⟩ := hl
        exact ⟨(hst d _).1, fun d' e => by cases e; exact Or.inl (hst d _).2⟩
  | nok u f d =>
    simp only [execPole, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, _, _, ⟨ton, st0⟩, _, h⟩ := h
    cases ton with
    | zero q =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -, -⟩ := h
      exact ⟨(hst d _).1, fun d' e => by cases e; exact Or.inl (hst d _).2⟩
    | one => simp at h
    | two => simp at h
  | cal a v d | caf a v d _ | cam a v d _ =>
    simp only [execPole, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, ⟨ton, st0⟩, _, h⟩ := h
    cases ton with
    | zero q =>
      simp only [afterCall, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -, -⟩ := h
      exact ⟨(hst d _).1, fun d' e => by cases e; exact Or.inl (hst d _).2⟩
    | one => simp [afterCall] at h
    | two => simp [afterCall] at h
  | csl a s d | csf a s d _ | csm a s d _ =>
    simp only [execPole, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, ⟨ton, st0⟩, _, h⟩ := h
    cases ton with
    | zero q =>
      simp only [afterCall, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -, -⟩ := h
      exact ⟨(hst d _).1, fun d' e => by cases e; exact Or.inl (hst d _).2⟩
    | one => simp [afterCall] at h
    | two => simp [afterCall] at h
  | cel q | lob q | equ q _ | hsp _ _ | hse _ _ | hdp _ q _ | hde _ q _ | hmp _ _ _ | hme _ _ _ | hcp _ _ | hce _ _ =>
    refine ⟨fun r _ => ?_, fun d e => by simp [aliasDst] at e⟩
    simp only [execPole, Option.map_eq_some_iff] at h
    obtain ⟨⟨_, R0, _⟩, hl, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl, -, -⟩ := he
    simp only [localPole] at hl
    repeat' (first | (rw [Option.bind_eq_some_iff] at hl; obtain ⟨_, _, hl⟩ := hl) | split at hl)
    all_goals first
      | (simp only [Option.some.injEq, Prod.mk.injEq] at hl; rw [← hl.2.1])
      | simp at hl

theorem execPole_cel {lib : Lib} {O : Oracle σ} {gul : Noun} {st st' : σ} {s : Nat}
    {regs R : Map (Option Noun)} {t t' : Trace} {n : Noun}
    (h : execPole lib O gul st (Pole.cel s) regs t = some (Tone.zero n, R, t', st')) :
    ∃ x y, read s regs = some (C x y) := by
  simp only [execPole, localPole, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
  obtain ⟨⟨_, _, _⟩, ⟨v, hv, hl⟩, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, -, -, -⟩ := he
  cases v with
  | atom => simp at hl
  | cell x y => exact ⟨x, y, hv⟩

theorem mem_erase_last {k d : Nat} {l : List Nat} (h : k ∈ l) : k ∈ (l ++ [d]).erase d := by
  by_cases e : k = d
  · subst e; rw [List.erase_append_left _ h]; simp
  · exact (List.mem_erase_of_ne e).mpr (List.mem_append_left _ h)

/-- A real read is a read of `aliasReads`. -/
theorem poleReads_sub {gul : Noun} {p : Pole} {k : Nat} (hk : k ∈ poleReads gul p) : k ∈ aliasReads p := by
  cases p with
  | inc s d => exact mem_erase_last (l := [s]) hk
  | con a b d => exact mem_erase_last (l := [a, b]) hk
  | hed s d => exact mem_erase_last (l := [s]) hk
  | tal s d => exact mem_erase_last (l := [s]) hk
  | cel q => exact hk
  | lob q => exact hk
  | equ a b => exact hk
  | hdp n q f =>
    simp only [poleReads] at hk
    split at hk
    · exact hk
    · simp at hk
  | hmp a v f => exact hk
  | spy e q d =>
    simp only [poleReads] at hk
    split at hk
    · simp at hk
    · exact mem_erase_last (l := [e, q]) hk
  | nok u f d => exact mem_erase_last (l := [u, f]) hk
  | cal a v d => show k ∈ (d :: v).erase d; rw [List.erase_cons_head]; exact hk
  | caf a v d _ => show k ∈ (d :: v).erase d; rw [List.erase_cons_head]; exact hk
  | cam a v d _ => show k ∈ (d :: v).erase d; rw [List.erase_cons_head]; exact hk
  | csl a s d => exact mem_erase_last (l := [s]) hk
  | csf a s d _ => exact mem_erase_last (l := [s]) hk
  | csm a s d _ => exact mem_erase_last (l := [s]) hk
  | imm => simp [poleReads] at hk
  | mov => simp [poleReads] at hk
  | hsp => simp [poleReads] at hk
  | hse => simp [poleReads] at hk
  | hde => simp [poleReads] at hk
  | hme => simp [poleReads] at hk
  | hcp => simp [poleReads] at hk
  | hce => simp [poleReads] at hk

theorem finReads_sub {f : Termin} {k : Nat} (hk : k ∈ finReads f) : k ∈ finRegs f := by
  cases f <;> simp only [finReads, finRegs, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
    List.mem_append] at hk ⊢
  all_goals first
    | exact Or.inl hk
    | exact hk
    | (rcases hk with h | h
       · exact Or.inl h
       · exact Or.inr (Or.inl h))

theorem jmpArgs_sub {f : Termin} {j : Jmp} {k : Nat} (hj : j ∈ getJmps f) (hk : some k ∈ j.args) :
    k ∈ finRegs f := by
  have hr : k ∈ jmpRegs j := by unfold jmpRegs; exact List.mem_filterMap.mpr ⟨some k, hk, rfl⟩
  cases f <;> simp only [getJmps, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hj <;>
    simp only [finRegs, List.mem_cons, List.mem_append]
  all_goals first
    | (rcases hj with rfl | rfl
       · exact Or.inr (Or.inl hr)
       · exact Or.inr (Or.inr hr))
    | (rcases hj with rfl | rfl
       · exact Or.inr (Or.inr (Or.inl hr))
       · exact Or.inr (Or.inr (Or.inr hr)))
    | (subst hj; exact hr)

theorem evalPassLoop_ok : ∀ (args : List (Option Nat)) (par : List Nat) (regs R : Map (Option Noun)),
    evalPassLoop args par regs = some R → Option.none ∉ args → Pure regs →
    Pure R ∧ (∀ r, Present regs r → Present R r) ∧ ∀ q ∈ par, Present R q
  | [], par, regs, R, h, _, hp => by
    simp only [evalPassLoop] at h
    split at h
    · rename_i e; cases h; subst e; exact ⟨hp, fun _ x => x, by simp⟩
    · cases h
  | _ :: _, [], _, _, h, _, _ => by simp [evalPassLoop] at h
  | a :: args, q :: par, regs, R, h, hn, hp => by
    simp only [evalPassLoop] at h
    cases a with
    | none => exact absurd (List.mem_cons_self ..) hn
    | some r =>
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨R1, hm, h⟩ := h
      unfold move at hm
      obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp hm
      cases u with
      | none => exact absurd hu (hp r)
      | some v =>
        obtain ⟨a1, a2, a3⟩ := evalPassLoop_ok args par _ R h (fun m => hn (List.mem_cons_of_mem _ m)) (pure_put hp)
        refine ⟨a1, fun r' hr => a2 r' (present_put hr), fun q' hq => ?_⟩
        rcases List.mem_cons.mp hq with rfl | hq
        · exact a2 _ (by unfold Present; simp [HoonMap.get_put])
        · exact a3 q' hq

/-! ## The invariant of a path from the entry -/

/-- Before the pass of a block: the arguments pending are in the file and
none is `~`. -/
def Phase1 (b : Blob) (i : Nat) (y : Cfg σ Map) : Prop :=
  y.b.par = b.par ∧ i = 0 ∧ (∀ k, some k ∈ y.params → Present y.regs k) ∧ Option.none ∉ y.params

/-- In the body of a block, at op `i`: its parameters and what its first `i`
ops wrote are in the file, and a register a `%cel` among them checked, with
no write since, holds a cell. -/
def Phase2 (b : Blob) (i : Nat) (y : Cfg σ Map) : Prop :=
  y.b.par = [] ∧ y.params = [] ∧ i ≤ b.body.length ∧ (∀ r ∈ b.par, Present y.regs r) ∧
  (∀ r ∈ (b.body.take i).filterMap aliasDst, Present y.regs r) ∧
  (∀ j s, j < i → b.body[j]? = some (Pole.cel s) →
    (∀ l, j < l → l < i → ∀ q, b.body[l]? = some q → aliasDst q ≠ some s) → ∃ x z, read s y.regs = some (C x z))

/-- **The invariant**: a configuration at op `i` of block `b`, reached
along the block path `p`, with no poison, and with every register below
`n` or defined by a block of `p` in the file. -/
def EInv (n : Nat) (bl : Map Blob) (y : Cfg σ Map) : Prop :=
  ∃ p b i, BPath bl (y.lab :: p) ∧ HoonMap.get bl y.lab = some b ∧ y.b.fin = b.fin ∧ y.b.body = b.body.drop i ∧
    Pure y.regs ∧ (∀ r, (r < n ∨ ∃ o' ∈ p, ∃ b', HoonMap.get bl o' = some b' ∧ r ∈ blockDefs b') → Present y.regs r) ∧
    (Phase1 b i y ∨ Phase2 b i y)

theorem phase2_of {b : Blob} {i : Nat} {y : Cfg σ Map} (h : Phase1 b i y ∨ Phase2 b i y) (hp : y.params = [])
    (hq : y.b.par = []) : Phase2 b i y := by
  rcases h with ⟨e, rfl, -, -⟩ | h
  · rw [hq] at e
    exact ⟨hq, hp, Nat.zero_le _, by rw [← e]; simp, by simp, fun j _ hj => absurd hj (Nat.not_lt_zero _)⟩
  · exact h

/-- **A read at op `i` (or at the end) is of a register in the file.** -/
theorem reads_present {n : Nat} {bl : Map Blob} (hD : DefFirst bl) (hR : Compiler.ReadsIn n bl)
    {y : Cfg σ Map} {p : List Nat} {b : Blob} {i : Nat} (hB : BPath bl (y.lab :: p)) (hb : HoonMap.get bl y.lab = some b)
    (hpast : ∀ r, (r < n ∨ ∃ o' ∈ p, ∃ b', HoonMap.get bl o' = some b' ∧ r ∈ blockDefs b') → Present y.regs r)
    (h2 : Phase2 b i y) {r : Nat} (hr : ReadAt b i r) : Present y.regs r := by
  rcases hR y.lab b i r (bpath_reach hB rfl) hb hr with hd | hn
  · rcases hD y.lab p b hB hb i r hr hd with h | h | h
    · exact h2.2.2.2.1 r h
    · exact h2.2.2.2.2.1 r h
    · exact hpast r (Or.inr h)
  · exact hpast r (Or.inl hn)

theorem einv_entry {n : Nat} {bl : Map Blob} {b0 : Blob} (hb0 : HoonMap.get bl 0 = some b0) {vals : List Noun}
    (hn : n ≤ vals.length) (st : σ) (t : Trace) :
    EInv n bl (⟨0, b0, [], regsOf vals, t, st⟩ : Cfg σ Map) := by
  refine ⟨[], b0, 0, BPath.start, hb0, rfl, by simp, pure_regsOf vals, fun r hr => ?_,
    Or.inl ⟨rfl, rfl, by simp, by simp⟩⟩
  rcases hr with hr | ⟨_, h, _⟩
  · exact present_regsOf (by omega)
  · cases h


/-- **`EInv` is kept by every step.** -/
theorem einv_step {lib : Lib} {O : Oracle σ} {c : Straight Map} {gul : Noun} {n : Nat}
    (hD : DefFirst c.blocks) (hR : Compiler.ReadsIn n c.blocks) (hP : NoPoison c.blocks)
    {x y : Cfg σ Map} {e : List (Nat × Nat)} (hs : Step lib O c gul x e y) (hx : EInv n c.blocks x) :
    EInv n c.blocks y := by
  obtain ⟨p, b, i, hB, hb, hfin, hbody, hpure, hpast, hph⟩ := hx
  cases hs with
  | @pass R hne hR' =>
    rcases hph with ⟨hpar, rfl, hargs, hnone⟩ | ⟨h1, h2, _⟩
    · unfold evalPass at hR'
      split at hR'
      · obtain ⟨a1, a2, a3⟩ := evalPassLoop_ok _ _ _ _ hR' hnone hpure
        refine ⟨p, b, 0, hB, hb, hfin, hbody, a1, fun r hr => a2 r (hpast r hr), Or.inr ⟨rfl, rfl, Nat.zero_le _,
          fun r hr => a3 r (by rw [hpar]; exact hr), by simp, fun j _ hj => absurd hj (Nat.not_lt_zero _)⟩⟩
      · cases hR'
    · exact absurd (by simp [h1, h2] at hne) id
  | @op p0 rest n' R t' st' hp0 hq hbo hpole =>
    have h2 := phase2_of hph hp0 hq
    obtain ⟨-, -, hle, hpar, hdefs, hcel⟩ := h2
    rw [hbody] at hbo
    have hget : b.body[i]? = some p0 := by rw [← List.head?_drop, hbo]; rfl
    have hrest : rest = b.body.drop (i + 1) := by
      rw [← List.drop_drop, hbo]; rfl
    have hlt : i < b.body.length := by
      rcases Nat.lt_or_ge i b.body.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hget; cases hget
    obtain ⟨hkeep, hdst⟩ := execPole_zero hpole
    have hdp : ∀ d, aliasDst p0 = some d → Present R d := by
      intro d hd
      rcases hdst d hd with ⟨v, hv⟩ | ⟨s, -, hv, hs⟩
      · unfold Present; rw [hv]; rfl
      · unfold Present; rw [hv]; exact hs
    have mono : ∀ r, Present x.regs r → Present R r := by
      intro r hr
      by_cases e : aliasDst p0 = some r
      · exact hdp r e
      · unfold Present at *; rw [hkeep r e]; exact hr
    have hpure' : Pure R := by
      intro r
      by_cases e : aliasDst p0 = some r
      · rcases hdst r e with ⟨v, hv⟩ | ⟨s, -, hv, -⟩
        · rw [hv]; simp
        · rw [hv]; exact hpure s
      · rw [hkeep r e]; exact hpure r
    refine ⟨p, b, i + 1, hB, hb, hfin, hrest, hpure', fun r hr => mono r (hpast r hr), Or.inr ⟨hq, hp0, hlt,
      fun r hr => mono r (hpar r hr), fun r hr => ?_, fun j s hj hjc hw => ?_⟩⟩
    · rw [List.take_add_one, List.filterMap_append, hget] at hr
      rcases List.mem_append.mp hr with hr | hr
      · exact mono r (hdefs r hr)
      · simp only [Option.toList_some, List.filterMap_cons, List.filterMap_nil] at hr
        revert hr; cases e : aliasDst p0 with
        | none => simp
        | some d => simp only [List.mem_singleton]; rintro rfl; exact hdp _ e
    · have keep_s : read s R = read s x.regs := by
        have : aliasDst p0 ≠ some s := by
          rcases Nat.lt_or_ge j i with h | h
          · exact hw i h (Nat.lt_succ_self i) p0 hget
          · have : j = i := by omega
            subst this; rw [hget] at hjc; cases hjc; simp [aliasDst]
        unfold read; rw [hkeep s this]
      rw [keep_s]
      rcases Nat.lt_or_ge j i with h | h
      · exact hcel j s h hjc fun l hl1 hl2 q hq => hw l hl1 (Nat.lt_succ_of_lt hl2) q hq
      · have : j = i := by omega
        subst this; rw [hget] at hjc; cases hjc
        exact execPole_cel hpole
  | @jump j b' hp0 hq hbo ht hb' =>
    have h2 := phase2_of hph hp0 hq
    obtain ⟨-, -, hle, hpar, hdefs, -⟩ := h2
    rw [hbody] at hbo
    have hi : i = b.body.length := by
      have := List.drop_eq_nil_iff.mp hbo; omega
    have hj : j ∈ getJmps b.fin := by rw [← hfin]; exact taken_mem ht
    refine ⟨x.lab :: p, b', 0, BPath.step hB hb hj, hb', rfl, rfl, hpure, fun r hr => ?_, Or.inl ⟨rfl, rfl,
      fun k hk => ?_, hP x.lab b j (bpath_reach hB rfl) hb hj⟩⟩
    · rcases hr with hr | ⟨o', ho', b2, hb2, hr⟩
      · exact hpast r (Or.inl hr)
      · rcases List.mem_cons.mp ho' with rfl | ho'
        · rw [hb] at hb2; cases hb2
          unfold blockDefs at hr
          rcases List.mem_append.mp hr with hr | hr
          · exact hpar r hr
          · exact hdefs r (by rw [hi, List.take_length]; exact hr)
        · exact hpast r (Or.inr ⟨o', ho', b2, hb2, hr⟩)
    · exact reads_present hD hR hB hb hpast (phase2_of hph hp0 hq) (Or.inr ⟨hi, jmpArgs_sub hj hk⟩)

theorem einv_steps {lib : Lib} {O : Oracle σ} {c : Straight Map} {gul : Noun} {n : Nat}
    (hD : DefFirst c.blocks) (hR : Compiler.ReadsIn n c.blocks) (hP : NoPoison c.blocks)
    {x y : Cfg σ Map} {es : List (Nat × Nat)} (hs : Steps lib O c gul x es y) (hx : EInv n c.blocks x) :
    EInv n c.blocks y := by
  induction hs with
  | refl => exact hx
  | step s _ ih => exact ih (einv_step hD hR hP s hx)

/-! ## `EntryOK` -/

/-- **`EntryOK` from the four static facts**: `DefFirst`, `ReadsIn` at the
argument count, `NoPoison`, `CelGuard`, and at least `nargs` entry values;
for every oracle, scry gate, state and trace. -/
theorem entryOK_of {c : Straight Map} (hD : DefFirst c.blocks) (hR : Compiler.ReadsIn c.nargs c.blocks)
    (hP : NoPoison c.blocks) (hG : CelGuard c.blocks) {vals : List Noun} (hn : c.nargs ≤ vals.length)
    (lib : Lib) (O : Oracle σ) (gul : Noun) (st : σ) (t : Trace) : EntryOK lib O c gul st vals t := by
  have inv : ∀ es y, Path.FromEntry (lib := lib) (O := O) (c := c) (gul := gul) st vals t es y →
      EInv c.nargs c.blocks y := by
    rintro es y ⟨b0, hb0, hs⟩
    exact einv_steps hD hR hP hs (einv_entry hb0 hn st t)
  -- a read of the next action is of a register in the file
  have rd : ∀ es y, Path.FromEntry (lib := lib) (O := O) (c := c) (gul := gul) st vals t es y → y.params = [] →
      y.b.par = [] → ∀ k, ((∃ p rest, y.b.body = p :: rest ∧ k ∈ aliasReads p) ∨
        (y.b.body = [] ∧ k ∈ finRegs y.b.fin)) → Present y.regs k ∧ Pure y.regs := by
    intro es y hy hp hq k hk
    obtain ⟨p, b, i, hB, hb, hfin, hbody, hpure, hpast, hph⟩ := inv es y hy
    have h2 := phase2_of hph hp hq
    refine ⟨reads_present hD hR hB hb hpast h2 ?_, hpure⟩
    rcases hk with ⟨p0, rest, hbo, hk⟩ | ⟨hbo, hk⟩
    · left; rw [← hbody, hbo]; exact hk
    · right; rw [hbody] at hbo; rw [← hfin]
      exact ⟨by have := List.drop_eq_nil_iff.mp hbo; have := h2.2.2.1; omega, hk⟩
  refine ⟨fun es y k hy hk => ?_, fun es y k hy hk => ?_, fun es y p rest hy hp hq hbo hsa => ?_⟩
  · obtain ⟨hp, hq, hk⟩ := hk
    have hk' : (∃ p rest, y.b.body = p :: rest ∧ k ∈ aliasReads p) ∨ (y.b.body = [] ∧ k ∈ finRegs y.b.fin) := by
      rcases hk with ⟨p, rest, hb, hk⟩ | ⟨hb, hk⟩
      · exact Or.inl ⟨p, rest, hb, poleReads_sub hk⟩
      · exact Or.inr ⟨hb, finReads_sub hk⟩
    obtain ⟨h1, h2⟩ := rd es y hy hp hq k hk'
    exact read_of_present h2 h1
  · obtain ⟨p, b, i, -, -, -, -, -, -, hph⟩ := inv es y hy
    rcases hph with ⟨-, -, ha, -⟩ | ⟨-, hp, -⟩
    · exact ha k hk
    · rw [hp] at hk; cases hk
  · have val : ∀ k, k ∈ aliasReads p → ∃ v, read k y.regs = some v := fun k hk => by
      obtain ⟨h1, h2⟩ := rd es y hy hp hq k (Or.inl ⟨p, rest, hbo, hk⟩)
      exact read_of_present h2 h1
    cases p with
    | imm a d => simp [execPole, localPole]
    | mov s d =>
      obtain ⟨h1, -⟩ := rd es y hy hp hq s
        (Or.inl ⟨_, rest, hbo, mem_erase_last (l := [s]) (List.mem_singleton_self s)⟩)
      unfold Present at h1
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp h1
      simp [execPole, localPole, move, hu]
    | con a b d =>
      obtain ⟨va, ha⟩ := val a (poleReads_sub (gul := gul) (p := Pole.con a b d) (by simp [poleReads]))
      obtain ⟨vb, hb⟩ := val b (poleReads_sub (gul := gul) (p := Pole.con a b d) (by simp [poleReads]))
      simp [execPole, localPole, ha, hb]
    | hed s d =>
      obtain ⟨p', b, i, hB, hb, hfin, hbody, hpure, hpast, hph⟩ := inv es y hy
      obtain ⟨-, -, -, -, -, hcel⟩ := phase2_of hph hp hq
      have hget : b.body[i]? = some (Pole.hed s d) := by rw [← List.head?_drop, ← hbody, hbo]; rfl
      obtain ⟨j, hj, hjc, hw⟩ := hG y.lab b i _ s (bpath_reach hB rfl) hb hget rfl
      obtain ⟨x, z, hxz⟩ := hcel j s hj hjc hw
      simp [execPole, localPole, hxz]
    | tal s d =>
      obtain ⟨p', b, i, hB, hb, hfin, hbody, hpure, hpast, hph⟩ := inv es y hy
      obtain ⟨-, -, -, -, -, hcel⟩ := phase2_of hph hp hq
      have hget : b.body[i]? = some (Pole.tal s d) := by rw [← List.head?_drop, ← hbody, hbo]; rfl
      obtain ⟨j, hj, hjc, hw⟩ := hG y.lab b i _ s (bpath_reach hB rfl) hb hget rfl
      obtain ⟨x, z, hxz⟩ := hcel j s hj hjc hw
      simp [execPole, localPole, hxz]
    | _ => simp [safeAssign] at hsa

end

end Glue
end SkaModel
end Formalization
