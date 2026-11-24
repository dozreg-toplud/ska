import lemmas.Ska.Opt

/-!
# Registers that hold a value where the code before holds poison

`+remove-hops` writes `0` where the code before poisons a parameter, so the
registers of the code after sit above those of the code before in the order
that puts poison below every value (`RegLe R R'`): at every register the two
maps agree, or the code before holds poison and the code after a value.  The
two maps have the same registers defined.

An op, a pass and a branch that read for real only registers holding values
in `R` do the same on `R'` (`execPole_le`, `evalPass_le`, `taken_le`,
`endOf_le`): a real read of a value is the same read in both maps, a move
copies related units, a store stores the same value.  A real read of a
poisoned register crashes the code before (`run_poison`), so on a run of the
code before that does not crash every real read reads a value
(`execPole_reads`, `taken_reads`, `endOf_reads`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock Path

variable {Map : Type → Type} [HoonMap Map]

/-- **The registers after are above the registers before**: the same unit,
or poison before and a value after. -/
def RegLe (R R' : Map (Option Noun)) : Prop :=
  ∀ k, HoonMap.get R' k = HoonMap.get R k ∨ (HoonMap.get R k = some none ∧ ∃ v, HoonMap.get R' k = some (some v))

theorem RegLe.refl (R : Map (Option Noun)) : RegLe R R := fun _ => Or.inl rfl

theorem RegLe.put {R R' : Map (Option Noun)} (h : RegLe R R') (d : Nat) (u : Option Noun) :
    RegLe (HoonMap.put R d u) (HoonMap.put R' d u) := by
  intro k; simp only [HoonMap.get_put]; split
  · exact Or.inl rfl
  · exact h k

theorem RegLe.put_poison {R R' : Map (Option Noun)} (h : RegLe R R') (d : Nat) (v : Noun) :
    RegLe (HoonMap.put R d none) (HoonMap.put R' d (some v)) := by
  intro k; simp only [HoonMap.get_put]; split
  · exact Or.inr ⟨rfl, v, rfl⟩
  · exact h k

theorem RegLe.store {R R' : Map (Option Noun)} (h : RegLe R R') (d : Nat) (v : Noun) :
    RegLe (store d v R) (store d v R') := h.put d (some v)

theorem RegLe.rd {R R' : Map (Option Noun)} (h : RegLe R R') {k : Nat} {v : Noun} (hv : read k R = some v) :
    read k R' = some v := by
  rw [read_eq_some] at hv ⊢
  rcases h k with e | ⟨e, -⟩
  · rw [e, hv]
  · rw [hv] at e; cases e

theorem RegLe.rd_eq {R R' : Map (Option Noun)} (h : RegLe R R') {k : Nat} (hv : ∃ v, read k R = some v) :
    read k R' = read k R := by
  obtain ⟨v, hv⟩ := hv; rw [hv, h.rd hv]

theorem RegLe.get_none {R R' : Map (Option Noun)} (h : RegLe R R') (k : Nat) :
    HoonMap.get R' k = none ↔ HoonMap.get R k = none := by
  rcases h k with e | ⟨e, v, e'⟩
  · rw [e]
  · rw [e, e']; simp

theorem RegLe.mapM {R R' : Map (Option Noun)} (h : RegLe R R') : ∀ (v : List Nat),
    (∀ k ∈ v, ∃ x, read k R = some x) → v.mapM (read · R') = v.mapM (read · R)
  | [], _ => rfl
  | a :: v, hv => by
    simp only [List.mapM_cons, h.rd_eq (hv a (by simp)),
      RegLe.mapM h v (fun k hk => hv k (List.mem_cons_of_mem _ hk))]

/-! ## Ops -/

section
variable {σ : Type}

/-- Related results of an op. -/
def PLe : Option (Tone × Map (Option Noun) × Trace × σ) → Option (Tone × Map (Option Noun) × Trace × σ) → Prop
  | Option.none, Option.none => True
  | some (a, R, t, s), some (a', R', t', s') => a = a' ∧ t = t' ∧ s = s' ∧ RegLe R R'
  | _, _ => False

/-- Related results of a local op. -/
def LLe : Option (Tone × Map (Option Noun) × Trace) → Option (Tone × Map (Option Noun) × Trace) → Prop
  | Option.none, Option.none => True
  | some (a, R, t), some (a', R', t') => a = a' ∧ t = t' ∧ RegLe R R'
  | _, _ => False

theorem localPole_le (lib : Lib) (gul : Noun) (p : Pole) {R R' : Map (Option Noun)} (t : Trace)
    (h : RegLe R R') (hr : ∀ k ∈ poleReads gul p, ∃ v, read k R = some v) :
    LLe (localPole lib gul p R t) (localPole lib gul p R' t) := by
  cases p with
  | imm n d => simpa [localPole, LLe] using h.store d n
  | mov s d =>
    simp only [localPole, move]
    rcases h s with e | ⟨e, v, e'⟩
    · rw [e]; cases HoonMap.get R s <;> simp [LLe, h.put]
    · rw [e, e']; simp [LLe, h.put_poison]
  | inc s d =>
    simp only [localPole, h.rd_eq (hr s (by simp [poleReads]))]
    cases e : read s R with
    | none => simp [LLe]
    | some v => cases v <;> simp [LLe, h, h.store]
  | con a b d =>
    simp only [localPole, h.rd_eq (hr a (by simp [poleReads])), h.rd_eq (hr b (by simp [poleReads]))]
    cases read a R <;> cases read b R <;> simp [LLe, h.store]
  | hed s d =>
    simp only [localPole, h.rd_eq (hr s (by simp [poleReads]))]
    cases e : read s R with
    | none => simp [LLe]
    | some v => cases v <;> simp [LLe, h.store]
  | tal s d =>
    simp only [localPole, h.rd_eq (hr s (by simp [poleReads]))]
    cases e : read s R with
    | none => simp [LLe]
    | some v => cases v <;> simp [LLe, h.store]
  | cel q =>
    simp only [localPole, h.rd_eq (hr q (by simp [poleReads]))]
    cases e : read q R with
    | none => simp [LLe]
    | some v => cases v <;> simp [LLe, h]
  | lob q =>
    simp only [localPole, h.rd_eq (hr q (by simp [poleReads]))]
    cases e : read q R with
    | none => simp [LLe]
    | some v => by_cases hv : v = A 0 ∨ v = A 1 <;> simp [LLe, h, hv]
  | equ a b =>
    simp only [localPole, h.rd_eq (hr a (by simp [poleReads])), h.rd_eq (hr b (by simp [poleReads]))]
    cases read a R <;> cases read b R <;> simp [LLe, h]
  | hsp n f => simp [localPole, LLe, h]
  | hse n f => simp [localPole, LLe, h]
  | hdp n q f =>
    simp only [localPole]
    split
    · rename_i hs
      rw [h.rd_eq (hr q (by simp [poleReads, hs]))]
      cases read q R <;> simp [LLe, h]
    · simp [LLe, h]
  | hde n q f =>
    simp only [localPole]
    split
    · cases popTrace t <;> simp [LLe, h]
    · simp [LLe, h]
  | hmp a v f =>
    simp only [localPole, h.mapM v (fun k hk => hr k (by simpa [poleReads] using hk))]
    cases v.mapM (read · R) <;> simp [LLe, h]
  | hme a v f =>
    simp only [localPole]
    cases popTrace t <;> simp [LLe, h]
  | hcp n f => simp [localPole, LLe, h]
  | hce n f =>
    simp only [localPole]
    cases popTrace t <;> simp [LLe, h]
  | spy e q d =>
    simp only [localPole]
    split
    · simp [LLe, h]
    · rename_i hg
      rw [h.rd_eq (hr e (by simp [poleReads, hg])), h.rd_eq (hr q (by simp [poleReads, hg]))]
      cases read e R <;> cases read q R <;> simp only [Option.bind_none, Option.bind_some, LLe]
      rename_i ref pax
      cases lib.slam gul (C ref pax) <;> simp only [Option.bind_none, Option.bind_some, LLe]
      rename_i res
      cases scryDecode res <;> simp only [Option.bind_none, Option.bind_some, LLe]
      rename_i dr
      cases dr <;> simp [LLe, h, h.store]
  | nok u f d => simp [localPole, LLe]
  | cal a v d => simp [localPole, LLe]
  | caf a v d n => simp [localPole, LLe]
  | cam a v d k => simp [localPole, LLe]
  | csl a s d => simp [localPole, LLe]
  | csf a s d n => simp [localPole, LLe]
  | csm a s d k => simp [localPole, LLe]

theorem afterCall_le (st : σ) {R R' : Map (Option Noun)} (t : Trace) (d : Nat) (h : RegLe R R') (ton : Tone) :
    PLe (afterCall st R t d ton) (afterCall st R' t d ton) := by
  cases ton <;> simp [afterCall, PLe, h, h.store]

/-- **An op whose real reads read values in `R` does the same on `R'`.** -/
theorem execPole_le (lib : Lib) (O : Oracle σ) (gul : Noun) (st : σ) (p : Pole) {R R' : Map (Option Noun)}
    (t : Trace) (h : RegLe R R') (hr : ∀ k ∈ poleReads gul p, ∃ v, read k R = some v) :
    PLe (execPole lib O gul st p R t) (execPole lib O gul st p R' t) := by
  have hloc : PLe ((localPole lib gul p R t).map fun (ton, regs', trace') => (ton, regs', trace', st))
      ((localPole lib gul p R' t).map fun (ton, regs', trace') => (ton, regs', trace', st)) := by
    have := localPole_le lib gul p t h hr
    revert this
    cases localPole lib gul p R t <;> cases localPole lib gul p R' t <;> simp [LLe, PLe]
  have call : ∀ (v : List Nat) (a : Bell) (mono : Bool) (d : Nat), (∀ k ∈ v, ∃ x, read k R = some x) →
      PLe ((v.mapM (read · R)).bind fun vs =>
          (O.call st a mono vs t gul).bind fun (ton, st') => afterCall st' R t d ton)
        ((v.mapM (read · R')).bind fun vs =>
          (O.call st a mono vs t gul).bind fun (ton, st') => afterCall st' R' t d ton) := by
    intro v a mono d hv
    rw [h.mapM v hv]
    cases v.mapM (read · R) <;> simp only [Option.bind_none, Option.bind_some, PLe]
    rename_i vs
    cases O.call st a mono vs t gul <;> simp only [Option.bind_none, Option.bind_some, PLe]
    exact afterCall_le _ t d h _
  have call1 : ∀ (s : Nat) (a : Bell) (d : Nat), (∃ x, read s R = some x) →
      PLe ((read s R).bind fun vs =>
          (O.call st a true [vs] t gul).bind fun (ton, st') => afterCall st' R t d ton)
        ((read s R').bind fun vs =>
          (O.call st a true [vs] t gul).bind fun (ton, st') => afterCall st' R' t d ton) := by
    intro s a d hv
    rw [h.rd_eq hv]
    cases read s R <;> simp only [Option.bind_none, Option.bind_some, PLe]
    rename_i vs
    cases O.call st a true [vs] t gul <;> simp only [Option.bind_none, Option.bind_some, PLe]
    exact afterCall_le _ t d h _
  cases p with
  | nok u f d =>
    simp only [execPole, h.rd_eq (hr u (by simp [poleReads])), h.rd_eq (hr f (by simp [poleReads]))]
    cases read u R <;> cases read f R <;> simp only [Option.bind_none, Option.bind_some, PLe]
    rename_i vu vf
    cases O.nok st vu vf gul <;> simp only [Option.bind_none, Option.bind_some, PLe]
    rename_i r; obtain ⟨ton, st'⟩ := r
    cases ton <;> simp [PLe, h, h.store]
  | cal a v d => exact call v a false d (fun k hk => hr k (by simpa [poleReads] using hk))
  | caf a v d n => exact call v a false d (fun k hk => hr k (by simpa [poleReads] using hk))
  | cam a v d k => exact call v a false d (fun k hk => hr k (by simpa [poleReads] using hk))
  | csl a s d => exact call1 s a d (hr s (by simp [poleReads]))
  | csf a s d n => exact call1 s a d (hr s (by simp [poleReads]))
  | csm a s d k => exact call1 s a d (hr s (by simp [poleReads]))
  | _ => exact hloc

/-- An op that does not crash read values for real. -/
theorem execPole_reads {lib : Lib} {O : Oracle σ} {gul : Noun} {st : σ} {p : Pole} {R : Map (Option Noun)}
    {t : Trace} (h : (execPole lib O gul st p R t).isSome) : ∀ k ∈ poleReads gul p, ∃ v, read k R = some v := by
  intro k hk
  cases e : read k R with
  | some v => exact ⟨v, rfl⟩
  | none => rw [execPole_poison hk e] at h; cases h

/-! ## Passes and branches -/

/-- Related optional maps. -/
def OLe : Option (Map (Option Noun)) → Option (Map (Option Noun)) → Prop
  | Option.none, Option.none => True
  | some a, some b => RegLe a b
  | _, _ => False

theorem evalPassLoop_le : ∀ (args : List (Option Nat)) (par : List Nat) {R R' : Map (Option Noun)},
    RegLe R R' → OLe (evalPassLoop args par R) (evalPassLoop args par R')
  | [], par, R, R', h => by cases par <;> simp [evalPassLoop, OLe, h]
  | a :: args, [], _, _, h => by simp [evalPassLoop, OLe]
  | a :: args, p :: par, R, R', h => by
      cases a with
      | none =>
        simp only [evalPassLoop, Option.bind_some]
        exact evalPassLoop_le args par (h.put p none)
      | some r =>
        simp only [evalPassLoop, move]
        rcases h r with e | ⟨e, v, e'⟩
        · rw [e]
          cases HoonMap.get R r with
          | none => simp [OLe]
          | some u => simpa using evalPassLoop_le args par (h.put p u)
        · rw [e, e']; simpa using evalPassLoop_le args par (h.put_poison p v)

/-- **A pass does the same on related registers.** -/
theorem evalPass_le (args : List (Option Nat)) (par : List Nat) {R R' : Map (Option Noun)} (h : RegLe R R') :
    OLe (evalPass args par R) (evalPass args par R') := by
  unfold evalPass; split
  · exact evalPassLoop_le args par h
  · trivial

theorem OLe.fwd {a b : Option (Map (Option Noun))} (h : OLe a b) {R : Map (Option Noun)} (ha : a = some R) :
    ∃ R', b = some R' ∧ RegLe R R' := by
  subst ha; cases b with
  | none => cases h
  | some R' => exact ⟨R', rfl, h⟩

theorem OLe.bwd {a b : Option (Map (Option Noun))} (h : OLe a b) {R' : Map (Option Noun)} (hb : b = some R') :
    ∃ R, a = some R ∧ RegLe R R' := by
  subst hb; cases a with
  | none => cases h
  | some R => exact ⟨R, rfl, h⟩

theorem PLe.fwd {a b : Option (Tone × Map (Option Noun) × Trace × σ)} (h : PLe a b) {ton : Tone}
    {R : Map (Option Noun)} {t : Trace} {s : σ} (ha : a = some (ton, R, t, s)) :
    ∃ R', b = some (ton, R', t, s) ∧ RegLe R R' := by
  subst ha
  match b, h with
  | some (a', R', t', s'), ⟨e1, e2, e3, e4⟩ => subst e1 e2 e3; exact ⟨R', rfl, e4⟩

theorem PLe.bwd {a b : Option (Tone × Map (Option Noun) × Trace × σ)} (h : PLe a b) {ton : Tone}
    {R' : Map (Option Noun)} {t : Trace} {s : σ} (hb : b = some (ton, R', t, s)) :
    ∃ R, a = some (ton, R, t, s) ∧ RegLe R R' := by
  subst hb
  match a, h with
  | some (a', R, t', s'), ⟨e1, e2, e3, e4⟩ => subst e1 e2 e3; exact ⟨R, rfl, e4⟩

/-- **A branch whose real reads read values takes the same jump.** -/
theorem taken_le {R R' : Map (Option Noun)} (h : RegLe R R') (f : Termin)
    (hr : ∀ k ∈ finReads f, ∃ v, read k R = some v) : taken R' f = taken R f := by
  cases f with
  | clq s z o => simp only [taken, h.rd_eq (hr s (by simp [finReads]))]
  | eqq l r z o =>
    simp only [taken, h.rd_eq (hr l (by simp [finReads])), h.rd_eq (hr r (by simp [finReads]))]
  | brn s z o => simp only [taken, h.rd_eq (hr s (by simp [finReads]))]
  | brz s z o => simp only [taken, h.rd_eq (hr s (by simp [finReads]))]
  | lti n s z o => simp only [taken, h.rd_eq (hr s (by simp [finReads]))]
  | _ => rfl

/-- A branch that takes a jump read values for real. -/
theorem taken_reads {R : Map (Option Noun)} {f : Termin} {j : Jmp} (h : taken R f = some j) :
    ∀ k ∈ finReads f, ∃ v, read k R = some v := by
  intro k hk
  cases e : read k R with
  | some v => exact ⟨v, rfl⟩
  | none =>
    exfalso
    cases f <;> simp only [finReads, List.mem_cons, List.not_mem_nil, or_false] at hk <;>
      simp [taken] at h
    all_goals first
      | (subst hk; simp [e] at h; done)
      | (rcases hk with rfl | rfl <;> simp [e] at h <;> obtain ⟨_, _, _, _, _⟩ := h <;> simp_all; done)
      | skip
    all_goals (rcases hk with rfl | rfl <;> simp_all)

/-- The jump a branch takes is one of its jumps. -/
theorem taken_mem {R : Map (Option Noun)} {f : Termin} {j : Jmp} (h : taken R f = some j) : j ∈ getJmps f := by
  cases f with
  | lti n s z o =>
    simp only [taken] at h
    obtain ⟨v, -, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [getJmps]
    exact (show ∀ (c : Bool), (if c = true then z else o) ∈ [z, o] from fun c => by cases c <;> simp) _
  | clq s z o =>
    simp only [taken] at h
    obtain ⟨v, -, rfl⟩ := Option.map_eq_some_iff.mp h; split <;> simp [getJmps]
  | eqq l r z o =>
    simp only [taken] at h
    obtain ⟨v, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨w, -, rfl⟩ := Option.map_eq_some_iff.mp h; split <;> simp [getJmps]
  | brn s z o =>
    simp only [taken] at h
    obtain ⟨v, -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h; simp [getJmps]
    · split at h
      · cases h; simp [getJmps]
      · cases h
  | brz s z o =>
    simp only [taken] at h
    obtain ⟨v, -, rfl⟩ := Option.map_eq_some_iff.mp h; split <;> simp [getJmps]
  | hop t => simp only [taken, Option.some.injEq] at h; subst h; simp [getJmps]
  | _ => simp [taken] at h

variable {lib : Lib} {O : Oracle σ} {gul : Noun}

/-- An end that returns read values for real. -/
theorem endOf_reads {x : Cfg σ Map} {r : Tone × σ} (h : endOf lib O gul x = some r) :
    ∀ k, ReadsAt gul x k → ∃ v, read k x.regs = some v := by
  intro k hk
  cases e : read k x.regs with
  | some v => exact ⟨v, rfl⟩
  | none =>
    have h1 := endOf_run (c := (⟨NeedOrd.this, 0, HoonMap.empty⟩ : Straight Map)) h
    rw [run_poison hk e] at h1; cases h1

/-- **An end whose real reads read values is the same on related registers**,
when the next action is the same. -/
theorem endOf_le {x x' : Cfg σ Map} (h : RegLe x.regs x'.regs) (hr : ∀ k, ReadsAt gul x k → ∃ v, read k x.regs = some v)
    (hp : x'.params = x.params) (hq : x'.b.par = x.b.par) (ht : x'.t = x.t) (hs : x'.st = x.st)
    (hb : (x.b.body = [] ∧ x'.b.body = [] ∧ x'.b.fin = x.b.fin) ∨
      ∃ p rest rest', x.b.body = p :: rest ∧ x'.b.body = p :: rest') :
    endOf lib O gul x' = endOf lib O gul x := by
  obtain ⟨lab, ⟨par, body, fin⟩, params, R, t, st⟩ := x
  obtain ⟨lab', ⟨par', body', fin'⟩, params', R', t', st'⟩ := x'
  simp only at h hp hq ht hs hb hr ⊢
  subst hp hq ht hs
  unfold endOf
  simp only
  split
  · rfl
  rename_i hne
  simp only [not_or, ne_eq, Decidable.not_not] at hne
  obtain ⟨rfl, rfl⟩ := hne
  rcases hb with ⟨rfl, rfl, rfl⟩ | ⟨p, rest, rest', rfl, rfl⟩
  · have hr' : ∀ k ∈ finReads fin', ∃ v, read k R = some v := fun k hk => hr k ⟨rfl, rfl, Or.inr ⟨rfl, hk⟩⟩
    cases fin' with
    | brn s z o => simp only [h.rd_eq (hr' s (by simp [finReads]))]
    | jmp a v => simp only [h.mapM v (fun k hk => hr' k (by simpa [finReads] using hk))]
    | jmf a v n => simp only [h.mapM v (fun k hk => hr' k (by simpa [finReads] using hk))]
    | jsp a s => simp only [h.rd_eq (hr' s (by simp [finReads]))]
    | jsf a s n => simp only [h.rd_eq (hr' s (by simp [finReads]))]
    | don s => simp only [h.rd_eq (hr' s (by simp [finReads]))]
    | _ => rfl
  · have hp' := execPole_le lib O gul st' p t' h (fun k hk => hr k ⟨rfl, rfl, Or.inl ⟨p, rest, rfl, hk⟩⟩)
    simp only
    revert hp'
    cases execPole lib O gul st' p R t' <;> cases execPole lib O gul st' p R' t'
    · simp
    · simp [PLe]
    · simp [PLe]
    · rename_i a b
      obtain ⟨ta, Ra, tra, sa⟩ := a
      obtain ⟨tb, Rb, trb, sb⟩ := b
      simp only [PLe]
      rintro ⟨rfl, rfl, rfl, -⟩
      cases ta <;> rfl

end

end Opt
end SkaModel
end Formalization
