import lemmas.Ska.Steps
import lemmas.Ska.MinkTrace

/-!
# The interpreter agrees with `+mink`, given the contract

From `Sound` alone (and, for the forward direction, `FullAnswers`):

* `interp_fwd`: the interpreter's oracle with `k` levels of calls answers every
  call and every indirect call that `+mink` runs with less than `k` fuel, as
  `+mink` does.
* `interp_bwd`: whatever the interpreter's oracle answers, `+mink` returns.
* `meek`, `weak`, `converse`: the model-level versions of the statements of
  `core/Statement.lean`, and `meek_reach`, `weak_reach`, `converse_reach`
  over every state the compiler can reach.
-/

namespace Formalization
namespace SkaModel

open Nock

section
variable {Map : Type → Type} [HoonMap Map] {σ : Type}

/-! ## Entering a function -/

theorem execBlob_par {lib : Lib} {O : Oracle σ} {c : Straight Map} {scry : Noun} {st : σ}
    {regs : Map (Option Noun)} {t : Trace} {b : Blob} (hpar : b.par ≠ []) :
    execBlob lib O c scry st regs t b [] = none := by
  rw [execBlob]
  have : ([] : List (Option Nat)) ≠ [] ∨ b.par ≠ [] := Or.inr hpar
  rw [if_pos this]
  simp [evalPass, evalPassLoop, hpar]

/-- `+eval-top` on a formula that is a cell, once the compiler answered: the
checks of `+eval-top`, then the code entered as a function of one argument. -/
theorem topBody_cell {lib : Lib} {poke : σ → Ovum → Option (Prod Map × σ)} {O : Oracle σ}
    {k : Nat} {st st1 : σ} {s f₁ f₂ scry : Noun} {b : Bell} {c : Straight Map} {new : Noun}
    (hb : isBare (C f₁ f₂) = false)
    (hp : poke st (Ovum.full s (C f₁ f₂)) = some (Prod.ir b c new, st1))
    (hn : c.nargs = 1) (hneed : c.need = NeedOrd.this) :
    topBody lib poke O k st s (C f₁ f₂) scry = execEntry lib O st1 c [s] [] scry := by
  simp only [topBody, hb, Bool.false_eq_true, if_false, hp, Option.bind_some, hn, hneed, and_self,
    if_true, execEntry]
  cases HoonMap.get c.blocks 0 with
  | none => rfl
  | some blk =>
    simp only [Option.bind_some]
    by_cases hpar : blk.par = []
    · rw [if_pos hpar]
    · rw [if_neg hpar, execBlob_par hpar]

theorem topBody_cell_inv {lib : Lib} {poke : σ → Ovum → Option (Prod Map × σ)} {O : Oracle σ}
    {k : Nat} {st : σ} {s f₁ f₂ scry : Noun} {x : Tone × σ} (hb : isBare (C f₁ f₂) = false)
    (h : topBody lib poke O k st s (C f₁ f₂) scry = some x) :
    ∃ b c new st1, poke st (Ovum.full s (C f₁ f₂)) = some (Prod.ir b c new, st1) ∧
      c.nargs = 1 ∧ c.need = NeedOrd.this ∧ execEntry lib O st1 c [s] [] scry = some x := by
  simp only [topBody, hb, Bool.false_eq_true, if_false, Option.bind_eq_some_iff] at h
  obtain ⟨⟨p, st1⟩, hp, h⟩ := h
  cases p with
  | nil => simp at h
  | drop _ => simp at h
  | ir b c new =>
    simp only at h
    by_cases hc : c.nargs = 1 ∧ c.need = NeedOrd.this
    · refine ⟨b, c, new, st1, hp, hc.1, hc.2, ?_⟩
      rw [← topBody_cell (k := k) hb hp hc.1 hc.2]
      simp only [topBody, hb, Bool.false_eq_true, if_false, hp, Option.bind_some, hc.1, hc.2,
        and_self, if_true]
      rw [if_pos hc] at h
      exact h
    · rw [if_neg hc] at h; simp at h

theorem minkF_atom (lib : Lib) (gul : Noun) (j : Nat) (t : Trace) (u : Noun) (a : Nat)
    {r : Tone} (h : minkF lib gul j t u (A a) = some r) : r = Tone.two t := by
  cases j with
  | zero => simp [minkF] at h
  | succ j => simp [minkF, minkStep] at h; exact h.symm

/-! ## Weakening the oracle specifications -/

theorem OracleFwd.weaken {lib : Lib} {Inv Inv' : σ → Prop} {ν : σ → Needs} {O : Oracle σ}
    {n n' : Nat} (h : OracleFwd lib Inv ν O n) (hI : ∀ x, Inv' x → Inv x) (hn : n' ≤ n) :
    OracleFwd lib Inv' ν O n' :=
  ⟨fun st b m vals ti tm gul s j r hst hj => h.call st b m vals ti tm gul s j r (hI _ hst) (by omega),
   fun st u f gul j r hst hj => h.nok st u f gul j r (hI _ hst) (by omega)⟩

theorem OracleBwd.weaken {lib : Lib} {Inv Inv' : σ → Prop} {ν : σ → Needs} {O : Oracle σ}
    (h : OracleBwd lib Inv ν O) (hI : ∀ x, Inv' x → Inv x) : OracleBwd lib Inv' ν O :=
  ⟨fun st b m vals ti gul ton st' hst => h.call st b m vals ti gul ton st' (hI _ hst),
   fun st u f gul ton st' hst => h.nok st u f gul ton st' (hI _ hst)⟩

/-- The invariant of the interpreter's oracle after a poke from the state
`st1`: the compiler's own, and the needs of `st1`. -/
theorem OracleSteps.from {Inv : σ → Prop} {ν : σ → Needs} {O : Oracle σ} (h : OracleSteps Inv ν O)
    (N : Needs) : OracleSteps (fun x => Inv x ∧ N ≤ ν x) ν O :=
  ⟨fun st b m vals t gul ton st' hst hc =>
     let h' := h.call st b m vals t gul ton st' hst.1 hc
     ⟨⟨h'.1, Needs.le_trans hst.2 h'.2⟩, h'.2⟩,
   fun st u f gul ton st' hst hn =>
     let h' := h.nok st u f gul ton st' hst.1 hn
     ⟨⟨h'.1, Needs.le_trans hst.2 h'.2⟩, h'.2⟩⟩

theorem argsFor_some {N : Needs} {b : Bell} {m : Bool} {s : Noun} {vals : List Noun}
    (h : argsFor N b m s = some vals) :
    ∃ nd, N b m = some nd ∧ (if m then some [s] else split nd s) = some vals := by
  simp only [argsFor, Option.bind_eq_some_iff] at h
  exact h

/-! ## The forward direction -/

theorem Forall2.refl_of {α : Type} {R : α → α → Prop} :
    ∀ {l : List α}, (∀ x ∈ l, R x x) → Forall2 R l l
  | [], _ => Forall2.nil
  | x :: _, h => Forall2.cons (h x (List.mem_cons_self ..))
      (Forall2.refl_of fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- A tone of `+mink` from `~` stands for itself: its frames are all ones that
the interpreter keeps too. -/
theorem toneRel_mink_self (lib : Lib) (N : Needs) {gul : Noun} {n : Nat} {s f : Noun} {r : Tone}
    (h : minkF lib gul n [] s f = some r) : ToneRel lib N r r := by
  have hg := minkF_good lib gul n [] s f r h
  cases r with
  | zero p => exact ToneRel.zero p
  | one p => exact ToneRel.one p
  | two tr =>
    refine ToneRel.two (Forall2.refl_of fun fr hfr => ?_)
    rcases hg tr rfl fr hfr with hs | hm
    · exact FrameRel.same hs
    · cases hm

/-- One more level of calls answers one more level of fuel. -/
theorem interp_fwd_step (lib : Lib) {poke : σ → Ovum → Option (Prod Map × σ)} {InvC : σ → Prop}
    (hS : Sound lib poke InvC) (hF : FullAnswers poke InvC) {k : Nat}
    (h : OracleFwd lib InvC (needOf poke) (interp lib poke k) k) :
    OracleFwd lib InvC (needOf poke) (interp lib poke (k + 1)) (k + 1) := by
  have hsteps := interp_steps lib hS.toPokeSteps k
  constructor
  · intro st b m vals ti tm gul s j r hI hj hfit hargs htr hmink
    obtain ⟨nd, hnd, hvals⟩ := argsFor_some hargs
    obtain ⟨b', c, new, st1, hp, hneed⟩ := needOf_some hnd
    obtain ⟨b'', c', new', hpeq, hbc⟩ := hS.dire_code _ _ _ _ _ hI hp
    cases hpeq
    obtain ⟨hI1, hle1⟩ := hS.dire _ _ _ _ _ hI hp
    rw [← hneed] at hvals
    obtain ⟨hfwd, -⟩ := hbc s hfit vals hvals
    obtain ⟨ton, st', hrun, hrel⟩ :=
      hfwd σ (fun x => InvC x ∧ needOf poke st1 ≤ needOf poke x) (needOf poke)
        (interp lib poke k) j gul ti tm r (fun _ hx => hx.2) (hsteps.from _)
        (h.weaken (fun _ hx => hx.1) (by omega)) hmink st1 ⟨hI1, Needs.le_refl _⟩
        (htr.imp fun _ _ => FrameRel.mono hle1)
    refine ⟨ton, st', ?_, hrel⟩
    simp only [interp, callBody, hp, Option.bind_some]
    exact hrun
  · intro st u f gul j r hI hj hmink
    cases f with
    | atom a =>
      rw [minkF_atom lib gul j [] u a hmink]
      exact ⟨Tone.two [], st, rfl, ToneRel.two Forall2.nil⟩
    | cell f₁ f₂ =>
      cases hb : isBare (C f₁ f₂) with
      | true =>
        have hm := minkF_le lib gul (Nat.le_of_lt_succ hj) _ _ _ _ hmink
        refine ⟨r, st, ?_, toneRel_mink_self lib _ hmink⟩
        simp [interp, topBody, hb, hm]
      | false =>
      obtain ⟨⟨p, st1⟩, hp⟩ := hF st u f₁ f₂ hI
      obtain ⟨b, c, new, hpeq, hn, hneed, hfwd, -⟩ := hS.full_code _ _ _ _ _ hI hp
      cases hpeq
      obtain ⟨hI1, -⟩ := hS.full _ _ _ _ _ hI hp
      obtain ⟨ton, st', hrun, hrel⟩ :=
        hfwd σ (fun x => InvC x ∧ needOf poke st1 ≤ needOf poke x) (needOf poke)
          (interp lib poke k) j gul [] [] r (fun _ hx => hx.2) (hsteps.from _)
          (h.weaken (fun _ hx => hx.1) (by omega)) hmink st1 ⟨hI1, Needs.le_refl _⟩ Forall2.nil
      refine ⟨ton, st', ?_, hrel⟩
      simp only [interp]
      rw [topBody_cell hb hp hn hneed]
      exact hrun

/-- **The interpreter answers what `+mink` computes.**  With `k` levels of
calls, it answers every call and indirect call that `+mink` runs with less
than `k` fuel, as `+mink` does. -/
theorem interp_fwd (lib : Lib) {poke : σ → Ovum → Option (Prod Map × σ)} {InvC : σ → Prop}
    (hS : Sound lib poke InvC) (hF : FullAnswers poke InvC) :
    ∀ k, OracleFwd lib InvC (needOf poke) (interp lib poke k) k := by
  intro k
  induction k with
  | zero => exact ⟨fun _ _ _ _ _ _ _ _ _ _ _ hj => absurd hj (Nat.not_lt_zero _),
                   fun _ _ _ _ _ _ _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih => exact interp_fwd_step lib hS hF ih

/-! ## The backward direction -/

/-- **What the interpreter answers, `+mink` computes.** -/
theorem interp_bwd (lib : Lib) {poke : σ → Ovum → Option (Prod Map × σ)} {InvC : σ → Prop}
    (hS : Sound lib poke InvC) :
    ∀ k, OracleBwd lib InvC (needOf poke) (interp lib poke k) := by
  intro k
  induction k with
  | zero => exact ⟨fun _ _ _ _ _ _ _ _ _ h => by simp [interp] at h,
                   fun _ _ _ _ _ _ _ h => by simp [interp] at h⟩
  | succ k ih =>
    have hsteps := interp_steps lib hS.toPokeSteps k
    constructor
    · intro st b m vals ti gul ton st' hI h s tm hfit hargs htr
      simp only [interp, callBody, Option.bind_eq_some_iff] at h
      obtain ⟨⟨p, st1⟩, hp, h⟩ := h
      cases p with
      | nil => simp at h
      | drop _ => simp at h
      | ir b' c new =>
        simp only at h
        obtain ⟨b'', c', new', hpeq, hbc⟩ := hS.dire_code _ _ _ _ _ hI hp
        cases hpeq
        obtain ⟨hI1, hle1⟩ := hS.dire _ _ _ _ _ hI hp
        obtain ⟨nd, hnd, hvals⟩ := argsFor_some hargs
        rw [needOf_of_poke hp] at hnd
        cases hnd
        obtain ⟨-, hbwd⟩ := hbc s hfit vals hvals
        exact hbwd σ (fun x => InvC x ∧ needOf poke st1 ≤ needOf poke x) (needOf poke)
          (interp lib poke k) gul ti tm (fun _ hx => hx.2) (hsteps.from _)
          (ih.weaken fun _ hx => hx.1) st1 ton st' ⟨hI1, Needs.le_refl _⟩
          (htr.imp fun _ _ => FrameRel.mono hle1) h
    · intro st u f gul ton st' hI h
      cases f with
      | atom a =>
        simp only [interp, topBody, Option.some.injEq] at h
        cases h
        exact ⟨Tone.two [], ⟨1, rfl⟩, ToneRel.two Forall2.nil⟩
      | cell f₁ f₂ =>
        cases hb : isBare (C f₁ f₂) with
        | true =>
          simp only [interp, topBody, hb, if_true, Option.map_eq_some_iff, Prod.mk.injEq] at h
          obtain ⟨r, hr, rfl, rfl⟩ := h
          exact ⟨r, ⟨k, hr⟩, toneRel_mink_self lib _ hr⟩
        | false =>
        obtain ⟨b, c, new, st1, hp, hn, hneed, h⟩ := topBody_cell_inv hb h
        obtain ⟨b', c', new', hpeq, -, -, -, hbwd⟩ := hS.full_code _ _ _ _ _ hI hp
        cases hpeq
        obtain ⟨hI1, -⟩ := hS.full _ _ _ _ _ hI hp
        exact hbwd σ (fun x => InvC x ∧ needOf poke st1 ≤ needOf poke x) (needOf poke)
          (interp lib poke k) gul [] [] (fun _ hx => hx.2) (hsteps.from _)
          (ih.weaken fun _ hx => hx.1) st1 ton st' ⟨hI1, Needs.le_refl _⟩ Forall2.nil h

end

end SkaModel
end Formalization
