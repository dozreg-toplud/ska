import lemmas.Ska.CompIndirectWrap

/-!
# The indirect call at a `%next` goal: the step from the run's jump

README Gaps 12.13 (sixteenth session), the first step of the indirect call
under the parents of `FragU`.  At a goal `%next laz th` the case `%2` of
`runLC` is the one of the top (`runLC_n2_none`) with `+simple-next` the
identity and the `+kerf` block `out` hopping to `th` after the ops of
`+kern` that take the product register `pro` apart into `laz`'s registers,
instead of the block `don`.  So the code from the run's jump is: the runs of
`p` and `q` (`indirect_mid`'s `RunOKNV` of the cons `[p q]` into the `%nok`
block `o`), the `%nok` block (`goJ_nok`, the oracle at a new state), then
the block `out` at that new state.

The relation for code that calls is `GoalSemCM` (`CompCallStep.lean`), not
a property `Φ` of the code as at the top: at the top the code after the
call is the fixed `mov`, `don`, so a `Φ` naming the whole run to the end is
enough, but under a parent the code goes on at the goal's jump `th`, which
the parent's later parts own, and the parent needs to know at which state
and with which registers (`GoesC`: a state `st'` with `Inv` and bigger
needs, registers holding the goal's need and keeping `K`).  `GoalSemCM` says
that, with `+mink`'s tone for the crash cases, and the pure parts' relations
lift to it at the same state (`goalSemC_of_goalSem`).

`indirect_semN`: from the run of `[p q]` into `o` (its `GoalSem` at the
pair of the products, the oracle untouched), the `%nok` block at `o` and
what the block `out` does with a product in `pro` at every state
(`OutNext`, which `kern_spec` is to give for the block of `+kerf`), the code
from the run's jump meets `GoalSemCM` at the goal `%next laz th` for
`+mink`'s tone on the formula (`MinkN2`, so any `Annot` of `[2 p q]` but the
bare ones).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **What the block `out` does with a product in `pro`** for the goal
`%next laz th`, at every state where `Inv` holds: `GoalSemCM` at
`Tone.zero p` (go on at `th` holding `laz`'s need, or crash where `p` does
not fit). -/
def OutNext (lib : Lib) {σ : Type} (O : Oracle σ) (c : Straight Map) (gul : Noun) (Inv : σ → Prop)
    (ν : σ → Needs) (K : Nat → Prop) (pro out : Nat) (laz : Sure S) (th : Jmp) : Prop :=
  ∀ (st : σ) (regs : Map (Option Noun)) (ti tm : Trace) (p : Noun), Inv st → Forall2 (FrameRel lib (ν st)) ti tm →
    SkaModel.read pro regs = some p →
    GoalSemCM lib O c gul Inv ν K st regs ti tm (jmp0 out) (CGoal.next laz th) (Tone.zero p)

/-- **The indirect call at a `%next` goal, from the run's jump**: the code
meets `GoalSemCM` for `+mink`'s tone on the formula, given the `GoalSem` of
the run of `[p q]` into the `%nok` block `o`, that block, and `OutNext` of
the block `out`.  The registers kept (`K`) are kept by the run of `[p q]`
(`K'`) and are not `pro`. -/
theorem indirect_semN {lib : Lib} {P : Noun → Prop} {f : Noun} {p q : Nomm} (M : MinkN2 lib P f p q)
    {σ : Type} {Inv : σ → Prop} {ν : σ → Needs} {O : Oracle σ} {n : Nat} {gul : Noun}
    (hS : OracleSteps Inv ν O) (hF : OracleFwd lib Inv ν O n) {c : Straight Map}
    {a b pro o out : Nat} (hb : HoonMap.get c.blocks o = some ⟨[], [Pole.nok a b pro], Termin.hop (jmp0 out)⟩)
    {K K' : Nat → Prop} (hK : ∀ x, K x → K' x ∧ x ≠ pro)
    {laz : Sure S} {th : Jmp} (Hout : OutNext lib O c gul Inv ν K pro out laz th)
    {st : σ} (hI : Inv st) {ti tm : Trace} (htr : Forall2 (FrameRel lib (ν st)) ti tm)
    {s : Noun} (hs : P s) {r : Tone} (hm : minkF lib gul n tm s f = some r)
    {je : Jmp} {regs : Map (Option Noun)}
    (G : GoalSem lib O c gul st K' regs ti je (CGoal.next (pairSure a b : Sure S) (jmp0 o))
      (pureEval (Nomm.cons p q) s)) :
    GoalSemCM lib O c gul Inv ν K st regs ti tm je (CGoal.next laz th) r := by
  rw [pureEval_cons] at G
  rcases M.fwd hs hm with ⟨n', x, y, hlt, ex, ey, hm'⟩ | ⟨en, er⟩
  · rw [ex, ey] at G
    simp only [Option.bind_some] at G
    obtain ⟨regs', ⟨h2, h3⟩, hk', e⟩ := G.1 ⟨⟨trivial, trivial⟩, looks_empty _⟩
    have J := goJ_nok (lib := lib) (O := O) (gul := gul) hb st regs' ti h2 h3
    rw [minkF_trace] at hm'
    obtain ⟨r0, h0, rfl⟩ := Option.map_eq_some_iff.mp hm'
    obtain ⟨ton, st', hO, hrel⟩ := hF.nok st x y gul n' r0 hI hlt h0
    obtain ⟨hI', hν⟩ := hS.nok st x y gul ton st' hI hO
    rw [hO, Option.bind_some] at J
    cases hrel with
    | zero p' =>
      have J' : goJ lib O c gul st regs' ti (jmp0 o) =
          goJ lib O c gul st' (SkaModel.store pro p' regs') ti (jmp0 out) := J
      have Ho := Hout st' (SkaModel.store pro p' regs') ti tm p' hI' (frames_mono hν htr)
        (read_store_eq pro p' regs')
      show GoalSemCM lib O c gul Inv ν K st regs ti tm je (CGoal.next laz th) (Tone.zero p')
      refine ⟨fun hf => ?_, fun hf => ?_⟩
      · obtain ⟨st'', regs'', hI'', hle, hh, hk, he⟩ := Ho.1 hf
        refine ⟨st'', regs'', hI'', Needs.le_trans hν hle, hh, fun z hz => ?_, e.trans (J'.trans he)⟩
        rw [hk z hz, read_store_ne (hK z hz).2, hk' z (hK z hz).1]
      · obtain ⟨ton2, st'', hI'', hle, he, hrel2⟩ := Ho.2 hf
        exact ⟨ton2, st'', hI'', Needs.le_trans hν hle, e.trans (J'.trans he), hrel2⟩
    | one p' =>
      exact ⟨Tone.one p', st', hI', hν, e.trans J, ToneRel.one p'⟩
    | two hl =>
      exact ⟨_, st', hI', hν, e.trans J, ToneRel.two (Forall2.append hl (frames_mono hν htr))⟩
  · rw [en] at G
    have G' : goJ lib O c gul st regs ti je = some (Tone.two ti, st) := G
    rw [er]
    exact ⟨Tone.two ti, st, hI, Needs.le_refl _, G', ToneRel.two htr⟩

/-! ## Any goal -/

section
variable {lib : Lib} {σ : Type} {Inv : σ → Prop} {ν : σ → Needs} {O : Oracle σ} {c : Straight Map} {gul : Noun}

theorem returnsC_step {st st' : σ} {regs regs' : Map (Option Noun)} {t : Trace} {je je' : Jmp} {r : Tone}
    (hν : ν st ≤ ν st') (e : goJ lib O c gul st regs t je = goJ lib O c gul st' regs' t je')
    (H : ReturnsC lib O c gul Inv ν st' regs' t je' r) : ReturnsC lib O c gul Inv ν st regs t je r := by
  obtain ⟨ton, st'', hI, hle, he, hr⟩ := H
  exact ⟨ton, st'', hI, Needs.le_trans hν hle, e.trans he, hr⟩

theorem goesC_step {K : Nat → Prop} {st st' : σ} {regs regs' : Map (Option Noun)} {t : Trace} {je je' j : Jmp}
    {Q : Map (Option Noun) → Prop} (hν : ν st ≤ ν st')
    (hk : ∀ x, K x → SkaModel.read x regs' = SkaModel.read x regs)
    (e : goJ lib O c gul st regs t je = goJ lib O c gul st' regs' t je')
    (H : GoesC lib O c gul Inv ν K st' regs' t je' j Q) : GoesC lib O c gul Inv ν K st regs t je j Q := by
  obtain ⟨st'', regs'', hI, hle, hq, hk', he⟩ := H
  exact ⟨st'', regs'', hI, Needs.le_trans hν hle, hq, fun x hx => (hk' x hx).trans (hk x hx), e.trans he⟩

/-- **`GoalSemCM` moves back over a step** of the code that goes from
`(st, regs, je)` to `(st', regs', je')` with the needs grown and the kept
registers kept. -/
theorem goalSemCM_step {K : Nat → Prop} {st st' : σ} {regs regs' : Map (Option Noun)} {t tm : Trace}
    {je je' : Jmp} (hν : ν st ≤ ν st') (hk : ∀ x, K x → SkaModel.read x regs' = SkaModel.read x regs)
    (e : goJ lib O c gul st regs t je = goJ lib O c gul st' regs' t je') :
    ∀ (goal : CGoal S) (r : Tone), GoalSemCM lib O c gul Inv ν K st' regs' t tm je' goal r →
      GoalSemCM lib O c gul Inv ν K st regs t tm je goal r
  | CGoal.done, _, H => returnsC_step hν e H
  | CGoal.next _ _, Tone.zero _, H =>
      ⟨fun hf => goesC_step hν hk e (H.1 hf), fun hf => returnsC_step hν e (H.2 hf)⟩
  | CGoal.next _ _, Tone.one _, H => returnsC_step hν e H
  | CGoal.next _ _, Tone.two _, H => returnsC_step hν e H
  | CGoal.pick _ _, Tone.zero _, H =>
      ⟨fun h0 => goesC_step hν hk e (H.1 h0), fun h1 => goesC_step hν hk e (H.2.1 h1),
        fun a b => returnsC_step hν e (H.2.2 a b)⟩
  | CGoal.pick _ _, Tone.one _, H => returnsC_step hν e H
  | CGoal.pick _ _, Tone.two _, H => returnsC_step hν e H

/-- A tone that is no product is returned, for every goal. -/
theorem goalSemCM_ret {K : Nat → Prop} {st : σ} {regs : Map (Option Noun)} {t tm : Trace} {je : Jmp} :
    ∀ (goal : CGoal S) (r : Tone), (∀ p, r ≠ Tone.zero p) → ReturnsC lib O c gul Inv ν st regs t je r →
      GoalSemCM lib O c gul Inv ν K st regs t tm je goal r
  | CGoal.done, _, _, H => H
  | CGoal.next _ _, Tone.zero p, hn, _ => absurd rfl (hn p)
  | CGoal.next _ _, Tone.one _, _, H => H
  | CGoal.next _ _, Tone.two _, _, H => H
  | CGoal.pick _ _, Tone.zero p, hn, _ => absurd rfl (hn p)
  | CGoal.pick _ _, Tone.one _, _, H => H
  | CGoal.pick _ _, Tone.two _, _, H => H

end

/-- **What the block `out` does with a product in `pro`** for any goal, at
every state where `Inv` holds. -/
def OutGoal (lib : Lib) {σ : Type} (O : Oracle σ) (c : Straight Map) (gul : Noun) (Inv : σ → Prop)
    (ν : σ → Needs) (K : Nat → Prop) (pro out : Nat) (goal : CGoal S) : Prop :=
  ∀ (st : σ) (regs : Map (Option Noun)) (ti tm : Trace) (p : Noun), Inv st → Forall2 (FrameRel lib (ν st)) ti tm →
    SkaModel.read pro regs = some p →
    GoalSemCM lib O c gul Inv ν K st regs ti tm (jmp0 out) goal (Tone.zero p)

/-- **The indirect call at any goal, from the run's jump** (`indirect_semN`
for `%next`, the block `out` of `+kerf` meeting `OutGoal`): for `%pick` the
block of `+simple-next` is a `brn` on the register of `+kern`, for `%done` a
`don`. -/
theorem indirect_semG {lib : Lib} {P : Noun → Prop} {f : Noun} {p q : Nomm} (M : MinkN2 lib P f p q)
    {σ : Type} {Inv : σ → Prop} {ν : σ → Needs} {O : Oracle σ} {n : Nat} {gul : Noun}
    (hS : OracleSteps Inv ν O) (hF : OracleFwd lib Inv ν O n) {c : Straight Map}
    {a b pro o out : Nat} (hb : HoonMap.get c.blocks o = some ⟨[], [Pole.nok a b pro], Termin.hop (jmp0 out)⟩)
    {K K' : Nat → Prop} (hK : ∀ x, K x → K' x ∧ x ≠ pro)
    {goal : CGoal S} (Hout : OutGoal lib O c gul Inv ν K pro out goal)
    {st : σ} (hI : Inv st) {ti tm : Trace} (htr : Forall2 (FrameRel lib (ν st)) ti tm)
    {s : Noun} (hs : P s) {r : Tone} (hm : minkF lib gul n tm s f = some r)
    {je : Jmp} {regs : Map (Option Noun)}
    (G : GoalSem lib O c gul st K' regs ti je (CGoal.next (pairSure a b : Sure S) (jmp0 o))
      (pureEval (Nomm.cons p q) s)) :
    GoalSemCM lib O c gul Inv ν K st regs ti tm je goal r := by
  rw [pureEval_cons] at G
  rcases M.fwd hs hm with ⟨n', x, y, hlt, ex, ey, hm'⟩ | ⟨en, er⟩
  · rw [ex, ey] at G
    simp only [Option.bind_some] at G
    obtain ⟨regs', ⟨h2, h3⟩, hk', e⟩ := G.1 ⟨⟨trivial, trivial⟩, looks_empty _⟩
    have J := goJ_nok (lib := lib) (O := O) (gul := gul) hb st regs' ti h2 h3
    rw [minkF_trace] at hm'
    obtain ⟨r0, h0, rfl⟩ := Option.map_eq_some_iff.mp hm'
    obtain ⟨ton, st', hO, hrel⟩ := hF.nok st x y gul n' r0 hI hlt h0
    obtain ⟨hI', hν⟩ := hS.nok st x y gul ton st' hI hO
    rw [hO, Option.bind_some] at J
    cases hrel with
    | zero p' =>
      have J' : goJ lib O c gul st regs' ti (jmp0 o) =
          goJ lib O c gul st' (SkaModel.store pro p' regs') ti (jmp0 out) := J
      exact goalSemCM_step hν (fun z hz => by rw [read_store_ne (hK z hz).2, hk' z (hK z hz).1]) (e.trans J')
        goal _ (Hout st' (SkaModel.store pro p' regs') ti tm p' hI' (frames_mono hν htr)
          (read_store_eq pro p' regs'))
    | one p' =>
      exact goalSemCM_ret goal _ (fun _ h => by cases h) ⟨Tone.one p', st', hI', hν, e.trans J, ToneRel.one p'⟩
    | two hl =>
      exact goalSemCM_ret goal _ (fun _ h => by cases h)
        ⟨_, st', hI', hν, e.trans J, ToneRel.two (Forall2.append hl (frames_mono hν htr))⟩
  · rw [en] at G
    have G' : goJ lib O c gul st regs ti je = some (Tone.two ti, st) := G
    rw [er]
    exact goalSemCM_ret goal _ (fun _ h => by cases h) ⟨Tone.two ti, st, hI, Needs.le_refl _, G', ToneRel.two htr⟩

end Comp
end SkaModel
end Formalization
