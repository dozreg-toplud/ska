import lemmas.Ska.Contract

/-!
# The state of the compiler only changes by pokes

`execBlob` changes the state only through its oracle, so whatever relation
of states every answer of the oracle makes a step of, every run of a function
makes a step of (`execBlob_state`).  With the compiler's invariant and the
growth of its needs as that relation, the interpreter keeps both, whatever it
runs (`interp_steps`).
-/

namespace Formalization
namespace SkaModel

open Nock

section
variable {Map : Type → Type} [HoonMap Map] {σ : Type}

theorem afterCall_state {st : σ} {regs : Map Noun} {trace : Trace} {d : Nat} {ton : Tone}
    {r : Tone × Map Noun × Trace × σ} (h : afterCall st regs trace d ton = some r) :
    r.2.2.2 = st := by
  cases ton <;> simp [afterCall] at h <;> subst h <;> rfl

/-- The state after an op is the state before it, or the state an answer of
the oracle left. -/
theorem execPole_state {lib : Lib} {O : Oracle σ} {scry : Noun} {st : σ} {pole : Pole}
    {regs : Map Noun} {trace : Trace} {r : Tone × Map Noun × Trace × σ} (Q : σ → Prop)
    (hst : Q st)
    (hcall : ∀ a m vs t ton st', O.call st a m vs t scry = some (ton, st') → Q st')
    (hnok : ∀ u f ton st', O.nok st u f scry = some (ton, st') → Q st')
    (h : execPole lib O scry st pole regs trace = some r) : Q r.2.2.2 := by
  cases pole
  case nok u f d =>
    simp only [execPole, Option.bind_eq_some_iff] at h
    obtain ⟨vu, _, vf, _, ⟨ton, st'⟩, hn, h⟩ := h
    cases ton <;> simp at h <;> subst h <;> exact hnok _ _ _ _ hn
  case cal a v d =>
    simp only [execPole, Option.bind_eq_some_iff] at h
    obtain ⟨vs, _, ⟨ton, st'⟩, hc, h⟩ := h
    rw [afterCall_state h]; exact hcall _ _ _ _ _ _ hc
  case caf a v d _ =>
    simp only [execPole, Option.bind_eq_some_iff] at h
    obtain ⟨vs, _, ⟨ton, st'⟩, hc, h⟩ := h
    rw [afterCall_state h]; exact hcall _ _ _ _ _ _ hc
  case cam a v d _ =>
    simp only [execPole, Option.bind_eq_some_iff] at h
    obtain ⟨vs, _, ⟨ton, st'⟩, hc, h⟩ := h
    rw [afterCall_state h]; exact hcall _ _ _ _ _ _ hc
  case csl a s d =>
    simp only [execPole, Option.bind_eq_some_iff] at h
    obtain ⟨vs, _, ⟨ton, st'⟩, hc, h⟩ := h
    rw [afterCall_state h]; exact hcall _ _ _ _ _ _ hc
  case csf a s d _ =>
    simp only [execPole, Option.bind_eq_some_iff] at h
    obtain ⟨vs, _, ⟨ton, st'⟩, hc, h⟩ := h
    rw [afterCall_state h]; exact hcall _ _ _ _ _ _ hc
  case csm a s d _ =>
    simp only [execPole, Option.bind_eq_some_iff] at h
    obtain ⟨vs, _, ⟨ton, st'⟩, hc, h⟩ := h
    rw [afterCall_state h]; exact hcall _ _ _ _ _ _ hc
  all_goals
    simp only [execPole, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h
    exact hst

/-- Every run of a function makes a step of any preorder of states that every
answer of the oracle makes a step of. -/
theorem execBlob_state {lib : Lib} {O : Oracle σ} {s : Straight Map} {scry : Noun}
    (P : σ → σ → Prop) (hrefl : ∀ x, P x x) (htrans : ∀ x y z, P x y → P y z → P x z)
    (hcall : ∀ st a m vs t ton st', O.call st a m vs t scry = some (ton, st') → P st st')
    (hnok : ∀ st u f ton st', O.nok st u f scry = some (ton, st') → P st st') :
    ∀ st regs trace b params r, execBlob lib O s scry st regs trace b params = some r →
      P st r.2 := by
  intro st regs trace b params r h
  refine execBlob.partial_correctness lib O s scry (fun st _ _ _ _ r => P st r.2) ?_
    st regs trace b params r h
  intro rec ih st regs trace b params r h
  simp only [Option.bind_eq_bind] at h
  have hop : ∀ (j : Jmp), ((HoonMap.get s.blocks j.there).bind fun b' =>
      rec st regs trace b' j.args) = some r → P st r.2 := by
    intro j h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    exact ih _ _ _ _ _ _ h
  split at h
  · obtain ⟨regs', _, h⟩ := Option.bind_eq_some_iff.mp h
    exact ih _ _ _ _ _ _ h
  · split at h
    · obtain ⟨⟨ton, regs', trace', st'⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
      have hst : P st st' :=
        execPole_state (r := (ton, regs', trace', st')) (P st) (hrefl st)
          (fun _ _ _ _ _ _ hc => hcall _ _ _ _ _ _ _ hc) (fun _ _ _ _ hn => hnok _ _ _ _ _ hn) hp
      split at h
      · exact htrans _ _ _ hst (ih _ _ _ _ _ _ h)
      · cases h; exact hst
    · split at h
      · obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h; exact hop _ h
      · obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h; exact hop _ h
      · obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
        exact hop _ h
      · obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
        split at h
        · exact hop _ h
        · split at h
          · exact hop _ h
          · cases h; exact hrefl _
      · obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h; exact hop _ h
      · exact hop _ h
      · obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h; exact hcall _ _ _ _ _ _ _ h
      · obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h; exact hcall _ _ _ _ _ _ _ h
      · obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h; exact hcall _ _ _ _ _ _ _ h
      · obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h; exact hcall _ _ _ _ _ _ _ h
      · obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h; cases h; exact hrefl _
      · cases h; exact hrefl _

theorem execEntry_state {lib : Lib} {O : Oracle σ} {st : σ} {c : Straight Map}
    {vals : List Noun} {trace : Trace} {scry : Noun} {r : Tone × σ}
    (P : σ → σ → Prop) (hrefl : ∀ x, P x x) (htrans : ∀ x y z, P x y → P y z → P x z)
    (hcall : ∀ st a m vs t ton st', O.call st a m vs t scry = some (ton, st') → P st st')
    (hnok : ∀ st u f ton st', O.nok st u f scry = some (ton, st') → P st st')
    (h : execEntry lib O st c vals trace scry = some r) : P st r.2 := by
  simp only [execEntry, Option.bind_eq_some_iff] at h
  obtain ⟨b, _, h⟩ := h
  exact execBlob_state P hrefl htrans hcall hnok _ _ _ _ _ _ h

/-- The step of the compiler's invariant and of its needs. -/
def InvStep (poke : σ → Ovum → Option (Prod Map × σ)) (InvC : σ → Prop) (st st' : σ) : Prop :=
  InvC st → InvC st' ∧ needOf poke st ≤ needOf poke st'

omit [HoonMap Map] in
theorem InvStep.refl {poke : σ → Ovum → Option (Prod Map × σ)} {InvC : σ → Prop} (x : σ) :
    InvStep poke InvC x x :=
  fun h => ⟨h, Needs.le_refl _⟩

omit [HoonMap Map] in
theorem InvStep.trans {poke : σ → Ovum → Option (Prod Map × σ)} {InvC : σ → Prop} (x y z : σ)
    (h : InvStep poke InvC x y) (h' : InvStep poke InvC y z) : InvStep poke InvC x z := by
  intro hx
  obtain ⟨hy, hxy⟩ := h hx
  obtain ⟨hz, hyz⟩ := h' hy
  exact ⟨hz, Needs.le_trans hxy hyz⟩

/-- The interpreter keeps the compiler's invariant, and the needs only grow,
whatever it runs: its state changes by pokes only. -/
theorem interp_steps (lib : Lib) {poke : σ → Ovum → Option (Prod Map × σ)} {InvC : σ → Prop}
    (hP : PokeSteps poke InvC) :
    ∀ k, OracleSteps InvC (needOf poke) (interp lib poke k) := by
  intro k
  induction k with
  | zero => exact ⟨fun _ _ _ _ _ _ _ _ _ h => by simp [interp] at h,
                   fun _ _ _ _ _ _ _ h => by simp [interp] at h⟩
  | succ k ih =>
    have hc : ∀ st a m vs t scry ton st', (interp lib poke k).call st a m vs t scry =
        some (ton, st') → InvStep poke InvC st st' :=
      fun _ _ _ _ _ _ _ _ h hI => ih.call _ _ _ _ _ _ _ _ hI h
    have hn : ∀ st u f scry ton st', (interp lib poke k).nok st u f scry = some (ton, st') →
        InvStep poke InvC st st' :=
      fun _ _ _ _ _ _ h hI => ih.nok _ _ _ _ _ _ hI h
    constructor
    · intro st b m vals t gul ton st' hI h
      simp only [interp, callBody, Option.bind_eq_some_iff] at h
      obtain ⟨⟨p, st1⟩, hp, h⟩ := h
      split at h
      · have h1 := hP.dire _ _ _ _ _ hI hp
        have h2 := execEntry_state (r := (ton, st')) (InvStep poke InvC) InvStep.refl
          InvStep.trans (fun _ _ _ _ _ _ _ h => hc _ _ _ _ _ _ _ _ h)
          (fun _ _ _ _ _ h => hn _ _ _ _ _ _ h) h
        exact InvStep.trans _ _ _ (fun _ => h1) h2 hI
      · simp at h
    · intro st u f gul ton st' hI h
      simp only [interp, topBody] at h
      split at h
      · cases h; exact ⟨hI, Needs.le_refl _⟩
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨⟨p, st1⟩, hp, h⟩ := h
        have h1 := hP.full _ _ _ _ _ hI hp
        split at h
        · split at h
          · simp only [Option.bind_eq_some_iff] at h
            obtain ⟨b, _, h⟩ := h
            split at h
            · have h2 := execBlob_state (InvStep poke InvC) InvStep.refl InvStep.trans
                (fun _ _ _ _ _ _ _ h => hc _ _ _ _ _ _ _ _ h)
                (fun _ _ _ _ _ h => hn _ _ _ _ _ _ h) _ _ _ _ _ _ h
              exact InvStep.trans _ _ _ (fun _ => h1) h2 hI
            · simp at h
          · simp at h
        · simp at h

end

end SkaModel
end Formalization
