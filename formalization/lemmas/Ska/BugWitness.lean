import lemmas.Ska.Contract
import lemmas.Ska.MinkTrace
import lemmas.Ska.ContractExamples
import lemmas.Ska.Theorems

/-!
# Two places where the analysis and `+mink` part ways

Found by reading `+ska-callgraph` (the `fol-loop` of `+run`), against the
contract.  The analysis is not modelled in Lean yet, so what it produces on
these formulas is read off the Hoon; what is proved here is the other half:
`+mink`'s result on them, and that no code which satisfies the contract can
return what the analysis's code returns.  Code that makes no calls is run
with the oracle that answers nothing, which satisfies every hypothesis of
`ContractBwd`.

1. **The inliner drops a formula-formula that can crash.**  In the `[%2 p q]`
   case of `fol-loop`, when the product of `q` is a known cell and
   `+inlineable`, the nomm is `[%7 nomm.s nomm.inline]`: `nomm.f` is dropped
   whether or not it can crash, loop or block.  (The direct call keeps it
   unless `+safe-fol-fol`.)  On `[2 [0 1] 7 [0 0] 1 0 1]` the product of
   `[7 [0 0] 1 0 1]` is `&+[0 1]`, so the nomm is `[%7 [%0 1] [%0 1]]`, and
   the code returns the subject; `+mink` crashes (`inline_drop`).
2. **The default case crashes before `+mink` would.**  `fol-loop` matches
   `[%5 p=^ q=^]` and the like, and anything else is `[%0 0]`, a crash with the
   trace as it is.  `+mink` matches `[%5 a=* b=*]` and runs `a` first.  On
   `[5 [11 [%spot 1 0] 0 0] 0]` the analysis's code crashes with an empty trace;
   `+mink` crashes with a `%spot` frame (`default_crash`).  With a loop or a
   blocking scry in place of the hint, `+mink` loops or blocks.
3. **`%bare` loops in the interpreter.**  `fol-loop` makes `[11 %bare q]` the
   indirect call `[%2 [%0 1] [%1 [11 %bare q]] ~]`, compiled to a `%nok` of
   the formula itself on the subject.  Vere gives that formula to its plain
   interpreter; `+eval-top` runs `%nok` by `+eval-top`, which compiles and
   runs the same code again.  So `+eval-top` never returns on
   `[11 %bare 1 42]`, which Nock reduces to `42` (`bare_loops`), and `Meek`
   fails.  `+mink` itself runs its hint under `~> %bare`.
-/

namespace Formalization
namespace SkaModel

open Nock

/-- The oracle that answers nothing. -/
def silent (σ : Type) : Oracle σ := ⟨fun _ _ _ _ _ _ => none, fun _ _ _ _ => none⟩

theorem silent_steps {σ : Type} (Inv : σ → Prop) (ν : σ → Needs) : OracleSteps Inv ν (silent σ) :=
  ⟨fun _ _ _ _ _ _ _ _ _ h => by simp [silent] at h, fun _ _ _ _ _ _ _ h => by simp [silent] at h⟩

theorem silent_bwd {σ : Type} (lib : Lib) (Inv : σ → Prop) (ν : σ → Needs) :
    OracleBwd lib Inv ν (silent σ) :=
  ⟨fun _ _ _ _ _ _ _ _ _ h => by simp [silent] at h, fun _ _ _ _ _ _ _ h => by simp [silent] at h⟩

section
variable {Map : Type → Type} [HoonMap Map]

/-- What code that satisfies the backward contract returns, without calls,
`+mink` returns. -/
theorem contract_silent {lib : Lib} {N : Needs} {s f gul : Noun} {c : Straight Map}
    (hB : ContractBwd lib N s f [s] c) {ton : Tone}
    (h : execEntry lib (silent Unit) () c [s] [] gul = some (ton, ())) :
    ∃ r, Mink lib gul [] s f r ∧ ToneRel lib N ton r := by
  have := hB Unit (fun _ => True) (fun _ => N) (silent Unit) gul [] [] (fun _ _ => Needs.le_refl _)
    (silent_steps _ _) (silent_bwd lib _ _) () ton () trivial Forall2.nil h
  exact this

/-- The formula of the first finding. -/
def fInline : Noun := n3 (A 2) (slot 1) (n3 (A 7) (slot 0) (quote (slot 1)))

theorem mink_fInline (lib : Lib) (gul s : Noun) (t : Trace) :
    ∀ n r, minkF lib gul n t s fInline = some r → r = Tone.two t := by
  intro n r h
  match n, h with
  | 0, h => simp [minkF] at h
  | 1, h => simp [minkF, minkStep, fInline] at h
  | 2, h => simp [minkF, minkStep, fInline] at h
  | n + 3, h =>
    simp [minkF_succ_eq, minkStep, fInline, slot?_zero] at h
    exact h.symm

/-- **The first finding, against the contract.**  Code for
`[2 [0 1] 7 [0 0] 1 0 1]` that satisfies the contract never returns a
product, as the analysis's `[%7 [%0 1] [%0 1]]` does. -/
theorem inline_drop {lib : Lib} {N : Needs} {s gul : Noun} {c : Straight Map}
    (hB : ContractBwd lib N s fInline [s] c) (v : Noun) :
    execEntry lib (silent Unit) () c [s] [] gul ≠ some (Tone.zero v, ()) := by
  intro h
  obtain ⟨r, ⟨n, hn⟩, hrel⟩ := contract_silent hB h
  rw [mink_fInline lib gul s [] n r hn] at hrel
  cases hrel

/-- The formula of the second finding: `%spot` is `0x746f7073`. -/
def fDefault : Noun :=
  n3 (A 5) (n3 (A 11) (C (A Tag.spot) (quote (A 0))) (slot 0)) (A 0)

theorem mink_fDefault (lib : Lib) (gul s : Noun) :
    ∀ n r, minkF lib gul n [] s fDefault = some r → r = Tone.two [(Tag.spot, A 0)] := by
  intro n r h
  match n, h with
  | 0, h => simp [minkF] at h
  | 1, h => simp [minkF, minkStep, fDefault] at h
  | 2, h => simp [minkF, minkStep, fDefault] at h
  | n + 3, h =>
    have hs : stopTag Tag.spot = true := by decide
    simp [minkF_succ_eq, minkStep, fDefault, hs, slot?_zero] at h
    exact h.symm

/-- **The second finding, against the contract.**  Code for
`[5 [11 [%spot 1 0] 0 0] 0]` that satisfies the contract never crashes with an
empty trace, as the analysis's `[%0 0]` does. -/
theorem default_crash {lib : Lib} {N : Needs} {s gul : Noun} {c : Straight Map}
    (hB : ContractBwd lib N s fDefault [s] c) :
    execEntry lib (silent Unit) () c [s] [] gul ≠ some (Tone.two [], ()) := by
  intro h
  obtain ⟨r, ⟨n, hn⟩, hrel⟩ := contract_silent hB h
  rw [mink_fDefault lib gul s n r hn] at hrel
  cases hrel with
  | two hl => cases hl

/-- The code that `fol-loop` and `+comp` make of `[11 %bare q]`: the formula
in a register, an indirect call of it on the subject, its product returned. -/
def selfNok (f : Noun) : Straight Map :=
  oneBlock ⟨[], [Pole.imm f 1, Pole.nok 0 1 2], Termin.don 2⟩

/-- **The third finding.**  A compiler that answers `%full s f` with the
indirect call of `f` itself, from every state, makes the interpreter never
return on `[s f]`, at any depth of calls. -/
theorem bare_loops (lib : Lib) {σ : Type} (poke : σ → Ovum → Option (Prod Map × σ))
    (s f₁ f₂ gul : Noun)
    (hp : ∀ st, ∃ b new st', poke st (Ovum.full s (C f₁ f₂)) =
      some (Prod.ir b (selfNok (Map := Map) (C f₁ f₂)) new, st')) :
    ∀ k st, (interp lib poke k).nok st s (C f₁ f₂) gul = none := by
  intro k
  induction k with
  | zero => intro st; rfl
  | succ k ih =>
    intro st
    obtain ⟨b, new, st', hpk⟩ := hp st
    simp only [interp]
    rw [topBody_cell hpk rfl rfl]
    rw [selfNok, execEntry_oneBlock, execBlob_body, execPole_imm, Option.bind_some]
    simp only
    rw [execBlob_body]
    simp [execPole, read_store, read_put, ih]

/-- Nock reduces `[11 %bare 1 42]` to `42`: `%bare` is
`0x65726162`. -/
theorem eval_bare (s : Noun) : EvalH s (n3 (A 11) (A 0x65726162) (quote (A 42))) (A 42) :=
  EvalH.op11_atom EvalH.op1

end

end SkaModel
end Formalization
