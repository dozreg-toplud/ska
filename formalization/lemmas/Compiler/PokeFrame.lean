import lemmas.Compiler.EvalCall

/-!
# What the poke keeps

The compiler's core is `cr = [poke-battery [battery state ctx]]`: the inner
`|%` with `+load`, `+peek`, `+poke` and `+wish` over the core of
`+compiled-mono`, over `=|  state=state-0`, over the library.  The state is at
axis `14` (its head is the version `%0`), and everything the interpreter
reads through `cr` (layers 2 and 4, `CorIn`) is under axis `15`.

`+poke` returns `[prod ..poke]`, where `..poke` is its own core with the state
changed by `=^`, `=.` and `%=`, which compile to Nock `10` edits of axes under
`14`.  So a returned core agrees with `cr` at axis `15` (`PokeFrame`), and that
is all `CorIn` needs (`corIn_of_tail`).  `PokeFrame` is stated on the pill's
Nock alone, and with the first half of `PokeIs` it gives the second half
(`pokeIs_of_frame`).  It is not proved: the arm's Nock (about a thousand cells
before the arms it calls) branches four ways and calls `+ska-poke`,
`+compiled-mono`, `+optimize` and the cache arms, whose products go into the
state only; a proof needs either each branch run symbolically with the calls
left opaque, or an abstract interpretation of the formula that tracks which
axes of the subject a value can differ from `cr` at.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon

/-- Two nouns that agree at axis `a` agree at every axis under it. -/
theorem slot_under {s t : Noun} {a : Nat} (ha : 0 < a) (h : slot? a s = slot? a t) :
    ∀ k n, n / 2 ^ k = a → slot? n s = slot? n t
  | 0, n, hn => by simp at hn; subst hn; exact h
  | k + 1, n, hn => by
    have hn' : n / 2 / 2 ^ k = a := by rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']; exact hn
    have h2 : 2 ≤ n := by
      rcases Nat.lt_or_ge n 2 with hl | hl
      · have : n / 2 = 0 := by omega
        rw [this, Nat.zero_div] at hn'; omega
      · exact hl
    rw [slot?_step n h2, slot?_step n h2, slot_under ha h k (n / 2) hn']

/-- `CorIn` reads `cr` under axis `15` only. -/
theorem corIn_of_tail {cr cr' : Noun} (hc : CorIn cr) (h : slot? 15 cr' = slot? 15 cr) :
    CorIn cr' := by
  obtain ⟨h2, h4⟩ := hc
  simp only [read.layer2.axis, icore, Nat.reduceDiv, nock_exec] at h2 h4
  refine ⟨?_, ?_⟩
  · simp only [read.layer2.axis, icore, nock_exec]
    rw [slot_under (by decide) h 17 _ (by decide)]; exact h2
  · simp only [read.layer2.axis, icore, Nat.reduceDiv, nock_exec]
    rw [slot_under (by decide) h 15 _ (by decide)]; exact h4

/-- The pill's poke at `cr`, on any ovum and on any path that returns, returns
`[prod cr']` with `cr'` equal to `cr` under axis `15`: only the state changed. -/
def PokeFrame (cr : Noun) : Prop :=
  ∀ ovo x, pokeN cr ovo = some x → ∃ prod cr', x = C prod cr' ∧ slot? 15 cr' = slot? 15 cr

/-- The second half of `PokeIs` from the first and the frame of the pill's
poke. -/
theorem pokeIs_of_frame {pk : Noun → Ovum → Option (SkaModel.Prod (TreapMap mugF) × Noun)}
    {cr : Noun} (hc : CorIn cr) (hf : PokeFrame cr)
    (hpk : ∀ ov, pokeN cr ov.toNoun = (pk cr ov).map fun r => C r.1.toNoun r.2) :
    PokeIs pk cr := by
  refine ⟨hpk, fun ov r e => ?_⟩
  have h := hpk ov
  rw [e, Option.map_some] at h
  obtain ⟨prod, cr', e1, e2⟩ := hf _ _ h
  simp only [Noun.cell.injEq] at e1
  rw [← e1.2] at e2
  exact corIn_of_tail hc e2

end Compiler
end Formalization
