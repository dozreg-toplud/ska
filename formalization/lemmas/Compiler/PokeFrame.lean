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
is all the layers of `CorIn` need (`corIn_of_tail`).  `PokeFrame` is stated on
the pill's Nock alone, and with the first half of `PokeIs` it gives the second
half (`pokeIs_of_frame`).

`CorIn` also asks that the pill's `cor` reach `cr` by pokes (`PokeReach`).
Without that, `∀ cr, CorIn cr → PokeIs pk cr` held for no `pk`: the code of
`+poke` sits in `cr` itself, at axis `2`, and a core with the layers in place
and a battery of its own can return anything (`junk_layers`, whose poke
returns `[0 0]`; `PokeIs` would then ask `CorIn 0`).
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

/-- The layers of `CorIn` are read in `cr` under axis `15` only. -/
theorem corIn_of_tail {cr cr' : Noun} (hc : CorIn cr) (h : slot? 15 cr' = slot? 15 cr)
    (hr : PokeReach cr') : CorIn cr' := by
  obtain ⟨h2, h4, -⟩ := hc
  simp only [read.layer2.axis, icore, Nat.reduceDiv, nock_exec] at h2 h4
  refine ⟨?_, ?_, hr⟩
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
    (hpk : ∀ ov, ¬ Ska.Hot ov.toNoun → pokeN cr ov.toNoun = (pk cr ov).map fun r => C r.1.toNoun r.2) :
    PokeIs pk cr := by
  refine ⟨hpk, fun ov r e hh => ?_⟩
  have h := hpk ov hh
  rw [e, Option.map_some] at h
  obtain ⟨prod, cr', e1, e2⟩ := hf _ _ h
  have hr := PokeReach.poke hc.2.2 h hh
  simp only [Noun.cell.injEq] at e1
  rw [← e1.2] at e2
  exact corIn_of_tail hc e2 hr

/-! ## Why `CorIn` asks for `PokeReach` -/

/-- The head and the tail of the pill's `cor`. -/
def corHead : Noun := match cor with | Noun.cell h _ => h | Noun.atom _ => A 0
def corTail : Noun := match cor with | Noun.cell _ t => t | Noun.atom _ => A 0

theorem cor_eq : cor = C corHead corTail := by kernel_rfl

/-- A battery whose `+poke` builds a gate that returns `[0 0]`. -/
def junkBattery : Noun :=
  C (A 0) (C (A 0) (C (A 0) (C (A 1) (C (C (A 1) (C (A 0) (A 0))) (C (A 0) (A 0))))))

/-- With the pill's tail and another battery, a core has layers 2 and 4 where
the interpreter reads them, and its poke returns `[0 0]` on every noun.  So
the layers alone do not make `PokeIs` satisfiable: it would ask `CorIn 0`. -/
theorem junk_layers :
    slot? read.layer2.axis (icore (C junkBattery corTail)) = some layer2 ∧
      slot? (read.layer2.axis / 4) (icore (C junkBattery corTail)) = some layer4 ∧
      ∀ ovo, pokeN (C junkBattery corTail) ovo = some (C (A 0) (A 0)) := by
  have h2 : slot? read.layer2.axis (icore cor) = some layer2 := by unfold icore; kernel_rfl
  have h4 : slot? (read.layer2.axis / 4) (icore cor) = some layer4 := by unfold icore; kernel_rfl
  rw [cor_eq] at h2 h4
  simp only [read.layer2.axis, icore, Nat.reduceDiv, nock_exec] at h2 h4
  refine ⟨?_, ?_, fun ovo => ?_⟩
  · simpa [read.layer2.axis, icore, nock_exec] using h2
  · simpa [read.layer2.axis, icore, nock_exec] using h4
  · simp [pokeN, junkBattery, Ska.axPoke, nock_exec]

end Compiler
end Formalization
