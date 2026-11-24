import lemmas.Compiler.EvalCall
import lemmas.Compiler.Frame

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
half (`pokeIs_of_frame`).  It holds of every core with `CorIn`
(`pokeFrame_corIn`): the abstract interpreter of `Frame.lean`, run by the
kernel on the arm, shows that the poke of a core with the pill's battery
returns a core equal to it at axes `2`, `6` and `15` (`poke_frame`), so every
core the pill reaches by pokes has the pill's battery (`pokeReach_frame`).

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

/-! ## The frame of the pill's `+poke`

The kernel runs the abstract interpreter of `Frame.lean` on the battery of
the gate that the pill's inner `+poke` builds, from the subject
`[battery [ovo cr]]` as the base: every shape of the product (37 of them,
one per path through the branches) has the base's `cr` at axes `2`, `6` and
`15` of its tail.  There are 72 shapes, one per path through the branches
that the abstract run cannot decide.  Every call of the arm returns an
unknown noun there, and the products of the calls go into the state only. -/

/-- The arm of the inner `+poke` and the battery of its gate. -/
def ipokeArm : Noun := (slot? Ska.axPoke cor).getD (A 0)

def ipokeBat : Noun :=
  match ipokeArm with
  | Noun.cell _ (Noun.cell _ (Noun.cell (Noun.cell _ b) _)) => b
  | _ => A 0

theorem cor_ipoke : slot? Ska.axPoke cor =
    some (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) ipokeBat) (C (A 0) (A 1))))) := by
  unfold Ska.axPoke; kernel_rfl

/-- The shape has `sub q` at the path `p`. -/
def isSubAt (p q : List Bool) (r : Frame.Ab) : Bool :=
  match Frame.aslotPath p r with
  | [Frame.Ab.sub q'] => q' == q
  | _ => false

theorem isSubAt_eq {p q : List Bool} {r : Frame.Ab} (h : isSubAt p q r = true) :
    Frame.aslotPath p r = [Frame.Ab.sub q] := by
  unfold isSubAt at h
  split at h
  · rename_i q' e
    rw [e, beq_iff_eq.1 h]
  · cases h

/-- The tail of the product agrees with the base's `cr` (at `[true, true]`)
at axes `2`, `6` and `15`. -/
def frameOK (r : Frame.Ab) : Bool :=
  isSubAt [true, false] [true, true, false] r &&
    isSubAt [true, true, false] [true, true, true, false] r &&
    isSubAt [true, true, true, true] [true, true, true, true, true] r

theorem ipoke_check : (Frame.absNock 1000 (.sub []) ipokeBat).all frameOK = true := by
  kernel_rfl

theorem slot2_path (n : Noun) : slot? 2 n = slotAtPath n [false] := rfl
theorem slot6_path (n : Noun) : slot? 6 n = slotAtPath n [true, false] := rfl
theorem slot15_path (n : Noun) : slot? 15 n = slotAtPath n [true, true, true] := rfl

/-- The pill's poke, on any core whose battery is the pill's, returns
`[prod cr']` with `cr'` equal to `cr` at axes `2`, `6` and `15`: everywhere
but the state at `14`. -/
theorem poke_frame {cr : Noun} (hb : slot? 2 cr = slot? 2 cor) {ovo x : Noun}
    (h : pokeN cr ovo = some x) :
    ∃ prod cr', x = C prod cr' ∧ slot? 2 cr' = slot? 2 cr ∧ slot? 6 cr' = slot? 6 cr ∧
      slot? 15 cr' = slot? 15 cr := by
  have h23 : slot? Ska.axPoke cr = slot? Ska.axPoke cor :=
    slot_under (by decide) hb 3 _ (by decide)
  unfold pokeN at h
  rw [h23, cor_ipoke] at h
  simp only [nock_exec] at h
  have he := eval_of_nock h
  obtain ⟨r, hr, gr⟩ := Frame.absNock_sound (S := C ipokeBat (C ovo cr)) he 1000 (.sub [])
    (by simp [Frame.Ab.Gam, slotAtPath])
  have hok := List.all_eq_true.1 ipoke_check r hr
  simp only [frameOK, Bool.and_eq_true] at hok
  obtain ⟨⟨h1, h2⟩, h3⟩ := hok
  have e1 := Frame.slotAtPath_sub _ gr (isSubAt_eq h1)
  have e2 := Frame.slotAtPath_sub _ gr (isSubAt_eq h2)
  have e3 := Frame.slotAtPath_sub _ gr (isSubAt_eq h3)
  obtain ⟨b, hb'⟩ : ∃ b, slot? 2 cr = some b := by
    rw [hb, cor_eq]; exact ⟨_, rfl⟩
  rw [slot2_path] at hb'
  cases x with
  | atom _ => simp [slotAtPath] at e1; simp [slotAtPath, hb'] at e1
  | cell prod cr' =>
    refine ⟨prod, cr', rfl, ?_, ?_, ?_⟩
    · rw [slot2_path, slot2_path]; simpa [slotAtPath] using e1
    · rw [slot6_path, slot6_path]; simpa [slotAtPath] using e2
    · rw [slot15_path, slot15_path]; simpa [slotAtPath] using e3

/-- Every core the pill reaches by pokes has the pill's battery, and the
library of `cor` under axis `15`. -/
theorem pokeReach_frame {cr : Noun} (h : PokeReach cr) :
    slot? 2 cr = slot? 2 cor ∧ slot? 6 cr = slot? 6 cor ∧ slot? 15 cr = slot? 15 cor := by
  induction h with
  | start => exact ⟨rfl, rfl, rfl⟩
  | poke _ hp _ ih =>
    obtain ⟨prod, cr', e, h2, h6, h15⟩ := poke_frame ih.1 hp
    simp only [Noun.cell.injEq] at e
    obtain ⟨-, rfl⟩ := e
    exact ⟨h2.trans ih.1, h6.trans ih.2.1, h15.trans ih.2.2⟩

/-- **`PokeFrame`** holds of every core with `CorIn`. -/
theorem pokeFrame_corIn {cr : Noun} (hc : CorIn cr) : PokeFrame cr := by
  intro ovo x h
  obtain ⟨prod, cr', e, -, -, h15⟩ := poke_frame (pokeReach_frame hc.2.2).1 h
  exact ⟨prod, cr', e, h15⟩

end Compiler
end Formalization
