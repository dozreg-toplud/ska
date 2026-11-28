import lemmas.Glue.NskProxy

/-!
# Glue: the frame of `SDW` (track G, fourteenth pass; toward `SDWEndC`)

`SDW` (`Glue/NskProxy.lean`) reads the generator's `cond` and `re`, so the frame `KS` of
`SplitDefBase.lean` (a step maps an `SDS` state to an `SDS` state) does not carry over: a step
must also not give a key to a register that a split reads without defining it.  The frame here
is a RELATION between the state before and after a step, `GrowSD g g'`:

* every block of `g'` is a block of `g` (same key, same blob) or has `SDBody`;
* every `cond` key of `g'` that is not one of `g` is at least `g.re` (`+proxy` allocates its key
  at the old `re`: `proxy_fresh`);
* `re` does not go down.

`GrowSD` is reflexive and transitive, and `SDW` is kept along it (`sdw_grow`).  `KSW P m`
says that `m` relates its states by `GrowSD` and its product meets `P`; it has the
combinators of `KS` (`pure'`, `bind'`, `mono`, `fail`, `crash`, `ite'`), so the port of
`SplitDefRun.lean` is the port of its primitive steps (`putBlock`, the register allocations,
`+proxy`) to `GrowSD`, then the same proof text.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt Comp Raw

variable {Map : Type → Type} [HoonMap Map]

/-- **What a step may do to the state and keep `SDW`.** -/
def GrowSD (g g' : Comp.Gen Map) : Prop :=
  (∀ o b, HoonMap.get g'.blocks o = some b → HoonMap.get g.blocks o = some b ∨ SDBody b.body) ∧
    (∀ s, HoonMap.get g.cond s = Option.none → HoonMap.get g'.cond s ≠ Option.none → g.re ≤ s) ∧
    g.re ≤ g'.re

theorem GrowSD.refl (g : Comp.Gen Map) : GrowSD g g :=
  ⟨fun _ _ h => Or.inl h, fun _ h h' => absurd h h', Nat.le_refl _⟩

theorem GrowSD.trans {g g1 g2 : Comp.Gen Map} (h1 : GrowSD g g1) (h2 : GrowSD g1 g2) : GrowSD g g2 := by
  refine ⟨fun o b hb => ?_, fun s hs hs2 => ?_, Nat.le_trans h1.2.2 h2.2.2⟩
  · rcases h2.1 o b hb with h | h
    · exact h1.1 o b h
    · exact Or.inr h
  · cases e : HoonMap.get g1.cond s with
    | none => exact Nat.le_trans h1.2.2 (h2.2.1 s e hs2)
    | some v => exact h1.2.1 s hs (by rw [e]; simp)

/-- **`SDW` is kept along `GrowSD`.** -/
theorem sdw_grow {g g' : Comp.Gen Map} (hW : SDW g) (hG : GrowSD g g') : SDW g' := by
  intro o b hb i p s hp hs
  rcases hG.1 o b hb with hold | hsd
  · rcases hW o b hold i p s hp hs with h | ⟨hc, hlt⟩
    · exact Or.inl h
    · refine Or.inr ⟨?_, Nat.lt_of_lt_of_le hlt hG.2.2⟩
      cases e : HoonMap.get g'.cond s with
      | none => rfl
      | some v => exact absurd (hG.2.1 s hc (by rw [e]; simp)) (by omega)
  · exact Or.inl (hsd i p s hp hs)

/-- **`SDS` states are related to their `SDS` successors**: a step whose result has `SDS` and
that keeps `cond` and `re` in the `GrowSD` sense (no old block needed). -/
theorem growSD_of_sds {g g' : Comp.Gen Map} (h : SDS g')
    (hc : ∀ s, HoonMap.get g.cond s = Option.none → HoonMap.get g'.cond s ≠ Option.none → g.re ≤ s)
    (hr : g.re ≤ g'.re) : GrowSD g g' :=
  ⟨fun o b hb => Or.inr (h o b hb), hc, hr⟩

/-- **The frame of `SDW`**: the step relates its states by `GrowSD`, its product meets `P`. -/
structure KSW {α : Type} (P : α → Prop) (m : CM Map α) : Prop where
  k : ∀ g x g', m g = some (x, g') → GrowSD g g' ∧ P x

namespace KSW

theorem pure' {α : Type} {P : α → Prop} {a : α} (h : P a) : KSW P (pure a : CM Map α) := by
  constructor; intro g x g' e; cases e; exact ⟨GrowSD.refl g, h⟩

theorem bind' {α β : Type} {P : α → Prop} {Q : β → Prop} {m : CM Map α} {f : α → CM Map β}
    (hm : KSW P m) (hf : ∀ a, P a → KSW Q (f a)) : KSW Q (m >>= f) := by
  constructor
  intro g x g' e
  obtain ⟨a, g1, h1, h2⟩ := bind_some e
  obtain ⟨b1, pa⟩ := hm.k g a g1 h1
  obtain ⟨b2, qx⟩ := (hf a pa).k g1 x g' h2
  exact ⟨b1.trans b2, qx⟩

theorem mono {α : Type} {P Q : α → Prop} {m : CM Map α} (h : KSW P m) (hpq : ∀ a, P a → Q a) : KSW Q m := by
  constructor
  intro g x g' e
  obtain ⟨b1, p⟩ := h.k g x g' e
  exact ⟨b1, hpq x p⟩

theorem fail {α : Type} {P : α → Prop} : KSW P (fun _ => Option.none : CM Map α) := by
  constructor; intro g x g' h; cases h

theorem crash {α : Type} {P : α → Prop} : KSW P (crashM : CM Map α) := fail

theorem ite' {α : Type} {P : α → Prop} (c : Prop) [Decidable c] {a b : CM Map α} (ha : KSW P a) (hb : KSW P b) :
    KSW P (if c then a else b) := by
  split
  · exact ha
  · exact hb

/-- **A run in the frame keeps `SDW`.** -/
theorem sdw {α : Type} {P : α → Prop} {m : CM Map α} (h : KSW P m) {g g' : Comp.Gen Map} {x : α}
    (hW : SDW g) (e : m g = some (x, g')) : SDW g' ∧ P x :=
  let ⟨hG, hp⟩ := h.k g x g' e
  ⟨sdw_grow hW hG, hp⟩

end KSW

end Glue
end SkaModel
end Formalization
