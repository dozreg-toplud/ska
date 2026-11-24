import lemmas.Ska.OptBranch
import lemmas.Ska.OptHops
import lemmas.Ska.OptMiddle
import lemmas.Ska.OptDead

/-!
# `+optimize-once` and `+optimize`

`structLoop`: the structural `|-` of `+optimize-once`: `+remove-hops` with
the current `rev` and `topo`, `+remove-useless-branching`,
`+remove-empty-middle`; on no change it returns `topo` and `rev` as they were
at the start of the turn (as the Hoon does), else it recomputes them by
`+bb-topo` and `+rev-cfg` and turns again.  `optimizeOnce` then runs `+alias`,
filters `topo` by the blocks that remain, recomputes `rev`, runs
`+trim-trace-hints`, `+remove-dead-code` on `(flop topo)`, and the three
structural passes with that `rev` and `topo`.  `optLoop` is the loop of
`+optimize` and `optimizeF` adds `+switch-chains`.  `+alias`,
`+trim-trace-hints` and `+switch-chains` are parameters (`Passes`).  The Hoon
loops have no fuel: the fuel here is the Hoon when it suffices, and `none`
otherwise (or on a crash).

`optimize_keeps`: if every pass keeps the code at the arguments the driver
gives it (`DriverHyp`, stated over an invariant `Inv` of the blocks, `topo`
and `rev` that the caller chooses, meant as `TopoOK` with `rev` the reverse
CFG), then `optimizeF` keeps the code.  `rub_keeps` discharges the semantic
half of the field `rub`.  Termination of `+optimize` is the named hypothesis
`OptHalts`: some fuel is enough.  A measure that would prove it: every
structural pass that reports a change removes a block (`+remove-hops`), turns
a two-way end into a hop (`+remove-useless-branching`) or makes a jump skip a
block on an acyclic CFG (`+remove-empty-middle`), so the pair (number of
blocks, number of two-way ends, sum over jumps of the length of the chain of
empty blocks after it) decreases lexicographically; `+alias` reports a change
only when it folds a branch or drops a block, which decreases the same pair,
but that is a fact about `+alias` still to be proved.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock

variable {Map : Type → Type} [HoonMap Map]

/-- The passes the driver takes as parameters. -/
structure Passes (Map : Type → Type) [HoonMap Map] where
  alias : Nat → Map Blob → Map (List Nat) → List Nat → Option (Bool × Map Blob)
  trim : Map Blob → List Nat → Map (List Nat) → Option (Map Blob)
  switch : Map Blob → Option (Map Blob)

section
variable [MapKeys Map]

/-- The structural loop of `+optimize-once`. -/
def structLoop (fuel : Nat) : Nat → Map Blob → List Nat → Map (List Nat) →
    Option (List Nat × Map (List Nat) × Map Blob)
  | 0, _, _, _ => none
  | n + 1, bl, topo, rev =>
    (removeHops fuel bl rev topo).bind fun r1 =>
    (removeUselessBranching r1.2).bind fun r2 =>
    (removeEmptyMiddle fuel r2.2).bind fun r3 =>
    if !(r1.1 || r2.1 || r3.1) then some (topo, rev, r3.2) else
    (bbTopo fuel r3.2).bind fun topo' => structLoop fuel n r3.2 topo' (revCfg r3.2 topo')

/-- `+optimize-once`. -/
def optimizeOnce (fuel : Nat) (P : Passes Map) (s : Straight Map) : Option (Bool × Straight Map) :=
  (bbTopo fuel s.blocks).bind fun topo0 =>
  (structLoop fuel fuel s.blocks topo0 (revCfg s.blocks topo0)).bind fun r =>
  (P.alias s.nargs r.2.2 r.2.1 r.1).bind fun ra =>
  let topo := r.1.filter fun o => (HoonMap.get ra.2 o).isSome
  let rev := revCfg ra.2 topo
  (P.trim ra.2 topo rev).bind fun bt =>
  (removeDeadCode bt topo.reverse).bind fun bd =>
  (removeHops fuel bd rev topo).bind fun r1 =>
  (removeUselessBranching r1.2).bind fun r2 =>
  (removeEmptyMiddle fuel r2.2).map fun r3 =>
  (ra.1 || r1.1 || r2.1 || r3.1, withBlocks s r3.2)

/-- The loop of `+optimize`. -/
def optLoop (fuel : Nat) (P : Passes Map) : Nat → Straight Map → Option (Straight Map)
  | 0, _ => none
  | n + 1, s => (optimizeOnce fuel P s).bind fun r => if r.1 then optLoop fuel P n r.2 else some r.2

/-- `+optimize`. -/
def optimizeF (fuel : Nat) (P : Passes Map) (s : Straight Map) : Option (Straight Map) :=
  (optLoop fuel P fuel s).bind fun s' => (P.switch s'.blocks).map (withBlocks s')

/-- **Termination of `+optimize`**, as a hypothesis: some fuel suffices. -/
def OptHalts (P : Passes Map) (s : Straight Map) : Prop := ∃ fuel, (optimizeF fuel P s).isSome

/-- A pass on blocks keeps every function with those blocks. -/
def KeepsB (bl bl' : Map Blob) : Prop := ∀ c : Straight Map, c.blocks = bl → Keeps c (withBlocks c bl')

/-- **What the driver assumes of the passes**, at the arguments it gives
them, over an invariant `Inv` of the blocks, `topo` and `rev`. -/
structure DriverHyp (fuel : Nat) (P : Passes Map) (Inv : Map Blob → List Nat → Map (List Nat) → Prop) :
    Prop where
  topo : ∀ bl topo, bbTopo fuel bl = some topo → Inv bl topo (revCfg bl topo)
  hops : ∀ bl topo rev ch bl', Inv bl topo rev → removeHops fuel bl rev topo = some (ch, bl') →
    KeepsB bl bl' ∧ (ch = false → Inv bl' topo rev)
  rub : ∀ bl topo rev ch bl', removeUselessBranching bl = some (ch, bl') →
    KeepsB bl bl' ∧ (Inv bl topo rev → ch = false → Inv bl' topo rev)
  middle : ∀ bl topo rev ch bl', removeEmptyMiddle fuel bl = some (ch, bl') →
    KeepsB bl bl' ∧ (Inv bl topo rev → ch = false → Inv bl' topo rev)
  alias : ∀ n bl topo rev f bl', Inv bl topo rev → P.alias n bl rev topo = some (f, bl') →
    KeepsB bl bl' ∧
      Inv bl' (topo.filter fun o => (HoonMap.get bl' o).isSome)
        (revCfg bl' (topo.filter fun o => (HoonMap.get bl' o).isSome))
  trim : ∀ bl topo rev bl', Inv bl topo rev → P.trim bl topo rev = some bl' → KeepsB bl bl' ∧ Inv bl' topo rev
  dead : ∀ bl topo rev bl', Inv bl topo rev → removeDeadCode bl topo.reverse = some bl' →
    KeepsB bl bl' ∧ Inv bl' topo rev
  switch : ∀ bl bl', P.switch bl = some bl' → KeepsB bl bl'

/-- The semantic half of the field `rub` holds. -/
theorem rub_keepsB {bl bl' : Map Blob} {ch : Bool} (h : removeUselessBranching bl = some (ch, bl')) :
    KeepsB bl bl' := by
  intro c hc; subst hc; exact rub_keeps c h

theorem KeepsB.trans {bl bl1 bl2 : Map Blob} (h1 : KeepsB bl bl1) (h2 : KeepsB bl1 bl2) : KeepsB bl bl2 :=
  fun c hc => keeps_trans (h1 c hc) (h2 (withBlocks c bl1) rfl)

theorem KeepsB.refl (bl : Map Blob) : KeepsB bl bl := by
  intro c hc; subst hc; exact keeps_refl c

variable {fuel : Nat} {P : Passes Map} {Inv : Map Blob → List Nat → Map (List Nat) → Prop}

theorem structLoop_keeps (H : DriverHyp fuel P Inv) : ∀ (n : Nat) (bl : Map Blob) topo rev r,
    Inv bl topo rev → structLoop fuel n bl topo rev = some r → KeepsB bl r.2.2 ∧ Inv r.2.2 r.1 r.2.1
  | 0, _, _, _, _, _, h => by cases h
  | n + 1, bl, topo, rev, r, hi, h => by
    simp only [structLoop, Option.bind_eq_some_iff] at h
    obtain ⟨⟨c1, b1⟩, h1, ⟨c2, b2⟩, h2, ⟨c3, b3⟩, h3, h⟩ := h
    obtain ⟨k1, i1⟩ := H.hops _ _ _ _ _ hi h1
    obtain ⟨k2, i2⟩ := H.rub b1 topo rev _ _ h2
    obtain ⟨k3, i3⟩ := H.middle b2 topo rev _ _ h3
    simp only at h
    by_cases hc : (c1 || c2 || c3) = false
    · simp only [hc, Bool.not_false, if_true, Option.some.injEq] at h
      subst h
      simp only [Bool.or_eq_false_iff] at hc
      exact ⟨k1.trans (k2.trans k3), i3 (i2 (i1 hc.1.1) hc.1.2) hc.2⟩
    · simp only [Bool.not_eq_false] at hc
      simp only [hc, Bool.not_true, if_false, Bool.false_eq_true] at h
      obtain ⟨topo', ht, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k4, i4⟩ := structLoop_keeps H n b3 topo' _ r (H.topo _ _ ht) h
      exact ⟨k1.trans (k2.trans (k3.trans k4)), i4⟩

theorem optimizeOnce_keeps (H : DriverHyp fuel P Inv) {s : Straight Map} {ch : Bool} {s' : Straight Map}
    (h : optimizeOnce fuel P s = some (ch, s')) : Keeps s s' := by
  simp only [optimizeOnce, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨topo0, ht0, ⟨tp, rv, bs⟩, hs, ⟨fa, ba⟩, ha, bt, htr, bd, hd, ⟨c1, b1⟩, h1, ⟨c2, b2⟩, h2,
    ⟨c3, b3⟩, h3, h⟩ := h
  simp only [Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  obtain ⟨k0, i0⟩ := structLoop_keeps H fuel s.blocks topo0 _ _ (H.topo _ _ ht0) hs
  obtain ⟨ka, ia⟩ := H.alias _ _ _ _ _ _ i0 ha
  obtain ⟨kt, it⟩ := H.trim _ _ _ _ ia htr
  obtain ⟨kd, idd⟩ := H.dead _ _ _ _ it hd
  obtain ⟨k1, -⟩ := H.hops _ _ _ _ _ idd h1
  obtain ⟨k2, -⟩ := H.rub b1 [] HoonMap.empty _ _ h2
  obtain ⟨k3, -⟩ := H.middle b2 [] HoonMap.empty _ _ h3
  exact (k0.trans (ka.trans (kt.trans (kd.trans (k1.trans (k2.trans k3)))))) s rfl

theorem optLoop_keeps (H : DriverHyp fuel P Inv) : ∀ (n : Nat) (s s' : Straight Map),
    optLoop fuel P n s = some s' → Keeps s s'
  | 0, _, _, h => by cases h
  | n + 1, s, s', h => by
    simp only [optLoop, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ch, s1⟩, h1, h⟩ := h
    have k1 := optimizeOnce_keeps H h1
    cases ch
    · simp only [Bool.false_eq_true, if_false, Option.some.injEq] at h
      subst h; exact k1
    · simp only [if_true] at h
      exact keeps_trans k1 (optLoop_keeps H n s1 s' h)

/-- **`+optimize` keeps the code**, given that its passes do. -/
theorem optimize_keeps (H : DriverHyp fuel P Inv) {s s' : Straight Map} (h : optimizeF fuel P s = some s') :
    Keeps s s' := by
  simp only [optimizeF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨s1, h1, bl, hsw, rfl⟩ := h
  exact keeps_trans (optLoop_keeps H fuel s s1 h1) (H.switch _ _ hsw s1 rfl)

end

end Opt
end SkaModel
end Formalization
