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
gives it (`DriverHyp`, stated over a block invariant `BInv` that every pass
keeps, meant as `ParNodup` and `PassOK`, and an invariant `TInv` of the
blocks, `topo` and `rev`, meant as `TopoOK` with `rev` listing the
predecessors), then `optimizeF` keeps the code on blocks with `BInv`
(`Keeps`: on entries with `ReadsOK` and `ArgsOK`, the same `execEntry`, and
both kept).  The fields proved so far are in `OptDriverFields.lean`.  Termination of `+optimize` is the named hypothesis
`OptHalts`: some fuel is enough.  A measure that proves it: every
structural pass that reports a change removes a block (`+remove-hops`), turns
a two-way end into a hop (`+remove-useless-branching`) or makes a jump skip a
block on an acyclic CFG (`+remove-empty-middle`), so the triple (number of
blocks, weight of the two-way ends, sum over the jumps of the rank of the
target) decreases lexicographically.  `+alias` reports a change when it folds
a branch, drops a block, or turns a `%brn` on a known loob into a `%brz`; the
last keeps the blocks and the two-way ends, so the weight counts a `%brn` `2`
and the other two-way ends `1` (`Compiler/OptLinkTotal*.lean`, README Gaps
13).
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
them, over two invariants: `BInv` of the blocks alone, which every pass keeps
whatever its change flag, and `TInv` of the blocks, `topo` and `rev`, which
`+bb-topo` with `+rev-cfg` makes and which a structural pass needs to keep
only when it reports no change (the driver then keeps the old `topo` and
`rev`). -/
structure DriverHyp (fuel : Nat) (P : Passes Map) (BInv : Map Blob → Prop)
    (TInv : Map Blob → List Nat → Map (List Nat) → Prop) : Prop where
  topo : ∀ bl topo, BInv bl → bbTopo fuel bl = some topo → TInv bl topo (revCfg bl topo)
  hops : ∀ bl topo rev ch bl', BInv bl → TInv bl topo rev → removeHops fuel bl rev topo = some (ch, bl') →
    KeepsB bl bl' ∧ BInv bl' ∧ (ch = false → TInv bl' topo rev)
  rub : ∀ bl topo rev ch bl', BInv bl → removeUselessBranching bl = some (ch, bl') →
    KeepsB bl bl' ∧ BInv bl' ∧ (TInv bl topo rev → ch = false → TInv bl' topo rev)
  middle : ∀ bl topo rev ch bl', BInv bl → removeEmptyMiddle fuel bl = some (ch, bl') →
    KeepsB bl bl' ∧ BInv bl' ∧ (TInv bl topo rev → ch = false → TInv bl' topo rev)
  alias : ∀ n bl topo rev f bl', BInv bl → TInv bl topo rev → P.alias n bl rev topo = some (f, bl') →
    KeepsB bl bl' ∧ BInv bl' ∧
      TInv bl' (topo.filter fun o => (HoonMap.get bl' o).isSome)
        (revCfg bl' (topo.filter fun o => (HoonMap.get bl' o).isSome))
  trim : ∀ bl topo rev bl', BInv bl → TInv bl topo rev → P.trim bl topo rev = some bl' →
    KeepsB bl bl' ∧ BInv bl' ∧ TInv bl' topo rev
  dead : ∀ bl topo rev bl', BInv bl → TInv bl topo rev → removeDeadCode bl topo.reverse = some bl' →
    KeepsB bl bl' ∧ BInv bl' ∧ TInv bl' topo rev
  switch : ∀ bl bl', BInv bl → P.switch bl = some bl' → KeepsB bl bl'

theorem KeepsB.trans {bl bl1 bl2 : Map Blob} (h1 : KeepsB bl bl1) (h2 : KeepsB bl1 bl2) : KeepsB bl bl2 :=
  fun c hc => keeps_trans (h1 c hc) (h2 (withBlocks c bl1) rfl)

theorem KeepsB.refl (bl : Map Blob) : KeepsB bl bl := by
  intro c hc; subst hc; exact keeps_refl c

variable {fuel : Nat} {P : Passes Map} {BInv : Map Blob → Prop}
  {TInv : Map Blob → List Nat → Map (List Nat) → Prop}

theorem structLoop_keeps (H : DriverHyp fuel P BInv TInv) : ∀ (n : Nat) (bl : Map Blob) topo rev r,
    BInv bl → TInv bl topo rev → structLoop fuel n bl topo rev = some r →
      KeepsB bl r.2.2 ∧ BInv r.2.2 ∧ TInv r.2.2 r.1 r.2.1
  | 0, _, _, _, _, _, _, h => by cases h
  | n + 1, bl, topo, rev, r, hb, hi, h => by
    simp only [structLoop, Option.bind_eq_some_iff] at h
    obtain ⟨⟨c1, b1⟩, h1, ⟨c2, b2⟩, h2, ⟨c3, b3⟩, h3, h⟩ := h
    obtain ⟨k1, j1, i1⟩ := H.hops _ _ _ _ _ hb hi h1
    obtain ⟨k2, j2, i2⟩ := H.rub b1 topo rev _ _ j1 h2
    obtain ⟨k3, j3, i3⟩ := H.middle b2 topo rev _ _ j2 h3
    simp only at h
    by_cases hc : (c1 || c2 || c3) = false
    · simp only [hc, Bool.not_false, if_true, Option.some.injEq] at h
      subst h
      simp only [Bool.or_eq_false_iff] at hc
      exact ⟨k1.trans (k2.trans k3), j3, i3 (i2 (i1 hc.1.1) hc.1.2) hc.2⟩
    · simp only [Bool.not_eq_false] at hc
      simp only [hc, Bool.not_true, if_false, Bool.false_eq_true] at h
      obtain ⟨topo', ht, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k4, j4, i4⟩ := structLoop_keeps H n b3 topo' _ r j3 (H.topo _ _ j3 ht) h
      exact ⟨k1.trans (k2.trans (k3.trans k4)), j4, i4⟩

theorem optimizeOnce_keeps (H : DriverHyp fuel P BInv TInv) {s : Straight Map} {ch : Bool} {s' : Straight Map}
    (hb : BInv s.blocks) (h : optimizeOnce fuel P s = some (ch, s')) : Keeps s s' ∧ BInv s'.blocks := by
  simp only [optimizeOnce, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨topo0, ht0, ⟨tp, rv, bs⟩, hs, ⟨fa, ba⟩, ha, bt, htr, bd, hd, ⟨c1, b1⟩, h1, ⟨c2, b2⟩, h2,
    ⟨c3, b3⟩, h3, h⟩ := h
  simp only [Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  obtain ⟨k0, j0, i0⟩ := structLoop_keeps H fuel s.blocks topo0 _ _ hb (H.topo _ _ hb ht0) hs
  obtain ⟨ka, ja, ia⟩ := H.alias _ _ _ _ _ _ j0 i0 ha
  obtain ⟨kt, jt, it⟩ := H.trim _ _ _ _ ja ia htr
  obtain ⟨kd, jd, idd⟩ := H.dead _ _ _ _ jt it hd
  obtain ⟨k1, j1, -⟩ := H.hops _ _ _ _ _ jd idd h1
  obtain ⟨k2, j2, -⟩ := H.rub b1 [] HoonMap.empty _ _ j1 h2
  obtain ⟨k3, j3, -⟩ := H.middle b2 [] HoonMap.empty _ _ j2 h3
  exact ⟨(k0.trans (ka.trans (kt.trans (kd.trans (k1.trans (k2.trans k3)))))) s rfl, j3⟩

theorem optLoop_keeps (H : DriverHyp fuel P BInv TInv) : ∀ (n : Nat) (s s' : Straight Map),
    BInv s.blocks → optLoop fuel P n s = some s' → Keeps s s' ∧ BInv s'.blocks
  | 0, _, _, _, h => by cases h
  | n + 1, s, s', hb, h => by
    simp only [optLoop, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ch, s1⟩, h1, h⟩ := h
    obtain ⟨k1, j1⟩ := optimizeOnce_keeps H hb h1
    cases ch
    · simp only [Bool.false_eq_true, if_false, Option.some.injEq] at h
      subst h; exact ⟨k1, j1⟩
    · simp only [if_true] at h
      obtain ⟨k2, j2⟩ := optLoop_keeps H n s1 s' j1 h
      exact ⟨keeps_trans k1 k2, j2⟩

/-- **`+optimize` keeps the code**, given that its passes do, on blocks with
the block invariant. -/
theorem optimize_keeps (H : DriverHyp fuel P BInv TInv) {s s' : Straight Map} (hb : BInv s.blocks)
    (h : optimizeF fuel P s = some s') : Keeps s s' := by
  simp only [optimizeF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨s1, h1, bl, hsw, rfl⟩ := h
  obtain ⟨k1, j1⟩ := optLoop_keeps H fuel s s1 hb h1
  exact keeps_trans k1 (H.switch _ _ j1 hsw s1 rfl)

end

end Opt
end SkaModel
end Formalization
