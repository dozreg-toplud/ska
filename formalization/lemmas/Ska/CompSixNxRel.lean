import lemmas.Ska.CompSixLSWrap
import lemmas.Ska.CompTenLS

/-!
# `[6 c a b]` under `%next`: the relation of a forked result

README Gaps 12.36.  Under a goal `%next` the result of a `%6` is never flat
(`CompSixLSCheck.lean`, `tally`), so no `LOKS` member is a `%6`.  Its result
is a one-level tree whose forks `+past-fork` may wrap: with a calling test
each branch's need `a` at fork label `o` becomes `[bunt ~ [o a]~]`, so the
labels of the entries repeat.  The relation is stated on the UNWRAPPED need
`nexU`: its labels are distinct, so `RunOKLS` holds of it as it stands.
`+kern` walks the real need as `nexU` (`Unwraps.walkEq`, from
`walkLazy_wrap`).  Checked before any proof in `CompSixNxCheck.lean`.

* `WrapSide`, `Unwraps` (the real need is `nexU` with some fork sides
  wrapped at their own labels), `unwraps_refl`, `Unwraps.walkEq`.
* `Tree1` (every fork's two needs flat, every bond flat), `flat_tree1`.
* `AskNodup` (the labels of the entries that ask something are distinct).
* `RunOKLT` (the result relation: `nexU` with the run's jump, `Unwraps`,
  `Tree1` of `nexU`, `RunOKLS` of `nexU`), `RunOKLS.toT`.
* `LOKT x` (`LOKS x` with `RunOKLT` and no `Flat` of the result), `LOKTE x`
  (`LOKT` at goals without entries, as `LOKSE`), `LOKS.toT`, `LOKSE.toTE`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Wrapped forks -/

/-- **One fork side of the real need against the unwrapped one**: the same,
or the wrapper `[bunt ~ [o a]~]` of `+past-fork` at the side's own label. -/
def WrapSide (e e' : Nat × Lazy S) : Prop :=
  e = e' ∨ (e.1 = e'.1 ∧ e.2 = mk Sure.bunt [] [(e'.1, e'.2)])

/-- **The real need is the unwrapped one with some fork sides wrapped.** -/
def Unwraps (l u : Lazy S) : Prop :=
  l.sure = u.sure ∧ l.bond = u.bond ∧
    Forall2 (fun (e e' : ForkE S) => WrapSide e.1 e'.1 ∧ WrapSide e.2 e'.2) l.fork u.fork

theorem forall2_refl {α : Type} {R : α → α → Prop} (h : ∀ a, R a a) : ∀ l : List α, Forall2 R l l
  | [] => Forall2.nil
  | a :: l => Forall2.cons (h a) (forall2_refl h l)

theorem unwraps_refl (l : Lazy S) : Unwraps l l :=
  ⟨rfl, rfl, forall2_refl (fun _ => ⟨Or.inl rfl, Or.inl rfl⟩) _⟩

theorem wrapSide_walk {f : Nat → Sure S → CM Map Unit} (hf : ∀ (o : Nat) (g : Gen Map), f o Sure.bunt g = some ((), g))
    {e e' : Nat × Lazy S} (h : WrapSide e e') : e.1 = e'.1 ∧ walkLazy f e.1 e.2 = walkLazy f e'.1 e'.2 := by
  rcases h with rfl | ⟨h1, h2⟩
  · exact ⟨rfl, rfl⟩
  · refine ⟨h1, ?_⟩
    rw [h2, h1]
    exact walkLazy_wrap hf e'.1 e'.2

theorem walkForks_unwraps {f : Nat → Sure S → CM Map Unit} (hf : ∀ (o : Nat) (g : Gen Map), f o Sure.bunt g = some ((), g))
    {F F' : List (ForkE S)}
    (h : Forall2 (fun (e e' : ForkE S) => WrapSide e.1 e'.1 ∧ WrapSide e.2 e'.2) F F') :
    walkForks f F = walkForks f F' := by
  induction h with
  | nil => rfl
  | @cons a b as bs hab _ ih =>
    obtain ⟨⟨oy, y⟩, ⟨on, n⟩⟩ := a
    obtain ⟨⟨oy', y'⟩, ⟨on', n'⟩⟩ := b
    obtain ⟨e1, w1⟩ := wrapSide_walk hf hab.1
    obtain ⟨e2, w2⟩ := wrapSide_walk hf hab.2
    simp only at e1 e2 w1 w2
    simp only [walkForks, w1, w2, ih]

theorem forall2_isEmpty {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β} (h : Forall2 R l l') :
    l.isEmpty = l'.isEmpty := by
  cases h <;> rfl

/-- **`+kern`'s walks see the real need as the unwrapped one.** -/
theorem Unwraps.walkEq {l u : Lazy S} (h : Unwraps l u) : WalkEq (Map := Map) l u := by
  intro f hf o
  rcases l with ⟨s, F, B⟩
  rcases u with ⟨s', F', B'⟩
  obtain ⟨hs, hb, hF⟩ := h
  simp only [sure_mk, bond_mk, fork_mk] at hs hb hF
  subst hs hb
  simp only [walkLazy, forall2_isEmpty hF, walkForks_unwraps hf hF]

/-! ## The shape -/

/-- **A one-level tree**: every fork's two needs flat, every bond flat. -/
def Tree1 (u : Lazy S) : Prop := (∀ e ∈ u.fork, Flat e.1.2 ∧ Flat e.2.2) ∧ FlatB u.bond

theorem flat_tree1 {l : Lazy S} (h : Flat l) : Tree1 l := by
  refine ⟨fun e he => ?_, h.2⟩
  rw [h.1] at he
  cases he

/-- **The labels of the entries that ask something are distinct.** -/
def AskNodup (l : Lazy S) : Prop :=
  (((entries l).filter fun e => !noneEquivalent e.2.sure).map Prod.fst).Nodup

/-! ## The relation and the hypothesis -/

/-- **The result relation of a run whose result may be forked**: an
unwrapped `nexU` with the run's jump, the real need `nex` its wrapping,
`nexU` a one-level tree, and `RunOKLS` of `nexU`. -/
def RunOKLT (lib : Lib) (N : Needs) (P : Noun → Prop) (f : Noun) (L : Lazy S) (th : Jmp) (Q : Wit) (x : Bool)
    (g0 g1 : Gen Map) (nex : NextL S) : Prop :=
  ∃ nexU : NextL S, nexU.th = nex.th ∧ Unwraps nex.laz nexU.laz ∧ Tree1 nexU.laz ∧
    RunOKLS (Map := Map) lib N P f L th Q x g0 g1 nexU

theorem RunOKLS.toT {lib : Lib} {N : Needs} {P : Noun → Prop} {f : Noun} {L : Lazy S} {th : Jmp} {Q : Wit}
    {x : Bool} {g0 g1 : Gen Map} {nex : NextL S} (h : RunOKLS (Map := Map) lib N P f L th Q x g0 g1 nex)
    (hf : Flat nex.laz) : RunOKLT (Map := Map) lib N P f L th Q x g0 g1 nex :=
  ⟨nex, rfl, unwraps_refl _, flat_tree1 hf, h⟩

/-- **`LOKS` for runs whose result may be forked**: the premises of
`LOKS.run`, and its conclusions with `RunOKLT` in place of `RunOKLS` and no
`Flat` of the result. -/
structure LOKT (x : Bool) (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop) (f : Noun) (nm : Nomm) : Prop where
  clean : ∀ {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    Clean L.sure.ned → runLC env sup nm (CGoalL.next L th) region g0 = some (nex, g1) → Clean nex.laz.sure.ned
  run : ∀ {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    1 ≤ th.there → th.there < g0.bo → th.args = [] → th.there ∉ (entries L).map Prod.fst → Distinct L.sure.ned →
    (∀ x, NMem L.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) →
    (∀ e ∈ entries L, e.1 < g0.bo ∧ ∃ B th', HoonMap.get g0.blocks e.1 = some ⟨[], B, Termin.hop th'⟩) →
    ((entries L).map Prod.fst).Nodup →
    (∀ e ∈ entries L, Distinct e.2.sure.ned ∧
      ∀ x, NMem e.2.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) →
    Flat L → Clean L.sure.ned → (∀ e ∈ entries L, Clean e.2.sure.ned) →
    runLC env sup nm (CGoalL.next L th) region g0 = some (nex, g1) →
    (∃ Q, RunOKLT (Map := Map) lib N P f L th Q x g0 g1 nex) ∧ nex.th.there ∉ (entries nex.laz).map Prod.fst ∧
      (nex.th = th ∨ g0.bo ≤ nex.th.there) ∧ (∀ e ∈ entries nex.laz, Clean e.2.sure.ned)

/-- **`LOKT` at goals without entries** (as `LOKSE` is `LOKS`): the goal
`L` of every run with no entry, so the premises on entries go. -/
structure LOKTE (x : Bool) (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop) (f : Noun) (nm : Nomm) : Prop where
  clean : ∀ {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    entries L = [] → Clean L.sure.ned → runLC env sup nm (CGoalL.next L th) region g0 = some (nex, g1) →
    Clean nex.laz.sure.ned
  run : ∀ {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    entries L = [] → sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    1 ≤ th.there → th.there < g0.bo → th.args = [] → Distinct L.sure.ned →
    (∀ x, NMem L.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) → Clean L.sure.ned →
    runLC env sup nm (CGoalL.next L th) region g0 = some (nex, g1) →
    (∃ Q, RunOKLT (Map := Map) lib N P f L th Q x g0 g1 nex) ∧ nex.th.there ∉ (entries nex.laz).map Prod.fst ∧
      (nex.th = th ∨ g0.bo ≤ nex.th.there) ∧ (∀ e ∈ entries nex.laz, Clean e.2.sure.ned)

theorem entries_nil_flat {L : Lazy S} (h : entries L = []) : Flat L := by
  rcases L with ⟨s, F, B⟩
  cases F with
  | cons e F => cases e with | mk a b => cases a; cases b; simp [entries, forkEntries] at h
  | nil =>
    cases B with
    | nil => exact flat_ofSure s
    | cons e B => cases e; simp [entries, bondEntries] at h

/-- **Every `LOKS` member meets `LOKT`.** -/
theorem LOKS.toT {x : Bool} {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (H : LOKS (S := S) (Map := Map) x lib N env P f nm) : LOKT (S := S) (Map := Map) x lib N env P f nm := by
  refine ⟨H.clean, fun c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 hr => ?_⟩
  obtain ⟨⟨Q, R⟩, j1, j2, hf, hc⟩ := H.run c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 hr
  exact ⟨⟨Q, R.toT hf⟩, j1, j2, hc⟩

/-- **Every `LOKT` member meets `LOKTE`.** -/
theorem LOKT.toE {x : Bool} {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (H : LOKT (S := S) (Map := Map) x lib N env P f nm) : LOKTE (S := S) (Map := Map) x lib N env P f nm := by
  refine ⟨fun _ c hr => H.clean c hr, fun he c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 hr => ?_⟩
  exact H.run c1 c2 c3 c4 c5 c6 c7 c8 c9 (by rw [he]; simp) c10 c11 (by rw [he]; simp) (by rw [he]; simp)
    (by rw [he]; simp) (entries_nil_flat he) c12 (by rw [he]; simp) hr

end Comp
end SkaModel
end Formalization
