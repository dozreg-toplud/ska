import lemmas.Ska.RawInvCLSARunSteps

/-!
# The mid-run fact with no state: the count of a tree's registers

README Gaps 14 (b), track D.  Track G's `KIMid.run` (`Glue/GuardCallsB.lean`)
asks a run from a goal whose sure needs each have distinct registers (`GD`)
to return such a lazy.  That is FALSE (`RawInvCLKIMidW.lean`): with two bonds
at one label, `+copy` merges one sure need of each run's tree with the same
entry of the other, and a register shared by two entries of the goal lands
twice in one sure need.  What holds is the count of `RawInvCLSARunBase.lean`
without the blocks: every register occurs in the result's tree at most as
often as in the goal's, plus once if the run allocated it.  So a goal whose
tree has distinct registers ACROSS its entries, and bonds at distinct labels
(`LG`), returns such a tree.  This file holds the frame of that count; it
asks nothing of the state (no `ATS`, no `SarSt`, no `Fresh`).

* `KUC ri m ro`: `re` and `bo` grow and every register occurs in `ro x` at
  most as often as in `ri`, plus once if fresh (`fr`); `ku_bind`, `ku_pure`,
  `ku_mono`, `ku_re`, `ku_emit`, `ku_addOps`, `ku_setTag`, `ku_get`,
  `ku_proxy`, `ku_fail`, `ku_ite`.
* `RB m`: `re` and `bo` grow (a step whose product carries no tree);
  `ku_ofRB`, `rb_bind`, `rb_pure`, `rb_re`, `rb_emit`, `rb_addOps`,
  `rb_setTag`, `rb_get`, `rb_proxy`, `rb_of`.
* `KURun rp`: every run of `rp` from an `LG` goal returns an `LG` result,
  grows `re` and `bo`, and has the count from `sarG goal` to `sarR x.laz`.
* `KUSteps`: the local steps the induction rests on.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The count of a step -/

/-- **The state-free count of a step**: `re` and `bo` grow, and every
register occurs in the output's trees at most as often as in the input's,
plus once if the step allocated it. -/
def KUC {α : Type} (ri : List Nat) (m : CM Map α) (ro : α → List Nat) : Prop :=
  ∀ (g : Comp.Gen Map) x g', m g = some (x, g') → g.re ≤ g'.re ∧ g.bo ≤ g'.bo ∧
    ∀ y, (ro x).count y ≤ ri.count y + fr g.re g'.re y

theorem ku_bind {α β : Type} {ri : List Nat} {r1 : α → List Nat} {ro : β → List Nat} {m : CM Map α}
    {f : α → CM Map β} (hm : KUC (Map := Map) ri m r1) (hf : ∀ a, KUC (Map := Map) (r1 a) (f a) ro) :
    KUC (Map := Map) ri (m >>= f) ro := by
  intro g x g' h
  obtain ⟨a, g1, h1, h2⟩ := bind_some h
  obtain ⟨l1, b1, c1⟩ := hm g a g1 h1
  obtain ⟨l2, b2, c2⟩ := hf a g1 x g' h2
  refine ⟨Nat.le_trans l1 l2, Nat.le_trans b1 b2, fun y => ?_⟩
  have := c1 y; have := c2 y; have := fr_add l1 l2 y
  omega

theorem ku_pure {α : Type} {ri : List Nat} {ro : α → List Nat} {a : α} (h : ∀ y, (ro a).count y ≤ ri.count y) :
    KUC (Map := Map) ri (pure a : CM Map α) ro := by
  intro g x g' e
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨Nat.le_refl _, Nat.le_refl _, fun y => by have := h y; omega⟩

theorem ku_mono {α : Type} {ri ri' : List Nat} {ro ro' : α → List Nat} {m : CM Map α} (h : KUC (Map := Map) ri m ro)
    (hi : ∀ y, ri.count y ≤ ri'.count y) (ho : ∀ x y, (ro' x).count y ≤ (ro x).count y) :
    KUC (Map := Map) ri' m ro' := by
  intro g x g' e
  obtain ⟨l1, b1, c1⟩ := h g x g' e
  exact ⟨l1, b1, fun y => by have := c1 y; have := hi y; have := ho x y; omega⟩

theorem ku_fail {α : Type} {ri : List Nat} {ro : α → List Nat} :
    KUC (Map := Map) ri (fun _ => Option.none : CM Map α) ro :=
  fun _ _ _ e => by cases e

theorem ku_ite {α : Type} {ri : List Nat} {ro : α → List Nat} (c : Prop) [Decidable c] {a b : CM Map α}
    (ha : KUC (Map := Map) ri a ro) (hb : KUC (Map := Map) ri b ro) : KUC (Map := Map) ri (if c then a else b) ro := by
  split
  · exact ha
  · exact hb

/-! ## Steps whose product carries no tree -/

/-- **`re` and `bo` grow.** -/
def RB {α : Type} (m : CM Map α) : Prop :=
  ∀ (g : Comp.Gen Map) x g', m g = some (x, g') → g.re ≤ g'.re ∧ g.bo ≤ g'.bo

/-- A step that grows `re` and `bo` passes any tree through. -/
theorem ku_ofRB {α : Type} {m : CM Map α} (h : RB (Map := Map) m) (ri : List Nat) :
    KUC (Map := Map) ri m (fun _ => ri) := by
  intro g x g' e
  obtain ⟨l, b⟩ := h g x g' e
  exact ⟨l, b, fun y => Nat.le_add_right _ _⟩

theorem rb_of {α : Type} {m : CM Map α} {ri : List Nat} {ro : α → List Nat} (h : KUC (Map := Map) ri m ro) :
    RB (Map := Map) m :=
  fun g x g' e => ⟨(h g x g' e).1, (h g x g' e).2.1⟩

theorem rb_bind {α β : Type} {m : CM Map α} {f : α → CM Map β} (hm : RB (Map := Map) m)
    (hf : ∀ a, RB (Map := Map) (f a)) : RB (Map := Map) (m >>= f) := by
  intro g x g' h
  obtain ⟨a, g1, h1, h2⟩ := bind_some h
  obtain ⟨l1, b1⟩ := hm g a g1 h1
  obtain ⟨l2, b2⟩ := hf a g1 x g' h2
  exact ⟨Nat.le_trans l1 l2, Nat.le_trans b1 b2⟩

theorem rb_pure {α : Type} (a : α) : RB (Map := Map) (pure a : CM Map α) := by
  intro g x g' e
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem rb_fail {α : Type} : RB (Map := Map) (fun _ => Option.none : CM Map α) :=
  fun _ _ _ e => by cases e

theorem rb_ite {α : Type} (c : Prop) [Decidable c] {a b : CM Map α}
    (ha : RB (Map := Map) a) (hb : RB (Map := Map) b) : RB (Map := Map) (if c then a else b) := by
  split
  · exact ha
  · exact hb

theorem rb_re : RB (Map := Map) (re : CM Map Nat) := by
  intro g x g' e
  rw [re_apply] at e
  simp only [Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨Nat.le_succ _, Nat.le_refl _⟩

theorem rb_emit (b : Blob) : RB (Map := Map) (emit b : CM Map Nat) := by
  intro g x g' e
  rw [emit_apply] at e
  simp only [Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨by simp [Gen.emitted], by simp [Gen.emitted]⟩

theorem rb_addOps (o : Nat) (A : List Pole) : RB (Map := Map) (addOps o A : CM Map Unit) := by
  intro g x g' e
  unfold addOps at e
  split at e
  · cases e; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · obtain ⟨b, _, e⟩ := Option.map_eq_some_iff.mp e
    cases e; exact ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem rb_setTag (o : Nat) (region : List Nat) : RB (Map := Map) (setTag o region : CM Map Unit) := by
  intro g x g' e
  unfold setTag at e
  cases e
  split <;> exact ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem rb_get : RB (Map := Map) (get : CM Map (Comp.Gen Map)) := by
  intro g x g' e
  rw [get_apply] at e
  cases e
  exact ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem rb_proxy (r o : Nat) : RB (Map := Map) (proxy r o : CM Map Nat) := by
  intro g x g' e
  unfold proxy at e
  simp only at e
  split at e
  · cases e; exact ⟨Nat.le_succ _, Nat.le_refl _⟩
  · obtain ⟨tag, _, e⟩ := Option.map_eq_some_iff.mp e
    cases e; exact ⟨Nat.le_succ _, Nat.le_refl _⟩

theorem ku_re (ri : List Nat) : KUC (Map := Map) ri (re : CM Map Nat) (fun r => ri ++ [r]) := by
  intro g x g' e
  rw [re_apply] at e
  simp only [Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  refine ⟨Nat.le_succ _, Nat.le_refl _, fun y => ?_⟩
  simp only [List.count_append, List.count_singleton, fr]
  by_cases e : g.re = y
  · subst e; simp
  · have : ¬ (g.re ≤ y ∧ y < g.re + 1) := fun h => e (by omega)
    simp [e, this]

theorem ku_emit (ri : List Nat) (b : Blob) : KUC (Map := Map) ri (emit b) (fun _ => ri) := ku_ofRB (rb_emit b) ri

theorem ku_addOps (ri : List Nat) (o : Nat) (A : List Pole) : KUC (Map := Map) ri (addOps o A) (fun _ => ri) :=
  ku_ofRB (rb_addOps o A) ri

theorem ku_setTag (ri : List Nat) (o : Nat) (region : List Nat) :
    KUC (Map := Map) ri (setTag o region) (fun _ => ri) := ku_ofRB (rb_setTag o region) ri

theorem ku_get (ri : List Nat) : KUC (Map := Map) ri (get : CM Map (Comp.Gen Map)) (fun _ => ri) := ku_ofRB rb_get ri

theorem ku_proxy (ri : List Nat) (r o : Nat) : KUC (Map := Map) ri (proxy r o) (fun _ => ri) := ku_ofRB (rb_proxy r o) ri

/-! ## The statement at run level -/

/-- **What a run owes, with no state**: from an `LG` goal, an `LG` result;
`re` and `bo` grow; every register occurs in the result's tree at most as
often as in the goal's, plus once if the run allocated it. -/
def KURun (rp : CGoalL S → List Nat → CM Map (NextL S)) : Prop :=
  ∀ (goal : CGoalL S) region (g g' : Comp.Gen Map) (x : NextL S), LG goal g → rp goal region g = some (x, g') →
    LG x.goal g' ∧ g.re ≤ g'.re ∧ g.bo ≤ g'.bo ∧ ∀ y, (sarR x.laz).count y ≤ (sarG goal).count y + fr g.re g'.re y

/-- **The local steps of the induction** (state-free counts; `RB` for the
steps whose product carries no tree). -/
structure KUSteps (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] : Prop where
  split : ∀ (nex : NextL S), KUC (Map := Map) (sarR nex.laz) (splitL nex) (fun x => sarR x.1 ++ sarR x.2.1)
  into : ∀ (nex : NextL S) (axe : Nat),
    KUC (Map := Map) (sarR nex.laz) (intoL nex axe) (fun x => sarR x.1 ++ sarR x.2.1)
  copy : ∀ (first : NextL S) (second : Lazy S), LabUniq first.laz → LabUniq second →
    KUC (Map := Map) (sarR first.laz ++ sarR second) (copyL first second) (fun x => sarR x.laz)
  past : ∀ (cod : Bell → Option Bool) (nex : NextL S) (nom : Nomm) (region : List Nat),
    KUC (Map := Map) (sarR nex.laz) (pastL cod nex nom region) (fun x => sarR x.laz)
  mede : ∀ (th : Jmp) (k : Noun) (laz : Lazy S), RB (Map := Map) (medeL th k laz)
  collapse : ∀ (nex : NextL S), RB (Map := Map) (collapseLazyAtomL nex)
  kerf : ∀ (nex : NextL S), RB (Map := Map) (kerf nex)
  forl : ∀ (r o : Nat), RB (Map := Map) (forl r o)
  doneBlocks : RB (Map := Map) (doneBlocks : CM Map (Nat × Nat))

end Raw
end SkaModel
end Formalization
