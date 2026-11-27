import lemmas.Compiler.CompSccLoopSoftMemDone

/-! # `hreq` of the soft `%done` step: the empty case and when `+soft-ask` makes a try (README Gaps 21.19)

`hreq` of `mem_done_stepS` / `MemDoneCallS` asks that after `+coerce-lazy` (`coerceLazyLS`) every
soft call of the soft map has requirements `%none` / `%this` (`ReqTN`).

* **The empty case**: `SE m`, a step of `CMS` that keeps a soft map without keys as it is.
  `withSoft` then reads `|` everywhere, and `softAsk` on a missing key either returns the state
  (`drop`) or fails.  `se_coerceLazyLS` (mutual with the bonds and the forks), and
  **`hreq_of_empty`**: from a soft map with no keys `hreq` holds (the 59 compiles of the corpus
  without a soft call, whose run ends with the empty map, `runLCS_sim`).
* **When a requirement is a try**: `+soft-ask` is called by `sureLoopS o ned tgt` at a soft
  block `o`, at each `%this r` of the final need `ned`, with the sub-need `tgt` of the target
  (`+sure-require-look` of the block's sure) at the same place; it records `(r, tgt)`.  So a
  requirement is not `%none` / `%this` exactly when the member's final need takes WHOLE (`%this`)
  a part of the subject that the soft call's target takes APART (a cell or `%both` there).
  `noTry ned tgt` is that test; **`sr_sureLoopS`**: under `noTry`, `sureLoopS` keeps `SoftReq`
  (every soft call's requirements `%none` / `%this`) and the keys. -/

namespace Formalization

namespace SkaModel
namespace Comp

open Nock Lazy

set_option linter.unusedSectionVars false

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- A soft map without keys. -/
def SoftEmpty (m : Map SoftCall) : Prop := ∀ o, HoonMap.get m o = Option.none

/-- A step of `CMS` that keeps a soft map without keys as it is. -/
structure SE {α : Type} (m : CMS Map α) : Prop where
  keep : ∀ s x s', SoftEmpty s.soft → m s = some (x, s') → s'.soft = s.soft

namespace SE

theorem pure' {α : Type} (a : α) : SE (pure a : CMS Map α) := by
  constructor; intro s x s' _ h; cases h; rfl

theorem bind' {α β : Type} {m : CMS Map α} {f : α → CMS Map β} (hm : SE m) (hf : ∀ a, SE (f a)) :
    SE (m >>= f) := by
  constructor
  intro s x s' he h
  simp only [bind, StateT.bind] at h
  obtain ⟨⟨a, s1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
  have e1 := hm.keep s a s1 he h1
  have he1 : SoftEmpty s1.soft := by rw [e1]; exact he
  exact ((hf a).keep s1 x s' he1 h2).trans e1

theorem liftS' {α : Type} (m : CM Map α) : SE (liftS m) := by
  constructor
  intro s x s' _ h
  unfold liftS at h
  obtain ⟨⟨a, g1⟩, -, e⟩ := Option.map_eq_some_iff.mp h
  cases e
  rfl

theorem ite' {α : Type} (c : Prop) [Decidable c] {a b : CMS Map α} (ha : SE a) (hb : SE b) :
    SE (if c then a else b) := by
  split
  · exact ha
  · exact hb

theorem withSoft' {α : Type} {k : (Nat → Bool) → CMS Map α} (hk : ∀ f, SE (k f)) : SE (withSoft k) := by
  constructor
  intro s x s' he h
  exact (hk s.isSoft).keep s x s' he h

theorem softAsk' (o src : Nat) (ned : Need) : SE (softAsk o src ned : CMS Map Unit) := by
  constructor
  intro s x s' he h
  unfold softAsk at h
  split at h
  · cases h; rfl
  · rw [he o] at h; cases h

end SE

theorem se_sureLoopS (o : Nat) : ∀ (ned tgt : Need), SE (sureLoopS o ned tgt : CMS Map Unit)
  | Need.none, _ => by
    unfold sureLoopS
    exact SE.ite' _ (SE.pure' _) (SE.liftS' _)
  | Need.this _, _ => by
    unfold sureLoopS
    exact SE.withSoft' fun _ => SE.ite' _ (SE.softAsk' _ _ _) (SE.liftS' _)
  | Need.pair p q, tgt => by
    unfold sureLoopS
    cases tgt
    · exact SE.bind' (se_sureLoopS o p _) fun _ => se_sureLoopS o q _
    · exact SE.liftS' _
    · exact SE.liftS' _
    · exact SE.pure' _
  | Need.both _ h t, tgt => by
    unfold sureLoopS
    cases tgt
    · exact SE.bind' (se_sureLoopS o h _) fun _ => se_sureLoopS o t _
    · exact SE.ite' _ (SE.liftS' _) (SE.bind' (SE.liftS' _) fun _ =>
        SE.bind' (se_sureLoopS o h _) fun _ => se_sureLoopS o t _)
    · exact SE.ite' _ (SE.liftS' _) (SE.liftS' _)
    · exact SE.pure' _

theorem se_coerceLazyS (ned : Need) (o : Nat) (laz : Sure S) (less : Cape) :
    SE (coerceLazyS ned o laz less : CMS Map Unit) := by
  unfold coerceLazyS
  exact SE.bind' (SE.liftS' _) fun _ => SE.bind' (SE.liftS' _) fun _ => se_sureLoopS _ _ _

mutual
theorem se_coerceLazyLS (ned : Need) (less : Cape) : ∀ (o : Nat) (l : Lazy S),
    SE (coerceLazyLS ned less o l : CMS Map Unit)
  | o, mk s f b => by
    unfold coerceLazyLS
    exact SE.bind' (se_coerceLazyS _ _ _ _) fun _ => SE.ite' _ (SE.pure' _)
      (SE.bind' (se_coerceBondsS ned less b) fun _ => se_coerceForksS ned less f)

theorem se_coerceBondsS (ned : Need) (less : Cape) : ∀ (l : List (Nat × Lazy S)),
    SE (coerceBondsS ned less l : CMS Map Unit)
  | [] => by unfold coerceBondsS; exact SE.pure' _
  | (o, l) :: rest => by
    unfold coerceBondsS
    exact SE.bind' (se_coerceLazyLS ned less o l) fun _ => se_coerceBondsS ned less rest

theorem se_coerceForksS (ned : Need) (less : Cape) : ∀ (l : List (ForkE S)),
    SE (coerceForksS ned less l : CMS Map Unit)
  | [] => by unfold coerceForksS; exact SE.pure' _
  | ((oy, y), (on, n)) :: rest => by
    unfold coerceForksS
    exact SE.bind' (se_coerceLazyLS ned less oy y) fun _ =>
      SE.bind' (se_coerceLazyLS ned less on n) fun _ => se_coerceForksS ned less rest
end

/-! ## When `+soft-ask` records a try -/

/-- **`sureLoopS o ned tgt` asks only `%none` / `%this`**: at each `%this` of `ned` the aligned
sub-need of `tgt` is `%none` or `%this` (the places where `sureLoopS` crashes or emits ops are
not constrained). -/
def noTry : Need → Need → Bool
  | Need.none, _ => true
  | Need.this _, Need.none => true
  | Need.this _, Need.this _ => true
  | Need.this _, _ => false
  | Need.pair p q, Need.pair tp tq => noTry p tp && noTry q tq
  | Need.pair _ _, _ => true
  | Need.both _ h t, Need.pair tp tq => noTry h tp && noTry t tq
  | Need.both _ h t, Need.both _ th tt => noTry h th && noTry t tt
  | Need.both _ _ _, _ => true

/-- Every soft call's requirements are `%none` / `%this`. -/
def SoftReq (m : Map SoftCall) : Prop := ∀ o c, HoonMap.get m o = some c → Compiler.ReqTN c.req

/-- A step that keeps `SoftReq` and the keys of the soft map. -/
structure SR {α : Type} (m : CMS Map α) : Prop where
  keep : ∀ s x s', SoftReq s.soft → m s = some (x, s') →
    SoftReq s'.soft ∧ ∀ o, (HoonMap.get s'.soft o).isSome = (HoonMap.get s.soft o).isSome

namespace SR

theorem pure' {α : Type} (a : α) : SR (pure a : CMS Map α) := by
  constructor; intro s x s' h e; cases e; exact ⟨h, fun _ => rfl⟩

theorem bind' {α β : Type} {m : CMS Map α} {f : α → CMS Map β} (hm : SR m) (hf : ∀ a, SR (f a)) :
    SR (m >>= f) := by
  constructor
  intro s x s' hr h
  simp only [bind, StateT.bind] at h
  obtain ⟨⟨a, s1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hr1, hk1⟩ := hm.keep s a s1 hr h1
  obtain ⟨hr2, hk2⟩ := (hf a).keep s1 x s' hr1 h2
  exact ⟨hr2, fun o => (hk2 o).trans (hk1 o)⟩

theorem liftS' {α : Type} (m : CM Map α) : SR (liftS m) := by
  constructor
  intro s x s' hr h
  unfold liftS at h
  obtain ⟨⟨a, g1⟩, -, e⟩ := Option.map_eq_some_iff.mp h
  cases e
  exact ⟨hr, fun _ => rfl⟩

theorem ite' {α : Type} (c : Prop) [Decidable c] {a b : CMS Map α} (ha : SR a) (hb : SR b) :
    SR (if c then a else b) := by
  split
  · exact ha
  · exact hb

theorem withSoft' {α : Type} {k : (Nat → Bool) → CMS Map α} (hk : ∀ f, SR (k f)) : SR (withSoft k) := by
  constructor
  intro s x s' hr h
  exact (hk s.isSoft).keep s x s' hr h

/-- `+soft-ask` of a `%none` / `%this` keeps `SoftReq` and the keys. -/
theorem softAsk' (o src : Nat) (ned : Need) (hn : ned = Need.none ∨ ∃ d, ned = Need.this d) :
    SR (softAsk o src ned : CMS Map Unit) := by
  constructor
  intro s x s' hr h
  unfold softAsk at h
  split at h
  · cases h; exact ⟨hr, fun _ => rfl⟩
  · obtain ⟨c, hc, e⟩ := Option.map_eq_some_iff.mp h
    cases e
    refine ⟨fun k c' hk => ?_, fun k => ?_⟩
    · rw [HoonMap.get_put] at hk
      by_cases hko : k = o
      · rw [if_pos hko] at hk
        cases hk
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hn
        · exact hr o c hc p hp
      · rw [if_neg hko] at hk
        exact hr k c' hk
    · show (HoonMap.get (HoonMap.put s.soft o _) k).isSome = _
      rw [HoonMap.get_put]
      by_cases hko : k = o
      · rw [if_pos hko, hko, hc]; rfl
      · rw [if_neg hko]

end SR

/-- **Under `noTry`, `sureLoopS` keeps `SoftReq` and the keys.** -/
theorem sr_sureLoopS (o : Nat) : ∀ (ned tgt : Need), noTry ned tgt = true → SR (sureLoopS o ned tgt : CMS Map Unit)
  | Need.none, _, _ => by
    unfold sureLoopS
    exact SR.ite' _ (SR.pure' _) (SR.liftS' _)
  | Need.this _, tgt, h => by
    unfold sureLoopS
    have hn : tgt = Need.none ∨ ∃ d, tgt = Need.this d := by
      cases tgt with
      | none => exact Or.inl rfl
      | this d => exact Or.inr ⟨d, rfl⟩
      | pair _ _ => simp [noTry] at h
      | both _ _ _ => simp [noTry] at h
    exact SR.withSoft' fun _ => SR.ite' _ (SR.softAsk' _ _ _ hn) (SR.liftS' _)
  | Need.pair p q, tgt, h => by
    unfold sureLoopS
    cases tgt with
    | pair tp tq =>
      simp only [noTry, Bool.and_eq_true] at h
      exact SR.bind' (sr_sureLoopS o p _ h.1) fun _ => sr_sureLoopS o q _ h.2
    | this _ => exact SR.liftS' _
    | both _ _ _ => exact SR.liftS' _
    | none => exact SR.pure' _
  | Need.both _ hh t, tgt, h => by
    unfold sureLoopS
    cases tgt with
    | pair tp tq =>
      simp only [noTry, Bool.and_eq_true] at h
      exact SR.bind' (sr_sureLoopS o hh _ h.1) fun _ => sr_sureLoopS o t _ h.2
    | both _ th tt =>
      simp only [noTry, Bool.and_eq_true] at h
      exact SR.ite' _ (SR.liftS' _) (SR.bind' (SR.liftS' _) fun _ =>
        SR.bind' (sr_sureLoopS o hh _ h.1) fun _ => sr_sureLoopS o t _ h.2)
    | this _ => exact SR.ite' _ (SR.liftS' _) (SR.liftS' _)
    | none => exact SR.pure' _

end Comp
end SkaModel

namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

/-- **`hreq` from a soft map without keys**: `coerceLazyLS` keeps it, so the `+tap:by` after it
is empty. -/
theorem hreq_of_empty (nedF : Need) (cape : Cape) (o : Nat) (laz : Lazy CSet) (g2 : Gen (TreapMap mugF))
    (sf : TreapMap mugF SoftCall) (he : SoftEmpty sf) :
    ∀ u sf3, coerceLazyLS nedF cape o laz ⟨g2, sf⟩ = some (u, sf3) →
      ∀ p ∈ TreapMap.tap sf3.soft, ReqTN p.2.req := by
  intro u sf3 h p hp
  have e := (se_coerceLazyLS nedF cape o laz).keep ⟨g2, sf⟩ u sf3 he h
  rw [e] at hp
  have hg := (TreapMap.mem_tap sf p.1 p.2).mp hp
  have h0 : TreapMap.get sf p.1 = Option.none := he p.1
  rw [h0] at hg
  cases hg

/-- `hreq` at the start of `MemDoneCallS`: the run's soft map is the bunt. -/
theorem hreq_of_bunt (nedF : Need) (cape : Cape) (o : Nat) (laz : Lazy CSet) (g2 : Gen (TreapMap mugF))
    (sf : TreapMap mugF SoftCall) (he : sf = HoonMap.empty) :
    ∀ u sf3, coerceLazyLS nedF cape o laz ⟨g2, sf⟩ = some (u, sf3) →
      ∀ p ∈ TreapMap.tap sf3.soft, ReqTN p.2.req :=
  hreq_of_empty nedF cape o laz g2 sf (fun k => by rw [he]; exact HoonMap.get_empty k)

/-- **`hreq` from `SoftReq`**: when the run's soft calls have requirements `%none` / `%this` and
`+coerce-lazy` keeps that (`SR`, e.g. through `sr_sureLoopS` at its soft blocks), `hreq` holds. -/
theorem hreq_of_SR (nedF : Need) (cape : Cape) (o : Nat) (laz : Lazy CSet) (g2 : Gen (TreapMap mugF))
    (sf : TreapMap mugF SoftCall) (hr : SoftReq sf)
    (hsr : ∀ s x s', s.soft = sf → coerceLazyLS nedF cape o laz s = some (x, s') → SoftReq s'.soft) :
    ∀ u sf3, coerceLazyLS nedF cape o laz ⟨g2, sf⟩ = some (u, sf3) →
      ∀ p ∈ TreapMap.tap sf3.soft, ReqTN p.2.req := by
  intro u sf3 h p hp
  exact hsr _ u sf3 rfl h p.1 p.2 ((TreapMap.mem_tap _ p.1 p.2).mp hp)

end Compiler
end Formalization
