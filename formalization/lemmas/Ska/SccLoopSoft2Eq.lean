import lemmas.Ska.SccLoopSoft2

/-! # Where `runLCS2` is `runLCS` (README Gaps 21.20)

`runLCS2` differs from `runLCS` at four places only: `%1` on `%next` (`medeLS` for
`liftS (medeL ..)`) and the `+collapse-lazy-atom` of `%3`, `%4`, `%5` on `%next`
(`collapseLazyAtomLS` for `liftS (collapseLazyAtomL ..)`); everything else is the same text.
Both differ only through `crashNeedS`, which is `crashNeed` at a block that is not soft.
`LiftsAt sm m n`: on every state whose soft map is `sm`, `m` is `liftS n`.  Proved:
* `crashNeedS_lifts`: at a block not in `sm`;
* `medeLoopS_lifts`: at a block not in `sm`, or where the constant fits the need (`medeOk`:
  track K's `MedeFits`, no atom where a cell is needed);
* `medeLS_lifts`: when every node of the lazy need is such a block (`LazyAll`), the walk's
  needs being those `sureRequireLook` gives;
* `collapseLazyAtomLS_lifts`: when no bond or fork block of the lazy need is soft and asks a
  cell (`colOk`). -/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- **`m` is `liftS n` on the states with soft map `sm`.** -/
def LiftsAt {α : Type} (sm : Map SoftCall) (m : CMS Map α) (n : CM Map α) : Prop :=
  ∀ g, m ⟨g, sm⟩ = (n g).map fun p => (p.1, ⟨p.2, sm⟩)

theorem liftsAt_lift {α : Type} (sm : Map SoftCall) (n : CM Map α) : LiftsAt sm (liftS n) n :=
  fun _ => rfl

theorem liftsAt_pure {α : Type} (sm : Map SoftCall) (a : α) : LiftsAt sm (pure a : CMS Map α) (pure a) :=
  fun _ => rfl

theorem liftsAt_bind {α β : Type} {sm : Map SoftCall} {m : CMS Map α} {n : CM Map α}
    {k : α → CMS Map β} {k' : α → CM Map β} (h : LiftsAt sm m n) (hk : ∀ a, LiftsAt sm (k a) (k' a)) :
    LiftsAt sm (m >>= k) (n >>= k') := by
  intro g
  show (m ⟨g, sm⟩).bind (fun p => k p.1 p.2) = ((n g).bind fun p => k' p.1 p.2).map _
  rw [h g]
  cases n g with
  | none => rfl
  | some p => exact hk p.1 p.2

/-- `liftsAt_bind` where the rest may use what the first step returned. -/
theorem liftsAt_bind_dep {α β : Type} {sm : Map SoftCall} {m : CMS Map α} {n : CM Map α}
    {k : α → CMS Map β} {k' : α → CM Map β} (h : LiftsAt sm m n)
    (hk : ∀ g a g', n g = some (a, g') → k a ⟨g', sm⟩ = (k' a g').map fun p => (p.1, ⟨p.2, sm⟩)) :
    LiftsAt sm (m >>= k) (n >>= k') := by
  intro g
  show (m ⟨g, sm⟩).bind (fun p => k p.1 p.2) = ((n g).bind fun p => k' p.1 p.2).map _
  rw [h g]
  cases hn : n g with
  | none => rfl
  | some p => exact hk g p.1 p.2 hn

theorem liftsAt_get {α : Type} {sm : Map SoftCall} {k : GenSf Map → CMS Map α} {k' : Gen Map → CM Map α}
    (h : ∀ g, LiftsAt sm (k ⟨g, sm⟩) (k' g)) : LiftsAt sm (get >>= k) (get >>= k') :=
  fun g => h g g

theorem liftsAt_withSoft {α : Type} {sm : Map SoftCall} {k : (Nat → Bool) → CMS Map α} {n : CM Map α}
    (h : LiftsAt sm (k fun o => (HoonMap.get sm o).isSome) n) : LiftsAt sm (withSoft k) n :=
  fun g => h g

/-- **`crashNeedS` is `crashNeed` at a block that is not soft.** -/
theorem crashNeedS_lifts (sm : Map SoftCall) (o : Nat) (a : Sum Nat Nat) (ned : Need)
    (ho : HoonMap.get sm o = none) : LiftsAt sm (crashNeedS o a ned) (crashNeed o a ned) := by
  cases a with
  | inr p =>
    unfold crashNeedS
    exact liftsAt_withSoft (by simp only [ho, Option.isSome_none]; exact liftsAt_lift _ _)
  | inl n =>
    unfold crashNeedS crashNeed
    exact liftsAt_bind (liftsAt_lift _ _) fun r =>
      liftsAt_withSoft (by simp only [ho, Option.isSome_none]; exact liftsAt_lift _ _)

/-- No atom where the need is a cell: no `+crash-need` in `+mede` (track K's `MedeFits`). -/
def medeOk : Noun → Need → Bool
  | Noun.cell a b, Need.pair p q => medeOk a p && medeOk b q
  | Noun.cell a b, Need.both _ h t => medeOk a h && medeOk b t
  | Noun.atom _, Need.pair _ _ => false
  | Noun.atom _, Need.both _ _ _ => false
  | _, _ => true

/-- **The loop of `+mede` is a lift** at a block not soft, or where the constant fits. -/
theorem medeLoopS_lifts (sm : Map SoftCall) (o : Nat) :
    ∀ (som : Noun) (ned : Need), (HoonMap.get sm o = none ∨ medeOk som ned = true) →
      LiftsAt sm (medeLoopS o som ned) (medeLoop o som ned)
  | _, Need.none, _ => by unfold medeLoopS medeLoop; exact liftsAt_pure _ _
  | som, Need.this r, _ => by unfold medeLoopS medeLoop; exact liftsAt_lift _ _
  | Noun.atom n, Need.pair p q, h => by
    unfold medeLoopS medeLoop
    exact crashNeedS_lifts sm o _ _ (h.resolve_right (by simp [medeOk]))
  | Noun.cell a b, Need.pair p q, h => by
    unfold medeLoopS medeLoop
    have h' : medeOk (Noun.cell a b) (Need.pair p q) = true → medeOk a p = true ∧ medeOk b q = true :=
      fun hm => by simpa [medeOk] using hm
    exact liftsAt_bind (medeLoopS_lifts sm o a p (h.imp id fun hm => (h' hm).1)) fun _ =>
      medeLoopS_lifts sm o b q (h.imp id fun hm => (h' hm).2)
  | Noun.atom n, Need.both r h t, hh => by
    unfold medeLoopS medeLoop
    exact crashNeedS_lifts sm o _ _ (hh.resolve_right (by simp [medeOk]))
  | Noun.cell a b, Need.both r h t, hh => by
    unfold medeLoopS medeLoop
    have h' : medeOk (Noun.cell a b) (Need.both r h t) = true → medeOk a h = true ∧ medeOk b t = true :=
      fun hm => by simpa [medeOk] using hm
    exact liftsAt_bind (liftsAt_lift _ _) fun _ =>
      liftsAt_bind (medeLoopS_lifts sm o a h (hh.imp id fun hm => (h' hm).1)) fun _ =>
        medeLoopS_lifts sm o b t (hh.imp id fun hm => (h' hm).2)

mutual
/-- `P` at every node of a lazy need (the root at `o`, the forks and bonds at their blocks). -/
def LazyAll (P : Nat → Sure S → Prop) : Nat → Lazy S → Prop
  | o, mk s fk bd => P o s ∧ ForksAll P fk ∧ BondsAll P bd

def ForksAll (P : Nat → Sure S → Prop) : List ((Nat × Lazy S) × (Nat × Lazy S)) → Prop
  | [] => True
  | ((oy, y), (on, n)) :: rest => LazyAll P oy y ∧ LazyAll P on n ∧ ForksAll P rest

def BondsAll (P : Nat → Sure S → Prop) : List (Nat × Lazy S) → Prop
  | [] => True
  | (o, l) :: rest => LazyAll P o l ∧ BondsAll P rest
end

section walk
variable (sm : Map SoftCall) (f : Nat → Sure S → CMS Map Unit) (f' : Nat → Sure S → CM Map Unit)
  (P : Nat → Sure S → Prop)

mutual
/-- **`walkLazyS` is `walkLazy` lifted** when the gates are, at every node. -/
theorem walkLazyS_lifts (hf : ∀ o s, P o s → LiftsAt sm (f o s) (f' o s)) : ∀ (o : Nat) (l : Lazy S), LazyAll P o l →
    LiftsAt sm (walkLazyS f o l) (walkLazy f' o l)
  | o, mk s fk bd, h => by
    unfold walkLazyS walkLazy
    unfold LazyAll at h
    exact liftsAt_bind (hf o s h.1) fun _ => by
      by_cases hc : (fk.isEmpty && bd.isEmpty) = true
      · simp only [hc, if_true]; exact liftsAt_pure _ _
      · simp only [hc]
        exact liftsAt_bind (walkForksS_lifts hf fk h.2.1) fun _ => walkBondsS_lifts hf bd h.2.2

theorem walkForksS_lifts (hf : ∀ o s, P o s → LiftsAt sm (f o s) (f' o s)) : ∀ (l : List ((Nat × Lazy S) × (Nat × Lazy S))), ForksAll P l →
    LiftsAt sm (walkForksS f l) (walkForks f' l)
  | [], _ => by unfold walkForksS walkForks; exact liftsAt_pure _ _
  | ((oy, y), (on, n)) :: rest, h => by
    unfold walkForksS walkForks
    unfold ForksAll at h
    exact liftsAt_bind (walkLazyS_lifts hf oy y h.1) fun _ =>
      liftsAt_bind (walkLazyS_lifts hf on n h.2.1) fun _ => walkForksS_lifts hf rest h.2.2

theorem walkBondsS_lifts (hf : ∀ o s, P o s → LiftsAt sm (f o s) (f' o s)) : ∀ (l : List (Nat × Lazy S)), BondsAll P l →
    LiftsAt sm (walkBondsS f l) (walkBonds f' l)
  | [], _ => by unfold walkBondsS walkBonds; exact liftsAt_pure _ _
  | (o, l) :: rest, h => by
    unfold walkBondsS walkBonds
    unfold BondsAll at h
    exact liftsAt_bind (walkLazyS_lifts hf o l h.1) fun _ => walkBondsS_lifts hf rest h.2
end
end walk

/-- What `+mede` needs at a node: the block is not soft, or every need `sureRequireLook` gives
there fits the constant. -/
def medeAt (sm : Map SoftCall) (som : Noun) (o : Nat) (s : Sure S) : Prop :=
  HoonMap.get sm o = none ∨ ∀ (g : Gen Map) ned g', sureRequireLook s g = some (ned, g') → medeOk som ned = true

/-- **`medeLS` is `medeL` lifted** when every node of the lazy need is `medeAt` (at any root
block: the root is the block `+mede` emits). -/
theorem medeLS_lifts (sm : Map SoftCall) (th : Jmp) (som : Noun) (laz : Lazy S)
    (h : ∀ o, LazyAll (medeAt sm som) o laz) : LiftsAt sm (medeLS th som laz) (medeL th som laz) := by
  unfold medeLS medeL
  refine liftsAt_bind (liftsAt_lift _ _) fun o => liftsAt_get fun g => ?_
  by_cases hd : g.drop = true
  · simp only [hd, if_true]; exact liftsAt_pure _ _
  · simp only [hd, Bool.false_eq_true, if_false]
    refine liftsAt_bind (walkLazyS_lifts sm _ _ (medeAt sm som) ?_ o laz (h o)) (fun _ => liftsAt_pure _ _)
    intro o' s hP
    exact liftsAt_bind_dep (liftsAt_lift _ _) fun g a g' hs =>
      medeLoopS_lifts sm o' som a (hP.imp id fun hm => hm g a g' hs) g'

/-- What `+collapse-lazy-atom` needs at a node: the block is not soft, or the need there is
`%none` / `%this` (no `+crash-need`). -/
def colAt (sm : Map SoftCall) (o : Nat) (s : Sure S) : Prop :=
  HoonMap.get sm o = none ∨ ∀ (g : Gen Map) ned g', sureRequireLook s g = some (ned, g') →
    (ned = Need.none ∨ ∃ r, ned = Need.this r)

/-- **The gate of `+collapse-lazy-atom` is a lift** at a `colAt` node. -/
theorem collapseGateS_lifts (sm : Map SoftCall) (r o oLaz : Nat) (s : Sure S) (hP : colAt sm oLaz s) :
    LiftsAt sm (collapseGateS r o oLaz s) (collapseGate r o oLaz s) := by
  unfold collapseGateS collapseGate
  refine liftsAt_bind_dep (liftsAt_lift _ _) fun g a g' hs => ?_
  have hc : a = Need.none ∨ (∃ r, a = Need.this r) ∨ HoonMap.get sm oLaz = none := by
    rcases hP with h | h
    · exact Or.inr (Or.inr h)
    · rcases h g a g' hs with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  cases a with
  | none => rfl
  | this r' =>
    by_cases hr : r = r'
    · simp only [hr, if_true]; rfl
    · simp only [hr, if_false]; rfl
  | pair p q =>
    have ho : HoonMap.get sm oLaz = none := by
      rcases hc with h | ⟨_, h⟩ | h <;> first | exact h | cases h
    exact liftsAt_bind (liftsAt_lift _ _) (fun src => crashNeedS_lifts sm oLaz _ _ ho) g'
  | both x p q =>
    have ho : HoonMap.get sm oLaz = none := by
      rcases hc with h | ⟨_, h⟩ | h <;> first | exact h | cases h
    exact liftsAt_bind (liftsAt_lift _ _) (fun src => crashNeedS_lifts sm oLaz _ _ ho) g'

/-- **`collapseLazyAtomLS` is `collapseLazyAtomL` lifted** when every node of the walked need
(the sure part `%this r` at any root block, the forks and bonds of `nex.laz`) is `colAt`. -/
theorem collapseLazyAtomLS_lifts (sm : Map SoftCall) (nex : NextL S)
    (h : ∀ r o, LazyAll (colAt sm) o (mk ⟨Need.this r, nex.laz.sure.lok⟩ nex.laz.fork nex.laz.bond)) :
    LiftsAt sm (collapseLazyAtomLS nex) (collapseLazyAtomL nex) := by
  unfold collapseLazyAtomLS collapseLazyAtomL
  by_cases ha : nex.th.args ≠ []
  · rw [if_pos ha, if_pos ha]; intro g; rfl
  · rw [if_neg ha, if_neg ha]
    by_cases hn : noneEquivalentL nex.laz = true
    · rw [if_pos hn, if_pos hn]; exact liftsAt_pure _ _
    · rw [if_neg hn, if_neg hn]
      refine liftsAt_bind (liftsAt_lift _ _) fun nedSure => ?_
      refine liftsAt_bind (n := collapseHead nedSure nex.th.there) (liftsAt_lift _ _) fun ⟨r, there⟩ => ?_
      refine liftsAt_get fun g => ?_
      by_cases hd : g.drop = true
      · simp only [hd, if_true]; exact liftsAt_pure _ _
      · simp only [hd, Bool.false_eq_true, if_false]
        exact liftsAt_bind (walkLazyS_lifts sm _ _ (colAt sm)
          (fun o s hP => collapseGateS_lifts sm r there o s hP) there _ (h r there)) fun _ => liftsAt_pure _ _

end Comp
end SkaModel
end Formalization
