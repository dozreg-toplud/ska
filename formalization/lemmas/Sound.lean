import lemmas.Fuel

/-!
The executable helpers of `Nock.lean` (`slot?`, `edit?`, `evalFuel`) agree
with the relations that state the specification (`Slot`, `Edit`, `Eval`).

* `slot?_iff` and `edit?_iff` are exact characterizations.
* `evalFuel_sound` says that a successful fuelled run is a derivation of
  `Eval`.  It is what lets the kernel compute a concrete evaluation and hand
  back a fact about the relational semantics.
-/

namespace Formalization
namespace Nock

/-! ## Axis paths -/

theorem axisPathFuel_succ (fuel axis : Nat) (h : 2 ≤ axis) :
    axisPathFuel (fuel + 1) axis =
      (axisPathFuel fuel (axis / 2)).map (· ++ [decide (axis % 2 = 1)]) := by
  match axis, h with
  | axis + 2, _ =>
    simp only [axisPathFuel]
    cases axisPathFuel fuel ((axis + 2) / 2) <;> rfl

theorem axisPathFuel_one (fuel : Nat) : axisPathFuel (fuel + 1) 1 = some [] := rfl

theorem axisPathFuel_zero (fuel : Nat) : axisPathFuel fuel 0 = none := by
  cases fuel <;> rfl

/-- With enough fuel the path does not depend on the fuel. -/
theorem axisPathFuel_enough :
    ∀ (fuel fuel' axis : Nat), axis ≤ fuel → axis ≤ fuel' →
      axisPathFuel fuel axis = axisPathFuel fuel' axis := by
  intro fuel
  induction fuel with
  | zero =>
    intro fuel' axis h _
    obtain rfl : axis = 0 := by omega
    rw [axisPathFuel_zero, axisPathFuel_zero]
  | succ fuel ih =>
    intro fuel' axis h h'
    match axis, h, h' with
    | 0, _, _ => rw [axisPathFuel_zero, axisPathFuel_zero]
    | 1, _, h' =>
      obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
      rfl
    | axis + 2, h, h' =>
      obtain ⟨k, rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
      rw [axisPathFuel_succ _ _ (by omega), axisPathFuel_succ _ _ (by omega),
        ih k ((axis + 2) / 2) (by omega) (by omega)]

theorem axisPath_zero : axisPath 0 = none := rfl

theorem axisPath_one : axisPath 1 = some [] := rfl

theorem axisPath_step (axis : Nat) (h : 2 ≤ axis) :
    axisPath axis = (axisPath (axis / 2)).map (· ++ [decide (axis % 2 = 1)]) := by
  unfold axisPath
  obtain ⟨k, rfl⟩ : ∃ k, axis = k + 1 := ⟨axis - 1, by omega⟩
  rw [axisPathFuel_succ _ _ h,
    axisPathFuel_enough k ((k + 1) / 2) ((k + 1) / 2) (by omega) (Nat.le_refl _)]

/-! ## Slot -/

/-- One step down from a noun: the head or the tail of a cell. -/
def child (right : Bool) : Noun → Option Noun
  | Noun.atom _ => none
  | Noun.cell head tail => some (if right then tail else head)

theorem slotAtPath_append (subject : Noun) (path : List Bool) (right : Bool) :
    slotAtPath subject (path ++ [right]) = (slotAtPath subject path).bind (child right) := by
  induction path generalizing subject with
  | nil => cases subject <;> cases right <;> simp [slotAtPath, child]
  | cons step rest ih =>
    cases subject with
    | atom _ => simp [slotAtPath]
    | cell head tail => cases step <;> simp [slotAtPath, ih]

theorem slot?_zero (subject : Noun) : slot? 0 subject = none := rfl

@[simp] theorem slot?_one (subject : Noun) : slot? 1 subject = some subject := by
  cases subject <;> rfl

/-- The spec's recursion for `/`: the low bit of the axis is the last step. -/
theorem slot?_step (axis : Nat) (h : 2 ≤ axis) (subject : Noun) :
    slot? axis subject =
      (slot? (axis / 2) subject).bind (child (decide (axis % 2 = 1))) := by
  unfold slot?
  rw [axisPath_step axis h]
  cases axisPath (axis / 2) with
  | none => rfl
  | some path => simp [slotAtPath_append]

theorem Slot.pos {axis subject out} (h : Slot axis subject out) : 0 < axis := by
  induction h <;> omega

theorem slot?_sound : ∀ (axis : Nat) {subject out : Noun},
    slot? axis subject = some out → Slot axis subject out := by
  intro axis
  induction axis using Nat.strongRecOn with
  | _ axis ih =>
    intro subject out h
    by_cases h0 : axis = 0
    · subst h0; simp [slot?_zero] at h
    by_cases h1 : axis = 1
    · subst h1
      simp only [slot?_one, Option.some.injEq] at h
      subst h
      exact Slot.one
    have h2 : 2 ≤ axis := by omega
    rw [slot?_step _ h2] at h
    cases hq : slot? (axis / 2) subject with
    | none => simp [hq] at h
    | some q =>
      have hslot := ih (axis / 2) (by omega) hq
      rw [hq] at h
      cases q with
      | atom _ => simp [child] at h
      | cell head tail =>
        simp only [Option.bind_some, child, Option.some.injEq] at h
        by_cases hodd : axis % 2 = 1
        · simp only [hodd, decide_true, if_true] at h
          subst h
          have : axis = 2 * (axis / 2) + 1 := by omega
          rw [this]
          exact Slot.right hslot
        · simp only [hodd, decide_false] at h
          subst h
          have : axis = 2 * (axis / 2) := by omega
          rw [this]
          exact Slot.left hslot

theorem slot?_complete {axis subject out} (h : Slot axis subject out) :
    slot? axis subject = some out := by
  induction h with
  | one => exact slot?_one _
  | @left axis subject head tail h ih =>
    have := h.pos
    rw [slot?_step _ (by omega)]
    have h2 : 2 * axis / 2 = axis := by omega
    have h3 : ¬ (2 * axis % 2 = 1) := by omega
    simp [h2, ih, child]
  | @right axis subject head tail h ih =>
    have := h.pos
    rw [slot?_step _ (by omega)]
    have h2 : (2 * axis + 1) / 2 = axis := by omega
    have h3 : (2 * axis + 1) % 2 = 1 := by omega
    simp [h2, h3, ih, child]

theorem slot?_iff {axis subject out} :
    slot? axis subject = some out ↔ Slot axis subject out :=
  ⟨slot?_sound axis, slot?_complete⟩

theorem Slot.deterministic {axis subject out out'}
    (h : Slot axis subject out) (h' : Slot axis subject out') : out = out' := by
  have := slot?_complete h
  rw [slot?_complete h'] at this
  exact (Option.some.inj this).symm

/-! ## Edit -/

/-- The replacement that the spec's recursion for `#` builds one level up. -/
def graft (right : Bool) (replacement : Noun) : Noun → Option Noun
  | Noun.atom _ => none
  | Noun.cell head tail => some (if right then C head replacement else C replacement tail)

theorem editAtPath_append (path : List Bool) (right : Bool) (replacement subject : Noun) :
    editAtPath (path ++ [right]) replacement subject =
      (slotAtPath subject path).bind fun old =>
        (graft right replacement old).bind fun replacement' =>
          editAtPath path replacement' subject := by
  induction path generalizing subject with
  | nil => cases subject <;> cases right <;> simp [editAtPath, slotAtPath, graft]
  | cons step rest ih =>
    cases subject with
    | atom _ => cases step <;> simp [editAtPath, slotAtPath]
    | cell head tail =>
      cases step
      · simp only [List.cons_append, editAtPath, slotAtPath, ih]
        cases slotAtPath head rest with
        | none => rfl
        | some old =>
          simp only [Option.bind_some]
          cases graft right replacement old with
          | none => rfl
          | some replacement' => rfl
      · simp only [List.cons_append, editAtPath, slotAtPath, ih]
        cases slotAtPath tail rest with
        | none => rfl
        | some old =>
          simp only [Option.bind_some]
          cases graft right replacement old with
          | none => rfl
          | some replacement' => rfl

theorem edit?_zero (replacement subject : Noun) : edit? 0 replacement subject = none := rfl

@[simp] theorem edit?_one (replacement subject : Noun) :
    edit? 1 replacement subject = some replacement := by
  cases subject <;> rfl

/-- The spec's recursion for `#`. -/
theorem edit?_step (axis : Nat) (h : 2 ≤ axis) (replacement subject : Noun) :
    edit? axis replacement subject =
      (slot? (axis / 2) subject).bind fun old =>
        (graft (decide (axis % 2 = 1)) replacement old).bind fun replacement' =>
          edit? (axis / 2) replacement' subject := by
  unfold edit? slot?
  rw [axisPath_step axis h]
  cases axisPath (axis / 2) with
  | none => rfl
  | some path => simp [editAtPath_append]

theorem edit?_sound : ∀ (axis : Nat) {replacement subject out : Noun},
    edit? axis replacement subject = some out → Edit axis replacement subject out := by
  intro axis
  induction axis using Nat.strongRecOn with
  | _ axis ih =>
    intro replacement subject out h
    by_cases h0 : axis = 0
    · subst h0; simp [edit?_zero] at h
    by_cases h1 : axis = 1
    · subst h1
      simp only [edit?_one, Option.some.injEq] at h
      subst h
      exact Edit.one
    have h2 : 2 ≤ axis := by omega
    rw [edit?_step _ h2] at h
    cases hq : slot? (axis / 2) subject with
    | none => simp [hq] at h
    | some q =>
      have hslot := slot?_sound _ hq
      rw [hq] at h
      cases q with
      | atom _ => simp [graft] at h
      | cell head tail =>
        simp only [Option.bind_some, graft] at h
        have hrec := ih (axis / 2) (by omega) h
        by_cases hodd : axis % 2 = 1
        · simp only [hodd, decide_true, if_true] at hrec
          have : axis = 2 * (axis / 2) + 1 := by omega
          rw [this]
          exact Edit.right (Slot.left hslot) hrec
        · simp only [hodd, decide_false] at hrec
          have : axis = 2 * (axis / 2) := by omega
          rw [this]
          exact Edit.left (Slot.right hslot) hrec

theorem Edit.pos {axis replacement subject out} (h : Edit axis replacement subject out) :
    0 < axis := by
  induction h <;> omega

theorem edit?_complete {axis replacement subject out}
    (h : Edit axis replacement subject out) : edit? axis replacement subject = some out := by
  induction h with
  | one => exact edit?_one _ _
  | @left axis replacement subject tail out hslot h ih =>
    have := h.pos
    rw [edit?_step _ (by omega)]
    have h2 : 2 * axis / 2 = axis := by omega
    have h3 : ¬ (2 * axis % 2 = 1) := by omega
    have hs := slot?_complete hslot
    rw [slot?_step _ (by omega)] at hs
    have h4 : (2 * axis + 1) / 2 = axis := by omega
    have h5 : (2 * axis + 1) % 2 = 1 := by omega
    rw [h4] at hs
    cases hq : slot? axis subject with
    | none => simp [hq] at hs
    | some q =>
      cases q with
      | atom _ => simp [hq, child] at hs
      | cell head tail' =>
        simp only [hq, h5, child, Option.bind_some, decide_true, if_true,
          Option.some.injEq] at hs
        subst hs
        simp [h2, hq, graft, ih]
  | @right axis replacement subject head out hslot h ih =>
    have := h.pos
    rw [edit?_step _ (by omega)]
    have h2 : (2 * axis + 1) / 2 = axis := by omega
    have h3 : (2 * axis + 1) % 2 = 1 := by omega
    have hs := slot?_complete hslot
    rw [slot?_step _ (by omega)] at hs
    have h4 : 2 * axis / 2 = axis := by omega
    have h5 : ¬ (2 * axis % 2 = 1) := by omega
    rw [h4] at hs
    cases hq : slot? axis subject with
    | none => simp [hq] at hs
    | some q =>
      cases q with
      | atom _ => simp [hq, child] at hs
      | cell head' tail =>
        simp only [hq, h5, child, Option.bind_some, decide_false, Bool.false_eq_true,
          if_false, Option.some.injEq] at hs
        subst hs
        simp [h2, h3, hq, graft, ih]

theorem edit?_iff {axis replacement subject out} :
    edit? axis replacement subject = some out ↔ Edit axis replacement subject out :=
  ⟨edit?_sound axis, edit?_complete⟩

theorem Edit.deterministic {axis replacement subject out out'}
    (h : Edit axis replacement subject out) (h' : Edit axis replacement subject out') :
    out = out' := by
  have := edit?_complete h
  rw [edit?_complete h'] at this
  exact (Option.some.inj this).symm

/-! ## The fuelled evaluator -/

/-- A successful fuelled run is a derivation of the big-step relation. -/
theorem evalFuel_sound : ∀ (fuel : Nat) {subject formula out : Noun},
    evalFuel fuel subject formula = some out → Eval subject formula out := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ h; simp [evalFuel] at h
  | succ fuel ih =>
    intro subject formula out h
    unfold evalFuel at h
    split at h
    · simp at h
    · -- cell
      split at h
      · rename_i left right hl hr
        simp only [Option.some.injEq] at h
        subst h
        exact Eval.cell (ih hl) (ih hr)
      · simp at h
    · exact Eval.op0 (slot?_sound _ h)
    · simp only [Option.some.injEq] at h
      subst h
      exact Eval.op1
    · split at h
      · rename_i subject' formula' hb hc
        exact Eval.op2 (ih hb) (ih hc) (ih h)
      · simp at h
    · split at h
      · rename_i noun hb
        simp only [Option.some.injEq] at h
        subst h
        exact Eval.op3 (ih hb)
      · simp at h
    · split at h
      · rename_i atom hb
        simp only [Option.some.injEq] at h
        subst h
        exact Eval.op4 (ih hb)
      · simp at h
    · split at h
      · rename_i left right hb hc
        simp only [Option.some.injEq] at h
        subst h
        exact Eval.op5 (ih hb) (ih hc)
      · simp at h
    · split at h
      · rename_i hb
        exact Eval.op6_zero (ih hb) (ih h)
      · rename_i hb
        exact Eval.op6_one (ih hb) (ih h)
      · simp at h
    · split at h
      · rename_i subject' hb
        exact Eval.op7 (ih hb) (ih h)
      · simp at h
    · split at h
      · rename_i produced hb
        exact Eval.op8 (ih hb) (ih h)
      · simp at h
    · split at h
      · rename_i core hc
        exact Eval.op9 (ih hc) (ih h)
      · simp at h
    · split at h
      · rename_i replacement editedBase hc hd
        exact Eval.op10 (ih hc) (ih hd) (edit?_sound _ h)
      · simp at h
    · split at h
      · rename_i hint product hc hd
        exact Eval.op11_cell (ih hc) (ih hd) (ih h)
      · simp at h
    · exact Eval.op11_atom (ih h)
    · simp at h

end Nock
end Formalization
