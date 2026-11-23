import Lean
import lemmas.Run
import lemmas.Attr

/-!
Symbolic execution of Nock with `simp`.

`simp only [nock_exec]` rewrites `nock subject formula` by the opcode rules of
`Run.lean`.  The subject may contain variables.  Two simprocs do the tree
addressing: `slot? axis subject` and `edit? axis replacement subject` with a
literal axis are computed along the cells of `subject`, with a proof built from
the spec's own recursion (`slot?_left` and friends), so definitions such as a
core from the pill are opened only along the path that the axis names.

Formulas that are constants stay closed: `nock subject dec.loop` is not
rewritten until a proof opens `dec.loop` or supplies a lemma about it.  That
keeps recursion from unfolding forever.
-/

namespace Formalization
namespace Nock

/-! ## The spec's recursion, as rules for one step down -/

theorem slot?_left {k : Nat} {s x y : Noun} (h : slot? k s = some (C x y)) :
    slot? (2 * k) s = some x :=
  slot?_complete (Slot.left (slot?_sound _ h))

theorem slot?_right {k : Nat} {s x y : Noun} (h : slot? k s = some (C x y)) :
    slot? (2 * k + 1) s = some y :=
  slot?_complete (Slot.right (slot?_sound _ h))

theorem slot?_pos {k : Nat} {s out : Noun} (h : slot? k s = some out) : 0 < k :=
  (slot?_sound _ h).pos

theorem slot?_left_atom {k : Nat} {s : Noun} {a : Nat} (h : slot? k s = some (A a)) :
    slot? (2 * k) s = none := by
  have := slot?_pos h
  rw [slot?_step _ (by omega)]
  have h2 : 2 * k / 2 = k := by omega
  simp [h2, h, child]

theorem slot?_right_atom {k : Nat} {s : Noun} {a : Nat} (h : slot? k s = some (A a)) :
    slot? (2 * k + 1) s = none := by
  have := slot?_pos h
  rw [slot?_step _ (by omega)]
  have h2 : (2 * k + 1) / 2 = k := by omega
  simp [h2, h, child]

theorem slot?_left_none {k : Nat} {s : Noun} (hk : 0 < k) (h : slot? k s = none) :
    slot? (2 * k) s = none := by
  rw [slot?_step _ (by omega)]
  have h2 : 2 * k / 2 = k := by omega
  simp [h2, h]

theorem slot?_right_none {k : Nat} {s : Noun} (hk : 0 < k) (h : slot? k s = none) :
    slot? (2 * k + 1) s = none := by
  rw [slot?_step _ (by omega)]
  have h2 : (2 * k + 1) / 2 = k := by omega
  simp [h2, h]

theorem edit?_left {k : Nat} {r s x y : Noun} (h : slot? k s = some (C x y)) :
    edit? (2 * k) r s = edit? k (C r y) s := by
  have := slot?_pos h
  rw [edit?_step _ (by omega)]
  have h2 : 2 * k / 2 = k := by omega
  have h3 : ¬ (2 * k % 2 = 1) := by omega
  simp [h2, h, graft]

theorem edit?_right {k : Nat} {r s x y : Noun} (h : slot? k s = some (C x y)) :
    edit? (2 * k + 1) r s = edit? k (C x r) s := by
  have := slot?_pos h
  rw [edit?_step _ (by omega)]
  have h2 : (2 * k + 1) / 2 = k := by omega
  have h3 : (2 * k + 1) % 2 = 1 := by omega
  simp [h2, h, graft]

/-! ## Simprocs -/

open Lean Meta

/-- What sits at an axis of a subject expression. -/
inductive Found where
  /-- `noun` with a proof of `slot? axis subject = some noun` -/
  | noun (noun proof : Expr)
  /-- the path runs into an atom; a proof of `slot? axis subject = some (A a)` one level up
  gives the caller `none` -/
  | atom (proof : Expr)
  /-- the path runs into a term that is neither a cell nor an atom -/
  | stuck

/-- Walk `subject` to `axis` (which is at least 1). -/
partial def findSlot (subject : Expr) (axis : Nat) : MetaM Found := do
  if axis == 1 then
    return .noun subject (mkApp (mkConst ``slot?_one) subject)
  let k := axis / 2
  match ← findSlot subject k with
  | .stuck => return .stuck
  | .atom _ => return .stuck
  | .noun parent proof =>
    let parent ← whnfD parent
    if parent.isAppOfArity ``Noun.cell 2 then
      let x := parent.getArg! 0
      let y := parent.getArg! 1
      if axis % 2 == 0 then
        return .noun x (mkApp5 (mkConst ``slot?_left) (mkNatLit k) subject x y proof)
      else
        return .noun y (mkApp5 (mkConst ``slot?_right) (mkNatLit k) subject x y proof)
    else if parent.isAppOfArity ``Noun.atom 1 then
      let a := parent.getArg! 0
      if axis % 2 == 0 then
        return .atom (mkApp4 (mkConst ``slot?_left_atom) (mkNatLit k) subject a proof)
      else
        return .atom (mkApp4 (mkConst ``slot?_right_atom) (mkNatLit k) subject a proof)
    else
      return .stuck

def optionNoun : Expr := mkApp (mkConst ``Option [Level.zero]) (mkConst ``Noun)

def someNoun (noun : Expr) : Expr :=
  mkApp2 (mkConst ``Option.some [Level.zero]) (mkConst ``Noun) noun

def noneNoun : Expr := mkApp (mkConst ``Option.none [Level.zero]) (mkConst ``Noun)

/-- `slot? axis subject` for a literal axis of at least 2. -/
simproc [nock_exec] slotLit (slot? _ _) := fun e => do
  unless e.isAppOfArity ``slot? 2 do return .continue
  let some axis := (e.getArg! 0).nat? | return .continue
  unless axis ≥ 2 do return .continue
  let subject := e.getArg! 1
  match ← findSlot subject axis with
  | .stuck => return .continue
  | .noun noun proof =>
    let rhs := someNoun noun
    let proof ← mkExpectedTypeHint proof (← mkEq e rhs)
    return .done { expr := rhs, proof? := some proof }
  | .atom proof =>
    let proof ← mkExpectedTypeHint proof (← mkEq e noneNoun)
    return .done { expr := noneNoun, proof? := some proof }

/-- `edit? axis replacement subject = some out`, with the proof. -/
partial def findEdit (replacement subject : Expr) (axis : Nat) :
    MetaM (Option (Expr × Expr)) := do
  if axis == 1 then
    return some (replacement, mkApp2 (mkConst ``edit?_one) replacement subject)
  let k := axis / 2
  match ← findSlot subject k with
  | .noun parent proof =>
    let parent ← whnfD parent
    unless parent.isAppOfArity ``Noun.cell 2 do return none
    let x := parent.getArg! 0
    let y := parent.getArg! 1
    let cell := mkConst ``Noun.cell
    if axis % 2 == 0 then
      let replacement' := mkApp2 cell replacement y
      let some (out, rest) ← findEdit replacement' subject k | return none
      let step := mkApp6 (mkConst ``edit?_left) (mkNatLit k) replacement subject x y proof
      return some (out, ← mkEqTrans step rest)
    else
      let replacement' := mkApp2 cell x replacement
      let some (out, rest) ← findEdit replacement' subject k | return none
      let step := mkApp6 (mkConst ``edit?_right) (mkNatLit k) replacement subject x y proof
      return some (out, ← mkEqTrans step rest)
  | _ => return none

/-- `edit? axis replacement subject` for a literal axis of at least 2. -/
simproc [nock_exec] editLit (edit? _ _ _) := fun e => do
  unless e.isAppOfArity ``edit? 3 do return .continue
  let some axis := (e.getArg! 0).nat? | return .continue
  unless axis ≥ 2 do return .continue
  let some (out, proof) ← findEdit (e.getArg! 1) (e.getArg! 2) axis | return .continue
  let rhs := someNoun out
  let proof ← mkExpectedTypeHint proof (← mkEq e rhs)
  return .done { expr := rhs, proof? := some proof }

/-! ## The rule set -/

@[nock_exec] theorem wut_atom (a : Nat) : wut (A a) = A 1 := rfl

@[nock_exec] theorem wut_cell (x y : Noun) : wut (C x y) = A 0 := rfl

theorem eqCode_self (x : Noun) : eqCode x x = A 0 := by simp [eqCode]

theorem eqCode_atom (a b : Nat) : eqCode (A a) (A b) = if a = b then A 0 else A 1 := by
  simp [eqCode]

theorem nock_ite (c : Prop) [Decidable c] (s f g : Noun) :
    nock s (if c then f else g) = if c then nock s f else nock s g := by
  split <;> rfl

attribute [nock_exec] nock_cell nock_op0 nock_op1 nock_op2 nock_op3 nock_op4 nock_op5 nock_op6
  nock_op7 nock_op8 nock_op9 nock_op10 nock_op11_cell nock_op11_atom
  pick_zero pick_one pick_eqCode lus_atom lus_cell slot?_one slot?_zero edit?_one edit?_zero
  Option.bind_some Option.bind_none

/-- Open the formula of a goal `nock subject formula = _`. -/
syntax "nock_open " ident : tactic

macro_rules
  | `(tactic| nock_open $name:ident) =>
    `(tactic| conv => { lhs; arg 2; unfold $name:ident })

end Nock
end Formalization
