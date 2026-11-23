import core.Nock

/-!
Executable counterparts of the specification in `core/Nock.lean`: `slot?`,
`edit?` and the fuelled `evalFuel`.  Nothing here is trusted; `Sound.lean`
proves them against `Slot`, `Edit` and `Eval`.
-/

namespace Formalization
namespace Nock

-- Slot axes for /:
-- /[1 a]           = a
-- /[2 a b]         = a
-- /[3 a b]         = b
-- /[(a + a) b]     = /[2 /[a b]]
-- /[(a + a + 1) b] = /[3 /[a b]]
--
-- This executable helper decodes an axis as its binary path with the leading 1
-- dropped: false=head and true=tail.
def axisPathFuel : Nat -> Nat -> Option (List Bool)
  | 0, _ => none
  | Nat.succ fuel, axis =>
      match axis with
      | 0 => none
      | 1 => some []
      | _ =>
          match axisPathFuel fuel (axis / 2) with
          | none => none
          | some path => some (path ++ [decide (axis % 2 = 1)])

def axisPath (axis : Nat) : Option (List Bool) :=
  axisPathFuel axis axis

def slotAtPath : Noun -> List Bool -> Option Noun
  | subject, [] => some subject
  | Noun.atom _, _ :: _ => none
  | Noun.cell head _, false :: rest => slotAtPath head rest
  | Noun.cell _ tail, true :: rest => slotAtPath tail rest

def slot? (axis : Nat) (subject : Noun) : Option Noun :=
  match axisPath axis with
  | none => none
  | some path => slotAtPath subject path

def editAtPath : List Bool -> Noun -> Noun -> Option Noun
  | [], replacement, _ => some replacement
  | _ :: _, _, Noun.atom _ => none
  | false :: rest, replacement, Noun.cell head tail =>
      match editAtPath rest replacement head with
      | none => none
      | some head' => some (C head' tail)
  | true :: rest, replacement, Noun.cell head tail =>
      match editAtPath rest replacement tail with
      | none => none
      | some tail' => some (C head tail')

def edit? (axis : Nat) (replacement subject : Noun) : Option Noun :=
  match axisPath axis with
  | none => none
  | some path => editAtPath path replacement subject

-- Executable counterpart to Eval. It follows the same successful cases, bounded
-- by fuel so Lean accepts it as structurally recursive. `none` represents an
-- invalid, crashing, non-terminating, or out-of-fuel evaluation.
def evalFuel (fuel : Nat) (subject formula : Noun) : Option Noun :=
  match fuel with
  | 0 => none
  | Nat.succ fuel' =>
      match formula with
      | Noun.atom _ => none
      | Noun.cell (Noun.cell b c) d =>
          match evalFuel fuel' subject (C b c), evalFuel fuel' subject d with
          | some left, some right => some (C left right)
          | _, _ => none
      | Noun.cell (Noun.atom 0) (Noun.atom axis) =>
          slot? axis subject
      | Noun.cell (Noun.atom 1) noun =>
          some noun
      | Noun.cell (Noun.atom 2) (Noun.cell b c) =>
          match evalFuel fuel' subject b, evalFuel fuel' subject c with
          | some subject', some formula' => evalFuel fuel' subject' formula'
          | _, _ => none
      | Noun.cell (Noun.atom 3) b =>
          match evalFuel fuel' subject b with
          | some noun => some (wut noun)
          | none => none
      | Noun.cell (Noun.atom 4) b =>
          match evalFuel fuel' subject b with
          | some (Noun.atom atom) => some (A (atom + 1))
          | _ => none
      | Noun.cell (Noun.atom 5) (Noun.cell b c) =>
          match evalFuel fuel' subject b, evalFuel fuel' subject c with
          | some left, some right => some (eqCode left right)
          | _, _ => none
      | Noun.cell (Noun.atom 6) (Noun.cell b (Noun.cell c d)) =>
          match evalFuel fuel' subject b with
          | some (Noun.atom 0) => evalFuel fuel' subject c
          | some (Noun.atom 1) => evalFuel fuel' subject d
          | _ => none
      | Noun.cell (Noun.atom 7) (Noun.cell b c) =>
          match evalFuel fuel' subject b with
          | some subject' => evalFuel fuel' subject' c
          | none => none
      | Noun.cell (Noun.atom 8) (Noun.cell b c) =>
          match evalFuel fuel' subject b with
          | some produced => evalFuel fuel' (C produced subject) c
          | none => none
      | Noun.cell (Noun.atom 9) (Noun.cell (Noun.atom axis) c) =>
          match evalFuel fuel' subject c with
          | some core => evalFuel fuel' core (invoke axis)
          | none => none
      | Noun.cell (Noun.atom 10) (Noun.cell (Noun.cell (Noun.atom axis) c) d) =>
          match evalFuel fuel' subject c, evalFuel fuel' subject d with
          | some replacement, some editedBase => edit? axis replacement editedBase
          | _, _ => none
      | Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell _ c) d) =>
          match evalFuel fuel' subject c, evalFuel fuel' subject d with
          | some hint, some product => evalFuel fuel' (C hint product) (slot 3)
          | _, _ => none
      | Noun.cell (Noun.atom 11) (Noun.cell (Noun.atom _) c) =>
          evalFuel fuel' subject c
      | _ => none

end Nock
end Formalization
