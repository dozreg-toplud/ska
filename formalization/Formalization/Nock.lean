/- Verbatim local specification from docs/nock/4.txt:

Nock 4K

A noun is an atom or a cell. An atom is a natural number. A cell is an ordered pair of nouns.

Reduce by the first matching pattern; variables match any noun.

nock(a)             *a
[a b c]             [a [b c]]

?[a b]              0
?a                  1
+[a b]              +[a b]
+a                  1 + a
=[a a]              0
=[a b]              1

/[1 a]              a
/[2 a b]            a
/[3 a b]            b
/[(a + a) b]        /[2 /[a b]]
/[(a + a + 1) b]    /[3 /[a b]]
/a                  /a

#[1 a b]            a
#[(a + a) b c]      #[a [b /[(a + a + 1) c]] c]
#[(a + a + 1) b c]  #[a [/[(a + a) c] b] c]
#a                  #a

*[a [b c] d]        [*[a b c] *[a d]]

*[a 0 b]            /[b a]
*[a 1 b]            b
*[a 2 b c]          *[*[a b] *[a c]]
*[a 3 b]            ?*[a b]
*[a 4 b]            +*[a b]
*[a 5 b c]          =[*[a b] *[a c]]

*[a 6 b c d]        *[a *[[c d] 0 *[[2 3] 0 *[a 4 4 b]]]]
*[a 7 b c]          *[*[a b] c]
*[a 8 b c]          *[[*[a b] a] c]
*[a 9 b c]          *[*[a c] 2 [0 1] 0 b]
*[a 10 [b c] d]     #[b *[a c] *[a d]]

*[a 11 [b c] d]     *[[*[a c] *[a d]] 0 3]
*[a 11 b c]         *[a c]

*a                  *a
-/

namespace Formalization
namespace Nock

-- Nock nouns:
-- "A noun is an atom or a cell. An atom is a natural number.
-- A cell is an ordered pair of nouns."
inductive Noun where
  | atom : Nat -> Noun
  | cell : Noun -> Noun -> Noun
  deriving DecidableEq, Repr

-- Constructors with short names for writing Nock formulas.
abbrev A : Nat -> Noun := Noun.atom
abbrev C : Noun -> Noun -> Noun := Noun.cell

-- Nock lists associate to the right: [a b c] == [a [b c]].
def n2 (x y : Noun) : Noun :=
  C x y

def n3 (x y z : Noun) : Noun :=
  C x (C y z)

def n4 (w x y z : Noun) : Noun :=
  C w (C x (C y z))

-- Formula notation for *[a 0 b].
def slot (axis : Nat) : Noun :=
  n2 (A 0) (A axis)

-- Formula notation for *[a 1 b].
def quote (noun : Noun) : Noun :=
  n2 (A 1) noun

-- The ? operator:
-- ?[a b] = 0
-- ?a     = 1
def wut : Noun -> Noun
  | Noun.atom _ => A 1
  | Noun.cell _ _ => A 0

-- The = operator:
-- =[a a] = 0
-- =[a b] = 1
def eqCode (left right : Noun) : Noun :=
  if left = right then A 0 else A 1

-- The formula produced by opcode 9's expansion:
-- *[a 9 b c] = *[*[a c] 2 [0 1] 0 b].
-- This helper is the "2 [0 1] 0 b" part.
def invoke (axis : Nat) : Noun :=
  n3 (A 2) (slot 1) (slot axis)

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

-- Relational slot lookup for /.
--
-- one   corresponds to /[1 a] = a.
-- left  corresponds to /[(a + a) b] = /[2 /[a b]].
-- right corresponds to /[(a + a + 1) b] = /[3 /[a b]].
inductive Slot : Nat -> Noun -> Noun -> Prop where
  -- /[1 a] = a
  | one {subject} :
      Slot 1 subject subject
  -- /[(a + a) b] = /[2 /[a b]]
  | left {axis subject head tail} :
      Slot axis subject (C head tail) ->
      Slot (2 * axis) subject head
  -- /[(a + a + 1) b] = /[3 /[a b]]
  | right {axis subject head tail} :
      Slot axis subject (C head tail) ->
      Slot (2 * axis + 1) subject tail

-- Relational edit for #.
--
-- one   corresponds to #[1 a b] = a.
-- left  corresponds to #[(a + a) b c] =
--   #[a [b /[(a + a + 1) c]] c].
-- right corresponds to #[(a + a + 1) b c] =
--   #[a [/[(a + a) c] b] c].
inductive Edit : Nat -> Noun -> Noun -> Noun -> Prop where
  -- #[1 a b] = a
  | one {replacement subject} :
      Edit 1 replacement subject replacement
  -- #[(a + a) b c] = #[a [b /[(a + a + 1) c]] c]
  | left {axis replacement head tail head'} :
      Edit axis replacement head head' ->
      Edit (2 * axis) replacement (C head tail) (C head' tail)
  -- #[(a + a + 1) b c] = #[a [/[(a + a) c] b] c]
  | right {axis replacement head tail tail'} :
      Edit axis replacement tail tail' ->
      Edit (2 * axis + 1) replacement (C head tail) (C head tail')

-- Big-step Nock evaluation: Eval subject formula out means *[subject formula]
-- reduces to out.
--
-- The final catch-all "*a = *a" is intentionally absent: it is the crashing or
-- non-reducing case, so this relation only derives successful evaluations.
inductive Eval : Noun -> Noun -> Noun -> Prop where
  -- *[a [b c] d] = [*[a b c] *[a d]]
  | cell {subject b c d left right} :
      Eval subject (C b c) left ->
      Eval subject d right ->
      Eval subject (C (C b c) d) (C left right)
  -- *[a 0 b] = /[b a]
  | op0 {subject axis out} :
      Slot axis subject out ->
      Eval subject (slot axis) out
  -- *[a 1 b] = b
  | op1 {subject noun} :
      Eval subject (quote noun) noun
  -- *[a 2 b c] = *[*[a b] *[a c]]
  | op2 {subject b c subject' formula' out} :
      Eval subject b subject' ->
      Eval subject c formula' ->
      Eval subject' formula' out ->
      Eval subject (n3 (A 2) b c) out
  -- *[a 3 b] = ?*[a b]
  | op3 {subject b noun} :
      Eval subject b noun ->
      Eval subject (n2 (A 3) b) (wut noun)
  -- *[a 4 b] = +*[a b]; +a = 1 + a for atoms.
  -- There is no successful constructor for +[a b] = +[a b].
  | op4 {subject b atom} :
      Eval subject b (A atom) ->
      Eval subject (n2 (A 4) b) (A (atom + 1))
  -- *[a 5 b c] = =[*[a b] *[a c]]
  | op5 {subject b c left right} :
      Eval subject b left ->
      Eval subject c right ->
      Eval subject (n3 (A 5) b c) (eqCode left right)
  -- *[a 6 b c d] expands to:
  -- *[a *[[c d] 0 *[[2 3] 0 *[a 4 4 b]]]]
  -- The expansion evaluates *[a b], increments twice, slots into [2 3],
  -- and selects c when the test is 0, or d when the test is 1.
  | op6_zero {subject b c d out} :
      Eval subject b (A 0) ->
      Eval subject c out ->
      Eval subject (n4 (A 6) b c d) out
  -- Same spec clause as op6_zero, for the test result 1 branch.
  | op6_one {subject b c d out} :
      Eval subject b (A 1) ->
      Eval subject d out ->
      Eval subject (n4 (A 6) b c d) out
  -- *[a 7 b c] = *[*[a b] c]
  | op7 {subject b c subject' out} :
      Eval subject b subject' ->
      Eval subject' c out ->
      Eval subject (n3 (A 7) b c) out
  -- *[a 8 b c] = *[[*[a b] a] c]
  | op8 {subject b c produced out} :
      Eval subject b produced ->
      Eval (C produced subject) c out ->
      Eval subject (n3 (A 8) b c) out
  -- *[a 9 b c] = *[*[a c] 2 [0 1] 0 b]
  | op9 {subject axis c core out} :
      Eval subject c core ->
      Eval core (invoke axis) out ->
      Eval subject (n3 (A 9) (A axis) c) out
  -- *[a 10 [b c] d] = #[b *[a c] *[a d]]
  | op10 {subject axis c d replacement editedBase out} :
      Eval subject c replacement ->
      Eval subject d editedBase ->
      Edit axis replacement editedBase out ->
      Eval subject (n3 (A 10) (n2 (A axis) c) d) out
  -- *[a 11 [b c] d] = *[[*[a c] *[a d]] 0 3]
  | op11_cell {subject b c d hint product out} :
      Eval subject c hint ->
      Eval subject d product ->
      Eval (C hint product) (slot 3) out ->
      Eval subject (n3 (A 11) (C b c) d) out
  -- *[a 11 b c] = *[a c]
  | op11_atom {subject tag c out} :
      Eval subject c out ->
      Eval subject (n3 (A 11) (A tag) c) out

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
