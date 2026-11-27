module

public import core.Nock
/-!
The form of the Nock specification that the proofs work with: `Slot` and
`Edit` on `Nat` axes, and `Eval` with opcode 6 as two rules and atoms where
the specification's rules have variables that only an atom can fill.
Nothing here is trusted: `lemmas/SpecEquiv.lean` proves `Eval` equal to
`Nock` of `core/Nock.lean` (`nock_iff_eval`), `Slot` to `Fas` and `Edit` to
`Hax`.
-/

@[expose] public section

namespace Formalization
namespace Nock

-- Nock lists associate to the right: [a b c] == [a [b c]].
abbrev n2 (x y : Noun) : Noun :=
  C x y

abbrev n3 (x y z : Noun) : Noun :=
  C x (C y z)

abbrev n4 (w x y z : Noun) : Noun :=
  C w (C x (C y z))

-- Formula notation for *[a 0 b].
abbrev slot (axis : Nat) : Noun :=
  n2 (A 0) (A axis)

-- Formula notation for *[a 1 b].
abbrev quote (noun : Noun) : Noun :=
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
abbrev invoke (axis : Nat) : Noun :=
  n3 (A 2) (slot 1) (slot axis)

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
--
-- Edit axis replacement subject out means #[axis replacement subject] = out.
-- As in the spec, an edit at axis 2a is an edit at axis a whose replacement
-- is the new head paired with the old tail, so the axis is consumed from its
-- low bit while the path it names is walked from the root.
inductive Edit : Nat -> Noun -> Noun -> Noun -> Prop where
  -- #[1 a b] = a
  | one {replacement subject} :
      Edit 1 replacement subject replacement
  -- #[(a + a) b c] = #[a [b /[(a + a + 1) c]] c]
  | left {axis replacement subject tail out} :
      Slot (2 * axis + 1) subject tail ->
      Edit axis (C replacement tail) subject out ->
      Edit (2 * axis) replacement subject out
  -- #[(a + a + 1) b c] = #[a [/[(a + a) c] b] c]
  | right {axis replacement subject head out} :
      Slot (2 * axis) subject head ->
      Edit axis (C head replacement) subject out ->
      Edit (2 * axis + 1) replacement subject out

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

end Nock
end Formalization
