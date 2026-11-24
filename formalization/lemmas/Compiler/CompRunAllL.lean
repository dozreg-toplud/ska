import lemmas.Compiler.CompRunTenL

/-!
# The run link on lazy goals for the plain class (`RunLinkL`)

**`comp_run_all_l`**: for every nomm of the plain class (`PlainOk`: `%0`,
`%1`, `%3`, `%4`, `%5`, `%7`, cons, `%10` with an axis not `0`, and the
indirect call `[2 p q ~]`, nested in any way, no `%6`), every goal and state
with `GInv` (lazy needs with forks and bonds to any depth, with the looks,
the registers below the counter, no register twice, no key twice, the
labels below the label counter, the mode `%run`), every region, every
`env` and `msup`, the `$` arm of `+run` is `runLC env msup` (for every
`mono`, Hoon `sup` and rest of the state with an empty `soft`).  Given only
`slot? 7 ctx = some compK` and `slot? 52 ctx = some cod`.

By induction on the nomm: each case takes its parts' links on every goal
with `GInv` (the induction hypothesis) and their results (`res_all`, which
gives `GInv` of the next goal and `CopyH` at each `+copy`).  So the call
nested anywhere is covered: `[8 [9 2 [0 1]] c]` for every `c` of the class
(the `example` below), a call in the head of a cons (its result has a bond
from `+past`), a call in the tail (the head runs for a goal with a bond),
calls under `%3`, `%4`, `%5`, `%7`, `%10`, and calls whose subject or
formula calls.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-- **The run link on every goal with the invariant**, for every nomm of
the plain class. -/
theorem comp_run_all_l (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) : ∀ (n : Nomm), PlainOk n = true → ∀ (msup : Option Nomm) (region : List Nat)
      (goal : CGoalL CSet) (g : Gen (TreapMap mugF)), GInv g goal →
      CompRunAtR (runLC env msup) ctx n goal region g
  | Nomm.cons p q, h, msup, region, goal, g, hi => by
    have h' := h
    simp only [PlainOk, Bool.and_eq_true] at h'
    exact comp_run_consL h7 hcode env msup p q
      ⟨comp_run_all_l h7 hcode env p h'.1 msup region, res_all env p h'.1 msup region, h'.1⟩
      ⟨comp_run_all_l h7 hcode env q h'.2 msup region, res_all env q h'.2 msup region, h'.2⟩ goal g hi
  | Nomm.n0 ax, _, msup, region, goal, g, hi => crc_of_pure env rfl (comp_run_n0L h7 ax goal region g hi) msup
  | Nomm.n1 k, _, msup, region, goal, g, hi => crc_of_pure env rfl (comp_run_n1L h7 k goal region g hi) msup
  | Nomm.n2 p q Option.none, h, msup, region, goal, g, hi => by
    have h' := h
    simp only [PlainOk, Bool.and_eq_true] at h'
    exact comp_run_n2L h7 hcode env msup p q
      ⟨comp_run_all_l h7 hcode env p h'.1 msup region, res_all env p h'.1 msup region, h'.1⟩
      ⟨comp_run_all_l h7 hcode env q h'.2 msup region, res_all env q h'.2 msup region, h'.2⟩ goal g hi
  | Nomm.n3 p, h, msup, region, goal, g, hi => by
    simp only [PlainOk] at h
    exact comp_run_n3L h7 env msup p goal region g hi (comp_run_all_l h7 hcode env p h msup region)
  | Nomm.n4 p, h, msup, region, goal, g, hi => by
    simp only [PlainOk] at h
    exact comp_run_n4L h7 env msup p goal region g hi (comp_run_all_l h7 hcode env p h msup region)
  | Nomm.n5 p q, h, msup, region, goal, g, hi => by
    have h' := h
    simp only [PlainOk, Bool.and_eq_true] at h'
    exact comp_run_n5L h7 hcode env msup p q
      ⟨comp_run_all_l h7 hcode env p h'.1 msup region, res_all env p h'.1 msup region, h'.1⟩
      ⟨comp_run_all_l h7 hcode env q h'.2 msup region, res_all env q h'.2 msup region, h'.2⟩ goal g hi
  | Nomm.n7 p q, h, msup, region, goal, g, hi => by
    simp only [PlainOk, Bool.and_eq_true] at h
    exact comp_run_n7C env msup p q goal region g (comp_run_all_l h7 hcode env q h.2 (some p) region goal g hi)
      (fun nex g1 e => comp_run_all_l h7 hcode env p h.1 msup region nex.goal g1
        (res_all env q h.2 (some p) region goal g g1 nex hi e).2.2.1)
  | Nomm.n10 a v q, h, msup, region, goal, g, hi => by
    have h' := h
    simp only [PlainOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h'
    exact comp_run_n10L h7 hcode env msup a h'.1.1 v q
      ⟨comp_run_all_l h7 hcode env v h'.1.2 msup region, res_all env v h'.1.2 msup region, h'.1.2⟩
      ⟨comp_run_all_l h7 hcode env q h'.2 msup region, res_all env q h'.2 msup region, h'.2⟩ goal g hi
  | Nomm.n2 _ _ (some _), h, _, _, _, _, _ => by simp [PlainOk] at h
  | Nomm.n6 _ _ _, h, _, _, _, _, _ => by simp [PlainOk] at h
  | Nomm.n11s _ _ _, h, _, _, _, _, _ => by simp [PlainOk] at h
  | Nomm.n11d _ _ _ _, h, _, _, _, _, _ => by simp [PlainOk] at h
  | Nomm.n12 _ _, h, _, _, _, _, _ => by simp [PlainOk] at h
  | Nomm.mean _ _ _ _ _, h, _, _, _, _, _ => by simp [PlainOk] at h

/-- **`RunLinkL` holds** of every context with the compiler's core at axis
`7` and a code table at axis `52`. -/
theorem runLinkL (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod) :
    RunLinkL ctx :=
  fun env n hn goal region g hi msup => comp_run_all_l h7 hcode env n hn msup region goal g hi

/-- **At the entry of `+comp`**: from the bunt state with `[%done ~]` and the
region `~`. -/
theorem comp_run_entry_l (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (n : Nomm) (hn : PlainOk n = true) :
    CompRunAtC env ctx n CGoalL.done [] genEntry :=
  runLinkL h7 hcode env n hn CGoalL.done [] genEntry rfl

/-- **The fragment of `CompRunCall.lean` is in the plain class.** -/
theorem plainOk_of_indOk : ∀ (n : Nomm), indOk n = true → PlainOk n = true := by
  intro n
  induction n with
  | cons p q ihp ihq =>
    intro h; simp only [indOk, Bool.and_eq_true] at h
    simp only [PlainOk, Bool.and_eq_true]
    simp only [Nomm.pure, Bool.and_eq_true, noSix, tenOk] at h
    exact ⟨ihp (indOk_of_pure p h.1.1.1 h.1.2.1 h.2.1), ihq (indOk_of_pure q h.1.1.2 h.1.2.2 h.2.2)⟩
  | n0 _ => intro _; rfl
  | n1 _ => intro _; rfl
  | n2 p q info ihp ihq =>
    intro h
    cases info with
    | none =>
      simp only [indOk, Bool.and_eq_true] at h
      simp only [PlainOk, Bool.and_eq_true]
      exact ⟨ihp (indOk_of_pure p h.1.1.1 h.1.1.2 h.1.2), ihq h.2⟩
    | some _ => simp [indOk, Nomm.pure] at h
  | n3 p ih => intro h; simp only [indOk] at h; exact ih h
  | n4 p ih => intro h; simp only [indOk] at h; exact ih h
  | n5 p q ihp ihq =>
    intro h; simp only [indOk, Bool.and_eq_true] at h
    simp only [PlainOk, Bool.and_eq_true]
    exact ⟨ihp (indOk_of_pure p h.1.1.1 h.1.1.2 h.1.2), ihq h.2⟩
  | n6 _ _ _ _ _ _ => intro h; simp [indOk, noSix] at h
  | n7 p q ihp ihq =>
    intro h; simp only [indOk, Bool.and_eq_true] at h
    simp only [PlainOk, Bool.and_eq_true]
    exact ⟨ihp h.1, ihq h.2⟩
  | n10 a v q ihv ihq =>
    intro h; simp only [indOk, Bool.and_eq_true] at h
    simp only [Nomm.pure, Bool.and_eq_true, noSix, tenOk, bne_iff_ne, ne_eq] at h
    simp only [PlainOk, Bool.and_eq_true, bne_iff_ne, ne_eq]
    exact ⟨⟨h.2.1.1, ihv (indOk_of_pure v h.1.1.1 h.1.2.1 h.2.1.2)⟩, ihq (indOk_of_pure q h.1.1.2 h.1.2.2 h.2.2)⟩
  | n11s _ _ _ _ => intro h; simp [indOk, Nomm.pure] at h
  | n11d _ _ _ _ _ _ => intro h; simp [indOk, Nomm.pure] at h
  | n12 _ _ _ _ => intro h; simp [indOk, Nomm.pure] at h
  | mean _ _ _ _ _ _ _ => intro h; simp [indOk, Nomm.pure] at h

/-- **An example**: the Nock `[8 [9 2 [0 1]] c]` (push the product of arm
`2` of the subject, then `c`), as the nomm `[7 [[7 [0 1] [2 [0 1] [0 2]]] [0
1]] c]`, for every `c` of the class, on every goal and state with the
invariant: the link with no hypothesis but the context.  The cons pushes
the call's product with the subject, so `c` runs first in the compilation
for the goal, and the cons runs for the goal `c` returns (a lazy goal when
`c` calls). -/
example (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod) (env : CallEnv)
    (c : Nomm) (hc : PlainOk c = true) (goal : CGoalL CSet) (region : List Nat) (g : Gen (TreapMap mugF))
    (hi : GInv g goal) :
    CompRunAtC env ctx
      (Nomm.n7 (Nomm.cons (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n0 2) Option.none)) (Nomm.n0 1)) c)
      goal region g :=
  runLinkL h7 hcode env _ (by simp [PlainOk, hc]) goal region g hi

/-- The same with `c` a call nested in a cons whose head calls:
`[8 [9 2 [0 1]] [[2 [0 3] [0 2]] [0 1]]]` under `%done`, from every state
that does not drop. -/
example (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod) (env : CallEnv)
    (region : List Nat) (g : Gen (TreapMap mugF)) (hd : g.drop = false) :
    CompRunAtC env ctx
      (Nomm.n7 (Nomm.cons (Nomm.n7 (Nomm.n0 1) (Nomm.n2 (Nomm.n0 1) (Nomm.n0 2) Option.none)) (Nomm.n0 1))
        (Nomm.cons (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 1)))
      CGoalL.done region g :=
  runLinkL h7 hcode env _ rfl CGoalL.done region g hd

end Compiler
end Formalization
