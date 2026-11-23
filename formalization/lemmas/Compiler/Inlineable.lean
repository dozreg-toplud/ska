import lemmas.Compiler.Lib
import lemmas.Pill.Arm.Inlineable
import lemmas.Ska.FolLoop

/-!
`+inlineable` of the compiler against `inlineable` of `lemmas/Ska/FolLoop.lean`.
The gate reads nothing from its context; it calls itself through `=*  l  .`.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel

@[nock_exec] theorem inlineable_arm (c : Noun) :
    nock c inlineable.arm = some (C inlineable.battery (C (C (A 0) (A 0)) c)) := by
  nock_open inlineable.arm; simp only [nock_exec]

theorem loob_and' (a b : Bool) : (if a = true then Hoon.loob b else A 1) = Hoon.loob (a && b) := by
  cases a <;> rfl

theorem loob_rev (b : Bool) : (if b = true then A 0 else A 1) = Hoon.loob b := by
  cases b <;> rfl

theorem ite_some {α : Type} (c : Prop) [Decidable c] (x y : α) :
    (if c then some x else some y) = some (if c then x else y) := by
  split <;> rfl

set_option hygiene false in
/-- The common step of the cases: run the tests, recurse by `ih`. -/
macro "inl_simp" : tactic => `(tactic|
  (simp (disch := (simp only [nsize] at hlt ⊢; omega)) [nock_exec, nock_ite, inlineable, ih,
     ite_some, loob_rev, loob_and', Bool.and_assoc]
   try rfl))

set_option maxHeartbeats 1000000 in
/-- Slamming `+inlineable` on a noun, by induction on its size.  About seventy
cases of the formula run the whole chain of tests, hence the heartbeats. -/
theorem inlineable_gate (ctx : Noun) : ∀ (n : Nat) (f : Noun), nsize f < n →
    nock (C inlineable.battery (C f ctx)) inlineable.battery
      = some (Hoon.loob (inlineable f)) := by
  intro n
  induction n with
  | zero => intro f h; omega
  | succ n ih =>
    intro f hlt
    nock_open inlineable.battery
    rcases f with a | ⟨k | ⟨h1, h2⟩, t⟩
    · simp [nock_exec, inlineable, Hoon.loob]
    · rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
      · rcases t with _ | ⟨_, _⟩ <;> inl_simp
      · inl_simp
      · inl_simp
      · rcases t with _ | ⟨_, _⟩ <;> inl_simp
      · rcases t with _ | ⟨_, _⟩ <;> inl_simp
      · rcases t with _ | ⟨_ | ⟨_, _⟩, _ | ⟨_, _⟩⟩ <;> inl_simp
      · rcases t with _ | ⟨_ | ⟨_, _⟩, _ | ⟨_ | ⟨_, _⟩, _ | ⟨_, _⟩⟩⟩ <;> inl_simp
      · rcases t with _ | ⟨_ | ⟨_, _⟩, _ | ⟨_, _⟩⟩ <;> inl_simp
      · rcases t with _ | ⟨_ | ⟨_, _⟩, _ | ⟨_, _⟩⟩ <;> inl_simp
      · inl_simp
      · rcases t with _ | ⟨_ | ⟨_ | ⟨_, _⟩, _ | ⟨_, _⟩⟩, _ | ⟨_, _⟩⟩ <;> inl_simp
      · rcases t with _ | ⟨_ | ⟨_ | ⟨_, _⟩, _ | ⟨_, _⟩⟩, _ | ⟨_, _⟩⟩ <;> inl_simp
      · rcases t with _ | ⟨_ | ⟨_, _⟩, _ | ⟨_, _⟩⟩ <;> inl_simp
      · have hm : inlineable (C (A (k + 13)) t) = false := by rcases t with _ | ⟨_, _⟩ <;> rfl
        simp [nock_exec, hm, Hoon.loob]
    · rcases t with _ | ⟨t1, t2⟩
      · simp [nock_exec, inlineable, Hoon.loob]
      · simp only [nsize] at hlt
        inl_simp

/-- Slamming `+inlineable` on a noun, in any context. -/
theorem inlineable_gate' (ctx f : Noun) :
    nock (C inlineable.battery (C f ctx)) inlineable.battery = some (Hoon.loob (inlineable f)) :=
  inlineable_gate ctx _ f (Nat.lt_succ_self _)

end Compiler
end Formalization
