import lemmas.Compiler.CompRunSoftQ
import lemmas.Compiler.CompRunSoftMede
import lemmas.Compiler.CompRunSoftDefs

/-! # Soft-free parts after a soft call: the model is a lift, the link a `Q` link (README Gaps 19 (g))

After the corpus's soft tail call, the enclosing parts (the subjects of the `%7`s: cons, `%10`,
`%0`, `%1`, `%7`) run with the call's entry in `soft.gen`.  They make no call and no `%6`, so
the model `runLCS` on them is `runLCM env |` lifted (`soft.gen` kept), and their pill link is a
`CompRunAtXQ` link at the rest predicate `x.soft = softMapNoun sm` (`CompRunSoftQ.lean`).

* `liftS_bind`, `liftS_pure`: `liftS` is a monad map;
* `SoftFree`: cons, `%0`, `%1`, `%7`, `%10` only;
* **`runLCS_lift`**: on a `SoftFree` nomm, `runLCS env snd sup` is `runLCM env false sup` with the
  soft map kept;
* **`crxts_of_q`**: a `CompRunAtXQ` link at `x.soft = softMapNoun gs.soft` with a `Y` that keeps
  `soft` is a `CompRunAtXTS` link, when the model is a lift. -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun}

theorem liftS_bind {α β : Type} (m : CM (TreapMap mugF) α) (f : α → CM (TreapMap mugF) β) :
    ((liftS m >>= fun a => liftS (f a)) : CMS (TreapMap mugF) β) = liftS (m >>= f) := by
  funext s
  simp only [liftS, bind, StateT.bind]
  cases m s.g with
  | none => rfl
  | some p => rfl

theorem liftS_pure {α : Type} (a : α) : (pure a : CMS (TreapMap mugF) α) = liftS (pure a) := rfl

/-- **The nomms that read nothing of `soft.gen` in the model**: cons, `%0`, `%1`, `%7`, `%10`. -/
def SoftFree : Nomm → Bool
  | Nomm.cons p q => SoftFree p && SoftFree q
  | Nomm.n0 _ => true
  | Nomm.n1 _ => true
  | Nomm.n7 p q => SoftFree p && SoftFree q
  | Nomm.n10 _ v q => SoftFree v && SoftFree q
  | _ => false

theorem runLC_n1 (env : CallEnv) (sup : Option Nomm) (k : Noun) (goal : CGoalL CSet) (region : List Nat) :
    (runLC env sup (Nomm.n1 k) goal region : CM (TreapMap mugF) (NextL CSet)) = runL (Nomm.n1 k) goal region := rfl

/-- **The model on a soft-free nomm is a lift**: `runLCS` is `runLCM env |` on the `Gen` part, the
soft map kept. -/
theorem runLCS_lift (env : CallEnv) (snd : Nomm → NeedOrd → Bool) : ∀ (n : Nomm), SoftFree n = true →
    ∀ (sup : Option Nomm), runLCS (S := CSet) (Map := TreapMap mugF) env snd sup n
      = fun goal region => liftS (runLCM env false sup n goal region)
  | Nomm.cons p q, h, sup => by
    simp only [SoftFree, Bool.and_eq_true] at h
    have ihp := runLCS_lift env snd p h.1 sup
    have ihq := runLCS_lift env snd q h.2 sup
    funext goal region
    cases goal with
    | next laz th =>
      simp only [runLCS, runLCM, ihp, ihq, liftS_bind, liftS_pure]
      simp only [← liftS_bind, ← liftS_pure, bind_assoc, pure_bind]
    | pick z o =>
      simp only [runLCS, runLCM, ihp, ihq, liftS_bind, liftS_pure]
      simp only [← liftS_bind, ← liftS_pure, bind_assoc, pure_bind]
    | done =>
      simp only [runLCS, runLCM, ihp, ihq, liftS_bind, liftS_pure]
      simp only [← liftS_bind, ← liftS_pure, bind_assoc, pure_bind]
  | Nomm.n0 ax, _, sup => by
    funext goal region
    simp only [runLCS]
    rfl
  | Nomm.n1 k, _, sup => by
    funext goal region
    simp only [runLCS]
    rfl
  | Nomm.n7 p q, h, sup => by
    simp only [SoftFree, Bool.and_eq_true] at h
    have ihp := runLCS_lift env snd p h.1 sup
    have ihq := runLCS_lift env snd q h.2 (some p)
    funext goal region
    simp only [runLCS, runLCM, ihp, ihq, liftS_bind]
  | Nomm.n10 a v q, h, sup => by
    simp only [SoftFree, Bool.and_eq_true] at h
    have ihv := runLCS_lift env snd v h.1 sup
    have ihq := runLCS_lift env snd q h.2 sup
    funext goal region
    simp only [runLCS, runLCM, ihv, ihq]
    simp only [← liftS_bind, ← liftS_pure, bind_assoc, pure_bind]
  | Nomm.n2 _ _ _, h, _ => by simp [SoftFree] at h
  | Nomm.n3 _, h, _ => by simp [SoftFree] at h
  | Nomm.n4 _, h, _ => by simp [SoftFree] at h
  | Nomm.n5 _ _, h, _ => by simp [SoftFree] at h
  | Nomm.n6 _ _ _, h, _ => by simp [SoftFree] at h
  | Nomm.n11s _ _ _, h, _ => by simp [SoftFree] at h
  | Nomm.n11d _ _ _ _, h, _ => by simp [SoftFree] at h
  | Nomm.n12 _ _, h, _ => by simp [SoftFree] at h
  | Nomm.mean _ _ _ _ _, h, _ => by simp [SoftFree] at h

/-- **A `Q` link at a fixed soft map is a link in the soft shape**: when the model is the lift of
`R`, a `CompRunAtXQ` link at `x.soft = softMapNoun gs.soft` whose `Y` keeps `soft` gives the
`CompRunAtXTS` link (the rest returned already holds the map's noun). -/
theorem crxts_of_q {R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)}
    {RS : Nomm → CGoalL CSet → List Nat → CMS (TreapMap mugF) (NextL CSet)}
    {X : GenRest → Noun → Noun → Prop} {Y : GenRest → GenRest → Prop} {n : Nomm} {goal : CGoalL CSet}
    {region : List Nat} {gs : GenSf (TreapMap mugF)} (hl : RS n goal region = liftS (R n goal region))
    (h : CompRunAtXQ (fun x => x.soft = softMapNoun gs.soft) R ctx X (fun a c => Y a c ∧ c.soft = a.soft) n goal
      region gs.g) :
    CompRunAtXTS RS ctx X Y n goal region gs := by
  intro x mono sup hs hX
  obtain ⟨x', ⟨hy, hs'⟩, hr⟩ := h x mono sup hs hX
  refine ⟨x', hy, ?_⟩
  rw [hr, hl]
  have hx' : { x' with soft := softMapNoun gs.soft } = x' := by
    obtain ⟨c', s', f'⟩ := x'
    simp only at hs' ⊢
    rw [hs', hs]
  simp only [liftS]
  cases R n goal region gs.g with
  | none => rfl
  | some p => simp only [Option.map_some, hx']

end Compiler
end Formalization
