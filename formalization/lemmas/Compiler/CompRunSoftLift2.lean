import lemmas.Compiler.CompRunSoftLift
import lemmas.Compiler.CompRunSoftClass
import lemmas.Ska.SccLoopSoft2Eq

/-! # Soft-free parts on the fixed soft model `runLCS2` (track K, README Gaps 19 (g), 21.20)

Track I's `runLCS2` asks `+soft-ask` in `+crash-need` from both its callers: `+mede` (`%1` on
`%next`, `medeLS`) and `+collapse-lazy-atom` (`%3` / `%4` / `%5`, `collapseLazyAtomLS`).  On a
`SoftFree` nomm (cons, `%0`, `%1`, `%7`, `%10`) only the first matters, so `runLCS2` is the lift
of `runLCM env |` at a soft map `sm` exactly when every `%1` constant fits every node `+mede`
walks there (`medeAt`; `medeLS_lifts`).

* `n1Consts`: the constants of the `%1`s of a nomm;
* `MedeAllAt sm n`: every one of them is `medeAt sm` at every node of every lazy need;
* **`runLCS2_lift`**: on a `SoftFree` nomm under `MedeAllAt`, `runLCS2 env snd sup n goal region`
  is `runLCM env false sup n goal region` lifted at `sm` (`LiftsAt`);
* `medeAllAt_empty`: `MedeAllAt` holds at a soft map with no entry;
* `crxts_of_q_at`: `crxts_of_q` with the model a lift only at the state's soft map;
* **`crxts_softFree2`**: the soft-shape link `CompRunAtXTS (runLCS2 ..)` of a soft-free part,
  from the soft-free class (as `crxts_softFree` for `runLCS`) and `MedeAllAt gs.soft n`. -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp Lazy

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- The constants of the `%1`s of a nomm (through cons, `%7`, `%10`: the `SoftFree` forms). -/
def n1Consts : Nomm → List Noun
  | Nomm.cons p q => n1Consts p ++ n1Consts q
  | Nomm.n1 k => [k]
  | Nomm.n7 p q => n1Consts p ++ n1Consts q
  | Nomm.n10 _ v q => n1Consts v ++ n1Consts q
  | _ => []

/-- **Every `%1` constant of `n` fits every node `+mede` may walk at the soft map `sm`.** -/
def MedeAllAt (sm : TreapMap mugF SoftCall) (n : Nomm) : Prop :=
  ∀ k ∈ n1Consts n, ∀ (o : Nat) (laz : Lazy CSet), LazyAll (medeAt sm k) o laz

theorem medeAllAt_left {sm : TreapMap mugF SoftCall} {p q : Nomm}
    (h : ∀ k ∈ n1Consts p ++ n1Consts q, ∀ (o : Nat) (laz : Lazy CSet), LazyAll (medeAt sm k) o laz) :
    MedeAllAt sm p := fun k hk => h k (List.mem_append_left _ hk)

theorem medeAllAt_right {sm : TreapMap mugF SoftCall} {p q : Nomm}
    (h : ∀ k ∈ n1Consts p ++ n1Consts q, ∀ (o : Nat) (laz : Lazy CSet), LazyAll (medeAt sm k) o laz) :
    MedeAllAt sm q := fun k hk => h k (List.mem_append_right _ hk)

theorem liftsAt_none {α : Type} (sm : TreapMap mugF SoftCall) :
    LiftsAt sm (fun _ => Option.none : CMS (TreapMap mugF) α) (fun _ => Option.none) := fun _ => rfl

/-- **`runLCS2` on a soft-free nomm is the lift of `runLCM env |`** at a soft map `sm` where every
`%1` constant is `medeAt` at every node (the only place `runLCS2` asks `soft.gen` there). -/
theorem runLCS2_lift (env : CallEnv) (snd : Nomm → NeedOrd → Bool) : ∀ (n : Nomm), SoftFree n = true →
    ∀ (sm : TreapMap mugF SoftCall), MedeAllAt sm n → ∀ (sup : Option Nomm) (goal : CGoalL CSet) (region : List Nat),
      LiftsAt sm (runLCS2 (S := CSet) (Map := TreapMap mugF) env snd sup n goal region)
        (runLCM env false sup n goal region)
  | Nomm.cons p q, h, sm, hm, sup, goal, region => by
    simp only [SoftFree, Bool.and_eq_true] at h
    have ihp := runLCS2_lift env snd p h.1 sm (medeAllAt_left hm) sup
    have ihq := runLCS2_lift env snd q h.2 sm (medeAllAt_right hm) sup
    cases goal with
    | next laz th =>
      simp only [runLCS2, runLCM, pure_bind]
      refine liftsAt_bind (liftsAt_lift _ _) fun x => ?_
      rcases x with ⟨hed, tel, o⟩
      refine liftsAt_bind (liftsAt_lift _ _) fun nexh => ?_
      refine liftsAt_bind (ihq _ _) fun nex2 => ?_
      refine liftsAt_bind (liftsAt_lift _ _) fun nex2' => ?_
      exact liftsAt_bind (ihp _ _) fun nex1 => liftsAt_lift _ _
    | pick z o =>
      simp only [runLCS2, runLCM, pure_bind]
      refine liftsAt_bind (liftsAt_lift _ _) fun o' => ?_
      refine liftsAt_bind (ihq _ _) fun nex2 => ?_
      refine liftsAt_bind (liftsAt_lift _ _) fun nex2' => ?_
      exact liftsAt_bind (ihp _ _) fun nex1 => liftsAt_lift _ _
    | done =>
      simp only [runLCS2, runLCM, bind_assoc]
      refine liftsAt_bind (liftsAt_lift _ _) fun r => ?_
      refine liftsAt_bind (liftsAt_lift _ _) fun o => ?_
      simp only [pure_bind]
      refine liftsAt_bind (liftsAt_lift _ _) fun x => ?_
      rcases x with ⟨hed, tel, o'⟩
      refine liftsAt_bind (liftsAt_lift _ _) fun nexh => ?_
      refine liftsAt_bind (ihq _ _) fun nex2 => ?_
      refine liftsAt_bind (liftsAt_lift _ _) fun nex2' => ?_
      exact liftsAt_bind (ihp _ _) fun nex1 => liftsAt_lift _ _
  | Nomm.n0 ax, _, sm, _, sup, goal, region => by
    simp only [runLCS2]
    exact liftsAt_lift _ _
  | Nomm.n1 k, _, sm, hm, sup, goal, region => by
    cases goal with
    | next laz th =>
      have e : (runLCM env false sup (Nomm.n1 k) (CGoalL.next laz th) region : CM (TreapMap mugF) (NextL CSet))
          = (do let o ← medeL th k laz; pure ⟨ofSure Sure.bunt, jmp0 o⟩) := rfl
      rw [e]
      simp only [runLCS2]
      exact liftsAt_bind (medeLS_lifts sm th k laz (fun o => hm k (by simp [n1Consts]) o laz)) fun _ => liftsAt_pure _ _
    | pick z o =>
      simp only [runLCS2]
      exact liftsAt_lift _ _
    | done =>
      simp only [runLCS2]
      exact liftsAt_lift _ _
  | Nomm.n7 p q, h, sm, hm, sup, goal, region => by
    simp only [SoftFree, Bool.and_eq_true] at h
    have ihp := runLCS2_lift env snd p h.1 sm (medeAllAt_left hm) sup
    have ihq := runLCS2_lift env snd q h.2 sm (medeAllAt_right hm) (some p)
    simp only [runLCS2, runLCM]
    exact liftsAt_bind (ihq _ _) fun nex => ihp _ _
  | Nomm.n10 a v q, h, sm, hm, sup, goal, region => by
    simp only [SoftFree, Bool.and_eq_true] at h
    have ihv := runLCS2_lift env snd v h.1.2 sm (medeAllAt_left hm) sup
    have ihq := runLCS2_lift env snd q h.2 sm (medeAllAt_right hm) sup
    simp only [runLCS2, runLCM]
    refine liftsAt_bind (liftsAt_lift _ _) fun next => ?_
    refine liftsAt_bind (liftsAt_lift _ _) fun x => ?_
    rcases x with ⟨don, rec, o⟩
    refine liftsAt_bind (liftsAt_lift _ _) fun nexR => ?_
    refine liftsAt_bind (ihv _ _) fun nexDon => ?_
    refine liftsAt_bind (liftsAt_lift _ _) fun nexDon' => ?_
    exact liftsAt_bind (ihq _ _) fun nexRec => liftsAt_lift _ _
  | Nomm.n2 _ _ _, h, _, _, _, _, _ => by simp [SoftFree] at h
  | Nomm.n3 _, h, _, _, _, _, _ => by simp [SoftFree] at h
  | Nomm.n4 _, h, _, _, _, _, _ => by simp [SoftFree] at h
  | Nomm.n5 _ _, h, _, _, _, _, _ => by simp [SoftFree] at h
  | Nomm.n6 _ _ _, h, _, _, _, _, _ => by simp [SoftFree] at h
  | Nomm.n11s _ _ _, h, _, _, _, _, _ => by simp [SoftFree] at h
  | Nomm.n11d _ _ _ _, h, _, _, _, _, _ => by simp [SoftFree] at h
  | Nomm.n12 _ _, h, _, _, _, _, _ => by simp [SoftFree] at h
  | Nomm.mean _ _ _ _ _, h, _, _, _, _, _ => by simp [SoftFree] at h

mutual
theorem lazyAll_of {P : Nat → Sure CSet → Prop} (h : ∀ o s, P o s) : ∀ (o : Nat) (l : Lazy CSet), LazyAll P o l
  | o, Lazy.mk s fk bd => by unfold LazyAll; exact ⟨h o s, forksAll_of h fk, bondsAll_of h bd⟩
theorem forksAll_of {P : Nat → Sure CSet → Prop} (h : ∀ o s, P o s) :
    ∀ (fk : List ((Nat × Lazy CSet) × (Nat × Lazy CSet))), ForksAll P fk
  | [] => by unfold ForksAll; trivial
  | ((oy, y), (on, n)) :: rest => by unfold ForksAll; exact ⟨lazyAll_of h oy y, lazyAll_of h on n, forksAll_of h rest⟩
theorem bondsAll_of {P : Nat → Sure CSet → Prop} (h : ∀ o s, P o s) : ∀ (bd : List (Nat × Lazy CSet)), BondsAll P bd
  | [] => by unfold BondsAll; trivial
  | (o, l) :: rest => by unfold BondsAll; exact ⟨lazyAll_of h o l, bondsAll_of h rest⟩
end

/-- `MedeAllAt` at a soft map with no entry: every node is not soft. -/
theorem medeAllAt_empty {sm : TreapMap mugF SoftCall} (h0 : ∀ o, HoonMap.get sm o = Option.none) (n : Nomm) :
    MedeAllAt sm n := by
  intro k _ o laz
  exact lazyAll_of (fun o' _ => Or.inl (h0 o')) o laz

/-- **`crxts_of_q` with the model a lift only at the state's soft map** (`LiftsAt gs.soft`). -/
theorem crxts_of_q_at {ctx : Noun} {R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)}
    {RS : Nomm → CGoalL CSet → List Nat → CMS (TreapMap mugF) (NextL CSet)}
    {X : GenRest → Noun → Noun → Prop} {Y : GenRest → GenRest → Prop} {n : Nomm} {goal : CGoalL CSet}
    {region : List Nat} {gs : GenSf (TreapMap mugF)} (hl : LiftsAt gs.soft (RS n goal region) (R n goal region))
    (h : CompRunAtXQ (fun x => x.soft = softMapNoun gs.soft) R ctx X (fun a c => Y a c ∧ c.soft = a.soft) n goal
      region gs.g) :
    CompRunAtXTS RS ctx X Y n goal region gs := by
  have hp : RS n goal region gs = liftS (R n goal region) gs := hl gs.g
  intro x mono sup hs hX
  obtain ⟨x', ⟨hy, hs'⟩, hr⟩ := h x mono sup hs hX
  refine ⟨x', hy, ?_⟩
  rw [hr, hp]
  have hx' : { x' with soft := softMapNoun gs.soft } = x' := by
    obtain ⟨c', s', f'⟩ := x'
    simp only at hs' ⊢
    rw [hs', hs]
  simp only [liftS]
  cases R n goal region gs.g with
  | none => rfl
  | some p => simp only [Option.map_some, hx']

/-- **The soft-shape link of a soft-free part on the fixed model `runLCS2`**: `crxts_softFree`
with `runLCS2` for `runLCS`, under `MedeAllAt gs.soft n` (every `%1` constant fits every node
`+mede` may walk at the state's soft map: `+crash-need`'s `+soft-ask` is never asked). -/
theorem crxts_softFree2 {ctx : Noun} (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (X : Option Nomm → GenRest → Noun → Noun → Prop)
    (Y : GenRest → GenRest → Prop) (gs : GenSf (TreapMap mugF))
    (hY : ∀ msup, YOkQ (fun x => x.soft = softMapNoun gs.soft) (X msup) (fun a c => Y a c ∧ c.soft = a.soft))
    (hXs : ∀ msup p x mono sup, X msup x mono sup → X (some p) x mono (C (A 0) p.toNoun))
    (L : LeafQ (fun x => x.soft = softMapNoun gs.soft) env ctx X (fun a c => Y a c ∧ c.soft = a.soft))
    (n : Nomm) (hn : SoftFree n = true) (hm : MedeAllAt gs.soft n) (msup : Option Nomm) (region : List Nat)
    (goal : CGoalL CSet) (hi : GInv gs.g goal) :
    CompRunAtXTS (runLCS2 env snd msup) ctx (X msup) Y n goal region gs :=
  crxts_of_q_at (R := runLCM env false msup) (runLCS2_lift env snd n hn gs.soft hm msup goal region)
    ((comp_run_softFreeQ h7 hcode env _ X _ hY hXs L n hn msup region).link goal gs.g hi)

end Compiler
end Formalization
