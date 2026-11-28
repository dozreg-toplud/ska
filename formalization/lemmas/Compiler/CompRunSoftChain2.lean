import lemmas.Compiler.CompRunSoftChain
import lemmas.Compiler.CompRunSoftLift2
import lemmas.Ska.SccLoopSoft2

/-! # The corpus's soft chains on the fixed soft model `runLCS2` (track K, README Gaps 19 (g), 21.20)

`comp_run_softChain` (`CompRunSoftChain.lean`) links the chains `[7 p1 .. [7 pk [2 [0 1] [1 f]
[~ b ~]]]]` against `runLCS`.  On track I's `runLCS2` the same chain is linked here when every
`%1` constant of each soft-free `pi` fits every node `+mede` walks at the soft map the run of the
rest left (`MedeAllAt`, so `+crash-need`'s `+soft-ask` is not asked there; the case where it is
asked needs the pill link of that branch, not done).

* `callLS_congr_q`: a direct call with a `safeFolFol` formula never runs `rq`;
* `runLCS2_softTail_eq`: on the soft tail call, `runLCS2` is `runLCS`;
* `crxts_congr`: the link depends on the model only at its state;
* `comp_run_n7TS2`: the `%7` link on `runLCS2` (the proof of `comp_run_n7TS`);
* `SoftChainOk2`: `SoftChainOk` with the result invariant on `runLCS2` and `MedeAllAt`;
* **`comp_run_softChain2`**: the chain in the soft shape `CompRunAtXTS (runLCS2 env snd msup)`. -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun}

/-- **A direct call whose formula is `safeFolFol` never runs `rq`.** -/
theorem callLS_congr_q {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] (env : CallEnv)
    (rp rq rq' : CGoalL S → List Nat → CMS Map (NextL S)) (p q : Nomm) (b : Bell) (key : Option Noun)
    (sup : Option Nomm) (goal : CGoalL S) (region : List Nat) (hq : safeFolFol q = true) :
    callLS env rp rq p q (some (b, key)) sup goal region = callLS env rp rq' p q (some (b, key)) sup goal region := by
  simp only [callLS, hq, if_true]

/-- **On the soft tail call `runLCS2` is `runLCS`**: `%0` is lifted in both, and the formula
`%1 f` is `safeFolFol`, never run. -/
theorem runLCS2_softTail_eq (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (msup : Option Nomm) (f : Noun)
    (b : Bell) (goal : CGoalL CSet) (region : List Nat) :
    runLCS2 (S := CSet) (Map := TreapMap mugF) env snd msup (Nomm.n2 (Nomm.n0 1) (Nomm.n1 f) (some (b, Option.none)))
        goal region
      = runLCS env snd msup (Nomm.n2 (Nomm.n0 1) (Nomm.n1 f) (some (b, Option.none))) goal region := by
  have h0 : runLCS2 (S := CSet) (Map := TreapMap mugF) env snd msup (Nomm.n0 1)
      = runLCS env snd msup (Nomm.n0 1) := by
    funext g r; simp only [runLCS2, runLCS]
  simp only [runLCS2, runLCS, h0]
  exact callLS_congr_q env _ _ _ _ _ b Option.none msup goal region rfl

/-- The link depends on the model only at its state. -/
theorem crxts_congr {R R' : Nomm → CGoalL CSet → List Nat → CMS (TreapMap mugF) (NextL CSet)}
    {X : GenRest → Noun → Noun → Prop} {Y : GenRest → GenRest → Prop} {n : Nomm} {goal : CGoalL CSet}
    {region : List Nat} {gs : GenSf (TreapMap mugF)} (he : R n goal region gs = R' n goal region gs)
    (h : CompRunAtXTS R ctx X Y n goal region gs) : CompRunAtXTS R' ctx X Y n goal region gs := by
  intro x mono sup hs hX
  obtain ⟨x', hy, hr⟩ := h x mono sup hs hX
  exact ⟨x', hy, by rw [hr, he]⟩

/-- **The `%7` link on `runLCS2`** (the proof of `comp_run_n7TS`). -/
theorem comp_run_n7TS2 {X : GenRest → Noun → Noun → Prop} {Y : GenRest → GenRest → Prop} (hYk : YOkS X Y)
    (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (msup : Option Nomm) (p q : Nomm) (goal : CGoalL CSet)
    (region : List Nat) (gs : GenSf (TreapMap mugF)) {Xq : GenRest → Noun → Noun → Prop}
    (hq : CompRunAtXTS (runLCS2 env snd (some p)) ctx Xq Y q goal region gs)
    (hXq : ∀ x mono sup, X x mono sup → Xq x mono (C (A 0) p.toNoun))
    (hp : ∀ nex gs1, runLCS2 env snd (some p) q goal region gs = some (nex, gs1) →
      CompRunAtXTS (runLCS2 env snd msup) ctx X Y p nex.goal region gs1) :
    CompRunAtXTS (runLCS2 env snd msup) ctx X Y (Nomm.n7 p q) goal region gs := by
  intro x mono sup hs hX
  obtain ⟨x1, hy1, h1⟩ := hq x mono (C (A 0) p.toNoun) hs (hXq x mono sup hX)
  simp only [crSubj, compCore] at h1
  simp only [Nomm.toNoun]
  rw [cr_disp_n7]
  cases e : runLCS2 (S := CSet) (Map := TreapMap mugF) env snd (some p) q goal region gs with
  | none =>
    rw [e] at h1
    refine ⟨x1, hy1, ?_⟩
    simp only [compCore]
    generalize comp.door = Dr at h1 ⊢
    nock_open crK7
    simp [nock_exec, crSubj, cr_bat_dol, h1, runLCS2, e, bind, StateT.bind]
  | some r =>
    obtain ⟨nex, gs1⟩ := r
    rw [e] at h1
    obtain ⟨x2, hy2, h2⟩ := hp nex gs1 e { x1 with soft := softMapNoun gs1.soft } mono sup rfl
      (hYk.softX _ (hYk.pres hX hy1))
    refine ⟨x2, hYk.trans (hYk.softY _ hy1) hy2, ?_⟩
    simp only [crSubj, compCore] at h2 h1
    simp only [compCore]
    generalize comp.door = Dr at h1 h2 ⊢
    nock_open crK7
    simp [nock_exec, crSubj, cr_bat_dol, h1, h2, runLCS2, e, bind, StateT.bind]

/-- **The chain on `runLCS2`**: `SoftChainOk` with, at each `%7`, the `GInv` of the goal the run
of `q` returns on `runLCS2` and `MedeAllAt` of the subject `p` at the soft map it leaves. -/
def SoftChainOk2 (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (cod ctx : Noun) (E : GenRest → Prop)
    (region : List Nat) : Option Nomm → Nomm → Prop
  | msup, Nomm.n2 (Nomm.n0 1) (Nomm.n1 f) (some (b, Option.none)) => SoftCallOk env cod ctx E msup f b
  | _, Nomm.n7 p q => SoftFree p = true ∧ SoftChainOk2 env snd cod ctx E region (some p) q ∧
      ∀ gs nex gs1, runLCS2 (S := CSet) (Map := TreapMap mugF) env snd (some p) q CGoalL.done region gs
        = some (nex, gs1) → GInv gs1.g nex.goal ∧ MedeAllAt gs1.soft p
  | _, _ => False

/-- **The corpus's soft members on the fixed model**: a `SoftChainOk2` nomm under `%done` at every
soft map, against `runLCS2 env snd msup`, as `comp_run_softChain`. -/
theorem comp_run_softChain2 (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (E : GenRest → Prop) (Y : GenRest → GenRest → Prop)
    (hYS : ∀ msup, YOkS (XN E msup) Y)
    (L : ∀ sm : TreapMap mugF SoftCall,
      LeafQ (fun x => x.soft = softMapNoun sm) env ctx (XN E) (fun a c => Y a c ∧ c.soft = a.soft))
    (region : List Nat) :
    ∀ (n : Nomm) (msup : Option Nomm), SoftChainOk2 env snd cod ctx E region msup n →
      ∀ gs, CompRunAtXTS (runLCS2 env snd msup) ctx (XN E msup) Y n CGoalL.done region gs
  | Nomm.n7 p q, msup, ⟨hp, hq, hres⟩, gs => by
    have IH := comp_run_softChain2 h7 hcode env snd E Y hYS L region q (some p) hq
    exact comp_run_n7TS2 (hYS msup) env snd msup p q CGoalL.done region gs (IH gs)
      (fun x mono sup hX => ⟨hX.1, hX.2.1, rfl⟩)
      (fun nex gs1 e => crxts_softFree2 h7 hcode env snd (XN E) Y gs1 (fun ms => yOkQ_of_S (hYS ms) _)
        (fun ms p' x mono sup hX => ⟨hX.1, hX.2.1, rfl⟩) (L gs1.soft) p hp (hres gs nex gs1 e).2 msup region
        nex.goal (hres gs nex gs1 e).1)
  | Nomm.n2 (Nomm.n0 1) (Nomm.n1 f) (some (b, Option.none)), msup, hok, gs => by
    have h1 := comp_run_softChain h7 hcode env snd E Y hYS L region
      (Nomm.n2 (Nomm.n0 1) (Nomm.n1 f) (some (b, Option.none))) msup hok gs
    exact crxts_congr (by rw [runLCS2_softTail_eq]) h1

end Compiler
end Formalization
