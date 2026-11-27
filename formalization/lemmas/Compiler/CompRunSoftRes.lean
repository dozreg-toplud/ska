import lemmas.Compiler.CompRunSoftChain

/-!
# The result invariant of the corpus's soft chains (README Gaps 19 (g), the `GInv` field)

The field of `SoftChainOk` at each `%7`, `GInv gs1.g nex.goal` for the run of the rest of the chain
under `%done`, is asked at EVERY soft state `gs`, also at states whose `drop` is set, where every
result lemma (`ResForR`, `GRes`) is silent: they all start from `GInv g goal`, whose `%done` case is
`drop` `|`.  `comp_run_softChain` is used only from such states (`memDoneCall_ofS`, at `gen0`; the
`%7` case passes its own `gs`), so the field is restated with the premise `GInv gs.g %done`.
Here, with that premise:

* **`res_softFree`**: the result invariant `ResForR` of every `SoftFree` nomm (cons, `%0`, `%1`,
  `%7`, `%10`), by the cases' `res_*RN`;
* `SoftCallRes`: the soft tail call's own result invariant (not proved: `+soft-bond`'s bond and
  `+emit`'s label bounds), `SoftChainG` (the chain's shape with `SoftCallRes` at the call in place
  of the `GInv` fields);
* **`softChainG_ginv`**: the restated field for the whole chain, from `SoftCallRes` alone
  (`runLCS_lift` and `res_softFree` at each soft-free part).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **What a soft-free nomm returns** (`GRes` from a goal with `GInv`), at `mono` `|`. -/
theorem res_softFree (env : CallEnv) :
    ∀ (n : Nomm), SoftFree n = true → ∀ (msup : Option Nomm) (region : List Nat),
      ResForR (runLCM env false msup) n region
  | Nomm.cons p q, h, msup, region => by
    simp only [SoftFree, Bool.and_eq_true] at h
    exact res_consRN (res_softFree env p h.1 msup region) (res_softFree env q h.2 msup region)
  | Nomm.n0 ax, _, msup, region => resR_of_resN rfl (res_n0 env msup ax region)
  | Nomm.n1 k, _, msup, region => resR_of_resN rfl (res_n1 env msup k region)
  | Nomm.n7 p q, h, msup, region => by
    simp only [SoftFree, Bool.and_eq_true] at h
    exact res_n7RN (res_softFree env q h.2 (some p) region) (res_softFree env p h.1 msup region)
  | Nomm.n10 a v q, h, msup, region => by
    simp only [SoftFree, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact res_n10RN h.1.1 (res_softFree env v h.1.2 msup region) (res_softFree env q h.2 msup region)
  | Nomm.n2 _ _ _, h, _, _ => by simp [SoftFree] at h
  | Nomm.n3 _, h, _, _ => by simp [SoftFree] at h
  | Nomm.n4 _, h, _, _ => by simp [SoftFree] at h
  | Nomm.n5 _ _, h, _, _ => by simp [SoftFree] at h
  | Nomm.n6 _ _ _, h, _, _ => by simp [SoftFree] at h
  | Nomm.n11s _ _ _, h, _, _ => by simp [SoftFree] at h
  | Nomm.n11d _ _ _ _, h, _, _ => by simp [SoftFree] at h
  | Nomm.n12 _ _, h, _, _ => by simp [SoftFree] at h
  | Nomm.mean _ _ _ _ _, h, _, _ => by simp [SoftFree] at h

/-- **The soft tail call's result invariant** (the obligation left): from a state with `GInv` at
`%done`, the run of `[2 [0 1] [1 f] [~ b ~]]` returns a goal with `GInv`. -/
def SoftCallRes (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (region : List Nat) (msup : Option Nomm) (f : Noun)
    (b : Bell) : Prop :=
  ∀ (gs : GenSf (TreapMap mugF)) (nex : NextL CSet) (gs1 : GenSf (TreapMap mugF)), GInv gs.g CGoalL.done →
    runLCS env snd msup (Nomm.n2 (Nomm.n0 1) (Nomm.n1 f) (some (b, Option.none))) CGoalL.done region gs
      = some (nex, gs1) → GInv gs1.g nex.goal

/-- **The chain's shape with the call's result invariant** (`SoftChainOk` without its `GInv`
fields, `SoftCallRes` at the call). -/
def SoftChainG (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (cod ctx : Noun) (E : GenRest → Prop)
    (region : List Nat) : Option Nomm → Nomm → Prop
  | msup, Nomm.n2 (Nomm.n0 1) (Nomm.n1 f) (some (b, Option.none)) =>
      SoftCallOk env cod ctx E msup f b ∧ SoftCallRes env snd region msup f b
  | _, Nomm.n7 p q => SoftFree p = true ∧ SoftChainG env snd cod ctx E region (some p) q
  | _, _ => False

/-- **The `GInv` field, restated with its premise, for the whole chain**: from a state with `GInv`
at `%done`, the run of a `SoftChainG` nomm returns a goal with `GInv`. -/
theorem softChainG_ginv (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (cod ctx : Noun) (E : GenRest → Prop)
    (region : List Nat) :
    ∀ (n : Nomm) (msup : Option Nomm), SoftChainG env snd cod ctx E region msup n →
      ∀ (gs : GenSf (TreapMap mugF)) (nex : NextL CSet) (gs1 : GenSf (TreapMap mugF)), GInv gs.g CGoalL.done →
        runLCS env snd msup n CGoalL.done region gs = some (nex, gs1) → GInv gs1.g nex.goal
  | Nomm.n7 p q, msup, ⟨hp, hq⟩, gs, nex, gs1, hi, h => by
    simp only [runLCS] at h
    obtain ⟨⟨nex1, gs'⟩, e1, h⟩ := Option.bind_eq_some_iff.1 h
    have hi' := softChainG_ginv env snd cod ctx E region q (some p) hq gs nex1 gs' hi e1
    rw [runLCS_lift env snd p hp msup] at h
    simp only [liftS] at h
    obtain ⟨⟨a, g⟩, e2, e3⟩ := Option.map_eq_some_iff.1 h
    cases e3
    exact (res_softFree env p hp msup region nex1.goal gs'.g g a hi' e2).2.2.1
  | Nomm.n2 (Nomm.n0 1) (Nomm.n1 f) (some (b, Option.none)), msup, ⟨_, hres⟩, gs, nex, gs1, hi, h =>
    hres gs nex gs1 hi h

end Compiler
end Formalization
