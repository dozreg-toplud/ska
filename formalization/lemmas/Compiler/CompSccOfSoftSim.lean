import lemmas.Compiler.CompSofOff
import lemmas.Compiler.CompSccOfSoft

/-!
# The field `sim` of `MemRunS` discharged (README Gaps 19 (g), `sim`)

`MemRunS`'s second case (a `DirOk` member of a loop with soft calls) asked as a field that the soft
model equals `runLC` on the member from `gen0` (`sim`), since `runLCS_eq` asks `sof` false at every
call of every nomm.  `runLCS_simD` (`CompSofOff.lean`, generated) asks it only at the member's own
calls (`SofOff`), and `DirCallsTN` records it per call (`CallOkTN`):

* **`sofOff_of_dirTN`**: `DirCallsTN` gives `SofOff`;
* **`memRunS_dir`**: `DirOk` and `DirCallsTN` at `EMD` give `MemRunS` (no `sim` asked).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun}

/-- **`DirCallsTN` gives `SofOff`**: each call's `CallOkTN` holds `sof` false at the callee's need. -/
theorem sofOff_of_dirTN {env : CallEnv} {cod : Noun} {E : GenRest → Prop} {Y : GenRest → GenRest → Prop} :
    ∀ (n : Nomm) (ms : Option Nomm), DirCallsTN env cod ctx E Y ms n → SofOff env ms n
  | Nomm.cons p q, ms, hd => by
    simp only [DirCallsTN] at hd; simp only [SofOff]
    exact ⟨sofOff_of_dirTN p ms hd.1, sofOff_of_dirTN q ms hd.2⟩
  | Nomm.n0 _, _, _ => by simp only [SofOff]
  | Nomm.n1 _, _, _ => by simp only [SofOff]
  | Nomm.n2 p q Option.none, ms, hd => by
    simp only [DirCallsTN] at hd; simp only [SofOff]
    exact ⟨sofOff_of_dirTN p ms hd.1, sofOff_of_dirTN q ms hd.2⟩
  | Nomm.n2 p q (some (b, k)), ms, hd => by
    simp only [DirCallsTN] at hd; simp only [SofOff]
    refine ⟨fun nb' hnb' => ?_, sofOff_of_dirTN p ms hd.2.1, sofOff_of_dirTN q ms hd.2.2⟩
    obtain ⟨nb, hnb, hsf, -⟩ := hd.1.2.2.2
    rw [hnb] at hnb'
    cases hnb'
    exact hsf
  | Nomm.n3 p, ms, hd => by
    simp only [DirCallsTN] at hd; simp only [SofOff]
    exact sofOff_of_dirTN p ms hd
  | Nomm.n4 p, ms, hd => by
    simp only [DirCallsTN] at hd; simp only [SofOff]
    exact sofOff_of_dirTN p ms hd
  | Nomm.n5 p q, ms, hd => by
    simp only [DirCallsTN] at hd; simp only [SofOff]
    exact ⟨sofOff_of_dirTN p ms hd.1, sofOff_of_dirTN q ms hd.2⟩
  | Nomm.n6 p q r, ms, hd => by
    simp only [DirCallsTN] at hd; simp only [SofOff]
    exact ⟨sofOff_of_dirTN p ms hd.1, sofOff_of_dirTN q ms hd.2.1, sofOff_of_dirTN r ms hd.2.2⟩
  | Nomm.n7 p q, ms, hd => by
    simp only [DirCallsTN] at hd; simp only [SofOff]
    exact ⟨sofOff_of_dirTN p ms hd.1, sofOff_of_dirTN q (some p) hd.2⟩
  | Nomm.n10 _ v q, ms, hd => by
    simp only [DirCallsTN] at hd; simp only [SofOff]
    exact ⟨sofOff_of_dirTN v ms hd.1, sofOff_of_dirTN q ms hd.2⟩
  | Nomm.n11s _ _ _, _, _ => by simp only [SofOff]
  | Nomm.n11d _ _ _ _, _, _ => by simp only [SofOff]
  | Nomm.n12 _ _, _, _ => by simp only [SofOff]
  | Nomm.mean _ _ _ _ _, _, _ => by simp only [SofOff]

/-- **`MemRunS` of a `DirOk` member without the field `sim`**: the soft model equals `runLC` on
it from `gen0` by `runLCS_eqD`, `sof` false at its calls by `sofOff_of_dirTN`. -/
theorem memRunS_dir {r : RealCfg} {snd : Nomm → NeedOrd → Bool} {order : List Noun} {kids : Noun → List Noun}
    {st : St Noun NeedOrd} {env : CallEnv} {SC0 MO0 : Noun} {inl : Noun → Option Nomm} {P Pf : Noun → Prop}
    {S : Noun} {xs : GenRest} {CODE : Noun} {nm : Nomm} (hn : DirOk nm = true)
    (hd : DirCallsTN (envDoneS r snd order kids st) CODE ctx (EMD env SC0 MO0 inl P Pf S st xs)
      (ExtE (EMD env SC0 MO0 inl P Pf S st xs)) Option.none nm) :
    MemRunS r snd order kids st env SC0 MO0 inl P Pf S xs CODE ctx nm :=
  Or.inr ⟨hn, hd, runLCS_eqD (envDoneS r snd order kids st) snd nm Option.none (sofOff_of_dirTN nm Option.none hd)
    CGoalL.done [] gen0⟩

end Compiler
end Formalization
