import lemmas.Compiler.PokeLinkEvalCases
import lemmas.Compiler.PokeLinkEvalHave
import lemmas.Compiler.PokeLinkEvalTwo
import lemmas.Compiler.PokeLinkTop5

/-!
# `EvalFinAt` (track P, README Gaps 23)

* `ef_loop_all`: the trap `nomm-loop` of `+eval-finalized` agrees with
  `efGo` on every nomm (induction on the nomm, one case lemma per case of
  its `?-`: `PokeLinkEvalBase.lean`, `PokeLinkEvalCases.lean`,
  `PokeLinkEvalHave.lean`, `PokeLinkEvalTwo.lean`).
* `ef_arm`: the arm `0x57de` of `ana` builds the gate.
* **`evalFinAt : EvalFinAt`**: the leaf of the SCC loop's link
  (`PokeLinkLoopRun.lean`) is a theorem.
* `loopLinkAt_good5E`: the SCC loop's link on a `PGood5` state from track
  Q's `SccsLeafAt` alone.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF SkaModel.PokeM

set_option linter.unusedSimpArgs false

/-- **The trap on every nomm.** -/
theorem ef_loop_all (b : Bell) (M : FinMap Bell Noun) : ∀ n, EfLoopAt b M n := by
  intro n
  induction n with
  | cons p q ihp ihq => exact ef_cons b M p q ihp ihq
  | n0 p => exact ef_0 b M p
  | n1 p => exact ef_1 b M p
  | n2 p q i ihp ihq => exact ef_2 b M p q i ihp ihq
  | n3 p ih => exact ef_3 b M p ih
  | n4 p _ => exact ef_4 b M p
  | n5 p q ihp ihq => exact ef_5 b M p q ihp ihq
  | n6 p q r _ ihq ihr => exact ef_6 b M p q r ihq ihr
  | n7 p q ihp ihq => exact ef_7 b M p q ihp ihq
  | n10 a v q ihv ihq => exact ef_10 b M a v q ihv ihq
  | n11s t q bd ih => exact ef_11s b M t q bd ih
  | n11d t h q bd ihh ihq => exact ef_11d b M t h q bd ihh ihq
  | n12 p q _ _ => exact ef_12 b M p q
  | mean p c q bd k ihp ihq => exact ef_mean b M p c q bd k ihp ihq

/-- The arm builds the gate `[efBat [bunt ana]]`. -/
theorem ef_arm : nock ana efArm = some (C efBat (C (C (C (C (A 1) (A 0)) (C (A 0) (A 0))) (A 0)) ana)) := by
  rw [efArm_eq]; simp [nock_exec]

set_option maxHeartbeats 1000000 in
/-- The battery of the gate on `[b code]`: `efGot`, then the trap. -/
theorem ef_bat (M : FinMap Bell Noun) (b : Bell) (n : Nomm) (fb : Noun) (rr : Sock × Bool × Bool)
    (hb : M.get b = some (C n.toNoun fb)) (he : efGo (accFt M) b.less n = some rr) :
    nock (C efBat (C (C (TKey.enc b) (M.toNoun id)) ana)) efBat = some (flagNoun rr.2) := by
  have hgc : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
    ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
  have hget : getF mugF (TKey.enc b) (M.toNoun id) = some (C (A 0) (C n.toNoun fb)) := by
    rw [FinMap.getF_toNoun, hb]; rfl
  have hgot := got_gate layer2 hgc (TKey.enc b) _ _ hget
  have hl := ef_loop_all b M n b.less rr he
  unfold efK at hl
  obtain ⟨s, p, t⟩ := rr
  simp only [efRes] at hl
  have hk : TKey.enc b = C b.less.toNoun b.fol := rfl
  rw [hk] at hgot hl ⊢
  conv => lhs; arg 2; rw [efBat_eq]
  rw [efGot_eq]
  simp [nock_exec, ana_l2e, by.arm_at, by_arm, by.got.arm_at, got_arm, hgot, hl]

/-- **`EvalFinAt`**: `+eval-finalized` in the pill computes `efGo`'s flags. -/
theorem evalFinAt : EvalFinAt := by
  intro M b n fb rr G0 Y hb he hS
  have hB := ef_bat M b n fb rr hb he
  unfold lpEf
  simp [nock_exec, hS, ana_efArm, ef_arm, hB]

/-- **The SCC loop's leaf on a `PGood5` state from `SccsLeafAt` alone**
(`loopLinkAt_good5` with `evalFinAt`). -/
theorem loopLinkAt_good5E (root : Ident) (r1 r2 r3 r4 jRest callsN varsN seekN hotN : Noun)
    (gr : Callgraph FinMap × Noun)
    (r : Callgraph FinMap × FinMap Bell (FDatum FinMap) × Memo FinMap × FDatum FinMap × Noun)
    {Cls : Straight (TreapMap mugF) → Prop} {st : PSt} (hg : PGood5 Cls st) {E : BEnv FinMap} {n : Nat}
    {bg : FinMap Bell (VarEntry FinMap) × FinMap Bell (FinMap Bell Unit)} (vr : Noun)
    (hbg : bakeGraph E n = some bg) (hEv : E.vars = st.long.vars)
    (hN : ∀ b e, FinMap.get (addCode st.long.code (newCode st.long.code bg.1)) b = some e → NoAx0 e.nomm)
    (hS : SccsLeafAt root r1 r2 r3 r4 jRest (codeNoun flagsOf st.long.code) callsN varsN seekN hotN gr r
      (newCode st.long.code bg.1) bg.1 vr) :
    LoopLinkAt root r1 r2 r3 r4 jRest (codeNoun flagsOf st.long.code) callsN varsN seekN hotN gr r
      flagsOf st.long.code (newCode st.long.code bg.1) bg.1 vr :=
  loopLinkAt_good5 evalFinAt root r1 r2 r3 r4 jRest callsN varsN seekN hotN gr r hg vr hbg hEv hN hS

end Compiler
end Formalization
