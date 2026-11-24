import lemmas.Compiler.CompSccGate
import lemmas.Compiler.CompInlined
import lemmas.Compiler.CompShapeCol
import lemmas.Hoon.IntIn
import lemmas.Hoon.UniBy

/-!
# `+compile-scc-in` on an SCC of one bell, with its calls linked

`cu_gate_scc_one` of `CompSccGate.lean` carries hypotheses on the Nock of
arms that were not linked.  Here they are discharged:

* `hinl` (`+inlined`): `inl_gate` of `CompInlined.lean`, under `InlOK`, a
  statement on `inl.cache` and `code.long-ska`;
* `hsc` (`+shape-collapse`): `hsc_of_sure` of `CompShapeCol.lean`, with the
  shape `ord` equal to `sur`, the product of `+sure-of`;
* `hkids`, `hju`: for a bell with no callee in `calls.long-ska` (`NoCalls`),
  `kids` is `[[b ~] ~ ~]` (`csi_kids_nocalls`: the `+rep:in` over `[b ~ ~]`
  with `+gut:by` and `+int:in` of `~`) and `~(has ju kids) b b` is `|`
  (`ju_has_kids`);
* `huni` (`+uni:by` of `nary` and `[[b st] ~ ~]`): on a map `nary` it is
  `putF` (`uni_by_one`);
* `hsur`: on the fragment the run looks at no axis `0` (`cra_run_lok`), so
  `+sure-of` succeeds (`sureOf_some`); its product is named `sccSur`;
* `hst` (`finishLF … = some st`): the theorems are stated as a `bind` over
  `finishLF`, the gate crashing when it is `none` (`csi_final_one_none`,
  `cu_gate_none`);
* `hwas`, `hw`: they follow from `hput` (`getF_of_putF`).

What stays on the model side: the run succeeds (`hrunL`), with `args.then`
empty (`hargs`), `+need-ord-alloc-regs` of `sccSur` succeeds (`hnoar`), and
nothing is baked (`hb`).  On the state nouns: `b` is not in `nary.cache`
(`hnary`) which is a map (`hnmap`), `calls.long-ska` has no callee of `b`
(`hcalls`), `InlOK` for `inl.cache`, and the put of `sur` into
`sure.cache` succeeds (`hput`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## `kids` and `done` for a bell with no callee -/

/-- `calls.long-ska` has no callee of `b`: no entry, or the empty set. -/
def NoCalls (B CALLS : Noun) : Prop :=
  getF mugF B CALLS = some (A 0) ∨ getF mugF B CALLS = some (C (A 0) (A 0))

/-- The jug `kids` of an SCC of one bell `b` with no callee: `[[b ~] ~ ~]`. -/
def kidsOne (B : Noun) : Noun := C (C B (A 0)) (C (A 0) (A 0))

/-- **`kids` of `[b ~ ~]` when `b` has no callee**: the `+rep:in` over the
one bell puts at `b` the `+int:in` of `~` (the `+gut:by` of `calls`) and
`scc`, which is `~`. -/
theorem csi_kids_nocalls (B CODE JETS CALLS JH CACHE : Noun) (hc : NoCalls B CALLS) :
    nock (C (A 0) (C csiBody (C (csiSam (setOne B) (C CODE (C JETS CALLS)) JH CACHE) compK))) csiKids
      = some (kidsOne B) := by
  have hL := compK_layer2
  have hgut : nock (C by.gut.battery (C (C B (A 0)) (C by.battery (C CALLS layer2)))) by.gut.battery
      = some (A 0) := by
    rcases hc with h | h
    · have := gut_gate (mug := mugF) layer2 ⟨fall.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ B (A 0) CALLS
        (A 0) h (Or.inl rfl)
      simpa using this
    · have := gut_gate (mug := mugF) layer2 ⟨fall.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ B (A 0) CALLS
        (C (A 0) (A 0)) h (Or.inr ⟨_, rfl⟩)
      simpa using this
  have hput := put_gate (mug := mugF) layer2 gorIn_morIn_layer2 B (A 0) (A 0) (kidsOne B) rfl
  unfold csiKids csiSam setOne
  generalize compK = KC at hL
  simp [nock_exec, hL, in.arm_at, in_arm, in.rep.arm_at, rep_arm, rep_gate_one, by.arm_at, by_arm,
    by.put.arm_at, put_arm, hput, in.int.arm_at, int_in_arm, int_in_nil, by.gut.arm_at, gut_arm, hgut]

/-- `~(has ju kids) b b` is `|` on `kidsOne b`. -/
theorem ju_has_kids (B : Noun) : juHasF mugF B B (kidsOne B) = some false := by
  simp [juHasF, juGetF, kidsOne, getF, unUnit, hasInF]

/-! ## The crashes -/

/-- **`final` crashes when `member` does.** -/
theorem csi_final_one_none (b ML CACHE DN KIDS LONG JH CACHE0 : Noun)
    (hm : nock (C memBody (C (memSam b (A 0x656e6f64) (A 1) ML (A 0) CACHE) (csiCtx DN KIDS (setOne b) LONG JH CACHE0)))
      memBody = none) :
    nock (csiFC (A 1) ML CACHE DN KIDS (setOne b) LONG JH CACHE0) fBody = none := by
  have hL := compK_layer2
  have hbb := bell_bunt
  have hr := roll_gate_one layer2 fGate bellBunt (C ML CACHE)
    (csiFC (A 1) ML CACHE DN KIDS (setOne b) LONG JH CACHE0) b
  simp only [listN, appendN] at hr
  have hmc : nock (C fGate (C (C b (C ML CACHE)) (csiFC (A 1) ML CACHE DN KIDS (setOne b) LONG JH CACHE0))) fGate
      = none := by
    unfold fGate
    unfold csiFC csiSM memSam at *
    generalize memBody = MB at hm ⊢
    simp [nock_exec, hm]
  conv => { lhs; arg 2; unfold fBody }
  unfold csiFC csiSM csiCtx setOne memCtx at *
  generalize compK = KC at hL hbb hr hmc ⊢
  unfold bellBuntF at hbb
  simp only [nock_exec] at hbb
  simp [nock_exec, hL, fRoll, roll.arm_at, roll_arm, fTap, in.arm_at, in_arm, in.tap.arm_at, tap_arm, tap_loop, tapF,
    fRBunt, hbb, hr, hmc]

/-- **The gate of `+compile-unary` crashes when `+compile-scc-in` does**:
the trap crashes at its first call, and `road-pure` returns only what the
trap returns (`cu_rp_iff`). -/
theorem cu_gate_none (SAM : Noun) (hcsi : nock (cuTC SAM) cuCsi = none) :
    nock (C cuGB (C SAM compK)) cuGB = none := by
  rw [cu_gate_rp]
  have htr : nock (cuTC SAM) cuTrap = none := by
    conv => { lhs; arg 2; unfold cuTrap }
    rw [nock_op7, nock_op0]
    simp only [slot?_one, Option.bind_some]
    rw [nock_op8, nock_op7, nock_op0]
    simp only [slot?_one, Option.bind_some, hcsi, Option.bind_none]
  have ht : nock (cuTC SAM) rpK = none := by
    unfold rpK
    rw [nock_op9, nock_op0]
    simp only [slot?_one, Option.bind_some]
    unfold cuTC at htr ⊢
    simp only [nock_exec, htr]
  cases e : nock (C rpBat (C (cuTC SAM) rpCtx)) rpBat with
  | none => rfl
  | some y => rw [(cu_rp_iff _ y).1 e] at ht; cases ht

/-! ## The model side -/

/-- `+get:by` succeeds where `+put:by` does, with `~` or `[~ u]`. -/
theorem getF_of_putF (b c : Noun) : ∀ (a : Noun) {out : Noun}, putF mugF b c a = some out →
    ∃ w, getF mugF b a = some w ∧ (w = A 0 ∨ ∃ u, w = C (A 0) u)
  | Noun.atom 0, _, _ => ⟨A 0, rfl, Or.inl rfl⟩
  | Noun.atom (n + 1), _, h => by simp [putF] at h
  | Noun.cell (Noun.atom _) _, _, h => by simp [putF] at h
  | Noun.cell (Noun.cell _ _) (Noun.atom _), _, h => by simp [putF] at h
  | Noun.cell (Noun.cell p q) (Noun.cell l r), out, h => by
    by_cases e : b = p
    · exact ⟨C (A 0) q, by simp [getF, e], Or.inr ⟨q, rfl⟩⟩
    · by_cases g : gorF mugF b p = true
      · cases hl : putF mugF b c l with
        | none => simp [putF, e, g, hl] at h
        | some o =>
          obtain ⟨w, hw, hw'⟩ := getF_of_putF b c l hl
          exact ⟨w, by simp [getF, e, g, hw], hw'⟩
      · cases hr : putF mugF b c r with
        | none => simp [putF, e, g, hr] at h
        | some o =>
          obtain ⟨w, hw, hw'⟩ := getF_of_putF b c r hr
          exact ⟨w, by simp [getF, e, g, hw], hw'⟩

/-- `+sure-of` succeeds when no look is at axis `0`. -/
theorem sureOf_some (less : Cape) (lok : CSet) (h0 : ∀ y ∈ HoonSet.toList lok, y ≠ 0) (ned : NeedOrd) :
    ∃ r, sureOf ned lok less = some r := by
  unfold sureOf
  generalize HoonSet.toList lok = L at h0
  induction L generalizing ned with
  | nil => exact ⟨ned, rfl⟩
  | cons y ys ih =>
    have hy : y ≠ 0 := h0 y (by simp)
    have hs : ∃ n', sureOfStep less ned y = some n' := by
      unfold sureOfStep axeInLessCape
      by_cases e : y = 1
      · exact ⟨ned, by simp [e]⟩
      · exact ⟨if axeInCape y less = true then ned else sureLook y ned, by simp [e, hy]⟩
    obtain ⟨n', hn'⟩ := hs
    obtain ⟨r, hr⟩ := ih n' (fun z hz => h0 z (by simp [hz]))
    exact ⟨r, by simp [List.foldlM, hn', hr]⟩

/-- **`sur` of the final pass**: `+sure-of` of the sure part of the run's
`laz`.  It is also the shape that `+shape-collapse` gives (`hsc_of_sure`). -/
noncomputable def sccSur (nex : NextL CSet) (cape : Cape) : NeedOrd :=
  (sureOf (needToOrd nex.laz.sure.ned) nex.laz.sure.lok cape).getD NeedOrd.none

/-- On the fragment, the run's `laz` is `[s ~ ~]` with no look at `0`, and
`+sure-of` of it is `sccSur`. -/
theorem scc_sur_frag (nm : Nomm) (hpu : nm.pure = true) (h6 : noSix nm = true) (nex : NextL CSet)
    (g1 : Gen (TreapMap mugF))
    (hrunL : runL nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1)) (cape : Cape) :
    nex.laz = Lazy.ofSure nex.laz.sure ∧
      sureOf (needToOrd nex.laz.sure.ned) nex.laz.sure.lok cape = some (sccSur nex cape) := by
  rw [show (CGoalL.done : CGoalL CSet) = CGoal.toL CGoal.done from rfl, runL_toL nm hpu h6] at hrunL
  cases e : run (S := CSet) (Map := TreapMap mugF) nm CGoal.done gen0 with
  | none => simp [e, Functor.map, StateT.map] at hrunL
  | some q =>
    obtain ⟨nex0, g0⟩ := q
    simp [e, Functor.map, StateT.map] at hrunL
    obtain ⟨rfl, rfl⟩ := hrunL
    have hl := cra_run_lok nm hpu h6 CGoal.done gen0 g0 nex0 e trivial
    obtain ⟨r, hr⟩ := sureOf_some cape nex0.laz.lok hl (needToOrd nex0.laz.ned)
    refine ⟨rfl, ?_⟩
    simp only [Next.toL, Lazy.sure_mk, Lazy.ofSure, sccSur] at hr ⊢
    rw [hr]
    rfl

/-! ## The gate on an SCC of one bell -/

/-- **`+compile-scc-in` on an SCC of one bell `b` with no callee, not in
`nary.cache`, whose nomm is pure, `%6`-free and `tenOk`**: the gate
returns `[[[b st] ~ ~] cache']` with `st` the straight of `finishLF nm sur
cape` (`sur` the shape `sccSur` of the run) and crashes when that is
`none`; `cache'` has `nary` with `st` put at `b` (`putF`, the `+uni:by`),
`inl` as `InlOK` says, and `sure` with `sur` put at `b` (`SURE'`).  The
hypotheses on the model: the run succeeds with no argument in `args.then`,
`+need-ord-alloc-regs` of `sur` succeeds, nothing is baked. -/
theorem csi_gate_scc_one_m (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hcalls : NoCalls (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (hpu : nm.pure = true) (h6 : noSix nm = true) (ht : tenOk nm = true)
    (nex : NextL CSet) (g1 : Gen (TreapMap mugF))
    (hrunL : runL nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
    (hargs : nex.th.args = []) (nedF : Need) (g2 : Gen (TreapMap mugF))
    (hnoar : needOrdAllocRegs (sccSur nex cape) g1 = some (nedF, g2))
    (hb : NoBake nedF (Sock.mk cape DATA))
    (SURE' : Noun) (hput : putF mugF (C (C cape.toNoun DATA) FOL) (sccSur nex cape).toNoun SURE = some SURE') :
    nock (C csiBody (C (csiSam (setOne (C (C cape.toNoun DATA) FOL)) (C CODE (C JETS CALLS)) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) csiBody
      = (finishLF (S := CSet) (Map := TreapMap mugF) nm (sccSur nex cape) cape (fun n => (n, []))).bind fun st =>
          (putF mugF (C (C cape.toNoun DATA) FOL) st.toNoun NARY).map fun NARYU =>
            C (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))) (cacheN NARYU MONO SCCS INL' SURE') := by
  have hcache : cacheN NARY MONO SCCS INL SURE = C NARY (C MONO (C SCCS (C INL SURE))) := rfl
  rw [hcache, csi_to_final _ _ _ _ _ _ hnary (csi_kids_nocalls _ CODE JETS CALLS JH _ hcalls) (ju_has_kids _)]
  obtain ⟨hlz, hsur⟩ := scc_sur_frag nm hpu h6 nex g1 hrunL cape
  have hsc := hsc_of_sure nex nex.laz.sure hlz cape (sccSur nex cape) hsur
  have hi := inl_gate (C (C cape.toNoun DATA) FOL) CODE (C JETS CALLS) JH NARY MONO SCCS INL SURE INL' nm hpu hinl
  obtain ⟨WAS, hwas, hw⟩ := getF_of_putF _ _ SURE hput
  have hput' : putF mugF (C (C cape.toNoun DATA) FOL) (memSurKN false WAS (sccSur nex cape).toNoun) SURE
      = some SURE' := by simpa [memSurKN] using hput
  have hm := mem_gate cape DATA FOL false (C NARY (C MONO (C SCCS (C INL SURE)))) (A 0)
    (kidsOne (C (C cape.toNoun DATA) FOL)) (A 0) csiBody (setOne (C (C cape.toNoun DATA) FOL)) CODE (C JETS CALLS) JH
    (C NARY (C MONO (C SCCS (C INL SURE)))) nm NARY MONO SCCS INL' SURE hi hpu h6 ht nex g1 hrunL nex.laz.sure hlz
    (sccSur nex cape) hsc hargs nedF g2 hnoar hb (sccSur nex cape) hsur WAS SURE' hwas hw hput'
  cases e : finishLF (S := CSet) (Map := TreapMap mugF) nm (sccSur nex cape) cape (fun n => (n, [])) with
  | none =>
    rw [e, Option.map_none] at hm
    exact csi_final_one_none _ _ _ _ _ _ _ _ hm
  | some st =>
    rw [e, Option.map_some] at hm
    obtain ⟨NARYU, hp, -, -⟩ := putF_spec mugF NARY (C (C cape.toNoun DATA) FOL) st.toNoun hnmap
    have hu := uni_by_one (mug := mugF) layer2 gorIn_morIn_layer2 NARY (C (C cape.toNoun DATA) FOL) st.toNoun hnmap
    rw [hp] at hu
    rw [csi_final_one (hm := hm) (huni := hu)]
    simp [hp, cacheN]

/-- **`cu_gate_scc_one` with the calls linked**: the gate of
`+compile-unary` on `[func [b ~ ~] long-ska jets-hot cache]`, under the
hypotheses of `csi_gate_scc_one_m`, returns `finishLU` of the nomm `n` of
`func` with the n-ary map `[[b st] ~ ~]` and the cache of
`csi_gate_scc_one_m`, and crashes when `finishLF` is `none`. -/
theorem cu_gate_scc_one_m (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hcalls : NoCalls (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (hpu : nm.pure = true) (h6 : noSix nm = true) (ht : tenOk nm = true)
    (nex : NextL CSet) (g1 : Gen (TreapMap mugF))
    (hrunL : runL nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
    (hargs : nex.th.args = []) (nedF : Need) (g2 : Gen (TreapMap mugF))
    (hnoar : needOrdAllocRegs (sccSur nex cape) g1 = some (nedF, g2))
    (hb : NoBake nedF (Sock.mk cape DATA))
    (SURE' : Noun) (hput : putF mugF (C (C cape.toNoun DATA) FOL) (sccSur nex cape).toNoun SURE = some SURE')
    (FUNC V : Noun) (n : Nomm) (hpu' : n.pure = true) (h6' : noSix n = true) (ht' : tenOk n = true)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (C cuGB (C (cuSam FUNC (setOne (C (C cape.toNoun DATA) FOL)) CODE (C JETS CALLS) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) cuGB
      = (finishLF (S := CSet) (Map := TreapMap mugF) nm (sccSur nex cape) cape (fun n => (n, []))).bind fun st =>
          (putF mugF (C (C cape.toNoun DATA) FOL) st.toNoun NARY).bind fun NARYU =>
            (finishLU (S := CSet) (Map := TreapMap mugF) n).map fun st' =>
              C (C st'.toNoun (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))))
                (cacheN NARYU MONO SCCS INL' SURE') := by
  have hcsi := csi_gate_scc_one_m cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hcalls nm INL'
    hinl hpu h6 ht nex g1 hrunL hargs nedF g2 hnoar hb SURE' hput
  rw [← cu_csi_eq FUNC] at hcsi
  cases e : finishLF (S := CSet) (Map := TreapMap mugF) nm (sccSur nex cape) cape (fun n => (n, [])) with
  | none =>
    rw [e] at hcsi
    exact cu_gate_none _ hcsi
  | some st =>
    obtain ⟨NARYU, hp, -, -⟩ := putF_spec mugF NARY (C (C cape.toNoun DATA) FOL) st.toNoun hnmap
    rw [e] at hcsi
    simp only [Option.bind_some, hp, Option.map_some] at hcsi ⊢
    exact cu_gate FUNC _ CODE (C JETS CALLS) JH _ _ _ V n hpu' h6' ht' hcsi hgot hv

end Compiler
end Formalization
