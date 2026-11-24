import lemmas.Compiler.CompRunCall
import lemmas.Compiler.CompNoNN

/-!
# The facts of the final pass on the fragment with indirect calls

`cu_gate_scc_one_f` (`CompSccOne.lean`) takes a pure nomm because of the
run link (`comp_run_entry`) and of five facts of the run that its proofs
derive from the fragment: `cond` stays empty (`mem_cond_frag`), the `laz`
of the result is fork-free (`mem_laz_frag`), the result jumps with no
argument (`args_frag`), `+sure-of` of the result succeeds (`scc_sur_frag`)
and `+need-ord-alloc-regs` of its shape succeeds (`noar_frag`).  Here they
are proved of `runLC env ~` (the model's run with calls, as `finishLFC` and
`finishLUC` run it) on every nomm of `indOk`:

* `crx_run`: the facts a run of the fragment keeps besides `CrOut`: `cond`
  unchanged, no argument when the goal passes none, the invariant `NN` of
  `CompNoNN.lean` of the result's need when the goal's has it.  The case
  `%2` adds `+kerf` (`kerf_ofSure`: `cond` unchanged), the call block and
  the `+copy` of the two runs (`kc_copy`, `crx_copy_args`, `nn_copy`);
* `mem_cond_frag_c`, `mem_laz_frag_c`, `args_frag_c`, `scc_sur_frag_c`,
  `noar_frag_c`: the five facts for the run from `gen0` with `[%done ~]`.

The run link at that entry is `comp_run_entry_c`.  And `+inlined`: on a
nomm with indirect calls and no direct call, hint or `%12` (`indPure`,
which every nomm of `indOk` meets, `indPure_of_indOk`) its walk is the
identity (`inl_trap_ind`: the case `[%2 p q ~]` rebuilds the call from its
walked parts), so `inl_gate_ind` is `inl_gate` there.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- What a run of the fragment keeps besides `CrOut`. -/
def CrX (g : Gen (TreapMap mugF)) (gl : CGoal CSet) (g' : Gen (TreapMap mugF)) (n : Next CSet) : Prop :=
  g'.cond = g.cond ∧ (ArgsNil gl → n.th.args = []) ∧ (NNg gl → NN n.laz.ned)

theorem crx_pure {env : CallEnv} {msup : Option Nomm} {region : List Nat} {n : Nomm}
    (hpu : n.pure = true) (h6 : noSix n = true) {gl : CGoal CSet} {g g' : Gen (TreapMap mugF)} {nex : NextL CSet}
    (e : runLC env msup n (CGoal.toL gl) region g = some (nex, g')) : ∃ m, nex = Next.toL m ∧ CrX g gl g' m := by
  rw [runLC_eq env n (Nomm.noCall_of_pure n hpu), runL_toL n hpu h6, map_apply] at e
  obtain ⟨m, e1, rfl⟩ := crf_map_some e
  exact ⟨m, rfl, (kc_run n gl).keep g m g' e1, fun ha => crx_run_args n hpu h6 gl g g' m e1 ha,
    fun hn => nn_run n hpu h6 gl g g' m e1 hn⟩

/-- A run for a fresh register's goal `[%next (lazy-from-reg r) [~ o]]`. -/
theorem crx_tail {g g1 g' : Gen (TreapMap mugF)} {gl : CGoal CSet} {r o : Nat} {m : Next CSet}
    (h : CrX g1 (CGoal.next (lazyReg r) (jmp0 o)) g' m) (hc : g1.cond = g.cond) : CrX g gl g' m :=
  ⟨h.1.trans hc, fun _ => h.2.1 rfl, fun _ => h.2.2 trivial⟩

theorem crx_emit {b : Blob} {g g' : Gen (TreapMap mugF)} {o : Nat} (h : emit b g = some (o, g')) :
    g'.cond = g.cond := (KC.emit' b).keep g o g' h

/-- **The other facts of a run of the fragment**: `cond` unchanged, no
argument from a goal that passes none, `NN` of the result from a goal whose
need has it. -/
theorem crx_run (env : CallEnv) : ∀ (n : Nomm), indOk n = true → ∀ (msup : Option Nomm) (region : List Nat)
    (gl : CGoal CSet) (g g' : Gen (TreapMap mugF)) (nex : NextL CSet), CrInv g gl →
    runLC env msup n (CGoal.toL gl) region g = some (nex, g') → ∃ m, nex = Next.toL m ∧ CrX g gl g' m
  | Nomm.n2 p q Option.none, hok, msup, region, gl, g, g', nex, hi, h => by
    have hok' := hok
    simp only [indOk, Bool.and_eq_true] at hok'
    obtain ⟨⟨⟨hpp, hp6⟩, _⟩, hq⟩ := hok'
    obtain ⟨nex0, g1, out, pro, g2, o, g3, nexF, g4, nexF', g5, nexS, g6, h1, h2, h3, h4, h5, h6, h7⟩ :=
      runLC_n2_none h
    rw [simpleNextL_toL, map_apply] at h1
    obtain ⟨n0, e1, rfl⟩ := crf_map_some h1
    obtain ⟨k1, -⟩ := keeps_simpleNext hi.2.1 hi.2.2.1 e1
    have d1 := k1.dropF hi.2.1
    have c1 := (kc_simpleNext gl).keep g n0 g1 e1
    have h2' : kerf (⟨Lazy.ofSure n0.laz, n0.th⟩ : NextL CSet) g1 = some ((out, pro), g2) := h2
    obtain ⟨-, -, -, ed2, c2, -, l2, -⟩ := kerf_ofSure h2' d1
    have d2 : g2.drop = false := ed2.trans d1
    obtain ⟨r3, d3⟩ := crf_emit h3 d2
    have c3 := crx_emit h3
    simp only at r3 c3
    have iq := cri_reg o (show g2.re + 1 < g3.re by omega) d3
    obtain ⟨nF, rfl, OF⟩ := crf_run env q hq msup region _ g3 g4 nexF iq h4
    obtain ⟨nF', e4, XF⟩ := crx_run env q hq msup region _ g3 g4 _ iq h4
    obtain rfl := next_toL_inj e4
    rw [pastL_pure env.cod _ hpp region, pure_apply] at h5
    simp only [Option.some.injEq, Prod.mk.injEq] at h5
    obtain ⟨rfl, rfl⟩ := h5
    have h6' : runLC env msup p (CGoal.toL (CGoal.next (lazyReg g2.re) nF.th)) region g4 = some (nexS, g6) := h6
    rw [cr2_run_pure env msup hpp hp6, map_apply] at h6'
    obtain ⟨nS, e6, rfl⟩ := crf_map_some h6'
    have h7' : copyL (Next.toL nS) (Lazy.ofSure nF.laz) g6 = some (nex, g') := h7
    rw [copyL_toL, map_apply] at h7'
    obtain ⟨n', e7, rfl⟩ := crf_map_some h7'
    refine ⟨n', rfl, ?_, fun _ => crx_copy_args e7, fun _ => nn_copy e7 (nn_run p hpp hp6 _ g4 g6 nS e6 trivial)
      (XF.2.2 trivial)⟩
    rw [(kc_copy nS nF.laz).keep g6 n' g' e7, (kc_run p _).keep g4 nS g6 e6, XF.1, c3, c2, c1]
  | Nomm.n5 p q, hok, msup, region, gl, g, g', nex, hi, h => by
    have hok' := hok
    simp only [indOk, Bool.and_eq_true] at hok'
    obtain ⟨⟨⟨hpp, hp6⟩, _⟩, hq⟩ := hok'
    rw [cr5_modelC] at h
    obtain ⟨o, g1, h1, h⟩ := bind_some h
    obtain ⟨l1, d1⟩ := cr5_br_keeps (g := { g with re := g.re + 1 + 1 }) hi.2.1 h1
    have c1 : g1.cond = g.cond := by
      have k : KC (cr5BrM g.re (g.re + 1) gl : CM (TreapMap mugF) Nat) := by
        cases gl with
        | pick z o => exact KC.emit' _
        | done => exact KC.bind' kc_doneBlocks fun _ => KC.emit' _
        | next laz th =>
          unfold cr5BrM
          refine KC.bind' (kc_collapseLazyAtom _) fun a => ?_
          cases a with
          | none => exact KC.ite' _ (KC.emit' _) KC.fail
          | some x => exact KC.bind' (kc_forl _ _) fun _ => KC.emit' _
      exact k.keep { g with re := g.re + 1 + 1 } o g1 h1
    have l1' : g.re + 1 + 1 ≤ g1.re := l1
    obtain ⟨nexF, g4, h4, h⟩ := bind_some h
    have iq := cri_reg o (show g.re + 1 < g1.re by omega) d1
    obtain ⟨nF, rfl, OF⟩ := crf_run env q hq msup region _ g1 g4 nexF iq h4
    obtain ⟨nF', e4, XF⟩ := crx_run env q hq msup region _ g1 g4 _ iq h4
    obtain rfl := next_toL_inj e4
    obtain ⟨nexF', g5, h5, h⟩ := bind_some h
    rw [pastL_pure env.cod _ hpp region, pure_apply] at h5
    simp only [Option.some.injEq, Prod.mk.injEq] at h5
    obtain ⟨rfl, rfl⟩ := h5
    obtain ⟨nexS, g6, h6, h7⟩ := bind_some h
    rw [cr2_run_pure env msup hpp hp6, map_apply] at h6
    obtain ⟨nS, e6, rfl⟩ := crf_map_some h6
    have h7' : copyL (Next.toL nS) (Lazy.ofSure nF.laz) g6 = some (nex, g') := h7
    rw [copyL_toL, map_apply] at h7'
    obtain ⟨n', e7, rfl⟩ := crf_map_some h7'
    refine ⟨n', rfl, ?_, fun _ => crx_copy_args e7, fun _ => nn_copy e7 (nn_run p hpp hp6 _ g4 g6 nS e6 trivial)
      (XF.2.2 trivial)⟩
    rw [(kc_copy nS nF.laz).keep g6 n' g' e7, (kc_run p _).keep g4 nS g6 e6, XF.1, c1]
  | Nomm.n3 p, hok, msup, region, gl, g, g', nex, hi, h => by
    simp only [indOk] at hok
    cases gl with
    | next laz th =>
      have h0 := h
      simp only [CGoal.toL, runLC] at h
      split at h
      · exact crx_run env p hok msup region (CGoal.next laz th) g g' nex hi h
      · obtain ⟨a, g1, h1, h⟩ := bind_some h
        obtain ⟨l1, d1⟩ := cri_cla hi.2.1 h1
        have c1 := (kc_collapseLazyAtom (S := CSet) (Map := TreapMap mugF) ⟨laz, th⟩).keep g a g1
          (by rw [← collapseLazyAtomL_mk]; exact h1)
        rcases a with _ | ⟨r, o⟩
        · simp at h
        · obtain ⟨⟨z, o'⟩, g2, h2, h⟩ := bind_some h
          have k2 := keepsA_forl (P := fun _ => True) d1 trivial (fun _ _ => trivial) h2
          have c2 := (kc_forl (Map := TreapMap mugF) r o).keep g1 _ g2 h2
          have l2 := k2.le
          obtain ⟨r', g3, h3, h⟩ := bind_some h
          rw [re_apply] at h3
          simp only [Option.some.injEq, Prod.mk.injEq] at h3
          obtain ⟨rfl, rfl⟩ := h3
          obtain ⟨oc, g4, h4, h⟩ := bind_some h
          obtain ⟨r4, d4⟩ := crf_emit h4 (k2.dropF d1)
          have c4 := crx_emit h4
          simp only at r4 c4
          obtain ⟨m, e, X⟩ := crx_run env p hok msup region (CGoal.next (lazyReg g2.re) (jmp0 oc)) g4 g' nex
            (cri_reg oc (by omega) d4) h
          exact ⟨m, e, crx_tail X (by rw [c4, c2, c1])⟩
    | pick z o =>
      simp only [CGoal.toL, runLC] at h
      obtain ⟨r, g1, h1, h⟩ := bind_some h
      rw [re_apply] at h1
      simp only [Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨oc, g2, h2, h⟩ := bind_some h
      obtain ⟨r2, d2⟩ := crf_emit h2 hi.2.1
      have c2 := crx_emit h2
      simp only at r2 c2
      obtain ⟨m, e, X⟩ := crx_run env p hok msup region (CGoal.next (lazyReg g.re) (jmp0 oc)) g2 g' nex
        (cri_reg oc (by omega) d2) h
      exact ⟨m, e, crx_tail X (by rw [c2])⟩
    | done =>
      simp only [CGoal.toL, runLC] at h
      obtain ⟨⟨o0, o1⟩, g1, h1, h⟩ := bind_some h
      have k1 := keepsA_doneBlocks (P := fun _ => True) hi.2.1 (fun _ _ => trivial) h1
      have c1 := (kc_doneBlocks (Map := TreapMap mugF)).keep g _ g1 h1
      have l1 := k1.le
      obtain ⟨r, g2, h2, h⟩ := bind_some h
      rw [re_apply] at h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      obtain ⟨oc, g3, h3, h⟩ := bind_some h
      obtain ⟨r3, d3⟩ := crf_emit h3 (k1.dropF hi.2.1)
      have c3 := crx_emit h3
      simp only at r3 c3
      obtain ⟨m, e, X⟩ := crx_run env p hok msup region (CGoal.next (lazyReg g1.re) (jmp0 oc)) g3 g' nex
        (cri_reg oc (by omega) d3) h
      exact ⟨m, e, crx_tail X (by rw [c3, c1])⟩
  | Nomm.n4 p, hok, msup, region, gl, g, g', nex, hi, h => by
    simp only [indOk] at hok
    cases gl with
    | done =>
      simp only [CGoal.toL, runLC] at h
      obtain ⟨pro, g1, h1, h⟩ := bind_some h
      rw [re_apply] at h1
      simp only [Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨arg, g2, h2, h⟩ := bind_some h
      rw [re_apply] at h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      obtain ⟨o, g3, h3, h⟩ := bind_some h
      obtain ⟨r3, d3⟩ := crf_emit h3 hi.2.1
      have c3 := crx_emit h3
      simp only at r3 c3
      obtain ⟨m, e, X⟩ := crx_run env p hok msup region (CGoal.next (lazyReg (g.re + 1)) (jmp0 o)) g3 g' nex
        (cri_reg o (by omega) d3) h
      exact ⟨m, e, crx_tail X (by rw [c3])⟩
    | pick z o =>
      simp only [CGoal.toL, runLC] at h
      obtain ⟨pro, g1, h1, h⟩ := bind_some h
      rw [re_apply] at h1
      simp only [Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨arg, g2, h2, h⟩ := bind_some h
      rw [re_apply] at h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      obtain ⟨o', g3, h3, h⟩ := bind_some h
      obtain ⟨r3, d3⟩ := crf_emit h3 hi.2.1
      have c3 := crx_emit h3
      simp only at r3 c3
      obtain ⟨m, e, X⟩ := crx_run env p hok msup region (CGoal.next (lazyReg (g.re + 1)) (jmp0 o')) g3 g' nex
        (cri_reg o' (by omega) d3) h
      exact ⟨m, e, crx_tail X (by rw [c3])⟩
    | next laz th =>
      simp only [CGoal.toL, runLC] at h
      obtain ⟨a, g1, h1, h⟩ := bind_some h
      obtain ⟨l1, d1⟩ := cri_cla hi.2.1 h1
      have c1 := (kc_collapseLazyAtom (S := CSet) (Map := TreapMap mugF) ⟨laz, th⟩).keep g a g1
        (by rw [← collapseLazyAtomL_mk]; exact h1)
      obtain ⟨⟨pro, th'⟩, g2, h2, h⟩ := bind_some h
      have k2 : g1.re ≤ g2.re ∧ g2.drop = false ∧ g2.cond = g1.cond := by
        rcases a with _ | x
        · simp only at h2
          obtain ⟨r, g5, h5, h2⟩ := bind_some h2
          rw [re_apply] at h5
          simp only [Option.some.injEq, Prod.mk.injEq] at h5
          obtain ⟨rfl, rfl⟩ := h5
          split at h2
          · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
            obtain ⟨-, rfl⟩ := h2
            exact ⟨by simp, d1, rfl⟩
          · cases h2
        · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
          obtain ⟨-, rfl⟩ := h2
          exact ⟨Nat.le_refl _, d1, rfl⟩
      obtain ⟨arg, g3, h3, h⟩ := bind_some h
      rw [re_apply] at h3
      simp only [Option.some.injEq, Prod.mk.injEq] at h3
      obtain ⟨rfl, rfl⟩ := h3
      obtain ⟨o, g4, h4, h⟩ := bind_some h
      obtain ⟨r4, d4⟩ := crf_emit h4 k2.2.1
      have c4 := crx_emit h4
      simp only at r4 c4
      obtain ⟨m, e, X⟩ := crx_run env p hok msup region (CGoal.next (lazyReg g2.re) (jmp0 o)) g4 g' nex
        (cri_reg o (by omega) d4) h
      exact ⟨m, e, crx_tail X (by rw [c4, k2.2.2, c1])⟩
  | Nomm.n7 p q, hok, msup, region, gl, g, g', nex, hi, h => by
    simp only [indOk, Bool.and_eq_true] at hok
    simp only [runLC] at h
    obtain ⟨nex1, g1, h1, h⟩ := bind_some h
    obtain ⟨n1, rfl, O1⟩ := crf_run env q hok.2 (some p) region gl g g1 nex1 hi h1
    obtain ⟨n1', e1, X1⟩ := crx_run env q hok.2 (some p) region gl g g1 _ hi h1
    obtain rfl := next_toL_inj e1
    rw [Next.goal_toL] at h
    obtain ⟨m, e, X2⟩ := crx_run env p hok.1 msup region n1.goal g1 g' nex (cro_goal O1) h
    exact ⟨m, e, X2.1.trans X1.1, fun ha => X2.2.1 (X1.2.1 ha), fun hn => X2.2.2 (X1.2.2 hn)⟩
  | Nomm.n2 _ _ (some _), hok, _, _, _, _, _, _, _, _ => by simp [indOk, Nomm.pure] at hok
  | Nomm.cons _ _, hok, _, _, _, _, _, _, _, h => by
    simp only [indOk, Bool.and_eq_true] at hok; exact crx_pure hok.1.1 hok.1.2 h
  | Nomm.n0 _, hok, _, _, _, _, _, _, _, h => by
    simp only [indOk, Bool.and_eq_true] at hok; exact crx_pure hok.1.1 hok.1.2 h
  | Nomm.n1 _, hok, _, _, _, _, _, _, _, h => by
    simp only [indOk, Bool.and_eq_true] at hok; exact crx_pure hok.1.1 hok.1.2 h
  | Nomm.n6 _ _ _, hok, _, _, _, _, _, _, _, _ => by simp [indOk, noSix] at hok
  | Nomm.n10 _ _ _, hok, _, _, _, _, _, _, _, h => by
    simp only [indOk, Bool.and_eq_true] at hok; exact crx_pure hok.1.1 hok.1.2 h
  | Nomm.n11s _ _ _, hok, _, _, _, _, _, _, _, _ => by simp [indOk, Nomm.pure] at hok
  | Nomm.n11d _ _ _ _, hok, _, _, _, _, _, _, _, _ => by simp [indOk, Nomm.pure] at hok
  | Nomm.n12 _ _, hok, _, _, _, _, _, _, _, _ => by simp [indOk, Nomm.pure] at hok
  | Nomm.mean _ _ _ _ _, hok, _, _, _, _, _, _, _, _ => by simp [indOk, Nomm.pure] at hok

/-! ## The five facts of the final pass -/

/-- The run of the final pass with calls, from `gen0` with `[%done ~]`, on
the fragment: a fork-free result with `CrOut` and `CrX`. -/
theorem cfr_run (env : CallEnv) {nm : Nomm} (hn : indOk nm = true) {nex : NextL CSet} {g1 : Gen (TreapMap mugF)}
    (hrun : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1)) :
    ∃ m, nex = Next.toL m ∧ CrOut gen0 CGoal.done g1 m ∧ CrX gen0 CGoal.done g1 m := by
  have hi : CrInv (gen0 : Gen (TreapMap mugF)) CGoal.done := cri_entry
  obtain ⟨m, e, O⟩ := crf_run env nm hn Option.none [] CGoal.done gen0 g1 nex hi hrun
  obtain ⟨m', e', X⟩ := crx_run env nm hn Option.none [] CGoal.done gen0 g1 nex hi hrun
  rw [e] at e'
  obtain rfl := next_toL_inj e'
  exact ⟨m, e, O, X⟩

/-- `cond` stays empty (`mem_cond_frag` for calls). -/
theorem mem_cond_frag_c (env : CallEnv) {nm : Nomm} (hn : indOk nm = true) {nex : NextL CSet}
    {g1 : Gen (TreapMap mugF)}
    (hrun : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1)) :
    ∀ k, HoonMap.get g1.cond k = Option.none := by
  obtain ⟨m, -, -, X⟩ := cfr_run env hn hrun
  intro k
  rw [X.1]
  exact gen0_cond_none k

/-- The result's `laz` is fork-free (`mem_laz_frag` for calls). -/
theorem mem_laz_frag_c (env : CallEnv) {nm : Nomm} (hn : indOk nm = true) {nex : NextL CSet}
    {g1 : Gen (TreapMap mugF)}
    (hrun : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1)) :
    ∃ s : Sure CSet, nex.laz = Lazy.ofSure s := by
  obtain ⟨m, rfl, -, -⟩ := cfr_run env hn hrun
  exact ⟨m.laz, rfl⟩

/-- The result jumps with no argument (`args_frag` for calls). -/
theorem args_frag_c (env : CallEnv) {nm : Nomm} (hn : indOk nm = true) {nex : NextL CSet}
    {g1 : Gen (TreapMap mugF)}
    (hrun : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1)) :
    nex.th.args = [] := by
  obtain ⟨m, rfl, -, X⟩ := cfr_run env hn hrun
  exact X.2.1 trivial

/-- `+sure-of` of the result succeeds and is `sccSur` (`scc_sur_frag` for
calls). -/
theorem scc_sur_frag_c (env : CallEnv) {nm : Nomm} (hn : indOk nm = true) {nex : NextL CSet}
    {g1 : Gen (TreapMap mugF)}
    (hrun : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
    (cape : Cape) :
    nex.laz = Lazy.ofSure nex.laz.sure ∧
      sureOf (needToOrd nex.laz.sure.ned) nex.laz.sure.lok cape = some (sccSur nex cape) := by
  obtain ⟨m, rfl, O, -⟩ := cfr_run env hn hrun
  obtain ⟨r, hr⟩ := sureOf_some cape m.laz.lok O.2.2.2.2.2 (needToOrd m.laz.ned)
  refine ⟨rfl, ?_⟩
  simp only [Next.toL, Lazy.sure_mk, Lazy.ofSure, sccSur] at hr ⊢
  rw [hr]
  rfl

/-- `+need-ord-alloc-regs` of `sccSur` succeeds (`noar_frag` for calls). -/
theorem noar_frag_c (env : CallEnv) {nm : Nomm} (hn : indOk nm = true) {nex : NextL CSet}
    {g1 : Gen (TreapMap mugF)}
    (hrun : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
    (cape : Cape) :
    ∃ nedF g2, needOrdAllocRegs (sccSur nex cape) g1 = some (nedF, g2) := by
  obtain ⟨hlz, hsur⟩ := scc_sur_frag_c env hn hrun cape
  have hnn : NN nex.laz.sure.ned := by
    obtain ⟨m, rfl, -, X⟩ := cfr_run env hn hrun
    exact X.2.2 trivial
  have hno := nno_sureOf cape nex.laz.sure.lok _ (nno_needToOrd hnn) _ hsur
  obtain ⟨n, g2, e, -⟩ := noar_nno (sccSur nex cape) g1 hno
  exact ⟨n, g2, e⟩

/-! ## `+inlined` on a nomm whose calls are all indirect

The trap of `+inlined` rebuilds an indirect call `[%2 p q ~]` from its walked
parts and returns it (`?~  info.nomm  [keep cache]`), so on a nomm with no
direct call, no hint and no `%12` (`indPure`) the walk is the identity and
keeps the cache, and `+inlined` is as on a pure nomm. -/

/-- No direct call, no hint, no `%12`, no `%mean`: the indirect calls are
allowed. -/
def indPure : Nomm → Bool
  | Nomm.cons p q => indPure p && indPure q
  | Nomm.n0 _ => true
  | Nomm.n1 _ => true
  | Nomm.n2 p q Option.none => indPure p && indPure q
  | Nomm.n3 p => indPure p
  | Nomm.n4 p => indPure p
  | Nomm.n5 p q => indPure p && indPure q
  | Nomm.n6 p q r => indPure p && indPure q && indPure r
  | Nomm.n7 p q => indPure p && indPure q
  | Nomm.n10 _ v q => indPure v && indPure q
  | _ => false

theorem indPure_of_pure : ∀ (n : Nomm), n.pure = true → indPure n = true := by
  intro n
  induction n <;> simp_all [Nomm.pure, indPure]

theorem indPure_of_indOk : ∀ (n : Nomm), indOk n = true → indPure n = true
  | Nomm.n2 p q Option.none, h => by
    simp only [indOk, Bool.and_eq_true] at h
    simp only [indPure, Bool.and_eq_true]
    exact ⟨indPure_of_pure p h.1.1.1, indPure_of_indOk q h.2⟩
  | Nomm.n5 p q, h => by
    simp only [indOk, Bool.and_eq_true] at h
    simp only [indPure, Bool.and_eq_true]
    exact ⟨indPure_of_pure p h.1.1.1, indPure_of_indOk q h.2⟩
  | Nomm.n3 p, h => by simp only [indOk] at h; simp only [indPure]; exact indPure_of_indOk p h
  | Nomm.n4 p, h => by simp only [indOk] at h; simp only [indPure]; exact indPure_of_indOk p h
  | Nomm.n7 p q, h => by
    simp only [indOk, Bool.and_eq_true] at h
    simp only [indPure, Bool.and_eq_true]
    exact ⟨indPure_of_indOk p h.1, indPure_of_indOk q h.2⟩
  | Nomm.n2 _ _ (some _), h => by simp [indOk, Nomm.pure] at h
  | Nomm.cons _ _, h => by simp only [indOk, Bool.and_eq_true] at h; exact indPure_of_pure _ h.1.1
  | Nomm.n0 _, _ => rfl
  | Nomm.n1 _, _ => rfl
  | Nomm.n6 _ _ _, h => by simp [indOk, noSix] at h
  | Nomm.n10 _ _ _, h => by simp only [indOk, Bool.and_eq_true] at h; exact indPure_of_pure _ h.1.1
  | Nomm.n11s _ _ _, h => by simp [indOk, Nomm.pure] at h
  | Nomm.n11d _ _ _ _, h => by simp [indOk, Nomm.pure] at h
  | Nomm.n12 _ _, h => by simp [indOk, Nomm.pure] at h
  | Nomm.mean _ _ _ _ _, h => by simp [indOk, Nomm.pure] at h

/-- **The trap of `+inlined` on a nomm whose calls are indirect** is the
identity and returns the cache it was given. -/
theorem inl_trap_ind : ∀ nm : Nomm, indPure nm = true → ∀ (HOT N BAT B LONG JH CA KK : Noun),
    nock (C inlTrap (C nm.toNoun (inlR HOT N BAT B LONG JH CA KK))) inlTrap = some (C nm.toNoun CA) := by
  intro nm
  induction nm with
  | cons p q ihp ihq =>
    intro hpu HOT N BAT B LONG JH CA KK
    simp only [indPure, Bool.and_eq_true] at hpu
    have hp := ihp hpu.1 HOT N BAT B LONG JH CA KK
    have hq := ihq hpu.2 HOT N BAT B LONG JH CA KK
    obtain ⟨a, b, hab⟩ := nomm_cell p
    rw [hab] at hp
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR at hp hq ⊢
    simp [nock_exec, Nomm.toNoun, hab, inlBCons, hp, hq]
  | n0 ax =>
    intro hpu HOT N BAT B LONG JH CA KK
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR
    simp [nock_exec, Nomm.toNoun]
  | n1 k =>
    intro hpu HOT N BAT B LONG JH CA KK
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR
    simp [nock_exec, Nomm.toNoun]
  | n2 p q info ihp ihq =>
    cases info with
    | some _ => intro hpu; simp [indPure] at hpu
    | none =>
      intro hpu HOT N BAT B LONG JH CA KK
      simp only [indPure, Bool.and_eq_true] at hpu
      have hp := ihp hpu.1 HOT N BAT B LONG JH CA KK
      have hq := ihq hpu.2 HOT N BAT B LONG JH CA KK
      conv => { lhs; arg 2; unfold inlTrap }
      unfold inlR at hp hq ⊢
      simp [nock_exec, Nomm.toNoun, unitNoun, inlB2, hp, hq]
  | n3 p ihp =>
    intro hpu HOT N BAT B LONG JH CA KK
    simp only [indPure] at hpu
    have hp := ihp hpu HOT N BAT B LONG JH CA KK
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR at hp ⊢
    simp [nock_exec, Nomm.toNoun, inlB3, hp]
  | n4 p ihp =>
    intro hpu HOT N BAT B LONG JH CA KK
    simp only [indPure] at hpu
    have hp := ihp hpu HOT N BAT B LONG JH CA KK
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR at hp ⊢
    simp [nock_exec, Nomm.toNoun, inlB4, hp]
  | n5 p q ihp ihq =>
    intro hpu HOT N BAT B LONG JH CA KK
    simp only [indPure, Bool.and_eq_true] at hpu
    have hp := ihp hpu.1 HOT N BAT B LONG JH CA KK
    have hq := ihq hpu.2 HOT N BAT B LONG JH CA KK
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR at hp hq ⊢
    simp [nock_exec, Nomm.toNoun, inlB5, hp, hq]
  | n6 p q r ihp ihq ihr =>
    intro hpu HOT N BAT B LONG JH CA KK
    simp only [indPure, Bool.and_eq_true] at hpu
    have hp := ihp hpu.1.1 HOT N BAT B LONG JH CA KK
    have hq := ihq hpu.1.2 HOT N BAT B LONG JH CA KK
    have hr := ihr hpu.2 HOT N BAT B LONG JH CA KK
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR at hp hq hr ⊢
    simp [nock_exec, Nomm.toNoun, inlB6, hp, hq, hr]
  | n7 p q ihp ihq =>
    intro hpu HOT N BAT B LONG JH CA KK
    simp only [indPure, Bool.and_eq_true] at hpu
    have hp := ihp hpu.1 HOT N BAT B LONG JH CA KK
    have hq := ihq hpu.2 HOT N BAT B LONG JH CA KK
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR at hp hq ⊢
    simp [nock_exec, Nomm.toNoun, inlB7, hp, hq]
  | n10 a v q ihv ihq =>
    intro hpu HOT N BAT B LONG JH CA KK
    simp only [indPure, Bool.and_eq_true] at hpu
    have hv := ihv hpu.1 HOT N BAT B LONG JH CA KK
    have hq := ihq hpu.2 HOT N BAT B LONG JH CA KK
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR at hv hq ⊢
    simp [nock_exec, Nomm.toNoun, inlB10, hv, hq]
  | n11s _ _ _ => intro hpu; simp [indPure] at hpu
  | n11d _ _ _ _ => intro hpu; simp [indPure] at hpu
  | n12 _ _ => intro hpu; simp [indPure] at hpu
  | mean _ _ _ _ _ => intro hpu; simp [indPure] at hpu

/-- **`+inlined` on a miss in `inl.cache`, for a nomm whose calls are indirect**: the nomm of `b`
in `code.long-ska` (`+got:by`, `hgot`, `hv`), walked to itself, and the cache
whose `inl` has it put at `b` (`hput`). -/
theorem inl_gate_miss_ind (B CODE LSR JH C1 C2 C3 INL SURE V INL' : Noun) (nm : Nomm) (hpu : indPure nm = true)
    (hinl : getF mugF B INL = some (A 0))
    (hgot : getF mugF B CODE = some (C (A 0) V)) (hv : slot? 2 V = some nm.toNoun)
    (hput : putF mugF B nm.toNoun INL = some INL') :
    nock (C inlBody (C (C B (C (C CODE LSR) (C JH (cacheN C1 C2 C3 INL SURE)))) compK)) inlBody
      = some (C nm.toNoun (cacheN C1 C2 C3 INL' SURE)) := by
  have hL := compK_layer2
  have hoff := inline_off_at
  have hg := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ B INL (A 0) hinl
  have hgt := got_gate (mug := mugF) layer2 ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ B CODE V hgot
  have hp := put_gate (mug := mugF) layer2 gorIn_morIn_layer2 B nm.toNoun INL INL' hput
  obtain ⟨v1, v2, rfl⟩ : ∃ a b, V = C a b := by
    cases V with
    | atom _ => simp [nock_exec] at hv
    | cell a b => exact ⟨a, b, rfl⟩
  simp only [nock_exec, Option.some.injEq] at hv
  subst hv
  have ht := fun HOT => inl_trap_ind nm hpu HOT (A 0) inlBodyN B (C CODE LSR) JH (cacheN C1 C2 C3 INL SURE) compK
  rw [inlBody_eq]
  conv => { lhs; arg 2; unfold inlBodyN }
  unfold cacheN inlR at *
  generalize compK = KC at hL hoff ht ⊢
  simp [nock_exec, hL, inlGet, inlMiss, inlInner, inlGot, inlAfter, inlHot, by.arm_at, by_arm, by.get.arm_at,
    get_arm, hg, by.got.arm_at, got_arm, hgt, hoff, ht, by.put.arm_at, put_arm, hp]

/-- **`+inlined` on a nomm whose calls are indirect**: under `InlOK`, the gate returns `nm` and
the cache with `inl` replaced by `INL'`. -/
theorem inl_gate_ind (B CODE LSR JH C1 C2 C3 INL SURE INL' : Noun) (nm : Nomm) (hpu : indPure nm = true)
    (hok : InlOK B CODE INL nm INL') :
    nock (C inlBody (C (C B (C (C CODE LSR) (C JH (cacheN C1 C2 C3 INL SURE)))) compK)) inlBody
      = some (C nm.toNoun (cacheN C1 C2 C3 INL' SURE)) := by
  rcases hok with ⟨h, e⟩ | ⟨h, ⟨V, hg, hv⟩, hp⟩
  · rw [e]; exact inl_gate_hit B (C CODE LSR) JH C1 C2 C3 INL SURE nm.toNoun h
  · exact inl_gate_miss_ind B CODE LSR JH C1 C2 C3 INL SURE V INL' nm hpu h hg hv hp


end Compiler
end Formalization
