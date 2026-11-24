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
* `hkids`, `hju`: for a bell that does not call itself (`NoSelfCall`: no
  entry at `b` in `calls.long-ska`, or a set of callees without `b`),
  `kids` is `[[b ~] ~ ~]` (`csi_kids_noself`: the `+rep:in` over `[b ~ ~]`
  with `+gut:by` and `+int:in`, `int_in` of `Hoon/IntIn.lean`; with no
  callee at all, `csi_kids_nocalls`) and `~(has ju kids) b b` is `|`
  (`ju_has_kids`);
* `huni` (`+uni:by` of `nary` and `[[b st] ~ ~]`): on a map `nary` it is
  `putF` (`uni_by_one`);
* `hsur`: on the fragment the run looks at no axis `0` (`cra_run_lok`), so
  `+sure-of` succeeds (`sureOf_some`); its product is named `sccSur`;
* `hst` (`finishLF … = some st`): the theorems are stated as a `bind` over
  `finishLF`, the gate crashing when it is `none` (`csi_final_one_none`,
  `cu_gate_none`);
* `hwas`, `hw`: they follow from `hput` (`getF_of_putF`).

* `hargs`: on the fragment the run for `[%done ~]` jumps with no argument
  (`crx_run_args`, `args_frag`).

What stays on the model side in `csi_gate_scc_one_m`: the run succeeds
(`hrunL`), `+need-ord-alloc-regs` of `sccSur` succeeds (`hnoar`), and
nothing is baked (`hb`); `csi_gate_scc_one_f` folds the first two into a
`bind` (the gate crashes where the model is `none`) and keeps `NoBakeOne`.  On the state nouns: `b` is not in `nary.cache`
(`hnary`) which is a map (`hnmap`), `b` is not among its own callees in
`calls.long-ska` (`hcalls`), `InlOK` for `inl.cache`, and the put of `sur` into
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

/-- `b` does not call itself: `calls.long-ska` has no entry at `b`, or a
set of callees that does not hold `b`. -/
def NoSelfCall (B CALLS : Noun) : Prop :=
  getF mugF B CALLS = some (A 0) ∨ ∃ CB, getF mugF B CALLS = some (C (A 0) CB) ∧ IsSet mugF CB ∧ ¬ Has CB B

theorem noSelfCall_of_noCalls {B CALLS : Noun} (h : NoCalls B CALLS) : NoSelfCall B CALLS := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr ⟨A 0, h, isSet_nil, not_has_atom⟩

theorem isSet_setOne (B : Noun) : IsSet mugF (setOne B) :=
  isSet_node_iff.2 ⟨isSet_nil, isSet_nil, fun _ h => absurd h not_has_atom, fun _ h => absurd h not_has_atom⟩

/-- **`kids` of `[b ~ ~]` when `b` does not call itself**: the `+int:in` of
the callees of `b` and `[b ~ ~]` is `~` (`int_in`, `isSet_ext`), so `kids`
is `[[b ~] ~ ~]`. -/
theorem csi_kids_noself (B CODE JETS CALLS JH CACHE : Noun) (hc : NoSelfCall B CALLS) :
    nock (C (A 0) (C csiBody (C (csiSam (setOne B) (C CODE (C JETS CALLS)) JH CACHE) compK))) csiKids
      = some (kidsOne B) := by
  have hL := compK_layer2
  obtain ⟨CB, hgut, hcb, hnb⟩ : ∃ CB, nock (C by.gut.battery (C (C B (A 0)) (C by.battery (C CALLS layer2))))
      by.gut.battery = some CB ∧ IsSet mugF CB ∧ ¬ Has CB B := by
    rcases hc with h | ⟨CB, h, hs, hn⟩
    · have := gut_gate (mug := mugF) layer2 ⟨fall.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ B (A 0) CALLS
        (A 0) h (Or.inl rfl)
      exact ⟨A 0, by simpa using this, isSet_nil, not_has_atom⟩
    · have := gut_gate (mug := mugF) layer2 ⟨fall.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ B (A 0) CALLS
        (C (A 0) CB) h (Or.inr ⟨_, rfl⟩)
      exact ⟨CB, by simpa using this, hs, hn⟩
  obtain ⟨X, hint, hxs, hxk⟩ := int_in (mug := mugF) layer2 gorIn_morIn_layer2 CB (setOne B) hcb (isSet_setOne B)
  have hx0 : X = A 0 := isSet_ext hxs isSet_nil fun k => by
    rw [hxk k]
    constructor
    · rintro ⟨h1, h2⟩
      rcases has_node.1 h2 with rfl | h | h
      · exact absurd h1 hnb
      · exact absurd h not_has_atom
      · exact absurd h not_has_atom
    · intro h; exact absurd h not_has_atom
  subst hx0
  have hput := put_gate (mug := mugF) layer2 gorIn_morIn_layer2 B (A 0) (A 0) (kidsOne B) rfl
  unfold csiKids csiSam setOne at *
  generalize compK = KC at hL
  simp [nock_exec, hL, in.arm_at, in_arm, in.rep.arm_at, rep_arm, rep_gate_one, by.arm_at, by_arm,
    by.put.arm_at, put_arm, hput, in.int.arm_at, int_in_arm, hint, by.gut.arm_at, gut_arm, hgut]

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

/-! ## `args.then` of the run is `~` -/

/-- The goal passes no argument: `args` of the jump of a `%next` goal and
of the two jumps of a `%pick` goal is `~`. -/
def ArgsNil : CGoal CSet → Prop
  | CGoal.next _ th => th.args = []
  | CGoal.pick z o => z.args = [] ∧ o.args = []
  | CGoal.done => True

theorem crx_copy_args {f : Next CSet} {s : Sure CSet} {g g' : Gen (TreapMap mugF)} {nex : Next CSet}
    (h : copy f s g = some (nex, g')) : nex.th.args = [] := by
  simp only [copy, copyLazy, cra_bind, cf_emit_g] at h
  obtain ⟨o, g1, e1, a, g2, e2, e3⟩ := h
  simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e3
  obtain ⟨rfl, rfl⟩ := e3
  rfl

theorem crx_bomb_args {miss : Option Nat} {g g' : Gen (TreapMap mugF)} {nex : Next CSet}
    (h : bomb miss g = some (nex, g')) : nex.th.args = [] := by
  simp only [bomb, cra_bind, cf_emit_g, pure, StateT.pure] at h
  obtain ⟨o, g1, -, h⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  rfl

theorem crx_sn_args (gl : CGoal CSet) (ha : ArgsNil gl) (g : Gen (TreapMap mugF)) (nex : Next CSet)
    (g1 : Gen (TreapMap mugF)) (e : simpleNext gl g = some (nex, g1)) : nex.th.args = [] := by
  cases gl with
  | next laz th =>
    simp [simpleNext, pure, StateT.pure] at e
    rw [← e.1]; exact ha
  | done =>
    simp [simpleNext, re, bind, StateT.bind, pure, StateT.pure, cd_emit_eq] at e
    rcases e with ⟨rfl, -⟩
    rfl
  | pick z o =>
    simp [simpleNext, re, bind, StateT.bind, pure, StateT.pure, cd_emit_eq] at e
    rcases e with ⟨rfl, -⟩
    rfl

/-- **A run of the model from a goal with no argument returns a `next`
with none**, for every pure nomm with no `%6`: the `next` comes from
`+copy`, `+bomb` or `+simple-next`, which jump with no argument, or from a
run on such a goal. -/
theorem crx_run_args : ∀ (n : Nomm), n.pure = true → noSix n = true → ∀ (gl : CGoal CSet)
    (g g' : Gen (TreapMap mugF)) (nex : Next CSet), run n gl g = some (nex, g') → ArgsNil gl → nex.th.args = []
  | Nomm.cons p q, hpu, h6, gl, g, g', nex, h, ha => by
    simp only [Nomm.pure, Bool.and_eq_true] at hpu
    have hnext : ∀ s th g, run (Nomm.cons p q) (CGoal.next s th) g = some (nex, g') → nex.th.args = [] := by
      intro s th g h
      rw [crc_run_next p q hpu.1 hpu.2] at h
      simp only [cra_bind] at h
      obtain ⟨⟨hed, tel, o⟩, g1, e1, nex2, g2, e2, nex1, g3, e3, e4⟩ := h
      exact crx_copy_args e4
    cases gl with
    | next s th => exact hnext s th g h
    | done => rw [crc_run_done] at h; exact hnext _ _ _ h
    | pick z o =>
      rw [crc_run_pick p q hpu.1] at h
      simp only [cra_bind] at h
      obtain ⟨nex2, g2, e2, nex1, g3, e3, e4⟩ := h
      exact crx_copy_args e4
  | Nomm.n0 ax, _, _, gl, g, g', nex, h, ha => by
    simp only [run] at h
    split at h
    · exact crx_bomb_args h
    · rw [cra_bind] at h
      obtain ⟨nex0, g1, e1, h⟩ := h
      have h0 := crx_sn_args gl ha g nex0 g1 e1
      split at h
      · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h; exact h0
      · cases ef : «from» ax nex0.laz with
        | none => simp [ef] at h
        | some laz =>
          simp [ef, pure, StateT.pure] at h
          obtain ⟨rfl, -⟩ := h
          exact h0
  | Nomm.n1 k, _, _, gl, g, g', nex, h, ha => by
    cases gl with
    | done =>
      simp only [run, cra_bind, pure, StateT.pure] at h
      obtain ⟨r, g1, -, o, g2, -, h⟩ := h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h; rfl
    | pick z o =>
      simp only [run] at h
      split at h
      · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h; exact ha.1
      · split at h
        · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h; exact ha.2
        · exact crx_bomb_args h
    | next laz th =>
      simp only [run, cra_bind, pure, StateT.pure] at h
      obtain ⟨o, g1, -, h⟩ := h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h; rfl
  | Nomm.n3 p, hpu, h6, gl, g, g', nex, h, ha => by
    have ih := crx_run_args p hpu h6
    cases gl with
    | next laz th =>
      simp only [run] at h
      split at h
      · exact ih _ _ _ _ h ha
      · rw [cra_bind] at h
        obtain ⟨a, g1, -, h⟩ := h
        rcases a with _ | ⟨r, o⟩
        · cases h
        · simp only [cra_bind] at h
          obtain ⟨⟨z, o'⟩, g2, -, r', g3, -, oc, g4, -, h⟩ := h
          exact ih _ _ _ _ h rfl
    | pick z o =>
      simp only [run, cra_bind] at h
      obtain ⟨r, g1, -, oc, g2, -, h⟩ := h
      exact ih _ _ _ _ h rfl
    | done =>
      simp only [run, cra_bind] at h
      obtain ⟨⟨o0, o1⟩, g1, -, r, g2, -, oc, g3, -, h⟩ := h
      exact ih _ _ _ _ h rfl
  | Nomm.n4 p, hpu, h6, gl, g, g', nex, h, ha => by
    have ih := crx_run_args p hpu h6
    cases gl with
    | done =>
      simp only [run, cra_bind] at h
      obtain ⟨pro, g1, -, arg, g2, -, o, g3, -, h⟩ := h
      exact ih _ _ _ _ h rfl
    | pick z o =>
      simp only [run, cra_bind] at h
      obtain ⟨pro, g1, -, arg, g2, -, o', g3, -, h⟩ := h
      exact ih _ _ _ _ h rfl
    | next laz th =>
      simp only [run, cra_bind] at h
      obtain ⟨a, g1, -, ⟨pro, th'⟩, g2, -, arg, g3, -, o, g4, -, h⟩ := h
      exact ih _ _ _ _ h rfl
  | Nomm.n5 p q, hpu, h6, gl, g, g', nex, h, ha => by
    simp only [Nomm.pure, Bool.and_eq_true] at hpu
    rw [cr_run_n5_eq p q hpu.1] at h
    simp only [cra_bind] at h
    obtain ⟨o, g1, -, nexq, g2, e2, nexp, g3, e3, e4⟩ := h
    exact crx_copy_args e4
  | Nomm.n7 p q, hpu, h6, gl, g, g', nex, h, ha => by
    simp only [Nomm.pure, Bool.and_eq_true] at hpu
    simp only [noSix, Bool.and_eq_true] at h6
    have ihp := crx_run_args p hpu.1 h6.1
    have ihq := crx_run_args q hpu.2 h6.2
    simp only [run, cra_bind] at h
    obtain ⟨nex1, g1, e1, h⟩ := h
    exact ihp _ _ _ _ h (ihq _ _ _ _ e1 ha)
  | Nomm.n10 a v q, hpu, h6, gl, g, g', nex, h, ha => by
    simp only [Nomm.pure, Bool.and_eq_true] at hpu
    rw [cr_run_n10_eq a v q hpu.1 hpu.2] at h
    simp only [cra_bind] at h
    obtain ⟨nex0, g1, -, ⟨don, rec, o⟩, g2, e2, nexD, g3, e3, nexR, g4, e4, e5⟩ := h
    exact crx_copy_args e5
  | Nomm.n2 _ _ _, hpu, _, _, _, _, _, _, _ => by simp [Nomm.pure] at hpu
  | Nomm.n6 _ _ _, _, h6, _, _, _, _, _, _ => by simp [noSix] at h6
  | Nomm.n11s _ _ _, hpu, _, _, _, _, _, _, _ => by simp [Nomm.pure] at hpu
  | Nomm.n11d _ _ _ _, hpu, _, _, _, _, _, _, _ => by simp [Nomm.pure] at hpu
  | Nomm.n12 _ _, hpu, _, _, _, _, _, _, _ => by simp [Nomm.pure] at hpu
  | Nomm.mean _ _ _ _ _, hpu, _, _, _, _, _, _, _ => by simp [Nomm.pure] at hpu

/-- **`hargs` from the run**: on the fragment, the run for `[%done ~]`
returns a `next` whose `args.then` is `~`. -/
theorem args_frag (nm : Nomm) (hpu : nm.pure = true) (h6 : noSix nm = true) (nex : NextL CSet)
    (g1 : Gen (TreapMap mugF))
    (hrunL : runL nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1)) :
    nex.th.args = [] := by
  rw [show (CGoalL.done : CGoalL CSet) = CGoal.toL CGoal.done from rfl, runL_toL nm hpu h6] at hrunL
  cases e : run (S := CSet) (Map := TreapMap mugF) nm CGoal.done gen0 with
  | none => simp [e, Functor.map, StateT.map] at hrunL
  | some q =>
    obtain ⟨nex0, g0⟩ := q
    simp [e, Functor.map, StateT.map] at hrunL
    obtain ⟨rfl, rfl⟩ := hrunL
    exact crx_run_args nm hpu h6 CGoal.done gen0 g0 nex0 e trivial

/-! ## The gate on an SCC of one bell -/

/-- **`+compile-scc-in` on an SCC of one bell `b` with no callee, not in
`nary.cache`, whose nomm is pure, `%6`-free and `tenOk`**: the gate
returns `[[[b st] ~ ~] cache']` with `st` the straight of `finishLF nm sur
cape` (`sur` the shape `sccSur` of the run) and crashes when that is
`none`; `cache'` has `nary` with `st` put at `b` (`putF`, the `+uni:by`),
`inl` as `InlOK` says, and `sure` with `sur` put at `b` (`SURE'`).  The
hypotheses on the model: the run succeeds, `+need-ord-alloc-regs` of `sur`
succeeds, nothing is baked. -/
theorem csi_gate_scc_one_m (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (hpu : nm.pure = true) (h6 : noSix nm = true) (ht : tenOk nm = true)
    (nex : NextL CSet) (g1 : Gen (TreapMap mugF))
    (hrunL : runL nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
    (nedF : Need) (g2 : Gen (TreapMap mugF))
    (hnoar : needOrdAllocRegs (sccSur nex cape) g1 = some (nedF, g2))
    (hb : NoBake nedF (Sock.mk cape DATA))
    (SURE' : Noun) (hput : putF mugF (C (C cape.toNoun DATA) FOL) (sccSur nex cape).toNoun SURE = some SURE') :
    nock (C csiBody (C (csiSam (setOne (C (C cape.toNoun DATA) FOL)) (C CODE (C JETS CALLS)) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) csiBody
      = (finishLF (S := CSet) (Map := TreapMap mugF) nm (sccSur nex cape) cape (fun n => (n, []))).bind fun st =>
          (putF mugF (C (C cape.toNoun DATA) FOL) st.toNoun NARY).map fun NARYU =>
            C (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))) (cacheN NARYU MONO SCCS INL' SURE') := by
  have hcache : cacheN NARY MONO SCCS INL SURE = C NARY (C MONO (C SCCS (C INL SURE))) := rfl
  rw [hcache, csi_to_final _ _ _ _ _ _ hnary (csi_kids_noself _ CODE JETS CALLS JH _ hcalls) (ju_has_kids _)]
  obtain ⟨hlz, hsur⟩ := scc_sur_frag nm hpu h6 nex g1 hrunL cape
  have hargs := args_frag nm hpu h6 nex g1 hrunL
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
    (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (hpu : nm.pure = true) (h6 : noSix nm = true) (ht : tenOk nm = true)
    (nex : NextL CSet) (g1 : Gen (TreapMap mugF))
    (hrunL : runL nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
    (nedF : Need) (g2 : Gen (TreapMap mugF))
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
    hinl hpu h6 ht nex g1 hrunL nedF g2 hnoar hb SURE' hput
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

/-! ## The crashes of the final pass of `member` -/

/-- The final pass crashes when the run does. -/
theorem mem_final_run_none (GN NM DCTX S0 : Noun) (hmode : edit? 46 (A 0x6e7572) (C GN (memS3 NM DCTX S0))
      = some (C GN (memS3 NM DCTX S0)))
    (hrun : nock (crSubj (A 1) NM (C (A 0x656e6f64) (A 0)) (A 0) (A 0) (C comp.door (C GN DCTX))) crDol = none) :
    nock (C GN (memS3 NM DCTX S0)) memFinal = none := by
  conv => { lhs; arg 2; unfold memFinal }
  simp [nock_exec, hmode, mem_run_call, hrun]

/-- The final pass crashes when `+collapse-shape` does. -/
theorem mem_final_cs_none (GN NM DCTX CAPE DATA FOL KEEP ML TOP CA CTX NEXN G1N : Noun)
    (hmode : edit? 46 (A 0x6e7572) (C GN (memS3 NM DCTX (memS0 (C (C CAPE DATA) FOL) KEEP ML TOP CA CTX)))
      = some (C GN (memS3 NM DCTX (memS0 (C (C CAPE DATA) FOL) KEEP ML TOP CA CTX))))
    (hrun : nock (crSubj (A 1) NM (C (A 0x656e6f64) (A 0)) (A 0) (A 0) (C comp.door (C GN DCTX))) crDol
      = some (C NEXN G1N))
    (hcs : nock (C csBody (C (C NEXN CAPE) (C comp.door (C G1N DCTX)))) csBody = none) :
    nock (C GN (memS3 NM DCTX (memS0 (C (C CAPE DATA) FOL) KEEP ML TOP CA CTX))) memFinal = none := by
  conv => { lhs; arg 2; unfold memFinal }
  simp [nock_exec, memF2, hmode, mem_run_call, hrun, mem_cs_call, hcs]

/-- **`member` on its final pass crashes when the run does**, or when
`+collapse-shape` does: `args.then` not `~`, or `+need-ord-alloc-regs` of
`sccSur` crashing. -/
theorem mem_gate_none (cape : Cape) (DATA FOL : Noun) (keep : Bool)
    (ML TOP CACHE DN KIDS ML0 CB SCC CODE LSR JH CACHE0 : Noun) (nm : Nomm) (CA : Noun)
    (hinl : nock (C inlBody (C (C (C (C cape.toNoun DATA) FOL) (C (C CODE LSR) (C JH CACHE))) compK)) inlBody
      = some (C nm.toNoun CA))
    (hpu : nm.pure = true) (h6 : noSix nm = true) (ht : tenOk nm = true)
    (hcrash : runL nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = none ∨
      ∃ nex g1, runL nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1) ∧
        (nex.th.args ≠ [] ∨ needOrdAllocRegs (sccSur nex cape) g1 = none)) :
    nock (C memBody (C (memSam (C (C cape.toNoun DATA) FOL) (A 0x656e6f64) (loob keep) ML TOP CACHE)
        (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0))) memBody = none := by
  have h7 : slot? 7 (memDCtx SCC (C CODE LSR) JH ML TOP (C (C cape.toNoun DATA) FOL)) = some compK := rfl
  have hcode : slot? 52 (memDCtx SCC (C CODE LSR) JH ML TOP (C (C cape.toNoun DATA) FOL)) = some CODE := by
    simp [memDCtx, nock_exec]
  rw [mem_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨_, _, _, rfl⟩ hinl, mem_r3, mem_res]
  have hrunN := comp_run_entry h7 hcode nm hpu h6 ht (cuRest CA) (A 1) (A 0) (cu_entry_nosoft _)
  rcases hcrash with hr | ⟨nex, g1, hr, hc⟩
  · have hr' : runL nm (CGoal.toL (CGoal.done : CGoal CSet)) [] (gen0 : Gen (TreapMap mugF)) = none := hr
    rw [← gen0_eq, hr', cu_done_noun] at hrunN
    simp only [listNoun, Option.map_none, compCore] at hrunN
    rw [mem_final_run_none (hmode := mem_mode_noop _ _) (hrun := hrunN)]
    rfl
  · have hr' : runL nm (CGoal.toL (CGoal.done : CGoal CSet)) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1) := hr
    rw [← gen0_eq, hr', cu_done_noun] at hrunN
    simp only [listNoun, Option.map_some, compCore] at hrunN
    obtain ⟨hlz, hsur⟩ := scc_sur_frag nm hpu h6 nex g1 hr cape
    have hsc := hsc_of_sure nex nex.laz.sure hlz cape (sccSur nex cape) hsur
    have hcsN := cs_gate _ h7 (cuRest CA) g1 nex cape.toNoun (sccSur nex cape) hsc
    have hnone : (if nex.th.args ≠ [] then Option.none else
        (needOrdAllocRegs (sccSur nex cape) g1).map fun p =>
          C (C p.1.toNoun (C nex.laz.toNoun (A nex.th.there))) (genNoun p.2 (cuRest CA))) = Option.none := by
      rcases hc with ha | hn
      · simp [ha]
      · simp [hn]
    rw [hnone] at hcsN
    simp only [compCore] at hcsN
    rw [mem_final_cs_none (hmode := mem_mode_noop _ _) (hrun := hrunN) (hcs := hcsN)]
    rfl

/-! ## The gate with the model hypotheses folded in -/

/-- **The final pass of `member` for an SCC of one bell**, as a model: the
run of `nm` for `[%done ~]`, then `finishLF` with `ord` the shape `sccSur`
of that run. -/
noncomputable def finishSccOne (nm : Nomm) (cape : Cape) : Option (Straight (TreapMap mugF)) :=
  (runL nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))).bind fun p =>
    finishLF (S := CSet) (Map := TreapMap mugF) nm (sccSur p.1 cape) cape (fun n => (n, []))

/-- Nothing is baked whenever the final pass gets to `+bake-need`. -/
def NoBakeOne (nm : Nomm) (cape : Cape) (DATA : Noun) : Prop :=
  ∀ nex g1 nedF g2, runL nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1) →
    needOrdAllocRegs (sccSur nex cape) g1 = some (nedF, g2) → NoBake nedF (Sock.mk cape DATA)

/-- **`+compile-scc-in` on an SCC of one bell, with the model hypotheses
folded in**: on the fragment (`nm` pure, `%6`-free, `tenOk`) and when
nothing is baked (`NoBakeOne`), the gate returns the noun of the model:
`[[[b st] ~ ~] cache']` with `st` from the run of `nm` and `finishLF` with
`ord := sccSur`, `nary` with `st` put at `b`, `inl` as `InlOK` says and
`sure` with `sccSur` put at `b`; it crashes when the model is `none`.  The
other hypotheses speak of the state nouns only. -/
theorem csi_gate_scc_one_f (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (hpu : nm.pure = true) (h6 : noSix nm = true) (ht : tenOk nm = true)
    (hbake : NoBakeOne nm cape DATA) :
    nock (C csiBody (C (csiSam (setOne (C (C cape.toNoun DATA) FOL)) (C CODE (C JETS CALLS)) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) csiBody
      = (runL nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))).bind fun p =>
          (finishLF (S := CSet) (Map := TreapMap mugF) nm (sccSur p.1 cape) cape (fun n => (n, []))).bind fun st =>
            (putF mugF (C (C cape.toNoun DATA) FOL) st.toNoun NARY).bind fun NARYU =>
              (putF mugF (C (C cape.toNoun DATA) FOL) (sccSur p.1 cape).toNoun SURE).map fun SURE' =>
                C (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))) (cacheN NARYU MONO SCCS INL' SURE') := by
  have hi := inl_gate (C (C cape.toNoun DATA) FOL) CODE (C JETS CALLS) JH NARY MONO SCCS INL SURE INL' nm hpu hinl
  have hcrash : (runL nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = none ∨
      ∃ nex g1, runL nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1) ∧
        (nex.th.args ≠ [] ∨ needOrdAllocRegs (sccSur nex cape) g1 = none)) →
      nock (C csiBody (C (csiSam (setOne (C (C cape.toNoun DATA) FOL)) (C CODE (C JETS CALLS)) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) csiBody = none := by
    intro hc
    have hcache : cacheN NARY MONO SCCS INL SURE = C NARY (C MONO (C SCCS (C INL SURE))) := rfl
    rw [hcache, csi_to_final _ _ _ _ _ _ hnary (csi_kids_noself _ CODE JETS CALLS JH _ hcalls) (ju_has_kids _)]
    exact csi_final_one_none _ _ _ _ _ _ _ _ (mem_gate_none cape DATA FOL false (A 0) (A 0)
      (C NARY (C MONO (C SCCS (C INL SURE)))) (A 0) (kidsOne _) (A 0) csiBody _ CODE (C JETS CALLS) JH
      (C NARY (C MONO (C SCCS (C INL SURE)))) nm _ hi hpu h6 ht hc)
  cases hr : runL nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) with
  | none => exact hcrash (Or.inl hr)
  | some p =>
    obtain ⟨nex, g1⟩ := p
    simp only [Option.bind_some]
    by_cases ha : nex.th.args = []
    · cases hn : needOrdAllocRegs (sccSur nex cape) g1 with
      | none =>
        have hf : finishLF (S := CSet) (Map := TreapMap mugF) nm (sccSur nex cape) cape (fun n => (n, []))
            = Option.none := by
          unfold finishLF; simp [hr, ha, hn]
        rw [hf, hcrash (Or.inr ⟨nex, g1, hr, Or.inr hn⟩)]
        rfl
      | some q =>
        obtain ⟨nedF, g2⟩ := q
        obtain ⟨SURE', hp, -, -⟩ := putF_spec mugF SURE (C (C cape.toNoun DATA) FOL) (sccSur nex cape).toNoun hsmap
        rw [csi_gate_scc_one_m cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hcalls nm INL'
          hinl hpu h6 ht nex g1 hr nedF g2 hn (hbake nex g1 nedF g2 hr hn) SURE' hp]
        cases finishLF (S := CSet) (Map := TreapMap mugF) nm (sccSur nex cape) cape (fun n => (n, [])) with
        | none => rfl
        | some st =>
          obtain ⟨NARYU, hq, -, -⟩ := putF_spec mugF NARY (C (C cape.toNoun DATA) FOL) st.toNoun hnmap
          simp [hq, hp]
    · have hf : finishLF (S := CSet) (Map := TreapMap mugF) nm (sccSur nex cape) cape (fun n => (n, []))
          = Option.none := by
        unfold finishLF; simp [hr, ha]
      rw [hf, hcrash (Or.inr ⟨nex, g1, hr, Or.inl ha⟩)]
      rfl

/-- **The gate of `+compile-unary` on `[func [b ~ ~] long-ska jets-hot
cache]` with the model hypotheses folded in**: under the hypotheses of
`csi_gate_scc_one_f`, and for the nomm `n` of `func` (pure, `%6`-free,
`tenOk`), it returns `finishLU n` with the n-ary map and the cache of the
model, and crashes when the model of the SCC is `none`. -/
theorem cu_gate_scc_one_f (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (hpu : nm.pure = true) (h6 : noSix nm = true) (ht : tenOk nm = true)
    (hbake : NoBakeOne nm cape DATA)
    (FUNC V : Noun) (n : Nomm) (hpu' : n.pure = true) (h6' : noSix n = true) (ht' : tenOk n = true)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (C cuGB (C (cuSam FUNC (setOne (C (C cape.toNoun DATA) FOL)) CODE (C JETS CALLS) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) cuGB
      = (runL nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))).bind fun p =>
          (finishLF (S := CSet) (Map := TreapMap mugF) nm (sccSur p.1 cape) cape (fun n => (n, []))).bind fun st =>
            (putF mugF (C (C cape.toNoun DATA) FOL) st.toNoun NARY).bind fun NARYU =>
              (putF mugF (C (C cape.toNoun DATA) FOL) (sccSur p.1 cape).toNoun SURE).bind fun SURE' =>
                (finishLU (S := CSet) (Map := TreapMap mugF) n).map fun st' =>
                  C (C st'.toNoun (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))))
                    (cacheN NARYU MONO SCCS INL' SURE') := by
  have hcsi := csi_gate_scc_one_f cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hsmap hcalls
    nm INL' hinl hpu h6 ht hbake
  rw [← cu_csi_eq FUNC] at hcsi
  cases hr : runL nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) with
  | none =>
    rw [hr] at hcsi
    exact cu_gate_none _ hcsi
  | some p =>
    obtain ⟨nex, g1⟩ := p
    rw [hr] at hcsi
    simp only [Option.bind_some] at hcsi ⊢
    cases e : finishLF (S := CSet) (Map := TreapMap mugF) nm (sccSur nex cape) cape (fun n => (n, [])) with
    | none =>
      rw [e] at hcsi
      exact cu_gate_none _ hcsi
    | some st =>
      obtain ⟨NARYU, hq, -, -⟩ := putF_spec mugF NARY (C (C cape.toNoun DATA) FOL) st.toNoun hnmap
      obtain ⟨SURE', hp, -, -⟩ := putF_spec mugF SURE (C (C cape.toNoun DATA) FOL) (sccSur nex cape).toNoun hsmap
      rw [e] at hcsi
      simp only [Option.bind_some, hq, hp, Option.map_some] at hcsi ⊢
      exact cu_gate FUNC _ CODE (C JETS CALLS) JH _ _ _ V n hpu' h6' ht' hcsi hgot hv

/-! ## The cache hit -/

/-- The gate of the `+turn` of the cache hit: `|=(b=bell [b (~(got by
nary.cache) b)])`, as it stands in `csiHit`. -/
def csiHitGate : Noun :=
  (C (C (A 0) (A 6)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 701)
    (C (A 10) (C (C (A 6) (C (A 0) (A 1006))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6)
    (C (A 0) (A 14))) (C (A 0) (A 2)))))))))

/-- `csiHit` holds `csiHitGate`, a fact about the definitions. -/
theorem csiHit_gate : csiHit = (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3ffff)))) (C (A 9)
    (C (A 378) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0))))) (C (A 0) (A 2)))))))) (C (A 9)
    (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0)
    (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9)
    (C (A 6102) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 186) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0)
    (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (A 1) (A 0)) (C (A 0) (A 0))))
    (C (C (A 1) csiHitGate) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (A 0) (A 55))) :=
  rfl

/-- The gate of the `+turn` on a bell `b` that `nary.cache` holds. -/
theorem csi_hit_gate (x SCC LONG JH NARY CR V : Noun) (hv : getF mugF x NARY = some (C (A 0) V)) :
    nock (C csiHitGate (C x (C csiBody (C (csiSam SCC LONG JH (C NARY CR)) compK)))) csiHitGate = some (C x V) := by
  have hL := compK_layer2
  have hg := got_gate (mug := mugF) layer2 ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ x NARY V hv
  unfold csiHitGate csiSam
  generalize compK = KC at hL
  generalize csiBody = CB
  simp [nock_exec, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg]

/-- **The cache hit of `+compile-scc-in`**: when every member `b` of `scc`
(a tree) is in `nary.cache` with the straight `vals b`, the gate returns the
map that `+gas:by` builds from `~` and the pairs `[b (vals b)]` in the order
of `+tap:in`, and the cache unchanged. -/
theorem csi_hit (SCC LONG JH NARY CR OUT : Noun) (hs : Tree SCC) (vals : Noun → Noun)
    (hv : ∀ b ∈ tapList SCC, getF mugF b NARY = some (C (A 0) (vals b)))
    (hg : gasF mugF (A 0) ((tapList SCC).map fun b => (b, vals b)) = some OUT) :
    nock (C csiBody (C (csiSam SCC LONG JH (C NARY CR)) compK)) csiBody = some (C OUT (C NARY CR)) := by
  have hL := compK_layer2
  have htap : tapF SCC (A 0) = some (listN (tapList SCC)) := by simpa [listN] using tapF_list hs []
  have hlevy := levy_gate layer2 by.has.battery (A 0) (C by.battery (C NARY layer2)) (fun _ => true) (tapList SCC)
    (fun x hx => by
      rw [has_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ x NARY _ (hv x hx)]
      simp)
  rw [show (tapList SCC).all (fun _ => true) = true by simp] at hlevy
  have hturn := turn_gate layer2 homoIn_layer2 csiHitGate (C (C (A 1) (A 0)) (C (A 0) (A 0)))
    (C csiBody (C (csiSam SCC LONG JH (C NARY CR)) compK)) (fun b => C b (vals b)) (tapList SCC)
    (fun x hx => csi_hit_gate x SCC LONG JH NARY CR (vals x) (hv x hx))
  have hgas : nock (C by.gas.battery (C (listN ((tapList SCC).map fun b => C b (vals b)))
      (C by.battery (C (A 0) layer2)))) by.gas.battery = some OUT := by
    have := gas_gate (mug := mugF) layer2 gorIn_morIn_layer2 _ (A 0) OUT hg
    simpa [List.map_map, pairNoun, Function.comp_def] using this
  conv => { lhs; arg 2; unfold csiBody }
  rw [csiHit_gate]
  unfold csiSam at hturn ⊢
  generalize csiBody = CB at hturn ⊢
  generalize compK = KC at hL hturn ⊢
  simp [nock_exec, hL, csiLevy, levy.arm_at, levy_arm, in.arm_at, in_arm, in.tap.arm_at, tap_arm, tap_loop, htap,
    by.arm_at, by_arm, by.has.arm_at, has_arm, hlevy, by.gas.arm_at, gas_arm, hgas, turn.arm_at, turn_arm, hturn]

/-- **The cache hit on an SCC of one bell**: `[[[b st] ~ ~] cache]`. -/
theorem csi_hit_one (B LONG JH NARY CR ST : Noun) (hv : getF mugF B NARY = some (C (A 0) ST)) :
    nock (C csiBody (C (csiSam (setOne B) LONG JH (C NARY CR)) compK)) csiBody
      = some (C (C (C B ST) (C (A 0) (A 0))) (C NARY CR)) :=
  csi_hit (setOne B) LONG JH NARY CR _ (Tree.node Tree.nil Tree.nil) (fun _ => ST)
    (fun b hb => by simp [setOne, tapList] at hb; subst hb; exact hv) (by simp [setOne, tapList, gasF, putF])

/-- **`+compile-unary` on a cache hit**: when every member of `scc` is in
`nary.cache`, the gate returns `finishLU` of the nomm of `func` with the
n-ary map of `csi_hit` and the cache unchanged. -/
theorem cu_gate_hit (FUNC SCC CODE LSR JH NARY CR OUT V : Noun) (hs : Tree SCC) (vals : Noun → Noun)
    (hv : ∀ b ∈ tapList SCC, getF mugF b NARY = some (C (A 0) (vals b)))
    (hg : gasF mugF (A 0) ((tapList SCC).map fun b => (b, vals b)) = some OUT)
    (n : Nomm) (hpu : n.pure = true) (h6 : noSix n = true) (ht : tenOk n = true)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hvn : slot? 2 V = some n.toNoun) :
    nock (C cuGB (C (cuSam FUNC SCC CODE LSR JH (C NARY CR)) compK)) cuGB
      = (finishLU (S := CSet) (Map := TreapMap mugF) n).map fun st => C (C st.toNoun OUT) (C NARY CR) := by
  have hcsi := csi_hit SCC (C CODE LSR) JH NARY CR OUT hs vals hv hg
  rw [← cu_csi_eq FUNC] at hcsi
  exact cu_gate FUNC SCC CODE LSR JH _ _ _ V n hpu h6 ht hcsi hgot hvn

end Compiler
end Formalization
