import lemmas.Compiler.CompRunShapeLeaf
import lemmas.Compiler.CompRunShapeFromCut
import lemmas.Compiler.CompFromGen

/-!
# The link of `+laze-from` (track A, 2026-11-27)

`+laze-from` (door arm `0x1576a`, cut in `CompRunShapeFromCut.lean`) against `lazeFrom` of
`Ska/RunShape.lean`, on every `laze` (forks and bonds to any depth) whose sure needs look at
no axis `0` (`LzNZ`), on every noun `G` of `gen` (the arm reads none of it).

**`LazeFromAt` of `CompRunShapeLeaf.lean` is false** at the door: on a look `0` the gate
`|=(x=@ (peg axe x))` of the `+run:in` runs `(peg axe 0)`, whose last case recurs on
`(div 0 2)` forever (the same as `+from-sure`, `CompFrom.lean`), while the model's
`setRun (pegF axe)` returns.  Witness: `axe = 2`, `laz = [[%none ~] [0 ~ ~]] ~ ~]`.  So
`rs_n0` and `rs_cls` hold vacuously.  The true statement is `LazeFromAtW` (with `LzNZ`),
proved here (`lazeFromAtW_door`); `rs_n0W` is the case `[0 a]` from it.

* `lf_arm`: the arm builds the gate `[lfGate lfBunt D]` on every core `D`.
* `lf_loop`: the trap down the axis is `fromOrd`.
* `lf_sur`: the `=/  sur` is `fromSureS`.
* **`lf_all`** (with `lf_forks`, `lf_bonds`): the gate is `lazeFrom`.
* **`lazeFromAtW_door`**, **`rs_n0W`**.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

mutual
/-- No sure need of the `laze` looks at axis `0`. -/
def LzNZ : Laze CSet → Prop
  | Laze.mk s f b => (∀ y ∈ HoonSet.toList s.lok, y ≠ 0) ∧ LzNZF f ∧ LzNZB b
def LzNZF : List ((Nat × Laze CSet) × (Nat × Laze CSet)) → Prop
  | [] => True
  | ((_, y), (_, n)) :: r => LzNZ y ∧ LzNZ n ∧ LzNZF r
def LzNZB : List (Nat × Laze CSet) → Prop
  | [] => True
  | (_, l) :: r => LzNZ l ∧ LzNZB r
end

/-- The noun of a fork entry. -/
noncomputable def lzfE (e : (Nat × Laze CSet) × (Nat × Laze CSet)) : Noun :=
  C (C (A e.1.1) e.1.2.toNoun) (C (A e.2.1) e.2.2.toNoun)

/-- The noun of a bond entry. -/
noncomputable def lzbE (e : Nat × Laze CSet) : Noun := C (A e.1) e.2.toNoun

theorem lz_forksNoun : ∀ f : List ((Nat × Laze CSet) × (Nat × Laze CSet)),
    Laze.forksNoun f = listN (f.map lzfE)
  | [] => rfl
  | ((oy, y), (on, n)) :: r => by
    simp only [Laze.forksNoun, List.map_cons, listN, appendN_cons, lzfE]
    rw [lz_forksNoun r]; rfl

theorem lz_bondsNoun : ∀ b : List (Nat × Laze CSet), Laze.bondsNoun b = listN (b.map lzbE)
  | [] => rfl
  | (o, l) :: r => by
    simp only [Laze.bondsNoun, List.map_cons, listN, appendN_cons, lzbE]
    rw [lz_bondsNoun r]; rfl

theorem lz_toNoun_mk (s : SureO CSet) (f b) :
    (Laze.mk s f b).toNoun = C s.toNoun (C (listN (f.map lzfE)) (listN (b.map lzbE))) := by
  simp only [Laze.toNoun, lz_forksNoun, lz_bondsNoun]

/-- The arm builds its gate. -/
theorem lf_arm (d : Noun) : nock d lfArm = some (C lfGate (C lfBunt d)) := by
  unfold lfArm lfHint; simp only [nock_exec]

theorem lfPeg_eq : lfPeg = cfPegBat := rfl

/-- The trap of the `=/  sur` down the axis, on the core `[lfLoop ned S]`. -/
theorem lf_loop (hc : CompIn ctx) (L G : Noun) (ned : NeedOrd) :
    ∀ axe, 1 ≤ axe →
    nock (C lfLoop (C ned.toNoun (C lfGate (C (C (A axe) L) (C comp.door (C G ctx)))))) lfLoop
      = (fromOrd axe ned).map NeedOrd.toNoun := by
  have hl1 := cf_layer1 hc
  have har := cf_arith
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
    intro ha
    by_cases a1 : axe = 1
    · subst a1
      nock_open lfLoop
      rw [fromOrd.eq_def]
      simp [nock_exec]
    · have h2 : 2 ≤ axe := by omega
      have hcap := cap_gate layer1 har.2.2.2 axe h2
      have hmas := mas_gate layer1 har axe h2
      have hm1 : 1 ≤ masF axe := masF_pos axe h2
      have ihm := ih (masF axe) (by rw [masF_eq_mas]; exact mas_lt axe h2) hm1
      have hne : ¬ (1 = axe) := by omega
      nock_open lfLoop
      rw [fromOrd.eq_def]
      rcases capF_cases axe h2 with hc2 | hc3
      · simp [nock_exec, hl1, hne, a1, cap_arm, cap.arm_at, hcap, hc2, mas_arm, mas.arm_at, hmas, ihm,
          show ¬ axe = 0 by omega, ← capF_eq_cap, ← masF_eq_mas, NeedOrd.toNoun, Tag.none]
        cases fromOrd (masF axe) ned <;> simp [NeedOrd.toNoun, Tag.none]
      · simp [nock_exec, hl1, hne, a1, cap_arm, cap.arm_at, hcap, hc3, mas_arm, mas.arm_at, hmas, ihm,
          show ¬ axe = 0 by omega, ← capF_eq_cap, ← masF_eq_mas, NeedOrd.toNoun, Tag.none]
        cases fromOrd (masF axe) ned <;> simp [NeedOrd.toNoun, Tag.none]

theorem no_cell : ∀ n : NeedOrd, ∃ a b, n.toNoun = C a b
  | NeedOrd.pair p q => ⟨_, _, rfl⟩
  | NeedOrd.both h t => ⟨_, _, rfl⟩
  | NeedOrd.this => ⟨_, _, rfl⟩
  | NeedOrd.none => ⟨_, _, rfl⟩

/-- The `=/  sur`: `fromSureS`, for an axis not `0` and no look at `0`. -/
theorem lf_sur (hc : CompIn ctx) (G FB : Noun) (axe : Nat) (ha : 1 ≤ axe) (s : SureO CSet)
    (h0 : ∀ y ∈ HoonSet.toList s.lok, y ≠ 0) :
    nock (C lfGate (C (C (A axe) (C s.toNoun FB)) (C comp.door (C G ctx)))) lfSur
      = (fromSureS axe s).map SureO.toNoun := by
  obtain ⟨ned, lok⟩ := s
  simp only at h0
  have hr : nock (C in.run.battery (C (C cfPegBat (C (A 0) (C lfGate (C (C (A axe)
      (C (C ned.toNoun (HoonSet.toNoun lok)) FB)) (C comp.door (C G ctx)))))) (C in.battery
      (C (HoonSet.toNoun lok) layer2)))) in.run.battery = some (HoonSet.toNoun (setRun (pegF axe) lok)) := by
    refine cs_run_in_gate_on layer2 cs_inIn_layer2 _ _ _ (csLift (pegF axe)) _ (cs_tree lok)
      (fun n hn => ?_) _ (cs_runInF _ lok)
    rw [cs_preorder] at hn
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hn
    exact cf_peg_gate hc _ G _ axe y ha (Nat.pos_of_ne_zero (h0 y hy))
  have hl := lf_loop hc (C (C ned.toNoun (HoonSet.toNoun lok)) FB) G ned axe ha
  simp only [cfPegBat] at hr
  simp only [SureO.toNoun]
  have a0 : ¬ axe = 0 := by omega
  have ha0 : ¬ (0 = axe) := fun h => a0 h.symm
  cases ned with
  | none =>
    simp only [NeedOrd.toNoun, Tag.none] at hr hl
    by_cases a1 : axe = 1
    · subst a1
      unfold lfSur; simp [nock_exec, fromSureS, NeedOrd.toNoun, Tag.none]
    have ha1 : ¬ (1 = axe) := fun h => a1 h.symm
    by_cases he : HoonSet.toList lok = []
    · have hn := (cs_toNoun_nil lok).2 he
      have hi : HoonSet.isEmpty lok = true := (HoonSet.isEmpty_iff lok).2 he
      unfold lfSur
      simp [nock_exec, fromSureS, NeedOrd.toNoun, Tag.none, hn, ha0, ha1, a0, a1, hi, cs_setOne,
        SureO.toNoun]
    · have hn : ¬ (A 0 = HoonSet.toNoun lok) := fun h => he ((cs_toNoun_nil lok).1 h.symm)
      have hi : HoonSet.isEmpty lok = false := by
        cases e : HoonSet.isEmpty lok
        · rfl
        · exact absurd ((HoonSet.isEmpty_iff lok).1 e) he
      unfold lfSur lfRl
      simp [nock_exec, fromSureS, NeedOrd.toNoun, Tag.none, hn, ha0, ha1, a0, a1, hi, hc, in_arm,
        in.arm_at, in.run.arm_at, cs_run_in_arm, hr, lfPeg_eq, cfPegBat, SureO.toNoun]
  | pair p q =>
    obtain ⟨a, b, hp⟩ := no_cell p
    have hl' := hl
    simp only [NeedOrd.toNoun, hp] at hr hl'
    unfold lfSur lfRl
    simp [nock_exec, fromSureS, NeedOrd.toNoun, hp, Tag.none, ha0, a0, hc, in_arm, in.arm_at,
      in.run.arm_at, cs_run_in_arm, hr, hl', lfPeg_eq, cfPegBat, SureO.toNoun]
    cases fromOrd axe _ <;> simp [SureO.toNoun]
  | both h t =>
    simp only [NeedOrd.toNoun, Tag.both] at hr hl
    unfold lfSur lfRl
    simp [nock_exec, fromSureS, NeedOrd.toNoun, Tag.none, Tag.both, ha0, a0, hc, in_arm, in.arm_at,
      in.run.arm_at, cs_run_in_arm, hr, hl, lfPeg_eq, cfPegBat, SureO.toNoun]
    cases fromOrd axe _ <;> simp [SureO.toNoun]
  | this =>
    simp only [NeedOrd.toNoun, Tag.this] at hr hl
    unfold lfSur lfRl
    simp [nock_exec, fromSureS, NeedOrd.toNoun, Tag.none, Tag.this, ha0, a0, hc, in_arm, in.arm_at,
      in.run.arm_at, cs_run_in_arm, hr, hl, lfPeg_eq, cfPegBat, SureO.toNoun]
    cases fromOrd axe _ <;> simp [SureO.toNoun]

/-- The fork gate of the `+turn`, in the model. -/
noncomputable def lzfFork (axe : Nat) (e : (Nat × Laze CSet) × (Nat × Laze CSet)) :
    Option ((Nat × Laze CSet) × (Nat × Laze CSet)) :=
  (lazeFrom axe e.1.2).bind fun y' => (lazeFrom axe e.2.2).map fun n' => ((e.1.1, y'), (e.2.1, n'))

/-- The bond gate of the `+turn`, in the model. -/
noncomputable def lzfBond (axe : Nat) (e : Nat × Laze CSet) : Option (Nat × Laze CSet) :=
  (lazeFrom axe e.2).map fun l' => (e.1, l')

theorem lzf_fromF (axe : Nat) : ∀ fk : List ((Nat × Laze CSet) × (Nat × Laze CSet)),
    fromF axe fk = fk.mapM (lzfFork axe)
  | [] => rfl
  | ((oy, y), (on, n)) :: rest => by
    simp only [fromF, List.mapM_cons, lzfFork, lzf_fromF axe rest]
    cases lazeFrom axe y <;> cases lazeFrom axe n <;> cases rest.mapM (lzfFork axe) <;> rfl

theorem lzf_fromB (axe : Nat) : ∀ bd : List (Nat × Laze CSet), fromB axe bd = bd.mapM (lzfBond axe)
  | [] => rfl
  | (ob, l) :: rest => by
    simp only [fromB, List.mapM_cons, lzfBond, lzf_fromB axe rest]
    cases lazeFrom axe l <;> cases rest.mapM (lzfBond axe) <;> rfl

section
variable (hc : CompIn ctx) (G : Noun) (axe : Nat)
include hc

mutual
/-- **`+laze-from` on every `laze`** (forks and bonds to any depth) whose sure needs look at
no axis `0`: `lazeFrom axe`, on every noun `G` of `gen`. -/
theorem lf_all : ∀ (laz : Laze CSet), LzNZ laz →
    nock (C lfGate (C (C (A axe) laz.toNoun) (C comp.door (C G ctx)))) lfGate
      = (lazeFrom axe laz).map Laze.toNoun
  | Laze.mk s fk bd, ⟨hs, hfk, hbd⟩ => by
    rw [lz_toNoun_mk]
    by_cases a0 : axe = 0
    · subst a0
      conv => { lhs; arg 2; unfold lfGate }
      simp [nock_exec, lazeFrom]
    have ha : 1 ≤ axe := Nat.pos_of_ne_zero a0
    have ha0 : ¬ (0 = axe) := fun h => a0 h.symm
    have hf := lf_sur hc G (C (listN (fk.map lzfE)) (listN (bd.map lzbE))) axe ha s hs
    have tF := lz_test lzfE fk
    have tB := lz_test lzbE bd
    conv => { lhs; arg 2; unfold lfGate }
    cases e1 : fromSureS axe s with
    | none =>
      rw [e1] at hf
      simp [nock_exec, hf, lazeFrom, e1, a0, ha0]
    | some s' =>
      rw [e1] at hf
      have hFk := turn_gate_mapT lzfE lzfE layer2 homoIn_layer2 lfGF (C lfBunt lfBunt)
        (C s'.toNoun (C lfGate (C (C (A axe) (C s.toNoun (C (listN (fk.map lzfE)) (listN (bd.map lzbE)))))
          (C comp.door (C G ctx))))) (lzfFork axe) fk (fun e he => lf_forks fk hfk e he _ _)
      have hBd := turn_gate_mapT lzbE lzbE layer2 homoIn_layer2 lfGB lfBunt
        (C s'.toNoun (C lfGate (C (C (A axe) (C s.toNoun (C (listN (fk.map lzfE)) (listN (bd.map lzbE)))))
          (C comp.door (C G ctx))))) (lzfBond axe) bd (fun e he => lf_bonds bd hbd e he _ _)
      rcases tF with ⟨t1, t2, t3⟩ | ⟨t1, t2, t3⟩ <;> rcases tB with ⟨t4, t5, t6⟩ | ⟨t4, t5, t6⟩ <;>
      · first | replace t1 := eq_false t1 | replace t1 := eq_true t1
        first | replace t4 := eq_false t4 | replace t4 := eq_true t4
        cases e2 : fk.mapM (lzfFork axe) with
        | none =>
          rw [e2] at hFk
          simp [nock_exec, hf, lazeFrom, e1, a0, ha0, t1, t2, t3, t4, t5, t6, List.isEmpty_iff, lfBody,
            hc, turn.arm_at, turn_arm, hFk, lzf_fromF, e2, lz_toNoun_mk]
        | some f' =>
          rw [e2] at hFk
          cases e3 : bd.mapM (lzfBond axe) with
          | none =>
            rw [e3] at hBd
            simp [nock_exec, hf, lazeFrom, e1, a0, ha0, t1, t2, t3, t4, t5, t6, List.isEmpty_iff, lfBody,
              hc, turn.arm_at, turn_arm, hFk, hBd, lzf_fromF, lzf_fromB, e2, e3, lz_toNoun_mk]
          | some b' =>
            rw [e3] at hBd
            simp [nock_exec, hf, lazeFrom, e1, a0, ha0, t1, t2, t3, t4, t5, t6, List.isEmpty_iff, lfBody,
              hc, turn.arm_at, turn_arm, hFk, hBd, lzf_fromF, lzf_fromB, e2, e3, lz_toNoun_mk]

theorem lf_forks : ∀ (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet))), LzNZF fk → ∀ e ∈ fk, ∀ X L : Noun,
    nock (C lfGF (C (lzfE e) (C X (C lfGate (C (C (A axe) L) (C comp.door (C G ctx))))))) lfGF
      = (lzfFork axe e).map lzfE
  | [], _, e, he => absurd he List.not_mem_nil
  | ((oy, y), (on, n)) :: rest, ⟨hy, hn, hr⟩, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro X L
      have ihy := lf_all y hy
      have ihn := lf_all n hn
      unfold lfGF
      cases e1 : lazeFrom axe y with
      | none => rw [e1] at ihy; simp [nock_exec, lzfE, ihy, lzfFork, e1, lf_at, lf_at', lf_arm]
      | some y' =>
        rw [e1] at ihy
        cases e2 : lazeFrom axe n with
        | none => rw [e2] at ihn; simp [nock_exec, lzfE, ihy, ihn, lzfFork, e1, e2, lf_at, lf_at', lf_arm]
        | some n' => rw [e2] at ihn; simp [nock_exec, lzfE, ihy, ihn, lzfFork, e1, e2, lf_at, lf_at', lf_arm]
    · exact lf_forks rest hr e he'

theorem lf_bonds : ∀ (bd : List (Nat × Laze CSet)), LzNZB bd → ∀ e ∈ bd, ∀ X L : Noun,
    nock (C lfGB (C (lzbE e) (C X (C lfGate (C (C (A axe) L) (C comp.door (C G ctx))))))) lfGB
      = (lzfBond axe e).map lzbE
  | [], _, e, he => absurd he List.not_mem_nil
  | (ob, l) :: rest, ⟨hl, hr⟩, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro X L
      have ihl := lf_all l hl
      unfold lfGB
      cases e1 : lazeFrom axe l with
      | none => rw [e1] at ihl; simp [nock_exec, lzbE, ihl, lzfBond, e1, lf_at, lf_at', lf_arm]
      | some l' => rw [e1] at ihl; simp [nock_exec, lzbE, ihl, lzfBond, e1, lf_at, lf_at', lf_arm]
    · exact lf_bonds rest hr e he'
end

end

end Compiler
end Formalization
