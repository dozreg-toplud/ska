import lemmas.Compiler.SkaJointConv

/-!
# `+ska-callgraph` against `Ana.skaCallgraph`

The gate `+ska-callgraph` (arm `341` of `ana`, `ska_cg.arm`, battery
`ska_cg.battery`) on the sample `[[bus fol] memo-final reg]` with the context
`ana`.  Its battery is split by the kernel (`cg_battery_eq`):
`[8 [1 st-bunt] [7 [10 [1534 [0 59]] [0 1]] [8 [1 K_bat] [8 cgA cgT]]]]`,
the bunt of `ska-state` with `regs` edited, the core `K` (`cgK`), the call
`cgA` of `+analyze` on the root, which `analyze_iff` gives, and the print
`cgT`: the gate `print-ska` at axis `254` of `ana` (`cg_ps_at`), whose battery
`[9 97710 [0 255]]` pulls the arm `same` of layer 2 (`same_at`), because
`ska-verb` is not defined, so the trap of the print (`cgTrap`, kept whole: it
quotes the type of the result) never runs, and `same` returns
`[g.st.res regs.st.res]`.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon SkaModel.Ana

variable {R : Type}

set_option linter.unusedSimpArgs false

/-! ## The pieces of the battery -/

/-- The trap `|.` of the print of `+ska-callgraph`, kept whole. -/
noncomputable def cgTrap : Noun := (slot? 8384445 ska_cg.battery).getD (A 0)

/-- The bunt of `ska-state`: eight `~` and the bunts of `regs` and `stats`. -/
def cgStBunt : Noun :=
  C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0)
    (C (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0)))))))))))))

/-- The call of `+analyze` on `[[bus fol] st]`. -/
def cgA : Noun :=
  C (A 8) (C (C (A 9) (C (A 92) (C (A 0) (A 1))))
    (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 120)) (C (A 0) (A 121)))))
      (C (A 0) (A 14)))) (C (A 0) (A 2)))))))

/-- The print: `print-ska` slammed with `[0 trap]`, and what it returns
slammed with `[g.st.res regs.st.res]`, for any trap `t`. -/
def cgTF (t : Noun) : Noun :=
  C (A 8) (C (C (A 8) (C (C (A 0) (A 8190)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6)
      (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) t) (C (A 0) (A 1)))))))
      (C (A 0) (A 2))))))))
    (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 10)) (C (A 0) (A 3070))))))
      (C (A 0) (A 2)))))))

/-- The print of `+ska-callgraph`. -/
noncomputable def cgT : Noun := cgTF cgTrap

theorem cg_battery_eq : ska_cg.battery =
    C (A 8) (C (C (A 1) cgStBunt) (C (A 7) (C (C (A 10) (C (C (A 1534) (C (A 0) (A 59))) (C (A 0) (A 1))))
      (C (A 8) (C (C (A 1) ska_cg.k_bat) (C (A 8) (C cgA cgT))))))) := by kernel_rfl

/-! ## `print-ska` and `same` -/

/-- The sample of the gate `print-ska`. -/
noncomputable def psSam : Noun := (slot? 1018 ana).getD (A 0)

/-- The context of the gate `print-ska`. -/
noncomputable def psCtx : Noun := (slot? 1019 ana).getD (A 0)

theorem cg_ps_at : slot? 254 ana = some (C (C (A 9) (C (A 97710) (C (A 0) (A 255)))) (C psSam psCtx)) := by kernel_rfl

theorem ps_ctx_l2 : slot? 63 psCtx = some layer2 := by kernel_rfl

/-- The arm `same` of layer 2, `|*(* +<)`. -/
def sameArm : Noun := C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) (C (A 0) (A 6))) (C (A 0) (A 1))))

theorem same_at : slot? 97710 layer2 = some sameArm := by kernel_rfl

/-- **The print** returns `[g.st.res regs.st.res]`, whatever the trap, for a
gate `print-ska` whose battery pulls `same` from its context. -/
theorem cg_print (S sam ctx l2 t : Noun)
    (h : slot? 8190 S = some (C (C (A 9) (C (A 97710) (C (A 0) (A 255)))) (C sam ctx)))
    (hc : slot? 63 ctx = some l2) (hs : slot? 97710 l2 = some sameArm) :
    nock S (cgTF t) = (slot? 10 S).bind fun a => (slot? 3070 S).bind fun b => some (C a b) := by
  unfold cgTF
  simp only [nock_exec, h, Option.bind_some, hc, hs]
  unfold sameArm
  simp only [nock_exec, Option.bind_some]
  cases h10 : slot? 10 S <;> cases h3070 : slot? 3070 S <;> simp [nock_exec]

theorem slot8190 (a b c d e X : Noun) :
    slot? 8190 (C a (C b (C c (C d (C e X))))) = slot? 254 X := by
  simp only [nock_exec]

/-! ## The core `K` and the run -/

/-- The sample of `+ska-callgraph`: `[[bus fol] memo-final reg]`. -/
noncomputable def cgSam (regsNoun : R → Noun) (root : Ident) (memoF : Memo FinMap) (reg : R) : Noun :=
  C (identNoun root) (C (memoNoun memoF) (regsNoun reg))

/-- The core `K` that the gate builds. -/
noncomputable def cgK (regsNoun : R → Noun) (root : Ident) (memoF : Memo FinMap) (reg : R) : Noun :=
  C ska_cg.k_bat (C ((SkaState.init (M := FinMap) reg).toNoun regsNoun)
    (C ska_cg.battery (C (cgSam regsNoun root memoF reg) ana)))

/-- `stats` of the bunt of `ska-state`. -/
def stats0 : Noun := C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))

theorem init_toNoun (regsNoun : R → Noun) (reg : R) :
    (SkaState.init (M := FinMap) reg).toNoun regsNoun =
      C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0)
        (C (regsNoun reg) stats0)))))))) := by
  simp only [SkaState.toNoun, SkaState.init, memoNoun, Stats.toNoun]
  show C (FinMap.toNoun _ FinMap.empty) (C (FinMap.toNoun _ FinMap.empty) (C (FinMap.toNoun _ FinMap.empty)
    (C (A 0) (C (A 0) (C (FinMap.setNoun FinMap.empty) (C (A 0) (C (FinMap.toNoun _ FinMap.empty) _))))))) = _
  rw [FinMap.toNoun_empty, FinMap.toNoun_empty, FinMap.toNoun_empty, FinMap.setNoun_empty,
    FinMap.toNoun_empty]
  rfl

theorem cgK_31 (regsNoun : R → Noun) (root : Ident) (memoF : Memo FinMap) (reg : R) :
    slot? 31 (cgK regsNoun root memoF reg) = some ana := rfl

theorem cgK_2 (regsNoun : R → Noun) (root : Ident) (memoF : Memo FinMap) (reg : R) :
    slot? 2 (cgK regsNoun root memoF reg) = some ska_cg.k_bat := rfl

theorem cgK_122 (regsNoun : R → Noun) (root : Ident) (memoF : Memo FinMap) (reg : R) :
    slot? 122 (cgK regsNoun root memoF reg) = some (memoNoun memoF) := by
  unfold cgK cgSam; simp only [nock_exec]

/-- The battery of `+ska-callgraph` is the call of `+analyze` on the root and
the initial state in the core `cgK`, then the print. -/
theorem cg_run (regsNoun : R → Noun) (root : Ident) (memoF : Memo FinMap) (reg : R) :
    nock (C ska_cg.battery (C (cgSam regsNoun root memoF reg) ana)) ska_cg.battery =
      (nock (anaSubj regsNoun (cgK regsNoun root memoF reg) root (SkaState.init reg)) ska_analyze.battery).bind
        fun x => nock (C x (cgK regsNoun root memoF reg)) cgT := by
  conv => lhs; arg 2; rw [cg_battery_eq]
  unfold cgK anaSubj cgA
  rw [init_toNoun]
  unfold cgSam identNoun cgStBunt stats0
  simp only [nock_exec, Option.bind_some, kc_analyze_at, ska_analyze_arm]

/-- The print on a result of `+analyze`. -/
theorem cg_print_ana (regsNoun : R → Noun) (root : Ident) (memoF : Memo FinMap) (reg : R)
    (r : Nat × SkaState FinMap R) :
    nock (C (anaNoun regsNoun r) (cgK regsNoun root memoF reg)) cgT =
      some (C (Treap.toNoun FDatum.toNoun r.2.g) (regsNoun r.2.regs)) := by
  unfold cgT
  rw [cg_print _ psSam psCtx layer2 _ (by unfold cgK; rw [slot8190, cg_ps_at]) ps_ctx_l2 same_at]
  unfold anaNoun SkaState.toNoun
  simp only [nock_exec, Option.bind_some]

section
variable (regsNoun : R → Noun) (env : Env R)
  (hhe : env.he = heSock) (hth : env.threshold = 32) (hsoft : env.softSpot = softSpotF)
  (hreg : RegisterFastIs regsNoun env)
include hhe hth hsoft hreg

/-- **`+ska-callgraph`**: the pill's gate on the sample
`[[bus fol] memo-final reg]` in its context `ana` returns exactly
`[g regs]` of what `Ana.skaCallgraph` returns at some fuel. -/
theorem ska_callgraph_iff (root : Ident) (memoF : Memo FinMap) (reg : R) (y : Noun) :
    nock (C ska_cg.battery (C (cgSam regsNoun root memoF reg) ana)) ska_cg.battery = some y ↔
      ∃ r m, Ana.skaCallgraph env m root memoF reg = some r ∧
        y = C (Treap.toNoun FDatum.toNoun r.1) (regsNoun r.2) := by
  rw [cg_run]
  have hA := analyze_iff regsNoun env memoF (cgK regsNoun root memoF reg) (cgK_31 _ _ _ _) (cgK_2 _ _ _ _)
    (cgK_122 _ _ _ _) hhe hth hsoft hreg root (SkaState.init reg)
  constructor
  · intro h
    obtain ⟨x, hx, hy⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r, m, hr, rfl⟩ := (hA x).1 hx
    rw [cg_print_ana] at hy
    refine ⟨(r.2.g, r.2.regs), m, ?_, (Option.some.inj hy).symm⟩
    unfold Ana.skaCallgraph
    rw [hr]; rfl
  · rintro ⟨r', m, hr', rfl⟩
    unfold Ana.skaCallgraph at hr'
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 hr'
    rw [(hA _).2 ⟨r, m, hr, rfl⟩, Option.bind_some, cg_print_ana]

end

end Compiler
end Formalization
