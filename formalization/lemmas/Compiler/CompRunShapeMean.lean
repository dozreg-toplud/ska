import lemmas.Compiler.CompRunShapeMeanCut
import lemmas.Compiler.CompRunShapeMeanKCut
import lemmas.Compiler.CompRunShapeEleven

/-!
# `+run-shape`: the case `[%mean p b q body k]` (track A, 2026-11-28)

The case `rsKmean` (`rsmArm`, cut in `CompRunShapeMeanCut.lean`) against `runShape` on `Nomm.mean`,
on `RsAtE`.  Its parts: `+laze-past-if` of `simple` over `q` (`lpi_gate`: `q` closed for
`+sound-far`), the run of `q`, `+id`, the bond `l-fol`; `ned` (`rsmNed`): `+mean-konst` (`rmk_gate`,
door arm `0x17c`, which reads `pure` of the code entry of `b`), `[%none ~]` on a konst, else
`+callee-need` (read at the rests of `E` as `ShapeCall.need` reads it); `l-arg` (`rsmArg`): `[ned ~]`
when `(sound p ned)` (`p` closed for `+sound-far`), else a bond with a new identifier put in `sofs`;
the run of `p` on `l-arg` and `+laze-copy` (`rsmEnd`).

* `rs_disp_mean`, `rsKmean_eq`, **`rmk_gate`** (`+mean-konst`);
* `MeanNeed`: what the case reads of `+callee-need`;
* **`rs_nmeanE`**: the case; `meanNz`: it keeps `LzNZ`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun} {E : RsRest → Prop}

theorem rs_disp_mean (t s goal sup D : Noun) :
    nock (rsS s (C (A Tag.mean) t) goal sup D) rsDol = nock (rsS s (C (A Tag.mean) t) goal sup D) rsKmean := by
  nock_open rsDol
  simp [nock_exec, rsS, rsCoreG, rsTc, rsT, Tag.mean]

theorem rsKmean_eq : rsKmean = rsmArm := by simp [rsKmean, rsm_at]

/-- The code entry of `b` gives `pure` when the key is a `^` (what `+mean-konst` reads). -/
def MeanPure (cod : Noun) (env : ShapeEnv) (b : Bell) (k : Option Noun) : Prop :=
  k ≠ Option.none → ∃ V pu, getF mugF b.toNoun cod = some (C (A 0) V) ∧ slot? 6 V = some (loob pu) ∧
    env.pure b = some pu

/-- **`+mean-konst`** at the door of `+run-shape`: `~` on `k` `~` or a callee that is not `pure`,
else `k` (`meanKonstS` says which). -/
theorem rmk_gate (hc : CompIn ctx) {cod : Noun} (hcode : slot? 52 ctx = some cod) (env : ShapeEnv) (b : Bell)
    (k : Option Noun) (hmp : MeanPure cod env b k) (G : Noun) :
    nock (C rmkGate (C (C b.toNoun (unitNoun id k)) (C comp.door (C G ctx)))) rmkGate
      = (meanKonstS env b k).map fun kon => if kon then unitNoun id k else A 0 := by
  rcases k with _ | n
  · simp [rmkGate, nock_exec, unitNoun, meanKonstS]
  · obtain ⟨V, pu, hgot, hv, hpu⟩ := hmp (by simp)
    have hgt := got_gate (mug := mugF) layer2 ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ b.toNoun cod V hgot
    have hc' : slot? 262143 ctx = some layer2 := hc
    cases pu <;>
      simp [rmkGate, nock_exec, unitNoun, meanKonstS, hpu, hc', hcode, by.arm_at, by_arm, by.got.arm_at, got_arm,
        hgt, hv, loob]

/-- **What the case reads of `+callee-need`** at the rest `y`, when the key is not a konst:
`env.need b`, with `gen` unchanged. -/
def MeanNeed (ctx : Noun) (env : ShapeEnv) (b : Bell) (k : Option Noun) (y : RsRest) : Prop :=
  meanKonstS env b k = some false → ∃ nb, env.need b = some nb ∧ ∀ st : RSt CSet,
    nock (C cneBat (C b.toNoun (rsDoor st y ctx))) cneBat = some (C nb.toNoun (rsGenNoun st y))

/-- `l-arg` of the case, in the model. -/
noncomputable def rsmArgM (env : ShapeEnv) (p : Nomm) (ned : NeedOrd) : SM CSet (Laze CSet) := do
  let snd ← shLiftS (soundS env p ned)
  if snd then pure (nedL ned) else do
    let j ← idS
    putSofs j
    pure (Laze.mk SureO.bunt [] [(j, nedL ned)])

/-- `ned` of the case, in the model. -/
noncomputable def rsmNedM (env : ShapeEnv) (b : Bell) (k : Option Noun) : SM CSet NeedOrd := do
  let kon ← shLiftS (meanKonstS env b k)
  if kon then pure NeedOrd.none else shLiftS (env.need b)

/-- The model's case in these parts. -/
theorem runShape_mean (env : ShapeEnv) (sup : Option Nomm) (p : Nomm) (b : Bell) (q : Nomm) (body : Noun)
    (k : Option Noun) (goal : GoalS CSet) :
    runShape env sup (Nomm.mean p b q body k) goal = (do
      let gol ← lazePastIf env (simpleS goal) q
      let lf ← runShape env sup q (GoalS.next gol)
      let i ← idS
      let ned ← rsmNedM env b k
      let la ← rsmArgM env p ned
      let lt ← runShape env sup p (GoalS.next la)
      shLiftS (lazeCopy lt (Laze.mk SureO.bunt [] [(i, lf)])) : SM CSet (Laze CSet)) := by
  rw [runShape]; simp only [rsmNedM, rsmArgM, bind_assoc]

theorem lzNZ_argM (env : ShapeEnv) (p : Nomm) (ned : NeedOrd) (st : RSt CSet) (la : Laze CSet) (st1 : RSt CSet)
    (e : rsmArgM env p ned st = some (la, st1)) : LzNZ la := by
  unfold rsmArgM at e
  obtain ⟨snd, s1, e1, e⟩ := sm_bind_some e
  cases snd
  · simp [bind, StateT.bind, idS, putSofs, pure, StateT.pure] at e
    rw [← e.1]; exact lzNZ_softL _ ned
  · simp [pure, StateT.pure] at e
    rw [← e.1]; exact lzNZ_nedL ned

/-- **The case `[%mean p b q body k]` keeps `LzNZ`**, given that the runs of `p` and `q` do. -/
theorem meanNz (env : ShapeEnv) (p : Nomm) (b : Bell) (q : Nomm) (body : Noun) (k : Option Noun)
    (sup : Option Nomm) (goal : GoalS CSet) (hg : GoalNZ goal)
    (hrp : ∀ g st l st1, GoalNZ g → runShape env sup p g st = some (l, st1) → LzNZ l)
    (hrq : ∀ g st l st1, GoalNZ g → runShape env sup q g st = some (l, st1) → LzNZ l)
    (st : RSt CSet) (l : Laze CSet) (st1 : RSt CSet)
    (e : runShape env sup (Nomm.mean p b q body k) goal st = some (l, st1)) : LzNZ l := by
  rw [runShape_mean] at e
  obtain ⟨gol, s1, e1, e⟩ := sm_bind_some e
  obtain ⟨lf, s2, e2, e⟩ := sm_bind_some e
  obtain ⟨i, s3, e3, e⟩ := sm_bind_some e
  obtain ⟨ned, s4, e4, e⟩ := sm_bind_some e
  obtain ⟨la, s5, e5, e⟩ := sm_bind_some e
  obtain ⟨lt, s6, e6, e⟩ := sm_bind_some e
  have hf := hrq (GoalS.next gol) _ _ _ (lazePastIf_nz env _ q st gol s1 (simpleS_nz goal hg) e1) e2
  have hb : LzNZ (Laze.mk SureO.bunt [] [(i, lf)] : Laze CSet) :=
    ⟨fun y hy => absurd hy (HoonSet.mem_empty y), trivial, hf, trivial⟩
  exact lazeCopyEnd_nz (hrp (GoalS.next la) _ _ _ (lzNZ_argM env p ned _ la s5 e5) e6) hb e

end Compiler
end Formalization
