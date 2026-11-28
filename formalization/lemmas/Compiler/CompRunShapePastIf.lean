import lemmas.Compiler.CompRunShapePastIfCut
import lemmas.Compiler.CompRunShapeTwo

/-!
# The link of `+laze-past-if` (track A, 2026-11-28)

`+laze-past-if` (door arm `0x57e`, cut in `CompRunShapePastIfCut.lean`) against `lazePastIf` of
`Ska/RunShape.lean`, at the door of `+run-shape` (`rsDoor`), exact, on every `laze` and every nomm
that is closed for `+sound-far` at depth `3` (`SfClosed env.cod 3 nom`: then `soundS` returns,
`soundFar_some`), with the code table `cod` at axis `52` of `ctx` holding `env.cod` (`CodeNomms`).

* `lpi_small`: the inline test `?=(?(~ [%1 ~ ~]) lok.sure.laz)` is `HoonSet.small`;
* `lpi_snd`: `(sound nom ned.sure.laz)` is `soundS`;
* **`lpi_gate`**: the gate is `lazePastIf`; `lazePastIf_some` (it returns), `lazePastIf_nz`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun}

/-- **The test of the looks of `+laze-past-if`** on the noun of a `laze` at axis `12`. -/
theorem lpi_small (bat rest D : Noun) (laz : Laze CSet) :
    nock (C bat (C (C laz.toNoun rest) D)) lpiSmall = some (loob (HoonSet.small laz.sure.lok)) := by
  obtain ⟨⟨ned, lok⟩, f, b⟩ := laz
  unfold lpiSmall
  rcases cs_small_cases lok with ⟨hsm, hl | hl⟩ | ⟨hsm, n, l, r, hl, hne⟩
  · simp [nock_exec, Laze.toNoun, SureO.toNoun, Laze.sure, eqCode_atom, eqCode, loob, hl, hsm]
  · simp [nock_exec, Laze.toNoun, SureO.toNoun, Laze.sure, eqCode_atom, eqCode, loob, hl, hsm]
  · rcases n with k | ⟨n1, n2⟩
    · by_cases hk : k = 1
      · subst hk
        rcases l with l | ⟨l1, l2⟩
        · by_cases hl0 : l = 0
          · subst hl0
            rcases r with r | ⟨r1, r2⟩
            · have hr0 : r ≠ 0 := fun e => hne ⟨rfl, rfl, by rw [e]⟩
              simp [nock_exec, Laze.toNoun, SureO.toNoun, Laze.sure, eqCode_atom, loob, hl, hsm, Ne.symm hr0]
            · simp [nock_exec, Laze.toNoun, SureO.toNoun, Laze.sure, eqCode_atom, eqCode, loob, hl, hsm]
          · simp [nock_exec, Laze.toNoun, SureO.toNoun, Laze.sure, eqCode_atom, loob, hl, hsm, Ne.symm hl0]
        · simp [nock_exec, Laze.toNoun, SureO.toNoun, Laze.sure, eqCode_atom, eqCode, loob, hl, hsm]
      · simp [nock_exec, Laze.toNoun, SureO.toNoun, Laze.sure, eqCode_atom, loob, hl, hsm, Ne.symm hk]
    · simp [nock_exec, Laze.toNoun, SureO.toNoun, Laze.sure, eqCode_atom, eqCode, loob, hl, hsm]

/-- `+laze-past-if` returns in the model when `soundS` does. -/
theorem lazePastIf_some (env : ShapeEnv) (laz : Laze CSet) (nom : Nomm) (hsf : SfClosed env.cod 3 nom)
    (st : RSt CSet) : ∃ r, lazePastIf env laz nom st = some r := by
  obtain ⟨s, hs⟩ := soundFar_some env.cod 3 nom hsf laz.sure.ned
  unfold lazePastIf
  cases hsm : HoonSet.small laz.sure.lok <;> cases s <;>
    simp [hsm, soundS, hs, shLiftS, bind, StateT.bind, pure, StateT.pure, idS]

section
variable (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
  (env : ShapeEnv) (hcn : CodeNomms env.cod cod)
include h7 hcode hcn

/-- **`(sound nom ned.sure.laz)`** of the gate: `soundS`, where it returns. -/
theorem lpi_snd (nom : Nomm) (st : RSt CSet) (y : RsRest) (laz : Laze CSet) (s : Bool)
    (hs : soundS env nom laz.sure.ned = some s) :
    nock (C lpiGate (C (C laz.toNoun nom.toNoun) (rsDoor st y ctx))) lpiSnd = some (loob s) := by
  obtain ⟨⟨ned, lok⟩, f, b⟩ := laz
  simp only [Laze.sure] at hs
  have hsq := rsd_snd h7 hcode (rsGenNoun st y) nom.toNoun ned.toNoun
  have hq := sf_gate env.cod cod hcn 3 nom ned s hs
  unfold lpiSnd
  simp [nock_exec, rsDoor, rsd_snd_at', snd_arm, hsq, hq, Laze.toNoun, SureO.toNoun]

/-- **`+laze-past-if` is `lazePastIf`** at the door of `+run-shape`, exact, on every `laze` and every
nomm closed for `+sound-far` at depth `3`. -/
theorem lpi_gate (nom : Nomm) (hsf : SfClosed env.cod 3 nom) (st : RSt CSet) (y : RsRest) (laz : Laze CSet) :
    nock (C lpiGate (C (C laz.toNoun nom.toNoun) (rsDoor st y ctx))) lpiGate
      = (lazePastIf env laz nom st).map fun p => C p.1.toNoun (rsGenNoun p.2 y) := by
  obtain ⟨s, hs⟩ := soundFar_some env.cod 3 nom hsf laz.sure.ned
  have hs' : soundS env nom laz.sure.ned = some s := hs
  have hsm := lpi_small lpiGate nom.toNoun (rsDoor st y ctx) laz
  have hsn := lpi_snd h7 hcode env hcn nom st y laz s hs'
  conv => { lhs; arg 2; unfold lpiGate }
  unfold lpiTest
  generalize lpiSmall = SM at hsm
  generalize lpiSnd = SN at hsn
  obtain ⟨sr, f, bd⟩ := laz
  cases hk : HoonSet.small sr.lok <;> cases s
  all_goals
    simp only [Laze.sure, Laze.toNoun, SureO.toNoun, rsDoor] at hk hs' hsm hsn
    simp [nock_exec, hsm, hsn, hk, hs', loob, lazePastIf, shLiftS, bind, StateT.bind, pure,
      StateT.pure, rsDoor, lpiNo, lzp_id_at', comp_id_at, idS, rs_id, Laze.toNoun, Laze.forksNoun,
      Laze.bondsNoun, SureO.toNoun, SureO.bunt, NeedOrd.toNoun, Tag.none, HoonSet.toNoun_empty, Laze.sure,
      Laze.fork, Laze.bond]

end

/-- The arm on the door gives the gate `lpiGate` (the call `[9 0x57e 0 63]` of the cases). -/
theorem lpi_door (y : Noun) : nock (C comp.door y) (C (A 9) (C (A 0x57e) (C (A 0) (A 1))))
    = some (C lpiGate (C lpiBunt (C comp.door y))) := by
  simp [nock_exec, lpi_at', lpiArm]

/-- **`+laze-past-if` keeps `LzNZ`.** -/
theorem lazePastIf_nz (env : ShapeEnv) (laz : Laze CSet) (nom : Nomm) (st : RSt CSet) (r : Laze CSet)
    (st1 : RSt CSet) (hl : LzNZ laz) (e : lazePastIf env laz nom st = some (r, st1)) : LzNZ r := by
  unfold lazePastIf at e
  obtain ⟨s, f, bd⟩ := laz
  obtain ⟨hs, hf, hb⟩ := hl
  cases hsm : HoonSet.small s.lok <;> simp only [Laze.sure, hsm, if_false, if_true] at e
  · simp [bind, StateT.bind, pure, StateT.pure, idS, Laze.fork, Laze.bond] at e
    rw [← e.1]
    exact ⟨fun y hy => absurd hy (HoonSet.mem_empty y), hf, ⟨hs, trivial, trivial⟩, hb⟩
  · cases e1 : soundS env nom s.ned with
    | none => simp [bind, StateT.bind, shLiftS, e1] at e
    | some k =>
      cases k
      · simp [bind, StateT.bind, shLiftS, e1, pure, StateT.pure, idS, Laze.fork, Laze.bond] at e
        rw [← e.1]
        exact ⟨fun y hy => absurd hy (HoonSet.mem_empty y), hf, ⟨hs, trivial, trivial⟩, hb⟩
      · simp [bind, StateT.bind, shLiftS, e1, pure, StateT.pure] at e
        rw [← e.1]
        exact ⟨hs, hf, hb⟩

end Compiler
end Formalization
