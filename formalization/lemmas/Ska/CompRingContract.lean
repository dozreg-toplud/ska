import lemmas.Ska.CompRingSem
import lemmas.Ska.CompRingRunEq

/-!
# The contract of code that calls through rings (track K, README Gaps 19 (h))

The code the compiler emits through rings runs as the code it would emit with no ring
(`execEntry_ringEq`, `CompRingSem.lean`), once the two compiles are related:

* `RingEraseU env nm`: `finishLUCMR env nm` and `finishLUCM env.noRing nm` both return or both
  fail, with the same need and argument count and blocks of the same erasures; `RingEraseF` the
  same for the n-ary final pass (`finishLFCR` / `finishLFC`).  STATED, checked on the 19 cases of
  `tools/hoon/ringdump.hoon` (`ringEraseMono`, `ringEraseNary` in `CompRingCheck.lean`, all
  true), not proved: it is a simulation of `runLCMR env` against `runLCMR env.noRing` through the
  primitives that read or rewrite blocks (`CompLazyRun.lean` lines 240, 370, 385, `addOps`).
* **`finishLUCMR_entry`**, **`finishLFCR_entry`**: under it, the ring code is entered as the
  no-ring code, on every oracle, state, arguments, trace and scry gate.  So every contract of
  `finishLUCM env.noRing nm` (tracks C, J) is one of `finishLUCMR env nm`: `env.noRing` keeps
  `need`, `sure`, `pure`, `cod`, `sof` (`noRing_need` and the like), which is all a contract
  reads of the environment besides `ring`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

theorem noRing_need (env : CallEnv) : env.noRing.need = env.need := rfl
theorem noRing_sure (env : CallEnv) : env.noRing.sure = env.sure := rfl
theorem noRing_pure (env : CallEnv) : env.noRing.pure = env.pure := rfl
theorem noRing_cod (env : CallEnv) : env.noRing.cod = env.cod := rfl
theorem noRing_sof (env : CallEnv) : env.noRing.sof = env.sof := rfl

/-- Two compile results related by the rings: both fail, or both return, with the same need,
argument count, and blocks of the same erasures. -/
def RingRel (a b : Option (Straight Map)) : Prop :=
  match a, b with
  | Option.none, Option.none => True
  | some cR, some c0 => cR.need = c0.need ∧ cR.nargs = c0.nargs ∧ RingSame cR c0
  | _, _ => False

/-- **`+compile-unary` through rings erases to the one without** (to prove; checked). -/
def RingEraseU (env : CallEnv) (nm : Nomm) : Prop :=
  RingRel (finishLUCMR (S := S) (Map := Map) env nm) (finishLUCM (S := S) (Map := Map) env.noRing nm)

/-- **The n-ary final pass through rings erases to the one without** (to prove; checked). -/
def RingEraseF (env : CallEnv) (nm : Nomm) (ord : NeedOrd) (less : Cape)
    (bake : Need → Need × List (Nat × Noun)) : Prop :=
  RingRel (finishLFCR (S := S) (Map := Map) env nm ord less bake)
    (finishLFC (S := S) (Map := Map) env.noRing nm ord less bake)

theorem ringRel_refl (a : Option (Straight Map)) : RingRel a a := by
  rcases a with _ | c
  · trivial
  · exact ⟨rfl, rfl, fun _ => rfl⟩

/-- **The ring code is entered as the no-ring code** (`+compile-unary`): under `RingEraseU`,
when `finishLUCMR env nm` returns `cR`, `finishLUCM env.noRing nm` returns `c0` with the same
need and argument count, and entering `cR` is entering `c0` on every oracle, state, arguments,
trace and scry gate. -/
theorem finishLUCMR_entry {env : CallEnv} {nm : Nomm} (h : RingEraseU (S := S) (Map := Map) env nm)
    {cR : Straight Map} (e : finishLUCMR (S := S) (Map := Map) env nm = some cR) :
    ∃ c0, finishLUCM (S := S) (Map := Map) env.noRing nm = some c0 ∧ cR.need = c0.need ∧ cR.nargs = c0.nargs ∧
      ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (st : σ) (vals : List Noun) (t : Trace) (gul : Noun),
        execEntry lib O st cR vals t gul = execEntry lib O st c0 vals t gul := by
  unfold RingEraseU at h
  rw [e] at h
  cases e0 : finishLUCM (S := S) (Map := Map) env.noRing nm with
  | none => rw [e0] at h; exact h.elim
  | some c0 =>
    rw [e0] at h
    exact ⟨c0, rfl, h.1, h.2.1, fun lib σ O st vals t gul => execEntry_ringEq h.2.2 st vals t⟩

/-- **The same for the n-ary final pass.** -/
theorem finishLFCR_entry {env : CallEnv} {nm : Nomm} {ord : NeedOrd} {less : Cape}
    {bake : Need → Need × List (Nat × Noun)} (h : RingEraseF (S := S) (Map := Map) env nm ord less bake)
    {cR : Straight Map} (e : finishLFCR (S := S) (Map := Map) env nm ord less bake = some cR) :
    ∃ c0, finishLFC (S := S) (Map := Map) env.noRing nm ord less bake = some c0 ∧ cR.need = c0.need ∧
      cR.nargs = c0.nargs ∧
      ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (st : σ) (vals : List Noun) (t : Trace) (gul : Noun),
        execEntry lib O st cR vals t gul = execEntry lib O st c0 vals t gul := by
  unfold RingEraseF at h
  rw [e] at h
  cases e0 : finishLFC (S := S) (Map := Map) env.noRing nm ord less bake with
  | none => rw [e0] at h; exact h.elim
  | some c0 =>
    rw [e0] at h
    exact ⟨c0, rfl, h.1, h.2.1, fun lib σ O st vals t gul => execEntry_ringEq h.2.2 st vals t⟩

/-- Under `RingEraseU`, the ring compile fails exactly when the no-ring one does. -/
theorem finishLUCMR_none {env : CallEnv} {nm : Nomm} (h : RingEraseU (S := S) (Map := Map) env nm)
    (e : finishLUCM (S := S) (Map := Map) env.noRing nm = Option.none) :
    finishLUCMR (S := S) (Map := Map) env nm = Option.none := by
  unfold RingEraseU at h
  rw [e] at h
  cases e1 : finishLUCMR (S := S) (Map := Map) env nm with
  | none => rfl
  | some _ => rw [e1] at h; exact h.elim

end Comp
end SkaModel
end Formalization
