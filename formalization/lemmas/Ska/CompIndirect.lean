import lemmas.Ska.CompRunLCEq
import lemmas.Ska.CompRun
import lemmas.Ska.CompWholeTop

/-!
# The indirect call `[2 p q]`: the steps of its run

README Gaps 12.11 (the first step toward the first call theorem).  The case `%2` of `runLC` with no
callee information (`callL` with `info` `~`, lines 3900 to 3930 of
`nock-compilation.hoon`) is `+simple-next` of the goal, `+kerf` of it (the
hop block `out` and the product register `pro`), two fresh registers
`rSub` and `rFol`, the block `[%nok rSub rFol pro]` hopping to `out`, then
`q` for `%next (lazy-from-reg rFol)` into that block, `+past`, `p` for
`%next (lazy-from-reg rSub)` into the jump of `q`, and `+copy`.
`runLC_n2_none` takes a run of it apart into these steps, in the order the
run makes them, which is the order a proof of `SemCM` for the indirect call
follows: the runs of `p` and `q` are the fork-free `%next` runs that `OKNV`
of `FragU` covers, the `+kerf` block is `kern_spec`'s, and the `%nok` block
is `goJ_nok`'s.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The run of an indirect call, step by step.** -/
theorem runLC_n2_none {env : CallEnv} {sup : Option Nomm} {p q : Nomm} {goal : CGoalL S} {region : List Nat}
    {g0 g' : Gen Map} {nex : NextL S}
    (h : runLC env sup (Nomm.n2 p q Option.none) goal region g0 = some (nex, g')) :
    ∃ (nex0 : NextL S) (g1 : Gen Map) (out pro : Nat) (g2 : Gen Map) (o : Nat) (g3 : Gen Map)
      (nexF : NextL S) (g4 : Gen Map) (nexF' : NextL S) (g5 : Gen Map) (nexS : NextL S) (g6 : Gen Map),
      simpleNextL goal g0 = some (nex0, g1) ∧ kerf nex0 g1 = some ((out, pro), g2) ∧
      emit ⟨[], [Pole.nok g2.re (g2.re + 1) pro], Termin.hop (jmp0 out)⟩
        { { g2 with re := g2.re + 1 } with re := g2.re + 1 + 1 } = some (o, g3) ∧
      runLC env sup q (CGoalL.next (ofSure (lazyReg (g2.re + 1))) (jmp0 o)) region g3 = some (nexF, g4) ∧
      pastL env.cod nexF p region g4 = some (nexF', g5) ∧
      runLC env sup p (CGoalL.next (ofSure (lazyReg g2.re)) nexF'.th) region g5 = some (nexS, g6) ∧
      copyL nexS nexF'.laz g6 = some (nex, g') := by
  simp only [runLC, callL] at h
  obtain ⟨nex0, g1, h1, h⟩ := bind_some h
  obtain ⟨⟨out, pro⟩, g2, h2, h⟩ := bind_some h
  obtain ⟨rSub, ga, ha, h⟩ := bind_some h
  rw [re_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨rFol, gb, hb, h⟩ := bind_some h
  rw [re_apply] at hb
  simp only [Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  obtain ⟨o, g3, h3, h⟩ := bind_some h
  obtain ⟨nexF, g4, h4, h⟩ := bind_some h
  obtain ⟨nexF', g5, h5, h⟩ := bind_some h
  obtain ⟨nexS, g6, h6, h⟩ := bind_some h
  exact ⟨nex0, g1, out, pro, g2, o, g3, nexF, g4, nexF', g5, nexS, g6, h1, h2, h3, h4, h5, h6, h⟩

/-- **The first call theorem, stated** (not proved): the whole-subject code of
the indirect call `[2 p q]` with `p` and `q` in `FragU` meets the forward
half of the contract on the subject whole, against any needs.  With it,
`RawMono` holds on the class `FragUM` extended by such calls. -/
def IndirectTopFwd (lib : Lib) : Prop :=
  ∀ (code : Bell → Option Nomm) (bl : Bell) (p q : Nomm) (env : CallEnv) (c : Straight Map) (N : Needs),
    CodeOK lib code → Annot lib code (SkaModel.Fits bl.less) bl.fol (Nomm.n2 p q Option.none) →
    FragU (S := S) p → FragU (S := S) q → sixCount p + sixCount q ≤ 255 →
    finishLUC (S := S) env (Nomm.n2 p q Option.none) = some c →
    ∀ s, SkaModel.Fits bl.less s → ContractFwd lib N s bl.fol [s] c

end Comp
end SkaModel
end Formalization
