import lemmas.Ska.CompSixLSR
import lemmas.Ska.CompNaryTopDirect

/-!
# The tail call of `R` as a branch: `DoneE` from track J's `tailN_done`

README Gaps 12.35.  `doneE_tailN`: the n-ary direct call `[2 p q b]` under
`%done` meets `DoneE` under the hypotheses of `tailN_done` and `NoEnt p`:
`DoneOK` is `tailN_done`, and the result has no entry because it is `+copy`
of `p`'s result (no entry by `NoEnt`) into the bunt (`runLC_tailN`,
`copyL_bunt`).  With it the n-ary contract of `R` holds under the
hypotheses of `tailN_done` for `callR` alone (`finishLFC_contractRT`): the
needs of `R-bell` in the environment (`hring`, `hned`, `hsof`, `hNf`),
`SplitsLess`, and the products of the `%10` fitting the bell (`hAp`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The n-ary direct call under `%done` meets `DoneE`** (`tailN_done` and
a result without entries). -/
theorem doneE_tailN (lib : Lib) {N : Needs} {env : CallEnv} {P : Noun → Prop} {p q : Nomm} {fb fq : Noun}
    {b : Bell} {bNed : NeedOrd} (hring : env.ring b = Option.none) (hned : env.need b = some bNed)
    (hsof : ∀ m, env.sof m p q b bNed = false) (hNf : N b false = some bNed) (hspl : SplitsLess b bNed)
    (Sp : LOKS (S := S) (Map := Map) false lib N env P fb p) (Np : NoEnt (S := S) (Map := Map) env p)
    (hcount : sixCount p ≤ 255) (hq : safeFolFol q = true)
    (hAp : ∀ x gul y, P x → Mink lib gul [] x fb (Tone.zero y) → SkaModel.Fits b.less y)
    (hq1 : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {rc : Tone}, P s → minkF lib gul n tm s fq = some rc →
      rc = Tone.zero b.fol)
    (hq2 : ∀ {s gul : Noun} {tm : Trace}, P s → Mink lib gul tm s fq (Tone.zero b.fol)) :
    DoneE (S := S) (Map := Map) lib N env P (n3 (A 2) fb fq) (Nomm.n2 p q (some (b, Option.none))) := by
  intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
  refine ⟨tailN_done lib hring hned hsof hNf hspl Sp hcount hq hAp hq1 hq2 b0 d0 hu hcl hcb hr, ?_⟩
  obtain ⟨sub, gA, nexS, g5, ha, hp, hc⟩ := runLC_tailN hring hned (hsof _) hq hr
  have eS : entries nexS.laz = [] :=
    Np (goal := CGoal.next ⟨sub, HoonSet.empty⟩ (jmp0 gA.bo)) trivial hp
  have eL := eq_ofSure_of_entries eS
  unfold copyL at hc
  obtain ⟨o, g6, -, hc⟩ := bind_some hc
  obtain ⟨laz, g7, h7, hc⟩ := bind_some hc
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  rw [eL, copyLazyL_ofSure] at h7
  obtain ⟨s, g8, -, h7⟩ := bind_some h7
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h7
  obtain ⟨rfl, rfl⟩ := h7
  exact entries_ofSure _

/-- **The n-ary contract of `R` under the hypotheses of `tailN_done` for its
call** `[2 [0 1] [1 R] [R-bell ~]]` on the products of the `%10`: the needs of
`R-bell` in the environment, `SplitsLess`, the products of `[0 1]` fitting
the bell (`[1 R]` returns the bell's formula: `quote_hq1`, `quote_hq2`). -/
theorem finishLFC_contractRT (lib : Lib) {env : CallEnv} {P : Noun → Prop} (N : Needs) {bNed : NeedOrd}
    (hring : env.ring bellR = Option.none) (hned : env.need bellR = some bNed)
    (hsof : ∀ m, env.sof m (Nomm.n0 1) (Nomm.n1 nounR) bellR bNed = false) (hNf : N bellR false = some bNed)
    (hspl : SplitsLess bellR bNed)
    (hAp : ∀ x gul y, Img lib P tenRF x → Mink lib gul [] x (slot 1) (Tone.zero y) → SkaModel.Fits bellR.less y)
    {ord : NeedOrd} {less : Cape} {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, []))
    {c : Straight Map} (h : finishLFC (S := S) env nommR ord less bake = some c) :
    ∀ s, P s → CapeAxes less s → ∀ args, SkaModel.split c.need s = some args →
      ContractFwd lib N s (nommRFOf (n3 (A 2) (slot 1) (C (A 1) nounR))) args c ∧
        ContractBwd lib N s (nommRFOf (n3 (A 2) (slot 1) (C (A 1) nounR))) args c :=
  finishLFC_contractR lib N (doneE_tailN lib hring hned hsof hNf hspl
    (lokS_n0 lib env (Nat.le_refl 1) (fun s hs gul tm r =>
      mink_pure (codeOK_none lib) rfl ((CallTreeA.n0 1).annot _) hs gul tm r))
    (noEnt_pure env rfl rfl) (by decide) rfl hAp (fun _ h => quote_hq1 h) (fun _ => quote_hq2)) hbake h

end Comp
end SkaModel
end Formalization
