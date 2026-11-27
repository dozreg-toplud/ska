import lemmas.Ska.CompDirectMLS
import lemmas.Ska.CompDirectMTailEx

/-!
# A direct call under `%4` at the top, with `mono` `&`

README Gaps 18.13 (track J, 2026-11-27).  The first contract theorem with a
direct call under `%next` (the `%cal` form of `callLBM`):

* `four_doneBM` (generated, `CompDirectMLS.lean`): `four_doneB` for the
  whole-subject run (`runLCM env true`), the operand meeting `LOKSFM`.
* `finishLUCM_contractFourDirect`: both halves of the contract of
  `[4 [2 p [1 k] b]]` on the real whole-subject code, `p` meeting `LOKS
  false` with no direct call (track C's class), hypotheses only on the needs
  and `Annot.direct`; `finishLUCM_bellContractFourDirect` the `BellContract`
  form for `p = [0 1]`.
* The instance `[4 callR]` (`R`'s call under `%4`): a `#guard` of its code
  (the blocks of `%dn` of `CompDirectMCheck.lean` from the `%4` on), and
  `fourCallR_bellContract`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

section
variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **`[4 [2 p [1 k] b]]` at the top meets both halves of the contract** on
the real whole-subject code (`finishLUCM`): the direct call under `%next`
(`lokSM_direct`), `p` meeting `LOKS false` with no direct call, the callee
not pure, the needs as in `tail_done`, the products of `p` fitting the
bell. -/
theorem finishLUCM_contractFourDirect (lib : Lib) {env : CallEnv} {P : Noun → Prop} {p : Nomm} {fb k : Noun}
    {b : Bell} {N : Needs} {bNed ndT : NeedOrd} (hring : env.ring b = Option.none) (hned : env.need b = some bNed)
    (hNf : N b false = some bNed) (hNt : N b true = some ndT) (hpure : env.pure b = false)
    (Sp : LOKS (S := S) (Map := Map) false lib N env P fb p) (hpd : p.noDirect = true) (hcount : sixCount p ≤ 255)
    (hAp : ∀ x gul y, P x → Mink lib gul [] x fb (Tone.zero y) → SkaModel.Fits b.less y) (hk : k = b.fol)
    {c : Straight Map}
    (hc : finishLUCM (S := S) env (Nomm.n4 (Nomm.n2 p (Nomm.n1 k) (some (b, Option.none)))) = some c) :
    c.need = NeedOrd.this ∧ ∀ s, P s → ContractFwd lib N s (n2 (A 4) (n3 (A 2) fb (C (A 1) k))) [s] c ∧
      ContractBwd lib N s (n2 (A 4) (n3 (A 2) fb (C (A 1) k))) [s] c := by
  subst hk
  have Sc := lokSM_direct (S := S) (Map := Map) lib env (q := Nomm.n1 b.fol) (fq := C (A 1) b.fol) hring hned hNf hNt
    hpure Sp hpd rfl hAp (fun _ h => quote_hq1 h) (fun _ => quote_hq2)
  exact finishLUCM_contractGB lib N (fun hr => (four_doneBM lib Sc.toF (minkC4_four lib P _)
    (by simp only [sixCount]; omega) (by simp [gen0]) rfl upBelow_gen0 clear_gen0 condBelow_gen0 hr).run) hc

end

/-! ## The instance: `R`'s call under `%4` -/

/-- The caller's bell for `[4 callR]`: the subject fits `R-bell`. -/
def bellF : Bell := ⟨bellR.less, n2 (A 4) (tailFol nounR)⟩

/- The whole-subject code of `[4 callR]`, registers and labels as the
Hoon's: the blocks of `%dn` (`CompDirectMCheck.lean`) from the `%4` on
(`inc`, `+kerf`'s `out`, the merge block with `par [v5]`, `cal R-bell [v3]
v7` and `csl R-bell v6 v8` hopping with their product, the tree); `%dn`'s
`[[1 R] [0 1]]` in front is the `%1` no class has yet. -/
#guard monoOutM (Nomm.n4 callR) 10 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 6] (hp 8)), (1, bk [Pole.inc 2 1] (Termin.don 1)),
    (2, bk [Pole.mov 4 2] (hp 1)), (3, bkp [5] [Pole.mov 5 4] (hp 2)),
    (4, bk [Pole.cal bellR [3] 7] (hpa 7 3)), (5, bk [Pole.csl bellR 6 8] (hpa 8 3)),
    (6, bk [Pole.mov 9 3] (hp 4)), (7, bk [Pole.hed 6 10, Pole.tal 6 9] (hp 6)),
    (8, bk [] (Termin.clq 6 (jmp0 7) (jmp0 5))), (9, Option.none)])

/-- **The bell contract of `R`'s call under `%4` at the top**, on the real
whole-subject code, for every needs table with `R-bell`'s n-ary need
`[~ this]` and a need for its call by subject. -/
theorem fourCallR_bellContract {lib : Lib} {N : Needs} {ndT : NeedOrd}
    (hNf : N bellR false = some (NeedOrd.pair NeedOrd.none NeedOrd.this)) (hNt : N bellR true = some ndT)
    {cd : Straight FM} (hc : finishLUCM (S := LS) envD (Nomm.n4 callR) = some cd) :
    cd.need = NeedOrd.this ∧ BellContract lib N bellF true cd := by
  have H := finishLUCM_contractFourDirect (S := LS) lib (P := SkaModel.Fits bellF.less) (env := envD) rfl
    (by simp [envD]) hNf hNt rfl (lokS_callTree (S := LS) (Map := FM) lib envD _ (CallTree.n0 1)).1 rfl
    (by simp [sixCount]) (fun x gul y hx hm => by
      have := Mink.det hm ⟨1, minkStep_axis1 _ _ _ _ _⟩
      cases this; exact hx) rfl hc
  refine ⟨H.1, fun s hs args hargs => ?_⟩
  simp only [if_true, Option.some.injEq] at hargs
  subst hargs
  exact H.2 s hs

end Comp
end SkaModel
end Formalization
