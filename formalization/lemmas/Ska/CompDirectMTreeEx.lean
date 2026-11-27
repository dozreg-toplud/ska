import lemmas.Ska.CompDirectMTree
import lemmas.Ska.CompDirectMCheck

/-!
# Instances of `CallTreeD` against the compiler's blocks

README Gaps 18.14 (track J, 2026-11-27).  The nomms of `CompDirectMCheck.lean`
whose code a `#guard` there compares with the raw blocks of the real
compiler (`tools/hoon/directdump2.hoon`), as members of `CallTreeD` at every
subject, with both halves of the contract of `finishLUCM_contractCallTreeD`:

* `dt_contract`: `%dt`'s nomm `dtNomm`, `[7 [[1 R] [0 1]] [7 [0 1] [2 [0 1]
  [1 R] R-bell]]]`, a direct call in the `q` of a `%7` in the `q` of a `%7`;
* `dc_contract`, `dk_contract`: `%dc`, `%dk`, `dtNomm` in the head and in the
  tail of a cons;
* `dn_contract`: `%dn`, `[4 dtNomm]` (the `%1` of `[[1 R] [0 1]]` under
  `%next`, `CallTreeD.n1`).

The contracts are for the formula of the nomm, `dtFolD`
(`[7 [[1 R] [0 1]] [7 [0 1] [2 [0 1] [1 R]]]]`), not for `%dt`'s
`[8 [1 R] [9 2 [0 1]]]` (README Gaps 18.9).  The `#guard`s below check that
`finishLUCM` makes code for each nomm, so the theorems are not vacuous; the
code itself is the Hoon's by the `#guard`s of `CompDirectMCheck.lean`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-- The formula of `dtNomm`: `[7 [[1 R] [0 1]] [7 [0 1] [2 [0 1] [1 R]]]]`. -/
def dtFolD : Noun := n3 (A 7) (C (quote nounR) (slot 1)) (n3 (A 7) (slot 1) (tailFol nounR))

/-- `[[1 R] [0 1]]` on `s` is `[R s]`. -/
theorem mink_quoteCons {lib : Lib} {gul s y : Noun}
    (h : Mink lib gul [] s (C (quote nounR) (slot 1)) (Tone.zero y)) : y = C nounR s := by
  have h' : Mink lib gul [] s (C (quote nounR) (slot 1)) (Tone.zero (C nounR s)) :=
    ⟨3, by simp [minkF, minkStep, slot?, axisPath, axisPathFuel, slotAtPath]⟩
  have := Mink.det h h'
  cases this; rfl

/-- The products of `[0 1]` on the subjects after `[[1 R] [0 1]]` fit
`R-bell`'s subject `[R *]`. -/
theorem dt_fits {lib : Lib} {P : Noun → Prop} :
    ∀ x gul y, Img lib (Img lib P (C (quote nounR) (slot 1))) (slot 1) x →
      Mink lib gul [] x (slot 1) (Tone.zero y) → SkaModel.Fits bellR.less y := by
  rintro x gul y ⟨x1, gul1, ⟨x0, gul0, -, h0⟩, h1⟩ hm
  have e1 := Mink.det hm ⟨1, minkStep_axis1 _ _ _ _ _⟩
  have e2 := Mink.det h1 ⟨1, minkStep_axis1 _ _ _ _ _⟩
  cases e1; cases e2
  rw [mink_quoteCons h0]
  exact Or.inr ⟨_, _, _, _, rfl, rfl, rfl, trivial⟩

/-- **`dtNomm` is in `CallTreeD`** (index `true`) at every set of subjects,
for every needs table with `R-bell`'s n-ary need `[~ this]` and a need for
its call by subject. -/
theorem callTreeD_dt (lib : Lib) {N : Needs} {P : Noun → Prop} {ndT : NeedOrd}
    (hNf : N bellR false = some (NeedOrd.pair NeedOrd.none NeedOrd.this)) (hNt : N bellR true = some ndT) :
    CallTreeD lib envD N P true dtFolD dtNomm :=
  CallTreeD.seven (CallTreeD.cons (CallTreeD.n1 nounR) (CallTreeD.n0 1))
    (CallTreeD.seven (CallTreeD.n0 1)
      (CallTreeD.direct (CallTreeD.n0 1) rfl (by simp [envD]) hNf hNt rfl rfl (QDirect.quote lib _ bellR) dt_fits))

#guard (finishLUCM (S := LS) (Map := FM) envD dtNomm).isSome
#guard (finishLUCM (S := LS) (Map := FM) envD (Nomm.cons dtNomm (Nomm.n0 1))).isSome
#guard (finishLUCM (S := LS) (Map := FM) envD (Nomm.cons (Nomm.n0 1) dtNomm)).isSome
#guard (finishLUCM (S := LS) (Map := FM) envD (Nomm.n4 dtNomm)).isSome

/-- **`%dt`'s nomm at the top meets both halves of the contract** on the
real whole-subject code, on every subject. -/
theorem dt_contract (lib : Lib) {N : Needs} {ndT : NeedOrd}
    (hNf : N bellR false = some (NeedOrd.pair NeedOrd.none NeedOrd.this)) (hNt : N bellR true = some ndT)
    {c : Straight FM} (hc : finishLUCM (S := LS) envD dtNomm = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s dtFolD [s] c ∧ ContractBwd lib N s dtFolD [s] c :=
  (fun H => ⟨H.1, fun s => H.2 s trivial⟩)
    (finishLUCM_contractCallTreeD (S := LS) lib (callTreeD_dt (P := fun _ => True) lib hNf hNt) hc)

/-- **`%dc`: `dtNomm` in the head of a cons**, `[[7 [[1 R] [0 1]] [7 [0 1]
callR]] [0 1]]`, at the top. -/
theorem dc_contract (lib : Lib) {N : Needs} {ndT : NeedOrd}
    (hNf : N bellR false = some (NeedOrd.pair NeedOrd.none NeedOrd.this)) (hNt : N bellR true = some ndT)
    {c : Straight FM} (hc : finishLUCM (S := LS) envD (Nomm.cons dtNomm (Nomm.n0 1)) = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s (C dtFolD (slot 1)) [s] c ∧
      ContractBwd lib N s (C dtFolD (slot 1)) [s] c :=
  (fun H => ⟨H.1, fun s => H.2 s trivial⟩)
    (finishLUCM_contractCallTreeD (S := LS) lib
      (CallTreeD.cons (callTreeD_dt (P := fun _ => True) lib hNf hNt) (CallTreeD.n0 1)) hc)

/-- **`%dk`: `dtNomm` in the tail of a cons**, `[[0 1] [7 [[1 R] [0 1]] [7
[0 1] callR]]]`, at the top. -/
theorem dk_contract (lib : Lib) {N : Needs} {ndT : NeedOrd}
    (hNf : N bellR false = some (NeedOrd.pair NeedOrd.none NeedOrd.this)) (hNt : N bellR true = some ndT)
    {c : Straight FM} (hc : finishLUCM (S := LS) envD (Nomm.cons (Nomm.n0 1) dtNomm) = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s (C (slot 1) dtFolD) [s] c ∧
      ContractBwd lib N s (C (slot 1) dtFolD) [s] c :=
  (fun H => ⟨H.1, fun s => H.2 s trivial⟩)
    (finishLUCM_contractCallTreeD (S := LS) lib
      (CallTreeD.cons (CallTreeD.n0 1) (callTreeD_dt (P := fun _ => True) lib hNf hNt)) hc)

/-- **`%dn`: `[4 dtNomm]`** at the top (the `%1` of `[[1 R] [0 1]]` under
`%next`, the direct call under `%next` below two `%7`s and the `%4`). -/
theorem dn_contract (lib : Lib) {N : Needs} {ndT : NeedOrd}
    (hNf : N bellR false = some (NeedOrd.pair NeedOrd.none NeedOrd.this)) (hNt : N bellR true = some ndT)
    {c : Straight FM} (hc : finishLUCM (S := LS) envD (Nomm.n4 dtNomm) = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s (n2 (A 4) dtFolD) [s] c ∧
      ContractBwd lib N s (n2 (A 4) dtFolD) [s] c :=
  (fun H => ⟨H.1, fun s => H.2 s trivial⟩)
    (finishLUCM_contractCallTreeD (S := LS) lib (CallTreeD.four (callTreeD_dt (P := fun _ => True) lib hNf hNt)) hc)

end Comp
end SkaModel
end Formalization
