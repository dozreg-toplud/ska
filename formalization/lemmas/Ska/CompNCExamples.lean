import lemmas.Ska.CompHypOfNC

/-!
# Examples of the induction over `NC`

README Gaps 12.22.  The raw blocks of `tools/hoon/calldump4.hoon` checked
against `finishLUC` (`#guard`), and formulas proved end to end through
`finishLUC_contractNC` (both halves of the contract).

`[4 [2 [0 3] [0 2]]]` (`%i4`, subject `[[4 0 1] 5]`, product `7`): `0: v0 ->
cel, hed -> v5, tal -> v4, hop 3`; `3: nok v4 v5 -> v3`; `2: mov v3 v2` (the
call's `+kerf` into `arg = v2`); `1: inc v2 v1, don v1`.

`[[0 1] [8 [0 3] [2 [0 2] [0 6]]]]` (`%c8t`, the nomm `[[0 1] [7 [[0 3] [0
1]] [2 [0 2] [0 6]]]]`): `0: v0 -> cel, hed -> v6, tal -> v5, hop 5` (the
call's parts, `[0 3]` and `[0 1]` of the pushed pair composed through the
copy); `5: nok v5 v6 -> v4`; `4: mov v4 v3`; `3: mov v0 v2` (the bond of the
head `[0 1]` behind the tail's call); `2: con v2 v3 -> v1`; `1: don v1`.  The
tail `[7 p q]` has a call-free cons `p` and a calling `q` whose result has
no entry (`sevenN`), and its `EntNew` comes from `p`'s `JNew` (the block of
`p`'s `+copy`) and `q`'s `EntNew`, which no constructor of `FragI` gave.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

-- `%i4`
#guard monoOutC envR (Nomm.n4 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) 5 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 6, Pole.cel 6, Pole.hed 6 8, Pole.mov 8 5, Pole.tal 6 7, Pole.mov 7 4] (hp 3)),
    (1, bk [Pole.inc 2 1] (Termin.don 1)),
    (2, bk [Pole.mov 3 2] (hp 1)),
    (3, bk [Pole.nok 4 5 3] (hp 2)),
    (4, none)])

-- `%c8t`
#guard monoOutC envR (Nomm.cons (Nomm.n0 1) (Nomm.n7 (Nomm.cons (Nomm.n0 3) (Nomm.n0 1))
    (Nomm.n2 (Nomm.n0 2) (Nomm.n0 6) Option.none))) 7 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 7, Pole.cel 7, Pole.hed 7 9, Pole.mov 9 6, Pole.tal 7 8, Pole.mov 8 5] (hp 5)),
    (1, bk [] (Termin.don 1)),
    (2, bk [Pole.con 2 3 1] (hp 1)),
    (3, bk [Pole.mov 0 2] (hp 2)),
    (4, bk [Pole.mov 4 3] (hp 3)),
    (5, bk [Pole.nok 5 6 4] (hp 4)),
    (6, none)])

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- `[7 [[0 3] [0 1]] [2 [0 2] [0 6]]]` is in `NC 0 true`: `sevenN` with
the call-free cons `p`. -/
theorem nc_c8tTail : NC (S := S) 0 true (Nomm.n7 (Nomm.cons (Nomm.n0 3) (Nomm.n0 1))
    (Nomm.n2 (Nomm.n0 2) (Nomm.n0 6) Option.none)) :=
  NC.sevenN (t := true) (t' := true) (NC.ind (t := true) (t' := true) NC.n0 NC.n0 rfl)
    (NoEntF.ind rfl rfl (NoEntF.pure rfl rfl)) (NC.cons (t := true) (t' := true) NC.n0 NC.n0 (fun e => by cases e))
    (fun x => by simp [Nomm.pure] at x)

/-- **`[[0 1] [8 [0 3] [2 [0 2] [0 6]]]]` end to end** (`%c8t`): a cons
whose tail is the `n8` form with a call-free pushed pair and a calling body
(the head `[0 1]` under the bond goal of the tail, the tail's `EntNew` from
the pushed pair's `JNew`). -/
theorem c8t_example {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {bl : Bell}
    (hfol : bl.fol = C (slot 1) (n3 (A 8) (slot 3) (n3 (A 2) (slot 2) (slot 6)))) {env : CallEnv}
    {cd : Straight Map}
    (h : finishLUC (S := S) env (Nomm.cons (Nomm.n0 1) (Nomm.n7 (Nomm.cons (Nomm.n0 3) (Nomm.n0 1))
      (Nomm.n2 (Nomm.n0 2) (Nomm.n0 6) Option.none))) = some cd)
    (N : Needs) : cd.need = NeedOrd.this ∧ BellContract lib N bl true cd := by
  have hA : Annot lib code (SkaModel.Fits bl.less) bl.fol (Nomm.cons (Nomm.n0 1)
      (Nomm.n7 (Nomm.cons (Nomm.n0 3) (Nomm.n0 1)) (Nomm.n2 (Nomm.n0 2) (Nomm.n0 6) Option.none))) := by
    rw [hfol]
    exact Annot.cons Annot.n0 (Annot.n8 Annot.n0 (Annot.indirect Annot.n0 Annot.n0))
  have hf : NC (S := S) 0 true (Nomm.cons (Nomm.n0 1) (Nomm.n7 (Nomm.cons (Nomm.n0 3) (Nomm.n0 1))
      (Nomm.n2 (Nomm.n0 2) (Nomm.n0 6) Option.none))) :=
    NC.cons (t := true) (t' := true) NC.n0 nc_c8tTail (fun _ => rfl)
  exact finishLUC_contractNC hok hA hf (by decide) h N

/-- **`[4 [2 [0 3] [0 2]]]` end to end** (`%i4`): the increment of a call's
product, under `%done` (`four_runD`: the call under `%next` of the register
`arg` into the block `[inc arg pro] don pro`). -/
theorem four_example {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {bl : Bell}
    (hfol : bl.fol = n2 (A 4) (n3 (A 2) (slot 3) (slot 2))) {env : CallEnv} {cd : Straight Map}
    (h : finishLUC (S := S) env (Nomm.n4 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) = some cd)
    (N : Needs) : cd.need = NeedOrd.this ∧ BellContract lib N bl true cd := by
  have hA : Annot lib code (SkaModel.Fits bl.less) bl.fol (Nomm.n4 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) := by
    rw [hfol]
    exact Annot.n4 (Annot.indirect Annot.n0 Annot.n0)
  exact finishLUC_contractNC hok hA (NC.n4 (NC.ind (t := true) (t' := true) NC.n0 NC.n0 rfl)) (by decide) h N

end Comp
end SkaModel
end Formalization
