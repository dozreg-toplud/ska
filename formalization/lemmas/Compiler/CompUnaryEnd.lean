import lemmas.Compiler.CompKerfLink
import lemmas.Compiler.CompUnary
import lemmas.Compiler.RoadPure

/-!
# The end of `+compile-unary`: `+run`, then `+kerf`

`cu_run_kerf`: from the entry state of `+compile-unary` (`cu_entry_run`),
the pill's `+run` on a pure nomm with no `%6` and `tenOk`, then the pill's
`+kerf` on the `next` it returns, with the state it returns put into the
door, is the model's `runL` then `kerf` (the first two steps of
`finishLU`).  The `next` is fork-free and its looks are not at `0`
(`cra_run_lok`), and `soft` stays the empty map of the entry, so
`comp_kerf` applies.

`road-pure` of `+compile-unary` is the noun of `+ska-poke`'s (`cu_rp_at`:
axis `254` of `compTypes`, which is axis `62` of `ana`), so the link of
`RoadPure.lean` applies to its trap as it is: the gate returns `y` exactly
when the trap does (`cu_rp_iff`, for every trap).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

variable {ctx : Noun}

/-- `road-pure` as `+compile-unary` reaches it (axis `4094` of its gate's
subject after `=/  args`, axis `254` of `compTypes`) is `road-pure` of
`+ska-poke`. -/
theorem cu_rp_at : slot? 254 compTypes = some (C rpBat (C rpSam rpCtx)) := rp_at

/-- **`road-pure` returns `y` exactly when its trap does**, for every trap
`T` (the proof of `ska_poke_iff`, for any trap). -/
theorem cu_rp_iff (T y : Noun) : nock (C rpBat (C T rpCtx)) rpBat = some y ↔ nock T rpK = some y := by
  rw [rp_run_iff T rpCtx rpL5 y rp_l4 rp_l5 rp_mean_at]
  constructor
  · exact fun h => h.2
  · intro h
    obtain ⟨n, hn⟩ := mink_of_evalH rpLib (A 0) (SkaModel.EvalA.toEvalH (evalA_of_nock h))
    exact ⟨⟨y, n, hn []⟩, h⟩

/-- **`+run` then `+kerf` from the entry of `+compile-unary`** is `runL`
then `kerf`: the product of `+run` is split into the `next` noun `N` and the
state `G`, and `+kerf` runs on `N` in the door with `G`. -/
theorem cu_run_kerf (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (n : Nomm) (hpu : n.pure = true) (h6 : noSix n = true) (ht : tenOk n = true)
    (cache mono sup : Noun) :
    (nock (crSubj mono n.toNoun (CGoal.toL (CGoal.done : CGoal CSet)).toNoun (listNoun A []) sup
        (compCore genEntry (cuRest cache) ctx)) crDol).bind (fun R =>
      (slot? 2 R).bind fun N => (slot? 3 R).bind fun G =>
        nock (C kerfBat (C N (C comp.door (C G ctx)))) kerfBat)
      = ((runL n (CGoal.toL (CGoal.done : CGoal CSet)) [] genEntry).bind fun p => kerf p.1 p.2).map
          fun p => C (C (A p.1.1) (A p.1.2)) (genNoun p.2 (cuRest cache)) := by
  obtain ⟨hc, hl, hm⟩ := comp_ctx_pill ctx h7
  rw [cu_entry_run h7 hcode n hpu h6 ht cache mono sup, runL_toL n hpu h6]
  cases e : run (S := CSet) (Map := TreapMap mugF) n CGoal.done genEntry with
  | none => simp [e, Functor.map, StateT.map]
  | some p =>
    obtain ⟨nex, g1⟩ := p
    have hk := comp_kerf hc hl hm (cuRest cache) g1 nex (cu_entry_nosoft cache g1.bo)
      (cra_run_lok n hpu h6 CGoal.done genEntry g1 nex e trivial)
    simp only [compCore] at hk
    simp only [e, Functor.map, StateT.map, bind, pure, Option.bind_some, Option.map_some, cr_next_noun]
    simp only [nock_exec, Option.bind_some]
    exact hk

end Compiler
end Formalization
