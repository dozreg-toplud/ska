import lemmas.Compiler.PokeLinkGood3
import lemmas.Compiler.PokeLinkLoopRun

/-!
# `PGood4`: the invariant that carries the flags (track P, README Gaps 23)

`PGood4` = `PGood3` + `InfoCalls` of `code` + a solution `F` of the SCC loop
on `code` (`FlagSol`) with flags at every key (`FlagTot`), what
`loopLinkAt_flagsOfT` asks of the state.

* `good4_empty`: the empty state.
* `good4_long`: a poke that keeps `long` (the model's `%jets`, `%fast`: in
  the Hoon too, `%jets` writes `jets-hot` and the four caches, and
  `+ska-cole-settle` only `cole` and `pend`; `code` and `calls` are never
  written outside `+ska-poke`) keeps the new clauses.
* `flags_poke`: `%full` on the table: after `+ska-poke`'s SCC loop over a
  `TarjanSpec` list, the new table has `InfoCalls`, and the loop's flags `G`
  are a total solution.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF SkaModel.PokeM

/-- Every key of `T` has flags in `F`. -/
def FlagTot (T : FinMap Bell (VarEntry FinMap)) (F : FlagTab) : Prop :=
  ∀ c e, FinMap.get T c = some e → ∃ p, F c = some p

/-- **The invariant with the flags.** -/
structure PGood4 (Cls : Straight (TreapMap mugF) → Prop) (st : PSt) : Prop where
  good3 : PGood3 Cls st
  info : InfoCalls st.long.code
  flags : ∃ F, FlagSol st.long.code F ∧ FlagTot st.long.code F

theorem good4_empty (Cls : Straight (TreapMap mugF) → Prop) : PGood4 Cls emptySt where
  good3 := good3_empty Cls
  info := fun b e h => by simp [emptySt, FinMap.get, Treap.empty, FinMap.empty] at h
  flags := ⟨fun _ => none, flagSol_none _ (fun b => by simp [emptySt, FinMap.get, Treap.empty, FinMap.empty]),
    fun c e h => by simp [emptySt, FinMap.get, Treap.empty, FinMap.empty] at h⟩

/-- A poke that keeps `long` keeps the clauses of the flags. -/
theorem good4_long {Cls : Straight (TreapMap mugF) → Prop} {st st' : PSt} (h : PGood4 Cls st)
    (h3 : PGood3 Cls st') (hl : st'.long = st.long) : PGood4 Cls st' where
  good3 := h3
  info := hl ▸ h.info
  flags := hl ▸ h.flags

/-- **`%full` on the table**: the new table has `InfoCalls`, and the
loop's flags are a total solution of it. -/
theorem flags_poke {code : FinMap Bell (VarEntry FinMap)} {E : BEnv FinMap} {n : Nat}
    {bg : FinMap Bell (VarEntry FinMap) × FinMap Bell (FinMap Bell Unit)}
    (hc : CodeClosed code) (hv : VarsKeys E.vars code) (hi : InfoCalls code) (hbg : bakeGraph E n = some bg)
    {L : List (List Bell)} (hL : TarjanSpec (newCode code bg.1) L) {F G : FlagTab} (hF : FlagSol code F)
    (hFt : FlagTot code F) (hr : sccLoop (nmOf (addCode code (newCode code bg.1))) F L = some G) :
    InfoCalls (addCode code (newCode code bg.1)) ∧ FlagSol (addCode code (newCode code bg.1)) G ∧
      FlagTot (addCode code (newCode code bg.1)) G :=
  ⟨infoCalls_addCode hi hbg, (flagsOf_poke hc hv hi hbg hL hF hr).2.2.2.2,
    (acc_final (addsTo_addCode code bg.1) hL hF.1 hFt hr).2⟩

end Compiler
end Formalization
