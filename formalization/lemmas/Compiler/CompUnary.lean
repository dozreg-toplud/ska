import lemmas.Compiler.CompRunAll
import lemmas.Compiler.CompCtx

/-!
# `+compile-unary`: the entry state of its run

`+compile-unary` (line 3390 of `nock-compilation.hoon`) is arm `2810` of
`K` (`compK`, axis `63` of `cor`), found by the cord `%compile-unary` of its
`%fast` hint inside the arm (`cu_fast_at`).  Its gate runs the trap `|.`
under `road-pure` (`+mule` of `vi`), and the trap, after `+compile-scc-in`
and the call of `+comp`, runs

    =|  gen=line-short
    =.  cache.gen  cache

as `[8 [1 cuBunt] [7 [10 [766 [0 4079]] [0 1]] REST]]`: the bunt of
`line-short` is a constant of the formula (`cu_bunt_at`, at axis
`6035972415486` of `compK`), and the edit writes the sample's `cache`
(axis `4079` of the subject after the push) at axis `766`, which is
`cache` (axis `510`) of the state at axis `2`.  The constant is

    [0 1 0 %run ~ ~ ~ [~ ~ ~ ~ ~] ~ ~]

(`re-gen` `0`, `bo-gen` `1`, `id-gen` `0`, `mode` `%run`, empty `blocks`,
`tags`, `cond`, the bunt of `comp-cache`, empty `soft` and `sofs`).  With
`cache` set it is `genNoun genEntry ⟨cache, ~, ~⟩` (`cu_entry_noun`), whose
`soft` is empty (`cu_entry_nosoft`), so `comp_run_entry` applies to the
run that follows (`cu_entry_run`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

/-- The bunt of `line-short` in the Nock of `+compile-unary`. -/
def cuBunt : Noun :=
  C (A 0) (C (A 1) (C (A 0) (C (A 0x6e7572) (C (A 0) (C (A 0) (C (A 0)
    (C (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))) (C (A 0) (A 0)))))))))

/-- The `%fast` cord of arm `2810` of `K` is `%compile-unary`. -/
theorem cu_fast_at : slot? 359798 compK = some (A 0x7972616e752d656c69706d6f63) := by
  kernel_rfl

/-- **The `=|` of `+compile-unary`**: the formula at axis `1508993103871`
of `K` is `[8 [1 cuBunt] [7 [10 [766 [0 4079]] [0 1]] ..]]`. -/
theorem cu_eight_at : slot? 3017986207742 compK = some (A 8) := by kernel_rfl
theorem cu_bunt_at : slot? 6035972415486 compK = some (C (A 1) cuBunt) := by kernel_rfl
theorem cu_edit_at : slot? 24143889661950 compK =
    some (C (A 10) (C (C (A 766) (C (A 0) (A 4079))) (C (A 0) (A 1)))) := by kernel_rfl
theorem cu_seven_at : slot? 12071944830974 compK = some (A 7) := by kernel_rfl

/-- The rest of the state of the entry: `cache` set, `soft` and `sofs`
empty. -/
def cuRest (cache : Noun) : GenRest := ⟨cache, A 0, A 0⟩

/-- **The entry state of `+compile-unary` is `genEntry`**: the bunt with
`cache` set is the noun of `genEntry` with the rest `cuRest cache`. -/
theorem cu_entry_noun (cache : Noun) :
    edit? 510 cache cuBunt = some (genNoun (genEntry : Gen (TreapMap mugF)) (cuRest cache)) := by
  rfl

/-- `soft` is empty at the entry. -/
theorem cu_entry_nosoft (cache : Noun) : (cuRest cache).NoSoft := by
  intro o
  rfl

/-- The push and the edit: the trap's subject `S` with `cache` at axis
`2031` becomes `[genNoun genEntry (cuRest cache) S]`. -/
theorem cu_entry_step (S R cache : Noun) (hc : slot? 2031 S = some cache) :
    nock S (C (A 8) (C (C (A 1) cuBunt) (C (A 7) (C (C (A 10) (C (C (A 766) (C (A 0) (A 4079)))
      (C (A 0) (A 1)))) R))))
      = nock (C (genNoun (genEntry : Gen (TreapMap mugF)) (cuRest cache)) S) R := by
  simp only [nock_exec, hc, Option.bind_some]
  rfl

/-- **The run that follows the entry is `runL`** for every pure nomm with
no `%6` and no `%10` at axis `0`, for every `cache`: `comp_run_entry` on
the state `+compile-unary` builds. -/
theorem cu_entry_run {ctx : Noun} (h7 : slot? 7 ctx = some compK) {cod : Noun}
    (hcode : slot? 52 ctx = some cod) (n : Nomm) (hpu : n.pure = true) (h6 : noSix n = true)
    (ht : tenOk n = true) (cache mono sup : Noun) :
    nock (crSubj mono n.toNoun (CGoal.toL (CGoal.done : CGoal CSet)).toNoun (listNoun A []) sup
        (compCore genEntry (cuRest cache) ctx)) crDol
      = (runL n (CGoal.toL (CGoal.done : CGoal CSet)) [] genEntry).map
          fun p => C p.1.goal.toNoun (genNoun p.2 (cuRest cache)) :=
  comp_run_entry h7 hcode n hpu h6 ht (cuRest cache) mono sup (cu_entry_nosoft cache)

end Compiler
end Formalization
