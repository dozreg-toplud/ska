import lemmas.Ska.OptSwitchHyp

/-!
# `+switch-chains`: toward the walk

From the second chain on, `switchWalk` calls `switchTag bl out` and
`switchPlain bl out`: they read the blocks before (`bl`) and write into the
blocks so far (`out`).  The only read of `bl` in either is the block at the
head `o` (`HoonMap.get bl o`), so where the head's block in `out` is still
the one of `bl` the step is the same as on `out` alone (`switchTag_out`,
`switchPlain_out`), which is the form `tag_keeps_of` takes.

The walk over tagged chains is `switchWalk_tag` (`OptSwitchMulti.lean`), the
walk over chains of both kinds `switchWalk_all` (`OptSwitchWalkAll.lean`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock

variable {Map : Type → Type} [HoonMap Map]

/-- **One tagged chain reads `bl` only at its head.** -/
theorem switchTag_out {bl out : Map Blob} {fuel o : Nat} {cs : List STest} {done : List Nat}
    (h : HoonMap.get bl o = HoonMap.get out o) :
    switchTag bl out fuel o cs done = switchTag out out fuel o cs done := by
  cases cs with
  | nil => rfl
  | cons t0 tl => simp only [switchTag, h]

/-- **One plain chain reads `bl` only at its head.** -/
theorem switchPlain_out {bl out : Map Blob} {fuel o : Nat} {ps : List (Nat × SPlain)} {done : List Nat}
    {nex : Nat} (h : HoonMap.get bl o = HoonMap.get out o) :
    switchPlain bl out fuel o ps done nex = switchPlain out out fuel o ps done nex := by
  cases ps with
  | nil => rfl
  | cons p0 pl => simp only [switchPlain, h]

end Opt
end SkaModel
end Formalization
