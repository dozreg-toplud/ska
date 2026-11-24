import lemmas.Ska.OptSwitchHyp

/-!
# `+switch-chains`: toward the walk

From the second chain on, `switchWalk` calls `switchTag bl out` and
`switchPlain bl out`: they read the blocks before (`bl`) and write into the
blocks so far (`out`).  The only read of `bl` in either is the block at the
head `o` (`HoonMap.get bl o`), so where the head's block in `out` is still
the one of `bl` the step is the same as on `out` alone (`switchTag_out`,
`switchPlain_out`), which is the form `tag_keeps_of` takes.

Left for the walk (`switchWalk_keeps`, not proved): that the head of a later
chain still has its block of `bl` in `out` (it is not in `done`, and the
tree nodes of earlier regions are labels of those regions or fresh labels,
neither of which is a member of `topo` after it), and `TagHyp` carried from
`bl` to `out` (the earlier regions are disjoint from the later chain by
`labs_into`, so the blocks the later chain reads are unchanged, and the
fields over `Reach out k` need the tree nodes of earlier regions to mention
only their regions' registers and to jump only to their hits and miss).
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
