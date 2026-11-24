import lemmas.Ska.OptDriverTopo

/-!
# `+switch-chains`: what it does, and its preservation statement

`+switch-chains` (`nock-compilation.hoon`, about line 9135) runs once, after
the loop of `+optimize`, and is the only pass that makes `%lti`.  It is not
modelled yet.  Line by line:

1. `topo` by `+bb-topo`, `rev` by `+rev-cfg`, and `uses`: how many times each
   register is mentioned (parameters, `+get-regs` of every op and end).
2. `test-of p`: the block `p` ends in a `%clq s` whose yes side `y` has `p` as
   its only predecessor, no parameters, a body of exactly a `%hed s d` and an
   `%imm c r` (in either order), and an `%eqq` of `d` and `r` whose no side
   is the no side of the `%clq`; `c` an atom below `2^31`, `d` and `r`
   mentioned twice each.  `chain-of p`: the tests chained through the no
   sides, each an empty block reached from the two blocks of the test before
   only, on the same `s`.
3. `plain-of p`: the block ends in an `%eqq` of a register `d` and a register
   `r` its body sets by an `%imm c r` (`c` an atom below `2^31`, `r` mentioned
   twice, `l ≠ r`).  `plains-of p`: the chain through the no sides, each a
   block with no parameters, a body of one `%imm`, reached from the test
   before only, on the same `d`.
4. `cases`: the first case of each constant, sorted.  `tree`: a binary
   search over the cases, a leaf an `%imm c r` with an `%eqq d r` to its hit
   or to the miss, an inner node an `%lti` on the constant of the first case
   of its upper half.
5. The walk over `topo` (blocks of a chain done are skipped): a chain of
   four tests or more replaces its blocks by the tree under the yes side of
   the first test, which does the `%hed` first, and the first block's end
   becomes the `%clq` to it and to the final miss; else a chain of four plain
   tests or more puts the root of the tree at the end of the first block
   (without its `%imm` of the first constant) and the other nodes in the
   blocks of the chain and new labels from `nex`, the first label no block
   has.

## What preservation needs

The search takes the hit of the first case of the constant the register
holds, and the miss otherwise, as the chain does: the chain tests the cases in
order, the first equal one wins, and `cases` keeps the first of each constant.
The `%hed` moves to the root, where the chain did it after the `%clq`, so on
the yes side only.  The `%imm` ops of the chain are dropped from blocks the
search no longer passes (`uses = 2` makes sure nothing else reads them).  The
dropped blocks are reached only from the chain (`rev`), so no other jump
changes.  `ReadsOK` is needed where the chain read `d` or `r` and the tree
reads it in another place; `%lti` reads its register and compares an atom.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Opt

variable {Map : Type → Type} [HoonMap Map]

/-- **The preservation statement of `+switch-chains`** (open), for the pass
as a function on blocks: `Keeps` on blocks with `DInv`.  It is the field
`switch` of `DriverRest`. -/
def SwitchKeeps (switch : Map Blob → Option (Map Blob)) : Prop :=
  ∀ (c : Straight Map) bl', DInv c.blocks → switch c.blocks = some bl' → Keeps c (withBlocks c bl')

/-- `SwitchKeeps` gives the field `switch` of `DriverRest`. -/
theorem switch_field {switch : Map Blob → Option (Map Blob)} (h : SwitchKeeps switch) :
    ∀ (bl : Map Blob) bl', DInv bl → switch bl = some bl' → KeepsB bl bl' :=
  fun bl bl' hb hs c hc => by subst hc; exact h c bl' hb hs

end Opt
end SkaModel
end Formalization
