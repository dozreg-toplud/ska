import lemmas.Ska.CompModel
import lemmas.Exec

/-!
# The noun of the state of `+comp`

The door `|_  gen=line-short` of `+comp` threads the 10-tuple

    [re-gen bo-gen id-gen mode blocks tags cond cache soft sofs]

`Gen` of `Ska/CompModel.lean` keeps the first seven fields (`mode` as the
flag `drop`) and leaves out `cache`, `soft` and `sofs`.  `genNoun g x` is the
Hoon's noun with those three carried as opaque nouns (`GenRest`), so that a
link of an arm that neither reads nor writes them is an exact equality over
`genNoun`.  The fields sit at axes `2`, `6`, `14`, `30`, `62`, `126`, `254`
(`cond`), `510` (`cache`), `1022` (`soft`) and `1023` (`sofs`).

The encodings are the shared ones of `Ska/Types.lean` that the interpreter
links use: `Blob.toNoun` (with `Pole.toNoun`, `Termin.toNoun`), `listNoun A`
for a region, and `HoonMap.toNoun`.  A value of `cond`, `[def=@uvre
tag=(list @uxid)]`, is `[def tag]`.

The arms `+re`, `+oo`, `+id`, `+dropping`, `+set-tag`, `+emir`, `+emit` and
`+add-ops` read and write only the first seven fields.  `re_noun`, `oo_noun`,
`id_noun` are what their Hoon builds on the noun (`[re-gen.gen gen(re-gen
+(re-gen.gen))]`, an edit at axis `2`, `6`, `14`): the model's result,
encoded.  The pill's arms of the door are not linked yet.
-/

namespace Formalization
namespace Compiler

open Nock SkaModel SkaModel.Comp

/-- `%drop` and `%run`. -/
def cgModeNoun (drop : Bool) : Noun := if drop then A 0x706f7264 else A 0x6e7572

/-- The fields of `line-short` that `Gen` leaves out. -/
structure GenRest where
  cache : Noun
  soft : Noun
  sofs : Noun

variable {Map : Type → Type} [HoonMap Map]

/-- A value of `cond`. -/
def condValNoun (p : Nat × List Nat) : Noun := C (A p.1) (listNoun A p.2)

/-- The noun of the state of `+comp`. -/
def genNoun (g : Gen Map) (x : GenRest) : Noun :=
  C (A g.re) (C (A g.bo) (C (A g.id) (C (cgModeNoun g.drop)
    (C (HoonMap.toNoun Blob.toNoun g.blocks) (C (HoonMap.toNoun (listNoun A) g.tags)
      (C (HoonMap.toNoun condValNoun g.cond) (C x.cache (C x.soft x.sofs))))))))

theorem genNoun_re (g : Gen Map) (x : GenRest) : slot? 2 (genNoun g x) = some (A g.re) := by
  simp only [genNoun, nock_exec]
theorem genNoun_bo (g : Gen Map) (x : GenRest) : slot? 6 (genNoun g x) = some (A g.bo) := by
  simp only [genNoun, nock_exec]
theorem genNoun_id (g : Gen Map) (x : GenRest) : slot? 14 (genNoun g x) = some (A g.id) := by
  simp only [genNoun, nock_exec]
theorem genNoun_mode (g : Gen Map) (x : GenRest) :
    slot? 30 (genNoun g x) = some (cgModeNoun g.drop) := by
  simp only [genNoun, nock_exec]
theorem genNoun_blocks (g : Gen Map) (x : GenRest) :
    slot? 62 (genNoun g x) = some (HoonMap.toNoun Blob.toNoun g.blocks) := by
  simp only [genNoun, nock_exec]
theorem genNoun_tags (g : Gen Map) (x : GenRest) :
    slot? 126 (genNoun g x) = some (HoonMap.toNoun (listNoun A) g.tags) := by
  simp only [genNoun, nock_exec]

/-- `+re` on the noun: `[re-gen.gen gen(re-gen +(re-gen.gen))]`. -/
theorem re_noun (g : Gen Map) (x : GenRest) :
    (edit? 2 (A (g.re + 1)) (genNoun g x)).map (C (A g.re)) =
      (re g).map fun p => C (A p.1) (genNoun p.2 x) := by
  simp only [genNoun, re, nock_exec, Option.map_some]

/-- `+oo` on the noun: an edit at axis `6`. -/
theorem oo_noun (g : Gen Map) (x : GenRest) :
    (edit? 6 (A (g.bo + 1)) (genNoun g x)).map (C (A g.bo)) =
      (oo g).map fun p => C (A p.1) (genNoun p.2 x) := by
  simp only [genNoun, oo, nock_exec, Option.map_some]

/-- `+id` on the noun: an edit at axis `14`. -/
theorem id_noun (g : Gen Map) (x : GenRest) :
    (edit? 14 (A (g.id + 1)) (genNoun g x)).map (C (A g.id)) =
      (freshId g).map fun p => C (A p.1) (genNoun p.2 x) := by
  simp only [genNoun, freshId, nock_exec, Option.map_some]

end Compiler
end Formalization
