import lemmas.Compiler.PokeLinkHotJets
import lemmas.Compiler.PokeLinkColeUpd

/-!
# The models of the pokes other than `%full` (track P, README Gaps 23)

The route's choice for `Ar.jetsPoke` (`jetsPokeP`), read off the pill's
`%jets` branch of `+poke` and `+ska-cole-settle`, and checked against the
real compiler (`tools/hoon/hotempty.hoon`, `%jmod`):

* on `[%jets ~]` at `jets-hot = ~`: `hot = (malt ~) = ~`, so the test of the
  branch holds exactly when `pend` is `~` (`[%drop ~]`, the state kept,
  `pokeN_jets_idle`); else `+ska-cole-settle` with the key set `~`: a `+rep:by`
  over `code` (`settleStepO`: a bell with a ring is kept, else `gut:by seek`
  with `&`, `+cole-match` on `pend` and `arms`, `+cole-put` and `put:in rung`
  on a ring), then `pend := ~`; `+hot-stale` of `(hot-diff ~ ~) = ~` with
  `hot = ~` is `~` (no ring is driven, no ring differs), so the cache is not
  touched and `[%drop ~]` is the product;
* any other `p` (an atom other than `~`: the mold crashes; a cell: `Hot`), or
  `jets-hot` not `~` (no reached state, `reach_hotEmpty`): no answer.

The cache is NOT recompiled at the new `call.cole` (track K's finding: a
cached caller keeps `%jmp` where a fresh compile would emit `%jmf`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeM FinMap

/-- `(~(gut by seek) b &)` on the answer of `get:by`. -/
def gutYes : Option Noun → Option Noun
  | some (Noun.atom 0) => some (A 0)
  | some (Noun.cell (Noun.atom 0) v) => some v
  | _ => none

/-- **The step gate of `+ska-cole-settle`** on a node `[b entry]` of `code`
and the pair `[rung [call back]]`: a bell with a ring in `call` is skipped;
else `+cole-match` of `b` with `(~(gut by seek) b &)` on `pend` and `arms`,
and on `[~ r]` the bell joins `rung` and `+cole-put` puts it. -/
noncomputable def settleStepO (seekN pend arms hot : Noun) : Noun → Noun → Option Noun
  | Noun.cell b _, Noun.cell rung (Noun.cell ca bk) =>
    match getF mugF b ca with
    | some (Noun.atom 0) =>
      (gutYes (getF mugF b seekN)).bind fun sek =>
        match coleMatchP b sek pend arms hot with
        | some (Noun.atom 0) => some (C rung (C ca bk))
        | some (Noun.cell (Noun.atom 0) r) =>
          (putInF mugF b rung).bind fun rung' => (colePutO b r (C ca bk)).map (C rung')
        | _ => none
    | some _ => some (C rung (C ca bk))
    | none => none
  | _, _ => none

/-- **`+ska-cole-settle`** of the jets noun `[root core batt arms pend cole]`
over the code noun `codeN` and the seek noun `seekN`, with the ring set `hot`:
`rung` and the new jets noun.  With `pend = ~` it is `[~ j]`. -/
noncomputable def settleO (codeN seekN hot : Noun) : Noun → Option (Noun × Noun)
  | Noun.cell r1 (Noun.cell r2 (Noun.cell r3 (Noun.cell ar (Noun.cell pd cole)))) =>
    if pd = A 0 then some (A 0, C r1 (C r2 (C r3 (C ar (C pd cole))))) else
    (repO (settleStepO seekN pd ar hot) codeN (C (A 0) cole)).bind fun
      | Noun.cell rung cole' => some (rung, C r1 (C r2 (C r3 (C ar (C (A 0) cole')))))
      | Noun.atom _ => none
  | _ => none

/-- The seek noun of `long-ska` (as `longNoun` lays it out). -/
noncomputable def seekNoun (L : LongB FinMap) : Noun := L.code.toNoun fun e => e.seek.toNoun

/-- **The model of the `%jets` branch** (the route's choice for
`Ar.jetsPoke`): on `p = ~` at `jets-hot = ~`, no stale bell, the settled jets
noun, `jets-hot = ~`, the cache unchanged. -/
noncomputable def jetsPokeP (fl : Flags) (st : PSt) (p : Noun) :
    Option (List Bell × Noun × Noun × Cache FinMap (TreapMap mugF) (Noun × Noun)) :=
  if p = A 0 ∧ st.hot = A 0 then
    (settleO (codeNoun fl st.long.code) (seekNoun st.long) (A 0) st.jets).map fun r => ([], r.2, A 0, st.cache)
  else none

/-- With `pend = ~` the model keeps the jets noun. -/
theorem settleO_idle (codeN seekN hot r1 r2 r3 ar cole : Noun) :
    settleO codeN seekN hot (C r1 (C r2 (C r3 (C ar (C (A 0) cole))))) =
      some (A 0, C r1 (C r2 (C r3 (C ar (C (A 0) cole))))) := by
  simp [settleO]

/-- The model on `[%jets ~]` at `jets-hot = ~`. -/
theorem jetsPokeP_nil (fl : Flags) (st : PSt) (hh : st.hot = A 0) :
    jetsPokeP fl st (A 0) =
      (settleO (codeNoun fl st.long.code) (seekNoun st.long) (A 0) st.jets).map fun r => ([], r.2, A 0, st.cache) := by
  simp [jetsPokeP, hh]

end Compiler
end Formalization
