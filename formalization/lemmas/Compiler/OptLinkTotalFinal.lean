import lemmas.Compiler.OptLinkTotalReads
import lemmas.Ska.RawInvATX

/-!
# The totality of `+optimize` on raw output of `FragX`

`readsKeep_of`: `ReadsKeep` (`OptLinkTotalN.lean`) for the passes of the
Hoon at `DInvR`, from the per-pass facts of `OptLinkTotalReads.lean`
(`hops_reads`, `rub_reads`, `mid_reads`, `trim_reads`, `dead_reads`), given
**`AliasReadsN`**: the model of `+alias` keeps `ReadsIn N` (open).

**`gateTotalN_of`**: track D's `GateTotalN` (`RawInvStX.lean`), given
`AliasReadsN`.  **`opt_total_finishLFX'`**, **`opt_total_finishLUX'`**: the
pill's `+optimize` returns on the raw output of every nomm of `FragX`, for
both final passes, given only `AliasReadsN` (`AliasRetN` is `aliasRetN_of`,
`RunAT` is track D's `runAT_fragX`).
-/

namespace Formalization
namespace Compiler

open Nock SkaModel Opt Comp Raw Pill Hoon

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

section
variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

/-- **`+alias` keeps `ReadsIn N`** (open): on blocks with `DInvR`, `TopoInvR`
and `ReadsIn N`, the output of the model at `N` has `ReadsIn N`. -/
def AliasReadsN (Map : Type → Type) [HoonMap Map] [MapKeys Map] (pick : List Nat → Nat) : Prop :=
  ∀ N (bl : Map Blob) topo rev f bl', DInvR bl → TopoInvR bl topo rev → ReadsIn N bl →
    aliasM pick N bl rev topo = some (f, bl') → ReadsIn N bl'

/-- **`ReadsKeep` for the passes of the Hoon**, given `AliasReadsN`. -/
theorem readsKeep_of {pick : List Nat → Nat} (hA : AliasReadsN Map pick) (sfuel N : Nat) :
    ReadsKeep (Map := Map) ⟨aliasM pick, trimTraceHints, switchChains sfuel⟩ N DInvR where
  hops := fun _ _ _ _ _ _ hJ hT hR h => hops_reads hT.1.1.1 hT.1.1.2.1 hJ.2.1 h hR
  rub := fun _ _ _ _ hR h => rub_reads h hR
  middle := fun _ _ _ _ _ hR h => mid_reads h hR
  alias := fun bl topo rev f bl' hJ hT hR h => hA N bl topo rev f bl' hJ hT hR h
  trim := fun _ _ _ _ _ _ hR h => trim_reads h hR
  dead := fun _ _ _ _ hJ hT hR h => dead_reads hT.1.1 h hJ.2.1 hR

end

/-- **`GateTotalN`**, given `AliasReadsN`. -/
theorem gateTotalN_of (hA : AliasReadsN (TreapMap mugF) (Ana.pickR FinMap)) : GateTotalN :=
  fun ρ L _ s hI hJ hR => opt_gate_totalN_of s (fun sfuel => readsKeep_of hA sfuel s.nargs) hI hJ hR

section
variable {S : Type} [HoonSet S]

open Pill Hoon in
/-- **The pill's `+optimize` returns on the raw n-ary code of every nomm of
`FragX`**, given `AliasReadsN` only. -/
theorem opt_total_finishLFX' (hA : AliasReadsN (TreapMap mugF) (Ana.pickR FinMap))
    {nm : Nomm} (hf : FragX (S := S) nm) (hc : sixCount nm ≤ 255)
    {ord : NeedOrd} {less : Cape} {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, []))
    {c' : Straight (TreapMap mugF)} (h : finishLF (S := S) (Map := TreapMap mugF) nm ord less bake = some c') :
    ∃ sfuel fuel s', Opt.optimizeF fuel ⟨Opt.aliasM (Ana.pickR FinMap), Opt.trimTraceHints,
      Opt.switchChains sfuel⟩ c' = some s' ∧ nock (C optBody (C c'.toNoun optC)) optBody = some s'.toNoun :=
  opt_total_finishLFX_at (gateTotalN_of hA) (fun ρ L => aliasRetN_of _ (fun l hl => Ana.pickR_mem l hl) ρ L)
    hf hc hbake h

open Pill Hoon in
/-- **The same for the raw whole-subject code.** -/
theorem opt_total_finishLUX' (hA : AliasReadsN (TreapMap mugF) (Ana.pickR FinMap))
    {nm : Nomm} (hf : FragX (S := S) nm) (hc : sixCount nm ≤ 255)
    {c' : Straight (TreapMap mugF)} (h : finishLU (S := S) (Map := TreapMap mugF) nm = some c') :
    ∃ sfuel fuel s', Opt.optimizeF fuel ⟨Opt.aliasM (Ana.pickR FinMap), Opt.trimTraceHints,
      Opt.switchChains sfuel⟩ c' = some s' ∧ nock (C optBody (C c'.toNoun optC)) optBody = some s'.toNoun :=
  opt_total_finishLUX_at (gateTotalN_of hA) (fun ρ L => aliasRetN_of _ (fun l hl => Ana.pickR_mem l hl) ρ L) hf hc h

end

end Compiler
end Formalization
