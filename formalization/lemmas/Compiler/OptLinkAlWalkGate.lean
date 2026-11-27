import lemmas.Compiler.OptLinkAlWalkTurn

/-!
# `+alias`: the walk, the gate and `AliasLink` (phase 16, README Gaps 13)

* `al_walk`: **the walk `alWalk` on `topo` is `aliasWalk`**, by induction on
  `topo` from `al_end` and `al_turn`, carrying `RevNodup`, `BrzInv` and
  `NoLti` of `g.new` (`revNodup_block`, `brzInv_block`, `noLti_block`).
* `al_gate`: **the gate body read from the pill (`aliasBody`) is `aliasM`**
  for `pick = Ana.pickR FinMap`: `aliasBody_eq`, the prelude `al_prelude`,
  the start `genRel_start`, then `al_walk`.
* **`al_link`**: `AliasLink P` for every `P` with `P.alias = aliasM
  (Ana.pickR FinMap)` (its first conjunct `aliasM_noLti`), given the three
  named hypotheses of `OptLinkAlWalkTurn.lean` (`AlStartLink`, `AlParsLink`,
  `AlBodyLink`).
* `opt_gate_alias`: `opt_gate_sw` with `AliasLink` so discharged: the pill's
  `+optimize` is linked to `optimizeF` given only those three.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local instance] SkaModel.Ana.tkeyNat

/-- **Phase 16, the walk**: `alWalk` on `topo` from `gen` `GenRel g` returns
`[folded new]` of the state `aliasWalk` ends in. -/
theorem al_walk (h9 : AlStartLink) (h12 : AlParsLink) (h13 : AlBodyLink) (nargs : Nat)
    (bl : TreapMap mugF Blob) (hbl : NoLti bl) (RV : Noun) :
    ∀ (topo : List Nat) (g g' : Opt.AGen (TreapMap mugF)) (GEN : Noun), GenRel g GEN → Opt.RevNodup g.rev →
      Opt.BrzInv g → NoLti g.new → Opt.aliasWalk (Ana.pickR FinMap) nargs bl topo g = some g' →
      nock (alWS GEN (A nargs) (HoonMap.toNoun Blob.toNoun bl) RV (listNoun A topo)) alWalk
        = some (C (flag g'.folded) (HoonMap.toNoun Blob.toNoun g'.new))
  | [], g, g', GEN, hg, _, _, _, h => by
    cases h
    exact al_end hg _ _ _
  | o :: topo, g, g', GEN, hg, hn, hz, hl, h => by
    simp only [Opt.aliasWalk] at h
    obtain ⟨g1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨GEN1, hG1, hN⟩ := al_turn h9 h12 h13 hg hn hz hl nargs bl hbl RV (listNoun A topo) o h1
    simp only [listNoun]
    rw [hN]
    exact al_walk h9 h12 h13 nargs bl hbl RV topo g1 g' GEN1 hG1 (Opt.revNodup_block hn h1)
      (Opt.brzInv_block hz h1) (noLti_of_opt (Opt.noLti_block (noLti_opt hbl) (noLti_opt hl) h1)) h

/-- **The gate body of `+alias`** (`aliasBody`, read from the pill) is
`aliasM (Ana.pickR FinMap)`. -/
theorem al_gate (h9 : AlStartLink) (h12 : AlParsLink) (h13 : AlBodyLink) (nargs : Nat)
    (bl : TreapMap mugF Blob) (hbl : NoLti bl) (rev : TreapMap mugF (List Nat)) (topo : List Nat)
    (ra : Bool × TreapMap mugF Blob) (h : Opt.aliasM (Ana.pickR FinMap) nargs bl rev topo = some ra) :
    nock (C aliasBody (C (C (A nargs) (C (HoonMap.toNoun Blob.toNoun bl) (C (jarN rev) (listNoun A topo)))) optC))
      aliasBody = some (C (flag ra.1) (HoonMap.toNoun Blob.toNoun ra.2)) := by
  rw [aliasBody_eq]
  obtain ⟨R0, hR, hP⟩ := al_prelude (A nargs) (HoonMap.toNoun Blob.toNoun bl) (listNoun A topo) rev
  rw [hP]
  unfold Opt.aliasM at h
  obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp h
  exact al_walk h9 h12 h13 nargs bl hbl (jarN rev) topo (alG0 rev) g (alGen0 R0) (genRel_start hR)
    (Opt.revNodup_init rev) (Opt.brzInv_empty fun p => HoonMap.get_empty p)
    (fun p b hb => by simp [alG0, HoonMap.get_empty] at hb) hg

/-- **`AliasLink`** for the passes whose `+alias` is `aliasM (Ana.pickR
FinMap)`, given phases 9 and 10 (`AlStartLink`), 12 (`AlParsLink`) and the
statement of `al_body_gen` (`AlBodyLink`). -/
theorem al_link (P : Opt.Passes (TreapMap mugF)) (hP : P.alias = Opt.aliasM (Ana.pickR FinMap))
    (h9 : AlStartLink) (h12 : AlParsLink) (h13 : AlBodyLink) : AliasLink P := by
  intro nargs bl rev topo ra hl h
  rw [hP] at h
  exact ⟨noLti_of_opt (Opt.aliasM_noLti (noLti_opt hl) h), al_gate h9 h12 h13 nargs bl hl rev topo ra h⟩

/-- **`+optimize`** linked with `AliasLink` discharged by `al_link`. -/
theorem opt_gate_alias (P : Opt.Passes (TreapMap mugF)) (hP : P.alias = Opt.aliasM (Ana.pickR FinMap))
    (h9 : AlStartLink) (h12 : AlParsLink) (h13 : AlBodyLink)
    (hPt : ∀ bl topo rev, P.trim bl topo rev = Opt.trimTraceHints bl topo rev) (sfuel : Nat)
    (hPs : ∀ bl, P.switch bl = Opt.switchChains sfuel bl)
    (fuel : Nat) (s s' : Straight (TreapMap mugF)) (hl : NoLti s.blocks) (h : Opt.optimizeF fuel P s = some s') :
    nock (C optBody (C s.toNoun optC)) optBody = some s'.toNoun :=
  opt_gate_sw P (al_link P hP h9 h12 h13) hPt sfuel hPs fuel s s' hl h

end Compiler
end Formalization
