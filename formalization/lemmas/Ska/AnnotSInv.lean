import lemmas.Ska.AnnotSBake
import lemmas.Ska.AnnotSFol

/-!
# `InvBSR` is a theorem (track Q, README Gaps 27)

`folTopK`: the hypothesis `FolTopK` of the memo and poke strands
(`AnnotSMemo.lean`) is `folTopR_annotK` (`AnnotSFol.lean`).

`InvK`: the invariant of the states the pokes reach: `InvB`, a ghost
`PokeInvK` of the memo (the analysis's nomms satisfy `AnnotK`: `Annot` with
`DetK` of the formula part at a direct call with no memo key), and `CodeOKS`
of the real table.  `SkaStep`: one `skaPokeB` poke on a root sock that is
well formed, normal and not `%void` (the hypotheses of `skaPokeB_sound`).

**`invBSR_skaPokeB`**: `InvBSR` with `I := InvK`: inside `InvB`, true of the
empty state, kept by every step (`skaPokeB_soundK`), giving `CodeOKS`.
`inlAnnot_of_invK`: `inlAnnot` on the states of `InvK`, from `InlPill` alone.
-/

namespace Formalization
namespace SkaModel
namespace AnnotSF

open Nock Ana Bake PokeM

/-- The hypothesis of the memo and poke strands holds. -/
theorem folTopK (lib : Lib) : FolTopK lib :=
  fun _ _ hT _ _ _ _ _ hwf h => folTopR_annotK hT hwf h

section State

variable {M : Type → Type → Type} [Treap M]

/-- **The invariant of the reached states.** -/
def InvK (lib : Lib) (L : LongB M) : Prop :=
  InvB lib L ∧ (∃ code, PokeInvK lib L.memo code) ∧ Glue.CodeOKS lib (realOf L.code)

/-- One poke of `+ska-poke` up to the code table, on a root sock that is well
formed, normal and not `%void`, with any parameters. -/
def SkaStep (M : Type → Type → Type) [Treap M] (R : Type) (L L' : LongB M) : Prop :=
  ∃ (env : Env R) (jet : (Bell → Option Datum) → R → Bell → Bool) (fold frozen : Bool) (n : Nat)
    (bf : BEnv M → Nat) (root : Ident) (reg reg' : R) (rb : Bell),
    WellFormed root.1 ∧ NormSock root.1 ∧ root.1 ≠ Sock.void ∧
      skaPokeB env jet fold frozen n bf root L reg = some (rb, L', reg')

/-- **`InvBSR` holds of the pokes of `+ska-poke`**, with the invariant
`InvK`. -/
theorem invBSR_skaPokeB (M : Type → Type → Type) [Treap M] (R : Type) (lib : Lib) :
    InvBSR M lib (SkaStep M R) := by
  refine ⟨InvK lib, fun _ h => h.1, ⟨InvB.init lib, ⟨_, PokeInvK.init lib⟩, ?_⟩, ?_, fun _ h => h.2.2⟩
  · intro bl nb hb
    simp [realOf, Treap.get_empty] at hb
  · rintro L L' ⟨hB, hpk, hS⟩ ⟨env, jet, fold, frozen, n, bf, root, reg, reg', rb, hw, hnr, hnv, h⟩
    obtain ⟨h1, h2, h3, -⟩ := skaPokeB_soundK (folTopK lib) env hB hpk hS hw hnr hnv h
    exact ⟨h1, h2, h3⟩

/-- **`inlAnnot` on the reached states**, from `InlPill` alone. -/
theorem inlAnnot_of_invK {lib : Lib} {Map : Type → Type} [HoonMap Map] {J H : Type}
    {D : CompData M Map J H} (hP : Glue.InlPill lib D) :
    ∀ long jets hot b nm, InvK lib long → D.inl long jets hot b = some nm →
      Annot lib (realOf long.code) (Fits b.less) b.fol nm :=
  inlAnnot_of_inv hP (fun _ h => h.1) (fun _ h => h.2.2)

end State

end AnnotSF
end SkaModel
end Formalization
