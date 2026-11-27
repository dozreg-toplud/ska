import lemmas.Glue.MonoCalls
import lemmas.Glue.Entry
import lemmas.Ska.RawInvATX

/-!
# `rawEntry` on `FragX`

LEDGER 2.c.  `entryOK_of` (`Glue/Entry.lean`) gives `EntryOK` from
`DefFirst`, `ReadsIn` at the argument count, `NoPoison` and `CelGuard`.  On
the raw output of `FragX` track D proved the first two (`optIn_finishLUX`,
`optIn_finishLFX` give `OptIn`, whose field `defFirst` is `DefFirst`;
`optInput_finishLUX_at`, `optInput_finishLFX_at` give `ReadsIn`).  The other
two are the LEAVES `GuardMonoX`, `GuardNaryX` (static facts of the raw
blocks of the model, checked on all of `enumX` and `enumCX`,
`Glue/EntryCheck.lean`).

* `entry_finishLUX`, `entry_finishLFX`: `EntryOK` of the raw code of `FragX`
  on every entry of the right length, for every oracle, scry gate, state and
  trace (no hypothesis on the subject: the check found none needed).
* `entryMono_fragX`, `entryNary_fragX`: the leaves `EntryMono`,
  `EntryNary` of `Glue/MonoCalls.lean` on the lifted classes.
* `rawEntry_fragX`: the field `rawEntry` of `CompRestO` on `FragX` from the
  reference side alone.
* `CompRestOE`: `CompRestO` without `rawEntry`; `compHyp_of_fragX'`:
  `CompHyp` from it and the two leaves.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Ana Bake PokeM

variable {M : Type → Type → Type} [Treap M] {Map : Type → Type} [HoonMap Map] [Comp.HoonMapKeys Map]
  [Opt.MapKeys Map] {J H CR : Type}

variable {S : Type} [Comp.HoonSet S]

/-! ## The two leaves -/

/-- **Leaf: the raw whole-subject code of `FragX` passes no `~` and guards
every `%hed` / `%tal` by a `%cel`.** -/
def GuardMonoX (S : Type) [Comp.HoonSet S] (Map : Type → Type) [HoonMap Map] [Comp.HoonMapKeys Map]
    [Opt.MapKeys Map] : Prop :=
  ∀ nm (c : Straight Map), Comp.FragX (S := S) nm → Comp.sixCount nm ≤ 255 →
    Comp.finishLU (S := S) (Map := Map) nm = some c → NoPoison c.blocks ∧ CelGuard c.blocks

/-- **Leaf: the same of the raw n-ary code of `FragX`, nothing baked.** -/
def GuardNaryX (S : Type) [Comp.HoonSet S] (Map : Type → Type) [HoonMap Map] [Comp.HoonMapKeys Map]
    [Opt.MapKeys Map] : Prop :=
  ∀ nm ord less (bake : Comp.Need → Comp.Need × List (Nat × Noun)) (c : Straight Map),
    Comp.FragX (S := S) nm → Comp.sixCount nm ≤ 255 → (∀ ned, bake ned = (ned, [])) →
    Comp.finishLF (S := S) (Map := Map) nm ord less bake = some c → NoPoison c.blocks ∧ CelGuard c.blocks

/-! ## Argument counts -/

theorem split_length : ∀ (n : NeedOrd) (x : Noun) (a : List Noun), SkaModel.split n x = some a →
    a.length = Comp.countArgs n
  | NeedOrd.none, _, a, h => by simp [SkaModel.split] at h; subst h; rfl
  | NeedOrd.this, _, a, h => by simp [SkaModel.split] at h; subst h; rfl
  | NeedOrd.pair p q, Noun.cell u v, a, h => by
    simp only [SkaModel.split, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨a1, h1, a2, h2, rfl⟩ := h
    simp [Comp.countArgs, split_length p u a1 h1, split_length q v a2 h2]
  | NeedOrd.both p q, Noun.cell u v, a, h => by
    simp only [SkaModel.split, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨a1, h1, a2, h2, rfl⟩ := h
    simp [Comp.countArgs, split_length p u a1 h1, split_length q v a2 h2]
  | NeedOrd.pair _ _, Noun.atom _, a, h => by simp [SkaModel.split] at h
  | NeedOrd.both _ _, Noun.atom _, a, h => by simp [SkaModel.split] at h

theorem finishLF_nargs {nm : Nomm} {ord : NeedOrd} {less : Cape} {bake : Comp.Need → Comp.Need × List (Nat × Noun)}
    {c : Straight Map} (h : Comp.finishLF (S := S) (Map := Map) nm ord less bake = some c) :
    c.nargs = Comp.countArgs c.need := by
  unfold Comp.finishLF at h
  obtain ⟨⟨nex, g1⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  by_cases ha : nex.th.args ≠ []
  · rw [if_pos ha] at h; cases h
  rw [if_neg ha] at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  exact Comp.toStraightF_nargs h

theorem finishLU_nargs1 {nm : Nomm} {c : Straight Map} (h : Comp.finishLU (S := S) (Map := Map) nm = some c) :
    c.nargs = 1 := by
  unfold Comp.finishLU at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  exact (toStraightF_this h).2

/-! ## `EntryOK` of the raw code of `FragX` -/

/-- **`EntryOK` of the raw whole-subject code of `FragX`**, entered with any
one value. -/
theorem entry_finishLUX (hg : GuardMonoX S Map) {nm : Nomm} (hf : Comp.FragX (S := S) nm)
    (hc : Comp.sixCount nm ≤ 255) {c : Straight Map} (h : Comp.finishLU (S := S) (Map := Map) nm = some c)
    (x : Noun) (lib : Lib) {σ : Type} (O : Oracle σ) (gul : Noun) (st : σ) (t : Trace) :
    Opt.EntryOK lib O c gul st [x] t := by
  obtain ⟨hP, hG⟩ := hg nm c hf hc h
  obtain ⟨_, _, _, hR⟩ := Raw.optInput_finishLUX_at hf hc h
  exact entryOK_of (Raw.optIn_finishLUX hf hc h).defFirst hR hP hG (by rw [finishLU_nargs1 h]; simp) lib O gul st t

/-- **`EntryOK` of the raw n-ary code of `FragX`**, entered with the split
of any subject by its need. -/
theorem entry_finishLFX (hg : GuardNaryX S Map) {nm : Nomm} (hf : Comp.FragX (S := S) nm)
    (hc : Comp.sixCount nm ≤ 255) {ord : NeedOrd} {less : Cape} {bake : Comp.Need → Comp.Need × List (Nat × Noun)}
    (hbake : ∀ ned, bake ned = (ned, [])) {c : Straight Map}
    (h : Comp.finishLF (S := S) (Map := Map) nm ord less bake = some c)
    (x : Noun) (args : List Noun) (hargs : SkaModel.split c.need x = some args)
    (lib : Lib) {σ : Type} (O : Oracle σ) (gul : Noun) (st : σ) (t : Trace) :
    Opt.EntryOK lib O c gul st args t := by
  obtain ⟨hP, hG⟩ := hg nm ord less bake c hf hc hbake h
  obtain ⟨_, _, _, hR⟩ := Raw.optInput_finishLFX_at hf hc hbake h
  exact entryOK_of (Raw.optIn_finishLFX hf hc hbake h).defFirst hR hP hG
    (by rw [finishLF_nargs h, split_length _ _ _ hargs]; exact Nat.le_refl _) lib O gul st t

/-- **The leaf `EntryMono` on `FragX`**, from `GuardMonoX`. -/
theorem entryMono_fragX (lib : Lib) (hg : GuardMonoX S Map) : EntryMono S Map lib (liftMC (FragXM S)) := by
  intro env N bl nm s hf hs x _ σ O gul st t
  rw [Comp.finishLUCM_eq _ (Comp.noDirect_of_fragX hf.1),
    Comp.finishLUC_eq _ (Nomm.noCall_of_pure nm (Comp.fragX_pure hf.1))] at hs
  exact entry_finishLUX hg hf.1 hf.2 hs x lib O gul st t

/-- **The leaf `EntryNary` on `FragX`**, from `GuardNaryX`. -/
theorem entryNary_fragX (lib : Lib) (hg : GuardNaryX S Map) : EntryNary S Map lib (liftNC (FragXN S)) := by
  intro env N bl cape bake nm ord s hf hs x _ args hargs σ O gul st t
  rw [Comp.finishLFC_eq _ (Nomm.noCall_of_pure nm (Comp.fragX_pure hf.1))] at hs
  exact entry_finishLFX hg hf.1 hf.2.1 hf.2.2 hs x args hargs lib O gul st t

/-! ## The field `rawEntry` and `CompHyp` on `FragX` -/

/-- **`rawEntry` of `CompRestO` on `FragX`**, from the reference side and
the two leaves. -/
theorem rawEntry_fragX {lib : Lib} {ref : Ref M Map J H} {D : CompData M Map J H}
    (P : RefSide S lib ref D (FragXM S) (FragXN S)) (hm : GuardMonoX S Map) (hn : GuardNaryX S Map) :
    ∀ long jets hot b m s, InvB lib long → ref long jets hot b m = some s →
      ∀ x, SkaModel.Fits b.less x → ∀ args, (if m then some [x] else SkaModel.split s.need x) = some args →
        ∀ (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ) (t : Trace), Opt.EntryOK lib O s gul st args t := by
  intro long jets hot b m s hI hr x _ args hargs σ O gul st t
  cases m with
  | true =>
    simp only [if_true, Option.some.injEq] at hargs
    subst hargs
    obtain ⟨nm, hnm, hs⟩ := P.refMono long jets hot b s hI hr
    have hf := P.inFragM long jets hot b nm hI hnm (by rw [hr]; rfl)
    rw [Comp.finishLUC_eq _ (Nomm.noCall_of_pure nm (Comp.fragX_pure hf.1))] at hs
    exact entry_finishLUX hm hf.1 hf.2 hs x lib O gul st t
  | false =>
    simp only [Bool.false_eq_true, if_false] at hargs
    obtain ⟨nm, nb, cape, data, hnb, hinl, hbl, hs⟩ := P.refNary long jets hot b s hI hr
    have hf := P.inFragN long jets hot b nm cape data hI hinl hbl (by rw [hr]; rfl)
    rw [Comp.finishLFC_eq _ (Nomm.noCall_of_pure nm (Comp.fragX_pure hf.1))] at hs
    exact entry_finishLFX hn hf.1 hf.2.1 hf.2.2 hs x args hargs lib O gul st t

section
variable (A : Arms M Map J H CR)

/-- **`CompRestO` without `rawEntry`**: every other field the field of
`CompRestO` of the same name, unchanged. -/
structure CompRestOE (S : Type) [Comp.HoonSet S] (M' : Type → Type → Type) [Treap M'] (A : Arms M Map J H CR)
    (lib : Lib) (ref : Ref M Map J H) (D : CompData M Map J H) (FM : Nomm → Prop)
    (FN : Cape → (Comp.Need → Comp.Need × List (Nat × Noun)) → Nomm → Prop) : Prop
    extends RefSide S lib ref D FM FN where
  optRef : OptRef M' A lib ref
  inlAnnot : ∀ long jets hot b nm, InvB lib long → D.inl long jets hot b = some nm →
    Annot lib (realOf long.code) (SkaModel.Fits b.less) b.fol nm
  callee : ∀ long jets hot b m, InvB lib long → Comp.CalleeNeeds (D.env long jets hot b m) (refN A ref long jets hot)
  unary : ∀ b scc long jets hot c s n c', A.compileUnary b scc long jets hot c = some ((s, n), c') →
    ref long jets hot b true = some s ∧ (CacheOK ref long jets hot c → CacheOK ref long jets hot c')
  scc : ∀ scc long jets hot c m c', A.compileScc scc long jets hot c = some (m, c') →
    (∀ b s, Treap.get m b = some s → ref long jets hot b false = some s) ∧
      (CacheOK ref long jets hot c → CacheOK ref long jets hot c')
  answers : ∀ st b m s, InvS lib ref st → ref st.long st.jets st.hot b m = some s →
    (compileStep A st b m).isSome
  stable : ∀ s f long jets hot r b m x, A.skaPoke s f long jets hot = some r → InvB lib long →
    ref long jets hot b m = some x → ref r.2.1 r.2.2.1 hot b m = some x
  jetRoot : ∀ s f long jets hot r out, A.skaPoke s f long jets hot = some r → InvB lib long →
    A.jetRoot r.2.2.1 hot r.1 = some out →
    out.nargs = 1 ∧ out.need = NeedOrd.this ∧
      ContractFwd lib (refN A ref r.2.1 r.2.2.1 hot) s f [s] out ∧
      ContractBwd lib (refN A ref r.2.1 r.2.2.1 hot) s f [s] out
  jets : ∀ st p r, ¬ HotOvum (Ovum.jets p) → A.jetsPoke st p = some r →
    CacheOK ref st.long st.jets st.hot st.cache → CacheOK ref st.long r.2.1 r.2.2.1 r.2.2.2
  fast : ∀ st rs p r, A.fastPoke st rs p = some r →
    CacheOK ref st.long st.jets st.hot st.cache → CacheOK ref st.long r.1 st.hot r.2

/-- **`CompHyp` when every nomm compiled is in `FragX`, with `rawEntry`
discharged**: from `CompRestOE` and the two leaves `GuardMonoX`,
`GuardNaryX` (`compHyp_of_fragX` with `rawEntry_fragX`). -/
theorem compHyp_of_fragX' {M' : Type → Type → Type} [Treap M'] {lib : Lib} {ref : Ref M Map J H}
    {D : CompData M Map J H} (P : CompRestOE S M' A lib ref D (FragXM S) (FragXN S))
    (hm : GuardMonoX S Map) (hn : GuardNaryX S Map) : CompHyp A lib ref :=
  compHyp_of_fragX A
    { toRefSide := P.toRefSide, rawEntry := rawEntry_fragX P.toRefSide hm hn, optRef := P.optRef,
      inlAnnot := P.inlAnnot, callee := P.callee, unary := P.unary, scc := P.scc, answers := P.answers,
      stable := P.stable, jetRoot := P.jetRoot, jets := P.jets, fast := P.fast }

end

end Glue
end SkaModel
end Formalization
