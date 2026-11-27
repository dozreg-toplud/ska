import lemmas.Ska.CompHypOfNC
import lemmas.Ska.RawInvWholeX
import lemmas.Ska.AnaEnds
import lemmas.Compiler.OptLinkTotalAvail

/-!
# Glue: `CompPieces` with track D's `OptIn` and the optimizer's own passes

`CompPieces` of `Ska/CompHypOf.lean` (2026-11-24) asks, for `+optimize`,
`rawDInv` (the raw blocks meet `DInvS`), `optEq` (`+optimize` is `optimizeF`
with the passes `D.optP` on EVERY straight), `optAlias` (`DriverRestSSA`) and
`optSSA` (`SSAKeepR`), and derives `Opt.Keeps` from them
(`optimize_keeps_ssaR`).  Since then track D proved `OptIn` of the raw blocks
on `FragX` (`optIn_finishLUX`, `optIn_finishLFX`) and that `+optimize` with
the pill's passes keeps every straight whose blocks meet `OptIn`
(`optimize_keeps_optIn`), and track H that the pill's `+optimize` returns on
the raw code of `FragX` (`optimize_total_finishLUX`, `-LFX`).

Here the four fields are replaced by two:
* `RawOptIn`: the raw blocks of every reference form meet `OptIn`;
* `OptRef`: on every reference form, `A.optimize` is `optimizeF` with the
  passes of the pill (`aliasM (pickR M')`, `trimTraceHints`,
  `switchChains sfuel`) at SOME fuels, per form (not one `sfuel` for all).

`CompRestO` is `CompRest` with that change; `CompPiecesO` adds `RawOptIn`
and the raw contract; `compHyp_of_piecesO` gives `CompHyp`, the hypothesis
of `gap_of_comp`, like `compHyp_of_pieces`.  On `FragX` (call-free, `%6`,
cons, `%5`, `%10`, at most 255 `%6`, nothing baked in the n-ary version),
`RawOptIn`, `rawMono` and `rawNary` follow from the reference side alone
(`compHyp_of_fragX`), and `OptRef` follows from the pill's totality given
that `A.optimize` is the pill's `+optimize` on reference forms and that
`Straight.toNoun` is injective (`optRef_fragX`).

`fullAnswers_of_cg` composes the halting side: `FullAnswers` of the model of
`+poke` from `CgHalts`, `MemoNoCallees` under `InvB`, `BakeEnds` and
`RootAnswers`, with the analysis fuel `anaFuel`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Ana Bake PokeM

variable {M : Type → Type → Type} [Treap M] {Map : Type → Type} [HoonMap Map] [Comp.HoonMapKeys Map]
  [Opt.MapKeys Map] {J H CR : Type}

/-! ## The two new fields -/

/-- **(c) restated with `OptIn`**: the raw blocks of every reference form of
a table with `InvB` meet track D's `OptIn` (in place of `DInvS`). -/
def RawOptIn (lib : Lib) (ref : Ref M Map J H) : Prop :=
  ∀ long jets hot b m s, InvB lib long → ref long jets hot b m = some s → Opt.OptIn s.blocks

/-- **(d) restated**: on every reference form, `A.optimize` is `optimizeF`
with the passes of the pill at some fuels (chosen per form). -/
def OptRef (M' : Type → Type → Type) [Treap M'] (A : Arms M Map J H CR) (lib : Lib)
    (ref : Ref M Map J H) : Prop :=
  ∀ long jets hot b m s, InvB lib long → ref long jets hot b m = some s →
    ∃ fuel sfuel, Opt.optimizeF fuel ⟨Opt.aliasM (Ana.pickR M'), Opt.trimTraceHints, Opt.switchChains sfuel⟩ s =
      some (A.optimize s)

/-- **`+optimize` keeps every reference form**, from `OptRef` and `RawOptIn`
(`optimize_keeps_optIn`). -/
theorem keeps_of_optIn {M' : Type → Type → Type} [Treap M'] {A : Arms M Map J H CR} {lib : Lib}
    {ref : Ref M Map J H} (hO : OptRef M' A lib ref) (hI : RawOptIn lib ref)
    {long : LongB M} {jets : J} {hot : H} {b : Bell} {m : Bool} {s : Straight Map}
    (hL : InvB lib long) (hr : ref long jets hot b m = some s) : Opt.Keeps s (A.optimize s) := by
  obtain ⟨fuel, sfuel, h⟩ := hO long jets hot b m s hL hr
  exact Opt.optimize_keeps_optIn M' (hI long jets hot b m s hL hr) h

/-! ## The restated pieces -/

/-- (a) and (b) of `CompRest` on the reference side: the reference compiler
is the model, on nomms of the classes. -/
structure RefSide (S : Type) [Comp.HoonSet S] (lib : Lib) (ref : Ref M Map J H) (D : CompData M Map J H)
    (FM : Nomm → Prop) (FN : Cape → (Comp.Need → Comp.Need × List (Nat × Noun)) → Nomm → Prop) : Prop where
  /-- As `CompRest.refMono`. -/
  refMono : ∀ long jets hot b s, InvB lib long → ref long jets hot b true = some s →
    ∃ nm, realOf long.code b = some nm ∧ Comp.finishLUC (S := S) (D.env long jets hot b true) nm = some s
  /-- As `CompRest.refNary`. -/
  refNary : ∀ long jets hot b s, InvB lib long → ref long jets hot b false = some s →
    ∃ nm nb cape data, realOf long.code b = some nb ∧ D.inl long jets hot b = some nm ∧
      b.less = Sock.mk cape data ∧
      Comp.finishLFC (S := S) (D.env long jets hot b false) nm (D.ord long jets hot b) cape
        (D.bake long jets hot b) = some s
  /-- As `CompRest.inFragM`. -/
  inFragM : ∀ long jets hot b nm, InvB lib long → realOf long.code b = some nm →
    (ref long jets hot b true).isSome → FM nm
  /-- As `CompRest.inFragN`. -/
  inFragN : ∀ long jets hot b nm cape data, InvB lib long → D.inl long jets hot b = some nm →
    b.less = Sock.mk cape data → (ref long jets hot b false).isSome → FN cape (D.bake long jets hot b) nm

/-- **`CompRest` with `OptRef` in place of `rawDInv`, `optEq`, `optAlias`,
`optSSA`** (`RawOptIn` and the raw contract are in `CompPiecesO`).  Every
other field is the field of `CompRest` of the same name, unchanged. -/
structure CompRestO (S : Type) [Comp.HoonSet S] (M' : Type → Type → Type) [Treap M'] (A : Arms M Map J H CR)
    (lib : Lib) (ref : Ref M Map J H) (D : CompData M Map J H) (FM : Nomm → Prop)
    (FN : Cape → (Comp.Need → Comp.Need × List (Nat × Noun)) → Nomm → Prop) : Prop
    extends RefSide S lib ref D FM FN where
  rawEntry : ∀ long jets hot b m s, InvB lib long → ref long jets hot b m = some s →
    ∀ x, SkaModel.Fits b.less x → ∀ args, (if m then some [x] else SkaModel.split s.need x) = some args →
      ∀ (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ) (t : Trace), Opt.EntryOK lib O s gul st args t
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

/-- **The restated pieces**: `CompRestO`, `RawOptIn` and the raw contract. -/
structure CompPiecesO (S : Type) [Comp.HoonSet S] (M' : Type → Type → Type) [Treap M'] (A : Arms M Map J H CR)
    (lib : Lib) (ref : Ref M Map J H) (D : CompData M Map J H) (FM : Nomm → Prop)
    (FN : Cape → (Comp.Need → Comp.Need × List (Nat × Noun)) → Nomm → Prop) : Prop
    extends CompRestO S M' A lib ref D FM FN where
  rawOptIn : RawOptIn lib ref
  rawMono : RawMono S Map lib FM
  rawNary : RawNary S Map lib FN

variable {S : Type} [Comp.HoonSet S] (A : Arms M Map J H CR)

/-- **The contract field of `CompHyp` from the restated pieces** (the proof of
`contract_of_pieces`, with `keeps_of_optIn` for `CompRest.keeps`). -/
theorem contract_of_piecesO {M' : Type → Type → Type} [Treap M'] {lib : Lib} {ref : Ref M Map J H}
    {D : CompData M Map J H} {FM : Nomm → Prop}
    {FN : Cape → (Comp.Need → Comp.Need × List (Nat × Noun)) → Nomm → Prop}
    (P : CompPiecesO S M' A lib ref D FM FN) :
    ∀ long jets hot b m s, InvB lib long → ref long jets hot b m = some s →
      BellContract lib (refN A ref long jets hot) b m (A.optimize s) ∧
        (m = true → (A.optimize s).nargs = 1 ∧ (A.optimize s).need = NeedOrd.this) := by
  intro long jets hot b m s hI hr
  have hk := keeps_of_optIn P.optRef P.rawOptIn hI hr
  have raw : BellContract lib (refN A ref long jets hot) b m s := by
    cases m with
    | true =>
      obtain ⟨nm, hnm, hs⟩ := P.refMono long jets hot b s hI hr
      exact P.rawMono _ b nm _ s _ hI.codeOK (hI.codeOK b nm hnm)
        (P.inFragM long jets hot b nm hI hnm (by rw [hr]; rfl)) (P.callee long jets hot b true hI) hs
    | false =>
      obtain ⟨nm, nb, cape, data, hnb, hinl, hbl, hs⟩ := P.refNary long jets hot b s hI hr
      have hn : NormSock b.less := hI.bellNorm b nb hnb
      rw [hbl] at hn
      exact P.rawNary _ b nm _ _ cape data _ s _ hI.codeOK (P.inlAnnot long jets hot b nm hI hinl) hbl
        (capeNorm_of_normCape hn) (P.inFragN long jets hot b nm cape data hI hinl hbl (by rw [hr]; rfl))
        (P.callee long jets hot b false hI) hs
  refine ⟨bellContract_of_keeps raw hk (P.rawEntry long jets hot b m s hI hr), fun hm => ?_⟩
  subst hm
  obtain ⟨nm, -, hs⟩ := P.refMono long jets hot b s hI hr
  obtain ⟨e1, e2⟩ := finishLUC_this hs
  obtain ⟨k1, k2, -, -⟩ := hk
  exact ⟨by rw [k2, e2], by rw [k1, e1]⟩

/-- **`CompHyp` from the restated pieces**, the hypothesis of `gap_of_comp`. -/
theorem compHyp_of_piecesO {M' : Type → Type → Type} [Treap M'] {lib : Lib} {ref : Ref M Map J H}
    {D : CompData M Map J H} {FM : Nomm → Prop}
    {FN : Cape → (Comp.Need → Comp.Need × List (Nat × Noun)) → Nomm → Prop}
    (P : CompPiecesO S M' A lib ref D FM FN) : CompHyp A lib ref where
  unary := P.unary
  scc := P.scc
  answers := P.answers
  contract := contract_of_piecesO A P
  stable := P.stable
  jetRoot := P.jetRoot
  jets := P.jets
  fast := P.fast

/-! ## On `FragX` -/

/-- The whole-subject class on which everything raw is proved: `FragX` with
at most 255 `%6`. -/
def FragXM (S : Type) [Comp.HoonSet S] (nm : Nomm) : Prop := Comp.FragX (S := S) nm ∧ Comp.sixCount nm ≤ 255

/-- The n-ary class: `FragX`, at most 255 `%6`, nothing baked. -/
def FragXN (S : Type) [Comp.HoonSet S] (_cape : Cape) (bake : Comp.Need → Comp.Need × List (Nat × Noun))
    (nm : Nomm) : Prop :=
  Comp.FragX (S := S) nm ∧ Comp.sixCount nm ≤ 255 ∧ ∀ ned, bake ned = (ned, [])

/-- (b) on `FragXM` (`FragX ⊆ FragU`, `rawMono_fragU`). -/
theorem rawMono_fragX (lib : Lib) : RawMono S Map lib (FragXM S) := by
  intro code bl nm env s N hok hA hf hc h
  exact rawMono_fragU (S := S) (Map := Map) lib code bl nm env s N hok hA ⟨Comp.FragU.x hf.1, hf.2⟩ hc h

/-- (b) on `FragXN` (`rawNary_fragU`). -/
theorem rawNary_fragX (lib : Lib) : RawNary S Map lib (FragXN S) := by
  intro code bl nm env ord cape data bake s N hok hA hbl hn hf hc h
  exact rawNary_fragU (S := S) (Map := Map) lib code bl nm env ord cape data bake s N hok hA hbl hn
    ⟨Comp.FragU.x hf.1, hf.2.1, hf.2.2⟩ hc h

/-- **`rawDInv` restated with `OptIn`, discharged on `FragX`**: from the
reference side alone (track D's `optIn_finishLUX`, `optIn_finishLFX`). -/
theorem rawOptIn_fragX {lib : Lib} {ref : Ref M Map J H} {D : CompData M Map J H}
    (P : RefSide S lib ref D (FragXM S) (FragXN S)) : RawOptIn lib ref := by
  intro long jets hot b m s hI hr
  cases m with
  | true =>
    obtain ⟨nm, hnm, hs⟩ := P.refMono long jets hot b s hI hr
    have hf := P.inFragM long jets hot b nm hI hnm (by rw [hr]; rfl)
    rw [Comp.finishLUC_eq _ (Nomm.noCall_of_pure nm (Comp.fragX_pure hf.1))] at hs
    exact Raw.optIn_finishLUX hf.1 hf.2 hs
  | false =>
    obtain ⟨nm, nb, cape, data, hnb, hinl, hbl, hs⟩ := P.refNary long jets hot b s hI hr
    have hf := P.inFragN long jets hot b nm cape data hI hinl hbl (by rw [hr]; rfl)
    rw [Comp.finishLFC_eq _ (Nomm.noCall_of_pure nm (Comp.fragX_pure hf.1))] at hs
    exact Raw.optIn_finishLFX hf.1 hf.2.1 hf.2.2 hs

/-- **`CompHyp` when every nomm compiled is in `FragX`** (nothing baked in
the n-ary version): from `CompRestO` alone. -/
theorem compHyp_of_fragX {M' : Type → Type → Type} [Treap M'] {lib : Lib} {ref : Ref M Map J H}
    {D : CompData M Map J H} (P : CompRestO S M' A lib ref D (FragXM S) (FragXN S)) : CompHyp A lib ref :=
  compHyp_of_piecesO A
    { toCompRestO := P, rawOptIn := rawOptIn_fragX P.toRefSide, rawMono := rawMono_fragX lib,
      rawNary := rawNary_fragX lib }

/-! ## `OptRef` on `FragX` from the pill's totality -/

section
open Compiler Pill Hoon

/-- **`OptRef` on `FragX`**, from track H's totality (`optimize_total_finishLUX`,
`-LFX`), given that `A.optimize` is what the pill's `+optimize` returns on
every reference form and that `Straight.toNoun` is injective (neither is
proved). -/
theorem optRef_fragX {A : Arms M (TreapMap mugF) J H CR} {lib : Lib} {ref : Ref M (TreapMap mugF) J H}
    {D : CompData M (TreapMap mugF) J H} (P : RefSide S lib ref D (FragXM S) (FragXN S))
    (hpill : ∀ long jets hot b m s, InvB lib long → ref long jets hot b m = some s →
      nock (C optBody (C s.toNoun optC)) optBody = some (A.optimize s).toNoun)
    (hinj : ∀ a b : Straight (TreapMap mugF), a.toNoun = b.toNoun → a = b) :
    OptRef FinMap A lib ref := by
  intro long jets hot b m s hI hr
  have hp := hpill long jets hot b m s hI hr
  have fin : ∀ s' : Straight (TreapMap mugF), nock (C optBody (C s.toNoun optC)) optBody = some s'.toNoun →
      s' = A.optimize s := fun s' h => by
    rw [hp, Option.some.injEq] at h
    exact (hinj _ _ h).symm
  cases m with
  | true =>
    obtain ⟨nm, hnm, hs⟩ := P.refMono long jets hot b s hI hr
    have hf := P.inFragM long jets hot b nm hI hnm (by rw [hr]; rfl)
    rw [Comp.finishLUC_eq _ (Nomm.noCall_of_pure nm (Comp.fragX_pure hf.1))] at hs
    obtain ⟨sfuel, fuel, s', h1, h2⟩ := optimize_total_finishLUX hf.1 hf.2 hs
    exact ⟨fuel, sfuel, by rw [h1, fin s' h2]⟩
  | false =>
    obtain ⟨nm, nb, cape, data, hnb, hinl, hbl, hs⟩ := P.refNary long jets hot b s hI hr
    have hf := P.inFragN long jets hot b nm cape data hI hinl hbl (by rw [hr]; rfl)
    rw [Comp.finishLFC_eq _ (Nomm.noCall_of_pure nm (Comp.fragX_pure hf.1))] at hs
    obtain ⟨sfuel, fuel, s', h1, h2⟩ := optimize_total_finishLFX hf.1 hf.2.1 hf.2.2 hs
    exact ⟨fuel, sfuel, by rw [h1, fin s' h2]⟩

end

/-! ## The halting side -/

/-- **`FullAnswers` of the model of `+poke`** with the analysis fuel
`anaFuel`, from `CgHalts` (no proof), `MemoNoCallees` under `InvB` (not a
field of `InvB`), `BakeEnds` and `RootAnswers` (`fullAnswers_of_loops`,
`anaEnds_of_N`, `anaEndsN_of_halts`, `anaHalts_of_cgHalts`). -/
theorem fullAnswers_of_cg {R : Type} {lib : Lib} {ref : Ref M Map J H} {env : Env R}
    {jet : H → J → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool} {bf : BEnv M → Nat}
    {regOf : J → R} {jetsOf : J → R → J} {newOf : R → Noun}
    (hC : CompHyp A lib ref)
    (hA : A.skaPoke = anaArm env jet fold frozen (anaFuel env regOf) bf regOf jetsOf newOf)
    (hcg : CgHalts (M := M) lib env regOf) (hm : ∀ L : LongB M, InvB lib L → MemoNoCallees L.memo)
    (hb : BakeEnds lib env jet fold frozen (anaFuel env regOf) bf regOf) (hr : RootAnswers lib A ref) :
    FullAnswers (pokeS A) (InvS lib ref) :=
  fullAnswers_of_loops A hC hA (anaEnds_of_N (anaEndsN_of_halts (anaHalts_of_cgHalts hcg)) hm) hb hr

end Glue
end SkaModel
end Formalization
