import lemmas.Glue.PokeOn
import lemmas.Glue.Assemble13

/-!
# Glue: the contract side over reached tables (track G, fourteenth pass)

The contract field of `CompHypOn` from the pieces of `CompRestM`, each asked only at the tables
of a predicate `Tr long jets hot` (the tables of reached states), and the class facts
`ClassLeaves13` (global: facts of the model).

* `refOn Tr ref`: the reference compiler cut down to the `Tr` tables (`none` elsewhere).  Every
  field of `RefSideM` whose premise is an answer of `ref` holds of `refOn Tr ref` when it holds
  of `ref` at the `Tr` tables (`refSideM_on`), so the proofs of `rawEntry_of`,
  `optRef_of_total`, `rawOptIn_of` and `keeps_of_optIn` are used as they are, at `refOn`.
* `contractOn_of`: the proof of `contract_of_piecesM` with every piece at the `Tr` tables.
* `refD S D`: the reference compiler that IS the model (`finishLUCM` of the table's nomm,
  `finishLFC` of `D.inl`): `refMono` and `refNary` hold of it by definition
  (`refMono_refD`, `refNary_refD`), so they are no longer leaves once `ref := refD S D`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Ana Bake PokeM Compiler Pill Hoon

variable {S : Type} [Comp.HoonSet S]

/-- **The reference compiler cut down to the `Tr` tables.** -/
noncomputable def refOn (Tr : LongB FinMap → Noun → Noun → Prop) (ref : Ref FinMap (TreapMap mugF) Noun Noun) :
    Ref FinMap (TreapMap mugF) Noun Noun := fun long jets hot b m =>
  open Classical in if Tr long jets hot then ref long jets hot b m else none

variable {Tr : LongB FinMap → Noun → Noun → Prop} {ref : Ref FinMap (TreapMap mugF) Noun Noun}

theorem refOn_of {long : LongB FinMap} {jets hot : Noun} (hT : Tr long jets hot) :
    refOn Tr ref long jets hot = ref long jets hot := by
  funext b m; simp [refOn, hT]

theorem refOn_some {long : LongB FinMap} {jets hot : Noun} {b : Bell} {m : Bool} {s : Straight (TreapMap mugF)}
    (h : refOn Tr ref long jets hot b m = some s) : Tr long jets hot ∧ ref long jets hot b m = some s := by
  unfold refOn at h
  split at h
  · exact ⟨by assumption, h⟩
  · cases h

theorem refN_on (Ar : ArmsP) {long : LongB FinMap} {jets hot : Noun} (hT : Tr long jets hot) :
    refN Ar (refOn Tr ref) long jets hot = refN Ar ref long jets hot := by
  unfold refN; rw [refOn_of hT]

/-- **`RefSideM` at the `Tr` tables.** -/
structure RefSideMOn (S : Type) [Comp.HoonSet S] (Ar : ArmsP) (lib : Lib) (ref : Ref FinMap (TreapMap mugF) Noun Noun)
    (D : CompData FinMap (TreapMap mugF) Noun Noun) (FM : MonoClass) (FN : NaryClass)
    (Tr : LongB FinMap → Noun → Noun → Prop) : Prop where
  refMono : ∀ long jets hot b s, InvB lib long → Tr long jets hot → ref long jets hot b true = some s →
    ∃ nm, realOf long.code b = some nm ∧ Comp.finishLUCM (S := S) (D.env long jets hot b true) nm = some s
  refNary : ∀ long jets hot b s, InvB lib long → Tr long jets hot → ref long jets hot b false = some s →
    ∃ nm nb cape data, realOf long.code b = some nb ∧ D.inl long jets hot b = some nm ∧
      b.less = Sock.mk cape data ∧
      Comp.finishLFC (S := S) (D.env long jets hot b false) nm (D.ord long jets hot b) cape
        (D.bake long jets hot b) = some s
  inFragM : ∀ long jets hot b nm, InvB lib long → Tr long jets hot → realOf long.code b = some nm →
    (ref long jets hot b true).isSome → FM (D.env long jets hot b true) (refN Ar ref long jets hot) b nm
  inFragN : ∀ long jets hot b nm cape data, InvB lib long → Tr long jets hot → D.inl long jets hot b = some nm →
    b.less = Sock.mk cape data → (ref long jets hot b false).isSome →
    FN (D.env long jets hot b false) (refN Ar ref long jets hot) b cape (D.bake long jets hot b) nm

/-- **`RefSideMOn` gives `RefSideM` of the cut-down reference.** -/
theorem refSideM_on {Ar : ArmsP} {lib : Lib} {D : CompData FinMap (TreapMap mugF) Noun Noun} {FM : MonoClass}
    {FN : NaryClass} (P : RefSideMOn S Ar lib ref D FM FN Tr) : RefSideM S Ar lib (refOn Tr ref) D FM FN where
  refMono := fun long jets hot b s hI hr =>
    let ⟨hT, hr'⟩ := refOn_some hr; P.refMono long jets hot b s hI hT hr'
  refNary := fun long jets hot b s hI hr =>
    let ⟨hT, hr'⟩ := refOn_some hr; P.refNary long jets hot b s hI hT hr'
  inFragM := fun long jets hot b nm hI hnm hs => by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨hT, hr'⟩ := refOn_some hx
    rw [refN_on Ar hT]
    exact P.inFragM long jets hot b nm hI hT hnm (by rw [hr']; rfl)
  inFragN := fun long jets hot b nm cape data hI hinl hbl hs => by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨hT, hr'⟩ := refOn_some hx
    rw [refN_on Ar hT]
    exact P.inFragN long jets hot b nm cape data hI hT hinl hbl (by rw [hr']; rfl)

/-- **The contract-side pieces at the `Tr` tables**: `RefSideMOn`, the pill's `+optimize`
(P), `inlAnnot` (Q), the callees' needs (I, J). -/
structure ContractLeavesOn (S : Type) [Comp.HoonSet S] (Ar : ArmsP) (lib : Lib)
    (ref : Ref FinMap (TreapMap mugF) Noun Noun) (D : CompData FinMap (TreapMap mugF) Noun Noun)
    (FM : MonoClass) (FN : NaryClass) (Tr : LongB FinMap → Noun → Noun → Prop) : Prop
    extends RefSideMOn S Ar lib ref D FM FN Tr where
  optPill : ∀ long jets hot b m s, InvB lib long → Tr long jets hot → ref long jets hot b m = some s →
    nock (C optBody (C s.toNoun optC)) optBody = some (Ar.optimize s).toNoun
  inlAnnot : ∀ long jets hot b nm, InvB lib long → Tr long jets hot → D.inl long jets hot b = some nm →
    Annot lib (realOf long.code) (SkaModel.Fits b.less) b.fol nm
  callee : ∀ long jets hot b m, InvB lib long → Tr long jets hot →
    Comp.CalleeNeeds (D.env long jets hot b m) (refN Ar ref long jets hot)

/-- **The contract at the `Tr` tables** (the proof of `contract_of_piecesM`). -/
theorem contractOn_of {Ar : ArmsP} {lib : Lib} {D : CompData FinMap (TreapMap mugF) Noun Noun} {FM : MonoClass}
    {FN : NaryClass} (P : ContractLeavesOn S Ar lib ref D FM FN Tr) (K : ClassLeaves13 S lib FM FN) :
    ∀ long jets hot b m s, InvB lib long → Tr long jets hot → ref long jets hot b m = some s →
      BellContract lib (refN Ar ref long jets hot) b m (Ar.optimize s) ∧
        (m = true → (Ar.optimize s).nargs = 1 ∧ (Ar.optimize s).need = NeedOrd.this) := by
  have PI : RefSideM S Ar lib (refOn Tr ref) D FM FN := refSideM_on P.toRefSideMOn
  have hOR : OptRef FinMap Ar lib (refOn Tr ref) := optRef_of_total PI K.totalMono K.totalNary
    (fun long jets hot b m s hI hr => let ⟨hT, hr'⟩ := refOn_some hr; P.optPill long jets hot b m s hI hT hr')
  have hRO : RawOptIn lib (refOn Tr ref) := rawOptIn_of Ar PI K.optInMono K.optInNary
  have hRE := rawEntry_of Ar PI K.entryMono K.entryNary
  intro long jets hot b m s hI hT hr
  have hr' : refOn Tr ref long jets hot b m = some s := by rw [refOn_of hT]; exact hr
  have hk := keeps_of_optIn hOR hRO hI hr'
  have raw : BellContract lib (refN Ar ref long jets hot) b m s := by
    cases m with
    | true =>
      obtain ⟨nm, hnm, hs⟩ := P.refMono long jets hot b s hI hT hr
      exact K.rawMono _ b nm _ s _ hI.codeOK (hI.codeOK b nm hnm)
        (P.inFragM long jets hot b nm hI hT hnm (by rw [hr]; rfl)) (P.callee long jets hot b true hI hT) hs
    | false =>
      obtain ⟨nm, nb, cape, data, hnb, hinl, hbl, hs⟩ := P.refNary long jets hot b s hI hT hr
      have hn : NormSock b.less := hI.bellNorm b nb hnb
      rw [hbl] at hn
      exact K.rawNary _ b nm _ _ cape data _ s _ hI.codeOK (P.inlAnnot long jets hot b nm hI hT hinl) hbl
        (capeNorm_of_normCape hn) (P.inFragN long jets hot b nm cape data hI hT hinl hbl (by rw [hr]; rfl))
        (P.callee long jets hot b false hI hT) hs
  refine ⟨bellContract_of_keeps raw hk (hRE long jets hot b m s hI hr'), fun hm => ?_⟩
  subst hm
  obtain ⟨nm, -, hs⟩ := P.refMono long jets hot b s hI hT hr
  obtain ⟨e1, e2⟩ := finishLUCM_this hs
  obtain ⟨k1, k2, -, -⟩ := hk
  exact ⟨by rw [k2, e2], by rw [k1, e1]⟩

/-- **`CompHypOn` from the state leaves, the contract-side leaves at the `Tr` tables and the
class facts**, when every `Rd` state's table is a `Tr` table. -/
theorem compHypOn_of {Ar : ArmsP} {lib : Lib} {D : CompData FinMap (TreapMap mugF) Noun Noun} {FM : MonoClass}
    {FN : NaryClass} {I : PSt → Prop} {Rd : PSt → Bell → Prop}
    (U : CompStateOn Ar lib ref I Rd) (P : ContractLeavesOn S Ar lib ref D FM FN Tr) (K : ClassLeaves13 S lib FM FN)
    (hRT : ∀ st b, Rd st b → Tr st.long st.jets st.hot) : CompHypOn Ar lib ref I Rd :=
  { toCompStateOn := U
    contract := fun st b m s hrd hI hr => contractOn_of P K st.long st.jets st.hot b m s hI (hRT st b hrd) hr }

/-! ## The model as the reference compiler -/

/-- **The reference compiler that is the model**: `finishLUCM` of the table's nomm (the
whole-subject version), `finishLFC` of `D.inl` at the bell's cape (the n-ary version). -/
noncomputable def refD (S : Type) [Comp.HoonSet S] (D : CompData FinMap (TreapMap mugF) Noun Noun) :
    Ref FinMap (TreapMap mugF) Noun Noun := fun long jets hot b m =>
  if m then (realOf long.code b).bind (Comp.finishLUCM (S := S) (D.env long jets hot b true))
  else match b.less with
    | Sock.mk cape _ => (realOf long.code b).bind fun _ => (D.inl long jets hot b).bind fun nm =>
        Comp.finishLFC (S := S) (D.env long jets hot b false) nm (D.ord long jets hot b) cape (D.bake long jets hot b)
    | _ => none

theorem refMono_refD (D : CompData FinMap (TreapMap mugF) Noun Noun) {long : LongB FinMap} {jets hot : Noun}
    {b : Bell} {s : Straight (TreapMap mugF)} (hr : refD S D long jets hot b true = some s) :
    ∃ nm, realOf long.code b = some nm ∧ Comp.finishLUCM (S := S) (D.env long jets hot b true) nm = some s := by
  simp only [refD, if_true, Option.bind_eq_some_iff] at hr
  exact hr

theorem refNary_refD (D : CompData FinMap (TreapMap mugF) Noun Noun) {long : LongB FinMap} {jets hot : Noun}
    {b : Bell} {s : Straight (TreapMap mugF)} (hr : refD S D long jets hot b false = some s) :
    ∃ nm nb cape data, realOf long.code b = some nb ∧ D.inl long jets hot b = some nm ∧
      b.less = Sock.mk cape data ∧
      Comp.finishLFC (S := S) (D.env long jets hot b false) nm (D.ord long jets hot b) cape
        (D.bake long jets hot b) = some s := by
  simp only [refD, Bool.false_eq_true, if_false] at hr
  obtain ⟨less, fol⟩ := b
  cases less with
  | mk cape data =>
    simp only [Option.bind_eq_some_iff] at hr
    obtain ⟨nb, hnb, nm, hnm, hs⟩ := hr
    exact ⟨nm, nb, cape, data, hnb, hnm, rfl, hs⟩
  | _ => simp at hr

/-- **The class leaves of `RefSideMOn` at `refD`**: `refMono`, `refNary` are theorems. -/
structure InFragOn (S : Type) [Comp.HoonSet S] (Ar : ArmsP) (lib : Lib) (D : CompData FinMap (TreapMap mugF) Noun Noun)
    (FM : MonoClass) (FN : NaryClass) (Tr : LongB FinMap → Noun → Noun → Prop) : Prop where
  inFragM : ∀ long jets hot b nm, InvB lib long → Tr long jets hot → realOf long.code b = some nm →
    (refD S D long jets hot b true).isSome → FM (D.env long jets hot b true) (refN Ar (refD S D) long jets hot) b nm
  inFragN : ∀ long jets hot b nm cape data, InvB lib long → Tr long jets hot → D.inl long jets hot b = some nm →
    b.less = Sock.mk cape data → (refD S D long jets hot b false).isSome →
    FN (D.env long jets hot b false) (refN Ar (refD S D) long jets hot) b cape (D.bake long jets hot b) nm

theorem refSideMOn_refD {Ar : ArmsP} {lib : Lib} {D : CompData FinMap (TreapMap mugF) Noun Noun} {FM : MonoClass}
    {FN : NaryClass} (P : InFragOn S Ar lib D FM FN Tr) : RefSideMOn S Ar lib (refD S D) D FM FN Tr where
  refMono := fun _ _ _ _ _ _ _ hr => refMono_refD D hr
  refNary := fun _ _ _ _ _ _ _ hr => refNary_refD D hr
  inFragM := P.inFragM
  inFragN := P.inFragN

end Glue
end SkaModel
end Formalization
