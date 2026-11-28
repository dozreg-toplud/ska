import lemmas.Glue.PiecesOn
import lemmas.Ska.CompHintClsGlue

/-!
# Glue: the contract side with hints, at `finishLUCH` (track G, fifteenth pass; M16)

Mismatch M16 of `LEDGER.md`: the Hoon at `mono &` compiles a hinted nomm by
`finishLUCH env snd` (`runLCH`, the hint cases; `snd` is the table's
`+sound`), while `RefSideM` / `RefSideMOn` ask for `finishLUCM` (which fails on
every hint).  Track J's class of hinted nomms (`HintClsB snd lib`, the check
`hcV`) has its raw contract at `finishLUCH` (`rawMonoH_hintCls`,
`hintContract_holds`: no hypothesis).  Here the contract side is restated at
`finishLUCH` by the `refD` pattern: the model WITH hints is the reference.

* `SndT`, `MonoClassH` (a class family indexed by `+sound`); the three
  mono model facts at `finishLUCH`: `OptInMonoH`, `EntryMonoH`,
  `OptTotalMonoH`; `ClassLeavesH` (`ClassLeaves13` with the mono fields at
  `finishLUCH`, for every `snd`);
* `classLeavesH_of13`: every `ClassLeaves13` class, on hint-free nomms
  (`noHintM`), is a `ClassLeavesH` class (`finishLUCH_eq`); `classLeavesH_or`;
* `HintLeaves`: the three model facts of J's class (named leaves);
  **`classLeavesH_hint`**: `ClassLeavesH` of `HintClsB` with J's raw contract
  (no hypothesis) and the n-ary class `NoNary` (empty);
* `RefSideMOnH`, `ContractLeavesOnH`, **`contractOnH_of`** (the proof of
  `contractOn_of` at `finishLUCH`), `compHypOnH_of`;
* **`refDH S D sn`**: `finishLUCH (D.env ..) (sn long)` of the table's nomm,
  `refD`'s n-ary half; `refMonoH_refDH`, `refNaryH_refDH`, `InFragOnH`,
  `refSideMOnH_refDH`; `finishLUCH_this`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Ana Bake PokeM Compiler Pill Hoon

/-- `+sound`'s model: a nomm and a need to a flag. -/
abbrev SndT : Type := Nomm → NeedOrd → Bool

/-- **A whole-subject class family indexed by `+sound`.** -/
abbrev MonoClassH : Type := SndT → MonoClass

variable {S : Type} [Comp.HoonSet S]

/-! ## The mono model facts at `finishLUCH` -/

/-- `OptInMono` at `finishLUCH env snd`. -/
def OptInMonoH (S : Type) [Comp.HoonSet S] (Map : Type → Type) [HoonMap Map] [Comp.HoonMapKeys Map]
    [Opt.MapKeys Map] (snd : SndT) (FM : MonoClass) : Prop :=
  ∀ env N bl nm (s : Straight Map), FM env N bl nm → Comp.finishLUCH (S := S) env snd nm = some s →
    Opt.OptIn s.blocks

/-- `EntryMono` at `finishLUCH env snd`. -/
def EntryMonoH (S : Type) [Comp.HoonSet S] (Map : Type → Type) [HoonMap Map] [Comp.HoonMapKeys Map]
    (lib : Lib) (snd : SndT) (FM : MonoClass) : Prop :=
  ∀ env N bl nm (s : Straight Map), FM env N bl nm → Comp.finishLUCH (S := S) env snd nm = some s →
    ∀ x, SkaModel.Fits bl.less x →
      ∀ (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ) (t : Trace), Opt.EntryOK lib O s gul st [x] t

/-- `OptTotalMono` at `finishLUCH env snd`. -/
def OptTotalMonoH (S : Type) [Comp.HoonSet S] (snd : SndT) (FM : MonoClass) : Prop :=
  ∀ env N bl nm (c : Straight (TreapMap mugF)), FM env N bl nm → Comp.finishLUCH (S := S) env snd nm = some c →
    ∃ sfuel fuel s', Opt.optimizeF fuel ⟨Opt.aliasM (Ana.pickR FinMap), Opt.trimTraceHints,
      Opt.switchChains sfuel⟩ c = some s' ∧ nock (C optBody (C c.toNoun optC)) optBody = some s'.toNoun

/-- **The model facts of a class pair with hints**: the mono fields at
`finishLUCH env snd`, for every `snd`; the n-ary fields as in
`ClassLeaves13`. -/
structure ClassLeavesH (S : Type) [Comp.HoonSet S] (lib : Lib) (FM : MonoClassH) (FN : NaryClass) : Prop where
  rawMono : ∀ snd, RawMonoH S (TreapMap mugF) lib snd (FM snd)
  rawNary : RawNaryD S (TreapMap mugF) lib FN
  optInMono : ∀ snd, OptInMonoH S (TreapMap mugF) snd (FM snd)
  optInNary : OptInNary S (TreapMap mugF) FN
  entryMono : ∀ snd, EntryMonoH S (TreapMap mugF) lib snd (FM snd)
  entryNary : EntryNary S (TreapMap mugF) lib FN
  totalMono : ∀ snd, OptTotalMonoH S snd (FM snd)
  totalNary : OptTotalNary S FN

/-- **Every `ClassLeaves13` class, on hint-free nomms, is a `ClassLeavesH`
class** (`finishLUCH_eq`). -/
theorem classLeavesH_of13 {lib : Lib} {FM : MonoClass} {FN : NaryClass} (h : ClassLeaves13 S lib FM FN) :
    ClassLeavesH S lib (fun _ => noHintM FM) FN where
  rawMono := fun snd => rawMonoH_of_D snd h.rawMono
  rawNary := h.rawNary
  optInMono := fun snd env N bl nm s hf hs => by
    rw [Comp.finishLUCH_eq env snd hf.2] at hs; exact h.optInMono env N bl nm s hf.1 hs
  optInNary := h.optInNary
  entryMono := fun snd env N bl nm s hf hs => by
    rw [Comp.finishLUCH_eq env snd hf.2] at hs; exact h.entryMono env N bl nm s hf.1 hs
  entryNary := h.entryNary
  totalMono := fun snd env N bl nm c hf hs => by
    rw [Comp.finishLUCH_eq env snd hf.2] at hs; exact h.totalMono env N bl nm c hf.1 hs
  totalNary := h.totalNary

/-- **The model facts with hints are closed under union.** -/
theorem classLeavesH_or {lib : Lib} {FM GM : MonoClassH} {FN GN : NaryClass} (h : ClassLeavesH S lib FM FN)
    (g : ClassLeavesH S lib GM GN) : ClassLeavesH S lib (fun snd => orM (FM snd) (GM snd)) (orN FN GN) where
  rawMono := fun snd => rawMonoH_or (h.rawMono snd) (g.rawMono snd)
  rawNary := (classLeaves_or (S := S) (lib := lib) (FM := fun _ _ _ _ => False) (GM := fun _ _ _ _ => False)
      ⟨fun _ _ _ _ _ _ _ _ hf => hf.elim, h.rawNary, fun _ _ _ _ _ hf => hf.elim, h.optInNary,
        fun _ _ _ _ _ hf => hf.elim, h.entryNary, fun _ _ _ _ _ hf => hf.elim, h.totalNary⟩
      ⟨fun _ _ _ _ _ _ _ _ hf => hf.elim, g.rawNary, fun _ _ _ _ _ hf => hf.elim, g.optInNary,
        fun _ _ _ _ _ hf => hf.elim, g.entryNary, fun _ _ _ _ _ hf => hf.elim, g.totalNary⟩).rawNary
  optInMono := fun snd env N bl nm s hf hs => hf.elim (fun hf => h.optInMono snd env N bl nm s hf hs)
    (fun hf => g.optInMono snd env N bl nm s hf hs)
  optInNary := fun env N bl cape bake nm ord s hf hs => hf.elim
    (fun hf => h.optInNary env N bl cape bake nm ord s hf hs) (fun hf => g.optInNary env N bl cape bake nm ord s hf hs)
  entryMono := fun snd env N bl nm s hf hs => hf.elim (fun hf => h.entryMono snd env N bl nm s hf hs)
    (fun hf => g.entryMono snd env N bl nm s hf hs)
  entryNary := fun env N bl cape bake nm ord s hf hs => hf.elim
    (fun hf => h.entryNary env N bl cape bake nm ord s hf hs) (fun hf => g.entryNary env N bl cape bake nm ord s hf hs)
  totalMono := fun snd env N bl nm c hf hs => hf.elim (fun hf => h.totalMono snd env N bl nm c hf hs)
    (fun hf => g.totalMono snd env N bl nm c hf hs)
  totalNary := fun env N bl cape bake nm ord c hf hs => hf.elim
    (fun hf => h.totalNary env N bl cape bake nm ord c hf hs) (fun hf => g.totalNary env N bl cape bake nm ord c hf hs)

/-! ## Track J's class of hinted nomms -/

/-- The empty n-ary class. -/
def NoNary : NaryClass := fun _ _ _ _ _ _ => False

/-- **The three model facts of J's hinted class** (named leaves: `OptIn`
(D), the entry (G, D), the totality of the pill's `+optimize` (H), each at
`finishLUCH`). -/
structure HintLeaves (S : Type) [Comp.HoonSet S] (lib : Lib) : Prop where
  optIn : ∀ snd, OptInMonoH S (TreapMap mugF) snd (HintClsB snd lib)
  entry : ∀ snd, EntryMonoH S (TreapMap mugF) lib snd (HintClsB snd lib)
  total : ∀ snd, OptTotalMonoH S snd (HintClsB snd lib)

/-- **J's hinted class as a `ClassLeavesH` class**: the raw contract is J's
theorem (`rawMonoH_hintCls`, `hintContract_holds`), the n-ary side empty. -/
theorem classLeavesH_hint {lib : Lib} (h : HintLeaves S lib) :
    ClassLeavesH S lib (fun snd => HintClsB snd lib) NoNary where
  rawMono := fun snd => rawMonoH_hintCls (hintContract_holds lib snd)
  rawNary := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hf => hf.elim
  optInMono := h.optIn
  optInNary := fun _ _ _ _ _ _ _ _ hf => hf.elim
  entryMono := h.entry
  entryNary := fun _ _ _ _ _ _ _ _ hf => hf.elim
  totalMono := h.total
  totalNary := fun _ _ _ _ _ _ _ _ hf => hf.elim

/-! ## The reference side at `finishLUCH`, on the `Tr` tables -/

variable {Tr : LongB FinMap → Noun → Noun → Prop} {ref : Ref FinMap (TreapMap mugF) Noun Noun}

/-- **`RefSideMOn` at `finishLUCH env (sn long)`.** -/
structure RefSideMOnH (S : Type) [Comp.HoonSet S] (Ar : ArmsP) (lib : Lib) (ref : Ref FinMap (TreapMap mugF) Noun Noun)
    (D : CompData FinMap (TreapMap mugF) Noun Noun) (sn : LongB FinMap → SndT) (FM : MonoClassH) (FN : NaryClass)
    (Tr : LongB FinMap → Noun → Noun → Prop) : Prop where
  refMono : ∀ long jets hot b s, InvB lib long → Tr long jets hot → ref long jets hot b true = some s →
    ∃ nm, realOf long.code b = some nm ∧ Comp.finishLUCH (S := S) (D.env long jets hot b true) (sn long) nm = some s
  refNary : ∀ long jets hot b s, InvB lib long → Tr long jets hot → ref long jets hot b false = some s →
    ∃ nm nb cape data, realOf long.code b = some nb ∧ D.inl long jets hot b = some nm ∧
      b.less = Sock.mk cape data ∧
      Comp.finishLFC (S := S) (D.env long jets hot b false) nm (D.ord long jets hot b) cape
        (D.bake long jets hot b) = some s
  inFragM : ∀ long jets hot b nm, InvB lib long → Tr long jets hot → realOf long.code b = some nm →
    (ref long jets hot b true).isSome → FM (sn long) (D.env long jets hot b true) (refN Ar ref long jets hot) b nm
  inFragN : ∀ long jets hot b nm cape data, InvB lib long → Tr long jets hot → D.inl long jets hot b = some nm →
    b.less = Sock.mk cape data → (ref long jets hot b false).isSome →
    FN (D.env long jets hot b false) (refN Ar ref long jets hot) b cape (D.bake long jets hot b) nm

/-- **The contract-side pieces at the `Tr` tables, with hints.** -/
structure ContractLeavesOnH (S : Type) [Comp.HoonSet S] (Ar : ArmsP) (lib : Lib)
    (ref : Ref FinMap (TreapMap mugF) Noun Noun) (D : CompData FinMap (TreapMap mugF) Noun Noun)
    (sn : LongB FinMap → SndT) (FM : MonoClassH) (FN : NaryClass) (Tr : LongB FinMap → Noun → Noun → Prop) : Prop
    extends RefSideMOnH S Ar lib ref D sn FM FN Tr where
  optPill : ∀ long jets hot b m s, InvB lib long → Tr long jets hot → ref long jets hot b m = some s →
    nock (C optBody (C s.toNoun optC)) optBody = some (Ar.optimize s).toNoun
  inlAnnot : ∀ long jets hot b nm, InvB lib long → Tr long jets hot → D.inl long jets hot b = some nm →
    Annot lib (realOf long.code) (SkaModel.Fits b.less) b.fol nm
  callee : ∀ long jets hot b m, InvB lib long → Tr long jets hot →
    Comp.CalleeNeeds (D.env long jets hot b m) (refN Ar ref long jets hot)

/-- **The code of `finishLUCH` has one argument and the need `this`.** -/
theorem finishLUCH_this {Map : Type → Type} [HoonMap Map] [Comp.HoonMapKeys Map] [Opt.MapKeys Map] {env : Comp.CallEnv} {snd : SndT}
    {nm : Nomm} {c : Straight Map} (h : Comp.finishLUCH (S := S) env snd nm = some c) :
    c.need = NeedOrd.this ∧ c.nargs = 1 := by
  unfold Comp.finishLUCH at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  exact toStraightF_this h

section
variable {Ar : ArmsP} {lib : Lib} {D : CompData FinMap (TreapMap mugF) Noun Noun} {sn : LongB FinMap → SndT}
  {FM : MonoClassH} {FN : NaryClass}

/-- `OptRef` of the cut-down reference from the totality leaves. -/
theorem optRefH_on (P : RefSideMOnH S Ar lib ref D sn FM FN Tr) (hm : ∀ snd, OptTotalMonoH S snd (FM snd))
    (hn : OptTotalNary S FN)
    (hpill : ∀ long jets hot b m s, InvB lib long → Tr long jets hot → ref long jets hot b m = some s →
      nock (C optBody (C s.toNoun optC)) optBody = some (Ar.optimize s).toNoun) :
    OptRef FinMap Ar lib (refOn Tr ref) := by
  intro long jets hot b m s hI hr0
  obtain ⟨hT, hr⟩ := refOn_some hr0
  have hp := hpill long jets hot b m s hI hT hr
  have fin : ∀ s' : Straight (TreapMap mugF), nock (C optBody (C s.toNoun optC)) optBody = some s'.toNoun →
      s' = Ar.optimize s := fun s' h => by
    rw [hp, Option.some.injEq] at h
    exact (straight_toNoun_inj h).symm
  cases m with
  | true =>
    obtain ⟨nm, hnm, hs⟩ := P.refMono long jets hot b s hI hT hr
    obtain ⟨sfuel, fuel, s', h1, h2⟩ :=
      hm (sn long) _ _ _ nm s (P.inFragM long jets hot b nm hI hT hnm (by rw [hr]; rfl)) hs
    exact ⟨fuel, sfuel, by rw [h1, fin s' h2]⟩
  | false =>
    obtain ⟨nm, nb, cape, data, hnb, hinl, hbl, hs⟩ := P.refNary long jets hot b s hI hT hr
    obtain ⟨sfuel, fuel, s', h1, h2⟩ :=
      hn _ _ _ _ _ nm _ s (P.inFragN long jets hot b nm cape data hI hT hinl hbl (by rw [hr]; rfl)) hs
    exact ⟨fuel, sfuel, by rw [h1, fin s' h2]⟩

/-- `RawOptIn` of the cut-down reference from the two `OptIn` leaves. -/
theorem rawOptInH_on (P : RefSideMOnH S Ar lib ref D sn FM FN Tr) (hm : ∀ snd, OptInMonoH S (TreapMap mugF) snd (FM snd))
    (hn : OptInNary S (TreapMap mugF) FN) : RawOptIn lib (refOn Tr ref) := by
  intro long jets hot b m s hI hr0
  obtain ⟨hT, hr⟩ := refOn_some hr0
  cases m with
  | true =>
    obtain ⟨nm, hnm, hs⟩ := P.refMono long jets hot b s hI hT hr
    exact hm (sn long) _ _ _ nm s (P.inFragM long jets hot b nm hI hT hnm (by rw [hr]; rfl)) hs
  | false =>
    obtain ⟨nm, nb, cape, data, hnb, hinl, hbl, hs⟩ := P.refNary long jets hot b s hI hT hr
    exact hn _ _ _ _ _ nm _ s (P.inFragN long jets hot b nm cape data hI hT hinl hbl (by rw [hr]; rfl)) hs

/-- `rawEntry` of the cut-down reference from the two entry leaves. -/
theorem rawEntryH_on (P : RefSideMOnH S Ar lib ref D sn FM FN Tr)
    (hm : ∀ snd, EntryMonoH S (TreapMap mugF) lib snd (FM snd)) (hn : EntryNary S (TreapMap mugF) lib FN) :
    ∀ long jets hot b m s, InvB lib long → refOn Tr ref long jets hot b m = some s →
      ∀ x, SkaModel.Fits b.less x → ∀ args, (if m then some [x] else SkaModel.split s.need x) = some args →
        ∀ (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ) (t : Trace), Opt.EntryOK lib O s gul st args t := by
  intro long jets hot b m s hI hr0 x hx args hargs
  obtain ⟨hT, hr⟩ := refOn_some hr0
  cases m with
  | true =>
    simp only [if_true, Option.some.injEq] at hargs
    subst hargs
    obtain ⟨nm, hnm, hs⟩ := P.refMono long jets hot b s hI hT hr
    exact hm (sn long) _ _ _ nm s (P.inFragM long jets hot b nm hI hT hnm (by rw [hr]; rfl)) hs x hx
  | false =>
    simp only [Bool.false_eq_true, if_false] at hargs
    obtain ⟨nm, nb, cape, data, hnb, hinl, hbl, hs⟩ := P.refNary long jets hot b s hI hT hr
    exact hn _ _ _ _ _ nm _ s (P.inFragN long jets hot b nm cape data hI hT hinl hbl (by rw [hr]; rfl)) hs x hx
      args hargs

/-- **The contract at the `Tr` tables, with hints** (the proof of
`contractOn_of` at `finishLUCH`). -/
theorem contractOnH_of (P : ContractLeavesOnH S Ar lib ref D sn FM FN Tr) (K : ClassLeavesH S lib FM FN) :
    ∀ long jets hot b m s, InvB lib long → Tr long jets hot → ref long jets hot b m = some s →
      BellContract lib (refN Ar ref long jets hot) b m (Ar.optimize s) ∧
        (m = true → (Ar.optimize s).nargs = 1 ∧ (Ar.optimize s).need = NeedOrd.this) := by
  have hOR := optRefH_on P.toRefSideMOnH K.totalMono K.totalNary P.optPill
  have hRO := rawOptInH_on P.toRefSideMOnH K.optInMono K.optInNary
  have hRE := rawEntryH_on P.toRefSideMOnH K.entryMono K.entryNary
  intro long jets hot b m s hI hT hr
  have hr' : refOn Tr ref long jets hot b m = some s := by rw [refOn_of hT]; exact hr
  have hk := keeps_of_optIn hOR hRO hI hr'
  have raw : BellContract lib (refN Ar ref long jets hot) b m s := by
    cases m with
    | true =>
      obtain ⟨nm, hnm, hs⟩ := P.refMono long jets hot b s hI hT hr
      exact K.rawMono (sn long) _ b nm _ s _ hI.codeOK (hI.codeOK b nm hnm)
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
  obtain ⟨e1, e2⟩ := finishLUCH_this hs
  obtain ⟨k1, k2, -, -⟩ := hk
  exact ⟨by rw [k2, e2], by rw [k1, e1]⟩

/-- **`CompHypOn` from the state leaves, the contract-side leaves with hints
and the class facts with hints.** -/
theorem compHypOnH_of {I : PSt → Prop} {Rd : PSt → Bell → Prop}
    (U : CompStateOn Ar lib ref I Rd) (P : ContractLeavesOnH S Ar lib ref D sn FM FN Tr) (K : ClassLeavesH S lib FM FN)
    (hRT : ∀ st b, Rd st b → Tr st.long st.jets st.hot) : CompHypOn Ar lib ref I Rd :=
  { toCompStateOn := U
    contract := fun st b m s hrd hI hr => contractOnH_of P K st.long st.jets st.hot b m s hI (hRT st b hrd) hr }

end

/-! ## The model with hints as the reference compiler -/

/-- **The reference compiler that is the model with hints**: `finishLUCH`
of the table's nomm under the table's `+sound` (`sn long`), `refD`'s n-ary
half. -/
noncomputable def refDH (S : Type) [Comp.HoonSet S] (D : CompData FinMap (TreapMap mugF) Noun Noun)
    (sn : LongB FinMap → SndT) : Ref FinMap (TreapMap mugF) Noun Noun := fun long jets hot b m =>
  if m then (realOf long.code b).bind (Comp.finishLUCH (S := S) (D.env long jets hot b true) (sn long))
  else refD S D long jets hot b false

theorem refMonoH_refDH (D : CompData FinMap (TreapMap mugF) Noun Noun) (sn : LongB FinMap → SndT)
    {long : LongB FinMap} {jets hot : Noun} {b : Bell} {s : Straight (TreapMap mugF)}
    (hr : refDH S D sn long jets hot b true = some s) :
    ∃ nm, realOf long.code b = some nm ∧ Comp.finishLUCH (S := S) (D.env long jets hot b true) (sn long) nm = some s := by
  simp only [refDH, if_true, Option.bind_eq_some_iff] at hr
  exact hr

theorem refDH_false (D : CompData FinMap (TreapMap mugF) Noun Noun) (sn : LongB FinMap → SndT)
    (long : LongB FinMap) (jets hot : Noun) (b : Bell) : refDH S D sn long jets hot b false = refD S D long jets hot b false := by
  simp [refDH]

/-- **The class leaves of `RefSideMOnH` at `refDH`.** -/
structure InFragOnH (S : Type) [Comp.HoonSet S] (Ar : ArmsP) (lib : Lib) (D : CompData FinMap (TreapMap mugF) Noun Noun)
    (sn : LongB FinMap → SndT) (FM : MonoClassH) (FN : NaryClass) (Tr : LongB FinMap → Noun → Noun → Prop) : Prop where
  inFragM : ∀ long jets hot b nm, InvB lib long → Tr long jets hot → realOf long.code b = some nm →
    (refDH S D sn long jets hot b true).isSome →
      FM (sn long) (D.env long jets hot b true) (refN Ar (refDH S D sn) long jets hot) b nm
  inFragN : ∀ long jets hot b nm cape data, InvB lib long → Tr long jets hot → D.inl long jets hot b = some nm →
    b.less = Sock.mk cape data → (refDH S D sn long jets hot b false).isSome →
    FN (D.env long jets hot b false) (refN Ar (refDH S D sn) long jets hot) b cape (D.bake long jets hot b) nm

theorem refSideMOnH_refDH {Ar : ArmsP} {lib : Lib} {D : CompData FinMap (TreapMap mugF) Noun Noun}
    {sn : LongB FinMap → SndT} {FM : MonoClassH} {FN : NaryClass} (P : InFragOnH S Ar lib D sn FM FN Tr) :
    RefSideMOnH S Ar lib (refDH S D sn) D sn FM FN Tr where
  refMono := fun _ _ _ _ _ _ _ hr => refMonoH_refDH D sn hr
  refNary := fun long jets hot b s _ _ hr => refNary_refD D (by rw [← refDH_false D sn]; exact hr)
  inFragM := P.inFragM
  inFragN := P.inFragN

end Glue
end SkaModel
end Formalization
