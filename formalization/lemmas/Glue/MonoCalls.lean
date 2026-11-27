import lemmas.Glue.RawOptIn
import lemmas.Ska.CompDirectMTree
import lemmas.Ska.CompNaryTop
import lemmas.Ska.CompNaryTopRec
import lemmas.Ska.CompSixLSClass
import lemmas.Ska.PokeEnc

/-!
# Glue: the contract side with calls (mismatch M3 of `LEDGER.md`, finished)

`RefSide.refMono` of `RawOptIn.lean` says that the reference whole-subject
code is `finishLUC` (`runLC`); the Hoon at `mono &` compiles a direct call by
`runLCM env true` (`finishLUCM`), and the contract theorems with direct calls
(track J's `finishLUCM_bellContractCallTreeD`) are about `finishLUCM` and
about a class `CallTreeD lib env N (Fits bl.less) x bl.fol nm` that sees the
call environment, the callees' needs and the bell.  Here:

* `MonoClass`, `NaryClass`: classes of nomms that see `env`, `N`, the bell
  (and, n-ary, the cape and the bake);
* `RawMonoD`, `RawNaryD`: the raw contracts on such classes, the first
  against `finishLUCM`;
* `RefSideM`, `CompRestM`, `CompPiecesM`: `RefSide`, `CompRestO`,
  `CompPiecesO` with `refMono` at `finishLUCM` and the classes taken at
  `D.env … b m` and `refN A ref …`; `compHyp_of_piecesM` ends in `CompHyp`;
* the bridges: `rawMonoD_of` (a `RawMono` class of `noDirect` nomms),
  `noDirect_NCG`, `noDirect_fragUFG`, `compRestM_of_O`;
* the classes with calls that the tracks reached: `MonoCalls` (`NCG`,
  `CallTreeD`, `TopTree`, `CallTreeA`, `Six0`) and `NaryCalls` (`FragUN`, `CallTreeA`,
  `CallTreeDN`, nothing baked), with their raw contracts `rawMonoD_calls`,
  `rawNaryD_calls`;
* the two optimizer leaves as statements about the MODEL, per class:
  `OptInMono`, `OptInNary` (track D's `OptIn` of the raw blocks) and
  `OptTotalMono`, `OptTotalNary` (track H's totality of the pill's
  `+optimize`); `rawOptIn_of`, `optRef_of_total` compose them; on `FragX`
  they are proved (`optInMono_fragX`, …, `optTotalNary_fragX`);
* `Compiler.straight_toNoun_inj` (track P's, `Ska/PokeEnc.lean`):
  `Straight.toNoun` is injective on `TreapMap mugF` (the `hinj` of
  `optRef_fragX`), so `optRef_fragX'` has no `hinj`;
* `compHyp_of_calls`: `CompHyp` on the classes with calls from `CompRestM`
  and the two leaves `OptInMono`, `OptInNary` (owner: track D).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Ana Bake PokeM

variable {M : Type → Type → Type} [Treap M] {Map : Type → Type} [HoonMap Map] [Comp.HoonMapKeys Map]
  [Opt.MapKeys Map] {J H CR : Type}

/-! ## Classes that see the call environment, the needs and the bell -/

/-- A class of whole-subject nomms that sees the call environment, the
callees' needs and the bell. -/
abbrev MonoClass : Type := Comp.CallEnv → Needs → Bell → Nomm → Prop

/-- A class of n-ary nomms that sees the call environment, the needs, the
bell, the cape and the bake. -/
abbrev NaryClass : Type :=
  Comp.CallEnv → Needs → Bell → Cape → (Comp.Need → Comp.Need × List (Nat × Noun)) → Nomm → Prop

/-- **(b) against `finishLUCM` on a class that sees `env`, `N`, the bell.** -/
def RawMonoD (S : Type) [Comp.HoonSet S] (Map : Type → Type) [HoonMap Map] [Comp.HoonMapKeys Map] (lib : Lib)
    (FM : MonoClass) : Prop :=
  ∀ (code : Bell → Option Nomm) (bl : Bell) (nm : Nomm) (env : Comp.CallEnv) (s : Straight Map) (N : Needs),
    CodeOK lib code → Annot lib code (SkaModel.Fits bl.less) bl.fol nm → FM env N bl nm → Comp.CalleeNeeds env N →
    Comp.finishLUCM (S := S) env nm = some s → BellContract lib N bl true s

/-- **(b) n-ary on a class that sees `env`, `N`, the bell** (`finishLFC`
runs `runLCM env false`, `finishLFC_eq_M`, so it is the real n-ary code). -/
def RawNaryD (S : Type) [Comp.HoonSet S] (Map : Type → Type) [HoonMap Map] [Comp.HoonMapKeys Map] (lib : Lib)
    (FN : NaryClass) : Prop :=
  ∀ (code : Bell → Option Nomm) (bl : Bell) (nm : Nomm) (env : Comp.CallEnv) (ord : NeedOrd) (cape : Cape)
    (data : Noun) (bake : Comp.Need → Comp.Need × List (Nat × Noun)) (s : Straight Map) (N : Needs),
    CodeOK lib code → Annot lib code (SkaModel.Fits bl.less) bl.fol nm → bl.less = Sock.mk cape data →
    Comp.CapeNorm cape → FN env N bl cape bake nm → Comp.CalleeNeeds env N →
    Comp.finishLFC (S := S) env nm ord cape bake = some s → BellContract lib N bl false s

variable {S : Type} [Comp.HoonSet S]

/-- A `Nomm → Prop` class read as a `MonoClass`. -/
def liftMC (F : Nomm → Prop) : MonoClass := fun _ _ _ nm => F nm

/-- A `RawNary` class read as a `NaryClass`. -/
def liftNC (F : Cape → (Comp.Need → Comp.Need × List (Nat × Noun)) → Nomm → Prop) : NaryClass :=
  fun _ _ _ cape bake nm => F cape bake nm

/-- The union of two classes. -/
def orM (F G : MonoClass) : MonoClass := fun env N bl nm => F env N bl nm ∨ G env N bl nm

/-- The union of two n-ary classes. -/
def orN (F G : NaryClass) : NaryClass := fun env N bl cape bake nm => F env N bl cape bake nm ∨ G env N bl cape bake nm

theorem rawMonoD_or {lib : Lib} {F G : MonoClass} (hF : RawMonoD S Map lib F) (hG : RawMonoD S Map lib G) :
    RawMonoD S Map lib (orM F G) := by
  intro code bl nm env s N hok hA hf hc h
  rcases hf with hf | hf
  · exact hF code bl nm env s N hok hA hf hc h
  · exact hG code bl nm env s N hok hA hf hc h

theorem rawNaryD_or {lib : Lib} {F G : NaryClass} (hF : RawNaryD S Map lib F) (hG : RawNaryD S Map lib G) :
    RawNaryD S Map lib (orN F G) := by
  intro code bl nm env ord cape data bake s N hok hA hbl hn hf hc h
  rcases hf with hf | hf
  · exact hF code bl nm env ord cape data bake s N hok hA hbl hn hf hc h
  · exact hG code bl nm env ord cape data bake s N hok hA hbl hn hf hc h

/-! ## The bridges from the classes without direct calls -/

/-- **`RawMonoD` from `RawMonoM`.** -/
theorem rawMonoD_of_M {lib : Lib} {F : Nomm → Prop} (h : RawMonoM S Map lib F) : RawMonoD S Map lib (liftMC F) :=
  fun code bl nm env s N hok hA hf hc hs => h code bl nm env s N hok hA hf hc hs

/-- **`RawMonoD` from `RawMono` on a class of `noDirect` nomms.** -/
theorem rawMonoD_of {lib : Lib} {F : Nomm → Prop} (h : RawMono S Map lib F)
    (hd : ∀ nm, F nm → nm.noDirect = true) : RawMonoD S Map lib (liftMC F) :=
  rawMonoD_of_M (rawMonoM_of h hd)

/-- **`RawNaryD` from `RawNary`.** -/
theorem rawNaryD_of {lib : Lib} {F : Cape → (Comp.Need → Comp.Need × List (Nat × Noun)) → Nomm → Prop}
    (h : RawNary S Map lib F) : RawNaryD S Map lib (liftNC F) :=
  fun code bl nm env ord cape data bake s N hok hA hbl hn hf hc hs =>
    h code bl nm env ord cape data bake s N hok hA hbl hn hf hc hs

/-- **`NCG` has no direct call** (`NC.noDirect`). -/
theorem noDirect_NCG {nm : Nomm} (h : NCG S nm) : nm.noDirect = true := by
  obtain ⟨⟨_, hn⟩, _⟩ := h
  exact hn.noDirect

/-- **`FragUFG` has no direct call** (`fragUFG_subNC`). -/
theorem noDirect_fragUFG {nm : Nomm} (h : FragUFG S nm) : nm.noDirect = true :=
  noDirect_NCG (fragUFG_subNC h)

/-- `RawMonoD` on `NCG` (so on `FragUFG` and the classes inside it). -/
theorem rawMonoD_NCG (lib : Lib) : RawMonoD S Map lib (liftMC (NCG S)) :=
  rawMonoD_of (rawMono_NCG lib) fun _ h => noDirect_NCG h

/-! ## The classes with calls -/

/-- **Track J's class with direct calls**, at the subjects of the bell. -/
def CallTreeDB (lib : Lib) : MonoClass := fun env N bl nm =>
  ∃ x, Comp.CallTreeD lib env N (SkaModel.Fits bl.less) x bl.fol nm

/-- **Track C's class of call trees** (indirect calls, `%3`, `%4`, `%5`,
`[7 p q]`), at the bell's formula. -/
def CallTreeAB : MonoClass := fun _ _ bl nm => ∃ x, Comp.CallTreeA x bl.fol nm

/-- **Track C's `TopTree`** at the bell's formula. -/
def TopTreeB : MonoClass := fun _ _ bl nm => Comp.TopTree bl.fol nm

theorem rawMonoD_callTreeD (lib : Lib) : RawMonoD S Map lib (CallTreeDB lib) := by
  intro code bl nm env s N _ _ hf _ h
  obtain ⟨x, hx⟩ := hf
  exact (Comp.finishLUCM_bellContractCallTreeD (S := S) hx h).2

theorem rawMonoD_callTreeA (lib : Lib) : RawMonoD S Map lib CallTreeAB := by
  intro code bl nm env s N _ _ hf _ h
  obtain ⟨x, hx⟩ := hf
  exact (Comp.finishLUCM_bellContractCallTreeA (S := S) (lib := lib) hx h N).2

theorem rawMonoD_topTree (lib : Lib) : RawMonoD S Map lib TopTreeB := by
  intro code bl nm env s N _ _ hf _ h
  exact (Comp.finishLUCM_bellContractTopTree (S := S) (lib := lib) hf h N).2

theorem pickTree_noDirect {f : Noun} {nm : Nomm} (h : Comp.PickTree f nm) : nm.noDirect = true := by
  induction h with
  | ind hp hq => simp [Nomm.noDirect, hp.noDirect, hq.noDirect]
  | n0 _ => rfl
  | seven hp _ ih => simp [Nomm.noDirect, hp.noDirect, ih]

theorem sixTest_noDirect {f : Noun} {c : Nomm} (h : Comp.SixTest (S := S) f c) : c.noDirect = true := by
  cases h with
  | pure _ ht _ => exact ht.noDirect
  | call hp _ => exact pickTree_noDirect hp
  | three ht _ => simp [Nomm.noDirect, ht.noDirect]

/-- **Track C's `Six0` has no direct call.** -/
theorem six0_noDirect {f : Noun} {nm : Nomm} {k : Nat} (h : Comp.Six0 (S := S) f nm k) : nm.noDirect = true := by
  induction h with
  | leaf ht _ => exact ht.noDirect
  | six hc _ _ _ iha ihb => simp [Nomm.noDirect, sixTest_noDirect hc, iha, ihb]

/-- **Track C's class with `%6` and calls** (`Six0`: tests of `SixTest`,
branches nested `%6` down to `CallTreeA` leaves), at the bell's formula. -/
def Six0B (S : Type) [Comp.HoonSet S] : MonoClass := fun _ _ bl nm => ∃ k, Comp.Six0 (S := S) bl.fol nm k

theorem rawMonoD_six0 (lib : Lib) : RawMonoD S Map lib (Six0B S) := by
  intro code bl nm env s N _ _ hf _ h
  obtain ⟨k, hk⟩ := hf
  rw [Comp.finishLUCM_eq env (six0_noDirect hk)] at h
  have H := Comp.finishLUC_contractSix0 (S := S) lib env (SkaModel.Fits bl.less) hk h N
  intro x hx args hargs
  simp only [if_true, Option.some.injEq] at hargs
  subst hargs
  exact H.2 x hx

/-- **The whole-subject classes with a raw contract, with calls**: `NCG`
(hence `FragUFG`, `FragU`), track J's `CallTreeD` (direct calls), track C's
`CallTreeA`, `TopTree` and `Six0` (`%6` with calls). -/
def MonoCalls (S : Type) [Comp.HoonSet S] (lib : Lib) : MonoClass :=
  orM (liftMC (NCG S)) (orM (CallTreeDB lib) (orM CallTreeAB (orM TopTreeB (Six0B S))))

/-- **The raw whole-subject contract on `MonoCalls`.** -/
theorem rawMonoD_calls (lib : Lib) : RawMonoD S Map lib (MonoCalls S lib) :=
  rawMonoD_or (rawMonoD_NCG lib) (rawMonoD_or (rawMonoD_callTreeD lib)
    (rawMonoD_or (rawMonoD_callTreeA lib) (rawMonoD_or (rawMonoD_topTree lib) (rawMonoD_six0 lib))))

/-- **Track J's n-ary class with calls**: `CallTreeA` at the bell's formula,
nothing baked. -/
def CallTreeAN : NaryClass := fun _ _ bl _ bake nm => (∃ x, Comp.CallTreeA x bl.fol nm) ∧ ∀ ned, bake ned = (ned, [])

theorem rawNaryD_callTreeA (lib : Lib) : RawNaryD S Map lib CallTreeAN := by
  intro code bl nm env ord cape data bake s N _ _ hbl hn hf _ h
  obtain ⟨⟨x, hx⟩, hb⟩ := hf
  exact Comp.finishLFC_bellContractCallTreeA (S := S) hx hbl hn hb h N

/-- **Track J's n-ary class with direct calls** (`CallTreeDN`, the `%cal`
and `%jmp` forms), at the subjects of the bell, nothing baked. -/
def CallTreeDNB (lib : Lib) : NaryClass := fun env N bl _ bake nm =>
  (∃ x, Comp.CallTreeDN lib env N (SkaModel.Fits bl.less) x bl.fol nm) ∧ ∀ ned, bake ned = (ned, [])

theorem rawNaryD_callTreeDN (lib : Lib) : RawNaryD S Map lib (CallTreeDNB lib) := by
  intro code bl nm env ord cape data bake s N _ _ hbl hn hf _ h
  obtain ⟨⟨x, hx⟩, hb⟩ := hf
  exact Comp.finishLFC_bellContractCallTreeDN (S := S) hx hbl hn hb h

/-- **The n-ary classes with a raw contract**: `FragUN` (call-free, nothing
baked), `CallTreeAN` and `CallTreeDNB` (nothing baked). -/
def NaryCalls (S : Type) [Comp.HoonSet S] (lib : Lib) : NaryClass :=
  orN (liftNC (FragUN S)) (orN CallTreeAN (CallTreeDNB lib))

theorem rawNaryD_calls (lib : Lib) : RawNaryD S Map lib (NaryCalls S lib) :=
  rawNaryD_or (rawNaryD_of (rawNary_fragU lib)) (rawNaryD_or (rawNaryD_callTreeA lib) (rawNaryD_callTreeDN lib))

/-! ## The restated pieces -/

/-- **`RefSide` with `refMono` at `finishLUCM`** and the classes taken at the
call environment of the compile and the needs of the reference compiler. -/
structure RefSideM (S : Type) [Comp.HoonSet S] (A : Arms M Map J H CR) (lib : Lib) (ref : Ref M Map J H)
    (D : CompData M Map J H) (FM : MonoClass) (FN : NaryClass) : Prop where
  /-- `CompRest.refMono` with the real whole-subject compile `finishLUCM`. -/
  refMono : ∀ long jets hot b s, InvB lib long → ref long jets hot b true = some s →
    ∃ nm, realOf long.code b = some nm ∧ Comp.finishLUCM (S := S) (D.env long jets hot b true) nm = some s
  /-- As `CompRest.refNary`. -/
  refNary : ∀ long jets hot b s, InvB lib long → ref long jets hot b false = some s →
    ∃ nm nb cape data, realOf long.code b = some nb ∧ D.inl long jets hot b = some nm ∧
      b.less = Sock.mk cape data ∧
      Comp.finishLFC (S := S) (D.env long jets hot b false) nm (D.ord long jets hot b) cape
        (D.bake long jets hot b) = some s
  /-- `CompRest.inFragM` for a class that sees `env`, `N`, the bell. -/
  inFragM : ∀ long jets hot b nm, InvB lib long → realOf long.code b = some nm →
    (ref long jets hot b true).isSome → FM (D.env long jets hot b true) (refN A ref long jets hot) b nm
  /-- `CompRest.inFragN` for a class that sees `env`, `N`, the bell. -/
  inFragN : ∀ long jets hot b nm cape data, InvB lib long → D.inl long jets hot b = some nm →
    b.less = Sock.mk cape data → (ref long jets hot b false).isSome →
    FN (D.env long jets hot b false) (refN A ref long jets hot) b cape (D.bake long jets hot b) nm

/-- **`CompRestO` over `RefSideM`**: every other field is the field of
`CompRestO` of the same name, unchanged. -/
structure CompRestM (S : Type) [Comp.HoonSet S] (M' : Type → Type → Type) [Treap M'] (A : Arms M Map J H CR)
    (lib : Lib) (ref : Ref M Map J H) (D : CompData M Map J H) (FM : MonoClass) (FN : NaryClass) : Prop
    extends RefSideM S A lib ref D FM FN where
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

/-- **The restated pieces with calls**: `CompRestM`, `RawOptIn` and the raw
contracts on classes that see `env`, `N`, the bell. -/
structure CompPiecesM (S : Type) [Comp.HoonSet S] (M' : Type → Type → Type) [Treap M'] (A : Arms M Map J H CR)
    (lib : Lib) (ref : Ref M Map J H) (D : CompData M Map J H) (FM : MonoClass) (FN : NaryClass) : Prop
    extends CompRestM S M' A lib ref D FM FN where
  rawOptIn : RawOptIn lib ref
  rawMono : RawMonoD S Map lib FM
  rawNary : RawNaryD S Map lib FN

/-- **The code of `finishLUCM` has one argument and the need `this`.** -/
theorem finishLUCM_this {env : Comp.CallEnv} {nm : Nomm} {c : Straight Map}
    (h : Comp.finishLUCM (S := S) env nm = some c) : c.need = NeedOrd.this ∧ c.nargs = 1 := by
  unfold Comp.finishLUCM at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  exact toStraightF_this h

variable (A : Arms M Map J H CR)

/-- **The contract field of `CompHyp` from `CompPiecesM`** (the proof of
`contract_of_piecesO`, at `finishLUCM`). -/
theorem contract_of_piecesM {M' : Type → Type → Type} [Treap M'] {lib : Lib} {ref : Ref M Map J H}
    {D : CompData M Map J H} {FM : MonoClass} {FN : NaryClass} (P : CompPiecesM S M' A lib ref D FM FN) :
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
  obtain ⟨e1, e2⟩ := finishLUCM_this hs
  obtain ⟨k1, k2, -, -⟩ := hk
  exact ⟨by rw [k2, e2], by rw [k1, e1]⟩

/-- **`CompHyp` from `CompPiecesM`**, the hypothesis of `gap_of_comp`. -/
theorem compHyp_of_piecesM {M' : Type → Type → Type} [Treap M'] {lib : Lib} {ref : Ref M Map J H}
    {D : CompData M Map J H} {FM : MonoClass} {FN : NaryClass} (P : CompPiecesM S M' A lib ref D FM FN) :
    CompHyp A lib ref where
  unary := P.unary
  scc := P.scc
  answers := P.answers
  contract := contract_of_piecesM A P
  stable := P.stable
  jetRoot := P.jetRoot
  jets := P.jets
  fast := P.fast

/-- **`CompRestO` on a class of `noDirect` nomms is `CompRestM`** on the
lifted classes (`finishLUCM_eq`): the old route is a special case. -/
theorem compRestM_of_O {M' : Type → Type → Type} [Treap M'] {lib : Lib} {ref : Ref M Map J H}
    {D : CompData M Map J H} {FM : Nomm → Prop}
    {FN : Cape → (Comp.Need → Comp.Need × List (Nat × Noun)) → Nomm → Prop}
    (P : CompRestO S M' A lib ref D FM FN) (hd : ∀ nm, FM nm → nm.noDirect = true) :
    CompRestM S M' A lib ref D (liftMC FM) (liftNC FN) where
  refMono := fun long jets hot b s hI hr => by
    obtain ⟨nm, hnm, hs⟩ := P.refMono long jets hot b s hI hr
    refine ⟨nm, hnm, ?_⟩
    rw [Comp.finishLUCM_eq _ (hd nm (P.inFragM long jets hot b nm hI hnm (by rw [hr]; rfl)))]
    exact hs
  refNary := P.refNary
  inFragM := P.inFragM
  inFragN := P.inFragN
  rawEntry := P.rawEntry
  optRef := P.optRef
  inlAnnot := P.inlAnnot
  callee := P.callee
  unary := P.unary
  scc := P.scc
  answers := P.answers
  stable := P.stable
  jetRoot := P.jetRoot
  jets := P.jets
  fast := P.fast

/-! ## The optimizer leaves as statements about the model, per class -/

/-- **Leaf (track D): the raw whole-subject blocks of the class meet `OptIn`.** -/
def OptInMono (S : Type) [Comp.HoonSet S] (Map : Type → Type) [HoonMap Map] [Comp.HoonMapKeys Map]
    [Opt.MapKeys Map] (FM : MonoClass) : Prop :=
  ∀ env N bl nm (s : Straight Map), FM env N bl nm → Comp.finishLUCM (S := S) env nm = some s → Opt.OptIn s.blocks

/-- **Leaf (track D): the raw n-ary blocks of the class meet `OptIn`.** -/
def OptInNary (S : Type) [Comp.HoonSet S] (Map : Type → Type) [HoonMap Map] [Comp.HoonMapKeys Map]
    [Opt.MapKeys Map] (FN : NaryClass) : Prop :=
  ∀ env N bl cape bake nm ord (s : Straight Map), FN env N bl cape bake nm →
    Comp.finishLFC (S := S) env nm ord cape bake = some s → Opt.OptIn s.blocks

/-- **`RawOptIn` from the two leaves.** -/
theorem rawOptIn_of {lib : Lib} {ref : Ref M Map J H} {D : CompData M Map J H} {FM : MonoClass}
    {FN : NaryClass} (P : RefSideM S A lib ref D FM FN) (hm : OptInMono S Map FM) (hn : OptInNary S Map FN) :
    RawOptIn lib ref := by
  intro long jets hot b m s hI hr
  cases m with
  | true =>
    obtain ⟨nm, hnm, hs⟩ := P.refMono long jets hot b s hI hr
    exact hm _ _ _ nm s (P.inFragM long jets hot b nm hI hnm (by rw [hr]; rfl)) hs
  | false =>
    obtain ⟨nm, nb, cape, data, hnb, hinl, hbl, hs⟩ := P.refNary long jets hot b s hI hr
    exact hn _ _ _ _ _ nm _ s (P.inFragN long jets hot b nm cape data hI hinl hbl (by rw [hr]; rfl)) hs

theorem optInMono_fragX : OptInMono S Map (liftMC (FragXM S)) := by
  intro env N bl nm s hf hs
  rw [Comp.finishLUCM_eq _ (Comp.noDirect_of_fragX hf.1),
    Comp.finishLUC_eq _ (Nomm.noCall_of_pure nm (Comp.fragX_pure hf.1))] at hs
  exact Raw.optIn_finishLUX hf.1 hf.2 hs

theorem optInNary_fragX : OptInNary S Map (liftNC (FragXN S)) := by
  intro env N bl cape bake nm ord s hf hs
  rw [Comp.finishLFC_eq _ (Nomm.noCall_of_pure nm (Comp.fragX_pure hf.1))] at hs
  exact Raw.optIn_finishLFX hf.1 hf.2.1 hf.2.2 hs

/-- **`CompHyp` on the classes with calls**: from `CompRestM` and the two
`OptIn` leaves of track D; the raw contracts are `rawMonoD_calls`,
`rawNaryD_calls`. -/
theorem compHyp_of_calls {M' : Type → Type → Type} [Treap M'] {lib : Lib} {ref : Ref M Map J H}
    {D : CompData M Map J H} (P : CompRestM S M' A lib ref D (MonoCalls S lib) (NaryCalls S lib))
    (hm : OptInMono S Map (MonoCalls S lib)) (hn : OptInNary S Map (NaryCalls S lib)) : CompHyp A lib ref :=
  compHyp_of_piecesM A
    { toCompRestM := P, rawOptIn := rawOptIn_of A P.toRefSideM hm hn, rawMono := rawMonoD_calls lib,
      rawNary := rawNaryD_calls lib }

/-! ## `rawEntry` as a statement about the model, per class -/

/-- **Leaf (no owner): `EntryOK` of the raw whole-subject code of the class**
on every subject of the bell, every oracle, scry gate, state and trace. -/
def EntryMono (S : Type) [Comp.HoonSet S] (Map : Type → Type) [HoonMap Map] [Comp.HoonMapKeys Map]
    (lib : Lib) (FM : MonoClass) : Prop :=
  ∀ env N bl nm (s : Straight Map), FM env N bl nm → Comp.finishLUCM (S := S) env nm = some s →
    ∀ x, SkaModel.Fits bl.less x →
      ∀ (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ) (t : Trace), Opt.EntryOK lib O s gul st [x] t

/-- **Leaf (no owner): `EntryOK` of the raw n-ary code of the class**, entered
with the split of a subject of the bell. -/
def EntryNary (S : Type) [Comp.HoonSet S] (Map : Type → Type) [HoonMap Map] [Comp.HoonMapKeys Map]
    (lib : Lib) (FN : NaryClass) : Prop :=
  ∀ env N bl cape bake nm ord (s : Straight Map), FN env N bl cape bake nm →
    Comp.finishLFC (S := S) env nm ord cape bake = some s →
    ∀ x, SkaModel.Fits bl.less x → ∀ args, SkaModel.split s.need x = some args →
      ∀ (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ) (t : Trace), Opt.EntryOK lib O s gul st args t

/-- **The field `rawEntry` of `CompRestM` from the two leaves.** -/
theorem rawEntry_of {lib : Lib} {ref : Ref M Map J H} {D : CompData M Map J H} {FM : MonoClass}
    {FN : NaryClass} (P : RefSideM S A lib ref D FM FN) (hm : EntryMono S Map lib FM)
    (hn : EntryNary S Map lib FN) :
    ∀ long jets hot b m s, InvB lib long → ref long jets hot b m = some s →
      ∀ x, SkaModel.Fits b.less x → ∀ args, (if m then some [x] else SkaModel.split s.need x) = some args →
        ∀ (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ) (t : Trace), Opt.EntryOK lib O s gul st args t := by
  intro long jets hot b m s hI hr x hx args hargs
  cases m with
  | true =>
    simp only [if_true, Option.some.injEq] at hargs
    subst hargs
    obtain ⟨nm, hnm, hs⟩ := P.refMono long jets hot b s hI hr
    exact hm _ _ _ nm s (P.inFragM long jets hot b nm hI hnm (by rw [hr]; rfl)) hs x hx
  | false =>
    simp only [Bool.false_eq_true, if_false] at hargs
    obtain ⟨nm, nb, cape, data, hnb, hinl, hbl, hs⟩ := P.refNary long jets hot b s hI hr
    exact hn _ _ _ _ _ nm _ s (P.inFragN long jets hot b nm cape data hI hinl hbl (by rw [hr]; rfl)) hs x hx
      args hargs

/-! ## `Straight.toNoun` is injective (the `hinj` of `optRef_fragX`)

Track P's `Compiler.straight_toNoun_inj` (`Ska/PokeEnc.lean`), importable
here since its `unitNoun_id_inj` became `unitNoun_id_injP` (M15 closed). -/

section
open Compiler Pill Hoon

/-- **`OptRef` on `FragX` without `hinj`**: `optRef_fragX` with
`straight_toNoun_inj`; one hypothesis left,
`hpill` (`A.optimize` is what the pill's `+optimize` returns on each
reference form). -/
theorem optRef_fragX' {A : Arms M (TreapMap mugF) J H CR} {lib : Lib} {ref : Ref M (TreapMap mugF) J H}
    {D : CompData M (TreapMap mugF) J H} (P : RefSide S lib ref D (FragXM S) (FragXN S))
    (hpill : ∀ long jets hot b m s, InvB lib long → ref long jets hot b m = some s →
      nock (C optBody (C s.toNoun optC)) optBody = some (A.optimize s).toNoun) :
    OptRef FinMap A lib ref :=
  optRef_fragX P hpill (fun _ _ h => straight_toNoun_inj h)

/-- **Leaf (the input side of track H's totality, track D's classes): the
pill's `+optimize` returns on the raw whole-subject code of the class, with
the model's passes.** -/
def OptTotalMono (S : Type) [Comp.HoonSet S] (FM : MonoClass) : Prop :=
  ∀ env N bl nm (c : Straight (TreapMap mugF)), FM env N bl nm → Comp.finishLUCM (S := S) env nm = some c →
    ∃ sfuel fuel s', Opt.optimizeF fuel ⟨Opt.aliasM (Ana.pickR FinMap), Opt.trimTraceHints,
      Opt.switchChains sfuel⟩ c = some s' ∧ nock (C optBody (C c.toNoun optC)) optBody = some s'.toNoun

/-- **Leaf, n-ary: the same on the raw n-ary code of the class.** -/
def OptTotalNary (S : Type) [Comp.HoonSet S] (FN : NaryClass) : Prop :=
  ∀ env N bl cape bake nm ord (c : Straight (TreapMap mugF)), FN env N bl cape bake nm →
    Comp.finishLFC (S := S) env nm ord cape bake = some c →
    ∃ sfuel fuel s', Opt.optimizeF fuel ⟨Opt.aliasM (Ana.pickR FinMap), Opt.trimTraceHints,
      Opt.switchChains sfuel⟩ c = some s' ∧ nock (C optBody (C c.toNoun optC)) optBody = some s'.toNoun

theorem optTotalMono_fragX : OptTotalMono S (liftMC (FragXM S)) := by
  intro env N bl nm c hf hs
  rw [Comp.finishLUCM_eq _ (Comp.noDirect_of_fragX hf.1),
    Comp.finishLUC_eq _ (Nomm.noCall_of_pure nm (Comp.fragX_pure hf.1))] at hs
  exact optimize_total_finishLUX hf.1 hf.2 hs

theorem optTotalNary_fragX : OptTotalNary S (liftNC (FragXN S)) := by
  intro env N bl cape bake nm ord c hf hs
  rw [Comp.finishLFC_eq _ (Nomm.noCall_of_pure nm (Comp.fragX_pure hf.1))] at hs
  exact optimize_total_finishLFX hf.1 hf.2.1 hf.2.2 hs

/-- **`OptRef` on any class from the totality leaves**, given `hpill` (no
`hinj`: `straight_toNoun_inj`). -/
theorem optRef_of_total {A : Arms M (TreapMap mugF) J H CR} {lib : Lib} {ref : Ref M (TreapMap mugF) J H}
    {D : CompData M (TreapMap mugF) J H} {FM : MonoClass} {FN : NaryClass} (P : RefSideM S A lib ref D FM FN)
    (hm : OptTotalMono S FM) (hn : OptTotalNary S FN)
    (hpill : ∀ long jets hot b m s, InvB lib long → ref long jets hot b m = some s →
      nock (C optBody (C s.toNoun optC)) optBody = some (A.optimize s).toNoun) :
    OptRef FinMap A lib ref := by
  intro long jets hot b m s hI hr
  have hp := hpill long jets hot b m s hI hr
  have fin : ∀ s' : Straight (TreapMap mugF), nock (C optBody (C s.toNoun optC)) optBody = some s'.toNoun →
      s' = A.optimize s := fun s' h => by
    rw [hp, Option.some.injEq] at h
    exact (straight_toNoun_inj h).symm
  cases m with
  | true =>
    obtain ⟨nm, hnm, hs⟩ := P.refMono long jets hot b s hI hr
    obtain ⟨sfuel, fuel, s', h1, h2⟩ := hm _ _ _ nm s (P.inFragM long jets hot b nm hI hnm (by rw [hr]; rfl)) hs
    exact ⟨fuel, sfuel, by rw [h1, fin s' h2]⟩
  | false =>
    obtain ⟨nm, nb, cape, data, hnb, hinl, hbl, hs⟩ := P.refNary long jets hot b s hI hr
    obtain ⟨sfuel, fuel, s', h1, h2⟩ :=
      hn _ _ _ _ _ nm _ s (P.inFragN long jets hot b nm cape data hI hinl hbl (by rw [hr]; rfl)) hs
    exact ⟨fuel, sfuel, by rw [h1, fin s' h2]⟩

end

end Glue
end SkaModel
end Formalization
