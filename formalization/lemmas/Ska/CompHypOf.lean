import lemmas.Ska.PokeModel
import lemmas.Ska.CompWholeTop
import lemmas.Ska.OptAliasSSAKeep

/-!
# `CompHyp` from named pieces

README Gaps 12.11.  `gap_of_comp` (`PokeAna.lean`) reduces the analysis side
of `Gap` to `CompHyp` (`PokeModel.lean`).  This file says what each field of
`CompHyp` asks of the Hoon, and derives `CompHyp` from `CompPieces`, a
structure of named hypotheses stated against the models of this track, so
that every theorem of the track discharges or refines one of its fields.

## The fields of `CompHyp`, against the Hoon

`ref long jets hot b m` is the reference compiler: the straight that
`+poke` returns for `%dire b m` before `+optimize` (line 9696), as a function
of `long-ska`, the jets state and `jets-hot` only.  For `m` `&` it is the
first component of `+compile-unary` (line 3390): `+run` with `mono` `&` on
`nomm:(~(got by code.long-ska) b)` for `[%done ~]`, `+kerf`, and
`+to-straight` of `[%next [[this+sub ~] ~ ~] ~ o]`, which `finishLUC` models
(exactly on nomms whose calls are all indirect).  For `m` `|` it is what the
final pass of `member` in `+compile-scc-in` (line 3505) puts into
`map-local` for `b`: `+run` with `mono` `|` on the nomm of `+inlined`,
`+collapse-shape`, `+bake-need` of `less.b`, `+coerce-lazy`, `+soft-done`,
the baked immediates and `+to-straight`, which `finishLFC` models with the
shape `ord` and the bake as parameters.

* `unary`: `+compile-unary` returns the reference form and keeps every
  cached form a reference one.  In the Hoon it first runs
  `+compile-scc-in` on the SCC (which fills `nary.cache`), and its cache
  is `cache.gen` after the run, so `inl` and `sure` of the cache must not
  change the code (they are `CR` in the model).
* `scc`: `+compile-scc` gives the reference forms of the whole SCC (the
  map of the final pass) and keeps the cache.
* `answers`: every bell that the reference compiler answers, `+poke`
  answers (`+scc-of`, then the compile, does not crash on it).
* `contract`: the reference code of a bell of a table with `InvB`, after
  `+optimize`, meets `BellContract` against the needs `refN` (the needs of
  the optimized reference forms), and the whole-subject version has one
  argument and the need `this`.  This is the field that `CompPieces`
  derives.
* `stable`: `+ska-poke` keeps every reference form (what is compiled holds:
  the code table only grows, `+scc-of` keeps old SCCs).
* `jetRoot`: the one-block straight `[%jsf func 0 rin]` of `%full` on a
  jetted root (line 9675) meets the contract of `%full`.
* `jets`, `fast`: the `%jets` and `%fast` branches keep `CacheOK`.

## The pieces

`CompData` holds what the Hoon computes and the models take as parameters:
the nomm of `+inlined` (`inl`, not modelled), the environment of the calls
(`env`: `+callee-need`, `+callee-sure`, the pure flags, the rings), the
shape of `+collapse-shape` (`ord`), the bake (`bake`: `+bake-need` is not
modelled), and the passes and fuel of `+optimize`.  `CompPieces` is
parametrized by two classes of nomms, `FM` for the whole-subject version
and `FN` for the n-ary one (the latter also sees the cape and the bake),
on which the raw contract is assumed; the goal is `FM` and `FN` true of
every nomm.

* (a) `refMono`, `refNary`: the reference compiler is the model.
* (b) `rawMono`, `rawNary`: the model's raw code of a nomm of the class
  meets `BellContract` (the run contract, per version, before
  `+optimize`); `inFragM`, `inFragN`: the nomms compiled are in the class.
* (c) `rawDInv`, `rawEntry`: the raw code meets the optimizer's input
  invariant (`DInvS` of the blocks, `EntryOK` of every entry on a subject
  that fits the bell).
* (d) `optEq`, `optAlias`, `optSSA`: `+optimize` is `optimizeF` with the
  passes of `CompData`, and its remaining hypotheses (`DriverRestSSA`,
  `SSAKeepR`), with which `optimize_keeps_ssaR` gives `Keeps`.
* (e) `inlAnnot`: the nomm of `+inlined` stands for the bell's formula.
* (f) the bake: inside `FN` (on the fragment, nothing is baked).
* (g) `callee`: the callees' needs the compiler used are the reference
  needs (`CalleeNeeds env (refN …)`; within an SCC this is the fixed point
  of `+compile-scc-in`).
* (h) `unary`, `scc`, `answers`, `stable`, `jetRoot`, `jets`, `fast`, as
  in `CompHyp`.

`compHyp_of_pieces` derives `CompHyp`.  `rawMono_fragU` and
`rawNary_fragU` prove (b) on `FragU` with at most 255 `%6` (and, for the
n-ary version, nothing baked), so `compHyp_of_frag` derives `CompHyp` from
`CompRest` (every field but (b)) with those classes.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace PokeM

open Nock Ana Bake

variable {M : Type → Type → Type} [Treap M] {Map : Type → Type} [HoonMap Map] [Comp.HoonMapKeys Map]
  [Opt.MapKeys Map] {J H CR : Type}

/-! ## The whole-subject code has one argument, the subject -/

theorem toStraightF_this {cond : Map (Nat × List Nat)} {blocks : Map Blob} {r o : Nat} {c : Straight Map}
    (h : Comp.toStraightF cond blocks (Comp.Need.this r) o = some c) :
    c.need = NeedOrd.this ∧ c.nargs = 1 := by
  have hn := Comp.toStraightF_nargs h
  unfold Comp.toStraightF at h
  obtain ⟨start, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨input, st⟩, hi, h⟩ := Option.bind_eq_some_iff.mp h
  have e : input = NeedOrd.this := by
    unfold Comp.rewriteInput at hi
    split at hi
    · simp only [Comp.rewriteInputGo, Comp.bindR_apply] at hi
      obtain ⟨_, _, hi⟩ := Option.bind_eq_some_iff.mp hi
      cases hi; rfl
    · cases hi
  have hneed : c.need = input := by
    simp only at h
    split at h
    · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h; rfl
    · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h; rfl
  rw [hneed, e] at hn ⊢
  exact ⟨rfl, hn⟩

/-- **The code of `+compile-unary` has one argument and the need `this`**,
whatever the nomm. -/
theorem finishLUC_this {S : Type} [Comp.HoonSet S] {env : Comp.CallEnv} {nm : Nomm} {c : Straight Map}
    (h : Comp.finishLUC (S := S) env nm = some c) : c.need = NeedOrd.this ∧ c.nargs = 1 := by
  unfold Comp.finishLUC at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  exact toStraightF_this h

/-! ## `+optimize` keeps the contract -/

/-- **A pass that keeps the code keeps the contract**, when every entry of
the contract has `EntryOK`. -/
theorem bellContract_of_keeps {lib : Lib} {N : Needs} {b : Bell} {m : Bool} {s s' : Straight Map}
    (hc : BellContract lib N b m s) (hk : Opt.Keeps s s')
    (he : ∀ x, SkaModel.Fits b.less x → ∀ args, (if m then some [x] else SkaModel.split s.need x) = some args →
      ∀ (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ) (t : Trace), Opt.EntryOK lib O s gul st args t) :
    BellContract lib N b m s' := by
  obtain ⟨hneed, -, -, hrun⟩ := hk
  intro x hx args hargs
  have hargs' : (if m then some [x] else SkaModel.split s.need x) = some args := by rw [← hneed]; exact hargs
  obtain ⟨F, B⟩ := hc x hx args hargs'
  have eq : ∀ (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun),
      execEntry lib O st s' args t gul = execEntry lib O st s args t gul :=
    fun σ O st t gul => (hrun lib σ O gul st args t (he x hx args hargs' σ O gul st t)).1
  refine ⟨fun σ Inv ν O n gul ti tm r h1 h2 h3 hm st hI htr => ?_,
    fun σ Inv ν O gul ti tm h1 h2 h3 st ton st' hI htr hr => ?_⟩
  · rw [eq]; exact F σ Inv ν O n gul ti tm r h1 h2 h3 hm st hI htr
  · rw [eq] at hr; exact B σ Inv ν O gul ti tm h1 h2 h3 st ton st' hI htr hr

theorem capeNorm_of_normCape : ∀ {c : Cape}, NormCape c → Comp.CapeNorm c
  | Cape.yes, _ => trivial
  | Cape.no, _ => trivial
  | Cape.cell _ _, ⟨h0, h1, h2⟩ => ⟨h0, capeNorm_of_normCape h1, capeNorm_of_normCape h2⟩

/-! ## The pieces -/

/-- What the Hoon computes and the models take as parameters. -/
structure CompData (M : Type → Type → Type) (Map : Type → Type) [HoonMap Map] (J H : Type) where
  /-- The nomm of `+inlined` (line 3298) for a bell, from `code.long-ska`,
  the rings and `jets-hot` (not modelled). -/
  inl : LongB M → J → H → Bell → Option Nomm
  /-- The environment of the calls in the compile of a bell, per version. -/
  env : LongB M → J → H → Bell → Bool → Comp.CallEnv
  /-- The shape of `+collapse-shape` in the final pass of the n-ary version. -/
  ord : LongB M → J → H → Bell → NeedOrd
  /-- `+bake-need` of `less.b` (not modelled). -/
  bake : LongB M → J → H → Bell → Comp.Need → Comp.Need × List (Nat × Noun)
  /-- The passes of `+optimize`, the fuel of `+switch-chains`, and the fuel
  of the loop for a straight. -/
  optP : Opt.Passes Map
  sfuel : Nat
  optFuel : Straight Map → Nat

/-- **Every piece but the raw contract** (b), for the classes `FM` and
`FN` of nomms on which the raw contract is known. -/
structure CompRest (S : Type) [Comp.HoonSet S] (A : Arms M Map J H CR) (lib : Lib) (ref : Ref M Map J H)
    (D : CompData M Map J H) (FM : Nomm → Prop)
    (FN : Cape → (Comp.Need → Comp.Need × List (Nat × Noun)) → Nomm → Prop) : Prop where
  /-- (a) The whole-subject reference code is the model's, on the nomm of
  the code table. -/
  refMono : ∀ long jets hot b s, InvB lib long → ref long jets hot b true = some s →
    ∃ nm, realOf long.code b = some nm ∧ Comp.finishLUC (S := S) (D.env long jets hot b true) nm = some s
  /-- (a) The n-ary reference code is the model's, on the nomm of
  `+inlined`, for a bell of the code table. -/
  refNary : ∀ long jets hot b s, InvB lib long → ref long jets hot b false = some s →
    ∃ nm nb cape data, realOf long.code b = some nb ∧ D.inl long jets hot b = some nm ∧
      b.less = Sock.mk cape data ∧
      Comp.finishLFC (S := S) (D.env long jets hot b false) nm (D.ord long jets hot b) cape
        (D.bake long jets hot b) = some s
  /-- (b) The nomms compiled are in the classes. -/
  inFragM : ∀ long jets hot b nm, InvB lib long → realOf long.code b = some nm →
    (ref long jets hot b true).isSome → FM nm
  inFragN : ∀ long jets hot b nm cape data, InvB lib long → D.inl long jets hot b = some nm →
    b.less = Sock.mk cape data → (ref long jets hot b false).isSome → FN cape (D.bake long jets hot b) nm
  /-- (c) The raw blocks meet the optimizer's block invariant. -/
  rawDInv : ∀ long jets hot b m s, InvB lib long → ref long jets hot b m = some s → Opt.DInvS s.blocks
  /-- (c) Every entry of the raw code on a subject that fits the bell meets
  `EntryOK`. -/
  rawEntry : ∀ long jets hot b m s, InvB lib long → ref long jets hot b m = some s →
    ∀ x, SkaModel.Fits b.less x → ∀ args, (if m then some [x] else SkaModel.split s.need x) = some args →
      ∀ (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ) (t : Trace), Opt.EntryOK lib O s gul st args t
  /-- (d) `+optimize` is the model with the passes of `D`. -/
  optEq : ∀ s, Opt.optimizeF (D.optFuel s) D.optP s = some (A.optimize s)
  /-- (d) `+alias` keeps the code and the invariants, the trim pass is the
  real one, the switch pass the model (`DriverRestSSA`). -/
  optAlias : ∀ fuel, Opt.DriverRestSSA fuel D.sfuel D.optP
  /-- (d) The passes of the loop keep single assignment (`SSAKeepR`). -/
  optSSA : ∀ fuel, Opt.SSAKeepR Map fuel
  /-- (e) The nomm of `+inlined` stands for the bell's formula. -/
  inlAnnot : ∀ long jets hot b nm, InvB lib long → D.inl long jets hot b = some nm →
    Annot lib (realOf long.code) (SkaModel.Fits b.less) b.fol nm
  /-- (g) The callees' needs the compiler used are the reference needs.
  Untested for a hot-jet callee, whose need `+callee-need` takes from
  `jets-hot` (line 4597), not from the callee's compile: the field says that
  `%dire b |` answers that same need.  Within an SCC the need is that of
  `map-local`, so the field holds there when the fixed point is the final
  pass's need. -/
  callee : ∀ long jets hot b m, InvB lib long → Comp.CalleeNeeds (D.env long jets hot b m) (refN A ref long jets hot)
  /-- (h) As `CompHyp.unary`. -/
  unary : ∀ b scc long jets hot c s n c', A.compileUnary b scc long jets hot c = some ((s, n), c') →
    ref long jets hot b true = some s ∧ (CacheOK ref long jets hot c → CacheOK ref long jets hot c')
  /-- (h) As `CompHyp.scc`. -/
  scc : ∀ scc long jets hot c m c', A.compileScc scc long jets hot c = some (m, c') →
    (∀ b s, Treap.get m b = some s → ref long jets hot b false = some s) ∧
      (CacheOK ref long jets hot c → CacheOK ref long jets hot c')
  /-- (h) As `CompHyp.answers`. -/
  answers : ∀ st b m s, InvS lib ref st → ref st.long st.jets st.hot b m = some s →
    (compileStep A st b m).isSome
  /-- (h) As `CompHyp.stable`. -/
  stable : ∀ s f long jets hot r b m x, A.skaPoke s f long jets hot = some r → InvB lib long →
    ref long jets hot b m = some x → ref r.2.1 r.2.2.1 hot b m = some x
  /-- (h) As `CompHyp.jetRoot`. -/
  jetRoot : ∀ s f long jets hot r out, A.skaPoke s f long jets hot = some r → InvB lib long →
    A.jetRoot r.2.2.1 hot r.1 = some out →
    out.nargs = 1 ∧ out.need = NeedOrd.this ∧
      ContractFwd lib (refN A ref r.2.1 r.2.2.1 hot) s f [s] out ∧
      ContractBwd lib (refN A ref r.2.1 r.2.2.1 hot) s f [s] out
  /-- (h) As `CompHyp.jets`. -/
  jets : ∀ st p r, ¬ HotOvum (Ovum.jets p) → A.jetsPoke st p = some r →
    CacheOK ref st.long st.jets st.hot st.cache → CacheOK ref st.long r.2.1 r.2.2.1 r.2.2.2
  /-- (h) As `CompHyp.fast`. -/
  fast : ∀ st rs p r, A.fastPoke st rs p = some r →
    CacheOK ref st.long st.jets st.hot st.cache → CacheOK ref st.long r.1 st.hot r.2

/-- (b) **The raw whole-subject contract on the class `FM`**. -/
def RawMono (S : Type) [Comp.HoonSet S] (Map : Type → Type) [HoonMap Map] [Comp.HoonMapKeys Map] (lib : Lib)
    (FM : Nomm → Prop) : Prop :=
  ∀ (code : Bell → Option Nomm) (bl : Bell) (nm : Nomm) (env : Comp.CallEnv) (s : Straight Map) (N : Needs),
    CodeOK lib code → Annot lib code (SkaModel.Fits bl.less) bl.fol nm → FM nm → Comp.CalleeNeeds env N →
    Comp.finishLUC (S := S) env nm = some s → BellContract lib N bl true s

/-- (b) **The raw n-ary contract on the class `FN`** (normal cape, any shape
`ord`). -/
def RawNary (S : Type) [Comp.HoonSet S] (Map : Type → Type) [HoonMap Map] [Comp.HoonMapKeys Map] (lib : Lib)
    (FN : Cape → (Comp.Need → Comp.Need × List (Nat × Noun)) → Nomm → Prop) : Prop :=
  ∀ (code : Bell → Option Nomm) (bl : Bell) (nm : Nomm) (env : Comp.CallEnv) (ord : NeedOrd) (cape : Cape)
    (data : Noun) (bake : Comp.Need → Comp.Need × List (Nat × Noun)) (s : Straight Map) (N : Needs),
    CodeOK lib code → Annot lib code (SkaModel.Fits bl.less) bl.fol nm → bl.less = Sock.mk cape data →
    Comp.CapeNorm cape → FN cape bake nm → Comp.CalleeNeeds env N →
    Comp.finishLFC (S := S) env nm ord cape bake = some s → BellContract lib N bl false s

/-- **The pieces**: `CompRest` and the raw contract (b) on the classes. -/
structure CompPieces (S : Type) [Comp.HoonSet S] (A : Arms M Map J H CR) (lib : Lib) (ref : Ref M Map J H)
    (D : CompData M Map J H) (FM : Nomm → Prop)
    (FN : Cape → (Comp.Need → Comp.Need × List (Nat × Noun)) → Nomm → Prop) : Prop
    extends CompRest S A lib ref D FM FN where
  rawMono : RawMono S Map lib FM
  rawNary : RawNary S Map lib FN

variable {S : Type} [Comp.HoonSet S] (A : Arms M Map J H CR)

/-- `+optimize` keeps every reference form. -/
theorem CompRest.keeps {lib : Lib} {ref : Ref M Map J H} {D : CompData M Map J H} {FM : Nomm → Prop}
    {FN : Cape → (Comp.Need → Comp.Need × List (Nat × Noun)) → Nomm → Prop}
    (P : CompRest S A lib ref D FM FN) {long : LongB M} {jets : J} {hot : H} {b : Bell} {m : Bool}
    {s : Straight Map} (hI : InvB lib long) (hr : ref long jets hot b m = some s) : Opt.Keeps s (A.optimize s) :=
  Opt.optimize_keeps_ssaR (P.optAlias _) (P.optSSA _) (P.rawDInv long jets hot b m s hI hr) (P.optEq s)

/-- **The contract field from the pieces.** -/
theorem contract_of_pieces {lib : Lib} {ref : Ref M Map J H} {D : CompData M Map J H} {FM : Nomm → Prop}
    {FN : Cape → (Comp.Need → Comp.Need × List (Nat × Noun)) → Nomm → Prop}
    (P : CompPieces S A lib ref D FM FN) :
    ∀ long jets hot b m s, InvB lib long → ref long jets hot b m = some s →
      BellContract lib (refN A ref long jets hot) b m (A.optimize s) ∧
        (m = true → (A.optimize s).nargs = 1 ∧ (A.optimize s).need = NeedOrd.this) := by
  intro long jets hot b m s hI hr
  have hk := P.keeps A hI hr
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

/-- **`CompHyp` from the pieces.** -/
theorem compHyp_of_pieces {lib : Lib} {ref : Ref M Map J H} {D : CompData M Map J H} {FM : Nomm → Prop}
    {FN : Cape → (Comp.Need → Comp.Need × List (Nat × Noun)) → Nomm → Prop}
    (P : CompPieces S A lib ref D FM FN) : CompHyp A lib ref where
  unary := P.unary
  scc := P.scc
  answers := P.answers
  contract := contract_of_pieces A P
  stable := P.stable
  jetRoot := P.jetRoot
  jets := P.jets
  fast := P.fast

/-! ## The raw contract on the fragment -/

/-- The class of the whole-subject version on which (b) is proved. -/
def FragUM (S : Type) [Comp.HoonSet S] (nm : Nomm) : Prop := Comp.FragU (S := S) nm ∧ Comp.sixCount nm ≤ 255

/-- The class of the n-ary version on which (b) is proved: nothing baked. -/
def FragUN (S : Type) [Comp.HoonSet S] (_cape : Cape) (bake : Comp.Need → Comp.Need × List (Nat × Noun))
    (nm : Nomm) : Prop :=
  Comp.FragU (S := S) nm ∧ Comp.sixCount nm ≤ 255 ∧ ∀ ned, bake ned = (ned, [])

/-- **(b) for the whole-subject version on `FragU`** (`finishLU_bellContractFU`). -/
theorem rawMono_fragU (lib : Lib) : RawMono S Map lib (FragUM S) := by
  intro code bl nm env s N hok hA hf _ h
  rw [Comp.finishLUC_eq env (Nomm.noCall_of_pure nm (Comp.fragU_pure hf.1))] at h
  exact Comp.finishLU_bellContractFU hok hA hf.1 hf.2 h N

/-- **(b) for the n-ary version on `FragU`, nothing baked**
(`finishLF_bellContractFU`). -/
theorem rawNary_fragU (lib : Lib) : RawNary S Map lib (FragUN S) := by
  intro code bl nm env ord cape data bake s N hok hA hbl hn hf _ h
  rw [Comp.finishLFC_eq env (Nomm.noCall_of_pure nm (Comp.fragU_pure hf.1))] at h
  exact Comp.finishLF_bellContractFU hok (Comp.fragU_pure hf.1) hA hf.1 hf.2.1 hbl hn hf.2.2 h N

/-- **`CompHyp` when every nomm compiled is in `FragU`** (and the n-ary
version bakes nothing): from `CompRest` alone. -/
theorem compHyp_of_frag {lib : Lib} {ref : Ref M Map J H} {D : CompData M Map J H}
    (P : CompRest S A lib ref D (FragUM S) (FragUN S)) : CompHyp A lib ref :=
  compHyp_of_pieces (S := S) A ⟨P, rawMono_fragU lib, rawNary_fragU lib⟩

end PokeM
end SkaModel
end Formalization
