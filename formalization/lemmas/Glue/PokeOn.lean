import lemmas.Glue.InvMemoP

/-!
# Glue: the `PokeM` chain over REACHED states (track G, fourteenth pass; misfit 4)

`CompHyp` (`Ska/PokeModel.lean`) asks `unary`, `scc`, `contract`, `stable`, ... on EVERY
table that meets `InvB` (and every cache), but the pill facts that discharge them hold only on
the states the compiler reaches (track K's record at `PGood6` states, track Q's `inlAnnot_of_inv`
on the states of an invariant).  Here the chain is re-proved relative to two predicates:

* `I`, an invariant of states (true of the bunt state, kept by every poke that names no jet:
  the record `ReachOn`, field `kept`);
* `Rd st b`, "the compile step runs on `st` at the bell `b`": every `I` state at every bell
  (`ReachOn.now`), and the state after `+ska-poke` in `%full` at the root bell (`ReachOn.ana`).

`CompHypOn A lib ref I Rd` is `CompHyp` with `unary`, `answers`, `contract` asked at `Rd`
states only, and `scc` (only `%dire` runs it), `stable`, `jetRoot`, `jets`, `fast` at `I`
states only.  The proofs are those of `compileStep_spec`, `needOf_eq`, `pokeS_sound`,
`pokeS_invKept`, `gap_of_armPM`, `fullAnswers_of_cgMP`, with the one change that `%full`
compares the needs of the first and the last state directly (the state in the middle need not
satisfy `I`).  The invariant of `Gap` is `liftInv (enc fl) (InvSMI lib ref I)`,
`InvSMI lib ref I st := InvSM lib ref st ∧ I st`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Ana Bake PokeM

section Gen

variable {M : Type → Type → Type} [Treap M] {Map : Type → Type} [HoonMap Map] {J H CR : Type}
variable (A : Arms M Map J H CR)

/-- The state of `%full` after `+ska-poke`, before the compile. -/
abbrev midSt (st : CSt M Map J H CR) (r : Bell × LongB M × J × Noun) : CSt M Map J H CR :=
  { st with long := r.2.1, jets := r.2.2.1 }

/-- **The reached states**: `I` is kept by every poke that names no jet, and the compile step
runs on `Rd` states only (`I` states at every bell; the state after `+ska-poke` at its root). -/
structure ReachOn (I : CSt M Map J H CR → Prop) (Rd : CSt M Map J H CR → Bell → Prop) : Prop where
  now : ∀ st b, I st → Rd st b
  ana : ∀ st s f r, I st → A.skaPoke s f st.long st.jets st.hot = some r → Rd (midSt st r) r.1
  kept : ∀ st ov p st', I st → ¬ HotOvum ov → pokeS A st ov = some (p, st') → I st'

/-- **`CompHyp` without `contract`, over the reached states.** -/
structure CompStateOn (lib : Lib) (ref : Ref M Map J H) (I : CSt M Map J H CR → Prop)
    (Rd : CSt M Map J H CR → Bell → Prop) : Prop where
  /-- `+compile-unary` (after `+scc-of`) gives the reference form and keeps the cache, at `Rd`. -/
  unary : ∀ (st : CSt M Map J H CR) b q s n c', Rd st b → A.sccOf b st.long st.cache.sccs = some q →
    A.compileUnary b q.1 st.long st.jets st.hot { st.cache with sccs := q.2 } = some ((s, n), c') →
    ref st.long st.jets st.hot b true = some s ∧
      (CacheOK ref st.long st.jets st.hot st.cache → CacheOK ref st.long st.jets st.hot c')
  /-- `+compile-scc` (after `+scc-of`) gives the reference forms and keeps the cache, at `I`. -/
  scc : ∀ (st : CSt M Map J H CR) b q m c', I st → A.sccOf b st.long st.cache.sccs = some q →
    A.compileScc q.1 st.long st.jets st.hot { st.cache with sccs := q.2 } = some (m, c') →
    (∀ b' s, Treap.get m b' = some s → ref st.long st.jets st.hot b' false = some s) ∧
      (CacheOK ref st.long st.jets st.hot st.cache → CacheOK ref st.long st.jets st.hot c')
  /-- The compiler answers every bell the reference compiler does, at `Rd`. -/
  answers : ∀ (st : CSt M Map J H CR) b m s, Rd st b → InvS lib ref st →
    ref st.long st.jets st.hot b m = some s → (compileStep A st b m).isSome
  /-- What is compiled holds across `+ska-poke`, at `I`. -/
  stable : ∀ (st : CSt M Map J H CR) s f r b m x, I st → A.skaPoke s f st.long st.jets st.hot = some r →
    InvB lib st.long → ref st.long st.jets st.hot b m = some x → ref r.2.1 r.2.2.1 st.hot b m = some x
  /-- The jetted root, at `I`. -/
  jetRoot : ∀ (st : CSt M Map J H CR) s f r out, I st → A.skaPoke s f st.long st.jets st.hot = some r →
    InvB lib st.long → A.jetRoot r.2.2.1 st.hot r.1 = some out →
    out.nargs = 1 ∧ out.need = NeedOrd.this ∧
      ContractFwd lib (refN A ref r.2.1 r.2.2.1 st.hot) s f [s] out ∧
      ContractBwd lib (refN A ref r.2.1 r.2.2.1 st.hot) s f [s] out
  /-- `%jets ~` keeps the cache, at `I`. -/
  jets : ∀ st p r, I st → ¬ HotOvum (Ovum.jets p) → A.jetsPoke st p = some r →
    CacheOK ref st.long st.jets st.hot st.cache → CacheOK ref st.long r.2.1 r.2.2.1 r.2.2.2
  /-- `%fast` keeps the cache, at `I`. -/
  fast : ∀ st rs p r, I st → A.fastPoke st rs p = some r →
    CacheOK ref st.long st.jets st.hot st.cache → CacheOK ref st.long r.1 st.hot r.2

/-- **`CompHyp` over the reached states.** -/
structure CompHypOn (lib : Lib) (ref : Ref M Map J H) (I : CSt M Map J H CR → Prop)
    (Rd : CSt M Map J H CR → Bell → Prop) : Prop extends CompStateOn A lib ref I Rd where
  /-- The contract, at the tables of `Rd` states. -/
  contract : ∀ (st : CSt M Map J H CR) b m s, Rd st b → InvB lib st.long →
    ref st.long st.jets st.hot b m = some s →
    BellContract lib (refN A ref st.long st.jets st.hot) b m (A.optimize s) ∧
      (m = true → (A.optimize s).nargs = 1 ∧ (A.optimize s).need = NeedOrd.this)

variable {A}
variable {lib : Lib} {ref : Ref M Map J H} {I : CSt M Map J H CR → Prop} {Rd : CSt M Map J H CR → Bell → Prop}

/-- `compileStep_spec` at a `Rd` state (and an `I` state for the n-ary version). -/
theorem compileStep_specOn (hC : CompStateOn A lib ref I Rd) {st st' : CSt M Map J H CR}
    {b : Bell} {m : Bool} {c : Straight Map} (hrd : Rd st b) (hi : m = false → I st)
    (hok : CacheOK ref st.long st.jets st.hot st.cache)
    (h : compileStep A st b m = some (c, st')) :
    ∃ s, ref st.long st.jets st.hot b m = some s ∧ c = A.optimize s ∧ st'.long = st.long ∧ st'.jets = st.jets ∧
      st'.hot = st.hot ∧ CacheOK ref st'.long st'.jets st'.hot st'.cache := by
  unfold compileStep at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨⟨scc, sccs⟩, hq, ⟨s, cache'⟩, hc, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  suffices ref st.long st.jets st.hot b m = some s ∧ CacheOK ref st.long st.jets st.hot cache' from
    ⟨s, this.1, rfl, rfl, rfl, rfl, this.2⟩
  cases m with
  | true =>
    simp only [if_true, compiledMono] at hc
    split at hc
    · rename_i s0 hs0
      cases hc
      exact ⟨hok.1 b _ hs0, hok⟩
    · simp only [Option.map_eq_some_iff] at hc
      obtain ⟨⟨⟨s1, n1⟩, c1⟩, hu, he⟩ := hc
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨hr, hk⟩ := hC.unary st b (scc, sccs) s1 n1 c1 hrd hq hu
      refine ⟨hr, fun b' s' hs' => ?_, (hk hok).2⟩
      simp only [Treap.get_put] at hs'
      split at hs'
      · rename_i e; cases hs'; subst e; exact hr
      · exact (hk hok).1 b' s' hs'
  | false =>
    simp only [Bool.false_eq_true, if_false, compiledNary] at hc
    split at hc
    · rename_i s0 hs0
      cases hc
      exact ⟨hok.2 b _ hs0, hok⟩
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
      obtain ⟨⟨m1, c1⟩, hu, s1, hs1, he⟩ := hc
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨hr, hk⟩ := hC.scc st b (scc, sccs) m1 c1 (hi rfl) hq hu
      exact ⟨hr b _ hs1, hk hok⟩

/-- `needOf_eq` at a state that is `Rd` at every bell. -/
theorem needOf_eqOn (hC : CompStateOn A lib ref I Rd) {st : CSt M Map J H CR} (hrd : ∀ b, Rd st b)
    (hi : I st) (hI : InvS lib ref st) : needOf (pokeS A) st = refN A ref st.long st.jets st.hot := by
  funext b m
  unfold needOf refN
  simp only [pokeS]
  cases hs : compileStep A st b m with
  | none =>
    cases hr : ref st.long st.jets st.hot b m with
    | none => rfl
    | some s =>
      have := hC.answers st b m s (hrd b) hI hr
      rw [hs] at this; cases this
  | some p =>
    obtain ⟨c, st'⟩ := p
    obtain ⟨s, hr, rfl, -⟩ := compileStep_specOn hC (hrd b) (fun _ => hi) hI.2 hs
    simp [hr]

theorem not_hot_dire (b : Bell) (m : Bool) : ¬ HotOvum (Ovum.dire b m) := id
theorem not_hot_full (s f : Noun) : ¬ HotOvum (Ovum.full s f) := id

/-- **`pokeS_sound` over the reached states.** -/
theorem pokeS_soundOn (hC : CompHypOn A lib ref I Rd) (hR : ReachOn A I Rd) (hA : AnaHyp A lib) :
    Sound lib (pokeS A) (fun st => InvS lib ref st ∧ I st) where
  dire := by
    intro st b m p st' hI h
    have hI'' : I st' := hR.kept st _ p st' hI.2 (not_hot_dire b m) h
    simp only [pokeS, Option.map_eq_some_iff] at h
    obtain ⟨⟨c, st2⟩, hs, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨s, _, rfl, hl, hj, hh, hok⟩ :=
      compileStep_specOn hC.toCompStateOn (hR.now st b hI.2) (fun _ => hI.2) hI.1.2 hs
    have hI' : InvS lib ref st2 := ⟨hl ▸ hI.1.1, hok⟩
    refine ⟨⟨hI', hI''⟩, ?_⟩
    rw [needOf_eqOn hC.toCompStateOn (fun b => hR.now st b hI.2) hI.2 hI.1,
      needOf_eqOn hC.toCompStateOn (fun b => hR.now st2 b hI'') hI'' hI', hl, hj, hh]
    exact Needs.le_refl _
  full := by
    intro st s f p st' hI h
    have hI' : I st' := hR.kept st _ p st' hI.2 (not_hot_full s f) h
    simp only [pokeS, Option.bind_eq_some_iff] at h
    obtain ⟨r, hr, h⟩ := h
    obtain ⟨hB, -, -⟩ := hA.ana s f st.long st.jets st.hot r hr hI.1.1
    have hok1 : CacheOK ref r.2.1 r.2.2.1 st.hot st.cache :=
      ⟨fun b x hx => hC.stable st s f r b true x hI.2 hr hI.1.1 (hI.1.2.1 b x hx),
       fun b x hx => hC.stable st s f r b false x hI.2 hr hI.1.1 (hI.1.2.2 b x hx)⟩
    have hle : ∀ st2 : CSt M Map J H CR, st2.long = r.2.1 → st2.jets = r.2.2.1 → st2.hot = st.hot → I st2 →
        InvS lib ref st2 → needOf (pokeS A) st ≤ needOf (pokeS A) st2 := by
      intro st2 hl hj hh hI2 hS2
      rw [needOf_eqOn hC.toCompStateOn (fun b => hR.now st b hI.2) hI.2 hI.1,
        needOf_eqOn hC.toCompStateOn (fun b => hR.now st2 b hI2) hI2 hS2, hl, hj, hh]
      intro b m x hx
      simp only [refN, Option.map_eq_some_iff] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, hC.stable st s f r b m y hI.2 hr hI.1.1 hy, rfl⟩
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨⟨⟨hB, hok1⟩, hI'⟩, hle _ rfl rfl rfl hI' ⟨hB, hok1⟩⟩
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨c, st2⟩, hs, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      obtain ⟨_, _, rfl, hl, hj, hh, hok⟩ :=
        compileStep_specOn hC.toCompStateOn (hR.ana st s f r hI.2 hr) (fun e => by cases e) hok1 hs
      have hI2 : InvS lib ref st2 := ⟨by rw [hl]; exact hB, hok⟩
      exact ⟨⟨hI2, hI'⟩, hle st2 hl hj hh hI' hI2⟩
  dire_code := by
    intro st b m p st' hI h
    have hI'' : I st' := hR.kept st _ p st' hI.2 (not_hot_dire b m) h
    simp only [pokeS, Option.map_eq_some_iff] at h
    obtain ⟨⟨c, st2⟩, hs, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨s, hr, rfl, hl, hj, hh, hok⟩ :=
      compileStep_specOn hC.toCompStateOn (hR.now st b hI.2) (fun _ => hI.2) hI.1.2 hs
    have hI' : InvS lib ref st2 := ⟨hl ▸ hI.1.1, hok⟩
    refine ⟨b, A.optimize s, Noun.atom 0, rfl, ?_⟩
    rw [needOf_eqOn hC.toCompStateOn (fun b => hR.now st2 b hI'') hI'' hI', hl, hj, hh]
    exact (hC.contract st b m s (hR.now st b hI.2) hI.1.1 hr).1
  full_code := by
    intro st s f p st' hI h
    have hI'' : I st' := hR.kept st _ p st' hI.2 (not_hot_full s f) h
    simp only [pokeS, Option.bind_eq_some_iff] at h
    obtain ⟨r, hr, h⟩ := h
    obtain ⟨hB, hfol, hfit⟩ := hA.ana s f st.long st.jets st.hot r hr hI.1.1
    have hok1 : CacheOK ref r.2.1 r.2.2.1 st.hot st.cache :=
      ⟨fun b x hx => hC.stable st s f r b true x hI.2 hr hI.1.1 (hI.1.2.1 b x hx),
       fun b x hx => hC.stable st s f r b false x hI.2 hr hI.1.1 (hI.1.2.2 b x hx)⟩
    have hI1 : InvS lib ref (midSt st r) := ⟨hB, hok1⟩
    split at h
    · rename_i out hout
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2, h3, h4⟩ := hC.jetRoot st s f r out hI.2 hr hI.1.1 hout
      refine ⟨r.1, out, r.2.2.2, rfl, h1, h2, ?_, ?_⟩
      · rw [needOf_eqOn hC.toCompStateOn (fun b => hR.now _ b hI'') hI'' hI1]; exact h3
      · rw [needOf_eqOn hC.toCompStateOn (fun b => hR.now _ b hI'') hI'' hI1]; exact h4
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨c, st2⟩, hs, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hrd := hR.ana st s f r hI.2 hr
      obtain ⟨x, hx, rfl, hl, hj, hh, hok⟩ := compileStep_specOn hC.toCompStateOn hrd (fun e => by cases e) hok1 hs
      have hI2 : InvS lib ref st2 := ⟨by rw [hl]; exact hB, hok⟩
      obtain ⟨hbc, hn⟩ := hC.contract (midSt st r) r.1 true x hrd hB hx
      obtain ⟨hn1, hn2⟩ := hn rfl
      refine ⟨r.1, A.optimize x, r.2.2.2, rfl, hn1, hn2, ?_⟩
      have := hbc s hfit [s] (by simp)
      rw [needOf_eqOn hC.toCompStateOn (fun b => hR.now st2 b hI'') hI'' hI2, hl, hj, hh, ← hfol]
      exact this

/-- **`pokeS_invKept` over the reached states.** -/
theorem pokeS_invKeptOn (hC : CompHypOn A lib ref I Rd) (hR : ReachOn A I Rd) (hA : AnaHyp A lib) :
    ∀ st ov p st', (InvS lib ref st ∧ I st) → ¬ HotOvum ov → pokeS A st ov = some (p, st') →
      (InvS lib ref st' ∧ I st') := by
  intro st ov p st' hI hhot h
  have hS := pokeS_soundOn hC hR hA
  have hI' : I st' := hR.kept st ov p st' hI.2 hhot h
  cases ov with
  | full s f => exact (hS.full st s f p st' hI h).1
  | dire b m => exact (hS.dire st b m p st' hI h).1
  | jets q =>
    simp only [pokeS, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    exact ⟨⟨hI.1.1, hC.jets st q r hI.2 hhot hr hI.1.2⟩, hI'⟩
  | fast rs q =>
    simp only [pokeS, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    exact ⟨⟨hI.1.1, hC.fast st rs q r hI.2 hr hI.1.2⟩, hI'⟩

/-- **The invariant of the fourteenth assembly**: `InvSM` and `I`. -/
def InvSMI (lib : Lib) (ref : Ref M Map J H) (I : CSt M Map J H CR → Prop) (st : CSt M Map J H CR) : Prop :=
  InvSM lib ref st ∧ I st

/-- **`RootAnswers` at the `I` states.** -/
def RootAnswersOn (lib : Lib) (A : Arms M Map J H CR) (ref : Ref M Map J H) (I : CSt M Map J H CR → Prop) : Prop :=
  ∀ (st : CSt M Map J H CR) s f r, I st → InvS lib ref st → A.skaPoke s f st.long st.jets st.hot = some r →
    A.jetRoot r.2.2.1 st.hot r.1 = none → ∃ x, ref r.2.1 r.2.2.1 st.hot r.1 true = some x

/-- **`RootAnswers` gives `RootAnswersOn`.** -/
theorem rootAnswersOn_of {lib : Lib} {ref : Ref M Map J H} (I : CSt M Map J H CR → Prop)
    (h : RootAnswers lib A ref) : RootAnswersOn lib A ref I :=
  fun st s f r _ hS hk hj => h st s f r hS hk hj

end Gen

section P

open Compiler Pill Hoon

variable {M : Type → Type → Type} [Treap M] {Map : Type → Type} [HoonMap Map] {J H CR R : Type}

/-- **`fullAnswers_of_cgMP` over the reached states.** -/
theorem fullAnswers_of_cgMPOn (A : Arms M Map J H CR) {lib : Lib} {ref : Ref M Map J H}
    {I : CSt M Map J H CR → Prop} {Rd : CSt M Map J H CR → Bell → Prop} {env : Env R}
    {jet : H → J → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool} {bf : BEnv M → Nat}
    {regOf : J → R} {jetsOf : H → J → R → LongB M → LongB M → J} {newOf : R → Noun}
    (hC : CompHypOn A lib ref I Rd) (hR : ReachOn A I Rd)
    (hA : A.skaPoke = anaArmP env jet fold frozen (anaFuel env regOf) bf regOf jetsOf newOf)
    (hcg : CgHalts (M := M) lib env regOf)
    (hb : BakeEnds lib env jet fold frozen (anaFuel env regOf) bf regOf) (hr : RootAnswersOn lib A ref I) :
    FullAnswers (pokeS A) (InvSMI lib ref I) := by
  intro st s f1 f2 hI
  obtain ⟨r, hk⟩ := anaArmP_someN jetsOf newOf (anaEndsN_of_halts (anaHalts_of_cgHalts hcg)) hb
    (finalEnds_always lib env jet fold frozen _ regOf) st.hot hI.1.1.1 hI.1.2 (s := s) (f1 := f1) (f2 := f2)
    (j := st.jets)
  rw [← hA] at hk
  have hAna := anaHyp_of_armP A (lib := lib) hA
  obtain ⟨hB, -, -⟩ := hAna.ana s (C f1 f2) st.long st.jets st.hot r hk hI.1.1.1
  have hok1 : CacheOK ref r.2.1 r.2.2.1 st.hot st.cache :=
    ⟨fun b x hx => hC.stable st s (C f1 f2) r b true x hI.2 hk hI.1.1.1 (hI.1.1.2.1 b x hx),
     fun b x hx => hC.stable st s (C f1 f2) r b false x hI.2 hk hI.1.1.1 (hI.1.1.2.2 b x hx)⟩
  have hI1 : InvS lib ref (midSt st r) := ⟨hB, hok1⟩
  simp only [pokeS, hk, Option.bind_some]
  split
  · exact ⟨_, rfl⟩
  · rename_i hj
    obtain ⟨x, hx⟩ := hr st s (C f1 f2) r hI.2 hI.1.1 hk hj
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (hC.answers _ r.1 true x (hR.ana st s _ r hI.2 hk) hI1 hx)
    exact ⟨_, by rw [hp]; rfl⟩

/-- **The shapes of `contract`, `invKept`, `invStart`, `halting` on `InvSMI`** for
`liftPoke (enc fl) (pokeS A)` on track P's arm (`gap_of_armPM`, `halting_of_cgMP` over the
reached states): `invStart` needs `I emptySt`. -/
theorem gap_of_armPMOn (A : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)) {lib : Lib}
    {ref : Ref FinMap (TreapMap mugF) Noun Noun} {I : PSt → Prop} {Rd : PSt → Bell → Prop} {R : Type}
    {env : Env R} {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → R}
    {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}
    (hC : CompHypOn A lib ref I Rd) (hR : ReachOn A I Rd) (h0 : I emptySt)
    (hA : A.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf) (fl : Flags) :
    Sound lib (liftPoke (enc fl) (pokeS A)) (liftInv (enc fl) (InvSMI lib ref I)) ∧
    (∀ t ov p t', liftInv (enc fl) (InvSMI lib ref I) t → ¬ HotOvum ov →
      liftPoke (enc fl) (pokeS A) t ov = some (p, t') → liftInv (enc fl) (InvSMI lib ref I) t') ∧
    liftInv (enc fl) (InvSMI lib ref I) cor := by
  have hAna := anaHyp_of_armP A (lib := lib) hA
  have hS0 : Sound lib (pokeS A) (fun st => (InvS lib ref st ∧ I st) ∧ MemoNoCallees st.long.memo) :=
    sound_and (pokeS_soundOn hC hR hAna) (pokeS_memoP A hA)
  have e : (fun st : PSt => (InvS lib ref st ∧ I st) ∧ MemoNoCallees st.long.memo) = InvSMI lib ref I :=
    funext fun st => propext ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩, fun ⟨⟨a, c⟩, b⟩ => ⟨⟨a, b⟩, c⟩⟩
  have hS : Sound lib (pokeS A) (InvSMI lib ref I) := e ▸ hS0
  have hK : ∀ st ov p st', InvSMI lib ref I st → ¬ HotOvum ov → pokeS A st ov = some (p, st') →
      InvSMI lib ref I st' := fun st ov p st' hI hh hp =>
    have k := pokeS_invKeptOn hC hR hAna st ov p st' ⟨hI.1.1, hI.2⟩ hh hp
    ⟨⟨k.1, pokeS_memoP A hA st ov p st' hI.1.2 hp⟩, k.2⟩
  exact ⟨sound_lift (enc_inj fl) hS, invKept_lift (enc_inj fl) hK,
    ⟨emptySt, (cor_enc fl).symm, invSM_init lib ref jets0 (Noun.atom 0) (Noun.atom 0, Noun.atom 0), h0⟩⟩

/-- **`halting` on `InvSMI` for `enc fl`.** -/
theorem halting_of_cgMPOn (A : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)) {lib : Lib}
    {ref : Ref FinMap (TreapMap mugF) Noun Noun} {I : PSt → Prop} {Rd : PSt → Bell → Prop} {R : Type}
    {env : Env R} {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
    {bf : BEnv FinMap → Nat} {regOf : Noun → R}
    {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}
    (hC : CompHypOn A lib ref I Rd) (hR : ReachOn A I Rd)
    (hA : A.skaPoke = anaArmP env jet fold frozen (anaFuel env regOf) bf regOf jetsOf newOf)
    (hcg : CgHalts (M := FinMap) lib env regOf)
    (hb : BakeEnds lib env jet fold frozen (anaFuel env regOf) bf regOf) (hr : RootAnswersOn lib A ref I)
    (fl : Flags) :
    FullAnswers (liftPoke (enc fl) (pokeS A)) (liftInv (enc fl) (InvSMI lib ref I)) :=
  fullAnswers_lift (enc_inj fl) (fullAnswers_of_cgMPOn A hC hR hA hcg hb hr)

end P

end Glue
end SkaModel
end Formalization
