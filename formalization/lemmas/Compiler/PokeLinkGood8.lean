import lemmas.Compiler.PokeLinkTailEnd
import lemmas.Ska.AnnotSInv

/-!
# `PGood8`: `PGood7` with track Q's `InvK` (track P, README Gaps 23)

The reached states of the poke model carry the analysis invariant of track Q
(`InvK lib L`, `Ska/AnnotSInv.lean`), at every `lib`, of the `long` of the
model state `st : PSt` whose encoding is the core (`enc fl st = cr`; `enc`
is injective, `enc_inj`, so that state is the only one):

* `PGood8 Cls st := PGood7 Cls st ∧ ∀ lib, InvK lib st.long`;
* `good8_empty`; `invK_armP`: one `%full` keeps `InvK` (`skaPokeB_soundK`,
  on the root sock `[& s]` with `wf_root`, `normSock_yes`, and `f` a cell:
  the hypotheses `anaHyp_of_armP` already gives `skaPokeB_sound`);
  `pokeS_full_long`, **`good8_full_step`**;
* `OtherKeeps8`: `OtherKeeps7` with `st'.long = st.long` (the pill's
  `%dire`, `%jets` and `%fast` write `jets.long-ska`, `jets-hot` and the
  cache only, never `memo`, `code`, `calls`, `vars` or `seek`: the Hoon of
  `+poke`, `+ska-cole-settle`, `+ska-cole-restore`); `otherKeeps7_of_8`;
* **`pokeReachGood8`**: every reached core is the encoding of a `PGood8`
  state; `reach_good8`: every state encoding a reached core is `PGood8`;
* **`pokeModel_fullReachP12`**: `pokeModel` on `%full` at every reachable
  core, and `PGood8` (so `PGood6` and `InvK lib st.long` at every `lib`) of
  every state whose encoding is a reached core.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF SkaModel.PokeM SkaModel.AnnotSF FinMap

/-- **The invariant**: `PGood7`, and track Q's `InvK` of `long` at every
`lib`. -/
structure PGood8 (Cls : Straight (TreapMap mugF) → Prop) (st : PSt) : Prop where
  good7 : PGood7 Cls st
  invK : ∀ lib, InvK lib st.long

theorem invK_empty (lib : Lib) : InvK lib emptySt.long :=
  ⟨InvB.init lib, ⟨_, PokeInvK.init lib⟩, fun _ _ hb => by simp [emptySt, realOf, Treap.get_empty] at hb⟩

theorem good8_empty (Cls : Straight (TreapMap mugF) → Prop) (lib : Lib) : PGood8 Cls emptySt :=
  ⟨good7_empty Cls lib, invK_empty⟩

section Keep

variable {Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)} {Cls : Straight (TreapMap mugF) → Prop}

/-- The `long` after a `%full` the model answers is the analysis' `long`. -/
theorem pokeS_full_long {st : PSt} {s f : Noun} {pr : SkaModel.Prod (TreapMap mugF)} {st' : PSt}
    (h : pokeS Ar st (Ovum.full s f) = some (pr, st')) :
    ∃ r, Ar.skaPoke s f st.long st.jets st.hot = some r ∧ st'.long = r.2.1 := by
  simp only [pokeS] at h
  obtain ⟨r, e1, h⟩ := Option.bind_eq_some_iff.1 h
  refine ⟨r, e1, ?_⟩
  split at h
  · cases h; rfl
  · obtain ⟨p, hp, e⟩ := Option.map_eq_some_iff.1 h
    cases e
    unfold compileStep at hp
    obtain ⟨q, e3, hp⟩ := Option.bind_eq_some_iff.1 hp
    obtain ⟨p', hp', e⟩ := Option.map_eq_some_iff.1 hp
    cases e
    rfl

variable {R : Type} {env : Env R}
  {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
  {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → R}
  {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}

/-- **`anaArmP` keeps `InvK`** (`skaPokeB_soundK`; the root sock `[& s]` is
well formed, normal and not `%void`, as for `skaPokeB_sound` in
`anaHyp_of_armP`). -/
theorem invK_armP (hA : Ar.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf)
    {lib : Lib} {s f j hot : Noun} {L : LongB FinMap} {r : Bell × LongB FinMap × Noun × Noun}
    (h : Ar.skaPoke s f L j hot = some r) (hI : InvK lib L) : InvK lib r.2.1 := by
  rw [hA] at h
  cases f with
  | atom _ => simp [anaArmP] at h
  | cell f1 f2 =>
    simp only [anaArmP, Option.map_eq_some_iff] at h
    obtain ⟨⟨rb, L', reg'⟩, hk, rfl⟩ := h
    have hroot : (Sock.mk Cape.yes s, C f1 f2).1 ≠ Sock.void := Sock.noConfusion
    obtain ⟨h1, h2, h3, -⟩ :=
      skaPokeB_soundK (folTopK lib) env hI.1 hI.2.1 hI.2.2 (wf_root s) (normSock_yes s) hroot hk
    exact ⟨h1, h2, h3⟩

/-- **The model's `%full` keeps `PGood8`.** -/
theorem good8_full_step (hA : Ar.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf)
    (hK : SkaKeeps Ar) (hU : UnaryKeeps Ar Cls) (hO : SccOfKeeps Ar) (hC : UnaryCacheKeeps Ar Cls)
    (hSI : SccOfIsK Ar) (hUS : UnarySccsIs Ar) (hTE : TarjanExists) (hJC : JetsOfCole6 jetsOf)
    (hJS : JetsOfSets jetsOf)
    (st : PSt) (s f : Noun) (pr : SkaModel.Prod (TreapMap mugF)) (st' : PSt)
    (hg : PGood8 Cls st) (h : pokeS Ar st (Ovum.full s f) = some (pr, st')) : PGood8 Cls st' := by
  refine ⟨good7_full_step hA hK hU hO hC hSI hUS hTE hJC hJS st s f pr st' hg.good7 h, fun lib => ?_⟩
  obtain ⟨r, e1, hl⟩ := pokeS_full_long h
  rw [hl]
  exact invK_armP hA e1 (hg.invK lib)

end Keep

/-! ## The other pokes, and the reached states -/

section Links

variable (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
  (Cls : Straight (TreapMap mugF) → Prop)

/-- **The pokes other than `%full` keep `PGood7` and `long`** (P; the pill's
`%dire` writes the cache, `%jets` and `%fast` write `jets.long-ska`,
`jets-hot` and the cache, none the rest of `long-ska`). -/
def OtherKeeps8 : Prop :=
  ∀ (st : PSt) ovo p c', PGood7 Cls st → pokeN (enc fl st) ovo = some (C p c') → ¬ Ska.Hot ovo →
    (∀ s f, ovo ≠ (Ovum.full s f).toNoun) → ∃ st', PGood7 Cls st' ∧ st'.long = st.long ∧ enc fl st' = c'

theorem otherKeeps7_of_8 {fl : Flags} {Cls : Straight (TreapMap mugF) → Prop} (h : OtherKeeps8 fl Cls) :
    OtherKeeps7 fl Cls := fun st ovo p c' hg hp hh hf => by
  obtain ⟨st', h1, -, h3⟩ := h st ovo p c' hg hp hh hf
  exact ⟨st', h1, h3⟩

theorem otherGood8 {fl : Flags} {Cls : Straight (TreapMap mugF) → Prop} (h : OtherKeeps8 fl Cls) :
    ∀ (st : PSt) ovo p c', PGood8 Cls st → pokeN (enc fl st) ovo = some (C p c') → ¬ Ska.Hot ovo →
      (∀ s f, ovo ≠ (Ovum.full s f).toNoun) → ∃ st', PGood8 Cls st' ∧ enc fl st' = c' := by
  intro st ovo p c' hg hp hh hf
  obtain ⟨st', h1, h2, h3⟩ := h st ovo p c' hg.good7 hp hh hf
  exact ⟨st', ⟨h1, fun lib => h2 ▸ hg.invK lib⟩, h3⟩

variable {R : Type} {envR : Env R}
  {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
  {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → R}
  {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}

/-- **Every core the pill reaches is an encoded `PGood8` state.** -/
theorem pokeReachGood8 (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP) (lib : Lib)
    (hA : Ar.skaPoke = anaArmP envR jet fold frozen fuel bf regOf jetsOf newOf)
    (hJA : Ar.jetRoot = jetRootP) (hR : SpRestGood7 fl Ar Cls env) (hC : SccLink fl Ar sccP)
    (hM : MonoLinkGood6 fl Ar Cls) (hO : OptLinkOn Cls Ar optP) (hK : SkaKeeps Ar) (hU : UnaryKeeps Ar Cls)
    (hSc : SccOfKeeps Ar) (hCK : UnaryCacheKeeps Ar Cls) (hSI : SccOfIsK Ar) (hUS : UnarySccsIs Ar)
    (hTE : TarjanExists) (hJC : JetsOfCole6 jetsOf) (hJS : JetsOfSets jetsOf)
    (hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none) (hX : OtherKeeps8 fl Cls) :
    ∀ cr, PokeReach cr → ∃ st, PGood8 Cls st ∧ enc fl st = cr := by
  intro cr h
  induction h with
  | start => exact ⟨emptySt, good8_empty Cls lib, (cor_enc fl).symm⟩
  | @poke c ovo p c' _ hp hh ih =>
    obtain ⟨st, hg, rfl⟩ := ih
    by_cases e : ∃ s f, ovo = (Ovum.full s f).toNoun
    · obtain ⟨s, f, rfl⟩ := e
      rw [pokeModel_fullGood7 fl Ar Cls env hhe hth hsoft hrf hA hJA hR hC hM hO hK hU hSc hSI hTE hJC hAt st
        hg.good7 s f, liftPoke_enc_fl] at hp
      cases e' : pokeS Ar st (Ovum.full s f) with
      | none => rw [e'] at hp; cases hp
      | some q =>
        rw [e'] at hp
        simp only [Option.map_some, Option.some.injEq, Noun.cell.injEq] at hp
        exact ⟨q.2, good8_full_step hA hK hU hSc hCK hSI hUS hTE hJC hJS st s f q.1 q.2 hg e', hp.2⟩
    · exact otherGood8 hX st ovo p c' hg hp hh fun s f h => e ⟨s, f, h⟩

end Links

/-- **`pokeModel` on `%full` at every reachable core, and `PGood8` at every
reached state** (the top of `pokeModel_fullReachP11` with `OtherKeeps8`):
for every `cr` with `CorIn cr`, the pill's `%full` is the model's; and every
state `st` with `PokeReach (enc flagsOf st)` is `PGood8 OptTotal`, so
`PGood6 OptTotal st` and `InvK lib st.long` at every `lib`.  Left, with
owners: `SpLeavesGood8` (P: `BakeLinkAt`; `SrEndAt`), `AnaRegsGood`
(analysis owner), the gate at `PGood6` states (K), `UnaryKeeps OptTotal`
(D), `UnaryCacheKeeps`, `UnarySccsIs` (K / Q), `OtherKeeps8` (P), the four
`env` equations. -/
theorem pokeModel_fullReachP12 (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
    (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP) (lib : Lib)
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    {bf : BEnv FinMap → Nat}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen (anaFuel env regOfP) bf regOfP jetsOfP newOfP)
    (hJA : Ar.jetRoot = jetRootP) (hOA : Ar.optimize = optimizeP) (hSA : Ar.sccOf = sccOfP)
    (hUA : Ar.compileUnary = compileUnaryP flagsOf)
    (hL : SpLeavesGood8 OptTotal env jet fold frozen bf jetsOfP newOfP) (hRG : AnaRegsGood env)
    (hG : ∀ st b sc, PGood6 OptTotal st → ∃ (NM CA V COLE SC0 : Noun) (env : Comp.CallEnv) (inl : Noun → Option Nomm)
      (n : Nomm) (ht : Noun → Nat) (D : Bell → Prop), UnaryGateAt flagsOf st b sc NM CA V COLE SC0 env inl n ht D)
    (hU : UnaryKeeps Ar OptTotal) (hCK : UnaryCacheKeeps Ar OptTotal) (hUS : UnarySccsIs Ar)
    (hX : OtherKeeps8 flagsOf OptTotal) :
    (∀ cr, CorIn cr → ∀ s f, pokeN cr (Ovum.full s f).toNoun =
      (liftPoke (enc flagsOf) (pokeS Ar) cr (Ovum.full s f)).map fun r => C r.1.toNoun r.2) ∧
    ∀ st : PSt, PokeReach (enc flagsOf st) → PGood8 OptTotal st := by
  refine ⟨pokeModel_fullReachP11 Ar env hhe hth hsoft hrf lib hA hJA hOA hSA hUA hL hRG hG hU hCK hUS
    (otherKeeps7_of_8 hX), fun st hst => ?_⟩
  have hM := monoLinkGood6_of_gate flagsOf Ar OptTotal hUA hG
  have hK := skaKeeps_of_armP Ar hA jetsOfGood_P
  have hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none := fun s a L j h => by
    rw [hA]; exact anaArmP_atom env jet fold frozen _ bf regOfP jetsOfP newOfP s a L j h
  obtain ⟨st', hg, he⟩ := pokeReachGood8 flagsOf Ar OptTotal env hhe hth hsoft hrf lib hA hJA
    (spRestGood7_of_leaves8 Ar OptTotal env hA (fuelOK_anaFuel env regOfP) regOfP_shape hRG hL)
    (sccLink_of flagsOf hSA sccImage) hM (optLinkOn_optimizeP hOA) hK hU (sccOfKeeps_of hSA) hCK
    (sccOfIsK_of hSA) hUS tarjanExists jetsOfCole6_P jetsOfSets_P hAt hX _ hst
  rw [enc_inj flagsOf _ _ he] at hg
  exact hg

/-- **`InvK` at every reached state**, in the form track G uses: the state
whose encoding is a reached core satisfies `InvK lib` of its `long`. -/
theorem reach_invK (Cls : Straight (TreapMap mugF) → Prop)
    (h : ∀ st : PSt, PokeReach (enc flagsOf st) → PGood8 Cls st) (lib : Lib) :
    ∀ st : PSt, PokeReach (enc flagsOf st) → PGood6 Cls st ∧ InvK lib st.long :=
  fun st hst => ⟨(h st hst).good7.good6, (h st hst).invK lib⟩

end Compiler
end Formalization
