import lemmas.Compiler.PokeLinkGood8

/-!
# `PGood9`: `PGood8` with `jets-hot` empty (track P, README Gaps 23)

The only write of `jets-hot.state` in the pill's `+poke` is in the `%jets`
branch (`=/ hot (malt p.ovo)`, then `jets-hot.state hot`), and `Reach` (and
`PokeReach`) admit only a `%jets` whose list is not a cell (`¬ Hot`): the
validated ovum is then `[%jets ~]` (`+validate-ovum` crashes on `[%jets 5]`:
`tools/hoon/hotatom.hoon`), so `hot = ~`.  `%full`, `%dire` and `%fast` only
read it, and the pill starts from the bunt.  Checked on the real compiler:
`tools/hoon/hotempty.hoon`, 42 pokes (18 `%full`, 11 `[%jets ~]`, 7 `%dire`,
6 `%fast`): `jets-hot` is `~` after each, a `[%jets ~]` with `pend` empty
returns `[%drop ~]` and the state unchanged, every `[%jets ~]` drops nothing,
and no poke but `%full` changes `memo`, `code`, `calls`, `vars` or `seek`.

* `PGood9 Cls st := PGood8 Cls st ∧ st.hot = A 0`; `good9_empty`;
  `pokeS_full_hot` (the model's `%full` keeps `hot`), **`good9_full_step`**;
* `OtherKeeps9`: `OtherKeeps8` asked at states with `hot = ~`, and keeping it;
* **`pokeReachGood9`**, **`pokeModel_fullReachP13`** (the top of
  `pokeModel_fullReachP12` with `OtherKeeps9`);
* the exports for tracks K and G: **`reach_hotEmpty`** (`st.hot = A 0` at
  every reached state), `reach_ringVals` (every value of `call.cole` is a
  `Ring.toNoun`: the clause `JetsGood` of `PGood`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF SkaModel.PokeM SkaModel.AnnotSF FinMap

/-- **The invariant**: `PGood8`, and `jets-hot` is `~`. -/
structure PGood9 (Cls : Straight (TreapMap mugF) → Prop) (st : PSt) : Prop where
  good8 : PGood8 Cls st
  hot : st.hot = A 0

theorem good9_empty (Cls : Straight (TreapMap mugF) → Prop) (lib : Lib) : PGood9 Cls emptySt :=
  ⟨good8_empty Cls lib, rfl⟩

section Keep

variable {Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)} {Cls : Straight (TreapMap mugF) → Prop}

/-- The model's `%full` keeps `jets-hot`. -/
theorem pokeS_full_hot {st : PSt} {s f : Noun} {pr : SkaModel.Prod (TreapMap mugF)} {st' : PSt}
    (h : pokeS Ar st (Ovum.full s f) = some (pr, st')) : st'.hot = st.hot := by
  simp only [pokeS] at h
  obtain ⟨r, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · cases h; rfl
  · obtain ⟨p, hp, e⟩ := Option.map_eq_some_iff.1 h
    cases e
    unfold compileStep at hp
    obtain ⟨q, -, hp⟩ := Option.bind_eq_some_iff.1 hp
    obtain ⟨p', -, e⟩ := Option.map_eq_some_iff.1 hp
    cases e
    rfl

variable {R : Type} {env : Env R}
  {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
  {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → R}
  {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}

/-- **The model's `%full` keeps `PGood9`.** -/
theorem good9_full_step (hA : Ar.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf)
    (hK : SkaKeeps Ar) (hU : UnaryKeeps Ar Cls) (hO : SccOfKeeps Ar) (hC : UnaryCacheKeeps Ar Cls)
    (hSI : SccOfIsK Ar) (hUS : UnarySccsIs Ar) (hTE : TarjanExists) (hJC : JetsOfCole6 jetsOf)
    (hJS : JetsOfSets jetsOf)
    (st : PSt) (s f : Noun) (pr : SkaModel.Prod (TreapMap mugF)) (st' : PSt)
    (hg : PGood9 Cls st) (h : pokeS Ar st (Ovum.full s f) = some (pr, st')) : PGood9 Cls st' :=
  ⟨good8_full_step hA hK hU hO hC hSI hUS hTE hJC hJS st s f pr st' hg.good8 h,
    (pokeS_full_hot h).trans hg.hot⟩

end Keep

/-! ## The other pokes, and the reached states -/

section Links

variable (fl : Flags) (Cls : Straight (TreapMap mugF) → Prop)

/-- **The pokes other than `%full` keep `PGood7`, `long` and `jets-hot = ~`**,
asked at states with `jets-hot = ~` (P; the pill's `%dire` writes the cache,
`[%jets ~]` and `%fast` write `jets.long-ska` and the cache, `[%jets ~]`
writes `jets-hot` with `(malt ~) = ~`). -/
def OtherKeeps9 : Prop :=
  ∀ (st : PSt) ovo p c', PGood7 Cls st → st.hot = A 0 → pokeN (enc fl st) ovo = some (C p c') →
    ¬ Ska.Hot ovo → (∀ s f, ovo ≠ (Ovum.full s f).toNoun) →
    ∃ st', PGood7 Cls st' ∧ st'.long = st.long ∧ st'.hot = A 0 ∧ enc fl st' = c'

theorem otherGood9 {fl : Flags} {Cls : Straight (TreapMap mugF) → Prop} (h : OtherKeeps9 fl Cls) :
    ∀ (st : PSt) ovo p c', PGood9 Cls st → pokeN (enc fl st) ovo = some (C p c') → ¬ Ska.Hot ovo →
      (∀ s f, ovo ≠ (Ovum.full s f).toNoun) → ∃ st', PGood9 Cls st' ∧ enc fl st' = c' := by
  intro st ovo p c' hg hp hh hf
  obtain ⟨st', h1, h2, h3, h4⟩ := h st ovo p c' hg.good8.good7 hg.hot hp hh hf
  exact ⟨st', ⟨⟨h1, fun lib => h2 ▸ hg.good8.invK lib⟩, h3⟩, h4⟩

variable (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
variable {R : Type} {envR : Env R}
  {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
  {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → R}
  {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}

/-- **Every core the pill reaches is an encoded `PGood9` state.** -/
theorem pokeReachGood9 (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP) (lib : Lib)
    (hA : Ar.skaPoke = anaArmP envR jet fold frozen fuel bf regOf jetsOf newOf)
    (hJA : Ar.jetRoot = jetRootP) (hR : SpRestGood7 fl Ar Cls env) (hC : SccLink fl Ar sccP)
    (hM : MonoLinkGood6 fl Ar Cls) (hO : OptLinkOn Cls Ar optP) (hK : SkaKeeps Ar) (hU : UnaryKeeps Ar Cls)
    (hSc : SccOfKeeps Ar) (hCK : UnaryCacheKeeps Ar Cls) (hSI : SccOfIsK Ar) (hUS : UnarySccsIs Ar)
    (hTE : TarjanExists) (hJC : JetsOfCole6 jetsOf) (hJS : JetsOfSets jetsOf)
    (hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none) (hX : OtherKeeps9 fl Cls) :
    ∀ cr, PokeReach cr → ∃ st, PGood9 Cls st ∧ enc fl st = cr := by
  intro cr h
  induction h with
  | start => exact ⟨emptySt, good9_empty Cls lib, (cor_enc fl).symm⟩
  | @poke c ovo p c' _ hp hh ih =>
    obtain ⟨st, hg, rfl⟩ := ih
    by_cases e : ∃ s f, ovo = (Ovum.full s f).toNoun
    · obtain ⟨s, f, rfl⟩ := e
      rw [pokeModel_fullGood7 fl Ar Cls env hhe hth hsoft hrf hA hJA hR hC hM hO hK hU hSc hSI hTE hJC hAt st
        hg.good8.good7 s f, liftPoke_enc_fl] at hp
      cases e' : pokeS Ar st (Ovum.full s f) with
      | none => rw [e'] at hp; cases hp
      | some q =>
        rw [e'] at hp
        simp only [Option.map_some, Option.some.injEq, Noun.cell.injEq] at hp
        exact ⟨q.2, good9_full_step hA hK hU hSc hCK hSI hUS hTE hJC hJS st s f q.1 q.2 hg e', hp.2⟩
    · exact otherGood9 hX st ovo p c' hg hp hh fun s f h => e ⟨s, f, h⟩

end Links

/-- **`pokeModel` on `%full` at every reachable core, and `PGood9` at every
reached state** (`pokeModel_fullReachP12` with `OtherKeeps9`): for every
`cr` with `CorIn cr`, the pill's `%full` is the model's; and every state
`st` with `PokeReach (enc flagsOf st)` is `PGood9 OptTotal`: `PGood6`,
`InvK lib st.long` at every `lib`, and `st.hot = A 0`.  Left, with owners:
`SpLeavesGood8` (P: `BakeLinkAt`; `SrEndAt`), `AnaRegsGood` (analysis
owner), the gate at `PGood6` states (K), `UnaryKeeps OptTotal` (D),
`UnaryCacheKeeps`, `UnarySccsIs` (K / Q), `OtherKeeps9` (P), the four `env`
equations. -/
theorem pokeModel_fullReachP13 (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
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
    (hX : OtherKeeps9 flagsOf OptTotal) :
    (∀ cr, CorIn cr → ∀ s f, pokeN cr (Ovum.full s f).toNoun =
      (liftPoke (enc flagsOf) (pokeS Ar) cr (Ovum.full s f)).map fun r => C r.1.toNoun r.2) ∧
    ∀ st : PSt, PokeReach (enc flagsOf st) → PGood9 OptTotal st := by
  have hM := monoLinkGood6_of_gate flagsOf Ar OptTotal hUA hG
  have hK := skaKeeps_of_armP Ar hA jetsOfGood_P
  have hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none := fun s a L j h => by
    rw [hA]; exact anaArmP_atom env jet fold frozen _ bf regOfP jetsOfP newOfP s a L j h
  have hR := spRestGood7_of_leaves8 Ar OptTotal env hA (fuelOK_anaFuel env regOfP) regOfP_shape hRG hL
  have hReach := pokeReachGood9 flagsOf OptTotal Ar env hhe hth hsoft hrf lib hA hJA hR
    (sccLink_of flagsOf hSA sccImage) hM (optLinkOn_optimizeP hOA) hK hU (sccOfKeeps_of hSA) hCK
    (sccOfIsK_of hSA) hUS tarjanExists jetsOfCole6_P jetsOfSets_P hAt hX
  refine ⟨fun cr hc s f => ?_, fun st hst => ?_⟩
  · obtain ⟨st, hg, rfl⟩ := hReach cr hc.2.2
    exact pokeModel_fullGood7 flagsOf Ar OptTotal env hhe hth hsoft hrf hA hJA hR (sccLink_of flagsOf hSA sccImage)
      hM (optLinkOn_optimizeP hOA) hK hU (sccOfKeeps_of hSA) (sccOfIsK_of hSA) tarjanExists jetsOfCole6_P hAt st
      hg.good8.good7 s f
  · obtain ⟨st', hg, he⟩ := hReach _ hst
    rw [enc_inj flagsOf _ _ he] at hg
    exact hg

/-! ## The exports -/

/-- **`jets-hot` is `~` at every reached state** (for tracks K and G): the
state whose encoding is a reached core has `hot = A 0`, so the map
`jets-hot`, its key set `~(key by jets-hot)` and every `~(get by jets-hot)`
answer are those of `~`. -/
theorem reach_hotEmpty (Cls : Straight (TreapMap mugF) → Prop)
    (h : ∀ st : PSt, PokeReach (enc flagsOf st) → PGood9 Cls st) :
    ∀ st : PSt, PokeReach (enc flagsOf st) → st.hot = A 0 :=
  fun st hst => (h st hst).hot

/-- **Every value of `call.cole` is a ring noun** at every reached state
(`JetsGood`, clause `jets` of `PGood`: `slot? 126` of the jets noun is
`call.cole`, a map whose values are `Ring.toNoun`s). -/
theorem reach_ringVals (Cls : Straight (TreapMap mugF) → Prop)
    (h : ∀ st : PSt, PokeReach (enc flagsOf st) → PGood9 Cls st) :
    ∀ st : PSt, PokeReach (enc flagsOf st) → ∃ cm, slot? 126 st.jets = some cm ∧ IsMap mugF cm ∧
      ∀ k v, Get cm k v → ∃ n : Ring, v = n.toNoun :=
  fun st hst => (h st hst).good8.good7.good6.good5.good4.good3.good2.good.jets.1

end Compiler
end Formalization
