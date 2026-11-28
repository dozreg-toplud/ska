import lemmas.Compiler.PokeLinkHotJets

/-!
# The top over `PGood9`, with the leaves asked only where `jets-hot = ~` (track P)

The statement finding of the fourteenth session (`SpLeavesAt8` asks `SrEndAt`
at `jetsOfP st.hot`, the MAP `jets-hot`, where the pill passes its key set)
is vacuous where `jets-hot = ~`: the map and its key set are then the same
noun `~`.  Every reached state has `jets-hot = ~` (`PGood9`), so the leaves
need only be asked there:

* `SpRestGood9`, `SpLeavesGood9`: `SpRestGood7`, `SpLeavesGood8` asked at
  `PGood7` states with `st.hot = A 0`;
* `spLeavesAt7_of_8At` (the step of `spLeavesGood7_of_8` at one state),
  **`spRestGood9_of_leaves9`**;
* `pokeModel_fullGood9` (the proof of `pokeModel_fullGood7` with the leaf
  read at the state only), `pokeReachGood9R`;
* **`pokeModel_fullReachP14`**: the top of `pokeModel_fullReachP13` with
  `SpLeavesGood9` for `SpLeavesGood8`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF SkaModel.PokeM FinMap

section Links

variable (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
  (Cls : Straight (TreapMap mugF) → Prop)

/-- `SpRestGood7` at states with `jets-hot = ~`. -/
def SpRestGood9 (env : Env Noun) : Prop :=
  ∀ (st : PSt) s f₁ f₂ r1 r2 r3 r4 jRest key, PGood7 Cls st → st.hot = A 0 →
    st.jets = C r1 (C r2 (C r3 (C r4 jRest))) →
    keyRaw (enc fl st) = some key → SpRestAt fl Ar env st s (C f₁ f₂) r1 r2 r3 r4 jRest key

variable {R : Type} {envR : Env R}
  {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
  {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → R}
  {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}

/-- **`pokeModel` on every `%full` at a `PGood7` state with `jets-hot = ~`**
(the proof of `pokeModel_fullGood7`, the leaf read at the state only). -/
theorem pokeModel_fullGood9 (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP)
    (hA : Ar.skaPoke = anaArmP envR jet fold frozen fuel bf regOf jetsOf newOf)
    (hJA : Ar.jetRoot = jetRootP) (hR : SpRestGood9 fl Ar Cls env) (hC : SccLink fl Ar sccP)
    (hM : MonoLinkGood6 fl Ar Cls) (hO : OptLinkOn Cls Ar optP) (hK : SkaKeeps Ar) (hU : UnaryKeeps Ar Cls)
    (hSc : SccOfKeeps Ar) (hSI : SccOfIsK Ar) (hTE : TarjanExists) (hJC : JetsOfCole6 jetsOf)
    (hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none) (st : PSt) (hg : PGood7 Cls st) (hh : st.hot = A 0)
    (s f : Noun) :
    pokeN (enc fl st) (Ovum.full s f).toNoun =
      (liftPoke (enc fl) (pokeS Ar) (enc fl st) (Ovum.full s f)).map fun r => C r.1.toNoun r.2 := by
  have hg2 := hg.good6.good5.good4.good3.good2
  cases f with
  | atom a => rw [pokeN_full_atom, liftPoke_enc_fl]; simp [pokeS, hAt]
  | cell f₁ f₂ =>
    refine pokeN_fullAt4 fl Ar Cls hC hO st s f₁ f₂ ?_ (fun r e => ?_) (fun r q e e3 => ?_)
      (optInAt_of_good hK hU st s _ hg2.good)
    · obtain ⟨r1, r2, r3, r4, pd, ca, bk, hj, -⟩ := hg2.good.maps
      obtain ⟨key, hk, -, -⟩ := keyRaw_enc fl st hg2.good.jets.2
      exact skaLinkAt_of fl Ar env hhe hth hsoft hrf st s (C f₁ f₂) r1 r2 r3 r4 (C pd (C ca bk)) key hj hk
        (hR st s f₁ f₂ r1 r2 r3 r4 _ key hg hh hj hk)
    · obtain ⟨_, hj'⟩ := hK st s _ r hg2.good.maps hg2.good.jets e
      exact jetRootLinkG_of fl Ar hJA st s _ r e hj'
    · exact hM _ r.1 q.1 (good6_mid hA hK hSc hSI hTE hJC st s _ hg.good6 r e q e3)

/-- **Every core the pill reaches is an encoded `PGood9` state**, with the
leaf of `+ska-poke` asked only where `jets-hot = ~`. -/
theorem pokeReachGood9R (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP) (lib : Lib)
    (hA : Ar.skaPoke = anaArmP envR jet fold frozen fuel bf regOf jetsOf newOf)
    (hJA : Ar.jetRoot = jetRootP) (hR : SpRestGood9 fl Ar Cls env) (hC : SccLink fl Ar sccP)
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
      rw [pokeModel_fullGood9 fl Ar Cls env hhe hth hsoft hrf hA hJA hR hC hM hO hK hU hSc hSI hTE hJC hAt st
        hg.good8.good7 hg.hot s f, liftPoke_enc_fl] at hp
      cases e' : pokeS Ar st (Ovum.full s f) with
      | none => rw [e'] at hp; cases hp
      | some q =>
        rw [e'] at hp
        simp only [Option.map_some, Option.some.injEq, Noun.cell.injEq] at hp
        exact ⟨q.2, good9_full_step hA hK hU hSc hCK hSI hUS hTE hJC hJS st s f q.1 q.2 hg e', hp.2⟩
    · exact otherGood9 hX st ovo p c' hg hp hh fun s f h => e ⟨s, f, h⟩

end Links

/-! ## The leaves at `jets-hot = ~` -/

/-- `SpLeavesGood8` asked only at `PGood7` states with `jets-hot = ~`: there
`jetsOfP st.hot` and the pill's `~(key by jets-hot)` are both `~`. -/
def SpLeavesGood9 (Cls : Straight (TreapMap mugF) → Prop) (env : Env Noun)
    (jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool)
    (fold frozen : Bool) (bf : BEnv FinMap → Nat)
    (jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun) (newOf : Noun → Noun) : Prop :=
  ∀ (st : PSt) s f₁ f₂ r1 r2 r3 r4 jRest key, PGood7 Cls st → st.hot = A 0 →
    st.jets = C r1 (C r2 (C r3 (C r4 jRest))) → keyRaw (enc flagsOf st) = some key →
    SpLeavesAt8 env jet fold frozen bf jetsOf newOf st s (C f₁ f₂) r1 r2 r3 r4 jRest key

/-- The step of `spLeavesGood7_of_8` at one state. -/
theorem spLeavesAt7_of_8At {Cls : Straight (TreapMap mugF) → Prop} {env : Env Noun}
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    {bf : BEnv FinMap → Nat}
    {jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun} {newOf : Noun → Noun}
    (hRG : AnaRegsGood env) (st : PSt) (s f₁ f₂ r1 r2 r3 r4 jRest key : Noun) (hg : PGood7 Cls st)
    (hj : st.jets = C r1 (C r2 (C r3 (C r4 jRest))))
    (hL : SpLeavesAt8 env jet fold frozen bf jetsOf newOf st s (C f₁ f₂) r1 r2 r3 r4 jRest key) :
    SpLeavesAt7 env jet fold frozen bf jetsOf newOf st s (C f₁ f₂) r1 r2 r3 r4 jRest key := by
  intro n gr r hcg hsp
  obtain ⟨hB, hT⟩ := hL n gr r hcg hsp
  refine ⟨hB, fun hm bg hbg => ?_⟩
  have hnew0 : NewOK (C r1 (C r2 (C r3 (C r4 (A 0))))) := ⟨r1, r2, r3, r4, A 0, rfl, A 0, rfl⟩
  obtain ⟨-, ro, co, ba, ar, nw, hreg, nco, hnco⟩ := hRG _ _ _ _ r (regsMaps_start hg.good6 hj) hnew0 hsp
  obtain ⟨x1, x2, x3, x4, pd, ca, bk, hx, -, -, -, -, hpdm, -, -⟩ := hg.good6.good5.good4.good3.good2.good.maps
  rw [hj] at hx
  simp only [Noun.cell.injEq] at hx
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hx
  have hp : JugSets pd := ⟨hpdm, hg.pendSets _ _ _ _ _ _ _ (hj.trans rfl)⟩
  obtain ⟨pd', hpd⟩ := uniJuO_some hp (newCoresO_sets hnco)
  have hgr : gr.2 = r.2.2.2.2 := (skaPoke_regs hcg hsp).symm
  exact tailEndAt_of_end _ _ _ _ _ _ _ _ _ gr r flagsOf _ _ _ _ _ _ ro co ba ar nw pd (C ca bk) nco pd'
    (hgr.trans hreg) rfl hnco hp hpd (hT ro co ba ar nw pd (C ca bk) nco pd' hreg hm rfl hnco hpd bg hbg)

/-- **`SpRestGood9` at `flagsOf` from `SpLeavesGood9`.** -/
theorem spRestGood9_of_leaves9 (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
    (Cls : Straight (TreapMap mugF) → Prop) (env : Env Noun)
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → Noun}
    {jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun} {newOf : Noun → Noun}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf) (hF : FuelOK env regOf fuel)
    (hreg : ∀ r1 r2 r3 r4 jRest, regOf (C r1 (C r2 (C r3 (C r4 jRest)))) = C r1 (C r2 (C r3 (C r4 (A 0)))))
    (hRG : AnaRegsGood env)
    (hL : SpLeavesGood9 Cls env jet fold frozen bf jetsOf newOf) : SpRestGood9 flagsOf Ar Cls env :=
  fun st s f₁ f₂ r1 r2 r3 r4 jRest key hg hh hj hk =>
    have H := spLeavesAt7_of_8At hRG st s f₁ f₂ r1 r2 r3 r4 jRest key hg hj
      (hL st s f₁ f₂ r1 r2 r3 r4 jRest key hg hh hj hk)
    spRestAt_of_leaves Ar Cls env hA hF hreg st hg.good6 s f₁ f₂ r1 r2 r3 r4 jRest key hj
      fun n gr r hcg hsp =>
        ⟨(H n gr r hcg hsp).1,
          (H n gr r hcg hsp).2 (hRG _ _ _ _ r (regsMaps_start hg.good6 hj) ⟨r1, r2, r3, r4, A 0, rfl, A 0, rfl⟩ hsp).1⟩

/-- **`pokeModel` on `%full` at every reachable core, and `PGood9` at every
reached state, with the leaves asked only where `jets-hot = ~`**
(`pokeModel_fullReachP13` with `SpLeavesGood9`).  Left, with owners:
`SpLeavesGood9` (P: `BakeLinkAt`; `SrEndAt`, now at `jets-hot = ~`),
`AnaRegsGood` (analysis owner), the gate at `PGood6` states (K),
`UnaryKeeps OptTotal` (D), `UnaryCacheKeeps`, `UnarySccsIs` (K / Q),
`OtherKeeps9` (P: `otherKeeps9_of` from `JetsSettle9`, `JetsAtom9`,
`NonJets9`), the four `env` equations. -/
theorem pokeModel_fullReachP14 (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
    (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP) (lib : Lib)
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    {bf : BEnv FinMap → Nat}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen (anaFuel env regOfP) bf regOfP jetsOfP newOfP)
    (hJA : Ar.jetRoot = jetRootP) (hOA : Ar.optimize = optimizeP) (hSA : Ar.sccOf = sccOfP)
    (hUA : Ar.compileUnary = compileUnaryP flagsOf)
    (hL : SpLeavesGood9 OptTotal env jet fold frozen bf jetsOfP newOfP) (hRG : AnaRegsGood env)
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
  have hR := spRestGood9_of_leaves9 Ar OptTotal env hA (fuelOK_anaFuel env regOfP) regOfP_shape hRG hL
  have hReach := pokeReachGood9R flagsOf Ar OptTotal env hhe hth hsoft hrf lib hA hJA hR
    (sccLink_of flagsOf hSA sccImage) hM (optLinkOn_optimizeP hOA) hK hU (sccOfKeeps_of hSA) hCK
    (sccOfIsK_of hSA) hUS tarjanExists jetsOfCole6_P jetsOfSets_P hAt hX
  refine ⟨fun cr hc s f => ?_, fun st hst => ?_⟩
  · obtain ⟨st, hg, rfl⟩ := hReach cr hc.2.2
    exact pokeModel_fullGood9 flagsOf Ar OptTotal env hhe hth hsoft hrf hA hJA hR (sccLink_of flagsOf hSA sccImage)
      hM (optLinkOn_optimizeP hOA) hK hU (sccOfKeeps_of hSA) (sccOfIsK_of hSA) tarjanExists jetsOfCole6_P hAt st
      hg.good8.good7 hg.hot s f
  · obtain ⟨st', hg, he⟩ := hReach _ hst
    rw [enc_inj flagsOf _ _ he] at hg
    exact hg

end Compiler
end Formalization
