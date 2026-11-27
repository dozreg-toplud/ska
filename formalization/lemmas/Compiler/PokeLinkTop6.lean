import lemmas.Compiler.PokeLinkGood6
import lemmas.Compiler.PokeLinkEvalFin
import lemmas.Compiler.CompSccOfMissImg
import lemmas.Compiler.CompTarjanLeaf

/-!
# The top of the `%full` branch on `PGood6` (track P, README Gaps 23)

`pokeModel_fullReachP5` restated over `PGood6` = `PGood5` + `ColeDom`, with
the `ColeCoh` step `JetsOfCole6` (true of `+ska-cole-update`: it asks
`ColeDom` and that the new table keeps the old keys) in place of the old
`hJC` (false of it, `coleCohM_put_bad`).  The links are asked on `PGood6`
states only, so every hypothesis is at most as strong as before.

* **`loopLinkAt_good6`**: the SCC loop's link `LoopLinkAt` at `flagsOf` on a
  `PGood6` state with no leaf left (`evalFinAt`, track Q's
  `sccsLeafAt_of_tarjan`);
* `SpRestGood6`, `MonoLinkGood6`, `monoLinkGood6_of_gate`, `OtherKeeps6`;
* `pokeModel_fullGood6`, `pokeReachGood6` (with track Q's `SccOfIsK`);
* **`pokeModel_fullReachP6`**: `SccImage`, `SccOfKeeps`, `SccOfIs`,
  `TarjanExists` and `SccsLeafAt` are no longer assumed (track Q's
  `sccImage`, `sccOfKeeps_of`, `sccOfIsK_of`, `tarjanExists`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF SkaModel.PokeM FinMap

/-- **The SCC loop's link on a `PGood6` state, no leaf left.** -/
theorem loopLinkAt_good6 (root : Ident) (r1 r2 r3 r4 jRest callsN varsN seekN hotN : Noun)
    (gr : Callgraph FinMap × Noun)
    (r : Callgraph FinMap × FinMap Bell (FDatum FinMap) × Memo FinMap × FDatum FinMap × Noun)
    {Cls : Straight (TreapMap mugF) → Prop} {st : PSt} (hg : PGood6 Cls st) {E : BEnv FinMap} {n : Nat}
    {bg : FinMap Bell (VarEntry FinMap) × FinMap Bell (FinMap Bell Unit)} (vr : Noun)
    (hbg : bakeGraph E n = some bg) (hEv : E.vars = st.long.vars)
    (hN : ∀ b e, FinMap.get (addCode st.long.code (newCode st.long.code bg.1)) b = some e → NoAx0 e.nomm) :
    LoopLinkAt root r1 r2 r3 r4 jRest (codeNoun flagsOf st.long.code) callsN varsN seekN hotN gr r
      flagsOf st.long.code (newCode st.long.code bg.1) bg.1 vr :=
  loopLinkAt_good5E root r1 r2 r3 r4 jRest callsN varsN seekN hotN gr r hg.good5 vr hbg hEv hN
    (sccsLeafAt_of_tarjan _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)

section Links

variable (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
  (Cls : Straight (TreapMap mugF) → Prop)

/-- `SpRestGood` on `PGood6` states. -/
def SpRestGood6 (env : Env Noun) : Prop :=
  ∀ (st : PSt) s f₁ f₂ r1 r2 r3 r4 jRest key, PGood6 Cls st → st.jets = C r1 (C r2 (C r3 (C r4 jRest))) →
    keyRaw (enc fl st) = some key → SpRestAt fl Ar env st s (C f₁ f₂) r1 r2 r3 r4 jRest key

/-- `MonoLinkGood` on `PGood6` states. -/
def MonoLinkGood6 : Prop := ∀ (st : PSt) b sc, PGood6 Cls st → MonoLinkAt fl Ar st b sc

/-- **`MonoLinkGood6` from track K's gate**, asked on `PGood6` states only. -/
theorem monoLinkGood6_of_gate (hA : Ar.compileUnary = compileUnaryP fl)
    (hG : ∀ st b sc, PGood6 Cls st → ∃ (NM CA V COLE SC0 : Noun) (env : Comp.CallEnv) (inl : Noun → Option Nomm) (n : Nomm)
      (ht : Noun → Nat) (D : Bell → Prop), UnaryGateAt fl st b sc NM CA V COLE SC0 env inl n ht D) :
    MonoLinkGood6 fl Ar Cls := by
  intro st b sc hg
  obtain ⟨NM, CA, V, COLE, SC0, env, inl, n, ht, D, H⟩ := hG st b sc hg
  exact monoLinkAt_of fl Ar hA st b sc (unaryImageAt_of_gateD H) (monoMissAt_of fl st b sc)

/-- **The pokes other than `%full` keep `PGood6`** (pill: `%dire`, `%jets`,
`%fast`; checked by `invdump2.hoon`, `%cdom` included). -/
def OtherKeeps6 : Prop :=
  ∀ (st : PSt) ovo p c', PGood6 Cls st → pokeN (enc fl st) ovo = some (C p c') → ¬ Ska.Hot ovo →
    (∀ s f, ovo ≠ (Ovum.full s f).toNoun) → ∃ st', PGood6 Cls st' ∧ enc fl st' = c'

variable {R : Type} {envR : Env R}
  {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
  {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → R}
  {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}

/-- **`pokeModel` on every `%full` at a `PGood6` state.** -/
theorem pokeModel_fullGood6 (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP)
    (hA : Ar.skaPoke = anaArmP envR jet fold frozen fuel bf regOf jetsOf newOf)
    (hJA : Ar.jetRoot = jetRootP) (hR : SpRestGood6 fl Ar Cls env) (hC : SccLink fl Ar sccP)
    (hM : MonoLinkGood6 fl Ar Cls) (hO : OptLinkOn Cls Ar optP) (hK : SkaKeeps Ar) (hU : UnaryKeeps Ar Cls)
    (hSc : SccOfKeeps Ar) (hSI : SccOfIsK Ar) (hTE : TarjanExists) (hJC : JetsOfCole6 jetsOf)
    (hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none) (st : PSt) (hg : PGood6 Cls st) (s f : Noun) :
    pokeN (enc fl st) (Ovum.full s f).toNoun =
      (liftPoke (enc fl) (pokeS Ar) (enc fl st) (Ovum.full s f)).map fun r => C r.1.toNoun r.2 := by
  have hg2 := hg.good5.good4.good3.good2
  cases f with
  | atom a => rw [pokeN_full_atom, liftPoke_enc_fl]; simp [pokeS, hAt]
  | cell f₁ f₂ =>
    refine pokeN_fullAt4 fl Ar Cls hC hO st s f₁ f₂ ?_ (fun r e => ?_) (fun r q e e3 => ?_)
      (optInAt_of_good hK hU st s _ hg2.good)
    · obtain ⟨r1, r2, r3, r4, pd, ca, bk, hj, -⟩ := hg2.good.maps
      obtain ⟨key, hk, -, -⟩ := keyRaw_enc fl st hg2.good.jets.2
      exact skaLinkAt_of fl Ar env hhe hth hsoft hrf st s (C f₁ f₂) r1 r2 r3 r4 (C pd (C ca bk)) key hj hk
        (hR st s f₁ f₂ r1 r2 r3 r4 _ key hg hj hk)
    · obtain ⟨_, hj'⟩ := hK st s _ r hg2.good.maps hg2.good.jets e
      exact jetRootLinkG_of fl Ar hJA st s _ r e hj'
    · exact hM _ r.1 q.1 (good6_mid hA hK hSc hSI hTE hJC st s _ hg r e q e3)

/-- **Every core the pill reaches is an encoded `PGood6` state.** -/
theorem pokeReachGood6 (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP) (lib : Lib)
    (hA : Ar.skaPoke = anaArmP envR jet fold frozen fuel bf regOf jetsOf newOf)
    (hJA : Ar.jetRoot = jetRootP) (hR : SpRestGood6 fl Ar Cls env) (hC : SccLink fl Ar sccP)
    (hM : MonoLinkGood6 fl Ar Cls) (hO : OptLinkOn Cls Ar optP) (hK : SkaKeeps Ar) (hU : UnaryKeeps Ar Cls)
    (hSc : SccOfKeeps Ar) (hCK : UnaryCacheKeeps Ar Cls) (hSI : SccOfIsK Ar) (hUS : UnarySccsIs Ar)
    (hTE : TarjanExists) (hJC : JetsOfCole6 jetsOf)
    (hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none) (hX : OtherKeeps6 fl Cls) :
    ∀ cr, PokeReach cr → ∃ st, PGood6 Cls st ∧ enc fl st = cr := by
  intro cr h
  induction h with
  | start => exact ⟨emptySt, good6_empty Cls lib, (cor_enc fl).symm⟩
  | @poke c ovo p c' _ hp hh ih =>
    obtain ⟨st, hg, rfl⟩ := ih
    by_cases e : ∃ s f, ovo = (Ovum.full s f).toNoun
    · obtain ⟨s, f, rfl⟩ := e
      rw [pokeModel_fullGood6 fl Ar Cls env hhe hth hsoft hrf hA hJA hR hC hM hO hK hU hSc hSI hTE hJC hAt st hg s f,
        liftPoke_enc_fl] at hp
      cases e' : pokeS Ar st (Ovum.full s f) with
      | none => rw [e'] at hp; cases hp
      | some q =>
        rw [e'] at hp
        simp only [Option.map_some, Option.some.injEq, Noun.cell.injEq] at hp
        exact ⟨q.2, good6_full_step hA hK hU hSc hCK hSI hUS hTE hJC st s f q.1 q.2 hg e', hp.2⟩
    · exact hX st ovo p c' hg hp hh fun s f h => e ⟨s, f, h⟩

end Links

/-- **`pokeModel` on `%full` at every reachable core, over `PGood6`**, on
track P's route (`anaArmP`, `optimizeP`, `sccOfP`, `jetRootP`, `OptTotal`,
`compileUnaryP`).  Left, with owners: `SpRestGood6` (P: the glue of
`spRest_of_parts`, `BakeLinkAt`, `TailEndAt`; the loop is
`loopLinkAt_good6`, no leaf), `JetsOfGood jetsOf` and `JetsOfCole6 jetsOf`
(P: `+ska-cole-update`), the gate `UnaryGateAt` at `PGood6` states (K, its
fields `got`, `nomm`, `cole`, `envFrom`, `noRing`, `ana` owed by P),
`UnaryKeeps OptTotal` (D), `UnaryCacheKeeps`, `UnarySccsIs` (K / Q),
`OtherKeeps6` (P: `%dire`, `%jets`, `%fast`), the four `env` equations. -/
theorem pokeModel_fullReachP6 (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
    (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP) (lib : Lib)
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → Noun}
    {jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun} {newOf : Noun → Noun}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf)
    (hJA : Ar.jetRoot = jetRootP) (hOA : Ar.optimize = optimizeP) (hSA : Ar.sccOf = sccOfP)
    (hUA : Ar.compileUnary = compileUnaryP fl)
    (hR : SpRestGood6 fl Ar OptTotal env)
    (hG : ∀ st b sc, PGood6 OptTotal st → ∃ (NM CA V COLE SC0 : Noun) (env : Comp.CallEnv) (inl : Noun → Option Nomm)
      (n : Nomm) (ht : Noun → Nat) (D : Bell → Prop), UnaryGateAt fl st b sc NM CA V COLE SC0 env inl n ht D)
    (hJ : JetsOfGood jetsOf) (hJC : JetsOfCole6 jetsOf)
    (hU : UnaryKeeps Ar OptTotal) (hCK : UnaryCacheKeeps Ar OptTotal) (hUS : UnarySccsIs Ar)
    (hX : OtherKeeps6 fl OptTotal) :
    ∀ cr, CorIn cr → ∀ s f, pokeN cr (Ovum.full s f).toNoun =
      (liftPoke (enc fl) (pokeS Ar) cr (Ovum.full s f)).map fun r => C r.1.toNoun r.2 := by
  have hM := monoLinkGood6_of_gate fl Ar OptTotal hUA hG
  have hI : SccImage := sccImage
  have hSc : SccOfKeeps Ar := sccOfKeeps_of hSA
  have hSI : SccOfIsK Ar := sccOfIsK_of hSA
  have hTE : TarjanExists := tarjanExists
  have hK := skaKeeps_of_armP Ar hA hJ
  have hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none := fun s a L j h => by
    rw [hA]; exact anaArmP_atom env jet fold frozen fuel bf regOf jetsOf newOf s a L j h
  intro cr hc s f
  obtain ⟨st, hg, rfl⟩ := pokeReachGood6 fl Ar OptTotal env hhe hth hsoft hrf lib hA hJA hR (sccLink_of fl hSA hI)
    hM (optLinkOn_optimizeP hOA) hK hU hSc hCK hSI hUS hTE hJC hAt hX cr hc.2.2
  exact pokeModel_fullGood6 fl Ar OptTotal env hhe hth hsoft hrf hA hJA hR (sccLink_of fl hSA hI) hM
    (optLinkOn_optimizeP hOA) hK hU hSc hSI hTE hJC hAt st hg s f

end Compiler
end Formalization
