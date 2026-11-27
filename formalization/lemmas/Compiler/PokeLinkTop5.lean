import lemmas.Compiler.PokeLinkGood5
import lemmas.Compiler.CompMonoLinkDec

/-!
# The top of the `%full` branch on `PGood5` (track P, README Gaps 23)

`pokeModel_fullReachP3` restated with the links asked on `PGood5` states:

* `good5_mid`: `PGood5` at the state `+compiled-mono` runs on;
* `MonoLinkGood5`, **`monoLinkGood5_of_gate`**: track K's `monoLinkGood3_of_gate`
  on `PGood5` states, so `UnaryGateAt` is asked only there; its field
  `heights` is `heights_good5` (from `htRank_of`), its fields `sccs`,
  `sccsGood`, `jug` are `pgoodK_sccs`, `pgoodK_calls`;
* `loopLinkAt_good5`: the SCC loop's leaf `LoopLinkAt` at `flagsOf` on a
  `PGood5` state from `EvalFinAt` and `SccsLeafAt` alone (`LoopTotal` is
  `loopTotal_of`, the `%10`s from `InvB`);
* `SpRestGood5`, `OtherKeeps5`, `pokeModel_fullGood5`, `pokeReachGood5`,
  **`pokeModel_fullReachP5`**.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF SkaModel.PokeM FinMap

section Mid

variable {Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)} {Cls : Straight (TreapMap mugF) → Prop}

/-- **`PGood5` at the state `+compiled-mono` runs on.** -/
theorem good5_mid {R : Type} {env : Env R}
    {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → R}
    {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf)
    (hK : SkaKeeps Ar) (hO : SccOfKeeps Ar) (hSI : SccOfIs Ar) (hTE : TarjanExists)
    (hJC : ∀ hot j reg L L', ColeCoh j → ColeCoh (jetsOf hot j reg L L'))
    (st : PSt) (s f : Noun) (hg : PGood5 Cls st) (r : Bell × LongB FinMap × Noun × Noun)
    (e1 : Ar.skaPoke s f st.long st.jets st.hot = some r)
    (q : FinMap Bell Unit × FinMap Bell (FinMap Bell Unit)) (e3 : Ar.sccOf r.1 r.2.1 st.cache.sccs = some q) :
    PGood5 Cls { st with long := r.2.1, jets := r.2.2.1, cache := { st.cache with sccs := q.2 } } := by
  have hg3 := good3_mid hK (skaCodeKeeps_of_armP Ar hA) hO st s f hg.good4.good3 r e1 q e3
  have e1' := e1
  rw [hA] at e1'
  obtain ⟨E, n, bg, reg', hbg, hEv, hcode, hjets⟩ := anaArmP_bake e1'
  obtain ⟨lib, hInv⟩ := hg.invB
  have hInv' : InvB lib r.2.1 := ((anaHyp_of_armP (lib := lib) Ar hA).ana s f st.long st.jets st.hot r e1 hInv).1
  have hc := hg.good4.good3.good2.closed
  have hv : VarsKeys E.vars st.long.code := hEv ▸ hg.good4.good3.vars
  have hi := hg.good4.info
  obtain ⟨F, hF, hFt⟩ := hg.good4.flags
  obtain ⟨L, hL⟩ := hTE (newCode st.long.code bg.1)
  obtain ⟨G, hG⟩ := loopTotal_poke hc hv hi hbg hFt hInv' hcode L hL
  obtain ⟨hi', hG1, hG2⟩ := flags_poke hc hv hi hbg hL hF hFt hG
  have hc' := (addCode_closed hc hv hbg).1
  have hsc := sccsIs_addCode (addsTo_addCode st.long.code bg.1) hc hg.sccsIs hg.good4.good3.good2.cache.sccs
  rw [← hcode] at hi' hG1 hG2 hc' hsc
  exact ⟨⟨hg3, hi', ⟨G, hG1, hG2⟩⟩, ⟨lib, hInv'⟩, hSI _ _ _ q hc' hsc e3,
    by show ColeCoh r.2.2.1; rw [hjets]; exact hJC _ _ _ _ _ hg.cole⟩

end Mid

/-! ## What `PGood5` gives the other tracks' leaves -/

/-- **The field `heights` of track K's `UnaryGateAt`** (and `HtRank`) at a
`PGood5` state. -/
theorem heights_good5 {Cls : Straight (TreapMap mugF) → Prop} {st : PSt} (hg : PGood5 Cls st) :
    ∃ ht, HtRank (sccsNoun st.cache.sccs) (callsNoun st.long) ht ∧ HtScc (sccsNoun st.cache.sccs) ht :=
  htRank_of hg.good4.good3.good2.closed hg.sccsIs

/-- **The SCC loop's leaf on a `PGood5` state** from `EvalFinAt` and
`SccsLeafAt`: `LoopTotal` is discharged, given that the new table has no
`%10` at axis `0` (`invB_noAx0` of the poke's `InvB`). -/
theorem loopLinkAt_good5 (hE : EvalFinAt) (root : Ident) (r1 r2 r3 r4 jRest callsN varsN seekN hotN : Noun)
    (gr : Callgraph FinMap × Noun)
    (r : Callgraph FinMap × FinMap Bell (FDatum FinMap) × Memo FinMap × FDatum FinMap × Noun)
    {Cls : Straight (TreapMap mugF) → Prop} {st : PSt} (hg : PGood5 Cls st) {E : BEnv FinMap} {n : Nat}
    {bg : FinMap Bell (VarEntry FinMap) × FinMap Bell (FinMap Bell Unit)} (vr : Noun)
    (hbg : bakeGraph E n = some bg) (hEv : E.vars = st.long.vars)
    (hN : ∀ b e, FinMap.get (addCode st.long.code (newCode st.long.code bg.1)) b = some e → NoAx0 e.nomm)
    (hS : SccsLeafAt root r1 r2 r3 r4 jRest (codeNoun flagsOf st.long.code) callsN varsN seekN hotN gr r
      (newCode st.long.code bg.1) bg.1 vr) :
    LoopLinkAt root r1 r2 r3 r4 jRest (codeNoun flagsOf st.long.code) callsN varsN seekN hotN gr r
      flagsOf st.long.code (newCode st.long.code bg.1) bg.1 vr := by
  have hc := hg.good4.good3.good2.closed
  have hv : VarsKeys E.vars st.long.code := hEv ▸ hg.good4.good3.vars
  obtain ⟨F, hF, hFt⟩ := hg.good4.flags
  exact loopLinkAt_flagsOfT hE root r1 r2 r3 r4 jRest callsN varsN seekN hotN gr r vr hc hv hg.good4.info hbg hF hFt hS
    (loopTotal_of (addsTo_addCode _ _) (addCode_closed hc hv hbg).1 (infoCalls_addCode hg.good4.info hbg) hN hFt)

/-- **No `%10` at axis `0` in the table of a poke** whose bake the model
finishes (`skaPokeB_sound`). -/
theorem noAx0_poke {R : Type} {env : Env R}
    {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → R}
    {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}
    {Cls : Straight (TreapMap mugF) → Prop} {st : PSt} (hg : PGood5 Cls st) {s f : Noun}
    {r : Bell × LongB FinMap × Noun × Noun}
    (e1 : anaArmP env jet fold frozen fuel bf regOf jetsOf newOf s f st.long st.jets st.hot = some r) :
    ∀ b e, FinMap.get r.2.1.code b = some e → NoAx0 e.nomm := by
  obtain ⟨lib, hInv⟩ := hg.invB
  cases f with
  | atom _ => simp [anaArmP] at e1
  | cell f1 f2 =>
    simp only [anaArmP, Option.map_eq_some_iff] at e1
    obtain ⟨⟨rb, L', reg'⟩, hk, rfl⟩ := e1
    have hroot : (Sock.mk Cape.yes s, C f1 f2).1 ≠ Sock.void := Sock.noConfusion
    exact invB_noAx0 (skaPokeB_sound env hInv (wf_root s) (normSock_yes s) hroot hk).1

/-! ## The links on `PGood5` states -/

section Links

variable (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
  (Cls : Straight (TreapMap mugF) → Prop)

/-- `SpRestGood` on `PGood5` states. -/
def SpRestGood5 (env : Env Noun) : Prop :=
  ∀ (st : PSt) s f₁ f₂ r1 r2 r3 r4 jRest key, PGood5 Cls st → st.jets = C r1 (C r2 (C r3 (C r4 jRest))) →
    keyRaw (enc fl st) = some key → SpRestAt fl Ar env st s (C f₁ f₂) r1 r2 r3 r4 jRest key

/-- `MonoLinkGood` on `PGood5` states. -/
def MonoLinkGood5 : Prop := ∀ (st : PSt) b sc, PGood5 Cls st → MonoLinkAt fl Ar st b sc

/-- **`MonoLinkGood5` from track K's gate**, asked on `PGood5` states only
(`monoLinkGood3_of_gate` restated). -/
theorem monoLinkGood5_of_gate (hA : Ar.compileUnary = compileUnaryP fl)
    (hG : ∀ st b sc, PGood5 Cls st → ∃ (NM CA V COLE SC0 : Noun) (env : Comp.CallEnv) (inl : Noun → Option Nomm) (n : Nomm)
      (ht : Noun → Nat) (D : Bell → Prop), UnaryGateAt fl st b sc NM CA V COLE SC0 env inl n ht D) :
    MonoLinkGood5 fl Ar Cls := by
  intro st b sc hg
  obtain ⟨NM, CA, V, COLE, SC0, env, inl, n, ht, D, H⟩ := hG st b sc hg
  exact monoLinkAt_of fl Ar hA st b sc (unaryImageAt_of_gateD H) (monoMissAt_of fl st b sc)

/-- **The pokes other than `%full` keep `PGood5`** (pill: `%dire`, `%jets`,
`%fast`; checked by `invdump2.hoon`). -/
def OtherKeeps5 : Prop :=
  ∀ (st : PSt) ovo p c', PGood5 Cls st → pokeN (enc fl st) ovo = some (C p c') → ¬ Ska.Hot ovo →
    (∀ s f, ovo ≠ (Ovum.full s f).toNoun) → ∃ st', PGood5 Cls st' ∧ enc fl st' = c'

variable {R : Type} {envR : Env R}
  {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
  {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → R}
  {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}

/-- **`pokeModel` on every `%full` at a `PGood5` state.** -/
theorem pokeModel_fullGood5 (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP)
    (hA : Ar.skaPoke = anaArmP envR jet fold frozen fuel bf regOf jetsOf newOf)
    (hJA : Ar.jetRoot = jetRootP) (hR : SpRestGood5 fl Ar Cls env) (hC : SccLink fl Ar sccP)
    (hM : MonoLinkGood5 fl Ar Cls) (hO : OptLinkOn Cls Ar optP) (hK : SkaKeeps Ar) (hU : UnaryKeeps Ar Cls)
    (hSc : SccOfKeeps Ar) (hSI : SccOfIs Ar) (hTE : TarjanExists)
    (hJC : ∀ hot j reg L L', ColeCoh j → ColeCoh (jetsOf hot j reg L L'))
    (hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none) (st : PSt) (hg : PGood5 Cls st) (s f : Noun) :
    pokeN (enc fl st) (Ovum.full s f).toNoun =
      (liftPoke (enc fl) (pokeS Ar) (enc fl st) (Ovum.full s f)).map fun r => C r.1.toNoun r.2 := by
  cases f with
  | atom a => rw [pokeN_full_atom, liftPoke_enc_fl]; simp [pokeS, hAt]
  | cell f₁ f₂ =>
    refine pokeN_fullAt4 fl Ar Cls hC hO st s f₁ f₂ ?_ (fun r e => ?_) (fun r q e e3 => ?_)
      (optInAt_of_good hK hU st s _ hg.good4.good3.good2.good)
    · obtain ⟨r1, r2, r3, r4, pd, ca, bk, hj, -⟩ := hg.good4.good3.good2.good.maps
      obtain ⟨key, hk, -, -⟩ := keyRaw_enc fl st hg.good4.good3.good2.good.jets.2
      exact skaLinkAt_of fl Ar env hhe hth hsoft hrf st s (C f₁ f₂) r1 r2 r3 r4 (C pd (C ca bk)) key hj hk
        (hR st s f₁ f₂ r1 r2 r3 r4 _ key hg hj hk)
    · obtain ⟨_, hj'⟩ := hK st s _ r hg.good4.good3.good2.good.maps hg.good4.good3.good2.good.jets e
      exact jetRootLinkG_of fl Ar hJA st s _ r e hj'
    · exact hM _ r.1 q.1 (good5_mid hA hK hSc hSI hTE hJC st s _ hg r e q e3)

/-- **Every core the pill reaches is an encoded `PGood5` state.** -/
theorem pokeReachGood5 (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP) (lib : Lib)
    (hA : Ar.skaPoke = anaArmP envR jet fold frozen fuel bf regOf jetsOf newOf)
    (hJA : Ar.jetRoot = jetRootP) (hR : SpRestGood5 fl Ar Cls env) (hC : SccLink fl Ar sccP)
    (hM : MonoLinkGood5 fl Ar Cls) (hO : OptLinkOn Cls Ar optP) (hK : SkaKeeps Ar) (hU : UnaryKeeps Ar Cls)
    (hSc : SccOfKeeps Ar) (hCK : UnaryCacheKeeps Ar Cls) (hSI : SccOfIs Ar) (hUS : UnarySccsIs Ar)
    (hTE : TarjanExists) (hJC : ∀ hot j reg L L', ColeCoh j → ColeCoh (jetsOf hot j reg L L'))
    (hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none) (hX : OtherKeeps5 fl Cls) :
    ∀ cr, PokeReach cr → ∃ st, PGood5 Cls st ∧ enc fl st = cr := by
  intro cr h
  induction h with
  | start => exact ⟨emptySt, good5_empty Cls lib, (cor_enc fl).symm⟩
  | @poke c ovo p c' _ hp hh ih =>
    obtain ⟨st, hg, rfl⟩ := ih
    by_cases e : ∃ s f, ovo = (Ovum.full s f).toNoun
    · obtain ⟨s, f, rfl⟩ := e
      rw [pokeModel_fullGood5 fl Ar Cls env hhe hth hsoft hrf hA hJA hR hC hM hO hK hU hSc hSI hTE hJC hAt st hg s f,
        liftPoke_enc_fl] at hp
      cases e' : pokeS Ar st (Ovum.full s f) with
      | none => rw [e'] at hp; cases hp
      | some q =>
        rw [e'] at hp
        simp only [Option.map_some, Option.some.injEq, Noun.cell.injEq] at hp
        exact ⟨q.2, good5_full_step hA hK hU hSc hCK hSI hUS hTE hJC st s f q.1 q.2 hg e', hp.2⟩
    · exact hX st ovo p c' hg hp hh fun s f h => e ⟨s, f, h⟩

end Links

/-- **`pokeModel` on `%full` at every reachable core, over `PGood5`**, on
track P's route (`anaArmP`, `optimizeP`, `sccOfP`, `jetRootP`, `OptTotal`,
`compileUnaryP`), with `MonoLinkGood` from track K's gate.  Left, with
owners: `SpRestGood5` (P: `spRest`, whose loop part is `loopLinkAt_good5`
from `EvalFinAt` (P) and `SccsLeafAt` (Q)), `SccImage` (P), `SccOfKeeps`,
`SccOfIs` (P: `+scc-of`), `TarjanExists` (P), `JetsOfGood jetsOf` and the
`ColeCoh` step (P: `+ska-cole-update`), the gate `UnaryGateAt` at `PGood5`
states (K, with its fields owed by P, I, A, C, J), `UnaryKeeps OptTotal` (D),
`UnaryCacheKeeps`, `UnarySccsIs` (K), `OtherKeeps5` (P: `%dire`, `%jets`,
`%fast`), the four `env` equations. -/
theorem pokeModel_fullReachP5 (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
    (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP) (lib : Lib)
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → Noun}
    {jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun} {newOf : Noun → Noun}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf)
    (hJA : Ar.jetRoot = jetRootP) (hOA : Ar.optimize = optimizeP) (hSA : Ar.sccOf = sccOfP)
    (hUA : Ar.compileUnary = compileUnaryP fl)
    (hR : SpRestGood5 fl Ar OptTotal env) (hI : SccImage) (hSc : SccOfKeeps Ar) (hSI : SccOfIs Ar)
    (hTE : TarjanExists)
    (hG : ∀ st b sc, PGood5 OptTotal st → ∃ (NM CA V COLE SC0 : Noun) (env : Comp.CallEnv) (inl : Noun → Option Nomm)
      (n : Nomm) (ht : Noun → Nat) (D : Bell → Prop), UnaryGateAt fl st b sc NM CA V COLE SC0 env inl n ht D)
    (hJ : JetsOfGood jetsOf) (hJC : ∀ hot j reg L L', ColeCoh j → ColeCoh (jetsOf hot j reg L L'))
    (hU : UnaryKeeps Ar OptTotal) (hCK : UnaryCacheKeeps Ar OptTotal) (hUS : UnarySccsIs Ar)
    (hX : OtherKeeps5 fl OptTotal) :
    ∀ cr, CorIn cr → ∀ s f, pokeN cr (Ovum.full s f).toNoun =
      (liftPoke (enc fl) (pokeS Ar) cr (Ovum.full s f)).map fun r => C r.1.toNoun r.2 := by
  have hM := monoLinkGood5_of_gate fl Ar OptTotal hUA hG
  have hK := skaKeeps_of_armP Ar hA hJ
  have hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none := fun s a L j h => by
    rw [hA]; exact anaArmP_atom env jet fold frozen fuel bf regOf jetsOf newOf s a L j h
  intro cr hc s f
  obtain ⟨st, hg, rfl⟩ := pokeReachGood5 fl Ar OptTotal env hhe hth hsoft hrf lib hA hJA hR (sccLink_of fl hSA hI)
    hM (optLinkOn_optimizeP hOA) hK hU hSc hCK hSI hUS hTE hJC hAt hX cr hc.2.2
  exact pokeModel_fullGood5 fl Ar OptTotal env hhe hth hsoft hrf hA hJA hR (sccLink_of fl hSA hI) hM
    (optLinkOn_optimizeP hOA) hK hU hSc hSI hTE hJC hAt st hg s f

end Compiler
end Formalization
