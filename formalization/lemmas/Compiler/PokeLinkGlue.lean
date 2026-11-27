import lemmas.Compiler.PokeLinkTop6
import lemmas.Compiler.PokeLinkRestNew
import lemmas.Compiler.PokeLinkRestTail

/-!
# The glue of `spRest`: `SpRestAt` from its parts (track P, README Gaps 23)

`spRest_of_parts` computes `spRest` from `BakeLinkAt`, `NewCodeLinkAt`,
`LoopLinkAt`, `TailLinkAt`; `SpRestAt` is an iff over the pill's product at
some fuel of the analysis and the model's `anaArmP`.  The glue:

* the fuel: the pill's analysis at some fuel `n` returns the `r` the model's
  returns at its fuel (`FuelOK`); backwards the model's fuel is a fuel;
* the registrations: the model starts from `regOf j` (asked to be
  `[r1 r2 r3 r4 ~]` of the jets noun), and `skaPoke_regs`: the pill's regs
  `gr.2` are the model's `r.2.2.2.2` at the same fuel;
* `spRest_bake_none`: where the model's bake has no answer, `BakeLinkAt`
  says the pill's has none, so `spRest` crashes;
* `anaArmP_cell`: the model's `+ska-poke` laid out.

What is left at a state is `SpLeavesAt`: `BakeLinkAt` at the model's
environment `spE` and fuel `bf`, and the jets leaf `TailEndAt` with `j'` the
model's `jetsOf` and `newN` its `newOf`.  `NewCodeLinkAt` is
`newCodeLinkAt`, `LoopLinkAt` is `loopLinkAt_good6` (no leaf), `TailLinkAt`
is `tailLinkAt_of`.

* **`spRestAt_of_leaves`**, **`spRestGood6_of_leaves`**;
* **`pokeModel_fullReachP6L`**: the top at the flags `flagsOf`, with
  `SpRestGood6` replaced by `FuelOK`, the shape of `regOf`, and the leaves.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF SkaModel.PokeM FinMap

/-- The environment of `+bake-graph` in the model's `+ska-poke` at a state. -/
noncomputable def spE (jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool) (fold frozen : Bool) (st : PSt)
    (root : Ident) (r : Callgraph FinMap × FinMap Bell (FDatum FinMap) × Memo FinMap × FDatum FinMap × Noun) :
    BEnv FinMap :=
  pokeEnv (jet st.hot st.jets (pokeDat r.2.1 r.2.2.1) r.2.2.2.2) fold frozen st.long.vars root r.2.1 r.2.2.1 r.2.2.2.1

/-- The table after the poke. -/
noncomputable def spL (st : PSt) (r : Callgraph FinMap × FinMap Bell (FDatum FinMap) × Memo FinMap × FDatum FinMap × Noun)
    (bg : FinMap Bell (VarEntry FinMap) × FinMap Bell (FinMap Bell Unit)) : LongB FinMap :=
  ⟨r.2.2.1, addCode st.long.code (newCode st.long.code bg.1), bg.2⟩

/-- **The model's `+ska-poke` on a cell formula, laid out.** -/
theorem anaArmP_cell (env : Env Noun) (jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool)
    (fold frozen : Bool) (fuel : Noun → Noun → LongB FinMap → Noun → Nat) (bf : BEnv FinMap → Nat)
    (regOf : Noun → Noun) (jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun) (newOf : Noun → Noun)
    (st : PSt) (s f₁ f₂ : Noun) :
    anaArmP env jet fold frozen fuel bf regOf jetsOf newOf s (C f₁ f₂) st.long st.jets st.hot =
      (Ana.skaPoke env (fuel s (C f₁ f₂) st.long st.jets) (Sock.mk Cape.yes s, C f₁ f₂) st.long.memo
        (regOf st.jets)).bind fun r =>
      (bakeGraph (spE jet fold frozen st (Sock.mk Cape.yes s, C f₁ f₂) r)
        (bf (spE jet fold frozen st (Sock.mk Cape.yes s, C f₁ f₂) r))).map fun bg =>
      ((spE jet fold frozen st (Sock.mk Cape.yes s, C f₁ f₂) r).root, spL st r bg,
        jetsOf st.hot st.jets r.2.2.2.2 st.long (spL st r bg), newOf r.2.2.2.2) := by
  simp only [anaArmP, skaPokeB]
  cases Ana.skaPoke env (fuel s (C f₁ f₂) st.long st.jets) (Sock.mk Cape.yes s, C f₁ f₂) st.long.memo
      (regOf st.jets) with
  | none => rfl
  | some r =>
    simp only [Option.bind_some, Option.map_map]
    rfl

/-- **The pill's regs are the model's**: at one fuel, `Ana.skaPoke` returns
the registrations of `+ska-callgraph`. -/
theorem skaPoke_regs {env : Env Noun} {n : Nat} {root : Ident} {memo : Memo FinMap} {reg : Noun}
    {gr : Callgraph FinMap × Noun}
    {r : Callgraph FinMap × FinMap Bell (FDatum FinMap) × Memo FinMap × FDatum FinMap × Noun}
    (hg : Ana.skaCallgraph env n root memo reg = some gr) (hr : Ana.skaPoke env n root memo reg = some r) :
    r.2.2.2.2 = gr.2 := by
  unfold Ana.skaPoke at hr
  rw [hg, Option.bind_some] at hr
  obtain ⟨p, -, hp⟩ := Option.bind_eq_some_iff.1 hr
  obtain ⟨rd, -, rfl⟩ := Option.map_eq_some_iff.1 hp
  rfl

/-- Where `Ana.skaPoke` answers, so does `+ska-callgraph`. -/
theorem skaCallgraph_of_poke {env : Env Noun} {n : Nat} {root : Ident} {memo : Memo FinMap} {reg : Noun}
    {r : Callgraph FinMap × FinMap Bell (FDatum FinMap) × Memo FinMap × FDatum FinMap × Noun}
    (hr : Ana.skaPoke env n root memo reg = some r) : ∃ gr, Ana.skaCallgraph env n root memo reg = some gr := by
  unfold Ana.skaPoke at hr
  obtain ⟨gr, hg, -⟩ := Option.bind_eq_some_iff.1 hr
  exact ⟨gr, hg⟩

section Glue

variable (root : Ident) (r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN : Noun)
  (gr : Callgraph FinMap × Noun)
  (r : Callgraph FinMap × FinMap Bell (FDatum FinMap) × Memo FinMap × FDatum FinMap × Noun)

/-- **Where the pill's bake crashes, `spRest` crashes.** -/
theorem spRest_bake_none (h : nock (srS3 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r) srBake = none) :
    nock (srS0 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r) spRest = none := by
  rw [spRest_three]
  unfold srS3 at h ⊢
  simp only [srK3, srK4, srBakeId, nock_exec, Option.bind_some]
  simp only [srS3x, srS0] at h ⊢
  simp [h]

end Glue

/-! ## The leaves and the glue -/

/-- **The leaves of `spRest` at a state** (P): at every fuel where the
analysis answers, `BakeLinkAt` at the model's environment and fuel, and,
where the model's bake answers, the jets leaf `TailEndAt` with the model's
`jetsOf` and `newOf` (on the regs `r.2.2.2.2`, which are the pill's `gr.2`
by `skaPoke_regs`). -/
def SpLeavesAt (env : Env Noun) (jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool)
    (fold frozen : Bool) (bf : BEnv FinMap → Nat)
    (jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun) (newOf : Noun → Noun)
    (st : PSt) (s f r1 r2 r3 r4 jRest key : Noun) : Prop :=
  ∀ n gr r, Ana.skaCallgraph env n (Sock.mk Cape.yes s, f) st.long.memo (C r1 (C r2 (C r3 (C r4 (A 0))))) = some gr →
    Ana.skaPoke env n (Sock.mk Cape.yes s, f) st.long.memo (C r1 (C r2 (C r3 (C r4 (A 0))))) = some r →
    BakeLinkAt (Sock.mk Cape.yes s, f) r1 r2 r3 r4 jRest (codeNoun flagsOf st.long.code)
        (st.long.code.toNoun fun e => FinMap.setNoun e.calls) (st.long.vars.toNoun FinMap.setNoun)
        (st.long.code.toNoun fun e => e.seek.toNoun) key gr r
        (spE jet fold frozen st (Sock.mk Cape.yes s, f) r) (bf (spE jet fold frozen st (Sock.mk Cape.yes s, f) r)) ∧
    ∀ bg, bakeGraph (spE jet fold frozen st (Sock.mk Cape.yes s, f) r)
        (bf (spE jet fold frozen st (Sock.mk Cape.yes s, f) r)) = some bg →
      TailEndAt (Sock.mk Cape.yes s, f) r1 r2 r3 r4 jRest (codeNoun flagsOf st.long.code)
        (st.long.vars.toNoun FinMap.setNoun) key gr r flagsOf st.long.code (newCode st.long.code bg.1)
        (bg.1.toNoun varEntryNoun) (bg.2.toNoun FinMap.setNoun)
        (jetsOf st.hot st.jets r.2.2.2.2 st.long (spL st r bg)) (newOf r.2.2.2.2)

section Top

variable (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)) (Cls : Straight (TreapMap mugF) → Prop)

/-- **`SpRestAt` from the leaves**, on a `PGood6` state, at the flags
`flagsOf`. -/
theorem spRestAt_of_leaves (env : Env Noun)
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → Noun}
    {jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun} {newOf : Noun → Noun}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf) (hF : FuelOK env regOf fuel)
    (hreg : ∀ r1 r2 r3 r4 jRest, regOf (C r1 (C r2 (C r3 (C r4 jRest)))) = C r1 (C r2 (C r3 (C r4 (A 0)))))
    (st : PSt) (hg : PGood6 Cls st) (s f₁ f₂ r1 r2 r3 r4 jRest key : Noun)
    (hj : st.jets = C r1 (C r2 (C r3 (C r4 jRest))))
    (hL : SpLeavesAt env jet fold frozen bf jetsOf newOf st s (C f₁ f₂) r1 r2 r3 r4 jRest key) :
    SpRestAt flagsOf Ar env st s (C f₁ f₂) r1 r2 r3 r4 jRest key := by
  have hrg : regOf st.jets = C r1 (C r2 (C r3 (C r4 (A 0)))) := by rw [hj]; exact hreg _ _ _ _ _
  -- `spRest` from its parts at a fuel where the analysis answers
  have parts : ∀ n gr r, Ana.skaCallgraph env n (Sock.mk Cape.yes s, C f₁ f₂) st.long.memo (regOf st.jets) = some gr →
      Ana.skaPoke env n (Sock.mk Cape.yes s, C f₁ f₂) st.long.memo (regOf st.jets) = some r →
      ∀ bg, bakeGraph (spE jet fold frozen st (Sock.mk Cape.yes s, C f₁ f₂) r)
        (bf (spE jet fold frozen st (Sock.mk Cape.yes s, C f₁ f₂) r)) = some bg →
      nock (spAfter (fun x : Noun => x) (Sock.mk Cape.yes s, C f₁ f₂) r1 r2 r3 r4 jRest (lonRestNoun flagsOf st.long)
          key gr r) spRest =
        some (C (C (spE jet fold frozen st (Sock.mk Cape.yes s, C f₁ f₂) r).root.toNoun (newOf r.2.2.2.2))
          (longNoun flagsOf (jetsOf st.hot st.jets r.2.2.2.2 st.long (spL st r bg)) (spL st r bg))) := by
    intro n gr r hcg hsp bg hbg
    rw [hrg] at hcg hsp
    obtain ⟨hB, hT⟩ := hL n gr r hcg hsp
    have hT' := hT bg hbg
    -- the analysis at the model's fuel is the same, so `noAx0_poke` applies
    have hsp' := hF s (C f₁ f₂) st.long st.jets n r (by rw [hrg]; exact hsp)
    have e1 : anaArmP env jet fold frozen fuel bf regOf jetsOf newOf s (C f₁ f₂) st.long st.jets st.hot =
        some ((spE jet fold frozen st (Sock.mk Cape.yes s, C f₁ f₂) r).root, spL st r bg,
          jetsOf st.hot st.jets r.2.2.2.2 st.long (spL st r bg), newOf r.2.2.2.2) := by
      rw [anaArmP_cell, hsp', Option.bind_some, hbg, Option.map_some]
    have hN := noAx0_poke hg.good5 e1
    have hLp := loopLinkAt_good6 (Sock.mk Cape.yes s, C f₁ f₂) r1 r2 r3 r4 jRest
      (st.long.code.toNoun fun e => FinMap.setNoun e.calls) (st.long.vars.toNoun FinMap.setNoun)
      (st.long.code.toNoun fun e => e.seek.toNoun) key gr r hg (bg.2.toNoun FinMap.setNoun) hbg rfl hN
    have hNc := newCodeLinkAt (Sock.mk Cape.yes s, C f₁ f₂) r1 r2 r3 r4 jRest
      (st.long.code.toNoun fun e => FinMap.setNoun e.calls) (st.long.vars.toNoun FinMap.setNoun)
      (st.long.code.toNoun fun e => e.seek.toNoun) key gr r flagsOf st.long.code bg.1 (bg.2.toNoun FinMap.setNoun)
    have hTl := tailLinkAt_of (Sock.mk Cape.yes s, C f₁ f₂) r1 r2 r3 r4 jRest (codeNoun flagsOf st.long.code)
      (st.long.vars.toNoun FinMap.setNoun) key gr r flagsOf st.long.code (newCode st.long.code bg.1) bg.1
      (bg.2.toNoun FinMap.setNoun) (jetsOf st.hot st.jets r.2.2.2.2 st.long (spL st r bg)) (newOf r.2.2.2.2) hT'
    have hP := spRest_of_parts (Sock.mk Cape.yes s, C f₁ f₂) r1 r2 r3 r4 jRest (codeNoun flagsOf st.long.code)
      (st.long.code.toNoun fun e => FinMap.setNoun e.calls) (st.long.vars.toNoun FinMap.setNoun)
      (st.long.code.toNoun fun e => e.seek.toNoun) key gr r flagsOf
      (spE jet fold frozen st (Sock.mk Cape.yes s, C f₁ f₂) r) (bf (spE jet fold frozen st (Sock.mk Cape.yes s, C f₁ f₂) r))
      st.long.code bg (jetsOf st.hot st.jets r.2.2.2.2 st.long (spL st r bg)) (newOf r.2.2.2.2) ?_ ?_ ?_ ?_ ?_
    rotate_left
    · exact hbg
    · exact hB
    · exact hNc
    · exact hLp
    · exact hTl
    have e0 : spAfter (fun x : Noun => x) (Sock.mk Cape.yes s, C f₁ f₂) r1 r2 r3 r4 jRest (lonRestNoun flagsOf st.long)
        key gr r = srS0 (Sock.mk Cape.yes s, C f₁ f₂) r1 r2 r3 r4 jRest (codeNoun flagsOf st.long.code)
          (st.long.code.toNoun fun e => FinMap.setNoun e.calls) (st.long.vars.toNoun FinMap.setNoun)
          (st.long.code.toNoun fun e => e.seek.toNoun) key gr r := by
      simp only [srS0, lonRestNoun]
    rw [e0, hP]
    simp only [srRootN, spE, pokeEnv, longNoun, spL]
  intro y
  rw [hA]
  constructor
  · rintro ⟨n, gr, r, hcg, hsp, hy⟩
    rw [← hrg] at hcg hsp
    have hsp' := hF s (C f₁ f₂) st.long st.jets n r hsp
    cases hbg : bakeGraph (spE jet fold frozen st (Sock.mk Cape.yes s, C f₁ f₂) r)
        (bf (spE jet fold frozen st (Sock.mk Cape.yes s, C f₁ f₂) r)) with
    | none =>
      exfalso
      rw [hrg] at hcg hsp
      have hB := (hL n gr r hcg hsp).1
      unfold BakeLinkAt at hB
      rw [hbg, Option.map_none] at hB
      have := spRest_bake_none _ _ _ _ _ _ _ _ _ _ _ _ _ hB
      have e0 : spAfter (fun x : Noun => x) (Sock.mk Cape.yes s, C f₁ f₂) r1 r2 r3 r4 jRest
          (lonRestNoun flagsOf st.long) key gr r = srS0 (Sock.mk Cape.yes s, C f₁ f₂) r1 r2 r3 r4 jRest
            (codeNoun flagsOf st.long.code) (st.long.code.toNoun fun e => FinMap.setNoun e.calls)
            (st.long.vars.toNoun FinMap.setNoun) (st.long.code.toNoun fun e => e.seek.toNoun) key gr r := by
        simp only [srS0, lonRestNoun]
      rw [e0, this] at hy; cases hy
    | some bg =>
      rw [parts n gr r hcg hsp bg hbg, Option.some.injEq] at hy
      subst hy
      refine ⟨((spE jet fold frozen st (Sock.mk Cape.yes s, C f₁ f₂) r).root, spL st r bg,
        jetsOf st.hot st.jets r.2.2.2.2 st.long (spL st r bg), newOf r.2.2.2.2), ?_, rfl⟩
      rw [anaArmP_cell, hsp', Option.bind_some, hbg, Option.map_some]
  · rintro ⟨res, hres, rfl⟩
    rw [anaArmP_cell] at hres
    obtain ⟨r, hsp, hres⟩ := Option.bind_eq_some_iff.1 hres
    obtain ⟨bg, hbg, rfl⟩ := Option.map_eq_some_iff.1 hres
    obtain ⟨gr, hcg⟩ := skaCallgraph_of_poke hsp
    refine ⟨_, gr, r, by rw [← hrg]; exact hcg, by rw [← hrg]; exact hsp, ?_⟩
    exact parts _ gr r hcg hsp bg hbg

/-- **The leaves on `PGood6` states** (P: `+bake-graph` and the jets). -/
def SpLeavesGood (env : Env Noun) (jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool)
    (fold frozen : Bool) (bf : BEnv FinMap → Nat)
    (jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun) (newOf : Noun → Noun) : Prop :=
  ∀ (st : PSt) s f₁ f₂ r1 r2 r3 r4 jRest key, PGood6 Cls st → st.jets = C r1 (C r2 (C r3 (C r4 jRest))) →
    keyRaw (enc flagsOf st) = some key → SpLeavesAt env jet fold frozen bf jetsOf newOf st s (C f₁ f₂) r1 r2 r3 r4 jRest key

/-- **`SpRestGood6` at `flagsOf` from the leaves.** -/
theorem spRestGood6_of_leaves (env : Env Noun)
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → Noun}
    {jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun} {newOf : Noun → Noun}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf) (hF : FuelOK env regOf fuel)
    (hreg : ∀ r1 r2 r3 r4 jRest, regOf (C r1 (C r2 (C r3 (C r4 jRest)))) = C r1 (C r2 (C r3 (C r4 (A 0)))))
    (hL : SpLeavesGood Cls env jet fold frozen bf jetsOf newOf) : SpRestGood6 flagsOf Ar Cls env :=
  fun st s f₁ f₂ r1 r2 r3 r4 jRest key hg hj hk =>
    spRestAt_of_leaves Ar Cls env hA hF hreg st hg s f₁ f₂ r1 r2 r3 r4 jRest key hj (hL st s f₁ f₂ r1 r2 r3 r4 jRest key hg hj hk)

end Top

/-- **`pokeModel` on `%full` at every reachable core, over `PGood6`, at the
flags `flagsOf`, with `spRest` reduced to its leaves.**  Left, with owners:
`SpLeavesGood` (P: `BakeLinkAt`, the worklist of `+bake-graph`, and
`TailEndAt`, the jets), `FuelOK` and the shape of `regOf` (P: met by
`anaFuel`, `fuelOK_anaFuel`, and the regs of the jets noun),
`JetsOfGood jetsOf`, `JetsOfCole6 jetsOf` (P: `+ska-cole-update`), the gate
`UnaryGateAt` at `PGood6` states (K; fields owed by P), `UnaryKeeps OptTotal`
(D), `UnaryCacheKeeps`, `UnarySccsIs` (K / Q), `OtherKeeps6` (P), the four
`env` equations. -/
theorem pokeModel_fullReachP6L (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
    (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP) (lib : Lib)
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → Noun}
    {jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun} {newOf : Noun → Noun}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf)
    (hJA : Ar.jetRoot = jetRootP) (hOA : Ar.optimize = optimizeP) (hSA : Ar.sccOf = sccOfP)
    (hUA : Ar.compileUnary = compileUnaryP flagsOf)
    (hF : FuelOK env regOf fuel)
    (hreg : ∀ r1 r2 r3 r4 jRest, regOf (C r1 (C r2 (C r3 (C r4 jRest)))) = C r1 (C r2 (C r3 (C r4 (A 0)))))
    (hL : SpLeavesGood OptTotal env jet fold frozen bf jetsOf newOf)
    (hG : ∀ st b sc, PGood6 OptTotal st → ∃ (NM CA V COLE SC0 : Noun) (env : Comp.CallEnv) (inl : Noun → Option Nomm)
      (n : Nomm) (ht : Noun → Nat) (D : Bell → Prop), UnaryGateAt flagsOf st b sc NM CA V COLE SC0 env inl n ht D)
    (hJ : JetsOfGood jetsOf) (hJC : JetsOfCole6 jetsOf)
    (hU : UnaryKeeps Ar OptTotal) (hCK : UnaryCacheKeeps Ar OptTotal) (hUS : UnarySccsIs Ar)
    (hX : OtherKeeps6 flagsOf OptTotal) :
    ∀ cr, CorIn cr → ∀ s f, pokeN cr (Ovum.full s f).toNoun =
      (liftPoke (enc flagsOf) (pokeS Ar) cr (Ovum.full s f)).map fun r => C r.1.toNoun r.2 :=
  pokeModel_fullReachP6 flagsOf Ar env hhe hth hsoft hrf lib hA hJA hOA hSA hUA
    (spRestGood6_of_leaves Ar OptTotal env hA hF hreg hL) hG hJ hJC hU hCK hUS hX

end Compiler
end Formalization
