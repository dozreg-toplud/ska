import lemmas.Compiler.PokeLinkGlue

/-!
# The top with the fuel and the regs chosen (track P, README Gaps 23)

`pokeModel_fullReachP6L` takes the fuel `fuel` and the start of the
registrations `regOf` as parameters with two hypotheses, `FuelOK env regOf
fuel` and the shape `regOf [r1 r2 r3 r4 *] = [r1 r2 r3 r4 ~]`.  Here both are
chosen, so neither is assumed:

* `regOfP`: the first four slots of the jets noun, ended by `~` (the Hoon's
  `[root core batt arms ~]:jets.lon`); `regOfP_shape` is the shape;
* the fuel `anaFuel env regOfP`, a good fuel by `fuelOK_anaFuel`;
* **`pokeModel_fullReachP7`**: `pokeModel_fullReachP6L` at these.

And three fields of track K's record `GateRest5` that are state facts (P owes
them): `got` and `nomm` at a key of the table (`gateGot_of_key`: the entry
noun is `[nomm flags]`), `cole` at every `PGood6` state (`gateCole_of_good`:
axis `190` of `[jets calls]` is `call.cole`, by the shape `JetsMaps`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF SkaModel.PokeM FinMap

/-- **The registrations `+ska-poke` starts from**: `[root core batt arms ~]:jets.lon`
(on a jets noun with fewer than four slots, `~`; no state has one). -/
def regOfP : Noun → Noun
  | Noun.cell r1 (Noun.cell r2 (Noun.cell r3 (Noun.cell r4 _))) => C r1 (C r2 (C r3 (C r4 (A 0))))
  | _ => A 0

theorem regOfP_shape (r1 r2 r3 r4 jRest : Noun) :
    regOfP (C r1 (C r2 (C r3 (C r4 jRest)))) = C r1 (C r2 (C r3 (C r4 (A 0)))) := rfl

/-- **`pokeModel` on `%full` at every reachable core, over `PGood6`, at the
flags `flagsOf`, the fuel `anaFuel env regOfP` and the regs `regOfP`**: no
`FuelOK` and no shape of `regOf` left.  Left, with owners: `SpLeavesGood`
(P), `JetsOfGood jetsOf`, `JetsOfCole6 jetsOf` (P), the gate at `PGood6`
states (K; fields owed by P), `UnaryKeeps OptTotal` (D), `UnaryCacheKeeps`,
`UnarySccsIs` (K / Q), `OtherKeeps6` (P), the four `env` equations. -/
theorem pokeModel_fullReachP7 (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
    (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP) (lib : Lib)
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    {bf : BEnv FinMap → Nat}
    {jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun} {newOf : Noun → Noun}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen (anaFuel env regOfP) bf regOfP jetsOf newOf)
    (hJA : Ar.jetRoot = jetRootP) (hOA : Ar.optimize = optimizeP) (hSA : Ar.sccOf = sccOfP)
    (hUA : Ar.compileUnary = compileUnaryP flagsOf)
    (hL : SpLeavesGood OptTotal env jet fold frozen bf jetsOf newOf)
    (hG : ∀ st b sc, PGood6 OptTotal st → ∃ (NM CA V COLE SC0 : Noun) (env : Comp.CallEnv) (inl : Noun → Option Nomm)
      (n : Nomm) (ht : Noun → Nat) (D : Bell → Prop), UnaryGateAt flagsOf st b sc NM CA V COLE SC0 env inl n ht D)
    (hJ : JetsOfGood jetsOf) (hJC : JetsOfCole6 jetsOf)
    (hU : UnaryKeeps Ar OptTotal) (hCK : UnaryCacheKeeps Ar OptTotal) (hUS : UnarySccsIs Ar)
    (hX : OtherKeeps6 flagsOf OptTotal) :
    ∀ cr, CorIn cr → ∀ s f, pokeN cr (Ovum.full s f).toNoun =
      (liftPoke (enc flagsOf) (pokeS Ar) cr (Ovum.full s f)).map fun r => C r.1.toNoun r.2 :=
  pokeModel_fullReachP6L Ar env hhe hth hsoft hrf lib hA hJA hOA hSA hUA
    (fuelOK_anaFuel env regOfP) regOfP_shape hL hG hJ hJC hU hCK hUS hX

/-! ## Fields of `GateRest5` that are state facts -/

/-- **`got` and `nomm` of `GateRest5`** at a key `b` of the table: the entry
noun is `V = [nomm flags]`. -/
theorem gateGot_of_key (fl : Flags) (st : PSt) (b : Bell) (e : VarEntry FinMap)
    (h : FinMap.get st.long.code b = some e) :
    getF mugF b.toNoun (codeNoun fl st.long.code) = some (C (A 0) (C e.nomm.toNoun (fl st.long.code b))) ∧
    slot? 2 (C e.nomm.toNoun (fl st.long.code b)) = some e.nomm.toNoun := by
  refine ⟨?_, by simp [nock_exec]⟩
  have hc := codeNoun_getF fl st.long.code b
  rw [h] at hc
  exact hc

/-- **`cole` of `GateRest5`** at every `PGood6` state: axis `190` of
`[jets calls]` is `call.cole`, a map. -/
theorem gateCole_of_good {Cls : Straight (TreapMap mugF) → Prop} {st : PSt} (hg : PGood6 Cls st) :
    ∃ r1 r2 r3 r4 pd ca bk, st.jets = C r1 (C r2 (C r3 (C r4 (C pd (C ca bk))))) ∧ IsMap mugF ca ∧
      slot? 190 (C st.jets (callsNoun st.long)) = some ca := by
  obtain ⟨r1, r2, r3, r4, pd, ca, bk, hj, -, -, -, -, -, hca, -⟩ := hg.good5.good4.good3.good2.good.maps
  refine ⟨r1, r2, r3, r4, pd, ca, bk, hj, hca, ?_⟩
  rw [hj]
  simp [nock_exec]

end Compiler
end Formalization
