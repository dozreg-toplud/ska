import lemmas.Compiler.FolLoopCall
import lemmas.Compiler.SoftSpot
import lemmas.Compiler.TreapSet

/-!
One level of the trap `fol-loop` with the hypotheses that are now theorems
discharged: `CalleePutIs` (`calleePutIs`, from `FinMap.putInF_setNoun` of
`Compiler/TreapSet.lean`) and `SoftSpotIs` (`softSpotIs_of`, for every `env`
whose `softSpot` is `softSpotF`).  What stays assumed: the calls of the trap to
itself (`GoIs`), the loop `resolve` (`ResIs`), `+register-fast`
(`RegisterFastIs`) and `ana` at axis `511` of the rest of `+run`'s subject.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon SkaModel.Ana

variable {R : Type}

/-- `+put:in` on the noun of a set of callee entries is the noun of
`Treap.ins`. -/
theorem calleePutIs : CalleePutIs := fun m k => FinMap.putInF_setNoun m k

/-- One level of the trap is `Ana.folStep` on every formula, given its calls to
itself, the loop `resolve`, `+register-fast` and `ana` at axis `511` of the rest,
for every `env` whose `softSpot` is the model `softSpotF`. -/
theorem fol_loop_step_all' (regsNoun : R → Noun) (env : Env R) (hsoft : env.softSpot = softSpotF)
    (res : ResGo FinMap R) (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIs regsNoun rest go)
    (hana : slot? 511 rest = some ana) (hreg : RegisterFastIs regsNoun env)
    (hres : ResIs regsNoun rest res)
    (fol : Noun) (sub : Anno) (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nock (folSubj regsNoun rest fol sub seat mk bc df gen) fol_loop.battery
      = (Ana.folStep env res go fol sub seat mk bc df gen).map (folOutNoun regsNoun) := by
  rw [nock_eq_nockW]
  exact fol_loop_step_all nock (fun _ _ _ => rfl) regsNoun env res go rest hgo hana (softSpotIs_of env hsoft)
    hreg (dirIsW_of nock nock (fun s => nock_eq_nockW s _) (fun _ _ _ => rfl) regsNoun res rest hana hres
      calleePutIs) fol sub seat mk bc df gen

/-- One level of the trap run by `nockW c`, for any `c` that is `nock` off the
four formulas (`FFar`): `Ana.folStep` with the calls of the trap to itself as
`c` makes them (`GoIsW c`) and the trap `nock-2-direct-non-inlined` as `c`
kicks it (`DirIsW c`). -/
theorem fol_loop_step_allW' (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f)
    (regsNoun : R → Noun) (env : Env R) (hsoft : env.softSpot = softSpotF)
    (res : ResGo FinMap R) (go : FolGoS FinMap R) (rest : Noun) (hgo : GoIsW c regsNoun rest go)
    (hana : slot? 511 rest = some ana) (hreg : RegisterFastIs regsNoun env)
    (hdir : DirIsW c regsNoun rest res)
    (fol : Noun) (sub : Anno) (seat mk : Option Noun) (bc df : Bool) (gen : GenS FinMap R) :
    nockW c (folSubj regsNoun rest fol sub seat mk bc df gen) fol_loop.battery
      = (Ana.folStep env res go fol sub seat mk bc df gen).map (folOutNoun regsNoun) :=
  fol_loop_step_all c hcf regsNoun env res go rest hgo hana (softSpotIs_of env hsoft) hreg hdir
    fol sub seat mk bc df gen

end Compiler
end Formalization
