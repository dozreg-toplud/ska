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
      = (Ana.folStep env res go fol sub seat mk bc df gen).map (folOutNoun regsNoun) :=
  fol_loop_step_all regsNoun env res go rest hgo hana (softSpotIs_of env hsoft) hreg hres calleePutIs
    fol sub seat mk bc df gen

end Compiler
end Formalization
