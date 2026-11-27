import lemmas.Compiler.CompRunDirectMonoP
import lemmas.Compiler.CompRunAllSix

/-!
# The direct call of `%2` under `mono` `&` on parts of the class

README Gaps 19.  `comp_run_n2_directML` (`CompRunDirectMonoP.lean`) with its
parts from track A's class (`SixOk` with `Bake.NoAx0`: `comp_run_all_l6`,
`res_all6`, `sixOk_noDirect`): the case `%2` on a direct call with no memo
key whose subject and formula are in the class, at `mono` `A 0` against
`runLCM env true msup`, on every goal with `GInv`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

variable {ctx : Noun}

/-- A nomm of the class (`SixOk`, `Bake.NoAx0`) as `PartL`. -/
theorem partL_six (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod) (env : CallEnv)
    {n : Nomm} (h : SixOk n = true) (ha : Bake.NoAx0 n) (msup : Option Nomm) (region : List Nat) :
    PartL env msup ctx n region :=
  ⟨fun goal g hi => comp_run_all_l6 h7 hcode env n h ha msup region goal g hi, res_all6 env n h ha msup region,
    sixOk_noDirect _ h⟩

/-- **The case `%2` on a direct call with no memo key under `mono` `&`, its
subject and formula in the class**, on every goal with `GInv`, against
`runLCM env true msup` at `mono` `A 0`, for every rest `x` with `NoSoft` and
`CallNounM`. -/
theorem comp_run_n2_direct_six (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (hp : SixOk p = true) (hpa : Bake.NoAx0 p)
    (hq : SixOk q = true) (hqa : Bake.NoAx0 q) (b : Bell) (hcd : CodePure cod env b) (nb : NeedOrd)
    (hri : env.ring b = Option.none) (hnb : env.need b = some nb) (region : List Nat) (goal : CGoalL CSet)
    (g : Gen (TreapMap mugF)) (hinv : GInv g goal) :
    CompRunAtMM env msup ctx (fun x => ∃ sur SOF, CallNounM msup ctx p q b nb sur x (A 0) SOF)
      (Nomm.n2 p q (some (b, Option.none))) goal region g :=
  comp_run_n2_directML h7 hcode env msup p q (partL_six h7 hcode env hp hpa msup region)
    (partL_six h7 hcode env hq hqa msup region) b hcd nb hri hnb goal g hinv

/-- **What that case returns** (`GRes`). -/
theorem res_n2_direct_six (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (hp : SixOk p = true)
    (hpa : Bake.NoAx0 p) (hq : SixOk q = true) (hqa : Bake.NoAx0 q) {b : Bell} {nb : NeedOrd}
    (hri : env.ring b = Option.none) (hnb : env.need b = some nb) (region : List Nat) :
    ResForR (runLCM env true msup) (Nomm.n2 p q (some (b, Option.none))) region :=
  res_n2_directMono (fun goal g g' nex hi h => by
      rw [runLCM_true env (noDirect_of_nd p (sixOk_noDirect _ hp))] at h
      exact res_all6 env p hp hpa msup region goal g g' nex hi h)
    (fun goal g g' nex hi h => by
      rw [runLCM_true env (noDirect_of_nd q (sixOk_noDirect _ hq))] at h
      exact res_all6 env q hq hqa msup region goal g g' nex hi h)
    hri hnb

end Compiler
end Formalization
