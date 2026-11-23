import lemmas.Ska.CompDown
import lemmas.Ska.CompCoerce

/-!
# The final pass meets the contract, with no assumption about the model

`finish_bellContract` of `CompTopOK.lean` with its two hypotheses about the
model discharged: `RunDown` by `runDown` (`CompDown.lean`) and `CoerceSpec`
by `coerceSpec` (`CompCoerce.lean`).  What it still assumes: the nomm is on
the fragment `Frag` and pure, nothing is baked, and the bell's cape has no
cell whose halves both know nothing (`CapeNorm`).
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- **The final pass meets the relation at the entry**, on the fragment,
when nothing is baked. -/
theorem finish_compDone' [HoonMapKeys Map] (lib : Lib) {nm : Nomm} (hf : Frag nm (CGoal.done : CGoal S))
    {ord : NeedOrd} {less : Cape} {bake : Need → Need × List (Nat × Noun)} {c' : Straight Map}
    (hbake : ∀ ned, bake ned = (ned, [])) (h : finish (S := S) nm ord less bake = some c') :
    CompDoneOn lib c' nm (CapeAxes less) :=
  finish_compDone lib hf hbake (runDown nm) coerceSpec h

/-- **The final pass meets the contract** of its bell, on the fragment, for
every shape `ord` for which it does not crash, when nothing is baked and the
bell's cape has no `[| |]`. -/
theorem finish_bellContract' [HoonMapKeys Map] {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {b : Bell} {nm : Nomm} (hp : nm.pure = true) (hA : Annot lib code (SkaModel.Fits b.less) b.fol nm)
    (hf : Frag nm (CGoal.done : CGoal S)) {cape : Cape} {data : Noun} (hb : b.less = Sock.mk cape data)
    (hn : CapeNorm cape) {ord : NeedOrd} {bake : Need → Need × List (Nat × Noun)}
    (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map} (h : finish (S := S) nm ord cape bake = some c')
    (N : Needs) : BellContract lib N b false c' :=
  finish_bellContract hok hp hA hf hb hn hbake (runDown nm) coerceSpec h N

end Comp
end SkaModel
end Formalization
