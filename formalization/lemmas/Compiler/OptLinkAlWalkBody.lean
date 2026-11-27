import lemmas.Compiler.OptLinkAlWalkHyp
import lemmas.Compiler.OptLinkAlBodyGate

/-! # `+alias`: `AlBodyLink` is `al_body_gen` (phase 13) -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

attribute [local instance] SkaModel.Ana.tkeyNat

/-- **`AlBodyLink`** holds: it is the statement of `al_body_gen`. -/
theorem al_body_link : AlBodyLink :=
  fun _ _ _ _ hg PN IM IN PRE NA BL REV TOPO b ops st' hb => al_body_gen hg PN IM IN PRE NA BL REV TOPO b ops st' hb

end Compiler
end Formalization
