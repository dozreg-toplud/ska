import lemmas.Compiler.OptLinkAlWalkHyp
import lemmas.Compiler.OptLinkAlBodyGate
import lemmas.Compiler.OptLinkAlStartAll
import lemmas.Compiler.OptLinkAlParsTrap

/-!
# `+alias`: the three hypotheses of the walk, proved

* `al_start_link`: `AlStartLink` is `al_start` (phases 9 and 10, track B;
  `alStartW` is `alStartF`, `alStartW_eq`).
* `al_pars_link`: `AlParsLink` is `al_pars` (phase 12, track G).
* `al_body_link`: `AlBodyLink` is `al_body_gen` (phase 13).

`OptLinkAlWalkGate.lean` imports this file: `al_link` is `al_link_of`
with these three.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

attribute [local instance] SkaModel.Ana.tkeyNat

theorem alStartW_eq (K : Noun) : alStartW K = alStartF K := rfl

/-- **`AlStartLink`** holds: it is `al_start`. -/
theorem al_start_link : AlStartLink := by
  intro g GEN hg hb hn nargs BL REV T o preH hd hm info imms hi hj K
  rw [alStartW_eq]
  exact al_start hg hb hn nargs BL REV T o preH hd hm hi hj K

/-- **`AlParsLink`** holds: it is `al_pars`. -/
theorem al_pars_link : AlParsLink := by
  intro g info imms GEN hg hr hl nargs bl RV T IM IN o pre hd hm b edges loc0 hb he hp
  obtain ⟨GEN', h1, h2⟩ := al_pars hg hr (noLti_opt hl) IM IN (A nargs) (HoonMap.toNoun Blob.toNoun bl) RV T o pre
    hd hm b edges loc0 he hp
  exact ⟨GEN', h2, h1⟩

/-- **`AlBodyLink`** holds: it is the statement of `al_body_gen`. -/
theorem al_body_link : AlBodyLink :=
  fun _ _ _ _ hg PN IM IN PRE NA BL REV TOPO b ops st' hb => al_body_gen hg PN IM IN PRE NA BL REV TOPO b ops st' hb

end Compiler
end Formalization
