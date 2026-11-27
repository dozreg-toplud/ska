import lemmas.Compiler.CompSccOfMiss2
import lemmas.Run

/-!
# The mold bunts of the roll of `+scc-of` (track Q)

`ScoBunts sccCore`: the bunts `smB1` (`*(set bell)`, the mold `set` of the
hoon core, arm `6098`, on the mold `bell`, arm `382` of axis `31` of the
core) and `smB2` (`*bell`) return on the core of `+scc-of`; both by the
kernel (`evalFuel`, as track P's `tailBunt_run`).  With it, `sccG_miss`
has no hypothesis on the pill's molds left.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel Tarjan

/-- The value of `smB1` on the core of `+scc-of`. -/
noncomputable def smB1V : Noun :=
  (evalFuel 3000 (C (A 0) (C (A 0) (C (A 0) (C (A 0) sccCore)))) smB1).getD (A 0)

/-- The value of `smB2` on the core of `+scc-of`. -/
noncomputable def smB2V : Noun :=
  (evalFuel 3000 (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) sccCore)))))) smB2).getD (A 0)

theorem smB1_run : nock (C (A 0) (C (A 0) (C (A 0) (C (A 0) sccCore)))) smB1 = some smB1V :=
  nock_of_evalFuel (fuel := 3000) (by kernel_rfl)

theorem smB2_run : nock (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) sccCore)))))) smB2 = some smB2V :=
  nock_of_evalFuel (fuel := 3000) (by kernel_rfl)

/-- **The bunts of the roll return on the core of `+scc-of`.** -/
theorem scoBunts_sccCore : ScoBunts sccCore := ⟨⟨_, smB1_run⟩, ⟨_, smB2_run⟩⟩

/-- **The miss of `+scc-of` from `TarjanLinkAt` alone**: when `sccs` has no
entry for `b` and `calls` is a map of trees, at every fuel, whenever
`scoMiss` returns, track P's `sccG` returns the same `[s sccs]`. -/
theorem sccG_missT (B CA SC : Noun) (hg : getF mugF B SC = some (A 0)) (hCA : CallsOK CA) (n : Nat)
    (hT : ∀ SUB, scoSub CA SC n [B] (A 0) = some SUB → TarjanLinkAt SUB) :
    ∀ r, scoMiss B CA SC n = some r → sccG B CA SC = some r :=
  sccG_miss B CA SC hg hCA n scoBunts_sccCore hT

end Compiler
end Formalization
