import lemmas.Compiler.CompTarjanStep
import lemmas.Hoon.Ju

/-!
# `+tarjan`: the unvisited kid (track Q)

**`tj_kunvis`**: the gate `tjKBat` on a kid that `vis` lacks runs
`connect(v kid, kids (~(get ju g) kid), acc acc)`: the trap `tjConn` on
the core of `connect` with `[[kid kids'] acc]`, `kids'` the `+get:ju` of
`g` (axis `6` of the context), and returns `(min lowest lowest-kid)` and
the trap's state.  The `+get:ju` and the recursive call are hypotheses (the
induction on the fuel discharges the call).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel Tarjan

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- `slot? 65535` of a context whose axis `32767` is `layer2`. -/
theorem tj_layer1 {CTX : Noun} (hL : slot? 32767 CTX = some layer2) : slot? 65535 CTX = some layer1 := by
  have h := layer2_layer1
  revert h
  cases layer2 with
  | atom _ => intro h; simp [nock_exec] at h
  | cell a b =>
    intro h
    simp only [nock_exec, Option.some.injEq] at h
    subst h
    exact slot?_right hL

/-- **An unvisited kid**: `vis` lacks `kid`; the gate runs `connect` on it
and lowers `lowest` to what it returns. -/
theorem tj_kunvis {CTX G : Noun} (hL : slot? 32767 CTX = some layer2) (hG : slot? 6 CTX = some G)
    (IX V0 KIDS0 ACC0 : Noun) {VIS : Noun} (IDX STK CUR FIN : Noun) (vis : Noun → Option Nat)
    (hv : TjMapIs VIS vis) (KID : Noun) (LO : Nat) (hk : vis KID = none)
    {KIDS' ACC' : Noun} {lk : Nat}
    (hju : nock (C ju.get.battery (C KID (C ju.battery (C G layer2)))) ju.get.battery = some KIDS')
    (hrec : nock (tjConnCore KID KIDS' (tjAccN IDX VIS STK CUR FIN) CTX) tjConn = some (C (A lk) ACC')) :
    nock (tjKCore KID LO (tjAccN IDX VIS STK CUR FIN) (C IX (tjConnCore V0 KIDS0 ACC0 CTX))) tjKBat
      = some (C (A (min LO lk)) ACC') := by
  have hn : ∀ u, ¬ Get VIS KID u := fun u h => by
    obtain ⟨i, hi, -⟩ := (hv.2 KID u).1 h
    rw [hk] at hi; cases hi
  have hget := get_gate layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ KID VIS _ (getF_none hv.1 hn)
  have hl1 := tj_layer1 hL
  have hrec' := hrec
  simp only [tjConnCore, tjAccN] at hrec'
  rw [tjKBat_eq, tjKUnvis_eq, tjKGet_eq]
  simp [tjKCore, tjConnCore, tjAccN, nock_exec, hL, hG, by.arm_at, by_arm, by.get.arm_at, get_arm, hget,
    ju.arm_at, ju_arm, ju.get.arm_at, ju_get_arm, hju, hrec', min.arm_at, min_arm,
    min_gate layer1 arith_layer1.2.2.2.1, hl1]

end Compiler
end Formalization
