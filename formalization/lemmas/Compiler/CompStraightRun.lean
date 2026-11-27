import lemmas.Compiler.CompStraightMapTop

/-!
# `+to-straight` with `run` `|`: the stateful `rer`

README Gaps 20.  When the input registers are not a run (a baked or coerced
input of the n-ary final pass), `rer` renames through the state `[re-gen
m]` of the `|^` core: a register met before is read from `m`, a new one gets
`re-gen` and `re-gen` goes up.  The model is `rer cond proxies false ren` in
the state monad `RM` (`Ska/CompStraightMap.lean`).

* `rmN`: the noun of a state `(re-gen, m)`, `m` a `TreapMap mugF Nat`;
* `RerM`: the stateful counterpart of `RerS` (track I): in the core
  `[tsCoreBat [(rmN st) R]]` the gate `rer` returns the noun of the model's
  `rer` on `st`;
* **`tsr_rer`**: the gate `rer` with `run` `|` and any `proxies`, in a core
  whose rest has the shape that the pushes of `+to-straight` give (as in
  track I's `tsm_rer_prox`), is `RerM` of the model's `rer cond proxies
  false ren`: `+get:by` of `m` at the unproxied register, on a miss the
  edit of `re-gen` and `+put:by` of `m`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The noun of the state `[re-gen m]` of the map path. -/
noncomputable def rmN (st : Nat × TreapMap mugF Nat) : Noun := C (A st.1) (HoonMap.toNoun A st.2)

/-- **The stateful `rer`**: in the core `[tsCoreBat [(rmN st) R]]` the gate
renames as the model's `rr` on the state `st` and returns the new state. -/
def RerM (rr : Nat → RM (TreapMap mugF) Nat) (R : Noun) : Prop :=
  ∀ r st, nock (C tsRerBody (C (A r) (C tsCoreBat (C (rmN st) R)))) tsRerBody
    = (rr r st).map fun p => C (A p.1) (rmN p.2)

/-- The branch of `rer` through `m`, as the kernel computes it. -/
theorem tsRerMap_eq : tsRerMap =
    (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffffff)))) (C (A 9) (C (A 764) (C (A 10) (C (C (A 6) (C (A 0) (A 125))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (C (A 0) (A 124)) (C (A 4) (C (A 0) (A 124)))))) (C (A 7) (C (C (A 10) (C (C (A 252) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 10) (C (C (A 253) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 509))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 62)) (C (A 0) (A 6)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (C (A 0) (A 2)) (C (A 0) (A 126))))))))))))) (C (C (A 0) (A 5)) (C (A 0) (A 62)))))))) := by
  kernel_rfl

/-- **`rer` with `run` `|`**: through `m`, for an `unproxy` gate that gives
the model's `unproxy cond`. -/
theorem tsr_rer (cond : TreapMap mugF (Nat × List Nat)) (proxies : Bool) (ren : Nat → Nat)
    (UB US UC SB REN N R0 INS REST : Noun)
    (hu : ∀ r, nock (C UB (C (A r) UC)) UB = some (A (unproxy cond r)))
    (hL : slot? 0x7fffffff (C SB (C REN (C (A 1) (C N (C R0 (C INS (C (loob proxies) (C (C UB (C US UC))
      REST)))))))) = some layer2) :
    RerM (rer cond proxies false ren)
      (C SB (C REN (C (A 1) (C N (C R0 (C INS (C (loob proxies) (C (C UB (C US UC)) REST)))))))) := by
  intro r st
  generalize hR : C SB (C REN (C (A 1) (C N (C R0 (C INS (C (loob proxies) (C (C UB (C US UC)) REST))))))) = R
    at hL
  have h14 : slot? 14 R = some (A 1) := by rw [← hR]; simp [nock_exec]
  have h254 : slot? 254 R = some (loob proxies) := by rw [← hR]; simp [nock_exec]
  have h510 : slot? 510 R = some (C UB (C US UC)) := by rw [← hR]; simp [nock_exec]
  clear hR
  have hgc : SomeIn layer2 ∧ GorIn mugF layer2 := ⟨someIn_layer2, gorIn_morIn_layer2.1⟩
  have hpc : GorIn mugF layer2 ∧ MorIn mugF layer2 := gorIn_morIn_layer2
  obtain ⟨n0, m⟩ := st
  have hu' := hu r
  conv => { lhs; arg 2; unfold tsRerBody }
  rw [tsRerMap_eq]
  generalize tsCoreBat = K
  cases proxies
  · have hget := getF_hoonMap A m r
    have hg := get_gate layer2 hgc (A r) (HoonMap.toNoun A m) _ hget
    have hput := putF_hoonMap A m r n0
    have hp := put_gate layer2 hpc (A r) (A n0) (HoonMap.toNoun A m) _ hput
    cases e : HoonMap.get m r <;>
      simp [nock_exec, rmN, loob, h14, h254, h510, hL, by_arm, by.arm_at, by.get.arm_at, by.put.arm_at, get_arm,
        put_arm, hg, hp, e, unitNoun, rer]
  · have hget := getF_hoonMap A m (unproxy cond r)
    have hg := get_gate layer2 hgc (A (unproxy cond r)) (HoonMap.toNoun A m) _ hget
    have hput := putF_hoonMap A m (unproxy cond r) n0
    have hp := put_gate layer2 hpc (A (unproxy cond r)) (A n0) (HoonMap.toNoun A m) _ hput
    cases e : HoonMap.get m (unproxy cond r) <;>
      simp [nock_exec, rmN, loob, h14, h254, h510, hL, by_arm, by.arm_at, by.get.arm_at, by.put.arm_at, get_arm,
        put_arm, hg, hp, hu', e, unitNoun, rer]

end Compiler
end Formalization
