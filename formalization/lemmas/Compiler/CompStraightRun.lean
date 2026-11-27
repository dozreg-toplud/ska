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

/-! ## `rewrite-par` and `rewrite-args` with the state -/

/-- `spinM` of a gate of `RM` is its `mapM`. -/
theorem spinM_mapM {α β σ : Type} (f : α → StateT σ Option β) : ∀ (l : List α) (s : σ),
    spinM (fun a s => f a s) l s = (l.mapM f) s
  | [], s => rfl
  | a :: l, s => by
    have ih := spinM_mapM f l
    simp only [spinM, List.mapM_cons, bind, StateT.bind, pure, StateT.pure]
    cases h : f a s with
    | none => rfl
    | some p =>
      simp only [Option.bind_some, ih]
      cases (List.mapM f l) p.2 <;> rfl

/-- **The gate of the `+spin` of `rewrite-par`** with the state: `=.  gen  g`,
then `rer` in the core with that `gen`. -/
theorem tsr_parG {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun} (hrer : RerM rr R) (B J G0 : Noun) (r : Nat)
    (st : Nat × TreapMap mugF Nat) :
    nock (C tsmParG (C (C (A r) (rmN st)) (C B (C J (C tsCoreBat (C G0 R)))))) tsmParG
      = (rr r st).map fun p => C (A p.1) (rmN p.2) := by
  have hra := ts_rer_at
  have h := hrer r st
  generalize tsCoreBat = K at hra h ⊢
  generalize tsRerBody = RB at hra h ⊢
  generalize rmN st = GS at h ⊢
  simp [nock_exec, tsmParG, hra, h]

/-- **`rewrite-par` with the state**: the model's `rewritePar rr`. -/
theorem tsr_par {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun} (hrer : RerM rr R)
    (hL : slot? 0x7fffffff R = some layer2) (v : List Nat) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmParBody (C (listNoun A v) (C tsCoreBat (C (rmN st) R)))) tsmParBody
      = (rewritePar rr v st).map fun p => C (listNoun A p.1) (rmN p.2) := by
  cases v with
  | nil =>
    conv => { lhs; arg 2; unfold tsmParBody }
    simp [nock_exec, listNoun, rewritePar, List.mapM_nil, pure, StateT.pure]
  | cons a0 as =>
    have hsp := spin_arm_l2
    rw [spin_gate_eq] at hsp
    have hs1 := spin.arm_at
    have hSpin := spin_gate_T A A rmN layer2 spinIn_layer2 tsmParG (C (A 0) (rmN st))
      (C tsmParBody (C (listNoun A (a0 :: as)) (C tsCoreBat (C (rmN st) R))))
      (fun a s => rr a s) (a0 :: as) st
      (fun a _ s => tsr_parG hrer _ _ _ a s)
    rw [spinM_mapM] at hSpin
    have e : ∀ x : Option (List Nat × (Nat × TreapMap mugF Nat)),
        x.map (fun r => C (listN (r.1.map A)) (rmN r.2)) = x.map (fun r => C (listNoun A r.1) (rmN r.2)) := by
      intro x; cases x <;> simp [listNoun_map_listN]
    rw [e, ← listNoun_map_listN] at hSpin
    simp only [listNoun, List.map_cons] at hSpin
    unfold rewritePar
    conv => { lhs; arg 2; unfold tsmParBody }
    generalize tsCoreBat = K at hSpin ⊢
    generalize tsmParG = PG at hSpin ⊢
    generalize tsmParBody = PB at hSpin ⊢
    generalize rmN st = GS at hSpin ⊢
    simp [nock_exec, listNoun, hL, hs1, spin.axis, hsp, hSpin]

/-- The model's step of `rewrite-args` on one unit. -/
def argStep (rr : Nat → RM (TreapMap mugF) Nat) : Option Nat → RM (TreapMap mugF) (Option Nat)
  | Option.none => pure Option.none
  | some r => do let r1 ← rr r; pure (some r1)

/-- **The gate of the `+spin` of `rewrite-args`** with the state. -/
theorem tsr_argG {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun} (hrer : RerM rr R) (B J G0 : Noun)
    (a : Option Nat) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmArgG1 (C (C (unitNoun A a) (rmN st)) (C B (C J (C tsCoreBat (C G0 R)))))) tsmArgG1
      = (argStep rr a st).map fun p => C (unitNoun A p.1) (rmN p.2) := by
  have hra := ts_rer_at
  cases a with
  | none => simp [nock_exec, tsmArgG1, unitNoun, argStep, pure, StateT.pure]
  | some r =>
    have h := hrer r st
    generalize tsCoreBat = K at hra h ⊢
    generalize tsRerBody = RB at hra h ⊢
    cases e : rr r st with
    | none =>
      rw [e] at h
      simp [nock_exec, tsmArgG1, unitNoun, hra, h, argStep, bind, StateT.bind, e]
    | some p =>
      rw [e] at h
      simp [nock_exec, tsmArgG1, unitNoun, hra, h, argStep, bind, StateT.bind, e, pure, StateT.pure]

/-- **`rewrite-args` with the state**: the model's `rewriteArgs rr`. -/
theorem tsr_args {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun} (hrer : RerM rr R)
    (hL : slot? 0x7fffffff R = some layer2)
    (hU : ∀ J G, nock (C tsmArgBody (C J (C tsCoreBat (C G R)))) tsmArgBuntF1 = some (C (A 0) G)) (j : Jmp)
    (st : Nat × TreapMap mugF Nat) :
    nock (C tsmArgBody (C (Jmp.toNoun j) (C tsCoreBat (C (rmN st) R)))) tsmArgBody
      = (rewriteArgs rr j st).map fun p => C (Jmp.toNoun p.1) (rmN p.2) := by
  obtain ⟨args, there⟩ := j
  cases args with
  | nil =>
    conv => { lhs; arg 2; unfold tsmArgBody }
    simp [nock_exec, Jmp.toNoun, listNoun, rewriteArgs, pure, StateT.pure]
  | cons a0 as =>
    have hsp := spin_arm_l2
    rw [spin_gate_eq] at hsp
    have hs1 := spin.arm_at
    have hSpin := spin_gate_T (unitNoun A) (unitNoun A) rmN layer2 spinIn_layer2 tsmArgG1 (C (A 0) (rmN st))
      (C tsmArgBody (C (Jmp.toNoun ⟨a0 :: as, there⟩) (C tsCoreBat (C (rmN st) R))))
      (fun a s => argStep rr a s) (a0 :: as) st
      (fun a _ s => tsr_argG hrer _ _ _ a s)
    rw [spinM_mapM] at hSpin
    have hm : (fun a => match a with
        | Option.none => (pure Option.none : RM (TreapMap mugF) (Option Nat))
        | some r => do let r1 ← rr r; pure (some r1)) = argStep rr := by
      funext a; cases a <;> rfl
    have hu := hU (Jmp.toNoun ⟨a0 :: as, there⟩) (rmN st)
    have hR : rewriteArgs rr ⟨a0 :: as, there⟩ st
        = (List.mapM (argStep rr) (a0 :: as) st).bind (fun p => some ((⟨p.1, there⟩ : Jmp), p.2)) := by
      unfold rewriteArgs
      rw [if_neg (List.cons_ne_nil _ _), ← hm]
      rfl
    rw [hR]
    cases em : List.mapM (argStep rr) (a0 :: as) st with
    | none =>
      rw [em] at hSpin
      simp only [Option.map_none] at hSpin
      rw [← listNoun_map_listN] at hSpin
      simp only [Jmp.toNoun, listNoun, List.map_cons] at hSpin hu
      conv => { lhs; arg 2; unfold tsmArgBody }
      generalize tsmArgBuntF1 = UB at hu ⊢
      generalize tsCoreBat = K at hSpin hu ⊢
      generalize tsmArgG1 = AG at hSpin ⊢
      generalize tsmArgBody = AB at hSpin hu ⊢
      generalize rmN st = GS at hSpin hu ⊢
      simp [nock_exec, Jmp.toNoun, listNoun, hL, hs1, spin.axis, hsp, hSpin, hu]
    | some q =>
      rw [em] at hSpin
      simp only [Option.map_some] at hSpin
      rw [← listNoun_map_listN, ← listNoun_map_listN] at hSpin
      simp only [Jmp.toNoun, listNoun, List.map_cons] at hSpin hu
      conv => { lhs; arg 2; unfold tsmArgBody }
      generalize tsmArgBuntF1 = UB at hu ⊢
      generalize tsCoreBat = K at hSpin hu ⊢
      generalize tsmArgG1 = AG at hSpin ⊢
      generalize tsmArgBody = AB at hSpin hu ⊢
      generalize rmN st = GS at hSpin hu ⊢
      simp [nock_exec, Jmp.toNoun, listNoun, hL, hs1, spin.axis, hsp, hSpin, hu]

end Compiler
end Formalization
