import lemmas.Compiler.CompStraightMapNouns
import lemmas.Compiler.CompChaseFin
import lemmas.Compiler.CompCopyLib

/-!
# The map path of `+to-straight`: the rewrite gates

README Gaps 20.  The arms of the `|^` core of `+to-straight` that only its
map branch (`proxies` `&`) runs, linked in a core `[tsCoreBat [G R]]` whose
`rer` renames by `f` and returns its own `gen` `G` (`hrer`).  That is the
case of the whole-subject compile: one input, so `run` is `&`, and `rer` is
`[(ren (unproxy r)) gen]` whatever `gen` is.  Against the model
(`Ska/CompStraightMap.lean`, the stateless lemmas `rewriteArgs_stateless`,
`rewriteFin_stateless`, ...): every gate returns `[x G]` with `x` the
renaming of its input by `f`, the jumps chased by `+chase`.

* `+spin` with a gate that keeps its state (`spinM_pure`);
* `rewrite-args` (`tsm_args`), `rewrite-jump` (`tsm_jmp`), `rewrite-hop`
  (`tsm_hop`), `rewrite-par` (`tsm_par`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- `spinM` of a gate that keeps the state is a map. -/
theorem spinM_pure {α β : Type} (g : α → β) : ∀ (l : List α),
    spinM (fun a (_ : Unit) => some (g a, ())) l () = some (l.map g, ())
  | [] => rfl
  | a :: l => by simp [spinM, spinM_pure g l]

/-- The stateless `rer`: in the core `[tsCoreBat [G R]]` it renames by `f`
and returns `G`. -/
def RerS (f : Nat → Nat) (G R : Noun) : Prop :=
  ∀ r, nock (C tsRerBody (C (A r) (C tsCoreBat (C G R)))) tsRerBody = some (C (A (f r)) G)

/-! ## `rewrite-args` -/

/-- **The gate of the `+spin` of `rewrite-args`** on one unit. -/
theorem tsm_argG {f : Nat → Nat} {G R : Noun} (hrer : RerS f G R) (B J : Noun) (a : Option Nat) :
    nock (C tsmArgG1 (C (C (unitNoun A a) G) (C B (C J (C tsCoreBat (C G R)))))) tsmArgG1
      = some (C (unitNoun A (a.map f)) G) := by
  have hra := ts_rer_at
  unfold RerS at hrer
  generalize tsCoreBat = K at hra hrer ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  cases a with
  | none => simp [nock_exec, tsmArgG1, unitNoun]
  | some r => simp [nock_exec, tsmArgG1, unitNoun, hra, hrer]

/-- **`rewrite-args`**: the arguments of a jump renamed by `f`, `G` kept. -/
theorem tsm_args {f : Nat → Nat} {G R : Noun} (hrer : RerS f G R)
    (hL : slot? 0x7fffffff R = some layer2)
    (hU : ∀ J, nock (C tsmArgBody (C J (C tsCoreBat (C G R)))) tsmArgBuntF1 = some (C (A 0) G)) (j : Jmp) :
    nock (C tsmArgBody (C (Jmp.toNoun j) (C tsCoreBat (C G R)))) tsmArgBody
      = some (C (Jmp.toNoun (renJmp f j)) G) := by
  obtain ⟨args, there⟩ := j
  cases args with
  | nil =>
    conv => { lhs; arg 2; unfold tsmArgBody }
    simp [nock_exec, Jmp.toNoun, renJmp, listNoun]
  | cons a0 as =>
    have hsp := spin_arm_l2
    rw [spin_gate_eq] at hsp
    have hs1 := spin.arm_at
    have hSpin := spin_gate_T (unitNoun A) (unitNoun A) (fun _ : Unit => G) layer2 spinIn_layer2 tsmArgG1 (C (A 0) G)
      (C tsmArgBody (C (Jmp.toNoun ⟨a0 :: as, there⟩) (C tsCoreBat (C G R))))
      (fun a (_ : Unit) => some (a.map f, ())) (a0 :: as) ()
      (fun a _ _ => by
        rw [tsm_argG hrer]; rfl)
    rw [spinM_pure] at hSpin
    have hu := hU (Jmp.toNoun ⟨a0 :: as, there⟩)
    simp only [Option.map_some] at hSpin
    rw [← listNoun_map_listN, ← listNoun_map_listN] at hSpin
    simp only [Jmp.toNoun, listNoun, List.map_cons] at hSpin hu
    conv => { lhs; arg 2; unfold tsmArgBody }
    generalize tsmArgBuntF1 = UB at hu ⊢
    generalize tsCoreBat = K at hSpin hu ⊢
    generalize tsmArgG1 = AG at hSpin ⊢
    generalize tsmArgBody = AB at hSpin hu ⊢
    simp [nock_exec, Jmp.toNoun, renJmp, listNoun, hL, hs1, spin.axis, hsp, hSpin, hu]

/-! ## `rewrite-jump` and `rewrite-hop` -/

/-- The arms of the core that the jump gates pull. -/
theorem tsm_core_arms (G R : Noun) :
    slot? 1519 (C tsCoreBat (C G R)) = some (C (A 8) (C (C (A 1) (C (A 0) (A 0)))
      (C (C (A 1) tsmArgBody) (C (A 0) (A 1))))) ∧
    slot? 21 (C tsCoreBat (C G R)) = some tsChaseArm := by
  have h1 := tsmArg_at
  have h2 := ts_chase_at
  unfold tsChaseArm
  generalize tsCoreBat = K at h1 h2 ⊢
  constructor
  · simp [nock_exec, h1]
  · simp [nock_exec, h2]

/-- **`rewrite-jump`**: `(rewrite-args (chase & j))`. -/
theorem tsm_jmp {f : Nat → Nat} {G R : Noun} (bs : TreapMap mugF Blob) (hrer : RerS f G R)
    (hL : slot? 0x7fffffff R = some layer2)
    (hU : ∀ J, nock (C tsmArgBody (C J (C tsCoreBat (C G R)))) tsmArgBuntF1 = some (C (A 0) G))
    (hB : slot? 4094 (C tsCoreBat (C G R)) = some (HoonMap.toNoun Blob.toNoun bs)) (j : Jmp) :
    nock (C tsmJmpBody (C (Jmp.toNoun j) (C tsCoreBat (C G R)))) tsmJmpBody
      = (chase bs true j).map fun j' => C (Jmp.toNoun (renJmp f j')) G := by
  have hL' : slot? 0x1ffffffff (C tsCoreBat (C G R)) = some layer2 := by simp [nock_exec, hL]
  have hY : slot? 46 (C tsCoreBat (C G R)) = some tsBypArm := by
    have h := ts_byp_at
    unfold tsBypArm
    generalize tsCoreBat = K at h ⊢
    simp [nock_exec, h]
  have hch := ch_gate bs true (C tsCoreBat (C G R)) hB hL' hY j
  rw [show loob true = A 0 from rfl] at hch
  obtain ⟨h1519, h21⟩ := tsm_core_arms G R
  cases e : chase bs true j with
  | none =>
    rw [e] at hch
    generalize tsCoreBat = K at hch h1519 h21 ⊢
    conv => { lhs; arg 2; unfold tsmJmpBody }
    simp [nock_exec, h1519, h21, tsChaseArm, hch, loob]
  | some j' =>
    rw [e] at hch
    have ha := tsm_args hrer hL hU j'
    generalize tsCoreBat = K at hch h1519 h21 ha ⊢
    conv => { lhs; arg 2; unfold tsmJmpBody }
    simp [nock_exec, h1519, h21, tsChaseArm, hch, ha, loob]

/-- **`rewrite-hop`**: `(rewrite-args (chase | j))`. -/
theorem tsm_hop {f : Nat → Nat} {G R : Noun} (bs : TreapMap mugF Blob) (hrer : RerS f G R)
    (hL : slot? 0x7fffffff R = some layer2)
    (hU : ∀ J, nock (C tsmArgBody (C J (C tsCoreBat (C G R)))) tsmArgBuntF1 = some (C (A 0) G))
    (hB : slot? 4094 (C tsCoreBat (C G R)) = some (HoonMap.toNoun Blob.toNoun bs)) (j : Jmp) :
    nock (C tsmHopBody (C (Jmp.toNoun j) (C tsCoreBat (C G R)))) tsmHopBody
      = (chase bs false j).map fun j' => C (Jmp.toNoun (renJmp f j')) G := by
  have hL' : slot? 0x1ffffffff (C tsCoreBat (C G R)) = some layer2 := by simp [nock_exec, hL]
  have hY : slot? 46 (C tsCoreBat (C G R)) = some tsBypArm := by
    have h := ts_byp_at
    unfold tsBypArm
    generalize tsCoreBat = K at h ⊢
    simp [nock_exec, h]
  have hch := ch_gate bs false (C tsCoreBat (C G R)) hB hL' hY j
  rw [show loob false = A 1 from rfl] at hch
  obtain ⟨h1519, h21⟩ := tsm_core_arms G R
  cases e : chase bs false j with
  | none =>
    rw [e] at hch
    generalize tsCoreBat = K at hch h1519 h21 ⊢
    conv => { lhs; arg 2; unfold tsmHopBody }
    simp [nock_exec, h1519, h21, tsChaseArm, hch, loob]
  | some j' =>
    rw [e] at hch
    have ha := tsm_args hrer hL hU j'
    generalize tsCoreBat = K at hch h1519 h21 ha ⊢
    conv => { lhs; arg 2; unfold tsmHopBody }
    simp [nock_exec, h1519, h21, tsChaseArm, hch, ha, loob]

/-! ## `rewrite-par` -/

/-- **The gate of the `+spin` of `rewrite-par`** on one register. -/
theorem tsm_parG {f : Nat → Nat} {G R : Noun} (hrer : RerS f G R) (B J : Noun) (r : Nat) :
    nock (C tsmParG (C (C (A r) G) (C B (C J (C tsCoreBat (C G R)))))) tsmParG = some (C (A (f r)) G) := by
  have hra := ts_rer_at
  unfold RerS at hrer
  generalize tsCoreBat = K at hra hrer ⊢
  generalize tsRerBody = RB at hra hrer ⊢
  simp [nock_exec, tsmParG, hra, hrer]

/-- **`rewrite-par`**: a list of registers renamed by `f`, `G` kept. -/
theorem tsm_par {f : Nat → Nat} {G R : Noun} (hrer : RerS f G R)
    (hL : slot? 0x7fffffff R = some layer2) (v : List Nat) :
    nock (C tsmParBody (C (listNoun A v) (C tsCoreBat (C G R)))) tsmParBody
      = some (C (listNoun A (v.map f)) G) := by
  cases v with
  | nil =>
    conv => { lhs; arg 2; unfold tsmParBody }
    simp [nock_exec, listNoun]
  | cons a0 as =>
    have hsp := spin_arm_l2
    rw [spin_gate_eq] at hsp
    have hs1 := spin.arm_at
    have hSpin := spin_gate_T A A (fun _ : Unit => G) layer2 spinIn_layer2 tsmParG (C (A 0) G)
      (C tsmParBody (C (listNoun A (a0 :: as)) (C tsCoreBat (C G R))))
      (fun a (_ : Unit) => some (f a, ())) (a0 :: as) ()
      (fun a _ _ => by rw [tsm_parG hrer]; rfl)
    rw [spinM_pure] at hSpin
    simp only [Option.map_some] at hSpin
    rw [← listNoun_map_listN, ← listNoun_map_listN] at hSpin
    simp only [listNoun, List.map_cons] at hSpin
    conv => { lhs; arg 2; unfold tsmParBody }
    generalize tsCoreBat = K at hSpin ⊢
    generalize tsmParG = PG at hSpin ⊢
    generalize tsmParBody = PB at hSpin ⊢
    simp [nock_exec, listNoun, hL, hs1, spin.axis, hsp, hSpin]

end Compiler
end Formalization
