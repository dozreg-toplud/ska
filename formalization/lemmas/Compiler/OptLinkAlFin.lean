import lemmas.Compiler.OptLinkAlPrelude
import lemmas.Compiler.CompLift
import lemmas.Ska.OptAliasBrz

/-!
# `+alias`: the end of a block, the ends that only rename (phase 14, README Gaps 13)

```hoon
  =^  fin-new=termin  gen
    ?-    -.fin.bob
        ...
        %hop  [fin.bob(args.t (turn args.t.fin.bob (lift rn))) gen]
        %jmp  [fin.bob(v (turn v.fin.bob rn)) gen]
        %jmf  [fin.bob(v (turn v.fin.bob rn)) gen]
        %jsp  [fin.bob(s (rn s.fin.bob)) gen]
        %jsf  [fin.bob(s (rn s.fin.bob)) gen]
        %don  [fin.bob(s (rn s.fin.bob)) gen]
        %bom  [fin.bob gen]
    ==
```

The `?-` (`alFin`) runs in the subject `[body-new [par-new [bob [imms [info
[pre WALK]]]]]]` (`alFS`), where `WALK = [alBat [GEN [Y [Z optC]]]]` is the
core of the walk (axis `127`): `fin.bob` is at `59`, `gen` at `510`, and
`rn` is the arm `10` of `WALK`.  `GEN` is `[new old info imms info-local
imms-local rev folded]` (`alGenN`).

* `alFS`, `alGenN`: the subject and the noun of `gen`.
* `alBat_rn`: the battery with the arm `rn` at `6` exposed.
* `alF_hop`, `alF_jmp`, `alF_jmf`, `alF_jsp`, `alF_jsf`, `alF_don`,
  `alF_bom`: **each case returns `[fin-new gen]` with `fin-new` the
  model's end**, the registers renamed by `f` where `old.gen` is `OldRel` to
  `f`, and `gen` unchanged.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The noun of `gen`: `[new old info imms info-local imms-local rev folded]`. -/
def alGenN (NEW OLD INFO IMMS LOC IMML REV FOLD : Noun) : Noun :=
  C NEW (C OLD (C INFO (C IMMS (C LOC (C IMML (C REV FOLD))))))

/-- The subject of the end: `[body-new [par-new [bob [imms [info [pre WALK]]]]]]`,
the walk core `WALK = [alBat [GEN [Y [Z optC]]]]`. -/
def alFS (X1 X2 BOB X4 X5 X6 GEN Y Z : Noun) : Noun :=
  C X1 (C X2 (C BOB (C X4 (C X5 (C X6 (C alBat (C GEN (C Y (C Z optC)))))))))

/-- The arm `rn` of the battery. -/
def alRnArm : Noun := C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) alRnB) (C (A 0) (A 1))))

theorem alBat_rn : ∃ R1 R2, alBat = C R1 (C alRnArm R2) := ⟨_, _, rfl⟩

theorem al_rn_arm (d : Noun) : nock d alRnArm = some (C alRnB (C (A 0) d)) := by
  simp [alRnArm, nock_exec]

/-- `rn` as a gate: the slam on `r` of `[alRnB [0 WALK]]` is `f r`. -/
theorem al_rn_gate (R1 R2 NEW OLD REST Y Z : Noun) (f : Nat → Nat) (h : OldRel OLD f) (r : Nat) :
    nock (C alRnB (C (A r) (C (C R1 (C alRnArm R2)) (C (C NEW (C OLD REST)) (C Y (C Z optC)))))) alRnB
      = some (A (f r)) :=
  al_rn _ Y Z NEW OLD REST f h r

/-! ## The ends that only rename -/

theorem alF_don (X1 X2 P B X4 X5 X6 NEW OLD REST Y Z : Noun) (f : Nat → Nat) (h : OldRel OLD f)
    (s : Nat) :
    nock (alFS X1 X2 (C P (C B (Termin.toNoun (Termin.don s)))) X4 X5 X6 (C NEW (C OLD REST)) Y Z)
        alFinDon
      = some (C (Termin.toNoun (Termin.don (f s))) (C NEW (C OLD REST))) := by
  obtain ⟨R1, R2, hB⟩ := alBat_rn
  have hrn := al_rn_gate R1 R2 NEW OLD REST Y Z f h
  unfold alFS
  rw [hB]
  generalize optC = OC at hrn
  simp [nock_exec, alFinDon, al_rn_arm, Termin.toNoun, hrn]

theorem alF_jsp (X1 X2 P B X4 X5 X6 NEW OLD REST Y Z : Noun) (f : Nat → Nat) (h : OldRel OLD f)
    (a : Bell) (s : Nat) :
    nock (alFS X1 X2 (C P (C B (Termin.toNoun (Termin.jsp a s)))) X4 X5 X6 (C NEW (C OLD REST)) Y Z)
        alFinJsp
      = some (C (Termin.toNoun (Termin.jsp a (f s))) (C NEW (C OLD REST))) := by
  obtain ⟨R1, R2, hB⟩ := alBat_rn
  have hrn := al_rn_gate R1 R2 NEW OLD REST Y Z f h
  unfold alFS
  rw [hB]
  generalize optC = OC at hrn
  simp [nock_exec, alFinJsp, al_rn_arm, Termin.toNoun, hrn]

theorem alF_jsf (X1 X2 P B X4 X5 X6 NEW OLD REST Y Z : Noun) (f : Nat → Nat) (h : OldRel OLD f)
    (a : Bell) (s : Nat) (n : Ring) :
    nock (alFS X1 X2 (C P (C B (Termin.toNoun (Termin.jsf a s n)))) X4 X5 X6 (C NEW (C OLD REST)) Y Z)
        alFinJsf
      = some (C (Termin.toNoun (Termin.jsf a (f s) n)) (C NEW (C OLD REST))) := by
  obtain ⟨R1, R2, hB⟩ := alBat_rn
  have hrn := al_rn_gate R1 R2 NEW OLD REST Y Z f h
  unfold alFS
  rw [hB]
  generalize optC = OC at hrn
  simp [nock_exec, alFinJsf, al_rn_arm, Termin.toNoun, hrn]

theorem alF_jmp (X1 X2 P B X4 X5 X6 NEW OLD REST Y Z : Noun) (f : Nat → Nat) (h : OldRel OLD f)
    (a : Bell) (v : List Nat) :
    nock (alFS X1 X2 (C P (C B (Termin.toNoun (Termin.jmp a v)))) X4 X5 X6 (C NEW (C OLD REST)) Y Z)
        alFinJmp
      = some (C (Termin.toNoun (Termin.jmp a (v.map f))) (C NEW (C OLD REST))) := by
  obtain ⟨R1, R2, hB⟩ := alBat_rn
  have hrn := al_rn_gate R1 R2 NEW OLD REST Y Z f h
  have ht := mr_turn_ren alRnB (A 0) _ f hrn v
  have hL := optC_layer2
  unfold alFS
  rw [hB]
  generalize optC = OC at hrn ht hL
  simp [nock_exec, alFinJmp, al_rn_arm, Termin.toNoun, hL, turn.arm_at, turn_arm, ht]

theorem alF_jmf (X1 X2 P B X4 X5 X6 NEW OLD REST Y Z : Noun) (f : Nat → Nat) (h : OldRel OLD f)
    (a : Bell) (v : List Nat) (n : Ring) :
    nock (alFS X1 X2 (C P (C B (Termin.toNoun (Termin.jmf a v n)))) X4 X5 X6 (C NEW (C OLD REST)) Y Z)
        alFinJmf
      = some (C (Termin.toNoun (Termin.jmf a (v.map f) n)) (C NEW (C OLD REST))) := by
  obtain ⟨R1, R2, hB⟩ := alBat_rn
  have hrn := al_rn_gate R1 R2 NEW OLD REST Y Z f h
  have ht := mr_turn_ren alRnB (A 0) _ f hrn v
  have hL := optC_layer2
  unfold alFS
  rw [hB]
  generalize optC = OC at hrn ht hL
  simp [nock_exec, alFinJmf, al_rn_arm, Termin.toNoun, hL, turn.arm_at, turn_arm, ht]

theorem alF_hop (X1 X2 P B X4 X5 X6 NEW OLD REST Y Z : Noun) (f : Nat → Nat) (h : OldRel OLD f)
    (t : Jmp) :
    nock (alFS X1 X2 (C P (C B (Termin.toNoun (Termin.hop t)))) X4 X5 X6 (C NEW (C OLD REST)) Y Z)
        alFinHop
      = some (C (Termin.toNoun (Termin.hop { t with args := t.args.map (Option.map f) }))
          (C NEW (C OLD REST))) := by
  obtain ⟨R1, R2, hB⟩ := alBat_rn
  have hrn := al_rn_gate R1 R2 NEW OLD REST Y Z f h
  have ht := lf_turn alRnB (A 0) _ f hrn t.args
  have hL := optC_layer2
  unfold alFS
  rw [hB]
  generalize optC = OC at hrn ht hL
  obtain ⟨args, there⟩ := t
  simp [nock_exec, alFinHop, al_rn_arm, Termin.toNoun, Jmp.toNoun, hL, turn.arm_at, turn_arm, lf_lift_at,
    lf_lift_slam, ht]

theorem alF_bom (X1 X2 P B X4 X5 X6 GEN Y Z : Noun) (fin : Termin) :
    nock (alFS X1 X2 (C P (C B (Termin.toNoun fin))) X4 X5 X6 GEN Y Z) alFinLast
      = some (C (Termin.toNoun fin) GEN) := by
  obtain ⟨R1, R2, hB⟩ := alBat_rn
  unfold alFS
  rw [hB]
  generalize optC = OC
  cases fin <;> simp [nock_exec, alFinLast, Termin.toNoun]

end Compiler
end Formalization
