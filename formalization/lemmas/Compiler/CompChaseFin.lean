import lemmas.Compiler.CompChase

/-!
# `+chase-fin` of the `|^` core of `+to-straight`

`+chase-fin` (core arm `382`, battery axis `254` of `tsCoreBat`) builds the
gate `rj` (`cfRjBody`: `j(args (turn args.j (lift ren)))`) and switches on
the tag of `fin` (`cfSw`).  The jumps of `%clq`, `%eqq`, `%brn`, `%brz`
are chased with `branch` `&`, the one of `%hop` with `|`, then renamed by
`rj`; `%bom` chases its optional target.  An `%lti` falls into the last case
(`%bom`, under `%toss`), whose `+chase` looks up a cell as a key and
crashes, as the model's `none`.

The gate `rj` goes through `+lift` (a wet gate of `layer2`, arm `372`) and
`+bind`, which are not linked here: its link is the stated hypothesis
`CfRjAt`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The body of the gate `rj` of `+chase-fin` (`j(args (turn args.j (lift ren)))`). -/
def cfRjBody : Noun :=
  (C (A 10) (C (C (A 2) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x1fffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 372) (C (A 0) (A 0x1fffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 1022))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 6))))
/-- The 11-way `?-` of `+chase-fin` on the tag of `fin` (the last case `%bom`
under `%toss`). -/
def cfSw : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x716c63)) (C (A 0) (A 28)))) (C (C (A 10) (C (C (A 3) (C (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 122))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 0) (A 2)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 21) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 246)))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 2)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 21) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 247)))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 14)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x717165)) (C (A 0) (A 28)))) (C (C (A 10) (C (C (A 3) (C (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 122))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 246))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 0) (A 2)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 21) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 494)))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 2)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 21) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 495)))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 14)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6e7262)) (C (A 0) (A 28)))) (C (C (A 10) (C (C (A 3) (C (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 122))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 0) (A 2)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 21) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 246)))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 2)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 21) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 247)))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 14)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x7a7262)) (C (A 0) (A 28)))) (C (C (A 10) (C (C (A 3) (C (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 122))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 0) (A 2)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 21) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 246)))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 2)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 21) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 247)))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 14)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706f68)) (C (A 0) (A 28)))) (C (C (A 10) (C (C (A 3) (C (A 8) (C (C (A 0) (A 2)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 21) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 1)))) (C (A 0) (A 61)))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 14)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706d6a)) (C (A 0) (A 28)))) (C (C (A 10) (C (C (A 7) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0xfffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 123)) (C (A 0) (A 510)))) (C (A 0) (A 2))))))))) (C (A 0) (A 14)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x666d6a)) (C (A 0) (A 28)))) (C (C (A 10) (C (C (A 14) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0xfffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 246)) (C (A 0) (A 510)))) (C (A 0) (A 2))))))))) (C (A 0) (A 14)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x70736a)) (C (A 0) (A 28)))) (C (C (A 10) (C (C (A 7) (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 123))) (C (A 0) (A 2))))))))) (C (A 0) (A 14)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x66736a)) (C (A 0) (A 28)))) (C (C (A 10) (C (C (A 14) (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 246))) (C (A 0) (A 2))))))))) (C (A 0) (A 14)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6e6f64)) (C (A 0) (A 28)))) (C (C (A 10) (C (C (A 3) (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 61))) (C (A 0) (A 2))))))))) (C (A 0) (A 14)))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x6d6f62)) (C (A 0) (A 28))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 29)))) (C (C (A 0) (A 14)) (C (A 10) (C (C (A 3) (C (C (A 1) (A 0)) (C (A 7) (C (C (A 8) (C (C (A 9) (C (A 21) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0)) (C (A 0) (A 59))))))) (C (A 0) (A 2)))))))) (C (A 0) (A 3)))))) (C (A 0) (A 14)))))))))))))))))))))))))))))))))))))))
/-- **The arm `+chase-fin`** (battery axis `254`), a kernel fact. -/
theorem ts_cf_at : slot? 254 tsCoreBat = some (C (A 8) (C (C (A 1) (C (A 0x6d6f62) (A 0))) (C (C (A 1) (C (A 8) (C (C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) cfRjBody) (C (A 0) (A 1))))) cfSw))) (C (A 0) (A 1))))) := by
  kernel_rfl

/-- The arm `+chase` of the core (core arm `21`): the gate builder. -/
def tsChaseArm : Noun :=
  C (A 8) (C (C (A 1) (C (A 0) (C (A 0) (A 0)))) (C (C (A 1) tsChaseBat) (C (A 0) (A 1))))

/-- **The gate `+chase`** on `[branch j]`. -/
theorem ch_gate (bs : TreapMap mugF Blob) (br : Bool) (CORE : Noun)
    (hB : slot? 4094 CORE = some (HoonMap.toNoun Blob.toNoun bs))
    (hL : slot? 0x1ffffffff CORE = some layer2) (hY : slot? 46 CORE = some tsBypArm) (j : Jmp) :
    nock (C tsChaseBat (C (C (loob br) (Jmp.toNoun j)) CORE)) tsChaseBat
      = (chase bs br j).map Jmp.toNoun := by
  have h := ch_nock bs br CORE hB hL hY j
  unfold chL at h
  conv => { lhs; arg 2; unfold tsChaseBat }
  simp only [nock_exec, h]

/-- The body of the gate `+chase-fin`. -/
def cfBody : Noun :=
  C (A 8) (C (C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) cfRjBody) (C (A 0) (A 1))))) cfSw)

/-- **The link of the gate `rj` of `+chase-fin`**, stated: on a jump `j` it
gives `renJmp ren j`.  Not proved (it needs `+lift` and `+bind`). -/
def CfRjAt (ren : Nat → Nat) (CORE : Noun) : Prop :=
  ∀ (X finN : Noun) (j : Jmp),
    nock (C cfRjBody (C (Jmp.toNoun j) (C X (C finN CORE)))) cfRjBody = some (Jmp.toNoun (renJmp ren j))


/-- The hypotheses on the core of `+chase-fin`: the blocks `bs`, `layer2`,
the arms `+bypassable` and `+chase`, the gate `ren` (renaming by `ren`) and
the gate `rj` (`CfRjAt`). -/
structure CfCore (bs : TreapMap mugF Blob) (ren : Nat → Nat) (CORE : Noun) : Prop where
  hB : slot? 4094 CORE = some (HoonMap.toNoun Blob.toNoun bs)
  hL : slot? 0x1ffffffff CORE = some layer2
  hY : slot? 46 CORE = some tsBypArm
  hCh : slot? 21 CORE = some tsChaseArm
  hR : ∃ RB RS RC, slot? 30 CORE = some (C RB (C RS RC)) ∧
    ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r))
  hrj : CfRjAt ren CORE

/-- `+chase` with `branch` `&` as `+chase-fin` calls it. -/
theorem cf_chase_t {bs : TreapMap mugF Blob} {ren : Nat → Nat} {CORE : Noun} (h : CfCore bs ren CORE) (j : Jmp) :
    nock (C tsChaseBat (C (C (A 0) (Jmp.toNoun j)) CORE)) tsChaseBat = (chase bs true j).map Jmp.toNoun :=
  ch_gate bs true CORE h.hB h.hL h.hY j

/-- `+chase` with `branch` `|`. -/
theorem cf_chase_f {bs : TreapMap mugF Blob} {ren : Nat → Nat} {CORE : Noun} (h : CfCore bs ren CORE) (j : Jmp) :
    nock (C tsChaseBat (C (C (A 1) (Jmp.toNoun j)) CORE)) tsChaseBat = (chase bs false j).map Jmp.toNoun :=
  ch_gate bs false CORE h.hB h.hL h.hY j

theorem cf_clq {bs : TreapMap mugF Blob} {ren : Nat → Nat} {CORE : Noun} (h : CfCore bs ren CORE) (X : Noun) (s : Nat) (z o : Jmp) :
    nock (C X (C (Termin.toNoun (Termin.clq s z o)) CORE)) cfBody
      = (chaseFin bs ren (Termin.clq s z o)).map Termin.toNoun := by
  obtain ⟨RB, RS, RC, hR, hren⟩ := h.hR
  have hz := cf_chase_t h z
  have ho := cf_chase_t h o
  have hrj := h.hrj
  unfold CfRjAt at hrj
  cases ez : chase bs true z <;> cases eo : chase bs true o <;> rw [ez] at hz <;> rw [eo] at ho <;>
    simp [nock_exec, cfBody, cfSw, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, chaseFin, h.hCh, tsChaseArm, hR, hren,
      hz, ho, ez, eo, hrj]

theorem cf_eqq {bs : TreapMap mugF Blob} {ren : Nat → Nat} {CORE : Noun} (h : CfCore bs ren CORE) (X : Noun) (l r : Nat) (z o : Jmp) :
    nock (C X (C (Termin.toNoun (Termin.eqq l r z o)) CORE)) cfBody
      = (chaseFin bs ren (Termin.eqq l r z o)).map Termin.toNoun := by
  obtain ⟨RB, RS, RC, hR, hren⟩ := h.hR
  have hrj := h.hrj
  unfold CfRjAt at hrj
  have hz := cf_chase_t h z
  have ho := cf_chase_t h o
  cases ez : chase bs true z <;> cases eo : chase bs true o <;> rw [ez] at hz <;> rw [eo] at ho <;>
    simp [nock_exec, cfBody, cfSw, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, chaseFin, h.hCh, tsChaseArm, hR, hren,
      hrj, h.hL, turn.arm_at, hz, ho, ez, eo]

theorem cf_brn {bs : TreapMap mugF Blob} {ren : Nat → Nat} {CORE : Noun} (h : CfCore bs ren CORE) (X : Noun) (s : Nat) (z o : Jmp) :
    nock (C X (C (Termin.toNoun (Termin.brn s z o)) CORE)) cfBody
      = (chaseFin bs ren (Termin.brn s z o)).map Termin.toNoun := by
  obtain ⟨RB, RS, RC, hR, hren⟩ := h.hR
  have hrj := h.hrj
  unfold CfRjAt at hrj
  have hz := cf_chase_t h z
  have ho := cf_chase_t h o
  cases ez : chase bs true z <;> cases eo : chase bs true o <;> rw [ez] at hz <;> rw [eo] at ho <;>
    simp [nock_exec, cfBody, cfSw, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, chaseFin, h.hCh, tsChaseArm, hR, hren,
      hrj, h.hL, turn.arm_at, hz, ho, ez, eo]

theorem cf_brz {bs : TreapMap mugF Blob} {ren : Nat → Nat} {CORE : Noun} (h : CfCore bs ren CORE) (X : Noun) (s : Nat) (z o : Jmp) :
    nock (C X (C (Termin.toNoun (Termin.brz s z o)) CORE)) cfBody
      = (chaseFin bs ren (Termin.brz s z o)).map Termin.toNoun := by
  obtain ⟨RB, RS, RC, hR, hren⟩ := h.hR
  have hrj := h.hrj
  unfold CfRjAt at hrj
  have hz := cf_chase_t h z
  have ho := cf_chase_t h o
  cases ez : chase bs true z <;> cases eo : chase bs true o <;> rw [ez] at hz <;> rw [eo] at ho <;>
    simp [nock_exec, cfBody, cfSw, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, chaseFin, h.hCh, tsChaseArm, hR, hren,
      hrj, h.hL, turn.arm_at, hz, ho, ez, eo]

theorem cf_hop {bs : TreapMap mugF Blob} {ren : Nat → Nat} {CORE : Noun} (h : CfCore bs ren CORE) (X : Noun) (j : Jmp) :
    nock (C X (C (Termin.toNoun (Termin.hop j)) CORE)) cfBody
      = (chaseFin bs ren (Termin.hop j)).map Termin.toNoun := by
  obtain ⟨RB, RS, RC, hR, hren⟩ := h.hR
  have hrj := h.hrj
  unfold CfRjAt at hrj
  have ht := cf_chase_f h j
  cases et : chase bs false j <;> rw [et] at ht <;>
    simp [nock_exec, cfBody, cfSw, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, chaseFin, h.hCh, tsChaseArm, hR, hren,
      hrj, h.hL, turn.arm_at, ht, et]

theorem cf_jmp {bs : TreapMap mugF Blob} {ren : Nat → Nat} {CORE : Noun} (h : CfCore bs ren CORE) (X : Noun) (a : Bell) (v : List Nat) :
    nock (C X (C (Termin.toNoun (Termin.jmp a v)) CORE)) cfBody
      = (chaseFin bs ren (Termin.jmp a v)).map Termin.toNoun := by
  obtain ⟨RB, RS, RC, hR, hren⟩ := h.hR
  have hrj := h.hrj
  unfold CfRjAt at hrj
  have hv := mr_turn_ren RB RS RC ren hren v
  simp [nock_exec, cfBody, cfSw, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, chaseFin, h.hCh, tsChaseArm, hR, hren,
      hrj, h.hL, turn.arm_at, hv]

theorem cf_jmf {bs : TreapMap mugF Blob} {ren : Nat → Nat} {CORE : Noun} (h : CfCore bs ren CORE) (X : Noun) (a : Bell) (v : List Nat) (n : Ring) :
    nock (C X (C (Termin.toNoun (Termin.jmf a v n)) CORE)) cfBody
      = (chaseFin bs ren (Termin.jmf a v n)).map Termin.toNoun := by
  obtain ⟨RB, RS, RC, hR, hren⟩ := h.hR
  have hrj := h.hrj
  unfold CfRjAt at hrj
  have hv := mr_turn_ren RB RS RC ren hren v
  simp [nock_exec, cfBody, cfSw, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, chaseFin, h.hCh, tsChaseArm, hR, hren,
      hrj, h.hL, turn.arm_at, hv]

theorem cf_jsp {bs : TreapMap mugF Blob} {ren : Nat → Nat} {CORE : Noun} (h : CfCore bs ren CORE) (X : Noun) (a : Bell) (s : Nat) :
    nock (C X (C (Termin.toNoun (Termin.jsp a s)) CORE)) cfBody
      = (chaseFin bs ren (Termin.jsp a s)).map Termin.toNoun := by
  obtain ⟨RB, RS, RC, hR, hren⟩ := h.hR
  have hrj := h.hrj
  unfold CfRjAt at hrj
  simp [nock_exec, cfBody, cfSw, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, chaseFin, h.hCh, tsChaseArm, hR, hren,
      hrj, h.hL, turn.arm_at]

theorem cf_jsf {bs : TreapMap mugF Blob} {ren : Nat → Nat} {CORE : Noun} (h : CfCore bs ren CORE) (X : Noun) (a : Bell) (s : Nat) (n : Ring) :
    nock (C X (C (Termin.toNoun (Termin.jsf a s n)) CORE)) cfBody
      = (chaseFin bs ren (Termin.jsf a s n)).map Termin.toNoun := by
  obtain ⟨RB, RS, RC, hR, hren⟩ := h.hR
  have hrj := h.hrj
  unfold CfRjAt at hrj
  simp [nock_exec, cfBody, cfSw, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, chaseFin, h.hCh, tsChaseArm, hR, hren,
      hrj, h.hL, turn.arm_at]

theorem cf_don {bs : TreapMap mugF Blob} {ren : Nat → Nat} {CORE : Noun} (h : CfCore bs ren CORE) (X : Noun) (s : Nat) :
    nock (C X (C (Termin.toNoun (Termin.don s)) CORE)) cfBody
      = (chaseFin bs ren (Termin.don s)).map Termin.toNoun := by
  obtain ⟨RB, RS, RC, hR, hren⟩ := h.hR
  have hrj := h.hrj
  unfold CfRjAt at hrj
  simp [nock_exec, cfBody, cfSw, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, chaseFin, h.hCh, tsChaseArm, hR, hren,
      hrj, h.hL, turn.arm_at]

theorem cf_bom_none {bs : TreapMap mugF Blob} {ren : Nat → Nat} {CORE : Noun} (h : CfCore bs ren CORE) (X : Noun)  :
    nock (C X (C (Termin.toNoun (Termin.bom Option.none)) CORE)) cfBody
      = (chaseFin bs ren (Termin.bom Option.none)).map Termin.toNoun := by
  obtain ⟨RB, RS, RC, hR, hren⟩ := h.hR
  have hrj := h.hrj
  unfold CfRjAt at hrj
  simp [nock_exec, cfBody, cfSw, Termin.toNoun, unitNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, chaseFin, h.hCh, tsChaseArm, hR, hren,
      hrj, h.hL, turn.arm_at]

theorem cf_bom_some {bs : TreapMap mugF Blob} {ren : Nat → Nat} {CORE : Noun} (h : CfCore bs ren CORE) (X : Noun) (x : Nat) :
    nock (C X (C (Termin.toNoun (Termin.bom (some x))) CORE)) cfBody
      = (chaseFin bs ren (Termin.bom (some x))).map Termin.toNoun := by
  obtain ⟨RB, RS, RC, hR, hren⟩ := h.hR
  have hrj := h.hrj
  unfold CfRjAt at hrj
  have ht := cf_chase_t h ⟨[], x⟩
  simp only [Jmp.toNoun, listNoun] at ht
  cases et : chase bs true ⟨[], x⟩ <;> rw [et] at ht <;>
    simp [nock_exec, cfBody, cfSw, Termin.toNoun, Jmp.toNoun, listNoun, unitNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, chaseFin, h.hCh, tsChaseArm, hR, hren,
      hrj, h.hL, turn.arm_at, ht, et]


/-- `getF` of a cell on the noun of a map with atom keys is `~`. -/
theorem cf_getF_cell {ν : Type} (f : ν → Noun) (x y : Noun) :
    ∀ t : Tr ν, getF mugF (C x y) (t.toNoun f) = some (A 0)
  | Tr.nil => rfl
  | Tr.node k v l r => by
    have il := cf_getF_cell f x y l
    have ir := cf_getF_cell f x y r
    simp only [Tr.toNoun, getF]
    split
    · rename_i h; cases h
    · split <;> assumption

/-- `+chase` crashes on a jump whose target is a cell. -/
theorem cf_chase_cell {bs : TreapMap mugF Blob} {ren : Nat → Nat} {CORE : Noun} (h : CfCore bs ren CORE)
    (br x y : Noun) :
    nock (C tsChaseBat (C (C br (C (A 0) (C x y))) CORE)) tsChaseBat = none := by
  have hgc : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
    ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
  have hg := got_gate_nil layer2 hgc (C x y) (HoonMap.toNoun Blob.toNoun bs) (by
    rw [hoonMap_toNoun]; exact cf_getF_cell Blob.toNoun x y bs.1)
  have key : ∀ Bd Bt, nock (C Bd (C Bt (C (C br (C (A 0) (C x y))) CORE))) tsChaseBody = none := by
    intro Bd Bt
    unfold tsChaseBody
    simp [nock_exec, h.hB, h.hL, by_arm, by.arm_at, by.got.arm_at, got_arm, hg]
  conv => { lhs; arg 2; unfold tsChaseBat }
  simp only [nock_exec, key]

theorem cf_lti {bs : TreapMap mugF Blob} {ren : Nat → Nat} {CORE : Noun} (h : CfCore bs ren CORE) (X : Noun) (n s : Nat) (z o : Jmp) :
    nock (C X (C (Termin.toNoun (Termin.lti n s z o)) CORE)) cfBody
      = (chaseFin bs ren (Termin.lti n s z o)).map Termin.toNoun := by
  obtain ⟨RB, RS, RC, hR, hren⟩ := h.hR
  have hc := cf_chase_cell h (A 0) (A s) (C (Jmp.toNoun z) (Jmp.toNoun o))
  simp [nock_exec, cfBody, cfSw, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, chaseFin, h.hCh, tsChaseArm, hc]

/-- **`+chase-fin`** on any terminator: `chaseFin bs ren fin`, a crash when
it is `none`. -/
theorem cf_gate {bs : TreapMap mugF Blob} {ren : Nat → Nat} {CORE : Noun} (h : CfCore bs ren CORE) (X : Noun) (fin : Termin) :
    nock (C X (C (Termin.toNoun fin) CORE)) cfBody = (chaseFin bs ren fin).map Termin.toNoun := by
  cases fin with
  | clq s z o => exact cf_clq h X s z o
  | eqq l r z o => exact cf_eqq h X l r z o
  | brn s z o => exact cf_brn h X s z o
  | brz s z o => exact cf_brz h X s z o
  | hop j => exact cf_hop h X j
  | jmp a v => exact cf_jmp h X a v
  | jmf a v n => exact cf_jmf h X a v n
  | jsp a s => exact cf_jsp h X a s
  | jsf a s n => exact cf_jsf h X a s n
  | don s => exact cf_don h X s
  | bom o =>
    cases o with
    | none => exact cf_bom_none h X
    | some x => exact cf_bom_some h X x
  | lti n s z o => exact cf_lti h X n s z o

end Compiler
end Formalization
