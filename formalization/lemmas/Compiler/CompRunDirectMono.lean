import lemmas.Compiler.CompRunDirectS
import lemmas.Ska.CompDirectM

/-!
# The direct call of the case `%2` of `+run` under `mono` `&`: `+mono-try-call`

README Gaps 19.  `+mono-try-call` (door arm `437183`, line 7267) against
track J's model `monoTryLoop` / `monoTryCall` (`Ska/CompDirectM.lean`):

* `mtcLoop`: the battery of the trap `|-` (axis `56317` of the arm), on the
  subject `mtcT` (`o`, `fail`, `r`, the gate with its sample `[ned Z]`, the
  door); `mtc_loop`: it is `monoTryLoop fail ned r o`, by induction on
  `ned`, the state carried through `+re` and `+emit`.
* `mtcGB`, `mtc_gb`, `mtc_at`: the gate (the pushes of `r = sub.pes`,
  `fail = o.pes`, `o = opt`, then the trap); `mtc_gate`: the gate on `[ned
  opt [sub pes]]` is `monoTryCall ned opt sub pes`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

variable {ctx : Noun}

/-- The battery of the trap of `+mono-try-call`. -/
def mtcLoop : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 504)))) (C (C (C (A 0) (A 6)) (C (A 0) (A 510)))
    (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 504)))) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A
    30)) (C (A 0) (A 505)))) (C (C (A 0) (A 0)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 127)))) (C (A 9)
    (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A
    3)) (C (C (C (A 1) (A 0x766f6d)) (C (C (A 0) (A 30)) (C (A 0) (A 505)))) (C (A 1) (A 0))))) (C (C (A 7) (C
    (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A
    14))))))) (C (A 0) (A 2))))))))))) (C (A 6) (C (C (A 3) (C (A 0) (A 504))) (C (C (A 7) (C (C (A 0) (A 1))
    (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 127)))))) (C (A 7) (C (C (A
    10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A
    7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A
    255)))))) (C (A 7) (C (C (A 10) (C (C (A 2046) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0)
    (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A
    2) (C (A 10) (C (C (A 252) (C (A 0) (A 2041))) (C (A 10) (C (C (A 30) (C (A 0) (A 6))) (C (A 0) (A
    7)))))))))) (C (A 7) (C (C (A 10) (C (C (A 4094) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0)
    (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A
    2) (C (A 10) (C (C (A 252) (C (A 0) (A 4088))) (C (A 10) (C (C (A 30) (C (A 0) (A 6))) (C (A 10) (C (C (A
    6) (C (A 0) (A 2))) (C (A 0) (A 15)))))))))))) (C (A 7) (C (C (A 10) (C (C (A 8190) (C (A 0) (A 5))) (C (A
    0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A
    7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 2047)))) (C (A 9) (C (A 2) (C (A 10)
    (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1)
    (A 0x646568)) (C (C (A 0) (A 510)) (C (A 0) (A 14)))) (C (C (C (A 1) (A 0x6c6174)) (C (C (A 0) (A 510)) (C
    (A 0) (A 30)))) (C (A 1) (A 0)))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (C (A 7) (C
    (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 6))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C
    (A 0x3ffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C
    (C (A 9) (C (A 0xaaaa) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0)
    (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 7) (C (C (A 0) (A 3)) (C (C
    (A 1) (A 0x716c63)) (C (C (A 0) (A 1022)) (C (C (C (A 1) (A 0)) (C (A 0) (A 2))) (C (C (A 1) (A 0)) (C (A
    0) (A 510))))))))))) (C (A 0) (A 2)))))))))))))))))))))))))))))))))))))))))))))))) (C (A 11) (C (C (A
    0x73736f74) (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 504))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8)
    (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 127)))))) (C (A 7) (C (C (A 10) (C (C
    (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C
    (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 255)))))) (C (A
    7) (C (C (A 10) (C (C (A 2046) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0)
    (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C
    (C (A 252) (C (A 0) (A 8167))) (C (A 10) (C (C (A 30) (C (A 0) (A 6))) (C (A 0) (A 7)))))))))) (C (A 7) (C
    (C (A 10) (C (C (A 4094) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3)))
    (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A
    252) (C (A 0) (A 0x3fe6))) (C (A 10) (C (C (A 30) (C (A 0) (A 6))) (C (A 10) (C (C (A 6) (C (A 0) (A 2)))
    (C (A 0) (A 15)))))))))))) (C (A 7) (C (C (A 10) (C (C (A 8190) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7)
    (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1))
    (C (A 6) (C (C (A 5) (C (C (A 0) (A 510)) (C (A 0) (A 0x3ff2)))) (C (C (A 0) (A 0)) (C (A 8) (C (C (A 9) (C
    (A 0xaaaa) (C (A 0) (A 2047)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C
    (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x646568)) (C (C (A 0) (A 510)) (C (A 0) (A
    14)))) (C (C (C (A 1) (A 0x6c6174)) (C (C (A 0) (A 510)) (C (A 0) (A 30)))) (C (C (C (A 1) (A 0x766f6d)) (C
    (C (A 0) (A 510)) (C (A 0) (A 0x3ff2)))) (C (A 1) (A 0))))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A
    0x706f68)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 6))))))) (C (A 0) (A
    2))))))))))))) (C (A 7) (C (C (A 10) (C (C (A 0x3ffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C
    (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C
    (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1)
    (A 0)))) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0x716c63)) (C (C (A 0) (A 1022)) (C (C (C (A 1) (A 0))
    (C (A 0) (A 2))) (C (C (A 1) (A 0)) (C (A 0) (A 510))))))))))) (C (A 0) (A
    2)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
/-- The battery of the gate `+mono-try-call`. -/
noncomputable def mtcGB : Noun := (slot? 109 ((slot? 437183 comp.door).getD (A 0))).getD (A 0)

/-- The hint `~%  %comp-mono-try-call` of the arm. -/
def mtcHint : Noun :=
  C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x6c6c61632d7972742d6f6e6f6d2d706d6f63) (C (C (A 0) (A 0x7ffff))
    (A 0))))) (C (A 0) (A 1)))

theorem mtc_gb : mtcGB = C (A 8) (C (C (A 0) (A 54)) (C (A 8) (C (C (A 0) (A 119)) (C (A 8) (C (C (A 0) (A 122))
    (C (A 8) (C (C (A 1) mtcLoop) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))))) := by
  kernel_rfl

theorem mtc_at : slot? 437183 comp.door = some (C (A 7) (C (C (A 8) (C (C (A 1) (C (C (A 0x656e6f6e) (A 0))
    (C (A 0) (C (A 0) (A 0))))) (C (C (A 1) mtcGB) (C (A 0) (A 1))))) mtcHint)) := by
  kernel_rfl

/-- The subject of the trap: `o`, `fail`, `r`, the gate with the sample
`[ned Z]` (`Z` is `[opt pes]`, never read), the door. -/
noncomputable abbrev mtcT (ned : Need) (r o fail : Nat) (Z : Noun) (g : Gen (TreapMap mugF)) (x : GenRest) (ctx : Noun) : Noun :=
  C mtcLoop (C (A o) (C (A fail) (C (A r) (C mtcGB (C (C ned.toNoun Z) (compCore g x ctx))))))

theorem need_cell : ∀ n : Need, ∃ a b, n.toNoun = C a b
  | Need.none => ⟨_, _, rfl⟩
  | Need.this _ => ⟨_, _, rfl⟩
  | Need.pair _ _ => ⟨_, _, rfl⟩
  | Need.both _ _ _ => ⟨_, _, rfl⟩

theorem mtc_blob_mov (r rn o : Nat) :
    Blob.toNoun ⟨[], [Pole.mov r rn], Termin.hop (jmp0 o)⟩
      = C (A 0) (C (C (C (A 0x766f6d) (C (A r) (A rn))) (A 0)) (C (A 0x706f68) (C (A 0) (A o)))) := by
  simp [Blob.toNoun, listNoun, Termin.toNoun, Pole.toNoun, Tag.hop, Tag.mov, Jmp.toNoun, jmp0]

theorem mtc_blob_split (r rh rt o : Nat) :
    Blob.toNoun ⟨[], [Pole.hed r rh, Pole.tal r rt], Termin.hop (jmp0 o)⟩
      = C (A 0) (C (C (C (A 0x646568) (C (A r) (A rh))) (C (C (A 0x6c6174) (C (A r) (A rt))) (A 0)))
          (C (A 0x706f68) (C (A 0) (A o)))) := by
  simp [Blob.toNoun, listNoun, Termin.toNoun, Pole.toNoun, Tag.hop, Tag.hed, Tag.tal, Jmp.toNoun, jmp0]

theorem mtc_blob_split3 (r rh rt rn o : Nat) :
    Blob.toNoun ⟨[], [Pole.hed r rh, Pole.tal r rt, Pole.mov r rn], Termin.hop (jmp0 o)⟩
      = C (A 0) (C (C (C (A 0x646568) (C (A r) (A rh))) (C (C (A 0x6c6174) (C (A r) (A rt)))
          (C (C (A 0x766f6d) (C (A r) (A rn))) (A 0)))) (C (A 0x706f68) (C (A 0) (A o)))) := by
  simp [Blob.toNoun, listNoun, Termin.toNoun, Pole.toNoun, Tag.hop, Tag.hed, Tag.tal, Tag.mov, Jmp.toNoun, jmp0]

theorem mtc_blob_clq (r s f : Nat) :
    Blob.toNoun ⟨[], [], Termin.clq r (jmp0 s) (jmp0 f)⟩
      = C (A 0) (C (A 0) (C (A 0x716c63) (C (A r) (C (C (A 0) (A s)) (C (A 0) (A f)))))) := by
  simp [Blob.toNoun, listNoun, Termin.toNoun, Tag.clq, Jmp.toNoun, jmp0]

/-- The statement of the trap at one need. -/
def MtcAt (ctx : Noun) (x : GenRest) (fail : Nat) (Z : Noun) (ned : Need) : Prop :=
  ∀ (r o : Nat) (g : Gen (TreapMap mugF)),
    nock (mtcT ned r o fail Z g x ctx) mtcLoop = (monoTryLoop fail ned r o g).map fun p => C (A p.1) (genNoun p.2 x)

/-- **The trap on `%none`**: `[o gen]`. -/
theorem mtc_none (x : GenRest) (fail : Nat) (Z : Noun) : MtcAt ctx x fail Z Need.none := by
    intro r o g
    conv => { lhs; arg 2; unfold mtcLoop }
    simp [nock_exec, Need.toNoun, monoTryLoop, eqCode, pure, StateT.pure, Tag.none, compCore, genNoun]

/-- **The trap on `%this`**: `?<  =(r r.ned)`, then one `+emit` of `[~ [%mov r
r.ned]~ %hop ~ o]`. -/
theorem mtc_this (hc : CompIn ctx) (x : GenRest) (fail : Nat) (Z : Noun) (rn : Nat) :
    MtcAt ctx x fail Z (Need.this rn) := by
    intro r o g
    have hD := comp_emit_at
    have he := cf_emit (x := x) hc g ⟨[], [Pole.mov r rn], Termin.hop (jmp0 o)⟩
    rw [mtc_blob_mov] at he
    conv => { lhs; arg 2; unfold mtcLoop }
    simp only [mtcT, compCore] at he ⊢
    generalize comp.door = Dr at hD he ⊢
    by_cases hr : r = rn
    · subst hr
      simp [nock_exec, Need.toNoun, monoTryLoop, eqCode, Tag.none, Tag.this, crashM]
    · have hr' : rn ≠ r := Ne.symm hr
      simp [nock_exec, Need.toNoun, monoTryLoop, eqCode, Tag.none, Tag.this, hr, hr', hD, comp_emit_arm, he,
        cf_emit_g]

/-! ## The cut of the branches on a cell and on `%both`

Each is a chain of five `=^` pushes (`+re`, `+re`, the run on the tail, the
run on the head, the `+emit` of the split block) and a last `+emit` of the
`%clq` block; the `%both` branch sits under the hint `mtcBOh` (`?<` of the
`?-`).  Not linked yet (see README Gaps 19). -/

/-- The last part of `mtcPA`. -/
def mtcPAL : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7)
    (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 7) (C (C (A 0)
    (A 3)) (C (C (A 1) (A 0x716c63)) (C (C (A 0) (A 1022)) (C (C (C (A 1) (A 0)) (C (A 0) (A 2))) (C (C (A 1)
    (A 0)) (C (A 0) (A 510))))))))))) (C (A 0) (A 2))))))))

/-- The value of push `0` of `mtcPA`. -/
def mtcPAv0 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 127))))))

/-- The value of push `1` of `mtcPA`. -/
def mtcPAv1 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 255))))))

/-- The value of push `2` of `mtcPA`. -/
def mtcPAv2 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 252) (C (A 0) (A 2041))) (C (A 10) (C (C (A
    30) (C (A 0) (A 6))) (C (A 0) (A 7))))))))))

/-- The value of push `3` of `mtcPA`. -/
def mtcPAv3 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 252) (C (A 0) (A 4088))) (C (A 10) (C (C (A
    30) (C (A 0) (A 6))) (C (A 10) (C (C (A 6) (C (A 0) (A 2))) (C (A 0) (A 15))))))))))))

/-- The value of push `4` of `mtcPA`. -/
def mtcPAv4 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 2047)))) (C (A 9) (C (A 2) (C (A
    10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A
    1) (A 0x646568)) (C (C (A 0) (A 510)) (C (A 0) (A 14)))) (C (C (C (A 1) (A 0x6c6174)) (C (C (A 0) (A 510))
    (C (A 0) (A 30)))) (C (A 1) (A 0)))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (C (A 7)
    (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 6))))))) (C (A 0) (A 2))))))))))

def mtcPAr4 : Noun :=
  C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C mtcPAv4 (C (A 7) (C (C (A 10) (C (C (A 0x3ffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) mtcPAL)))))))

def mtcPAr3 : Noun :=
  C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C mtcPAv3 (C (A 7) (C (C (A 10) (C (C (A 8190) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) mtcPAr4)))))))

def mtcPAr2 : Noun :=
  C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C mtcPAv2 (C (A 7) (C (C (A 10) (C (C (A 4094) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) mtcPAr3)))))))

def mtcPAr1 : Noun :=
  C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C mtcPAv1 (C (A 7) (C (C (A 10) (C (C (A 2046) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) mtcPAr2)))))))

def mtcPAr0 : Noun :=
  C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C mtcPAv0 (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) mtcPAr1)))))))

/-- The last part of `mtcBO`. -/
def mtcBOL : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7)
    (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 7) (C (C (A 0)
    (A 3)) (C (C (A 1) (A 0x716c63)) (C (C (A 0) (A 1022)) (C (C (C (A 1) (A 0)) (C (A 0) (A 2))) (C (C (A 1)
    (A 0)) (C (A 0) (A 510))))))))))) (C (A 0) (A 2))))))))

/-- The value of push `0` of `mtcBO`. -/
def mtcBOv0 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 127))))))

/-- The value of push `1` of `mtcBO`. -/
def mtcBOv1 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 255))))))

/-- The value of push `2` of `mtcBO`. -/
def mtcBOv2 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 252) (C (A 0) (A 8167))) (C (A 10) (C (C (A
    30) (C (A 0) (A 6))) (C (A 0) (A 7))))))))))

/-- The value of push `3` of `mtcBO`. -/
def mtcBOv3 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 252) (C (A 0) (A 0x3fe6))) (C (A 10) (C (C
    (A 30) (C (A 0) (A 6))) (C (A 10) (C (C (A 6) (C (A 0) (A 2))) (C (A 0) (A 15))))))))))))

/-- The value of push `4` of `mtcBO`. -/
def mtcBOv4 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 0) (A 510)) (C (A 0) (A 0x3ff2)))) (C (C (A 0) (A
    0)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 2047)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C
    (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x646568)) (C
    (C (A 0) (A 510)) (C (A 0) (A 14)))) (C (C (C (A 1) (A 0x6c6174)) (C (C (A 0) (A 510)) (C (A 0) (A 30))))
    (C (C (C (A 1) (A 0x766f6d)) (C (C (A 0) (A 510)) (C (A 0) (A 0x3ff2)))) (C (A 1) (A 0))))))) (C (C (A 7)
    (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A
    6))))))) (C (A 0) (A 2)))))))))))))

def mtcBOr4 : Noun :=
  C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C mtcBOv4 (C (A 7) (C (C (A 10) (C (C (A 0x3ffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) mtcBOL)))))))

def mtcBOr3 : Noun :=
  C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C mtcBOv3 (C (A 7) (C (C (A 10) (C (C (A 8190) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) mtcBOr4)))))))

def mtcBOr2 : Noun :=
  C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C mtcBOv2 (C (A 7) (C (C (A 10) (C (C (A 4094) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) mtcBOr3)))))))

def mtcBOr1 : Noun :=
  C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C mtcBOv1 (C (A 7) (C (C (A 10) (C (C (A 2046) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) mtcBOr2)))))))

def mtcBOr0 : Noun :=
  C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C mtcBOv0 (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) mtcBOr1)))))))

/-- The tag and clue of the hint of the `%both` branch. -/
def mtcBOh : Noun :=
  (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 504)))))

def mtcT1 : Noun :=
  (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 504))))

def mtcY1 : Noun :=
  (C (C (A 0) (A 6)) (C (A 0) (A 510)))

def mtcT2 : Noun :=
  (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 504))))

def mtcY2 : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 0) (A 30)) (C (A 0) (A 505)))) (C (C (A 0) (A 0)) (C (A 8) (C (C (A 9) (C (A
    0xaaaa) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1)
    (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x766f6d)) (C (C (A 0) (A 30)) (C (A 0) (A
    505)))) (C (A 1) (A 0))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (C (A 7) (C (C (A 0)
    (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 14))))))) (C (A 0) (A 2)))))))))))

def mtcT3 : Noun :=
  (C (A 3) (C (A 0) (A 504)))

theorem mtc_loop_eq : mtcLoop = C (A 6) (C mtcT1 (C mtcY1 (C (A 6) (C mtcT2 (C mtcY2 (C (A 6) (C mtcT3
    (C mtcPAr0 (C (A 11) (C mtcBOh mtcBOr0)))))))))) := by
  kernel_rfl

end Compiler
end Formalization
