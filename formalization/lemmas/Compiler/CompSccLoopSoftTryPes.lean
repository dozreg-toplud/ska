import lemmas.Compiler.CompSccLoopSoftTryS
import lemmas.Compiler.CompCopyLink
import lemmas.Compiler.OptLinkSwTest

/-! # The pushes `pes` and `fail` of the try path of `+soft-emit` (README Gaps 21.22)

On the subject after `+soft-cons` (`tzSubj`: `[kon rub]`, `tom`, `flag`, `lat`, `tpS0`):
* `tz_ec_gate`: `+emit-cold` (line 5481, battery slot `16374` of `comp.door`) is `emitCold`;
* `tz_mean`: `?:  ?=(%mean kin.s)` goes on to `tpYN0` when `kin` is not `%mean`;
* `tz_pes`: `=^  pes  gen` (`tpYN0` to `tpYN3`, line 5433) is `softPesM`;
* `tz_fail`: `=^  fail  gen  (emit-cold ~ kon %hop ~ pes)` (`tpYN4` to `tpYN7`).

The `%call` side of `pes` is cut here at its pushes (`tzK0` .. `tzK19`, `tz_nh1`), one lemma per
push on `tzC` (the atoms pushed, last first): `tz_k0`, `tz_k4`, `tz_k8` (`re`), `tz_k12` (`+emit` of
the merge block), `tz_k16` (`+flatten-need`), `tz_k17` (`+emir` of `plain.s`), `tz_k18`
(`+emit-cold` of the pessimistic call); `tz_call_chain` composes them, `tz_pes_tail` is the
`%tail` side. -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The bunt of the sample of `+emit-cold` (a `blob`). -/
def tzEcBunt : Noun := (C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0))))

/-- The battery of the gate `+emit-cold`. -/
def tzEcBat : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 5460) (C (A 0) (A 7)))))) (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 756) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 2676) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 30))))) (C (A 0) (A 2)))))))))) (C (A 0) (A 6)))) (C (A 0) (A 2)))))))) (C (C (A 0) (A 2)) (C (A 8) (C (C (A 9) (C (A 350) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 0) (A 62)))) (C (A 0) (A 2)))))))))))))))))))

/-- The arm `+emit-cold`. -/
def tzEcArm : Noun := C (A 8) (C (C (A 1) tzEcBunt) (C (C (A 1) tzEcBat) (C (A 0) (A 1))))

theorem tz_ec_at : slot? 16374 comp.door = some tzEcArm := by kernel_rfl

theorem tz_oo_at : slot? 3412 comp.door = some comp.oo.arm := comp_oo_at

/-- **`+emit-cold`** on a blob is `emitCold`. -/
theorem tz_ec_gate {ctx : Noun} (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (x : GenRest) (b : Blob) :
    nock (C tzEcBat (C b.toNoun (compCore g x ctx))) tzEcBat
      = (emitCold b g).map fun p => C (A p.1) (genNoun p.2 x) := by
  obtain ⟨ha, hs, hm, _, _, _, _, _, _, _, hdv, hmd⟩ := arith_layer1
  have hbex : BexIn layer2 := ⟨bex.arm_at, hm⟩
  have hrsh : RshIn layer2 := ⟨rsh.arm_at, hbex, hdv⟩
  have hlsh : LshIn layer2 := ⟨lsh.arm_at, hbex⟩
  have hend : EndIn layer2 := ⟨end.arm_at, hbex, hmd⟩
  have hlog : LogicNeeds layer2 := ⟨hrsh, hlsh, hend, ha⟩
  have hbx := bex_gate layer2 hbex.2 30
  have hcn := con_gate layer2 hlog (2 ^ 30) g.bo
  have hoo := comp_oo ctx x g
  have he := comp_emir x hc { g with bo := g.bo + 1 } (2 ^ 30 ||| g.bo) b
  have hor : g.bo ||| 2 ^ 30 = 2 ^ 30 ||| g.bo := Nat.or_comm _ _
  nock_open tzEcBat
  simp only [compCore] at hoo he
  simp [nock_exec, oo, hoo, hc, con_arm, con.arm_at, hcn, bex_arm, bex.arm_at, hbx, comp_emir_arm, he,
    emitCold, bind, StateT.bind, pure, StateT.pure, hor]
  generalize (emir (1073741824 ||| g.bo) b _ : Option (Unit × Gen (TreapMap mugF))) = E
  cases E <;> rfl

/-- The arm `+emit-cold` builds its gate. -/
theorem tz_ec_arm (d : Noun) : nock d tzEcArm = some (C tzEcBat (C tzEcBunt d)) := by
  unfold tzEcArm; simp only [nock_exec]

/-- The subject after `+soft-cons`: `[[kon rub] tom flag lat tpS0]`. -/
abbrev tzS (kon : List Pole) (rub : Nat) (TOM FLAG LAT HD TR OPS CUT AXS : Noun) (o : Nat) (s : SoftCall)
    (g : Gen (TreapMap mugF)) (x : GenRest) (ctx : Noun) : Noun :=
  C (tpKR kon rub) (C TOM (C FLAG (C LAT (tpS0 HD TR OPS CUT AXS o s g x ctx))))

/-- **`?:  ?=(%mean kin.s)`**: a `%tail` or `%call` goes on to `tpYN0`. -/
theorem tz_mean (kon : List Pole) (rub : Nat) (TOM FLAG LAT HD TR OPS CUT AXS : Noun) (o : Nat)
    (s : SoftCall) (g : Gen (TreapMap mugF)) (x : GenRest) (ctx : Noun) (hk : s.kin = 0 ∨ s.kin = 1) :
    nock (tzS kon rub TOM FLAG LAT HD TR OPS CUT AXS o s g x ctx) tpY6
      = nock (tzS kon rub TOM FLAG LAT HD TR OPS CUT AXS o s g x ctx) tpYN0 := by
  conv => { lhs; arg 2; unfold tpY6 }
  rcases hk with hk | hk <;>
    simp [nock_exec, tpYT, Compiler.SoftCall.toNoun, hk, eqCode_atom, loob]

/-- **`pes` for a `%tail` call** without a ring: `(emit-cold ~ ~ %jsp b.s rub)`. -/
theorem tz_pes_tail {ctx : Noun} (hc : CompIn ctx) (kon : List Pole) (rub : Nat)
    (TOM FLAG LAT HD TR OPS CUT AXS : Noun) (o : Nat) (s : SoftCall) (g : Gen (TreapMap mugF)) (x : GenRest)
    (hk : s.kin = 1) (hr : s.rin = none) :
    nock (tzS kon rub TOM FLAG LAT HD TR OPS CUT AXS o s g x ctx) tpYN0
      = (emitCold ⟨[], [], Termin.jsp s.b rub⟩ g).bind fun p =>
          nock (C (A p.1) (tzS kon rub TOM FLAG LAT HD TR OPS CUT AXS o s p.2 x ctx)) tpYN4 := by
  have hD := tz_ec_at
  have hE := tz_ec_gate hc g x ⟨[], [], Termin.jsp s.b rub⟩
  conv => { lhs; arg 2; unfold tpYN0 tpYN1 tpYN2 tpYN3 tpYNH1 tpYNH2 }
  simp only [Blob.toNoun, Termin.toNoun, listNoun, List.foldr, Tag.jsp] at hE
  cases he : emitCold ⟨[], [], Termin.jsp s.b rub⟩ g with
  | none =>
    rw [he] at hE
    simp only [Option.map_none] at hE
    simp only [tzS, tpS0, seS0, compCore, Option.bind_none] at hE ⊢
    generalize comp.door = Dr at hD hE ⊢
    simp [nock_exec, Compiler.SoftCall.toNoun, hk, hr, eqCode_atom, loob, hD, tz_ec_arm, hE]
  | some p =>
    rw [he] at hE
    simp only [Option.map_some] at hE
    simp only [tzS, tpS0, seS0, compCore, Option.bind_some] at hE ⊢
    generalize comp.door = Dr at hD hE ⊢
    simp [nock_exec, Compiler.SoftCall.toNoun, hk, hr, eqCode_atom, loob, hD, tz_ec_arm, hE]

/-- **`fail`**: `=^  fail  gen  (emit-cold ~ kon %hop ~ pes)` (`tpYN4` to `tpYN7`). -/
theorem tz_fail {ctx : Noun} (hc : CompIn ctx) (kon : List Pole) (rub PES : Nat)
    (TOM FLAG LAT HD TR OPS CUT AXS : Noun) (o : Nat) (s : SoftCall) (g : Gen (TreapMap mugF)) (x : GenRest) :
    nock (C (A PES) (tzS kon rub TOM FLAG LAT HD TR OPS CUT AXS o s g x ctx)) tpYN4
      = (emitCold ⟨[], kon, Termin.hop (jmp0 PES)⟩ g).bind fun p =>
          nock (C (A p.1) (C (A PES) (tzS kon rub TOM FLAG LAT HD TR OPS CUT AXS o s p.2 x ctx))) tpYN8 := by
  have hD := tz_ec_at
  have hE := tz_ec_gate hc g x ⟨[], kon, Termin.hop (jmp0 PES)⟩
  conv => { lhs; arg 2; unfold tpYN4 tpYN5 tpYN6 tpYN7 tpYNH5 tpYNH6 }
  cases he : emitCold ⟨[], kon, Termin.hop (jmp0 PES)⟩ g with
  | none =>
    rw [he] at hE
    simp only [Blob.toNoun, Termin.toNoun, listNoun, List.foldr, Tag.hop, jmp0, Jmp.toNoun] at hE
    simp only [Option.map_none] at hE
    simp only [tzS, tpKR, tpS0, seS0, compCore, Option.bind_none] at hE ⊢
    generalize comp.door = Dr at hD hE ⊢
    generalize listNoun Pole.toNoun kon = KN at hE ⊢
    simp [nock_exec, hD, tz_ec_arm, hE]
  | some p =>
    rw [he] at hE
    simp only [Blob.toNoun, Termin.toNoun, listNoun, List.foldr, Tag.hop, jmp0, Jmp.toNoun] at hE
    simp only [Option.map_some] at hE
    simp only [tzS, tpKR, tpS0, seS0, compCore, Option.bind_some] at hE ⊢
    generalize comp.door = Dr at hD hE ⊢
    generalize listNoun Pole.toNoun kon = KN at hE ⊢
    simp [nock_exec, hD, tz_ec_arm, hE]

/-! ### The `%call` side of `pes` (`tpYNH1` cut at its pushes) -/

def tzK19 : Noun :=
  (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 0x1fffee)))) (C (C (C (A 1) (A 0x6c7363)) (C (C (A 0) (A 0xffff6)) (C (C (A 0) (A 253)) (C (A 0) (A 30))))) (C (C (A 1) (A 0x667363)) (C (C (A 0) (A 0xffff6)) (C (C (A 0) (A 253)) (C (C (A 0) (A 30)) (C (A 0) (A 0x3fffdd))))))))) (C (A 1) (A 0))))) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0x706f68)) (C (C (C (C (A 1) (A 0)) (C (A 0) (A 30))) (C (A 1) (A 0))) (C (A 0) (A 6))))))))) (C (A 0) (A 2))))))

def tzK18 : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x5ff6) (C (A 0) (A 0x1ffff)))) tzK19))

def tzKH17 : Noun :=
  (C (A 10) (C (C (A 0x7fffe) (C (A 8) (C (C (A 9) (C (A 350) (C (A 0) (A 0x1ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 0x1ffff7e)) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 0x1fffee)))) (C (C (C (A 1) (A 0x6c6163)) (C (C (A 0) (A 0xffff6)) (C (C (A 0) (A 2)) (C (A 0) (A 62))))) (C (C (A 1) (A 0x666163)) (C (C (A 0) (A 0xffff6)) (C (C (A 0) (A 2)) (C (C (A 0) (A 62)) (C (A 0) (A 0x3fffdd))))))))) (C (A 1) (A 0))) (C (C (A 1) (A 0x706f68)) (C (C (C (C (A 1) (A 0)) (C (A 0) (A 62))) (C (A 1) (A 0))) (C (A 0) (A 6)))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1))))

def tzK17 : Noun :=
  (C (A 7) (C tzKH17 tzK18))

def tzKH16 : Noun :=
  (C (A 8) (C (C (A 9) (C (A 348) (C (A 0) (A 0xffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 0x3fffde))) (C (A 0) (A 2))))))))

def tzK16 : Noun :=
  (C (A 8) (C tzKH16 tzK17))

def tzK15 : Noun :=
  (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) tzK16))

def tzKH14 : Noun :=
  (C (A 10) (C (C (A 0x3fffe) (C (A 0) (A 5))) (C (A 0) (A 1))))

def tzK14 : Noun :=
  (C (A 7) (C tzKH14 tzK15))

def tzKH13 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 0x7fff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 2)) (C (A 1) (A 0))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x766f6d)) (C (C (A 0) (A 2)) (C (A 0) (A 0x1fffbfe)))) (C (A 1) (A 0))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 0x7fff7fe))))))) (C (A 0) (A 2))))))))))

def tzK13 : Noun :=
  (C (A 8) (C tzKH13 tzK14))

def tzK12 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) tzK13))

def tzK11 : Noun :=
  (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) tzK12))

def tzKH10 : Noun :=
  (C (A 10) (C (C (A 0x1fffe) (C (A 0) (A 5))) (C (A 0) (A 1))))

def tzK10 : Noun :=
  (C (A 7) (C tzKH10 tzK11))

def tzKH9 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 0x3fff))))))

def tzK9 : Noun :=
  (C (A 8) (C tzKH9 tzK10))

def tzK8 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) tzK9))

def tzK7 : Noun :=
  (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) tzK8))

def tzKH6 : Noun :=
  (C (A 10) (C (C (A 0xfffe) (C (A 0) (A 5))) (C (A 0) (A 1))))

def tzK6 : Noun :=
  (C (A 7) (C tzKH6 tzK7))

def tzKH5 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 8191))))))

def tzK5 : Noun :=
  (C (A 8) (C tzKH5 tzK6))

def tzK4 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) tzK5))

def tzK3 : Noun :=
  (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) tzK4))

def tzKH2 : Noun :=
  (C (A 10) (C (C (A 0x7ffe) (C (A 0) (A 5))) (C (A 0) (A 1))))

def tzK2 : Noun :=
  (C (A 7) (C tzKH2 tzK3))

def tzKH1 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 4095))))))

def tzK1 : Noun :=
  (C (A 8) (C tzKH1 tzK2))

def tzK0 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) tzK1))

def tzKY : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x5ff6) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 7) (C (C (A 0) (A 3)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 0xffee)))) (C (C (C (A 1) (A 0x70736a)) (C (C (A 0) (A 0x7ff6)) (C (A 0) (A 5)))) (C (C (A 1) (A 0x66736a)) (C (C (A 0) (A 0x7ff6)) (C (C (A 0) (A 5)) (C (A 0) (A 0x1ffdd))))))))))))) (C (A 0) (A 2))))))))

theorem tz_nh1 : tpYNH1 = C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6c696174)) (C (A 0) (A 0x3ffa)))) (C tzKY tzK0)))) := by rfl

section call

variable {ctx : Noun} (hc : CompIn ctx) (kon : List Pole) (rub : Nat) (TOM FLAG LAT HD TR OPS CUT AXS : Noun)
  (o : Nat) (s : SoftCall) (x : GenRest)

/-- The subject of the `%call` side after the pushes `l` (the last first). -/
abbrev tzC (l : List Nat) (g : Gen (TreapMap mugF)) : Noun :=
  l.foldr (fun a S => C (A a) S) (tzS kon rub TOM FLAG LAT HD TR OPS CUT AXS o s g x ctx)

include hc in
/-- `=^  pro-opt  gen  re`. -/
theorem tz_k0 (g : Gen (TreapMap mugF)) :
    nock (tzC kon rub TOM FLAG LAT HD TR OPS CUT AXS o s x (ctx := ctx) [] g) tzK0
      = nock (tzC kon rub TOM FLAG LAT HD TR OPS CUT AXS o s x (ctx := ctx) [g.re] { g with re := g.re + 1 }) tzK4 := by
  have hD := comp_re_at
  have hr := comp_re' ctx x g
  conv => { lhs; arg 2; unfold tzK0 tzK1 tzK2 tzK3 tzKH1 tzKH2 }
  simp only [tzC, List.foldr, tzS, tpS0, seS0, compCore] at hr ⊢
  generalize comp.door = Dr at hD hr ⊢
  simp [nock_exec, hD, hr]

/-- `=^  pro-pes  gen  re`. -/
theorem tz_k4 (r1 : Nat) (g : Gen (TreapMap mugF)) :
    nock (tzC kon rub TOM FLAG LAT HD TR OPS CUT AXS o s x (ctx := ctx) [r1] g) tzK4
      = nock (tzC kon rub TOM FLAG LAT HD TR OPS CUT AXS o s x (ctx := ctx) [g.re, r1] { g with re := g.re + 1 })
          tzK8 := by
  have hD := comp_re_at
  have hr := comp_re' ctx x g
  conv => { lhs; arg 2; unfold tzK4 tzK5 tzK6 tzK7 tzKH5 tzKH6 }
  simp only [tzC, List.foldr, tzS, tpS0, seS0, compCore] at hr ⊢
  generalize comp.door = Dr at hD hr ⊢
  simp [nock_exec, hD, hr]

/-- `=^  merged  gen  re`. -/
theorem tz_k8 (r1 r2 : Nat) (g : Gen (TreapMap mugF)) :
    nock (tzC kon rub TOM FLAG LAT HD TR OPS CUT AXS o s x (ctx := ctx) [r2, r1] g) tzK8
      = nock (tzC kon rub TOM FLAG LAT HD TR OPS CUT AXS o s x (ctx := ctx) [g.re, r2, r1]
          { g with re := g.re + 1 }) tzK12 := by
  have hD := comp_re_at
  have hr := comp_re' ctx x g
  conv => { lhs; arg 2; unfold tzK8 tzK9 tzK10 tzK11 tzKH9 tzKH10 }
  simp only [tzC, List.foldr, tzS, tpS0, seS0, compCore] at hr ⊢
  generalize comp.door = Dr at hD hr ⊢
  simp [nock_exec, hD, hr]

include hc in
/-- `=^  merge  gen  (emit ~[merged] [%mov merged pro.s]~ %hop ~ out.s)`. -/
theorem tz_k12 (r1 r2 r3 : Nat) (g : Gen (TreapMap mugF)) :
    nock (tzC kon rub TOM FLAG LAT HD TR OPS CUT AXS o s x (ctx := ctx) [r3, r2, r1] g) tzK12
      = (emit ⟨[r3], [Pole.mov r3 s.pro], Termin.hop (jmp0 s.out)⟩ g).bind fun p =>
          nock (tzC kon rub TOM FLAG LAT HD TR OPS CUT AXS o s x (ctx := ctx) [p.1, r3, r2, r1] p.2) tzK16 := by
  have hD := comp_emit_at
  have he := comp_emit x hc g ⟨[r3], [Pole.mov r3 s.pro], Termin.hop (jmp0 s.out)⟩
  conv => { lhs; arg 2; unfold tzK12 tzK13 tzK14 tzK15 tzKH13 tzKH14 }
  cases e : emit ⟨[r3], [Pole.mov r3 s.pro], Termin.hop (jmp0 s.out)⟩ g with
  | none => simp [cd_emit_eq] at e
  | some p =>
    rw [e] at he
    simp only [Blob.toNoun, Termin.toNoun, Pole.toNoun, listNoun, List.foldr, Tag.hop, Tag.mov, jmp0, Jmp.toNoun,
      Option.map_some] at he
    simp only [tzC, List.foldr, tzS, tpS0, seS0, compCore, Option.bind_some, Compiler.SoftCall.toNoun] at he ⊢
    generalize comp.door = Dr at hD he ⊢
    simp [nock_exec, hD, comp_emit_arm, he]

include hc in
/-- `sub-v`: `(flatten-need ned.s)`. -/
theorem tz_k16 (m r1 r2 r3 : Nat) (g : Gen (TreapMap mugF)) :
    nock (tzC kon rub TOM FLAG LAT HD TR OPS CUT AXS o s x (ctx := ctx) [m, r3, r2, r1] g) tzK16
      = nock (C (listNoun A (flattenNeed s.ned))
          (tzC kon rub TOM FLAG LAT HD TR OPS CUT AXS o s x (ctx := ctx) [m, r3, r2, r1] g)) tzK17 := by
  have hD := comp_fn_at
  have hf := comp_flatten_need hc (genNoun g x) s.ned
  conv => { lhs; arg 2; unfold tzK16 tzKH16 }
  simp only [tzC, List.foldr, tzS, tpS0, seS0, compCore, Compiler.SoftCall.toNoun] at hf ⊢
  generalize comp.door = Dr at hD hf ⊢
  simp [nock_exec, hD, comp_fn_arm, hf]

include hc in
/-- `=.  gen  (emir plain.s ~ [%cal b.s sub-v pro-opt]~ %hop ~[`pro-opt] merge)`. -/
theorem tz_k17 (hr : s.rin = none) (m r1 r2 r3 : Nat) (g : Gen (TreapMap mugF)) :
    nock (C (listNoun A (flattenNeed s.ned))
        (tzC kon rub TOM FLAG LAT HD TR OPS CUT AXS o s x (ctx := ctx) [m, r3, r2, r1] g)) tzK17
      = (emir s.plain ⟨[], [Pole.cal s.b (flattenNeed s.ned) r1], Termin.hop ⟨[some r1], m⟩⟩ g).bind fun p =>
          nock (C (listNoun A (flattenNeed s.ned))
            (tzC kon rub TOM FLAG LAT HD TR OPS CUT AXS o s x (ctx := ctx) [m, r3, r2, r1] p.2)) tzK18 := by
  have hD := comp_emir_at
  have he := comp_emir x hc g s.plain ⟨[], [Pole.cal s.b (flattenNeed s.ned) r1], Termin.hop ⟨[some r1], m⟩⟩
  conv => { lhs; arg 2; unfold tzK17 tzKH17 }
  cases e : emir s.plain ⟨[], [Pole.cal s.b (flattenNeed s.ned) r1], Termin.hop ⟨[some r1], m⟩⟩ g with
  | none => simp [emir] at e
  | some p =>
    rw [e] at he
    simp only [Blob.toNoun, Termin.toNoun, Pole.toNoun, listNoun, List.foldr, Tag.hop, Tag.cal, Jmp.toNoun,
      unitNoun, Option.map_some] at he
    simp only [tzC, List.foldr, tzS, tpS0, seS0, compCore, Option.bind_some, Compiler.SoftCall.toNoun, hr] at he ⊢
    generalize comp.door = Dr at hD he ⊢
    generalize listNoun A (flattenNeed s.ned) = SV at he ⊢
    simp [nock_exec, hD, comp_emir_arm, he]

include hc in
/-- The product: `(emit-cold ~ [%csl b.s rub pro-pes]~ %hop ~[`pro-pes] merge)`. -/
theorem tz_k18 (hr : s.rin = none) (SV : Noun) (m r1 r2 r3 : Nat) (g : Gen (TreapMap mugF)) :
    nock (C SV (tzC kon rub TOM FLAG LAT HD TR OPS CUT AXS o s x (ctx := ctx) [m, r3, r2, r1] g)) tzK18
      = (emitCold ⟨[], [Pole.csl s.b rub r2], Termin.hop ⟨[some r2], m⟩⟩ g).map fun p =>
          C (A p.1) (genNoun p.2 x) := by
  have hD := tz_ec_at
  have hE := tz_ec_gate hc g x ⟨[], [Pole.csl s.b rub r2], Termin.hop ⟨[some r2], m⟩⟩
  conv => { lhs; arg 2; unfold tzK18 tzK19 }
  simp only [Blob.toNoun, Termin.toNoun, Pole.toNoun, listNoun, List.foldr, Tag.hop, Tag.csl, Jmp.toNoun,
    unitNoun] at hE
  simp only [tzC, List.foldr, tzS, tpKR, tpS0, seS0, compCore, Compiler.SoftCall.toNoun, hr] at hE ⊢
  generalize comp.door = Dr at hD hE ⊢
  simp [nock_exec, hD, tz_ec_arm, hE]

include hc in
/-- **The `%call` side of `pes`** is `softPesM` (three `re`, the merge block, `+emir` of `plain.s`,
the pessimistic call by `+emit-cold`). -/
theorem tz_call_chain (hk : s.kin = 0) (hr : s.rin = none) (g : Gen (TreapMap mugF)) :
    nock (tzS kon rub TOM FLAG LAT HD TR OPS CUT AXS o s g x ctx) tzK0
      = (softPesM s rub g).map fun p => C (A p.1) (genNoun p.2 x) := by
  show nock (tzC kon rub TOM FLAG LAT HD TR OPS CUT AXS o s x (ctx := ctx) [] g) tzK0 = _
  rw [tz_k0 hc, tz_k4, tz_k8, tz_k12 hc, cd_emit_eq]
  simp only [Option.bind_some]
  rw [tz_k16 hc, tz_k17 hc _ _ _ _ _ _ _ _ _ _ _ _ _ hr]
  cases hd : g.drop <;>
  · simp only [emir, hd, if_true, if_false, Option.bind_some, Bool.false_eq_true]
    rw [tz_k18 hc _ _ _ _ _ _ _ _ _ _ _ _ _ hr]
    simp [softPesM, hk, bind, StateT.bind, re, pure, StateT.pure, cd_emit_eq, emir, hd]

include hc in
/-- **`pes`** (`tpYN0` to `tpYN3`, line 5433) for a `%tail` or `%call` without a ring: `softPesM`. -/
theorem tz_pes (hr : s.rin = none) (hk : s.kin = 0 ∨ s.kin = 1) (g : Gen (TreapMap mugF)) :
    nock (tzS kon rub TOM FLAG LAT HD TR OPS CUT AXS o s g x ctx) tpYN0
      = (softPesM s rub g).bind fun p =>
          nock (C (A p.1) (tzS kon rub TOM FLAG LAT HD TR OPS CUT AXS o s p.2 x ctx)) tpYN4 := by
  rcases hk with hk | hk
  · have hcall := tz_call_chain hc kon rub TOM FLAG LAT HD TR OPS CUT AXS o s x hk hr g
    conv => { lhs; arg 2; unfold tpYN0 tpYN1 tpYN2 tpYN3 tpYNH2 }
    rw [tz_nh1]
    cases e : (softPesM s rub g : Option (Nat × Gen (TreapMap mugF))) with
    | none =>
      rw [e] at hcall
      simp only [Option.map_none] at hcall
      simp only [tzS, tpKR, tpS0, seS0, compCore, Option.bind_none, Compiler.SoftCall.toNoun, hk,
        ↓reduceIte, Nat.zero_ne_one] at hcall ⊢
      simp [nock_exec, Compiler.SoftCall.toNoun, hk, eqCode_atom, hcall]
    | some p =>
      rw [e] at hcall
      simp only [Option.map_some] at hcall
      simp only [tzS, tpKR, tpS0, seS0, compCore, Option.bind_some, Compiler.SoftCall.toNoun, hk,
        ↓reduceIte, Nat.zero_ne_one] at hcall ⊢
      simp [nock_exec, Compiler.SoftCall.toNoun, hk, eqCode_atom, hcall]
  · rw [tz_pes_tail hc kon rub TOM FLAG LAT HD TR OPS CUT AXS o s g x hk hr]
    simp [softPesM, hk]

end call

end Compiler
end Formalization
