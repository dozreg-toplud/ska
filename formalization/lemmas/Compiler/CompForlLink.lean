import lemmas.Compiler.CompInto

/-!
# `+forl` of the door of `+comp`

    ++  forl
      |=  [r=@uvre o=@uwoo]
      =^  r-0   gen  re
      =^  r-1   gen  re
      =^  barg  gen  (emit ~[r] ~ %hop ~ o)
      =^  if-0  gen  (emit ~ [%imm `*`0 r-0]~ %hop ~[`r-0] barg)
      =^  if-1  gen  (emit ~ [%imm `*`1 r-1]~ %hop ~[`r-1] barg)
      [[if-0 if-1] gen]

The generator does not name the arm: `flBat` and `flArm` are written here and
tied to the pill by `comp_fl_at` (door axis `442362`).  The proof keeps the
state after each `+emit` folded as `cfEmitG b g` (`cf_emit_g`), so that each
step starts from a named state.  `+forl` reads and writes none of `cache`,
`soft`, `sofs`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

/-- The state after `+emit` of `b`. -/
def cfEmitG (b : Blob) (g : Gen (TreapMap mugF)) : Gen (TreapMap mugF) :=
  if g.drop then { g with bo := g.bo + 1 }
  else { g with bo := g.bo + 1, blocks := HoonMap.put g.blocks g.bo b }

theorem cf_emit_g (b : Blob) (g : Gen (TreapMap mugF)) : emit b g = some (g.bo, cfEmitG b g) :=
  cd_emit_eq g b

theorem cf_emitG_re (b : Blob) (g : Gen (TreapMap mugF)) : (cfEmitG b g).re = g.re := by
  unfold cfEmitG; split <;> rfl

theorem cf_emitG_bo (b : Blob) (g : Gen (TreapMap mugF)) : (cfEmitG b g).bo = g.bo + 1 := by
  unfold cfEmitG; split <;> rfl

variable {ctx : Noun} (x : GenRest)

variable {x} in
/-- `+emit` in the form the simprocs leave, with the state folded. -/
theorem cf_emit (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (b : Blob) :
    nock (C comp.emit.battery (C b.toNoun (C comp.door (C (genNoun g x) ctx)))) comp.emit.battery
      = some (C (A g.bo) (genNoun (cfEmitG b g) x)) := by
  have h := comp_emit x hc g b
  rw [cf_emit_g] at h
  exact h

def flBat : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 7)))))) (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 15)))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 43690) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 60)) (C (A 1) (A 0))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 125))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 43690) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x6d6d69)) (C (C (A 1) (A 0)) (C (A 0) (A 14)))) (C (A 1) (A 0))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0)) (C (A 0) (A 14))) (C (A 1) (A 0))))) (C (A 0) (A 6))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 43690) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x6d6d69)) (C (C (A 1) (A 1)) (C (A 0) (A 14)))) (C (A 1) (A 0))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0)) (C (A 0) (A 14))) (C (A 1) (A 0))))) (C (A 0) (A 14))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 0) (A 6)) (C (A 0) (A 2))) (C (A 0) (A 1022)))))))))))))))))))))))))))))))))))))))))))

def flArm : Noun :=
  (C (A 7) (C (C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) flBat) (C (A 0) (A 1))))) (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x6c726f662d706d6f63) (C (C (A 0) (A 0x7ffff)) (A 0))))) (C (A 0) (A 1))))))

/-- `+forl` is at door axis `442362` (core axis `704506`). -/
theorem comp_fl_at : slot? 442362 comp.door = some flArm := by kernel_rfl

/-- The arm `forl` builds its gate. -/
theorem comp_fl_arm (d : Noun) : nock d flArm =
    some (C flBat (C (C (A 0) (A 0)) d)) := by
  unfold flArm; simp only [nock_exec]

/-- The three blocks of `+forl`. -/
def flB1 (r o : Nat) : Blob := ⟨[r], [], Termin.hop (jmp0 o)⟩
def flB2 (r0 barg : Nat) : Blob := ⟨[], [Pole.imm (A 0) r0], Termin.hop ⟨[some r0], barg⟩⟩
def flB3 (r1 barg : Nat) : Blob := ⟨[], [Pole.imm (A 1) r1], Termin.hop ⟨[some r1], barg⟩⟩

/-- The model's `forl` with the states folded. -/
theorem fl_forl_eq (r o : Nat) (g : Gen (TreapMap mugF)) :
    forl r o g =
      let g1 : Gen (TreapMap mugF) := { g with re := g.re + 1 + 1 }
      let gA := cfEmitG (flB1 r o) g1
      let gB := cfEmitG (flB2 g.re g.bo) gA
      let gC := cfEmitG (flB3 (g.re + 1) g.bo) gB
      some ((gA.bo, gB.bo), gC) := by
  simp [forl, cf_emit_g, re, bind, StateT.bind, pure, StateT.pure, flB1, flB2, flB3,
    cf_emitG_bo]

variable {x} in
theorem fl_e1 (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (r o : Nat) :
    nock (C comp.emit.battery (C (C (C (A r) (A 0)) (C (A 0) (C (A 0x706f68) (C (A 0) (A o)))))
      (C comp.door (C (genNoun g x) ctx)))) comp.emit.battery
      = some (C (A g.bo) (genNoun (cfEmitG (flB1 r o) g) x)) :=
  cf_emit hc g (flB1 r o)

variable {x} in
theorem fl_e2 (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (r0 barg : Nat) :
    nock (C comp.emit.battery (C (C (A 0) (C (C (C (A 0x6d6d69) (C (A 0) (A r0))) (A 0))
      (C (A 0x706f68) (C (C (C (A 0) (A r0)) (A 0)) (A barg)))))
      (C comp.door (C (genNoun g x) ctx)))) comp.emit.battery
      = some (C (A g.bo) (genNoun (cfEmitG (flB2 r0 barg) g) x)) :=
  cf_emit hc g (flB2 r0 barg)

variable {x} in
theorem fl_e3 (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (r1 barg : Nat) :
    nock (C comp.emit.battery (C (C (A 0) (C (C (C (A 0x6d6d69) (C (A 1) (A r1))) (A 0))
      (C (A 0x706f68) (C (C (C (A 0) (A r1)) (A 0)) (A barg)))))
      (C comp.door (C (genNoun g x) ctx)))) comp.emit.battery
      = some (C (A g.bo) (genNoun (cfEmitG (flB3 r1 barg) g) x)) :=
  cf_emit hc g (flB3 r1 barg)

variable {x} in
/-- `+forl`: two fresh registers, then the blocks `barg`, `if-0`, `if-1`;
exact over `genNoun`, under `CompIn ctx` only. -/
theorem comp_forl (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (r o : Nat) :
    nock (C flBat (C (C (A r) (A o)) (compCore g x ctx))) flBat
      = (forl r o g).map fun p => C (C (A p.1.1) (A p.1.2)) (genNoun p.2 x) := by
  rw [fl_forl_eq]
  unfold flBat
  simp only [compCore, nock_exec, comp_re' ctx x, comp_emit_arm, fl_e1 hc, fl_e2 hc, fl_e3 hc,
    Option.map_some, cf_emitG_bo]

end Compiler
end Formalization
