import lemmas.Compiler.CompForlLink

/-!
# `+flatten-need`, `+copy-need-make-ops`, `+copy-lazy`, `+copy` of the door of `+comp`

The generator names none of these arms: their batteries are written here and
tied to the pill by kernel facts on `comp.door` (`comp_fn_at`, ...).

`+flatten-need` is a gate that recurs on itself (`=*  flat  .`) and welds the
lists of the halves with `+weld` of layer 2.  It reads no field of the state.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

variable {ctx : Noun}

/-! ## `+flatten-need` -/

def fnBat : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 12)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 12)))) (C (C (C (A 0) (A 13)) (C (A 1) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 8) (C (C (A 9) (C (A 0xbef7f4) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2)))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 12))))) (C (C (A 0) (A 26)) (C (A 8) (C (C (A 9) (C (A 0xbef7f4) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 118))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 119))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))))))))))))))))

def fnArm : Noun :=
  (C (A 7) (C (C (A 8) (C (C (A 1) (C (A 0x656e6f6e) (A 0))) (C (C (A 1) fnBat) (C (A 0) (A 1))))) (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x6465656e2d6e657474616c662d706d6f63) (C (C (A 0) (A 0x7ffff)) (A 0))))) (C (A 0) (A 1))))))

/-- `+flatten-need` is at door axis `220` (core axis `348`). -/
theorem comp_fn_at : slot? 220 comp.door = some fnArm := by kernel_rfl

/-- The arm `flatten-need` builds its gate. -/
theorem comp_fn_arm (d : Noun) : nock d fnArm =
    some (C fnBat (C (C (A 0x656e6f6e) (A 0)) d)) := by
  unfold fnArm; simp only [nock_exec]

/-- `+flatten-need`: the registers of a need, head before tail, on every
state noun `G` (the gate reads none). -/
theorem comp_flatten_need (hc : CompIn ctx) (G : Noun) :
    ∀ ned : Need, nock (C fnBat (C ned.toNoun (C comp.door (C G ctx)))) fnBat
      = some (listNoun A (flattenNeed ned))
  | Need.none => by
    unfold fnBat; simp [nock_exec, Need.toNoun, Tag.none, flattenNeed, listNoun]
  | Need.this r => by
    unfold fnBat; simp [nock_exec, Need.toNoun, Tag.this, eqCode_atom, flattenNeed, listNoun]
  | Need.pair p q => by
    obtain ⟨u, v, hp⟩ := cd_need_cell p
    have ihp := comp_flatten_need hc G p
    have ihq := comp_flatten_need hc G q
    rw [hp] at ihp
    have hw := cd_weld A (flattenNeed p) (flattenNeed q)
    unfold fnBat at ihp ihq ⊢
    simp [nock_exec, Need.toNoun, hp, eqCode, hc, weld_arm, weld.arm_at, ihp, ihq, hw, flattenNeed]
  | Need.both r h t => by
    have ihh := comp_flatten_need hc G h
    have iht := comp_flatten_need hc G t
    have hw := cd_weld A (flattenNeed h) (flattenNeed t)
    unfold fnBat at ihh iht ⊢
    simp [nock_exec, Need.toNoun, Tag.both, eqCode_atom, hc, weld_arm, weld.arm_at,
      ihh, iht, hw, flattenNeed, listNoun]

end Compiler
end Formalization
