import lemmas.Compiler.CompForlLink
import lemmas.Hoon.UniIn

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

/-! ## `+copy-need-make-ops`

The arm is a loop over a work list `sin` of entries `|+[l r]` (copy `r` into
`l`), `&+~` (cons the two needs on top of `sout`) and `&+`[r]` (the same
with a register), with the ops in `ops`.  The model `copyNeed` is the same
walk as a recursion (`cnm_seg`, by induction on the first need).

Four `~?` debug prints sit in the loop: when the registers of a `%mov` are
equal the pill evaluates a `%slog` hint whose clue renders the registers
with the library's printer.  The link takes the branch where every test is
false: the registers of a move differ (`cnMeet`), and the registers of both
needs are below `re-gen`, so a fresh register differs from them (`cnLt`).
-/

def cnmL0 : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 6)))) (C (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 14))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 29)))) (C (A 1) (A 1))))) (C (C (C (C (A 0) (A 28)) (C (A 0) (A 30))) (C (A 0) (A 510))) (C (A 0) (A 0))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 24)))) (C (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 14))) (C (C (A 3) (C (A 0) (A 29))) (C (A 1) (A 1))))) (C (C (A 8) (C (C (C (A 0) (A 58)) (C (A 0) (A 28))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 57)))) (C (C (A 8) (C (C (A 9) (C (A 350) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))) (C (A 7) (C (C (A 0) (A 1)) (C (C (A 1) (A 0x68746f62)) (C (C (A 0) (A 115)) (C (A 0) (A 2))))))))) (C (A 0) (A 123)))) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 3)))))))))) (C (A 0) (A 0))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 100)))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (C (A 0) (A 51)) (C (A 0) (A 14)))) (C (A 10) (C (C (A 6) (C (A 0) (A 13))) (C (A 0) (A 1)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 102)))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (C (A 0) (A 50)) (C (A 0) (A 14)))) (C (A 10) (C (C (A 6) (C (A 0) (A 13))) (C (A 0) (A 1)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 100)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 102)))) (C (C (A 8) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 101)) (C (A 0) (A 103)))) (C (C (A 11) (C (C (A 0x676f6c73) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 9) (C (A 10238) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 158) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (C (A 0x6c6c6563) (C (C (A 0x6d6f7461) (C (A 0x736174) (C (A 0) (A 0x612d6c2d736968742d79706f63)))) (C (A 0x6c6c6563) (C (C (A 0x6d6f7461) (C (A 0x65727675) (A 0))) (C (A 0x6d6f7461) (C (A 0x65727675) (A 0)))))))) (C (C (A 1) (A 0x612d6c2d736968742d79706f63)) (C (C (A 0) (A 101)) (C (A 0) (A 103)))))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))))) (C (A 1) (A 0)))) (C (A 1) (A 0))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (C (C (A 1) (A 0x766f6d)) (C (C (A 0) (A 101)) (C (A 0) (A 103)))) (C (A 0) (A 30)))) (C (A 10) (C (C (A 14) (C (C (A 0) (A 50)) (C (A 0) (A 14)))) (C (A 10) (C (C (A 6) (C (A 0) (A 13))) (C (A 0) (A 1)))))))))))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 102))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (C (A 0) (A 51)) (C (A 0) (A 510))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 127)))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 1) (A 0x68746f62)) (C (C (A 0) (A 2)) (C (A 0) (A 115)))) (C (A 0) (A 1022)))))))))))))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 229)) (C (A 0) (A 10)))) (C (C (A 11) (C (C (A 0x676f6c73) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 9) (C (A 10238) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 158) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (C (A 0x6c6c6563) (C (C (A 0x6d6f7461) (C (A 0x736174) (C (A 0) (A 0x622d6c2d736968742d79706f63)))) (C (A 0x6c6c6563) (C (C (A 0x6d6f7461) (C (A 0x65727675) (A 0))) (C (A 0x6d6f7461) (C (A 0x65727675) (A 0)))))))) (C (C (A 1) (A 0x622d6c2d736968742d79706f63)) (C (C (A 0) (A 229)) (C (A 0) (A 10)))))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))))) (C (A 1) (A 0)))) (C (A 1) (A 0))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (C (C (A 1) (A 0x766f6d)) (C (C (A 0) (A 10)) (C (A 0) (A 229)))) (C (A 0) (A 62)))) (C (A 10) (C (C (A 14) (C (C (A 0) (A 2)) (C (A 0) (A 30)))) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 3))))))))))))))))))))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 102)))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 100))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (C (A 0) (A 50)) (C (A 0) (A 510))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 127)))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 1) (A 0x68746f62)) (C (C (A 0) (A 2)) (C (A 0) (A 114)))) (C (A 0) (A 1022)))))))))))))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 10)) (C (A 0) (A 231)))) (C (C (A 11) (C (C (A 0x676f6c73) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 9) (C (A 10238) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 158) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (C (A 0x6c6c6563) (C (C (A 0x6d6f7461) (C (A 0x736174) (C (A 0) (A 0x722d736968742d79706f63)))) (C (A 0x6c6c6563) (C (C (A 0x6d6f7461) (C (A 0x65727675) (A 0))) (C (A 0x6d6f7461) (C (A 0x65727675) (A 0)))))))) (C (C (A 1) (A 0x722d736968742d79706f63)) (C (C (A 0) (A 10)) (C (A 0) (A 231)))))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))))) (C (A 1) (A 0)))) (C (A 1) (A 0))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (C (C (A 1) (A 0x766f6d)) (C (C (A 0) (A 10)) (C (A 0) (A 231)))) (C (A 0) (A 62)))) (C (A 10) (C (C (A 14) (C (C (A 0) (A 2)) (C (A 0) (A 30)))) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 3)))))))))))))))))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 100)))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 102))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (C (A 0) (A 51)) (C (A 0) (A 510))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 127)))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 1) (A 0x68746f62)) (C (C (A 0) (A 2)) (C (A 0) (A 115)))) (C (A 0) (A 1022)))))))))))))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 458)) (C (A 0) (A 10)))) (C (C (A 11) (C (C (A 0x676f6c73) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 9) (C (A 10238) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 158) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (C (A 0x6c6c6563) (C (C (A 0x6d6f7461) (C (A 0x736174) (C (A 0) (A 0x68746f622d79706f63)))) (C (A 0x6c6c6563) (C (C (A 0x6d6f7461) (C (A 0x65727675) (A 0))) (C (A 0x6d6f7461) (C (A 0x65727675) (A 0)))))))) (C (C (A 1) (A 0x68746f622d79706f63)) (C (C (A 0) (A 458)) (C (A 0) (A 10)))))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))))) (C (A 1) (A 0)))) (C (A 1) (A 0))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (C (C (A 1) (A 0x766f6d)) (C (C (A 0) (A 10)) (C (A 0) (A 458)))) (C (A 0) (A 62)))) (C (A 10) (C (C (A 6) (C (C (C (A 1) (A 1)) (C (C (A 0) (A 918)) (C (A 0) (A 22)))) (C (C (C (A 1) (A 1)) (C (C (A 0) (A 919)) (C (A 0) (A 23)))) (C (C (C (A 1) (A 0)) (C (C (A 1) (A 0)) (C (A 0) (A 10)))) (C (A 0) (A 29)))))) (C (A 0) (A 3)))))))))))))))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 102))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (C (A 1) (A 1)) (C (C (A 0) (A 100)) (C (A 0) (A 414)))) (C (C (C (A 1) (A 1)) (C (C (A 0) (A 101)) (C (A 0) (A 415)))) (C (C (C (A 1) (A 0)) (C (C (A 1) (A 0)) (C (A 0) (A 206)))) (C (A 0) (A 13)))))) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (C (A 1) (A 1)) (C (C (A 0) (A 100)) (C (A 0) (A 102)))) (C (C (C (A 1) (A 1)) (C (C (A 0) (A 101)) (C (A 0) (A 103)))) (C (C (A 1) (C (A 0) (A 0))) (C (A 0) (A 13)))))) (C (A 0) (A 1))))))))))))))))))))))))))))))))))

def cnmBat : Noun :=
  (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (C (C (A 1) (A 1)) (C (C (A 0) (A 60)) (C (A 0) (A 61)))) (C (A 1) (A 0))) (C (A 8) (C (C (A 1) cnmL0) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))))))

def cnmArm : Noun :=
  (C (A 7) (C (C (A 8) (C (C (A 1) (C (C (A 0x656e6f6e) (A 0)) (C (A 0x656e6f6e) (A 0)))) (C (C (A 1) cnmBat) (C (A 0) (A 1))))) (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x73706f2d656b616d2d6465656e2d79706f632d706d6f63) (C (C (A 0) (A 0x7ffff)) (A 0))))) (C (A 0) (A 1))))))

/-- `+copy-need-make-ops` is at door axis `3452` (core axis `5500`). -/
theorem comp_cnm_at : slot? 3452 comp.door = some cnmArm := by kernel_rfl

/-- The arm `copy-need-make-ops` builds its gate. -/
theorem comp_cnm_arm (d : Noun) : nock d cnmArm =
    some (C cnmBat (C (C (C (A 0x656e6f6e) (A 0)) (C (A 0x656e6f6e) (A 0))) d)) := by
  unfold cnmArm; simp only [nock_exec]

/-- An entry of the work list. -/
inductive CnE where
  | work (l r : Need)
  | cons
  | both (x : Nat)

def CnE.toNoun : CnE → Noun
  | work l r => C (A 1) (C l.toNoun r.toNoun)
  | cons => C (A 0) (A 0)
  | both x => C (A 0) (C (A 0) (A x))

/-- Every register of a need is below `k`. -/
def cnLt (k : Nat) : Need → Prop
  | Need.pair p q => cnLt k p ∧ cnLt k q
  | Need.both r h t => r < k ∧ cnLt k h ∧ cnLt k t
  | Need.this r => r < k
  | Need.none => True

theorem cnLt_mono {k k' : Nat} (hk : k ≤ k') : ∀ n : Need, cnLt k n → cnLt k' n
  | Need.pair p q, ⟨h1, h2⟩ => ⟨cnLt_mono hk p h1, cnLt_mono hk q h2⟩
  | Need.both r h t, ⟨h0, h1, h2⟩ => ⟨by omega, cnLt_mono hk h h1, cnLt_mono hk t h2⟩
  | Need.this r, h => by simp only [cnLt] at h ⊢; omega
  | Need.none, _ => trivial

/-- The registers that a `%mov` of the walk joins differ (fresh registers
aside, which `cnLt` covers). -/
def cnMeet : Need → Need → Prop
  | Need.none, _ => True
  | _, Need.none => True
  | Need.this rl, Need.this rr => rl ≠ rr
  | Need.this rl, Need.both x _ _ => rl ≠ x
  | Need.this _, Need.pair _ _ => True
  | Need.both x _ _, Need.this rr => x ≠ rr
  | Need.pair _ _, Need.this _ => True
  | Need.both rl hl tl, Need.both x hr tr => rl ≠ x ∧ cnMeet hl hr ∧ cnMeet tl tr
  | Need.both _ hl tl, Need.pair p q => cnMeet hl p ∧ cnMeet tl q
  | Need.pair pl ql, Need.pair pr qr => cnMeet pl pr ∧ cnMeet ql qr
  | Need.pair pl ql, Need.both _ h t => cnMeet pl h ∧ cnMeet ql t

/-- The subject of the loop. -/
def cnT (x : GenRest) (ctx B S : Noun) (sin : List CnE) (sout : List Need) (ops : List Pole)
    (g : Gen (TreapMap mugF)) : Noun :=
  C cnmL0 (C (listNoun CnE.toNoun sin) (C (listNoun Need.toNoun sout) (C (listNoun Pole.toNoun ops)
    (C B (C S (C comp.door (C (genNoun g x) ctx)))))))

variable (x : GenRest) (B S : Noun)

theorem cnm_st_none_l (r : Need) (rest : List CnE) (sout : List Need) (ops : List Pole)
    (g : Gen (TreapMap mugF)) :
    nock (cnT x ctx B S (CnE.work Need.none r :: rest) sout ops g) cnmL0
      = nock (cnT x ctx B S rest (r :: sout) ops g) cnmL0 := by
  nock_open cnmL0
  simp [nock_exec, cnT, listNoun, CnE.toNoun, Need.toNoun, Tag.none]

theorem cnm_st_none_r (l : Need) (hl : l ≠ Need.none) (rest : List CnE) (sout : List Need)
    (ops : List Pole) (g : Gen (TreapMap mugF)) :
    nock (cnT x ctx B S (CnE.work l Need.none :: rest) sout ops g) cnmL0
      = nock (cnT x ctx B S rest (l :: sout) ops g) cnmL0 := by
  nock_open cnmL0
  cases l with
  | none => exact absurd rfl hl
  | this r => simp [nock_exec, cnT, listNoun, CnE.toNoun, Need.toNoun, Tag.none, Tag.this]
  | both r h t => simp [nock_exec, cnT, listNoun, CnE.toNoun, Need.toNoun, Tag.none, Tag.both]
  | pair p q =>
    obtain ⟨u, v, hp⟩ := cd_need_cell p
    simp [nock_exec, cnT, listNoun, CnE.toNoun, Need.toNoun, Tag.none, hp, eqCode]

theorem cnm_st_this_this (rl rr : Nat) (hne : rl ≠ rr) (rest : List CnE) (sout : List Need)
    (ops : List Pole) (g : Gen (TreapMap mugF)) :
    nock (cnT x ctx B S (CnE.work (Need.this rl) (Need.this rr) :: rest) sout ops g) cnmL0
      = nock (cnT x ctx B S rest (Need.this rl :: sout) (Pole.mov rl rr :: ops) g) cnmL0 := by
  nock_open cnmL0
  simp [nock_exec, cnT, listNoun, CnE.toNoun, Need.toNoun, Pole.toNoun, Tag.this, Tag.mov,
    eqCode_atom, hne]

theorem cnm_st_this_both (rl r : Nat) (h t : Need) (hne : rl ≠ r) (rest : List CnE)
    (sout : List Need) (ops : List Pole) (g : Gen (TreapMap mugF)) :
    nock (cnT x ctx B S (CnE.work (Need.this rl) (Need.both r h t) :: rest) sout ops g) cnmL0
      = nock (cnT x ctx B S rest (Need.both r h t :: sout) (Pole.mov r rl :: ops) g) cnmL0 := by
  nock_open cnmL0
  simp [nock_exec, cnT, listNoun, CnE.toNoun, Need.toNoun, Pole.toNoun, Tag.this, Tag.both,
    Tag.mov, eqCode_atom, hne]

theorem cnm_st_this_pair (rl : Nat) (p q : Need) (g : Gen (TreapMap mugF)) (hne : rl ≠ g.re) (rest : List CnE)
    (sout : List Need) (ops : List Pole) :
    nock (cnT x ctx B S (CnE.work (Need.this rl) (Need.pair p q) :: rest) sout ops g) cnmL0
      = nock (cnT x ctx B S rest (Need.both g.re p q :: sout) (Pole.mov g.re rl :: ops)
          { g with re := g.re + 1 }) cnmL0 := by
  obtain ⟨u, v, hp⟩ := cd_need_cell p
  nock_open cnmL0
  simp [nock_exec, cnT, listNoun, CnE.toNoun, Need.toNoun, Pole.toNoun, Tag.this, Tag.both,
    Tag.mov, eqCode_atom, hne, hp, eqCode, comp_re' ctx x]

theorem cnm_st_both_this (r rr : Nat) (h t : Need) (hne : r ≠ rr) (rest : List CnE)
    (sout : List Need) (ops : List Pole) (g : Gen (TreapMap mugF)) :
    nock (cnT x ctx B S (CnE.work (Need.both r h t) (Need.this rr) :: rest) sout ops g) cnmL0
      = nock (cnT x ctx B S rest (Need.both r h t :: sout) (Pole.mov r rr :: ops) g) cnmL0 := by
  nock_open cnmL0
  simp [nock_exec, cnT, listNoun, CnE.toNoun, Need.toNoun, Pole.toNoun, Tag.this, Tag.both,
    Tag.mov, eqCode_atom, hne]

theorem cnm_st_pair_this (rr : Nat) (p q : Need) (g : Gen (TreapMap mugF)) (hne : g.re ≠ rr) (rest : List CnE)
    (sout : List Need) (ops : List Pole) :
    nock (cnT x ctx B S (CnE.work (Need.pair p q) (Need.this rr) :: rest) sout ops g) cnmL0
      = nock (cnT x ctx B S rest (Need.both g.re p q :: sout) (Pole.mov g.re rr :: ops)
          { g with re := g.re + 1 }) cnmL0 := by
  obtain ⟨u, v, hp⟩ := cd_need_cell p
  nock_open cnmL0
  simp [nock_exec, cnT, listNoun, CnE.toNoun, Need.toNoun, Pole.toNoun, Tag.this, Tag.both,
    Tag.mov, eqCode_atom, hne, hp, eqCode, comp_re' ctx x]

theorem cnm_st_both_both (rl x' : Nat) (hl tl hr tr : Need) (hne : rl ≠ x') (rest : List CnE)
    (sout : List Need) (ops : List Pole) (g : Gen (TreapMap mugF)) :
    nock (cnT x ctx B S (CnE.work (Need.both rl hl tl) (Need.both x' hr tr) :: rest) sout ops g) cnmL0
      = nock (cnT x ctx B S (CnE.work hl hr :: CnE.work tl tr :: CnE.both x' :: rest) sout
          (Pole.mov x' rl :: ops) g) cnmL0 := by
  nock_open cnmL0
  simp [nock_exec, cnT, listNoun, CnE.toNoun, Need.toNoun, Pole.toNoun, Tag.this, Tag.both,
    Tag.mov, eqCode_atom, hne]

theorem cnm_st_both_pair (rl : Nat) (hl tl p q : Need) (g : Gen (TreapMap mugF)) (hne : rl ≠ g.re) (rest : List CnE)
    (sout : List Need) (ops : List Pole) :
    nock (cnT x ctx B S (CnE.work (Need.both rl hl tl) (Need.pair p q) :: rest) sout ops g) cnmL0
      = nock (cnT x ctx B S (CnE.work hl p :: CnE.work tl q :: CnE.both g.re :: rest) sout
          (Pole.mov g.re rl :: ops) { g with re := g.re + 1 }) cnmL0 := by
  obtain ⟨u, v, hp⟩ := cd_need_cell p
  nock_open cnmL0
  simp [nock_exec, cnT, listNoun, CnE.toNoun, Need.toNoun, Pole.toNoun, Tag.this, Tag.both,
    Tag.mov, eqCode_atom, hne, hp, eqCode, comp_re' ctx x]

theorem cnm_st_pair_pair (pl ql pr qr : Need) (rest : List CnE)
    (sout : List Need) (ops : List Pole) (g : Gen (TreapMap mugF)) :
    nock (cnT x ctx B S (CnE.work (Need.pair pl ql) (Need.pair pr qr) :: rest) sout ops g) cnmL0
      = nock (cnT x ctx B S (CnE.work pl pr :: CnE.work ql qr :: CnE.cons :: rest) sout ops g)
          cnmL0 := by
  obtain ⟨u, v, hp⟩ := cd_need_cell pl
  obtain ⟨u', v', hp'⟩ := cd_need_cell pr
  nock_open cnmL0
  simp [nock_exec, cnT, listNoun, CnE.toNoun, Need.toNoun, Pole.toNoun, Tag.this, Tag.both,
    hp, hp', eqCode]

theorem cnm_st_pair_both (pl ql : Need) (x' : Nat) (h t : Need) (rest : List CnE)
    (sout : List Need) (ops : List Pole) (g : Gen (TreapMap mugF)) :
    nock (cnT x ctx B S (CnE.work (Need.pair pl ql) (Need.both x' h t) :: rest) sout ops g) cnmL0
      = nock (cnT x ctx B S (CnE.work pl h :: CnE.work ql t :: CnE.both x' :: rest) sout ops g)
          cnmL0 := by
  obtain ⟨u, v, hp⟩ := cd_need_cell pl
  nock_open cnmL0
  simp [nock_exec, cnT, listNoun, CnE.toNoun, Need.toNoun, Pole.toNoun, Tag.this, Tag.both,
    hp, eqCode]

theorem cnm_st_bothx (x' : Nat) (a b : Need) (rest : List CnE) (sout : List Need)
    (ops : List Pole) (g : Gen (TreapMap mugF)) :
    nock (cnT x ctx B S (CnE.both x' :: rest) (b :: a :: sout) ops g) cnmL0
      = nock (cnT x ctx B S rest (Need.both x' a b :: sout) ops g) cnmL0 := by
  nock_open cnmL0
  simp [nock_exec, cnT, listNoun, CnE.toNoun, Need.toNoun, Tag.both]

theorem cnm_st_cons (hl : CompLib ctx) (a b : Need) (rest : List CnE) (sout : List Need)
    (ops : List Pole) (g : Gen (TreapMap mugF)) :
    nock (cnT x ctx B S (CnE.cons :: rest) (b :: a :: sout) ops g) cnmL0
      = nock (cnT x ctx B S rest (consNeed a b :: sout) ops g) cnmL0 := by
  obtain ⟨K, hK, _, hcn⟩ := hl
  nock_open cnmL0
  simp [nock_exec, cnT, listNoun, CnE.toNoun, hK, hcn, cnArm, cn_gate]

theorem cnm_st_end (n : Need) (ops : List Pole) (g : Gen (TreapMap mugF)) :
    nock (cnT x ctx B S [] [n] ops g) cnmL0
      = some (C (C n.toNoun (listNoun Pole.toNoun ops)) (genNoun g x)) := by
  nock_open cnmL0
  simp [nock_exec, cnT, listNoun]

variable {x B S} in
/-- The walk of `+copy-need-make-ops` from an entry `|+[l r]`: the loop pops
the entry and pushes what `copyNeed` returns, with its ops and state. -/
theorem cnm_seg (hl : CompLib ctx) : ∀ (l r : Need) (rest : List CnE) (sout : List Need)
    (ops : List Pole) (g : Gen (TreapMap mugF)), cnLt g.re l → cnLt g.re r → cnMeet l r →
    ∃ n ops' g', copyNeed l r ops g = some ((n, ops'), g') ∧ g.re ≤ g'.re ∧
      nock (cnT x ctx B S (CnE.work l r :: rest) sout ops g) cnmL0
        = nock (cnT x ctx B S rest (n :: sout) ops' g') cnmL0 := by
  intro l
  induction l with
  | none =>
    intro r rest sout ops g _ _ _
    exact ⟨r, ops, g, by cases r <;> simp [copyNeed, pure, StateT.pure], Nat.le_refl _,
      cnm_st_none_l x B S r rest sout ops g⟩
  | this rl =>
    intro r rest sout ops g hlt hrt hm
    cases r with
    | none =>
      exact ⟨Need.this rl, ops, g, by simp [copyNeed, pure, StateT.pure], Nat.le_refl _,
        cnm_st_none_r x B S _ (by simp) rest sout ops g⟩
    | this rr =>
      exact ⟨Need.this rl, Pole.mov rl rr :: ops, g, by simp [copyNeed, pure, StateT.pure],
        Nat.le_refl _, cnm_st_this_this x B S rl rr hm rest sout ops g⟩
    | both r' h t =>
      exact ⟨Need.both r' h t, Pole.mov r' rl :: ops, g, by simp [copyNeed, pure, StateT.pure],
        Nat.le_refl _, cnm_st_this_both x B S rl r' h t hm rest sout ops g⟩
    | pair p q =>
      have hne : rl ≠ g.re := by simp only [cnLt] at hlt; omega
      exact ⟨Need.both g.re p q, Pole.mov g.re rl :: ops, { g with re := g.re + 1 },
        by simp [copyNeed, re, bind, StateT.bind, pure, StateT.pure], by simp,
        cnm_st_this_pair x B S rl p q g hne rest sout ops⟩
  | both rl hl tl ihh iht =>
    intro r rest sout ops g hlt hrt hm
    obtain ⟨h0, h1, h2⟩ := hlt
    cases r with
    | none =>
      exact ⟨Need.both rl hl tl, ops, g, by simp [copyNeed, pure, StateT.pure], Nat.le_refl _,
        cnm_st_none_r x B S _ (by simp) rest sout ops g⟩
    | this rr =>
      exact ⟨Need.both rl hl tl, Pole.mov rl rr :: ops, g, by simp [copyNeed, pure, StateT.pure],
        Nat.le_refl _, cnm_st_both_this x B S rl rr hl tl hm rest sout ops g⟩
    | both x' hr tr =>
      obtain ⟨hne, m1, m2⟩ := hm
      obtain ⟨_, r1, r2⟩ := hrt
      rw [cnm_st_both_both x B S rl x' hl tl hr tr hne]
      obtain ⟨a, ops1, g1, e1, le1, q1⟩ :=
        ihh hr (CnE.work tl tr :: CnE.both x' :: rest) sout (Pole.mov x' rl :: ops) g h1 r1 m1
      rw [q1]
      obtain ⟨b, ops2, g2, e2, le2, q2⟩ :=
        iht tr (CnE.both x' :: rest) (a :: sout) ops1 g1 (cnLt_mono le1 _ h2) (cnLt_mono le1 _ r2) m2
      rw [q2, cnm_st_bothx]
      exact ⟨Need.both x' a b, ops2, g2, by simp [copyNeed, e1, e2, bind, StateT.bind, pure,
        StateT.pure], Nat.le_trans le1 le2, rfl⟩
    | pair p q =>
      obtain ⟨m1, m2⟩ := hm
      obtain ⟨r1, r2⟩ := hrt
      have hne : rl ≠ g.re := by omega
      rw [cnm_st_both_pair x B S rl hl tl p q g hne]
      have hk : g.re ≤ g.re + 1 := by omega
      obtain ⟨a, ops1, g1, e1, le1, q1⟩ :=
        ihh p (CnE.work tl q :: CnE.both g.re :: rest) sout (Pole.mov g.re rl :: ops)
          { g with re := g.re + 1 } (cnLt_mono hk _ h1) (cnLt_mono hk _ r1) m1
      rw [q1]
      obtain ⟨b, ops2, g2, e2, le2, q2⟩ :=
        iht q (CnE.both g.re :: rest) (a :: sout) ops1 g1 (cnLt_mono (Nat.le_trans hk le1) _ h2)
          (cnLt_mono (Nat.le_trans hk le1) _ r2) m2
      rw [q2, cnm_st_bothx]
      exact ⟨Need.both g.re a b, ops2, g2, by simp [copyNeed, re, e1, e2, bind, StateT.bind, pure,
        StateT.pure], by simp at le1; omega, rfl⟩
  | pair pl ql ihp ihq =>
    intro r rest sout ops g hlt hrt hm
    obtain ⟨h1, h2⟩ := hlt
    cases r with
    | none =>
      exact ⟨Need.pair pl ql, ops, g, by simp [copyNeed, pure, StateT.pure], Nat.le_refl _,
        cnm_st_none_r x B S _ (by simp) rest sout ops g⟩
    | this rr =>
      have hne : g.re ≠ rr := by simp only [cnLt] at hrt; omega
      exact ⟨Need.both g.re pl ql, Pole.mov g.re rr :: ops, { g with re := g.re + 1 },
        by simp [copyNeed, re, bind, StateT.bind, pure, StateT.pure], by simp,
        cnm_st_pair_this x B S rr pl ql g hne rest sout ops⟩
    | both x' h t =>
      obtain ⟨m1, m2⟩ := hm
      obtain ⟨_, r1, r2⟩ := hrt
      rw [cnm_st_pair_both x B S pl ql x' h t]
      obtain ⟨a, ops1, g1, e1, le1, q1⟩ :=
        ihp h (CnE.work ql t :: CnE.both x' :: rest) sout ops g h1 r1 m1
      rw [q1]
      obtain ⟨b, ops2, g2, e2, le2, q2⟩ :=
        ihq t (CnE.both x' :: rest) (a :: sout) ops1 g1 (cnLt_mono le1 _ h2) (cnLt_mono le1 _ r2) m2
      rw [q2, cnm_st_bothx]
      exact ⟨Need.both x' a b, ops2, g2, by simp [copyNeed, e1, e2, bind, StateT.bind, pure,
        StateT.pure], Nat.le_trans le1 le2, rfl⟩
    | pair pr qr =>
      obtain ⟨m1, m2⟩ := hm
      obtain ⟨r1, r2⟩ := hrt
      rw [cnm_st_pair_pair x B S pl ql pr qr]
      obtain ⟨a, ops1, g1, e1, le1, q1⟩ :=
        ihp pr (CnE.work ql qr :: CnE.cons :: rest) sout ops g h1 r1 m1
      rw [q1]
      obtain ⟨b, ops2, g2, e2, le2, q2⟩ :=
        ihq qr (CnE.cons :: rest) (a :: sout) ops1 g1 (cnLt_mono le1 _ h2) (cnLt_mono le1 _ r2) m2
      rw [q2, cnm_st_cons x B S hl]
      exact ⟨consNeed a b, ops2, g2, by simp [copyNeed, e1, e2, bind, StateT.bind, pure,
        StateT.pure], Nat.le_trans le1 le2, rfl⟩

variable {x} in
/-- `+copy-need-make-ops`: the need of the copy and the ops, as `copyNeed`
from no ops, when the registers of the needs are below `re-gen` and no move
joins a register to itself. -/
theorem comp_copy_need (hl : CompLib ctx) (g : Gen (TreapMap mugF)) (l r : Need)
    (hlt : cnLt g.re l) (hrt : cnLt g.re r) (hm : cnMeet l r) :
    nock (C cnmBat (C (C l.toNoun r.toNoun) (compCore g x ctx))) cnmBat
      = (copyNeed l r [] g).map fun p => C (C p.1.1.toNoun (listNoun Pole.toNoun p.1.2)) (genNoun p.2 x) := by
  obtain ⟨n, ops', g', e, _, q⟩ := cnm_seg (x := x) (B := cnmBat)
    (S := C l.toNoun r.toNoun) hl l r [] [] [] g hlt hrt hm
  rw [cnm_st_end] at q
  simp only [cnT, listNoun, CnE.toNoun] at q
  rw [e]
  nock_open cnmBat
  simp [nock_exec, compCore, q]

/-! ## `+copy-lazy`

On fork-free lazy needs `[sure ~ ~]` the tests `=(~ fork.second)` and
`=(~ bond.second)` hold, so the fork and bond lists stay `~` and the merge
branches (the gates `clG0`, ..., `clG5`) are not reached.  The union of the
looks is `+uni:in` of layer 2, which computes `HoonSet.uni` of `csHoonSet`
(`cs_uni_is`, from `uni_in` of `Hoon/UniIn.lean` and `isSet_ext`).
-/

def clG5 : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 381) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2))))))))

def clG4 : Noun :=
  (C (A 0) (A 12))

def clG2 : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 381) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 56))) (C (A 0) (A 2))))))))

def clG1 : Noun :=
  (C (A 0) (A 24))

def clG3 : Noun :=
  (C clG4 (C (A 0) (A 6)))

def clG0 : Noun :=
  (C clG1 (C (A 0) (A 6)))

def clBat : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 5500) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 232)) (C (A 0) (A 236)))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 8) (C (C (A 9) (C (A 10990) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 60)) (C (A 0) (A 13)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 238)))) (C (C (C (A 0) (A 234)) (C (A 0) (A 62))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 234)))) (C (C (C (A 0) (A 238)) (C (A 0) (A 62))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 382) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 494)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))))) (C (C (A 1) clG0) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x5f7bffb) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1002)) (C (C (A 0) (A 254)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (A 7) (C (C (A 9) (C (A 2989) (C (A 0) (A 1023)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (A 0) (A 126))) (C (C (A 1) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 13))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 764) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 112))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (C (A 0) (A 28)) (C (A 0) (A 1022))) (C (A 6) (C (C (A 5) (C (C (A 0) (A 114)) (C (A 0) (A 22)))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 112)) (C (C (A 0) (A 113)) (C (A 0) (A 21))))) (C (A 0) (A 63)))))))) (C (A 7) (C (C (A 10) (C (C (A 2046) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 242)) (C (C (A 0) (A 243)) (C (A 0) (A 55))))) (C (A 0) (A 127)))))))) (C (A 7) (C (C (A 10) (C (C (A 4094) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (C (A 0) (A 496)) (C (A 0) (A 6))) (C (C (A 0) (A 498)) (C (A 0) (A 2)))) (C (A 0) (A 4094))))))))))))))))))) (C (A 0) (A 0))))))))))))) (C (A 0) (A 1)))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 767) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 2026)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))))) (C (C (A 1) clG1) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 9) (C (A 0xbef7f4) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7f5f) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 4078)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))))) (C (C (A 1) clG2) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2)))))))) (C (A 0) (A 510))))))))))))))))))))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 495)))) (C (C (C (A 0) (A 491)) (C (A 0) (A 126))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 491)))) (C (C (C (A 0) (A 495)) (C (A 0) (A 126))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 382) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1007)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))))) (C (C (A 1) clG3) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x5f7bffb) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 2027)) (C (C (A 0) (A 510)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (A 7) (C (C (A 9) (C (A 2742) (C (A 0) (A 2047)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (A 0) (A 254))) (C (C (A 1) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 13))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 764) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 56))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (C (A 0) (A 28)) (C (A 0) (A 2046))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 56)) (C (C (A 0) (A 57)) (C (A 0) (A 11))))) (C (A 0) (A 127)))))))) (C (A 7) (C (C (A 10) (C (C (A 4094) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 0) (A 120)) (C (A 0) (A 2))) (C (A 0) (A 4094))))))))))))))))))) (C (A 0) (A 1)))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 767) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 4075)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))))) (C (C (A 1) clG4) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 9) (C (A 0xbef7f4) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7f5f) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 8175)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))))) (C (C (A 1) clG5) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2)))))))) (C (A 0) (A 1022))))))))))))))))))))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (C (A 0) (A 28)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 174) (C (A 10) (C (C (A 6) (C (A 0) (A 2025))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 2029))) (C (A 0) (A 2))))))))) (C (C (A 0) (A 6)) (C (A 0) (A 2)))) (C (A 0) (A 254)))))))))))))))))))))))))))))))

def clArm : Noun :=
  (C (A 7) (C (C (A 8) (C (C (A 1) (C (A 0) (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))))) (C (C (A 1) clBat) (C (A 0) (A 1))))) (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x797a616c2d79706f632d706d6f63) (C (C (A 0) (A 0x7ffff)) (A 0))))) (C (A 0) (A 1))))))


/-- `+copy-lazy` is at door axis `1022` (core axis `1534`). -/
theorem comp_cl_at : slot? 1022 comp.door = some clArm := by kernel_rfl

/-- `+add-ops` at its door axis. -/
theorem comp_add_ops_at : slot? 6894 comp.door = some comp.add_ops.arm := by kernel_rfl

/-- The arm `copy-lazy` builds its gate. -/
theorem comp_cl_arm (d : Noun) : nock d clArm =
    some (C clBat (C (C (A 0) (C (lazyNoun (Sure.bunt : Sure CSet)) (lazyNoun (Sure.bunt : Sure CSet)))) d)) := by
  unfold clArm; simp [nock_exec, lazyNoun, Sure.toNoun, Sure.bunt, Need.toNoun, Tag.none, HoonSet.toNoun_empty]

/-- The arm `uni` of `+in` builds its gate, with the door's set as the bunt. -/
theorem cl_uni_arm (d : Noun) : nock d in.uni.arm =
    (slot? 6 d).map fun b => C in.uni.battery (C b d) := by
  unfold in.uni.arm; simp [nock_exec]; cases slot? 6 d <;> rfl

/-- What `+copy-lazy` assumes of `+uni:in` of layer 2: on the set nouns of
`csHoonSet` it computes the union. -/
def CsUniIs : Prop := ∀ a b : CSet,
  nock (C in.uni.battery (C (HoonSet.toNoun b) (C in.battery (C (HoonSet.toNoun a) layer2))))
    in.uni.battery = some (HoonSet.toNoun (HoonSet.uni a b))

/-- `+uni:in` of layer 2 on the set nouns of `csHoonSet` is the noun of the
union. -/
theorem cs_uni_is : CsUniIs := by
  intro a b
  obtain ⟨out, h, hs, hk⟩ := Hoon.uni_in layer2 gorIn_morIn_layer2 _ _ (cs_isSet a) (cs_isSet b)
  rw [h, isSet_ext hs (cs_isSet (HoonSet.uni a b))]
  intro k
  rw [hk, cs_has, cs_has, cs_has]
  constructor
  · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact ⟨y, (HoonSet.mem_uni a b y).2 (Or.inl hy), rfl⟩
    · exact ⟨y, (HoonSet.mem_uni a b y).2 (Or.inr hy), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    rcases (HoonSet.mem_uni a b y).1 hy with h | h
    · exact Or.inl ⟨y, h, rfl⟩
    · exact Or.inr ⟨y, h, rfl⟩

variable {x} in
/-- `+copy-lazy` on fork-free lazy needs, under the side conditions of
`comp_copy_need`. -/
theorem comp_copy_lazy (hc : CompIn ctx) (hl : CompLib ctx) (g : Gen (TreapMap mugF))
    (o : Nat) (f s : Sure CSet) (hlt : cnLt g.re f.ned) (hrt : cnLt g.re s.ned)
    (hm : cnMeet f.ned s.ned) :
    nock (C clBat (C (C (A o) (C (lazyNoun f) (lazyNoun s))) (compCore g x ctx))) clBat
      = (copyLazy o f s g).map fun p => C (lazyNoun p.1) (genNoun p.2 x) := by
  obtain ⟨n, ops, g1, e, _, _⟩ := cnm_seg (x := x) (B := cnmBat) (S := C (A 0) (A 0)) hl f.ned s.ned
    [] [] [] g hlt hrt hm
  have hcn := comp_copy_need (x := x) hl g f.ned s.ned hlt hrt hm
  rw [e] at hcn
  have hao := comp_add_ops x hc g1 o ops
  have huni := cs_uni_is f.lok s.lok
  have hD1 := comp_cnm_at
  have hD2 := comp_add_ops_at
  simp only [compCore] at hcn hao ⊢
  unfold clBat
  generalize comp.door = Dr at hD1 hD2 hcn hao ⊢
  cases ea : addOps (Map := TreapMap mugF) o ops g1 with
  | none =>
    rw [ea] at hao
    simp [nock_exec, lazyNoun, Sure.toNoun, hD1, hD2, comp_cnm_arm, comp_add_ops_arm, hcn, hao,
      copyLazy, e, ea, bind, StateT.bind]
  | some p =>
    obtain ⟨u, g2⟩ := p
    rw [ea] at hao
    simp [nock_exec, lazyNoun, Sure.toNoun, hD1, hD2, comp_cnm_arm, comp_add_ops_arm, hcn, hao,
      copyLazy, e, ea, bind, StateT.bind, hc, in_arm, in.arm_at, in.uni.arm_at, cl_uni_arm, huni,
      pure, StateT.pure]

/-! ## `+copy` -/

def cpBat : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 43690) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (A 0) (A 115)))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 1534) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (C (A 0) (A 242)) (C (A 0) (A 61))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 1) (A 0x7478656e)) (C (C (A 0) (A 2)) (C (C (A 1) (A 0)) (C (A 0) (A 6))))) (C (A 0) (A 126)))))))))))))))))))

def cpArm : Noun :=
  (C (A 7) (C (C (A 8) (C (C (A 1) (C (C (A 0x7478656e) (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))) (C (A 0) (A 0)))) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))))) (C (C (A 1) cpBat) (C (A 0) (A 1))))) (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x79706f632d706d6f63) (C (C (A 0) (A 0x7ffff)) (A 0))))) (C (A 0) (A 1))))))


/-- `+copy` is at door axis `220590` (core axis `351662`). -/
theorem comp_cp_at : slot? 220590 comp.door = some cpArm := by kernel_rfl

/-- `+emit` at its door axis. -/
theorem comp_emit_at : slot? 27306 comp.door = some comp.emit.arm := by kernel_rfl

variable {x} in
/-- `+copy`: `+emit` of `[~ ~ %hop then.first]`, then `+copy-lazy` into the
new block, on fork-free lazy needs, with the side conditions of
`comp_copy_need` on the sure needs. -/
theorem comp_copy (hc : CompIn ctx) (hl : CompLib ctx) (g : Gen (TreapMap mugF))
    (first : Next CSet) (second : Sure CSet) (hlt : cnLt g.re first.laz.ned)
    (hrt : cnLt g.re second.ned) (hm : cnMeet first.laz.ned second.ned) :
    nock (C cpBat (C (C first.goal.toNoun (lazyNoun second)) (compCore g x ctx))) cpBat
      = (copy first second g).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  obtain ⟨laz, th⟩ := first
  have he := cf_emit (x := x) hc g ⟨[], [], Termin.hop th⟩
  simp only [Blob.toNoun, listNoun, Termin.toNoun, Tag.hop, Jmp.toNoun] at he
  have hre := cf_emitG_re ⟨[], [], Termin.hop th⟩ g
  have hcl := comp_copy_lazy (x := x) hc hl (cfEmitG ⟨[], [], Termin.hop th⟩ g) g.bo laz second
    (by rw [hre]; exact hlt) (by rw [hre]; exact hrt) hm
  have hD1 := comp_cp_at
  have hD2 := comp_emit_at
  have hD3 := comp_cl_at
  simp only [compCore] at hcl ⊢
  unfold cpBat
  generalize comp.door = Dr at hD1 hD2 hD3 he hcl ⊢
  cases ec : copyLazy (Map := TreapMap mugF) g.bo laz second (cfEmitG ⟨[], [], Termin.hop th⟩ g) with
  | none =>
    rw [ec] at hcl
    simp [nock_exec, Next.goal, CGoal.toNoun, hD2, hD3, comp_emit_arm, he, comp_cl_arm, hcl, copy,
      cf_emit_g, ec, bind, StateT.bind, Jmp.toNoun]
  | some p =>
    obtain ⟨l2, g2⟩ := p
    rw [ec] at hcl
    simp [nock_exec, Next.goal, CGoal.toNoun, hD2, hD3, comp_emit_arm, he, comp_cl_arm, hcl, copy,
      cf_emit_g, ec, bind, StateT.bind, pure, StateT.pure, Jmp.toNoun, jmp0, listNoun]

/-! ## `+sure-require-look`

`~(rep in lok.sur)` with a gate whose accumulator starts at `[ned.sur gen]`
(the bunt of `_ned.sur` is `ned.sur`), and in the gate a trap down each
looked-at axis (`lookPath`).  The rep visits the looks in the pre-order of
the treap, which is `HoonSet.toList` of `csHoonSet` (`cs_preorder`).
-/

def srlL0 : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 28)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 116)))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 63)))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 1) (A 0x73696874)) (C (A 0) (A 2))) (C (A 0) (A 510))))))))))) (C (C (A 0) (A 58)) (C (A 0) (A 254)))))) (C (A 8) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 116)))) (C (C (C (A 1) (A 0)) (C (A 7) (C (C (A 1) (C (A 0x656e6f6e) (A 0))) (C (C (A 0) (A 1)) (C (A 0) (A 1)))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 116)))) (C (C (C (C (A 1) (A 0)) (C (A 0) (A 117))) (C (A 7) (C (C (A 1) (C (A 0x656e6f6e) (A 0))) (C (C (A 0) (A 1)) (C (A 0) (A 1)))))) (C (A 6) (C (C (A 3) (C (A 0) (A 116))) (C (C (C (A 1) (A 0)) (C (A 0) (A 58))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 116))))) (C (C (C (A 1) (A 0)) (C (A 0) (A 234))) (C (A 7) (C (C (A 0) (A 58)) (C (C (A 0) (A 14)) (C (A 0) (A 15))))))))))))))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 22) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 124))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 2)) (C (A 0) (A 2)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 58) (C (A 0) (A 10))) (C (A 10) (C (C (A 28) (C (A 8) (C (C (A 9) (C (A 47) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 124))) (C (A 0) (A 2))))))))) (C (A 0) (A 3)))))))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 0) (A 2)) (C (A 0) (A 27))) (C (A 0) (A 1022))))))))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 3)) (C (A 0) (A 2))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 58) (C (A 0) (A 11))) (C (A 10) (C (C (A 28) (C (A 8) (C (C (A 9) (C (A 47) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 124))) (C (A 0) (A 2))))))))) (C (A 0) (A 3)))))))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 0) (A 26)) (C (A 0) (A 2))) (C (A 0) (A 1022)))))))))))))))))))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 350) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 12)) (C (A 0) (A 13)))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 28)))) (C (C (C (A 0) (A 2)) (C (A 0) (A 2046))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 4))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (C (C (A 1) (A 0x73696874)) (C (A 0) (A 57))) (C (A 0) (A 2046))) (C (C (C (A 1) (A 0x68746f62)) (C (C (A 0) (A 57)) (C (A 0) (A 2)))) (C (A 0) (A 2046))))))))))))))))))))))))

def srlG : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 27))) (C (A 0) (A 1)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 12)))) (C (C (C (A 0) (A 26)) (C (A 0) (A 126))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 12)))) (C (C (A 0) (A 0)) (C (A 8) (C (C (A 1) srlL0) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))))))))

def srlBat : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 383) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (A 1) (A 0)) (C (C (A 0) (A 12)) (C (A 0) (A 30)))) (C (C (A 1) srlG) (C (A 0) (A 1)))))))) (C (A 0) (A 2))))))))

def srlArm : Noun :=
  (C (A 7) (C (C (A 8) (C (C (A 1) (C (C (A 0x656e6f6e) (A 0)) (A 0))) (C (C (A 1) srlBat) (C (A 0) (A 1))))) (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x6b6f6f6c2d657269757165722d657275732d706d6f63) (C (C (A 0) (A 0x7ffff)) (A 0))))) (C (A 0) (A 1))))))

/-- `+sure-require-look` is at door axis `887` (core axis `1399`). -/
theorem comp_srl_at : slot? 887 comp.door = some srlArm := by kernel_rfl

/-- The subject of the trap of the gate of the `rep`. -/
def srlT (x : GenRest) (ctx B SUR GI : Noun) (axe : Nat) (ned : Need) (g : Gen (TreapMap mugF)) :
    Noun :=
  C srlL0 (C srlG (C (C (A axe) (C ned.toNoun GI)) (C B (C SUR (C comp.door (C (genNoun g x) ctx))))))

theorem srl_wrap_none (n : Need) : wrapN Option.none n = n := rfl

theorem srl_cons_cases (a b : Need) :
    (a = Need.none ∧ b = Need.none ∧ consNeed a b = Need.none) ∨
      (¬ (a = Need.none ∧ b = Need.none) ∧ consNeed a b = Need.pair a b) := by
  by_cases h : a = Need.none ∧ b = Need.none
  · exact Or.inl ⟨h.1, h.2, by simp [consNeed, h]⟩
  · exact Or.inr ⟨h, by simp [consNeed, h]⟩

variable {x} in
/-- The trap of `+sure-require-look` is `lookPath`, on every axis from `1`. -/
theorem srl_loop (hc : CompIn ctx) (hl : CompLib ctx) (B SUR GI : Noun) :
    ∀ axe, 1 ≤ axe → ∀ (ned : Need) (g : Gen (TreapMap mugF)),
    nock (srlT x ctx B SUR GI axe ned g) srlL0
      = (lookPath ned axe g).map fun p => C p.1.toNoun (genNoun p.2 x) := by
  obtain ⟨K, hK, _, hcn⟩ := hl
  have hl1 := cf_layer1 hc
  have har := cf_arith
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
    intro ha ned g
    by_cases a1 : axe = 1
    · subst a1
      nock_open srlL0
      rw [lookPath.eq_def]
      cases ned with
      | none => simp [nock_exec, srlT, Need.toNoun, Tag.none, Tag.this, comp_re' ctx x, re, bind,
          StateT.bind, pure, StateT.pure]
      | this r => simp [nock_exec, srlT, Need.toNoun, Tag.none, Tag.this, pure, StateT.pure]
      | both r h t => simp [nock_exec, srlT, Need.toNoun, Tag.none, Tag.both, pure, StateT.pure]
      | pair p q =>
        obtain ⟨u, v, hp⟩ := cd_need_cell p
        simp [nock_exec, srlT, Need.toNoun, hp, eqCode, pure, StateT.pure]
    · have h2 : 2 ≤ axe := by omega
      have hcap := cap_gate layer1 har.2.2.2 axe h2
      have hmas := mas_gate layer1 har axe h2
      have hm1 : 1 ≤ masF axe := masF_pos axe h2
      have ihm := ih (masF axe) (by rw [masF_eq_mas]; exact mas_lt axe h2) hm1
      have hne : ¬ (1 = axe) := by omega
      have hna : ¬ (axe ≤ 1) := by omega
      nock_open srlL0
      rw [lookPath.eq_def]
      rcases capF_cases axe h2 with hc2 | hc3
      · cases ned with
        | none =>
          have IH := ihm Need.none g
          simp only [srlT, Need.toNoun, Tag.none] at IH
          try simp only [hp0] at IH
          cases e : lookPath (Map := TreapMap mugF) Need.none (masF axe) g with
          | none =>
            rw [e] at IH
            have hcn0 := True.intro
            have h3 := True.intro
            simp [nock_exec, srlT, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc2, mas_arm, mas.arm_at,
                hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, IH, e,
                split3, bind, StateT.bind, hK, hcn, cnArm, hcn0, h3, wrapN, pure, StateT.pure, eqCode]
          | some pr =>
            obtain ⟨x', g'⟩ := pr
            rw [e] at IH
            have hcn0 := cn_gate K x' Need.none
            rcases srl_cons_cases x' Need.none with ⟨h1, h1b, h3⟩ | ⟨h1, h3⟩
            · rw [h3] at hcn0
              simp only [h1, h1b, Need.toNoun, Tag.none] at hcn0
              try simp only [hp0] at hcn0
              simp [consNeed, nock_exec, srlT, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc2, mas_arm, mas.arm_at,
                hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, IH, e,
                split3, bind, StateT.bind, hK, hcn, cnArm, hcn0, h3, wrapN, pure, StateT.pure, eqCode, h1, h1b]
            · rw [h3] at hcn0
              simp only [Need.toNoun, Tag.none] at hcn0
              obtain ⟨u1, v1, hp1⟩ := cd_need_cell x'
              try simp only [hp0] at hcn0
              try simp only [hp1] at hcn0
              simp [nock_exec, srlT, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc2, mas_arm, mas.arm_at,
                hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, IH, e,
                split3, bind, StateT.bind, hK, hcn, cnArm, hcn0, h3, wrapN, pure, StateT.pure, eqCode, hp1]
        | this r =>
          have IH := ihm Need.none g
          simp only [srlT, Need.toNoun, Tag.none] at IH
          try simp only [hp0] at IH
          cases e : lookPath (Map := TreapMap mugF) Need.none (masF axe) g with
          | none =>
            rw [e] at IH
            have hcn0 := True.intro
            have h3 := True.intro
            simp [nock_exec, srlT, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc2, mas_arm, mas.arm_at,
                hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, IH, e,
                split3, bind, StateT.bind, hK, hcn, cnArm, hcn0, h3, wrapN, pure, StateT.pure, eqCode]
          | some pr =>
            obtain ⟨x', g'⟩ := pr
            rw [e] at IH
            have hcn0 := cn_gate K x' Need.none
            rcases srl_cons_cases x' Need.none with ⟨h1, h1b, h3⟩ | ⟨h1, h3⟩
            · rw [h3] at hcn0
              simp only [h1, h1b, Need.toNoun, Tag.none] at hcn0
              try simp only [hp0] at hcn0
              simp [consNeed, nock_exec, srlT, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc2, mas_arm, mas.arm_at,
                hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, IH, e,
                split3, bind, StateT.bind, hK, hcn, cnArm, hcn0, h3, wrapN, pure, StateT.pure, eqCode, h1, h1b]
            · rw [h3] at hcn0
              simp only [Need.toNoun, Tag.none] at hcn0
              obtain ⟨u1, v1, hp1⟩ := cd_need_cell x'
              try simp only [hp0] at hcn0
              try simp only [hp1] at hcn0
              simp [nock_exec, srlT, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc2, mas_arm, mas.arm_at,
                hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, IH, e,
                split3, bind, StateT.bind, hK, hcn, cnArm, hcn0, h3, wrapN, pure, StateT.pure, eqCode, hp1]
        | pair p q =>
          obtain ⟨u0, v0, hp0⟩ := cd_need_cell p
          have IH := ihm p g
          simp only [srlT, Need.toNoun, Tag.none] at IH
          try simp only [hp0] at IH
          cases e : lookPath (Map := TreapMap mugF) p (masF axe) g with
          | none =>
            rw [e] at IH
            have hcn0 := True.intro
            have h3 := True.intro
            simp [nock_exec, srlT, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc2, mas_arm, mas.arm_at,
                hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, IH, e,
                split3, bind, StateT.bind, hK, hcn, cnArm, hcn0, h3, wrapN, pure, StateT.pure, eqCode, hp0]
          | some pr =>
            obtain ⟨x', g'⟩ := pr
            rw [e] at IH
            have hcn0 := cn_gate K x' q
            rcases srl_cons_cases x' q with ⟨h1, h1b, h3⟩ | ⟨h1, h3⟩
            · rw [h3] at hcn0
              simp only [h1, h1b, Need.toNoun, Tag.none] at hcn0
              try simp only [hp0] at hcn0
              simp [consNeed, nock_exec, srlT, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc2, mas_arm, mas.arm_at,
                hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, IH, e,
                split3, bind, StateT.bind, hK, hcn, cnArm, hcn0, h3, wrapN, pure, StateT.pure, eqCode, hp0, h1, h1b]
            · rw [h3] at hcn0
              simp only [Need.toNoun, Tag.none] at hcn0
              obtain ⟨u1, v1, hp1⟩ := cd_need_cell x'
              try simp only [hp0] at hcn0
              try simp only [hp1] at hcn0
              simp [nock_exec, srlT, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc2, mas_arm, mas.arm_at,
                hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, IH, e,
                split3, bind, StateT.bind, hK, hcn, cnArm, hcn0, h3, wrapN, pure, StateT.pure, eqCode, hp0, hp1]
        | both r hh tt =>
          have IH := ihm hh g
          simp only [srlT, Need.toNoun, Tag.none] at IH
          try simp only [hp0] at IH
          cases e : lookPath (Map := TreapMap mugF) hh (masF axe) g with
          | none =>
            rw [e] at IH
            have hcn0 := True.intro
            have h3 := True.intro
            simp [nock_exec, srlT, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc2, mas_arm, mas.arm_at,
                hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, IH, e,
                split3, bind, StateT.bind, hK, hcn, cnArm, hcn0, h3, wrapN, pure, StateT.pure, eqCode]
          | some pr =>
            obtain ⟨x', g'⟩ := pr
            rw [e] at IH
            have hcn0 := cn_gate K x' tt
            rcases srl_cons_cases x' tt with ⟨h1, h1b, h3⟩ | ⟨h1, h3⟩
            · rw [h3] at hcn0
              simp only [h1, h1b, Need.toNoun, Tag.none] at hcn0
              try simp only [hp0] at hcn0
              simp [consNeed, nock_exec, srlT, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc2, mas_arm, mas.arm_at,
                hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, IH, e,
                split3, bind, StateT.bind, hK, hcn, cnArm, hcn0, h3, wrapN, pure, StateT.pure, eqCode, h1, h1b]
            · rw [h3] at hcn0
              simp only [Need.toNoun, Tag.none] at hcn0
              obtain ⟨u1, v1, hp1⟩ := cd_need_cell x'
              try simp only [hp0] at hcn0
              try simp only [hp1] at hcn0
              simp [nock_exec, srlT, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc2, mas_arm, mas.arm_at,
                hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, IH, e,
                split3, bind, StateT.bind, hK, hcn, cnArm, hcn0, h3, wrapN, pure, StateT.pure, eqCode, hp1]
      · cases ned with
        | none =>
          have IH := ihm Need.none g
          simp only [srlT, Need.toNoun, Tag.none] at IH
          try simp only [hp0] at IH
          cases e : lookPath (Map := TreapMap mugF) Need.none (masF axe) g with
          | none =>
            rw [e] at IH
            have hcn0 := True.intro
            have h3 := True.intro
            simp [nock_exec, srlT, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc3, mas_arm, mas.arm_at,
                hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, IH, e,
                split3, bind, StateT.bind, hK, hcn, cnArm, hcn0, h3, wrapN, pure, StateT.pure, eqCode]
          | some pr =>
            obtain ⟨x', g'⟩ := pr
            rw [e] at IH
            have hcn0 := cn_gate K Need.none x'
            rcases srl_cons_cases Need.none x' with ⟨h1, h1b, h3⟩ | ⟨h1, h3⟩
            · rw [h3] at hcn0
              simp only [h1, h1b, Need.toNoun, Tag.none] at hcn0
              try simp only [hp0] at hcn0
              simp [consNeed, nock_exec, srlT, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc3, mas_arm, mas.arm_at,
                hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, IH, e,
                split3, bind, StateT.bind, hK, hcn, cnArm, hcn0, h3, wrapN, pure, StateT.pure, eqCode, h1, h1b]
            · rw [h3] at hcn0
              simp only [Need.toNoun, Tag.none] at hcn0
              obtain ⟨u1, v1, hp1⟩ := cd_need_cell Need.none
              try simp only [hp0] at hcn0
              try simp only [hp1] at hcn0
              simp [nock_exec, srlT, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc3, mas_arm, mas.arm_at,
                hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, IH, e,
                split3, bind, StateT.bind, hK, hcn, cnArm, hcn0, h3, wrapN, pure, StateT.pure, eqCode, hp1]
        | this r =>
          have IH := ihm Need.none g
          simp only [srlT, Need.toNoun, Tag.none] at IH
          try simp only [hp0] at IH
          cases e : lookPath (Map := TreapMap mugF) Need.none (masF axe) g with
          | none =>
            rw [e] at IH
            have hcn0 := True.intro
            have h3 := True.intro
            simp [nock_exec, srlT, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc3, mas_arm, mas.arm_at,
                hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, IH, e,
                split3, bind, StateT.bind, hK, hcn, cnArm, hcn0, h3, wrapN, pure, StateT.pure, eqCode]
          | some pr =>
            obtain ⟨x', g'⟩ := pr
            rw [e] at IH
            have hcn0 := cn_gate K Need.none x'
            rcases srl_cons_cases Need.none x' with ⟨h1, h1b, h3⟩ | ⟨h1, h3⟩
            · rw [h3] at hcn0
              simp only [h1, h1b, Need.toNoun, Tag.none] at hcn0
              try simp only [hp0] at hcn0
              simp [consNeed, nock_exec, srlT, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc3, mas_arm, mas.arm_at,
                hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, IH, e,
                split3, bind, StateT.bind, hK, hcn, cnArm, hcn0, h3, wrapN, pure, StateT.pure, eqCode, h1, h1b]
            · rw [h3] at hcn0
              simp only [Need.toNoun, Tag.none] at hcn0
              obtain ⟨u1, v1, hp1⟩ := cd_need_cell Need.none
              try simp only [hp0] at hcn0
              try simp only [hp1] at hcn0
              simp [nock_exec, srlT, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc3, mas_arm, mas.arm_at,
                hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, IH, e,
                split3, bind, StateT.bind, hK, hcn, cnArm, hcn0, h3, wrapN, pure, StateT.pure, eqCode, hp1]
        | pair p q =>
          obtain ⟨u0, v0, hp0⟩ := cd_need_cell p
          have IH := ihm q g
          simp only [srlT, Need.toNoun, Tag.none] at IH
          try simp only [hp0] at IH
          cases e : lookPath (Map := TreapMap mugF) q (masF axe) g with
          | none =>
            rw [e] at IH
            have hcn0 := True.intro
            have h3 := True.intro
            simp [nock_exec, srlT, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc3, mas_arm, mas.arm_at,
                hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, IH, e,
                split3, bind, StateT.bind, hK, hcn, cnArm, hcn0, h3, wrapN, pure, StateT.pure, eqCode, hp0]
          | some pr =>
            obtain ⟨x', g'⟩ := pr
            rw [e] at IH
            have hcn0 := cn_gate K p x'
            rcases srl_cons_cases p x' with ⟨h1, h1b, h3⟩ | ⟨h1, h3⟩
            · rw [h3] at hcn0
              simp only [h1, h1b, Need.toNoun, Tag.none] at hcn0
              try simp only [hp0] at hcn0
              simp [consNeed, nock_exec, srlT, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc3, mas_arm, mas.arm_at,
                hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, IH, e,
                split3, bind, StateT.bind, hK, hcn, cnArm, hcn0, h3, wrapN, pure, StateT.pure, eqCode, hp0, h1, h1b]
            · rw [h3] at hcn0
              simp only [Need.toNoun, Tag.none] at hcn0
              obtain ⟨u1, v1, hp1⟩ := cd_need_cell p
              try simp only [hp0] at hcn0
              try simp only [hp1] at hcn0
              simp [nock_exec, srlT, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc3, mas_arm, mas.arm_at,
                hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, IH, e,
                split3, bind, StateT.bind, hK, hcn, cnArm, hcn0, h3, wrapN, pure, StateT.pure, eqCode, hp0, hp1]
        | both r hh tt =>
          have IH := ihm tt g
          simp only [srlT, Need.toNoun, Tag.none] at IH
          try simp only [hp0] at IH
          cases e : lookPath (Map := TreapMap mugF) tt (masF axe) g with
          | none =>
            rw [e] at IH
            have hcn0 := True.intro
            have h3 := True.intro
            simp [nock_exec, srlT, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc3, mas_arm, mas.arm_at,
                hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, IH, e,
                split3, bind, StateT.bind, hK, hcn, cnArm, hcn0, h3, wrapN, pure, StateT.pure, eqCode]
          | some pr =>
            obtain ⟨x', g'⟩ := pr
            rw [e] at IH
            have hcn0 := cn_gate K hh x'
            rcases srl_cons_cases hh x' with ⟨h1, h1b, h3⟩ | ⟨h1, h3⟩
            · rw [h3] at hcn0
              simp only [h1, h1b, Need.toNoun, Tag.none] at hcn0
              try simp only [hp0] at hcn0
              simp [consNeed, nock_exec, srlT, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc3, mas_arm, mas.arm_at,
                hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, IH, e,
                split3, bind, StateT.bind, hK, hcn, cnArm, hcn0, h3, wrapN, pure, StateT.pure, eqCode, h1, h1b]
            · rw [h3] at hcn0
              simp only [Need.toNoun, Tag.none] at hcn0
              obtain ⟨u1, v1, hp1⟩ := cd_need_cell hh
              try simp only [hp0] at hcn0
              try simp only [hp1] at hcn0
              simp [nock_exec, srlT, hl1, hne, hna, cap_arm, cap.arm_at, hcap, hc3, mas_arm, mas.arm_at,
                hmas, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none, Tag.this, Tag.both, IH, e,
                split3, bind, StateT.bind, hK, hcn, cnArm, hcn0, h3, wrapN, pure, StateT.pure, eqCode, hp1]

theorem srl_lookPath_some : ∀ (axe : Nat) (ned : Need) (g : Gen (TreapMap mugF)),
    ∃ p, lookPath ned axe g = some p := by
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
    intro ned g
    rw [lookPath.eq_def]
    by_cases ha : axe ≤ 1
    · simp only [ha, dite_true]
      cases ned <;> simp [re, bind, StateT.bind, pure, StateT.pure]
    · have hm := mas_lt axe (by omega)
      simp only [ha, dite_false]
      split
      · obtain ⟨p, hp⟩ := ih (mas axe) hm (split3 ned).2.1 g
        simp [bind, StateT.bind, hp, pure, StateT.pure]
      · obtain ⟨p, hp⟩ := ih (mas axe) hm (split3 ned).2.2 g
        simp [bind, StateT.bind, hp, pure, StateT.pure]

/-- One step of the `rep` of `+sure-require-look` on a look `y`. -/
noncomputable def srlStep (y : Nat) (s : Need × Gen (TreapMap mugF)) : Need × Gen (TreapMap mugF) :=
  if y = 1 then s else (lookPath s.1 y s.2).getD s

/-- The state noun of that `rep`, `[ned gen]`. -/
def srlN (x : GenRest) (s : Need × Gen (TreapMap mugF)) : Noun := C s.1.toNoun (genNoun s.2 x)

variable {x} in
/-- One slam of the gate of the `rep`, on a look that is not `0`. -/
theorem srl_gate (hc : CompIn ctx) (hl : CompLib ctx) (SUR G0 : Noun) (y : Nat) (hy : y ≠ 0)
    (s : Need × Gen (TreapMap mugF)) :
    nock (C srlG (C (C (A y) (srlN x s)) (C srlBat (C SUR (C comp.door (C G0 ctx)))))) srlG
      = some (srlN x (srlStep y s)) := by
  obtain ⟨n, g⟩ := s
  by_cases y1 : y = 1
  · subst y1
    nock_open srlG
    simp [nock_exec, srlN, srlStep]
  · have hlp := srl_loop (x := x) hc hl srlBat SUR (genNoun g x) y (by omega) n g
    obtain ⟨p, hp⟩ := srl_lookPath_some y n g
    rw [hp] at hlp
    simp only [srlT] at hlp
    have y1' : ¬ (1 = y) := fun h => y1 h.symm
    have hy' : ¬ (0 = y) := fun h => hy h.symm
    nock_open srlG
    simp [nock_exec, srlN, srlStep, y1, y1', hy', hlp, hp]

theorem srl_fold (l : List Nat) (h0 : ∀ y ∈ l, y ≠ 0) :
    ∀ (m : CM (TreapMap mugF) Need) (g : Gen (TreapMap mugF)) (s : Need × Gen (TreapMap mugF)),
    m g = some s →
    (l.foldl (fun acc axe => do
      let ned ← acc
      if axe = 1 then pure ned else
      if axe = 0 then fun _ => Option.none else
      lookPath ned axe) m) g = some (l.foldl (fun s y => srlStep y s) s) := by
  induction l with
  | nil => intro m g s h; simpa using h
  | cons y l ih =>
    intro m g s h
    simp only [List.foldl_cons]
    apply ih (fun z hz => h0 z (List.mem_cons_of_mem _ hz))
    have hy := h0 y List.mem_cons_self
    obtain ⟨n, g'⟩ := s
    by_cases y1 : y = 1
    · simp [bind, StateT.bind, h, y1, srlStep, pure, StateT.pure]
    · obtain ⟨p, hp⟩ := srl_lookPath_some y n g'
      simp [bind, StateT.bind, h, y1, hy, srlStep, hp]

variable {x} in
/-- `+sure-require-look`: `lookPath` down each looked-at axis, in the order
of `+rep:in` (the pre-order of the treap, `HoonSet.toList`), from the need of
the sure; with no look at axis `0`. -/
theorem comp_sure_require_look (hc : CompIn ctx) (hl : CompLib ctx) (g : Gen (TreapMap mugF))
    (sur : Sure CSet) (h0 : ∀ y ∈ HoonSet.toList sur.lok, y ≠ 0) :
    nock (C srlBat (C sur.toNoun (compCore g x ctx))) srlBat
      = (sureRequireLook sur g).map fun p => C p.1.toNoun (genNoun p.2 x) := by
  obtain ⟨ned, lok⟩ := sur
  simp only at h0
  have hrep := rep_gate_on (srlN x) (fun n s => match n with | Noun.atom y => srlStep y s | _ => s)
    in.battery layer2 srlG (A 0)
    (C srlBat (C (C ned.toNoun (HoonSet.toNoun lok)) (C comp.door (C (genNoun g x) ctx))))
    (HoonSet.toNoun lok) (cs_tree lok) (ned, g) (by
      intro n hn s
      rw [cs_preorder] at hn
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hn
      exact srl_gate hc hl _ _ y (h0 y hy) s)
  rw [cs_preorder, List.foldl_map] at hrep
  have hf := srl_fold (HoonSet.toList lok) h0 (pure ned) g (ned, g) rfl
  unfold sureRequireLook
  simp only at hf ⊢
  rw [hf]
  simp only [srlN] at hrep
  simp only [Sure.toNoun, compCore]
  nock_open srlBat
  simp [nock_exec, hc, in_arm, in.arm_at, in.rep.arm_at, rep_arm, hrep, srlN]

/-! ## `+insert-hop`

`?:  dropping  gen`, else `got` of block `a`, the tests that its end is a
`%hop` and that it has no parameters, `+emir` of `[~ body fin]` under `o2`,
and block `a` put back with no body and a `%hop` to `o1`.  It reads and
writes `blocks` only.
-/

def ihBat : Noun :=
  (C (A 6) (C (C (A 9) (C (A 1398) (C (A 0) (A 7)))) (C (C (A 0) (A 30)) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 2014))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706f68)) (C (A 0) (A 22)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 4)))) (C (C (A 8) (C (C (A 0) (A 23)) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 8) (C (C (A 9) (C (A 350) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 251)) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 0) (A 58)) (C (A 0) (A 59)))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 10) (C (C (A 62) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 8158))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (A 7) (C (C (A 0) (A 3)) (C (A 10) (C (C (A 15) (C (C (A 1) (A 0)) (C (A 0) (A 122)))) (C (A 10) (C (C (A 6) (C (A 1) (A 0))) (C (A 0) (A 6)))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 126)))))))) (C (A 0) (A 0))))) (C (A 0) (A 0))))))))))

def ihArm : Noun :=
  (C (A 7) (C (C (A 8) (C (C (A 1) (C (A 0) (C (A 0) (A 0)))) (C (C (A 1) ihBat) (C (A 0) (A 1))))) (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x706f682d747265736e692d706d6f63) (C (C (A 0) (A 0x7ffff)) (A 0))))) (C (A 0) (A 1))))))


/-- `+insert-hop` is at door axis `2` (core axis `4`). -/
theorem comp_ih_at : slot? 2 comp.door = some ihArm := by kernel_rfl

variable {x} in
/-- `+insert-hop` against `insertHop`, exact over `genNoun`, crashes
included, under `CompIn ctx` only. -/
theorem comp_insert_hop (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (a o1 o2 : Nat) :
    nock (C ihBat (C (C (A a) (C (A o1) (A o2))) (compCore g x ctx))) ihBat
      = (insertHop a o1 o2 g).map fun p => genNoun p.2 x := by
  have hget := getF_hoonMap Blob.toNoun g.blocks a
  have hgc : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
    ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
  nock_open ihBat
  cases hd : g.drop
  · cases e : HoonMap.get g.blocks a with
    | none =>
      rw [e] at hget
      have hgot := got_gate_nil layer2 hgc (A a) _ hget
      simp [nock_exec, compCore, comp_drop_at', dropArm, genNoun, cgModeNoun, hd, comp_h110,
        eqCode_atom, hc, by_arm, by.arm_at, by.got.arm_at, got_arm, hgot, insertHop, e]
    | some b =>
      rw [e] at hget
      have hgot := got_gate layer2 hgc (A a) _ _ hget
      obtain ⟨par, body, fin⟩ := b
      cases fin with
      | hop t =>
        cases par with
        | nil =>
          have hem := comp_emir x hc g o2 ⟨[], body, Termin.hop t⟩
          simp only [Blob.toNoun, listNoun, Termin.toNoun, Jmp.toNoun, emir, hd, Bool.false_eq_true,
            ite_false, Option.map_some, compCore, genNoun, cgModeNoun, Tag.hop] at hem
          have hput := put_gate layer2 gorIn_morIn_layer2 (A a)
            (Blob.toNoun ⟨[], [], Termin.hop ⟨[], o1⟩⟩) _ _
            (putF_hoonMap Blob.toNoun (HoonMap.put g.blocks o2 ⟨[], body, Termin.hop t⟩) a
              ⟨[], [], Termin.hop ⟨[], o1⟩⟩)
          simp only [Blob.toNoun, listNoun, Termin.toNoun, Jmp.toNoun, Tag.hop] at hput
          simp [nock_exec, compCore, comp_drop_at', dropArm, genNoun, cgModeNoun, hd, comp_h110,
            eqCode_atom, hc, by_arm, by.arm_at, by.got.arm_at, got_arm, hgot, insertHop, e,
            Blob.toNoun, Termin.toNoun, listNoun, Tag.hop, comp_emir_arm, hem, by.put.arm_at,
            put_arm, hput, Jmp.toNoun]
        | cons y ys =>
          simp [nock_exec, compCore, comp_drop_at', dropArm, genNoun, cgModeNoun, hd, comp_h110,
            eqCode_atom, hc, by_arm, by.arm_at, by.got.arm_at, got_arm, hgot, insertHop, e,
            Blob.toNoun, Termin.toNoun, listNoun, Tag.hop, eqCode]
      | _ =>
        simp [nock_exec, compCore, comp_drop_at', dropArm, genNoun, cgModeNoun, hd, comp_h110,
          eqCode_atom, hc, by_arm, by.arm_at, by.got.arm_at, got_arm, hgot, insertHop, e,
          Blob.toNoun, Termin.toNoun, Tag.hop, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.jmp, Tag.jmf,
          Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti]
  · simp [nock_exec, compCore, comp_drop_at', dropArm, genNoun, cgModeNoun, hd, comp_h110,
      eqCode_atom, insertHop]

end Compiler
end Formalization
