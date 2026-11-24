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

end Compiler
end Formalization
