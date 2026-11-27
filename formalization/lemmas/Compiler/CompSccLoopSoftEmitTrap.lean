import lemmas.Compiler.CompSccLoopSoftEmitBase

/-! # `+soft-emit`: the push `seCut` on `%this` / `%none` requirements (README Gaps 21.17)

The push `seCut` of `seBat` is the trap over `req.s` that calls `+soft-cut` (line 5604, battery
axis 220588 of the door, `skArm`) at each requirement and welds its lists in front of `acc`.
`+soft-cut` first calls `+soft-axis` (line 5552, battery axis 4062, `sxArm`), which on `%this r`
is `+get:by` of `r` in `axs`.  On a need `%none` or `%this` (the case of the corpus) neither
`+sure-at` nor the cell paths are reached:

* `sx_none`, `sx_this`: `+soft-axis` gives `%any`, or `[%at q]` / `%no` from the lookup;
* **`sk_gate`**: `+soft-cut` is `softCutT`, `gen` unchanged;
* `sk_trap`: the trap, by induction on the list;
* **`se_cut`**: the push on the subject `seS1`, against `softCuts`.

The parts are cut by a generator (`softcut.py` of track I's scratch, from `comp.door` and the
literal of `seCut`). -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

def sxBunt : Noun :=
  (C (C (A 0x656e6f6e) (A 0)) (A 0))

def sxThis : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 764) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 57))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (A 1) (A 0x6f6e)) (C (C (A 1) (A 0x7461)) (C (A 0) (A 5))))))))

def sxCell : Noun :=
  (C (A 6) (C (C (A 3) (C (A 0) (A 24))) (C (C (A 8) (C (C (A 9) (C (A 0x5554) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 24))) (C (A 0) (A 1)))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 25))) (C (A 0) (A 1)))))))))) (C (A 0) (A 2)))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 24))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0x5554) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 102))) (C (A 0) (A 1)))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 103))) (C (A 0) (A 1)))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 764) (C (A 10) (C (C (A 6) (C (A 0) (A 61))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 242))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x796e61)) (C (A 0) (A 6)))) (C (C (A 1) (A 0x6f6e)) (C (A 0) (A 6))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x796e61)) (C (A 0) (A 6)))) (C (C (C (A 1) (A 0x7461)) (C (A 0) (A 5))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6f6e)) (C (A 0) (A 6)))) (C (C (A 1) (A 0x6f6e)) (C (A 6) (C (C (A 5) (C (C (A 0) (A 13)) (C (A 0) (A 5)))) (C (C (A 0) (A 6)) (C (A 1) (A 0x6f6e)))))))))))))))))))))))

def skBunt : Noun :=
  (C (A 0) (C (C (A 0x656e6f6e) (A 0)) (C (A 0) (C (C (A 0x656e6f6e) (A 0)) (C (A 1) (A 0))))))

def skAx : Noun :=
  (C (A 8) (C (C (A 9) (C (A 6110) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 58)) (C (A 0) (A 118)))) (C (A 0) (A 2))))))))

def skT2 : Noun :=
  (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 6) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 116)))) (C (C (A 1) (A 0)) (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 116))))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 0x2bbe) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 13)) (C (C (A 0) (A 494)) (C (A 0) (A 495))))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1)))))

def skTop : Noun :=
  (C (C (C (A 1) (A 0)) (C (C (C (A 0) (A 5)) (C (C (A 0) (A 28)) (C (A 0) (A 58)))) (C (A 1) (A 0)))) (C (A 0) (A 62)))

def skThis : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 0) (A 28)) (C (A 0) (A 117)))) (C (C (A 0) (A 0)) (C (C (C (C (C (A 1) (A 0x766f6d)) (C (C (A 0) (A 28)) (C (A 0) (A 117)))) (C (A 1) (A 0))) (C (A 1) (A 0))) (C (A 0) (A 62))))))

def skCell : Noun :=
  (C (A 6) (C (C (A 3) (C (A 0) (A 116))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 15)))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 31)))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 26) (C (A 0) (A 500))) (C (A 10) (C (C (A 12) (C (A 0) (A 6))) (C (A 0) (A 15)))))))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 26) (C (A 0) (A 1013))) (C (A 10) (C (C (A 12) (C (A 0) (A 6))) (C (A 0) (A 31)))))))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (C (C (A 1) (A 0x6c6563)) (C (A 0) (A 508))) (C (A 8) (C (C (A 9) (C (A 0xbef7f4) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 12)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 13)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (C (C (A 1) (A 0x646568)) (C (C (A 0) (A 508)) (C (A 0) (A 30)))) (C (A 0) (A 12)))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 4)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 5)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (C (C (A 1) (A 0x6c6174)) (C (C (A 0) (A 508)) (C (A 0) (A 14)))) (C (A 0) (A 4)))))))))) (C (A 0) (A 2))))))))) (C (A 8) (C (C (A 9) (C (A 0xbef7f4) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 29)) (C (A 0) (A 13)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1022))))))))))))))))))))))))))))))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 116))))) (C (A 6) (C (C (A 5) (C (C (A 0) (A 28)) (C (A 0) (A 234)))) (C (C (A 0) (A 0)) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 15)))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 31)))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 26) (C (A 0) (A 2006))) (C (A 10) (C (C (A 12) (C (A 0) (A 6))) (C (A 0) (A 15)))))))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 26) (C (A 0) (A 4055))) (C (A 10) (C (C (A 12) (C (A 0) (A 6))) (C (A 0) (A 31)))))))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (C (C (A 1) (A 0x766f6d)) (C (C (A 0) (A 508)) (C (A 0) (A 4074)))) (C (C (C (A 1) (A 0x6c6563)) (C (A 0) (A 508))) (C (A 8) (C (C (A 9) (C (A 0xbef7f4) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 12)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 13)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (C (C (A 1) (A 0x646568)) (C (C (A 0) (A 508)) (C (A 0) (A 30)))) (C (A 0) (A 12)))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 4)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 5)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (C (C (A 1) (A 0x6c6174)) (C (C (A 0) (A 508)) (C (A 0) (A 14)))) (C (A 0) (A 4)))))))))) (C (A 0) (A 2)))))))))) (C (A 8) (C (C (A 9) (C (A 0xbef7f4) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 29)) (C (A 0) (A 13)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1022)))))))))))))))))))))))))))))))))))))))))))

def skCall : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x55dac) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 56)) (C (C (A 0) (A 57)) (C (C (A 0) (A 62)) (C (C (A 0) (A 0x3fbe)) (C (A 0) (A 4076))))))) (C (A 0) (A 2))))))))))

def skWelds : Noun :=
  (C (C (A 8) (C (C (A 9) (C (A 0xbef7f4) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 12)) (C (A 0) (A 124)))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 9) (C (A 0xbef7f4) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 13)) (C (A 0) (A 125)))) (C (A 0) (A 2)))))))))

/-- The battery of `+soft-axis`: `%none`, `%this`, then the cells (not linked). -/
def sxBat : Noun :=
  C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 24)))) (C (C (A 1) (A 0x796e61))
    (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 24)))) (C sxThis sxCell)))))

/-- `+soft-axis`: the gate. -/
def sxArm : Noun := C (A 8) (C (C (A 1) sxBunt) (C (C (A 1) sxBat) (C (A 0) (A 1))))

/-- `[[~ ~] gen]`. -/
def skNil : Noun := C (C (A 1) (C (A 0) (A 0))) (C (A 0) (A 62))

/-- The battery of `+soft-cut`: `q` from `+soft-axis`, `%any`, the part handed on, `%none`,
`%this`, then the cells (not linked). -/
def skBat : Noun :=
  C (A 8) (C skAx (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x796e61)) (C (A 0) (A 2)))) (C skNil
    (C (A 6) (C skT2 (C skTop (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 116))))
      (C skNil (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 116)))) (C skThis skCell)))))))))))))

/-- `+soft-cut`: the gate. -/
def skArm : Noun := C (A 8) (C (C (A 1) skBunt) (C (C (A 1) skBat) (C (A 0) (A 1))))

theorem sx_at : slot? 4062 comp.door = some sxArm := by kernel_rfl
theorem sk_at : slot? 220588 comp.door = some skArm := by kernel_rfl

/-- The trap of `seCut`. -/
def skTrap : Noun :=
  C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 6)))) (C (C (C (A 0) (A 14)) (C (A 0) (A 510)))
    (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C skCall (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5)))
      (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 9) (C (A 2) (C (A 10)
        (C (C (A 14) skWelds) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 3))))))))))))))))))

theorem seCut_eq : seCut = C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 1) (C (A 0) (A 0)))
    (C (A 8) (C (C (A 0) (A 0x1efff)) (C (A 8) (C (C (A 1) skTrap) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))))) :=
  rfl

/-- The noun of `req.s`. -/
def skReqN (l : List (Nat × Need)) : Noun := l.foldr (fun (s, n) acc => C (C (A s) n.toNoun) acc) (A 0)

theorem skReqN_nil : skReqN [] = A 0 := rfl
theorem skReqN_cons (s : Nat) (n : Need) (l : List (Nat × Need)) :
    skReqN ((s, n) :: l) = C (C (A s) n.toNoun) (skReqN l) := rfl

theorem sk_sNoun (s : SoftCall) : Compiler.SoftCall.toNoun s =
    C (A (if s.kin = 1 then 1818845556 else if s.kin = 0 then 1819042147 else 1851876717))
    (C s.b.toNoun (C (match s.rin with | Option.none => A 0 | some r => C (A 0) r) (C s.ned.toNoun
      (C s.sur.toNoun (C (A s.plain) (C (A s.head) (C (A s.last) (C (A s.pro) (C (A s.out) (C (A 0)
        (skReqN s.req))))))))))) := rfl

/-! ## `+soft-axis` -/

theorem sx_none (Dr G ctx M : Noun) :
    nock (C sxBat (C (C (C (A 0x656e6f6e) (A 0)) M) (C Dr (C G ctx)))) sxBat = some (A 0x796e61) := by
  simp [nock_exec, sxBat, Need.toNoun, Tag.none]

theorem sx_this {ctx : Noun} (hc : CompIn ctx) (Dr G M : Noun) {axs : List (Nat × Nat)} (hM : AxsRel M axs)
    (r : Nat) :
    nock (C sxBat (C (C (C (A 0x73696874) (A r)) M) (C Dr (C G ctx)))) sxBat
      = some (match axs.lookup r with | some q => C (A 0x7461) (A q) | Option.none => A 0x6f6e) := by
  have hgc : SomeIn layer2 ∧ GorIn mugF layer2 := ⟨someIn_layer2, gorIn_morIn_layer2.1⟩
  cases hl : axs.lookup r with
  | none =>
    have hg := get_gate layer2 hgc (A r) M _ (axsRel_get_none hM hl)
    simp [nock_exec, sxBat, sxThis, Need.toNoun, Tag.none, Tag.this, hc, by_arm, by.arm_at, by.get.arm_at,
      get_arm, hg]
  | some q =>
    have hg := get_gate layer2 hgc (A r) M _ (axsRel_get_some hM hl)
    simp [nock_exec, sxBat, sxThis, Need.toNoun, Tag.none, Tag.this, hc, by_arm, by.arm_at, by.get.arm_at,
      get_arm, hg]

/-! ## `+soft-cut` -/

/-- **`+soft-cut` on a need `%none` or `%this`**: `softCutT`, `gen` unchanged. -/
theorem sk_gate {ctx : Noun} (hc : CompIn ctx) (Dr G M : Noun) (hsa : slot? 4062 Dr = some sxArm)
    {axs : List (Nat × Nat)} (hM : AxsRel M axs) (src : Nat) (ned : Need)
    (hned : ned = Need.none ∨ ∃ r, ned = Need.this r) (SK : Noun) :
    nock (C skBat (C (C (A src) (C ned.toNoun (C M SK))) (C Dr (C G ctx)))) skBat
      = (softCutT src ned axs).map fun c => C (seCutN c) G := by
  rcases hned with rfl | ⟨r, rfl⟩
  · have h := sx_none Dr G ctx M
    simp [nock_exec, skBat, skAx, sxArm, hsa, h, skNil, softCutT, seCutN, listNoun, Need.toNoun, Tag.none]
  · have h := sx_this hc Dr G M hM r
    cases hl : axs.lookup r with
    | none =>
      simp only [hl] at h
      by_cases e : src = r
      · subst e
        simp [nock_exec, skBat, skAx, sxArm, hsa, h, skNil, skT2, skThis, softCutT, hl, Need.toNoun, Tag.none,
          Tag.this]
      · simp [nock_exec, skBat, skAx, sxArm, hsa, h, skNil, skT2, skThis, softCutT, hl, e, seCutN, listNoun,
          Pole.toNoun, Tag.mov, Need.toNoun, Tag.none, Tag.this]
    | some q =>
      simp only [hl] at h
      simp [nock_exec, skBat, skAx, sxArm, hsa, h, skNil, skT2, skTop, softCutT, hl, seCutN, listNoun,
        seTopN, Need.toNoun, Tag.none, Tag.this]

/-! ## The trap -/

/-- **The trap of `seCut`** over a list of requirements `%none` / `%this`, from any `acc`. -/
theorem sk_trap {ctx : Noun} (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (x : GenRest) (o : Nat) (s : SoftCall)
    (M : Noun) {axs : List (Nat × Nat)} (hM : AxsRel M axs) :
    ∀ (req : List (Nat × Need)) (acc : List Pole × List (Nat × Nat × Need)),
    (∀ p ∈ req, p.2 = Need.none ∨ ∃ r, p.2 = Need.this r) →
    nock (C skTrap (C (skReqN req) (C (seCutN acc) (seS1 M g x ctx o s)))) skTrap
      = (softCuts axs req acc).map fun c => C (seCutN c) (genNoun g x)
  | [], (a1, a2), _ => by
    conv => { lhs; arg 2; unfold skTrap }
    simp only [skReqN_nil, seS1, seS0, compCore, sk_sNoun]
    generalize comp.door = Dr
    generalize genNoun g x = GN
    simp [nock_exec, softCuts, seCutN]
  | (src, ned) :: rest, (a1, a2), hr => by
    have hned := hr (src, ned) (List.mem_cons_self ..)
    have ih := sk_trap hc g x o s M hM rest
    have hsa := sx_at
    have hsk := sk_at
    conv => { lhs; arg 2; unfold skTrap }
    simp only [skReqN_cons, seS1, seS0, compCore, sk_sNoun] at ih ⊢
    generalize comp.door = Dr at hsa hsk ih ⊢
    generalize genNoun g x = GN at ih ⊢
    cases hct : softCutT src ned axs with
    | none =>
      have hs : ∀ SK, nock (C skBat (C (C (A src) (C ned.toNoun (C M SK))) (C Dr (C GN ctx)))) skBat
          = Option.none := fun SK => by rw [sk_gate hc Dr GN M hsa hM src ned hned SK, hct]; rfl
      simp [nock_exec, skCall, skArm, hsk, hs, softCuts, hct]
    | some c =>
      obtain ⟨co, ct⟩ := c
      have hs : ∀ SK, nock (C skBat (C (C (A src) (C ned.toNoun (C M SK))) (C Dr (C GN ctx)))) skBat
          = some (C (seCutN (co, ct)) GN) := fun SK => by
        rw [sk_gate hc Dr GN M hsa hM src ned hned SK, hct]; rfl
      have ih' := ih (co ++ a1, ct ++ a2) (fun p hp => hr p (List.mem_cons_of_mem _ hp))
      have hw1 := cd_weld Pole.toNoun co a1
      have hw2 := cd_weld seTopN ct a2
      simp only [seCutN] at hs ih' ⊢
      simp [nock_exec, skCall, skArm, hsk, hs, skWelds, hc, weld_arm, weld.arm_at, hw1, hw2, softCuts, hct,
        ih', seCutN]

/-- **The push `seCut`**: on the subject after `seAxs` (`axs` the map of `M`), with every
requirement `%none` or `%this`, the product of the `=^` is `[[ops tops] gen]` of `softCuts`. -/
theorem se_cut (ctx : Noun) (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (x : GenRest) (o : Nat) (s : SoftCall)
    (M : Noun) (axs : List (Nat × Nat)) (hM : AxsRel M axs)
    (hreq : ∀ p ∈ s.req, p.2 = Need.none ∨ ∃ r, p.2 = Need.this r) :
    nock (seS1 M g x ctx o s) seCut = (softCuts axs s.req ([], [])).map fun c => C (seCutN c) (genNoun g x) := by
  have htr := sk_trap hc g x o s M hM s.req ([], []) hreq
  have e0 : seCutN (([] : List Pole), ([] : List (Nat × Nat × Need))) = C (A 0) (A 0) := rfl
  rw [e0] at htr
  rw [seCut_eq]
  simp only [seS1, seS0, compCore, sk_sNoun] at htr ⊢
  generalize comp.door = Dr at htr ⊢
  generalize genNoun g x = GN at htr ⊢
  simp [nock_exec, htr]

end Compiler
end Formalization
