import lemmas.Compiler.OptLinkHelpers

/-!
# `+remove-empty-middle`: the nouns and `rewrite-jump`

```hoon
++  remove-empty-middle
  ~%  %remove-empty-middle  ..ride  ~
  |=  blocks=(map @uwoo blob)
  ^-  [changed=? (map @uwoo blob)]
  =/  readers=(jug @uvre @uwoo)
    ?.  %-  ~(any by blocks)
        |=(b=blob &(?=(^ par.b) ?=(~ body.b) ?=(%hop -.fin.b)))
      ~
    %-  ~(rep by blocks)
    |=  [[o=@uwoo b=blob] acc=(jug @uvre @uwoo)]
    =/  put  |=([r=@uvre acc=(jug @uvre @uwoo)] (~(put ju acc) r o))
    =.  acc  (roll (get-regs fin.b) put(acc acc))
    %+  roll  body.b
    |=  [op=pole acc=_acc]
    (roll (get-regs op) put(acc acc))
  |^  ^-  [? (map @uwoo blob)]
  %-  ~(rep by blocks)
  |=  [[o=@uwoo b=blob] changed=_| new=(map @uwoo blob)]
  ...
  ++  rewrite-jump  ...
  ++  rewrite-hop  ...
  --
```

The arm is `2940` of `optC` (`rem_at`, nouns by `tools/gen/optlink.py
rem`).  The body computes `readers` (`remReaders`: `+any:by` with the test
`remAnyG`, then `+rep:by` with the gate `remRdG`) and kicks the arm `$`
(axis `10`) of the `|^` core `[remBat [readers [remBody [blocks optC]]]]`
(`remCore`), whose other arms are the gates `rewrite-hop` (axis `4`,
`remHopBody`) and `rewrite-jump` (axis `11`, `remJumpBody`).  The gate of
the `+roll` over `body.b` in `readers` takes the sample `[*pole acc]`, whose
bunt the mold `pole` (arm `2743` of `compTypes`) makes when it runs
(`remBuntF`, `pole_bunt`).

* `rj_gate`: where `rewriteJump` (`Ska/OptMiddle.lean`) returns, the gate
  `rewrite-jump` returns the same jump.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The nouns -/

/-- The gate `put` of `readers`: `(~(put ju acc) r o)`. -/
def remPutG : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 760) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 4) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 0) (A 248)))) (C (A 0) (A 2))))))))

/-- The gate of the `+roll` over `body.b` in `readers`. -/
def remOpG : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 84) (C (A 0) (A 1023)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 10) (C (C (A 13) (C (A 0) (A 13))) (C (A 0) (A 14)))))))) (C (A 0) (A 2))))))))

/-- The sample of that gate, `[*pole acc]`, its bunt made by the mold `pole` (arm `2743` of `compTypes`). -/
def remBuntF : Noun :=
  (C (C (A 7) (C (C (A 9) (C (A 2743) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (A 0) (A 29)))

/-- The gate of the `+rep:by` that makes `readers`. -/
def remRdG : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) remPutG) (C (A 0) (A 1))))) (C (A 7) (C (C (A 10) (C (C (A 29) (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 84) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 487))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 10) (C (C (A 13) (C (A 0) (A 29))) (C (A 0) (A 2)))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 486)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C remBuntF (C (C (A 1) remOpG) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))))))

/-- Its sample bunt. -/
def remRdB : Noun :=
  (C (C (A 0) (C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0))))) (A 0))

/-- The test of the `+any:by`: an empty block with parameters that ends in a `%hop`. -/
def remAnyG : Noun :=
  (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 26)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706f68)) (C (A 0) (A 54)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1)))))

/-- Its sample bunt. -/
def remAnyB : Noun :=
  (C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0))))

/-- `readers`. -/
def remReaders : Noun :=
  (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffff)))) (C (A 9) (C (A 20) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) remAnyB) (C (C (A 1) remAnyG) (C (A 0) (A 1)))))))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffff)))) (C (A 9) (C (A 767) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) remRdB) (C (C (A 1) remRdG) (C (A 0) (A 1)))))))) (C (A 0) (A 2)))))))) (C (A 1) (A 0)))))

/-- The gate of the `+levy` of `rewrite-hop`: no reader but `there.j`. -/
def remLevyG : Noun :=
  (C (A 5) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 94) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 760) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 46) (C (A 10) (C (C (A 6) (C (A 0) (A 510))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 253))) (C (A 0) (A 2))))))))))

/-- The trap that makes `sub`. -/
def remSubT : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 14)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 6)))) (C (C (A 0) (A 30)) (C (A 0) (A 0))))) (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 62))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 60)) (C (A 0) (A 28)))) (C (A 0) (A 2))))))))) (C (A 10) (C (C (A 14) (C (A 0) (A 29))) (C (A 10) (C (C (A 6) (C (A 0) (A 13))) (C (A 0) (A 1)))))))))) (C (A 0) (A 0))))))))

/-- The body of the gate `pass`. -/
def remPassB : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 6)))) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 1531) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 29)) (C (A 0) (A 14)))) (C (A 0) (A 2)))))))))))

/-- The gate body of `rewrite-hop` (arm `4` of the `|^` core). -/
def remHopBody : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 254))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 10)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706f68)) (C (A 0) (A 22)))) (C (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 0x2fbc) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 12)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) remLevyG) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 0) (A 12)) (C (A 8) (C (C (A 0) (A 124)) (C (A 8) (C (C (A 1) remSubT) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))))))) (C (A 8) (C (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) remPassB) (C (A 0) (A 1))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 494)) (C (A 0) (A 6)))) (C (A 0) (A 2)))))))) (C (A 0) (A 239)))) (C (A 0) (A 15)))))))))) (C (A 0) (A 14))))) (C (A 0) (A 14))))) (C (A 0) (A 14)))))))

/-- The gate body of `rewrite-jump` (arm `11` of the `|^` core). -/
def remJumpBody : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 12)))) (C (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 254))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 4)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 10)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706f68)) (C (A 0) (A 22)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 46)))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 23))) (C (A 0) (A 3)))))) (C (A 0) (A 14))))) (C (A 0) (A 14))))) (C (A 0) (A 14))))) (C (A 0) (A 0))))))) (C (A 0) (A 6)))))

/-- The gate of the `+rep:by` of `$` (arm `10` of the `|^` core). -/
def remMainG : Noun :=
  (C (A 8) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x716c63)) (C (A 0) (A 206)))) (C (C (A 10) (C (C (A 7) (C (C (A 8) (C (C (A 9) (C (A 11) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 1854))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 9) (C (A 11) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 1855))) (C (A 0) (A 2)))))))))) (C (A 0) (A 103)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x717165)) (C (A 0) (A 206)))) (C (C (A 10) (C (C (A 15) (C (C (A 8) (C (C (A 9) (C (A 11) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 3710))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 9) (C (A 11) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 3711))) (C (A 0) (A 2)))))))))) (C (A 0) (A 103)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6e7262)) (C (A 0) (A 206)))) (C (C (A 10) (C (C (A 7) (C (C (A 8) (C (C (A 9) (C (A 11) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 1854))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 9) (C (A 11) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 1855))) (C (A 0) (A 2)))))))))) (C (A 0) (A 103)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x7a7262)) (C (A 0) (A 206)))) (C (C (A 10) (C (C (A 7) (C (C (A 8) (C (C (A 9) (C (A 11) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 1854))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 9) (C (A 11) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 1855))) (C (A 0) (A 2)))))))))) (C (A 0) (A 103)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706f68)) (C (A 0) (A 206)))) (C (C (A 10) (C (C (A 3) (C (A 8) (C (C (A 9) (C (A 4) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 463))) (C (A 0) (A 2))))))))) (C (A 0) (A 103)))) (C (A 11) (C (C (A 0x73736f74) (C (A 1) (A 0))) (C (A 0) (A 103))))))))))))))))))) (C (C (A 6) (C (C (A 0) (A 58)) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 2)) (C (A 0) (A 231)))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 123))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 120)) (C (A 7) (C (C (A 0) (A 3)) (C (A 10) (C (C (A 7) (C (A 0) (A 2))) (C (A 0) (A 57)))))))) (C (A 0) (A 2)))))))))))

/-- Its sample bunt. -/
def remMainB : Noun :=
  (C (C (A 0) remAnyB) (C (A 1) (A 0)))

/-- The battery of the `|^` core: `rewrite-hop`, `$`, `rewrite-jump`. -/
def remBat : Noun :=
  (C (C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) remHopBody) (C (A 0) (A 1))))) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 767) (C (A 10) (C (C (A 6) (C (A 0) (A 62))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) remMainB) (C (C (A 1) remMainG) (C (A 0) (A 1)))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) remJumpBody) (C (A 0) (A 1)))))))

/-- The gate body of `+remove-empty-middle`. -/
def remBody : Noun :=
  (C (A 8) (C remReaders (C (A 8) (C (C (A 1) remBat) (C (A 9) (C (A 10) (C (A 0) (A 1))))))))

/-- Its sample bunt. -/
def remBunt : Noun :=
  (A 0)

/-- Its `%fast` hint. -/
def remHint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x656c6464696d2d7974706d652d65766f6d6572) (C (C (A 0) (A 0xffff)) (A 0))))) (C (A 0) (A 1))))

/-- The arm `+remove-empty-middle`. -/
def remArm : Noun := C (A 7) (C (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) remBody) (C (A 0) (A 1))))) remHint)

/-- `+remove-empty-middle` is arm `2940` of `optC`. -/
theorem rem_at : slot? 2940 optC = some remArm := by kernel_rfl

@[nock_exec] theorem rem_arm (d : Noun) : nock d remArm = some (C remBody (C (A 0) d)) := by
  unfold remArm remHint; generalize remBody = B; simp [nock_exec]

/-- The `|^` core: `[remBat [readers [remBody [blocks optC]]]]`. -/
def remCore (RD BL : Noun) : Noun := C remBat (C RD (C remBody (C BL optC)))

/-! ## The bunt of `pole` -/

/-- The mold `pole`, arm `2743` of `compTypes`. -/
noncomputable def poleMold : Noun := (slot? 2743 compTypes).getD (A 0)
theorem pole_mold_at : slot? 2743 compTypes = some poleMold := by kernel_rfl
/-- The gate the mold builds. -/
noncomputable def poleGate : Noun := (evalFuel 200 compTypes poleMold).getD (A 0)
theorem pole_gate : nock compTypes poleMold = some poleGate :=
  nock_of_evalFuel (fuel := 200) (by kernel_rfl)
/-- The bunt of `pole`: `[%csm *bell 0 0 0]`, its last case. -/
def poleBunt : Noun := C (A 0x6d7363) (C (C (C (A 1) (A 0)) (C (A 0) (A 0))) (C (A 0) (C (A 0) (A 0))))
theorem pole_bunt : nock poleGate (C (A 9) (C (A 2) (C (A 0) (A 1)))) = some poleBunt :=
  nock_of_evalFuel (fuel := 2000) (by kernel_rfl)

/-! ## `rewrite-jump` -/

/-- **`rewrite-jump`**: where `rewriteJump` returns, the gate returns the
same jump. -/
theorem rj_gate (bl : TreapMap mugF Blob) (RD : Noun) :
    ∀ (n : Nat) (j j' : Jmp), Opt.rewriteJump bl n j = some j' →
    nock (C remJumpBody (C j.toNoun (remCore RD (HoonMap.toNoun Blob.toNoun bl)))) remJumpBody
      = some j'.toNoun := by
  have hL := optC_layer2
  intro n
  induction n with
  | zero => intro j j' h; simp [Opt.rewriteJump] at h
  | succ n ih =>
    intro j j' h
    obtain ⟨args, there⟩ := j
    have hg := blocks_got bl there
    cases args with
    | cons a as =>
      simp [Opt.rewriteJump] at h
      subst h
      unfold remCore
      conv => lhs; arg 2; unfold remJumpBody
      generalize optC = OC at hL
      simp [nock_exec, Jmp.toNoun, listNoun]
    | nil =>
      simp only [Opt.rewriteJump, ne_eq, not_true_eq_false, if_false] at h
      obtain ⟨nex, hnex, h2⟩ := Option.bind_eq_some_iff.mp h
      rw [hnex] at hg
      obtain ⟨par, body, fin⟩ := nex
      simp only [Option.map_some, Blob.toNoun] at hg
      cases par with
      | cons p ps => simp at h2
      | nil =>
        cases body with
        | cons op ops =>
          simp at h2
          subst h2
          unfold remCore
          conv => lhs; arg 2; unfold remJumpBody
          generalize optC = OC at hL
          generalize HoonMap.toNoun Blob.toNoun bl = BL at hg
          simp [nock_exec, Jmp.toNoun, listNoun, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg]
        | nil =>
          cases fin with
          | hop t =>
            obtain ⟨targs, tthere⟩ := t
            cases targs with
            | cons a as =>
              simp at h2
              subst h2
              unfold remCore
              conv => lhs; arg 2; unfold remJumpBody
              generalize optC = OC at hL
              generalize HoonMap.toNoun Blob.toNoun bl = BL at hg
              simp [nock_exec, Jmp.toNoun, listNoun, Termin.toNoun, Tag.hop, hL, by.arm_at, by_arm,
                by.got.arm_at, got_arm, hg]
            | nil =>
              simp at h2
              have hn := ih ⟨[], tthere⟩ j' h2
              unfold remCore at hn ⊢
              conv => lhs; arg 2; unfold remJumpBody
              simp only [Jmp.toNoun, listNoun] at hn
              generalize optC = OC at hL hn
              generalize HoonMap.toNoun Blob.toNoun bl = BL at hg hn ⊢
              simp [nock_exec, Jmp.toNoun, listNoun, Termin.toNoun, Tag.hop, hL, by.arm_at, by_arm,
                by.got.arm_at, got_arm, hg, hn]
          | _ =>
            simp at h2
            subst h2
            unfold remCore
            conv => lhs; arg 2; unfold remJumpBody
            generalize optC = OC at hL
            generalize HoonMap.toNoun Blob.toNoun bl = BL at hg
            simp [nock_exec, Jmp.toNoun, listNoun, Termin.toNoun, Tag.hop, Tag.clq, Tag.eqq, Tag.brn, Tag.brz,
              Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, hL, by.arm_at, by_arm,
              by.got.arm_at, got_arm, hg]

/-! ## `rewrite-hop`: `sub` and `pass` -/

/-- `+del:in` of a label on a set of atoms. -/
theorem saw_del {S : Noun} {l : List Nat} (h : SawRel S l) (t : Nat) :
    ∃ S', nock (C in.del.battery (C (A t) (C in.battery (C S layer2)))) in.del.battery = some S' ∧
      SawRel S' (l.filter fun x => x ≠ t) := by
  have hm : IsMap mugF (toMap S) := h.1
  obtain ⟨out', hd, hm', hg⟩ := delF_spec (A t) hm
  rw [delF_toMap (A t) S h.1] at hd
  cases hx : delInF mugF (A t) S with
  | none => rw [hx] at hd; cases hd
  | some out =>
    rw [hx] at hd
    simp only [Option.map_some, Option.some.injEq] at hd
    subst hd
    refine ⟨out, del_in_gate layer2 gorIn_morIn_layer2 (A t) S out hx, hm', fun k => ?_⟩
    have e := hg k (A 0)
    unfold Has
    rw [e]
    change k ≠ A t ∧ Has S k ↔ _
    rw [h.2 k]
    constructor
    · rintro ⟨hk, n, hn, rfl⟩
      exact ⟨n, List.mem_filter.2 ⟨hn, by simpa using fun e => hk (by rw [e])⟩, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      obtain ⟨hn, hne⟩ := List.mem_filter.1 hn
      exact ⟨fun e => by simp at hne; exact hne (Noun.atom.inj e), n, hn, rfl⟩

/-- `sub` of `rewrite-hop` as a treap: the puts of the pairs, in order. -/
def subMap : List Nat → List (Option Nat) → TreapMap mugF (Option Nat) → Option (TreapMap mugF (Option Nat))
  | [], [], m => some m
  | [], _ :: _, _ => none
  | _ :: _, [], _ => none
  | p :: ps, a :: as, m => subMap ps as (HoonMap.put m p a)

theorem subMap_mkSub : ∀ (ps : List Nat) (as : List (Option Nat)) (m : TreapMap mugF (Option Nat))
    (f : Nat → Option (Option Nat)), HoonMap.get m = f →
    (subMap ps as m).map HoonMap.get = Opt.mkSub ps as f
  | [], [], m, f, h => by simp [subMap, Opt.mkSub, h]
  | [], _ :: _, _, _, _ => rfl
  | _ :: _, [], _, _, _ => rfl
  | p :: ps, a :: as, m, f, h => by
    simp only [subMap, Opt.mkSub]
    apply subMap_mkSub
    funext q
    rw [HoonMap.get_put, ← h]

/-- **The trap that makes `sub`** is `subMap`, in every context `T` (the
subject `[nex Y]` of `rewrite-hop`) with `layer2` at `0xffffff`. -/
theorem rem_subt (T : Noun) (hT : slot? 0xffffff T = some layer2) :
    ∀ (ps : List Nat) (as : List (Option Nat)) (m : TreapMap mugF (Option Nat)),
    nock (C remSubT (C (listNoun (unitNoun A) as) (C (listNoun A ps) (C (HoonMap.toNoun (unitNoun A) m) T))))
      remSubT = (subMap ps as m).map (HoonMap.toNoun (unitNoun A)) := by
  intro ps
  induction ps with
  | nil =>
    intro as m
    cases as with
    | nil =>
      conv => lhs; arg 2; unfold remSubT
      simp [nock_exec, listNoun, subMap]
    | cons a as =>
      conv => lhs; arg 2; unfold remSubT
      simp [nock_exec, listNoun, subMap, unitNoun]
  | cons p ps ih =>
    intro as m
    cases as with
    | nil =>
      conv => lhs; arg 2; unfold remSubT
      simp [nock_exec, listNoun, subMap]
    | cons a as =>
      have hp := putF_hoonMap (unitNoun A) m p a
      have hput := put_gate (mug := mugF) layer2 gorIn_morIn_layer2 (A p) _ _ _ hp
      have hn := ih as (HoonMap.put m p a)
      conv => lhs; arg 2; unfold remSubT
      cases a <;> simp only [unitNoun] at hput <;>
        simp [nock_exec, listNoun, subMap, unitNoun, hT, by.arm_at, by_arm, by.put.arm_at, put_arm, hput, hn]

/-- **The gate `pass`**: `passArg` of the lookup of `sub`. -/
theorem rem_pass (T : Noun) (hT : slot? 0xffffff T = some layer2) (m : TreapMap mugF (Option Nat))
    (a : Option Nat) :
    nock (C remPassB (C (unitNoun A a) (C (HoonMap.toNoun (unitNoun A) m) T))) remPassB
      = some (unitNoun A (Opt.passArg (HoonMap.get m) a)) := by
  cases a with
  | none => simp [nock_exec, remPassB, unitNoun, Opt.passArg]
  | some r =>
    have hc : FallIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 := ⟨fall.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
    cases e : HoonMap.get m r with
    | none =>
      have hg : getF mugF (A r) (HoonMap.toNoun (unitNoun A) m) = some (A 0) := by
        rw [getF_hoonMap, e]; rfl
      have hgut := gut_gate (mug := mugF) layer2 hc (A r) (C (A 0) (A r)) _ _ hg (Or.inl rfl)
      simp [nock_exec, remPassB, unitNoun, Opt.passArg, e, hT, by.arm_at, by_arm, by.gut.arm_at, gut_arm, hgut]
    | some x =>
      have hg : getF mugF (A r) (HoonMap.toNoun (unitNoun A) m) = some (C (A 0) (unitNoun A x)) := by
        rw [getF_hoonMap, e]; rfl
      have hgut := gut_gate (mug := mugF) layer2 hc (A r) (C (A 0) (A r)) _ _ hg (Or.inr ⟨_, rfl⟩)
      simp [nock_exec, remPassB, unitNoun, Opt.passArg, e, hT, by.arm_at, by_arm, by.gut.arm_at, gut_arm, hgut]


end Compiler
end Formalization
