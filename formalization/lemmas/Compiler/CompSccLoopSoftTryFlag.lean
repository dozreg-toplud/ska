import lemmas.Compiler.CompSccLoopSoftTryLast
import lemmas.Compiler.CompSccIn
import lemmas.Compiler.CompForlLink
import lemmas.Hoon.ListsSort

/-! # The flag path: the `|` side of `+soft-free` (README Gaps 21.22)

Generated in part by `tools/gen/softflag.py` (the definitions between `-- BEGIN softflag` and
`-- END softflag`): the arm of `+soft-try` (line 5517) and the battery of the gate `flag`
(`tpYH0Bat`, line 5370) cut at their pushes.
* `ty_try`: the gate `+soft-try` is the model's `softTry`. -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

-- BEGIN softflag

/- chains:
tyT26: 26 pushes, tail (16 cells)
tyF9: 9 pushes, tail (40 cells)
-/

def tyStBunt : Noun :=
  (C (A 0) (C (C (A 0x656e6f6e) (A 0)) (C (A 0) (C (A 0) (A 0)))))

def tyT26 : Noun :=
  (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 126)) (C (C (A 0) (A 62)) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 2044)) (C (A 0) (A 2)))))))) (C (A 0) (A 2))))))

def tyT25 : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0xaabbf) (C (A 0) (A 1023)))) tyT26))

def tyT24 : Noun :=
  (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) tyT25))

def tyTH23 : Noun :=
  (C (A 10) (C (C (A 4094) (C (A 0) (A 5))) (C (A 0) (A 1))))

def tyT23 : Noun :=
  (C (A 7) (C tyTH23 tyT24))

def tyTH22 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x6d6d69)) (C (C (A 1) (A 0)) (C (A 0) (A 6)))) (C (C (C (A 1) (A 0x6d6d69)) (C (C (A 1) (A 1)) (C (A 0) (A 2)))) (C (A 1) (A 0)))))) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0x706f68)) (C (C (A 8) (C (C (A 9) (C (A 0x17debe) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 254)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) (C (C (A 1) (A 0)) (C (A 0) (A 30)))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0)) (C (A 0) (A 2))))))) (C (A 0) (A 2)))))))) (C (A 0) (A 62))))))))) (C (A 0) (A 2))))))))))

def tyT22 : Noun :=
  (C (A 8) (C tyTH22 tyT23))

def tyT21 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) tyT22))

def tyT20 : Noun :=
  (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) tyT21))

def tyTH19 : Noun :=
  (C (A 10) (C (C (A 2046) (C (A 0) (A 5))) (C (A 0) (A 1))))

def tyT19 : Noun :=
  (C (A 7) (C tyTH19 tyT20))

def tyTH18 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 255))))))

def tyT18 : Noun :=
  (C (A 8) (C tyTH18 tyT19))

def tyT17 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) tyT18))

def tyT16 : Noun :=
  (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) tyT17))

def tyTH15 : Noun :=
  (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1))))

def tyT15 : Noun :=
  (C (A 7) (C tyTH15 tyT16))

def tyTH14 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 127))))))

def tyT14 : Noun :=
  (C (A 8) (C tyTH14 tyT15))

def tyT13 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) tyT14))

def tyT12 : Noun :=
  (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) tyT13))

def tyTH11 : Noun :=
  (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1))))

def tyT11 : Noun :=
  (C (A 7) (C tyTH11 tyT12))

def tyTH10 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0x706f68)) (C (C (A 8) (C (C (A 9) (C (A 0x17debe) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 348) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 5982) (C (A 0) (A 0x1ffffff)))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0)) (C (A 0) (A 502))))))) (C (A 0) (A 2)))))))) (C (A 0) (A 6))))))))) (C (A 0) (A 2))))))))))

def tyT10 : Noun :=
  (C (A 8) (C tyTH10 tyT11))

def tyT9 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) tyT10))

def tyT8 : Noun :=
  (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) tyT9))

def tyTH7 : Noun :=
  (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1))))

def tyT7 : Noun :=
  (C (A 7) (C tyTH7 tyT8))

def tyTH6 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 702) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xaebc) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 250))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2))))))))))

def tyT6 : Noun :=
  (C (A 8) (C tyTH6 tyT7))

def tyT5 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) tyT6))

def tyT4 : Noun :=
  (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) tyT5))

def tyTH3 : Noun :=
  (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1))))

def tyT3 : Noun :=
  (C (A 7) (C tyTH3 tyT4))

def tyTH2 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0x17debe) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 0) (A 494)))) (C (A 0) (A 2)))))))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 495))))))) (C (A 0) (A 2))))))))))

def tyT2 : Noun :=
  (C (A 8) (C tyTH2 tyT3))

def tyT1 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) tyT2))

def tyTH0 : Noun :=
  (C (A 8) (C (C (A 9) (C (A 348) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 58))) (C (A 0) (A 2))))))))

def tyT0 : Noun :=
  (C (A 8) (C tyTH0 tyT1))

def tyStArm : Noun :=
  (C (A 8) (C (C (A 1) tyStBunt) (C (C (A 1) tyT0) (C (A 0) (A 1)))))

def tyF9 : Noun :=
  (C (C (A 0) (A 5)) (C (A 8) (C (C (A 9) (C (A 350) (C (A 0) (A 8191)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 0x7ffdfe)) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x7a7262)))) (C (C (A 0) (A 13)) (C (C (A 0) (A 1015)) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0)) (C (A 0) (A 30)))))))))))) (C (A 0) (A 2)))))))))

def tyFH8 : Noun :=
  (C (A 10) (C (C (A 0x7ffe) (C (A 8) (C (C (A 9) (C (A 350) (C (A 0) (A 8191)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 0x3ffefe)) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0x17debe) (C (A 0) (A 0xffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1022)) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0x6d6d69)) (C (C (A 1) (A 0)) (C (A 0) (A 6)))))))) (C (A 0) (A 2)))))))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 12)))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1))))

def tyF8 : Noun :=
  (C (A 7) (C tyFH8 tyF9))

def tyF7 : Noun :=
  (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) tyF8))

def tyFH6 : Noun :=
  (C (A 10) (C (C (A 0x7ffe) (C (A 0) (A 5))) (C (A 0) (A 1))))

def tyF6 : Noun :=
  (C (A 7) (C tyFH6 tyF7))

def tyFH5 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 0) (A 126)) (C (A 8) (C (C (A 0) (A 2031)) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0x2fbd5) (C (A 0) (A 0x1ffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 1) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 6)))) (C (C (C (A 1) (A 0)) (C (A 0) (A 0x3fffe))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 0xffff)))))) (C (A 7) (C (C (A 10) (C (C (A 0x7fffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 9) (C (A 2398) (C (A 0) (A 0x1fffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2))))))))) (C (A 0) (A 3)))))))) (C (A 7) (C (C (A 10) (C (C (A 0xffffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 0) (A 6)) (C (A 0) (A 2))) (C (A 0) (A 0xffffe))))))))))))))))))))))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))))) (C (A 7) (C (C (A 10) (C (C (A 0x1fffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0x2fbd7f) (C (A 0) (A 0x3ffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0x2fbd7f) (C (A 0) (A 0x7ffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 1) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 14)))) (C (C (C (C (A 0) (A 62)) (C (A 0) (A 254))) (C (A 0) (A 0xffffe))) (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 8) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 13)))) (C (C (A 0) (A 254)) (C (A 0) (A 26))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x555df7) (C (A 0) (A 0x7ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 498)) (C (C (A 0) (A 499)) (C (C (A 0) (A 6)) (C (C (A 0) (A 60)) (C (A 0) (A 254))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 0x3ffffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 62) (C (A 0) (A 2))) (C (A 10) (C (C (A 14) (C (A 0) (A 125))) (C (A 10) (C (C (A 6) (C (A 0) (A 61))) (C (A 0) (A 7)))))))))))) (C (A 7) (C (C (A 10) (C (C (A 0x7ffffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 0) (A 4)) (C (A 0) (A 124))) (C (A 0) (A 0x7ffffe))))))))))))))))))))) (C (A 0) (A 0))))))))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))))))))))))))))))

def tyF5 : Noun :=
  (C (A 8) (C tyFH5 tyF6))

def tyF4 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) tyF5))

def tyF3 : Noun :=
  (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) tyF4))

def tyFH2 : Noun :=
  (C (A 10) (C (C (A 0x3ffe) (C (A 0) (A 5))) (C (A 0) (A 1))))

def tyF2 : Noun :=
  (C (A 7) (C tyFH2 tyF3))

def tyFH1 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 2047))))))

def tyF1 : Noun :=
  (C (A 8) (C tyFH1 tyF2))

def tyF0 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) tyF1))

-- END softflag

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem ty_st_at : slot? 3497463 comp.door = some tyStArm := by kernel_rfl

theorem ty_st_arm (d : Noun) : nock d tyStArm = some (C tyT0 (C tyStBunt d)) := by
  unfold tyStArm; simp only [nock_exec]

theorem ty_snoc_arm (c : Noun) : nock c snoc.arm = some (C snoc.battery (C (C (A 0) (A 0)) c)) := by
  nock_open snoc.arm; simp only [nock_exec]

/-! ## `+soft-try` -/

/-- The sample `[src ned pre f nxt]`. -/
abbrev tySam (src : Nat) (ned : Need) (pre f nxt : Nat) : Noun :=
  C (A src) (C ned.toNoun (C (A pre) (C (A f) (A nxt))))

/-- The subject of the battery of `+soft-try` after the pushes `l` (the last first). -/
abbrev tyTS (l : List Noun) (src : Nat) (ned : Need) (pre f nxt : Nat) (g : Gen (TreapMap mugF)) (x : GenRest)
    (ctx : Noun) : Noun :=
  l.foldr C (C tyT0 (C (tySam src ned pre f nxt) (compCore g x ctx)))

section stry

variable {ctx : Noun} (x : GenRest) (src : Nat) (ned : Need) (pre f nxt : Nat)

/-- `=/  out  (flatten-need ned)`. -/
theorem ty_t0 (hc : CompIn ctx) (g : Gen (TreapMap mugF)) :
    nock (tyTS [] src ned pre f nxt g x ctx) tyT0
      = nock (tyTS [listNoun A (flattenNeed ned)] src ned pre f nxt g x ctx) tyT1 := by
  have hD := comp_fn_at
  have hf := comp_flatten_need hc (genNoun g x) ned
  conv => { lhs; arg 2; unfold tyT0 tyTH0 }
  simp only [tyTS, tySam, List.foldr, compCore] at hf ⊢
  generalize comp.door = Dr at hD hf ⊢
  simp [nock_exec, hD, comp_fn_arm, hf]


/-- `=^  merge  gen  (emit (snoc out f) ~ %hop ~ nxt)`. -/
theorem ty_t1 (hc : CompIn ctx) (g : Gen (TreapMap mugF)) :
    nock (tyTS [listNoun A (flattenNeed ned)] src ned pre f nxt g x ctx) tyT1
      = nock (tyTS [A g.bo, listNoun A (flattenNeed ned)] src ned pre f nxt
          (cfEmitG ⟨flattenNeed ned ++ [f], [], Termin.hop (jmp0 nxt)⟩ g) x ctx) tyT5 := by
  have hD := comp_emit_at
  have he := cf_emit (x := x) hc g ⟨flattenNeed ned ++ [f], [], Termin.hop (jmp0 nxt)⟩
  have hs := snoc_gate layer2 weld.arm_at ((flattenNeed ned).map A) (A f)
  have hS := snoc.arm_at
  conv => { lhs; arg 2; unfold tyT1 tyT2 tyT3 tyT4 tyTH2 tyTH3 }
  simp only [Blob.toNoun, Termin.toNoun, Tag.hop, jmp0, Jmp.toNoun, cd_listNoun_listN, List.map_append,
    List.map, listN_nil] at he
  simp only [tyTS, tySam, List.foldr, compCore, cd_listNoun_listN, jmp0] at he ⊢
  generalize comp.door = Dr at hD he ⊢
  simp [nock_exec, hD, comp_emit_arm, he, hc, hS, ty_snoc_arm, hs]

/-- `=^  tem  gen  (need-ord-alloc-regs (need-to-ordered ned))`. -/
theorem ty_t5 (h7 : slot? 7 ctx = some compK) (m : Nat) (g : Gen (TreapMap mugF)) :
    nock (tyTS [A m, listNoun A (flattenNeed ned)] src ned pre f nxt g x ctx) tyT5
      = (needOrdAllocRegs (needToOrd ned) g).bind fun p =>
          nock (tyTS [p.1.toNoun, A m, listNoun A (flattenNeed ned)] src ned pre f nxt p.2 x ctx) tyT9 := by
  have hD := noar_at
  have hK := nta_at
  have hnt := nta_gate compK ned
  have hn := noar_gate ctx x (needToOrd ned) g
  conv => { lhs; arg 2; unfold tyT5 tyT6 tyT7 tyT8 tyTH6 tyTH7 }
  simp only [tyTS, tySam, List.foldr, compCore] at hn ⊢
  cases e : needOrdAllocRegs (needToOrd ned) g with
  | none =>
    rw [e] at hn
    generalize comp.door = Dr at hD hn ⊢
    simp [nock_exec, hD, hK, hnt, noarHint, ntaHint, h7, hn]
  | some p =>
    rw [e] at hn
    simp only [Option.map_some, Option.bind_some] at hn ⊢
    generalize comp.door = Dr at hD hn ⊢
    simp [nock_exec, hD, hK, hnt, noarHint, ntaHint, h7, hn]


/-- The `some` of `+turn` on registers: the units of the registers. -/
theorem ty_turn_some (l : List Nat) :
    nock (C turn.battery (C (C (listN (l.map A)) (C (C (C (A 1) (A 0)) (C (A 0) (A 6))) (C (A 0) layer2)))
      layer2)) turn.battery = some (listN (l.map fun r => C (A 0) (A r))) := by
  have h := turn_gate layer2 homoIn_layer2 (C (C (A 1) (A 0)) (C (A 0) (A 6))) (A 0) layer2 (fun n => C (A 0) n)
    (l.map A) (fun y _ => by simp [nock_exec])
  rw [h, List.map_map]; rfl

theorem ty_args_some (l : List Nat) (pre : Nat) :
    listNoun (unitNoun A) (l.map some ++ [some pre])
      = listN (l.map (fun r => C (A 0) (A r)) ++ [C (A 0) (A pre)]) := by
  rw [cd_listNoun_listN, List.map_append, List.map_map]; rfl

/-- `=^  good  gen  (emit ~ ~ [%hop (snoc (turn (flatten-need tem) some) `pre) merge])`. -/
theorem ty_t9 (hc : CompIn ctx) (tem : Need) (m : Nat) (g : Gen (TreapMap mugF)) :
    nock (tyTS [tem.toNoun, A m, listNoun A (flattenNeed ned)] src ned pre f nxt g x ctx) tyT9
      = nock (tyTS [A g.bo, tem.toNoun, A m, listNoun A (flattenNeed ned)] src ned pre f nxt
          (cfEmitG ⟨[], [], Termin.hop ⟨(flattenNeed tem).map some ++ [some pre], m⟩⟩ g) x ctx) tyT13 := by
  have hD := comp_emit_at
  have he := cf_emit (x := x) hc g ⟨[], [], Termin.hop ⟨(flattenNeed tem).map some ++ [some pre], m⟩⟩
  have hfn := comp_flatten_need hc (genNoun g x) tem
  have hD2 := comp_fn_at
  have ht := ty_turn_some (flattenNeed tem)
  have hs := snoc_gate layer2 weld.arm_at ((flattenNeed tem).map fun r => C (A 0) (A r)) (C (A 0) (A pre))
  have hS := snoc.arm_at
  have hT := turn.arm_at
  have hO := some.arm_at
  simp only [Blob.toNoun, Termin.toNoun, Tag.hop, Jmp.toNoun, ty_args_some, listNoun] at he
  rw [cd_listNoun_listN] at hfn
  conv => { lhs; arg 2; unfold tyT9 tyT10 tyT11 tyT12 tyTH10 tyTH11 }
  simp only [tyTS, tySam, List.foldr, compCore] at he hfn ⊢
  generalize comp.door = Dr at hD he hfn hD2 ⊢
  simp [nock_exec, hD, comp_emit_arm, he, hc, hS, ty_snoc_arm, hs, hD2, comp_fn_arm, hfn, hT, turn_arm, ht, hO]

/-- `=^  zero  gen  re`, `=^  one  gen  re`. -/
theorem ty_t13 (a b c d : Noun) (g : Gen (TreapMap mugF)) :
    nock (tyTS [a, b, c, d] src ned pre f nxt g x ctx) tyT13
      = nock (tyTS [A g.re, a, b, c, d] src ned pre f nxt { g with re := g.re + 1 } x ctx) tyT17 := by
  have hD := comp_re_at
  have hr := comp_re' ctx x g
  conv => { lhs; arg 2; unfold tyT13 tyT14 tyT15 tyT16 tyTH14 tyTH15 }
  simp only [tyTS, tySam, List.foldr, compCore] at hr ⊢
  generalize comp.door = Dr at hD hr ⊢
  simp [nock_exec, hD, hr]

theorem ty_t17 (a b c d e : Noun) (g : Gen (TreapMap mugF)) :
    nock (tyTS [a, b, c, d, e] src ned pre f nxt g x ctx) tyT17
      = nock (tyTS [A g.re, a, b, c, d, e] src ned pre f nxt { g with re := g.re + 1 } x ctx) tyT21 := by
  have hD := comp_re_at
  have hr := comp_re' ctx x g
  conv => { lhs; arg 2; unfold tyT17 tyT18 tyT19 tyT20 tyTH18 tyTH19 }
  simp only [tyTS, tySam, List.foldr, compCore] at hr ⊢
  generalize comp.door = Dr at hD hr ⊢
  simp [nock_exec, hD, hr]


/-- The `|=(* `zero)` of `+turn`: the unit of `zero` (axis `6` of the gate's context) at each. -/
theorem ty_turn_const (l : List Nat) (a z : Nat) (R : Noun) :
    nock (C turn.battery (C (C (listN (l.map A)) (C (C (C (A 1) (A 0)) (C (A 0) (A 30)))
      (C (A 0) (C (A a) (C (A z) R))))) layer2)) turn.battery = some (listN (l.map fun _ => C (A 0) (A z))) := by
  have h := turn_gate layer2 homoIn_layer2 (C (C (A 1) (A 0)) (C (A 0) (A 30))) (A 0) (C (A a) (C (A z) R))
    (fun _ => C (A 0) (A z)) (l.map A) (fun y _ => by simp [nock_exec])
  rw [h, List.map_map]; rfl

theorem ty_args_const (l : List Nat) (z one : Nat) :
    listNoun (unitNoun A) (l.map (fun _ => some z) ++ [some one])
      = listN (l.map (fun _ => C (A 0) (A z)) ++ [C (A 0) (A one)]) := by
  rw [cd_listNoun_listN, List.map_append, List.map_map]; rfl

/-- `=^  bad  gen  (emit ~ ~[[%imm 0 zero] [%imm 1 one]] [%hop (snoc (turn out |=(* `zero)) `one) merge])`. -/
theorem ty_t21 (hc : CompIn ctx) (one zero good : Nat) (tem : Need) (m : Nat) (g : Gen (TreapMap mugF)) :
    nock (tyTS [A one, A zero, A good, tem.toNoun, A m, listNoun A (flattenNeed ned)] src ned pre f nxt g x ctx) tyT21
      = nock (tyTS [A g.bo, A one, A zero, A good, tem.toNoun, A m, listNoun A (flattenNeed ned)] src ned pre f nxt
          (cfEmitG ⟨[], [Pole.imm (A 0) zero, Pole.imm (A 1) one],
            Termin.hop ⟨(flattenNeed ned).map (fun _ => some zero) ++ [some one], m⟩⟩ g) x ctx) tyT25 := by
  have hD := comp_emit_at
  have he := cf_emit (x := x) hc g ⟨[], [Pole.imm (A 0) zero, Pole.imm (A 1) one],
    Termin.hop ⟨(flattenNeed ned).map (fun _ => some zero) ++ [some one], m⟩⟩
  have hs := snoc_gate layer2 weld.arm_at ((flattenNeed ned).map fun _ => C (A 0) (A zero)) (C (A 0) (A one))
  have hS := snoc.arm_at
  have hT := turn.arm_at
  simp only [Blob.toNoun, Termin.toNoun, Tag.hop, Jmp.toNoun, ty_args_const, listNoun, Pole.toNoun, Tag.imm] at he
  conv => { lhs; arg 2; unfold tyT21 tyT22 tyT23 tyT24 tyTH22 tyTH23 }
  simp only [tyTS, tySam, List.foldr, compCore, cd_listNoun_listN] at he ⊢
  generalize comp.door = Dr at hD he ⊢
  simp [nock_exec, hD, comp_emit_arm, he, hc, hS, ty_snoc_arm, hs, hT, turn_arm, ty_turn_const]

/-- `(mono-try-call tem good [src bad])`. -/
theorem ty_t25 (hc : CompIn ctx) (bad one zero good : Nat) (tem : Need) (m : Nat) (g : Gen (TreapMap mugF)) :
    nock (tyTS [A bad, A one, A zero, A good, tem.toNoun, A m, listNoun A (flattenNeed ned)] src ned pre f nxt g x ctx)
        tyT25
      = (monoTryCall tem good src bad g).map fun p => C (A p.1) (genNoun p.2 x) := by
  have hD := mtc_at
  have hm := mtc_gate x hc tem good src bad g
  simp only [compCore] at hm
  conv => { lhs; arg 2; unfold tyT25 tyT26 }
  simp only [tyTS, tySam, List.foldr, compCore] at hm ⊢
  generalize comp.door = Dr at hD hm ⊢
  simp [nock_exec, hD, mtc_arm, hm]


/-- **`+soft-try`** (line 5517): the battery on `[src ned pre f nxt]` is the model's `softTry`. -/
theorem ty_try (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) (g : Gen (TreapMap mugF)) :
    nock (C tyT0 (C (tySam src ned pre f nxt) (compCore g x ctx))) tyT0
      = (softTry src ned pre f nxt g).map fun p => C (A p.1) (genNoun p.2 x) := by
  show nock (tyTS [] src ned pre f nxt g x ctx) tyT0 = _
  rw [ty_t0 x src ned pre f nxt hc g, ty_t1 x src ned pre f nxt hc g, ty_t5 x src ned pre f nxt h7]
  cases e : needOrdAllocRegs (needToOrd ned) (cfEmitG ⟨flattenNeed ned ++ [f], [], Termin.hop (jmp0 nxt)⟩ g) with
  | none =>
    simp [softTry, e, bind, StateT.bind, cf_emit_g]
  | some p =>
    obtain ⟨tem, g2⟩ := p
    simp only [Option.bind_some]
    rw [ty_t9 x src ned pre f nxt hc tem, ty_t13, ty_t17, ty_t21 x src ned pre f nxt hc, ty_t25 x src ned pre f nxt hc]
    simp [softTry, e, bind, StateT.bind, cf_emit_g, re]

end stry

end Compiler
end Formalization
