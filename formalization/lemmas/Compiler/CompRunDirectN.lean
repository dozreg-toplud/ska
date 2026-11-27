import lemmas.Compiler.CompRunTwo

/-!
# The direct call of the case `%2` of `+run`: the cut (`tools/gen/direct.py`)

`cr2Dir` (the branch of `?~  info.nomm` on `[~ b key]`) is
`[7 [0 1] [7 [0 1] [8 crDPure [6 crDTest crDDrop crDCall]]]]`: the `=*` of
`b-callee` and of `key` (no code but `[7 [0 1] _]`), the push of
`callee-pure` (`pure:(~(got by code.long-ska) b-callee)`, `crDPure`), the
test `&(callee-pure ?=(%next -.goal) (none-equivalent laz.goal))`
(`crDTest`), the dropped call (`crDDrop`, cut at its pushes: `crDNf` the run of `q`
under `+safe-fol-fol`, then `crDD1` from `+past`, `crDD2` from the run of
`p`, `crDD3` the `+copy`), and the call (`crDCall`, read from the pill).
`crd_eq` checks the cut against the pill.  README Gaps 19.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon

def crDD3 : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x55dae) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 0) (A 58)))) (C (A 0) (A 2))))))))

def crDD2 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 5) (C (A 10) (C (C (A 118) (C (C (A 1) (A 0x7478656e)) (C (C (A 1) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (A 11))))) (C (A 10) (C (C (A 58) (C (A 0) (A 2026))) (C (A 0) (A 15)))))))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) crDD3))))))))

def crDD1 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x2bfe) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (C (A 0) (A 2026)) (C (A 0) (A 2030))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) crDD2))))))))

def crDNf : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 767) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 2006))) (C (A 0) (A 2)))))))) (C (C (C (C (A 1) (A 0x7478656e)) (C (C (A 1) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (A 987)))) (C (A 0) (A 126))) (C (A 9) (C (A 5) (C (A 10) (C (C (A 118) (C (C (A 1) (A 0x7478656e)) (C (C (A 1) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (A 987))))) (C (A 10) (C (C (A 58) (C (A 0) (A 982))) (C (A 0) (A 3)))))))))))))

def crDDrop : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C crDNf (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) crDD1))))))))

def crDPure : Noun :=
  (C (A 7) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 4084))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 3934))) (C (A 0) (A 2)))))))) (C (A 0) (A 6))))

def crDTest : Noun :=
  (C (A 6) (C (C (A 0) (A 2)) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x7478656e)) (C (A 0) (A 492)))) (C (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 2811) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 2010))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1)))))

def crDCall : Noun := (slot? 35179473137663 comp.door).getD (A 0)

def crDHead : Noun :=
  C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C crDPure (C (A 6) (C crDTest (C crDDrop crDCall))))))))

/-- **The cut of the direct call**, checked against the pill. -/
theorem crd_eq : cr2Dir = crDHead := by kernel_rfl

/-- The test `?~  info.nomm` sends a direct call to `cr2Dir`. -/
theorem cr2_dir (P Q I mono goal region sup D : Noun) :
    nock (crSubj mono (C (A 2) (C P (C Q (C (A 0) I)))) goal region sup D) crK2
      = nock (crSubj mono (C (A 2) (C P (C Q (C (A 0) I)))) goal region sup D) cr2Dir := by
  rw [cr2_eq]
  unfold cr2Head
  simp [nock_exec, crSubj]

end Compiler
end Formalization
