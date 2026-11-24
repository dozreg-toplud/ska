import lemmas.Compiler.CompClaLink
import lemmas.Compiler.TreapList

/-!
# `+run` of the door of `+comp`: its frame, `+simple-next`, and the case `%0`

`+run` (door axis `2047`) is the gate `|=  [mono=? =nomm =goal region=(list
@uxid) sup=(unit nomm)]` whose body is a `|^` core: its battery is
`[simple-next $]` (`runSn`, `runDol`), pushed on the gate's core by the gate's
battery `runB` = `[8 [1 runBat] 9 5 0 1]`.  So the `$` arm runs on

    [runBat [runB [[mono nomm goal region sup] [comp.door [gen ctx]]]]]

with `mono` at `28`, `nomm` at `58`, `goal` at `118`, `region` at `238`,
`sup` at `239`, the door's core at `15` and `gen` at `62`.  A recursive
`$(nomm .., goal ..)` is `[9 5 10 [118 ..] 10 [58 ..] ..]` on that core,
with `gen` edited in place first, so `RunAt` (the `$` arm on a nomm and a
goal equals `runL`) is stated on this subject, for every `mono` and `sup`:
`runL` takes neither, and the cases it models (all but `%2` and `%11`) read
neither (`mono` is read in `%2` and `%mean`, `sup` in `%2` and written in
`%7`).

`runDol` is the `?-` over the nomm: a chain of twelve tests (`[^ *]`,
`%0`, `%1`, `%2`, `%3`, `%4`, `%5`, `%6`, `%7`, `%10`, `%11`, `%mean`) and
the last case `%12`.  The bodies of the cases linked here are written out;
the others are read from the pill (`(slot? k comp.door).getD (A 0)`); one
kernel fact ties the whole arm to the pill (`comp_run_at`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

def runSn : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x7478656e)) (C (A 0) (A 236)))) (C (C (C (A 0) (A 118)) (C (A 0) (A 62))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 15)))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 7) (C (C (A 0) (A 3)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f64)) (C (A 0) (A 492)))) (C (C (C (A 1) (A 0x6e6f64)) (C (A 0) (A 2))) (C (C (A 1) (A 0x6e7262)) (C (C (A 0) (A 2)) (C (A 7) (C (C (A 0) (A 246)) (C (C (A 0) (A 6)) (C (A 0) (A 7))))))))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 1) (A 0x7478656e)) (C (C (C (C (C (A 1) (A 0x73696874)) (C (A 0) (A 6))) (C (A 1) (A 0))) (C (A 1) (C (A 0) (A 0)))) (C (C (A 1) (A 0)) (C (A 0) (A 2))))) (C (A 0) (A 254))))))))))))))))))))))

def runKc : Noun := (slot? 16774878 comp.door).getD (A 0)

def runK0 : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 117)))) (C (C (A 8) (C (C (A 9) (C (A 1364) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x7478656e)) (C (A 0) (A 236)))) (C (C (C (A 1) (A 0)) (C (A 0) (A 951))) (C (A 1) (A 0)))))))) (C (A 0) (A 2)))))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 4) (C (A 0) (A 1)))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 245)))) (C (C (C (A 0) (A 2)) (C (A 0) (A 126))) (C (C (C (A 1) (A 0x7478656e)) (C (C (A 8) (C (C (A 9) (C (A 5630) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 501)) (C (A 0) (A 26)))) (C (A 0) (A 2)))))))) (C (A 0) (A 11)))) (C (A 0) (A 126)))))))))))))))))

def runK1 : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f64)) (C (A 0) (A 236)))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 15)))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x6d6d69)) (C (C (A 0) (A 245)) (C (A 0) (A 2)))) (C (A 1) (A 0))))) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0x6e6f64)) (C (A 0) (A 2)))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 1) (A 0x7478656e)) (C (C (A 1) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (C (A 1) (A 0)) (C (A 0) (A 2))))) (C (A 0) (A 254))))))))))))))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6b636970)) (C (A 0) (A 236)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 117)))) (C (C (C (C (A 1) (A 0x7478656e)) (C (C (A 1) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (A 474)))) (C (A 0) (A 62))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 117)))) (C (C (C (C (A 1) (A 0x7478656e)) (C (C (A 1) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (A 475)))) (C (A 0) (A 62))) (C (A 11) (C (C (A 0x73736f74) (C (A 1) (A 0))) (C (A 8) (C (C (A 9) (C (A 1364) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0))))) (C (A 0) (A 2)))))))))))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x7478656e)) (C (A 0) (A 236))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaab) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 987)) (C (C (A 0) (A 245)) (C (A 0) (A 986))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 1) (A 0x7478656e)) (C (C (A 1) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (C (A 1) (A 0)) (C (A 0) (A 2))))) (C (A 0) (A 126)))))))))))))))))))

def runK2 : Noun := (slot? 8588738558 comp.door).getD (A 0)

def runK3 : Noun := (slot? 68709908478 comp.door).getD (A 0)

def runK4 : Noun := (slot? 549679267838 comp.door).getD (A 0)

def runK5 : Noun := (slot? 4397434142718 comp.door).getD (A 0)

def runK6 : Noun := (slot? 35179473141758 comp.door).getD (A 0)

def runK7 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 5) (C (A 10) (C (C (A 239) (C (C (A 1) (A 0)) (C (A 0) (A 234)))) (C (A 10) (C (C (A 58) (C (A 0) (A 235))) (C (A 0) (A 1)))))))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 9) (C (A 5) (C (A 10) (C (C (A 118) (C (A 0) (A 2))) (C (A 10) (C (C (A 58) (C (A 0) (A 490))) (C (A 0) (A 3))))))))))))))))

def runK10 : Noun := (slot? 2251486281072638 comp.door).getD (A 0)

def runK11 : Noun := (slot? 18011890248581118 comp.door).getD (A 0)

def runKmean : Noun := (slot? 144095121988648958 comp.door).getD (A 0)

def runLast : Noun := (slot? 144095121988648959 comp.door).getD (A 0)

/-- The test `?=([%k *] nomm)` of the `?-` (the cell test first). -/
def runT (k : Nat) : Noun :=
  C (A 6) (C (C (A 3) (C (A 0) (A 58))) (C (C (A 5) (C (C (A 1) (A k)) (C (A 0) (A 116)))) (C (A 1) (A 1))))

/-- The test `?=([^ *] nomm)`. -/
def runTc : Noun :=
  C (A 6) (C (C (A 3) (C (A 0) (A 58))) (C (C (A 3) (C (A 0) (A 116))) (C (A 1) (A 1))))

/-- The `$` arm of the `|^` core: the `?-` over the nomm. -/
def runDol : Noun :=
  C (A 6) (C runTc (C runKc
  (C (A 6) (C (runT 0) (C runK0
  (C (A 6) (C (runT 1) (C runK1
  (C (A 6) (C (runT 2) (C runK2
  (C (A 6) (C (runT 3) (C runK3
  (C (A 6) (C (runT 4) (C runK4
  (C (A 6) (C (runT 5) (C runK5
  (C (A 6) (C (runT 6) (C runK6
  (C (A 6) (C (runT 7) (C runK7
  (C (A 6) (C (runT 10) (C runK10
  (C (A 6) (C (runT 11) (C runK11
  (C (A 6) (C (runT 0x6e61656d) (C runKmean runLast)))))))))))))))))))))))))))))))))))

/-- The battery of the `|^` core: `[simple-next $]`. -/
def runBat : Noun := C runSn runDol

/-- The battery of the gate: push the `|^` battery, run `$`. -/
def runB : Noun := C (A 8) (C (C (A 1) runBat) (C (A 9) (C (A 5) (C (A 0) (A 1)))))

/-- The bunt of the sample: `[& [0 0] [%next [[[%none ~] ~] ~ ~] ~ 0] ~ ~]`. -/
def runBunt : Noun :=
  C (A 0) (C (C (A 0) (A 0)) (C (C (A 0x7478656e) (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))) (C (A 0) (A 0)))) (C (A 0) (A 0))))

/-- The arm `+run`. -/
def runArm : Noun :=
  C (A 7) (C (C (A 8) (C (C (A 1) runBunt) (C (C (A 1) runB) (C (A 0) (A 1)))))
    (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x6e75722d706d6f63) (C (C (A 0) (A 0x7ffff)) (A 0))))) (C (A 0) (A 1)))))

/-- **`+run` is arm `2047` of the door.** -/
theorem comp_run_at : slot? 2047 comp.door = some runArm := by kernel_rfl

/-! ## The subject of `$` and the predicate `RunAt` -/

/-- The core of the `|^`: its battery on the gate's core, whose sample is
`[mono nomm goal region sup]` and whose context is the door's core `D`. -/
def runSubj (mono nomm goal region sup D : Noun) : Noun :=
  C runBat (C runB (C (C mono (C nomm (C goal (C region sup)))) D))

/-- `soft` has no key: `(~(has by soft.gen) o)` is `|` for every block, the
branch the models take (they take `soft` to be empty). -/
def GenRest.NoSoft (x : GenRest) : Prop := ∀ o, x.SoftOut o

/-- **The `$` arm of `+run` on the noun of a nomm and a goal is `runL`**, from
the state `g`, for every `mono`, `sup` and every rest `x` of the state with an
empty `soft` (kept as it is). -/
def RunAt (ctx : Noun) (n : Nomm) (goal : CGoalL CSet) (region : List Nat)
    (g : Gen (TreapMap mugF)) : Prop :=
  ∀ (x : GenRest) (mono sup : Noun), x.NoSoft →
    nock (runSubj mono n.toNoun goal.toNoun (listNoun A region) sup (compCore g x ctx)) runDol
      = (runL n goal region g).map fun p => C p.1.goal.toNoun (genNoun p.2 x)

/-! ## `+simple-next` -/

theorem run_re_at : slot? 3538943 comp.door = some comp.re.arm := comp_re_at

variable {ctx : Noun}

/-- **`+simple-next`** is `simpleNextL`: the goal itself when it is `%next`,
otherwise a fresh register `r` and a block that returns it (`%done`) or
branches on it (`%pick`), with the need `[[%this r] ~] ~ ~]`. -/
theorem run_simple_next (hc : CompIn ctx) (x : GenRest) (g : Gen (TreapMap mugF))
    (goal : CGoalL CSet) (mono nomm region sup : Noun) :
    nock (runSubj mono nomm goal.toNoun region sup (compCore g x ctx)) runSn
      = (simpleNextL goal g).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  have hre := comp_re' ctx x g
  have hD1 := comp_re_at
  have hD2 := comp_emit_at
  simp only [compCore] at hre ⊢
  cases goal with
  | next laz th =>
    unfold runSn
    simp [nock_exec, runSubj, CGoalL.toNoun, simpleNextL, NextL.goal, pure, StateT.pure]
  | done =>
    have he := comp_emit x hc { g with re := g.re + 1 } ⟨[], [], Termin.don g.re⟩
    simp only [compCore, Blob.toNoun, listNoun, Termin.toNoun, Tag.don] at he
    rw [cd_emit_eq] at he
    generalize comp.door = Dr at hD1 hD2 he hre ⊢
    unfold runSn
    simp [nock_exec, runSubj, CGoalL.toNoun, simpleNextL, NextL.goal, hre, hD1, hD2, comp_emit_arm, he,
      cd_emit_eq, re, bind, StateT.bind, pure, StateT.pure, Lazy.toNoun_ofSure, lazyNoun, Sure.toNoun,
      Need.toNoun, HoonSet.toNoun_empty, Jmp.toNoun, jmp0, listNoun, Tag.this]
  | pick z o =>
    have he := comp_emit x hc { g with re := g.re + 1 } ⟨[], [], Termin.brn g.re z o⟩
    simp only [compCore, Blob.toNoun, listNoun, Termin.toNoun, Tag.brn, Jmp.toNoun] at he
    rw [cd_emit_eq] at he
    generalize comp.door = Dr at hD1 hD2 he hre ⊢
    unfold runSn
    simp [nock_exec, runSubj, CGoalL.toNoun, simpleNextL, NextL.goal, hre, hD1, hD2, comp_emit_arm, he,
      cd_emit_eq, re, bind, StateT.bind, pure, StateT.pure, Lazy.toNoun_ofSure, lazyNoun, Sure.toNoun,
      Need.toNoun, HoonSet.toNoun_empty, Jmp.toNoun, jmp0, listNoun, Tag.this]

end Compiler
end Formalization
