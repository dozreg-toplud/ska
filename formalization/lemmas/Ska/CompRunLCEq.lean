import lemmas.Ska.CompRunLC
import lemmas.Ska.CompFinishF

/-!
# `runLC` is `runL` without calls, and its blocks against the raw blocks

README Gaps 12.9 (twelfth session).

* `Nomm.noCall`: no `%2` anywhere.  `hinted_noCall`: on such a nomm `+hinted`
  does not read the code table, so `+past` and `+past-fork` answer the same
  for `env.cod` and `noCode` (`pastL_cod`, `pastFork_cod`).
* `sixNextLC_eq`: the copies of the arms of `%6` are the originals when the
  test's `+hinted` does not depend on the table.
* `runLC_eq`: **on a nomm without `%2`, `runLC env sup` is `runL`**, for
  every environment and every `sup`, so every definition and theorem about
  `runL` holds of `runLC` there, and the links of the Hoon's arms to `runL`
  stay as they are.  `finishLFC`: the final pass of `+compile-scc-in` with
  `runLC` (`finishLF` with `runLC env ~` from `gen0`, as line 3525 calls
  `run` with `sup` `~`); `finishLFC_eq`: it is `finishLF` without `%2`.
* `#guard` checks: `finishLFC` on whole functions that call, against the
  n-ary raw blocks of `tools/hoon/calldump.hoon` (after `+to-straight`,
  registers as the raw ones): the recursive callee `R` itself, a tail call,
  a call under `%4`, in the head of a cons, in a branch of a `%6`, as the
  test of a `%6`, with its product unused, two calls in sequence, and two
  calls in a cons.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel

open Nock

/-- No `%2` anywhere in the nomm. -/
def Nomm.noCall : Nomm → Bool
  | Nomm.cons p q => p.noCall && q.noCall
  | Nomm.n0 _ => true
  | Nomm.n1 _ => true
  | Nomm.n2 _ _ _ => false
  | Nomm.n3 p => p.noCall
  | Nomm.n4 p => p.noCall
  | Nomm.n5 p q => p.noCall && q.noCall
  | Nomm.n6 p q r => p.noCall && q.noCall && r.noCall
  | Nomm.n7 p q => p.noCall && q.noCall
  | Nomm.n10 _ v q => v.noCall && q.noCall
  | Nomm.n11s _ q _ => q.noCall
  | Nomm.n11d _ h q _ => h.noCall && q.noCall
  | Nomm.n12 p q => p.noCall && q.noCall
  | Nomm.mean p _ q _ _ => p.noCall && q.noCall

/-- A pure nomm has no `%2`. -/
theorem Nomm.noCall_of_pure : ∀ (nm : Nomm), nm.pure = true → nm.noCall = true := by
  intro nm
  induction nm <;> simp_all [Nomm.pure, Nomm.noCall]

namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- **Without `%2`, `+hinted` does not read the code table.** -/
theorem hinted_noCall (c c' : Bell → Option Bool) : ∀ (nm : Nomm), nm.noCall = true →
    hinted c nm = hinted c' nm := by
  intro nm
  induction nm <;> simp_all [hinted, Nomm.noCall]

theorem pastL_cod {c c' : Bell → Option Bool} {nom : Nomm} (h : hinted c nom = hinted c' nom)
    (nex : NextL S) (region : List Nat) :
    (pastL c nex nom region : CM Map (NextL S)) = pastL c' nex nom region := by
  unfold pastL; rw [h]

theorem pastFork_cod {c c' : Bell → Option Bool} {nom : Nomm} (h : hinted c nom = hinted c' nom)
    (laz : Lazy S) : pastFork c laz nom = pastFork c' laz nom := by
  unfold pastFork; rw [h]

/-- **The copies of the arms of `%6` are the originals** when the test's
`+hinted` does not depend on the table. -/
theorem sixNextLC_eq [HoonMapKeys Map] {cod : Bell → Option Bool}
    (rp rq rr : CGoalL S → List Nat → CM Map (NextL S)) (p q r : Nomm)
    (h : hinted cod p = hinted noCode p) :
    ∀ (fuel : Nat) (laz : Lazy S) (th : Jmp) (region : List Nat),
      (sixNextLC cod rp rq rr p q r fuel laz th region : CM Map (NextL S)) =
        sixNextL rp rq rr p q r fuel laz th region := by
  have hf : ∀ laz : Lazy S, pastFork cod laz p = pastFork noCode laz p := fun laz => pastFork_cod h laz
  intro fuel
  induction fuel with
  | zero => intro _ _ _; rfl
  | succ fuel ih =>
    intro laz th region
    simp only [sixNextLC, sixNextL, sixNextForkC, sixNextFork, sixNextSimpleC, sixNextSimple, hf, ih] <;> rfl

/-- **On a nomm without `%2`, `runLC` is `runL`**, for every environment and
every `sup`. -/
theorem runLC_eq [HoonMapKeys Map] (env : CallEnv) : ∀ (nm : Nomm), nm.noCall = true →
    ∀ (sup : Option Nomm) (goal : CGoalL S) (region : List Nat),
      (runLC env sup nm goal region : CM Map (NextL S)) = runL nm goal region := by
  intro nm
  induction nm with
  | cons p q ihp ihq =>
    intro h sup goal region
    simp only [Nomm.noCall, Bool.and_eq_true] at h
    have hp := hinted_noCall env.cod noCode p h.1
    have hq := hinted_noCall env.cod noCode q h.2
    simp only [runLC, runL, ihp h.1, ihq h.2, pastL_cod hp, pastL_cod hq] <;> rfl
  | n0 _ => intro _ _ _ _; simp only [runLC, runL] <;> rfl
  | n1 _ => intro _ _ _ _; simp only [runLC, runL] <;> rfl
  | n2 _ _ _ => intro h; simp [Nomm.noCall] at h
  | n3 p ihp =>
    intro h sup goal region
    simp only [Nomm.noCall] at h
    simp only [runLC, runL, ihp h] <;> rfl
  | n4 p ihp =>
    intro h sup goal region
    simp only [Nomm.noCall] at h
    simp only [runLC, runL, ihp h] <;> rfl
  | n5 p q ihp ihq =>
    intro h sup goal region
    simp only [Nomm.noCall, Bool.and_eq_true] at h
    have hp := hinted_noCall env.cod noCode p h.1
    simp only [runLC, runL, ihp h.1, ihq h.2, pastL_cod hp] <;> rfl
  | n6 p q r ihp ihq ihr =>
    intro h sup goal region
    simp only [Nomm.noCall, Bool.and_eq_true] at h
    have hp := hinted_noCall env.cod noCode p h.1.1
    have ep : (runLC env sup p : CGoalL S → List Nat → CM Map (NextL S)) = runL p :=
      funext fun g => funext fun rg => ihp h.1.1 sup g rg
    have eq : (runLC env sup q : CGoalL S → List Nat → CM Map (NextL S)) = runL q :=
      funext fun g => funext fun rg => ihq h.1.2 sup g rg
    have er : (runLC env sup r : CGoalL S → List Nat → CM Map (NextL S)) = runL r :=
      funext fun g => funext fun rg => ihr h.2 sup g rg
    cases goal with
    | next laz th =>
      simp only [runLC, runL, ep, eq, er]
      exact sixNextLC_eq _ _ _ p q r hp 3 laz th region
    | done => simp only [runLC, runL, ihp h.1.1, ihq h.1.2, ihr h.2, pastFork_cod hp]
    | pick z o => simp only [runLC, runL, ihp h.1.1, ihq h.1.2, ihr h.2, pastFork_cod hp] <;> rfl
  | n7 p q ihp ihq =>
    intro h sup goal region
    simp only [Nomm.noCall, Bool.and_eq_true] at h
    simp only [runLC, runL, ihp h.1, ihq h.2] <;> rfl
  | n10 a v q ihv ihq =>
    intro h sup goal region
    simp only [Nomm.noCall, Bool.and_eq_true] at h
    have hv := hinted_noCall env.cod noCode v h.1
    have hq := hinted_noCall env.cod noCode q h.2
    simp only [runLC, runL, ihv h.1, ihq h.2, pastL_cod hv, pastL_cod hq] <;> rfl
  | n11s _ _ _ _ => intro _ _ _ _; simp only [runLC, runL] <;> rfl
  | n11d _ _ _ _ _ _ => intro _ _ _ _; simp only [runLC, runL] <;> rfl
  | n12 _ _ _ _ => intro _ _ _ _; simp only [runLC, runL] <;> rfl
  | mean _ _ _ _ _ _ _ => intro _ _ _ _; simp only [runLC, runL] <;> rfl

/-- **The final pass of `+compile-scc-in` with calls**: `finishLF` with
`runLC env ~` (line 3525: `(~(run comp gen) | nomm [%done ~] ~ ~)`). -/
def finishLFC [HoonMapKeys Map] (env : CallEnv) (nm : Nomm) (ord : NeedOrd) (less : Cape)
    (bake : Need → Need × List (Nat × Noun)) : Option (Straight Map) :=
  (runLC env Option.none nm (CGoalL.done : CGoalL S) [] gen0).bind fun (nex, g1) =>
    if nex.th.args ≠ [] then Option.none else
    (needOrdAllocRegs ord g1).bind fun (nedFinal, g2) =>
      let bak := bake nedFinal
      (coerceLazyL nedFinal less nex.th.there nex.laz g2).bind fun (_, g3) =>
        (addOps nex.th.there (bak.2.map fun (r, v) => Pole.imm v r) g3).bind fun (_, g4) =>
          toStraightF g4.cond g4.blocks bak.1 nex.th.there

/-- **Without `%2`, the final pass with calls is `finishLF`.** -/
theorem finishLFC_eq [HoonMapKeys Map] (env : CallEnv) {nm : Nomm} (h : nm.noCall = true) (ord : NeedOrd)
    (less : Cape) (bake : Need → Need × List (Nat × Noun)) :
    finishLFC (S := S) (Map := Map) env nm ord less bake = finishLF (S := S) nm ord less bake := by
  unfold finishLFC finishLF
  rw [runLC_eq env nm h]

/-! ## Checks against the raw blocks of whole functions -/

/-- The blocks `0 ..< n` of the code `finishLFC` makes for `nm`, the need
`ord`, the cape `cape` and nothing baked, in the environment of the dumps. -/
def wholeOut (nm : Nomm) (ord : NeedOrd) (cape : Cape) (n : Nat) : Option (List (Nat × Option Blob)) :=
  (finishLFC (S := LS) (Map := FM) envR nm ord cape (fun ned => (ned, []))).map fun c =>
    (List.range n).map fun k => (k, c.blocks.f k)

/-- `[8 [1 R] [9 2 [0 1]]]` as the analysis leaves it:
`[7 [[1 R] [0 1]] [7 [0 1] [2 [0 1] [1 R] [R-bell ~]]]]`. -/
def callTop : Nomm := Nomm.n7 (Nomm.cons (Nomm.n1 nounR) (Nomm.n0 1)) (Nomm.n7 (Nomm.n0 1) callR)

/-- The nomm of `R`: `[6 [3 [0 3]] [7 [10 [3 [0 7]] [0 1]] [2 [0 1] [1 R] [R-bell ~]]] [0 3]]`. -/
def nommR : Nomm :=
  Nomm.n6 (Nomm.n3 (Nomm.n0 3)) (Nomm.n7 (Nomm.n10 3 (Nomm.n0 7) (Nomm.n0 1)) callR) (Nomm.n0 3)

/-- A block with no parameters. -/
abbrev bk (body : List Pole) (fin : Termin) : Option Blob := some ⟨[], body, fin⟩

/-- A hop to `o`. -/
abbrev hp (o : Nat) : Termin := Termin.hop (jmp0 o)

/- `R` itself (need `[~ this]`, cape `[& |]`): `0w0 mov v0 v3, hop 8`;
`0w1 don v1`; `0w2 jmp R-bell [v2]`; `0w6 mov v0 v4, cel v4, tal v4 v5, mov
v5 v2, hop 2`; `0w7 mov v0 v1, hop 1`; `0w8 clq v3 6 7`. -/
#guard wholeOut nommR (NeedOrd.pair NeedOrd.none NeedOrd.this) (Cape.cell Cape.yes Cape.no) 10 ==
  some [(0, bk [Pole.mov 0 3] (hp 8)), (1, bk [] (Termin.don 1)), (2, bk [] (Termin.jmp bellR [2])),
    (3, none), (4, none), (5, none),
    (6, bk [Pole.mov 0 4, Pole.cel 4, Pole.tal 4 5, Pole.mov 5 2] (hp 2)),
    (7, bk [Pole.mov 0 1] (hp 1)), (8, bk [] (Termin.clq 3 (jmp0 6) (jmp0 7))), (9, none)]

/- The tail call `[8 [1 R] [9 2 [0 1]]]`: `0w0 mov v0 v1, hop 1`;
`0w1 jmp R-bell [v1]`. -/
#guard wholeOut callTop NeedOrd.this Cape.no 3 ==
  some [(0, bk [Pole.mov 0 1] (hp 1)), (1, bk [] (Termin.jmp bellR [1])), (2, none)]

/- Under `%4`: `0w0 mov v0 v3, hop 3`; `0w1 inc v2 v1, don v1`; `0w2 mov
v4 v2, hop 1`; `0w3 cal R-bell [v3] v4, hop 2`. -/
#guard wholeOut (Nomm.n4 callTop) NeedOrd.this Cape.no 5 ==
  some [(0, bk [Pole.mov 0 3] (hp 3)), (1, bk [Pole.inc 2 1] (Termin.don 1)),
    (2, bk [Pole.mov 4 2] (hp 1)), (3, bk [Pole.cal bellR [3] 4] (hp 2)), (4, none)]

/- In the head of a cons (the tail's need is bound behind the call: `+past`
of a call of an impure callee): `0w0 mov v0 v4, hop 5`; `0w1 don v1`; `0w2
con v2 v3 v1, hop 1`; `0w3 mov v0 v3, hop 2`; `0w4 mov v5 v2, hop 3`; `0w5
cal R-bell [v4] v5, hop 4`. -/
#guard wholeOut (Nomm.cons callTop (Nomm.n0 1)) NeedOrd.this Cape.no 7 ==
  some [(0, bk [Pole.mov 0 4] (hp 5)), (1, bk [] (Termin.don 1)), (2, bk [Pole.con 2 3 1] (hp 1)),
    (3, bk [Pole.mov 0 3] (hp 2)), (4, bk [Pole.mov 5 2] (hp 3)), (5, bk [Pole.cal bellR [4] 5] (hp 4)),
    (6, none)]

/- In a branch of a `%6`: `0w0 mov v0 v3, hop 9`; `0w1 imm 0 v1, don v1`;
`0w2 jmp R-bell [v2]`; `0w7 mov v0 v2, hop 2`; `0w9 clq v3 7 1`. -/
#guard wholeOut (Nomm.n6 (Nomm.n3 (Nomm.n0 1)) callTop (Nomm.n1 (A 0))) NeedOrd.this Cape.no 11 ==
  some [(0, bk [Pole.mov 0 3] (hp 9)), (1, bk [Pole.imm (A 0) 1] (Termin.don 1)),
    (2, bk [] (Termin.jmp bellR [2])), (3, none), (4, none), (5, none), (6, none),
    (7, bk [Pole.mov 0 2] (hp 2)), (8, none), (9, bk [] (Termin.clq 3 (jmp0 7) (jmp0 1))), (10, none)]

/- As the test of a `%6`: `0w0 mov v0 v3, hop 7`; `0w1 imm 1 v1, don v1`;
`0w2 imm 0 v2, don v2`; `0w5 brn v4 2 1`; `0w6 mov v5 v4, hop 5`; `0w7 cal
R-bell [v3] v5, hop 6`. -/
#guard wholeOut (Nomm.n6 callTop (Nomm.n1 (A 0)) (Nomm.n1 (A 1))) NeedOrd.this Cape.no 9 ==
  some [(0, bk [Pole.mov 0 3] (hp 7)), (1, bk [Pole.imm (A 1) 1] (Termin.don 1)),
    (2, bk [Pole.imm (A 0) 2] (Termin.don 2)), (3, none), (4, none),
    (5, bk [] (Termin.brn 4 (jmp0 2) (jmp0 1))), (6, bk [Pole.mov 5 4] (hp 5)),
    (7, bk [Pole.cal bellR [3] 5] (hp 6)), (8, none)]

/- The product unused (`R` is impure, the call is kept): `0w0 mov v0 v2,
hop 3`; `0w1 imm 5 v1, don v1`; `0w3 cal R-bell [v2] v3, hop 1`. -/
#guard wholeOut (Nomm.n7 callTop (Nomm.n1 (A 5))) NeedOrd.this Cape.no 5 ==
  some [(0, bk [Pole.mov 0 2] (hp 3)), (1, bk [Pole.imm (A 5) 1] (Termin.don 1)), (2, none),
    (3, bk [Pole.cal bellR [2] 3] (hp 1)), (4, none)]

/- Two calls in sequence, the second a tail call: `0w0 mov v0 v2, hop 7`;
`0w1 jmp R-bell [v1]`; `0w6 mov v3 v1, hop 1`; `0w7 cal R-bell [v2] v3,
hop 6`. -/
#guard wholeOut (Nomm.n7 callTop callTop) NeedOrd.this Cape.no 9 ==
  some [(0, bk [Pole.mov 0 2] (hp 7)), (1, bk [] (Termin.jmp bellR [1])), (2, none), (3, none),
    (4, none), (5, none), (6, bk [Pole.mov 3 1] (hp 1)), (7, bk [Pole.cal bellR [2] 3] (hp 6)), (8, none)]

/- Two calls in a cons, the second under `%4`: `0w0 mov v0 v7, hop d`;
`0w1 don v1`; `0w2 con v2 v3 v1, hop 1`; `0w3 mov v8 v2, hop 2`; `0w4 inc v4
v3, hop 3`; `0w5 mov v6 v4, hop 4`; `0w6 cal R-bell [v5] v6, hop 5`; `0wb
mov v0 v5, hop 6`; `0wd cal R-bell [v7] v8, hop b`. -/
#guard wholeOut (Nomm.cons callTop (Nomm.n4 callTop)) NeedOrd.this Cape.no 15 ==
  some [(0, bk [Pole.mov 0 7] (hp 13)), (1, bk [] (Termin.don 1)), (2, bk [Pole.con 2 3 1] (hp 1)),
    (3, bk [Pole.mov 8 2] (hp 2)), (4, bk [Pole.inc 4 3] (hp 3)), (5, bk [Pole.mov 6 4] (hp 4)),
    (6, bk [Pole.cal bellR [5] 6] (hp 5)), (7, none), (8, none), (9, none), (10, none),
    (11, bk [Pole.mov 0 5] (hp 6)), (12, none), (13, bk [Pole.cal bellR [7] 8] (hp 11)), (14, none)]

end Comp
end SkaModel
end Formalization
