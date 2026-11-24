import lemmas.Compiler.CompStraightStep

/-!
# `+bind` and `+lift` of `layer2`, and the gate `rj` of `+chase-fin`

```hoon
++  bind                                                ::  argue
  |*  [a=(unit) b=$-(* *)]
  ?~  a  ~
  [~ u=(b u.a)]
::
++  lift                                                ::  lift mold (fmap)
  |*  a=mold                                            ::  flipped rendering
  |*  b=(unit)  (bind b a)                              ::
```

`+bind` is arm `5983` of `layer2`, a gate whose battery is `lfBindBat`
(`lf_bind_at`).  `+lift` is arm `372`, a gate whose sample bunt is a mold
core (`lfLiftBunt`, read from the pill) and whose battery `lfLiftBat`
builds the inner gate `lfLiftIn` with the sample `0`; the inner gate pulls
`+bind` from its context's `layer2` and slams it on `[b a]` (`lf_lift_at`).

With them `(turn args.j (lift ren))` renames the registers of the jump
(`lf_turn`), so the gate `rj` of `+chase-fin` is `renJmp` (`lf_rj`), the
link `TsRjAt` holds (`lf_ts_rj`), and the end of `+compile-unary` holds with
no hypothesis on `+to-straight` (`cu_finish_all`).  The gate `ren-jmp` of
`+map-regs` (`mrRjBody`) is the same Nock at other axes (`lf_mr_rj`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The sample bunt of `+bind`, `[~ *$-(* *)]`. -/
def lfBindBunt : Noun := C (A 0) (C (C (A 0) (A 15)) (C (A 0) (C (A 0) (A 0))))

/-- The battery of `+bind`: `?~  a  ~`, `[~ (b u.a)]`. -/
def lfBindBat : Noun :=
  C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 12))))
    (C (C (A 1) (A 0)) (C (C (A 1) (A 0))
      (C (A 8) (C (C (A 0) (A 13)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 57))) (C (A 0) (A 2)))))))))))

/-- **The arm `+bind`** of `layer2`, a kernel fact. -/
theorem lf_bind_at : slot? 5983 layer2
    = some (C (A 8) (C (C (A 1) lfBindBunt) (C (C (A 1) lfBindBat) (C (A 0) (A 1))))) := by
  kernel_rfl

/-- The battery of the inner gate of `+lift`: `(bind b a)`. -/
def lfLiftIn : Noun :=
  C (A 8) (C (C (A 9) (C (A 5983) (C (A 0) (A 31))))
    (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 0) (A 62)))) (C (A 0) (A 2)))))))

/-- The battery of `+lift`: the inner gate with the sample `0`. -/
def lfLiftBat : Noun := C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) lfLiftIn) (C (A 0) (A 1))))

/-- The slam of `+lift` on a gate `G`: the inner gate with the sample `0`. -/
theorem lf_lift_slam (G c : Noun) :
    nock (C lfLiftBat (C G c)) lfLiftBat = some (C lfLiftIn (C (A 0) (C lfLiftBat (C G c)))) := by
  conv => { lhs; arg 2; unfold lfLiftBat }
  simp only [nock_exec]

/-- The sample bunt of `+lift` (a mold core), read from the pill: axis `13`
of the arm `372`. -/
noncomputable def lfLiftBunt : Noun := (slot? 2981 layer2).getD (A 0)

/-- **The arm `+lift`** of `layer2`, a kernel fact. -/
theorem lf_lift_at : slot? 372 layer2
    = some (C (A 8) (C (C (A 1) lfLiftBunt) (C (C (A 1) lfLiftBat) (C (A 0) (A 1))))) := by
  kernel_rfl

/-- **`+bind`** on a unit of an atom and a gate that renames atoms. -/
theorem lf_bind (c GB GS GC : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C GB (C (A r) GC)) GB = some (A (ren r))) (o : Option Nat) :
    nock (C lfBindBat (C (C (unitNoun A o) (C GB (C GS GC))) c)) lfBindBat
      = some (unitNoun A (o.map ren)) := by
  cases o <;> simp [nock_exec, lfBindBat, unitNoun, hren]

/-- **The inner gate of `(lift ren)`** on a unit of an atom. -/
theorem lf_inner (GB GS GC : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C GB (C (A r) GC)) GB = some (A (ren r))) (o : Option Nat) :
    nock (C lfLiftIn (C (unitNoun A o) (C lfLiftBat (C (C GB (C GS GC)) layer2)))) lfLiftIn
      = some (unitNoun A (o.map ren)) := by
  have hb := lf_bind layer2 GB GS GC ren hren o
  simp [nock_exec, lfLiftIn, lf_bind_at, hb]

/-- The renaming of the atom of a unit, on nouns. -/
def lfUnitRen (ren : Nat → Nat) : Noun → Noun
  | Noun.cell h (Noun.atom r) => C h (A (ren r))
  | x => x

theorem lf_unitRen (ren : Nat → Nat) (o : Option Nat) :
    lfUnitRen ren (unitNoun A o) = unitNoun A (o.map ren) := by
  cases o <;> rfl

/-- **`(turn v (lift ren))`** over a list of units of registers. -/
theorem lf_turn (GB GS GC : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C GB (C (A r) GC)) GB = some (A (ren r))) (v : List (Option Nat)) :
    nock (C turn.battery (C (C (listNoun (unitNoun A) v)
        (C lfLiftIn (C (A 0) (C lfLiftBat (C (C GB (C GS GC)) layer2))))) layer2)) turn.battery
      = some (listNoun (unitNoun A) (v.map (Option.map ren))) := by
  rw [listNoun_map_listN, listNoun_map_listN]
  rw [turn_gate layer2 homoIn_layer2 lfLiftIn (A 0) (C lfLiftBat (C (C GB (C GS GC)) layer2))
    (lfUnitRen ren) (v.map (unitNoun A)) (by
      intro x hx
      obtain ⟨o, _, rfl⟩ := List.mem_map.1 hx
      rw [lf_inner GB GS GC ren hren o, lf_unitRen])]
  simp [List.map_map, Function.comp_def, lf_unitRen]

/-- **The gate `rj` of `+chase-fin`** on a core with `layer2` at
`0x1ffffffff` and a renaming gate at `30`: `renJmp ren`. -/
theorem lf_rj (ren : Nat → Nat) (CORE : Noun)
    (hL : slot? 0x1ffffffff CORE = some layer2)
    (hR : ∃ RB RS RC, slot? 30 CORE = some (C RB (C RS RC)) ∧
      ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r))) : CfRjAt ren CORE := by
  obtain ⟨RB, RS, RC, h30, hren⟩ := hR
  intro X finN j
  obtain ⟨args, there⟩ := j
  have ht := lf_turn RB RS RC ren hren args
  simp [nock_exec, cfRjBody, Jmp.toNoun, renJmp, hL, h30, turn.arm_at, turn_arm, lf_lift_at, lf_lift_slam, ht]

/-- **The gate `ren-jmp` of `+map-regs`** (`mrRjBody`) on its subject
`[mrRjBody [j [I [b [MB [ren T]]]]]]`, with `layer2` at `32767` of the
types core `T`: `renJmp ren`. -/
theorem lf_mr_rj (I B MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) (j : Jmp) :
    nock (C mrRjBody (C (Jmp.toNoun j) (C I (C B (C MB (C (C RB (C RS RC)) T)))))) mrRjBody
      = some (Jmp.toNoun (renJmp ren j)) := by
  obtain ⟨args, there⟩ := j
  have ht := lf_turn RB RS RC ren hren args
  simp [nock_exec, mrRjBody, Jmp.toNoun, renJmp, hT, turn.arm_at, turn_arm, lf_lift_at, lf_lift_slam, ht]

/-- **`TsRjAt`**: the gate `rj` in every core of the renaming branch. -/
theorem lf_ts_rj {ctx : Noun} (hc : CompIn ctx) : TsRjAt ctx := by
  intro SB Bo BN D G o sub bs
  apply lf_rj
  · simp [tsSt, tsCoreSt, tsS7, tsS5, tsS0, nock_exec, hc]
  · exact ⟨tsRenBat, A 0, tsS7 BN BN (tsS0 D G ctx o sub) sub,
      by simp [tsSt, tsCoreSt, tsRenG, nock_exec], fun r => ts_ren hc BN BN D G o sub r⟩

/-- **The end of `+compile-unary` from its entry state**, with no hypothesis
on `+to-straight`: `+run`, `+kerf` and `+to-straight` give `finishLU n`. -/
theorem cu_finish_all {ctx : Noun} (h7 : slot? 7 ctx = some compK) {cod : Noun}
    (hcode : slot? 52 ctx = some cod)
    (n : Nomm) (hpu : n.pure = true) (h6 : noSix n = true) (ht : tenOk n = true)
    (cache mono sup : Noun) :
    ((nock (crSubj mono n.toNoun (CGoal.toL (CGoal.done : CGoal CSet)).toNoun (listNoun A []) sup
        (compCore genEntry (cuRest cache) ctx)) crDol).bind (fun R =>
      (slot? 2 R).bind fun N => (slot? 3 R).bind fun G =>
        nock (C kerfBat (C N (C comp.door (C G ctx)))) kerfBat)).bind (fun K =>
      (slot? 4 K).bind fun O => (slot? 5 K).bind fun SUB => (slot? 3 K).bind fun G2 =>
        nock (C tsBat (C (tsSample O SUB) (C comp.door (C G2 ctx)))) tsBat)
      = (finishLU (S := CSet) (Map := TreapMap mugF) n).map Straight.toNoun :=
  cu_finish_rj h7 hcode n hpu h6 ht cache mono sup (lf_ts_rj (comp_ctx_pill ctx h7).1)

end Compiler
end Formalization
