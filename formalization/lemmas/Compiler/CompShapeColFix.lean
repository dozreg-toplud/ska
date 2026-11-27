import lemmas.Compiler.CompShapeColI12

/-!
# `+inter2-fix-round` with forks

`fr_trap`: the trap `round` of `+inter2-fix-round` (arm `0xaebdf` of `K`,
`frTrap` of `CompShapeCol.lean`) on `prev` with the parent's shape `parent`
in its subject is `fixRound less prev parent` (`Ska/ShapeCol.lean`), forks
to any depth; `fr_gate`: the gate body is `fixRound less prev [%none ~]`.
The pieces: `=.  parent  (uni-need-ord parent sure.prev)` (`uno_gate`), the
`+turn` over `fork.prev` whose gate runs the trap again on both branches
with the updated `parent` in its subject (`fr_kids`, mutual with
`fr_trap`), and the `+roll` over the new kids from that `parent`, whose gate
is `uniOrd acc (msgOrd sure.y sure.n less)` (`fr_step`, `fr_roll`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The gate of the `+turn` over `fork.prev`: the trap again on both branches. -/
def frTG : Noun :=
  C (C (A 9) (C (A 2) (C (A 10) (C (C (A 60) (C (A 0) (A 12))) (C (A 0) (A 7))))))
    (C (A 9) (C (A 2) (C (A 10) (C (C (A 60) (C (A 0) (A 13))) (C (A 0) (A 7))))))

/-- Its sample bunt. -/
def frTB : Noun := C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (C (A 0x656e6f6e) (A 0)) (A 0))

/-- `frTurn` with its gate named. -/
def frTurnN : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0)
    (A 249)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) frTB) (C (C (A 1) frTG) (C (A 0) (A 1))))))))) (C (A 0)
    (A 2))))))))

theorem frTurn_eq : frTurn = frTurnN := rfl

/-- The subject of the trap `round`: `[round [parent gate]]`, the gate's
sample `[prev less]`. -/
def frT (parent : NeedOrd) (PREV LESS KC : Noun) : Noun :=
  C frTrap (C parent.toNoun (C frBody (C (C PREV LESS) KC)))

/-- **The gate of the `+roll`** on a fork and the accumulator. -/
theorem fr_step (less : Cape) (y n : I2) (P P' : NeedOrd) (KIDS PREV : Noun) :
    nock (C frGate (C (C (I2.forkN (y, n)) P.toNoun) (C KIDS (frT P' PREV less.toNoun compK)))) frGate
      = some (uniOrd P (msgOrd y.sure n.sure less)).toNoun := by
  have hu := uno_gate compK compK_cn P (msgOrd y.sure n.sure less)
  have hm := msg_gate_K y.sure n.sure less
  have hua := uno_at
  have hma := msg_at
  unfold msgS at hm
  cases y with
  | mk ys yf =>
  cases n with
  | mk ns nf =>
  simp only [I2.forkN, I2.toNoun_mk, I2.sure] at hu hm ⊢
  unfold frT frGate
  generalize compK = KC at hu hm hua hma ⊢
  simp [nock_exec, hua, uno_arm, hu, hma, msg_arm, hm]

/-- **The `+roll` over the new kids** from `P`: `rollMsg`. -/
theorem fr_roll (less : Cape) (P' : NeedOrd) (KIDS PREV : Noun) : ∀ (kids : List (I2 × I2)) (P : NeedOrd),
    (kids.map I2.forkN).foldlM
      (fun acc x => nock (C frGate (C (C x acc) (C KIDS (frT P' PREV less.toNoun compK)))) frGate) P.toNoun
      = some (rollMsg less kids P).toNoun
  | [], P => rfl
  | (y, n) :: r, P => by
    have h := fr_step less y n P P' KIDS PREV
    have ih := fr_roll less P' KIDS PREV r (uniOrd P (msgOrd y.sure n.sure less))
    simp [List.foldlM_cons, h, ih, rollMsg, List.foldl_cons]

mutual
/-- **The trap `round` of `+inter2-fix-round`** is `fixRound`. -/
theorem fr_trap (less : Cape) : ∀ (prev : I2) (parent : NeedOrd),
    nock (frT parent prev.toNoun less.toNoun compK) frTrap = some (fixRound less prev parent).toNoun
  | I2.mk s fk, parent => by
    have hu := uno_gate compK compK_cn parent s
    have hua := uno_at
    have hL := compK_layer2
    have hk := fr_kids less (uniOrd parent s) (I2.mk s fk).toNoun fk
    have ht := turn_gate_mapM layer2 homoIn_layer2 frTG frTB
      (frT (uniOrd parent s) (I2.mk s fk).toNoun less.toNoun compK)
      (fun x => nock (C frTG (C x (frT (uniOrd parent s) (I2.mk s fk).toNoun less.toNoun compK))) frTG)
      (fk.map I2.forkN) (fun _ _ => rfl)
    rw [hk] at ht
    have hr := roll_gate_M layer2 frGate (C i2nBunt i2nBunt) (uniOrd parent s).toNoun
      (C (listN ((fixKids less fk (uniOrd parent s)).map I2.forkN))
        (frT (uniOrd parent s) (I2.mk s fk).toNoun less.toNoun compK))
      (fun x acc => nock (C frGate (C (C x acc) (C (listN ((fixKids less fk (uniOrd parent s)).map I2.forkN))
        (frT (uniOrd parent s) (I2.mk s fk).toNoun less.toNoun compK)))) frGate)
      ((fixKids less fk (uniOrd parent s)).map I2.forkN) (fun _ _ _ => rfl)
    rw [fr_roll] at hr
    have hb := fr_bunt2_at (C (listN ((fixKids less fk (uniOrd parent s)).map I2.forkN))
      (frT (uniOrd parent s) (I2.mk s fk).toNoun less.toNoun compK)) (by unfold frT; rfl)
    rw [fixRound, I2.toNoun_mk, I2.forksNoun_eq]
    unfold frT at ht hr hb ⊢
    conv => { lhs; arg 2; unfold frTrap }
    rw [frTurn_eq]
    simp only [I2.toNoun_mk, I2.forksNoun_eq] at ht hr hb ⊢
    generalize frBody = FB at ht hr hb ⊢
    generalize frTrap = FT at ht hr hb ⊢
    generalize compK = KC at hu hua hL ht hr hb ⊢
    simp [nock_exec, frUni, hua, uno_arm, hu, frTurnN, hL, turn.arm_at, turn_arm, ht, frRoll, frRBunt, hb,
      roll.arm_at, roll_arm, hr]

/-- The gate of the `+turn` over the forks, on every fork list. -/
theorem fr_kids (less : Cape) (P : NeedOrd) (PREV : Noun) : ∀ fk : List (I2 × I2),
    (fk.map I2.forkN).mapM (fun x => nock (C frTG (C x (frT P PREV less.toNoun compK))) frTG)
      = some ((fixKids less fk P).map I2.forkN)
  | [] => rfl
  | (y, n) :: r => by
    have hy := fr_trap less y P
    have hn := fr_trap less n P
    have hr := fr_kids less P PREV r
    have hg : nock (C frTG (C (I2.forkN (y, n)) (frT P PREV less.toNoun compK))) frTG
        = some (I2.forkN (fixRound less y P, fixRound less n P)) := by
      unfold frT at hy hn ⊢
      unfold frTG I2.forkN
      generalize frTrap = FT at hy hn ⊢
      generalize frBody = FB at hy hn ⊢
      generalize compK = KC at hy hn ⊢
      simp [nock_exec, hy, hn]
    simp only [List.map_cons, List.mapM_cons, hg, hr, fixKids]
    rfl
end

/-- **`+inter2-fix-round`** on every `need-inter2`: `fixRound less prev [%none ~]`. -/
theorem fr_gate (less : Cape) (prev : I2) :
    nock (C frBody (C (C prev.toNoun less.toNoun) compK)) frBody = some (fixRound less prev NeedOrd.none).toNoun := by
  have h := fr_trap less prev NeedOrd.none
  unfold frT at h
  simp only [NeedOrd.toNoun, Tag.none] at h
  conv => { lhs; arg 2; unfold frBody }
  generalize frTrap = FT at h ⊢
  generalize frBody = FB at h ⊢
  simp [nock_exec, h, NeedOrd.toNoun]

end Compiler
end Formalization
