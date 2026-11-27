import lemmas.Compiler.CompRunAllL
import lemmas.Compiler.CompRunSixAll

/-!
# The run link and its result for the plain class with `%6`

`SixOk`: the plain class (`PlainOk`: `%0`, `%1`, `%3`, `%4`, `%5`, `%7`,
cons, `%10` with an axis not `0`, the indirect call `[2 p q ~]`) with `%6`,
nested in any way.  The side condition `Bake.NoAx0` (no `%10` at axis `0`,
anywhere): `+leap` needs it of the branches of each `%6`
(`lp6_leap`, `leapTwice_noAx0`), and every nomm `+fol-loop` makes has it
(`folLoop_noAx0` of `Ska/DatFacts.lean`).

* **`res_all6`**: every run of `runLC env msup` of a nomm of the class with
  `NoAx0`, from a goal and a state with `GInv`, returns a result with
  `GRes` (`%6` by `res_n6_all`, the rest as `res_all`).
* **`comp_run_all_l6`**: on every goal and state with `GInv`, every region,
  `env`, `msup`, the `$` arm of `+run` is `runLC env msup` (for every
  `mono`, Hoon `sup` and rest of the state with an empty `soft`), given
  only `slot? 7 ctx = some compK` and `slot? 52 ctx = some cod`.  `%6` by
  `comp_run_n6_all`, whose `SixParts` the induction gives: the link and the
  result of each operand on every goal with `GInv`, in the case's region
  and in every region `rid :: region`, and `+hinted` from `NoDirect`
  (`hinted_nd`).  The cases cons, `%2`, `%5`, `%10` take `PartL` of their
  parts, which now asks `NoDirect` of a part (`PartL.nd`), not `PlainOk`.
* Examples: `[[6 [0 2] [4 0 3] [1 0]] [0 1]]` and `[7 [0 1] [6 [0 2] [4 0
  3] [1 0]]]` on every goal with `GInv`, and `%6` at the entry of `+comp`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-- **The plain class with `%6`**. -/
def SixOk : Nomm → Bool
  | Nomm.cons p q => SixOk p && SixOk q
  | Nomm.n0 _ => true
  | Nomm.n1 _ => true
  | Nomm.n2 p q Option.none => SixOk p && SixOk q
  | Nomm.n3 p => SixOk p
  | Nomm.n4 p => SixOk p
  | Nomm.n5 p q => SixOk p && SixOk q
  | Nomm.n6 p q r => SixOk p && SixOk q && SixOk r
  | Nomm.n7 p q => SixOk p && SixOk q
  | Nomm.n10 a v q => a != 0 && SixOk v && SixOk q
  | _ => false

theorem sixOk_noDirect : ∀ (n : Nomm), SixOk n = true → NoDirect n
  | Nomm.cons p q, h => by
    simp only [SixOk, Bool.and_eq_true] at h; exact ⟨sixOk_noDirect p h.1, sixOk_noDirect q h.2⟩
  | Nomm.n0 _, _ => trivial
  | Nomm.n1 _, _ => trivial
  | Nomm.n2 p q Option.none, h => by
    simp only [SixOk, Bool.and_eq_true] at h; exact ⟨sixOk_noDirect p h.1, sixOk_noDirect q h.2⟩
  | Nomm.n3 p, h => by simp only [SixOk] at h; exact sixOk_noDirect p h
  | Nomm.n4 p, h => by simp only [SixOk] at h; exact sixOk_noDirect p h
  | Nomm.n5 p q, h => by
    simp only [SixOk, Bool.and_eq_true] at h; exact ⟨sixOk_noDirect p h.1, sixOk_noDirect q h.2⟩
  | Nomm.n6 p q r, h => by
    simp only [SixOk, Bool.and_eq_true] at h
    exact ⟨sixOk_noDirect p h.1.1, sixOk_noDirect q h.1.2, sixOk_noDirect r h.2⟩
  | Nomm.n7 p q, h => by
    simp only [SixOk, Bool.and_eq_true] at h; exact ⟨sixOk_noDirect p h.1, sixOk_noDirect q h.2⟩
  | Nomm.n10 a v q, h => by
    simp only [SixOk, Bool.and_eq_true] at h; exact ⟨sixOk_noDirect v h.1.2, sixOk_noDirect q h.2⟩
  | Nomm.n2 _ _ (some _), h => by simp [SixOk] at h
  | Nomm.n11s _ _ _, h => by simp [SixOk] at h
  | Nomm.n11d _ _ _ _, h => by simp [SixOk] at h
  | Nomm.n12 _ _, h => by simp [SixOk] at h
  | Nomm.mean _ _ _ _ _, h => by simp [SixOk] at h

/-- The plain class is in the class with `%6`. -/
theorem sixOk_of_plainOk : ∀ (n : Nomm), PlainOk n = true → SixOk n = true
  | Nomm.cons p q, h => by
    simp only [PlainOk, SixOk, Bool.and_eq_true] at h ⊢; exact ⟨sixOk_of_plainOk p h.1, sixOk_of_plainOk q h.2⟩
  | Nomm.n0 _, _ => rfl
  | Nomm.n1 _, _ => rfl
  | Nomm.n2 p q Option.none, h => by
    simp only [PlainOk, SixOk, Bool.and_eq_true] at h ⊢; exact ⟨sixOk_of_plainOk p h.1, sixOk_of_plainOk q h.2⟩
  | Nomm.n3 p, h => by simp only [PlainOk, SixOk] at h ⊢; exact sixOk_of_plainOk p h
  | Nomm.n4 p, h => by simp only [PlainOk, SixOk] at h ⊢; exact sixOk_of_plainOk p h
  | Nomm.n5 p q, h => by
    simp only [PlainOk, SixOk, Bool.and_eq_true] at h ⊢; exact ⟨sixOk_of_plainOk p h.1, sixOk_of_plainOk q h.2⟩
  | Nomm.n7 p q, h => by
    simp only [PlainOk, SixOk, Bool.and_eq_true] at h ⊢; exact ⟨sixOk_of_plainOk p h.1, sixOk_of_plainOk q h.2⟩
  | Nomm.n10 a v q, h => by
    simp only [PlainOk, SixOk, Bool.and_eq_true] at h ⊢
    exact ⟨⟨h.1.1, sixOk_of_plainOk v h.1.2⟩, sixOk_of_plainOk q h.2⟩
  | Nomm.n2 _ _ (some _), h => by simp [PlainOk] at h
  | Nomm.n6 _ _ _, h => by simp [PlainOk] at h
  | Nomm.n11s _ _ _, h => by simp [PlainOk] at h
  | Nomm.n11d _ _ _ _, h => by simp [PlainOk] at h
  | Nomm.n12 _ _, h => by simp [PlainOk] at h
  | Nomm.mean _ _ _ _ _, h => by simp [PlainOk] at h

/-- **What the runs of the class with `%6` return**, for nomms with
`Bake.NoAx0`. -/
theorem res_all6 (env : CallEnv) : ∀ (n : Nomm), SixOk n = true → Bake.NoAx0 n →
    ∀ (msup : Option Nomm) (region : List Nat), ResFor env msup n region
  | Nomm.cons p q, h, ha, msup, region => by
    simp only [SixOk, Bool.and_eq_true] at h
    simp only [Bake.NoAx0] at ha
    exact res_cons (res_all6 env p h.1 ha.1 msup region) (res_all6 env q h.2 ha.2 msup region)
  | Nomm.n0 ax, _, _, msup, region => res_n0 env msup ax region
  | Nomm.n1 k, _, _, msup, region => res_n1 env msup k region
  | Nomm.n2 p q Option.none, h, ha, msup, region => by
    simp only [SixOk, Bool.and_eq_true] at h
    simp only [Bake.NoAx0] at ha
    exact res_n2 (res_all6 env p h.1 ha.1 msup region) (res_all6 env q h.2 ha.2 msup region)
  | Nomm.n3 p, h, ha, msup, region => by
    simp only [SixOk] at h
    simp only [Bake.NoAx0] at ha
    exact res_n3 (res_all6 env p h ha msup region)
  | Nomm.n4 p, h, ha, msup, region => by
    simp only [SixOk] at h
    simp only [Bake.NoAx0] at ha
    exact res_n4 (res_all6 env p h ha msup region)
  | Nomm.n5 p q, h, ha, msup, region => by
    simp only [SixOk, Bool.and_eq_true] at h
    simp only [Bake.NoAx0] at ha
    exact res_n5 (res_all6 env p h.1 ha.1 msup region) (res_all6 env q h.2 ha.2 msup region)
  | Nomm.n6 p q r, h, ha, msup, region => by
    simp only [SixOk, Bool.and_eq_true] at h
    simp only [Bake.NoAx0] at ha
    exact res_n6_all (res_all6 env p h.1.1 ha.1 msup region) (res_all6 env q h.1.2 ha.2.1 msup region)
      (res_all6 env r h.2 ha.2.2 msup region) (fun rid => res_all6 env q h.1.2 ha.2.1 msup (rid :: region))
      (fun rid => res_all6 env r h.2 ha.2.2 msup (rid :: region)) ha.2.1 ha.2.2
  | Nomm.n7 p q, h, ha, msup, region => by
    simp only [SixOk, Bool.and_eq_true] at h
    simp only [Bake.NoAx0] at ha
    exact res_n7 (res_all6 env q h.2 ha.2 (some p) region) (res_all6 env p h.1 ha.1 msup region)
  | Nomm.n10 a v q, h, ha, msup, region => by
    simp only [SixOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp only [Bake.NoAx0] at ha
    exact res_n10 h.1.1 (res_all6 env v h.1.2 ha.2.1 msup region) (res_all6 env q h.2 ha.2.2 msup region)
  | Nomm.n2 _ _ (some _), h, _, _, _ => by simp [SixOk] at h
  | Nomm.n11s _ _ _, h, _, _, _ => by simp [SixOk] at h
  | Nomm.n11d _ _ _ _, h, _, _, _ => by simp [SixOk] at h
  | Nomm.n12 _ _, h, _, _, _ => by simp [SixOk] at h
  | Nomm.mean _ _ _ _ _, h, _, _, _ => by simp [SixOk] at h

/-- `SixParts` from the link, the result and `NoDirect`. -/
theorem sixParts_of {env : CallEnv} {msup : Option Nomm} {n : Nomm} {region : List Nat}
    (hl : ∀ (goal : CGoalL CSet) (g : Gen (TreapMap mugF)), GInv g goal →
      CompRunAtR (runLC env msup) ctx n goal region g)
    (hr : ResFor env msup n region) (hn : NoDirect n) : SixParts env msup ctx n region :=
  ⟨hl, hr, (hinted_nd env.cod hn).1, (hinted_nd env.cod hn).2⟩

/-- **The run link on every goal with the invariant, for the plain class
with `%6`**, for nomms with `Bake.NoAx0`. -/
theorem comp_run_all_l6 (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) : ∀ (n : Nomm), SixOk n = true → Bake.NoAx0 n → ∀ (msup : Option Nomm) (region : List Nat)
      (goal : CGoalL CSet) (g : Gen (TreapMap mugF)), GInv g goal →
      CompRunAtR (runLC env msup) ctx n goal region g
  | Nomm.cons p q, h, ha, msup, region, goal, g, hi => by
    have h' := h
    simp only [SixOk, Bool.and_eq_true] at h'
    simp only [Bake.NoAx0] at ha
    exact comp_run_consL h7 hcode env msup p q
      ⟨comp_run_all_l6 h7 hcode env p h'.1 ha.1 msup region, res_all6 env p h'.1 ha.1 msup region,
        sixOk_noDirect _ h'.1⟩
      ⟨comp_run_all_l6 h7 hcode env q h'.2 ha.2 msup region, res_all6 env q h'.2 ha.2 msup region,
        sixOk_noDirect _ h'.2⟩ goal g hi
  | Nomm.n0 ax, _, _, msup, region, goal, g, hi => crc_of_pure env rfl (comp_run_n0L h7 ax goal region g hi) msup
  | Nomm.n1 k, _, _, msup, region, goal, g, hi => crc_of_pure env rfl (comp_run_n1L h7 k goal region g hi) msup
  | Nomm.n2 p q Option.none, h, ha, msup, region, goal, g, hi => by
    have h' := h
    simp only [SixOk, Bool.and_eq_true] at h'
    simp only [Bake.NoAx0] at ha
    exact comp_run_n2L h7 hcode env msup p q
      ⟨comp_run_all_l6 h7 hcode env p h'.1 ha.1 msup region, res_all6 env p h'.1 ha.1 msup region,
        sixOk_noDirect _ h'.1⟩
      ⟨comp_run_all_l6 h7 hcode env q h'.2 ha.2 msup region, res_all6 env q h'.2 ha.2 msup region,
        sixOk_noDirect _ h'.2⟩ goal g hi
  | Nomm.n3 p, h, ha, msup, region, goal, g, hi => by
    simp only [SixOk] at h
    simp only [Bake.NoAx0] at ha
    exact comp_run_n3L h7 env msup p goal region g hi (comp_run_all_l6 h7 hcode env p h ha msup region)
  | Nomm.n4 p, h, ha, msup, region, goal, g, hi => by
    simp only [SixOk] at h
    simp only [Bake.NoAx0] at ha
    exact comp_run_n4L h7 env msup p goal region g hi (comp_run_all_l6 h7 hcode env p h ha msup region)
  | Nomm.n5 p q, h, ha, msup, region, goal, g, hi => by
    have h' := h
    simp only [SixOk, Bool.and_eq_true] at h'
    simp only [Bake.NoAx0] at ha
    exact comp_run_n5L h7 hcode env msup p q
      ⟨comp_run_all_l6 h7 hcode env p h'.1 ha.1 msup region, res_all6 env p h'.1 ha.1 msup region,
        sixOk_noDirect _ h'.1⟩
      ⟨comp_run_all_l6 h7 hcode env q h'.2 ha.2 msup region, res_all6 env q h'.2 ha.2 msup region,
        sixOk_noDirect _ h'.2⟩ goal g hi
  | Nomm.n6 p q r, h, ha, msup, region, goal, g, hi => by
    have h' := h
    simp only [SixOk, Bool.and_eq_true] at h'
    simp only [Bake.NoAx0] at ha
    exact comp_run_n6_all h7 hcode env msup p q r region
      (sixParts_of (comp_run_all_l6 h7 hcode env p h'.1.1 ha.1 msup region)
        (res_all6 env p h'.1.1 ha.1 msup region) (sixOk_noDirect _ h'.1.1))
      (sixParts_of (comp_run_all_l6 h7 hcode env q h'.1.2 ha.2.1 msup region)
        (res_all6 env q h'.1.2 ha.2.1 msup region) (sixOk_noDirect _ h'.1.2))
      (sixParts_of (comp_run_all_l6 h7 hcode env r h'.2 ha.2.2 msup region)
        (res_all6 env r h'.2 ha.2.2 msup region) (sixOk_noDirect _ h'.2))
      (fun rid => sixParts_of (comp_run_all_l6 h7 hcode env q h'.1.2 ha.2.1 msup (rid :: region))
        (res_all6 env q h'.1.2 ha.2.1 msup (rid :: region)) (sixOk_noDirect _ h'.1.2))
      (fun rid => sixParts_of (comp_run_all_l6 h7 hcode env r h'.2 ha.2.2 msup (rid :: region))
        (res_all6 env r h'.2 ha.2.2 msup (rid :: region)) (sixOk_noDirect _ h'.2))
      ha.2.1 ha.2.2 goal g hi
  | Nomm.n7 p q, h, ha, msup, region, goal, g, hi => by
    simp only [SixOk, Bool.and_eq_true] at h
    simp only [Bake.NoAx0] at ha
    exact comp_run_n7C env msup p q goal region g
      (comp_run_all_l6 h7 hcode env q h.2 ha.2 (some p) region goal g hi)
      (fun nex g1 e => comp_run_all_l6 h7 hcode env p h.1 ha.1 msup region nex.goal g1
        (res_all6 env q h.2 ha.2 (some p) region goal g g1 nex hi e).2.2.1)
  | Nomm.n10 a v q, h, ha, msup, region, goal, g, hi => by
    have h' := h
    simp only [SixOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h'
    simp only [Bake.NoAx0] at ha
    exact comp_run_n10L h7 hcode env msup a h'.1.1 v q
      ⟨comp_run_all_l6 h7 hcode env v h'.1.2 ha.2.1 msup region, res_all6 env v h'.1.2 ha.2.1 msup region,
        sixOk_noDirect _ h'.1.2⟩
      ⟨comp_run_all_l6 h7 hcode env q h'.2 ha.2.2 msup region, res_all6 env q h'.2 ha.2.2 msup region,
        sixOk_noDirect _ h'.2⟩ goal g hi
  | Nomm.n2 _ _ (some _), h, _, _, _, _, _, _ => by simp [SixOk] at h
  | Nomm.n11s _ _ _, h, _, _, _, _, _, _ => by simp [SixOk] at h
  | Nomm.n11d _ _ _ _, h, _, _, _, _, _, _ => by simp [SixOk] at h
  | Nomm.n12 _ _, h, _, _, _, _, _, _ => by simp [SixOk] at h
  | Nomm.mean _ _ _ _ _, h, _, _, _, _, _, _ => by simp [SixOk] at h

/-! ## Instances -/

/-- The nomm `[6 [0 2] [4 0 3] [1 0]]`: if the head of the subject is
`0`, the increment of its tail, else `0`. -/
def sixEx : Nomm := Nomm.n6 (Nomm.n0 2) (Nomm.n4 (Nomm.n0 3)) (Nomm.n1 (A 0))

/-- **`%6` under a cons**: `[[6 [0 2] [4 0 3] [1 0]] [0 1]]` on every goal
and state with the invariant, every region, `env`, `msup`, with no
hypothesis but the context. -/
example (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod) (env : CallEnv)
    (goal : CGoalL CSet) (region : List Nat) (g : Gen (TreapMap mugF)) (hi : GInv g goal) :
    CompRunAtC env ctx (Nomm.cons sixEx (Nomm.n0 1)) goal region g :=
  fun msup => comp_run_all_l6 h7 hcode env _ rfl (by simp [sixEx, Bake.NoAx0]) msup region goal g hi

/-- **`%6` under a `%7`**: `[7 [0 1] [6 [0 2] [4 0 3] [1 0]]]`, the same. -/
example (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod) (env : CallEnv)
    (goal : CGoalL CSet) (region : List Nat) (g : Gen (TreapMap mugF)) (hi : GInv g goal) :
    CompRunAtC env ctx (Nomm.n7 (Nomm.n0 1) sixEx) goal region g :=
  fun msup => comp_run_all_l6 h7 hcode env _ rfl (by simp [sixEx, Bake.NoAx0]) msup region goal g hi

/-- **`%6` at the entry of `+comp`**: from the bunt state with `[%done ~]`
and the region `~`; and what it returns meets `GRes`. -/
example (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod) (env : CallEnv) :
    CompRunAtC env ctx sixEx CGoalL.done [] genEntry ∧ ∀ msup, ResFor env msup sixEx [] :=
  ⟨fun msup => comp_run_all_l6 h7 hcode env _ rfl (by simp [sixEx, Bake.NoAx0]) msup [] CGoalL.done genEntry rfl,
   fun msup => res_all6 env _ rfl (by simp [sixEx, Bake.NoAx0]) msup []⟩

end Compiler
end Formalization
