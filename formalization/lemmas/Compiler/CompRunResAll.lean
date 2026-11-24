import lemmas.Compiler.CompRunRes

/-!
# What the runs of the plain class return (`RunResL`)

`res_all`: every run of `runLC env msup` of a nomm of the plain class
(`PlainOk`: `%0`, `%1`, `%3`, `%4`, `%5`, `%7`, cons, `%10` with an axis not
`0`, the indirect call, nested in any way) from a goal and a state with
`GInv` returns a result with `GRes`, by induction on the nomm: the leaves
and the fresh registers' goals directly, `%7` by composing (`gres_comp`),
and cons, `%5`, `%10`, `%2` through the tail (`tail_all`, from
`CompRunRes.lean`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- What a run of `n` returns, on every goal with the invariant. -/
def ResFor (env : CallEnv) (msup : Option Nomm) (n : Nomm) (region : List Nat) : Prop :=
  ∀ (goal : CGoalL CSet) (g g' : Gen (TreapMap mugF)) (nex : NextL CSet), GInv g goal →
    runLC env msup n goal region g = some (nex, g') → GRes g goal g' nex

/-- A result that asks nothing. -/
theorem gres_bunt {g g' : Gen (TreapMap mugF)} {goal : CGoalL CSet} {j : Jmp} (hr : g.re ≤ g'.re)
    (hb : g.bo ≤ g'.bo) (hd : g'.drop = false) (hj : JmpIn (· < g'.re) j) :
    GRes g goal g' ⟨Lazy.ofSure Sure.bunt, j⟩ :=
  ⟨hr, hb, ginv_bunt_j hd hj, fun x hx => by simp [lregs_bunt] at hx⟩

/-- `+simple-next` of a goal with the invariant. -/
theorem simpleNextL_res {g g1 : Gen (TreapMap mugF)} {goal : CGoalL CSet} {nex : NextL CSet} (hi : GInv g goal)
    (e : simpleNextL goal g = some (nex, g1)) : GRes g goal g1 nex := by
  obtain ⟨l, b, d⟩ := (km_simpleNextL _).keep g _ g1 e
  cases goal with
  | next laz th =>
    simp only [simpleNextL, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨Nat.le_refl _, Nat.le_refl _, hi, fun x hx => Or.inr hx⟩
  | done =>
    simp only [simpleNextL] at e
    obtain ⟨r, g5, h5, e⟩ := bind_some e
    rw [re_apply] at h5
    simp only [Option.some.injEq, Prod.mk.injEq] at h5
    obtain ⟨rfl, rfl⟩ := h5
    obtain ⟨o, g6, h6, e⟩ := bind_some e
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    obtain ⟨l6, b6, d6⟩ := (KM.emit' _).keep _ _ g6 h6
    refine ⟨l, b, ⟨linv_reg (show g.re < g6.re by simp at l6; omega), d.trans hi, jmpIn_jmp0 _ _⟩, fun x hx => ?_⟩
    simp [lregs_ofSure, flattenNeed] at hx
    exact Or.inl (by omega)
  | pick z o =>
    simp only [simpleNextL] at e
    obtain ⟨r, g5, h5, e⟩ := bind_some e
    rw [re_apply] at h5
    simp only [Option.some.injEq, Prod.mk.injEq] at h5
    obtain ⟨rfl, rfl⟩ := h5
    obtain ⟨o', g6, h6, e⟩ := bind_some e
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    obtain ⟨l6, b6, d6⟩ := (KM.emit' _).keep _ _ g6 h6
    refine ⟨l, b, ⟨linv_reg (show g.re < g6.re by simp at l6; omega), d.trans hi.1, jmpIn_jmp0 _ _⟩, fun x hx => ?_⟩
    simp [lregs_ofSure, flattenNeed] at hx
    exact Or.inl (by omega)

/-- The mode of a goal with the invariant. -/
theorem ginv_drop {g : Gen (TreapMap mugF)} {goal : CGoalL CSet} (h : GInv g goal) : g.drop = false := by
  cases goal with
  | next laz th => exact h.2.1
  | pick z o => exact h.1
  | done => exact h

/-- **The tail through the runs' results.** -/
theorem tail_all {env : CallEnv} {msup : Option Nomm} {p q : Nomm} {region : List Nat}
    (ihq : ResFor env msup q region) (ihp : ResFor env msup p region)
    {Gq Gp : Lazy CSet} {thq : Jmp} {g g2 g3 g4 g' : Gen (TreapMap mugF)} {n2 n2' n1 nex : NextL CSet}
    (hq : GInv g (CGoalL.next Gq thq)) (hp : LInv g.re g.bo Gp) (ap : (lregs Gp ++ lregs Gq).Nodup)
    (e1 : runLC env msup q (CGoalL.next Gq thq) region g = some (n2, g2))
    (e2 : pastL env.cod n2 p region g2 = some (n2', g3))
    (e3 : runLC env msup p (CGoalL.next Gp n2'.th) region g3 = some (n1, g4))
    (e4 : copyL n1 n2'.laz g4 = some (nex, g')) :
    g.re ≤ g'.re ∧ g.bo ≤ g'.bo ∧ GInv g' nex.goal ∧ ∀ x ∈ lregs nex.laz, x ∈ lregs Gp ++ lregs Gq ∨ g.re ≤ x := by
  have R2 := ihq _ _ _ _ hq e1
  have P := tail_pgoal hq hp R2 e2
  have R1 := ihp _ _ _ _ P.1 e3
  exact tail_res hq hp ap R2 e2 R1 e4

/-- The tail with two fresh registers `rp < rq` below the state's counter,
both at or above `k`. -/
theorem tail_fresh {env : CallEnv} {msup : Option Nomm} {p q : Nomm} {region : List Nat}
    (ihq : ResFor env msup q region) (ihp : ResFor env msup p region)
    {rp rq k : Nat} {thq : Jmp} {g1 g2 g3 g4 g' : Gen (TreapMap mugF)} {n2 n2' n1 nex : NextL CSet}
    (hk : k ≤ rp) (hpq : rp < rq) (hrq : rq < g1.re) (hd : g1.drop = false) (hj : JmpIn (· < g1.re) thq)
    (e1 : runLC env msup q (CGoalL.next (Lazy.ofSure (lazyReg rq)) thq) region g1 = some (n2, g2))
    (e2 : pastL env.cod n2 p region g2 = some (n2', g3))
    (e3 : runLC env msup p (CGoalL.next (Lazy.ofSure (lazyReg rp)) n2'.th) region g3 = some (n1, g4))
    (e4 : copyL n1 n2'.laz g4 = some (nex, g')) :
    g1.re ≤ g'.re ∧ g1.bo ≤ g'.bo ∧ GInv g' nex.goal ∧ ∀ x ∈ lregs nex.laz, k ≤ x := by
  obtain ⟨l, b, i, s⟩ := tail_all ihq ihp (ginv_reg_j hrq hd hj) (linv_reg (by omega))
    (by simp [lregs_reg]; omega) e1 e2 e3 e4
  refine ⟨l, b, i, fun x hx => ?_⟩
  rcases s x hx with e | e
  · simp [lregs_reg] at e; omega
  · omega

/-- The tail with two needs that ask nothing. -/
theorem tail_bunt {env : CallEnv} {msup : Option Nomm} {p q : Nomm} {region : List Nat}
    (ihq : ResFor env msup q region) (ihp : ResFor env msup p region)
    {thq : Jmp} {g1 g2 g3 g4 g' : Gen (TreapMap mugF)} {n2 n2' n1 nex : NextL CSet}
    (hd : g1.drop = false) (hj : JmpIn (· < g1.re) thq)
    (e1 : runLC env msup q (CGoalL.next (Lazy.ofSure Sure.bunt) thq) region g1 = some (n2, g2))
    (e2 : pastL env.cod n2 p region g2 = some (n2', g3))
    (e3 : runLC env msup p (CGoalL.next (Lazy.ofSure Sure.bunt) n2'.th) region g3 = some (n1, g4))
    (e4 : copyL n1 n2'.laz g4 = some (nex, g')) :
    g1.re ≤ g'.re ∧ g1.bo ≤ g'.bo ∧ GInv g' nex.goal ∧ ∀ x ∈ lregs nex.laz, g1.re ≤ x := by
  obtain ⟨l, b, i, s⟩ := tail_all ihq ihp (ginv_bunt_j hd hj) (linv_bunt _ _) (by simp [lregs_bunt]) e1 e2 e3 e4
  refine ⟨l, b, i, fun x hx => ?_⟩
  rcases s x hx with e | e
  · simp [lregs_bunt] at e
  · exact e

/-! ## The cases -/

theorem km_drop {α : Type} {m : CM (TreapMap mugF) α} (hm : KM m) {g g' : Gen (TreapMap mugF)} {x : α}
    (h : m g = some (x, g')) (hd : g.drop = false) : g.re ≤ g'.re ∧ g.bo ≤ g'.bo ∧ g'.drop = false :=
  let k := hm.keep g x g' h; ⟨k.1, k.2.1, k.2.2.trans hd⟩

theorem re_step {g g1 : Gen (TreapMap mugF)} {r : Nat} (h : (re : CM (TreapMap mugF) Nat) g = some (r, g1)) :
    r = g.re ∧ g1 = { g with re := g.re + 1 } := by
  rw [re_apply] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact ⟨h.1.symm, h.2.symm⟩

theorem res_n0 (env : CallEnv) (msup : Option Nomm) (ax : Nat) (region : List Nat) :
    ResFor env msup (Nomm.n0 ax) region := by
  intro goal g g' nex hi h
  have hd := ginv_drop hi
  simp only [runLC] at h
  split at h
  · obtain ⟨l, b, d⟩ := km_drop (km_bombL _) h hd
    simp only [bombL] at h
    obtain ⟨o, g1, e1, h⟩ := bind_some h
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact gres_bunt l b d (jmpIn_jmp0 _ _)
  · obtain ⟨nex0, g1, e1, h⟩ := bind_some h
    have S := simpleNextL_res hi e1
    split at h
    · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact S
    · cases hf : Lazy.fromL ax nex0.laz with
      | none => simp [hf] at h
      | some laz' =>
        simp only [hf, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨l, b, ⟨i, d, j⟩, s⟩ := S
        obtain ⟨i', r'⟩ := fromL_inv i hf
        exact ⟨l, b, ⟨i', d, j⟩, fun x hx => s x (by rw [← r']; exact hx)⟩

theorem res_n1 (env : CallEnv) (msup : Option Nomm) (k : Noun) (region : List Nat) :
    ResFor env msup (Nomm.n1 k) region := by
  intro goal g g' nex hi h
  have hd := ginv_drop hi
  cases goal with
  | done =>
    simp only [runLC] at h
    obtain ⟨r, g1, e1, h⟩ := bind_some h
    obtain ⟨o, g2, e2, h⟩ := bind_some h
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨l1, b1, d1⟩ := km_drop KM.re' e1 hd
    obtain ⟨l2, b2, d2⟩ := km_drop (KM.emit' _) e2 d1
    exact gres_bunt (by omega) (by omega) d2 (jmpIn_jmp0 _ _)
  | pick z o =>
    simp only [runLC] at h
    split at h
    · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact gres_bunt (Nat.le_refl _) (Nat.le_refl _) hd hi.2.1
    · split at h
      · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact gres_bunt (Nat.le_refl _) (Nat.le_refl _) hd hi.2.2
      · obtain ⟨l, b, d⟩ := km_drop (km_bombL _) h hd
        simp only [bombL] at h
        obtain ⟨o', g1, e1, h⟩ := bind_some h
        simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact gres_bunt l b d (jmpIn_jmp0 _ _)
  | next laz th =>
    simp only [runLC] at h
    obtain ⟨o, g1, e1, h⟩ := bind_some h
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨l, b, d⟩ := km_drop (km_medeL _ _ _) e1 hd
    exact gres_bunt l b d (jmpIn_jmp0 _ _)

/-- The end of `%3` and `%4`: a block, then `p` for a fresh register's goal. -/
theorem res_last {env : CallEnv} {msup : Option Nomm} {p : Nomm} {region : List Nat}
    (ih : ResFor env msup p region) {goal : CGoalL CSet} {g g1 g2 g' : Gen (TreapMap mugF)} {r oc : Nat}
    {b : Blob} {nex : NextL CSet} (e : emit b g1 = some (oc, g2))
    (h : runLC env msup p (CGoalL.next (Lazy.ofSure (lazyReg r)) (jmp0 oc)) region g2 = some (nex, g'))
    (hd : g1.drop = false) (hr : g.re ≤ r) (hr1 : r < g1.re) (hl : g.re ≤ g1.re) (hb : g.bo ≤ g1.bo) :
    GRes g goal g' nex := by
  obtain ⟨l2, b2, d2⟩ := km_drop (KM.emit' _) e hd
  exact gres_fresh (ih _ _ _ _ (ginv_reg oc (by omega) d2) h) hr (by omega) (by omega)

theorem res_n3 {env : CallEnv} {msup : Option Nomm} {p : Nomm} {region : List Nat}
    (ih : ResFor env msup p region) : ResFor env msup (Nomm.n3 p) region := by
  intro goal g g' nex hi h
  have hd := ginv_drop hi
  cases goal with
  | next laz th =>
    simp only [runLC] at h
    split at h
    · exact ih _ _ _ _ hi h
    · obtain ⟨a, g1, e1, h⟩ := bind_some h
      obtain ⟨l1, b1, d1⟩ := km_drop (km_collapseLazyAtomL _) e1 hd
      rcases a with _ | ⟨r, o⟩
      · cases h
      · obtain ⟨⟨z, o'⟩, g2, e2, h⟩ := bind_some h
        obtain ⟨l2, b2, d2⟩ := km_drop (km_forl _ _) e2 d1
        obtain ⟨r', g3, e3, h⟩ := bind_some h
        obtain ⟨rfl, rfl⟩ := re_step e3
        obtain ⟨oc, g4, e4, h⟩ := bind_some h
        refine res_last ih e4 h d2 ?_ ?_ ?_ ?_ <;> (try simp) <;> omega
  | pick z o =>
    simp only [runLC] at h
    obtain ⟨r, g1, e1, h⟩ := bind_some h
    obtain ⟨rfl, rfl⟩ := re_step e1
    obtain ⟨oc, g2, e2, h⟩ := bind_some h
    refine res_last ih e2 h hd ?_ ?_ ?_ ?_ <;> (try simp) <;> omega
  | done =>
    simp only [runLC] at h
    obtain ⟨⟨o0, o1⟩, g1, e1, h⟩ := bind_some h
    obtain ⟨l1, b1, d1⟩ := km_drop km_doneBlocks e1 hd
    obtain ⟨r, g2, e2, h⟩ := bind_some h
    obtain ⟨rfl, rfl⟩ := re_step e2
    obtain ⟨oc, g3, e3, h⟩ := bind_some h
    refine res_last ih e3 h d1 ?_ ?_ ?_ ?_ <;> (try simp) <;> omega

theorem res_n4 {env : CallEnv} {msup : Option Nomm} {p : Nomm} {region : List Nat}
    (ih : ResFor env msup p region) : ResFor env msup (Nomm.n4 p) region := by
  intro goal g g' nex hi h
  have hd := ginv_drop hi
  cases goal with
  | done =>
    simp only [runLC] at h
    obtain ⟨pro, g1, e1, h⟩ := bind_some h
    obtain ⟨rfl, rfl⟩ := re_step e1
    obtain ⟨arg, g2, e2, h⟩ := bind_some h
    obtain ⟨rfl, rfl⟩ := re_step e2
    obtain ⟨o, g3, e3, h⟩ := bind_some h
    refine res_last ih e3 h hd ?_ ?_ ?_ ?_ <;> (try simp) <;> omega
  | pick z o =>
    simp only [runLC] at h
    obtain ⟨pro, g1, e1, h⟩ := bind_some h
    obtain ⟨rfl, rfl⟩ := re_step e1
    obtain ⟨arg, g2, e2, h⟩ := bind_some h
    obtain ⟨rfl, rfl⟩ := re_step e2
    obtain ⟨o', g3, e3, h⟩ := bind_some h
    refine res_last ih e3 h hd ?_ ?_ ?_ ?_ <;> (try simp) <;> omega
  | next laz th =>
    simp only [runLC] at h
    obtain ⟨a, g1, e1, h⟩ := bind_some h
    obtain ⟨l1, b1, d1⟩ := km_drop (km_collapseLazyAtomL _) e1 hd
    obtain ⟨⟨pro, th'⟩, g2, e2, h⟩ := bind_some h
    have k2 : g1.re ≤ g2.re ∧ g1.bo ≤ g2.bo ∧ g2.drop = false := by
      rcases a with _ | x
      · simp only at e2
        obtain ⟨r, g5, h5, e2⟩ := bind_some e2
        obtain ⟨rfl, rfl⟩ := re_step h5
        split at e2
        · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e2
          obtain ⟨-, rfl⟩ := e2
          exact ⟨by simp, by simp, d1⟩
        · cases e2
      · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e2
        obtain ⟨-, rfl⟩ := e2
        exact ⟨Nat.le_refl _, Nat.le_refl _, d1⟩
    obtain ⟨arg, g3, e3, h⟩ := bind_some h
    obtain ⟨rfl, rfl⟩ := re_step e3
    obtain ⟨o, g4, e4, h⟩ := bind_some h
    refine res_last ih e4 h k2.2.2 ?_ ?_ ?_ ?_ <;> (try simp) <;> omega

theorem res_n7 {env : CallEnv} {msup : Option Nomm} {p q : Nomm} {region : List Nat}
    (ihq : ResFor env (some p) q region) (ihp : ResFor env msup p region) : ResFor env msup (Nomm.n7 p q) region := by
  intro goal g g' nex hi h
  simp only [runLC] at h
  obtain ⟨nex1, g1, e1, h⟩ := bind_some h
  have R1 := ihq _ _ _ _ hi e1
  exact gres_comp R1 (ihp _ _ _ _ R1.2.2.1 h)

/-- A run from a state reached from an earlier one, the goal's registers
fresh or the earlier goal's. -/
theorem gres_pre {g g1 g' : Gen (TreapMap mugF)} {goal goal' : CGoalL CSet} {nex : NextL CSet}
    (R : GRes g1 goal' g' nex) (hl : g.re ≤ g1.re) (hb : g.bo ≤ g1.bo)
    (hs : ∀ x ∈ gregs goal', g.re ≤ x ∨ x ∈ gregs goal) : GRes g goal g' nex := by
  obtain ⟨l, b, i, s⟩ := R
  refine ⟨by omega, by omega, i, fun x hx => ?_⟩
  rcases s x hx with e | e
  · exact Or.inl (by omega)
  · exact hs x e

theorem res_n5 {env : CallEnv} {msup : Option Nomm} {p q : Nomm} {region : List Nat}
    (ihp : ResFor env msup p region) (ihq : ResFor env msup q region) : ResFor env msup (Nomm.n5 p q) region := by
  intro goal g g' nex hi h
  have hd := ginv_drop hi
  simp only [runLC] at h
  obtain ⟨rp, g1, e1, h⟩ := bind_some h
  obtain ⟨rfl, rfl⟩ := re_step e1
  obtain ⟨rq, g2, e2, h⟩ := bind_some h
  obtain ⟨rfl, rfl⟩ := re_step e2
  obtain ⟨o, g3, e3, h⟩ := bind_some h
  have k3 := (?_ : KM _).keep _ _ _ e3
  rotate_left
  · cases goal with
    | pick z o' => exact KM.emit' _
    | done => exact KM.bind' km_doneBlocks fun _ => KM.emit' _
    | next laz th =>
      refine KM.bind' (km_collapseLazyAtomL _) fun a => ?_
      rcases a with _ | ⟨r, o'⟩
      · exact KM.ite' _ (KM.emit' _) KM.fail
      · exact KM.bind' (km_forl _ _) fun _ => KM.emit' _
  obtain ⟨n2, g4, e4, h⟩ := bind_some h
  obtain ⟨n2', g5, e5, h⟩ := bind_some h
  obtain ⟨n1, g6, e6, e7⟩ := bind_some h
  simp only at k3
  obtain ⟨l, b, i, s⟩ := tail_fresh ihq ihp (k := g.re) (Nat.le_refl _) (Nat.lt_succ_self _) (by omega)
    (by rw [k3.2.2]; exact hd) (jmpIn_jmp0 _ _) e4 e5 e6 e7
  exact ⟨by omega, by omega, i, fun x hx => Or.inl (s x hx)⟩

theorem res_n2 {env : CallEnv} {msup : Option Nomm} {p q : Nomm} {region : List Nat}
    (ihp : ResFor env msup p region) (ihq : ResFor env msup q region) :
    ResFor env msup (Nomm.n2 p q Option.none) region := by
  intro goal g g' nex hi h
  have hd := ginv_drop hi
  obtain ⟨nex0, g1, out, pro, g2, o, g3, nexF, g4, nexF', g5, nexS, g6, h1, h2, h3, h4, h5, h6, h7⟩ :=
    runLC_n2_none h
  obtain ⟨l1, b1, d1⟩ := km_drop (km_simpleNextL _) h1 hd
  obtain ⟨l2, b2, d2⟩ := km_drop (km_kerf _) h2 d1
  obtain ⟨l3, b3, d3⟩ := km_drop (KM.emit' _) h3 d2
  simp only at l3 b3
  obtain ⟨l, b, i, s⟩ := tail_fresh ihq ihp (k := g.re) (by omega) (Nat.lt_succ_self _) (by omega) d3
    (jmpIn_jmp0 _ _) h4 h5 h6 h7
  exact ⟨by omega, by omega, i, fun x hx => Or.inl (s x hx)⟩

/-- The `%next` branch of the cons. -/
theorem res_cons_next {env : CallEnv} {msup : Option Nomm} {p q : Nomm} {region : List Nat}
    (ihp : ResFor env msup p region) (ihq : ResFor env msup q region) {laz : Lazy CSet} {th : Jmp}
    {g g1 g2 g3 g4 g5 g' : Gen (TreapMap mugF)} {hed tel : Lazy CSet} {o : Nat} {nexh n2 n2' n1 nex : NextL CSet}
    (hi : GInv g (CGoalL.next laz th))
    (e1 : splitL ⟨laz, th⟩ g = some ((hed, tel, o), g1))
    (e2 : pastL env.cod ⟨hed, jmp0 o⟩ q region g1 = some (nexh, g2))
    (e3 : runLC env msup q (CGoalL.next tel nexh.th) region g2 = some (n2, g3))
    (e4 : pastL env.cod n2 p region g3 = some (n2', g4))
    (e5 : runLC env msup p (CGoalL.next nexh.laz n2'.th) region g4 = some (n1, g5))
    (e6 : copyL n1 n2'.laz g5 = some (nex, g')) :
    GRes g (CGoalL.next laz th) g' nex := by
  obtain ⟨l1, b1, d1, ih, it, nd, src⟩ := splitL_inv hi e1
  obtain ⟨r2, b2, d2, i2, j2, rg2⟩ := pastL_inv ih (jmpIn_jmp0 _ _) e2
  have hq : GInv g2 (CGoalL.next tel nexh.th) := ⟨linv_mono it (by omega) b2, d2.trans d1, j2⟩
  obtain ⟨l, b, i, s⟩ := tail_all ihq ihp hq i2 (by rw [rg2]; exact nd) e3 e4 e5 e6
  refine ⟨by omega, by omega, i, fun x hx => ?_⟩
  rcases s x hx with e | e
  · rw [rg2] at e
    rcases src x e with e' | e'
    · exact Or.inr e'
    · exact Or.inl e'
  · exact Or.inl (by omega)

theorem res_cons {env : CallEnv} {msup : Option Nomm} {p q : Nomm} {region : List Nat}
    (ihp : ResFor env msup p region) (ihq : ResFor env msup q region) : ResFor env msup (Nomm.cons p q) region := by
  intro goal g g' nex hi h
  have hd := ginv_drop hi
  simp only [runLC] at h
  obtain ⟨goal', g1, e1, h⟩ := bind_some h
  -- the goal after the `=>` for `%done`
  have G : GInv g1 goal' ∧ g.re ≤ g1.re ∧ g.bo ≤ g1.bo ∧ (∀ x ∈ gregs goal', g.re ≤ x ∨ x ∈ gregs goal) := by
    cases goal with
    | done =>
      simp only at e1
      obtain ⟨r, g5, h5, e1⟩ := bind_some e1
      obtain ⟨rfl, rfl⟩ := re_step h5
      obtain ⟨o, g6, h6, e1⟩ := bind_some e1
      simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e1
      obtain ⟨rfl, rfl⟩ := e1
      obtain ⟨l6, b6, d6⟩ := km_drop (KM.emit' _) h6 hd
      simp only at l6 b6
      refine ⟨ginv_reg _ (by omega) d6, by omega, by omega, fun x hx => ?_⟩
      simp [gregs, lregs_ofSure, lazyReg, flattenNeed] at hx
      exact Or.inl (by omega)
    | pick z o =>
      simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e1
      obtain ⟨rfl, rfl⟩ := e1
      exact ⟨hi, Nat.le_refl _, Nat.le_refl _, fun x hx => Or.inr hx⟩
    | next laz th =>
      simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e1
      obtain ⟨rfl, rfl⟩ := e1
      exact ⟨hi, Nat.le_refl _, Nat.le_refl _, fun x hx => Or.inr hx⟩
  obtain ⟨gi, gl, gb, gs⟩ := G
  cases goal' with
  | pick z o =>
    obtain ⟨o', g2, e2, h⟩ := bind_some h
    obtain ⟨l2, b2, d2⟩ := km_drop (KM.emit' _) e2 gi.1
    obtain ⟨n2, g3, e3, h⟩ := bind_some h
    obtain ⟨n2', g4, e4, h⟩ := bind_some h
    obtain ⟨n1, g5, e5, e6⟩ := bind_some h
    obtain ⟨l, b, i, s⟩ := tail_bunt ihq ihp d2 (jmpIn_jmp0 _ _) e3 e4 e5 e6
    exact ⟨by omega, by omega, i, fun x hx => Or.inl (by have := s x hx; omega)⟩
  | done => cases h
  | next laz th =>
    obtain ⟨⟨hed, tel, o⟩, g2, e2, h⟩ := bind_some h
    obtain ⟨nexh, g3, e3, h⟩ := bind_some h
    obtain ⟨n2, g4, e4, h⟩ := bind_some h
    obtain ⟨n2', g5, e5, h⟩ := bind_some h
    obtain ⟨n1, g6, e6, e7⟩ := bind_some h
    exact gres_pre (res_cons_next ihp ihq gi e2 e3 e4 e5 e6 e7) gl gb gs

theorem res_n10 {env : CallEnv} {msup : Option Nomm} {a : Nat} {v q : Nomm} {region : List Nat} (ha : a ≠ 0)
    (ihv : ResFor env msup v region) (ihq : ResFor env msup q region) :
    ResFor env msup (Nomm.n10 a v q) region := by
  intro goal g g' nex hi h
  simp only [runLC] at h
  obtain ⟨nx, g1, e1, h⟩ := bind_some h
  have S := simpleNextL_res hi e1
  obtain ⟨⟨don, rec, o⟩, g2, e2, h⟩ := bind_some h
  obtain ⟨nexR, g3, e3, h⟩ := bind_some h
  obtain ⟨n2, g4, e4, h⟩ := bind_some h
  obtain ⟨n2', g5, e5, h⟩ := bind_some h
  obtain ⟨n1, g6, e6, e7⟩ := bind_some h
  obtain ⟨sl, sb, si, ss⟩ := S
  obtain ⟨l2, b2, d2, id, ir, nd, src⟩ := intoL_inv ha si e2
  obtain ⟨r3, b3, d3, i3, j3, rg3⟩ := pastL_inv ir (jmpIn_jmp0 _ _) e3
  have hq : GInv g3 (CGoalL.next don nexR.th) := ⟨linv_mono id (by omega) b3, d3.trans d2, j3⟩
  have nd' : (lregs nexR.laz ++ lregs don).Nodup := by
    rw [rg3, List.nodup_append]
    obtain ⟨a1, a2, a3⟩ := List.nodup_append.1 nd
    exact ⟨a2, a1, fun x hx y hy e => a3 y hy x hx e.symm⟩
  obtain ⟨l, b, i, s⟩ := tail_all ihv ihq hq i3 nd' e4 e5 e6 e7
  refine ⟨by omega, by omega, i, fun x hx => ?_⟩
  rcases s x hx with e | e
  · have e' : x ∈ lregs don ++ lregs rec := by
      rw [rg3] at e
      rcases List.mem_append.1 e with e | e
      · exact List.mem_append_right _ e
      · exact List.mem_append_left _ e
    rcases src x e' with e'' | e''
    · rcases ss x e'' with f | f
      · exact Or.inl f
      · exact Or.inr f
    · exact Or.inl (by omega)
  · exact Or.inl (by omega)

/-- **What the runs of the plain class return** (`RunResL`). -/
theorem res_all (env : CallEnv) : ∀ (n : Nomm), PlainOk n = true → ∀ (msup : Option Nomm) (region : List Nat),
    ResFor env msup n region
  | Nomm.cons p q, h, msup, region => by
    simp only [PlainOk, Bool.and_eq_true] at h
    exact res_cons (res_all env p h.1 msup region) (res_all env q h.2 msup region)
  | Nomm.n0 ax, _, msup, region => res_n0 env msup ax region
  | Nomm.n1 k, _, msup, region => res_n1 env msup k region
  | Nomm.n2 p q Option.none, h, msup, region => by
    simp only [PlainOk, Bool.and_eq_true] at h
    exact res_n2 (res_all env p h.1 msup region) (res_all env q h.2 msup region)
  | Nomm.n3 p, h, msup, region => by
    simp only [PlainOk] at h
    exact res_n3 (res_all env p h msup region)
  | Nomm.n4 p, h, msup, region => by
    simp only [PlainOk] at h
    exact res_n4 (res_all env p h msup region)
  | Nomm.n5 p q, h, msup, region => by
    simp only [PlainOk, Bool.and_eq_true] at h
    exact res_n5 (res_all env p h.1 msup region) (res_all env q h.2 msup region)
  | Nomm.n7 p q, h, msup, region => by
    simp only [PlainOk, Bool.and_eq_true] at h
    exact res_n7 (res_all env q h.2 (some p) region) (res_all env p h.1 msup region)
  | Nomm.n10 a v q, h, msup, region => by
    simp only [PlainOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact res_n10 h.1.1 (res_all env v h.1.2 msup region) (res_all env q h.2 msup region)
  | Nomm.n2 _ _ (some _), h, _, _ => by simp [PlainOk] at h
  | Nomm.n6 _ _ _, h, _, _ => by simp [PlainOk] at h
  | Nomm.n11s _ _ _, h, _, _ => by simp [PlainOk] at h
  | Nomm.n11d _ _ _ _, h, _, _ => by simp [PlainOk] at h
  | Nomm.n12 _ _, h, _, _ => by simp [PlainOk] at h
  | Nomm.mean _ _ _ _ _, h, _, _ => by simp [PlainOk] at h

/-- **`RunResL` holds.** -/
theorem runResL : RunResL := fun env n hn msup goal region g g' nex hi h =>
  res_all env n hn msup region goal g g' nex hi h

end Compiler
end Formalization
