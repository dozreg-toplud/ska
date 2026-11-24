import lemmas.Compiler.CompRunSixS

/-!
# What the case `%6` returns under `%done` and `%pick`

`six_tail_res`: the tail of phase S (`sixTail`) keeps `GInv` and makes its
need of the registers of `nex-cond`, of `lazy`, and fresh ones (the register
of `+kern` when `+lazy-shut` fires).  `res_n6_dp`: a run of `%6` under
`%done` or `%pick` from a state with `GInv` returns a result with `GRes`,
given what the runs of the parts return (`ResFor`): the two branches' needs
are apart (each is made of fresh registers of its own run, `gregs` of
`%done` and `%pick` being empty), the fork of the two `%hop` blocks meets
`LInv` (`lyn_linv`), `+past-fork` keeps it (`linv_pastFork`), and the test's
need is fresh.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-- **The tail of phase S keeps the invariant.** -/
theorem six_tail_res {g g' : Gen (TreapMap mugF)} {nexCond : NextL CSet} {lazy : Lazy CSet} {nex : NextL CSet}
    (hc : LInv g.re g.bo nexCond.laz) (hl : LInv g.re g.bo lazy) (ap : (lregs nexCond.laz ++ lregs lazy).Nodup)
    (hd : g.drop = false) (h : sixTail nexCond lazy g = some (nex, g')) :
    g.re ≤ g'.re ∧ g.bo ≤ g'.bo ∧ GInv g' nex.goal ∧
      ∀ y ∈ lregs nex.laz, y ∈ lregs nexCond.laz ++ lregs lazy ∨ g.re ≤ y := by
  unfold sixTail at h
  rw [Lazy.softLess_noSoft] at h
  cases eb : Lazy.lazyBig lazy
  · simp only [eb, Bool.not_false, if_true] at h
    exact copyL_inv hc hl ap hd h
  · simp only [eb, Bool.not_true, Bool.false_eq_true, if_false] at h
    obtain ⟨o, g1, e1, h⟩ := bind_some h
    rw [emit_apply] at e1
    simp only [Option.some.injEq, Prod.mk.injEq] at e1
    obtain ⟨rfl, rfl⟩ := e1
    obtain ⟨lz, g2, e2, h⟩ := bind_some h
    unfold lazyShut at e2
    rw [Lazy.softLess_noSoft, eb] at e2
    simp only [Bool.not_true, Bool.false_eq_true, if_false] at e2
    obtain ⟨rk, g3, e3, e4⟩ := bind_some e2
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at e4
    obtain ⟨rfl, rfl⟩ := e4
    obtain ⟨er, lr⟩ := kern_reg e3
    obtain ⟨-, b3, d3⟩ := (km_kern (S := CSet) (Map := TreapMap mugF) _ _).keep _ _ _ e3
    simp only [emitted_re] at er lr
    have hb1 : (g.emitted ⟨[], [], Termin.hop nexCond.th⟩).bo = g.bo + 1 := by
      rcases g with ⟨re, bo, id, drop, blocks, tags, cond⟩; cases drop <;> rfl
    have dr1 : (g.emitted ⟨[], [], Termin.hop nexCond.th⟩).drop = false := by rw [emitted_drop]; exact hd
    have hc3 : LInv g3.re g3.bo nexCond.laz := linv_mono hc (by omega) (by omega)
    have hr3 : LInv g3.re g3.bo (Lazy.ofSure (lazyReg rk : Sure CSet)) := linv_reg (by omega)
    have ap3 : (lregs nexCond.laz ++ lregs (Lazy.ofSure (lazyReg rk : Sure CSet))).Nodup := by
      rw [lregs_reg, List.nodup_append]
      refine ⟨(List.nodup_append.1 ap).1, by simp, fun y hy z hz => ?_⟩
      simp only [List.mem_singleton] at hz
      have := lnb_regs hc.1 y hy
      omega
    obtain ⟨l4, b4, gi4, s4⟩ := copyL_inv (first := ⟨nexCond.laz, jmp0 g.bo⟩) hc3 hr3 ap3 (d3.trans dr1) h
    refine ⟨by omega, by omega, gi4, fun y hy => ?_⟩
    rcases s4 y hy with e | e
    · rw [List.mem_append, lregs_reg, List.mem_singleton] at e
      rcases e with e | e
      · exact Or.inl (List.mem_append_left _ e)
      · exact Or.inr (by omega)
    · exact Or.inr (by omega)

/-- **The fork of the two `%hop` blocks meets `LInv`**: the two needs with
`LInv` at the counters, apart, their blocks below the label counter. -/
theorem lyn_linv {kr kb yes nuh : Nat} {l0 l1 : Lazy CSet} (h0 : LInv kr kb l0) (h1 : LInv kr kb l1)
    (ap : ∀ y ∈ lregs l0, y ∉ lregs l1) (hy : yes < kb) (hn : nuh < kb) :
    LInv kr kb (Lazy.mk Sure.bunt [((yes, l0), (nuh, l1))] []) := by
  refine ⟨⟨(linv_bunt kr kb).1.1, ⟨by rw [walkP_irrel]; exact h0.1, by rw [walkP_irrel]; exact h1.1, trivial⟩,
    trivial⟩, ?_, ⟨by simp, by simp, ⟨h0.2.2.1, h1.2.2.1, trivial⟩, trivial⟩, ?_⟩
  · simp only [lregs, fregs, bregs, flattenNeed, Sure.bunt, List.nil_append, List.append_nil]
    exact List.nodup_append.2 ⟨h0.2.1, h1.2.1, fun a ha b hb e => ap a ha (e ▸ hb)⟩
  · intro o ho
    simp only [llabs, flabs, blabs, List.append_nil, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at ho
    rcases ho with rfl | rfl | ho | ho
    · exact hy
    · exact hn
    · exact h0.2.2.2 o ho
    · exact h1.2.2.2 o ho

/-- **What `%6` returns under `%done` and `%pick`.** -/
theorem res_n6_dp {env : CallEnv} {msup : Option Nomm} {p q r : Nomm} {region : List Nat}
    (ihp : ResFor env msup p region) (ihq : ResFor env msup q region) (ihr : ResFor env msup r region)
    (goal : CGoalL CSet) (hg : ∀ laz th, goal ≠ CGoalL.next laz th) (g g' : Gen (TreapMap mugF))
    (nex : NextL CSet) (hi : GInv g goal) (h : runLC env msup (Nomm.n6 p q r) goal region g = some (nex, g')) :
    GRes g goal g' nex := by
  have hgr : gregs goal = [] := by cases goal with
    | next laz th => exact absurd rfl (hg laz th)
    | done => rfl
    | pick z o => rfl
  have hd := ginv_drop hi
  rw [runLC_n6_dp env msup p q r goal hg region] at h
  obtain ⟨c0, g0, e0, h⟩ := bind_some h
  simp only [getCond, Option.some.injEq, Prod.mk.injEq] at e0
  obtain ⟨-, rfl⟩ := e0
  obtain ⟨nex1, g1, e1, h⟩ := bind_some h
  obtain ⟨c1, g1', e1', h⟩ := bind_some h
  simp only [getCond, Option.some.injEq, Prod.mk.injEq] at e1'
  obtain ⟨-, rfl⟩ := e1'
  obtain ⟨nex0, g2, e2, h⟩ := bind_some h
  obtain ⟨l1, b1, gi1, s1⟩ := ihr goal g g1 nex1 hi e1
  have hi1 : GInv g1 goal := ginv_mono hi l1 b1 ((ginv_drop gi1).trans hd.symm)
  obtain ⟨l2, b2, gi2, s2⟩ := ihq goal g1 g2 nex0 hi1 e2
  have d2 : g2.drop = false := ginv_drop gi2
  unfold sixLynDP at h
  obtain ⟨yes, g3, e3, h⟩ := bind_some h
  rw [emit_apply] at e3
  simp only [Option.some.injEq, Prod.mk.injEq] at e3
  obtain ⟨rfl, rfl⟩ := e3
  obtain ⟨nuh, g4, e4, h⟩ := bind_some h
  rw [emit_apply] at e4
  simp only [Option.some.injEq, Prod.mk.injEq] at e4
  obtain ⟨rfl, rfl⟩ := e4
  obtain ⟨u5, g5, e5, h⟩ := bind_some h
  rw [st_apply] at e5
  simp only [Option.some.injEq, Prod.mk.injEq] at e5
  obtain ⟨-, rfl⟩ := e5
  obtain ⟨u6, g6, e6, h⟩ := bind_some h
  rw [st_apply] at e6
  simp only [Option.some.injEq, Prod.mk.injEq] at e6
  obtain ⟨-, rfl⟩ := e6
  split at h
  · cases h
  split at h
  · cases h
  -- the state after the two blocks and their tags
  generalize hG : stG (g2.emitted ⟨[], [], Termin.hop nex0.th⟩).bo region
    (stG g2.bo region ((g2.emitted ⟨[], [], Termin.hop nex0.th⟩).emitted ⟨[], [], Termin.hop nex1.th⟩)) = G at h
  have rG : G.re = g2.re := by rw [← hG, stG_re, stG_re]; rfl
  have bG : G.bo = g2.bo + 2 := by rw [← hG, stG_bo, stG_bo]; rfl
  have dG : G.drop = false := by rw [← hG, stG_drop, stG_drop]; exact d2
  unfold sixPM at h
  obtain ⟨lazy, g7, e7, h⟩ := bind_some h
  simp only [liftO] at e7
  cases epf : Lazy.pastFork env.cod (Lazy.mk Sure.bunt [((g2.bo, nex0.laz), ((g2.emitted ⟨[], [], Termin.hop nex0.th⟩).bo, nex1.laz))] []) p with
  | none => rw [epf] at e7; cases e7
  | some lz =>
  rw [epf] at e7
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e7
  obtain ⟨rfl, rfl⟩ := e7
  obtain ⟨nexC, g8, e8, h⟩ := bind_some h
  obtain ⟨l8, b8, gi8, s8⟩ := ihp _ G g8 nexC
    (show GInv G (CGoalL.pick (jmp0 g2.bo) (jmp0 (g2.emitted ⟨[], [], Termin.hop nex0.th⟩).bo)) from
      ⟨dG, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩) e8
  -- the fork of the two blocks
  have f0 : ∀ y ∈ lregs nex0.laz, g1.re ≤ y := fun y hy => by
    rcases s2 y hy with e | e
    · exact e
    · simp [hgr] at e
  have f1 : ∀ y ∈ lregs nex1.laz, g.re ≤ y := fun y hy => by
    rcases s1 y hy with e | e
    · exact e
    · simp [hgr] at e
  have lv0 : LInv G.re G.bo nex0.laz := linv_mono gi2.1 (by omega) (by omega)
  have lv1 : LInv G.re G.bo nex1.laz := linv_mono gi1.1 (by omega) (by omega)
  have ap01 : ∀ y ∈ lregs nex0.laz, y ∉ lregs nex1.laz := fun y hy hy' => by
    have := f0 y hy; have := lnb_regs gi1.1.1 y hy'; omega
  have lvF := lyn_linv lv0 lv1 ap01 (yes := g2.bo) (nuh := (g2.emitted ⟨[], [], Termin.hop nex0.th⟩).bo)
    (by omega) (by simp [emitted_bo]; omega)
  have lvP : LInv G.re G.bo lz := linv_pastFork epf lvF
  have hC : LInv g8.re g8.bo nexC.laz := gi8.1
  have hP8 : LInv g8.re g8.bo lz := linv_mono lvP l8 b8
  have ap8 : (lregs nexC.laz ++ lregs lz).Nodup := by
    refine List.nodup_append.2 ⟨gi8.1.2.1, lvP.2.1, fun a ha b hb e => ?_⟩
    subst e
    have := lnb_regs lvP.1 a hb
    rcases s8 a ha with e | e
    · omega
    · simp [gregs] at e
  have d8 : g8.drop = false := ginv_drop gi8
  obtain ⟨l9, b9, gi9, s9⟩ := six_tail_res hC hP8 ap8 d8 h
  refine ⟨by omega, by omega, gi9, fun y hy => Or.inl ?_⟩
  rcases s9 y hy with e | e
  · rcases List.mem_append.1 e with e | e
    · rcases s8 y e with e' | e'
      · omega
      · simp [gregs] at e'
    · rw [lregs_pastFork epf] at e
      simp only [lregs, fregs, bregs, flattenNeed, Sure.bunt, List.nil_append, List.append_nil,
        List.mem_append] at e
      rcases e with e | e
      · have := f0 y e; omega
      · exact f1 y e
  · omega

end Compiler
end Formalization
