import lemmas.Compiler.CompRunKeep

/-!
# The invariant through the helpers, and the tail of two runs

The helpers of `+run` on a goal with `GInv`, in the form the cases use:
`+split` and `+into` (`splitL_inv`, `intoL_inv`: two halves with `LInv`,
apart, made of the goal's registers and fresh ones), `+from`
(`fromL_inv`), `+past` (`pastL_inv`), `+copy` (`copyL_inv`), and the goals
of fresh registers (`ginv_reg`, `gres_fresh`).

**The tail** of cons, `%5`, `%10` and `%2`: `q` runs for `[%next Gq thq]`,
`+past` over `p`, `p` runs for `[%next Gp then]`, `+copy`.  When `q`'s goal
meets `GInv`, `Gp` meets `LInv` and is apart from `Gq` (`(lregs Gp ++ lregs
Gq).Nodup`), and the runs meet `GRes`: `p`'s goal meets `GInv`
(`tail_pgoal`), the `+copy` joins two needs with `CopyH` (`tail_copyH`, the
side condition of `comp_copy_all`), and its result meets `GInv` with its
registers in `Gp`, `Gq` or fresh (`tail_res`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## `LInv` -/

theorem linv_mono {kr kb kr' kb' : Nat} {laz : Lazy CSet} (h : LInv kr kb laz) (hr : kr ≤ kr') (hb : kb ≤ kb') :
    LInv kr' kb' laz :=
  ⟨lall_mono (fun _ hs => ⟨hs.1, hs.2.mono hr⟩) h.1, h.2.1, h.2.2.1, fun o ho => Nat.lt_of_lt_of_le (h.2.2.2 o ho) hb⟩

theorem linv_reg {kr kb r : Nat} (hr : r < kr) : LInv kr kb (Lazy.ofSure (lazyReg r : Sure CSet)) := by
  refine ⟨⟨⟨cra_lok_reg r, nb_this hr⟩, trivial, trivial⟩, by simp [lregs_ofSure, lazyReg, flattenNeed],
    lkeys_ofSure _, by simp [llabs_ofSure]⟩

theorem linv_bunt (kr kb : Nat) : LInv kr kb (Lazy.ofSure (Sure.bunt : Sure CSet)) := by
  refine ⟨⟨⟨cra_lok_bunt, nb_none _⟩, trivial, trivial⟩, by simp [lregs_ofSure, Sure.bunt, flattenNeed],
    lkeys_ofSure _, by simp [llabs_ofSure]⟩

theorem lregs_reg (r : Nat) : lregs (Lazy.ofSure (lazyReg r : Sure CSet)) = [r] := by
  simp [lregs_ofSure, lazyReg, flattenNeed]

theorem lregs_bunt : lregs (Lazy.ofSure (Sure.bunt : Sure CSet)) = [] := by
  simp [lregs_ofSure, Sure.bunt, flattenNeed]

/-- A goal `[%next (lazy-from-reg r) ~ o]` below the counter meets `GInv`. -/
theorem ginv_reg {r : Nat} (o : Nat) {g : Gen (TreapMap mugF)} (hr : r < g.re) (hd : g.drop = false) :
    GInv g (CGoalL.next (Lazy.ofSure (lazyReg r)) (jmp0 o)) :=
  ⟨linv_reg hr, hd, jmpIn_jmp0 _ _⟩

theorem ginv_reg_j {r : Nat} {j : Jmp} {g : Gen (TreapMap mugF)} (hr : r < g.re) (hd : g.drop = false)
    (hj : JmpIn (· < g.re) j) : GInv g (CGoalL.next (Lazy.ofSure (lazyReg r)) j) :=
  ⟨linv_reg hr, hd, hj⟩

theorem ginv_bunt_j {j : Jmp} {g : Gen (TreapMap mugF)} (hd : g.drop = false) (hj : JmpIn (· < g.re) j) :
    GInv g (CGoalL.next (Lazy.ofSure Sure.bunt) j) :=
  ⟨linv_bunt _ _, hd, hj⟩

/-- `GInv` at larger counters. -/
theorem ginv_mono {g g' : Gen (TreapMap mugF)} {goal : CGoalL CSet} (h : GInv g goal) (hr : g.re ≤ g'.re)
    (hb : g.bo ≤ g'.bo) (hd : g'.drop = g.drop) : GInv g' goal := by
  have jm : ∀ j : Jmp, JmpIn (· < g.re) j → JmpIn (· < g'.re) j := fun j hj =>
    JmpIn.mono (fun x hx => Nat.lt_of_lt_of_le hx hr) hj
  cases goal with
  | next laz th => exact ⟨linv_mono h.1 hr hb, hd.trans h.2.1, jm _ h.2.2⟩
  | pick z o => exact ⟨hd.trans h.1, jm _ h.2.1, jm _ h.2.2⟩
  | done => exact hd.trans h

/-- **A run for a fresh register's goal, seen from an earlier state.** -/
theorem gres_fresh {g g1 g' : Gen (TreapMap mugF)} {goal : CGoalL CSet} {r : Nat} {j : Jmp} {nex : NextL CSet}
    (h : GRes g1 (CGoalL.next (Lazy.ofSure (lazyReg r)) j) g' nex) (hr : g.re ≤ r) (hl : g.re ≤ g1.re)
    (hb : g.bo ≤ g1.bo) : GRes g goal g' nex := by
  obtain ⟨l, b, i, s⟩ := h
  refine ⟨by omega, by omega, i, fun y hy => ?_⟩
  rcases s y hy with e | e
  · exact Or.inl (by omega)
  · simp only [gregs, lregs_reg, List.mem_singleton] at e; exact Or.inl (by omega)

/-- **Two runs in sequence**, the second for the goal the first returns. -/
theorem gres_comp {g g1 g' : Gen (TreapMap mugF)} {goal : CGoalL CSet} {n1 n2 : NextL CSet}
    (R1 : GRes g goal g1 n1) (R2 : GRes g1 n1.goal g' n2) : GRes g goal g' n2 := by
  obtain ⟨l1, b1, -, s1⟩ := R1
  obtain ⟨l2, b2, i2, s2⟩ := R2
  refine ⟨by omega, by omega, i2, fun y hy => ?_⟩
  rcases s2 y hy with e | e
  · exact Or.inl (by omega)
  · exact s1 y e

/-! ## The helpers -/

/-- **`+split` of a goal with the invariant**: two halves with `LInv` at the
counters it returns, apart, made of the goal's registers and fresh ones. -/
theorem splitL_inv {g g' : Gen (TreapMap mugF)} {laz h t : Lazy CSet} {th : Jmp} {o : Nat}
    (hi : GInv g (CGoalL.next laz th)) (e : splitL ⟨laz, th⟩ g = some ((h, t, o), g')) :
    g.re ≤ g'.re ∧ g.bo ≤ g'.bo ∧ g'.drop = false ∧ LInv g'.re g'.bo h ∧ LInv g'.re g'.bo t ∧
      (lregs h ++ lregs t).Nodup ∧ ∀ x ∈ lregs h ++ lregs t, x ∈ lregs laz ∨ g.re ≤ x := by
  obtain ⟨le, d, lh, lt⟩ := crInvL_split (crInvL_of_gInv hi) e
  obtain ⟨-, bo, -⟩ := (km_splitL _).keep g _ g' e
  have hb := lnb_regs hi.1.1
  obtain ⟨⟨-, hn, hk, hl⟩, -, -⟩ := hi
  simp only [splitL] at e
  obtain ⟨o1, g1, e1, e⟩ := bind_some e
  rw [emit_apply] at e1
  simp only [Option.some.injEq, Prod.mk.injEq] at e1
  obtain ⟨rfl, rfl⟩ := e1
  obtain ⟨⟨h', t'⟩, g2, e2, e⟩ := bind_some e
  simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e
  have H := split_halves laz g.bo (g.emitted ⟨[], [], Termin.hop th⟩) g2 h' t' hn (fun x hx => hb x hx) e2
  simp only [emitted_re] at H
  have nd := nodup_of_sub H.sub hn hb
  refine ⟨le, bo, d, ⟨lh, (List.nodup_append.1 nd).1, (H.keys hk).1, fun o ho => ?_⟩,
    ⟨lt, (List.nodup_append.1 nd).2.1, (H.keys hk).2, fun o ho => ?_⟩, nd, fun x hx => ?_⟩
  · have := hl o (H.labs o (Or.inl ho)); omega
  · have := hl o (H.labs o (Or.inr ho)); omega
  · rcases mem_of_sub H.sub hx with e | e
    · exact Or.inl e
    · exact Or.inr e.1

/-- **`+into` of a goal with the invariant**, for an axis not `0`. -/
theorem intoL_inv {g g' : Gen (TreapMap mugF)} {laz d r : Lazy CSet} {th : Jmp} {o axe : Nat} (ha : axe ≠ 0)
    (hi : GInv g (CGoalL.next laz th)) (e : intoL ⟨laz, th⟩ axe g = some ((d, r, o), g')) :
    g.re ≤ g'.re ∧ g.bo ≤ g'.bo ∧ g'.drop = false ∧ LInv g'.re g'.bo d ∧ LInv g'.re g'.bo r ∧
      (lregs d ++ lregs r).Nodup ∧ ∀ x ∈ lregs d ++ lregs r, x ∈ lregs laz ∨ g.re ≤ x := by
  obtain ⟨le, dr, ld, lr⟩ := crInvL_into ha (crInvL_of_gInv hi) e
  obtain ⟨-, bo, -⟩ := (km_intoL _ _).keep g _ g' e
  have hb := lnb_regs hi.1.1
  obtain ⟨⟨-, hn, hk, hl⟩, -, -⟩ := hi
  simp only [intoL] at e
  obtain ⟨o1, g1, e1, e⟩ := bind_some e
  rw [emit_apply] at e1
  simp only [Option.some.injEq, Prod.mk.injEq] at e1
  obtain ⟨rfl, rfl⟩ := e1
  obtain ⟨⟨d', r'⟩, g2, e2, e⟩ := bind_some e
  simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e
  have H := into_halves axe laz g.bo (g.emitted ⟨[], [], Termin.hop th⟩) g2 d' r' hn (fun x hx => hb x hx) e2
  simp only [emitted_re] at H
  have nd := nodup_of_sub H.sub hn hb
  refine ⟨le, bo, dr, ⟨ld, (List.nodup_append.1 nd).1, (H.keys hk).1, fun o ho => ?_⟩,
    ⟨lr, (List.nodup_append.1 nd).2.1, (H.keys hk).2, fun o ho => ?_⟩, nd, fun x hx => ?_⟩
  · have := hl o (H.labs o (Or.inl ho)); omega
  · have := hl o (H.labs o (Or.inr ho)); omega
  · rcases mem_of_sub H.sub hx with e | e
    · exact Or.inl e
    · exact Or.inr e.1

/-- **`+from` keeps `LInv` and the registers.** -/
theorem fromL_inv {kr kb axe : Nat} {laz laz' : Lazy CSet} (h : LInv kr kb laz) (e : Lazy.fromL axe laz = some laz') :
    LInv kr kb laz' ∧ lregs laz' = lregs laz := by
  obtain ⟨r, k, l⟩ := from_regs axe laz laz' e
  refine ⟨⟨crInvL_from h.1 e, r ▸ h.2.1, k h.2.2.1, fun o ho => h.2.2.2 o (l ▸ ho)⟩, r⟩

/-- **`+past` keeps `LInv`, the registers and the counter.** -/
theorem pastL_inv {cod : Bell → Option Bool} {nex nex' : NextL CSet} {nom : Nomm} {region : List Nat}
    {g g' : Gen (TreapMap mugF)} (hl : LInv g.re g.bo nex.laz) (hj : JmpIn (· < g.re) nex.th)
    (h : pastL cod nex nom region g = some (nex', g')) :
    g.re = g'.re ∧ g.bo ≤ g'.bo ∧ g'.drop = g.drop ∧ LInv g'.re g'.bo nex'.laz ∧ JmpIn (· < g'.re) nex'.th ∧
      lregs nex'.laz = lregs nex.laz := by
  obtain ⟨rg, re, bo, dr, kl, th⟩ := past_regs h
  obtain ⟨re', lnb⟩ := past_lnb 0 hl.1 h
  obtain ⟨k', l'⟩ := kl hl.2.2.1 hl.2.2.2
  refine ⟨re, bo, dr, ⟨lnb, rg ▸ hl.2.1, k', l'⟩, ?_, rg⟩
  rcases th with e | e
  · rw [e, ← re]; exact hj
  · rw [e]; exact jmpIn_jmp0 _ _

/-- **`+copy` of two needs with `LInv`, apart.** -/
theorem copyL_inv {first : NextL CSet} {second : Lazy CSet} {g g' : Gen (TreapMap mugF)} {nex : NextL CSet}
    (hf : LInv g.re g.bo first.laz) (hs : LInv g.re g.bo second) (ap : (lregs first.laz ++ lregs second).Nodup)
    (hd : g.drop = false) (h : copyL first second g = some (nex, g')) :
    g.re ≤ g'.re ∧ g.bo ≤ g'.bo ∧ GInv g' nex.goal ∧ ∀ x ∈ lregs nex.laz, x ∈ lregs first.laz ++ lregs second ∨ g.re ≤ x := by
  obtain ⟨le, lnb⟩ := crInvL_copy hf.1 hs.1 h
  obtain ⟨-, bo, dr⟩ := (km_copyL _ _).keep g _ g' h
  simp only [copyL] at h
  obtain ⟨o, g1, e1, h⟩ := bind_some h
  rw [emit_apply] at e1
  simp only [Option.some.injEq, Prod.mk.injEq] at e1
  obtain ⟨rfl, rfl⟩ := e1
  obtain ⟨laz, g2, e2, h⟩ := bind_some h
  simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hb : ∀ x ∈ lregs first.laz ++ lregs second, x < g.re := fun x hx => by
    rcases List.mem_append.1 hx with hx | hx
    · exact lnb_regs hf.1 x hx
    · exact lnb_regs hs.1 x hx
  have C := copy_regs first.laz g.bo second _ g2 laz hf.2.2.1 hs.2.2.1 ap (by simpa only [emitted_re] using hb) e2
  simp only [emitted_re, emitted_bo] at C
  refine ⟨le, bo, ⟨⟨lnb, nodup_of_sub C.sub ap hb, C.keys, fun o ho => ?_⟩, dr.trans hd, jmpIn_jmp0 _ _⟩,
    fun x hx => ?_⟩
  · rcases C.labs o ho with e | e
    · have := hf.2.2.2 o e; omega
    · have := hs.2.2.2 o e; omega
  · rcases mem_of_sub C.sub hx with e | e
    · exact Or.inl e
    · exact Or.inr e.1

/-! ## The tail of two runs -/

/-- **The goal of `p` in the tail meets `GInv`**, and what `+past` keeps. -/
theorem tail_pgoal {Gq Gp : Lazy CSet} {thq : Jmp} {g g2 g3 : Gen (TreapMap mugF)} {n2 n2' : NextL CSet}
    {cod : Bell → Option Bool} {p : Nomm} {region : List Nat}
    (hq : GInv g (CGoalL.next Gq thq)) (hp : LInv g.re g.bo Gp)
    (R2 : GRes g (CGoalL.next Gq thq) g2 n2) (e2 : pastL cod n2 p region g2 = some (n2', g3)) :
    GInv g3 (CGoalL.next Gp n2'.th) ∧ g.re ≤ g3.re ∧ g.bo ≤ g3.bo ∧ g2.re = g3.re ∧ LInv g3.re g3.bo n2'.laz ∧
      lregs n2'.laz = lregs n2.laz := by
  obtain ⟨l2, b2, ⟨i2, d2, j2⟩, s2⟩ := R2
  obtain ⟨r3, b3, d3, i3, j3, rg⟩ := pastL_inv i2 j2 e2
  exact ⟨⟨linv_mono hp (by omega) (by omega), d3.trans d2, j3⟩, by omega, by omega, r3, i3, rg⟩

/-- **The `+copy` of the tail meets `CopyH`.** -/
theorem tail_copyH {Gq Gp : Lazy CSet} {thq : Jmp} {g g2 g3 g4 : Gen (TreapMap mugF)} {n2 n2' n1 : NextL CSet}
    {cod : Bell → Option Bool} {p : Nomm} {region : List Nat}
    (hq : GInv g (CGoalL.next Gq thq)) (hp : LInv g.re g.bo Gp) (ap : (lregs Gp ++ lregs Gq).Nodup)
    (R2 : GRes g (CGoalL.next Gq thq) g2 n2) (e2 : pastL cod n2 p region g2 = some (n2', g3))
    (R1 : GRes g3 (CGoalL.next Gp n2'.th) g4 n1) :
    CopyH g4.re n1.laz n2'.laz ∧ (lregs n1.laz ++ lregs n2'.laz).Nodup := by
  obtain ⟨-, l3, b3, r3, i3, rg⟩ := tail_pgoal hq hp R2 e2
  obtain ⟨l4, b4, ⟨i4, -, -⟩, s4⟩ := R1
  obtain ⟨l2, -, -, s2⟩ := R2
  have hpb := lnb_regs hp.1
  have hqb := lnb_regs hq.1.1
  have apart : ∀ x ∈ lregs n1.laz, x ∉ lregs n2'.laz := by
    intro x h1 h2
    have x3 := lnb_regs i3.1 x h2
    rw [rg] at h2
    rcases s4 x h1 with e | e
    · omega
    · simp only [gregs] at e
      have := hpb x e
      rcases s2 x h2 with e' | e'
      · omega
      · simp only [gregs] at e'
        exact (List.nodup_append.1 ap).2.2 x e x e' rfl
  refine ⟨copyH_of_regs (lnb_regs i4.1) (fun x hx => Nat.lt_of_lt_of_le (lnb_regs i3.1 x hx) (by omega)) apart, ?_⟩
  rw [List.nodup_append]
  exact ⟨i4.2.1, i3.2.1, fun a ha b hb e => apart a ha (e ▸ hb)⟩

/-- **The result of the tail**: `GInv` at the new state, the registers of
`Gp`, `Gq` or fresh. -/
theorem tail_res {Gq Gp : Lazy CSet} {thq : Jmp} {g g2 g3 g4 g' : Gen (TreapMap mugF)} {n2 n2' n1 nex : NextL CSet}
    {cod : Bell → Option Bool} {p : Nomm} {region : List Nat}
    (hq : GInv g (CGoalL.next Gq thq)) (hp : LInv g.re g.bo Gp) (ap : (lregs Gp ++ lregs Gq).Nodup)
    (R2 : GRes g (CGoalL.next Gq thq) g2 n2) (e2 : pastL cod n2 p region g2 = some (n2', g3))
    (R1 : GRes g3 (CGoalL.next Gp n2'.th) g4 n1) (e4 : copyL n1 n2'.laz g4 = some (nex, g')) :
    g.re ≤ g'.re ∧ g.bo ≤ g'.bo ∧ GInv g' nex.goal ∧ ∀ x ∈ lregs nex.laz, x ∈ lregs Gp ++ lregs Gq ∨ g.re ≤ x := by
  obtain ⟨-, nd⟩ := tail_copyH hq hp ap R2 e2 R1
  obtain ⟨-, l3, b3, r3, i3, rg⟩ := tail_pgoal hq hp R2 e2
  have R1' := R1
  obtain ⟨l4, b4, ⟨i4, d4, -⟩, s4⟩ := R1
  obtain ⟨l2, -, -, s2⟩ := R2
  obtain ⟨l5, b5, i5, s5⟩ := copyL_inv i4 (linv_mono i3 l4 b4) nd d4 e4
  refine ⟨by omega, by omega, i5, fun x hx => ?_⟩
  rcases s5 x hx with e | e
  · rcases List.mem_append.1 e with e | e
    · rcases s4 x e with e' | e'
      · exact Or.inr (by omega)
      · simp only [gregs] at e'; exact Or.inl (List.mem_append_left _ e')
    · rw [rg] at e
      rcases s2 x e with e' | e'
      · exact Or.inr (by omega)
      · simp only [gregs] at e'; exact Or.inl (List.mem_append_right _ e')
  · exact Or.inr (by omega)

end Compiler
end Formalization
