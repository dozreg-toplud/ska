import lemmas.Ska.RawInvCut

/-!
# Raw `+comp` output: a `%6` at the top

README Gaps 14.  **`optIn_finishLF6`**: the n-ary raw blocks of `[6 c a b]`
under `%done`, with `c`, `a`, `b` in the first fragment (the class `Frag6`
of track C that has a `%6`), meet `OptIn`.  `runL_six_done` of track C takes
the run apart: `b` and `a` for `%done`, the branch blocks `yes` and `nuh`,
the test `c` for `%pick` into them, the entry hop; the final pass's
`+coerce-lazy` then puts a `+sure-loop` at the entry and at each branch
block.  The liveness at the entry is cut at the branch blocks
(`live_cut`): a path that avoids them stays in the test's code
(`run_closed`), which mentions only registers it allocated (`run_above`),
so it reads no register of a branch's need; a path through a branch block
meets the `+sure-loop` there.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

theorem tagged_eq (g : Comp.Gen Map) (o : Nat) (r : List Nat) :
    (g.tagged o r).blocks = g.blocks ∧ (g.tagged o r).bo = g.bo ∧ (g.tagged o r).re = g.re ∧
      (g.tagged o r).drop = g.drop := by
  unfold Gen.tagged; split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem si_of_eq {g g' : Comp.Gen Map} (h : SI g) (e1 : g'.blocks = g.blocks) (e2 : g'.bo = g.bo) (e3 : g'.re = g.re)
    (e4 : g'.drop = g.drop) : SI g' := by
  obtain ⟨d, b1, l, j, r, n, c, t, p, a⟩ := h
  exact ⟨by rw [e4]; exact d, by rw [e2]; exact b1, by rw [e1, e2]; exact l, by rw [e1]; exact j,
    by rw [e1, e3]; exact r, by rw [e1]; exact n, by rw [e1]; exact c, by rw [e1]; exact t, by rw [e1]; exact p,
    by rw [e1]; exact a⟩

/-- **A `%6` at the top, under `%done`: the n-ary raw blocks meet `OptIn`.** -/
theorem optIn_finishLF6 [MapKeys Map] {c a b : Nomm} (hc : ∀ z o, Frag c (CGoal.pick z o : CGoal S))
    (ha : Frag a (CGoal.done : CGoal S)) (hb : Frag b (CGoal.done : CGoal S)) {ord : NeedOrd} {less : Cape}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) (Map := Map) (Nomm.n6 c a b) ord less bake = some c') : OptIn c'.blocks := by
  rw [finishLF_eq hbake (fun _ _ h1 => runL_cond_frag6 (Or.inr ⟨c, a, b, rfl, hc, ha, hb⟩) h1)] at h
  unfold finishL at h
  obtain ⟨⟨nex, g4⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨n1, n0, nc, g1, g2, g3, hrb, hra, a0, a1, hrc, hadd, rfl⟩ := runL_six_done hc ha hb h1
  simp only at h
  split at h
  · cases h
  obtain ⟨⟨nedF, g5⟩, h5, h⟩ := Option.bind_eq_some_iff.mp h
  rw [hbake] at h
  simp only [List.map_nil] at h
  obtain ⟨⟨u6, g6⟩, h6, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨u7, g7⟩, h7, h⟩ := Option.bind_eq_some_iff.mp h
  -- `b`
  obtain ⟨S1, L1, nb1, d1, nd1, ab1, lob1, hib1, D1, -⟩ := top_run hrb
  -- `a`
  have nf1 : ∀ r, Defd g1.blocks r → ¬ GMem (CGoal.done : CGoal S) r := fun r _ e => e
  obtain ⟨S2, L2⟩ := run_raw a CGoal.done g1 g2 n0 S1 trivial trivial trivial trivial nf1 hra
  obtain ⟨l2, bo2, nb2, d2, s2, dd2, ab2, loa2, hia2⟩ := sub_facts (goal := (CGoal.done : CGoal S)) S1 trivial
    trivial trivial trivial hra
  have nd2 := defd_next S1 nf1 s2 dd2
  have G2 := (run_down a CGoal.done g1 g2 n0 trivial S1.bo1 S1.drop hra).grow
  have D2 : Down g2.blocks := G2.down D1 S1.bo1
  -- the branch blocks
  have Eyes : EmitOK g2 ⟨[], [], Termin.hop n0.th⟩ := emitOK_hop ab2 hia2
  obtain ⟨Sy, -, ey, qy, by'⟩ := si_emit S2 Eyes (emit_apply _ g2)
  have Enuh : EmitOK (g2.emitted ⟨[], [], Termin.hop n0.th⟩) ⟨[], [], Termin.hop n1.th⟩ :=
    emitOK_hop ab1 (by rw [by']; have := G2.bo; omega)
  obtain ⟨Sn, -, en, qn, bn'⟩ := si_emit Sy Enuh (emit_apply _ _)
  generalize hgs : sixGen g2 n0 n1 = gs at hrc
  have gsE : gs.blocks = (((g2.emitted ⟨[], [], Termin.hop n0.th⟩).emitted ⟨[], [], Termin.hop n1.th⟩)).blocks ∧
      gs.bo = g2.bo + 2 ∧ gs.re = g2.re ∧ gs.drop = false := by
    rw [← hgs]; unfold sixGen
    obtain ⟨t1, t2, t3, t4⟩ := tagged_eq (((g2.emitted ⟨[], [], Termin.hop n0.th⟩).emitted
      ⟨[], [], Termin.hop n1.th⟩).tagged g2.bo []) (g2.bo + 1) []
    obtain ⟨u1, u2, u3, u4⟩ := tagged_eq ((g2.emitted ⟨[], [], Termin.hop n0.th⟩).emitted
      ⟨[], [], Termin.hop n1.th⟩) g2.bo []
    refine ⟨by rw [t1, u1], by rw [t2, u2, bn', by'], by rw [t3, u3, qn, qy], by rw [t4, u4]; exact Sn.drop⟩
  obtain ⟨gsb, gsbo, gsre, gsd⟩ := gsE
  have Sgs : SI gs := si_of_eq Sn gsb (by rw [gsbo, bn', by']) (by rw [gsre, qn, qy]) (by rw [gsd]; exact Sn.drop.symm)
  have gsget : ∀ k, HoonMap.get gs.blocks k = if k = g2.bo + 1 then some ⟨[], [], Termin.hop n1.th⟩ else
      if k = g2.bo then some ⟨[], [], Termin.hop n0.th⟩ else HoonMap.get g2.blocks k := fun k => by
    rw [gsb, en, by', ey]
    by_cases e1 : k = g2.bo + 1
    · subst e1; simp [get_put_self]
    · rw [get_put_ne e1, if_neg e1]
      by_cases e2 : k = g2.bo
      · subst e2; simp [get_put_self]
      · rw [get_put_ne e2, if_neg e2]
  have Ggs : Grow g2 gs := by
    refine ⟨by rw [gsbo]; omega, by rw [gsd]; exact S2.drop.symm, fun k b hk hb => ?_, fun k b' hb' => ?_⟩
    · exact ⟨b, by rw [gsget, if_neg (by omega), if_neg (by omega)]; exact hb, rfl, rfl⟩
    · rw [gsget] at hb'
      by_cases e1 : k = g2.bo + 1
      · rw [if_pos e1] at hb'; cases hb'
        exact Or.inr ⟨by omega, by rw [gsbo]; omega, fun j hj => by
          simp [finJumps] at hj; subst hj; exact ⟨lob1, by have := G2.bo; omega⟩⟩
      · rw [if_neg e1] at hb'
        by_cases e2 : k = g2.bo
        · rw [if_pos e2] at hb'; cases hb'
          exact Or.inr ⟨by omega, by rw [gsbo]; omega, fun j hj => by
            simp [finJumps] at hj; subst hj; exact ⟨loa2, by omega⟩⟩
        · rw [if_neg e2] at hb'; exact Or.inl ⟨b', hb', rfl, rfl⟩
  -- `c`
  have hgc : GoalIn gs.re (CGoal.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1)) : CGoal S) :=
    ⟨jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩
  have hjc : GJ gs.bo (CGoal.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1)) : CGoal S) := by
    simp only [GJ, jmp0]; have := S2.bo1; omega
  have nfc : ∀ r, Defd gs.blocks r → ¬ GMem (CGoal.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1)) : CGoal S) r :=
    fun r _ e => e
  obtain ⟨S3, L3⟩ := run_raw c _ gs g3 nc Sgs hgc trivial hjc ⟨rfl, rfl⟩ nfc hrc
  obtain ⟨l3, bo3, nb3, d3, s3, dd3, ab3, loc3, hic3⟩ := sub_facts Sgs hgc trivial hjc ⟨rfl, rfl⟩ hrc
  obtain ⟨CL3, ent3⟩ := run_closed c _ gs g3 nc gsd Sgs.bo1 hjc (fun k hk => Sgs.none hk) hrc
  have AB3 := run_above (P := (gs.re ≤ ·)) (goal := (CGoal.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1)) : CGoal S)) gsd
    ⟨fun x hx => by simp [jmp0] at hx, fun x hx => by simp [jmp0] at hx⟩ (ple_le (Nat.le_refl _)) hrc
  have G3 := (run_down c _ gs g3 nc hjc Sgs.bo1 gsd hrc).grow
  -- the entry hop
  have Eh : EmitOK g3 ⟨[], [], Termin.hop nc.th⟩ := emitOK_hop ab3 hic3
  obtain ⟨Se, -, ee, qe, boe⟩ := si_emit S3 Eh (emit_apply _ g3)
  obtain ⟨S4, b4', hb4', e4, q4, o4⟩ := si_addOps Se (opsOK_nil _) hadd
  rw [ee, get_put_self] at hb4'; cases hb4'
  have get4 : ∀ k, HoonMap.get g4.blocks k = HoonMap.get (HoonMap.put g3.blocks g3.bo ⟨[], [], Termin.hop nc.th⟩) k :=
    fun k => by
      rw [e4, ee]; by_cases e : k = g3.bo
      · subst e; simp [get_put_self, pre_nil]
      · rw [get_put_ne e, get_put_ne e]
  have D4 : Down g4.blocks := by
    have D3 : Down g3.blocks := G3.down (Ggs.down D2 S2.bo1) Sgs.bo1
    intro k b hk
    rw [get4] at hk
    rcases get_put_cases hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · exact ⟨S3.bo1, fun j hj => by simp [finJumps] at hj; subst hj; exact ⟨loc3, hic3⟩⟩
    · exact D3 k b hk
  -- `c` leaves the blocks below `gs.bo` as they were (track C's `RunOK.ext`)
  have Xc := (run_ok (S := S) (Map := Map) ⟨fun _ _ => none, fun _ => none, fun _ _ => none, fun _ => A 0⟩ c _ gs g3
    nc (hc _ _) trivial trivial hrc).ext
  have gy3 : HoonMap.get g3.blocks g2.bo = some ⟨[], [], Termin.hop n0.th⟩ := by
    rw [Xc.2.2.2 _ (by omega), gsget, if_neg (by omega), if_pos rfl]
  have gn3 : HoonMap.get g3.blocks (g2.bo + 1) = some ⟨[], [], Termin.hop n1.th⟩ := by
    rw [Xc.2.2.2 _ (by omega), gsget, if_pos rfl]
  have lo3 : g2.bo + 2 ≤ g3.bo := by have := G3.bo; omega
  -- definitions so far
  have ddgs : ∀ y, Defd gs.blocks y → Defd g2.blocks y := fun y d => by
    obtain ⟨k, bk, hk, hm⟩ := defd_iff.mp d
    rw [gsget] at hk
    split at hk
    · cases hk; simp [blockDefs, defsOf] at hm
    · split at hk
      · cases hk; simp [blockDefs, defsOf] at hm
      · exact defd_iff.mpr ⟨k, bk, hk, hm⟩
  have dd4 : ∀ y, Defd g4.blocks y → Defd g3.blocks y := fun y d => by
    obtain ⟨k, bk, hk, hm⟩ := defd_iff.mp d
    rw [get4] at hk
    rcases get_put_cases hk with ⟨-, rfl⟩ | ⟨-, hk⟩
    · simp [blockDefs, defsOf] at hm
    · exact defd_iff.mpr ⟨k, bk, hk, hm⟩
  have re34 : g4.re = g3.re := by rw [q4, qe]
  -- registers: `b`'s below `g1.re`, `a`'s below `g2.re`, `c`'s from `gs.re = g2.re`
  have nb0 : ∀ y, NMem n0.laz.ned y → g1.re ≤ y ∧ y < g2.re := fun y hy =>
    ⟨(s2 y hy).elim id (fun e => e.elim), nb2 y hy⟩
  have nbc : ∀ y, NMem nc.laz.ned y → g2.re ≤ y ∧ y < g3.re := fun y hy =>
    ⟨by rw [← gsre]; exact (s3 y hy).elim id (fun e => e.elim), nb3 y hy⟩
  -- the input registers
  obtain ⟨⟨k5, e5⟩, l5, dF, mF⟩ := needOrdAllocRegs_spec ord g4 g5 nedF h5
  have S5 : SI g5 := by rw [e5]; exact si_reg S4 (by rw [e5] at l5; exact l5)
  have b5 : g5.blocks = g4.blocks := by rw [e5]
  have bo5 : g5.bo = g4.bo := by rw [e5]
  have mF' : ∀ y, NMem nedF y → g3.re ≤ y ∧ y < g5.re := fun y hy => by have := mF y hy; omega
  -- `+coerce-lazy`: the entry, then the two branch blocks
  simp only [coerceLazyL, coerceForks, coerceBonds, coerceLazyL_ofSure, List.isEmpty_cons, Bool.false_and,
    Bool.false_eq_true, if_false] at h6
  obtain ⟨uA, gA, hA, h6⟩ := bind_some h6
  have hbE : HoonMap.get g5.blocks g3.bo = some ⟨[], [], Termin.hop nc.th⟩ := by
    rw [b5, get4, get_put_self]
  obtain ⟨SA, boA, lA, AE, getA, rfA, cvA, dfA⟩ := raw_coerce (laz := ⟨nc.laz.ned, HoonSet.uni nc.laz.lok HoonSet.empty⟩)
    S5 hbE (fun y hy => (mF' y hy).2) d3 (fun y hy => by have := (nbc y hy).2; omega)
    (fun y hy e => by have := mF' y hy; have := nbc y e; omega)
    (fun y hy d => by
      rw [b5] at d
      rcases dd3 y (dd4 y d) with d' | ⟨-, -, hn⟩
      · have := S2.defd_lt (ddgs y d'); have := nbc y hy; omega
      · exact hn hy) hA
  obtain ⟨uB, gB, hB, h6⟩ := bind_some h6
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hB
  obtain ⟨-, rfl⟩ := hB
  obtain ⟨uC, gC, hC, h6⟩ := bind_some h6
  have Xa := (run_ok (S := S) (Map := Map) ⟨fun _ _ => none, fun _ => none, fun _ _ => none, fun _ => A 0⟩ a _ g1 g2
    n0 ha trivial trivial hra).ext
  have ddA : ∀ y, Defd gA.blocks y → Defd g3.blocks y ∨ y ∈ defsOf AE := fun y d => by
    rcases (defd_of_ifget hbE getA).mp d with d | d
    · rw [b5] at d; exact Or.inl (dd4 y d)
    · exact Or.inr d
  have hbY : HoonMap.get gA.blocks g2.bo = some ⟨[], [], Termin.hop n0.th⟩ := by
    rw [getA, if_neg (by omega), b5, get4, get_put_ne (by omega), gy3]
  obtain ⟨SC, boC, lC, AY, getC, rfC, cvC, dfC⟩ := raw_coerce (laz := n0.laz) SA hbY
    (fun y hy => by have := (mF' y hy).2; omega) d2 (fun y hy => by have := (nb0 y hy).2; omega)
    (fun y hy e => by have := mF' y hy; have := nb0 y e; omega)
    (fun y hy d => by
      have hb0 := nb0 y hy
      rcases ddA y d with d | d
      · rcases dd3 y d with d' | ⟨-, e, -⟩
        · exact nd2 y (ddgs y d') hy
        · rcases e with e | e
          · rw [gsre] at e; omega
          · exact e.elim
      · rcases dfA y d with e | e
        · have := nbc y e; omega
        · omega) hC
  obtain ⟨uD, gD, hD, h6⟩ := bind_some h6
  have ddC : ∀ y, Defd gC.blocks y → Defd g3.blocks y ∨ y ∈ defsOf AE ∨ y ∈ defsOf AY := fun y d => by
    rcases (defd_of_ifget hbY getC).mp d with d | d
    · rcases ddA y d with d | d
      · exact Or.inl d
      · exact Or.inr (Or.inl d)
    · exact Or.inr (Or.inr d)
  have hbN : HoonMap.get gC.blocks (g2.bo + 1) = some ⟨[], [], Termin.hop n1.th⟩ := by
    rw [getC, if_neg (by omega), getA, if_neg (by omega), b5, get4, get_put_ne (by omega), gn3]
  obtain ⟨SD, boD, lD, AN, getD, rfD, cvD, dfD⟩ := raw_coerce (laz := n1.laz) SC hbN
    (fun y hy => by have := (mF' y hy).2; omega) d1 (fun y hy => by have := nb1 y hy; omega)
    (fun y hy e => by have := mF' y hy; have := nb1 y e; omega)
    (fun y hy d => by
      have hb1' := nb1 y hy
      rcases ddC y d with d | d | d
      · rcases dd3 y d with d' | ⟨-, e, -⟩
        · rcases dd2 y (ddgs y d') with d'' | ⟨-, e', -⟩
          · exact nd1 y d'' hy
          · rcases e' with e' | e'
            · omega
            · exact e'.elim
        · rcases e with e | e
          · rw [gsre] at e; have := l2; omega
          · exact e.elim
      · rcases dfA y d with e | e
        · have := nbc y e; have := l2; omega
        · omega
      · rcases dfC y d with e | e
        · have := nb0 y e; omega
        · omega) hD
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h6
  obtain ⟨-, rfl⟩ := h6
  simp only [jmp0] at h7 h
  obtain ⟨S7, b7', hb7', e7, -, -⟩ := si_addOps SD (opsOK_nil _) h7
  rw [getD, if_neg (by omega), getC, if_neg (by omega), getA, if_pos rfl] at hb7'
  cases hb7'
  -- the final blocks
  have get7 : ∀ k, HoonMap.get g7.blocks k = if k = g3.bo then some (pre AE ⟨[], [], Termin.hop nc.th⟩) else
      if k = g2.bo then some (pre AY ⟨[], [], Termin.hop n0.th⟩) else
      if k = g2.bo + 1 then some (pre AN ⟨[], [], Termin.hop n1.th⟩) else HoonMap.get g3.blocks k := fun k => by
    rw [e7]
    by_cases e1 : k = g3.bo
    · subst e1; simp [get_put_self, pre_nil]
    · rw [get_put_ne e1, if_neg e1, getD]
      by_cases e3 : k = g2.bo + 1
      · rw [if_pos e3, if_neg (by omega), if_pos e3]
      · rw [if_neg e3, getC]
        by_cases e2 : k = g2.bo
        · rw [if_pos e2, if_pos e2]
        · rw [if_neg e2, if_neg e2, if_neg e3, getA, if_neg e1, b5, get4, get_put_ne e1]
  have D7 : Down g7.blocks := by
    refine downRk_of_fins D4.rank fun k b' hk => ?_
    rw [get7] at hk
    by_cases e1 : k = g3.bo
    · rw [if_pos e1] at hk; cases hk
      exact ⟨⟨[], [], Termin.hop nc.th⟩, by rw [get4, e1, get_put_self], rfl⟩
    rw [if_neg e1] at hk
    by_cases e2 : k = g2.bo
    · rw [if_pos e2] at hk; cases hk
      exact ⟨⟨[], [], Termin.hop n0.th⟩, by rw [get4, get_put_ne e1, e2, gy3], rfl⟩
    rw [if_neg e2] at hk
    by_cases e3 : k = g2.bo + 1
    · rw [if_pos e3] at hk; cases hk
      exact ⟨⟨[], [], Termin.hop n1.th⟩, by rw [get4, get_put_ne e1, e3, gn3], rfl⟩
    rw [if_neg e3] at hk
    exact ⟨b', by rw [get4, get_put_ne e1]; exact hk, rfl⟩
  have below2 : ∀ x, x < g2.bo → HoonMap.get g7.blocks x = HoonMap.get g2.blocks x := fun x hx => by
    rw [get7, if_neg (by omega), if_neg (by omega), if_neg (by omega), Xc.2.2.2 x (by omega), gsget,
      if_neg (by omega), if_neg (by omega)]
  have below1 : ∀ x, x < g1.bo → HoonMap.get g7.blocks x = HoonMap.get g1.blocks x := fun x hx => by
    rw [below2 x (by have := G2.bo; omega), Xa.2.2.2 x hx]
  -- liveness through a branch block
  have liveY : ∀ y, Live g7.blocks g2.bo y → NMem nedF y := fun y hl => by
    obtain ⟨bb, hb, hr⟩ := live_iff.mp hl
    rw [get7, if_neg (by omega), if_pos rfl] at hb; cases hb
    rcases hr with ⟨-, hr⟩ | ⟨j, hj, hl', hn⟩
    · rcases hr with hr | ⟨-, hr⟩
      · simp only [pre, List.append_nil] at hr; exact rfC y hr
      · simp [pre, finRegs, jmpRegs_nil ab2] at hr
    · simp [pre, getJmps] at hj; subst hj
      have l2' := (live_frame (S2.below g2.bo) below2 hia2).mp hl'
      exact absurd (cvC y ((L2 y l2').elim id (fun e => e.elim)))
        (fun e => hn (mem_blockDefs_pre.mpr (Or.inr e)))
  have liveN : ∀ y, Live g7.blocks (g2.bo + 1) y → NMem nedF y := fun y hl => by
    obtain ⟨bb, hb, hr⟩ := live_iff.mp hl
    rw [get7, if_neg (by omega), if_neg (by omega), if_pos rfl] at hb; cases hb
    rcases hr with ⟨-, hr⟩ | ⟨j, hj, hl', hn⟩
    · rcases hr with hr | ⟨-, hr⟩
      · simp only [pre, List.append_nil] at hr; exact rfD y hr
      · simp [pre, finRegs, jmpRegs_nil ab1] at hr
    · simp [pre, getJmps] at hj; subst hj
      have l1' := (live_frame (S1.below g1.bo) below1 hib1).mp hl'
      exact absurd (cvD y (L1 y l1')) (fun e => hn (mem_blockDefs_pre.mpr (Or.inr e)))
  -- liveness at the entry
  have liveE : ∀ y, Live g7.blocks g3.bo y → NMem nedF y := fun y hl => by
    obtain ⟨bb, hb, hr⟩ := live_iff.mp hl
    rw [get7, if_pos rfl] at hb; cases hb
    rcases hr with ⟨-, hr⟩ | ⟨j, hj, hl', hn⟩
    · rcases hr with hr | ⟨-, hr⟩
      · simp only [pre, List.append_nil] at hr; exact rfA y hr
      · simp [pre, finRegs, jmpRegs_nil ab3] at hr
    simp [pre, getJmps] at hj; subst hj
    have hnA : y ∉ defsOf AE := fun e => hn (mem_blockDefs_pre.mpr (Or.inr e))
    rcases live_cut (fun z => z = g2.bo ∨ z = g2.bo + 1) hl' with hv | ⟨z, hz | hz, hz'⟩
    · exfalso
      have hv3 : LiveAv g3.blocks (fun z => z = g2.bo ∨ z = g2.bo + 1) nc.th.there y :=
        liveAv_frame (S3.below g3.bo) (fun x hx hz => by
          rw [get7, if_neg (by omega), if_neg (fun e => hz (Or.inl e)), if_neg (fun e => hz (Or.inr e))]) hv hic3
      have hent : gs.bo ≤ nc.th.there := by
        rcases ent3 with e | e
        · exact e
        · exact absurd (by simpa [GTgt, jmp0] using e) hv3.notZ
      have hup : gs.re ≤ y := liveAv_region (R := fun x => gs.bo ≤ x ∧ x < g3.bo) (P := (gs.re ≤ ·))
        (fun x bx hx hzx hbx => ⟨AB3 x bx hx.1 hx.2 hbx, fun j hj => by
          rcases CL3 x bx hx.1 hbx j hj with e | e
          · exact Or.inl ⟨e, Nat.lt_trans (S3.jd.below g3.bo x bx hx.2 hbx j hj) hx.2⟩
          · exact Or.inr (by simpa [GTgt, jmp0] using e)⟩) hv3 ⟨hent, hic3⟩
      rcases L3 y hv3.forget with e | e
      · exact hnA (cvA y e)
      · rcases e with e | e
        · simp only [jmp0] at e
          obtain ⟨bb, hb, hr⟩ := live_iff.mp e
          rw [gsget, if_neg (by omega), if_pos rfl] at hb; cases hb
          rcases hr with ⟨-, hr⟩ | ⟨j, hj, hl'', -⟩
          · rcases hr with hr | ⟨-, hr⟩
            · simp [OpsRF] at hr
            · simp [finRegs, jmpRegs_nil ab2] at hr
          · simp [getJmps] at hj; subst hj
            have l2' := (live_frame (S2.below g2.bo) (fun x hx => by
              rw [gsget, if_neg (by omega), if_neg (by omega)]) hia2).mp hl''
            have := nb0 y ((L2 y l2').elim id (fun e => e.elim)); omega
        · simp only [jmp0] at e
          obtain ⟨bb, hb, hr⟩ := live_iff.mp e
          rw [gsget, if_pos rfl] at hb; cases hb
          rcases hr with ⟨-, hr⟩ | ⟨j, hj, hl'', -⟩
          · rcases hr with hr | ⟨-, hr⟩
            · simp [OpsRF] at hr
            · simp [finRegs, jmpRegs_nil ab1] at hr
          · simp [getJmps] at hj; subst hj
            have hbl : ∀ x, x < g1.bo → HoonMap.get gs.blocks x = HoonMap.get g1.blocks x := fun x hx => by
              rw [gsget, if_neg (by have := G2.bo; omega), if_neg (by have := G2.bo; omega), Xa.2.2.2 x hx]
            have l1' := (live_frame (S1.below g1.bo) hbl hib1).mp hl''
            have := nb1 y (L1 y l1'); have := l2; omega
    · subst hz; exact liveY y hz'
    · subst hz; exact liveN y hz'
  -- the inputs are defined nowhere
  have inE : ∀ y, NMem nedF y → ¬ Defd g7.blocks y := fun y hy d => by
    have m := mF' y hy
    obtain ⟨k, bk, hk, hm⟩ := defd_iff.mp d
    rw [get7] at hk
    split at hk
    · cases hk
      rcases mem_blockDefs_pre.mp hm with e | e
      · simp [blockDefs, defsOf] at e
      · rcases dfA y e with e | e
        · have := nbc y e; omega
        · omega
    split at hk
    · cases hk
      rcases mem_blockDefs_pre.mp hm with e | e
      · simp [blockDefs, defsOf] at e
      · rcases dfC y e with e | e
        · have := nb0 y e; have := l3; omega
        · omega
    split at hk
    · cases hk
      rcases mem_blockDefs_pre.mp hm with e | e
      · simp [blockDefs, defsOf] at e
      · rcases dfD y e with e | e
        · have := nb1 y e; have := l2; have := l3; omega
        · omega
    · have := S3.defd_lt (defd_iff.mpr ⟨k, bk, hk, hm⟩); omega
  rw [h7] at h
  simp only [Option.bind_some] at h
  exact optIn_toStraight h D7 S7.nd S7.cr S7.tr (downPar_of_args S7.aa S7.jd) liveE inE

/-- **On track C's class `Frag6`** (the first fragment, or a `%6` at the top
over it): the n-ary raw blocks meet `OptIn`. -/
theorem optIn_finishLF_frag6 [MapKeys Map] {nm : Nomm} (hf : Frag6 (S := S) nm) {ord : NeedOrd} {less : Cape}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) (Map := Map) nm ord less bake = some c') : OptIn c'.blocks := by
  rcases hf with hf | ⟨c, a, b, rfl, hc, ha, hb⟩
  · exact optIn_finishLF hf hbake h
  · exact optIn_finishLF6 hc ha hb hbake h

/-- **The field `rawDInv` of `CompHypOf.lean`, n-ary, on `Frag6`.** -/
theorem rawDInv_finishLF_frag6 [MapKeys Map] {nm : Nomm} (hf : Frag6 (S := S) nm) {ord : NeedOrd} {less : Cape}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) (Map := Map) nm ord less bake = some c') : DInvS c'.blocks :=
  dInvR_dInvS (optIn_iff.mp (optIn_finishLF_frag6 hf hbake h))

/-- **`+optimize` keeps the n-ary code of `Frag6`.** -/
theorem optimize_keeps_finishLF_frag6 [MapKeys Map] (M : Type → Type → Type) [Ana.Treap M] {fuel sfuel : Nat}
    {nm : Nomm} (hf : Frag6 (S := S) nm) {ord : NeedOrd} {less : Cape}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' s' : Straight Map}
    (h : finishLF (S := S) (Map := Map) nm ord less bake = some c')
    (ho : optimizeF fuel ⟨aliasM (Ana.pickR M), trimTraceHints, switchChains sfuel⟩ c' = some s') : Opt.Keeps c' s' :=
  optimize_keeps_optIn M (optIn_finishLF_frag6 hf hbake h) ho

end Raw
end SkaModel
end Formalization
