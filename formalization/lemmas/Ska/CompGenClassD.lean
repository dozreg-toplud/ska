import lemmas.Ska.CompGenClassB
import lemmas.Ska.CompGenClassA

/-!
# The frame of the general cons

README Gaps 12.39, item 12.  The cons `[p q]` of two call-free parts under
`%next L th` (`ConsGAt`, `CompGenClassB.lean`): `+split` (state `gS`), `q`
under `%next tel (jmp0 g0.bo)` (state `g2`), `p` under `%next hed nq.th`
(state `g3`), `+copy` of the two results (state `g1`).  From the parts'
frames (`FrameG`, `GrowU`, no goal entry re-pointed) and the copy's per-label
spec (`CopyRunAt`, its preconditions `CopyPreAt`, `LabDisj` of the merged
result, taken as premises: `CompGenClassC.lean`), the whole's `FrameG` with
the witness `consWit Qp Qq`, `GrowU g0 g1`, and no goal entry re-pointed
(`frameG_consG`).  A register of the merged result traces through the copy to
one of the two results (`cd_np_sure`, `cd_nq_sure`, `cd_np_ent`,
`cd_nq_ent`), then through the part's frame to its goal (a half), then
through the split to `L` (`HalfOK`), or is fresh.  A goal entry's block gets
the copy's, `p`'s, `q`'s and the split's ops in front (`cd_front_part`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **A part that re-points no goal entry put ops in front of each goal
entry's block** (none when the label is not the part's goal's). -/
theorem cd_front_part {L' : Lazy S} {th' : Jmp} {Q : Wit} {g g' : Gen Map} {n : NextL S}
    (F : FrameG (Map := Map) L' th' Q g g' n) (N : ∀ a ∈ (entries L').map Prod.fst, ¬ RepointG g g' a)
    {a : Nat} (ha : a < g.bo) : ∃ F', FrontBlk g g' a F' := by
  by_cases hm : a ∈ (entries L').map Prod.fst
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
    rcases F.fronts e he with h | h
    · exact h
    · exact absurd h (N _ hm)
  · refine ⟨[], fun B fin hb => ?_⟩
    rw [F.keep a ha hm, hb]
    rfl

/-- **A block's prefix through `emitted` and `Pref`.** -/
theorem cd_front_pref {g g' : Gen Map} {b : Blob} {P : Nat → List Pole} (PP : Pref (g.emitted b) g' P) {a : Nat}
    (ha : a ≠ g.bo) : FrontBlk g g' a (P a) := fun B fin hb => by
  rw [PP.get, ci_emitted_ne _ _ ha, hb]
  rfl

section Frame
variable {L : Lazy S} {th : Jmp} {p q : Nomm} {env : CallEnv} {sup : Option Nomm} {region : List Nat}
  {g0 g1 : Gen Map} {nex : NextL S} {hed tel : Lazy S} {gS g2 g3 : Gen Map} {nq np : NextL S}
  {Qq Qp : Wit}

/-- `p`'s sure registers: `L`'s or fresh, no key of `cond`. -/
theorem cd_np_sure (CA : ConsGAt L th p q env sup region g0 g1 nex hed tel gS g2 g3 nq np)
    (G : PremG (Map := Map) L th g0) (Fq : FrameG (Map := Map) tel (jmp0 g0.bo) Qq gS g2 nq)
    (Fp : FrameG (Map := Map) hed nq.th Qp g2 g3 np) {y : Nat} (hy : NMem np.laz.sure.ned y) :
    (NMem L.sure.ned y ∨ (g0.re ≤ y ∧ y < g3.re)) ∧ HoonMap.get g3.cond y = Option.none := by
  have r0 := CA.reS
  have r1 := Fq.re
  have r2 := Fp.re
  refine ⟨?_, Fp.ncond y hy⟩
  rcases Fp.regs y hy with h | h
  · rcases (CA.halfH G).sr y h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.1, by omega⟩
  · exact Or.inr ⟨by omega, h.2⟩

/-- `q`'s sure registers: `L`'s or fresh below `g2.re`, no key of `cond` at `g3`. -/
theorem cd_nq_sure (CA : ConsGAt L th p q env sup region g0 g1 nex hed tel gS g2 g3 nq np)
    (G : PremG (Map := Map) L th g0) (Fq : FrameG (Map := Map) tel (jmp0 g0.bo) Qq gS g2 nq)
    (Fp : FrameG (Map := Map) hed nq.th Qp g2 g3 np) {y : Nat} (hy : NMem nq.laz.sure.ned y) :
    (NMem L.sure.ned y ∨ (g0.re ≤ y ∧ y < g2.re)) ∧ HoonMap.get g3.cond y = Option.none := by
  have r0 := CA.reS
  have r1 := Fq.re
  have o : NMem L.sure.ned y ∨ (g0.re ≤ y ∧ y < g2.re) := by
    rcases Fq.regs y hy with h | h
    · rcases (CA.halfT G).sr y h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h.1, by omega⟩
    · exact Or.inr ⟨by omega, h.2⟩
  have lt : y < g2.re := by
    rcases o with h | h
    · have := G.goal.sregs y h; omega
    · exact h.2
  refine ⟨o, ?_⟩
  rcases Fp.cfr.2 y with e | h
  · rw [e]; exact Fq.ncond y hy
  · omega

/-- The registers of an entry of `p`'s result: an entry of `L`'s, `L`'s sure
ones, or fresh; no key of `cond`. -/
theorem cd_np_ent (CA : ConsGAt L th p q env sup region g0 g1 nex hed tel gS g2 g3 nq np)
    (G : PremG (Map := Map) L th g0) (Fq : FrameG (Map := Map) tel (jmp0 g0.bo) Qq gS g2 nq)
    (Fp : FrameG (Map := Map) hed nq.th Qp g2 g3 np) {e : Nat × Lazy S} (he : e ∈ entries np.laz) {y : Nat}
    (hy : NMem e.2.sure.ned y) :
    ((∃ e0 ∈ entries L, NMem e0.2.sure.ned y) ∨ NMem L.sure.ned y ∨ (g0.re ≤ y ∧ y < g3.re)) ∧
      HoonMap.get g3.cond y = Option.none := by
  have r0 := CA.reS
  have r1 := Fq.re
  have r2 := Fp.re
  refine ⟨?_, Fp.econd e he y hy⟩
  rcases (Fp.eregs e he).2 y hy with ⟨e1, he1, h⟩ | h | h
  · rcases (CA.halfH G).er e1 he1 y h with ⟨e0, he0, -, h⟩ | h
    · exact Or.inl ⟨e0, he0, h⟩
    · exact Or.inr (Or.inr ⟨h.1, by omega⟩)
  · rcases (CA.halfH G).sr y h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h.1, by omega⟩)
  · exact Or.inr (Or.inr ⟨by omega, h.2⟩)

/-- The registers of an entry of `q`'s result. -/
theorem cd_nq_ent (CA : ConsGAt L th p q env sup region g0 g1 nex hed tel gS g2 g3 nq np)
    (G : PremG (Map := Map) L th g0) (Fq : FrameG (Map := Map) tel (jmp0 g0.bo) Qq gS g2 nq)
    (Fp : FrameG (Map := Map) hed nq.th Qp g2 g3 np) {e : Nat × Lazy S} (he : e ∈ entries nq.laz) {y : Nat}
    (hy : NMem e.2.sure.ned y) :
    ((∃ e0 ∈ entries L, NMem e0.2.sure.ned y) ∨ NMem L.sure.ned y ∨ (g0.re ≤ y ∧ y < g2.re)) ∧
      HoonMap.get g3.cond y = Option.none := by
  have r0 := CA.reS
  have r1 := Fq.re
  have o : (∃ e0 ∈ entries L, NMem e0.2.sure.ned y) ∨ NMem L.sure.ned y ∨ (g0.re ≤ y ∧ y < g2.re) := by
    rcases (Fq.eregs e he).2 y hy with ⟨e1, he1, h⟩ | h | h
    · rcases (CA.halfT G).er e1 he1 y h with ⟨e0, he0, -, h⟩ | h
      · exact Or.inl ⟨e0, he0, h⟩
      · exact Or.inr (Or.inr ⟨h.1, by omega⟩)
    · rcases (CA.halfT G).sr y h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨h.1, by omega⟩)
    · exact Or.inr (Or.inr ⟨by omega, h.2⟩)
  have lt : y < g2.re := by
    rcases o with ⟨e0, he0, h⟩ | h | h
    · have := (G.goal.eregs e0 he0).2 y h; omega
    · have := G.goal.sregs y h; omega
    · exact h.2
  refine ⟨o, ?_⟩
  rcases Fp.cfr.2 y with e' | h
  · rw [e']; exact Fq.econd e he y hy
  · omega

/-- **The frame of the general cons**: from the parts' frames, growth and
no re-pointing, and the copy's per-label spec at its inputs. -/
theorem frameG_consG (CA : ConsGAt L th p q env sup region g0 g1 nex hed tel gS g2 g3 nq np)
    (G : PremG (Map := Map) L th g0)
    (Fq : FrameG (Map := Map) tel (jmp0 g0.bo) Qq gS g2 nq) (Gq : GrowU gS g2)
    (Nq : ∀ a ∈ (entries tel).map Prod.fst, ¬ RepointG gS g2 a)
    (Fp : FrameG (Map := Map) hed nq.th Qp g2 g3 np) (Gp : GrowU g2 g3)
    (Np : ∀ a ∈ (entries hed).map Prod.fst, ¬ RepointG g2 g3 a)
    (lup : Raw.LabUniq np.laz) (luq : Raw.LabUniq nq.laz)
    (CR : CopyRunAt (g3.emitted ⟨[], [], Termin.hop np.th⟩) g1 ((g3.bo, np.laz) :: entries np.laz)
      ((g3.bo, nq.laz) :: entries nq.laz) ((g3.bo, nex.laz) :: entries nex.laz))
    (CP : CopyPreAt (g3.emitted ⟨[], [], Termin.hop np.th⟩) ((g3.bo, np.laz) :: entries np.laz)
      ((g3.bo, nq.laz) :: entries nq.laz))
    (LD : LabDisj nex.laz) :
    FrameG (Map := Map) L th (consWit Qp Qq) g0 g1 nex ∧ GrowU g0 g1 ∧
      ∀ a ∈ (entries L).map Prod.fst, ¬ RepointG g0 g1 a := by
  have d3 : g3.drop = false := Fp.drop.trans (Fq.drop.trans CA.dS)
  obtain ⟨Pc, PPC, OC, AC⟩ := CR
  have bo1 : g1.bo = g3.bo + 1 := PPC.bo
  have re1 : g3.re ≤ g1.re := PPC.re
  have cd1 : g1.cond = g3.cond := PPC.cond
  have dr1 : g1.drop = g3.drop := PPC.drop
  have boS := CA.boS
  have bq := Fq.bo
  have bp := Fp.bo
  have r0 := CA.reS
  have r1 := Fq.re
  have r2 := Fp.re
  have b0 := G.bo
  have G3 : GrowU g0 g3 := CA.growS.trans (Gq.trans Gp)
  have U3 : UpBelow g3 := G3.up G.up
  have GC : GrowU g3 g1 := (growU_emit (jumpsBelow_hop Fp.lo Fp.hi) U3).trans PPC.growU
  have G1 : GrowU g0 g1 := G3.trans GC
  have CB3 : CondBelow g3 := Fp.cfr.below (Fq.cfr.below (CA.condBelowS G))
  -- the labels
  have hedL : ∀ e ∈ entries hed, e.1 ∈ (entries L).map Prod.fst ∧ e.1 < g0.bo := fun e he => by
    obtain ⟨e0, he0, h0⟩ := List.mem_map.mp (CA.labH e he)
    exact ⟨CA.labH e he, by rw [← h0]; exact (G.goal.lab e0 he0).2.1⟩
  have telL : ∀ e ∈ entries tel, e.1 ∈ (entries L).map Prod.fst ∧ e.1 < g0.bo := fun e he => by
    obtain ⟨e0, he0, h0⟩ := List.mem_map.mp (CA.labT e he)
    exact ⟨CA.labT e he, by rw [← h0]; exact (G.goal.lab e0 he0).2.1⟩
  have Qnp : ∀ e ∈ entries np.laz, (e.1 ∈ (entries L).map Prod.fst ∨ (g0.bo ≤ e.1 ∧ e.1 < g3.bo)) ∧
      ∃ B j, HoonMap.get g3.blocks e.1 = some ⟨[], B, Termin.hop j⟩ := fun e he => by
    obtain ⟨h, blk⟩ := Fp.labs e he
    refine ⟨?_, blk⟩
    rcases h with h | h
    · obtain ⟨e1, he1, h1⟩ := List.mem_map.mp h
      rw [← h1]; exact Or.inl (hedL e1 he1).1
    · exact Or.inr ⟨by omega, h.2⟩
  have Qnq : ∀ e ∈ entries nq.laz, (e.1 ∈ (entries L).map Prod.fst ∨ (g0.bo ≤ e.1 ∧ e.1 < g3.bo)) ∧
      ∃ B j, HoonMap.get g3.blocks e.1 = some ⟨[], B, Termin.hop j⟩ := fun e he => by
    obtain ⟨h, B, j, blk⟩ := Fq.labs e he
    have lt2 : e.1 < g2.bo := by
      rcases h with h | h
      · obtain ⟨e1, he1, h1⟩ := List.mem_map.mp h
        rw [← h1]; have := (telL e1 he1).2; omega
      · exact h.2
    refine ⟨?_, let ⟨B', h'⟩ := cb_lab_grow Gp lt2 blk; ⟨B', j, h'⟩⟩
    rcases h with h | h
    · obtain ⟨e1, he1, h1⟩ := List.mem_map.mp h
      rw [← h1]; exact Or.inl (telL e1 he1).1
    · exact Or.inr ⟨by omega, by omega⟩
  have ltL : ∀ e ∈ entries L, e.1 < g0.bo := fun e he => (G.goal.lab e he).2.1
  have ltLm : ∀ o ∈ (entries L).map Prod.fst, o < g0.bo := fun o ho => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho; exact ltL e he
  have lpL : ∀ e ∈ entries np.laz, e.1 < g3.bo := fun e he => by
    rcases (Qnp e he).1 with h | h
    · have := ltLm _ h; omega
    · exact h.2
  have lqL : ∀ e ∈ entries nq.laz, e.1 < g3.bo := fun e he => by
    rcases (Qnq e he).1 with h | h
    · have := ltLm _ h; omega
    · exact h.2
  obtain ⟨-, QN⟩ := Raw.lab_copyL (Q := fun o => (o ∈ (entries L).map Prod.fst ∨ (g0.bo ≤ o ∧ o < g3.bo)) ∧
      ∃ B j, HoonMap.get g3.blocks o = some ⟨[], B, Termin.hop j⟩) CA.cp lup luq Qnp Qnq
  have lnL : ∀ e ∈ entries nex.laz, e.1 < g3.bo := fun e he => by
    rcases (QN e he).1 with h | h
    · have := ltLm _ h; omega
    · exact h.2
  -- the copy's trace at a label
  have TR : ∀ k, ∀ M ∈ atL ((g3.bo, nex.laz) :: entries nex.laz) k, Distinct M.ned ∧ ∀ y, NMem M.ned y →
      (∃ F ∈ atL ((g3.bo, np.laz) :: entries np.laz) k ++ atL ((g3.bo, nq.laz) :: entries nq.laz) k,
        NMem F.ned y) ∨ (g3.re ≤ y ∧ y < g1.re) := fun k M hM => by
    obtain ⟨-, regs, -⟩ := AC k (CP k).1 (CP k).2
    exact regs M hM
  have cfresh : ∀ y, g3.re ≤ y → HoonMap.get g1.cond y = Option.none := fun y hy => by
    rw [cd1]; exact condBelow_none CB3 hy
  -- the root
  have mroot : nex.laz.sure ∈ atL ((g3.bo, nex.laz) :: entries nex.laz) g3.bo := cb_mem_atL_self _ _ _
  have hroot : ∀ y, NMem nex.laz.sure.ned y →
      (NMem L.sure.ned y ∨ (g0.re ≤ y ∧ y < g1.re)) ∧ HoonMap.get g1.cond y = Option.none := fun y hy => by
    rcases (TR _ _ mroot).2 y hy with ⟨F, hF, hm⟩ | h
    · rcases List.mem_append.mp hF with hF | hF
      · rw [cb_atL_root lpL hF] at hm
        obtain ⟨o, c⟩ := cd_np_sure CA G Fq Fp hm
        refine ⟨o.imp id fun h => ⟨h.1, by omega⟩, by rw [cd1]; exact c⟩
      · rw [cb_atL_root lqL hF] at hm
        obtain ⟨o, c⟩ := cd_nq_sure CA G Fq Fp hm
        refine ⟨o.imp id fun h => ⟨h.1, by omega⟩, by rw [cd1]; exact c⟩
    · exact ⟨Or.inr ⟨by omega, h.2⟩, cfresh y h.1⟩
  -- the entries
  have hent : ∀ e ∈ entries nex.laz, Distinct e.2.sure.ned ∧ ∀ y, NMem e.2.sure.ned y →
      ((∃ e0 ∈ entries L, NMem e0.2.sure.ned y) ∨ NMem L.sure.ned y ∨ (g0.re ≤ y ∧ y < g1.re)) ∧
        HoonMap.get g1.cond y = Option.none := fun e he => by
    have lk := lnL e he
    have m : e.2.sure ∈ atL ((g3.bo, nex.laz) :: entries nex.laz) e.1 := cb_mem_atL_of he _
    refine ⟨(TR _ _ m).1, fun y hy => ?_⟩
    rcases (TR _ _ m).2 y hy with ⟨F, hF, hm⟩ | h
    · rcases List.mem_append.mp hF with hF | hF
      · obtain ⟨e1, he1, -, rfl⟩ := cb_atL_ent lk hF
        obtain ⟨o, c⟩ := cd_np_ent CA G Fq Fp he1 hm
        exact ⟨o.imp id (Or.imp id fun h => ⟨h.1, by omega⟩), by rw [cd1]; exact c⟩
      · obtain ⟨e1, he1, -, rfl⟩ := cb_atL_ent lk hF
        obtain ⟨o, c⟩ := cd_nq_ent CA G Fq Fp he1 hm
        exact ⟨o.imp id (Or.imp id fun h => ⟨h.1, by omega⟩), by rw [cd1]; exact c⟩
    · exact ⟨Or.inr (Or.inr ⟨by omega, h.2⟩), cfresh y h.1⟩
  -- the split's prefix
  obtain ⟨Ps, PPS, OS, -⟩ := CA.sp
  refine ⟨{ re := by omega, bo := by omega, drop := ?_, keep := fun o ho hno => ?_, grow := G1.toG,
            cfr := ⟨by omega, fun k => ?_⟩, lo := ?_, hi := ?_, ent := ?_, regs := fun r hr => (hroot r hr).1,
            dist := (TR _ _ mroot).1, eregs := fun e he => ⟨(hent e he).1, fun r hr => ((hent e he).2 r hr).1⟩,
            labs := fun e he => ?_, labDisj := LD, dreg := fun s v d w r hq hr => ?_,
            ncond := fun r hr => (hroot r hr).2, econd := fun e he r hr => ((hent e he).2 r hr).2,
            fronts := fun e he => Or.inl ?_ }, G1, ca_not_repoint G.goal G.up G1⟩
  · rw [dr1, d3, G.drop]
  · -- a block at no goal label is kept
    have hc : Pc o = [] := OC o (fun hm => by
      rw [List.map_append, List.mem_append, List.map_cons, List.mem_cons, List.map_cons, List.mem_cons] at hm
      rcases hm with (h | h) | (h | h)
      · omega
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
        rcases (Qnp e he).1 with h | h
        · exact hno h
        · omega
      · omega
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
        rcases (Qnq e he).1 with h | h
        · exact hno h
        · omega)
    have hs : Ps o = [] := OS o (fun hm => by
      rw [List.map_cons, List.mem_cons] at hm
      rcases hm with h | h
      · omega
      · exact hno h)
    have nh : o ∉ (entries hed).map Prod.fst := fun h => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp h; exact hno (hedL e he).1
    have nt : o ∉ (entries tel).map Prod.fst := fun h => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp h; exact hno (telL e he).1
    rw [PPC.get, hc, ci_emitted_ne _ _ (by omega : o ≠ g3.bo), Fp.keep o (by omega) nh, Fq.keep o (by omega) nt,
      PPS.get, hs, ci_emitted_ne _ _ (by omega : o ≠ g0.bo)]
    cases HoonMap.get g0.blocks o <;> simp
  · -- `cond` changes only at fresh registers
    rw [cd1]
    rcases Fp.cfr.2 k with e3 | h3
    · rw [e3]
      rcases Fq.cfr.2 k with e2 | h2
      · rw [e2, CA.condS]; exact Or.inl rfl
      · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  · rw [CA.eth]; show 1 ≤ g3.bo; omega
  · rw [CA.eth]; show g3.bo < g1.bo; omega
  · refine Or.inl ⟨preBody (Pc g3.bo) ⟨[], [], Termin.hop np.th⟩, ?_, rfl, by rw [CA.eth]; rfl⟩
    rw [CA.eth]
    show HoonMap.get g1.blocks g3.bo = _
    rw [PPC.get, emitted_get g3 _ d3]
    rfl
  · obtain ⟨hm, B, j, blk⟩ := QN e he
    have lk := lnL e he
    refine ⟨hm.imp id fun h => ⟨h.1, by omega⟩, let ⟨B', h'⟩ := cb_lab_grow GC lk blk; ⟨B', j, h'⟩⟩
  · obtain ⟨vp, vq, dp, wp, dq, wq, hp, hq', rfl, rfl, rfl⟩ := hq
    rcases hr with h | h
    · have := Fp.dreg s vp dp wp r hp h; exact ⟨by omega, by omega⟩
    · have := Fq.dreg s vq dq wq r hq' h; exact ⟨by omega, by omega⟩
  · -- the fronts: the copy's, `p`'s, `q`'s and the split's ops
    have la := ltL e he
    obtain ⟨F2, h2⟩ := cd_front_part Fq Nq (a := e.1) (by omega)
    obtain ⟨F3, h3⟩ := cd_front_part Fp Np (a := e.1) (by omega)
    exact ⟨_, ((cd_front_pref PPS (by omega : e.1 ≠ g0.bo)).trans h2).trans h3 |>.trans
      (cd_front_pref PPC (by omega : e.1 ≠ g3.bo))⟩

end Frame

end Comp
end SkaModel
end Formalization
