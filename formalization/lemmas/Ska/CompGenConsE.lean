import lemmas.Ska.CompGenConsD
import lemmas.Ska.CompGenExQ
import lemmas.Ska.RawInvCLLabSplit

/-!
# The cons of two leaves under `%next`: the run taken apart, the frame's states

README Gaps 12.39, item 10.  `[[0 a] [0 b]]` (`a`, `b` at least `2`) under
`%next L th`: `+split` of the goal (`splitL_okD`), `+from` of the tail at `b`
and of the head at `a` (no state change), `+copy` of the two (`copyL`: a
fresh block hopping to the split's block, then `copyLazyL_okL`).

* `runLC_cons00_apart`: the run taken apart.
* `copyL_apart`: `copyL` as the emit and `copyLazyL`.
* `ConsSt`, `consSt_of_run`: the states of the run, the per-label specs of
  the split and of the copy, the `LabUniq` of the halves, `GrowU` from the
  start, and that no goal entry is re-pointed.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The cons of two leaves under `%next`, taken apart.** -/
theorem runLC_cons00_apart (env : CallEnv) (sup : Option Nomm) {a b : Nat} (ha : 2 ≤ a) (hb : 2 ≤ b)
    {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (h : runLC env sup (Nomm.cons (Nomm.n0 a) (Nomm.n0 b)) (CGoalL.next L th) region g0 = some (nex, g1)) :
    ∃ (hed tel hed' tel' : Lazy S) (o : Nat) (gS : Gen Map),
      splitL ⟨L, th⟩ g0 = some ((hed, tel, o), gS) ∧ fromL b tel = some tel' ∧ fromL a hed = some hed' ∧
      copyL ⟨hed', jmp0 o⟩ tel' gS = some (nex, g1) := by
  have e : (runLC env sup (Nomm.cons (Nomm.n0 a) (Nomm.n0 b)) (CGoalL.next L th) region : CM Map (NextL S)) = (do
        let (hed, tel, o) ← splitL ⟨L, th⟩
        let nexh ← pastL env.cod ⟨hed, jmp0 o⟩ (Nomm.n0 b) region
        let nex2 ← runLC env sup (Nomm.n0 b) (CGoalL.next tel nexh.th) region
        let nex2 ← pastL env.cod nex2 (Nomm.n0 a) region
        let nex1 ← runLC env sup (Nomm.n0 a) (CGoalL.next nexh.laz nex2.th) region
        copyL nex1 nex2.laz) := rfl
  rw [e] at h
  obtain ⟨⟨hed, tel, o⟩, gS, hs, h⟩ := bind_some h
  simp only at h
  obtain ⟨nexh, gb, hph, h⟩ := bind_some h
  rw [pastL_pure _ _ rfl, pure_apply] at hph
  simp only [Option.some.injEq, Prod.mk.injEq] at hph
  obtain ⟨rfl, rfl⟩ := hph
  obtain ⟨nexq, g2, h3, h⟩ := bind_some h
  rw [runLC_n0_next_from env sup hb] at h3
  obtain ⟨tel', hf1, e3⟩ := Option.map_eq_some_iff.mp h3
  simp only [Prod.mk.injEq] at e3
  obtain ⟨rfl, rfl⟩ := e3
  obtain ⟨nexq', g3, hp2, h⟩ := bind_some h
  rw [pastL_pure _ _ rfl, pure_apply] at hp2
  simp only [Option.some.injEq, Prod.mk.injEq] at hp2
  obtain ⟨rfl, rfl⟩ := hp2
  obtain ⟨nexp, g4, h4, hcp⟩ := bind_some h
  rw [runLC_n0_next_from env sup ha] at h4
  obtain ⟨hed', hf2, e4⟩ := Option.map_eq_some_iff.mp h4
  simp only [Prod.mk.injEq] at e4
  obtain ⟨rfl, rfl⟩ := e4
  exact ⟨hed, tel, hed', tel', o, gS, hs, hf1, hf2, hcp⟩

/-- **`+copy`, taken apart**: the fresh block hopping to the first's jump,
then `copyLazyL` at it. -/
theorem copyL_apart {first : NextL S} {second : Lazy S} {g g' : Gen Map} {nex : NextL S}
    (h : copyL first second g = some (nex, g')) :
    nex.th = jmp0 g.bo ∧ copyLazyL g.bo first.laz second (g.emitted ⟨[], [], Termin.hop first.th⟩) = some (nex.laz, g') := by
  unfold copyL at h
  obtain ⟨o, g0, h0, h⟩ := bind_some h
  rw [emit_apply] at h0
  simp only [Option.some.injEq, Prod.mk.injEq] at h0
  obtain ⟨rfl, rfl⟩ := h0
  obtain ⟨laz, g1, h1, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, h1⟩

/-- **The states of the cons of two leaves**: `gE` (the split's block
emitted), `gS` (after the split), `gC` (the copy's block emitted), `g1`. -/
structure ConsSt (L : Lazy S) (th : Jmp) (a b : Nat) (g0 g1 : Gen Map) (nex : NextL S) : Prop where
  ex : ∃ (hed tel hed' tel' : Lazy S) (gS : Gen Map),
    fromL b tel = some tel' ∧ fromL a hed = some hed' ∧
    HoonMap.get (g0.emitted ⟨[], [], Termin.hop th⟩).blocks g0.bo = some ⟨[], [], Termin.hop th⟩ ∧
    SplitOKD (g0.emitted ⟨[], [], Termin.hop th⟩) gS ((g0.bo, L) :: entries L) ((g0.bo, hed) :: entries hed)
      ((g0.bo, tel) :: entries tel) ∧
    Raw.LabUniq hed' ∧ Raw.LabUniq tel' ∧
    nex.th = jmp0 gS.bo ∧ gS.bo = g0.bo + 1 ∧
    HoonMap.get (gS.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩).blocks gS.bo =
      some ⟨[], [], Termin.hop (jmp0 g0.bo)⟩ ∧ gS.drop = false ∧
    CopyOKL (gS.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩) g1 ((gS.bo, hed') :: entries hed')
      ((gS.bo, tel') :: entries tel') ((gS.bo, nex.laz) :: entries nex.laz)
  grow : GrowU g0 g1
  norep : ∀ k ∈ (entries L).map Prod.fst, ¬ RepointG g0 g1 k
  bo : g1.bo = g0.bo + 2
  re : g0.re ≤ g1.re
  drop : g1.drop = g0.drop
  cond : g1.cond = g0.cond

theorem consSt_of_run (env : CallEnv) (sup : Option Nomm) {a b : Nat} (ha : 2 ≤ a) (hb : 2 ≤ b)
    {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (G : GoalG (Map := Map) L th g0) (lu : Raw.LabUniq L) (d0 : g0.drop = false) (hu : UpBelow g0)
    (h : runLC env sup (Nomm.cons (Nomm.n0 a) (Nomm.n0 b)) (CGoalL.next L th) region g0 = some (nex, g1)) :
    ConsSt L th a b g0 g1 nex := by
  obtain ⟨hed, tel, hed', tel', o, gS, hs, hf1, hf2, hcp⟩ := runLC_cons00_apart env sup ha hb h
  obtain ⟨rfl, eo, WS⟩ := splitL_okD hs d0 (fun e he => by
    obtain ⟨_, hlt, B, th', hb'⟩ := G.lab e he
    exact ⟨hlt, B, _, hb'⟩)
  obtain ⟨eth, hc⟩ := copyL_apart hcp
  obtain ⟨luh, lut, -, -⟩ := Raw.lab_splitL (Q := fun _ => True) hs lu (fun _ _ => trivial)
  have luh' := Raw.lu_fromL a hed hed' hf2 luh
  have lut' := Raw.lu_fromL b tel tel' hf1 lut
  have dE : (g0.emitted ⟨[], [], Termin.hop th⟩).drop = false := d0
  have WS0 := WS
  obtain ⟨PS, PPS, -, -⟩ := WS0
  have dS : gS.drop = false := PPS.drop.trans dE
  have WC := copyLazyL_okL gS.bo hed' tel' _ g1 nex.laz hc dS luh' lut'
  have WC0 := WC
  obtain ⟨PC, PPC, -, -⟩ := WC0
  have boS : gS.bo = g0.bo + 1 := PPS.bo
  have eC := emitted_get gS ⟨[], [], Termin.hop (jmp0 g0.bo)⟩ dS
  -- growth
  have GE : GrowU g0 (g0.emitted ⟨[], [], Termin.hop th⟩) := growU_emit (jumpsBelow_hop G.jmp.1 G.jmp.2) hu
  have uE := GE.up hu
  have GS := PPS.growU
  have uS := GS.up uE
  have GC : GrowU gS (gS.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩) :=
    growU_emit (jumpsBelow_hop (show 1 ≤ (jmp0 g0.bo).there from G.bo) (by simp only [jmp0]; omega)) uS
  have G1 : GrowU g0 g1 := GE.trans (GS.trans (GC.trans PPC.growU))
  refine ⟨⟨hed, tel, hed', tel', gS, hf1, hf2, eo, WS, luh', lut', eth, boS, eC, dS, WC⟩,
    G1, fun k hk hr => ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
    obtain ⟨B, fin, F, o1, o2, F2, hb0, hb1, l1, -, -, -, -⟩ := hr
    obtain ⟨_, hlt, B', th', hb'⟩ := G.lab e he
    obtain ⟨b', hb1', -, hfin⟩ := G1.keep e.1 _ hlt hb0
    rw [hb1] at hb1'
    simp only [Option.some.injEq] at hb1'
    subst hb1'
    rw [hb0] at hb'
    simp only [Option.some.injEq, Blob.mk.injEq] at hb'
    obtain ⟨-, -, rfl⟩ := hb'
    simp only [Termin.hop.injEq] at hfin
    have := hu e.1 o1 ⟨_, ⟨[], o1⟩, hb0, by rw [← hfin], rfl, by omega⟩
    omega
  · rw [PPC.bo, emitted_bo, boS]
  · have := PPS.re; have := PPC.re; simp only [emitted_re] at *; omega
  · rw [PPC.drop]; exact dS.trans d0.symm
  · rw [PPC.cond]; exact PPS.cond

end Comp
end SkaModel
end Formalization
