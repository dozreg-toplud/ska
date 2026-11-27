import lemmas.Ska.CompGenConsH
import lemmas.Ska.CompGenConsI

/-!
# The cons of two leaves: the sure part (`sem`, `semB`, `nec`)

README Gaps 12.39, item 11.  The run's jump enters the copy's block at
`gS.bo`: the copy's ops at that label take the result's sure need to the
moved halves' sure needs, the hop goes to the split's block at `g0.bo`,
whose ops build the goal's sure need for `[x y]`, and the hop goes to the
goal's jump (`goalSemD_cons00`).  The code's blocks there are the run's,
unproxied (`AgreeG`'s first clause), and unproxying leaves the ops alone:
their registers are the goal's sure registers or fresh.

* `semCore_cons00`: `SemG`, `SemGW` and `nec` of the cons of two leaves.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

theorem cj_atL_nil {es : List (Nat × Lazy S)} {o : Nat} (h : o ∉ es.map Prod.fst) : atL es o = [] := by
  simp only [atL, filter_fst_nil es o h, List.map_nil]

/-- **The sure part of the cons of two leaves**: `SemG`, `SemGW` and `nec`. -/
theorem semCore_cons00 (lib : Lib) {N : Needs} {P : Noun → Prop} {f : Noun} {a b : Nat}
    (M : MinkEq lib P f (Nomm.cons (Nomm.n0 a) (Nomm.n0 b)))
    {L : Lazy S} {th : Jmp} {g0 g1 : Gen Map} {nex : NextL S} {hed tel hed' tel' : Lazy S} {gS : Gen Map}
    (CA : ConsAt L th a b g0 g1 nex hed tel hed' tel' gS) (G : GoalG (Map := Map) L th g0)
    (hnc : ∀ r, NMem L.sure.ned r → HoonMap.get g0.cond r = Option.none) (hcb : CondBelow g0) (hta : th.args = [])
    (CR : CopyRunAt (gS.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩) g1 ((gS.bo, hed') :: entries hed')
      ((gS.bo, tel') :: entries tel') ((gS.bo, nex.laz) :: entries nex.laz))
    (CP : CopyPreAt (gS.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩) ((gS.bo, hed') :: entries hed')
      ((gS.bo, tel') :: entries tel'))
    (W : Noun → Noun) :
    SemG lib N P f L th (pureWit (Nomm.cons (Nomm.n0 a) (Nomm.n0 b)) (fun _ => Need.none) W) g0 g1 nex ∧
    SemGW lib N P f L th (pureWit (Nomm.cons (Nomm.n0 a) (Nomm.n0 b)) (fun _ => Need.none) W) g0 g1 nex ∧
    ∀ s, P s → ¬ FitsS nex.laz.sure s → NecC lib f (CGoal.next L.sure th) s := by
  have reE : (g0.emitted ⟨[], [], Termin.hop th⟩).re = g0.re := rfl
  have reC : (gS.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩).re = gS.re := rfl
  have rS := CA.reS
  have rC := CA.reC
  have boS := CA.boS
  have bo1 := CA.bo
  -- the labels of the entries lie below `g0.bo`
  have labL : ∀ k ∈ (entries L).map Prod.fst, k < g0.bo := fun k hk => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
    exact (G.lab e he).2.1
  have nS : ∀ (l : Lazy S), (∀ e ∈ entries l, e.1 ∈ (entries L).map Prod.fst) →
      gS.bo ∉ (entries l).map Prod.fst := fun l hl hm => by
    obtain ⟨e, he, ee⟩ := List.mem_map.mp hm
    have := labL _ (hl e he); omega
  have n0 : ∀ (l : Lazy S), (∀ e ∈ entries l, e.1 ∈ (entries L).map Prod.fst) →
      g0.bo ∉ (entries l).map Prod.fst := fun l hl hm => by
    obtain ⟨e, he, ee⟩ := List.mem_map.mp hm
    have := labL _ (hl e he); omega
  -- the root lists
  have aM : atL ((gS.bo, nex.laz) :: entries nex.laz) gS.bo = [nex.laz.sure] := by
    rw [ci_atL_self, cj_atL_nil (nS _ CA.labN)]
  have aF : atL ((gS.bo, hed') :: entries hed') gS.bo = [hed'.sure] := by
    rw [ci_atL_self, cj_atL_nil (nS _ CA.labH')]
  have aT : atL ((gS.bo, tel') :: entries tel') gS.bo = [tel'.sure] := by
    rw [ci_atL_self, cj_atL_nil (nS _ CA.labT')]
  have aE : atL ((g0.bo, L) :: entries L) g0.bo = [L.sure] := by
    rw [ci_atL_self, cj_atL_nil (n0 L (fun e he => List.mem_map_of_mem he))]
  have aH : atL ((g0.bo, hed) :: entries hed) g0.bo = [hed.sure] := by
    rw [ci_atL_self, cj_atL_nil (n0 _ CA.labH)]
  have aTs : atL ((g0.bo, tel) :: entries tel) g0.bo = [tel.sure] := by
    rw [ci_atL_self, cj_atL_nil (n0 _ CA.labT)]
  -- the split at its root
  obtain ⟨hdj, hreg0⟩ := ci_es G
  obtain ⟨PS, PPS, -, SA⟩ := SplitOKL.runAt CA.sp.toL hdj hreg0
  obtain ⟨Sfit, Sreg1, Sreg2, Srun⟩ := SA g0.bo
  rw [aE, aH, aTs] at Sfit Srun
  rw [aE, aH] at Sreg1
  rw [aE, aTs] at Sreg2
  -- the copy at its root
  have CR0 := CR
  obtain ⟨PC, PPC, OC, AC⟩ := CR0
  have C1 := AC gS.bo (CP gS.bo).1 (CP gS.bo).2
  rw [aF, aT, aM] at C1
  obtain ⟨Cfit, Creg, -, CRg, Crun⟩ := C1
  -- the moves
  have hf : fromSure a hed.sure = some hed'.sure := fromL_sure CA.f2
  have hg : fromSure b tel.sure = some tel'.sure := fromL_sure CA.f1
  have hm1 := (fromSure_spec (Map := Map) hf).2.2.2
  have hm2 := (fromSure_spec (Map := Map) hg).2.2.2
  have rH : ∀ y, NMem hed.sure.ned y → NMem L.sure.ned y ∨ (g0.re ≤ y ∧ y < gS.re) := fun y hy => by
    rcases Sreg1 _ (List.mem_singleton_self _) y hy with ⟨L', hL', hm⟩ | h
    · rw [List.mem_singleton.mp hL'] at hm; exact Or.inl hm
    · exact Or.inr h
  have rT : ∀ y, NMem tel.sure.ned y → NMem L.sure.ned y ∨ (g0.re ≤ y ∧ y < gS.re) := fun y hy => by
    rcases Sreg2 _ (List.mem_singleton_self _) y hy with ⟨L', hL', hm⟩ | h
    · rw [List.mem_singleton.mp hL'] at hm; exact Or.inl hm
    · exact Or.inr h
  -- the registers of the ops are no keys of `cond`
  have good : ∀ x, (NMem L.sure.ned x ∨ (g0.re ≤ x ∧ x < g1.re)) →
      x < g1.re ∧ HoonMap.get g0.cond x = Option.none := by
    intro x hx
    rcases hx with hm | ⟨h1, h2⟩
    · have := G.sregs x hm; exact ⟨by omega, hnc x hm⟩
    · exact ⟨h2, condBelow_none hcb h1⟩
  have regsC : RegsIn (fun x => x < g1.re ∧ HoonMap.get g0.cond x = Option.none) (PC gS.bo) := by
    refine RegsIn.mono (fun x hx => good x ?_) CRg
    rcases hx with ⟨F, hF, hm⟩ | ⟨h1, h2⟩
    · rcases List.mem_append.mp hF with hF | hF
      · rw [List.mem_singleton.mp hF] at hm
        rcases rH x (hm1 x hm) with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h.1, by omega⟩
      · rw [List.mem_singleton.mp hF] at hm
        rcases rT x (hm2 x hm) with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h.1, by omega⟩
    · exact Or.inr ⟨by rw [reC] at h1; omega, h2⟩
  have P00 := CA.sp
  obtain ⟨P0, PP0, -, A0⟩ := P00
  have eP : PS g0.bo = P0 g0.bo := ch_pref_uniq PPS PP0 CA.eo
  have regsS : RegsIn (fun x => x < g1.re ∧ HoonMap.get g0.cond x = Option.none) (PS g0.bo) := by
    rw [eP]
    obtain ⟨ps, eps, pE, -, -, sP, -⟩ := A0 g0.bo
    rw [eps]
    refine ch_regsIn_flatten _ ps (fun p hp => ?_)
    have hp1 : p.1 ∈ atL ((g0.bo, L) :: entries L) g0.bo := pE.mem_iff.mp (List.mem_map_of_mem hp)
    rw [aE, List.mem_singleton] at hp1
    have ra := (sP p hp).ra (fun x => HoonMap.get g0.cond x = Option.none)
      (fun r hr => by rw [hp1] at hr; exact hnc r hr) (fun r hr => condBelow_none hcb hr)
    have rb := (sP p hp).rb (fun r hr => by rw [hp1] at hr; exact G.sregs r hr)
    intro q hq x hx
    exact ⟨by have := rb q hq x hx; omega, ra q hq x hx⟩
  -- the run's blocks at the two roots
  have pc0 : PC g0.bo = [] := OC g0.bo (fun hm => by
    simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons] at hm
    rcases hm with (h | hm) | (h | hm)
    · omega
    · exact n0 hed' CA.labH' hm
    · omega
    · exact n0 tel' CA.labT' hm)
  have b1S : HoonMap.get g1.blocks gS.bo = some ⟨[], PC gS.bo ++ [], Termin.hop (jmp0 g0.bo)⟩ := by
    rw [PPC.get, CA.eC]; simp [preBody]
  have b10 : HoonMap.get g1.blocks g0.bo = some ⟨[], PS g0.bo ++ [], Termin.hop th⟩ := by
    rw [PPC.get, ci_emitted_ne _ _ (by omega : g0.bo ≠ gS.bo), PPS.get, CA.eo, pc0]; simp [preBody]
  have blocks : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      ∀ (c : Straight Map), (∀ o, g0.bo ≤ o → o < g1.bo → o ∉ (entries nex.laz).map Prod.fst →
        HoonMap.get c.blocks o = (HoonMap.get g1.blocks o).map (unproxyBlob cf)) →
      HoonMap.get c.blocks gS.bo = some ⟨[], PC gS.bo, Termin.hop (jmp0 g0.bo)⟩ ∧
      HoonMap.get c.blocks g0.bo = some ⟨[], PS g0.bo, Termin.hop th⟩ := by
    intro cf hcf c hc
    have fixO : ∀ A : List Pole, RegsIn (fun x => x < g1.re ∧ HoonMap.get g0.cond x = Option.none) A →
        A.map (renPole (unproxy cf)) = A := fun A hA =>
      renOps_fix (P := fun x => x < g1.re ∧ HoonMap.get g0.cond x = Option.none)
        (fun x hx => unproxy_none (by rw [hcf x hx.1, CA.cond]; exact hx.2)) hA
    refine ⟨?_, ?_⟩
    · rw [hc gS.bo (by omega) (by omega) (nS _ CA.labN), b1S]
      simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, List.append_nil, fixO _ regsC, renFin,
        renJmp_nil _ (show (jmp0 g0.bo).args = [] from rfl)]
    · rw [hc g0.bo (Nat.le_refl _) (by omega) (n0 _ CA.labN), b10]
      simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, List.append_nil, fixO _ regsS, renFin,
        renJmp_nil _ hta]
  -- the registers kept
  have hK : ∀ (ned : Need), (∀ x, NMem ned x → g1.re ≤ x) → ∀ y,
      ((y < g0.re ∨ NMem ned y) ∧ ¬ NMem L.sure.ned y) →
      ¬ NMem L.sure.ned y ∧ ¬ NMem hed'.sure.ned y ∧ ¬ NMem tel'.sure.ned y := by
    intro ned hned y ⟨h1, h2⟩
    have hy : y < g0.re ∨ g1.re ≤ y := h1.imp id (hned y)
    refine ⟨h2, fun hm => ?_, fun hm => ?_⟩
    · rcases rH y (hm1 y hm) with h | h
      · exact h2 h
      · omega
    · rcases rT y (hm2 y hm) with h | h
      · exact h2 h
      · omega
  refine ⟨?_, ?_, ?_⟩
  · intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs' hm ag hned regs hh hn
    rw [(M s hs' gul tm r).mp ⟨n, hm⟩]
    refine goalSemCMD_of_goalSemD hI htr (fun p hp => ⟨hp, rfl, rfl⟩) ?_
    show GoalSemD lib O c gul st _ regs t nex.th L.sure th Need.none (W s)
      (pureEval (Nomm.cons (Nomm.n0 a) (Nomm.n0 b)) s)
    obtain ⟨hbc, hbs⟩ := blocks cf hcf c (ag st t).1
    rw [CA.eth]
    exact goalSemD_cons00 lib O c gul st hbc hbs hf hg Cfit Crun Sfit Srun (hK ned hned) hh
  · intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs' ag hned regs hh hn res hres
    refine ⟨_, (M s hs' gul tm _).mpr rfl, goalSemCMD_of_goalSemD hI htr (fun p hp => ⟨hp, rfl, rfl⟩) ?_⟩
    show GoalSemD lib O c gul st _ regs t nex.th L.sure th Need.none (W s)
      (pureEval (Nomm.cons (Nomm.n0 a) (Nomm.n0 b)) s)
    obtain ⟨hbc, hbs⟩ := blocks cf hcf c (ag st t).1
    rw [CA.eth]
    exact goalSemD_cons00 lib O c gul st hbc hbs hf hg Cfit Crun Sfit Srun (hK ned hned) hh
  · intro s hs hnf
    refine necC_of_pure M hs ?_
    cases hp : pureEval (Nomm.cons (Nomm.n0 a) (Nomm.n0 b)) s with
    | none => exact Or.inl rfl
    | some v =>
      refine Or.inr ⟨v, rfl, fun hfit => hnf ?_⟩
      obtain ⟨x, y, hx, hy, rfl⟩ := ch_pure_cons hp
      have hs2 := (Sfit x y).mp (fun L' hL' => by rw [List.mem_singleton.mp hL']; exact hfit)
      have fh : FitsS hed.sure x := hs2.1 _ (List.mem_singleton_self _)
      have ft : FitsS tel.sure y := hs2.2 _ (List.mem_singleton_self _)
      have fh' := (fromSure_spec (Map := Map) hf).2.2.1 s x hx fh
      have ft' := (fromSure_spec (Map := Map) hg).2.2.1 s y hy ft
      exact (Cfit s).mpr ⟨fun F hF => by rw [List.mem_singleton.mp hF]; exact fh',
        fun T hT => by rw [List.mem_singleton.mp hT]; exact ft'⟩ _ (List.mem_singleton_self _)

end Comp
end SkaModel
end Formalization
