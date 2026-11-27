import lemmas.Ska.CompPairLSXCore

/-!
# A pair of runs under a flat lazy goal, parts of any flag: the `sem` clauses

README Gaps 12.32.  `pairLS_sem`, `pairLS_semB` (`CompPairLSSem.lean`) with
the section of `CompPairLSXFronts.lean` and the witness `pairWitX C HW`: at
the jump to the block `o` the halves hold the parts' products (`hHh`), and
the block `o` keeps them (`hA`, `hAB` with `Keep … ∨ NMem HW`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

section

variable {lib : Lib} {N : Needs} {P : Noun → Prop} {f fh ft : Noun} {L : Lazy S} {th : Jmp}
    {g0 g' g'' gb g1 g2 g3' g3 : Gen Map} {hed tel Lh : Lazy S} {o : Nat} {jt : Jmp} {Qh Qt : Wit}
    {nexq nexp : NextL S} {n : Next S} {x xp xq : Bool} {HW : Need} {r : List (Nat × Lazy S)} {PB : Nat → List Pole}
    {Fin : Noun → Nat → Trace → Noun → Noun → Tone → Prop} {FinB : Noun → Trace → Noun → Noun → Tone → Prop}
    (Mf : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {r : Tone}, P s → minkF lib gul n tm s f = some r →
      ∃ n', n' < n ∧ ∃ rh, minkF lib gul n' tm s fh = some rh ∧
        (((∀ q, rh ≠ Tone.zero q) ∧ r = rh) ∨ ∃ x, rh = Tone.zero x ∧ ∃ rt, minkF lib gul n' tm s ft = some rt ∧
          (((∀ q, rt ≠ Tone.zero q) ∧ r = rt) ∨ ∃ y, rt = Tone.zero y ∧ Fin gul n' tm x y r)))
    (Mb : ∀ {s gul : Noun} {tm : Trace} {rh : Tone}, P s → Mink lib gul tm s fh rh →
      ((∀ q, rh ≠ Tone.zero q) → Mink lib gul tm s f rh) ∧
      ∀ x rt, rh = Tone.zero x → Mink lib gul tm s ft rt →
        ((∀ q, rt ≠ Tone.zero q) → Mink lib gul tm s f rt) ∧
        ∀ y r, rt = Tone.zero y → FinB gul tm x y r → Mink lib gul tm s f r)
    (hFin : ∀ gul n' tm x y r, Fin gul n' tm x y r → r = Tone.zero (C x y))
    (hFinB : ∀ gul tm x y r, FinB gul tm x y r → r = Tone.zero (C x y))
    -- the goal
    (hLf : Flat L) (hLn : (L.bond.map Prod.fst).Nodup)
    (hLc : ∀ x, NMem L.sure.ned x → HoonMap.get g0.cond x = Option.none)
    (hLb : ∀ e ∈ L.bond, e.1 < g0.bo ∧ (∃ B th', HoonMap.get g0.blocks e.1 = some ⟨[], B, Termin.hop th'⟩) ∧
      Distinct e.2.sure.ned ∧ ∀ x, NMem e.2.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none)
    -- the sure part (`pairLC_ok`)
    (hg : GoalOK g0 (CGoal.next L.sure th)) (hpre : Ext g0 g') (hgr : GrowU g0 g') (hcnd : g'.cond = g0.cond)
    (hcb : CondBelow g0)
    (hlp : ∀ r, NMem hed.sure.ned r → NMem L.sure.ned r ∨ (g0.re ≤ r ∧ r < g'.re))
    (hlq : ∀ r, NMem tel.sure.ned r → NMem L.sure.ned r ∨ (g0.re ≤ r ∧ r < g'.re))
    (hpq : ∀ r, NMem hed.sure.ned r → ¬ NMem tel.sure.ned r)
    -- the bonds' splits
    (hB : Pref g' g'' PB) (hBo : ∀ k, k ∉ L.bond.map Prod.fst → PB k = [])
    (hhf : Flat hed) (htf : Flat tel)
    (hsp : ∀ e ∈ L.bond, ∃ sh st, SplitAt (Map := Map) e hed tel (PB e.1) g'.re g''.re sh st)
    (hhl : ∀ e ∈ hed.bond, e.1 ∈ L.bond.map Prod.fst) (htl : ∀ e ∈ tel.bond, e.1 ∈ L.bond.map Prod.fst)
    (hhn : (hed.bond.map Prod.fst).Nodup) (htn : (tel.bond.map Prod.fst).Nodup)
    -- the head's park
    (hgb : Ext g'' gb) (hgbU : GrowU g'' gb) (hgbc : gb.cond = g''.cond) (hgbre : gb.re = g''.re)
    (hjt : (jt = jmp0 o ∧ Lh = hed ∧ ((∀ x, FitsS hed.sure x) ∨ TotalC lib P ft)) ∨
      (jt = jmp0 g''.bo ∧ Lh = mk Sure.bunt [] ((g''.bo, ofSure hed.sure) :: hed.bond) ∧ g''.bo < gb.bo ∧
        HoonMap.get gb.blocks g''.bo = some ⟨[], [], Termin.hop (jmp0 o)⟩))
    (hhd : (∀ s, FitsS nexq.laz.sure s) ∨ TotalC lib P fh)
    -- the parts
    (hq : RunOKLS (Map := Map) lib N P ft tel jt Qt xq gb g1 nexq)
    (hp : RunOKLS (Map := Map) lib N P fh Lh nexq.th Qh xp g1 g2 nexp)
    (hqf : Flat nexq.laz) (hpf : Flat nexp.laz)
    (hqc : ∀ e ∈ entries nexq.laz, Clean e.2.sure.ned) (hpc : ∀ e ∈ entries nexp.laz, Clean e.2.sure.ned)
    (cq : Clean nexq.laz.sure.ned) (cp : Clean nexp.laz.sure.ned)
    -- the copy
    (hc : copy ⟨nexp.laz.sure, nexp.th⟩ nexq.laz.sure g2 = some (n, g3'))
    (hM : MergeBs (index (Map := Map) (fun e : Nat × Lazy S => e.1) nexq.laz.bond) nexp.laz.bond r g3' g3)
    (hu : UpBelow g0) (d0 : g0.drop = false)
    (hfix : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g0.cond k) →
      ∀ k, g0.bo ≤ k → k < g'.bo → (HoonMap.get g'.blocks k).map (unproxyBlob cf) = HoonMap.get g'.blocks k)
    (hnotF : ∀ gul n' tm x y r, (¬ FitsS hed.sure x ∨ ¬ FitsS tel.sure y) → Fin gul n' tm x y r →
      BadC (CGoal.next L.sure th) tm r)
    (hnotB : ∀ gul tm x y, (¬ FitsS hed.sure x ∨ ¬ FitsS tel.sure y) → ∃ r, FinB gul tm x y r ∧
      BadC (CGoal.next L.sure th) tm r)
    (hA : ∀ (c : Straight Map), Agree c g0 g' → ∀ (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ)
      (n : Nat) (gul : Noun), OracleSteps Inv ν O → OracleFwd lib Inv ν O n →
      ∀ (st : σ) (regs : Map (Option Noun)) (t tm : Trace) (x y : Noun) (n' : Nat) (r : Tone), n' < n → Inv st →
        Forall2 (FrameRel lib (ν st)) t tm → FitsS hed.sure x → FitsS tel.sure y → HoldsN hed.sure.ned regs x →
        HoldsN tel.sure.ned regs y → Fin gul n' tm x y r →
        GoalSemCM lib O c gul Inv ν (fun z => Keep g0 g' (CGoal.next L.sure th) z ∨ NMem HW z) st regs t tm (jmp0 o)
          (CGoal.next L.sure th) r)
    (hAB : ∀ (c : Straight Map), Agree c g0 g' → ∀ (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ)
      (gul : Noun), OracleSteps Inv ν O → OracleBwd lib Inv ν O →
      ∀ (st : σ) (regs : Map (Option Noun)) (t tm : Trace) (x y : Noun), Inv st →
        Forall2 (FrameRel lib (ν st)) t tm → FitsS hed.sure x → FitsS tel.sure y → HoldsN hed.sure.ned regs x →
        HoldsN tel.sure.ned regs y → ∀ res, goJ lib O c gul st regs t (jmp0 o) = some res →
        ∃ r, FinB gul tm x y r ∧
          GoalSemCM lib O c gul Inv ν (fun z => Keep g0 g' (CGoal.next L.sure th) z ∨ NMem HW z) st regs t tm (jmp0 o)
          (CGoal.next L.sure th) r)

    -- the halves in the witness and the parts' goal registers (README Gaps 12.32)
    (hHr : ∀ z, NMem HW z → g0.re ≤ z ∧ z < g'.re)
    (hHh : ∀ (R : Map (Option Noun)) (a b : Noun), HoldsN hed.sure.ned R a → HoldsN tel.sure.ned R b →
      HoldsN HW R (C a b))
    (hEH : ∀ (R : Map (Option Noun)) (a b : Noun), HoldsN (gsE x L) R (C a b) → HoldsN HW R (C a b) →
      HoldsN (gsE xp Lh) R a ∧ HoldsN (gsE xq tel) R b)
    (hG : ∀ e ∈ L.bond, ∀ z, NMem L.sure.ned z → ¬ NMem e.2.sure.ned z)
    (hPH : ∀ e ∈ L.bond, ∀ e1 ∈ nexp.laz.bond ++ nexq.laz.bond, e1.1 = e.1 → ∀ z,
      (NMem HW z ∨ NMem (gsE xp Lh) z ∨ NMem (gsE xq tel) z ∨ NMem (gsE x L) z) → ¬ NMem e1.2.sure.ned z)
include Mf Mb hFin hFinB hLf hLn hLc hLb hg hpre hgr hcnd hcb hlp hlq hpq hB hBo hhf htf hsp hhl htl hhn htn hgb hgbU hgbc hgbre hjt hhd hq hp hqf hpf hqc hpc cq cp hc hM hu d0 hfix hnotF hnotB hA hAB hHr hHh hEH hG hPH

/-- The forward `sem` clause of `pairLS_ok`. -/
theorem pairLSX_sem {idx : Map (Nat × Lazy S)}
    (hidx : index (Map := Map) (fun e : Nat × Lazy S => e.1) nexq.laz.bond = idx)
    (P0 : CopyPre nexp.laz.sure.ned nexq.laz.sure.ned g2.re)
    (d2 : g2.drop = false)
    (d3' : g3'.drop = false)
    (pnd : (nexp.laz.bond.map Prod.fst).Nodup)
    (eP : entries nexp.laz = nexp.laz.bond)
    (lp' : ∀ e ∈ nexp.laz.bond, (e.1 ∈ L.bond.map Prod.fst ∨ (e.1 = g''.bo ∧ g''.bo < gb.bo) ∨
      (g1.bo ≤ e.1 ∧ e.1 < g2.bo)))
    (labL : ∀ k, k ∈ L.bond.map Prod.fst → k < g0.bo)
    (gm : ∀ r, NMem L.sure.ned r → r < g0.re)
    (hcase : ∀ x, ¬ FitsS Lh.sure x → ¬ FitsS hed.sure x ∧ TotalC lib P ft)
    (core : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g3.re → HoonMap.get cf k = HoonMap.get g3.cond k) →
      ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ) (t : Trace) (s0 s : Noun),
      (∀ st' : σ, AgreeLB lib O c gul st' t cf ned g0 g3 (pairRes n r nexq.laz.bond nexp.laz.bond).laz s0 s) →
      (∀ x, NMem ned x → g3.re ≤ x) →
      ∀ regs, HoldsS n.laz regs s → HoldsN ned regs s0 →
      ∃ R1, Agree c g0 g' ∧ (∀ st' : σ, AgreeLB lib O c gul st' t cf ned g1 g2 nexp.laz s0 s) ∧
        (∀ x, NMem ned x → g2.re ≤ x) ∧
        HoldsS nexp.laz.sure R1 s ∧ HoldsN ned R1 s0 ∧
        goJ lib O c gul st regs t n.th = goJ lib O c gul st R1 t nexp.th ∧
        (∀ z, ((z < g0.re ∨ NMem ned z) ∧ ¬ NMem L.sure.ned z) → SkaModel.read z R1 = SkaModel.read z regs) ∧
        ∀ (x : Noun) (R2 : Map (Option Noun)) (d : Need) (w : Noun), Qh s x d w → FitsS Lh.sure x →
          HoldsN Lh.sure.ned R2 x → HoldsN d R2 w →
          (∀ z, ((z < g1.re ∨ NMem ned z) ∧ ¬ NMem Lh.sure.ned z) → SkaModel.read z R2 = SkaModel.read z R1) →
          (∀ st' : σ, AgreeLB lib O c gul st' t cf (Need.pair ned d) gb g1 nexq.laz (C s0 w) s) ∧
          (∀ z, NMem (Need.pair ned d) z → g1.re ≤ z) ∧ HoldsS nexq.laz.sure R2 s ∧
          HoldsN (Need.pair ned d) R2 (C s0 w) ∧
          ∀ (st2 : σ) (R3 : Map (Option Noun)) (y : Noun) (dq : Need) (wq : Noun), HoldsN tel.sure.ned R3 y →
            HoldsN dq R3 wq → (∀ z, NMem dq z → gb.re ≤ z ∧ z < g1.re) →
            (∀ z, ((z < gb.re ∨ NMem (Need.pair ned d) z) ∧ ¬ NMem tel.sure.ned z) →
              SkaModel.read z R3 = SkaModel.read z R2) →
            (FitsS hed.sure x → ∃ R4, HoldsN hed.sure.ned R4 x ∧ HoldsN tel.sure.ned R4 y ∧
              (∀ z, ((z < g0.re ∨ NMem ned z) ∧ ¬ NMem L.sure.ned z) → SkaModel.read z R4 = SkaModel.read z regs) ∧
              HoldsN d R4 w ∧ HoldsN dq R4 wq ∧
              goJ lib O c gul st2 R3 t jt = goJ lib O c gul st2 R4 t (jmp0 o)) ∧
            (¬ FitsS hed.sure x → goJ lib O c gul st2 R3 t jt = some (Tone.two t, st2))) :
    SemLB lib N P f L th (pairWitX C HW Qh Qt) g0 g3 (pairRes n r nexq.laz.bond nexp.laz.bond) := by
  have b0' := hpre.2.1
  have bB : g''.bo = g'.bo := hB.bo
  have bgb := hgb.2.1
  have b1 := hq.bo
  have b2 := hp.bo
  have r0' := hpre.1
  have rB := hB.re
  have r1 := hq.re
  have r2 := hp.re
  have qhi := hq.hi
  have phi := hp.hi
  have kc3 := (kc_copy _ _).keep _ _ _ hc
  obtain ⟨EC, eth, bo3, CM, CS⟩ := copy_ok hc
  have l3 := EC.1
  obtain ⟨CD, CF, CB⟩ := CS P0
  have Dc := copy_down (goal := CGoal.next L.sure th) hc hp.lo hp.hi d2 (Nat.le_trans hp.lo (Nat.le_of_lt hp.hi))
  rw [hidx] at hM
  obtain ⟨er, PM, PP, PMo, PMi⟩ := hM.spec d3' pnd (fun e he _ => by
    obtain ⟨B, th', hb⟩ := (hp.labs e (by rw [eP]; exact he)).2
    have : e.1 < g2.bo := by
      rcases lp' e he with a | ⟨a, a'⟩ | a
      · have := labL _ a; omega
      · omega
      · omega
    exact ⟨B, Termin.hop th', by rw [EC.2.2.2 _ this]; exact hb⟩)
  have bM : g3.bo = g3'.bo := PP.bo
  have rM : g3'.re ≤ g3.re := PP.re
  have cM : g3.cond = g3'.cond := PP.cond
  intro cf hcf c ned σ Inv ν O n0 gul hN hS hF st t tm s0 s r0 hI htr hs hm ag hned regs hh hn
  have hcf2 : ∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g2.cond k := fun k hk =>
    (hcf k (by omega)).trans (by rw [cM, kc3])
  have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk =>
    (hcf2 k (by omega)).trans (hp.cfr.get_lt hk)
  obtain ⟨R1, agQ0, agP, hned2, hs1, hn1, e1, keep1, K⟩ := core cf hcf c ned σ O gul st t s0 s ag hned regs hh hn
  obtain ⟨n', hn', rh, hmh, H⟩ := Mf hs hm
  have Gh := hp.sem cf hcf2 c ned σ Inv ν O n' gul hN hS (oracleFwd_le hF (Nat.le_of_lt hn')) st t tm s0 s rh hI htr
    hs hmh agP hned2 R1 hs1 hn1
  rcases H with ⟨hnz, rfl⟩ | ⟨x, rfl, rt, hmt, Ht⟩
  · exact goalSemCMD_ret hnz (returnsC_step (Needs.le_refl _) e1 (returnsC_of_goalSemCMD hnz Gh))
  by_cases fx : FitsS Lh.sure x
  · obtain ⟨st1, R2, d, w, hI1, hν1, hqd, hx2, hd2, k2, e2⟩ := Gh.1 fx
    obtain ⟨agQ, hnQ, hsQ, hnQ', J⟩ := K x R2 d w hqd fx hx2 hd2 k2
    have htr1 := frames_mono hν1 htr
    have Gq := hq.sem cf hcf1 c (Need.pair ned d) σ Inv ν O n' gul hN hS (oracleFwd_le hF (Nat.le_of_lt hn')) st1 t
      tm (C s0 w) s rt hI1 htr1 hs hmt agQ hnQ R2 hsQ hnQ'
    have e12 := e1.trans e2
    rcases Ht with ⟨hnz, rfl⟩ | ⟨y, rfl, hfin⟩
    · exact goalSemCMD_ret hnz (returnsC_step hν1 e12 (returnsC_of_goalSemCMD hnz Gq))
    by_cases fy : FitsS tel.sure y
    · obtain ⟨st2, R3, dq, wq, hI2, hν2, hqq, hy3, hdq3, k3, e3⟩ := Gq.1 fy
      obtain ⟨Jf, Jn⟩ := J st2 R3 y dq wq hy3 hdq3 (fun z hz => hq.dreg s y dq wq z hqq hz) k3
      by_cases fxp : FitsS hed.sure x
      · obtain ⟨R4, hx4, hy4, k4, hdp4, hdq4, e4⟩ := Jf fxp
        have A := hA c agQ0 σ Inv ν O n0 gul hS hF st2 R4 t tm x y n' r0 hn' hI2 (frames_mono hν2 htr1) fxp fy hx4
          hy4 hfin
        have AD := goalSemCMD_of_CM (Q := pairWitX C HW Qh Qt s) (d := Need.pair HW (Need.pair d dq))
          (w := C (C x y) (C w wq))
          (fun z hz => by
            rcases hz with hz | hz | hz
            · exact Or.inr hz
            · have := hp.dreg s x d w z hqd hz
              exact Or.inl ⟨Or.inr (by omega), fun hm => by have := gm z hm; omega⟩
            · have := hq.dreg s y dq wq z hqq hz
              exact Or.inl ⟨Or.inr (by omega), fun hm => by have := gm z hm; omega⟩)
          ⟨hHh R4 x y hx4 hy4, hdp4, hdq4⟩ (fun p hp' => by
            rw [hFin _ _ _ _ _ _ hfin] at hp'
            cases hp'
            exact ⟨x, y, d, dq, w, wq, rfl, rfl, rfl, hqd, hqq⟩) A
        exact goalSemCMD_step (Needs.le_trans hν1 hν2) k4 (e12.trans (e3.trans e4))
          (AD.mono (fun z hz => Or.inl ⟨hz.1.imp id (fun h => by have := hned z h; omega), hz.2⟩) (fun _ _ _ h => h))
      · exact goalSemCMD_bad (hnotF gul n' tm x y r0 (Or.inl fxp) hfin)
          ⟨Tone.two t, st2, hI2, Needs.le_trans hν1 hν2, e12.trans (e3.trans (Jn fxp)),
            ToneRel.two (frames_mono hν2 htr1)⟩
    · exact goalSemCMD_bad (hnotF gul n' tm x y r0 (Or.inr fy) hfin) (returnsC_step hν1 e12 (Gq.2 fy))
  · have R0 := Gh.2 fx
    obtain ⟨nfx, TT⟩ := hcase x fx
    rcases Ht with ⟨hnz, rfl⟩ | ⟨y, rfl, hfin⟩
    · rcases TT.1 s gul n' tm _ hs hmt with e | ⟨y, e⟩
      · subst e
        exact goalSemCMD_ret (fun _ e => by cases e) (returnsC_step (Needs.le_refl _) e1 R0)
      · exact absurd e (hnz y)
    · exact goalSemCMD_bad (hnotF gul n' tm x y r0 (Or.inl nfx) hfin) (returnsC_step (Needs.le_refl _) e1 R0)

/-- The backward `sem` clause of `pairLS_ok`. -/
theorem pairLSX_semB {idx : Map (Nat × Lazy S)}
    (hidx : index (Map := Map) (fun e : Nat × Lazy S => e.1) nexq.laz.bond = idx)
    (P0 : CopyPre nexp.laz.sure.ned nexq.laz.sure.ned g2.re)
    (d2 : g2.drop = false)
    (d3' : g3'.drop = false)
    (pnd : (nexp.laz.bond.map Prod.fst).Nodup)
    (eP : entries nexp.laz = nexp.laz.bond)
    (lp' : ∀ e ∈ nexp.laz.bond, (e.1 ∈ L.bond.map Prod.fst ∨ (e.1 = g''.bo ∧ g''.bo < gb.bo) ∨
      (g1.bo ≤ e.1 ∧ e.1 < g2.bo)))
    (labL : ∀ k, k ∈ L.bond.map Prod.fst → k < g0.bo)
    (gm : ∀ r, NMem L.sure.ned r → r < g0.re)
    (hcase : ∀ x, ¬ FitsS Lh.sure x → ¬ FitsS hed.sure x ∧ TotalC lib P ft)
    (core : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g3.re → HoonMap.get cf k = HoonMap.get g3.cond k) →
      ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ) (t : Trace) (s0 s : Noun),
      (∀ st' : σ, AgreeLB lib O c gul st' t cf ned g0 g3 (pairRes n r nexq.laz.bond nexp.laz.bond).laz s0 s) →
      (∀ x, NMem ned x → g3.re ≤ x) →
      ∀ regs, HoldsS n.laz regs s → HoldsN ned regs s0 →
      ∃ R1, Agree c g0 g' ∧ (∀ st' : σ, AgreeLB lib O c gul st' t cf ned g1 g2 nexp.laz s0 s) ∧
        (∀ x, NMem ned x → g2.re ≤ x) ∧
        HoldsS nexp.laz.sure R1 s ∧ HoldsN ned R1 s0 ∧
        goJ lib O c gul st regs t n.th = goJ lib O c gul st R1 t nexp.th ∧
        (∀ z, ((z < g0.re ∨ NMem ned z) ∧ ¬ NMem L.sure.ned z) → SkaModel.read z R1 = SkaModel.read z regs) ∧
        ∀ (x : Noun) (R2 : Map (Option Noun)) (d : Need) (w : Noun), Qh s x d w → FitsS Lh.sure x →
          HoldsN Lh.sure.ned R2 x → HoldsN d R2 w →
          (∀ z, ((z < g1.re ∨ NMem ned z) ∧ ¬ NMem Lh.sure.ned z) → SkaModel.read z R2 = SkaModel.read z R1) →
          (∀ st' : σ, AgreeLB lib O c gul st' t cf (Need.pair ned d) gb g1 nexq.laz (C s0 w) s) ∧
          (∀ z, NMem (Need.pair ned d) z → g1.re ≤ z) ∧ HoldsS nexq.laz.sure R2 s ∧
          HoldsN (Need.pair ned d) R2 (C s0 w) ∧
          ∀ (st2 : σ) (R3 : Map (Option Noun)) (y : Noun) (dq : Need) (wq : Noun), HoldsN tel.sure.ned R3 y →
            HoldsN dq R3 wq → (∀ z, NMem dq z → gb.re ≤ z ∧ z < g1.re) →
            (∀ z, ((z < gb.re ∨ NMem (Need.pair ned d) z) ∧ ¬ NMem tel.sure.ned z) →
              SkaModel.read z R3 = SkaModel.read z R2) →
            (FitsS hed.sure x → ∃ R4, HoldsN hed.sure.ned R4 x ∧ HoldsN tel.sure.ned R4 y ∧
              (∀ z, ((z < g0.re ∨ NMem ned z) ∧ ¬ NMem L.sure.ned z) → SkaModel.read z R4 = SkaModel.read z regs) ∧
              HoldsN d R4 w ∧ HoldsN dq R4 wq ∧
              goJ lib O c gul st2 R3 t jt = goJ lib O c gul st2 R4 t (jmp0 o)) ∧
            (¬ FitsS hed.sure x → goJ lib O c gul st2 R3 t jt = some (Tone.two t, st2))) :
    SemLBB lib N P f L th (pairWitX C HW Qh Qt) g0 g3 (pairRes n r nexq.laz.bond nexp.laz.bond) := by
  have b0' := hpre.2.1
  have bB : g''.bo = g'.bo := hB.bo
  have bgb := hgb.2.1
  have b1 := hq.bo
  have b2 := hp.bo
  have r0' := hpre.1
  have rB := hB.re
  have r1 := hq.re
  have r2 := hp.re
  have qhi := hq.hi
  have phi := hp.hi
  have kc3 := (kc_copy _ _).keep _ _ _ hc
  obtain ⟨EC, eth, bo3, CM, CS⟩ := copy_ok hc
  have l3 := EC.1
  obtain ⟨CD, CF, CB⟩ := CS P0
  have Dc := copy_down (goal := CGoal.next L.sure th) hc hp.lo hp.hi d2 (Nat.le_trans hp.lo (Nat.le_of_lt hp.hi))
  rw [hidx] at hM
  obtain ⟨er, PM, PP, PMo, PMi⟩ := hM.spec d3' pnd (fun e he _ => by
    obtain ⟨B, th', hb⟩ := (hp.labs e (by rw [eP]; exact he)).2
    have : e.1 < g2.bo := by
      rcases lp' e he with a | ⟨a, a'⟩ | a
      · have := labL _ a; omega
      · omega
      · omega
    exact ⟨B, Termin.hop th', by rw [EC.2.2.2 _ this]; exact hb⟩)
  have bM : g3.bo = g3'.bo := PP.bo
  have rM : g3'.re ≤ g3.re := PP.re
  have cM : g3.cond = g3'.cond := PP.cond
  intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
  have hcf2 : ∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g2.cond k := fun k hk =>
    (hcf k (by omega)).trans (by rw [cM, kc3])
  have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk =>
    (hcf2 k (by omega)).trans (hp.cfr.get_lt hk)
  obtain ⟨R1, agQ0, agP, hned2, hs1, hn1, e1, keep1, K⟩ := core cf hcf c ned σ O gul st t s0 s ag hned regs hh hn
  obtain ⟨rh, hmh, Gh⟩ := hp.semB cf hcf2 c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs agP hned2 R1 hs1 hn1
    res (by rw [← e1]; exact hres)
  cases rh with
  | one q =>
    exact ⟨_, (Mb hs hmh).1 (fun _ e => by cases e),
      goalSemCMD_ret (fun _ e => by cases e) (returnsC_step (Needs.le_refl _) e1 Gh)⟩
  | two t' =>
    exact ⟨_, (Mb hs hmh).1 (fun _ e => by cases e),
      goalSemCMD_ret (fun _ e => by cases e) (returnsC_step (Needs.le_refl _) e1 Gh)⟩
  | zero x =>
    by_cases fx : FitsS Lh.sure x
    · obtain ⟨st1, R2, d, w, hI1, hν1, hqd, hx2, hd2, k2, e2⟩ := Gh.1 fx
      obtain ⟨agQ, hnQ, hsQ, hnQ', J⟩ := K x R2 d w hqd fx hx2 hd2 k2
      have htr1 := frames_mono hν1 htr
      have e12 := e1.trans e2
      obtain ⟨rt, hmt, Gq⟩ := hq.semB cf hcf1 c (Need.pair ned d) σ Inv ν O gul hN hS hB st1 t tm (C s0 w) s hI1 htr1
        hs agQ hnQ R2 hsQ hnQ' res (by rw [← e12]; exact hres)
      have MB := (Mb hs hmh).2 x rt rfl hmt
      cases rt with
      | one q =>
        exact ⟨_, MB.1 (fun _ e => by cases e),
          goalSemCMD_ret (fun _ e => by cases e) (returnsC_step hν1 e12 Gq)⟩
      | two t' =>
        exact ⟨_, MB.1 (fun _ e => by cases e),
          goalSemCMD_ret (fun _ e => by cases e) (returnsC_step hν1 e12 Gq)⟩
      | zero y =>
        by_cases fy : FitsS tel.sure y
        · obtain ⟨st2, R3, dq, wq, hI2, hν2, hqq, hy3, hdq3, k3, e3⟩ := Gq.1 fy
          obtain ⟨Jf, Jn⟩ := J st2 R3 y dq wq hy3 hdq3 (fun z hz => hq.dreg s y dq wq z hqq hz) k3
          by_cases fxp : FitsS hed.sure x
          · obtain ⟨R4, hx4, hy4, k4, hdp4, hdq4, e4⟩ := Jf fxp
            have e14 := e12.trans (e3.trans e4)
            obtain ⟨r1, hfr, A⟩ := hAB c agQ0 σ Inv ν O gul hS hB st2 R4 t tm x y hI2 (frames_mono hν2 htr1) fxp fy
              hx4 hy4 res (by rw [← e14]; exact hres)
            have AD := goalSemCMD_of_CM (Q := pairWitX C HW Qh Qt s) (d := Need.pair HW (Need.pair d dq))
              (w := C (C x y) (C w wq))
              (fun z hz => by
                rcases hz with hz | hz | hz
                · exact Or.inr hz
                · have := hp.dreg s x d w z hqd hz
                  exact Or.inl ⟨Or.inr (by omega), fun hm => by have := gm z hm; omega⟩
                · have := hq.dreg s y dq wq z hqq hz
                  exact Or.inl ⟨Or.inr (by omega), fun hm => by have := gm z hm; omega⟩)
              ⟨hHh R4 x y hx4 hy4, hdp4, hdq4⟩ (fun p hp' => by
                rw [hFinB _ _ _ _ _ hfr] at hp'
                cases hp'
                exact ⟨x, y, d, dq, w, wq, rfl, rfl, rfl, hqd, hqq⟩) A
            exact ⟨r1, MB.2 y r1 rfl hfr, goalSemCMD_step (Needs.le_trans hν1 hν2) k4 e14
              (AD.mono (fun z hz => Or.inl ⟨hz.1.imp id (fun h => by have := hned z h; omega), hz.2⟩) (fun _ _ _ h => h))⟩
          · obtain ⟨r1, hfr, hbr⟩ := hnotB gul tm x y (Or.inl fxp)
            exact ⟨r1, MB.2 y r1 rfl hfr, goalSemCMD_bad hbr ⟨Tone.two t, st2, hI2, Needs.le_trans hν1 hν2,
              e12.trans (e3.trans (Jn fxp)), ToneRel.two (frames_mono hν2 htr1)⟩⟩
        · obtain ⟨r1, hfr, hbr⟩ := hnotB gul tm x y (Or.inr fy)
          exact ⟨r1, MB.2 y r1 rfl hfr, goalSemCMD_bad hbr (returnsC_step hν1 e12 (Gq.2 fy))⟩
    · have R0 := Gh.2 fx
      obtain ⟨nfx, TT⟩ := hcase x fx
      obtain ⟨rt, hmt, hrt⟩ := TT.2 s gul tm hs
      have MB := (Mb hs hmh).2 x rt rfl hmt
      rcases hrt with rfl | ⟨y, rfl⟩
      · exact ⟨_, MB.1 (fun _ e => by cases e),
          goalSemCMD_ret (fun _ e => by cases e) (returnsC_step (Needs.le_refl _) e1 R0)⟩
      · obtain ⟨r1, hfr, hbr⟩ := hnotB gul tm x y (Or.inl nfx)
        exact ⟨r1, MB.2 y r1 rfl hfr, goalSemCMD_bad hbr (returnsC_step (Needs.le_refl _) e1 R0)⟩

end

end Comp
end SkaModel
end Formalization
