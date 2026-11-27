import lemmas.Ska.CompPairLSCore
import lemmas.Ska.CompFrontSX

/-!
# The fronts of a pair under a flat lazy goal, parts of any flag: `pairLSX_fronts`

README Gaps 12.32.  The first piece of `pairLS_ok` for parts of any flag:
`pairLS_fronts` (`CompPairLSSem.lean`) with the parts' `RunOKLS` at any
flags `xp`, `xq`, the parent's at any `x`, and the witness `pairWitX C HW`
(the halves `HW` that `+split` allocated, held with the parts' products),
through `frontS_pairX` at each goal label.  The section is
`CompPairLSSem.lean`'s with the flags, `HW`, the keep of `HW` by the block
`o` in `hA`/`hAB` (`Keep … ∨ NMem HW`), and the new hypotheses: `HW` in the
split's range (`hHr`), the halves hold it (`hHh`), the parts' goal
registers held from the parent's and `HW` (`hEH`), the goal's entries apart
from its sure need (`hG`), and the parts' result entries at the goal's
labels apart from `HW` and the goals' registers (`hPH`, the fact the scratch
test of `CompFrontSX.lean` found true at goal labels).
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

/-- The fronts of `pairLS_ok` (`FrontsS`). -/
theorem pairLSX_fronts {idx : Map (Nat × Lazy S)}
    (hidx : index (Map := Map) (fun e : Nat × Lazy S => e.1) nexq.laz.bond = idx)
    (P0 : CopyPre nexp.laz.sure.ned nexq.laz.sure.ned g2.re)
    (d2 : g2.drop = false)
    (d3' : g3'.drop = false)
    (pnd : (nexp.laz.bond.map Prod.fst).Nodup)
    (eP : entries nexp.laz = nexp.laz.bond)
    (lp' : ∀ e ∈ nexp.laz.bond, (e.1 ∈ L.bond.map Prod.fst ∨ (e.1 = g''.bo ∧ g''.bo < gb.bo) ∨
      (g1.bo ≤ e.1 ∧ e.1 < g2.bo)))
    (labL : ∀ k, k ∈ L.bond.map Prod.fst → k < g0.bo)
    (eL : entries L = L.bond)
    (eH : entries hed = hed.bond)
    (eT : entries tel = tel.bond)
    (eQ : entries nexq.laz = nexq.laz.bond)
    (mLh : ∀ e, e ∈ entries Lh → e ∈ hed.bond ∨
      (e = (g''.bo, ofSure hed.sure) ∧ jt = jmp0 g''.bo ∧ g''.bo < gb.bo))
    (qnd : (nexq.laz.bond.map Prod.fst).Nodup)
    (cb2 : CondBelow g2)
    (idxN : ∀ k, HoonMap.get idx k = Option.none ↔ k ∉ nexq.laz.bond.map Prod.fst)
    (eR : entries (pairRes n r nexq.laz.bond nexp.laz.bond).laz = (pairRes n r nexq.laz.bond nexp.laz.bond).laz.bond)
    (mergeOK : ∀ (e : Nat × Lazy S), ∀ e1 ∈ nexp.laz.bond, ∀ e2 ∈ nexq.laz.bond, ∀ (s1 s2 s' : Sure S) (ga gc : Gen Map),
      e1.1 = e.1 → e2.1 = e.1 → e1.2 = ofSure s1 → e2.2 = ofSure s2 → g3'.re ≤ ga.re → gc.re ≤ g3.re →
      ga.drop = false → copyLazy e.1 s1 s2 ga = some (s', gc) →
      ∃ (A : List Pole) (gx : Gen Map), Pref ga gc (fun k => if k = e.1 then A else []) ∧
        CopyOK s1.ned s2.ned ga gx s'.ned A ∧ gx.re = gc.re ∧ s'.lok = HoonSet.uni s1.lok s2.lok ∧
        (∀ (Pr : Nat → Prop), NA Pr s1.ned → NA Pr s2.ned → Ple Pr ga.re → RegsIn Pr A) ∧
        RegsIn (· < gc.re) A ∧
        ∃ eb ∈ L.bond, ∃ sh st, SplitAt (Map := Map) eb hed tel (PB eb.1) g'.re g''.re sh st ∧ eb.1 = e.1 ∧
          CopyPre s1.ned s2.ned ga.re ∧
          (∀ x, NMem s1.ned x → x < g2.re ∧ (x < g1.re → NMem sh.ned x)) ∧
          (∀ x, NMem s2.ned x → x < g1.re ∧ (x < gb.re → NMem st.ned x))) :
    FrontsS (Map := Map) (pairWitX C HW Qh Qt) x g0 g3 L (pairRes n r nexq.laz.bond nexp.laz.bond) := by
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
  intro e he
  rw [eL] at he
  obtain ⟨sh, st, SA⟩ := hsp e he
  have hlt : e.1 < g0.bo := labL _ (List.mem_map_of_mem he)
  obtain ⟨-, -, -, hLe⟩ := hLb e he
  -- the tail's ops at the entry's block
  obtain ⟨Fq, hFq, FQ⟩ : ∃ Fq : List Pole,
      (∀ B fin, HoonMap.get gb.blocks e.1 = some ⟨[], B, fin⟩ → HoonMap.get g1.blocks e.1 = some ⟨[], Fq ++ B, fin⟩) ∧
      ∀ cf : Map (Nat × List Nat), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
        ∃ Lq : Sure S, FrontS (Map := Map) Qt (gsE xq tel) gb.re g1.re Lq (Fq.map (renPole (unproxy cf))) st ∧
          ((e.1, ofSure Lq) ∈ nexq.laz.bond ∨ (e.1 ∉ nexq.laz.bond.map Prod.fst ∧ Lq = Sure.bunt)) := by
    rcases SA.int with a | ⟨a, an, as⟩
    · have hin : (e.1, ofSure st) ∈ entries tel := by rw [eT]; exact a
      obtain ⟨F, hF, hf⟩ := hq.fs _ hin
      refine ⟨F, hF, fun cf hcf => ?_⟩
      rcases hf cf hcf with ⟨L', hm, FS'⟩ | ⟨hn, FS'⟩
      · rw [eQ] at hm
        refine ⟨L'.sure, FS', Or.inl ?_⟩
        have := hqf.2 _ hm
        simp only at this
        rw [← this]; exact hm
      · exact ⟨Sure.bunt, FS', Or.inr ⟨by rw [eQ] at hn; exact hn, rfl⟩⟩
    · refine ⟨[], fun B fin hB => ?_, fun cf hcf => ⟨Sure.bunt, frontS_empty an as, Or.inr ⟨fun hm => ?_, rfl⟩⟩⟩
      · rw [hq.keep _ (by omega) (by rw [eT]; exact a)]; exact hB
      · obtain ⟨e2, he2, ee⟩ := List.mem_map.mp hm
        rcases (hq.labs e2 (by rw [eQ]; exact he2)).1 with h | h
        · exact a (by rw [← eT, ← ee]; exact h)
        · omega
  -- the head's ops at the entry's block
  obtain ⟨Fp, hFp, FP⟩ : ∃ Fp : List Pole,
      (∀ B fin, HoonMap.get g1.blocks e.1 = some ⟨[], B, fin⟩ → HoonMap.get g2.blocks e.1 = some ⟨[], Fp ++ B, fin⟩) ∧
      ∀ cf : Map (Nat × List Nat), (∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g2.cond k) →
        ∃ Lp : Sure S, FrontS (Map := Map) Qh (gsE xp Lh) g1.re g2.re Lp (Fp.map (renPole (unproxy cf))) sh ∧
          ((e.1, ofSure Lp) ∈ nexp.laz.bond ∨ (e.1 ∉ nexp.laz.bond.map Prod.fst ∧ Lp = Sure.bunt)) := by
    rcases SA.inh with a | ⟨a, an, as⟩
    · have hin : (e.1, ofSure sh) ∈ entries Lh := by
        rcases hjt with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩
        · rw [eH]; exact a
        · have fl : Flat (mk (Sure.bunt : Sure S) [] ((g''.bo, ofSure hed.sure) :: hed.bond)) :=
            flat_mk (fun e he => by
              rcases List.mem_cons.mp he with h | h
              · rw [h]; rfl
              · exact hhf.2 e h)
          rw [entries_flat fl]
          exact List.mem_cons_of_mem _ a
      obtain ⟨F, hF, hf⟩ := hp.fs _ hin
      refine ⟨F, hF, fun cf hcf => ?_⟩
      rcases hf cf hcf with ⟨L', hm, FS'⟩ | ⟨hn, FS'⟩
      · rw [eP] at hm
        refine ⟨L'.sure, FS', Or.inl ?_⟩
        have := hpf.2 _ hm
        simp only at this
        rw [← this]; exact hm
      · exact ⟨Sure.bunt, FS', Or.inr ⟨by rw [eP] at hn; exact hn, rfl⟩⟩
    · have hn : e.1 ∉ (entries Lh).map Prod.fst := fun hm => by
        obtain ⟨e0, h0, ee⟩ := List.mem_map.mp hm
        rcases mLh e0 h0 with m | ⟨m, _, _⟩
        · exact a (by rw [← ee]; exact List.mem_map_of_mem m)
        · rw [m] at ee; simp only at ee; omega
      refine ⟨[], fun B fin hB => ?_, fun cf hcf => ⟨Sure.bunt, frontS_empty an as, Or.inr ⟨fun hm => ?_, rfl⟩⟩⟩
      · rw [hp.keep _ (by omega) hn]; exact hB
      · obtain ⟨e1, he1, ee⟩ := List.mem_map.mp hm
        rcases (hp.labs e1 (by rw [eP]; exact he1)).1 with h | h
        · exact hn (by rw [← ee]; exact h)
        · omega
  refine ⟨PM e.1 ++ Fp ++ Fq ++ PB e.1, fun B fin hB0 => ?_, fun cf hcf => ?_⟩
  · -- the ops in front of the entry's block
    have h1 : HoonMap.get g''.blocks e.1 = some ⟨[], PB e.1 ++ B, fin⟩ := hB.blk (by rw [hpre.2.2.2 _ hlt]; exact hB0)
    have h2 : HoonMap.get gb.blocks e.1 = some ⟨[], PB e.1 ++ B, fin⟩ := by rw [hgb.2.2.2 _ (by omega)]; exact h1
    have h4 := hFp _ _ (hFq _ _ h2)
    have h5 : HoonMap.get g3'.blocks e.1 = some ⟨[], Fp ++ (Fq ++ (PB e.1 ++ B)), fin⟩ := by
      rw [EC.2.2.2 _ (by omega)]; exact h4
    have h6 := PP.blk h5
    simpa only [List.append_assoc] using h6
  · -- the fronts at the state level
    have hcf2 : ∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g2.cond k := fun k hk =>
      (hcf k (by omega)).trans (by rw [cM, kc3])
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk =>
      (hcf2 k (by omega)).trans (hp.cfr.get_lt hk)
    have cf0 : ∀ k, k < gb.re → HoonMap.get cf k = HoonMap.get g0.cond k := fun k hk =>
      (hcf1 k (by omega)).trans ((hq.cfr.get_lt hk).trans (by rw [hgbc, hB.cond, hcnd]))
    obtain ⟨Lp, FPs, mp'⟩ := FP cf hcf2
    obtain ⟨Lq, FQs, mq'⟩ := FQ cf hcf1
    have uB : (PB e.1).map (renPole (unproxy cf)) = PB e.1 := by
      refine unproxy_ops (fun p hp' x hx => ?_)
      rcases SA.regs p hp' x hx with a | ⟨a, a'⟩
      · rw [cf0 x (by have := (hLe x a).1; omega)]; exact (hLe x a).2
      · rw [cf0 x (by omega)]; exact condBelow_none hcb (by omega)
    -- the copy at the label
    obtain ⟨M, Ac, hPM, hM1, hM2, hM3, hM4, hM5, hres⟩ : ∃ (M : Sure S) (Ac : List Pole), PM e.1 = Ac ∧
        (∀ x, NMem M.ned x → NMem Lp.ned x ∨ NMem Lq.ned x ∨ (g2.re ≤ x ∧ x < g3.re)) ∧
        (∀ s, FitsS M s ↔ FitsS Lp s ∧ FitsS Lq s) ∧ (∀ s, Looks M.lok s → Looks Lp.lok s ∧ Looks Lq.lok s) ∧
        CopySem Map Lp.ned Lq.ned M.ned Ac ∧ Ac.map (renPole (unproxy cf)) = Ac ∧
        ((e.1, ofSure M) ∈ (pairRes n r nexq.laz.bond nexp.laz.bond).laz.bond ∨
          (e.1 ∉ (pairRes n r nexq.laz.bond nexp.laz.bond).laz.bond.map Prod.fst ∧ M = Sure.bunt)) := by
      rcases mp' with hp1 | ⟨hp1, rfl⟩ <;> rcases mq' with hq1 | ⟨hq1, rfl⟩
      · -- both: merged
        obtain ⟨-, i2⟩ := PMi _ hp1
        have hg : HoonMap.get idx e.1 = some (e.1, ofSure Lq) := by
          rw [← hidx]; exact get_index_mem (fun e : Nat × Lazy S => e.1) qnd hq1
        obtain ⟨s1, s', ga, gc, es1, ms, l1, l2, dd, bb, cpy, pp⟩ := i2 e.1 Lq hg
        have e1 : s1 = Lp := by have := congrArg Lazy.sure es1; simpa [ofSure] using this.symm
        subst e1
        obtain ⟨A, gx, PA, CO, ex, lk, RA, RB, eb, heb, sh', st', SA', ebe, CP, L1, L2⟩ :=
          mergeOK e (e.1, ofSure s1) hp1 (e.1, ofSure Lq) hq1 s1 Lq s' ga gc rfl rfl rfl rfl l1 l2 dd cpy
        obtain ⟨-, -, CF', CS'⟩ := CO.sem CP
        refine ⟨s', A, pp A PA, fun x hx => ?_, fun s => ?_, fun s hl => ?_, CS', ?_, Or.inl ?_⟩
        · rcases CO.mem x hx with (a | a) | ⟨a, a'⟩
          · exact Or.inl a
          · exact Or.inr (Or.inl a)
          · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
        · simp only [FitsS, CF' s, lk, looks_uni]
          exact ⟨fun ⟨⟨a, b⟩, c, d⟩ => ⟨⟨a, c⟩, b, d⟩, fun ⟨⟨a, c⟩, b, d⟩ => ⟨⟨a, b⟩, c, d⟩⟩
        · rw [lk] at hl; exact (looks_uni _ _ s).mp hl
        · have RC := RA (fun x => x < g3.re → HoonMap.get cf x = Option.none)
            (fun x hx' h => by
              rw [hcf2 x (L1 x hx').1]; exact hp.econd (e.1, ofSure s1) (by rw [eP]; exact hp1) x hx')
            (fun x hx' h => by
              rw [hcf1 x (L2 x hx').1]; exact hq.econd (e.1, ofSure Lq) (by rw [eQ]; exact hq1) x hx')
            (fun x hx' h => by rw [hcf x h, cM, kc3]; exact condBelow_none cb2 (by omega))
          refine unproxy_ops (fun p hp' x hx => RC p hp' x hx ?_)
          have := RB p hp' x hx; simp only at this; omega
        · rw [mem_pairRes_bond]; exact Or.inl ms
      · -- the head's entry only
        have hn : HoonMap.get idx e.1 = Option.none := (idxN e.1).mpr hq1
        obtain ⟨i1, -⟩ := PMi _ hp1
        refine ⟨Lp, [], PMo e.1 (Or.inr hn), fun x hx => Or.inl hx, fun s => ?_, fun s hl => ⟨hl, looks_empty s⟩,
          copySem_left_nil _, rfl, Or.inl (mem_pairRes_bond.mpr (Or.inl (i1 hn)))⟩
        exact ⟨fun h => ⟨h, fitsS_bunt s⟩, fun h => h.1⟩
      · -- the tail's entry only
        refine ⟨Lq, [], PMo e.1 (Or.inl hp1), fun x hx => Or.inr (Or.inl hx), fun s => ?_,
          fun s hl => ⟨looks_empty s, hl⟩, copySem_right_nil _, rfl, Or.inl (mem_pairRes_bond.mpr (Or.inr ⟨hq1, hp1⟩))⟩
        exact ⟨fun h => ⟨fitsS_bunt s, h⟩, fun h => h.2⟩
      · -- no entry
        refine ⟨Sure.bunt, [], PMo e.1 (Or.inl hp1), fun x hx => by simp [Sure.bunt, NMem] at hx,
          fun s => ⟨fun _ => ⟨fitsS_bunt s, fitsS_bunt s⟩, fun _ => fitsS_bunt s⟩,
          fun s hl => ⟨looks_empty s, looks_empty s⟩, copySem_left_nil _, rfl, Or.inr ⟨fun hm => ?_, rfl⟩⟩
        obtain ⟨e', he', ee⟩ := List.mem_map.mp hm
        rcases mem_pairRes_bond.mp he' with h | ⟨h, _⟩
        · exact hp1 (by rw [← er, ← ee]; exact List.mem_map_of_mem h)
        · exact hq1 (by rw [← ee]; exact List.mem_map_of_mem h)
    have hLh' : ∀ x, NMem sh.ned x → x < gb.re ∧ (x < g0.re → NMem e.2.sure.ned x) := by
      intro x hx
      rcases SA.mh x hx with a | a
      · exact ⟨by have := (hLe x a).1; omega, fun _ => a⟩
      · exact ⟨by omega, fun h => by omega⟩
    have hLt' : ∀ x, NMem st.ned x → x < gb.re ∧ (x < g0.re → NMem e.2.sure.ned x) := by
      intro x hx
      rcases SA.mt x hx with a | a
      · exact ⟨by have := (hLe x a).1; omega, fun _ => a⟩
      · exact ⟨by omega, fun h => by omega⟩
    -- the parts' entries at the label are apart from the halves and the goals' registers
    have nP : ∀ z, (NMem HW z ∨ NMem (gsE xp Lh) z ∨ NMem (gsE xq tel) z ∨ NMem (gsE x L) z) →
        ¬ NMem Lp.ned z ∧ ¬ NMem Lq.ned z := fun z hz => by
      refine ⟨fun hm => ?_, fun hm => ?_⟩
      · rcases mp' with h1 | ⟨_, rfl⟩
        · exact hPH e he _ (List.mem_append_left _ h1) rfl z hz (by simpa [ofSure] using hm)
        · simp [Sure.bunt, NMem] at hm
      · rcases mq' with h1 | ⟨_, rfl⟩
        · exact hPH e he _ (List.mem_append_right _ h1) rfl z hz (by simpa [ofSure] using hm)
        · simp [Sure.bunt, NMem] at hm
    have gm' : ∀ z, NMem L.sure.ned z → z < g0.re := fun z hz => hg.2 z hz
    have F1 := frontS_pairX (comb := C) FPs FQs (lo0 := g0.re) (lo := g3.re) (Lb := e.2.sure) (Fs := PB e.1)
      (H := HW) (E := gsE x L)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun s v d w x hq' hx => hp.dreg s v d w x hq' hx) (fun s v d w x hq' hx => hq.dreg s v d w x hq' hx)
      hLh' hLt' SA.ht hM1 hM2 hM3 hM4 SA.fit SA.sem
      (fun z hz => by
        obtain ⟨h1, h2⟩ := hHr z hz
        obtain ⟨n1, n2⟩ := nP z (Or.inl hz)
        refine ⟨h1, by omega, n1, n2, fun hm => ?_, fun hm => ?_⟩
        · rcases SA.mh z hm with a | a
          · have := (hLe z a).1; omega
          · omega
        · rcases SA.mt z hm with a | a
          · have := (hLe z a).1; omega
          · omega)
      (fun z hz => nP z (Or.inr (Or.inl hz)))
      (fun z hz => by
        obtain ⟨n1, n2⟩ := nP z (Or.inr (Or.inr (Or.inl hz)))
        have hz' : NMem tel.sure.ned z := by
          cases xq
          · exact hz.elim
          · exact hz
        refine ⟨?_, n1, n2, fun hm => ?_⟩
        · rcases hlq z hz' with a | ⟨_, a⟩
          · have := gm' z a; omega
          · omega
        · rcases SA.mh z hm with a | a
          · rcases hlq z hz' with b | ⟨b, _⟩
            · exact hG e he z b a
            · have := (hLe z a).1; omega
          · rcases hlq z hz' with b | ⟨_, b⟩
            · have := gm' z b; omega
            · omega)
      (fun R a b h1 h2 => hEH R a b h1 h2)
    have eF : (PM e.1 ++ Fp ++ Fq ++ PB e.1).map (renPole (unproxy cf)) =
        Ac ++ Fp.map (renPole (unproxy cf)) ++ Fq.map (renPole (unproxy cf)) ++ PB e.1 := by
      rw [List.map_append, List.map_append, List.map_append, uB, hPM, hM5]
    rw [eF]
    rcases hres with h | ⟨h, rfl⟩
    · exact Or.inl ⟨ofSure M, by rw [eR]; exact h, F1⟩
    · exact Or.inr ⟨by rw [eR]; exact h, F1⟩

end

end Comp
end SkaModel
end Formalization
