import lemmas.Ska.CompPairLSXSem
import lemmas.Ska.CompPairLS

/-!
# A pair of runs under a flat lazy goal with entries, parts of any flag: `pairLSX_ok`

README Gaps 12.32.  `pairLS_ok` (`CompPairLS.lean`, copied by script) with
the parts at any flags and the witness `pairWitX C HW`, from
`pairLSX_core`, `pairLSX_sem`, `pairLSX_semB`, `pairLSX_fronts`.  The front
field comes from `FrontsS.toFrontG`: the result's entries at the goal's
labels are a part's entry there or the copy of two (`resE`, `copyLazy_ok`),
apart from the goal's registers by `hPH`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **`pairLS_ok` for parts of any flag** (README Gaps 12.32): the parts'
`RunOKLS` at any flags `xp`, `xq`, the whole's at any `x`, with the witness
`pairWitX C HW` (the halves `HW` that `+split` allocated, which the block `o`
keeps, `hA`/`hAB`), when the parts' goal registers are held from the
parent's and `HW` (`hEH`), the goal's entries are apart from its sure need
(`hG`), and the parts' result entries at the goal's labels are apart from
`HW` and the goals' registers (`hPH`). -/
theorem pairLSX_ok {lib : Lib} {N : Needs} {P : Noun → Prop} {f fh ft : Noun} {L : Lazy S} {th : Jmp}
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
      (NMem HW z ∨ NMem (gsE xp Lh) z ∨ NMem (gsE xq tel) z ∨ NMem (gsE x L) z) → ¬ NMem e1.2.sure.ned z) :
    RunOKLS (Map := Map) lib N P f L th (pairWitX C HW Qh Qt) x g0 g3 (pairRes n r nexq.laz.bond nexp.laz.bond) ∧
      g0.bo ≤ n.th.there ∧ n.th = jmp0 g2.bo ∧ Flat (pairRes n r nexq.laz.bond nexp.laz.bond).laz ∧
      (∀ e ∈ entries (pairRes n r nexq.laz.bond nexp.laz.bond).laz, Clean e.2.sure.ned) ∧
      (∀ e ∈ entries (pairRes n r nexq.laz.bond nexp.laz.bond).laz, e.1 < g2.bo) := by
  -- flat entries
  have eL : entries L = L.bond := entries_flat hLf
  have eH : entries hed = hed.bond := entries_flat hhf
  have eT : entries tel = tel.bond := entries_flat htf
  have eQ : entries nexq.laz = nexq.laz.bond := entries_flat hqf
  have eP : entries nexp.laz = nexp.laz.bond := entries_flat hpf
  -- the head's goal
  have hLs' : ∀ r, NMem Lh.sure.ned r → NMem hed.sure.ned r := fun r hr => by
    rcases hjt with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩
    · exact hr
    · exact absurd hr (by simp [Sure.bunt, NMem])
  have mLh : ∀ e, e ∈ entries Lh → e ∈ hed.bond ∨
      (e = (g''.bo, ofSure hed.sure) ∧ jt = jmp0 g''.bo ∧ g''.bo < gb.bo) := fun e he => by
    rcases hjt with ⟨_, rfl, _⟩ | ⟨hj, rfl, h', _⟩
    · rw [eH] at he; exact Or.inl he
    · have fl : Flat (mk (Sure.bunt : Sure S) [] ((g''.bo, ofSure hed.sure) :: hed.bond)) :=
        flat_mk (fun e he => by
          rcases List.mem_cons.mp he with rfl | he
          · rfl
          · exact hhf.2 e he)
      rw [entries_flat fl] at he
      rcases List.mem_cons.mp he with rfl | he
      · exact Or.inr ⟨rfl, hj, h'⟩
      · exact Or.inl he
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
  have labL : ∀ k, k ∈ L.bond.map Prod.fst → k < g0.bo := fun k hk => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
    exact (hLb e he).1
  have labLh : ∀ k, k ∈ (entries Lh).map Prod.fst → k ∈ L.bond.map Prod.fst ∨ (k = g''.bo ∧ g''.bo < gb.bo) :=
    fun k hk => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
      rcases mLh e he with h | ⟨rfl, _, h'⟩
      · exact Or.inl (hhl e h)
      · exact Or.inr ⟨rfl, h'⟩
  have labT : ∀ k, k ∈ (entries tel).map Prod.fst → k ∈ L.bond.map Prod.fst := fun k hk => by
    rw [eT] at hk
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
    exact htl e he
  -- the parts' result entries
  have lq' : ∀ e ∈ nexq.laz.bond, (e.1 ∈ L.bond.map Prod.fst ∨ (gb.bo ≤ e.1 ∧ e.1 < g1.bo)) := fun e he => by
    rcases (hq.labs e (by rw [eQ]; exact he)).1 with h | h
    · exact Or.inl (labT _ h)
    · exact Or.inr h
  have lp' : ∀ e ∈ nexp.laz.bond, (e.1 ∈ L.bond.map Prod.fst ∨ (e.1 = g''.bo ∧ g''.bo < gb.bo) ∨
      (g1.bo ≤ e.1 ∧ e.1 < g2.bo)) := fun e he => by
    rcases (hp.labs e (by rw [eP]; exact he)).1 with h | h
    · rcases labLh _ h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have shared : ∀ e1 ∈ nexp.laz.bond, ∀ e2 ∈ nexq.laz.bond, e1.1 = e2.1 → e1.1 ∈ L.bond.map Prod.fst :=
    fun e1 h1 e2 h2 e => by
      rcases lp' e1 h1 with a | ⟨a, a'⟩ | a
      · exact a
      · rcases lq' e2 h2 with b | b
        · rw [e]; exact b
        · omega
      · rcases lq' e2 h2 with b | b
        · rw [e]; exact b
        · omega
  have pnd : (nexp.laz.bond.map Prod.fst).Nodup := by have := hp.nodup; rwa [eP] at this
  have qnd : (nexq.laz.bond.map Prod.fst).Nodup := by have := hq.nodup; rwa [eQ] at this
  -- the copy of the sure needs
  have kc3 := (kc_copy _ _).keep _ _ _ hc
  obtain ⟨EC, eth, bo3, CM, CS⟩ := copy_ok hc
  have gm : ∀ r, NMem L.sure.ned r → r < g0.re := fun r hr => hg.2 r hr
  have lpl : ∀ r, NMem hed.sure.ned r → r < g'.re := fun r hr => by
    rcases hlp r hr with h | ⟨_, h⟩
    · exact Nat.lt_of_lt_of_le (gm r h) hpre.1
    · exact h
  have lql : ∀ r, NMem tel.sure.ned r → r < g'.re := fun r hr => by
    rcases hlq r hr with h | ⟨_, h⟩
    · exact Nat.lt_of_lt_of_le (gm r h) hpre.1
    · exact h
  have mp : ∀ r, NMem nexp.laz.sure.ned r → NMem hed.sure.ned r ∨ (g1.re ≤ r ∧ r < g2.re) := fun r hr =>
    (hp.regs r hr).imp_left (hLs' r)
  have mq : ∀ r, NMem nexq.laz.sure.ned r → NMem tel.sure.ned r ∨ (gb.re ≤ r ∧ r < g1.re) := hq.regs
  have l3 := EC.1
  have lowP : ∀ r, NMem nexp.laz.sure.ned r → r < g2.re := fun r hr => by
    rcases mp r hr with a | ⟨_, a⟩
    · have := lpl r a; omega
    · exact a
  have lowQ : ∀ r, NMem nexq.laz.sure.ned r → r < g1.re := fun r hr => by
    rcases mq r hr with a | ⟨_, a⟩
    · have := lql r a; omega
    · exact a
  have P0 : CopyPre nexp.laz.sure.ned nexq.laz.sure.ned g2.re := by
    refine ⟨cp, cq, ⟨hp.dist, hq.dist, fun r h1 h2 => ?_⟩, fun r hr => ?_⟩
    · rcases mp r h1 with a | a
      · rcases mq r h2 with b | b
        · exact hpq r a b
        · have := lpl r a; omega
      · rcases mq r h2 with b | b
        · have := lql r b; omega
        · omega
    · rcases hr with h | h
      · exact lowP r h
      · have := lowQ r h; omega
  obtain ⟨CD, CF, CB⟩ := CS P0
  have d2 : g2.drop = false := hp.drop.trans (hq.drop.trans (hgb.2.2.1.trans (hB.drop.trans (hpre.2.2.1.trans d0))))
  have Dc := copy_down (goal := CGoal.next L.sure th) hc hp.lo hp.hi d2 (Nat.le_trans hp.lo (Nat.le_of_lt hp.hi))
  have G2 : GrowU g0 g2 := hgr.trans (hB.growU.trans (hgbU.trans (hq.grow.trans hp.grow)))
  have u2 : UpBelow g2 := G2.up hu
  have CF2 : CondFresh g0 g2 :=
    ((condFresh_of_eq hpre.1 hcnd).trans (hB.condFresh.trans (condFresh_of_eq (by omega) hgbc))).trans
      (hq.cfr.trans hp.cfr)
  have cb2 : CondBelow g2 := CF2.below hcb
  -- the merge of the bonds
  have d3' : g3'.drop = false := EC.2.2.1.trans d2
  have hM0 := hM
  generalize hidx : index (Map := Map) (fun e : Nat × Lazy S => e.1) nexq.laz.bond = idx at hM
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
  have idxN : ∀ k, HoonMap.get idx k = Option.none ↔ k ∉ nexq.laz.bond.map Prod.fst := fun k => by
    constructor
    · intro h hk
      obtain ⟨e2, he2, rfl⟩ := List.mem_map.mp hk
      rw [← hidx, get_index_mem (fun e : Nat × Lazy S => e.1) qnd he2] at h; cases h
    · intro h
      rw [← hidx]
      exact get_index_none _ (fun e he x => h (x ▸ List.mem_map_of_mem he))
  have idxS : ∀ k e, HoonMap.get idx k = some e → e ∈ nexq.laz.bond ∧ e.1 = k := fun k e h => by
    rw [← hidx] at h; exact mem_of_get_index _ h
  have rnd : (r.map Prod.fst).Nodup := by rw [er]; exact pnd
  -- the entries of the result
  have resE : ∀ e ∈ (pairRes n r nexq.laz.bond nexp.laz.bond).laz.bond,
      (e ∈ nexp.laz.bond ∧ e.1 ∉ nexq.laz.bond.map Prod.fst) ∨
      (e ∈ nexq.laz.bond ∧ e.1 ∉ nexp.laz.bond.map Prod.fst) ∨
      (∃ e1 ∈ nexp.laz.bond, ∃ e2 ∈ nexq.laz.bond, ∃ (s1 s2 s' : Sure S) (ga gc : Gen Map),
        e1.1 = e.1 ∧ e2.1 = e.1 ∧ e = (e.1, ofSure s') ∧ e1.2 = ofSure s1 ∧ e2.2 = ofSure s2 ∧
        g3'.re ≤ ga.re ∧ gc.re ≤ g3.re ∧ ga.drop = false ∧
        (∀ B fin, HoonMap.get g3'.blocks e.1 = some ⟨[], B, fin⟩ → HoonMap.get ga.blocks e.1 = some ⟨[], B, fin⟩) ∧
        copyLazy e.1 s1 s2 ga = some (s', gc) ∧
        (∀ A, Pref ga gc (fun k => if k = e.1 then A else []) → PM e.1 = A)) := fun e he => by
    rcases mem_pairRes_bond.mp he with h | ⟨h1, h2⟩
    · have hk : e.1 ∈ nexp.laz.bond.map Prod.fst := by rw [← er]; exact List.mem_map_of_mem h
      obtain ⟨e1, he1, ee⟩ := List.mem_map.mp hk
      obtain ⟨i1, i2⟩ := PMi e1 he1
      cases hg1 : HoonMap.get idx e1.1 with
      | none =>
        have := eq_of_label rnd (i1 hg1) h ee
        subst this
        exact Or.inl ⟨he1, (idxN _).mp hg1⟩
      | some m =>
        rcases m with ⟨x, m⟩
        obtain ⟨hm, hx⟩ := idxS _ _ hg1
        have em : m = ofSure m.sure := hqf.2 (x, m) hm
        rw [em] at hg1
        obtain ⟨s1, s', ga, gc, es1, ms, l1, l2, dd, bb, cp', pp⟩ := i2 x m.sure hg1
        have := eq_of_label rnd ms h ee
        refine Or.inr (Or.inr ⟨e1, he1, (x, m), hm, s1, m.sure, s', ga, gc, ee, by rw [← ee, hx], ?_, es1, em,
          l1, l2, dd, ?_, ?_, ?_⟩)
        · rw [← this]
        · rw [← ee]; exact bb
        · rw [← ee]; exact cp'
        · rw [← ee]; exact pp
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
  -- the halves at the goal's entries
  have hedE : ∀ e0 ∈ hed.bond, ∃ eb ∈ L.bond, ∃ sh st, SplitAt (Map := Map) eb hed tel (PB eb.1) g'.re g''.re sh st ∧
      e0 = (eb.1, ofSure sh) := fun e0 h0 => by
    obtain ⟨eb, heb, ee⟩ := List.mem_map.mp (hhl e0 h0)
    obtain ⟨sh, st, SA⟩ := hsp eb heb
    rcases SA.inh with a | ⟨a, _⟩
    · exact ⟨eb, heb, sh, st, SA, eq_of_label hhn h0 a ee.symm⟩
    · exact absurd (by rw [ee]; exact List.mem_map_of_mem h0) a
  have telE : ∀ e0 ∈ tel.bond, ∃ eb ∈ L.bond, ∃ sh st, SplitAt (Map := Map) eb hed tel (PB eb.1) g'.re g''.re sh st ∧
      e0 = (eb.1, ofSure st) := fun e0 h0 => by
    obtain ⟨eb, heb, ee⟩ := List.mem_map.mp (htl e0 h0)
    obtain ⟨sh, st, SA⟩ := hsp eb heb
    rcases SA.int with a | ⟨a, _⟩
    · exact ⟨eb, heb, sh, st, SA, eq_of_label htn h0 a ee.symm⟩
    · exact absurd (by rw [ee]; exact List.mem_map_of_mem h0) a
  -- the registers of the goal entries of the parts
  have regLh : ∀ e0 ∈ entries Lh, ∀ x, NMem e0.2.sure.ned x →
      (∃ e ∈ L.bond, NMem e.2.sure.ned x) ∨ NMem L.sure.ned x ∨ (g0.re ≤ x ∧ x < g''.re) := fun e0 h0 x hx => by
    rcases mLh e0 h0 with h | ⟨rfl, _, _⟩
    · obtain ⟨eb, heb, sh, st, SA, rfl⟩ := hedE e0 h
      rcases SA.mh x hx with a | a
      · exact Or.inl ⟨eb, heb, a⟩
      · exact Or.inr (Or.inr ⟨by omega, a.2⟩)
    · rcases hlp x hx with a | a
      · exact Or.inr (Or.inl a)
      · exact Or.inr (Or.inr ⟨a.1, by omega⟩)
  have regT : ∀ e0 ∈ entries tel, ∀ x, NMem e0.2.sure.ned x →
      (∃ e ∈ L.bond, NMem e.2.sure.ned x) ∨ (g0.re ≤ x ∧ x < g''.re) := fun e0 h0 x hx => by
    rw [eT] at h0
    obtain ⟨eb, heb, sh, st, SA, rfl⟩ := telE e0 h0
    rcases SA.mt x hx with a | a
    · exact Or.inl ⟨eb, heb, a⟩
    · exact Or.inr ⟨by omega, a.2⟩
  -- the parts' result entries' registers
  have regP : ∀ e ∈ nexp.laz.bond, ∀ x, NMem e.2.sure.ned x →
      ((∃ e ∈ L.bond, NMem e.2.sure.ned x) ∨ NMem L.sure.ned x ∨ (g0.re ≤ x ∧ x < g2.re)) := fun e he x hx => by
    rcases (hp.eregs e (by rw [eP]; exact he)).2 x hx with ⟨e0, h0, m0⟩ | h | h
    · rcases regLh e0 h0 x m0 with a | a | a
      · exact Or.inl a
      · exact Or.inr (Or.inl a)
      · exact Or.inr (Or.inr ⟨a.1, by omega⟩)
    · rcases hlp x (hLs' x h) with a | a
      · exact Or.inr (Or.inl a)
      · exact Or.inr (Or.inr ⟨a.1, by omega⟩)
    · exact Or.inr (Or.inr ⟨by omega, h.2⟩)
  have regQ : ∀ e ∈ nexq.laz.bond, ∀ x, NMem e.2.sure.ned x →
      ((∃ e ∈ L.bond, NMem e.2.sure.ned x) ∨ NMem L.sure.ned x ∨ (g0.re ≤ x ∧ x < g1.re)) := fun e he x hx => by
    rcases (hq.eregs e (by rw [eQ]; exact he)).2 x hx with ⟨e0, h0, m0⟩ | h | h
    · rcases regT e0 h0 x m0 with a | a
      · exact Or.inl a
      · exact Or.inr (Or.inr ⟨a.1, by omega⟩)
    · rcases hlq x h with a | a
      · exact Or.inr (Or.inl a)
      · exact Or.inr (Or.inr ⟨a.1, by omega⟩)
    · exact Or.inr (Or.inr ⟨by omega, h.2⟩)
  -- the merged entries: label-local registers from the parts' fronts
  have locP : ∀ eb ∈ L.bond, ∀ sh st, SplitAt (Map := Map) eb hed tel (PB eb.1) g'.re g''.re sh st →
      ∀ e1 ∈ nexp.laz.bond, e1.1 = eb.1 → ∀ x, NMem e1.2.sure.ned x → x < g2.re ∧ (x < g1.re → NMem sh.ned x) := by
    intro eb heb sh st SA e1 he1 ee x hx
    have hlt : eb.1 < g0.bo := labL _ (List.mem_map_of_mem heb)
    have hin : (eb.1, ofSure sh) ∈ entries Lh := by
      rcases SA.inh with a | ⟨a, _⟩
      · rcases hjt with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩
        · rw [eH]; exact a
        · have fl : Flat (mk (Sure.bunt : Sure S) [] ((g''.bo, ofSure hed.sure) :: hed.bond)) :=
            flat_mk (fun e he => by
              rcases List.mem_cons.mp he with h | h
              · rw [h]; rfl
              · exact hhf.2 e h)
          rw [entries_flat fl]
          exact List.mem_cons_of_mem _ a
      · exfalso
        rcases (hp.labs e1 (by rw [eP]; exact he1)).1 with h | h
        · obtain ⟨e0, h0, e0e⟩ := List.mem_map.mp h
          rcases mLh e0 h0 with m | ⟨m, _, _⟩
          · exact a (by rw [← ee, ← e0e]; exact List.mem_map_of_mem m)
          · rw [m] at e0e; simp only at e0e; omega
        · omega
    obtain ⟨F, -, hf⟩ := hp.fs _ hin
    rcases hf g2.cond (fun k _ => rfl) with ⟨L', hm, FS⟩ | ⟨hn, _⟩
    · have : (eb.1, L') = e1 := eq_of_label pnd (by rw [← eP]; exact hm) he1 ee.symm
      subst this
      exact FS.loc x hx
    · exact absurd (by rw [eP, ← ee]; exact List.mem_map_of_mem he1) hn
  have locQ : ∀ eb ∈ L.bond, ∀ sh st, SplitAt (Map := Map) eb hed tel (PB eb.1) g'.re g''.re sh st →
      ∀ e2 ∈ nexq.laz.bond, e2.1 = eb.1 → ∀ x, NMem e2.2.sure.ned x → x < g1.re ∧ (x < gb.re → NMem st.ned x) := by
    intro eb heb sh st SA e2 he2 ee x hx
    have hin : (eb.1, ofSure st) ∈ entries tel := by
      rcases SA.int with a | ⟨a, _⟩
      · rw [eT]; exact a
      · exfalso
        rcases (hq.labs e2 (by rw [eQ]; exact he2)).1 with h | h
        · exact a (by rw [← ee, ← eT]; exact h)
        · have := labL eb.1 (List.mem_map_of_mem heb); omega
    obtain ⟨F, -, hf⟩ := hq.fs _ hin
    rcases hf g1.cond (fun k _ => rfl) with ⟨L', hm, FS⟩ | ⟨hn, _⟩
    · have : (eb.1, L') = e2 := eq_of_label qnd (by rw [← eQ]; exact hm) he2 ee.symm
      subst this
      exact FS.loc x hx
    · exact absurd (by rw [eQ, ← ee]; exact List.mem_map_of_mem he2) hn
  -- the result is flat
  have fR : Flat (pairRes n r nexq.laz.bond nexp.laz.bond).laz := by
    refine flat_mk (fun e he => ?_)
    rcases resE e he with ⟨h, _⟩ | ⟨h, _⟩ | ⟨e1, _, e2, _, s1, s2, s', ga, gc, _, _, ee, _⟩
    · exact hpf.2 e h
    · exact hqf.2 e h
    · rw [ee]; rfl
  have eR : entries (pairRes n r nexq.laz.bond nexp.laz.bond).laz = (pairRes n r nexq.laz.bond nexp.laz.bond).laz.bond :=
    entries_flat fR
  -- the copies at merged labels
  have mergeOK : ∀ (e : Nat × Lazy S), ∀ e1 ∈ nexp.laz.bond, ∀ e2 ∈ nexq.laz.bond, ∀ (s1 s2 s' : Sure S) (ga gc : Gen Map),
      e1.1 = e.1 → e2.1 = e.1 → e1.2 = ofSure s1 → e2.2 = ofSure s2 → g3'.re ≤ ga.re → gc.re ≤ g3.re →
      ga.drop = false → copyLazy e.1 s1 s2 ga = some (s', gc) →
      ∃ (A : List Pole) (gx : Gen Map), Pref ga gc (fun k => if k = e.1 then A else []) ∧
        CopyOK s1.ned s2.ned ga gx s'.ned A ∧ gx.re = gc.re ∧ s'.lok = HoonSet.uni s1.lok s2.lok ∧
        (∀ (Pr : Nat → Prop), NA Pr s1.ned → NA Pr s2.ned → Ple Pr ga.re → RegsIn Pr A) ∧
        RegsIn (· < gc.re) A ∧
        ∃ eb ∈ L.bond, ∃ sh st, SplitAt (Map := Map) eb hed tel (PB eb.1) g'.re g''.re sh st ∧ eb.1 = e.1 ∧
          CopyPre s1.ned s2.ned ga.re ∧
          (∀ x, NMem s1.ned x → x < g2.re ∧ (x < g1.re → NMem sh.ned x)) ∧
          (∀ x, NMem s2.ned x → x < g1.re ∧ (x < gb.re → NMem st.ned x)) := by
    intro e e1 he1 e2 he2 s1 s2 s' ga gc ee1 ee2 es1 es2 l1 l2 dd cpy
    obtain ⟨A, gx, PA, CO, ex, lk, RA, RB⟩ := copyLazy_ok cpy dd
    have hk : e1.1 ∈ L.bond.map Prod.fst := shared e1 he1 e2 he2 (ee1.trans ee2.symm)
    obtain ⟨eb, heb, ebe⟩ := List.mem_map.mp hk
    obtain ⟨sh, st, SA⟩ := hsp eb heb
    have L1 := locP eb heb sh st SA e1 he1 ebe.symm
    have L2 := locQ eb heb sh st SA e2 he2 (ee2.trans (ee1.symm.trans ebe.symm))
    rw [es1] at L1
    rw [es2] at L2
    refine ⟨A, gx, PA, CO, ex, lk, RA, RB (fun x hx => by have := (L1 x hx).1; omega)
      (fun x hx => by have := (L2 x hx).1; omega), eb, heb, sh, st, SA, ebe.trans ee1, ⟨?_, ?_, ⟨?_, ?_, fun x a b => ?_⟩, fun x hx => ?_⟩,
      L1, L2⟩
    · have := hpc e1 (by rw [eP]; exact he1); rw [es1] at this; exact this
    · have := hqc e2 (by rw [eQ]; exact he2); rw [es2] at this; exact this
    · have := (hp.eregs e1 (by rw [eP]; exact he1)).1; rw [es1] at this; exact this
    · have := (hq.eregs e2 (by rw [eQ]; exact he2)).1; rw [es2] at this; exact this
    · obtain ⟨a1, a2⟩ := L1 x a
      obtain ⟨b1', b2'⟩ := L2 x b
      by_cases h : x < gb.re
      · exact SA.ht x (a2 (by omega)) (b2' h)
      · by_cases h' : x < g1.re
        · have := a2 h'
          have := (SA.mh x this)
          rcases this with c | c
          · have := (hLb eb heb).2.2.2 x c; omega
          · omega
        · omega
    · rcases hx with hx | hx
      · have := (L1 x hx).1; omega
      · have := (L2 x hx).1; omega
  have dregR : ∀ s v d w x, pairWitX C HW Qh Qt s v d w → NMem d x → g0.re ≤ x ∧ x < g3.re := by
    intro s v d w x hq' hx
    obtain ⟨vp, vq, dp, dq, wp, wq, rfl, rfl, rfl, qp, qq⟩ := hq'
    rcases hx with hx | hx | hx
    · have := hHr x hx; exact ⟨by omega, by omega⟩
    · have := hp.dreg s vp dp wp x qp hx; exact ⟨by omega, by omega⟩
    · have := hq.dreg s vq dq wq x qq hx; exact ⟨by omega, by omega⟩
  -- blocks of the result's entries
  have blk3 : ∀ k B th', HoonMap.get g2.blocks k = some ⟨[], B, Termin.hop th'⟩ → k < g2.bo →
      ∃ B', HoonMap.get g3.blocks k = some ⟨[], B', Termin.hop th'⟩ := fun k B th' hb hk =>
    ⟨_, PP.blk (by rw [EC.2.2.2 k hk]; exact hb)⟩
  have blkQ : ∀ e ∈ nexq.laz.bond, ∃ B th', HoonMap.get g2.blocks e.1 = some ⟨[], B, Termin.hop th'⟩ := by
    intro e he
    obtain ⟨B, th', hb⟩ := (hq.labs e (by rw [eQ]; exact he)).2
    have hlt : e.1 < g1.bo := by
      rcases lq' e he with a | a
      · have := labL _ a; omega
      · omega
    by_cases hm : e.1 ∈ (entries Lh).map Prod.fst
    · obtain ⟨e0, h0, e0e⟩ := List.mem_map.mp hm
      obtain ⟨F, hF, -⟩ := hp.front e0 h0
      exact ⟨F ++ B, th', by rw [← e0e] at hb ⊢; exact hF B _ hb⟩
    · exact ⟨B, th', by rw [hp.keep _ hlt hm]; exact hb⟩
  have hcase : ∀ x, ¬ FitsS Lh.sure x → ¬ FitsS hed.sure x ∧ TotalC lib P ft := fun x hx => by
    rcases hjt with ⟨_, rfl, hfl⟩ | ⟨_, rfl, _⟩
    · exact ⟨hx, hfl.resolve_left (fun h => hx (h x))⟩
    · exact absurd (fitsS_bunt x) hx
  have NEC : ∀ s, P s → ¬ FitsS n.laz s → NecC lib f (CGoal.next L.sure th) s := by
    intro s hs hf
    by_cases a : FitsS nexp.laz.sure s
    · have b : ¬ FitsS nexq.laz.sure s := fun b => hf ((CF s).mpr ⟨a, b⟩)
      have NQ := hq.nec s hs b
      have HT : TotalC lib P fh := hhd.resolve_left (fun h => b (h s))
      refine ⟨fun gul n tm r hm => ?_, fun gul tm => ?_⟩
      · obtain ⟨n', _, rh, hmh, H⟩ := Mf hs hm
        rcases H with ⟨hnz, rfl⟩ | ⟨x, rfl, rt, hmt, Ht⟩
        · rcases HT.1 s gul n' tm _ hs hmh with e | ⟨y, e⟩
          · exact Or.inl e
          · exact absurd e (hnz y)
        · rcases Ht with ⟨hnz, rfl⟩ | ⟨y, rfl, hfin⟩
          · rcases NQ.1 gul n' tm _ hmt with e | ⟨q, e, _⟩
            · exact Or.inl e
            · exact absurd e (hnz q)
          · rcases NQ.1 gul n' tm _ hmt with e | ⟨q, e, hq'⟩
            · cases e
            · obtain rfl : y = q := by cases e; rfl
              exact hnotF gul n' tm x y r (Or.inr hq') hfin
      · obtain ⟨rh, hmh, hrh⟩ := HT.2 s gul tm hs
        rcases hrh with rfl | ⟨x, rfl⟩
        · exact ⟨_, (Mb hs hmh).1 (fun _ e => by cases e), Or.inl rfl⟩
        · obtain ⟨rt, hmt, hbt⟩ := NQ.2 gul tm
          rcases hbt with rfl | ⟨y, rfl, hy⟩
          · exact ⟨_, ((Mb hs hmh).2 x _ rfl hmt).1 (fun _ e => by cases e), Or.inl rfl⟩
          · obtain ⟨r, hfr, hbr⟩ := hnotB gul tm x y (Or.inr hy)
            exact ⟨r, ((Mb hs hmh).2 x _ rfl hmt).2 y r rfl hfr, hbr⟩
    · have NP := hp.nec s hs a
      refine ⟨fun gul n tm r hm => ?_, fun gul tm => ?_⟩
      · obtain ⟨n', _, rh, hmh, H⟩ := Mf hs hm
        rcases H with ⟨hnz, rfl⟩ | ⟨x, rfl, rt, hmt, Ht⟩
        · rcases NP.1 gul n' tm _ hmh with e | ⟨q, e, _⟩
          · exact Or.inl e
          · exact absurd e (hnz q)
        · rcases NP.1 gul n' tm _ hmh with e | ⟨q, e, hq'⟩
          · cases e
          · obtain rfl : x = q := by cases e; rfl
            obtain ⟨nfx, TT⟩ := hcase x hq'
            rcases Ht with ⟨hnz, rfl⟩ | ⟨y, rfl, hfin⟩
            · rcases TT.1 s gul n' tm _ hs hmt with e | ⟨y, e⟩
              · exact Or.inl e
              · exact absurd e (hnz y)
            · exact hnotF gul n' tm x y r (Or.inl nfx) hfin
      · obtain ⟨rh, hmh, hbh⟩ := NP.2 gul tm
        rcases hbh with rfl | ⟨x, rfl, hx⟩
        · exact ⟨_, (Mb hs hmh).1 (fun _ e => by cases e), Or.inl rfl⟩
        · obtain ⟨nfx, TT⟩ := hcase x hx
          obtain ⟨rt, hmt, hrt⟩ := TT.2 s gul tm hs
          rcases hrt with rfl | ⟨y, rfl⟩
          · exact ⟨_, ((Mb hs hmh).2 x _ rfl hmt).1 (fun _ e => by cases e), Or.inl rfl⟩
          · obtain ⟨r, hfr, hbr⟩ := hnotB gul tm x y (Or.inl nfx)
            exact ⟨r, ((Mb hs hmh).2 x _ rfl hmt).2 y r rfl hfr, hbr⟩
  -- the forward and backward clauses and the fronts
  -- the code of the copy block, the head and the block `o` mention no proxy
  have AC : AboveIn (fun r => HoonMap.get g2.cond r = Option.none) g2.bo g3' :=
    (keepsA_copy (P := fun r => HoonMap.get g2.cond r = Option.none) (first := ⟨nexp.laz.sure, nexp.th⟩) d2
      ⟨hp.ncond, jmpIn_nil (nextArgs_nil hp.ent (nextArgs_nil hq.ent (by
        rcases hjt with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl)))⟩
      (fun r h => by show HoonMap.get g2.cond r = Option.none; rw [hp.cfr.get_lt (lowQ r h)]; exact hq.ncond r h)
      (fun r hr => condBelow_none cb2 hr) hc).1.ab _ (aboveIn_start _ g2)
  have BC : BelowIn g2.bo g3' :=
    (keeps_copy (first := ⟨nexp.laz.sure, nexp.th⟩) d2 ⟨fun r hr => lowP r hr, jmpIn_nil (nextArgs_nil hp.ent
      (nextArgs_nil hq.ent (by rcases hjt with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl)))⟩
      (fun r hr => by have := lowQ r hr; omega) hc).1.bel _ (belowIn_start g2)
  have fixC : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g3.re → HoonMap.get cf k = HoonMap.get g3.cond k) →
      ∀ k, g2.bo ≤ k → k < g3.bo → (HoonMap.get g3.blocks k).map (unproxyBlob cf) = HoonMap.get g3.blocks k := by
    intro cf hcf k h0 h1
    have hk3 : HoonMap.get g3.blocks k = HoonMap.get g3'.blocks k := PP.same (PMo k (Or.inl (fun hm => by
      obtain ⟨e1, he1, rfl⟩ := List.mem_map.mp hm
      rcases lp' e1 he1 with a | ⟨a, a'⟩ | a
      · have := labL _ a; omega
      · omega
      · omega)))
    rw [hk3]
    have u0 : ∀ x, x < g3'.re → unproxy cf x = unproxy g3'.cond x := unproxy_agree (fun k hk => by
      rw [hcf k (by omega), cM])
    have u1 : ∀ x, HoonMap.get g2.cond x = Option.none → unproxy g3'.cond x = id x :=
      fun x hx => unproxy_none (by rw [kc3]; exact hx)
    cases hg : HoonMap.get g3'.blocks k with
    | none => rfl
    | some b =>
      simp only [Option.map_some]
      rw [unproxyBlob, renBlob_congr u0 (BC k b h0 (by omega) hg), renBlob_congr u1 (AC k b h0 (by omega) hg),
        renBlob_id]
  have mid3 : ∀ k, k < g1.bo → k ∉ (entries Lh).map Prod.fst → k ∉ nexp.laz.bond.map Prod.fst →
      HoonMap.get g3.blocks k = HoonMap.get g1.blocks k := fun k hk hn hn' => by
    rw [PP.same (PMo k (Or.inl hn')), EC.2.2.2 k (by omega), hp.keep k hk hn]
  have low3 : ∀ k, g0.bo ≤ k → k < g'.bo → HoonMap.get g3.blocks k = HoonMap.get g'.blocks k := fun k h0 hk => by
    have hnL : k ∉ (entries Lh).map Prod.fst := fun hm => by
      rcases labLh k hm with a | ⟨a, _⟩
      · have := labL _ a; omega
      · omega
    have hnP : k ∉ nexp.laz.bond.map Prod.fst := fun hm => by
      obtain ⟨e1, he1, rfl⟩ := List.mem_map.mp hm
      rcases lp' e1 he1 with a | ⟨a, a'⟩ | a
      · have := labL _ a; omega
      · omega
      · omega
    have hnT : k ∉ (entries tel).map Prod.fst := fun hm => by have := labL _ (labT k hm); omega
    rw [mid3 k (by omega) hnL hnP, hq.keep k (by omega) hnT, hgb.2.2.2 k (by omega), hB.same (hBo k (fun hm => by
      have := labL _ hm; omega))]
  have labR : ∀ k, k ∈ (entries (pairRes n r nexq.laz.bond nexp.laz.bond).laz).map Prod.fst →
      k ∈ nexp.laz.bond.map Prod.fst ∨ k ∈ nexq.laz.bond.map Prod.fst := fun k hk => by
    rw [eR] at hk
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
    rcases mem_pairRes_bond.mp he with h | ⟨h, _⟩
    · exact Or.inl (by rw [← er]; exact List.mem_map_of_mem h)
    · exact Or.inr (List.mem_map_of_mem h)
  -- the result's entries at the goal's labels are apart from the goal registers the fronts read
  have hLEg : ∀ e ∈ entries (pairRes n r nexq.laz.bond nexp.laz.bond).laz, e.1 ∈ (entries L).map Prod.fst →
      ∀ z, NMem (gsE x L) z → ¬ NMem e.2.sure.ned z := by
    intro e he hl z hz hm
    rw [eR] at he
    rw [eL] at hl
    obtain ⟨eb, heb, ebe⟩ := List.mem_map.mp hl
    have hz0 : z < g0.re := by
      cases x
      · exact hz.elim
      · exact gm z hz
    have hz' : NMem HW z ∨ NMem (gsE xp Lh) z ∨ NMem (gsE xq tel) z ∨ NMem (gsE x L) z := Or.inr (Or.inr (Or.inr hz))
    rcases resE e he with ⟨h1, _⟩ | ⟨h1, _⟩ |
        ⟨e1, he1, e2, he2, s1, s2, s', ga, gc, ee1, ee2, ee, es1, es2, l1, l2, dd, bb, cpy, pp⟩
    · exact hPH eb heb e (List.mem_append_left _ h1) ebe.symm z hz' hm
    · exact hPH eb heb e (List.mem_append_right _ h1) ebe.symm z hz' hm
    · obtain ⟨A, gx, PA, CO, ex, lk, RA, RB⟩ := copyLazy_ok cpy dd
      rw [ee] at hm
      rcases CO.mem z (by simpa [ofSure] using hm) with (a | a) | ⟨a, a'⟩
      · exact hPH eb heb e1 (List.mem_append_left _ he1) (ee1.trans ebe.symm) z hz' (by rw [es1]; simpa [ofSure] using a)
      · exact hPH eb heb e2 (List.mem_append_right _ he2) (ee2.trans ebe.symm) z hz' (by rw [es2]; simpa [ofSure] using a)
      · omega
  -- the shared part of the two `sem` clauses
  have core := pairLSX_core (Mf := Mf) (Mb := Mb) (hFin := hFin) (hFinB := hFinB) (hLf := hLf) (hLn := hLn) (hLc := hLc) (hLb := hLb) (hg := hg) (hpre := hpre) (hgr := hgr) (hcnd := hcnd) (hcb := hcb) (hlp := hlp) (hlq := hlq) (hpq := hpq) (hB := hB) (hBo := hBo) (hhf := hhf) (htf := htf) (hsp := hsp) (hhl := hhl) (htl := htl) (hhn := hhn) (htn := htn) (hgb := hgb) (hgbU := hgbU) (hgbc := hgbc) (hgbre := hgbre) (hjt := hjt) (hhd := hhd) (hq := hq) (hp := hp) (hqf := hqf) (hpf := hpf) (hqc := hqc) (hpc := hpc) (cq := cq) (cp := cp) (hc := hc) (hu := hu) (d0 := d0) (hfix := hfix) (hnotF := hnotF) (hnotB := hnotB) (hA := hA) (hAB := hAB) (hHr := hHr) (hHh := hHh) (hEH := hEH) (hG := hG) (hPH := hPH) (hM := hM0) (hidx := hidx) (P0 := P0) (d2 := d2) (d3' := d3') (pnd := pnd) (eP := eP) (lp' := lp') (labL := labL) (eQ := eQ) (hLs' := hLs') (labLh := labLh) (labT := labT) (lq' := lq') (lpl := lpl) (lql := lql) (mp := mp) (mq := mq) (lowP := lowP) (lowQ := lowQ) (idxN := idxN) (eR := eR) (fixC := fixC) (mid3 := mid3) (low3 := low3) (labR := labR)
  have SEM := pairLSX_sem (Mf := Mf) (Mb := Mb) (hFin := hFin) (hFinB := hFinB) (hLf := hLf) (hLn := hLn) (hLc := hLc) (hLb := hLb) (hg := hg) (hpre := hpre) (hgr := hgr) (hcnd := hcnd) (hcb := hcb) (hlp := hlp) (hlq := hlq) (hpq := hpq) (hB := hB) (hBo := hBo) (hhf := hhf) (htf := htf) (hsp := hsp) (hhl := hhl) (htl := htl) (hhn := hhn) (htn := htn) (hgb := hgb) (hgbU := hgbU) (hgbc := hgbc) (hgbre := hgbre) (hjt := hjt) (hhd := hhd) (hq := hq) (hp := hp) (hqf := hqf) (hpf := hpf) (hqc := hqc) (hpc := hpc) (cq := cq) (cp := cp) (hc := hc) (hu := hu) (d0 := d0) (hfix := hfix) (hnotF := hnotF) (hnotB := hnotB) (hA := hA) (hAB := hAB) (hHr := hHr) (hHh := hHh) (hEH := hEH) (hG := hG) (hPH := hPH) (hM := hM0) (hidx := hidx) (P0 := P0) (d2 := d2) (d3' := d3') (pnd := pnd) (eP := eP) (lp' := lp') (labL := labL) (gm := gm) (hcase := hcase) (core := core)
  have SEMB := pairLSX_semB (Mf := Mf) (Mb := Mb) (hFin := hFin) (hFinB := hFinB) (hLf := hLf) (hLn := hLn) (hLc := hLc) (hLb := hLb) (hg := hg) (hpre := hpre) (hgr := hgr) (hcnd := hcnd) (hcb := hcb) (hlp := hlp) (hlq := hlq) (hpq := hpq) (hB := hB) (hBo := hBo) (hhf := hhf) (htf := htf) (hsp := hsp) (hhl := hhl) (htl := htl) (hhn := hhn) (htn := htn) (hgb := hgb) (hgbU := hgbU) (hgbc := hgbc) (hgbre := hgbre) (hjt := hjt) (hhd := hhd) (hq := hq) (hp := hp) (hqf := hqf) (hpf := hpf) (hqc := hqc) (hpc := hpc) (cq := cq) (cp := cp) (hc := hc) (hu := hu) (d0 := d0) (hfix := hfix) (hnotF := hnotF) (hnotB := hnotB) (hA := hA) (hAB := hAB) (hHr := hHr) (hHh := hHh) (hEH := hEH) (hG := hG) (hPH := hPH) (hM := hM0) (hidx := hidx) (P0 := P0) (d2 := d2) (d3' := d3') (pnd := pnd) (eP := eP) (lp' := lp') (labL := labL) (gm := gm) (hcase := hcase) (core := core)
  have FS := pairLSX_fronts (Mf := Mf) (Mb := Mb) (hFin := hFin) (hFinB := hFinB) (hLf := hLf) (hLn := hLn) (hLc := hLc) (hLb := hLb) (hg := hg) (hpre := hpre) (hgr := hgr) (hcnd := hcnd) (hcb := hcb) (hlp := hlp) (hlq := hlq) (hpq := hpq) (hB := hB) (hBo := hBo) (hhf := hhf) (htf := htf) (hsp := hsp) (hhl := hhl) (htl := htl) (hhn := hhn) (htn := htn) (hgb := hgb) (hgbU := hgbU) (hgbc := hgbc) (hgbre := hgbre) (hjt := hjt) (hhd := hhd) (hq := hq) (hp := hp) (hqf := hqf) (hpf := hpf) (hqc := hqc) (hpc := hpc) (cq := cq) (cp := cp) (hc := hc) (hu := hu) (d0 := d0) (hfix := hfix) (hnotF := hnotF) (hnotB := hnotB) (hA := hA) (hAB := hAB) (hHr := hHr) (hHh := hHh) (hEH := hEH) (hG := hG) (hPH := hPH) (hM := hM0) (hidx := hidx) (P0 := P0) (d2 := d2) (d3' := d3') (pnd := pnd) (eP := eP) (lp' := lp') (labL := labL) (eL := eL) (eH := eH) (eT := eT) (eQ := eQ) (mLh := mLh) (qnd := qnd) (cb2 := cb2) (idxN := idxN) (eR := eR) (mergeOK := mergeOK)
  refine ⟨{
    re := by omega
    bo := by omega
    drop := by rw [PP.drop, EC.2.2.1, d2, d0]
    keep := fun k hk hn => ?_
    grow := G2.trans ((Dc.grow.toU u2).trans PP.growU)
    cfr := CF2.trans ((condFresh_of_eq EC.1 kc3).trans PP.condFresh)
    lo := Dc.lo
    hi := by show n.th.there < g3.bo; rw [bM]; exact Dc.hi
    ent := PP.entry Dc.entry
    regs := fun x hx => ?_
    dist := CD
    eregs := fun e he => ?_
    labs := fun e he => ?_
    nodup := ?_
    dreg := dregR
    nec := NEC
    ncond := fun x hx => ?_
    econd := fun e he x hx => ?_
    front := FS.toFrontG (by omega) (fun x hx => gm x hx) hLEg dregR
    sem := SEM
    semB := SEMB
    fs := FS }, by rw [eth]; simp only [jmp0]; omega, eth, fR, fun e he => ?_, fun e he => ?_⟩
  · -- keep
    have hk' : k ∉ (entries Lh).map Prod.fst := fun hm => by
      rcases labLh k hm with a | ⟨a, _⟩
      · rw [eL] at hn; exact hn a
      · omega
    have hkt : k ∉ (entries tel).map Prod.fst := fun hm => by rw [eL] at hn; exact hn (labT k hm)
    have hkp : k ∉ nexp.laz.bond.map Prod.fst := fun hm => by
      obtain ⟨e1, he1, rfl⟩ := List.mem_map.mp hm
      rcases lp' e1 he1 with a | ⟨a, _⟩ | a
      · rw [eL] at hn; exact hn a
      · omega
      · omega
    rw [PP.same (PMo k (Or.inl hkp)), EC.2.2.2 k (by omega), hp.keep k (by omega) hk',
      hq.keep k (by omega) hkt, hgb.2.2.2 k (by omega), hB.same (hBo k (by rw [eL] at hn; exact hn)),
      hpre.2.2.2 k hk]
  · -- regs
    rcases CM x hx with h | h | ⟨h, h'⟩
    · rcases mp x h with a | ⟨a, a'⟩
      · rcases hlp x a with b | ⟨b, b'⟩
        · exact Or.inl b
        · exact Or.inr ⟨b, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    · rcases mq x h with a | ⟨a, a'⟩
      · rcases hlq x a with b | ⟨b, b'⟩
        · exact Or.inl b
        · exact Or.inr ⟨b, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  · -- eregs
    rw [eR] at he
    rcases resE e he with ⟨h, _⟩ | ⟨h, _⟩ | ⟨e1, he1, e2, he2, s1, s2, s', ga, gc, ee1, ee2, ee, es1, es2, l1, l2, dd, -, cpy, -⟩
    · refine ⟨(hp.eregs e (by rw [eP]; exact h)).1, fun x hx => ?_⟩
      rcases regP e h x hx with ⟨e0, h0, m0⟩ | a | a
      · exact Or.inl ⟨e0, by rw [eL]; exact h0, m0⟩
      · exact Or.inr (Or.inl a)
      · exact Or.inr (Or.inr ⟨a.1, by omega⟩)
    · refine ⟨(hq.eregs e (by rw [eQ]; exact h)).1, fun x hx => ?_⟩
      rcases regQ e h x hx with ⟨e0, h0, m0⟩ | a | a
      · exact Or.inl ⟨e0, by rw [eL]; exact h0, m0⟩
      · exact Or.inr (Or.inl a)
      · exact Or.inr (Or.inr ⟨a.1, by omega⟩)
    · obtain ⟨A, gx, PA, CO, ex, lk, -, -, eb, heb, sh, st, SA, ebe, CP, L1, L2⟩ :=
        mergeOK e e1 he1 e2 he2 s1 s2 s' ga gc ee1 ee2 es1 es2 l1 l2 dd cpy
      obtain ⟨D, -, -, -⟩ := CO.sem CP
      rw [ee]
      refine ⟨D, fun x hx => ?_⟩
      rcases CO.mem x hx with (a | a) | ⟨a, a'⟩
      · rcases regP e1 he1 x (by rw [es1]; exact a) with ⟨e0, h0, m0⟩ | b | b
        · exact Or.inl ⟨e0, by rw [eL]; exact h0, m0⟩
        · exact Or.inr (Or.inl b)
        · exact Or.inr (Or.inr ⟨b.1, by omega⟩)
      · rcases regQ e2 he2 x (by rw [es2]; exact a) with ⟨e0, h0, m0⟩ | b | b
        · exact Or.inl ⟨e0, by rw [eL]; exact h0, m0⟩
        · exact Or.inr (Or.inl b)
        · exact Or.inr (Or.inr ⟨b.1, by omega⟩)
      · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
  · -- labs
    rw [eR] at he
    rcases resE e he with ⟨h, _⟩ | ⟨h, _⟩ | ⟨e1, he1, e2, he2, s1, s2, s', ga, gc, ee1, ee2, ee, -⟩
    · obtain ⟨B, th', hb⟩ := (hp.labs e (by rw [eP]; exact h)).2
      have hlt : e.1 < g2.bo := by
        rcases lp' e h with a | ⟨a, a'⟩ | a
        · have := labL _ a; omega
        · omega
        · omega
      obtain ⟨B', hb'⟩ := blk3 _ _ _ hb hlt
      refine ⟨?_, B', th', hb'⟩
      rcases lp' e h with a | ⟨a, a'⟩ | a
      · rw [eL]; exact Or.inl a
      · exact Or.inr ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    · obtain ⟨B, th', hb⟩ := blkQ e h
      have hlt : e.1 < g1.bo := by
        rcases lq' e h with a | a
        · have := labL _ a; omega
        · omega
      obtain ⟨B', hb'⟩ := blk3 _ _ _ hb (by omega)
      refine ⟨?_, B', th', hb'⟩
      rcases lq' e h with a | a
      · rw [eL]; exact Or.inl a
      · exact Or.inr ⟨by omega, by omega⟩
    · have hk : e1.1 ∈ L.bond.map Prod.fst := shared e1 he1 e2 he2 (ee1.trans ee2.symm)
      obtain ⟨B, th', hb⟩ := (hp.labs e1 (by rw [eP]; exact he1)).2
      obtain ⟨B', hb'⟩ := blk3 _ _ _ hb (by have := labL _ hk; omega)
      rw [ee1] at hk hb'
      exact ⟨by rw [eL]; exact Or.inl hk, B', th', hb'⟩
  · -- nodup
    rw [eR]
    show ((r ++ nexq.laz.bond.filter fun e => !(seen (S := S) (fun e : Nat × Lazy S => e.1) nexp.laz.bond e.1)).map
      Prod.fst).Nodup
    rw [List.map_append, List.nodup_append]
    refine ⟨rnd, qnd.sublist (List.Sublist.map _ List.filter_sublist), fun a ha b hb e => ?_⟩
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp hb
    obtain ⟨-, hs⟩ := List.mem_filter.mp he'
    have hn : e'.1 ∉ nexp.laz.bond.map Prod.fst := fun hm => by
      rw [(seen_iff (S := S) _ _ _).mpr hm] at hs; cases hs
    rw [er] at ha
    exact hn (e ▸ ha)
  · -- ncond
    rw [cM, kc3]
    rcases CM x hx with h | h | ⟨h, h'⟩
    · exact hp.ncond x h
    · rw [hp.cfr.get_lt (lowQ x h)]; exact hq.ncond x h
    · exact condBelow_none cb2 h
  · -- econd
    rw [cM, kc3]
    rw [eR] at he
    rcases resE e he with ⟨h, _⟩ | ⟨h, _⟩ | ⟨e1, he1, e2, he2, s1, s2, s', ga, gc, ee1, ee2, ee, es1, es2, l1, l2, dd, -, cpy, -⟩
    · exact hp.econd e (by rw [eP]; exact h) x hx
    · have hlt : x < g1.re := by
        rcases (hq.eregs e (by rw [eQ]; exact h)).2 x hx with ⟨e0, h0, m0⟩ | a | a
        · rcases regT e0 h0 x m0 with ⟨eb, heb, mb⟩ | b
          · have := (hLb eb heb).2.2.2 x mb; omega
          · omega
        · have := lql x a; omega
        · omega
      rw [hp.cfr.get_lt hlt]
      exact hq.econd e (by rw [eQ]; exact h) x hx
    · obtain ⟨A, gx, PA, CO, ex, lk, -, -, eb, heb, sh, st, SA, ebe, CP, L1, L2⟩ :=
        mergeOK e e1 he1 e2 he2 s1 s2 s' ga gc ee1 ee2 es1 es2 l1 l2 dd cpy
      rw [ee] at hx
      rcases CO.mem x hx with (a | a) | ⟨a, a'⟩
      · exact hp.econd e1 (by rw [eP]; exact he1) x (by rw [es1]; exact a)
      · rw [hp.cfr.get_lt (L2 x a).1]
        exact hq.econd e2 (by rw [eQ]; exact he2) x (by rw [es2]; exact a)
      · exact condBelow_none cb2 (by omega)
  · -- the result's entries are clean
    rw [eR] at he
    rcases resE e he with ⟨h, _⟩ | ⟨h, _⟩ | ⟨e1, he1, e2, he2, s1, s2, s', ga, gc, ee1, ee2, ee, es1, es2, -, -, -, -, cpy, -⟩
    · exact hpc e (by rw [eP]; exact h)
    · exact hqc e (by rw [eQ]; exact h)
    · rw [ee]
      have c1 := hpc e1 (by rw [eP]; exact he1)
      have c2 := hqc e2 (by rw [eQ]; exact he2)
      rw [es1] at c1; rw [es2] at c2
      exact clean_copyLazy cpy c1 c2
  · -- the result's labels lie below the copy block
    rw [eR] at he
    rcases resE e he with ⟨h, _⟩ | ⟨h, _⟩ | ⟨e1, he1, e2, he2, s1, s2, s', ga, gc, ee1, ee2, ee, -⟩
    · rcases lp' e h with a | ⟨a, a'⟩ | a
      · have := labL _ a; omega
      · omega
      · omega
    · rcases lq' e h with a | a
      · have := labL _ a; omega
      · omega
    · rw [← ee1]
      rcases lp' e1 he1 with a | ⟨a, a'⟩ | a
      · have := labL _ a; omega
      · omega
      · omega

end Comp
end SkaModel
end Formalization
