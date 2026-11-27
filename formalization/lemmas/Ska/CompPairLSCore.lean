import lemmas.Ska.CompFlatCopy

/-!
# A pair of runs under a flat lazy goal with entries: the shared part

README Gaps 12.24.  The first of the three files of `pairLS_ok`
(`CompPairLS.lean`, see its header): the data of the parent's split at a goal
entry (`SplitAt`), the result of the pair (`pairRes`), and `pairLS_core`, the
part that the two `sem` clauses share (from the registers at the copy block to
those at the head's start, to those at the tail's start, to those at the block
`o`).  The hypotheses of `pairLS_ok` are the section's variables; the facts
that its proof derives first are hypotheses of the lemma.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]


/-- **What the parent's split did at one goal entry** `e = (b, ofSure sb)`:
the halves `sh`, `st` (each kept as the half's bond at `b`, or pruned and
asking nothing), their registers (the entry's or allocated in `[lo, hi)`),
their shape, and the ops `A` in front of `b` that build `sb` from them. -/
structure SplitAt (e : Nat × Lazy S) (hed tel : Lazy S) (A : List Pole) (lo hi : Nat) (sh st : Sure S) : Prop where
  sure : e.2 = ofSure e.2.sure
  inh : (e.1, ofSure sh) ∈ hed.bond ∨ (e.1 ∉ hed.bond.map Prod.fst ∧ sh.ned = Need.none ∧ HoonSet.small sh.lok = true)
  int : (e.1, ofSure st) ∈ tel.bond ∨ (e.1 ∉ tel.bond.map Prod.fst ∧ st.ned = Need.none ∧ HoonSet.small st.lok = true)
  mh : ∀ y, NMem sh.ned y → NMem e.2.sure.ned y ∨ (lo ≤ y ∧ y < hi)
  mt : ∀ y, NMem st.ned y → NMem e.2.sure.ned y ∨ (lo ≤ y ∧ y < hi)
  dh : Distinct sh.ned
  dt : Distinct st.ned
  ht : ∀ y, NMem sh.ned y → ¬ NMem st.ned y
  ch : Clean sh.ned
  ct : Clean st.ned
  fit : ∀ a b, FitsS e.2.sure (C a b) ↔ FitsS sh a ∧ FitsS st b
  regs : RegsIn (fun x => NMem e.2.sure.ned x ∨ (lo ≤ x ∧ x < hi)) A
  sem : ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st' : σ) (t : Trace)
    (R : Map (Option Noun)) (a b : Noun), HoldsN sh.ned R a → HoldsN st.ned R b →
    ∃ R', Runs lib O c gul st' t A R R' ∧ HoldsN e.2.sure.ned R' (C a b) ∧
      ∀ y, ¬ NMem e.2.sure.ned y → SkaModel.read y R' = SkaModel.read y R


theorem eq_of_label {l : List (Nat × Lazy S)} (h : (l.map Prod.fst).Nodup) {a b : Nat × Lazy S} (ha : a ∈ l)
    (hb : b ∈ l) (e : a.1 = b.1) : a = b := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    have h' : x.1 ∉ xs.map Prod.fst ∧ (xs.map Prod.fst).Nodup := List.nodup_cons.mp h
    rcases List.mem_cons.mp ha with h1 | h1 <;> rcases List.mem_cons.mp hb with h2 | h2
    · rw [h1, h2]
    · exact absurd (by rw [← h1, e]; exact List.mem_map_of_mem h2) h'.1
    · exact absurd (by rw [← h2, ← e]; exact List.mem_map_of_mem h1) h'.1
    · exact ih h'.2 h1 h2

section
variable {lib : Lib} {N : Needs} {σ : Type} {Inv : σ → Prop} {ν : σ → Needs} {O : Oracle σ} {c : Straight Map} {gul : Noun}

/-- **`GoalSemCM` with a witness kept by the code**: `GoalSemCMD`. -/
theorem goalSemCMD_of_CM {K : Nat → Prop} {st : σ} {regs : Map (Option Noun)} {t tm : Trace} {je : Jmp}
    {sur : Sure S} {th : Jmp} {Q : Noun → Need → Noun → Prop} {d : Need} {w : Noun} (hd : ∀ z, NMem d z → K z)
    (hw : HoldsN d regs w) :
    ∀ {r : Tone}, (∀ p, r = Tone.zero p → Q p d w) →
      GoalSemCM lib O c gul Inv ν K st regs t tm je (CGoal.next sur th) r →
      GoalSemCMD lib O c gul Inv ν K st regs t tm je sur th Q r
  | Tone.zero p, hq, H => ⟨fun f => by
      obtain ⟨st', R, hI, hle, h1, h3, h4⟩ := H.1 f
      exact ⟨st', R, d, w, hI, hle, hq p rfl, h1, HoldsN.agree d (fun z hz => h3 z (hd z hz)) hw, h3, h4⟩, H.2⟩
  | Tone.one _, _, H => H
  | Tone.two _, _, H => H

/-- A tone that is a failure for a `%next` goal, where the code crashed. -/
theorem goalSemCMD_bad {K : Nat → Prop} {st : σ} {regs : Map (Option Noun)} {t tm : Trace} {je : Jmp}
    {sur : Sure S} {th : Jmp} {Q : Noun → Need → Noun → Prop} {r : Tone} (hb : BadC (CGoal.next sur th) tm r)
    (H : ReturnsC lib O c gul Inv ν st regs t je (Tone.two tm)) :
    GoalSemCMD lib O c gul Inv ν K st regs t tm je sur th Q r := by
  rcases hb with rfl | ⟨p, rfl, hp⟩
  · exact H
  · exact ⟨fun f => absurd f hp, fun _ => H⟩

end

theorem copySem_left_nil (l : Need) : CopySem Map l Need.none l [] :=
  fun lib σ O c gul st t R s hs => ⟨R, Runs.nil R, hs, trivial, fun _ _ => rfl⟩

theorem copySem_right_nil (r : Need) : CopySem Map Need.none r r [] :=
  fun lib σ O c gul st t R s hs => ⟨R, Runs.nil R, trivial, hs, fun _ _ => rfl⟩

/-- The result of the pair: the copy's sure need, the merged bonds, then the
tail's bonds whose label the head's result has not. -/
def pairRes (n : Next S) (r bq bp : List (Nat × Lazy S)) : NextL S :=
  ⟨mk n.laz [] (r ++ bq.filter fun e => !(seen (S := S) (fun e : Nat × Lazy S => e.1) bp e.1)), n.th⟩

theorem mem_pairRes_bond {n : Next S} {r bq bp : List (Nat × Lazy S)} {e : Nat × Lazy S} :
    e ∈ (pairRes n r bq bp).laz.bond ↔ e ∈ r ∨ (e ∈ bq ∧ e.1 ∉ bp.map Prod.fst) := by
  simp only [pairRes, bond_mk, List.mem_append, List.mem_filter, Bool.not_eq_true']
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · refine Or.inr ⟨h1, fun hm => ?_⟩
      rw [(seen_iff (S := S) _ _ _).mpr hm] at h2; cases h2
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · refine Or.inr ⟨h1, ?_⟩
      cases hs : seen (S := S) (fun e : Nat × Lazy S => e.1) bp e.1
      · rfl
      · exact absurd ((seen_iff (S := S) _ _ _).mp hs) h2

section

variable {lib : Lib} {N : Needs} {P : Noun → Prop} {f fh ft : Noun} {L : Lazy S} {th : Jmp}
    {g0 g' g'' gb g1 g2 g3' g3 : Gen Map} {hed tel Lh : Lazy S} {o : Nat} {jt : Jmp} {Qh Qt : Wit}
    {nexq nexp : NextL S} {n : Next S} {r : List (Nat × Lazy S)} {PB : Nat → List Pole}
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
    (hq : RunOKLS (Map := Map) lib N P ft tel jt Qt false gb g1 nexq)
    (hp : RunOKLS (Map := Map) lib N P fh Lh nexq.th Qh false g1 g2 nexp)
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
        GoalSemCM lib O c gul Inv ν (Keep g0 g' (CGoal.next L.sure th)) st regs t tm (jmp0 o) (CGoal.next L.sure th) r)
    (hAB : ∀ (c : Straight Map), Agree c g0 g' → ∀ (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ)
      (gul : Noun), OracleSteps Inv ν O → OracleBwd lib Inv ν O →
      ∀ (st : σ) (regs : Map (Option Noun)) (t tm : Trace) (x y : Noun), Inv st →
        Forall2 (FrameRel lib (ν st)) t tm → FitsS hed.sure x → FitsS tel.sure y → HoldsN hed.sure.ned regs x →
        HoldsN tel.sure.ned regs y → ∀ res, goJ lib O c gul st regs t (jmp0 o) = some res →
        ∃ r, FinB gul tm x y r ∧
          GoalSemCM lib O c gul Inv ν (Keep g0 g' (CGoal.next L.sure th)) st regs t tm (jmp0 o) (CGoal.next L.sure th) r)

include Mf Mb hFin hFinB hLf hLn hLc hLb hg hpre hgr hcnd hcb hlp hlq hpq hB hBo hhf htf hsp hhl htl hhn htn hgb hgbU hgbc hgbre hjt hhd hq hp hqf hpf hqc hpc cq cp hc hM hu d0 hfix hnotF hnotB hA hAB

/-- The shared part of the two `sem` clauses of `pairLS_ok`. -/
theorem pairLS_core {idx : Map (Nat × Lazy S)}
    (hidx : index (Map := Map) (fun e : Nat × Lazy S => e.1) nexq.laz.bond = idx)
    (P0 : CopyPre nexp.laz.sure.ned nexq.laz.sure.ned g2.re)
    (d2 : g2.drop = false)
    (d3' : g3'.drop = false)
    (pnd : (nexp.laz.bond.map Prod.fst).Nodup)
    (eP : entries nexp.laz = nexp.laz.bond)
    (lp' : ∀ e ∈ nexp.laz.bond, (e.1 ∈ L.bond.map Prod.fst ∨ (e.1 = g''.bo ∧ g''.bo < gb.bo) ∨
      (g1.bo ≤ e.1 ∧ e.1 < g2.bo)))
    (labL : ∀ k, k ∈ L.bond.map Prod.fst → k < g0.bo)
    (eQ : entries nexq.laz = nexq.laz.bond)
    (hLs' : ∀ r, NMem Lh.sure.ned r → NMem hed.sure.ned r)
    (labLh : ∀ k, k ∈ (entries Lh).map Prod.fst → k ∈ L.bond.map Prod.fst ∨ (k = g''.bo ∧ g''.bo < gb.bo))
    (labT : ∀ k, k ∈ (entries tel).map Prod.fst → k ∈ L.bond.map Prod.fst)
    (lq' : ∀ e ∈ nexq.laz.bond, (e.1 ∈ L.bond.map Prod.fst ∨ (gb.bo ≤ e.1 ∧ e.1 < g1.bo)))
    (lpl : ∀ r, NMem hed.sure.ned r → r < g'.re)
    (lql : ∀ r, NMem tel.sure.ned r → r < g'.re)
    (mp : ∀ r, NMem nexp.laz.sure.ned r → NMem hed.sure.ned r ∨ (g1.re ≤ r ∧ r < g2.re))
    (mq : ∀ r, NMem nexq.laz.sure.ned r → NMem tel.sure.ned r ∨ (gb.re ≤ r ∧ r < g1.re))
    (lowP : ∀ r, NMem nexp.laz.sure.ned r → r < g2.re)
    (lowQ : ∀ r, NMem nexq.laz.sure.ned r → r < g1.re)
    (idxN : ∀ k, HoonMap.get idx k = Option.none ↔ k ∉ nexq.laz.bond.map Prod.fst)
    (eR : entries (pairRes n r nexq.laz.bond nexp.laz.bond).laz = (pairRes n r nexq.laz.bond nexp.laz.bond).laz.bond)
    (fixC : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g3.re → HoonMap.get cf k = HoonMap.get g3.cond k) →
      ∀ k, g2.bo ≤ k → k < g3.bo → (HoonMap.get g3.blocks k).map (unproxyBlob cf) = HoonMap.get g3.blocks k)
    (mid3 : ∀ k, k < g1.bo → k ∉ (entries Lh).map Prod.fst → k ∉ nexp.laz.bond.map Prod.fst →
      HoonMap.get g3.blocks k = HoonMap.get g1.blocks k)
    (low3 : ∀ k, g0.bo ≤ k → k < g'.bo → HoonMap.get g3.blocks k = HoonMap.get g'.blocks k)
    (labR : ∀ k, k ∈ (entries (pairRes n r nexq.laz.bond nexp.laz.bond).laz).map Prod.fst →
      k ∈ nexp.laz.bond.map Prod.fst ∨ k ∈ nexq.laz.bond.map Prod.fst) :
    ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g3.re → HoonMap.get cf k = HoonMap.get g3.cond k) →
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
            (¬ FitsS hed.sure x → goJ lib O c gul st2 R3 t jt = some (Tone.two t, st2)) := by
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
  intro cf hcf c ned σ O gul st t s0 s ag hned regs hh hn
  have hcf2 : ∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g2.cond k := fun k hk =>
    (hcf k (by omega)).trans (by rw [cM, kc3])
  have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk =>
    (hcf2 k (by omega)).trans (hp.cfr.get_lt hk)
  have hcf0 : ∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g0.cond k := fun k hk =>
    (hcf1 k (by omega)).trans ((hq.cfr.get_lt (by omega)).trans (by rw [hgbc, hB.cond, hcnd]))
  have agC : Agree c g2 g3' := fun k h0 h1 => by
    have hnk : k ∉ (entries (pairRes n r nexq.laz.bond nexp.laz.bond).laz).map Prod.fst := fun hm => by
      rcases labR k hm with a | a
      · obtain ⟨e1, he1, rfl⟩ := List.mem_map.mp a
        rcases lp' e1 he1 with b | ⟨b, b'⟩ | b
        · have := labL _ b; omega
        · omega
        · omega
      · obtain ⟨e2, he2, rfl⟩ := List.mem_map.mp a
        rcases lq' e2 he2 with b | b
        · have := labL _ b; omega
        · omega
    rw [(ag st).1 k (by omega) (by omega) hnk]
    have := fixC cf hcf k h0 (by omega)
    rw [this, PP.same (PMo k (Or.inl (fun hm => by
      obtain ⟨e1, he1, rfl⟩ := List.mem_map.mp hm
      rcases lp' e1 he1 with a | ⟨a, a'⟩ | a
      · have := labL _ a; omega
      · omega
      · omega)))]
  obtain ⟨R1, hs1, hs1', u1, e1⟩ := CB d2 c agC lib σ O st regs t gul s hh
  have hned2 : ∀ r, NMem ned r → g2.re ≤ r := fun r hr => by have := hned r hr; omega
  have hn1 : HoldsN ned R1 s0 := HoldsN.agree _ (fun r hr => u1 r (fun hm => by
    have := lowP r hm; have := hned r hr; omega) (fun hm => by have := lowQ r hm; have := hned r hr; omega)) hn
  have agP : ∀ st' : σ, AgreeLB lib O c gul st' t cf ned g1 g2 nexp.laz s0 s := fun st' => by
    refine ⟨fun k h0 h1 hn' => ?_, fun e he l => ?_⟩
    · have hn'' : k ∉ nexp.laz.bond.map Prod.fst := by rw [← eP]; exact hn'
      have hnk : k ∉ (entries (pairRes n r nexq.laz.bond nexp.laz.bond).laz).map Prod.fst := fun hm => by
        rcases labR k hm with a | a
        · exact hn'' a
        · obtain ⟨e2, he2, rfl⟩ := List.mem_map.mp a
          rcases lq' e2 he2 with b | b
          · have := labL _ b; omega
          · omega
      rw [(ag st').1 k (by omega) (by omega) hnk, PP.same (PMo k (Or.inl hn'')), EC.2.2.2 k h1]
    · rw [eP] at he
      have hnq : e.1 ∉ nexq.laz.bond.map Prod.fst := fun hm => by
        obtain ⟨e2, he2, ee⟩ := List.mem_map.mp hm
        rcases lq' e2 he2 with b | b
        · have := labL _ b; omega
        · omega
      have hidx0 : HoonMap.get idx e.1 = Option.none := (idxN e.1).mpr hnq
      have hr : e ∈ (pairRes n r nexq.laz.bond nexp.laz.bond).laz.bond :=
        mem_pairRes_bond.mpr (Or.inl ((PMi e he).1 hidx0))
      obtain ⟨A, B, th', b3, c3, f3⟩ := (ag st').2 e (by rw [eR]; exact hr) (by omega)
      have e2 : HoonMap.get g3.blocks e.1 = HoonMap.get g2.blocks e.1 := by
        rw [PP.same (PMo e.1 (Or.inr hidx0)), EC.2.2.2 e.1 (by
          rcases lp' e he with a | ⟨a, a'⟩ | a
          · have := labL _ a; omega
          · omega
          · omega)]
      exact ⟨A, B, th', by rw [← e2]; exact b3, c3, f3.mono (by omega)⟩
  have agQ0 : Agree c g0 g' := fun k h0 h1 => by
    have hnk : k ∉ (entries (pairRes n r nexq.laz.bond nexp.laz.bond).laz).map Prod.fst := fun hm => by
      rcases labR k hm with a | a
      · obtain ⟨e1, he1, rfl⟩ := List.mem_map.mp a
        rcases lp' e1 he1 with b | ⟨b, b'⟩ | b
        · have := labL _ b; omega
        · omega
        · omega
      · obtain ⟨e2, he2, rfl⟩ := List.mem_map.mp a
        rcases lq' e2 he2 with b | b
        · have := labL _ b; omega
        · omega
    rw [(ag st).1 k h0 (by omega) hnk, low3 k h0 h1]
    exact hfix cf hcf0 k h0 h1
  -- the composite's kept registers lie outside both parts' needs
  have nlpK : ∀ z, (z < g0.re ∨ NMem ned z) → ¬ NMem L.sure.ned z → ¬ NMem hed.sure.ned z :=
    fun z k1 k2 hm => by
      rcases hlp z hm with b | ⟨b, b'⟩
      · exact k2 b
      · rcases k1 with k1 | k1
        · omega
        · have := hned z k1; omega
  have nlqK : ∀ z, (z < g0.re ∨ NMem ned z) → ¬ NMem L.sure.ned z → ¬ NMem tel.sure.ned z :=
    fun z k1 k2 hm => by
      rcases hlq z hm with b | ⟨b, b'⟩
      · exact k2 b
      · rcases k1 with k1 | k1
        · omega
        · have := hned z k1; omega
  have keep1 : ∀ z, ((z < g0.re ∨ NMem ned z) ∧ ¬ NMem L.sure.ned z) →
      SkaModel.read z R1 = SkaModel.read z regs :=
    fun z ⟨k1, k2⟩ => u1 z (fun hm => by
        rcases mp z hm with a | ⟨a, _⟩
        · exact nlpK z k1 k2 a
        · rcases k1 with k1 | k1
          · omega
          · have := hned z k1; omega)
      (fun hm => by
        rcases mq z hm with a | ⟨a, _⟩
        · exact nlqK z k1 k2 a
        · rcases k1 with k1 | k1
          · omega
          · have := hned z k1; omega)
  refine ⟨R1, agQ0, agP, hned2, hs1, hn1, e1, keep1, fun x R2 d w hqd fx hx2 hd2 k2 => ?_⟩
  have hdD : ∀ r, NMem d r → g1.re ≤ r ∧ r < g2.re := fun r hr => hp.dreg s x d w r hqd hr
  have nLs : ∀ r, NMem Lh.sure.ned r → r < g'.re := fun r hr => lpl r (hLs' r hr)
  have nLsN : ∀ r, NMem ned r → ¬ NMem Lh.sure.ned r := fun r hr hm => by
    have := nLs r hm; have := hned r hr; omega
  have hn2 : HoldsN ned R2 s0 := HoldsN.agree _ (fun r hr => k2 r ⟨Or.inr hr, nLsN r hr⟩) hn1
  have nlq : ∀ r, NMem (Need.pair ned d) r → ¬ NMem tel.sure.ned r := fun r hr hm => by
    have := lql r hm
    rcases hr with h | h
    · have := hned r h; omega
    · have := (hdD r h).1; omega
  have keep3 : ∀ (R3 : Map (Option Noun)),
      (∀ z, ((z < gb.re ∨ NMem (Need.pair ned d) z) ∧ ¬ NMem tel.sure.ned z) →
        SkaModel.read z R3 = SkaModel.read z R2) →
      ∀ z, ((z < g0.re ∨ NMem ned z) ∧ ¬ NMem L.sure.ned z) → SkaModel.read z R3 = SkaModel.read z regs :=
    fun R3 k3 z ⟨k1, k2'⟩ => by
      rw [k3 z ⟨k1.imp (fun h => by omega) (fun h => Or.inl h), nlqK z k1 k2'⟩,
        k2 z ⟨k1.imp (fun h => by omega) id, fun hm => nlpK z k1 k2' (hLs' z hm)⟩]
      exact keep1 z ⟨k1, k2'⟩
  refine ⟨fun st' => ⟨fun k h0 h1 hnk => ?_, fun e he l => ?_⟩, fun y hy => ?_,
    ⟨HoldsN.agree _ (fun r hr => k2 r ⟨Or.inl (lowQ r hr), fun hm => ?_⟩) hs1'.1, hs1'.2⟩, ⟨hn2, hd2⟩,
    fun st2 R3 y dq wq hy3 hdq3 hdqr k3 => ?_⟩
  · -- the tail's blocks
    have hk : k ∉ (entries Lh).map Prod.fst := fun hm => by
      rcases labLh k hm with a | ⟨a, _⟩
      · have := labL _ a; omega
      · omega
    have hnP : k ∉ nexp.laz.bond.map Prod.fst := fun hm => by
      obtain ⟨e1, he1, rfl⟩ := List.mem_map.mp hm
      rcases lp' e1 he1 with a | ⟨a, a'⟩ | a
      · have := labL _ a; omega
      · omega
      · omega
    have hnk' : k ∉ (entries (pairRes n r nexq.laz.bond nexp.laz.bond).laz).map Prod.fst := fun hm => by
      rcases labR k hm with a | a
      · exact hnP a
      · exact hnk (by rw [eQ]; exact a)
    rw [(ag st').1 k (by omega) (by omega) hnk', mid3 k h1 hk hnP]
  · rw [eQ] at he
    have hnP : e.1 ∉ nexp.laz.bond.map Prod.fst := fun hm => by
      obtain ⟨e1, he1, ee⟩ := List.mem_map.mp hm
      rcases lp' e1 he1 with a | ⟨a, a'⟩ | a
      · have := labL _ a; omega
      · omega
      · have := (hq.labs e (by rw [eQ]; exact he)).1
        rcases this with b | b
        · have := labL _ (labT _ b); omega
        · omega
    have hr : e ∈ (pairRes n r nexq.laz.bond nexp.laz.bond).laz.bond := mem_pairRes_bond.mpr (Or.inr ⟨he, hnP⟩)
    obtain ⟨A0, B0, th0, b3, c3, f3⟩ := (ag st').2 e (by rw [eR]; exact hr) (by omega)
    have hk : e.1 ∉ (entries Lh).map Prod.fst := fun hm => by
      rcases labLh _ hm with a | ⟨a, _⟩
      · have := labL _ a; omega
      · omega
    have hlt1 : e.1 < g1.bo := by
      rcases lq' e he with a | a
      · have := labL _ a; omega
      · omega
    refine ⟨A0, B0, th0, by rw [← mid3 e.1 hlt1 hk hnP]; exact b3, c3, ?_⟩
    exact (f3.pair d (fun r hr => by have := hdD r hr; omega) w).mono (by omega)
  · rcases hy with h | h
    · have := hned y h; omega
    · exact (hdD y h).1
  · -- a register of the tail's need is none of the head's goal's
    have := hLs' r hm
    rcases mq r hr with a | ⟨a, _⟩
    · exact hpq r this a
    · have := lpl r this; omega
  -- after the tail: at `jt`
  have hn3 : HoldsN (Need.pair ned d) R3 (C s0 w) :=
    HoldsN.agree _ (fun r hr => k3 r ⟨Or.inr hr, nlq r hr⟩) ⟨hn2, hd2⟩
  rcases hjt with ⟨rfl, hLe, _⟩ | ⟨rfl, hLe, hlt, hbb⟩
  · -- no bond: `hed.sure` held since the head's end
    subst hLe
    refine ⟨fun _ => ⟨R3, HoldsN.agree _ (fun r hr => k3 r ⟨Or.inl (by have := lpl r hr; omega),
      hpq r hr⟩) hx2, hy3, keep3 R3 k3, hn3.2, hdq3, rfl⟩, fun nf => absurd fx nf⟩
  · -- the bond block: the head's front fills `hed.sure`
    have hmem : (g''.bo, ofSure hed.sure) ∈ entries Lh := by
      rw [hLe]
      have fl : Flat (mk (Sure.bunt : Sure S) [] ((g''.bo, ofSure hed.sure) :: hed.bond)) :=
        flat_mk (fun e he => by
          rcases List.mem_cons.mp he with h | h
          · rw [h]; rfl
          · exact hhf.2 e h)
      rw [entries_flat fl]; exact List.mem_cons_self
    obtain ⟨F, hF, SF⟩ := hp.front _ hmem
    have hb1 : HoonMap.get g1.blocks g''.bo = some ⟨[], [], Termin.hop (jmp0 o)⟩ := by
      rw [hq.keep _ hlt (fun hm => by have := labL _ (labT _ hm); omega)]; exact hbb
    have hb2 := hF [] (Termin.hop (jmp0 o)) hb1
    rw [List.append_nil] at hb2
    have hnP : g''.bo ∉ nexp.laz.bond.map Prod.fst ∨ HoonMap.get idx g''.bo = Option.none := by
      refine Or.inr ((idxN _).mpr (fun hm => ?_))
      obtain ⟨e2, he2, ee⟩ := List.mem_map.mp hm
      rcases lq' e2 he2 with a | a
      · have := labL _ a; omega
      · omega
    have hb3 : HoonMap.get g3.blocks g''.bo = some ⟨[], F, Termin.hop (jmp0 o)⟩ := by
      rw [PP.same (PMo _ hnP), EC.2.2.2 _ (by omega)]; exact hb2
    obtain ⟨Af, hcb', FS'⟩ : ∃ Af, HoonMap.get c.blocks g''.bo = some ⟨[], Af, Termin.hop (jmp0 o)⟩ ∧
        FillSem lib O c gul st2 t (Need.pair (Need.pair ned d) (gsE false Lh)) g1.re hed.sure Af (C (C s0 w) x) x := by
      rcases SF cf hcf2 with ⟨L', hL', FP⟩ | ⟨hn2', FP⟩
      · have hL'' : (g''.bo, L') ∈ (pairRes n r nexq.laz.bond nexp.laz.bond).laz.bond := by
          rw [eP] at hL'
          exact mem_pairRes_bond.mpr (Or.inl ((PMi _ hL').1 (by
            rcases hnP with h | h
            · exact absurd (List.mem_map_of_mem hL') h
            · exact h)))
        obtain ⟨A0, B0, th'', hb3', hc3, hf3⟩ := (ag st2).2 (g''.bo, L') (by rw [eR]; exact hL'') (by omega)
        rw [hb3] at hb3'
        simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at hb3'
        obtain ⟨rfl, rfl⟩ := hb3'
        refine ⟨A0 ++ F.map (renPole (unproxy cf)), by rw [hc3, renJmp_nil _ (show (jmp0 o).args = [] from rfl)], ?_⟩
        exact FP lib σ O c gul st2 t ned A0 s0 s x d w hned2 hqd (hf3.mono (by omega))
      · refine ⟨[] ++ F.map (renPole (unproxy cf)), ?_, FP lib σ O c gul st2 t ned [] s0 s x d w hned2 hqd
          fillSem_bunt_nil⟩
        have hnk : g''.bo ∉ (entries (pairRes n r nexq.laz.bond nexp.laz.bond).laz).map Prod.fst := fun hm => by
          rcases labR _ hm with a | a
          · exact hn2' (by rw [eP]; exact a)
          · obtain ⟨e2, he2, ee⟩ := List.mem_map.mp a
            rcases lq' e2 he2 with b | b
            · have := labL _ b; omega
            · omega
        rw [(ag st2).1 g''.bo (by omega) (by omega) hnk, hb3]
        simp only [Option.map_some, unproxyBlob, renBlob, renFin, List.nil_append, List.map_nil,
          renJmp_nil _ (show (jmp0 o).args = [] from rfl)]
    have hn3' : HoldsN (Need.pair (Need.pair ned d) (gsE false Lh)) R3 (C (C s0 w) x) := ⟨hn3, trivial⟩
    obtain ⟨F1, F2⟩ := FS' R3 hn3'
    refine ⟨fun fxp => ?_, fun nfx => ?_⟩
    · obtain ⟨R4, r4, hl4, k4⟩ := F1 fxp
      have e4 : goJ lib O c gul st2 R3 t (jmp0 g''.bo) = goJ lib O c gul st2 R4 t (jmp0 o) := by
        have := r4 [] (Termin.hop (jmp0 o))
        simp only [List.append_nil] at this
        rw [goJ_jmp0 _ _ _ _ hcb', this, execBlob_hop]
      refine ⟨R4, hl4.1, HoldsN.agree _ (fun r hr => k4 r (Or.inr (by have := lql r hr; omega))
        (fun hm => hpq r hm hr)) hy3, fun z hz => ?_, HoldsN.agree _ (fun r hr => k4 r
          (Or.inl (Or.inl (Or.inr hr))) (fun hm => by have := lpl r hm; have := (hdD r hr).1; omega)) hn3.2,
        HoldsN.agree _ (fun r hr => k4 r (Or.inr (by have := (hdqr r hr).2; omega))
          (fun hm => by have := lpl r hm; have := (hdqr r hr).1; omega)) hdq3, e4⟩
      obtain ⟨k1, k2'⟩ := hz
      rw [k4 z (k1.elim (fun h => Or.inr (by omega)) (fun h => Or.inl (Or.inl (Or.inl h)))) (nlpK z k1 k2')]
      exact keep3 R3 k3 z ⟨k1, k2'⟩
    · have := F2 nfx [] (Termin.hop (jmp0 o))
      simp only [List.append_nil] at this
      rw [goJ_jmp0 _ _ _ _ hcb', this]

end

end Comp
end SkaModel
end Formalization
