import lemmas.Ska.CompFlatCopy

/-!
# A pair of runs under a flat lazy goal with entries: `pairLS_ok`

README Gaps 12.24.  `pairLC_ok` (`CompPairLC.lean`) composes the two parts
of a cons (or of the inner pair of the indirect call) under a fork-free goal
into `RunOKGC`.  `pairLS_ok` does the same under a flat goal `%next L th`
with bonds, into `RunOKLS` (`RunOKLB` with fronts at the state level,
`CompFrontS.lean`), with bodies at the entries and the parts' witnesses side
by side (`pairWit`).  The phases of the parent, in compile order:

1. the block `o = g0.bo` of the sure part (`+split`'s `split-sure`), `Ext g0 g'`;
2. the bonds' splits (`SplitBs`, `CompFlat.lean`): the ops `PB b` in front of
   each goal entry's block `b`, `Pref g' g'' PB`, the halves `hed`, `tel`
   (flat, pruned);
3. `+past` of the head's need behind the tail (`Ext g'' gb`, `hjt`);
4. the tail `q` with its own `+past` (`RunOKLS` under `tel`), then the head
   `p` (`RunOKLS` under `Lh`, `hed` or `hed`'s sure part parked in a bond);
5. `+copy`: the copy of the sure needs (`copy`, `Ext g2 g3'`) and the merge
   of the bonds (`MergeBs`, `CompFlatCopy.lean`, `Pref g3' g3 PM`).

At run time: the copy block, `p`'s code, `q`'s code (input need `pair ned
d_p`), the park block, the block `o`.  At a goal entry's block: the merge's
moves, `p`'s ops, `q`'s ops, the split's ops (`frontS_pair`).
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
variable {lib : Lib} {σ : Type} {Inv : σ → Prop} {ν : σ → Needs} {O : Oracle σ} {c : Straight Map} {gul : Noun}

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

/-- **A pair of runs under a flat lazy goal with entries** (see the header):
`RunOKLS` of the whole, its result flat with clean entries. -/
theorem pairLS_ok {lib : Lib} {P : Noun → Prop} {f fh ft : Noun} {L : Lazy S} {th : Jmp}
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
    (hq : RunOKLS (Map := Map) lib P ft tel jt Qt false gb g1 nexq)
    (hp : RunOKLS (Map := Map) lib P fh Lh nexq.th Qh false g1 g2 nexp)
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
          GoalSemCM lib O c gul Inv ν (Keep g0 g' (CGoal.next L.sure th)) st regs t tm (jmp0 o) (CGoal.next L.sure th) r) :
    RunOKLS (Map := Map) lib P f L th (pairWit C Qh Qt) false g0 g3 (pairRes n r nexq.laz.bond nexp.laz.bond) ∧
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
  have dregR : ∀ s v d w x, pairWit C Qh Qt s v d w → NMem d x → g0.re ≤ x ∧ x < g3.re := by
    intro s v d w x hq' hx
    obtain ⟨vp, vq, dp, dq, wp, wq, rfl, rfl, rfl, qp, qq⟩ := hq'
    rcases hx with hx | hx
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
  -- the shared part of the two `sem` clauses
  have core : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g3.re → HoonMap.get cf k = HoonMap.get g3.cond k) →
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
  have SEM : SemLB lib P f L th (pairWit C Qh Qt) g0 g3 (pairRes n r nexq.laz.bond nexp.laz.bond) := by
    intro cf hcf c ned σ Inv ν O n0 gul hS hF st t tm s0 s r0 hI htr hs hm ag hned regs hh hn
    have hcf2 : ∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g2.cond k := fun k hk =>
      (hcf k (by omega)).trans (by rw [cM, kc3])
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk =>
      (hcf2 k (by omega)).trans (hp.cfr.get_lt hk)
    obtain ⟨R1, agQ0, agP, hned2, hs1, hn1, e1, keep1, K⟩ := core cf hcf c ned σ O gul st t s0 s ag hned regs hh hn
    obtain ⟨n', hn', rh, hmh, H⟩ := Mf hs hm
    have Gh := hp.sem cf hcf2 c ned σ Inv ν O n' gul hS (oracleFwd_le hF (Nat.le_of_lt hn')) st t tm s0 s rh hI htr
      hs hmh agP hned2 R1 hs1 hn1
    rcases H with ⟨hnz, rfl⟩ | ⟨x, rfl, rt, hmt, Ht⟩
    · exact goalSemCMD_ret hnz (returnsC_step (Needs.le_refl _) e1 (returnsC_of_goalSemCMD hnz Gh))
    by_cases fx : FitsS Lh.sure x
    · obtain ⟨st1, R2, d, w, hI1, hν1, hqd, hx2, hd2, k2, e2⟩ := Gh.1 fx
      obtain ⟨agQ, hnQ, hsQ, hnQ', J⟩ := K x R2 d w hqd fx hx2 hd2 k2
      have htr1 := frames_mono hν1 htr
      have Gq := hq.sem cf hcf1 c (Need.pair ned d) σ Inv ν O n' gul hS (oracleFwd_le hF (Nat.le_of_lt hn')) st1 t
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
          have AD := goalSemCMD_of_CM (Q := pairWit C Qh Qt s) (d := Need.pair d dq) (w := C w wq)
            (fun z hz => by
              rcases hz with hz | hz
              · have := hp.dreg s x d w z hqd hz
                exact ⟨Or.inr (by omega), fun hm => by have := gm z hm; omega⟩
              · have := hq.dreg s y dq wq z hqq hz
                exact ⟨Or.inr (by omega), fun hm => by have := gm z hm; omega⟩)
            ⟨hdp4, hdq4⟩ (fun p hp' => by
              rw [hFin _ _ _ _ _ _ hfin] at hp'
              cases hp'
              exact ⟨x, y, d, dq, w, wq, rfl, rfl, rfl, hqd, hqq⟩) A
          exact goalSemCMD_step (Needs.le_trans hν1 hν2) k4 (e12.trans (e3.trans e4))
            (AD.mono (fun z hz => ⟨hz.1.imp id (fun h => by have := hned z h; omega), hz.2⟩) (fun _ _ _ h => h))
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
  have SEMB : SemLBB lib P f L th (pairWit C Qh Qt) g0 g3 (pairRes n r nexq.laz.bond nexp.laz.bond) := by
    intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    have hcf2 : ∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g2.cond k := fun k hk =>
      (hcf k (by omega)).trans (by rw [cM, kc3])
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk =>
      (hcf2 k (by omega)).trans (hp.cfr.get_lt hk)
    obtain ⟨R1, agQ0, agP, hned2, hs1, hn1, e1, keep1, K⟩ := core cf hcf c ned σ O gul st t s0 s ag hned regs hh hn
    obtain ⟨rh, hmh, Gh⟩ := hp.semB cf hcf2 c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs agP hned2 R1 hs1 hn1
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
        obtain ⟨rt, hmt, Gq⟩ := hq.semB cf hcf1 c (Need.pair ned d) σ Inv ν O gul hS hB st1 t tm (C s0 w) s hI1 htr1
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
              have AD := goalSemCMD_of_CM (Q := pairWit C Qh Qt s) (d := Need.pair d dq) (w := C w wq)
                (fun z hz => by
                  rcases hz with hz | hz
                  · have := hp.dreg s x d w z hqd hz
                    exact ⟨Or.inr (by omega), fun hm => by have := gm z hm; omega⟩
                  · have := hq.dreg s y dq wq z hqq hz
                    exact ⟨Or.inr (by omega), fun hm => by have := gm z hm; omega⟩)
                ⟨hdp4, hdq4⟩ (fun p hp' => by
                  rw [hFinB _ _ _ _ _ hfr] at hp'
                  cases hp'
                  exact ⟨x, y, d, dq, w, wq, rfl, rfl, rfl, hqd, hqq⟩) A
              exact ⟨r1, MB.2 y r1 rfl hfr, goalSemCMD_step (Needs.le_trans hν1 hν2) k4 e14
                (AD.mono (fun z hz => ⟨hz.1.imp id (fun h => by have := hned z h; omega), hz.2⟩) (fun _ _ _ h => h))⟩
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
  have FS : FrontsS (Map := Map) (pairWit C Qh Qt) false g0 g3 L (pairRes n r nexq.laz.bond nexp.laz.bond) := by
    intro e he
    rw [eL] at he
    obtain ⟨sh, st, SA⟩ := hsp e he
    have hlt : e.1 < g0.bo := labL _ (List.mem_map_of_mem he)
    obtain ⟨-, -, -, hLe⟩ := hLb e he
    -- the tail's ops at the entry's block
    obtain ⟨Fq, hFq, FQ⟩ : ∃ Fq : List Pole,
        (∀ B fin, HoonMap.get gb.blocks e.1 = some ⟨[], B, fin⟩ → HoonMap.get g1.blocks e.1 = some ⟨[], Fq ++ B, fin⟩) ∧
        ∀ cf : Map (Nat × List Nat), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
          ∃ Lq : Sure S, FrontS (Map := Map) Qt Need.none gb.re g1.re Lq (Fq.map (renPole (unproxy cf))) st ∧
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
          ∃ Lp : Sure S, FrontS (Map := Map) Qh Need.none g1.re g2.re Lp (Fp.map (renPole (unproxy cf))) sh ∧
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
      have F1 := frontS_pair (comb := C) FPs FQs (lo0 := g0.re) (lo := g3.re) (Lb := e.2.sure) (Fs := PB e.1)
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (fun s v d w x hq' hx => hp.dreg s v d w x hq' hx) (fun s v d w x hq' hx => hq.dreg s v d w x hq' hx)
        hLh' hLt' SA.ht hM1 hM2 hM3 hM4 SA.fit SA.sem
      have eF : (PM e.1 ++ Fp ++ Fq ++ PB e.1).map (renPole (unproxy cf)) =
          Ac ++ Fp.map (renPole (unproxy cf)) ++ Fq.map (renPole (unproxy cf)) ++ PB e.1 := by
        rw [List.map_append, List.map_append, List.map_append, uB, hPM, hM5]
      rw [eF]
      rcases hres with h | ⟨h, rfl⟩
      · exact Or.inl ⟨ofSure M, by rw [eR]; exact h, F1⟩
      · exact Or.inr ⟨by rw [eR]; exact h, F1⟩
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
    front := FS.toFront (by omega) (fun x hx => gm x hx) (fun _ _ x hx => hx.elim) dregR
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
