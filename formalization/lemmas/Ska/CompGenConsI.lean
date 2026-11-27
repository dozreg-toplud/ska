import lemmas.Ska.CompGenConsF

/-!
# The cons of two leaves: the copy's preconditions and the frame

README Gaps 12.39, item 11.  For the run of `[[0 a] [0 b]]` under `%next L th`
(`ConsAt`):

* `SplitOKD.cleanAt`: the split's halves at a label are clean when the goal's
  needs there are.
* `consCopyPre`: the copy's inputs meet `CopyPreAt` at every label (clean,
  distinct, below the copy's start, pairwise apart): the halves of the split
  at the label (the root `g0.bo` for the copy's root `gS.bo`) carried
  through `+from`.
* `frameG_cons00`: `FrameG` of the run, given `CopyRunAt` of the copy and
  `LabDisj` of the result.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Lists at one label -/

theorem ci_atL_self (o : Nat) (l : Lazy S) (es : List (Nat × Lazy S)) :
    atL ((o, l) :: es) o = l.sure :: atL es o := by
  simp [atL, List.filter_cons]

theorem ci_atL_ne {o k : Nat} (l : Lazy S) (es : List (Nat × Lazy S)) (h : o ≠ k) :
    atL ((o, l) :: es) k = atL es k := by
  simp [atL, List.filter_cons, h]

theorem ci_atL_sub (o : Nat) (l : Lazy S) (es : List (Nat × Lazy S)) (k : Nat) :
    (atL es k).Sublist (atL ((o, l) :: es) k) := by
  by_cases h : o = k
  · subst h; rw [ci_atL_self]; exact List.sublist_cons_self _ _
  · rw [ci_atL_ne _ _ h]; exact List.Sublist.refl _

theorem ci_mem_atL {es : List (Nat × Lazy S)} {e : Nat × Lazy S} (he : e ∈ es) : e.2.sure ∈ atL es e.1 :=
  List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨he, decide_eq_true rfl⟩, rfl⟩

theorem ci_emitted_ne (g : Gen Map) (b : Blob) {k : Nat} (hk : k ≠ g.bo) :
    HoonMap.get (g.emitted b).blocks k = HoonMap.get g.blocks k := by
  unfold Gen.emitted
  cases g.drop <;> simp [HoonMap.get_put, hk]

/-! ## The split's halves -/

/-- **The split's halves at a label are clean** when the goal's needs there are. -/
theorem SplitOKD.cleanAt {g g' : Gen Map} {es hs ts : List (Nat × Lazy S)} (W : SplitOKD g g' es hs ts) (k : Nat)
    (hc : ∀ L ∈ atL es k, Clean L.ned) : (∀ H ∈ atL hs k, Clean H.ned) ∧ (∀ T ∈ atL ts k, Clean T.ned) := by
  obtain ⟨P, PP, O, A⟩ := W
  obtain ⟨ps, eP, pE, dH, dT, sP, aP⟩ := A k
  have c1 : ∀ p ∈ ps, Clean p.1.ned := fun p hp => hc _ (pE.mem_iff.mp (List.mem_map_of_mem hp))
  refine ⟨fun H hH => ?_, fun T hT => ?_⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (dH.sub H hH)
    exact ((sP p hp).cl (c1 p hp)).1
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (dT.sub T hT)
    exact ((sP p hp).cl (c1 p hp)).2

/-- The halves at a label are distinct, with registers of the goal's needs
there or fresh. -/
theorem ci_splitHalves {g g' : Gen Map} {es hs ts : List (Nat × Lazy S)} (W : SplitOKD g g' es hs ts)
    (hreg : ∀ e ∈ es, Distinct e.2.sure.ned ∧ ∀ y, NMem e.2.sure.ned y → y < g.re) (k : Nat) :
    ∀ H ∈ atL hs k ++ atL ts k, Distinct H.ned ∧
      ∀ y, NMem H.ned y → (∃ L ∈ atL es k, NMem L.ned y) ∨ (g.re ≤ y ∧ y < g'.re) := by
  obtain ⟨P, PP, O, A⟩ := W
  obtain ⟨ps, eP, pE, dH, dT, sP, aP⟩ := A k
  have mE : ∀ p ∈ ps, p.1 ∈ atL es k := fun p hp => pE.mem_iff.mp (List.mem_map_of_mem hp)
  have hD : ∀ p ∈ ps, Distinct p.1.ned ∧ ∀ y, NMem p.1.ned y → y < g.re := fun p hp => by
    obtain ⟨e, he, -, es'⟩ := mem_atL (mE p hp)
    rw [← es']; exact hreg e he
  intro H hH
  rcases List.mem_append.mp hH with hH | hH
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (dH.sub H hH)
    refine ⟨((sP p hp).sem (hD p hp).1 (hD p hp).2).1, fun y hy => ?_⟩
    rcases (sP p hp).mh y hy with h | h
    · exact Or.inl ⟨p.1, mE p hp, h⟩
    · exact Or.inr h
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (dT.sub H hH)
    refine ⟨((sP p hp).sem (hD p hp).1 (hD p hp).2).2.1, fun y hy => ?_⟩
    rcases (sP p hp).mt y hy with h | h
    · exact Or.inl ⟨p.1, mE p hp, h⟩
    · exact Or.inr h

/-- The goal's entry list with its root: label-apart, distinct, below the start. -/
theorem ci_es {L : Lazy S} {th : Jmp} {g0 : Gen Map} (G : GoalG (Map := Map) L th g0) :
    ((g0.bo, L) :: entries L).Pairwise (fun e e' => e.1 = e'.1 → ∀ r, NMem e.2.sure.ned r → ¬ NMem e'.2.sure.ned r) ∧
    ∀ e ∈ (g0.bo, L) :: entries L, Distinct e.2.sure.ned ∧ ∀ y, NMem e.2.sure.ned y → y < g0.re := by
  refine ⟨List.pairwise_cons.mpr ⟨fun e' he' heq => ?_, G.labDisj⟩, fun e he => ?_⟩
  · exfalso
    have := (G.lab e' he').2.1
    have h2 : g0.bo = e'.1 := heq
    omega
  · rcases List.mem_cons.mp he with rfl | he
    · exact ⟨G.dist, G.sregs⟩
    · exact G.eregs e he

section Cons
variable {L : Lazy S} {th : Jmp} {a b : Nat} {g0 g1 : Gen Map} {nex : NextL S} {hed tel hed' tel' : Lazy S}
  {gS : Gen Map}

/-- **The split at a label**: the halves are distinct, with registers of the
goal's needs at the label or fresh, and pairwise apart. -/
theorem ci_splitR (CA : ConsAt L th a b g0 g1 nex hed tel hed' tel' gS) (G : GoalG (Map := Map) L th g0) (k : Nat) :
    (∀ H ∈ atL ((g0.bo, hed) :: entries hed) k ++ atL ((g0.bo, tel) :: entries tel) k, Distinct H.ned ∧
      ∀ y, NMem H.ned y → (∃ e ∈ (g0.bo, L) :: entries L, e.1 = k ∧ NMem e.2.sure.ned y) ∨
        (g0.re ≤ y ∧ y < gS.re)) ∧
    (atL ((g0.bo, hed) :: entries hed) k ++ atL ((g0.bo, tel) :: entries tel) k).Pairwise
      (fun L L' => ∀ r, NMem L.ned r → ¬ NMem L'.ned r) := by
  obtain ⟨hdj, hreg⟩ := ci_es G
  refine ⟨fun H hH => ?_, SplitOKD.apartAt CA.sp hdj hreg k⟩
  obtain ⟨d, rg⟩ := ci_splitHalves CA.sp hreg k H hH
  refine ⟨d, fun y hy => ?_⟩
  rcases rg y hy with ⟨L', hL', hm⟩ | h
  · obtain ⟨e, he, ek, rfl⟩ := mem_atL hL'
    exact Or.inl ⟨e, he, ek, hm⟩
  · exact Or.inr h

/-- **The copy's inputs at a label, paired with the split's halves** at the
split's label (`g0.bo` for the copy's root `gS.bo`, else the same label):
each moved need has fewer registers, and keeps cleanliness and
distinctness. -/
theorem ci_pair (CA : ConsAt L th a b g0 g1 nex hed tel hed' tel' gS) (G : GoalG (Map := Map) L th g0)
    (k k' : Nat) (hk : (k = gS.bo ∧ k' = g0.bo) ∨ (k ≠ gS.bo ∧ k' = k)) :
    ∃ qs : List (Sure S × Sure S),
      qs.map Prod.snd = atL ((gS.bo, hed') :: entries hed') k ++ atL ((gS.bo, tel') :: entries tel') k ∧
      (qs.map Prod.fst).Sublist (atL ((g0.bo, hed) :: entries hed) k' ++ atL ((g0.bo, tel) :: entries tel) k') ∧
      ∀ q ∈ qs, (Clean q.1.ned → Clean q.2.ned) ∧ (Distinct q.1.ned → Distinct q.2.ned) ∧
        ∀ r, NMem q.2.ned r → NMem q.1.ned r := by
  have fact : ∀ (ax : Nat) (p : Sure S × Sure S), fromSure ax p.1 = some p.2 →
      (Clean p.1.ned → Clean p.2.ned) ∧ (Distinct p.1.ned → Distinct p.2.ned) ∧ ∀ r, NMem p.2.ned r → NMem p.1.ned r :=
    fun ax p h => ⟨clean_fromSure h, fromSure_dist h, (fromSure_spec (Map := Map) h).2.2.2⟩
  have lt : ∀ {l : Lazy S}, (∀ e ∈ entries l, e.1 ∈ (entries L).map Prod.fst) → ∀ e ∈ entries l, e.1 < g0.bo :=
    fun hl e he => by
      obtain ⟨e0, he0, h0⟩ := List.mem_map.mp (hl e he)
      rw [← h0]; exact (G.lab e0 he0).2.1
  have boS := CA.boS
  rcases hk with ⟨rfl, rfl⟩ | ⟨hne, hkk⟩
  · refine ⟨[(hed.sure, hed'.sure), (tel.sure, tel'.sure)], ?_, ?_, ?_⟩
    · rw [ci_atL_self, ci_atL_self, atL_none (fun e he => by have := lt CA.labH' e he; omega),
        atL_none (fun e he => by have := lt CA.labT' e he; omega)]
      rfl
    · rw [ci_atL_self, ci_atL_self]
      exact (List.Sublist.cons_cons _ (List.nil_sublist _)).append (List.Sublist.cons_cons _ (List.nil_sublist _))
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact fact a (hed.sure, hed'.sure) (fromL_sure CA.f2)
      · exact fact b (tel.sure, tel'.sure) (fromL_sure CA.f1)
  · rw [hkk]
    obtain ⟨ph, h1, h2, h3⟩ := (fromL_ent a hed hed' CA.f2).pairsAt k
    obtain ⟨pt, t1, t2, t3⟩ := (fromL_ent b tel tel' CA.f1).pairsAt k
    refine ⟨ph ++ pt, ?_, ?_, ?_⟩
    · rw [List.map_append, h2, t2, ci_atL_ne _ _ (Ne.symm hne), ci_atL_ne _ _ (Ne.symm hne)]
    · rw [List.map_append, h1, t1]
      exact (ci_atL_sub _ _ _ _).append (ci_atL_sub _ _ _ _)
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact fact a q (h3 q hq)
      · exact fact b q (t3 q hq)

theorem ci_kk (k : Nat) (gS g0 : Gen Map) : ∃ k', (k = gS.bo ∧ k' = g0.bo) ∨ (k ≠ gS.bo ∧ k' = k) := by
  by_cases h : k = gS.bo
  · exact ⟨g0.bo, Or.inl ⟨h, rfl⟩⟩
  · exact ⟨k, Or.inr ⟨h, rfl⟩⟩

/-- **The copy's inputs meet `CopyPreAt`** at every label. -/
theorem consCopyPre (CA : ConsAt L th a b g0 g1 nex hed tel hed' tel' gS) (G : GoalG (Map := Map) L th g0)
    (cl : Clean L.sure.ned) (ecl : ∀ e ∈ entries L, Clean e.2.sure.ned) :
    CopyPreAt (gS.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩) ((gS.bo, hed') :: entries hed')
      ((gS.bo, tel') :: entries tel') := by
  unfold CopyPreAt
  intro k
  obtain ⟨k', hk⟩ := ci_kk k gS g0
  obtain ⟨qs, e2, sub, fq⟩ := ci_pair CA G k k' hk
  obtain ⟨SR, SA⟩ := ci_splitR CA G k'
  have SC := SplitOKD.cleanAt CA.sp k' (fun L' hL' => by
    obtain ⟨e, he, -, rfl⟩ := mem_atL hL'
    rcases List.mem_cons.mp he with rfl | he
    · exact cl
    · exact ecl e he)
  have hS1 : ∀ q ∈ qs, q.1 ∈ atL ((g0.bo, hed) :: entries hed) k' ++ atL ((g0.bo, tel) :: entries tel) k' :=
    fun q hq => sub.subset (List.mem_map_of_mem hq)
  have r1 := CA.reS
  rw [← e2]
  refine ⟨fun F hF => ?_, ?_⟩
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hF
    have m := hS1 q hq
    obtain ⟨d, rg⟩ := SR q.1 m
    have c : Clean q.1.ned := by
      rcases List.mem_append.mp m with m | m
      · exact SC.1 _ m
      · exact SC.2 _ m
    refine ⟨(fq q hq).1 c, (fq q hq).2.1 d, fun y hy => ?_⟩
    show y < gS.re
    rcases rg y ((fq q hq).2.2 y hy) with ⟨e, he, -, hm⟩ | h
    · have : y < g0.re := by
        rcases List.mem_cons.mp he with rfl | he
        · exact G.sregs y hm
        · exact (G.eregs e he).2 y hm
      omega
    · exact h.2
  · have P1 := SA.sublist sub
    rw [List.pairwise_map] at P1 ⊢
    exact P1.imp_of_mem fun {q q'} hq hq' h r hr hr' => h r ((fq q hq).2.2 r hr) ((fq q' hq').2.2 r hr')

/-- **The registers of the result's needs at a label** trace to the goal's
needs at the split's label, or are fresh. -/
theorem ci_trace (CA : ConsAt L th a b g0 g1 nex hed tel hed' tel' gS) (G : GoalG (Map := Map) L th g0)
    (CR : CopyRunAt (gS.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩) g1 ((gS.bo, hed') :: entries hed')
      ((gS.bo, tel') :: entries tel') ((gS.bo, nex.laz) :: entries nex.laz))
    (CP : CopyPreAt (gS.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩) ((gS.bo, hed') :: entries hed')
      ((gS.bo, tel') :: entries tel'))
    (k k' : Nat) (hk : (k = gS.bo ∧ k' = g0.bo) ∨ (k ≠ gS.bo ∧ k' = k)) :
    ∀ M ∈ atL ((gS.bo, nex.laz) :: entries nex.laz) k, Distinct M.ned ∧ ∀ y, NMem M.ned y →
      (∃ e ∈ (g0.bo, L) :: entries L, e.1 = k' ∧ NMem e.2.sure.ned y) ∨ (g0.re ≤ y ∧ y < g1.re) := by
  obtain ⟨Pc, PPC, OC, AC⟩ := CR
  obtain ⟨-, regs, -, -, -⟩ := AC k (CP k).1 (CP k).2
  obtain ⟨qs, e2, sub, fq⟩ := ci_pair CA G k k' hk
  obtain ⟨SR, -⟩ := ci_splitR CA G k'
  intro M hM
  obtain ⟨d, rg⟩ := regs M hM
  refine ⟨d, fun y hy => ?_⟩
  have r1 := CA.reS
  have r2 := CA.reC
  rcases rg y hy with ⟨F, hF, hm⟩ | h
  · rw [← e2] at hF
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hF
    rcases (SR q.1 (sub.subset (List.mem_map_of_mem hq))).2 y ((fq q hq).2.2 y hm) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.1, by omega⟩
  · have h1 := h.1
    simp only [emitted_re] at h1
    exact Or.inr ⟨by omega, h.2⟩

/-- **A goal entry's block after the run**: both prefixes in front. -/
theorem ci_blk (CA : ConsAt L th a b g0 g1 nex hed tel hed' tel' gS) {Ps Pc : Nat → List Pole}
    (PPS : Pref (g0.emitted ⟨[], [], Termin.hop th⟩) gS Ps)
    (PPC : Pref (gS.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩) g1 Pc) {k : Nat} (hk : k < g0.bo) :
    HoonMap.get g1.blocks k = (HoonMap.get g0.blocks k).map (preBody (Pc k ++ Ps k)) := by
  have boS := CA.boS
  rw [PPC.get, ci_emitted_ne _ _ (by omega : k ≠ gS.bo), PPS.get, ci_emitted_ne _ _ (by omega : k ≠ g0.bo)]
  cases HoonMap.get g0.blocks k <;> simp [preBody, List.append_assoc]

/-- **The frame of the cons of two leaves.** -/
theorem frameG_cons00 (CA : ConsAt L th a b g0 g1 nex hed tel hed' tel' gS) (G : GoalG (Map := Map) L th g0)
    (hnc : ∀ r, NMem L.sure.ned r → HoonMap.get g0.cond r = Option.none)
    (hec : ∀ e ∈ entries L, ∀ r, NMem e.2.sure.ned r → HoonMap.get g0.cond r = Option.none) (hcb : CondBelow g0)
    (CR : CopyRunAt (gS.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩) g1 ((gS.bo, hed') :: entries hed')
      ((gS.bo, tel') :: entries tel') ((gS.bo, nex.laz) :: entries nex.laz))
    (CP : CopyPreAt (gS.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩) ((gS.bo, hed') :: entries hed')
      ((gS.bo, tel') :: entries tel'))
    (LD : LabDisj nex.laz) (W : Noun → Noun) :
    FrameG (Map := Map) L th (pureWit (Nomm.cons (Nomm.n0 a) (Nomm.n0 b)) (fun _ => Need.none) W) g0 g1 nex := by
  have boS := CA.boS
  have bo1 := CA.bo
  have r1 := CA.reS
  have r2 := CA.reC
  have T0 := ci_trace CA G CR CP gS.bo g0.bo (Or.inl ⟨rfl, rfl⟩)
  have lt : ∀ e ∈ entries nex.laz, e.1 < g0.bo := fun e he => by
    obtain ⟨e0, he0, h0⟩ := List.mem_map.mp (CA.labN e he)
    rw [← h0]; exact (G.lab e0 he0).2.1
  have mroot : nex.laz.sure ∈ atL ((gS.bo, nex.laz) :: entries nex.laz) gS.bo :=
    ci_mem_atL (e := (gS.bo, nex.laz)) List.mem_cons_self
  have hregs : ∀ r, NMem nex.laz.sure.ned r → NMem L.sure.ned r ∨ (g0.re ≤ r ∧ r < g1.re) := fun r hr => by
    rcases (T0 _ mroot).2 r hr with ⟨e, he, ek, hm⟩ | h
    · rcases List.mem_cons.mp he with rfl | he
      · exact Or.inl hm
      · exfalso; have := (G.lab e he).2.1; omega
    · exact Or.inr h
  have heregs : ∀ e ∈ entries nex.laz, Distinct e.2.sure.ned ∧ ∀ r, NMem e.2.sure.ned r →
      (∃ e0 ∈ entries L, NMem e0.2.sure.ned r) ∨ NMem L.sure.ned r ∨ (g0.re ≤ r ∧ r < g1.re) := fun e he => by
    have l1 := lt e he
    have T := ci_trace CA G CR CP e.1 e.1 (Or.inr ⟨by omega, rfl⟩)
    have m : e.2.sure ∈ atL ((gS.bo, nex.laz) :: entries nex.laz) e.1 := ci_mem_atL (List.mem_cons_of_mem _ he)
    refine ⟨(T _ m).1, fun r hr => ?_⟩
    rcases (T _ m).2 r hr with ⟨e0, he0, -, hm⟩ | h
    · rcases List.mem_cons.mp he0 with rfl | he0
      · exact Or.inr (Or.inl hm)
      · exact Or.inl ⟨e0, he0, hm⟩
    · exact Or.inr (Or.inr h)
  obtain ⟨Ps, PPS, OS, -⟩ := CA.sp
  obtain ⟨Pc, PPC, OC, -⟩ := CR
  have cnd : ∀ r, g0.re ≤ r → HoonMap.get g1.cond r = Option.none := fun r hr => by
    rw [CA.cond]; exact condBelow_none hcb hr
  refine { re := by omega, bo := by omega, drop := CA.drop, keep := fun o ho hno => ?_, grow := CA.grow.toG,
           cfr := condFresh_of_eq (by omega) CA.cond, lo := ?_, hi := ?_, ent := ?_, regs := hregs,
           dist := (T0 _ mroot).1, eregs := heregs, labs := fun e he => ?_, labDisj := LD,
           dreg := fun s v d w r hq hr => ?_, ncond := fun r hr => ?_, econd := fun e he r hr => ?_,
           fronts := fun e he => Or.inl ⟨Pc e.1 ++ Ps e.1, fun B fin hb => ?_⟩ }
  · rw [ci_blk CA PPS PPC ho]
    have hc : Pc o = [] := OC o (fun hm => by
      rw [List.map_append, List.mem_append, List.map_cons, List.mem_cons, List.map_cons, List.mem_cons] at hm
      rcases hm with (h | h) | (h | h)
      · omega
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp h; exact hno (CA.labH' e he)
      · omega
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp h; exact hno (CA.labT' e he))
    have hs : Ps o = [] := OS o (fun hm => by
      rw [List.map_cons, List.mem_cons] at hm
      rcases hm with h | h
      · omega
      · exact hno h)
    rw [hc, hs]
    cases HoonMap.get g0.blocks o <;> simp [preBody]
  · rw [CA.eth]; show 1 ≤ gS.bo; omega
  · rw [CA.eth]; show gS.bo < g1.bo; omega
  · refine Or.inl ⟨preBody (Pc gS.bo) ⟨[], [], Termin.hop (jmp0 g0.bo)⟩, ?_, rfl, by rw [CA.eth]; rfl⟩
    rw [CA.eth]
    show HoonMap.get g1.blocks gS.bo = _
    rw [PPC.get, CA.eC]
    rfl
  · obtain ⟨e0, he0, h0⟩ := List.mem_map.mp (CA.labN e he)
    obtain ⟨_, hlt, B, th', hb⟩ := G.lab e0 he0
    refine ⟨Or.inl (CA.labN e he), Pc e0.1 ++ Ps e0.1 ++ B, th', ?_⟩
    rw [← h0, ci_blk CA PPS PPC hlt, hb]
    rfl
  · obtain ⟨_, rfl, _⟩ := hq
    exact hr.elim
  · rcases hregs r hr with h | h
    · rw [CA.cond]; exact hnc r h
    · exact cnd r h.1
  · rcases (heregs e he).2 r hr with ⟨e0, he0, hm⟩ | h | h
    · rw [CA.cond]; exact hec e0 he0 r hm
    · rw [CA.cond]; exact hnc r h
    · exact cnd r h.1
  · rw [ci_blk CA PPS PPC (G.lab e he).2.1, hb]
    rfl

end Cons

end Comp
end SkaModel
end Formalization
