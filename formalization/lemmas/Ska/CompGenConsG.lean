import lemmas.Ska.CompGenConsF

/-!
# `+copy` at one label, and `LabDisj` of the merged tree

README Gaps 12.39, item 11.

* `CopyOKL.runAt`: `CopyOKL` gives `CopyRunAt`: at every label where both
  inputs' needs are clean, distinct, below the start and pairwise apart, the
  pieces' ops build both sides' needs from the merged ones.
* `labDisj_copyLazyL`: the merged tree of `+copy` meets `LabDisj`: a fresh
  register lies in one entry at most (`Raw.cr_copyLazyL`, counted), an old
  one only through the inputs' apart halves at that label.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Helpers -/

theorem cg_mem_drop {l l' : List (Sure S)} (h : DropT l l') {s : Sure S} (hs : s ∈ l) : s ∈ l' ∨ TrivS s := by
  obtain ⟨k, p, t⟩ := h
  rcases List.mem_append.mp (p.mem_iff.mpr hs) with a | a
  · exact Or.inl a
  · exact Or.inr (t s a)

theorem cg_triv_nmem {s : Sure S} (h : TrivS s) (r : Nat) : ¬ NMem s.ned r := by
  rw [h.1]; simp [NMem]

theorem cg_pw_triv {l t : List (Sure S)} (hl : l.Pairwise fun L L' => ∀ r, NMem L.ned r → ¬ NMem L'.ned r)
    (ht : ∀ s ∈ t, TrivS s) : (l ++ t).Pairwise fun L L' => ∀ r, NMem L.ned r → ¬ NMem L'.ned r := by
  refine List.pairwise_append.mpr ⟨hl, ?_, fun a _ b hb r _ hr => cg_triv_nmem (ht b hb) r hr⟩
  exact List.pairwise_of_forall_mem_list fun a ha b _ r hr _ => cg_triv_nmem (ht a ha) r hr

theorem cg_flatMap_perm (cs : List (CopyE S)) :
    (cs.flatMap fun p => [p.1, p.2.1]).Perm ((cs.map fun p => p.1) ++ cs.map fun p => p.2.1) := by
  induction cs with
  | nil => simp
  | cons p ps ih =>
    simp only [List.flatMap_cons, List.map_cons, List.cons_append, List.singleton_append, List.nil_append]
    exact List.Perm.cons _ ((ih.cons _).trans List.perm_middle.symm)

theorem cg_mem_atL {es : List (Nat × Lazy S)} {e : Nat × Lazy S} (he : e ∈ es) : e.2.sure ∈ atL es e.1 := by
  unfold atL
  exact List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨he, decide_eq_true rfl⟩, rfl⟩

/-! ## `+copy` at one label -/

/-- **`CopyOKL` gives `CopyRunAt`.** -/
theorem CopyOKL.runAt {g g' : Gen Map} {fs ss rs : List (Nat × Lazy S)} (W : CopyOKL g g' fs ss rs) :
    CopyRunAt g g' fs ss rs := by
  obtain ⟨P, PP, O, A⟩ := W
  refine ⟨P, PP, O, fun k hpre hpw => ?_⟩
  obtain ⟨cs, eP, dF, dS, pR, sP⟩ := A k
  have mF : ∀ p ∈ cs, p.1 ∈ atL fs k ∨ TrivS p.1 := fun p hp =>
    cg_mem_drop dF (List.mem_map_of_mem (f := fun p : CopyE S => p.1) hp)
  have mS : ∀ p ∈ cs, p.2.1 ∈ atL ss k ∨ TrivS p.2.1 := fun p hp =>
    cg_mem_drop dS (List.mem_map_of_mem (f := fun p : CopyE S => p.2.1) hp)
  have good : ∀ F : Sure S, F ∈ atL fs k ∨ F ∈ atL ss k ∨ TrivS F →
      Clean F.ned ∧ Distinct F.ned ∧ ∀ y, NMem F.ned y → y < g.re := by
    rintro F (h | h | h)
    · exact hpre F (List.mem_append_left _ h)
    · exact hpre F (List.mem_append_right _ h)
    · rw [h.1]; exact ⟨trivial, trivial, fun y hy => absurd hy (by simp [NMem])⟩
  have dF' := dF
  have dS' := dS
  obtain ⟨k1, p1, t1⟩ := dF
  obtain ⟨k2, p2, t2⟩ := dS
  have pwX := cg_pw_triv hpw (t := k1 ++ k2) (fun s hs => by
    rcases List.mem_append.mp hs with h | h
    · exact t1 s h
    · exact t2 s h)
  have pp : ((atL fs k ++ atL ss k) ++ (k1 ++ k2)).Perm (cs.flatMap fun p => [p.1, p.2.1]) := by
    refine List.Perm.trans ?_ ((p1.append p2).trans (cg_flatMap_perm cs).symm)
    simp only [List.append_assoc]
    refine List.Perm.append_left _ ?_
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.perm_append_comm.append_right _
  have big := (pp.pairwise_iff (fun h r hr hr' => h r hr' hr)).mp pwX
  obtain ⟨inP, crP⟩ := List.pairwise_flatMap.mp big
  have pre : ∀ p ∈ cs, CopyPre p.1.ned p.2.1.ned g.re := fun p hp => by
    obtain ⟨c1, d1, l1⟩ := good p.1 ((mF p hp).elim Or.inl (fun h => Or.inr (Or.inr h)))
    obtain ⟨c2, d2, l2⟩ := good p.2.1 ((mS p hp).elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h)))
    have ap : ∀ r, NMem p.1.ned r → ¬ NMem p.2.1.ned r := List.pairwise_pair.mp (inP p hp)
    refine ⟨c1, c2, ⟨d1, d2, ap⟩, fun y hy => ?_⟩
    rcases hy with h | h
    · exact l1 y h
    · exact l2 y h
  have cross : cs.Pairwise (fun p q => ∀ r, NMem (Need.pair p.1.ned p.2.1.ned) r →
      ¬ NMem (Need.pair q.1.ned q.2.1.ned) r) := by
    refine crP.imp fun {p q} h r hr hr' => ?_
    rcases hr with a | a <;> rcases hr' with b | b
    · exact h _ (by simp) _ (by simp) r a b
    · exact h _ (by simp) _ (by simp) r a b
    · exact h _ (by simp) _ (by simp) r a b
    · exact h _ (by simp) _ (by simp) r a b
  have sem := fun p hp => (sP p hp).sem (pre p hp)
  have memR : ∀ M, M ∈ atL rs k ↔ ∃ p ∈ cs, p.2.2.1 = M := fun M => by
    rw [← pR.mem_iff, List.mem_map]
  refine ⟨fun z => ?_, fun M hM => ?_, ?_, ?_, fun lib σ O c gul st' t R z hz => ?_⟩
  · constructor
    · intro h
      refine ⟨fun F hF => ?_, fun T hT => ?_⟩
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (dF'.sub F hF)
        exact (((sem p hp).2.1 z).mp (h _ ((memR _).mpr ⟨p, hp, rfl⟩))).1
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (dS'.sub T hT)
        exact (((sem p hp).2.1 z).mp (h _ ((memR _).mpr ⟨p, hp, rfl⟩))).2
    · rintro ⟨h1, h2⟩ M hM
      obtain ⟨p, hp, rfl⟩ := (memR M).mp hM
      refine ((sem p hp).2.1 z).mpr ⟨?_, ?_⟩
      · rcases mF p hp with h | h
        · exact h1 _ h
        · exact fitsS_trivial h.1 h.2 z
      · rcases mS p hp with h | h
        · exact h2 _ h
        · exact fitsS_trivial h.1 h.2 z
  · obtain ⟨p, hp, rfl⟩ := (memR M).mp hM
    refine ⟨(sem p hp).1, fun y hy => ?_⟩
    rcases (sP p hp).mem y hy with a | a | a
    · rcases mF p hp with h | h
      · exact Or.inl ⟨p.1, List.mem_append_left _ h, a⟩
      · exact absurd a (cg_triv_nmem h y)
    · rcases mS p hp with h | h
      · exact Or.inl ⟨p.2.1, List.mem_append_right _ h, a⟩
      · exact absurd a (cg_triv_nmem h y)
    · exact Or.inr a
  · have pw : (cs.map fun p => p.2.2.1).Pairwise
        (fun M M' => ∀ r, r < g.re → NMem M.ned r → ¬ NMem M'.ned r) := by
      rw [List.pairwise_map]
      refine List.Pairwise.imp_of_mem ?_ cross
      intro p q hp hq h r hr a b
      have old : ∀ x : CopyE S, x ∈ cs → NMem x.2.2.1.ned r → NMem (Need.pair x.1.ned x.2.1.ned) r :=
        fun x hx m => by
          rcases (sP x hx).mem r m with c | c | c
          · exact Or.inl c
          · exact Or.inr c
          · exact absurd hr (Nat.not_lt.mpr c.1)
      exact h r (old p hp a) (old q hq b)
    exact (pR.pairwise_iff (fun h r hr a b => h r hr b a)).mp pw
  · rw [eP]
    intro op hop x hx
    obtain ⟨ops, hops, hop'⟩ := List.mem_flatten.mp hop
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hops
    have Pr := (sP p hp).ra (fun x => (∃ F ∈ atL fs k ++ atL ss k, NMem F.ned x) ∨ g.re ≤ x)
      (fun r hr => (mF p hp).elim (fun h => Or.inl ⟨p.1, List.mem_append_left _ h, hr⟩)
        (fun h => absurd hr (cg_triv_nmem h r)))
      (fun r hr => (mS p hp).elim (fun h => Or.inl ⟨p.2.1, List.mem_append_right _ h, hr⟩)
        (fun h => absurd hr (cg_triv_nmem h r)))
      (fun r hr => Or.inr hr) op hop' x hx
    have Lt := (sP p hp).rb (fun r hr => (pre p hp).lo r (Or.inl hr)) (fun r hr => (pre p hp).lo r (Or.inr hr))
      op hop' x hx
    rcases Pr with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, Lt⟩
  · have hz' : ∀ p ∈ cs, HoldsN p.2.2.1.ned R z := fun p hp => hz _ ((memR _).mpr ⟨p, hp, rfl⟩)
    obtain ⟨R', r, h1, k1'⟩ := copyPieces_run cs sP pre cross lib σ O c gul st' t R z hz'
    refine ⟨R', by rw [eP]; exact r, fun F hF => ?_, fun y hy => k1' y (fun p hp hm => ?_)⟩
    · rcases List.mem_append.mp hF with hF | hF
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (dF'.sub F hF)
        exact (h1 p hp).1
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (dS'.sub F hF)
        exact (h1 p hp).2
    · rcases hm with m | m
      · rcases mF p hp with h | h
        · exact hy p.1 (List.mem_append_left _ h) m
        · exact cg_triv_nmem h y m
      · rcases mS p hp with h | h
        · exact hy p.2.1 (List.mem_append_right _ h) m
        · exact cg_triv_nmem h y m

/-! ## `LabDisj` of the merged tree -/

/-- Registers counted at most once lie in one entry at most. -/
theorem cg_pw_count (Pr : Nat → Prop) : ∀ (es : List (Nat × Lazy S)),
    (∀ r, Pr r → List.count r (Raw.regsL es) ≤ 1) →
    es.Pairwise fun e e' => ∀ r, Pr r → NMem e.2.sure.ned r → ¬ NMem e'.2.sure.ned r
  | [], _ => List.Pairwise.nil
  | e :: rest, h => by
    refine List.pairwise_cons.mpr ⟨fun e' he' r hr m m' => ?_, cg_pw_count Pr rest fun r hr => ?_⟩
    · have h1 := h r hr
      rw [Raw.regsL_cons, List.count_append] at h1
      have a1 : 0 < List.count r (flattenNeed e.2.sure.ned) := List.count_pos_iff.mpr ((mem_flatten _ r).mpr m)
      have a2 : 0 < List.count r (Raw.regsL rest) := List.count_pos_iff.mpr (Raw.mem_regsL.mpr ⟨e', he', m'⟩)
      omega
    · have h1 := h r hr
      rw [Raw.regsL_cons, List.count_append] at h1
      omega

/-- A relation at every label of an entry list, as a relation of its entries at one label. -/
theorem cg_pw_atL (Rel : Sure S → Sure S → Prop) : ∀ (es : List (Nat × Lazy S)),
    (∀ k, (atL es k).Pairwise Rel) → es.Pairwise fun e e' => e.1 = e'.1 → Rel e.2.sure e'.2.sure
  | [], _ => List.Pairwise.nil
  | e :: rest, h => by
    refine List.pairwise_cons.mpr ⟨fun e' he' heq => ?_, cg_pw_atL Rel rest fun k => ?_⟩
    · have h1 := h e.1
      have eq : atL (e :: rest) e.1 = e.2.sure :: atL rest e.1 := by
        simp only [atL, List.filter_cons, decide_true, ↓reduceIte, List.map_cons]
      rw [eq, List.pairwise_cons] at h1
      refine h1.1 _ ?_
      unfold atL
      exact List.mem_map.mpr ⟨e', List.mem_filter.mpr ⟨he', decide_eq_true heq.symm⟩, rfl⟩
    · refine (h k).sublist ?_
      unfold atL
      exact List.Sublist.map _ (List.Sublist.filter _ (List.sublist_cons_self e rest))

/-- **The merged tree of `+copy` meets `LabDisj`.** -/
theorem labDisj_copyLazyL {o : Nat} {a b c : Lazy S} {g g' : Gen Map} (h : copyLazyL o a b g = some (c, g'))
    (hd : g.drop = false) (ha : Raw.LabUniq a) (hb : Raw.LabUniq b)
    (hlo : ∀ k, ∀ F ∈ atL ((o, a) :: entries a) k ++ atL ((o, b) :: entries b) k, ∀ y, NMem F.ned y → y < g.re)
    (hold : ∀ k, (atL ((o, c) :: entries c) k).Pairwise
      (fun M M' => ∀ r, r < g.re → NMem M.ned r → ¬ NMem M'.ned r)) :
    LabDisj c := by
  have CRr := Raw.cr_copyLazyL o a b g g' c h hd ha hb
  obtain ⟨D, -, hcnt⟩ := CRr.cnt
  have low : ∀ e ∈ ((o, a) :: entries a) ++ ((o, b) :: entries b), ∀ y, NMem e.2.sure.ned y → y < g.re := by
    intro e he y hy
    refine hlo e.1 e.2.sure ?_ y hy
    rcases List.mem_append.mp he with he | he
    · exact List.mem_append_left _ (cg_mem_atL he)
    · exact List.mem_append_right _ (cg_mem_atL he)
  have c1 : ∀ r, g.re ≤ r → List.count r (Raw.regsL ((o, c) :: entries c)) ≤ 1 := by
    intro r hr
    have h1 := hcnt r
    have h0 : List.count r (Raw.regsL (((o, a) :: entries a) ++ ((o, b) :: entries b))) = 0 :=
      List.count_eq_zero.mpr (fun hm => by
        obtain ⟨e, he, hm⟩ := Raw.mem_regsL.mp hm
        have := low e he r hm
        omega)
    have h2 := Raw.fr_le_one g.re g'.re r
    rw [List.count_append, h0] at h1
    omega
  have Pf := cg_pw_count (fun r => g.re ≤ r) ((o, c) :: entries c) c1
  have Po := cg_pw_atL _ ((o, c) :: entries c) hold
  have Pc : ((o, c) :: entries c).Pairwise
      (fun e e' => e.1 = e'.1 → ∀ r, NMem e.2.sure.ned r → ¬ NMem e'.2.sure.ned r) :=
    (List.pairwise_and_iff.mpr ⟨Pf, Po⟩).imp fun hh heq r hr hr' => by
      by_cases lt : r < g.re
      · exact hh.2 heq r lt hr hr'
      · exact hh.1 r (Nat.not_lt.mp lt) hr hr'
  exact (List.pairwise_cons.mp Pc).2

end Comp
end SkaModel
end Formalization
