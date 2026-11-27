import lemmas.Ska.CompGenConsB
import lemmas.Ska.RawInvCLLab
import lemmas.Ska.RawInvCLCopyMerge

/-!
# The cons in `RunOKGen`: `+copy-lazy` per label

README Gaps 12.39, item 10.  `copyLazyL_okL` (mutual with `mergeForks_okL`,
`mergeBonds_okL`): `+copy-lazy` of two trees meets `CopyOKL`, when both are
`LabUniq` (at every node bonds at distinct labels and forks at distinct
`yes` labels, track D's `Raw.LabUniq`): the forks (bonds) of the second
that the first names are merged once each, the others kept, so every need
of the second is some piece's second need (`match_perm`).

* `trivS_bunt`, `DropT.nil_of_triv`, `CopyOKL.keepL`, `CopyOKL.keepR`,
  `CopyOKL.base`, `CopyOKL.ofEq`.
* `matchG` (the entries of the second the first names, through the index),
  `match_perm`.
* **`copyLazyL_okL`**, `mergeForks_okL`, `mergeBonds_okL`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

theorem trivS_bunt : TrivS (Sure.bunt : Sure S) :=
  ⟨rfl, (HoonSet.small_iff _).2 fun x hx => absurd hx (HoonSet.mem_empty x)⟩

theorem nodup_of_map {α β : Type} (f : α → β) {l : List α} (h : (l.map f).Nodup) : l.Nodup :=
  List.Pairwise.of_map f (fun a b h e => h (congrArg f e)) h

theorem DropT.nil_of_triv {l : List (Sure S)} (h : ∀ s ∈ l, TrivS s) : DropT l [] := ⟨l, by simp, h⟩

theorem atL_nil (k : Nat) : atL ([] : List (Nat × Lazy S)) k = [] := by simp [atL]

/-- **Entries of the first kept as they were.** -/
theorem CopyOKL.keepL (g : Gen Map) (es : List (Nat × Lazy S)) : CopyOKL (Map := Map) g g es [] es := by
  refine ⟨fun _ => [], Pref.refl g, fun _ _ => rfl, fun k =>
    ⟨(atL es k).map fun L => (L, Sure.bunt, L, []), ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp [List.flatten_eq_nil_iff]
  · simp only [List.map_map, Function.comp_def]; simp only [List.map_id']; exact DropT.refl _
  · rw [atL_nil]
    refine DropT.nil_of_triv ?_
    intro s hs
    simp only [List.map_map, Function.comp_def, List.mem_map] at hs
    obtain ⟨_, _, rfl⟩ := hs
    exact trivS_bunt
  · simp only [List.map_map, Function.comp_def]; simp only [List.map_id']; exact List.Perm.refl _
  · intro p hp
    obtain ⟨L, _, rfl⟩ := List.mem_map.mp hp
    exact copyP_left _ _ L

/-- **Entries of the second kept as they were.** -/
theorem CopyOKL.keepR (g : Gen Map) (es : List (Nat × Lazy S)) : CopyOKL (Map := Map) g g [] es es := by
  refine ⟨fun _ => [], Pref.refl g, fun _ _ => rfl, fun k =>
    ⟨(atL es k).map fun L => (Sure.bunt, L, L, []), ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp [List.flatten_eq_nil_iff]
  · rw [atL_nil]
    refine DropT.nil_of_triv ?_
    intro s hs
    simp only [List.map_map, Function.comp_def, List.mem_map] at hs
    obtain ⟨_, _, rfl⟩ := hs
    exact trivS_bunt
  · simp only [List.map_map, Function.comp_def]; simp only [List.map_id']; exact DropT.refl _
  · simp only [List.map_map, Function.comp_def]; simp only [List.map_id']; exact List.Perm.refl _
  · intro p hp
    obtain ⟨L, _, rfl⟩ := List.mem_map.mp hp
    exact copyP_right _ _ L

theorem CopyOKL.ofEq {g g' : Gen Map} {fs ss rs fs' ss' rs' : List (Nat × Lazy S)} (W : CopyOKL g g' fs ss rs)
    (hf : fs = fs') (hs : ss = ss') (hr : rs = rs') : CopyOKL g g' fs' ss' rs' := by
  subst hf hs hr; exact W

/-- **The merge of two sure needs at a block** is the copy per label of the
root entries. -/
theorem CopyOKL.base {o : Nat} {s1 s2 s' : Sure S} {g g' : Gen Map} (h : copyLazy o s1 s2 g = some (s', g'))
    (hd : g.drop = false) (l1 l2 l' : Lazy S) (e1 : l1.sure = s1) (e2 : l2.sure = s2) (e' : l'.sure = s') :
    CopyOKL g g' [(o, l1)] [(o, l2)] [(o, l')] := by
  obtain ⟨A, PA, CP⟩ := copyP_root h hd
  refine ⟨fun k => if k = o then A else [], PA, fun k hk => ?_, fun k => ?_⟩
  · have : k ≠ o := fun e => hk (by simp [e])
    simp [this]
  · by_cases e : k = o
    · subst e
      refine ⟨[(s1, s2, s', A)], by simp, by simp [atL_single, e1, DropT.refl], by simp [atL_single, e2, DropT.refl],
        by simp [atL_single, e'], fun p hp => ?_⟩
      rw [List.mem_singleton.mp hp]; exact CP
    · have e'' : o ≠ k := fun x => e x.symm
      exact ⟨[], by simp [e], by simp [atL_single, e'', DropT.refl], by simp [atL_single, e'', DropT.refl],
        by simp [atL_single, e''], fun _ h => by simp at h⟩

/-! ## The entries of the second that the first names -/

/-- The entries of the second the first names, through the index. -/
def matchG {α : Type} (key : α → Nat) (idx : Map α) (l1 : List α) : List α :=
  l1.filterMap fun e => HoonMap.get idx (key e)

theorem matchG_keys_sub {α : Type} (key : α → Nat) (idx : Map α) (hk : ∀ k e, HoonMap.get idx k = some e → key e = k) :
    ∀ l1 : List α, ((matchG key idx l1).map key).Sublist (l1.map key)
  | [] => by simp [matchG]
  | x :: rest => by
    have ih := matchG_keys_sub key idx hk rest
    cases hg : HoonMap.get idx (key x) with
    | none =>
      simp only [matchG, List.filterMap_cons, hg, List.map_cons] at ih ⊢
      exact ih.cons _
    | some e =>
      simp only [matchG, List.filterMap_cons, hg, List.map_cons] at ih ⊢
      rw [hk _ e hg]
      exact ih.cons_cons _

theorem mem_matchG {α : Type} (key : α → Nat) {l1 l2 : List α} (h2 : (l2.map key).Nodup) (e : α) :
    e ∈ matchG key (index (Map := Map) key l2) l1 ↔ e ∈ l2 ∧ key e ∈ l1.map key := by
  unfold matchG
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, hg⟩
    obtain ⟨he, hk⟩ := Raw.gm_index_get (Map := Map) key hg
    exact ⟨he, List.mem_map.mpr ⟨x, hx, hk.symm⟩⟩
  · rintro ⟨he, hm⟩
    obtain ⟨x, hx, hk⟩ := List.mem_map.mp hm
    exact ⟨x, hx, by rw [hk]; exact Raw.gm_index_mem (Map := Map) key h2 he⟩

/-- **The named entries and the others are the second's entries**, when the
keys of both lists are distinct. -/
theorem match_perm {α : Type} (key : α → Nat) {l1 l2 : List α} (h1 : (l1.map key).Nodup) (h2 : (l2.map key).Nodup) :
    (matchG key (index (Map := Map) key l2) l1 ++ l2.filter (fun e => !(seen (S := S) key l1 (key e)))).Perm l2 := by
  have hk : ∀ k e, HoonMap.get (index (Map := Map) key l2) k = some e → key e = k :=
    fun k e h => (Raw.gm_index_get (Map := Map) key h).2
  have nm : (matchG key (index (Map := Map) key l2) l1).Nodup :=
    nodup_of_map key ((matchG_keys_sub key _ hk l1).nodup h1)
  have nf : (l2.filter (fun e => !(seen (S := S) key l1 (key e)))).Nodup :=
    nodup_of_map key (((List.filter_sublist).map key).nodup h2)
  have nd : (matchG key (index (Map := Map) key l2) l1 ++ l2.filter (fun e => !(seen (S := S) key l1 (key e)))).Nodup := by
    rw [List.nodup_append]
    refine ⟨nm, nf, fun a ha b hb hab => ?_⟩
    subst hab
    have := ((mem_matchG (Map := Map) key h2 a).mp ha).2
    have hs := (List.mem_filter.mp hb).2
    rw [(Raw.gm_seen (S := S) key l1 (key a)).mpr this] at hs
    simp at hs
  refine (List.perm_ext_iff_of_nodup nd (nodup_of_map key h2)).mpr fun e => ?_
  rw [List.mem_append, mem_matchG (Map := Map) key h2, List.mem_filter]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro he
    by_cases hm : key e ∈ l1.map key
    · exact Or.inl ⟨he, hm⟩
    · refine Or.inr ⟨he, ?_⟩
      cases hs : seen (S := S) key l1 (key e) with
      | false => rfl
      | true => exact absurd ((Raw.gm_seen (S := S) key l1 (key e)).mp hs) hm

/-! ## `+copy-lazy` per label -/

theorem fe_flatMap : ∀ (l : List (ForkE S)),
    forkEntries l = l.flatMap fun x => ((x.1.1, x.1.2) :: entries x.1.2) ++ ((x.2.1, x.2.2) :: entries x.2.2)
  | [] => by simp [forkEntries]
  | ((oy, y), (on, n)) :: rest => by
    simp only [forkEntries, List.flatMap_cons, fe_flatMap rest, List.append_assoc]

theorem be_flatMap : ∀ (l : List (Nat × Lazy S)), bondEntries l = l.flatMap fun x => (x.1, x.2) :: entries x.2
  | [] => by simp [bondEntries]
  | (o, l) :: rest => by simp only [bondEntries, List.flatMap_cons, be_flatMap rest]

theorem fe_perm {l l' : List (ForkE S)} (h : l.Perm l') : (forkEntries l).Perm (forkEntries l') := by
  rw [fe_flatMap, fe_flatMap]; exact h.flatMap_right _

theorem be_perm {l l' : List (Nat × Lazy S)} (h : l.Perm l') : (bondEntries l).Perm (bondEntries l') := by
  rw [be_flatMap, be_flatMap]; exact h.flatMap_right _

theorem pe_root (o : Nat) (x : Lazy S) (A B : List (Nat × Lazy S)) :
    ([(o, x)] ++ A ++ B).Perm ((o, x) :: (B ++ A)) := by
  simp only [List.singleton_append, List.cons_append]
  exact List.Perm.cons _ List.perm_append_comm

-- The three theorems are one command: the heartbeats of their bodies add up.
set_option maxHeartbeats 1600000

mutual
/-- **`+copy-lazy` per label**: the merge of two `LabUniq` trees at `o`. -/
theorem copyLazyL_okL : ∀ (o : Nat) (first second : Lazy S) (g g' : Gen Map) (res : Lazy S),
    copyLazyL o first second g = some (res, g') → g.drop = false → Raw.LabUniq first → Raw.LabUniq second →
    CopyOKL g g' ((o, first) :: entries first) ((o, second) :: entries second) ((o, res) :: entries res)
  | o, mk s1 f1 b1, second, g, g', res, h, hd, lu1, lu2 => by
    rw [copyLazyL] at h
    obtain ⟨⟨ned, ops⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨u, g2, h2, h⟩ := bind_some h
    cases u
    obtain ⟨fork, g3, h3, h⟩ := bind_some h
    obtain ⟨bond, g4, h4, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hc : copyLazy o s1 second.sure g = some (⟨ned, HoonSet.uni s1.lok second.sure.lok⟩, g2) := by
      simp only [copyLazy, bind_apply, h1, Option.bind_some, h2, pure_apply]
    have W0 := CopyOKL.base hc hd (mk s1 f1 b1) second
      (mk ⟨ned, HoonSet.uni s1.lok second.sure.lok⟩ fork bond) rfl rfl rfl
    have d2 : g2.drop = false := W0.drop.trans hd
    obtain ⟨nb1, nf1, lb1, lf1⟩ := (Raw.labUniq_mk s1 f1 b1).mp lu1
    have lu2' : Raw.LabUniq (mk second.sure second.fork second.bond) := by rw [eta]; exact lu2
    obtain ⟨nb2, nf2, lb2, lf2⟩ := (Raw.labUniq_mk _ _ _).mp lu2'
    have WF : CopyOKL g2 g3 (forkEntries f1) (forkEntries second.fork) (forkEntries fork) := by
      by_cases e1 : second.fork.isEmpty = true
      · rw [if_pos e1] at h3
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
        obtain ⟨rfl, rfl⟩ := h3
        rw [List.isEmpty_iff.mp e1]
        exact (CopyOKL.keepL g2 _).ofEq rfl (by simp [forkEntries]) rfl
      · rw [if_neg e1] at h3
        by_cases e2 : f1.isEmpty = true
        · rw [if_pos e2] at h3
          simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
          obtain ⟨rfl, rfl⟩ := h3
          rw [List.isEmpty_iff.mp e2]
          exact (CopyOKL.keepR g2 _).ofEq (by simp [forkEntries]) rfl rfl
        · rw [if_neg e2] at h3
          obtain ⟨merged, g3', hm, h3⟩ := bind_some h3
          simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
          obtain ⟨rfl, rfl⟩ := h3
          have MF := mergeForks_okL _ f1 g2 g3' merged hm d2 (fun k e he => by
              obtain ⟨hm', hk⟩ := Raw.gm_index_get (Map := Map) _ he
              exact ⟨hk, lf2 e hm'⟩) lf1
          have KR := CopyOKL.keepR (Map := Map) g3'
            (forkEntries (second.fork.filter fun e => !(seen (S := S) (fun e : ForkE S => e.1.1) f1 e.1.1)))
          refine (MF.trans KR).perm (List.Perm.of_eq (List.append_nil _)) ?_ (List.Perm.of_eq (Raw.fe_append _ _).symm)
          rw [← Raw.fe_append]
          exact fe_perm (match_perm (Map := Map) (fun e : ForkE S => e.1.1) nf1 nf2)
    have d3 : g3.drop = false := WF.drop.trans d2
    have WB : CopyOKL g3 g4 (bondEntries b1) (bondEntries second.bond) (bondEntries bond) := by
      by_cases e1 : second.bond.isEmpty = true
      · rw [if_pos e1] at h4
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
        obtain ⟨rfl, rfl⟩ := h4
        rw [List.isEmpty_iff.mp e1]
        exact (CopyOKL.keepL g3 _).ofEq rfl (by simp [bondEntries]) rfl
      · rw [if_neg e1] at h4
        by_cases e2 : b1.isEmpty = true
        · rw [if_pos e2] at h4
          simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
          obtain ⟨rfl, rfl⟩ := h4
          rw [List.isEmpty_iff.mp e2]
          exact (CopyOKL.keepR g3 _).ofEq (by simp [bondEntries]) rfl rfl
        · rw [if_neg e2] at h4
          obtain ⟨merged, g4', hm, h4⟩ := bind_some h4
          simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
          obtain ⟨rfl, rfl⟩ := h4
          have MB := mergeBonds_okL _ b1 g3 g4' merged hm d3 (fun k e he => by
              obtain ⟨hm', hk⟩ := Raw.gm_index_get (Map := Map) _ he
              exact ⟨hk, lb2 e hm'⟩) lb1
          have KR := CopyOKL.keepR (Map := Map) g4'
            (bondEntries (second.bond.filter fun e => !(seen (S := S) (fun e : Nat × Lazy S => e.1) b1 e.1)))
          refine (MB.trans KR).perm (List.Perm.of_eq (List.append_nil _)) ?_ (List.Perm.of_eq (Raw.be_append _ _).symm)
          rw [← Raw.be_append]
          exact be_perm (match_perm (Map := Map) (fun e : Nat × Lazy S => e.1) nb1 nb2)
    refine ((W0.trans WF).trans WB).perm (pe_root _ _ _ _) ?_ (pe_root _ _ _ _)
    rw [Raw.entries_parts second]
    exact pe_root _ _ _ _

/-- Its spin over the forks of the first. -/
theorem mergeForks_okL : ∀ (idx : Map (ForkE S)) (f1 : List (ForkE S)) (g g' : Gen Map) (m : List (ForkE S)),
    mergeForks idx f1 g = some (m, g') → g.drop = false →
    (∀ k e, HoonMap.get idx k = some e → e.1.1 = k ∧ Raw.LabUniq e.1.2 ∧ Raw.LabUniq e.2.2) →
    (∀ x ∈ f1, Raw.LabUniq x.1.2 ∧ Raw.LabUniq x.2.2) →
    CopyOKL g g' (forkEntries f1) (forkEntries (matchG (fun e : ForkE S => e.1.1) idx f1)) (forkEntries m)
  | idx, [], g, g', m, h, _, _, _ => by
    simp only [mergeForks, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (CopyOKL.nil g).ofEq rfl (by simp [matchG, forkEntries]) rfl
  | idx, ((oy, y), (on, n)) :: rest, g, g', m, h, hd, hi, hl => by
    unfold mergeForks at h
    obtain ⟨e, g1, h1, h⟩ := bind_some h
    obtain ⟨r, g2, h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hl' : ∀ x ∈ rest, Raw.LabUniq x.1.2 ∧ Raw.LabUniq x.2.2 := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    cases hg : HoonMap.get idx oy with
    | none =>
      rw [hg] at h1
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      have IH := mergeForks_okL idx rest g g2 r h2 hd hi hl'
      refine ((CopyOKL.keepL (Map := Map) g (forkEntries [((oy, y), (on, n))])).trans IH).ofEq ?_ ?_ ?_
      · simp [forkEntries]
      · simp [matchG, hg, forkEntries]
      · simp [forkEntries]
    | some me =>
      obtain ⟨⟨oy', my⟩, ⟨mon, mn⟩⟩ := me
      rw [hg] at h1
      simp only at h1
      by_cases hon : on = mon
      · rw [if_pos hon] at h1
        obtain ⟨y', g3, h3, h1⟩ := bind_some h1
        obtain ⟨n', g4, h4, h1⟩ := bind_some h1
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        obtain ⟨hk, lmy, lmn⟩ := hi oy _ hg
        simp only at hk
        subst hk
        subst hon
        have Wy := copyLazyL_okL oy' y my g g3 y' h3 hd (hl _ List.mem_cons_self).1 lmy
        have d3 : g3.drop = false := by rw [CopyOKL.drop Wy]; exact hd
        have ln : Raw.LabUniq n := (hl ((oy', y), (on, n)) List.mem_cons_self).2
        have lmn' : Raw.LabUniq mn := lmn
        have h4' : copyLazyL on n mn g3 = some (n', g4) := h4
        have Wn : CopyOKL g3 g4 ((on, n) :: entries n) ((on, mn) :: entries mn) ((on, n') :: entries n') :=
          copyLazyL_okL on n mn g3 g4 n' h4' d3 ln lmn'
        have IH := mergeForks_okL idx rest g4 g2 r h2 (Wn.drop.trans d3) hi hl'
        refine ((Wy.trans Wn).trans IH).ofEq ?_ ?_ ?_
        · simp [forkEntries]
        · simp [matchG, hg, forkEntries]
        · simp [forkEntries]
      · rw [if_neg hon] at h1; cases h1

/-- Its spin over the bonds of the first. -/
theorem mergeBonds_okL : ∀ (idx : Map (Nat × Lazy S)) (b1 : List (Nat × Lazy S)) (g g' : Gen Map)
    (m : List (Nat × Lazy S)),
    mergeBonds idx b1 g = some (m, g') → g.drop = false →
    (∀ k e, HoonMap.get idx k = some e → e.1 = k ∧ Raw.LabUniq e.2) →
    (∀ x ∈ b1, Raw.LabUniq x.2) →
    CopyOKL g g' (bondEntries b1) (bondEntries (matchG (fun e : Nat × Lazy S => e.1) idx b1)) (bondEntries m)
  | idx, [], g, g', m, h, _, _, _ => by
    simp only [mergeBonds, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (CopyOKL.nil g).ofEq rfl (by simp [matchG, bondEntries]) rfl
  | idx, (ob, l) :: rest, g, g', m, h, hd, hi, hl => by
    unfold mergeBonds at h
    obtain ⟨e, g1, h1, h⟩ := bind_some h
    obtain ⟨r, g2, h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hl' : ∀ x ∈ rest, Raw.LabUniq x.2 := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    cases hg : HoonMap.get idx ob with
    | none =>
      rw [hg] at h1
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      have IH := mergeBonds_okL idx rest g g2 r h2 hd hi hl'
      refine ((CopyOKL.keepL (Map := Map) g (bondEntries [(ob, l)])).trans IH).ofEq ?_ ?_ ?_
      · simp [bondEntries]
      · simp [matchG, hg, bondEntries]
      · simp [bondEntries]
    | some me =>
      obtain ⟨ob', mm⟩ := me
      rw [hg] at h1
      simp only at h1
      obtain ⟨l', g3, h3, h1⟩ := bind_some h1
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨hk, lm⟩ := hi ob _ hg
      simp only at hk
      subst hk
      have Wl := copyLazyL_okL ob' l mm g g3 l' h3 hd (hl _ List.mem_cons_self) lm
      have IH := mergeBonds_okL idx rest g3 g2 r h2 (Wl.drop.trans hd) hi hl'
      refine (Wl.trans IH).ofEq ?_ ?_ ?_
      · simp [bondEntries]
      · simp [matchG, hg, bondEntries]
      · simp [bondEntries]
end

end Comp
end SkaModel
end Formalization
