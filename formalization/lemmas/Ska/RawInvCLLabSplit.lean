import lemmas.Ska.RawInvCLLab
import lemmas.Ska.CompSixNxTag
import lemmas.Ska.CompFromRun

/-!
# `LabUniq` through `+split`, `+into` and `+from`

README Gaps 14 (b), track D.  The steps of a run that take a goal's lazy
tree apart keep `LabUniq` (bonds at distinct labels and forks at distinct
`yes` labels at every node) and the labels of the entries:

* `lq_splitLoop` (mutual with `lq_splitForks`, `lq_splitBonds`: the halves
  keep the label lists and `LabUniq` of every child; the prune only drops
  children), **`lab_splitL`**;
* `lq_intoLoopL` (mutual with `lq_intoForks`, `lq_intoBonds`), **`lab_intoL`**;
* `lu_fromL` (mutual with `lu_fromForks`, `lu_fromBonds`), **`lab_fromL`**
  (the labels by `fromL_ent`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## `+split` -/

mutual
/-- **`+split` keeps `LabUniq` and the labels of the entries.** -/
theorem lq_splitLoop {Q : Nat → Prop} : ∀ (l : Lazy S) (o : Nat) (g g' : Comp.Gen Map) (x : Lazy S × Lazy S),
    splitLoop l o g = some (x, g') → LabUniq l → (∀ e ∈ entries l, Q e.1) →
    LabUniq x.1 ∧ LabUniq x.2 ∧ (∀ e ∈ entries x.1, Q e.1) ∧ ∀ e ∈ entries x.2, Q e.1
  | mk s f b, o, g, g', x, h, hl, hq => by
    rw [splitLoop] at h
    obtain ⟨⟨sh, st⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨hb, hf, hB, hF⟩ := (labUniq_mk s f b).mp hl
    cases hfb : (f.isEmpty && b.isEmpty)
    · simp only [fork_mk, bond_mk, hfb, Bool.false_eq_true, if_false] at h
      obtain ⟨⟨fh, ft⟩, g2, h2, h⟩ := bind_some h
      obtain ⟨⟨bh, bt⟩, g3, h3, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨F1, F2, F3, F4, F5, F6⟩ := lq_splitForks f g1 g2 _ h2 hF
        (fun e he => hq e (by simp only [entries, List.mem_append]; exact Or.inr he))
      obtain ⟨B1, B2, B3, B4, B5, B6⟩ := lq_splitBonds b g2 g3 _ h3 hB
        (fun e he => hq e (by simp only [entries, List.mem_append]; exact Or.inl he))
      refine ⟨labUniq_prune ((labUniq_mk _ _ _).mpr ⟨?_, ?_, B3, F3⟩),
        labUniq_prune ((labUniq_mk _ _ _).mpr ⟨?_, ?_, B4, F4⟩), fun e he => ?_, fun e he => ?_⟩
      · simp only [B1]; exact hb
      · simp only [F1]; exact hf
      · simp only [B2]; exact hb
      · simp only [F2]; exact hf
      · have he' := entries_prune_sub _ e he
        simp only [entries, List.mem_append] at he'
        rcases he' with a | a
        · exact B5 e a
        · exact F5 e a
      · have he' := entries_prune_sub _ e he
        simp only [entries, List.mem_append] at he'
        rcases he' with a | a
        · exact B6 e a
        · exact F6 e a
    · simp only [fork_mk, bond_mk, hfb, if_true, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨labUniq_ofSure _, labUniq_ofSure _, fun e he => by simp [entries_ofSure] at he,
        fun e he => by simp [entries_ofSure] at he⟩

theorem lq_splitForks {Q : Nat → Prop} : ∀ (f : List (ForkE S)) (g g' : Comp.Gen Map)
    (x : List (ForkE S) × List (ForkE S)),
    splitForks f g = some (x, g') → (∀ y ∈ f, LabUniq y.1.2 ∧ LabUniq y.2.2) → (∀ e ∈ forkEntries f, Q e.1) →
    x.1.map (·.1.1) = f.map (·.1.1) ∧ x.2.map (·.1.1) = f.map (·.1.1) ∧
      (∀ y ∈ x.1, LabUniq y.1.2 ∧ LabUniq y.2.2) ∧ (∀ y ∈ x.2, LabUniq y.1.2 ∧ LabUniq y.2.2) ∧
      (∀ e ∈ forkEntries x.1, Q e.1) ∧ ∀ e ∈ forkEntries x.2, Q e.1
  | [], g, g', x, h, _, _ => by
    rw [splitForks] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, rfl, fun y hy => absurd hy List.not_mem_nil, fun y hy => absurd hy List.not_mem_nil,
      fun e he => by simp [forkEntries] at he, fun e he => by simp [forkEntries] at he⟩
  | ((oy, y), (on, n)) :: rest, g, g', x, h, hl, hq => by
    rw [splitForks] at h
    obtain ⟨⟨yh, yt⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨⟨nh, nt⟩, g2, h2, h⟩ := bind_some h
    obtain ⟨⟨rh, rt⟩, g3, h3, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have l0 := hl _ List.mem_cons_self
    have Y := lq_splitLoop y oy g g1 _ h1 l0.1 (fun e he => hq e (by simp [forkEntries, he]))
    have N := lq_splitLoop n on g1 g2 _ h2 l0.2 (fun e he => hq e (by simp [forkEntries, he]))
    obtain ⟨R1, R2, R3, R4, R5, R6⟩ := lq_splitForks rest g2 g3 _ h3 (fun z hz => hl z (List.mem_cons_of_mem _ hz))
      (fun e he => hq e (by simp [forkEntries, he]))
    have qy : Q oy := hq (oy, y) (by simp [forkEntries])
    have qn : Q on := hq (on, n) (by simp [forkEntries])
    refine ⟨by simp only [List.map_cons, R1], by simp only [List.map_cons, R2], fun z hz => ?_, fun z hz => ?_,
      fun e he => ?_, fun e he => ?_⟩
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨Y.1, N.1⟩
      · exact R3 z hz
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨Y.2.1, N.2.1⟩
      · exact R4 z hz
    · simp only [forkEntries, List.mem_append, List.mem_cons] at he
      rcases he with ((rfl | he) | (rfl | he)) | he
      · exact qy
      · exact Y.2.2.1 e he
      · exact qn
      · exact N.2.2.1 e he
      · exact R5 e he
    · simp only [forkEntries, List.mem_append, List.mem_cons] at he
      rcases he with ((rfl | he) | (rfl | he)) | he
      · exact qy
      · exact Y.2.2.2 e he
      · exact qn
      · exact N.2.2.2 e he
      · exact R6 e he

theorem lq_splitBonds {Q : Nat → Prop} : ∀ (b : List (Nat × Lazy S)) (g g' : Comp.Gen Map)
    (x : List (Nat × Lazy S) × List (Nat × Lazy S)),
    splitBonds b g = some (x, g') → (∀ e ∈ b, LabUniq e.2) → (∀ e ∈ bondEntries b, Q e.1) →
    x.1.map (·.1) = b.map (·.1) ∧ x.2.map (·.1) = b.map (·.1) ∧
      (∀ e ∈ x.1, LabUniq e.2) ∧ (∀ e ∈ x.2, LabUniq e.2) ∧
      (∀ e ∈ bondEntries x.1, Q e.1) ∧ ∀ e ∈ bondEntries x.2, Q e.1
  | [], g, g', x, h, _, _ => by
    rw [splitBonds] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, rfl, fun y hy => absurd hy List.not_mem_nil, fun y hy => absurd hy List.not_mem_nil,
      fun e he => by simp [bondEntries] at he, fun e he => by simp [bondEntries] at he⟩
  | (o, l) :: rest, g, g', x, h, hl, hq => by
    rw [splitBonds] at h
    obtain ⟨⟨lh, lt⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨⟨rh, rt⟩, g2, h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have L1 := lq_splitLoop l o g g1 _ h1 (hl _ List.mem_cons_self) (fun e he => hq e (by simp [bondEntries, he]))
    obtain ⟨R1, R2, R3, R4, R5, R6⟩ := lq_splitBonds rest g1 g2 _ h2 (fun z hz => hl z (List.mem_cons_of_mem _ hz))
      (fun e he => hq e (by simp [bondEntries, he]))
    have qo : Q o := hq (o, l) (by simp [bondEntries])
    refine ⟨by simp only [List.map_cons, R1], by simp only [List.map_cons, R2], fun z hz => ?_, fun z hz => ?_,
      fun e he => ?_, fun e he => ?_⟩
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact L1.1
      · exact R3 z hz
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact L1.2.1
      · exact R4 z hz
    · simp only [bondEntries, List.mem_append, List.mem_cons] at he
      rcases he with (rfl | he) | he
      · exact qo
      · exact L1.2.2.1 e he
      · exact R5 e he
    · simp only [bondEntries, List.mem_append, List.mem_cons] at he
      rcases he with (rfl | he) | he
      · exact qo
      · exact L1.2.2.2 e he
      · exact R6 e he
end

/-- **`+split` keeps `LabUniq` and the labels of the entries.** -/
theorem lab_splitL {Q : Nat → Prop} {nex : NextL S} {g g' : Comp.Gen Map} {hed tel : Lazy S} {o : Nat}
    (h : splitL nex g = some ((hed, tel, o), g')) (hl : LabUniq nex.laz) (hq : ∀ e ∈ entries nex.laz, Q e.1) :
    LabUniq hed ∧ LabUniq tel ∧ (∀ e ∈ entries hed, Q e.1) ∧ ∀ e ∈ entries tel, Q e.1 := by
  unfold splitL at h
  obtain ⟨o', g1, _, h⟩ := bind_some h
  obtain ⟨⟨h', t'⟩, g2, h2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
  exact lq_splitLoop _ _ _ _ _ h2 hl hq

/-! ## `+into` -/

mutual
/-- **`+into` keeps `LabUniq` and the labels of the entries.** -/
theorem lq_intoLoopL {Q : Nat → Prop} (axe : Nat) : ∀ (l : Lazy S) (o : Nat) (g g' : Comp.Gen Map) (x : Lazy S × Lazy S),
    intoLoopL axe l o g = some (x, g') → LabUniq l → (∀ e ∈ entries l, Q e.1) →
    LabUniq x.1 ∧ LabUniq x.2 ∧ (∀ e ∈ entries x.1, Q e.1) ∧ ∀ e ∈ entries x.2, Q e.1
  | mk s f b, o, g, g', x, h, hl, hq => by
    rw [intoLoopL] at h
    obtain ⟨⟨sh, st⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨hb, hf, hB, hF⟩ := (labUniq_mk s f b).mp hl
    cases hfb : (f.isEmpty && b.isEmpty)
    · simp only [fork_mk, bond_mk, hfb, Bool.false_eq_true, if_false] at h
      obtain ⟨⟨fh, ft⟩, g2, h2, h⟩ := bind_some h
      obtain ⟨⟨bh, bt⟩, g3, h3, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨F1, F2, F3, F4, F5, F6⟩ := lq_intoForks axe f g1 g2 _ h2 hF
        (fun e he => hq e (by simp only [entries, List.mem_append]; exact Or.inr he))
      obtain ⟨B1, B2, B3, B4, B5, B6⟩ := lq_intoBonds axe b g2 g3 _ h3 hB
        (fun e he => hq e (by simp only [entries, List.mem_append]; exact Or.inl he))
      refine ⟨labUniq_prune ((labUniq_mk _ _ _).mpr ⟨?_, ?_, B3, F3⟩),
        labUniq_prune ((labUniq_mk _ _ _).mpr ⟨?_, ?_, B4, F4⟩), fun e he => ?_, fun e he => ?_⟩
      · simp only [B1]; exact hb
      · simp only [F1]; exact hf
      · simp only [B2]; exact hb
      · simp only [F2]; exact hf
      · have he' := entries_prune_sub _ e he
        simp only [entries, List.mem_append] at he'
        rcases he' with a | a
        · exact B5 e a
        · exact F5 e a
      · have he' := entries_prune_sub _ e he
        simp only [entries, List.mem_append] at he'
        rcases he' with a | a
        · exact B6 e a
        · exact F6 e a
    · simp only [fork_mk, bond_mk, hfb, if_true, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨labUniq_ofSure _, labUniq_ofSure _, fun e he => by simp [entries_ofSure] at he,
        fun e he => by simp [entries_ofSure] at he⟩

theorem lq_intoForks {Q : Nat → Prop} (axe : Nat) : ∀ (f : List (ForkE S)) (g g' : Comp.Gen Map)
    (x : List (ForkE S) × List (ForkE S)),
    intoForks axe f g = some (x, g') → (∀ y ∈ f, LabUniq y.1.2 ∧ LabUniq y.2.2) → (∀ e ∈ forkEntries f, Q e.1) →
    x.1.map (·.1.1) = f.map (·.1.1) ∧ x.2.map (·.1.1) = f.map (·.1.1) ∧
      (∀ y ∈ x.1, LabUniq y.1.2 ∧ LabUniq y.2.2) ∧ (∀ y ∈ x.2, LabUniq y.1.2 ∧ LabUniq y.2.2) ∧
      (∀ e ∈ forkEntries x.1, Q e.1) ∧ ∀ e ∈ forkEntries x.2, Q e.1
  | [], g, g', x, h, _, _ => by
    rw [intoForks] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, rfl, fun y hy => absurd hy List.not_mem_nil, fun y hy => absurd hy List.not_mem_nil,
      fun e he => by simp [forkEntries] at he, fun e he => by simp [forkEntries] at he⟩
  | ((oy, y), (on, n)) :: rest, g, g', x, h, hl, hq => by
    rw [intoForks] at h
    obtain ⟨⟨yh, yt⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨⟨nh, nt⟩, g2, h2, h⟩ := bind_some h
    obtain ⟨⟨rh, rt⟩, g3, h3, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have l0 := hl _ List.mem_cons_self
    have Y := lq_intoLoopL axe y oy g g1 _ h1 l0.1 (fun e he => hq e (by simp [forkEntries, he]))
    have N := lq_intoLoopL axe n on g1 g2 _ h2 l0.2 (fun e he => hq e (by simp [forkEntries, he]))
    obtain ⟨R1, R2, R3, R4, R5, R6⟩ := lq_intoForks axe rest g2 g3 _ h3 (fun z hz => hl z (List.mem_cons_of_mem _ hz))
      (fun e he => hq e (by simp [forkEntries, he]))
    have qy : Q oy := hq (oy, y) (by simp [forkEntries])
    have qn : Q on := hq (on, n) (by simp [forkEntries])
    refine ⟨by simp only [List.map_cons, R1], by simp only [List.map_cons, R2], fun z hz => ?_, fun z hz => ?_,
      fun e he => ?_, fun e he => ?_⟩
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨Y.1, N.1⟩
      · exact R3 z hz
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨Y.2.1, N.2.1⟩
      · exact R4 z hz
    · simp only [forkEntries, List.mem_append, List.mem_cons] at he
      rcases he with ((rfl | he) | (rfl | he)) | he
      · exact qy
      · exact Y.2.2.1 e he
      · exact qn
      · exact N.2.2.1 e he
      · exact R5 e he
    · simp only [forkEntries, List.mem_append, List.mem_cons] at he
      rcases he with ((rfl | he) | (rfl | he)) | he
      · exact qy
      · exact Y.2.2.2 e he
      · exact qn
      · exact N.2.2.2 e he
      · exact R6 e he

theorem lq_intoBonds {Q : Nat → Prop} (axe : Nat) : ∀ (b : List (Nat × Lazy S)) (g g' : Comp.Gen Map)
    (x : List (Nat × Lazy S) × List (Nat × Lazy S)),
    intoBonds axe b g = some (x, g') → (∀ e ∈ b, LabUniq e.2) → (∀ e ∈ bondEntries b, Q e.1) →
    x.1.map (·.1) = b.map (·.1) ∧ x.2.map (·.1) = b.map (·.1) ∧
      (∀ e ∈ x.1, LabUniq e.2) ∧ (∀ e ∈ x.2, LabUniq e.2) ∧
      (∀ e ∈ bondEntries x.1, Q e.1) ∧ ∀ e ∈ bondEntries x.2, Q e.1
  | [], g, g', x, h, _, _ => by
    rw [intoBonds] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, rfl, fun y hy => absurd hy List.not_mem_nil, fun y hy => absurd hy List.not_mem_nil,
      fun e he => by simp [bondEntries] at he, fun e he => by simp [bondEntries] at he⟩
  | (o, l) :: rest, g, g', x, h, hl, hq => by
    rw [intoBonds] at h
    obtain ⟨⟨lh, lt⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨⟨rh, rt⟩, g2, h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have L1 := lq_intoLoopL axe l o g g1 _ h1 (hl _ List.mem_cons_self) (fun e he => hq e (by simp [bondEntries, he]))
    obtain ⟨R1, R2, R3, R4, R5, R6⟩ := lq_intoBonds axe rest g1 g2 _ h2 (fun z hz => hl z (List.mem_cons_of_mem _ hz))
      (fun e he => hq e (by simp [bondEntries, he]))
    have qo : Q o := hq (o, l) (by simp [bondEntries])
    refine ⟨by simp only [List.map_cons, R1], by simp only [List.map_cons, R2], fun z hz => ?_, fun z hz => ?_,
      fun e he => ?_, fun e he => ?_⟩
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact L1.1
      · exact R3 z hz
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact L1.2.1
      · exact R4 z hz
    · simp only [bondEntries, List.mem_append, List.mem_cons] at he
      rcases he with (rfl | he) | he
      · exact qo
      · exact L1.2.2.1 e he
      · exact R5 e he
    · simp only [bondEntries, List.mem_append, List.mem_cons] at he
      rcases he with (rfl | he) | he
      · exact qo
      · exact L1.2.2.2 e he
      · exact R6 e he
end


/-- **`+into` keeps `LabUniq` and the labels of the entries.** -/
theorem lab_intoL {Q : Nat → Prop} {nex : NextL S} {axe : Nat} {g g' : Comp.Gen Map} {d r : Lazy S} {o : Nat}
    (h : intoL nex axe g = some ((d, r, o), g')) (hl : LabUniq nex.laz) (hq : ∀ e ∈ entries nex.laz, Q e.1) :
    LabUniq d ∧ LabUniq r ∧ (∀ e ∈ entries d, Q e.1) ∧ ∀ e ∈ entries r, Q e.1 := by
  unfold intoL at h
  obtain ⟨o', g1, _, h⟩ := bind_some h
  obtain ⟨⟨d', r'⟩, g2, h2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
  exact lq_intoLoopL axe _ _ _ _ _ h2 hl hq

/-! ## `+from` -/

mutual
/-- **`+from` keeps `LabUniq`.** -/
theorem lu_fromL (axe : Nat) : ∀ (L L' : Lazy S), fromL axe L = some L' → LabUniq L → LabUniq L'
  | mk s f b, L', h, hl => by
    unfold fromL at h
    split at h
    · obtain ⟨s', _, rfl⟩ := Option.map_eq_some_iff.mp h
      exact labUniq_ofSure _
    · obtain ⟨hb, hf, hB, hF⟩ := (labUniq_mk s f b).mp hl
      obtain ⟨s', _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨f', hf', h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨F1, F2⟩ := lu_fromForks axe f f' hf' hF
      obtain ⟨B1, B2⟩ := lu_fromBonds axe b b' hb' hB
      exact (labUniq_mk _ _ _).mpr ⟨by rw [B1]; exact hb, by rw [F1]; exact hf, B2, F2⟩

theorem lu_fromForks (axe : Nat) : ∀ (f f' : List (ForkE S)), fromForks axe f = some f' →
    (∀ y ∈ f, LabUniq y.1.2 ∧ LabUniq y.2.2) →
    f'.map (·.1.1) = f.map (·.1.1) ∧ ∀ y ∈ f', LabUniq y.1.2 ∧ LabUniq y.2.2
  | [], f', h, _ => by
    simp only [fromForks, Option.some.injEq] at h
    subst h; exact ⟨rfl, fun y hy => absurd hy List.not_mem_nil⟩
  | ((oy, y), (on, n)) :: rest, f', h, hl => by
    simp only [fromForks] at h
    obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨n', hn, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
    have l0 := hl _ List.mem_cons_self
    obtain ⟨R1, R2⟩ := lu_fromForks axe rest r hr (fun z hz => hl z (List.mem_cons_of_mem _ hz))
    refine ⟨by simp only [List.map_cons, R1], fun z hz => ?_⟩
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨lu_fromL axe y y' hy l0.1, lu_fromL axe n n' hn l0.2⟩
    · exact R2 z hz

theorem lu_fromBonds (axe : Nat) : ∀ (b b' : List (Nat × Lazy S)), fromBonds axe b = some b' →
    (∀ e ∈ b, LabUniq e.2) → b'.map (·.1) = b.map (·.1) ∧ ∀ e ∈ b', LabUniq e.2
  | [], b', h, _ => by
    simp only [fromBonds, Option.some.injEq] at h
    subst h; exact ⟨rfl, fun y hy => absurd hy List.not_mem_nil⟩
  | (o, l) :: rest, b', h, hl => by
    simp only [fromBonds] at h
    obtain ⟨l', hl', h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨R1, R2⟩ := lu_fromBonds axe rest r hr (fun z hz => hl z (List.mem_cons_of_mem _ hz))
    refine ⟨by simp only [List.map_cons, R1], fun z hz => ?_⟩
    rcases List.mem_cons.mp hz with rfl | hz
    · exact lu_fromL axe l l' hl' (hl _ List.mem_cons_self)
    · exact R2 z hz
end

/-- **`+from` keeps `LabUniq` and the labels of the entries.** -/
theorem lab_fromL {Q : Nat → Prop} {axe : Nat} {L L' : Lazy S} (h : fromL axe L = some L')
    (hl : LabUniq L) (hq : ∀ e ∈ entries L, Q e.1) : LabUniq L' ∧ ∀ e ∈ entries L', Q e.1 :=
  ⟨lu_fromL axe L L' h hl, fun e he => by
    obtain ⟨l, _, hm⟩ := (fromL_ent axe L L' h).mem_right he
    exact hq (e.1, l) hm⟩

end Raw
end SkaModel
end Formalization
