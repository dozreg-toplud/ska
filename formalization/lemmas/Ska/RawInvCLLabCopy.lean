import lemmas.Ska.RawInvCLLab
import lemmas.Ska.RawInvCLCopyMerge
import lemmas.Ska.CompSixNxTag

/-!
# `LabUniq` through `+copy` and `+past`

README Gaps 14 (b), track D.  Two local steps of `LabUniq` at run level
(`RawInvCLLab.lean`):

* `lu_copyLazyL` (mutual with `lu_mergeForks`, `lu_mergeBonds`):
  `+copy-lazy` keeps `LabUniq` with no other hypothesis.  At a node the
  bonds are `mergeBonds` of `first`'s (the same labels, in order) followed
  by `second`'s whose label `seen` does not find among `first`'s (a sublist
  of `second`'s, apart from `first`'s); forks the same by the `yes` label;
  a merged child is `+copy-lazy` of a child of each side (`gm_index_get`:
  `index` returns a member of `second`'s list).
* **`lab_copyL`**: `+copy` of two `LabUniq` trees is `LabUniq`, and its
  entries' labels are among its inputs' (`copyLazyL_lab`).
* **`lab_pastL`**: `+past` keeps `LabUniq` and "entries below `bo`": the
  new bond's label is `g.bo`, above every entry.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

theorem labUniq_parts {l : Lazy S} (h : LabUniq l) :
    (l.bond.map (·.1)).Nodup ∧ (l.fork.map (·.1.1)).Nodup ∧
      (∀ e ∈ l.bond, LabUniq e.2) ∧ ∀ x ∈ l.fork, LabUniq x.1.2 ∧ LabUniq x.2.2 := by
  rcases l with ⟨s, f, b⟩
  exact (labUniq_mk s f b).mp h

mutual
/-- **`+copy-lazy` keeps `LabUniq`.** -/
theorem lu_copyLazyL (o : Nat) : ∀ (a b : Lazy S) (g g' : Comp.Gen Map) (l : Lazy S),
    copyLazyL o a b g = some (l, g') → LabUniq a → LabUniq b → LabUniq l
  | mk s1 f1 b1, second, g, g', l, h, ha, hb => by
    rw [copyLazyL] at h
    obtain ⟨⟨ned, ops⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨_, g2, h2, h⟩ := bind_some h
    obtain ⟨fork, g3, h3, h⟩ := bind_some h
    obtain ⟨bond, g4, h4, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hb1, hf1, hB1, hF1⟩ := (labUniq_mk s1 f1 b1).mp ha
    obtain ⟨hb2, hf2, hB2, hF2⟩ := labUniq_parts hb
    have F : (fork.map (·.1.1)).Nodup ∧ ∀ x ∈ fork, LabUniq x.1.2 ∧ LabUniq x.2.2 := by
      by_cases c1 : second.fork.isEmpty = true
      · rw [if_pos c1, pure_apply] at h3
        simp only [Option.some.injEq, Prod.mk.injEq] at h3
        obtain ⟨rfl, rfl⟩ := h3
        exact ⟨hf1, hF1⟩
      · rw [if_neg c1] at h3
        by_cases c2 : f1.isEmpty = true
        · rw [if_pos c2, pure_apply] at h3
          simp only [Option.some.injEq, Prod.mk.injEq] at h3
          obtain ⟨rfl, rfl⟩ := h3
          exact ⟨hf2, hF2⟩
        · rw [if_neg c2] at h3
          obtain ⟨merged, g5, h5, h3⟩ := bind_some h3
          simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
          obtain ⟨rfl, rfl⟩ := h3
          obtain ⟨M1, M2⟩ := lu_mergeForks o _ (fun k e' hk => hF2 e' (gm_index_get _ hk).1) f1 g2 g5 merged h5 hF1
          refine ⟨?_, fun x hx => ?_⟩
          · rw [List.map_append, M1, List.nodup_append]
            refine ⟨hf1, (List.filter_sublist.map _).nodup hf2, ?_⟩
            intro a ha' c hc hac
            obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
            have hs := (List.mem_filter.mp hx).2
            subst hac
            have : seen (S := S) (fun e : ForkE S => e.1.1) f1 x.1.1 = true := (gm_seen _ _ _).mpr ha'
            simp [this] at hs
          · rcases List.mem_append.mp hx with hx | hx
            · exact M2 x hx
            · exact hF2 x (List.mem_filter.mp hx).1
    have B : (bond.map (·.1)).Nodup ∧ ∀ x ∈ bond, LabUniq x.2 := by
      by_cases c1 : second.bond.isEmpty = true
      · rw [if_pos c1, pure_apply] at h4
        simp only [Option.some.injEq, Prod.mk.injEq] at h4
        obtain ⟨rfl, rfl⟩ := h4
        exact ⟨hb1, hB1⟩
      · rw [if_neg c1] at h4
        by_cases c2 : b1.isEmpty = true
        · rw [if_pos c2, pure_apply] at h4
          simp only [Option.some.injEq, Prod.mk.injEq] at h4
          obtain ⟨rfl, rfl⟩ := h4
          exact ⟨hb2, hB2⟩
        · rw [if_neg c2] at h4
          obtain ⟨merged, g5, h5, h4⟩ := bind_some h4
          simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
          obtain ⟨rfl, rfl⟩ := h4
          obtain ⟨M1, M2⟩ := lu_mergeBonds o _ (fun k e' hk => hB2 e' (gm_index_get _ hk).1) b1 g3 g5 merged h5 hB1
          refine ⟨?_, fun x hx => ?_⟩
          · rw [List.map_append, M1, List.nodup_append]
            refine ⟨hb1, (List.filter_sublist.map _).nodup hb2, ?_⟩
            intro a ha' c hc hac
            obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
            have hs := (List.mem_filter.mp hx).2
            subst hac
            have : seen (S := S) (fun e : Nat × Lazy S => e.1) b1 x.1 = true := (gm_seen _ _ _).mpr ha'
            simp [this] at hs
          · rcases List.mem_append.mp hx with hx | hx
            · exact M2 x hx
            · exact hB2 x (List.mem_filter.mp hx).1
    exact (labUniq_mk _ _ _).mpr ⟨B.1, F.1, B.2, F.2⟩

/-- The `spin` over the forks keeps the `yes` labels and `LabUniq` of the
children. -/
theorem lu_mergeForks (o : Nat) (idx : Map (ForkE S))
    (hidx : ∀ k e, HoonMap.get idx k = some e → LabUniq e.1.2 ∧ LabUniq e.2.2) :
    ∀ (l : List (ForkE S)) (g g' : Comp.Gen Map) (r : List (ForkE S)),
    mergeForks idx l g = some (r, g') → (∀ x ∈ l, LabUniq x.1.2 ∧ LabUniq x.2.2) →
    r.map (·.1.1) = l.map (·.1.1) ∧ ∀ x ∈ r, LabUniq x.1.2 ∧ LabUniq x.2.2
  | [], g, g', r, h, _ => by
    rw [mergeForks] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩
  | ((oy, y), (on, n)) :: rest, g, g', r, h, hq => by
    rw [mergeForks] at h
    obtain ⟨e1, g1, h1, h⟩ := bind_some h
    obtain ⟨r1, g2, h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have R := lu_mergeForks o idx hidx rest g1 g2 r1 h2 (fun x hx => hq x (List.mem_cons_of_mem _ hx))
    have q0 : LabUniq y ∧ LabUniq n := hq _ List.mem_cons_self
    have E : e1.1.1 = oy ∧ LabUniq e1.1.2 ∧ LabUniq e1.2.2 := by
      cases hget : HoonMap.get idx oy with
      | none =>
        simp only [hget, pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact ⟨rfl, q0⟩
      | some v =>
        rcases v with ⟨⟨fst, my⟩, ⟨mon, mn⟩⟩
        simp only [hget] at h1
        by_cases hon : on = mon
        · rw [if_pos hon] at h1
          obtain ⟨y', g3, h3, h1⟩ := bind_some h1
          obtain ⟨n', g4, h4, h1⟩ := bind_some h1
          simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
          obtain ⟨rfl, rfl⟩ := h1
          have I := hidx _ _ hget
          exact ⟨rfl, lu_copyLazyL oy y my g g3 y' h3 q0.1 I.1, lu_copyLazyL on n mn g3 g4 n' h4 q0.2 I.2⟩
        · rw [if_neg hon] at h1; cases h1
    refine ⟨by simp only [List.map_cons, E.1, R.1], fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact E.2
    · exact R.2 x hx

/-- The `spin` over the bonds keeps the labels and `LabUniq` of the
children. -/
theorem lu_mergeBonds (o : Nat) (idx : Map (Nat × Lazy S))
    (hidx : ∀ k e, HoonMap.get idx k = some e → LabUniq e.2) :
    ∀ (l : List (Nat × Lazy S)) (g g' : Comp.Gen Map) (r : List (Nat × Lazy S)),
    mergeBonds idx l g = some (r, g') → (∀ x ∈ l, LabUniq x.2) →
    r.map (·.1) = l.map (·.1) ∧ ∀ x ∈ r, LabUniq x.2
  | [], g, g', r, h, _ => by
    rw [mergeBonds] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩
  | (ob, l) :: rest, g, g', r, h, hq => by
    rw [mergeBonds] at h
    obtain ⟨e1, g1, h1, h⟩ := bind_some h
    obtain ⟨r1, g2, h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have R := lu_mergeBonds o idx hidx rest g1 g2 r1 h2 (fun x hx => hq x (List.mem_cons_of_mem _ hx))
    have q0 : LabUniq l := hq _ List.mem_cons_self
    have E : e1.1 = ob ∧ LabUniq e1.2 := by
      cases hget : HoonMap.get idx ob with
      | none =>
        simp only [hget, pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact ⟨rfl, q0⟩
      | some v =>
        rcases v with ⟨fst, m⟩
        simp only [hget] at h1
        obtain ⟨l', g3, h3, h1⟩ := bind_some h1
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact ⟨rfl, lu_copyLazyL ob l m g g3 l' h3 q0 (hidx _ _ hget)⟩
    refine ⟨by simp only [List.map_cons, E.1, R.1], fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact E.2
    · exact R.2 x hx
end

/-- **`+copy` keeps `LabUniq`**, and its entries lie at labels of its
inputs' entries. -/
theorem lab_copyL {Q : Nat → Prop} {first : NextL S} {second : Lazy S} {g g' : Comp.Gen Map} {nex : NextL S}
    (h : copyL first second g = some (nex, g')) (h1 : LabUniq first.laz) (h2 : LabUniq second)
    (q1 : ∀ e ∈ entries first.laz, Q e.1) (q2 : ∀ e ∈ entries second, Q e.1) :
    LabUniq nex.laz ∧ ∀ e ∈ entries nex.laz, Q e.1 := by
  unfold copyL at h
  obtain ⟨o, ga, ha, h⟩ := bind_some h
  obtain ⟨laz, gb, hb, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨lu_copyLazyL o first.laz second ga gb laz hb h1 h2, copyLazyL_lab o first.laz second ga gb laz hb q1 q2⟩

/-- **`+past` keeps `LabUniq`** and the entries below `bo`: its new bond's
label `g.bo` is above every entry of the need it parks. -/
theorem lab_pastL {cod : Bell → Option Bool} {nex : NextL S} {nom : Nomm} {region : List Nat}
    {g g' : Comp.Gen Map} {nex' : NextL S} (h : pastL cod nex nom region g = some (nex', g'))
    (hl : LabUniq nex.laz) (hq : ∀ e ∈ entries nex.laz, e.1 < g.bo) :
    LabUniq nex'.laz ∧ ∀ e ∈ entries nex'.laz, e.1 < g'.bo := by
  obtain ⟨⟨s, f, b⟩, th⟩ := nex
  unfold pastL at h
  split at h
  · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hl, hq⟩
  rcases hh : hinted cod nom with _ | ⟨_ | _⟩
  · rw [hh] at h; cases h
  · rw [hh] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hl, hq⟩
  rw [hh] at h
  dsimp only at h
  obtain ⟨o, ga, ha, h⟩ := bind_some h
  rw [emit_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨u, gb, hb, h⟩ := bind_some h
  rw [setTag_apply] at hb
  simp only [Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨-, rfl⟩ := hb
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hbo : ((g.emitted ⟨[], [], Termin.hop th⟩).tagged g.bo region).bo = g.bo + 1 := by
    simp [Gen.emitted]
  obtain ⟨hb, hf, hB, hF⟩ := (labUniq_mk s f b).mp hl
  have hE : ∀ e, e ∈ bondEntries b ∨ e ∈ forkEntries f → e.1 < g.bo := fun e he =>
    hq e (by simp only [entries, List.mem_append]; exact he)
  have hbl : ∀ x ∈ b, x.1 < g.bo := fun x hx => hE x (Or.inl (bondEntries_of_mem hx).1)
  refine ⟨(labUniq_mk _ _ _).mpr ⟨?_, List.nodup_nil, fun e he => ?_, fun x hx => absurd hx List.not_mem_nil⟩, ?_⟩
  · rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, hb⟩
    obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hm
    have := hbl x hx
    simp only at hxe
    omega
  · rcases List.mem_cons.mp he with rfl | he
    · exact (labUniq_mk s f []).mpr ⟨List.nodup_nil, hf, fun _ h => absurd h List.not_mem_nil, hF⟩
    · exact hB e he
  · intro e he
    rw [hbo]
    simp only [entries, bondEntries, List.mem_append, List.mem_cons] at he
    rcases he with ((rfl | (he | he)) | he) | he
    · exact Nat.lt_succ_self _
    · simp at he
    · exact Nat.lt_succ_of_lt (hE e (Or.inr he))
    · exact Nat.lt_succ_of_lt (hE e (Or.inl he))
    · simp [forkEntries] at he

end Raw
end SkaModel
end Formalization
