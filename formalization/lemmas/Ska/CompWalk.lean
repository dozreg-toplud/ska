import lemmas.Ska.CompEntryRun

/-!
# `+walk-lazy` with a gate that puts ops in front of one block

`walkLazy_ok`: when the gate of `+walk-lazy` puts ops in front of the block
it is given and changes nothing else (`WalkOK` of one entry), the walk puts
ops in front of the block of the need and of every entry, each meeting the
gate's property `P`, and changes nothing else, given distinct labels.  The
walk visits the forks before the bonds, `entries` lists the bonds first;
`WalkOK` depends only on the members of the list.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- **`g'` comes from `g` by ops in front of the blocks at the labels of
`es`**, the ops at each meeting `P` with the registers allocated between. -/
structure WalkOK (P : Nat → Nat → Nat → Sure S → List Pole → Prop) (g g' : Gen Map)
    (es : List (Nat × Lazy S)) : Prop where
  bo : g'.bo = g.bo
  drop : g'.drop = g.drop
  le : g.re ≤ g'.re
  cnd : g'.cond = g.cond
  other : ∀ o, o ∉ es.map Prod.fst → HoonMap.get g'.blocks o = HoonMap.get g.blocks o
  at_ : ∀ e ∈ es, ∃ A : List Pole, (∀ B fin, HoonMap.get g.blocks e.1 = some ⟨[], B, fin⟩ →
    HoonMap.get g'.blocks e.1 = some ⟨[], A ++ B, fin⟩) ∧ P g.re g'.re e.1 e.2.sure A

/-- `P` holds for a wider range of registers. -/
def PMono (P : Nat → Nat → Nat → Sure S → List Pole → Prop) : Prop :=
  ∀ lo hi lo' hi' o s A, P lo hi o s A → lo' ≤ lo → hi ≤ hi' → P lo' hi' o s A

theorem WalkOK.nil (P : Nat → Nat → Nat → Sure S → List Pole → Prop) (g : Gen Map) : WalkOK P g g [] :=
  ⟨rfl, rfl, Nat.le_refl _, rfl, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩

theorem WalkOK.congr {P : Nat → Nat → Nat → Sure S → List Pole → Prop} {g g' : Gen Map}
    {es es' : List (Nat × Lazy S)} (h : WalkOK P g g' es) (hm : ∀ e, e ∈ es ↔ e ∈ es') : WalkOK P g g' es' :=
  ⟨h.bo, h.drop, h.le, h.cnd, fun o ho => h.other o fun hm' => ho (by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm'
      exact List.mem_map.mpr ⟨e, (hm e).mp he, rfl⟩), fun e he => h.at_ e ((hm e).mpr he)⟩

theorem WalkOK.trans {P : Nat → Nat → Nat → Sure S → List Pole → Prop} (pm : PMono P) {g g1 g2 : Gen Map}
    {es1 es2 : List (Nat × Lazy S)} (a : WalkOK P g g1 es1) (b : WalkOK P g1 g2 es2)
    (hd : ∀ x ∈ es1.map Prod.fst, x ∉ es2.map Prod.fst) : WalkOK P g g2 (es1 ++ es2) := by
  refine ⟨b.bo.trans a.bo, b.drop.trans a.drop, Nat.le_trans a.le b.le, b.cnd.trans a.cnd, fun o ho => ?_,
    fun e he => ?_⟩
  · simp only [List.map_append, List.mem_append, not_or] at ho
    exact (b.other o ho.2).trans (a.other o ho.1)
  · rcases List.mem_append.mp he with h | h
    · obtain ⟨A, hA, hP⟩ := a.at_ e h
      have hn : e.1 ∉ es2.map Prod.fst := hd _ (List.mem_map.mpr ⟨e, h, rfl⟩)
      exact ⟨A, fun B fin hb => (b.other _ hn).trans (hA B fin hb), pm _ _ _ _ _ _ _ hP (Nat.le_refl _) b.le⟩
    · obtain ⟨A, hA, hP⟩ := b.at_ e h
      have hn : e.1 ∉ es1.map Prod.fst := fun hm => hd _ hm (List.mem_map.mpr ⟨e, h, rfl⟩)
      exact ⟨A, fun B fin hb => hA B fin ((a.other _ hn).trans hb), pm _ _ _ _ _ _ _ hP a.le (Nat.le_refl _)⟩

theorem nodup_disj {a b : List Nat} (h : (a ++ b).Nodup) : ∀ x ∈ a, x ∉ b := fun x hx hb =>
  (List.nodup_append.mp h).2.2 x hx x hb rfl

/-- The gate puts ops at the one block it is given. -/
def GateOK (P : Nat → Nat → Nat → Sure S → List Pole → Prop) (f : Nat → Sure S → CM Map Unit) : Prop :=
  ∀ (o : Nat) (l : Lazy S) (g g' : Gen Map), f o l.sure g = some ((), g') → g.drop = false →
    WalkOK P g g' [(o, l)]

mutual
theorem walkLazy_ok {P : Nat → Nat → Nat → Sure S → List Pole → Prop} (pm : PMono P)
    {f : Nat → Sure S → CM Map Unit} (hf : GateOK P f) : ∀ (o : Nat) (l : Lazy S) (g g' : Gen Map), walkLazy f o l g = some ((), g') →
    g.drop = false → (((o, l) :: entries l).map Prod.fst).Nodup → WalkOK P g g' ((o, l) :: entries l)
  | o, mk s fk bd, g, g', h, hd, hn => by
    unfold walkLazy at h
    obtain ⟨u, g1, h1, hr⟩ := bind_some h
    have W1 := hf o (mk s fk bd) g g1 h1 hd
    have d1 : g1.drop = false := W1.drop.trans hd
    simp only [entries, List.map_cons, List.map_append, List.nodup_cons, List.mem_append, not_or] at hn ⊢
    split at hr
    · rename_i hfb
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hfb
      obtain ⟨rfl, rfl⟩ := hfb
      have h' : some ((), g1) = some ((), g') := hr
      cases h'
      simpa [bondEntries, forkEntries] using W1
    · obtain ⟨u2, g2, h2, h3⟩ := bind_some hr
      have WF := walkForks_ok pm hf fk g1 g2 h2 d1 (List.nodup_append.mp hn.2).2.1
      have WB := walkBonds_ok pm hf bd g2 g' h3 (WF.drop.trans d1) (List.nodup_append.mp hn.2).1
      have W := (W1.trans pm WF (by
          intro x hx hm; simp only [List.map_cons, List.map_nil, List.mem_singleton] at hx; subst hx
          exact hn.1.2 hm)).trans pm WB (by
          intro x hx hm
          simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
            List.map_append] at hx
          rcases hx with rfl | hx
          · exact hn.1.1 hm
          · exact nodup_disj hn.2 x hm hx)
      exact W.congr fun e => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_append, List.append_assoc]
        constructor <;> rintro (h | h | h) <;> simp [h]

theorem walkForks_ok {P : Nat → Nat → Nat → Sure S → List Pole → Prop} (pm : PMono P)
    {f : Nat → Sure S → CM Map Unit} (hf : GateOK P f) : ∀ (fk : List (ForkE S)) (g g' : Gen Map), walkForks f fk g = some ((), g') →
    g.drop = false → ((forkEntries fk).map Prod.fst).Nodup → WalkOK P g g' (forkEntries fk)
  | [], g, g', h, _, _ => by
    simp only [walkForks, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact WalkOK.nil P g
  | ((oy, y), (on, n)) :: rest, g, g', h, hd, hn => by
    unfold walkForks at h
    obtain ⟨u1, g1, h1, h⟩ := bind_some h
    obtain ⟨u2, g2, h2, h3⟩ := bind_some h
    simp only [forkEntries, List.map_append] at hn ⊢
    have hn1 := List.nodup_append.mp hn
    have hn2 := List.nodup_append.mp hn1.1
    have Wy := walkLazy_ok pm hf oy y g g1 h1 hd hn2.1
    have Wn := walkLazy_ok pm hf on n g1 g2 h2 (Wy.drop.trans hd) hn2.2.1
    have Wr := walkForks_ok pm hf rest g2 g' h3 (Wn.drop.trans (Wy.drop.trans hd)) hn1.2.1
    refine (Wy.trans pm Wn (nodup_disj hn1.1)).trans pm Wr ?_
    simp only [List.map_append]; exact nodup_disj hn

theorem walkBonds_ok {P : Nat → Nat → Nat → Sure S → List Pole → Prop} (pm : PMono P)
    {f : Nat → Sure S → CM Map Unit} (hf : GateOK P f) : ∀ (bd : List (Nat × Lazy S)) (g g' : Gen Map), walkBonds f bd g = some ((), g') →
    g.drop = false → ((bondEntries bd).map Prod.fst).Nodup → WalkOK P g g' (bondEntries bd)
  | [], g, g', h, _, _ => by
    simp only [walkBonds, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact WalkOK.nil P g
  | (o, l) :: rest, g, g', h, hd, hn => by
    unfold walkBonds at h
    obtain ⟨u1, g1, h1, h2⟩ := bind_some h
    simp only [bondEntries, List.map_append] at hn ⊢
    have hn1 := List.nodup_append.mp hn
    have Wl := walkLazy_ok pm hf o l g g1 h1 hd hn1.1
    have Wr := walkBonds_ok pm hf rest g1 g' h2 (Wl.drop.trans hd) hn1.2.1
    exact Wl.trans pm Wr (nodup_disj hn)
end

end Comp
end SkaModel
end Formalization
