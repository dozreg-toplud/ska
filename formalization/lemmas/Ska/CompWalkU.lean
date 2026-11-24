import lemmas.Ska.CompWalk
import lemmas.Ska.CompUnproxy

/-!
# `+walk-lazy` with a gate that may make proxies

`walkLazy_ok` (`CompWalk.lean`) asks the gate to leave `cond` alone, which
the gate of `+mede` does.  The gate of `+collapse-lazy-atom`
(`collapseGate`) makes a proxy at every lazy block other than its own
(`+proxy`), so `cond` grows there.  `WalkOKC C` is `WalkOK` with the
relation `C` between the two states in place of `g'.cond = g.cond`, and
`walkLazy_okC` is `walkLazy_ok` for any reflexive and transitive `C`.  The
instance for the collapse case is `ProxyFor r`: `cond` grew only by fresh
proxies (`CondFresh`), each standing for `r`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- **`WalkOK` with the relation `C` between the states in place of an
unchanged `cond`.** -/
structure WalkOKC (C : Gen Map → Gen Map → Prop) (P : Nat → Nat → Nat → Sure S → List Pole → Prop) (g g' : Gen Map)
    (es : List (Nat × Lazy S)) : Prop where
  bo : g'.bo = g.bo
  drop : g'.drop = g.drop
  le : g.re ≤ g'.re
  cnd : C g g'
  other : ∀ o, o ∉ es.map Prod.fst → HoonMap.get g'.blocks o = HoonMap.get g.blocks o
  at_ : ∀ e ∈ es, ∃ A : List Pole, (∀ B fin, HoonMap.get g.blocks e.1 = some ⟨[], B, fin⟩ →
    HoonMap.get g'.blocks e.1 = some ⟨[], A ++ B, fin⟩) ∧ P g.re g'.re e.1 e.2.sure A

section
variable {C : Gen Map → Gen Map → Prop} (cr : ∀ g, C g g) (ct : ∀ a b c : Gen Map, C a b → C b c → C a c)
include cr ct

theorem WalkOKC.nil (P : Nat → Nat → Nat → Sure S → List Pole → Prop) (g : Gen Map) : WalkOKC C P g g [] :=
  ⟨rfl, rfl, Nat.le_refl _, cr g, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩

omit cr ct in
theorem WalkOKC.congr {P : Nat → Nat → Nat → Sure S → List Pole → Prop} {g g' : Gen Map}
    {es es' : List (Nat × Lazy S)} (h : WalkOKC C P g g' es) (hm : ∀ e, e ∈ es ↔ e ∈ es') : WalkOKC C P g g' es' :=
  ⟨h.bo, h.drop, h.le, h.cnd, fun o ho => h.other o fun hm' => ho (by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm'
      exact List.mem_map.mpr ⟨e, (hm e).mp he, rfl⟩), fun e he => h.at_ e ((hm e).mpr he)⟩

omit cr in
theorem WalkOKC.trans {P : Nat → Nat → Nat → Sure S → List Pole → Prop} (pm : PMono P) {g g1 g2 : Gen Map}
    {es1 es2 : List (Nat × Lazy S)} (a : WalkOKC C P g g1 es1) (b : WalkOKC C P g1 g2 es2)
    (hd : ∀ x ∈ es1.map Prod.fst, x ∉ es2.map Prod.fst) : WalkOKC C P g g2 (es1 ++ es2) := by
  refine ⟨b.bo.trans a.bo, b.drop.trans a.drop, Nat.le_trans a.le b.le, ct _ _ _ a.cnd b.cnd, fun o ho => ?_,
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

end

/-- The gate puts ops at the one block it is given, with `C` between the
states. -/
def GateOKC (C : Gen Map → Gen Map → Prop) (P : Nat → Nat → Nat → Sure S → List Pole → Prop)
    (f : Nat → Sure S → CM Map Unit) : Prop :=
  ∀ (o : Nat) (l : Lazy S) (g g' : Gen Map), f o l.sure g = some ((), g') → g.drop = false →
    WalkOKC C P g g' [(o, l)]

mutual
theorem walkLazy_okC {C : Gen Map → Gen Map → Prop} (cr : ∀ g, C g g) (ct : ∀ a b c : Gen Map, C a b → C b c → C a c)
    {P : Nat → Nat → Nat → Sure S → List Pole → Prop} (pm : PMono P)
    {f : Nat → Sure S → CM Map Unit} (hf : GateOKC C P f) : ∀ (o : Nat) (l : Lazy S) (g g' : Gen Map),
    walkLazy f o l g = some ((), g') →
    g.drop = false → (((o, l) :: entries l).map Prod.fst).Nodup → WalkOKC C P g g' ((o, l) :: entries l)
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
      have WF := walkForks_okC cr ct pm hf fk g1 g2 h2 d1 (List.nodup_append.mp hn.2).2.1
      have WB := walkBonds_okC cr ct pm hf bd g2 g' h3 (WF.drop.trans d1) (List.nodup_append.mp hn.2).1
      have W := (W1.trans ct pm WF (by
          intro x hx hm; simp only [List.map_cons, List.map_nil, List.mem_singleton] at hx; subst hx
          exact hn.1.2 hm)).trans ct pm WB (by
          intro x hx hm
          simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
            List.map_append] at hx
          rcases hx with rfl | hx
          · exact hn.1.1 hm
          · exact nodup_disj hn.2 x hm hx)
      exact W.congr fun e => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_append, List.append_assoc]
        constructor <;> rintro (h | h | h) <;> simp [h]

theorem walkForks_okC {C : Gen Map → Gen Map → Prop} (cr : ∀ g, C g g) (ct : ∀ a b c : Gen Map, C a b → C b c → C a c)
    {P : Nat → Nat → Nat → Sure S → List Pole → Prop} (pm : PMono P)
    {f : Nat → Sure S → CM Map Unit} (hf : GateOKC C P f) : ∀ (fk : List (ForkE S)) (g g' : Gen Map),
    walkForks f fk g = some ((), g') →
    g.drop = false → ((forkEntries fk).map Prod.fst).Nodup → WalkOKC C P g g' (forkEntries fk)
  | [], g, g', h, _, _ => by
    simp only [walkForks, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact WalkOKC.nil cr ct P g
  | ((oy, y), (on, n)) :: rest, g, g', h, hd, hn => by
    unfold walkForks at h
    obtain ⟨u1, g1, h1, h⟩ := bind_some h
    obtain ⟨u2, g2, h2, h3⟩ := bind_some h
    simp only [forkEntries, List.map_append] at hn ⊢
    have hn1 := List.nodup_append.mp hn
    have hn2 := List.nodup_append.mp hn1.1
    have Wy := walkLazy_okC cr ct pm hf oy y g g1 h1 hd hn2.1
    have Wn := walkLazy_okC cr ct pm hf on n g1 g2 h2 (Wy.drop.trans hd) hn2.2.1
    have Wr := walkForks_okC cr ct pm hf rest g2 g' h3 (Wn.drop.trans (Wy.drop.trans hd)) hn1.2.1
    refine (Wy.trans ct pm Wn (nodup_disj hn1.1)).trans ct pm Wr ?_
    simp only [List.map_append]; exact nodup_disj hn

theorem walkBonds_okC {C : Gen Map → Gen Map → Prop} (cr : ∀ g, C g g) (ct : ∀ a b c : Gen Map, C a b → C b c → C a c)
    {P : Nat → Nat → Nat → Sure S → List Pole → Prop} (pm : PMono P)
    {f : Nat → Sure S → CM Map Unit} (hf : GateOKC C P f) : ∀ (bd : List (Nat × Lazy S)) (g g' : Gen Map),
    walkBonds f bd g = some ((), g') →
    g.drop = false → ((bondEntries bd).map Prod.fst).Nodup → WalkOKC C P g g' (bondEntries bd)
  | [], g, g', h, _, _ => by
    simp only [walkBonds, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact WalkOKC.nil cr ct P g
  | (o, l) :: rest, g, g', h, hd, hn => by
    unfold walkBonds at h
    obtain ⟨u1, g1, h1, h2⟩ := bind_some h
    simp only [bondEntries, List.map_append] at hn ⊢
    have hn1 := List.nodup_append.mp hn
    have Wl := walkLazy_okC cr ct pm hf o l g g1 h1 hd hn1.1
    have Wr := walkBonds_okC cr ct pm hf rest g1 g' h2 (Wl.drop.trans hd) hn1.2.1
    exact Wl.trans ct pm Wr (nodup_disj hn)
end

/-! ## The relation for the collapse case -/

/-- **`cond` grew only by fresh proxies for `r`**: `CondFresh`, and every
entry that changed stands for `r`. -/
def ProxyFor (r : Nat) (g g' : Gen Map) : Prop :=
  CondFresh g g' ∧ ∀ k, HoonMap.get g'.cond k ≠ HoonMap.get g.cond k → ∃ tag, HoonMap.get g'.cond k = some (r, tag)

theorem ProxyFor.refl (r : Nat) (g : Gen Map) : ProxyFor r g g :=
  ⟨CondFresh.refl g, fun _ h => absurd rfl h⟩

theorem ProxyFor.trans {r : Nat} {a b c : Gen Map} (h1 : ProxyFor r a b) (h2 : ProxyFor r b c) : ProxyFor r a c := by
  refine ⟨h1.1.trans h2.1, fun k hk => ?_⟩
  by_cases e : HoonMap.get c.cond k = HoonMap.get b.cond k
  · rw [e] at hk ⊢; exact h1.2 k hk
  · exact h2.2 k e

/-- `+proxy` makes one proxy, for `r`. -/
theorem proxy_proxyFor {r o p : Nat} {g g' : Gen Map} (h : proxy r o g = some (p, g')) : ProxyFor r g g' := by
  have P := proxy_condFresh h
  refine ⟨P.2.2.2.2.1, fun k hk => ?_⟩
  unfold proxy at h
  simp only at h
  by_cases hd : g.drop = true
  · rw [if_pos hd] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact absurd rfl hk
  · rw [if_neg hd] at h
    obtain ⟨tag, _, ht⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at ht
    obtain ⟨rfl, rfl⟩ := ht
    by_cases e : k = g.re
    · subst e; exact ⟨tag, by simp [HoonMap.get_put]⟩
    · exact absurd (by simp [HoonMap.get_put, e]) hk

/-- **The walk of `+collapse-lazy-atom` with any gate that makes proxies for
`r` only.** -/
theorem walkLazy_okP {r : Nat} {P : Nat → Nat → Nat → Sure S → List Pole → Prop} (pm : PMono P)
    {f : Nat → Sure S → CM Map Unit} (hf : GateOKC (ProxyFor r) P f) (o : Nat) (l : Lazy S) (g g' : Gen Map)
    (h : walkLazy f o l g = some ((), g')) (hd : g.drop = false) (hn : (((o, l) :: entries l).map Prod.fst).Nodup) :
    WalkOKC (ProxyFor r) P g g' ((o, l) :: entries l) :=
  walkLazy_okC (ProxyFor.refl r) (fun _ _ _ a b => ProxyFor.trans a b) pm hf o l g g' h hd hn

end Comp
end SkaModel
end Formalization
