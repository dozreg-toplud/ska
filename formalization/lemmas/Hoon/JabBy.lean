module

public import lemmas.Hoon.PutBy
import all lemmas.Pill.Arm.By

/-!
`+jab:by` of the pill's `hoon.hoon`: change the value under a key with a gate.

```hoon
++  jab
  ~/  %jab
  |*  [key=_?>(?=(^ a) p.n.a) fun=$-(_?>(?=(^ a) q.n.a) _?>(?=(^ a) q.n.a))]
  ^+  a
  ::
  ?~  a  !!
  ::
  ?:  =(key p.n.a)
    a(q.n (fun q.n.a))
  ::
  ?:  (gor key p.n.a)
    a(l $(a l.a))
  ::
  a(r $(a r.a))
```

The theorems are about the gate, slammed on `[key fun]` with a gate
`fun = [fp fs fc]` that maps a value `x` to `g x`.  (The arm itself bunts its
sample from the map, which crashes on the empty map.)
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

/-- `+jab:by`: apply `g` to the value under `key`; a crash where the key is
missing. -/
def jabF (mug : Noun → Nat) (key : Noun) (g : Noun → Noun) : Noun → Option Noun
  | Noun.cell (Noun.cell p q) (Noun.cell l r) =>
    if key = p then some (C (C p (g q)) (C l r))
    else if gorF mug key p then
      match jabF mug key g l with
      | some x => some (C (C p q) (C x r))
      | none => none
    else
      match jabF mug key g r with
      | some x => some (C (C p q) (C l x))
      | none => none
  | _ => none

theorem jab_gate {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx) (B key fp fs fc : Noun)
    (g : Noun → Noun) (hg : ∀ x, nock (C fp (C x fc)) fp = some (g x)) :
    ∀ (a out : Noun), jabF mug key g a = some out →
      nock (C by.jab.battery (C (C key (C fp (C fs fc))) (C B (C a ctx)))) by.jab.battery
        = some out := by
  intro a
  have hgor := gor_gate (mug := mug) ctx hc.2
  have hgo := hc.1
  fun_induction jabF mug key g a
  all_goals intro out h
  all_goals first
    | (simp at h; done)
    | skip
  all_goals first
    | (cases h
       nock_open by.jab.battery
       simp [nock_exec, *]
       done)
    | (nock_open by.jab.battery
       simp [nock_exec, *])

/-- On a map that holds `key` with the value `v`, `jabF` rebinds `key` to
`g v` and keeps the invariant. -/
theorem jabF_spec {mug : Noun → Nat} (key : Noun) (g : Noun → Noun) {a : Noun}
    (h : IsMap mug a) {v : Noun} (hv : Get a key v) :
    ∃ out, jabF mug key g a = some out ∧ IsMap mug out ∧
      ∀ k w, Get out k w ↔ (k = key ∧ w = g v) ∨ (k ≠ key ∧ Get a k w) := by
  induction h with
  | nil => exact absurd hv Get_atom
  | @node p q l r hl hr hL hR ihl ihr =>
    by_cases e : key = p
    · subst e
      have hq : v = q := Get.unique (IsMap.node hl hr hL hR) hv Get.here
      subst hq
      refine ⟨C (C key (g v)) (C l r), by simp [jabF], IsMap.node hl hr hL hR, fun k w => ?_⟩
      rw [Get_node, Get_node]
      constructor
      · rintro (⟨rfl, rfl⟩ | h | h)
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨(hL k w h).1, Or.inr (Or.inl h)⟩
        · exact Or.inr ⟨(hR k w h).1, Or.inr (Or.inr h)⟩
      · rintro (⟨rfl, rfl⟩ | ⟨ne, ⟨rfl, _⟩ | h | h⟩)
        · exact Or.inl ⟨rfl, rfl⟩
        · exact absurd rfl ne
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
    · rw [Get_node] at hv
      by_cases gk : gorF mug key p = true
      · have hvl : Get l key v := by
          rcases hv with ⟨e', _⟩ | h | h
          · exact absurd e' e
          · exact h
          · exact absurd (gorF_antisymm mug gk (hR key v h).2.1) e
        obtain ⟨x, hx, hmx, hgx⟩ := ihl hvl
        refine ⟨C (C p q) (C x r), by simp [jabF, e, gk, hx], ?_, ?_⟩
        · refine IsMap.node hmx hr (fun k w hk => ?_) hR
          rcases (hgx k w).1 hk with ⟨rfl, _⟩ | ⟨_, h⟩
          · exact hL k v hvl
          · exact hL k w h
        · intro k w
          rw [Get_node, Get_node, hgx]
          constructor
          · rintro (⟨rfl, rfl⟩ | h | h)
            · exact Or.inr ⟨Ne.symm e, Or.inl ⟨rfl, rfl⟩⟩
            · rcases h with h | ⟨ne, h⟩
              · exact Or.inl h
              · exact Or.inr ⟨ne, Or.inr (Or.inl h)⟩
            · refine Or.inr ⟨fun hk => ?_, Or.inr (Or.inr h)⟩
              subst hk
              exact e (gorF_antisymm mug gk (hR k w h).2.1)
          · rintro (h | ⟨ne, h | h | h⟩)
            · exact Or.inr (Or.inl (Or.inl h))
            · exact Or.inl h
            · exact Or.inr (Or.inl (Or.inr ⟨ne, h⟩))
            · exact Or.inr (Or.inr h)
      · have hvr : Get r key v := by
          rcases hv with ⟨e', _⟩ | h | h
          · exact absurd e' e
          · exact absurd (hL key v h).2.1 gk
          · exact h
        obtain ⟨x, hx, hmx, hgx⟩ := ihr hvr
        refine ⟨C (C p q) (C l x), by simp [jabF, e, gk, hx], ?_, ?_⟩
        · refine IsMap.node hl hmx hL (fun k w hk => ?_)
          rcases (hgx k w).1 hk with ⟨rfl, _⟩ | ⟨_, h⟩
          · exact hR k v hvr
          · exact hR k w h
        · intro k w
          rw [Get_node, Get_node, hgx]
          constructor
          · rintro (⟨rfl, rfl⟩ | h | h)
            · exact Or.inr ⟨Ne.symm e, Or.inl ⟨rfl, rfl⟩⟩
            · refine Or.inr ⟨fun hk => ?_, Or.inr (Or.inl h)⟩
              subst hk
              exact gk (hL k w h).2.1
            · rcases h with h | ⟨ne, h⟩
              · exact Or.inl h
              · exact Or.inr ⟨ne, Or.inr (Or.inr h)⟩
          · rintro (h | ⟨ne, h | h | h⟩)
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inr ⟨ne, h⟩))

/-- `+jab:by` on a map that holds `key` with value `v`: the result is a map
with `key` rebound to `g v` and the other pairs kept. -/
theorem jab_by {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx) (a key fp fs fc : Noun)
    (g : Noun → Noun) (hg : ∀ x, nock (C fp (C x fc)) fp = some (g x)) (h : IsMap mug a)
    {v : Noun} (hv : Get a key v) :
    ∃ out,
      Eval (C by.jab.battery (C (C key (C fp (C fs fc))) (C by.battery (C a ctx))))
        by.jab.battery out ∧
      IsMap mug out ∧ ∀ k w, Get out k w ↔ (k = key ∧ w = g v) ∨ (k ≠ key ∧ Get a k w) := by
  obtain ⟨out, hj, hm, hget⟩ := jabF_spec key g h hv
  exact ⟨out, eval_of_nock (jab_gate ctx hc by.battery key fp fs fc g hg a out hj), hm, hget⟩

end Hoon
end Formalization

end
