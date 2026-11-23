module

public import lemmas.Hoon.PutBy
import all lemmas.Pill.Arm.By

/-!
`+del:by` of the pill's `hoon.hoon` deletes a key from a map.

```hoon
++  del                                               ::  delete at key b
  ~/  %del
  |*  b=*
  =>  .(b `_?>(?=(^ a) p.n.a)`b)
  |-  ^+  a
  ?~  a
    ~
  ?.  =(b p.n.a)
    ?:  (gor b p.n.a)
      a(l $(a l.a))
    a(r $(a r.a))
  |-  ^-  [$?(~ _a)]
  ?~  l.a  r.a
  ?~  r.a  l.a
  ?:  (mor p.n.l.a p.n.r.a)
    l.a(r $(l.a r.l.a))
  r.a(l $(r.a l.r.a))
```

`by.del.loop1` is the outer loop and `by.del.loop0` the merge of the two
subtrees of the node that holds the key.  The models `delF` and `mergeF`
follow the Hoon; `del_by` says what the arm does to a map.
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

/-! ## The models -/

/-- The merge of two treaps whose keys are apart, by `+mor` at the roots. -/
def mergeF (mug : Noun → Nat) (l r : Noun) : Option Noun :=
  match l, r with
  | Noun.atom 0, r => some r
  | Noun.cell (Noun.cell p q) (Noun.cell ll lr), Noun.atom 0 => some (C (C p q) (C ll lr))
  | Noun.cell (Noun.cell p q) (Noun.cell ll lr), Noun.cell (Noun.cell p' q') (Noun.cell rl rr) =>
    if morF mug p p' then
      match mergeF mug lr (C (C p' q') (C rl rr)) with
      | some x => some (C (C p q) (C ll x))
      | none => none
    else
      match mergeF mug (C (C p q) (C ll lr)) rl with
      | some x => some (C (C p' q') (C x rr))
      | none => none
  | _, _ => none
termination_by sizeOf l + sizeOf r
decreasing_by all_goals simp_wf; omega

/-- `+del:by`: delete the key `b` from the treap `a`. -/
def delF (mug : Noun → Nat) (b : Noun) : Noun → Option Noun
  | Noun.atom 0 => some (A 0)
  | Noun.cell (Noun.cell p q) (Noun.cell l r) =>
    if b = p then mergeF mug l r
    else if gorF mug b p then
      match delF mug b l with
      | some x => some (C (C p q) (C x r))
      | none => none
    else
      match delF mug b r with
      | some x => some (C (C p q) (C l x))
      | none => none
  | _ => none

/-! ## The Nock -/

@[nock_exec] theorem del_arm (d : Noun) :
    nock d by.del.arm = some (C by.del.battery (C (A 0) d)) := by
  nock_open by.del.arm; simp only [nock_exec]

theorem merge_loop {mug : Noun → Nat} (ctx : Noun) (hc : MorIn mug ctx) (b n : Noun) (B : Noun) :
    ∀ l r out, mergeF mug l r = some out →
      nock (C by.del.loop0 (C by.del.loop1 (C by.del.battery (C b (C B (C (C n (C l r)) ctx))))))
        by.del.loop0 = some out := by
  intro l r
  have hmor := mor_gate (mug := mug) ctx hc.2
  have hm := hc.1
  fun_induction mergeF mug l r
  all_goals intro out h
  all_goals first
    | (simp at h; done)
    | skip
  all_goals first
    | (cases h
       nock_open by.del.loop0
       simp [nock_exec, *]
       done)
    | (nock_open by.del.loop0
       simp [nock_exec, *])

theorem del_loop {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx) (b a : Noun) :
    ∀ out, delF mug b a = some out →
      nock (C by.del.loop1 (C by.del.battery (C b (C by.battery (C a ctx))))) by.del.loop1
        = some out := by
  have hgor := gor_gate (mug := mug) ctx hc.1.2
  have hg := hc.1.1
  have hmerge := merge_loop ctx hc.2 b
  fun_induction delF mug b a
  all_goals intro out h
  all_goals first
    | (simp at h; done)
    | skip
  all_goals first
    | (cases h
       nock_open by.del.loop1
       simp [nock_exec, *]
       done)
    | (nock_open by.del.loop1
       simp [nock_exec, *])

/-- The gate `del` of the door `by` with map `a`, slammed on `b`. -/
theorem del_gate {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx)
    (b a out : Noun) (h : delF mug b a = some out) :
    nock (C by.del.battery (C b (C by.battery (C a ctx)))) by.del.battery = some out := by
  nock_open by.del.battery
  simp only [nock_exec, del_loop ctx hc b a out h]

/-! ## On a map -/

/-- The keys of `l` all come before the keys of `r` in `+gor` order. -/
def Apart (mug : Noun → Nat) (l r : Noun) : Prop :=
  ∀ kl vl kr vr, Get l kl vl → Get r kr vr → gorF mug kl kr = true ∧ kl ≠ kr

theorem mergeF_spec {mug : Noun → Nat} : ∀ (n : Nat) (l r : Noun), sizeOf l + sizeOf r < n →
    IsMap mug l → IsMap mug r → Apart mug l r →
    ∃ m, mergeF mug l r = some m ∧ IsMap mug m ∧ ∀ k v, Get m k v ↔ Get l k v ∨ Get r k v := by
  intro n
  induction n with
  | zero => intro l r h; omega
  | succ n ih =>
    intro l r hs hl hr hap
    cases hl with
    | nil =>
      refine ⟨r, by simp [mergeF], hr, fun k v => ?_⟩
      simp [Get_atom]
    | @node p q ll lr hll hlr hLL hLR =>
      cases hr with
      | nil =>
        refine ⟨C (C p q) (C ll lr), by simp [mergeF], IsMap.node hll hlr hLL hLR, fun k v => ?_⟩
        simp [Get_atom]
      | @node p' q' rl rr hrl hrr hRL hRR =>
        have hpp : gorF mug p p' = true ∧ p ≠ p' := hap p q p' q' Get.here Get.here
        by_cases m : morF mug p p' = true
        · -- the left root stays on top: merge its right subtree with the right treap
          obtain ⟨x, hx, hmx, hgx⟩ := ih lr (C (C p' q') (C rl rr)) (by simp at hs ⊢; omega)
            hlr (IsMap.node hrl hrr hRL hRR)
            (fun kl vl kr vr h1 h2 => hap kl vl kr vr (Get.right h1) h2)
          refine ⟨C (C p q) (C ll x), by simp [mergeF, m, hx], ?_, ?_⟩
          · refine IsMap.node hll hmx hLL ?_
            intro k v hk
            rcases (hgx k v).1 hk with hk | hk
            · exact hLR k v hk
            · obtain ⟨g, ne⟩ := hap p q k v Get.here hk
              refine ⟨Ne.symm ne, g, ?_⟩
              exact morF_of_root (IsMap.node hrl hrr hRL hRR) m k v hk
          · intro k v
            rw [Get_node, Get_node (p := p), hgx]
            constructor
            · rintro (h | h | h | h)
              · exact Or.inl (Or.inl h)
              · exact Or.inl (Or.inr (Or.inl h))
              · exact Or.inl (Or.inr (Or.inr h))
              · exact Or.inr h
            · rintro ((h | h | h) | h)
              · exact Or.inl h
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr (Or.inl h))
              · exact Or.inr (Or.inr (Or.inr h))
        · -- the right root goes on top: merge the left treap with its left subtree
          have m' : morF mug p' p = true := morF_of_not mug m
          obtain ⟨x, hx, hmx, hgx⟩ := ih (C (C p q) (C ll lr)) rl (by simp at hs ⊢; omega)
            (IsMap.node hll hlr hLL hLR) hrl
            (fun kl vl kr vr h1 h2 => hap kl vl kr vr h1 (Get.left h2))
          refine ⟨C (C p' q') (C x rr), by simp [mergeF, m, hx], ?_, ?_⟩
          · refine IsMap.node hmx hrr ?_ hRR
            intro k v hk
            rcases (hgx k v).1 hk with hk | hk
            · obtain ⟨g, ne⟩ := hap k v p' q' hk Get.here
              exact ⟨ne, g, morF_of_root (IsMap.node hll hlr hLL hLR) m' k v hk⟩
            · exact hRL k v hk
          · intro k v
            rw [Get_node, Get_node (p := p'), hgx]
            constructor
            · rintro (h | h | h)
              · exact Or.inr (Or.inl h)
              · rcases h with h | h
                · exact Or.inl h
                · exact Or.inr (Or.inr (Or.inl h))
              · exact Or.inr (Or.inr (Or.inr h))
            · rintro (h | h | h | h)
              · exact Or.inr (Or.inl (Or.inl h))
              · exact Or.inl h
              · exact Or.inr (Or.inl (Or.inr h))
              · exact Or.inr (Or.inr h)

/-- `delF` on a map deletes the key and keeps the invariant. -/
theorem delF_spec {mug : Noun → Nat} (b : Noun) {a : Noun} (h : IsMap mug a) :
    ∃ out, delF mug b a = some out ∧ IsMap mug out ∧
      ∀ k v, Get out k v ↔ k ≠ b ∧ Get a k v := by
  induction h with
  | nil => exact ⟨A 0, rfl, IsMap.nil, fun k v => by simp [Get_atom]⟩
  | @node p q l r hl hr hL hR ihl ihr =>
    by_cases e : b = p
    · subst e
      obtain ⟨m, hm, hmm, hgm⟩ := mergeF_spec _ l r (Nat.lt_succ_self _) hl hr
        (fun kl vl kr vr h1 h2 => by
          obtain ⟨ne1, g1, _⟩ := hL kl vl h1
          obtain ⟨ne2, g2, _⟩ := hR kr vr h2
          refine ⟨gorF_trans mug g1 g2, fun e => ?_⟩
          subst e
          exact ne1 (gorF_antisymm mug g1 g2))
      refine ⟨m, by simp [delF, hm], hmm, fun k v => ?_⟩
      rw [hgm, Get_node]
      constructor
      · rintro (h | h)
        · exact ⟨(hL k v h).1, Or.inr (Or.inl h)⟩
        · exact ⟨(hR k v h).1, Or.inr (Or.inr h)⟩
      · rintro ⟨ne, ⟨rfl, _⟩ | h | h⟩
        · exact absurd rfl ne
        · exact Or.inl h
        · exact Or.inr h
    · by_cases g : gorF mug b p = true
      · obtain ⟨x, hx, hmx, hgx⟩ := ihl
        refine ⟨C (C p q) (C x r), by simp [delF, e, g, hx], ?_, ?_⟩
        · exact IsMap.node hmx hr (fun k v hk => hL k v ((hgx k v).1 hk).2) hR
        · intro k v
          rw [Get_node, Get_node, hgx]
          constructor
          · rintro (⟨rfl, rfl⟩ | ⟨ne, h⟩ | h)
            · exact ⟨Ne.symm e, Or.inl ⟨rfl, rfl⟩⟩
            · exact ⟨ne, Or.inr (Or.inl h)⟩
            · refine ⟨fun hk => ?_, Or.inr (Or.inr h)⟩
              subst hk
              exact e (gorF_antisymm mug g (hR k v h).2.1)
          · rintro ⟨ne, h | h | h⟩
            · exact Or.inl h
            · exact Or.inr (Or.inl ⟨ne, h⟩)
            · exact Or.inr (Or.inr h)
      · obtain ⟨x, hx, hmx, hgx⟩ := ihr
        refine ⟨C (C p q) (C l x), by simp [delF, e, g, hx], ?_, ?_⟩
        · exact IsMap.node hl hmx hL (fun k v hk => hR k v ((hgx k v).1 hk).2)
        · intro k v
          rw [Get_node, Get_node, hgx]
          constructor
          · rintro (⟨rfl, rfl⟩ | h | ⟨ne, h⟩)
            · exact ⟨Ne.symm e, Or.inl ⟨rfl, rfl⟩⟩
            · refine ⟨fun hk => ?_, Or.inr (Or.inl h)⟩
              subst hk
              exact g (hL k v h).2.1
            · exact ⟨ne, Or.inr (Or.inr h)⟩
          · rintro ⟨ne, h | h | h⟩
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr ⟨ne, h⟩)

/-- `+del:by` on a map ends, keeps the invariant, and holds the pairs of `a`
under the other keys. -/
theorem del_by {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx)
    (a k : Noun) (h : IsMap mug a) :
    ∃ out,
      Eval (C by.del.battery (C k (C by.battery (C a ctx)))) by.del.battery out ∧
      IsMap mug out ∧ ∀ k' v', Get out k' v' ↔ k' ≠ k ∧ Get a k' v' := by
  obtain ⟨out, hd, hm, hg⟩ := delF_spec k h
  exact ⟨out, eval_of_nock (del_gate ctx hc k a out hd), hm, hg⟩

end Hoon
end Formalization

end
