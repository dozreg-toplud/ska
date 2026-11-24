module

public import lemmas.Hoon.SetFolds
import lemmas.KernelRfl
import all lemmas.Pill.Arm.In

/-!
`+bif:in` and `+dif:in` of the pill's `hoon.hoon`.

```hoon
++  bif                                               ::  splits a by b
  ~/  %bif
  |*  b=*
  ^+  [l=a r=a]
  =<  +
  |-  ^+  a
  ?~  a
    [b ~ ~]
  ?:  =(b n.a)
    a
  ?:  (gor b n.a)
    =+  c=$(a l.a)
    ?>  ?=(^ c)
    [n.c l.c [n.a r.c r.a]]
  =+  c=$(a r.a)
  ?>  ?=(^ c)
  [n.c [n.a l.a l.c] r.c]
::
++  dif                                               ::  difference
  ~/  %dif
  |*  b=_a
  |-  ^+  a
  ?~  b
    a
  =+  c=(bif n.b)
  ?>  ?=(^ c)
  =+  d=$(a l.c, b l.b)
  =+  e=$(a r.c, b r.b)
  |-  ^-  [$?(~ _a)]
  ?~  d  e
  ?~  e  d
  ?:  (mor n.d n.e)
    [n.d l.d $(d r.d)]
  [n.e $(e l.e) r.e]
```

The generator names no noun of `+bif`, so its arm is defined here
(`bifArm`, the arm at axis `86` of the door, `bif_arm_at`, checked by the
kernel); it is wanted as `in.bif.*` at the next regeneration.  The `?>` of
`+dif` compiles to a dynamic hint `%toss` whose clue is `?=(^ c)`, which never
crashes.  The merge of `+dif` is `mergeInF` of `+del:in` (`dif_merge_loop`).

`bifInF_spec`: on a set, `+bif` returns a node with root `b` whose subtrees are
sets holding the keys of `a` before `b` and after `b` in `+gor` order.
`difInF_spec`: on two sets, `+dif` returns a set holding the keys of `a` that
`b` does not hold.  `dif_in_gate` is the gate on those.
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

/-! ## The nouns of `+bif` -/

/-- The loop of `+bif`. -/
def bifLoop : Noun := C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 62)))) (C (C (C (A 0) (A 14)) (C (A 1) (C (A 0) (A 0)))) (C (A 6) (C (C (A 5) (C (C (A 0) (A 14)) (C (A 0) (A 124)))) (C (C (A 0) (A 62)) (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 182) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 30)) (C (A 0) (A 252)))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 62) (C (A 0) (A 250))) (C (A 0) (A 1)))))) (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 10) (C (C (A 7) (C (A 10) (C (C (A 6) (C (A 0) (A 11))) (C (A 0) (A 126))))) (C (A 0) (A 2)))) (C (A 0) (A 0))))))) (C (A 8) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 62) (C (A 0) (A 251))) (C (A 0) (A 1)))))) (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 10) (C (C (A 6) (C (A 10) (C (C (A 7) (C (A 0) (A 10))) (C (A 0) (A 126))))) (C (A 0) (A 2)))) (C (A 0) (A 0)))))))))))))))

/-- The battery of the gate of `+bif`. -/
def bifBattery : Noun := C (A 7) (C (C (A 8) (C (C (A 1) bifLoop) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (A 0) (A 3)))

/-- The arm `+bif` of the door `+in`. -/
def bifArm : Noun := C (A 7) (C (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) bifBattery) (C (A 0) (A 1))))) (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x666962) (C (C (A 0) (A 7)) (A 0))))) (C (A 0) (A 1)))))

/-- `+bif` sits at axis `86` of the door, as `+dif` reads it. -/
theorem bif_arm_at : ∀ x, slot? 86 (C in.battery x) = some bifArm := by
  intro x; kernel_rfl

@[nock_exec] theorem bif_arm (d : Noun) :
    nock d bifArm = some (C bifBattery (C (A 0) d)) := by
  nock_open bifArm; simp only [nock_exec]

@[nock_exec] theorem dif_in_arm (a d : Noun) :
    nock (C in.battery (C a d)) in.dif.arm = some (C in.dif.battery (C a (C in.battery (C a d)))) := by
  nock_open in.dif.arm; simp only [nock_exec]

/-! ## The models -/

/-- The loop of `+bif`: the node with root `b` and the keys of `a` split
around it. -/
def bifInF (mug : Noun → Nat) (b : Noun) : Noun → Option Noun
  | Noun.atom 0 => some (C b (C (A 0) (A 0)))
  | Noun.cell n (Noun.cell l r) =>
    if b = n then some (C n (C l r))
    else if gorF mug b n then
      match bifInF mug b l with
      | some (Noun.cell nc (Noun.cell lc rc)) => some (C nc (C lc (C n (C rc r))))
      | _ => none
    else
      match bifInF mug b r with
      | some (Noun.cell nc (Noun.cell lc rc)) => some (C nc (C (C n (C l lc)) rc))
      | _ => none
  | _ => none

/-- `+dif:in`: the keys of `a` that `b` does not hold. -/
def difInF (mug : Noun → Nat) : Noun → Noun → Option Noun
  | a, Noun.atom 0 => some a
  | a, Noun.cell nb (Noun.cell lb rb) =>
    match bifInF mug nb a with
    | some (Noun.cell _ (Noun.cell lc rc)) =>
      match difInF mug lc lb, difInF mug rc rb with
      | some d, some e => mergeInF mug d e
      | _, _ => none
    | _ => none
  | _, _ => none

/-! ## The Nock -/

theorem bif_loop {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx) (B b : Noun) :
    ∀ a out, bifInF mug b a = some out →
      nock (C bifLoop (C B (C b (C in.battery (C a ctx))))) bifLoop = some out := by
  intro a
  have hgor := gor_gate (mug := mug) ctx hc.2
  have hg := hc.1
  fun_induction bifInF mug b a
  all_goals intro out h
  all_goals first
    | (simp at h; done)
    | skip
  all_goals first
    | (cases h
       nock_open bifLoop
       simp [nock_exec, *]
       done)
    | (nock_open bifLoop
       simp [nock_exec, *])

theorem bif_gate {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx) (a b n l r : Noun)
    (h : bifInF mug b a = some (C n (C l r))) :
    nock (C bifBattery (C b (C in.battery (C a ctx)))) bifBattery = some (C l r) := by
  nock_open bifBattery
  simp only [nock_exec, bif_loop ctx hc _ b a _ h]

theorem dif_merge_loop {mug : Noun → Nat} (ctx : Noun) (hc : MorIn mug ctx) (c b a : Noun) :
    ∀ d e out, mergeInF mug d e = some out →
      nock (C in.dif.loop0 (C e (C d (C c (C in.dif.loop1 (C in.dif.battery (C b (C in.battery (C a ctx)))))))))
        in.dif.loop0 = some out := by
  intro d e
  have hmor := mor_gate (mug := mug) ctx hc.2
  have hm := hc.1
  fun_induction mergeInF mug d e
  all_goals intro out h
  all_goals first
    | (simp at h; done)
    | skip
  all_goals first
    | (cases h
       nock_open in.dif.loop0
       simp [nock_exec, *]
       done)
    | (nock_open in.dif.loop0
       simp [nock_exec, *])

theorem dif_loop {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx) :
    ∀ a b out, difInF mug a b = some out →
      nock (C in.dif.loop1 (C in.dif.battery (C b (C in.battery (C a ctx))))) in.dif.loop1 = some out := by
  intro a b
  have hmerge := dif_merge_loop ctx hc.2
  have hbif := bif_gate ctx hc.1
  fun_induction difInF mug a b
  all_goals intro out h
  all_goals first
    | (simp at h; done)
    | skip
  · cases h
    nock_open in.dif.loop1
    simp [nock_exec]
  · rename_i a nb lb rb nc lc rc hb d e he hd ih2 ih1
    have h1 := hbif a nb nc lc rc hb
    have h2 := ih2 d hd
    have h3 := ih1 e he
    have h4 := hmerge (C lc rc) (C nb (C lb rb)) a d e out h
    nock_open in.dif.loop1
    simp [nock_exec, bif_arm_at, h1, h2, h3, h4]

theorem dif_in_gate {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx)
    (a b out : Noun) (h : difInF mug a b = some out) :
    nock (C in.dif.battery (C b (C in.battery (C a ctx)))) in.dif.battery = some out := by
  nock_open in.dif.battery
  simp only [nock_exec, dif_loop ctx hc a b out h]

/-! ## On sets -/

theorem isSet_nil {mug : Noun → Nat} : IsSet mug (A 0) := by
  show IsMap mug (toMap (A 0)); simp only [toMap_atom]; exact IsMap.nil

theorem isSet_node_iff {mug : Noun → Nat} {n l r : Noun} : IsSet mug (C n (C l r)) ↔
    IsSet mug l ∧ IsSet mug r ∧
    (∀ k, Has l k → k ≠ n ∧ gorF mug k n = true ∧ morF mug n k = true) ∧
    (∀ k, Has r k → k ≠ n ∧ gorF mug n k = true ∧ morF mug n k = true) := by
  unfold IsSet Has
  rw [toMap_node]
  constructor
  · intro h
    obtain ⟨hl, hr, hL, hR⟩ := IsMap_node h
    exact ⟨hl, hr, fun k hk => hL k _ hk, fun k hk => hR k _ hk⟩
  · rintro ⟨hl, hr, hL, hR⟩
    refine IsMap.node hl hr (fun k v hk => ?_) (fun k v hk => ?_)
    · have e := Get_toMap hk; subst e; exact hL k hk
    · have e := Get_toMap hk; subst e; exact hR k hk

/-- `+bif` on a set: the node with root `b`, the keys before `b` on the left
and those after it on the right, both sets. -/
theorem bifInF_spec {mug : Noun → Nat} (b : Noun) : ∀ {a : Noun}, IsSet mug a → ∃ lc rc,
    bifInF mug b a = some (C b (C lc rc)) ∧ IsSet mug lc ∧ IsSet mug rc ∧
    (∀ k, Has lc k ↔ Has a k ∧ k ≠ b ∧ gorF mug k b = true) ∧
    (∀ k, Has rc k ↔ Has a k ∧ k ≠ b ∧ gorF mug b k = true) := by
  intro a ha
  have ta := Tree.of_isSet ha
  induction ta with
  | nil =>
    refine ⟨A 0, A 0, by simp [bifInF], isSet_nil, isSet_nil, ?_, ?_⟩ <;> intro k <;>
      simp [not_has_atom]
  | @node n l r tl tr ihl ihr =>
    obtain ⟨hl, hr, hL, hR⟩ := isSet_node_iff.1 ha
    by_cases e : b = n
    · subst e
      refine ⟨l, r, by simp [bifInF], hl, hr, fun k => ?_, fun k => ?_⟩
      · rw [has_node]
        constructor
        · intro hk; exact ⟨Or.inr (Or.inl hk), (hL k hk).1, (hL k hk).2.1⟩
        · rintro ⟨h | h | h, ne, g⟩
          · exact absurd h ne
          · exact h
          · exact absurd (gorF_antisymm mug g (hR k h).2.1) ne
      · rw [has_node]
        constructor
        · intro hk; exact ⟨Or.inr (Or.inr hk), (hR k hk).1, (hR k hk).2.1⟩
        · rintro ⟨h | h | h, ne, g⟩
          · exact absurd h ne
          · exact absurd (gorF_antisymm mug (hL k h).2.1 g) ne
          · exact h
    · have e' : n ≠ b := fun h => e h.symm
      by_cases g : gorF mug b n = true
      · obtain ⟨lc, rc, h1, hlc, hrc, hLc, hRc⟩ := ihl hl
        refine ⟨lc, C n (C rc r), by simp [bifInF, e, g, h1], hlc,
          isSet_node_iff.2 ⟨hrc, hr, fun k hk => hL k ((hRc k).1 hk).1, hR⟩, fun k => ?_, fun k => ?_⟩
        · rw [hLc, has_node]
          constructor
          · rintro ⟨h, ne, gk⟩; exact ⟨Or.inr (Or.inl h), ne, gk⟩
          · rintro ⟨h | h | h, ne, gk⟩
            · rw [h] at gk; exact absurd (gorF_antisymm mug g gk) e
            · exact ⟨h, ne, gk⟩
            · exact absurd (gorF_antisymm mug g (gorF_trans mug (hR k h).2.1 gk)) e
        · rw [has_node, hRc, has_node]
          constructor
          · rintro (h | ⟨h, ne, gk⟩ | h)
            · rw [h]; exact ⟨Or.inl rfl, e', g⟩
            · exact ⟨Or.inr (Or.inl h), ne, gk⟩
            · refine ⟨Or.inr (Or.inr h), fun hk => ?_, gorF_trans mug g (hR k h).2.1⟩
              have h2 := (hR k h).2.1
              rw [hk] at h2
              exact e (gorF_antisymm mug g h2)
          · rintro ⟨h | h | h, ne, gk⟩
            · exact Or.inl h
            · exact Or.inr (Or.inl ⟨h, ne, gk⟩)
            · exact Or.inr (Or.inr h)
      · have g' : gorF mug n b = true := gorF_of_not mug g
        obtain ⟨lc, rc, h1, hlc, hrc, hLc, hRc⟩ := ihr hr
        refine ⟨C n (C l lc), rc, by simp [bifInF, e, g, h1],
          isSet_node_iff.2 ⟨hl, hlc, hL, fun k hk => hR k ((hLc k).1 hk).1⟩, hrc, fun k => ?_, fun k => ?_⟩
        · rw [has_node, hLc, has_node]
          constructor
          · rintro (h | h | ⟨h, ne, gk⟩)
            · rw [h]; exact ⟨Or.inl rfl, e', g'⟩
            · refine ⟨Or.inr (Or.inl h), fun hk => ?_, gorF_trans mug (hL k h).2.1 g'⟩
              have h2 := (hL k h).2.1
              rw [hk] at h2
              exact g h2
            · exact ⟨Or.inr (Or.inr h), ne, gk⟩
          · rintro ⟨h | h | h, ne, gk⟩
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr ⟨h, ne, gk⟩)
        · rw [hRc, has_node]
          constructor
          · rintro ⟨h, ne, gk⟩; exact ⟨Or.inr (Or.inr h), ne, gk⟩
          · rintro ⟨h | h | h, ne, gk⟩
            · rw [h] at gk; exact absurd gk g
            · exact absurd (gorF_trans mug gk (hL k h).2.1) g
            · exact ⟨h, ne, gk⟩

/-- `+dif:in` on two sets: a set holding the keys of `a` that `b` does not
hold. -/
theorem difInF_spec {mug : Noun → Nat} : ∀ {b : Noun}, IsSet mug b → ∀ (a : Noun), IsSet mug a →
    ∃ out, difInF mug a b = some out ∧ IsSet mug out ∧ ∀ k, Has out k ↔ Has a k ∧ ¬ Has b k := by
  intro b hb
  have tb := Tree.of_isSet hb
  revert hb
  induction tb with
  | nil =>
    intro _ a ha
    exact ⟨a, by simp [difInF], ha, fun k => by simp [not_has_atom]⟩
  | @node nb lb rb tl tr ihl ihr =>
    intro hb a ha
    obtain ⟨hlb, hrb, hLb, hRb⟩ := isSet_node_iff.1 hb
    obtain ⟨lc, rc, h1, hlc, hrc, hLc, hRc⟩ := bifInF_spec nb ha
    obtain ⟨d, hd, hds, hdk⟩ := ihl hlb lc hlc
    obtain ⟨e, he, hes, hek⟩ := ihr hrb rc hrc
    have hap : Apart mug (toMap d) (toMap e) := by
      intro kl vl kr vr h1' h2'
      have e1 := Get_toMap h1'
      have e2 := Get_toMap h2'
      subst e1 e2
      obtain ⟨_, n1, g1⟩ := (hLc kl).1 ((hdk kl).1 h1').1
      obtain ⟨_, n2, g2⟩ := (hRc kr).1 ((hek kr).1 h2').1
      refine ⟨gorF_trans mug g1 g2, fun hk => ?_⟩
      rw [hk] at g1
      exact n2 (gorF_antisymm mug g1 g2)
    obtain ⟨m, hm, hmm, hmk⟩ := mergeF_spec _ (toMap d) (toMap e) (Nat.lt_succ_self _) hds hes hap
    rw [mergeF_toMap _ d e (Nat.lt_succ_self _) hds hes] at hm
    cases hx : mergeInF mug d e with
    | none => rw [hx] at hm; cases hm
    | some out =>
      rw [hx] at hm
      simp only [Option.map_some, Option.some.injEq] at hm
      subst hm
      refine ⟨out, by simp [difInF, h1, hd, he, hx], hmm, fun k => ?_⟩
      show Get (toMap out) k (A 0) ↔ _
      rw [hmk, has_node]
      show Has d k ∨ Has e k ↔ _
      rw [hdk, hek, hLc, hRc]
      constructor
      · rintro (⟨⟨h, ne, g⟩, hn⟩ | ⟨⟨h, ne, g⟩, hn⟩)
        · refine ⟨h, ?_⟩
          rintro (h' | h' | h')
          · exact ne h'
          · exact hn h'
          · exact ne (gorF_antisymm mug g (hRb k h').2.1)
        · refine ⟨h, ?_⟩
          rintro (h' | h' | h')
          · exact ne h'
          · exact ne (gorF_antisymm mug (hLb k h').2.1 g)
          · exact hn h'
      · rintro ⟨h, hn⟩
        have ne : k ≠ nb := fun h' => hn (Or.inl h')
        rcases gorF_total mug k nb with g | g
        · exact Or.inl ⟨⟨h, ne, g⟩, fun h' => hn (Or.inr (Or.inl h'))⟩
        · exact Or.inr ⟨⟨h, ne, g⟩, fun h' => hn (Or.inr (Or.inr h'))⟩

/-- `+dif:in` on two sets, in a context with `+gor` and `+mor`. -/
theorem dif_in {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx) (a b : Noun)
    (ha : IsSet mug a) (hb : IsSet mug b) :
    ∃ out, nock (C in.dif.battery (C b (C in.battery (C a ctx)))) in.dif.battery = some out ∧
      IsSet mug out ∧ ∀ k, Has out k ↔ Has a k ∧ ¬ Has b k := by
  obtain ⟨out, h, hs, hk⟩ := difInF_spec hb a ha
  exact ⟨out, dif_in_gate ctx hc a b out h, hs, hk⟩

end Hoon
end Formalization

end
