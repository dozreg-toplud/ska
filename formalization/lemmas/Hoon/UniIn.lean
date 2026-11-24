module

public import lemmas.Hoon.DifIn
import all lemmas.Pill.Arm.In

/-!
`+uni:in` of the pill's `hoon.hoon`.

```hoon
++  uni                                               ::  union
  ~/  %uni
  |*  b=_a
  ?:  =(a b)  a
  |-  ^+  a
  ?~  b
    a
  ?~  a
    b
  ?:  =(n.b n.a)
    b(l $(a l.a, b l.b), r $(a r.a, b r.b))
  ?:  (mor n.a n.b)
    ?:  (gor n.b n.a)
      $(l.a $(a l.a, r.b ~), b r.b)
    $(r.a $(a r.a, l.b ~), b l.b)
  ?:  (gor n.a n.b)
    $(l.b $(b l.b, r.a ~), a r.a)
  $(r.b $(b r.b, l.a ~), a l.a)
```

The loop is not structurally recursive: its outer calls take the result of
an inner call as one of their sets.  It ends on sets only, so its model is a
relation, `UniR` (one constructor per branch), and `uni_loop` runs the Nock on
every derivation.  `uniR_total` builds a derivation on two sets by induction
on the number of nodes: while the root of `a` comes first in `+mor` order it
stays the root and the loop walks down `b` (`uni_domA`), and symmetrically
(`uni_domB`); the inner calls are on fewer nodes.  For example in the first
case of `+mor`, `$(a l.a, r.b ~)` has the nodes of `l.a`, `n.b` and `l.b`,
fewer than those of `a` and `b`, and the outer call has at most as many,
with `n.a` still first.

`uni_in`: on two sets, the gate returns a set whose members are those of
both.
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

/-! ## The model -/

/-- The loop of `+uni:in`, one constructor per branch. -/
inductive UniR (mug : Noun → Nat) : Noun → Noun → Noun → Prop where
  | nilB (a : Noun) : UniR mug a (A 0) a
  | nilA (b : Noun) : b ≠ A 0 → UniR mug (A 0) b b
  | same {n la ra lb rb l r : Noun} : UniR mug la lb l → UniR mug ra rb r →
      UniR mug (C n (C la ra)) (C n (C lb rb)) (C n (C l r))
  | mg {na la ra nb lb rb x out : Noun} : nb ≠ na → morF mug na nb = true →
      gorF mug nb na = true → UniR mug la (C nb (C lb (A 0))) x →
      UniR mug (C na (C x ra)) rb out → UniR mug (C na (C la ra)) (C nb (C lb rb)) out
  | mn {na la ra nb lb rb x out : Noun} : nb ≠ na → morF mug na nb = true →
      gorF mug nb na = false → UniR mug ra (C nb (C (A 0) rb)) x →
      UniR mug (C na (C la x)) lb out → UniR mug (C na (C la ra)) (C nb (C lb rb)) out
  | ng {na la ra nb lb rb x out : Noun} : nb ≠ na → morF mug na nb = false →
      gorF mug na nb = true → UniR mug (C na (C la (A 0))) lb x →
      UniR mug ra (C nb (C x rb)) out → UniR mug (C na (C la ra)) (C nb (C lb rb)) out
  | nn {na la ra nb lb rb x out : Noun} : nb ≠ na → morF mug na nb = false →
      gorF mug na nb = false → UniR mug (C na (C (A 0) ra)) rb x →
      UniR mug la (C nb (C lb x)) out → UniR mug (C na (C la ra)) (C nb (C lb rb)) out

/-! ## The Nock -/

theorem uni_loop {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx) :
    ∀ {a b out : Noun}, UniR mug a b out →
      nock (C in.uni.loop (C in.uni.battery (C b (C in.battery (C a ctx))))) in.uni.loop
        = some out := by
  have hgor := gor_gate (mug := mug) ctx hc.1.2
  have hmor := mor_gate (mug := mug) ctx hc.2.2
  have hg := hc.1.1
  have hm := hc.2.1
  intro a b out h
  induction h with
  | nilB a =>
    nock_open in.uni.loop
    simp [nock_exec]
  | nilA b hb =>
    nock_open in.uni.loop
    simp [nock_exec, Ne.symm hb]
  | same _ _ ih1 ih2 =>
    nock_open in.uni.loop
    simp [nock_exec, ih1, ih2]
  | mg e m g _ _ ih1 ih2 =>
    nock_open in.uni.loop
    simp [nock_exec, e, m, g, hg, hm, hgor, hmor, ih1, ih2]
  | mn e m g _ _ ih1 ih2 =>
    nock_open in.uni.loop
    simp [nock_exec, e, m, g, hg, hm, hgor, hmor, ih1, ih2]
  | ng e m g _ _ ih1 ih2 =>
    nock_open in.uni.loop
    simp [nock_exec, e, m, g, hg, hm, hgor, hmor, ih1, ih2]
  | nn e m g _ _ ih1 ih2 =>
    nock_open in.uni.loop
    simp [nock_exec, e, m, g, hg, hm, hgor, hmor, ih1, ih2]

theorem uni_in_gate {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx)
    {a b out : Noun} (h : UniR mug a b out) :
    nock (C in.uni.battery (C b (C in.battery (C a ctx)))) in.uni.battery
      = some (if a = b then a else out) := by
  have hl := uni_loop ctx hc h
  nock_open in.uni.battery
  by_cases e : a = b
  · subst e; simp [nock_exec]
  · simp [nock_exec, e, hl]


/-! ## On sets -/

/-- The number of nodes of a treap. -/
def uniSz : Noun → Nat
  | Noun.cell _ (Noun.cell l r) => uniSz l + uniSz r + 1
  | _ => 0

/-- What the loop gives on `a` and `b`: a derivation to a set with the members
of both, with at most as many nodes as both. -/
def UniP (mug : Noun → Nat) (a b : Noun) : Prop :=
  ∃ out, UniR mug a b out ∧ IsSet mug out ∧ (∀ k, Has out k ↔ Has a k ∨ Has b k) ∧
    uniSz out ≤ uniSz a + uniSz b

theorem uni_sz_node (n l r : Noun) : uniSz (C n (C l r)) = uniSz l + uniSz r + 1 := rfl

theorem uni_sz_nil : uniSz (A 0) = 0 := rfl

theorem uni_has3 {n l r k : Noun} : Has (C n (C l r)) k ↔ k = n ∨ Has l k ∨ Has r k := has_node

theorem uni_has_nil {k : Noun} : Has (A 0) k ↔ False := ⟨fun h => not_has_atom h, False.elim⟩

/-- The same root: both halves are unions of fewer nodes. -/
theorem uni_same {mug : Noun → Nat} {m : Nat}
    (ih : ∀ a b, uniSz a + uniSz b < m → IsSet mug a → IsSet mug b → UniP mug a b)
    {n la ra lb rb : Noun} (ha : IsSet mug (C n (C la ra))) (hb : IsSet mug (C n (C lb rb)))
    (hs : uniSz (C n (C la ra)) + uniSz (C n (C lb rb)) ≤ m) :
    UniP mug (C n (C la ra)) (C n (C lb rb)) := by
  obtain ⟨hla, hra, hLa, hRa⟩ := isSet_node_iff.1 ha
  obtain ⟨hlb, hrb, hLb, hRb⟩ := isSet_node_iff.1 hb
  rw [uni_sz_node, uni_sz_node] at hs
  obtain ⟨l, h1, hl, hlk, hls⟩ := ih la lb (by omega) hla hlb
  obtain ⟨r, h2, hr, hrk, hrs⟩ := ih ra rb (by omega) hra hrb
  refine ⟨C n (C l r), UniR.same h1 h2, isSet_node_iff.2 ⟨hl, hr, fun k hk => ?_, fun k hk => ?_⟩,
    fun k => ?_, ?_⟩
  · rcases (hlk k).1 hk with h | h
    · exact hLa k h
    · exact hLb k h
  · rcases (hrk k).1 hk with h | h
    · exact hRa k h
    · exact hRb k h
  · rw [uni_has3, uni_has3, uni_has3, hlk, hrk]
    constructor
    · rintro (h | (h | h) | (h | h))
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inl (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr (Or.inr h))
    · rintro ((h | h | h) | (h | h | h))
      · exact Or.inl h
      · exact Or.inr (Or.inl (Or.inl h))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inl h
      · exact Or.inr (Or.inl (Or.inr h))
      · exact Or.inr (Or.inr (Or.inr h))
  · rw [uni_sz_node, uni_sz_node, uni_sz_node]; omega

/-- The root of `a` comes first in `+mor` order among the keys of `b`: the
loop walks down `b` with `n.a` at the root. -/
theorem uni_domA {mug : Noun → Nat} {m : Nat}
    (ih : ∀ a b, uniSz a + uniSz b < m → IsSet mug a → IsSet mug b → UniP mug a b) :
    ∀ {b : Noun}, Tree b → IsSet mug b → ∀ na la ra, IsSet mug (C na (C la ra)) →
      (∀ k, Has b k → morF mug na k = true) → uniSz (C na (C la ra)) + uniSz b ≤ m →
      UniP mug (C na (C la ra)) b := by
  intro b tb
  induction tb with
  | nil =>
    intro _ na la ra ha _ _
    refine ⟨_, UniR.nilB _, ha, fun k => ?_, by rw [uni_sz_nil]; omega⟩
    rw [uni_has_nil, or_false]
  | @node nb lb rb _ _ ihl ihr =>
    intro hb na la ra ha hdom hsz
    by_cases e : nb = na
    · subst e; exact uni_same ih ha hb hsz
    have hmo : morF mug na nb = true := hdom nb (uni_has3.2 (Or.inl rfl))
    obtain ⟨hlb, hrb, hLb, hRb⟩ := isSet_node_iff.1 hb
    obtain ⟨hla, hra, hLa, hRa⟩ := isSet_node_iff.1 ha
    have hsz' := hsz
    rw [uni_sz_node, uni_sz_node] at hsz'
    by_cases g : gorF mug nb na = true
    · have hsb : IsSet mug (C nb (C lb (A 0))) :=
        isSet_node_iff.2 ⟨hlb, isSet_nil, hLb, fun k hk => absurd hk not_has_atom⟩
      obtain ⟨x, h1, hx, hxk, hxs⟩ := ih la (C nb (C lb (A 0)))
        (by rw [uni_sz_node, uni_sz_nil]; omega) hla hsb
      rw [uni_sz_node, uni_sz_nil] at hxs
      have hX : ∀ k, Has x k → k ≠ na ∧ gorF mug k na = true ∧ morF mug na k = true := by
        intro k hk
        rcases (hxk k).1 hk with h | h
        · exact hLa k h
        · rcases uni_has3.1 h with h | h | h
          · subst h; exact ⟨e, g, hmo⟩
          · have gk := gorF_trans mug (hLb k h).2.1 g
            refine ⟨fun hk' => ?_, gk, hdom k (uni_has3.2 (Or.inr (Or.inl h)))⟩
            subst hk'
            exact e (gorF_antisymm mug g (hLb k h).2.1)
          · exact absurd h not_has_atom
      have hsa : IsSet mug (C na (C x ra)) := isSet_node_iff.2 ⟨hx, hra, hX, hRa⟩
      obtain ⟨out, h2, ho, hok, hos⟩ := ihr hrb na x ra hsa
        (fun k hk => hdom k (uni_has3.2 (Or.inr (Or.inr hk)))) (by rw [uni_sz_node]; omega)
      rw [uni_sz_node] at hos
      refine ⟨out, UniR.mg e hmo g h1 h2, ho, fun k => ?_, by rw [uni_sz_node, uni_sz_node]; omega⟩
      rw [hok, uni_has3, hxk, uni_has3, uni_has3, uni_has3, uni_has_nil]
      constructor
      · rintro ((h | (h | h | h | h) | h) | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr (Or.inl h))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact h.elim
        · exact Or.inl (Or.inr (Or.inr h))
        · exact Or.inr (Or.inr (Or.inr h))
      · rintro ((h | h | h) | (h | h | h))
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr (Or.inl (Or.inl h)))
        · exact Or.inl (Or.inr (Or.inr h))
        · exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl h))))
        · exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl h)))))
        · exact Or.inr h
    · have g' : gorF mug na nb = true := gorF_of_not mug g
      have gf : gorF mug nb na = false := by simpa using g
      have hsb : IsSet mug (C nb (C (A 0) rb)) :=
        isSet_node_iff.2 ⟨isSet_nil, hrb, fun k hk => absurd hk not_has_atom, hRb⟩
      obtain ⟨x, h1, hx, hxk, hxs⟩ := ih ra (C nb (C (A 0) rb))
        (by rw [uni_sz_node, uni_sz_nil]; omega) hra hsb
      rw [uni_sz_node, uni_sz_nil] at hxs
      have hX : ∀ k, Has x k → k ≠ na ∧ gorF mug na k = true ∧ morF mug na k = true := by
        intro k hk
        rcases (hxk k).1 hk with h | h
        · exact hRa k h
        · rcases uni_has3.1 h with h | h | h
          · subst h; exact ⟨e, g', hmo⟩
          · exact absurd h not_has_atom
          · have gk := gorF_trans mug g' (hRb k h).2.1
            refine ⟨fun hk' => ?_, gk, hdom k (uni_has3.2 (Or.inr (Or.inr h)))⟩
            subst hk'
            exact e (gorF_antisymm mug (hRb k h).2.1 g')
      have hsa : IsSet mug (C na (C la x)) := isSet_node_iff.2 ⟨hla, hx, hLa, hX⟩
      obtain ⟨out, h2, ho, hok, hos⟩ := ihl hlb na la x hsa
        (fun k hk => hdom k (uni_has3.2 (Or.inr (Or.inl hk)))) (by rw [uni_sz_node]; omega)
      rw [uni_sz_node] at hos
      refine ⟨out, UniR.mn e hmo gf h1 h2, ho, fun k => ?_, by rw [uni_sz_node, uni_sz_node]; omega⟩
      rw [hok, uni_has3, hxk, uni_has3, uni_has3, uni_has3, uni_has_nil]
      constructor
      · rintro ((h | h | h | h | h | h) | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr (Or.inl h))
        · exact Or.inl (Or.inr (Or.inr h))
        · exact Or.inr (Or.inl h)
        · exact h.elim
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inr (Or.inr (Or.inl h))
      · rintro ((h | h | h) | (h | h | h))
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr (Or.inl h))
        · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact Or.inr h
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

/-- The root of `b` comes first in `+mor` order among the keys of `a`: the
loop walks down `a` with `n.b` at the root. -/
theorem uni_domB {mug : Noun → Nat} {m : Nat}
    (ih : ∀ a b, uniSz a + uniSz b < m → IsSet mug a → IsSet mug b → UniP mug a b) :
    ∀ {a : Noun}, Tree a → IsSet mug a → ∀ nb lb rb, IsSet mug (C nb (C lb rb)) →
      (∀ k, Has a k → morF mug nb k = true) → uniSz a + uniSz (C nb (C lb rb)) ≤ m →
      UniP mug a (C nb (C lb rb)) := by
  intro a ta
  induction ta with
  | nil =>
    intro _ nb lb rb hb _ _
    refine ⟨_, UniR.nilA _ (by simp), hb, fun k => ?_, by rw [uni_sz_nil]; omega⟩
    rw [uni_has_nil, false_or]
  | @node na la ra _ _ ihl ihr =>
    intro ha nb lb rb hb hdom hsz
    by_cases e : nb = na
    · subst e; exact uni_same ih ha hb hsz
    have e' : na ≠ nb := fun h => e h.symm
    have hmo : morF mug nb na = true := hdom na (uni_has3.2 (Or.inl rfl))
    have hmf : morF mug na nb = false := by
      cases h : morF mug na nb
      · rfl
      · exact absurd (morF_antisymm mug hmo h) e
    obtain ⟨hlb, hrb, hLb, hRb⟩ := isSet_node_iff.1 hb
    obtain ⟨hla, hra, hLa, hRa⟩ := isSet_node_iff.1 ha
    have hsz' := hsz
    rw [uni_sz_node, uni_sz_node] at hsz'
    by_cases g : gorF mug na nb = true
    · have hsa : IsSet mug (C na (C la (A 0))) :=
        isSet_node_iff.2 ⟨hla, isSet_nil, hLa, fun k hk => absurd hk not_has_atom⟩
      obtain ⟨x, h1, hx, hxk, hxs⟩ := ih (C na (C la (A 0))) lb
        (by rw [uni_sz_node, uni_sz_nil]; omega) hsa hlb
      rw [uni_sz_node, uni_sz_nil] at hxs
      have hX : ∀ k, Has x k → k ≠ nb ∧ gorF mug k nb = true ∧ morF mug nb k = true := by
        intro k hk
        rcases (hxk k).1 hk with h | h
        · rcases uni_has3.1 h with h | h | h
          · subst h; exact ⟨e', g, hmo⟩
          · have gk := gorF_trans mug (hLa k h).2.1 g
            refine ⟨fun hk' => ?_, gk, hdom k (uni_has3.2 (Or.inr (Or.inl h)))⟩
            subst hk'
            exact e (gorF_antisymm mug (hLa k h).2.1 g)
          · exact absurd h not_has_atom
        · exact hLb k h
      have hsb : IsSet mug (C nb (C x rb)) := isSet_node_iff.2 ⟨hx, hrb, hX, hRb⟩
      obtain ⟨out, h2, ho, hok, hos⟩ := ihr hra nb x rb hsb
        (fun k hk => hdom k (uni_has3.2 (Or.inr (Or.inr hk)))) (by rw [uni_sz_node]; omega)
      rw [uni_sz_node] at hos
      refine ⟨out, UniR.ng e hmf g h1 h2, ho, fun k => ?_, by rw [uni_sz_node, uni_sz_node]; omega⟩
      simp only [hok, hxk, uni_has3, uni_has_nil, or_false, false_or, or_assoc, or_comm, or_left_comm]
    · have g' : gorF mug nb na = true := gorF_of_not mug g
      have gf : gorF mug na nb = false := by simpa using g
      have hsa : IsSet mug (C na (C (A 0) ra)) :=
        isSet_node_iff.2 ⟨isSet_nil, hra, fun k hk => absurd hk not_has_atom, hRa⟩
      obtain ⟨x, h1, hx, hxk, hxs⟩ := ih (C na (C (A 0) ra)) rb
        (by rw [uni_sz_node, uni_sz_nil]; omega) hsa hrb
      rw [uni_sz_node, uni_sz_nil] at hxs
      have hX : ∀ k, Has x k → k ≠ nb ∧ gorF mug nb k = true ∧ morF mug nb k = true := by
        intro k hk
        rcases (hxk k).1 hk with h | h
        · rcases uni_has3.1 h with h | h | h
          · subst h; exact ⟨e', g', hmo⟩
          · exact absurd h not_has_atom
          · have gk := gorF_trans mug g' (hRa k h).2.1
            refine ⟨fun hk' => ?_, gk, hdom k (uni_has3.2 (Or.inr (Or.inr h)))⟩
            subst hk'
            exact e (gorF_antisymm mug g' (hRa k h).2.1)
        · exact hRb k h
      have hsb : IsSet mug (C nb (C lb x)) := isSet_node_iff.2 ⟨hlb, hx, hLb, hX⟩
      obtain ⟨out, h2, ho, hok, hos⟩ := ihl hla nb lb x hsb
        (fun k hk => hdom k (uni_has3.2 (Or.inr (Or.inl hk)))) (by rw [uni_sz_node]; omega)
      rw [uni_sz_node] at hos
      refine ⟨out, UniR.nn e hmf gf h1 h2, ho, fun k => ?_, by rw [uni_sz_node, uni_sz_node]; omega⟩
      simp only [hok, hxk, uni_has3, uni_has_nil, or_false, false_or, or_assoc, or_comm, or_left_comm]

/-- One level of the induction on the number of nodes. -/
theorem uni_step {mug : Noun → Nat} {m : Nat}
    (ih : ∀ a b, uniSz a + uniSz b < m → IsSet mug a → IsSet mug b → UniP mug a b)
    (a b : Noun) (hs : uniSz a + uniSz b ≤ m) (ha : IsSet mug a) (hb : IsSet mug b) :
    UniP mug a b := by
  have ta := Tree.of_isSet ha
  have tb := Tree.of_isSet hb
  cases tb with
  | nil => exact ⟨a, UniR.nilB a, ha, fun k => by rw [uni_has_nil, or_false], by rw [uni_sz_nil]; omega⟩
  | @node nb lb rb _ _ =>
    obtain ⟨_, _, hLb, hRb⟩ := isSet_node_iff.1 hb
    cases ta with
    | nil => exact uni_domB ih Tree.nil ha nb lb rb hb (fun k hk => absurd hk not_has_atom) hs
    | @node na la ra tla tra =>
      obtain ⟨_, _, hLa, hRa⟩ := isSet_node_iff.1 ha
      by_cases mo : morF mug na nb = true
      · refine uni_domA ih (Tree.node (by assumption) (by assumption)) hb na la ra ha (fun k hk => ?_) hs
        rcases uni_has3.1 hk with h | h | h
        · subst h; exact mo
        · exact morF_trans mug mo (hLb k h).2.2
        · exact morF_trans mug mo (hRb k h).2.2
      · have mo' := morF_of_not mug mo
        refine uni_domB ih (Tree.node tla tra) ha nb lb rb hb (fun k hk => ?_) hs
        rcases uni_has3.1 hk with h | h | h
        · subst h; exact mo'
        · exact morF_trans mug mo' (hLa k h).2.2
        · exact morF_trans mug mo' (hRa k h).2.2

theorem uniP_of_sets {mug : Noun → Nat} : ∀ (m : Nat) (a b : Noun), uniSz a + uniSz b ≤ m →
    IsSet mug a → IsSet mug b → UniP mug a b := by
  intro m
  induction m with
  | zero => exact uni_step (fun a b h => absurd h (Nat.not_lt_zero _))
  | succ m ih => exact uni_step (fun a b h ha hb => ih a b (by omega) ha hb)

/-- `+uni:in` on two sets, in a context with `+gor` and `+mor`: a set holding
the keys of both. -/
theorem uni_in {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx) (a b : Noun)
    (ha : IsSet mug a) (hb : IsSet mug b) :
    ∃ out, nock (C in.uni.battery (C b (C in.battery (C a ctx)))) in.uni.battery = some out ∧
      IsSet mug out ∧ ∀ k, Has out k ↔ Has a k ∨ Has b k := by
  obtain ⟨out, h, hs, hk, _⟩ := uniP_of_sets _ a b (Nat.le_refl _) ha hb
  rw [uni_in_gate ctx hc h]
  by_cases e : a = b
  · subst e
    exact ⟨a, by simp, ha, fun k => ⟨Or.inl, fun h => h.elim id id⟩⟩
  · exact ⟨out, by simp [e], hs, hk⟩

end Hoon
end Formalization

end
