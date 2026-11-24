module

public import lemmas.Hoon.UniIn
public import lemmas.Hoon.RollUni
public import lemmas.Hoon.Canon
import all lemmas.Pill.Arm.By

/-!
`+uni:by` of the pill's `hoon.hoon`.

```hoon
++  uni                                               ::  union, merge
  ~/  %uni
  |*  b=_a
  |-  ^+  a
  ?~  b
    a
  ?~  a
    b
  ?:  =(p.n.b p.n.a)
    b(l $(a l.a, b l.b), r $(a r.a, b r.b))
  ?:  (mor p.n.a p.n.b)
    ?:  (gor p.n.b p.n.a)
      $(l.a $(a l.a, r.b ~), b r.b)
    $(r.a $(a r.a, l.b ~), b l.b)
  ?:  (gor p.n.a p.n.b)
    $(l.b $(b l.b, r.a ~), a r.a)
  $(r.b $(b r.b, l.a ~), a l.a)
```

The loop is that of `+uni:in` (`Hoon/UniIn.lean`) on the keys `p.n`, with
the pair of `b` kept where the keys are equal, and without the first test
`=(a b)`.  Its model is the relation `UniByR`, one constructor per branch;
`uni_by_loop` runs the Nock on every derivation.  `uniByP_of_maps` builds a
derivation on two maps by induction on the number of nodes, as
`uniP_of_sets` does, to a map whose pairs are those of `b` and those of `a`
whose key `b` does not hold.

`uni_by_one`: on a map `a` and the map `[[k v] ~ ~]` of one pair, the gate
returns the map that `putF` gives, the same noun by `isMap_ext`.
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

/-! ## The model -/

/-- The loop of `+uni:by`, one constructor per branch. -/
inductive UniByR (mug : Noun → Nat) : Noun → Noun → Noun → Prop where
  | nilB (a : Noun) : UniByR mug a (A 0) a
  | nilA (b : Noun) : b ≠ A 0 → UniByR mug (A 0) b b
  | same {k va la ra vb lb rb l r : Noun} : UniByR mug la lb l → UniByR mug ra rb r →
      UniByR mug (C (C k va) (C la ra)) (C (C k vb) (C lb rb)) (C (C k vb) (C l r))
  | mg {ka va la ra kb vb lb rb x out : Noun} : kb ≠ ka → morF mug ka kb = true →
      gorF mug kb ka = true → UniByR mug la (C (C kb vb) (C lb (A 0))) x →
      UniByR mug (C (C ka va) (C x ra)) rb out →
      UniByR mug (C (C ka va) (C la ra)) (C (C kb vb) (C lb rb)) out
  | mn {ka va la ra kb vb lb rb x out : Noun} : kb ≠ ka → morF mug ka kb = true →
      gorF mug kb ka = false → UniByR mug ra (C (C kb vb) (C (A 0) rb)) x →
      UniByR mug (C (C ka va) (C la x)) lb out →
      UniByR mug (C (C ka va) (C la ra)) (C (C kb vb) (C lb rb)) out
  | ng {ka va la ra kb vb lb rb x out : Noun} : kb ≠ ka → morF mug ka kb = false →
      gorF mug ka kb = true → UniByR mug (C (C ka va) (C la (A 0))) lb x →
      UniByR mug ra (C (C kb vb) (C x rb)) out →
      UniByR mug (C (C ka va) (C la ra)) (C (C kb vb) (C lb rb)) out
  | nn {ka va la ra kb vb lb rb x out : Noun} : kb ≠ ka → morF mug ka kb = false →
      gorF mug ka kb = false → UniByR mug (C (C ka va) (C (A 0) ra)) rb x →
      UniByR mug la (C (C kb vb) (C lb x)) out →
      UniByR mug (C (C ka va) (C la ra)) (C (C kb vb) (C lb rb)) out

/-! ## The Nock -/

theorem uni_by_loop {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx) :
    ∀ {a b out : Noun}, UniByR mug a b out →
      nock (C by.uni.loop (C by.uni.battery (C b (C by.battery (C a ctx))))) by.uni.loop
        = some out := by
  have hgor := gor_gate (mug := mug) ctx hc.1.2
  have hmor := mor_gate (mug := mug) ctx hc.2.2
  have hg := hc.1.1
  have hm := hc.2.1
  intro a b out h
  induction h with
  | nilB a =>
    nock_open by.uni.loop
    simp [nock_exec]
  | nilA b hb =>
    nock_open by.uni.loop
    simp [nock_exec, Ne.symm hb]
  | same _ _ ih1 ih2 =>
    nock_open by.uni.loop
    simp [nock_exec, ih1, ih2]
  | mg e m g _ _ ih1 ih2 =>
    nock_open by.uni.loop
    simp [nock_exec, e, m, g, hg, hm, hgor, hmor, ih1, ih2]
  | mn e m g _ _ ih1 ih2 =>
    nock_open by.uni.loop
    simp [nock_exec, e, m, g, hg, hm, hgor, hmor, ih1, ih2]
  | ng e m g _ _ ih1 ih2 =>
    nock_open by.uni.loop
    simp [nock_exec, e, m, g, hg, hm, hgor, hmor, ih1, ih2]
  | nn e m g _ _ ih1 ih2 =>
    nock_open by.uni.loop
    simp [nock_exec, e, m, g, hg, hm, hgor, hmor, ih1, ih2]

/-- The gate `uni` of the door `by` with map `a`, slammed on `b`. -/
theorem uni_by_gate {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx)
    {a b out : Noun} (h : UniByR mug a b out) :
    nock (C by.uni.battery (C b (C by.battery (C a ctx)))) by.uni.battery = some out := by
  have hl := uni_by_loop ctx hc h
  nock_open by.uni.battery
  simp [nock_exec, hl]

/-! ## On maps -/

/-- The map `a` holds the key `k`. -/
def KIn (a k : Noun) : Prop := ∃ v, Get a k v

theorem kin_of_get {a k v : Noun} (h : Get a k v) : KIn a k := ⟨v, h⟩

theorem kin_nil {k : Noun} : ¬ KIn (A 0) k := fun ⟨_, h⟩ => Get_atom h

theorem kin_node {p q l r k : Noun} : KIn (C (C p q) (C l r)) k ↔ k = p ∨ KIn l k ∨ KIn r k := by
  unfold KIn
  constructor
  · rintro ⟨v, h⟩
    rcases Get_node.1 h with ⟨e, _⟩ | h | h
    · exact Or.inl e
    · exact Or.inr (Or.inl ⟨v, h⟩)
    · exact Or.inr (Or.inr ⟨v, h⟩)
  · rintro (e | ⟨v, h⟩ | ⟨v, h⟩)
    · exact ⟨q, Get_node.2 (Or.inl ⟨e, rfl⟩)⟩
    · exact ⟨v, Get_node.2 (Or.inr (Or.inl h))⟩
    · exact ⟨v, Get_node.2 (Or.inr (Or.inr h))⟩

theorem get_nil {k v : Noun} : Get (A 0) k v ↔ False := ⟨fun h => Get_atom h, False.elim⟩

/-- The pairs of the union: those of `b`, and those of `a` whose key `b`
does not hold. -/
def UniSpec (a b out : Noun) : Prop := ∀ k v, Get out k v ↔ Get b k v ∨ (Get a k v ∧ ¬ KIn b k)

theorem uniSpec_kin {a b out : Noun} (h : UniSpec a b out) (k : Noun) : KIn out k ↔ KIn a k ∨ KIn b k := by
  constructor
  · rintro ⟨v, hv⟩
    rcases (h k v).1 hv with hb | ⟨ha, _⟩
    · exact Or.inr ⟨v, hb⟩
    · exact Or.inl ⟨v, ha⟩
  · rintro (⟨v, ha⟩ | ⟨v, hb⟩)
    · by_cases hk : KIn b k
      · obtain ⟨w, hw⟩ := hk; exact ⟨w, (h k w).2 (Or.inl hw)⟩
      · exact ⟨v, (h k v).2 (Or.inr ⟨ha, hk⟩)⟩
    · exact ⟨v, (h k v).2 (Or.inl hb)⟩

/-- What the loop gives on `a` and `b`: a derivation to a map with the pairs
of `UniSpec`, with at most as many nodes as both. -/
def UniByP (mug : Noun → Nat) (a b : Noun) : Prop :=
  ∃ out, UniByR mug a b out ∧ IsMap mug out ∧ UniSpec a b out ∧ uniSz out ≤ uniSz a + uniSz b

theorem uni_sz_pair (k v l r : Noun) : uniSz (C (C k v) (C l r)) = uniSz l + uniSz r + 1 := rfl

/-- The same key at both roots: both halves are unions of fewer nodes. -/
theorem uniBy_same {mug : Noun → Nat} {m : Nat}
    (ih : ∀ a b, uniSz a + uniSz b < m → IsMap mug a → IsMap mug b → UniByP mug a b)
    {k va la ra vb lb rb : Noun} (ha : IsMap mug (C (C k va) (C la ra))) (hb : IsMap mug (C (C k vb) (C lb rb)))
    (hs : uniSz (C (C k va) (C la ra)) + uniSz (C (C k vb) (C lb rb)) ≤ m) :
    UniByP mug (C (C k va) (C la ra)) (C (C k vb) (C lb rb)) := by
  obtain ⟨hla, hra, hLa, hRa⟩ := IsMap_node ha
  obtain ⟨hlb, hrb, hLb, hRb⟩ := IsMap_node hb
  rw [uni_sz_pair, uni_sz_pair] at hs
  obtain ⟨l, h1, hl, hlk, hls⟩ := ih la lb (by omega) hla hlb
  obtain ⟨r, h2, hr, hrk, hrs⟩ := ih ra rb (by omega) hra hrb
  have d1 : ∀ k' v', Get la k' v' → ¬ KIn rb k' := fun k' v' h ⟨w, hw⟩ =>
    (hLa _ _ h).1 (gorF_antisymm mug (hLa _ _ h).2.1 (hRb _ _ hw).2.1)
  have d2 : ∀ k' v', Get ra k' v' → ¬ KIn lb k' := fun k' v' h ⟨w, hw⟩ =>
    (hLb _ _ hw).1 (gorF_antisymm mug (hLb _ _ hw).2.1 (hRa _ _ h).2.1)
  refine ⟨C (C k vb) (C l r), UniByR.same h1 h2, IsMap.node hl hr ?_ ?_, ?_, ?_⟩
  · intro k' v' hg
    rcases (hlk k' v').1 hg with h | ⟨h, _⟩
    · exact hLb _ _ h
    · exact hLa _ _ h
  · intro k' v' hg
    rcases (hrk k' v').1 hg with h | ⟨h, _⟩
    · exact hRb _ _ h
    · exact hRa _ _ h
  · intro k' v'
    have e1 := fun v' h => (hLa k' v' h).1
    have e2 := fun v' h => (hRa k' v' h).1
    have e3 := fun v' h => (hLb k' v' h).1
    have e4 := fun v' h => (hRb k' v' h).1
    have f1 := d1 k'
    have f2 := d2 k'
    rw [Get_node, Get_node, Get_node, hlk, hrk, kin_node]
    grind
  · rw [uni_sz_pair, uni_sz_pair, uni_sz_pair]; omega

theorem uni_sz_zero : uniSz (A 0) = 0 := rfl

/-- The root of `a` comes first in `+mor` order among the keys of `b`: the
loop walks down `b` with the pair of `a` at the root. -/
theorem uniBy_domA {mug : Noun → Nat} {m : Nat}
    (ih : ∀ a b, uniSz a + uniSz b < m → IsMap mug a → IsMap mug b → UniByP mug a b) :
    ∀ {b : Noun}, IsMap mug b → ∀ ka va la ra, IsMap mug (C (C ka va) (C la ra)) →
      (∀ k v, Get b k v → morF mug ka k = true) → uniSz (C (C ka va) (C la ra)) + uniSz b ≤ m →
      UniByP mug (C (C ka va) (C la ra)) b := by
  intro b hb
  induction hb with
  | nil =>
    intro ka va la ra ha _ _
    refine ⟨_, UniByR.nilB _, ha, fun k v => ?_, by rw [uni_sz_zero]; omega⟩
    simp only [get_nil, false_or]
    exact ⟨fun h => ⟨h, kin_nil⟩, fun h => h.1⟩
  | @node kb vb lb rb hlb hrb hLb hRb ihl ihr =>
    intro ka va la ra ha hdom hsz
    have hb : IsMap mug (C (C kb vb) (C lb rb)) := IsMap.node hlb hrb hLb hRb
    by_cases e : kb = ka
    · subst e; exact uniBy_same ih ha hb hsz
    have hmo : morF mug ka kb = true := hdom kb vb Get.here
    obtain ⟨hla, hra, hLa, hRa⟩ := IsMap_node ha
    have hsz' := hsz
    rw [uni_sz_pair, uni_sz_pair] at hsz'
    by_cases g : gorF mug kb ka = true
    · have hsb : IsMap mug (C (C kb vb) (C lb (A 0))) :=
        IsMap.node hlb IsMap.nil hLb (fun k v h => absurd h Get_atom)
      obtain ⟨x, h1, hx, hxk, hxs⟩ := ih la (C (C kb vb) (C lb (A 0)))
        (by rw [uni_sz_pair, uni_sz_zero]; omega) hla hsb
      rw [uni_sz_pair, uni_sz_zero] at hxs
      have hX : ∀ k v, Get x k v → k ≠ ka ∧ gorF mug k ka = true ∧ morF mug ka k = true := by
        intro k v hk
        rcases (hxk k v).1 hk with h | ⟨h, _⟩
        · rcases Get_node.1 h with ⟨rfl, _⟩ | h | h
          · exact ⟨e, g, hmo⟩
          · have gk := gorF_trans mug (hLb k v h).2.1 g
            refine ⟨fun hk' => ?_, gk, hdom k v (Get.left h)⟩
            subst hk'
            exact e (gorF_antisymm mug g (hLb _ v h).2.1)
          · exact absurd h Get_atom
        · exact hLa k v h
      have hsa : IsMap mug (C (C ka va) (C x ra)) := IsMap.node hx hra hX hRa
      obtain ⟨out, h2, ho, hok, hos⟩ := ihr ka va x ra hsa
        (fun k v hk => hdom k v (Get.right hk)) (by rw [uni_sz_pair]; omega)
      rw [uni_sz_pair] at hos
      refine ⟨out, UniByR.mg e hmo g h1 h2, ho, fun k v => ?_, by rw [uni_sz_pair, uni_sz_pair]; omega⟩
      have F1 : k = kb → ¬ KIn rb k := fun hk ⟨w, hw⟩ => (hRb k w hw).1 hk
      have F2 : ∀ v, Get lb k v → ¬ KIn rb k := fun v h ⟨w, hw⟩ =>
        (hLb k v h).1 (gorF_antisymm mug (hLb k v h).2.1 (hRb k w hw).2.1)
      have F3 : k = ka → k ≠ kb ∧ ¬ KIn lb k := by
        rintro rfl
        exact ⟨fun h => e h.symm, fun ⟨w, hw⟩ => e (gorF_antisymm mug g (hLb k w hw).2.1)⟩
      have F4 : ∀ v, Get ra k v → k ≠ kb ∧ ¬ KIn lb k := by
        intro v h
        refine ⟨fun hk => ?_, fun ⟨w, hw⟩ => ?_⟩
        · subst hk; exact e (gorF_antisymm mug g (hRa k v h).2.1)
        · exact (hRa k v h).1 (gorF_antisymm mug (gorF_trans mug (hLb k w hw).2.1 g) (hRa k v h).2.1)
      rw [hok k v]
      simp only [Get_node]
      rw [hxk k v]
      simp only [Get_node, get_nil, kin_node, false_or, or_false]
      have kn := @kin_nil k
      clear ih ihl ihr hdom hsz hsz' hX hsa h1 h2 hxk hok hos hxs ho hx hsb hb hla hra hlb hrb hLa hRa hLb hRb
      grind
    · have g' : gorF mug ka kb = true := gorF_of_not mug g
      have gf : gorF mug kb ka = false := by simpa using g
      have hsb : IsMap mug (C (C kb vb) (C (A 0) rb)) :=
        IsMap.node IsMap.nil hrb (fun k v h => absurd h Get_atom) hRb
      obtain ⟨x, h1, hx, hxk, hxs⟩ := ih ra (C (C kb vb) (C (A 0) rb))
        (by rw [uni_sz_pair, uni_sz_zero]; omega) hra hsb
      rw [uni_sz_pair, uni_sz_zero] at hxs
      have hX : ∀ k v, Get x k v → k ≠ ka ∧ gorF mug ka k = true ∧ morF mug ka k = true := by
        intro k v hk
        rcases (hxk k v).1 hk with h | ⟨h, _⟩
        · rcases Get_node.1 h with ⟨rfl, _⟩ | h | h
          · exact ⟨e, g', hmo⟩
          · exact absurd h Get_atom
          · have gk := gorF_trans mug g' (hRb k v h).2.1
            refine ⟨fun hk' => ?_, gk, hdom k v (Get.right h)⟩
            subst hk'
            exact e (gorF_antisymm mug (hRb _ v h).2.1 g')
        · exact hRa k v h
      have hsa : IsMap mug (C (C ka va) (C la x)) := IsMap.node hla hx hLa hX
      obtain ⟨out, h2, ho, hok, hos⟩ := ihl ka va la x hsa
        (fun k v hk => hdom k v (Get.left hk)) (by rw [uni_sz_pair]; omega)
      rw [uni_sz_pair] at hos
      refine ⟨out, UniByR.mn e hmo gf h1 h2, ho, fun k v => ?_, by rw [uni_sz_pair, uni_sz_pair]; omega⟩
      have F1 : k = kb → ¬ KIn lb k := fun hk ⟨w, hw⟩ => (hLb k w hw).1 hk
      have F2 : ∀ v, Get rb k v → ¬ KIn lb k := fun v h ⟨w, hw⟩ =>
        (hLb k w hw).1 (gorF_antisymm mug (hLb k w hw).2.1 (hRb k v h).2.1)
      have F3 : k = ka → k ≠ kb ∧ ¬ KIn rb k := by
        rintro rfl
        exact ⟨fun h => e h.symm, fun ⟨w, hw⟩ => e (gorF_antisymm mug (hRb k w hw).2.1 g')⟩
      have F4 : ∀ v, Get la k v → k ≠ kb ∧ ¬ KIn rb k := by
        intro v h
        refine ⟨fun hk => ?_, fun ⟨w, hw⟩ => ?_⟩
        · subst hk; exact e (gorF_antisymm mug (hLa k v h).2.1 g')
        · exact (hLa k v h).1 (gorF_antisymm mug (hLa k v h).2.1 (gorF_trans mug g' (hRb k w hw).2.1))
      rw [hok k v]
      simp only [Get_node]
      rw [hxk k v]
      simp only [Get_node, get_nil, kin_node, false_or, or_false]
      have kn := @kin_nil k
      clear ih ihl ihr hdom hsz hsz' hX hsa h1 h2 hxk hok hos hxs ho hx hsb hb hla hra hlb hrb hLa hRa hLb hRb
      grind

/-- The root of `b` comes first in `+mor` order among the keys of `a`: the
loop walks down `a` with the pair of `b` at the root. -/
theorem uniBy_domB {mug : Noun → Nat} {m : Nat}
    (ih : ∀ a b, uniSz a + uniSz b < m → IsMap mug a → IsMap mug b → UniByP mug a b) :
    ∀ {a : Noun}, IsMap mug a → ∀ kb vb lb rb, IsMap mug (C (C kb vb) (C lb rb)) →
      (∀ k v, Get a k v → morF mug kb k = true) → uniSz a + uniSz (C (C kb vb) (C lb rb)) ≤ m →
      UniByP mug a (C (C kb vb) (C lb rb)) := by
  intro a ha
  induction ha with
  | nil =>
    intro kb vb lb rb hb _ _
    refine ⟨_, UniByR.nilA _ (by simp), hb, fun k v => ?_, by rw [uni_sz_zero]; omega⟩
    simp only [get_nil, false_and, or_false]
  | @node ka va la ra hla hra hLa hRa ihl ihr =>
    intro kb vb lb rb hb hdom hsz
    have ha : IsMap mug (C (C ka va) (C la ra)) := IsMap.node hla hra hLa hRa
    by_cases e : kb = ka
    · subst e; exact uniBy_same ih ha hb hsz
    have e' : ka ≠ kb := fun h => e h.symm
    have hmo : morF mug kb ka = true := hdom ka va Get.here
    have hmf : morF mug ka kb = false := by
      cases h : morF mug ka kb
      · rfl
      · exact absurd (morF_antisymm mug hmo h) e
    obtain ⟨hlb, hrb, hLb, hRb⟩ := IsMap_node hb
    have hsz' := hsz
    rw [uni_sz_pair, uni_sz_pair] at hsz'
    by_cases g : gorF mug ka kb = true
    · have hsa : IsMap mug (C (C ka va) (C la (A 0))) :=
        IsMap.node hla IsMap.nil hLa (fun k v h => absurd h Get_atom)
      obtain ⟨x, h1, hx, hxk, hxs⟩ := ih (C (C ka va) (C la (A 0))) lb
        (by rw [uni_sz_pair, uni_sz_zero]; omega) hsa hlb
      rw [uni_sz_pair, uni_sz_zero] at hxs
      have hX : ∀ k v, Get x k v → k ≠ kb ∧ gorF mug k kb = true ∧ morF mug kb k = true := by
        intro k v hk
        rcases (hxk k v).1 hk with h | ⟨h, _⟩
        · exact hLb k v h
        · rcases Get_node.1 h with ⟨rfl, _⟩ | h | h
          · exact ⟨e', g, hmo⟩
          · have gk := gorF_trans mug (hLa k v h).2.1 g
            refine ⟨fun hk' => ?_, gk, hdom k v (Get.left h)⟩
            subst hk'
            exact e (gorF_antisymm mug (hLa _ v h).2.1 g)
          · exact absurd h Get_atom
      have hsb : IsMap mug (C (C kb vb) (C x rb)) := IsMap.node hx hrb hX hRb
      obtain ⟨out, h2, ho, hok, hos⟩ := ihr kb vb x rb hsb
        (fun k v hk => hdom k v (Get.right hk)) (by rw [uni_sz_pair]; omega)
      rw [uni_sz_pair] at hos
      refine ⟨out, UniByR.ng e hmf g h1 h2, ho, fun k v => ?_, by rw [uni_sz_pair, uni_sz_pair]; omega⟩
      have G1 : k = ka → k ≠ kb ∧ ¬ KIn rb k := by
        rintro rfl
        exact ⟨e', fun ⟨w, hw⟩ => e (gorF_antisymm mug (hRb k w hw).2.1 g)⟩
      have G2 : ∀ v, Get la k v → k ≠ kb ∧ ¬ KIn rb k := by
        intro v h
        refine ⟨fun hk => ?_, fun ⟨w, hw⟩ => ?_⟩
        · subst hk; exact e (gorF_antisymm mug (hLa k v h).2.1 g)
        · exact (hRb k w hw).1 (gorF_antisymm mug (gorF_trans mug (hLa k v h).2.1 g) (hRb k w hw).2.1)
      have G3 : ∀ v, Get ra k v → k ≠ ka ∧ ¬ KIn la k := fun v h =>
        ⟨(hRa k v h).1, fun ⟨w, hw⟩ => (hLa k w hw).1 (gorF_antisymm mug (hLa k w hw).2.1 (hRa k v h).2.1)⟩
      have hxK := uniSpec_kin hxk k
      rw [hok k v]
      simp only [Get_node, kin_node]
      rw [hxk k v, hxK]
      simp only [Get_node, get_nil, kin_node, kin_nil, false_or, or_false]
      clear ih ihl ihr hdom hsz hsz' hX hsa hsb h1 h2 hxk hok hos hxs ho hx hb ha hla hra hlb hrb hLa hRa hLb hRb hxK
      grind
    · have g' : gorF mug kb ka = true := gorF_of_not mug g
      have gf : gorF mug ka kb = false := by simpa using g
      have hsa : IsMap mug (C (C ka va) (C (A 0) ra)) :=
        IsMap.node IsMap.nil hra (fun k v h => absurd h Get_atom) hRa
      obtain ⟨x, h1, hx, hxk, hxs⟩ := ih (C (C ka va) (C (A 0) ra)) rb
        (by rw [uni_sz_pair, uni_sz_zero]; omega) hsa hrb
      rw [uni_sz_pair, uni_sz_zero] at hxs
      have hX : ∀ k v, Get x k v → k ≠ kb ∧ gorF mug kb k = true ∧ morF mug kb k = true := by
        intro k v hk
        rcases (hxk k v).1 hk with h | ⟨h, _⟩
        · exact hRb k v h
        · rcases Get_node.1 h with ⟨rfl, _⟩ | h | h
          · exact ⟨e', g', hmo⟩
          · exact absurd h Get_atom
          · have gk := gorF_trans mug g' (hRa k v h).2.1
            refine ⟨fun hk' => ?_, gk, hdom k v (Get.right h)⟩
            subst hk'
            exact e (gorF_antisymm mug g' (hRa _ v h).2.1)
      have hsb : IsMap mug (C (C kb vb) (C lb x)) := IsMap.node hlb hx hLb hX
      obtain ⟨out, h2, ho, hok, hos⟩ := ihl kb vb lb x hsb
        (fun k v hk => hdom k v (Get.left hk)) (by rw [uni_sz_pair]; omega)
      rw [uni_sz_pair] at hos
      refine ⟨out, UniByR.nn e hmf gf h1 h2, ho, fun k v => ?_, by rw [uni_sz_pair, uni_sz_pair]; omega⟩
      have G1 : k = ka → k ≠ kb ∧ ¬ KIn lb k := by
        rintro rfl
        exact ⟨e', fun ⟨w, hw⟩ => e (gorF_antisymm mug g' (hLb k w hw).2.1)⟩
      have G2 : ∀ v, Get ra k v → k ≠ kb ∧ ¬ KIn lb k := by
        intro v h
        refine ⟨fun hk => ?_, fun ⟨w, hw⟩ => ?_⟩
        · subst hk; exact e (gorF_antisymm mug g' (hRa k v h).2.1)
        · exact (hLb k w hw).1 (gorF_antisymm mug (hLb k w hw).2.1 (gorF_trans mug g' (hRa k v h).2.1))
      have G3 : ∀ v, Get la k v → k ≠ ka ∧ ¬ KIn ra k := fun v h =>
        ⟨(hLa k v h).1, fun ⟨w, hw⟩ => (hRa k w hw).1 (gorF_antisymm mug (hLa k v h).2.1 (hRa k w hw).2.1)⟩
      have hxK := uniSpec_kin hxk k
      rw [hok k v]
      simp only [Get_node, kin_node]
      rw [hxk k v, hxK]
      simp only [Get_node, get_nil, kin_node, kin_nil, false_or, or_false]
      clear ih ihl ihr hdom hsz hsz' hX hsa hsb h1 h2 hxk hok hos hxs ho hx hb ha hla hra hlb hrb hLa hRa hLb hRb hxK
      grind

/-- One level of the induction on the number of nodes. -/
theorem uniBy_step {mug : Noun → Nat} {m : Nat}
    (ih : ∀ a b, uniSz a + uniSz b < m → IsMap mug a → IsMap mug b → UniByP mug a b)
    (a b : Noun) (hs : uniSz a + uniSz b ≤ m) (ha : IsMap mug a) (hb : IsMap mug b) :
    UniByP mug a b := by
  cases hb with
  | nil =>
    refine ⟨a, UniByR.nilB a, ha, fun k v => ?_, by rw [uni_sz_zero]; omega⟩
    simp only [get_nil, false_or]
    exact ⟨fun h => ⟨h, kin_nil⟩, fun h => h.1⟩
  | @node kb vb lb rb hlb hrb hLb hRb =>
    have hb : IsMap mug (C (C kb vb) (C lb rb)) := IsMap.node hlb hrb hLb hRb
    cases ha with
    | nil => exact uniBy_domB ih IsMap.nil kb vb lb rb hb (fun k v h => absurd h Get_atom) hs
    | @node ka va la ra hla hra hLa hRa =>
      have ha : IsMap mug (C (C ka va) (C la ra)) := IsMap.node hla hra hLa hRa
      by_cases mo : morF mug ka kb = true
      · refine uniBy_domA ih hb ka va la ra ha (fun k v hk => ?_) hs
        rcases Get_node.1 hk with ⟨rfl, _⟩ | h | h
        · exact mo
        · exact morF_trans mug mo (hLb k v h).2.2
        · exact morF_trans mug mo (hRb k v h).2.2
      · have mo' := morF_of_not mug mo
        refine uniBy_domB ih ha kb vb lb rb hb (fun k v hk => ?_) hs
        rcases Get_node.1 hk with ⟨rfl, _⟩ | h | h
        · exact mo'
        · exact morF_trans mug mo' (hLa k v h).2.2
        · exact morF_trans mug mo' (hRa k v h).2.2

theorem uniByP_of_maps {mug : Noun → Nat} : ∀ (m : Nat) (a b : Noun), uniSz a + uniSz b ≤ m →
    IsMap mug a → IsMap mug b → UniByP mug a b := by
  intro m
  induction m with
  | zero => exact uniBy_step (fun a b h => absurd h (Nat.not_lt_zero _))
  | succ m ih => exact uniBy_step (fun a b h ha hb => ih a b (by omega) ha hb)

/-- **`+uni:by` on two maps**, in a context with `+gor` and `+mor`: a map
with the pairs of `b` and those of `a` whose key `b` does not hold. -/
theorem uni_by {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx) (a b : Noun)
    (ha : IsMap mug a) (hb : IsMap mug b) :
    ∃ out, nock (C by.uni.battery (C b (C by.battery (C a ctx)))) by.uni.battery = some out ∧
      IsMap mug out ∧ UniSpec a b out := by
  obtain ⟨out, h, hs, hk, _⟩ := uniByP_of_maps _ a b (Nat.le_refl _) ha hb
  exact ⟨out, uni_by_gate ctx hc h, hs, hk⟩

/-- **`+uni:by` of a map `a` and a map of one pair `[[k v] ~ ~]`** is `+put:by`
of `a` at `k`: the same noun as `putF`, both maps with the same pairs. -/
theorem uni_by_one {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx) (a k v : Noun)
    (ha : IsMap mug a) :
    nock (C by.uni.battery (C (C (C k v) (C (A 0) (A 0))) (C by.battery (C a ctx)))) by.uni.battery
      = putF mug k v a := by
  have hb : IsMap mug (C (C k v) (C (A 0) (A 0))) :=
    IsMap.node IsMap.nil IsMap.nil (fun _ _ h => absurd h Get_atom) (fun _ _ h => absurd h Get_atom)
  obtain ⟨out, hn, ho, hs⟩ := uni_by ctx hc a _ ha hb
  obtain ⟨out', hp, ho', hg⟩ := putF_spec mug a k v ha
  rw [hn, hp, isMap_ext ho ho' fun k' v' => ?_]
  rw [hs k' v', hg k' v', Get_node, kin_node]
  simp only [get_nil, kin_nil, or_false]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h2, h1⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h2, h1⟩

end Hoon
end Formalization

end
