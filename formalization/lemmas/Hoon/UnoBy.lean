module

public import lemmas.Hoon.UniBy
import lemmas.KernelRfl
import all lemmas.Pill.Arm.By

/-!
`+uno:by` of the pill's `hoon.hoon`, the general union of two maps.

```hoon
++  uno                                               ::  general union
  |*  b=_a
  |*  meg=$-([* * *] *)
  |-  ^+  a
  ?~  b
    a
  ?~  a
    b
  ?:  =(p.n.b p.n.a)
    :+  [p.n.a `_?>(?=(^ a) q.n.a)`(meg p.n.a q.n.a q.n.b)]
      $(b l.b, a l.a)
    $(b r.b, a r.a)
  ?:  (mor p.n.a p.n.b)
    ?:  (gor p.n.b p.n.a)
      $(l.a $(a l.a, r.b ~), b r.b)
    $(r.a $(a r.a, l.b ~), b l.b)
  ?:  (gor p.n.a p.n.b)
    $(l.b $(b l.b, r.a ~), a r.a)
  $(r.b $(b r.b, l.a ~), a l.a)
```

The arm is at axis `2` of the battery of `+by` (`uno_at`, axis `4` of the
door), with no jet hint; the nouns were cut by `tools/gen/optlink.py uno`.
The arm makes the gate `|*  b=_a` (`unoOuter`) with the door's map as its
bunt, which makes the gate `|*  meg` (`unoMegGate`), whose body kicks the
trap `unoTrap`.  The trap is that of `+uni:by` (`Hoon/UniBy.lean`) with the
pair `[p.n.a (meg p.n.a q.n.a q.n.b)]` where the keys are equal.

The model is the relation `UnoByR mug V f`, one constructor per branch,
where the gate `meg` returns `f k va vb` on two values with `V`; `uno_loop`
runs the Nock on every derivation.  `unoByP_of_maps` builds a derivation on
two maps whose values have `V` (with `f` keeping `V`), as `uniByP_of_maps`
does, to a map whose value at each key is `mergeO f k` of the values of
`a` and `b` there (`look`: the value at a key, the first in pre-order; on a
map it is `Get`, `look_get`).  `uno_by`: the whole call, `~(uno by a)`
slammed on `b` and then on the gate `meg`.
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

/-! ## The nouns -/

/-- The trap of `+uno:by`. -/
def unoTrap : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 62)))) (C (C (A 0) (A 254)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 254)))) (C (C (A 0) (A 62)) (C (A 6) (C (C (A 5) (C (C (A 0) (A 248)) (C (A 0) (A 1016)))) (C (C (C (C (A 0) (A 1016)) (C (A 8) (C (C (A 0) (A 14)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 2040)) (C (C (A 0) (A 2041)) (C (A 0) (A 505))))) (C (A 0) (A 2))))))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 254) (C (A 0) (A 1018))) (C (A 10) (C (C (A 62) (C (A 0) (A 250))) (C (A 0) (A 1)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 254) (C (A 0) (A 1019))) (C (A 10) (C (C (A 62) (C (A 0) (A 251))) (C (A 0) (A 1)))))))))) (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 90) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 2040)) (C (A 0) (A 504)))) (C (A 0) (A 2)))))))) (C (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 182) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 504)) (C (A 0) (A 2040)))) (C (A 0) (A 2)))))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 1018) (C (A 9) (C (A 2) (C (A 10) (C (C (A 254) (C (A 0) (A 1018))) (C (A 10) (C (C (A 251) (C (A 1) (A 0))) (C (A 0) (A 1))))))))) (C (A 10) (C (C (A 62) (C (A 0) (A 251))) (C (A 0) (A 1)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 1019) (C (A 9) (C (A 2) (C (A 10) (C (C (A 254) (C (A 0) (A 1019))) (C (A 10) (C (C (A 250) (C (A 1) (A 0))) (C (A 0) (A 1))))))))) (C (A 10) (C (C (A 62) (C (A 0) (A 250))) (C (A 0) (A 1))))))))))) (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 182) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 2040)) (C (A 0) (A 504)))) (C (A 0) (A 2)))))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 254) (C (A 0) (A 1019))) (C (A 10) (C (C (A 250) (C (A 9) (C (A 2) (C (A 10) (C (C (A 1019) (C (A 1) (A 0))) (C (A 10) (C (C (A 62) (C (A 0) (A 250))) (C (A 0) (A 1))))))))) (C (A 0) (A 1)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 254) (C (A 0) (A 1018))) (C (A 10) (C (C (A 251) (C (A 9) (C (A 2) (C (A 10) (C (C (A 1018) (C (A 1) (A 0))) (C (A 10) (C (C (A 62) (C (A 0) (A 251))) (C (A 0) (A 1))))))))) (C (A 0) (A 1)))))))))))))))))))))))

/-- The body of the gate `|*  meg` that `+uno:by` makes: the trap, kicked. -/
def unoMegGate : Noun :=
  (C (A 8) (C (C (A 1) unoTrap) (C (A 9) (C (A 2) (C (A 0) (A 1))))))

/-- Its sample bunt. -/
def unoMegBunt : Noun :=
  (C (C (A 0) (A 15)) (C (C (A 0) (C (A 0) (A 0))) (C (C (A 0) (C (A 0) (A 0))) (A 0))))

/-- The body of the gate `|*  b=_a`: it makes the gate `|*  meg`. -/
def unoOuter : Noun :=
  (C (A 8) (C (C (A 1) unoMegBunt) (C (C (A 1) unoMegGate) (C (A 0) (A 1)))))

/-- The arm `+uno:by` (axis `2` of the battery of `+by`). -/
def unoArm : Noun :=
  (C (A 8) (C (C (A 0) (A 6)) (C (C (A 1) unoOuter) (C (A 0) (A 1)))))

/-- `+uno:by` is axis `2` of the battery of `+by`. -/
theorem uno_at : ∀ x, slot? 4 (C by.battery x) = some unoArm := by
  intro x; kernel_rfl

@[nock_exec] theorem uno_arm (a ctx : Noun) :
    nock (C by.battery (C a ctx)) unoArm = some (C unoOuter (C a (C by.battery (C a ctx)))) := by
  unfold unoArm; generalize unoOuter = O; simp [nock_exec]

/-- The gate `|*  b=_a` slammed on `b`: the gate `|*  meg`. -/
theorem uno_outer (b D : Noun) :
    nock (C unoOuter (C b D)) unoOuter = some (C unoMegGate (C unoMegBunt (C unoOuter (C b D)))) := by
  conv => lhs; arg 2; unfold unoOuter
  generalize unoMegGate = G; generalize unoMegBunt = U; generalize unoOuter = O; simp [nock_exec]

/-! ## The model -/

/-- The loop of `+uno:by`, one constructor per branch; `meg` gives `f k va
vb` on values with `V`. -/
inductive UnoByR (mug : Noun → Nat) (V : Noun → Prop) (f : Noun → Noun → Noun → Noun) :
    Noun → Noun → Noun → Prop where
  | nilB (a : Noun) : UnoByR mug V f a (A 0) a
  | nilA (b : Noun) : b ≠ A 0 → UnoByR mug V f (A 0) b b
  | same {k va la ra vb lb rb l r : Noun} : V va → V vb → UnoByR mug V f la lb l → UnoByR mug V f ra rb r →
      UnoByR mug V f (C (C k va) (C la ra)) (C (C k vb) (C lb rb)) (C (C k (f k va vb)) (C l r))
  | mg {ka va la ra kb vb lb rb x out : Noun} : kb ≠ ka → morF mug ka kb = true →
      gorF mug kb ka = true → UnoByR mug V f la (C (C kb vb) (C lb (A 0))) x →
      UnoByR mug V f (C (C ka va) (C x ra)) rb out →
      UnoByR mug V f (C (C ka va) (C la ra)) (C (C kb vb) (C lb rb)) out
  | mn {ka va la ra kb vb lb rb x out : Noun} : kb ≠ ka → morF mug ka kb = true →
      gorF mug kb ka = false → UnoByR mug V f ra (C (C kb vb) (C (A 0) rb)) x →
      UnoByR mug V f (C (C ka va) (C la x)) lb out →
      UnoByR mug V f (C (C ka va) (C la ra)) (C (C kb vb) (C lb rb)) out
  | ng {ka va la ra kb vb lb rb x out : Noun} : kb ≠ ka → morF mug ka kb = false →
      gorF mug ka kb = true → UnoByR mug V f (C (C ka va) (C la (A 0))) lb x →
      UnoByR mug V f ra (C (C kb vb) (C x rb)) out →
      UnoByR mug V f (C (C ka va) (C la ra)) (C (C kb vb) (C lb rb)) out
  | nn {ka va la ra kb vb lb rb x out : Noun} : kb ≠ ka → morF mug ka kb = false →
      gorF mug ka kb = false → UnoByR mug V f (C (C ka va) (C (A 0) ra)) rb x →
      UnoByR mug V f la (C (C kb vb) (C lb x)) out →
      UnoByR mug V f (C (C ka va) (C la ra)) (C (C kb vb) (C lb rb)) out

/-! ## The Nock -/

theorem uno_loop {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx)
    (V : Noun → Prop) (f : Noun → Noun → Noun → Noun) (MB MS MC : Noun)
    (hf : ∀ k va vb, V va → V vb → nock (C MB (C (C k (C va vb)) MC)) MB = some (f k va vb)) :
    ∀ {a b out : Noun}, UnoByR mug V f a b out →
      nock (C unoTrap (C unoMegGate (C (C MB (C MS MC)) (C unoOuter (C b (C by.battery (C a ctx)))))))
        unoTrap = some out := by
  have hgor := gor_gate (mug := mug) ctx hc.1.2
  have hmor := mor_gate (mug := mug) ctx hc.2.2
  have hg := hc.1.1
  have hm := hc.2.1
  intro a b out h
  induction h with
  | nilB a =>
    nock_open unoTrap
    simp [nock_exec]
  | nilA b hb =>
    nock_open unoTrap
    simp [nock_exec, Ne.symm hb]
  | @same k va la ra vb lb rb l r v1 v2 _ _ ih1 ih2 =>
    have h3 := hf k va vb v1 v2
    nock_open unoTrap
    simp [nock_exec, ih1, ih2, h3]
  | mg e m g _ _ ih1 ih2 =>
    nock_open unoTrap
    simp [nock_exec, e, m, g, hg, hm, hgor, hmor, ih1, ih2]
  | mn e m g _ _ ih1 ih2 =>
    nock_open unoTrap
    simp [nock_exec, e, m, g, hg, hm, hgor, hmor, ih1, ih2]
  | ng e m g _ _ ih1 ih2 =>
    nock_open unoTrap
    simp [nock_exec, e, m, g, hg, hm, hgor, hmor, ih1, ih2]
  | nn e m g _ _ ih1 ih2 =>
    nock_open unoTrap
    simp [nock_exec, e, m, g, hg, hm, hgor, hmor, ih1, ih2]

/-- The gate `|*  meg` slammed on the gate `[MB [MS MC]]`. -/
theorem uno_gate {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx)
    (V : Noun → Prop) (f : Noun → Noun → Noun → Noun) (MB MS MC : Noun)
    (hf : ∀ k va vb, V va → V vb → nock (C MB (C (C k (C va vb)) MC)) MB = some (f k va vb))
    {a b out : Noun} (h : UnoByR mug V f a b out) :
    nock (C unoMegGate (C (C MB (C MS MC)) (C unoOuter (C b (C by.battery (C a ctx)))))) unoMegGate
      = some out := by
  have hl := uno_loop ctx hc V f MB MS MC hf h
  conv => lhs; arg 2; unfold unoMegGate
  generalize unoTrap = T at hl ⊢
  simp [nock_exec, hl]

/-! ## The value at a key -/

/-- The value at a key: the first in pre-order. -/
def look : Noun → Noun → Option Noun
  | Noun.cell (Noun.cell p q) (Noun.cell l r), k => if k = p then some q else (look l k).or (look r k)
  | _, _ => none

theorem look_node (p q l r k : Noun) :
    look (C (C p q) (C l r)) k = if k = p then some q else (look l k).or (look r k) := rfl

theorem look_nil (k : Noun) : look (A 0) k = none := rfl

/-- On a map, `look` is `Get`. -/
theorem look_get {mug : Noun → Nat} {a : Noun} (h : IsMap mug a) : ∀ k v, look a k = some v ↔ Get a k v := by
  induction h with
  | nil => intro k v; simp [look_nil, Get_atom]
  | @node p q l r hl hr hL hR ihl ihr =>
    intro k v
    rw [look_node, Get_node]
    by_cases e : k = p
    · subst e
      simp only [if_true, Option.some.injEq, true_and]
      constructor
      · rintro rfl; exact Or.inl rfl
      · rintro (rfl | h | h)
        · rfl
        · exact absurd rfl (hL _ _ h).1
        · exact absurd rfl (hR _ _ h).1
    · simp only [e, if_false, false_and, false_or]
      rw [← ihl, ← ihr]
      cases e1 : look l k with
      | none => simp
      | some w =>
        simp only [Option.some_or, Option.some.injEq]
        constructor
        · intro h; exact Or.inl h
        · rintro (h | h)
          · exact h
          · exfalso
            have g1 := (hL k w ((ihl k w).1 e1)).2.1
            have g2 := (hR k v ((ihr k v).1 h)).2.1
            exact (hL k w ((ihl k w).1 e1)).1 (gorF_antisymm mug g1 g2)

theorem look_none {mug : Noun → Nat} {a : Noun} (h : IsMap mug a) (k : Noun) : look a k = none ↔ ¬ KIn a k := by
  constructor
  · rintro e ⟨v, hv⟩
    rw [← look_get h] at hv
    rw [e] at hv
    cases hv
  · intro hk
    cases e : look a k with
    | none => rfl
    | some v => exact absurd ⟨v, (look_get h k v).1 e⟩ hk

/-- `look` of a key with no value under the ordering facts of a node. -/
theorem look_ord {mug : Noun → Nat} {a : Noun} (h : IsMap mug a) {k : Noun} {P : Prop}
    (hP : ∀ v, Get a k v → P) : look a k ≠ none → P := by
  intro e
  cases e1 : look a k with
  | none => exact absurd e1 e
  | some v => exact hP v ((look_get h k v).1 e1)

theorem eq_none_of {o : Option Noun} {P : Prop} (h : o ≠ none → P) (hn : ¬ P) : o = none := by
  cases o with
  | none => rfl
  | some w => exact absurd (h (by simp)) hn

/-- The value at a key of the union, from those of the two maps. -/
def mergeO (f : Noun → Noun → Noun → Noun) (k : Noun) : Option Noun → Option Noun → Option Noun
  | some va, some vb => some (f k va vb)
  | x, none => x
  | none, y => y

theorem mergeO_none_left (f : Noun → Noun → Noun → Noun) (k : Noun) (y : Option Noun) :
    mergeO f k none y = y := by cases y <;> rfl

theorem mergeO_none_right (f : Noun → Noun → Noun → Noun) (k : Noun) (x : Option Noun) :
    mergeO f k x none = x := by cases x <;> rfl

/-- Every value of the map has `V`. -/
def VAll (V : Noun → Prop) (a : Noun) : Prop := ∀ k v, Get a k v → V v

/-- What the loop gives on `a` and `b`: a derivation to a map whose values
have `V` and whose value at each key is `mergeO`, with at most as many nodes
as both. -/
def UnoByP (mug : Noun → Nat) (V : Noun → Prop) (f : Noun → Noun → Noun → Noun) (a b : Noun) : Prop :=
  ∃ out, UnoByR mug V f a b out ∧ IsMap mug out ∧ VAll V out ∧
    (∀ k, look out k = mergeO f k (look a k) (look b k)) ∧ uniSz out ≤ uniSz a + uniSz b

/-- A key of the union is a key of one of the maps. -/
theorem kin_of_merge {mug : Noun → Nat} {f : Noun → Noun → Noun → Noun} {a b out : Noun}
    (ho : IsMap mug out) (hs : ∀ k, look out k = mergeO f k (look a k) (look b k)) {k v : Noun}
    (hk : Get out k v) : look a k ≠ none ∨ look b k ≠ none := by
  have e := (look_get ho k v).2 hk
  rw [hs k] at e
  cases e1 : look a k with
  | none =>
    cases e2 : look b k with
    | none => rw [e1, e2] at e; cases e
    | some w => exact Or.inr (by simp)
  | some w => exact Or.inl (by simp)

/-- The ordering facts of a key of a map, from `look`. -/
theorem ord_of_look {mug : Noun → Nat} {a : Noun} (ha : IsMap mug a) {k p : Noun}
    (hO : ∀ k v, Get a k v → k ≠ p ∧ gorF mug k p = true ∧ morF mug p k = true) :
    look a k ≠ none → k ≠ p ∧ gorF mug k p = true ∧ morF mug p k = true :=
  look_ord ha (fun v h => hO k v h)

theorem ord_of_look' {mug : Noun → Nat} {a : Noun} (ha : IsMap mug a) {k p : Noun}
    (hO : ∀ k v, Get a k v → k ≠ p ∧ gorF mug p k = true ∧ morF mug p k = true) :
    look a k ≠ none → k ≠ p ∧ gorF mug p k = true ∧ morF mug p k = true :=
  look_ord ha (fun v h => hO k v h)

theorem vall_node {V : Noun → Prop} {p q l r : Noun} (h : VAll V (C (C p q) (C l r))) :
    V q ∧ VAll V l ∧ VAll V r :=
  ⟨h p q Get.here, fun k v hk => h k v (Get.left hk), fun k v hk => h k v (Get.right hk)⟩

theorem vall_mk {V : Noun → Prop} {p q l r : Noun} (hq : V q) (hl : VAll V l) (hr : VAll V r) :
    VAll V (C (C p q) (C l r)) := by
  intro k v hk
  rcases Get_node.1 hk with ⟨-, rfl⟩ | h | h
  · exact hq
  · exact hl k v h
  · exact hr k v h

theorem vall_nil {V : Noun → Prop} : VAll V (A 0) := fun _ _ h => absurd h Get_atom

/-- The same key at both roots: both halves are unions of fewer nodes. -/
theorem unoBy_same {mug : Noun → Nat} {V : Noun → Prop} {f : Noun → Noun → Noun → Noun} {m : Nat}
    (hV : ∀ k va vb, V va → V vb → V (f k va vb))
    (ih : ∀ a b, uniSz a + uniSz b < m → IsMap mug a → IsMap mug b → VAll V a → VAll V b → UnoByP mug V f a b)
    {k va la ra vb lb rb : Noun} (ha : IsMap mug (C (C k va) (C la ra))) (hb : IsMap mug (C (C k vb) (C lb rb)))
    (hva : VAll V (C (C k va) (C la ra))) (hvb : VAll V (C (C k vb) (C lb rb)))
    (hs : uniSz (C (C k va) (C la ra)) + uniSz (C (C k vb) (C lb rb)) ≤ m) :
    UnoByP mug V f (C (C k va) (C la ra)) (C (C k vb) (C lb rb)) := by
  obtain ⟨hla, hra, hLa, hRa⟩ := IsMap_node ha
  obtain ⟨hlb, hrb, hLb, hRb⟩ := IsMap_node hb
  obtain ⟨v1, vla, vra⟩ := vall_node hva
  obtain ⟨v2, vlb, vrb⟩ := vall_node hvb
  rw [uni_sz_pair, uni_sz_pair] at hs
  obtain ⟨l, h1, hl, vl, hlk, hls⟩ := ih la lb (by omega) hla hlb vla vlb
  obtain ⟨r, h2, hr, vr, hrk, hrs⟩ := ih ra rb (by omega) hra hrb vra vrb
  refine ⟨C (C k (f k va vb)) (C l r), UnoByR.same v1 v2 h1 h2, IsMap.node hl hr ?_ ?_,
    vall_mk (hV k va vb v1 v2) vl vr, ?_, ?_⟩
  · intro k' v' hg
    rcases kin_of_merge hl hlk hg with h | h
    · exact ord_of_look hla hLa h
    · exact ord_of_look hlb hLb h
  · intro k' v' hg
    rcases kin_of_merge hr hrk hg with h | h
    · exact ord_of_look' hra hRa h
    · exact ord_of_look' hrb hRb h
  · intro k'
    rw [look_node, look_node, look_node, hlk, hrk]
    have A1 := ord_of_look hla hLa (k := k')
    have A2 := ord_of_look' hra hRa (k := k')
    have B1 := ord_of_look hlb hLb (k := k')
    have B2 := ord_of_look' hrb hRb (k := k')
    have G : ∀ x y, gorF mug x k = true → gorF mug k y = true → x ≠ k → x ≠ y := by
      intro x y g1 g2 hx e
      subst e
      exact hx (gorF_antisymm mug g1 g2)
    by_cases e : k' = k
    · subst e
      have c1 : look la k' = none := eq_none_of (fun c => (A1 c).1) (fun h => h rfl)
      have c2 : look ra k' = none := eq_none_of (fun c => (A2 c).1) (fun h => h rfl)
      have c3 : look lb k' = none := eq_none_of (fun c => (B1 c).1) (fun h => h rfl)
      have c4 : look rb k' = none := eq_none_of (fun c => (B2 c).1) (fun h => h rfl)
      simp [mergeO, c1, c2, c3, c4]
    · simp only [e, if_false]
      have d1 : look la k' ≠ none → look ra k' = none ∧ look rb k' = none := by
        intro c
        have g := A1 c
        exact ⟨eq_none_of (fun c' => (A2 c').2.1) (fun g2 => g.1 (gorF_antisymm mug g.2.1 g2)),
          eq_none_of (fun c' => (B2 c').2.1) (fun g2 => g.1 (gorF_antisymm mug g.2.1 g2))⟩
      have d2 : look lb k' ≠ none → look ra k' = none ∧ look rb k' = none := by
        intro c
        have g := B1 c
        exact ⟨eq_none_of (fun c' => (A2 c').2.1) (fun g2 => g.1 (gorF_antisymm mug g.2.1 g2)),
          eq_none_of (fun c' => (B2 c').2.1) (fun g2 => g.1 (gorF_antisymm mug g.2.1 g2))⟩
      clear A1 A2 B1 B2 G
      cases e1 : look la k' <;> cases e2 : look ra k' <;> cases e3 : look lb k' <;>
        cases e4 : look rb k' <;> simp_all [mergeO]
  · rw [uni_sz_pair, uni_sz_pair, uni_sz_pair]; omega

theorem look_pair_nil (k v l k' : Noun) :
    look (C (C k v) (C l (A 0))) k' = if k' = k then some v else look l k' := by
  rw [look_node, look_nil]; cases look l k' <;> rfl

theorem look_nil_pair (k v r k' : Noun) :
    look (C (C k v) (C (A 0) r)) k' = if k' = k then some v else look r k' := by
  rw [look_node, look_nil]; rfl

/-- Two keys in opposite `+gor` order are equal. -/
theorem gor_ne {mug : Noun → Nat} {x y : Noun} (h1 : gorF mug x y = true) (h2 : gorF mug y x = true)
    (hne : x ≠ y) : False := hne (gorF_antisymm mug h1 h2)

/-- The value at a key in the branch `mn`. -/
theorem look_mn (f : Noun → Noun → Noun → Noun) (k ka kb va vb : Noun) (la ra lb rb : Option Noun)
    (e : kb ≠ ka) (f1 : la ≠ none → ra = none) (f1' : la ≠ none → k ≠ kb) (f1'' : la ≠ none → rb = none)
    (f3 : lb ≠ none → rb = none) (f4 : rb ≠ none → k ≠ ka) (c1 : la ≠ none → k ≠ ka)
    (c2 : ra ≠ none → k ≠ ka) (c3 : lb ≠ none → k ≠ kb) (c4 : rb ≠ none → k ≠ kb) :
    mergeO f k (if k = ka then some va else la.or (mergeO f k ra (if k = kb then some vb else rb))) lb
      = mergeO f k (if k = ka then some va else la.or ra) (if k = kb then some vb else lb.or rb) := by
  by_cases ea : k = ka <;> by_cases eb : k = kb <;>
    cases la <;> cases ra <;> cases lb <;> cases rb <;> simp_all [mergeO]

/-- The value at a key in the branch `ng`. -/
theorem look_ng (f : Noun → Noun → Noun → Noun) (k ka kb va vb : Noun) (la ra lb rb : Option Noun)
    (e : kb ≠ ka) (f1 : la ≠ none → ra = none) (f1' : la ≠ none → k ≠ kb) (f1'' : la ≠ none → rb = none)
    (f3 : lb ≠ none → rb = none) (f4 : rb ≠ none → k ≠ ka) (c1 : la ≠ none → k ≠ ka)
    (c2 : ra ≠ none → k ≠ ka) (c3 : lb ≠ none → k ≠ kb) (c4 : rb ≠ none → k ≠ kb) :
    mergeO f k ra (if k = kb then some vb else (mergeO f k (if k = ka then some va else la) lb).or rb)
      = mergeO f k (if k = ka then some va else la.or ra) (if k = kb then some vb else lb.or rb) := by
  by_cases ea : k = ka <;> by_cases eb : k = kb <;>
    cases la <;> cases ra <;> cases lb <;> cases rb <;> simp_all [mergeO]

/-- The value at a key in the branch `nn`. -/
theorem look_nn (f : Noun → Noun → Noun → Noun) (k ka kb va vb : Noun) (la ra lb rb : Option Noun)
    (e : kb ≠ ka) (f1 : la ≠ none → ra = none) (f2 : ra ≠ none → k ≠ kb) (f2' : ra ≠ none → lb = none)
    (f3 : lb ≠ none → rb = none) (f5 : k = ka → lb = none) (c1 : la ≠ none → k ≠ ka)
    (c2 : ra ≠ none → k ≠ ka) (c3 : lb ≠ none → k ≠ kb) (c4 : rb ≠ none → k ≠ kb) :
    mergeO f k la (if k = kb then some vb else lb.or (mergeO f k (if k = ka then some va else ra) rb))
      = mergeO f k (if k = ka then some va else la.or ra) (if k = kb then some vb else lb.or rb) := by
  by_cases ea : k = ka <;> by_cases eb : k = kb <;>
    cases la <;> cases ra <;> cases lb <;> cases rb <;> simp_all [mergeO]

/-- The root of `a` comes first in `+mor` order among the keys of `b`. -/
theorem unoBy_domA {mug : Noun → Nat} {V : Noun → Prop} {f : Noun → Noun → Noun → Noun} {m : Nat}
    (hV : ∀ k va vb, V va → V vb → V (f k va vb))
    (ih : ∀ a b, uniSz a + uniSz b < m → IsMap mug a → IsMap mug b → VAll V a → VAll V b → UnoByP mug V f a b) :
    ∀ {b : Noun}, IsMap mug b → VAll V b → ∀ ka va la ra, IsMap mug (C (C ka va) (C la ra)) →
      VAll V (C (C ka va) (C la ra)) →
      (∀ k v, Get b k v → morF mug ka k = true) → uniSz (C (C ka va) (C la ra)) + uniSz b ≤ m →
      UnoByP mug V f (C (C ka va) (C la ra)) b := by
  intro b hb
  induction hb with
  | nil =>
    intro _ ka va la ra ha hva _ _
    exact ⟨_, UnoByR.nilB _, ha, hva, fun k => by rw [look_nil, mergeO_none_right], by rw [uni_sz_zero]; omega⟩
  | @node kb vb lb rb hlb hrb hLb hRb ihl ihr =>
    intro hvb ka va la ra ha hva hdom hsz
    have hb : IsMap mug (C (C kb vb) (C lb rb)) := IsMap.node hlb hrb hLb hRb
    by_cases e : kb = ka
    · subst e; exact unoBy_same hV ih ha hb hva hvb hsz
    have hmo : morF mug ka kb = true := hdom kb vb Get.here
    obtain ⟨hla, hra, hLa, hRa⟩ := IsMap_node ha
    obtain ⟨v1, vla, vra⟩ := vall_node hva
    obtain ⟨v2, vlb, vrb⟩ := vall_node hvb
    have hsz' := hsz
    rw [uni_sz_pair, uni_sz_pair] at hsz'
    by_cases g : gorF mug kb ka = true
    · have hsb : IsMap mug (C (C kb vb) (C lb (A 0))) :=
        IsMap.node hlb IsMap.nil hLb (fun k v h => absurd h Get_atom)
      obtain ⟨x, h1, hx, vx, hxk, hxs⟩ := ih la (C (C kb vb) (C lb (A 0)))
        (by rw [uni_sz_pair, uni_sz_zero]; omega) hla hsb vla (vall_mk v2 vlb vall_nil)
      rw [uni_sz_pair, uni_sz_zero] at hxs
      have hX : ∀ k v, Get x k v → k ≠ ka ∧ gorF mug k ka = true ∧ morF mug ka k = true := by
        intro k v hk
        rcases kin_of_merge hx hxk hk with h | h
        · exact ord_of_look hla hLa h
        · rw [look_pair_nil] at h
          by_cases ek : k = kb
          · subst ek; exact ⟨e, g, hmo⟩
          · rw [if_neg ek] at h
            have o := ord_of_look hlb hLb h
            have gk := gorF_trans mug o.2.1 g
            refine ⟨fun hk' => ?_, gk, ?_⟩
            · subst hk'; exact gor_ne g o.2.1 e
            · obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 h
              exact hdom k w (Get.left ((look_get hlb k w).1 hw))
      have hsa : IsMap mug (C (C ka va) (C x ra)) := IsMap.node hx hra hX hRa
      obtain ⟨out, h2, ho, vo, hok, hos⟩ := ihr vrb ka va x ra hsa (vall_mk v1 vx vra)
        (fun k v hk => hdom k v (Get.right hk)) (by rw [uni_sz_pair]; omega)
      rw [uni_sz_pair] at hos
      refine ⟨out, UnoByR.mg e hmo g h1 h2, ho, vo, fun k => ?_, by rw [uni_sz_pair, uni_sz_pair]; omega⟩
      rw [hok k, look_node, look_node, look_node, hxk k, look_pair_nil]
      have A1 := ord_of_look hla hLa (k := k)
      have A2 := ord_of_look' hra hRa (k := k)
      have B1 := ord_of_look hlb hLb (k := k)
      have B2 := ord_of_look' hrb hRb (k := k)
      have f1 : look la k ≠ none → look ra k = none :=
        fun c => eq_none_of (fun c' => (A2 c').2.1) (fun g2 => gor_ne (A1 c).2.1 g2 (A1 c).1)
      have f2 : look ra k ≠ none → look lb k = none :=
        fun c => eq_none_of (fun c' => (B1 c').2.1)
          (fun g2 => gor_ne g (gorF_trans mug (A2 c).2.1 g2) e)
      have f2' : look ra k ≠ none → k ≠ kb := by
        intro c hk; subst hk; exact gor_ne g (A2 c).2.1 e
      have f3 : look lb k ≠ none → look rb k = none :=
        fun c => eq_none_of (fun c' => (B2 c').2.1) (fun g2 => gor_ne (B1 c).2.1 g2 (B1 c).1)
      have f5 : k = ka → look lb k = none := by
        intro hk; subst hk
        exact eq_none_of (fun c' => (B1 c').2.1) (fun g2 => gor_ne g g2 e)
      have c1 : look la k ≠ none → k ≠ ka := fun c => (A1 c).1
      have c2 : look ra k ≠ none → k ≠ ka := fun c => (A2 c).1
      have c3 : look lb k ≠ none → k ≠ kb := fun c => (B1 c).1
      have c4 : look rb k ≠ none → k ≠ kb := fun c => (B2 c).1
      clear A1 A2 B1 B2 hok hxk hX hsa h1 h2 ih ihl ihr hdom
      by_cases ea : k = ka <;> by_cases eb : k = kb <;>
        cases e1 : look la k <;> cases e2 : look ra k <;> cases e3 : look lb k <;>
        cases e4 : look rb k <;> simp_all [mergeO]
    · have g' : gorF mug ka kb = true := gorF_of_not mug g
      have gf : gorF mug kb ka = false := by simpa using g
      have hsb : IsMap mug (C (C kb vb) (C (A 0) rb)) :=
        IsMap.node IsMap.nil hrb (fun k v h => absurd h Get_atom) hRb
      obtain ⟨x, h1, hx, vx, hxk, hxs⟩ := ih ra (C (C kb vb) (C (A 0) rb))
        (by rw [uni_sz_pair, uni_sz_zero]; omega) hra hsb vra (vall_mk v2 vall_nil vrb)
      rw [uni_sz_pair, uni_sz_zero] at hxs
      have hX : ∀ k v, Get x k v → k ≠ ka ∧ gorF mug ka k = true ∧ morF mug ka k = true := by
        intro k v hk
        rcases kin_of_merge hx hxk hk with h | h
        · exact ord_of_look' hra hRa h
        · rw [look_nil_pair] at h
          by_cases ek : k = kb
          · subst ek; exact ⟨e, g', hmo⟩
          · rw [if_neg ek] at h
            have o := ord_of_look' hrb hRb h
            have gk := gorF_trans mug g' o.2.1
            refine ⟨fun hk' => ?_, gk, ?_⟩
            · subst hk'; exact gor_ne o.2.1 g' e
            · obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 h
              exact hdom k w (Get.right ((look_get hrb k w).1 hw))
      have hsa : IsMap mug (C (C ka va) (C la x)) := IsMap.node hla hx hLa hX
      obtain ⟨out, h2, ho, vo, hok, hos⟩ := ihl vlb ka va la x hsa (vall_mk v1 vla vx)
        (fun k v hk => hdom k v (Get.left hk)) (by rw [uni_sz_pair]; omega)
      rw [uni_sz_pair] at hos
      refine ⟨out, UnoByR.mn e hmo gf h1 h2, ho, vo, fun k => ?_, by rw [uni_sz_pair, uni_sz_pair]; omega⟩
      rw [hok k, look_node, look_node, look_node, hxk k, look_nil_pair]
      have A1 := ord_of_look hla hLa (k := k)
      have A2 := ord_of_look' hra hRa (k := k)
      have B1 := ord_of_look hlb hLb (k := k)
      have B2 := ord_of_look' hrb hRb (k := k)
      have f1 : look la k ≠ none → look ra k = none :=
        fun c => eq_none_of (fun c' => (A2 c').2.1) (fun g2 => gor_ne (A1 c).2.1 g2 (A1 c).1)
      have f1' : look la k ≠ none → k ≠ kb := by
        intro c hk; subst hk; exact gor_ne g' (A1 c).2.1 (fun h => e h.symm)
      have f1'' : look la k ≠ none → look rb k = none :=
        fun c => eq_none_of (fun c' => (B2 c').2.1)
          (fun g2 => gor_ne (gorF_trans mug (A1 c).2.1 g') g2 (f1' c))
      have f3 : look lb k ≠ none → look rb k = none :=
        fun c => eq_none_of (fun c' => (B2 c').2.1) (fun g2 => gor_ne (B1 c).2.1 g2 (B1 c).1)
      have f4 : look rb k ≠ none → k ≠ ka := by
        intro c hk; subst hk; exact gor_ne g' (B2 c).2.1 (fun h => e h.symm)
      exact look_mn f k ka kb va vb _ _ _ _ e f1 f1' f1'' f3 f4 (fun c => (A1 c).1) (fun c => (A2 c).1)
        (fun c => (B1 c).1) (fun c => (B2 c).1)

/-- The root of `b` comes first in `+mor` order among the keys of `a`. -/
theorem unoBy_domB {mug : Noun → Nat} {V : Noun → Prop} {f : Noun → Noun → Noun → Noun} {m : Nat}
    (hV : ∀ k va vb, V va → V vb → V (f k va vb))
    (ih : ∀ a b, uniSz a + uniSz b < m → IsMap mug a → IsMap mug b → VAll V a → VAll V b → UnoByP mug V f a b) :
    ∀ {a : Noun}, IsMap mug a → VAll V a → ∀ kb vb lb rb, IsMap mug (C (C kb vb) (C lb rb)) →
      VAll V (C (C kb vb) (C lb rb)) →
      (∀ k v, Get a k v → morF mug kb k = true) → uniSz a + uniSz (C (C kb vb) (C lb rb)) ≤ m →
      UnoByP mug V f a (C (C kb vb) (C lb rb)) := by
  intro a ha
  induction ha with
  | nil =>
    intro _ kb vb lb rb hb hvb _ _
    exact ⟨_, UnoByR.nilA _ (by simp), hb, hvb, fun k => by rw [look_nil, mergeO_none_left],
      by rw [uni_sz_zero]; omega⟩
  | @node ka va la ra hla hra hLa hRa ihl ihr =>
    intro hva kb vb lb rb hb hvb hdom hsz
    have ha : IsMap mug (C (C ka va) (C la ra)) := IsMap.node hla hra hLa hRa
    by_cases e : kb = ka
    · subst e; exact unoBy_same hV ih ha hb hva hvb hsz
    have e' : ka ≠ kb := fun h => e h.symm
    have hmo : morF mug kb ka = true := hdom ka va Get.here
    have hmf : morF mug ka kb = false := by
      cases h : morF mug ka kb
      · rfl
      · exact absurd (morF_antisymm mug hmo h) e
    obtain ⟨hlb, hrb, hLb, hRb⟩ := IsMap_node hb
    obtain ⟨v1, vla, vra⟩ := vall_node hva
    obtain ⟨v2, vlb, vrb⟩ := vall_node hvb
    have hsz' := hsz
    rw [uni_sz_pair, uni_sz_pair] at hsz'
    by_cases g : gorF mug ka kb = true
    · have hsa : IsMap mug (C (C ka va) (C la (A 0))) :=
        IsMap.node hla IsMap.nil hLa (fun k v h => absurd h Get_atom)
      obtain ⟨x, h1, hx, vx, hxk, hxs⟩ := ih (C (C ka va) (C la (A 0))) lb
        (by rw [uni_sz_pair, uni_sz_zero]; omega) hsa hlb (vall_mk v1 vla vall_nil) vlb
      rw [uni_sz_pair, uni_sz_zero] at hxs
      have hX : ∀ k v, Get x k v → k ≠ kb ∧ gorF mug k kb = true ∧ morF mug kb k = true := by
        intro k v hk
        rcases kin_of_merge hx hxk hk with h | h
        · rw [look_pair_nil] at h
          by_cases ek : k = ka
          · subst ek; exact ⟨e', g, hmo⟩
          · rw [if_neg ek] at h
            have o := ord_of_look hla hLa h
            have gk := gorF_trans mug o.2.1 g
            refine ⟨fun hk' => ?_, gk, ?_⟩
            · subst hk'; exact gor_ne g o.2.1 e'
            · obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 h
              exact hdom k w (Get.left ((look_get hla k w).1 hw))
        · exact ord_of_look hlb hLb h
      have hsb : IsMap mug (C (C kb vb) (C x rb)) := IsMap.node hx hrb hX hRb
      obtain ⟨out, h2, ho, vo, hok, hos⟩ := ihr vra kb vb x rb hsb (vall_mk v2 vx vrb)
        (fun k v hk => hdom k v (Get.right hk)) (by rw [uni_sz_pair]; omega)
      rw [uni_sz_pair] at hos
      refine ⟨out, UnoByR.ng e hmf g h1 h2, ho, vo, fun k => ?_, by rw [uni_sz_pair, uni_sz_pair]; omega⟩
      rw [hok k, look_node, look_node, look_node, hxk k, look_pair_nil]
      have A1 := ord_of_look hla hLa (k := k)
      have A2 := ord_of_look' hra hRa (k := k)
      have B1 := ord_of_look hlb hLb (k := k)
      have B2 := ord_of_look' hrb hRb (k := k)
      have f1 : look la k ≠ none → look ra k = none :=
        fun c => eq_none_of (fun c' => (A2 c').2.1) (fun g2 => gor_ne (A1 c).2.1 g2 (A1 c).1)
      have f1' : look la k ≠ none → k ≠ kb := by
        intro c hk; subst hk; exact gor_ne g (A1 c).2.1 e'
      have f1'' : look la k ≠ none → look rb k = none :=
        fun c => eq_none_of (fun c' => (B2 c').2.1)
          (fun g2 => gor_ne (gorF_trans mug (A1 c).2.1 g) g2 (f1' c))
      have f3 : look lb k ≠ none → look rb k = none :=
        fun c => eq_none_of (fun c' => (B2 c').2.1) (fun g2 => gor_ne (B1 c).2.1 g2 (B1 c).1)
      have f4 : look rb k ≠ none → k ≠ ka := by
        intro c hk; subst hk; exact gor_ne g (B2 c).2.1 e'
      exact look_ng f k ka kb va vb _ _ _ _ e f1 f1' f1'' f3 f4 (fun c => (A1 c).1) (fun c => (A2 c).1)
        (fun c => (B1 c).1) (fun c => (B2 c).1)
    · have g' : gorF mug kb ka = true := gorF_of_not mug g
      have gf : gorF mug ka kb = false := by simpa using g
      have hsa : IsMap mug (C (C ka va) (C (A 0) ra)) :=
        IsMap.node IsMap.nil hra (fun k v h => absurd h Get_atom) hRa
      obtain ⟨x, h1, hx, vx, hxk, hxs⟩ := ih (C (C ka va) (C (A 0) ra)) rb
        (by rw [uni_sz_pair, uni_sz_zero]; omega) hsa hrb (vall_mk v1 vall_nil vra) vrb
      rw [uni_sz_pair, uni_sz_zero] at hxs
      have hX : ∀ k v, Get x k v → k ≠ kb ∧ gorF mug kb k = true ∧ morF mug kb k = true := by
        intro k v hk
        rcases kin_of_merge hx hxk hk with h | h
        · rw [look_nil_pair] at h
          by_cases ek : k = ka
          · subst ek; exact ⟨e', g', hmo⟩
          · rw [if_neg ek] at h
            have o := ord_of_look' hra hRa h
            have gk := gorF_trans mug g' o.2.1
            refine ⟨fun hk' => ?_, gk, ?_⟩
            · subst hk'; exact gor_ne o.2.1 g' (fun h => e h.symm)
            · obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 h
              exact hdom k w (Get.right ((look_get hra k w).1 hw))
        · exact ord_of_look' hrb hRb h
      have hsb : IsMap mug (C (C kb vb) (C lb x)) := IsMap.node hlb hx hLb hX
      obtain ⟨out, h2, ho, vo, hok, hos⟩ := ihl vla kb vb lb x hsb (vall_mk v2 vlb vx)
        (fun k v hk => hdom k v (Get.left hk)) (by rw [uni_sz_pair]; omega)
      rw [uni_sz_pair] at hos
      refine ⟨out, UnoByR.nn e hmf gf h1 h2, ho, vo, fun k => ?_, by rw [uni_sz_pair, uni_sz_pair]; omega⟩
      rw [hok k, look_node, look_node, look_node, hxk k, look_nil_pair]
      have A1 := ord_of_look hla hLa (k := k)
      have A2 := ord_of_look' hra hRa (k := k)
      have B1 := ord_of_look hlb hLb (k := k)
      have B2 := ord_of_look' hrb hRb (k := k)
      have f1 : look la k ≠ none → look ra k = none :=
        fun c => eq_none_of (fun c' => (A2 c').2.1) (fun g2 => gor_ne (A1 c).2.1 g2 (A1 c).1)
      have f2 : look ra k ≠ none → k ≠ kb := by
        intro c hk; subst hk; exact gor_ne g' (A2 c).2.1 e
      have f2' : look ra k ≠ none → look lb k = none :=
        fun c => eq_none_of (fun c' => (B1 c').2.1)
          (fun g2 => gor_ne g' (gorF_trans mug (A2 c).2.1 g2) e)
      have f3 : look lb k ≠ none → look rb k = none :=
        fun c => eq_none_of (fun c' => (B2 c').2.1) (fun g2 => gor_ne (B1 c).2.1 g2 (B1 c).1)
      have f5 : k = ka → look lb k = none := by
        intro hk; subst hk
        exact eq_none_of (fun c' => (B1 c').2.1) (fun g2 => gor_ne g' g2 e)
      exact look_nn f k ka kb va vb _ _ _ _ e f1 f2 f2' f3 f5 (fun c => (A1 c).1) (fun c => (A2 c).1)
        (fun c => (B1 c).1) (fun c => (B2 c).1)

/-- One level of the induction on the number of nodes. -/
theorem unoBy_step {mug : Noun → Nat} {V : Noun → Prop} {f : Noun → Noun → Noun → Noun} {m : Nat}
    (hV : ∀ k va vb, V va → V vb → V (f k va vb))
    (ih : ∀ a b, uniSz a + uniSz b < m → IsMap mug a → IsMap mug b → VAll V a → VAll V b → UnoByP mug V f a b)
    (a b : Noun) (hs : uniSz a + uniSz b ≤ m) (ha : IsMap mug a) (hb : IsMap mug b) (hva : VAll V a)
    (hvb : VAll V b) : UnoByP mug V f a b := by
  cases hb with
  | nil =>
    exact ⟨a, UnoByR.nilB a, ha, hva, fun k => by rw [look_nil, mergeO_none_right], by rw [uni_sz_zero]; omega⟩
  | @node kb vb lb rb hlb hrb hLb hRb =>
    have hb : IsMap mug (C (C kb vb) (C lb rb)) := IsMap.node hlb hrb hLb hRb
    cases ha with
    | nil => exact unoBy_domB hV ih IsMap.nil hva kb vb lb rb hb hvb (fun k v h => absurd h Get_atom) hs
    | @node ka va la ra hla hra hLa hRa =>
      have ha : IsMap mug (C (C ka va) (C la ra)) := IsMap.node hla hra hLa hRa
      by_cases mo : morF mug ka kb = true
      · refine unoBy_domA hV ih hb hvb ka va la ra ha hva (fun k v hk => ?_) hs
        rcases Get_node.1 hk with ⟨rfl, _⟩ | h | h
        · exact mo
        · exact morF_trans mug mo (hLb k v h).2.2
        · exact morF_trans mug mo (hRb k v h).2.2
      · have mo' := morF_of_not mug mo
        refine unoBy_domB hV ih ha hva kb vb lb rb hb hvb (fun k v hk => ?_) hs
        rcases Get_node.1 hk with ⟨rfl, _⟩ | h | h
        · exact mo'
        · exact morF_trans mug mo' (hLa k v h).2.2
        · exact morF_trans mug mo' (hRa k v h).2.2

theorem unoByP_of_maps {mug : Noun → Nat} {V : Noun → Prop} {f : Noun → Noun → Noun → Noun}
    (hV : ∀ k va vb, V va → V vb → V (f k va vb)) : ∀ (m : Nat) (a b : Noun), uniSz a + uniSz b ≤ m →
    IsMap mug a → IsMap mug b → VAll V a → VAll V b → UnoByP mug V f a b := by
  intro m
  induction m with
  | zero => exact unoBy_step hV (fun a b h => absurd h (Nat.not_lt_zero _))
  | succ m ih => exact unoBy_step hV (fun a b h ha hb hva hvb => ih a b (by omega) ha hb hva hvb)

/-- **`+uno:by` on two maps**, the gate `|*  meg` slammed on a gate that
gives `f k va vb` on values with `V`, `f` keeping `V`: a map whose values
have `V`, with the value `mergeO f k` of those of `a` and `b` at each key. -/
theorem uno_by {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx)
    (V : Noun → Prop) (f : Noun → Noun → Noun → Noun) (MB MS MC : Noun)
    (hf : ∀ k va vb, V va → V vb → nock (C MB (C (C k (C va vb)) MC)) MB = some (f k va vb))
    (hV : ∀ k va vb, V va → V vb → V (f k va vb)) (a b : Noun) (ha : IsMap mug a) (hb : IsMap mug b)
    (hva : VAll V a) (hvb : VAll V b) :
    ∃ out, nock (C unoMegGate (C (C MB (C MS MC)) (C unoOuter (C b (C by.battery (C a ctx)))))) unoMegGate
        = some out ∧ IsMap mug out ∧ VAll V out ∧ ∀ k, look out k = mergeO f k (look a k) (look b k) := by
  obtain ⟨out, h, hm, hv, hk, _⟩ := unoByP_of_maps hV _ a b (Nat.le_refl _) ha hb hva hvb
  exact ⟨out, uno_gate ctx hc V f MB MS MC hf h, hm, hv, hk⟩

end Hoon
end Formalization

end
