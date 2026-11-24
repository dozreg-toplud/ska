module

public import lemmas.Hoon.UniIn
public import lemmas.Hoon.RepBy
import lemmas.Pill.Facts
import all lemmas.Pill.Arm.In
import all lemmas.Pill.Arm.By

/-!
`+int:in` of the pill's `hoon.hoon` on an empty door set, and `+rep` over a
treap of one node.

```hoon
++  int                                               ::  intersection
  ~/  %int
  |*  b=_a
  |-  ^+  a
  ?~  b
    ~
  ?~  a
    ~
  ?.  (mor n.a n.b)
    $(a b, b a)
  ?:  =(n.b n.a)
    a(l $(a l.a, b l.b), r $(a r.a, b r.b))
  ?:  (gor n.b n.a)
    %-  uni(a $(a l.a, r.b ~))  $(b r.b)
  %-  uni(a $(a r.a, l.b ~))  $(b l.b)
```

`int_in_nil`: with the door's set `a` empty the gate returns `~` whatever
`b` is (by its first test when `b` is `~`, by its second otherwise).

The whole loop: the relation `IntR`, one constructor per branch, where the
two last branches unite the products of two inner calls with `+uni:in`
(`UniR` of `UniIn.lean`, and the gate's first test `=(a b)`); `int_loop`
runs the Nock on every derivation.  `intP_of_sets` builds a derivation on
two sets by induction on the number of nodes (the swap `$(a b, b a)` keeps
the number and leads to a branch where `n.a` comes first in `+mor`), to a
set whose members are those of both (`int_in`).

`rep_gate_one`: `+rep` over `[x ~ ~]` is the gate on `x` and the first
accumulator, whatever the gate (as `roll_gate_one` for `+roll`).
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

/-- The arm `int` of a door `+in` builds its gate, whose sample bunt is the
door's set. -/
theorem int_in_arm (a ctx : Noun) :
    nock (C in.battery (C a ctx)) in.int.arm = some (C in.int.battery (C a (C in.battery (C a ctx)))) := by
  nock_open in.int.arm
  simp [nock_exec]

theorem int_loop_nil (B ctx : Noun) :
    nock (C in.int.loop (C in.int.battery (C B (C in.battery (C (A 0) ctx))))) in.int.loop = some (A 0) := by
  nock_open in.int.loop
  by_cases h : B = A 0
  · subst h; simp [nock_exec]
  · simp [nock_exec, eqCode, Ne.symm h]

/-- **`+int:in` with the door's set empty** is `~`. -/
theorem int_in_nil (B ctx : Noun) :
    nock (C in.int.battery (C B (C in.battery (C (A 0) ctx)))) in.int.battery = some (A 0) := by
  nock_open in.int.battery
  simp only [nock_exec, int_loop_nil]

theorem rep_loop_nil (B ctx bp e bc acc : Noun) :
    nock (C by.rep.loop (C by.rep.battery (C (C bp (C (C e acc) bc)) (C B (C (A 0) ctx))))) by.rep.loop
      = some acc := by
  nock_open by.rep.loop
  simp [nock_exec]

/-- **`+rep` over a treap of one node** is the gate on that node and the
first accumulator, whatever the gate. -/
theorem rep_gate_one (B ctx bp e acc bc x : Noun) :
    nock (C by.rep.battery (C (C bp (C (C e acc) bc)) (C B (C (C x (C (A 0) (A 0))) ctx)))) by.rep.battery
      = nock (C bp (C (C x acc) bc)) bp := by
  nock_open by.rep.battery
  simp only [nock_exec]
  nock_open by.rep.loop
  cases e1 : nock (C bp (C (C x acc) bc)) bp with
  | none => simp [nock_exec, e1]
  | some r => simp [nock_exec, e1, rep_loop_nil]

/-! ## The whole loop -/

/-- The loop of `+int:in`, one constructor per branch. -/
inductive IntR (mug : Noun → Nat) : Noun → Noun → Noun → Prop where
  | nilB (a : Noun) : IntR mug a (A 0) (A 0)
  | nilA (b : Noun) : b ≠ A 0 → IntR mug (A 0) b (A 0)
  | swap {na la ra nb lb rb out : Noun} : morF mug na nb = false →
      IntR mug (C nb (C lb rb)) (C na (C la ra)) out → IntR mug (C na (C la ra)) (C nb (C lb rb)) out
  | same {n la ra lb rb l r : Noun} : IntR mug la lb l → IntR mug ra rb r →
      IntR mug (C n (C la ra)) (C n (C lb rb)) (C n (C l r))
  | lt {na la ra nb lb rb x y u : Noun} : nb ≠ na → morF mug na nb = true → gorF mug nb na = true →
      IntR mug la (C nb (C lb (A 0))) x → IntR mug (C na (C la ra)) rb y → UniR mug x y u →
      IntR mug (C na (C la ra)) (C nb (C lb rb)) (if x = y then x else u)
  | gt {na la ra nb lb rb x y u : Noun} : nb ≠ na → morF mug na nb = true → gorF mug nb na = false →
      IntR mug ra (C nb (C (A 0) rb)) x → IntR mug (C na (C la ra)) lb y → UniR mug x y u →
      IntR mug (C na (C la ra)) (C nb (C lb rb)) (if x = y then x else u)

theorem uni_in_arm (a ctx : Noun) :
    nock (C in.battery (C a ctx)) in.uni.arm = some (C in.uni.battery (C a (C in.battery (C a ctx)))) := by
  nock_open in.uni.arm
  simp [nock_exec]

theorem int_loop {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx) :
    ∀ {a b out : Noun}, IntR mug a b out →
      nock (C in.int.loop (C in.int.battery (C b (C in.battery (C a ctx))))) in.int.loop = some out := by
  have hgor := gor_gate (mug := mug) ctx hc.1.2
  have hmor := mor_gate (mug := mug) ctx hc.2.2
  have hg := hc.1.1
  have hm := hc.2.1
  intro a b out h
  induction h with
  | nilB a =>
    nock_open in.int.loop
    simp [nock_exec]
  | nilA b hb =>
    nock_open in.int.loop
    simp [nock_exec, eqCode, Ne.symm hb]
  | swap m _ ih =>
    nock_open in.int.loop
    simp [nock_exec, m, hm, hmor, ih]
  | @same n la ra lb rb l r _ _ ih1 ih2 =>
    nock_open in.int.loop
    simp [nock_exec, hm, hmor, morF_refl, ih1, ih2]
  | lt e m g _ _ hu ih1 ih2 =>
    have hun := uni_in_gate ctx hc hu
    nock_open in.int.loop
    simp [nock_exec, e, m, g, hg, hm, hgor, hmor, ih1, ih2, in.uni.arm_at, uni_in_arm, hun]
  | gt e m g _ _ hu ih1 ih2 =>
    have hun := uni_in_gate ctx hc hu
    nock_open in.int.loop
    simp [nock_exec, e, m, g, hg, hm, hgor, hmor, ih1, ih2, in.uni.arm_at, uni_in_arm, hun]

/-- The gate `int` of the door `in` with set `a`, slammed on `b`. -/
theorem int_in_gate {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx)
    {a b out : Noun} (h : IntR mug a b out) :
    nock (C in.int.battery (C b (C in.battery (C a ctx)))) in.int.battery = some out := by
  nock_open in.int.battery
  simp only [nock_exec, int_loop ctx hc h]

/-! ## On sets -/

/-- What the loop gives on `a` and `b`: a derivation to a set with the
members of both. -/
def IntP (mug : Noun → Nat) (a b : Noun) : Prop :=
  ∃ out, IntR mug a b out ∧ IsSet mug out ∧ ∀ k, Has out k ↔ Has a k ∧ Has b k

/-- The union of the last two branches: a set with the members of both. -/
theorem int_uni {mug : Noun → Nat} {x y : Noun} (hx : IsSet mug x) (hy : IsSet mug y) :
    ∃ u, UniR mug x y u ∧ IsSet mug (if x = y then x else u) ∧
      ∀ k, Has (if x = y then x else u) k ↔ Has x k ∨ Has y k := by
  obtain ⟨u, hu, hs, hk, _⟩ := uniP_of_sets _ x y (Nat.le_refl _) hx hy
  refine ⟨u, hu, ?_, fun k => ?_⟩
  · split
    · exact hx
    · exact hs
  · split
    · rename_i e; subst e; exact ⟨Or.inl, fun h => h.elim id id⟩
    · exact hk k

/-- The branches where `n.a` comes first in `+mor`, from `IntP` on fewer
nodes. -/
theorem intP_mor {mug : Noun → Nat} {m : Nat}
    (ih : ∀ a b, uniSz a + uniSz b < m → IsSet mug a → IsSet mug b → IntP mug a b)
    {na la ra nb lb rb : Noun} (ha : IsSet mug (C na (C la ra))) (hb : IsSet mug (C nb (C lb rb)))
    (mo : morF mug na nb = true) (hs : uniSz (C na (C la ra)) + uniSz (C nb (C lb rb)) ≤ m) :
    IntP mug (C na (C la ra)) (C nb (C lb rb)) := by
  obtain ⟨hla, hra, hLa, hRa⟩ := isSet_node_iff.1 ha
  obtain ⟨hlb, hrb, hLb, hRb⟩ := isSet_node_iff.1 hb
  have hs' := hs
  rw [uni_sz_node, uni_sz_node] at hs'
  by_cases e : nb = na
  · subst e
    obtain ⟨l, h1, hl, hlk⟩ := ih la lb (by omega) hla hlb
    obtain ⟨r, h2, hr, hrk⟩ := ih ra rb (by omega) hra hrb
    refine ⟨C nb (C l r), IntR.same h1 h2, isSet_node_iff.2 ⟨hl, hr, fun k hk => hLa k ((hlk k).1 hk).1,
      fun k hk => hRa k ((hrk k).1 hk).1⟩, fun k => ?_⟩
    have c1 : ∀ k, Has la k → ¬ Has rb k := fun k h1 h2 =>
      (hLa k h1).1 (gorF_antisymm mug (hLa k h1).2.1 (hRb k h2).2.1)
    have c2 : ∀ k, Has ra k → ¬ Has lb k := fun k h1 h2 =>
      (hLb k h2).1 (gorF_antisymm mug (hLb k h2).2.1 (hRa k h1).2.1)
    have d1 := fun h => (hLa k h).1
    have d2 := fun h => (hRa k h).1
    have d3 := fun h => (hLb k h).1
    have d4 := fun h => (hRb k h).1
    have e1 := c1 k
    have e2 := c2 k
    rw [has_node, has_node, has_node, hlk, hrk]
    clear ih hs hs' h1 h2 hl hr hlk hrk hla hra hlb hrb hLa hRa hLb hRb ha hb c1 c2
    grind
  · by_cases g : gorF mug nb na = true
    · have hsb : IsSet mug (C nb (C lb (A 0))) :=
        isSet_node_iff.2 ⟨hlb, isSet_nil, hLb, fun k hk => absurd hk not_has_atom⟩
      obtain ⟨x, h1, hx, hxk⟩ := ih la (C nb (C lb (A 0))) (by rw [uni_sz_node, uni_sz_nil]; omega) hla hsb
      obtain ⟨y, h2, hy, hyk⟩ := ih (C na (C la ra)) rb (by rw [uni_sz_node]; omega) ha hrb
      obtain ⟨u, hu, ho, hok⟩ := int_uni hx hy
      refine ⟨_, IntR.lt e mo g h1 h2 hu, ho, fun k => ?_⟩
      -- the members of `b` below `n.b` and `n.b` are in `l.a` when in `a`
      have f1 : Has (C na (C la ra)) k → (k = nb ∨ Has lb k) → Has la k := by
        intro hk hk2
        have gk : gorF mug k na = true ∧ k ≠ na := by
          rcases hk2 with rfl | h
          · exact ⟨g, e⟩
          · refine ⟨gorF_trans mug (hLb k h).2.1 g, fun hk' => ?_⟩
            subst hk'; exact e (gorF_antisymm mug g (hLb _ h).2.1)
        rcases has_node.1 hk with h | h | h
        · exact absurd h gk.2
        · exact h
        · exact absurd (gorF_antisymm mug gk.1 (hRa k h).2.1) gk.2
      have f2 : Has la k → Has (C na (C la ra)) k := fun h => has_node.2 (Or.inr (Or.inl h))
      rw [hok, hxk, hyk]
      simp only [has_node, not_has_atom, or_false] at f1 f2 ⊢
      clear ih hs hs' h1 h2 hx hy hxk hyk hu ho hok hla hra hlb hrb hLa hRa hLb hRb ha hb hsb
      grind
    · have g' : gorF mug na nb = true := gorF_of_not mug g
      have gf : gorF mug nb na = false := by simpa using g
      have hsb : IsSet mug (C nb (C (A 0) rb)) :=
        isSet_node_iff.2 ⟨isSet_nil, hrb, fun k hk => absurd hk not_has_atom, hRb⟩
      obtain ⟨x, h1, hx, hxk⟩ := ih ra (C nb (C (A 0) rb)) (by rw [uni_sz_node, uni_sz_nil]; omega) hra hsb
      obtain ⟨y, h2, hy, hyk⟩ := ih (C na (C la ra)) lb (by rw [uni_sz_node]; omega) ha hlb
      obtain ⟨u, hu, ho, hok⟩ := int_uni hx hy
      refine ⟨_, IntR.gt e mo gf h1 h2 hu, ho, fun k => ?_⟩
      have f1 : Has (C na (C la ra)) k → (k = nb ∨ Has rb k) → Has ra k := by
        intro hk hk2
        have gk : gorF mug na k = true ∧ k ≠ na := by
          rcases hk2 with rfl | h
          · exact ⟨g', e⟩
          · refine ⟨gorF_trans mug g' (hRb k h).2.1, fun hk' => ?_⟩
            subst hk'; exact e (gorF_antisymm mug (hRb _ h).2.1 g')
        rcases has_node.1 hk with h | h | h
        · exact absurd h gk.2
        · exact absurd (gorF_antisymm mug (hLa k h).2.1 gk.1) gk.2
        · exact h
      have f2 : Has ra k → Has (C na (C la ra)) k := fun h => has_node.2 (Or.inr (Or.inr h))
      rw [hok, hxk, hyk]
      simp only [has_node, not_has_atom, false_or] at f1 f2 ⊢
      clear ih hs hs' h1 h2 hx hy hxk hyk hu ho hok hla hra hlb hrb hLa hRa hLb hRb ha hb hsb
      grind

/-- One level of the induction on the number of nodes. -/
theorem intP_step {mug : Noun → Nat} {m : Nat}
    (ih : ∀ a b, uniSz a + uniSz b < m → IsSet mug a → IsSet mug b → IntP mug a b)
    (a b : Noun) (hs : uniSz a + uniSz b ≤ m) (ha : IsSet mug a) (hb : IsSet mug b) : IntP mug a b := by
  have ta := Tree.of_isSet ha
  have tb := Tree.of_isSet hb
  cases tb with
  | nil => exact ⟨A 0, IntR.nilB a, isSet_nil, fun k => ⟨fun h => absurd h not_has_atom, fun h => absurd h.2 not_has_atom⟩⟩
  | @node nb lb rb _ _ =>
    cases ta with
    | nil => exact ⟨A 0, IntR.nilA _ (by simp), isSet_nil,
        fun k => ⟨fun h => absurd h not_has_atom, fun h => absurd h.1 not_has_atom⟩⟩
    | @node na la ra _ _ =>
      by_cases mo : morF mug na nb = true
      · exact intP_mor ih ha hb mo hs
      · have mo' := morF_of_not mug mo
        have mf : morF mug na nb = false := by simpa using mo
        obtain ⟨out, h, ho, hk⟩ := intP_mor ih hb ha mo' (by omega)
        exact ⟨out, IntR.swap mf h, ho, fun k => by rw [hk k]; exact And.comm⟩

theorem intP_of_sets {mug : Noun → Nat} : ∀ (m : Nat) (a b : Noun), uniSz a + uniSz b ≤ m →
    IsSet mug a → IsSet mug b → IntP mug a b := by
  intro m
  induction m with
  | zero => exact intP_step (fun a b h => absurd h (Nat.not_lt_zero _))
  | succ m ih => exact intP_step (fun a b h ha hb => ih a b (by omega) ha hb)

/-- **`+int:in` on two sets**, in a context with `+gor` and `+mor`: a set
holding the members of both. -/
theorem int_in {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx) (a b : Noun)
    (ha : IsSet mug a) (hb : IsSet mug b) :
    ∃ out, nock (C in.int.battery (C b (C in.battery (C a ctx)))) in.int.battery = some out ∧
      IsSet mug out ∧ ∀ k, Has out k ↔ Has a k ∧ Has b k := by
  obtain ⟨out, h, hs, hk⟩ := intP_of_sets _ a b (Nat.le_refl _) ha hb
  exact ⟨out, int_in_gate ctx hc h, hs, hk⟩

end Hoon
end Formalization

end
