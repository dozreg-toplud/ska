import lemmas.Compiler.OptLinkAlJInfo

/-!
# `+alias`: `join-imms` (phase 5 of the plan, README Gaps 13)

```hoon
  ++  join-imms
    |=  [a=(jug * @uvre) b=(jug * @uvre)]
    ^-  (jug * @uvre)
    |-  ^-  (jug * @uvre)
    ?~  b  ~
    ?~  a  ~
    ?:  =(a b)  a
    ?:  (mor p.n.a p.n.b)
      ?:  =(p.n.b p.n.a)
        =/  v  (~(int in q.n.a) q.n.b)
        =/  l  $(a l.a, b l.b)
        =/  r  $(a r.a, b r.b)
        ?:  =(~ v)  (~(uni by l) r)
        [[p.n.b v] l r]
      ?:  (gor p.n.b p.n.a)
        (~(uni by $(a l.a, r.b ~)) $(b r.b))
      (~(uni by $(a r.a, l.b ~)) $(b l.b))
    ?:  (gor p.n.a p.n.b)
      (~(uni by $(b l.b, r.a ~)) $(a r.a))
    (~(uni by $(b r.b, l.a ~)) $(a l.a))
```

* `JMR a b out`: the loop (the trap `alJMTrap`), one constructor per branch
  as `JIR` of `OptLinkAlJInfo.lean`, the root of equal keys split in two:
  `same` (the intersection `v` of the two sets, by `IntR`, not empty) and
  `same0` (empty, the key dropped: `+uni:by` of the two halves).
  `jm_loop` runs the Nock on every derivation.
* `jmP_of_maps`: on two maps whose values are sets that are not empty
  (`SetVals`), a derivation to such a map holding a key of both exactly
  where the two sets meet, its value their intersection.
* `al_jimms`: **`join-imms` of two related jugs is related to
  `joinImmsA`** (`ImmsRel`: each value a set with the members of the list
  at its key, an empty list absent).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The loop of `join-imms`, one constructor per branch. -/
inductive JMR : Noun → Noun → Noun → Prop where
  | nilB (a : Noun) : JMR a (A 0) (A 0)
  | nilA (b : Noun) : b ≠ A 0 → JMR (A 0) b (A 0)
  | eq {a : Noun} : a ≠ A 0 → JMR a a a
  | same {k va la ra vb lb rb v l r : Noun} : C (C k va) (C la ra) ≠ C (C k vb) (C lb rb) →
      IntR mugF va vb v → v ≠ A 0 → JMR la lb l → JMR ra rb r →
      JMR (C (C k va) (C la ra)) (C (C k vb) (C lb rb)) (C (C k v) (C l r))
  | same0 {k va la ra vb lb rb l r u : Noun} : C (C k va) (C la ra) ≠ C (C k vb) (C lb rb) →
      IntR mugF va vb (A 0) → JMR la lb l → JMR ra rb r → UniByR mugF l r u →
      JMR (C (C k va) (C la ra)) (C (C k vb) (C lb rb)) u
  | mg {ka va la ra kb vb lb rb x y u : Noun} : C (C ka va) (C la ra) ≠ C (C kb vb) (C lb rb) →
      kb ≠ ka → morF mugF ka kb = true → gorF mugF kb ka = true →
      JMR la (C (C kb vb) (C lb (A 0))) x → JMR (C (C ka va) (C la ra)) rb y → UniByR mugF x y u →
      JMR (C (C ka va) (C la ra)) (C (C kb vb) (C lb rb)) u
  | mn {ka va la ra kb vb lb rb x y u : Noun} : C (C ka va) (C la ra) ≠ C (C kb vb) (C lb rb) →
      kb ≠ ka → morF mugF ka kb = true → gorF mugF kb ka = false →
      JMR ra (C (C kb vb) (C (A 0) rb)) x → JMR (C (C ka va) (C la ra)) lb y → UniByR mugF x y u →
      JMR (C (C ka va) (C la ra)) (C (C kb vb) (C lb rb)) u
  | ng {ka va la ra kb vb lb rb x y u : Noun} : C (C ka va) (C la ra) ≠ C (C kb vb) (C lb rb) →
      morF mugF ka kb = false → gorF mugF ka kb = true →
      JMR (C (C ka va) (C la (A 0))) lb x → JMR ra (C (C kb vb) (C lb rb)) y → UniByR mugF x y u →
      JMR (C (C ka va) (C la ra)) (C (C kb vb) (C lb rb)) u
  | nn {ka va la ra kb vb lb rb x y u : Noun} : C (C ka va) (C la ra) ≠ C (C kb vb) (C lb rb) →
      morF mugF ka kb = false → gorF mugF ka kb = false →
      JMR (C (C ka va) (C (A 0) ra)) rb x → JMR la (C (C kb vb) (C lb rb)) y → UniByR mugF x y u →
      JMR (C (C ka va) (C la ra)) (C (C kb vb) (C lb rb)) u

/-- **The loop of `join-imms`** on a derivation, in any core whose context
holds `optC` where the `|^` core of `+alias` has it. -/
theorem jm_loop (X G Y Z OC P : Noun) (hL2 : slot? 0x1ffff OC = some layer2) :
    ∀ {a b out : Noun}, JMR a b out →
      nock (C alJMTrap (C P (C (C a b) (C X (C G (C Y (C Z OC))))))) alJMTrap = some out := by
  have hc := gorIn_morIn_layer2
  have hgor := gor_gate (mug := mugF) layer2 hc.1.2
  have hmor := mor_gate (mug := mugF) layer2 hc.2.2
  have hg := hc.1.1
  have hm := hc.2.1
  intro a b out h
  induction h with
  | nilB a =>
    nock_open alJMTrap
    simp [nock_exec]
  | nilA b hb =>
    nock_open alJMTrap
    simp [nock_exec, eqCode, Ne.symm hb]
  | eq ha =>
    nock_open alJMTrap
    simp [nock_exec, eqCode, ha, Ne.symm ha]
  | same hne hv hv0 _ _ ih1 ih2 =>
    have hi := int_in_gate layer2 hc hv
    nock_open alJMTrap
    simp [nock_exec, eqCode, hne, hL2, hm, hmor, morF_refl, in.arm_at, in_arm, in.int.arm_at, int_in_arm, hi,
      ih1, ih2, hv0, Ne.symm hv0]
  | same0 hne hv _ _ hu ih1 ih2 =>
    have hi := int_in_gate layer2 hc hv
    have hun := uni_by_gate layer2 hc hu
    nock_open alJMTrap
    simp [nock_exec, eqCode, hne, hL2, hm, hmor, morF_refl, in.arm_at, in_arm, in.int.arm_at, int_in_arm, hi,
      ih1, ih2, by.arm_at, by_arm, by.uni.arm_at, uni_by_arm, hun]
  | mg hne e m g _ _ hu ih1 ih2 =>
    have hun := uni_by_gate layer2 hc hu
    nock_open alJMTrap
    simp [nock_exec, eqCode, hne, e, m, g, hL2, hg, hm, hgor, hmor, ih1, ih2, by.arm_at, by_arm,
      by.uni.arm_at, uni_by_arm, hun]
  | mn hne e m g _ _ hu ih1 ih2 =>
    have hun := uni_by_gate layer2 hc hu
    nock_open alJMTrap
    simp [nock_exec, eqCode, hne, e, m, g, hL2, hg, hm, hgor, hmor, ih1, ih2, by.arm_at, by_arm,
      by.uni.arm_at, uni_by_arm, hun]
  | ng hne m g _ _ hu ih1 ih2 =>
    have hun := uni_by_gate layer2 hc hu
    nock_open alJMTrap
    simp [nock_exec, eqCode, hne, m, g, hL2, hg, hm, hgor, hmor, ih1, ih2, by.arm_at, by_arm,
      by.uni.arm_at, uni_by_arm, hun]
  | nn hne m g _ _ hu ih1 ih2 =>
    have hun := uni_by_gate layer2 hc hu
    nock_open alJMTrap
    simp [nock_exec, eqCode, hne, m, g, hL2, hg, hm, hgor, hmor, ih1, ih2, by.arm_at, by_arm,
      by.uni.arm_at, uni_by_arm, hun]


/-! ## On maps -/

/-- Every value is a set that is not empty. -/
def SetVals (a : Noun) : Prop := ∀ k v, Get a k v → IsSet mugF v ∧ v ≠ A 0

theorem setVals_sub {a a' : Noun} (h : SetVals a) (hs : ∀ k v, Get a' k v → Get a k v) : SetVals a' :=
  fun k v hg => h k v (hs k v hg)

/-- Two sets meet. -/
def Meet (va vb : Noun) : Prop := ∃ e, Has va e ∧ Has vb e

/-- The key `k` is in both maps, with sets that meet. -/
def Kp (a b k : Noun) : Prop := ∃ va vb, Get a k va ∧ Get b k vb ∧ Meet va vb

/-- The value kept at a key: the intersection of the two sets, not empty. -/
def VSpec (va vb v : Noun) : Prop := IsSet mugF v ∧ v ≠ A 0 ∧ ∀ e, Has v e ↔ Has va e ∧ Has vb e

/-- What the loop gives on `a` and `b`. -/
def JMP (a b : Noun) : Prop :=
  ∃ out, JMR a b out ∧ IsMap mugF out ∧
    (∀ k v, Get out k v → ∃ va vb, Get a k va ∧ Get b k vb ∧ VSpec va vb v) ∧
    ∀ k, KIn out k ↔ Kp a b k

theorem set_nonempty {v : Noun} (hv : IsSet mugF v) (h0 : v ≠ A 0) : ∃ e, Has v e := by
  cases Tree.of_isSet hv with
  | nil => exact absurd rfl h0
  | node => exact ⟨_, has_node.2 (Or.inl rfl)⟩

/-- The union of the two inner products of a branch. -/
theorem jm_comb {a b a1 b1 a2 b2 x y : Noun} (ha : IsMap mugF a) (hb : IsMap mugF b)
    (hx : IsMap mugF x) (hy : IsMap mugF y)
    (sx : ∀ k v, Get x k v → ∃ va vb, Get a1 k va ∧ Get b1 k vb ∧ VSpec va vb v)
    (sy : ∀ k v, Get y k v → ∃ va vb, Get a2 k va ∧ Get b2 k vb ∧ VSpec va vb v)
    (s1a : ∀ k v, Get a1 k v → Get a k v) (s1b : ∀ k v, Get b1 k v → Get b k v)
    (s2a : ∀ k v, Get a2 k v → Get a k v) (s2b : ∀ k v, Get b2 k v → Get b k v)
    (kx : ∀ k, KIn x k ↔ Kp a1 b1 k) (ky : ∀ k, KIn y k ↔ Kp a2 b2 k)
    (hk : ∀ k, (KIn a1 k ∧ KIn b1 k) ∨ (KIn a2 k ∧ KIn b2 k) ↔ KIn a k ∧ KIn b k) :
    ∃ u, UniByR mugF x y u ∧ IsMap mugF u ∧
      (∀ k v, Get u k v → ∃ va vb, Get a k va ∧ Get b k vb ∧ VSpec va vb v) ∧
      ∀ k, KIn u k ↔ Kp a b k := by
  obtain ⟨u, hu, hs, hsp, _⟩ := uniByP_of_maps _ x y (Nat.le_refl _) hx hy
  refine ⟨u, hu, hs, fun k v h => ?_, fun k => ?_⟩
  · rcases (hsp k v).1 h with h | ⟨h, -⟩
    · obtain ⟨va, vb, h1, h2, h3⟩ := sy k v h
      exact ⟨va, vb, s2a _ _ h1, s2b _ _ h2, h3⟩
    · obtain ⟨va, vb, h1, h2, h3⟩ := sx k v h
      exact ⟨va, vb, s1a _ _ h1, s1b _ _ h2, h3⟩
  · rw [uniSpec_kin hsp, kx, ky]
    constructor
    · rintro (⟨va, vb, g1, g2, m⟩ | ⟨va, vb, g1, g2, m⟩)
      · exact ⟨va, vb, s1a _ _ g1, s1b _ _ g2, m⟩
      · exact ⟨va, vb, s2a _ _ g1, s2b _ _ g2, m⟩
    · rintro ⟨va, vb, g1, g2, m⟩
      rcases (hk k).2 ⟨⟨va, g1⟩, ⟨vb, g2⟩⟩ with ⟨⟨va', g1'⟩, ⟨vb', g2'⟩⟩ | ⟨⟨va', g1'⟩, ⟨vb', g2'⟩⟩
      · have e1 := Get.unique ha (s1a _ _ g1') g1
        have e2 := Get.unique hb (s1b _ _ g2') g2
        subst e1 e2
        exact Or.inl ⟨_, _, g1', g2', m⟩
      · have e1 := Get.unique ha (s2a _ _ g1') g1
        have e2 := Get.unique hb (s2b _ _ g2') g2
        subst e1 e2
        exact Or.inr ⟨_, _, g1', g2', m⟩

/-- Equal maps. -/
theorem jmP_eq {b : Noun} (hb : IsMap mugF b) (hvb : SetVals b) (h0 : b ≠ A 0) : JMP b b := by
  refine ⟨b, JMR.eq h0, hb, fun k v h => ⟨v, v, h, h, (hvb k v h).1, (hvb k v h).2,
    fun e => ⟨fun h => ⟨h, h⟩, fun h => h.1⟩⟩, fun k => ⟨fun ⟨v, h⟩ => ?_, fun ⟨va, _, h, _, _⟩ => ⟨va, h⟩⟩⟩
  obtain ⟨e, he⟩ := set_nonempty (hvb k v h).1 (hvb k v h).2
  exact ⟨v, v, h, h, e, he, he⟩

/-- The keys kept under equal roots. -/
theorem kp_same {k va la ra vb lb rb : Noun} (ha : IsMap mugF (C (C k va) (C la ra)))
    (hb : IsMap mugF (C (C k vb) (C lb rb))) (k' : Noun) :
    Kp (C (C k va) (C la ra)) (C (C k vb) (C lb rb)) k' ↔ (k' = k ∧ Meet va vb) ∨ Kp la lb k' ∨ Kp ra rb k' := by
  obtain ⟨oLa, oRa⟩ := kin_ord ha
  obtain ⟨oLb, oRb⟩ := kin_ord hb
  constructor
  · rintro ⟨wa, wb, g1, g2, m⟩
    rcases Get_node.1 g1 with ⟨rfl, rfl⟩ | g1 | g1 <;> rcases Get_node.1 g2 with ⟨e, rfl⟩ | g2 | g2
    · exact Or.inl ⟨rfl, m⟩
    · exact absurd rfl (oLb _ ⟨_, g2⟩).1
    · exact absurd rfl (oRb _ ⟨_, g2⟩).1
    · exact absurd e (oLa _ ⟨_, g1⟩).1
    · exact Or.inr (Or.inl ⟨_, _, g1, g2, m⟩)
    · exact absurd (gorF_antisymm mugF (oLa _ ⟨_, g1⟩).2 (oRb _ ⟨_, g2⟩).2) (oLa _ ⟨_, g1⟩).1
    · exact absurd e (oRa _ ⟨_, g1⟩).1
    · exact absurd (gorF_antisymm mugF (oLb _ ⟨_, g2⟩).2 (oRa _ ⟨_, g1⟩).2) (oLb _ ⟨_, g2⟩).1
    · exact Or.inr (Or.inr ⟨_, _, g1, g2, m⟩)
  · rintro (⟨rfl, m⟩ | ⟨wa, wb, g1, g2, m⟩ | ⟨wa, wb, g1, g2, m⟩)
    · exact ⟨va, vb, Get_node.2 (Or.inl ⟨rfl, rfl⟩), Get_node.2 (Or.inl ⟨rfl, rfl⟩), m⟩
    · exact ⟨wa, wb, get_left g1, get_left g2, m⟩
    · exact ⟨wa, wb, get_right g1, get_right g2, m⟩

/-- The same key at both roots. -/
theorem jmP_same {m : Nat}
    (ih : ∀ a b, uniSz a + uniSz b < m → IsMap mugF a → IsMap mugF b → SetVals a → SetVals b → JMP a b)
    {k va la ra vb lb rb : Noun} (ha : IsMap mugF (C (C k va) (C la ra))) (hb : IsMap mugF (C (C k vb) (C lb rb)))
    (hne : C (C k va) (C la ra) ≠ C (C k vb) (C lb rb))
    (hs : uniSz (C (C k va) (C la ra)) + uniSz (C (C k vb) (C lb rb)) ≤ m)
    (hva : SetVals (C (C k va) (C la ra))) (hvb : SetVals (C (C k vb) (C lb rb))) :
    JMP (C (C k va) (C la ra)) (C (C k vb) (C lb rb)) := by
  obtain ⟨hla, hra, hLa, hRa⟩ := IsMap_node ha
  obtain ⟨hlb, hrb, hLb, hRb⟩ := IsMap_node hb
  rw [uni_sz_pair, uni_sz_pair] at hs
  have sa := hva k va (Get_node.2 (Or.inl ⟨rfl, rfl⟩))
  have sb := hvb k vb (Get_node.2 (Or.inl ⟨rfl, rfl⟩))
  obtain ⟨v, hv, hvs, hvk⟩ := intP_of_sets _ va vb (Nat.le_refl _) sa.1 sb.1
  obtain ⟨l, h1, hl, hlv, hlk⟩ := ih la lb (by omega) hla hlb
    (setVals_sub hva (fun _ _ h => get_left h)) (setVals_sub hvb (fun _ _ h => get_left h))
  obtain ⟨r, h2, hr, hrv, hrk⟩ := ih ra rb (by omega) hra hrb
    (setVals_sub hva (fun _ _ h => get_right h)) (setVals_sub hvb (fun _ _ h => get_right h))
  by_cases v0 : v = A 0
  · subst v0
    obtain ⟨u, hu, hus, husp, _⟩ := uniByP_of_maps _ l r (Nat.le_refl _) hl hr
    refine ⟨u, JMR.same0 hne hv h1 h2 hu, hus, fun k' w hw => ?_, fun k' => ?_⟩
    · rcases (husp k' w).1 hw with hw | ⟨hw, -⟩
      · obtain ⟨wa, wb, g1, g2, g3⟩ := hrv k' w hw
        exact ⟨wa, wb, get_right g1, get_right g2, g3⟩
      · obtain ⟨wa, wb, g1, g2, g3⟩ := hlv k' w hw
        exact ⟨wa, wb, get_left g1, get_left g2, g3⟩
    · have nm : ¬ Meet va vb := fun ⟨e, h1, h2⟩ => not_has_atom ((hvk e).2 ⟨h1, h2⟩)
      rw [uniSpec_kin husp, hlk, hrk, kp_same ha hb]
      simp [nm]
  · refine ⟨C (C k v) (C l r), JMR.same hne hv v0 h1 h2, IsMap.node hl hr ?_ ?_, ?_, fun k' => ?_⟩
    · intro k' w hw
      obtain ⟨w', -, h', -, -⟩ := hlv k' w hw
      exact hLa k' w' h'
    · intro k' w hw
      obtain ⟨w', -, h', -, -⟩ := hrv k' w hw
      exact hRa k' w' h'
    · intro k' w hw
      rcases Get_node.1 hw with ⟨rfl, rfl⟩ | hw | hw
      · exact ⟨va, vb, Get_node.2 (Or.inl ⟨rfl, rfl⟩), Get_node.2 (Or.inl ⟨rfl, rfl⟩), hvs, v0, hvk⟩
      · obtain ⟨wa, wb, g1, g2, g3⟩ := hlv k' w hw
        exact ⟨wa, wb, get_left g1, get_left g2, g3⟩
      · obtain ⟨wa, wb, g1, g2, g3⟩ := hrv k' w hw
        exact ⟨wa, wb, get_right g1, get_right g2, g3⟩
    · obtain ⟨e, he⟩ := set_nonempty hvs v0
      have hm : Meet va vb := ⟨e, (hvk e).1 he⟩
      rw [kin_node, hlk, hrk, kp_same ha hb]
      simp [hm]

theorem jmP_step {m : Nat}
    (ih : ∀ a b, uniSz a + uniSz b < m → IsMap mugF a → IsMap mugF b → SetVals a → SetVals b → JMP a b)
    (a b : Noun) (hs : uniSz a + uniSz b ≤ m) (ha : IsMap mugF a) (hb : IsMap mugF b) (hva : SetVals a) (hvb : SetVals b) :
    JMP a b := by
  cases hb with
  | nil =>
    exact ⟨A 0, JMR.nilB a, IsMap.nil, fun k v h => absurd h Get_atom,
      fun k => ⟨fun h => absurd h kin_nil, fun ⟨_, _, _, h, _⟩ => absurd h Get_atom⟩⟩
  | @node kb vb lb rb hlb hrb hLb hRb =>
    cases ha with
    | nil =>
      exact ⟨A 0, JMR.nilA _ (by simp), IsMap.nil, fun k v h => absurd h Get_atom,
        fun k => ⟨fun h => absurd h kin_nil, fun ⟨_, _, h, _, _⟩ => absurd h Get_atom⟩⟩
    | @node ka va la ra hla hra hLa hRa =>
      have ha : IsMap mugF (C (C ka va) (C la ra)) := IsMap.node hla hra hLa hRa
      have hb : IsMap mugF (C (C kb vb) (C lb rb)) := IsMap.node hlb hrb hLb hRb
      obtain ⟨oLa, oRa⟩ := kin_ord ha
      obtain ⟨oLb, oRb⟩ := kin_ord hb
      have hs' := hs
      rw [uni_sz_pair, uni_sz_pair] at hs'
      by_cases hab : C (C ka va) (C la ra) = C (C kb vb) (C lb rb)
      · rw [hab] at hva ⊢
        exact jmP_eq hb hvb (by simp)
      by_cases mo : morF mugF ka kb = true
      · by_cases e : kb = ka
        · subst e
          exact jmP_same ih ha hb hab hs hva hvb
        by_cases g : gorF mugF kb ka = true
        · obtain ⟨x, h1, hx, hxv, hxk⟩ := ih la (C (C kb vb) (C lb (A 0)))
            (by rw [uni_sz_pair, uni_sz_nil]; omega) hla (isMap_cutR hb)
            (setVals_sub hva (fun _ _ h => get_left h)) (setVals_sub hvb (fun _ _ h => get_cutR h))
          obtain ⟨y, h2, hy, hyv, hyk⟩ := ih _ rb (by rw [uni_sz_pair]; omega) ha hrb
            (setVals_sub hva (fun _ _ h => h)) (setVals_sub hvb (fun _ _ h => get_right h))
          obtain ⟨u, hu, ho, hov, hok⟩ := jm_comb ha hb hx hy hxv hyv (fun _ _ h => get_left h)
            (fun _ _ h => get_cutR h) (fun _ _ h => h) (fun _ _ h => get_right h) hxk hyk (fun k => by
              rw [kin_cutR, kin_node, kin_node]
              have f1 : (k = kb ∨ KIn lb k) → k ≠ ka ∧ gorF mugF k ka = true := by
                rintro (rfl | h)
                · exact ⟨e, g⟩
                · refine ⟨fun hk => ?_, gorF_trans mugF (oLb k h).2 g⟩
                  subst hk; exact e (gorF_antisymm mugF g (oLb _ h).2)
              have f2 : KIn ra k → gorF mugF ka k = true := fun h => (oRa k h).2
              have f3 : KIn ra k → k ≠ ka := fun h => (oRa k h).1
              have f4 : gorF mugF k ka = true → gorF mugF ka k = true → k = ka := fun h1 h2 =>
                gorF_antisymm mugF h1 h2
              clear h1 h2 hx hy hxv hyv hxk hyk ih hs hs' hla hra hLa hRa hlb hrb hLb hRb ha hb oLa oLb oRb hva hvb
              grind)
          exact ⟨u, JMR.mg hab e mo g h1 h2 hu, ho, hov, hok⟩
        · have g' : gorF mugF ka kb = true := gorF_of_not mugF g
          have gf : gorF mugF kb ka = false := by simpa using g
          obtain ⟨x, h1, hx, hxv, hxk⟩ := ih ra (C (C kb vb) (C (A 0) rb))
            (by rw [uni_sz_pair, uni_sz_nil]; omega) hra (isMap_cutL hb)
            (setVals_sub hva (fun _ _ h => get_right h)) (setVals_sub hvb (fun _ _ h => get_cutL h))
          obtain ⟨y, h2, hy, hyv, hyk⟩ := ih _ lb (by rw [uni_sz_pair]; omega) ha hlb
            (setVals_sub hva (fun _ _ h => h)) (setVals_sub hvb (fun _ _ h => get_left h))
          obtain ⟨u, hu, ho, hov, hok⟩ := jm_comb ha hb hx hy hxv hyv (fun _ _ h => get_right h)
            (fun _ _ h => get_cutL h) (fun _ _ h => h) (fun _ _ h => get_left h) hxk hyk (fun k => by
              rw [kin_cutL, kin_node, kin_node]
              have f1 : (k = kb ∨ KIn rb k) → k ≠ ka ∧ gorF mugF ka k = true := by
                rintro (rfl | h)
                · exact ⟨e, g'⟩
                · refine ⟨fun hk => ?_, gorF_trans mugF g' (oRb k h).2⟩
                  subst hk; exact e (gorF_antisymm mugF (oRb _ h).2 g')
              have f2 : KIn la k → gorF mugF k ka = true := fun h => (oLa k h).2
              have f3 : KIn la k → k ≠ ka := fun h => (oLa k h).1
              have f4 : gorF mugF k ka = true → gorF mugF ka k = true → k = ka := fun h1 h2 =>
                gorF_antisymm mugF h1 h2
              clear h1 h2 hx hy hxv hyv hxk hyk ih hs hs' hla hra hLa hRa hlb hrb hLb hRb ha hb oRa oLb oRb hva hvb
              grind)
          exact ⟨u, JMR.mn hab e mo gf h1 h2 hu, ho, hov, hok⟩
      · have mf : morF mugF ka kb = false := by simpa using mo
        have e : ka ≠ kb := fun h => by subst h; exact mo (morF_refl mugF _)
        by_cases g : gorF mugF ka kb = true
        · obtain ⟨x, h1, hx, hxv, hxk⟩ := ih (C (C ka va) (C la (A 0))) lb
            (by rw [uni_sz_pair, uni_sz_nil]; omega) (isMap_cutR ha) hlb
            (setVals_sub hva (fun _ _ h => get_cutR h)) (setVals_sub hvb (fun _ _ h => get_left h))
          obtain ⟨y, h2, hy, hyv, hyk⟩ := ih ra _ (by rw [uni_sz_pair]; omega) hra hb
            (setVals_sub hva (fun _ _ h => get_right h)) (setVals_sub hvb (fun _ _ h => h))
          obtain ⟨u, hu, ho, hov, hok⟩ := jm_comb ha hb hx hy hxv hyv (fun _ _ h => get_cutR h)
            (fun _ _ h => get_left h) (fun _ _ h => get_right h) (fun _ _ h => h) hxk hyk (fun k => by
              rw [kin_cutR, kin_node, kin_node]
              have f1 : (k = ka ∨ KIn la k) → k ≠ kb ∧ gorF mugF k kb = true := by
                rintro (rfl | h)
                · exact ⟨e, g⟩
                · refine ⟨fun hk => ?_, gorF_trans mugF (oLa k h).2 g⟩
                  subst hk; exact e (gorF_antisymm mugF g (oLa _ h).2)
              have f2 : KIn rb k → gorF mugF kb k = true := fun h => (oRb k h).2
              have f3 : KIn rb k → k ≠ kb := fun h => (oRb k h).1
              have f4 : gorF mugF k kb = true → gorF mugF kb k = true → k = kb := fun h1 h2 =>
                gorF_antisymm mugF h1 h2
              clear h1 h2 hx hy hxv hyv hxk hyk ih hs hs' hla hra hLa hRa hlb hrb hLb hRb ha hb oLa oRa oLb hva hvb
              grind)
          exact ⟨u, JMR.ng hab mf g h1 h2 hu, ho, hov, hok⟩
        · have g' : gorF mugF kb ka = true := gorF_of_not mugF g
          have gf : gorF mugF ka kb = false := by simpa using g
          obtain ⟨x, h1, hx, hxv, hxk⟩ := ih (C (C ka va) (C (A 0) ra)) rb
            (by rw [uni_sz_pair, uni_sz_nil]; omega) (isMap_cutL ha) hrb
            (setVals_sub hva (fun _ _ h => get_cutL h)) (setVals_sub hvb (fun _ _ h => get_right h))
          obtain ⟨y, h2, hy, hyv, hyk⟩ := ih la _ (by rw [uni_sz_pair]; omega) hla hb
            (setVals_sub hva (fun _ _ h => get_left h)) (setVals_sub hvb (fun _ _ h => h))
          obtain ⟨u, hu, ho, hov, hok⟩ := jm_comb ha hb hx hy hxv hyv (fun _ _ h => get_cutL h)
            (fun _ _ h => get_right h) (fun _ _ h => get_left h) (fun _ _ h => h) hxk hyk (fun k => by
              rw [kin_cutL, kin_node, kin_node]
              have f1 : (k = ka ∨ KIn ra k) → k ≠ kb ∧ gorF mugF kb k = true := by
                rintro (rfl | h)
                · exact ⟨e, g'⟩
                · refine ⟨fun hk => ?_, gorF_trans mugF g' (oRa k h).2⟩
                  subst hk; exact e (gorF_antisymm mugF (oRa _ h).2 g')
              have f2 : KIn lb k → gorF mugF k kb = true := fun h => (oLb k h).2
              have f3 : KIn lb k → k ≠ kb := fun h => (oLb k h).1
              have f4 : gorF mugF k kb = true → gorF mugF kb k = true → k = kb := fun h1 h2 =>
                gorF_antisymm mugF h1 h2
              clear h1 h2 hx hy hxv hyv hxk hyk ih hs hs' hla hra hLa hRa hlb hrb hLb hRb ha hb oLa oRa oRb hva hvb
              grind)
          exact ⟨u, JMR.nn hab mf gf h1 h2 hu, ho, hov, hok⟩

theorem jmP_of_maps : ∀ (m : Nat) (a b : Noun), uniSz a + uniSz b ≤ m →
    IsMap mugF a → IsMap mugF b → SetVals a → SetVals b → JMP a b := by
  intro m
  induction m with
  | zero => exact jmP_step (fun a b h => absurd h (Nat.not_lt_zero _))
  | succ m ih => exact jmP_step (fun a b h ha hb hva hvb => ih a b (by omega) ha hb hva hvb)

/-! ## Against the model -/

/-- A jug of nouns to sets of registers holds the immediates `m`: each value
a set with the members of the list at its key and not empty, and every key
whose list is not empty there. -/
def ImmsRel (N : Noun) (m : Opt.AImms) : Prop :=
  IsMap mugF N ∧ (∀ k v, Get N k v → SawRel v (m k) ∧ v ≠ A 0) ∧ ∀ k, m k ≠ [] → KIn N k

/-- **`join-imms`** of two jugs related to `ma` and `mb` is related to `joinImmsA ma mb`. -/
theorem al_jimms (X G Y Z : Noun) {Na Nb : Noun} {ma mb : Opt.AImms} (ha : ImmsRel Na ma)
    (hb : ImmsRel Nb mb) :
    ∃ N, nock (C alJImmsB (C (C Na Nb) (alCtx X G Y Z))) alJImmsB = some N ∧
      ImmsRel N (Opt.joinImmsA ma mb) := by
  obtain ⟨out, hR, hmap, hv, hk⟩ := jmP_of_maps _ Na Nb (Nat.le_refl _) ha.1 hb.1
    (fun k v h => ⟨(ha.2.1 k v h).1.1, (ha.2.1 k v h).2⟩) (fun k v h => ⟨(hb.2.1 k v h).1.1, (hb.2.1 k v h).2⟩)
  refine ⟨out, ?_, hmap, fun k v hg => ?_, fun k hk0 => ?_⟩
  · have hl := jm_loop X G Y Z optC alJImmsB optC_layer2 hR
    unfold alCtx
    nock_open alJImmsB
    simp [nock_exec, hl]
  · obtain ⟨va, vb, g1, g2, hs, h0, hm⟩ := hv k v hg
    exact ⟨sawRel_int (ha.2.1 k va g1).1 (hb.2.1 k vb g2).1 hs hm, h0⟩
  · obtain ⟨n, hn⟩ := List.exists_mem_of_ne_nil _ hk0
    obtain ⟨h1, h2⟩ := List.mem_filter.1 hn
    have h2' : n ∈ mb k := by simpa using h2
    obtain ⟨va, g1⟩ := ha.2.2 k (List.ne_nil_of_mem h1)
    obtain ⟨vb, g2⟩ := hb.2.2 k (List.ne_nil_of_mem h2')
    exact (hk k).2 ⟨va, vb, g1, g2, A n, ((ha.2.1 k va g1).1.has_atom n).2 h1,
      ((hb.2.1 k vb g2).1.has_atom n).2 h2'⟩

end Compiler
end Formalization
