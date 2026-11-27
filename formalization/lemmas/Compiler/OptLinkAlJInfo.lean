import lemmas.Compiler.OptLinkAlPInfo

/-!
# `+alias`: `join-info` (phase 4 of the plan, README Gaps 13)

```hoon
  ++  join-info
    |=  [a=(map @uvre info-reg) b=(map @uvre info-reg)]
    ^-  (map @uvre info-reg)
    |-  ^-  (map @uvre info-reg)
    ?~  b  ~
    ?~  a  ~
    ?:  =(a b)  a
    ?:  (mor p.n.a p.n.b)
      ?:  =(p.n.b p.n.a)
        %=  b
          n  [p.n.b (join-reg q.n.a q.n.b)]
          l  $(a l.a, b l.b)
          r  $(a r.a, b r.b)
        ==
      ?:  (gor p.n.b p.n.a)
        (~(uni by $(a l.a, r.b ~)) $(b r.b))
      (~(uni by $(a r.a, l.b ~)) $(b l.b))
    ?:  (gor p.n.a p.n.b)
      (~(uni by $(b l.b, r.a ~)) $(a r.a))
    (~(uni by $(b r.b, l.a ~)) $(a l.a))
```

* `JIR jr a b out`: the loop (the trap `alJITrap`), one constructor per
  branch, where `jr va vb v` says that `join-reg` of `va` and `vb` is `v`
  and the four last branches unite the products of two inner calls with
  `+uni:by` (`UniByR`); `ji_loop` runs the Nock on every derivation.
* `jiP_of_maps`: on two maps whose values `join-reg` takes (`jr` defined on
  them), a derivation to a map holding exactly the keys of both, the value
  at each the `jr` of the two or, from an equal subtree, the value itself.
* `al_jinfo`: **`join-info` of two related maps is related to `joinInfoA`**
  (`InfoMapRel`: a map of atoms to related `info-reg` nouns, the same keys).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The loop of `join-info`, one constructor per branch. -/
inductive JIR (jr : Noun → Noun → Noun → Prop) : Noun → Noun → Noun → Prop where
  | nilB (a : Noun) : JIR jr a (A 0) (A 0)
  | nilA (b : Noun) : b ≠ A 0 → JIR jr (A 0) b (A 0)
  | eq {a : Noun} : a ≠ A 0 → JIR jr a a a
  | same {k va la ra vb lb rb v l r : Noun} : C (C k va) (C la ra) ≠ C (C k vb) (C lb rb) →
      jr va vb v → JIR jr la lb l → JIR jr ra rb r →
      JIR jr (C (C k va) (C la ra)) (C (C k vb) (C lb rb)) (C (C k v) (C l r))
  | mg {ka va la ra kb vb lb rb x y u : Noun} : C (C ka va) (C la ra) ≠ C (C kb vb) (C lb rb) →
      kb ≠ ka → morF mugF ka kb = true → gorF mugF kb ka = true →
      JIR jr la (C (C kb vb) (C lb (A 0))) x → JIR jr (C (C ka va) (C la ra)) rb y → UniByR mugF x y u →
      JIR jr (C (C ka va) (C la ra)) (C (C kb vb) (C lb rb)) u
  | mn {ka va la ra kb vb lb rb x y u : Noun} : C (C ka va) (C la ra) ≠ C (C kb vb) (C lb rb) →
      kb ≠ ka → morF mugF ka kb = true → gorF mugF kb ka = false →
      JIR jr ra (C (C kb vb) (C (A 0) rb)) x → JIR jr (C (C ka va) (C la ra)) lb y → UniByR mugF x y u →
      JIR jr (C (C ka va) (C la ra)) (C (C kb vb) (C lb rb)) u
  | ng {ka va la ra kb vb lb rb x y u : Noun} : C (C ka va) (C la ra) ≠ C (C kb vb) (C lb rb) →
      morF mugF ka kb = false → gorF mugF ka kb = true →
      JIR jr (C (C ka va) (C la (A 0))) lb x → JIR jr ra (C (C kb vb) (C lb rb)) y → UniByR mugF x y u →
      JIR jr (C (C ka va) (C la ra)) (C (C kb vb) (C lb rb)) u
  | nn {ka va la ra kb vb lb rb x y u : Noun} : C (C ka va) (C la ra) ≠ C (C kb vb) (C lb rb) →
      morF mugF ka kb = false → gorF mugF ka kb = false →
      JIR jr (C (C ka va) (C (A 0) ra)) rb x → JIR jr la (C (C kb vb) (C lb rb)) y → UniByR mugF x y u →
      JIR jr (C (C ka va) (C la ra)) (C (C kb vb) (C lb rb)) u

/-- The arm `join-reg` at the head of the battery of the `|^` core. -/
def alJRArm : Noun := C (A 8) (C (C (A 1) alJRegBunt) (C (C (A 1) alJRegB) (C (A 0) (A 1))))

/-- `join-reg` in the core `K`. -/
def jrK (K va vb v : Noun) : Prop := nock (C alJRegB (C (C va vb) K)) alJRegB = some v

/-- **The loop of `join-info`** on a derivation, in a core whose battery has
`join-reg` at its head and whose context holds `optC`. -/
theorem ji_loop (R G Y Z OC P : Noun) (hL2 : slot? 0x1ffff OC = some layer2) :
    ∀ {a b out : Noun}, JIR (jrK (C (C alJRArm R) (C G (C Y (C Z OC))))) a b out →
      nock (C alJITrap (C P (C (C a b) (C (C alJRArm R) (C G (C Y (C Z OC))))))) alJITrap = some out := by
  have hc := gorIn_morIn_layer2
  have hgor := gor_gate (mug := mugF) layer2 hc.1.2
  have hmor := mor_gate (mug := mugF) layer2 hc.2.2
  have hg := hc.1.1
  have hm := hc.2.1
  intro a b out h
  induction h with
  | nilB a =>
    nock_open alJITrap
    simp [nock_exec]
  | nilA b hb =>
    nock_open alJITrap
    simp [nock_exec, eqCode, Ne.symm hb]
  | eq ha =>
    nock_open alJITrap
    simp [nock_exec, eqCode, ha, Ne.symm ha]
  | same hne hv _ _ ih1 ih2 =>
    unfold jrK at hv
    nock_open alJITrap
    unfold alJRArm at hv ih1 ih2 ⊢
    simp [nock_exec, eqCode, hne, hL2, hm, hmor, morF_refl, hv, ih1, ih2]
  | mg hne e m g _ _ hu ih1 ih2 =>
    have hun := uni_by_gate layer2 hc hu
    nock_open alJITrap
    simp [nock_exec, eqCode, hne, e, m, g, hL2, hg, hm, hgor, hmor, ih1, ih2, by.arm_at, by_arm,
      by.uni.arm_at, uni_by_arm, hun]
  | mn hne e m g _ _ hu ih1 ih2 =>
    have hun := uni_by_gate layer2 hc hu
    nock_open alJITrap
    simp [nock_exec, eqCode, hne, e, m, g, hL2, hg, hm, hgor, hmor, ih1, ih2, by.arm_at, by_arm,
      by.uni.arm_at, uni_by_arm, hun]
  | ng hne m g _ _ hu ih1 ih2 =>
    have hun := uni_by_gate layer2 hc hu
    nock_open alJITrap
    simp [nock_exec, eqCode, hne, m, g, hL2, hg, hm, hgor, hmor, ih1, ih2, by.arm_at, by_arm,
      by.uni.arm_at, uni_by_arm, hun]
  | nn hne m g _ _ hu ih1 ih2 =>
    have hun := uni_by_gate layer2 hc hu
    nock_open alJITrap
    simp [nock_exec, eqCode, hne, m, g, hL2, hg, hm, hgor, hmor, ih1, ih2, by.arm_at, by_arm,
      by.uni.arm_at, uni_by_arm, hun]

/-! ## On maps -/

/-- The value at a key of both: `join-reg` of the two, or the value itself
where the two are equal (an equal subtree). -/
def JV (jr : Noun → Noun → Noun → Prop) (va vb v : Noun) : Prop := v = va ∧ va = vb ∨ jr va vb v

/-- What the loop gives on `a` and `b`: a derivation to a map with the keys
of both, the value at each `JV` of the two. -/
def JIP (jr : Noun → Noun → Noun → Prop) (a b : Noun) : Prop :=
  ∃ out, JIR jr a b out ∧ IsMap mugF out ∧
    (∀ k v, Get out k v → ∃ va vb, Get a k va ∧ Get b k vb ∧ JV jr va vb v) ∧
    ∀ k, KIn out k ↔ KIn a k ∧ KIn b k

/-- `join-reg` returns on the values of each key of both maps. -/
def JrOn (jr : Noun → Noun → Noun → Prop) (a b : Noun) : Prop :=
  ∀ k va vb, Get a k va → Get b k vb → ∃ v, jr va vb v

theorem jrOn_sub {jr : Noun → Noun → Noun → Prop} {a b a' b' : Noun} (h : JrOn jr a b)
    (ha : ∀ k v, Get a' k v → Get a k v) (hb : ∀ k v, Get b' k v → Get b k v) : JrOn jr a' b' :=
  fun k va vb h1 h2 => h k va vb (ha k va h1) (hb k vb h2)

/-- The union of the two inner products of a branch. -/
theorem ji_comb {jr : Noun → Noun → Noun → Prop} {a b a1 b1 a2 b2 x y : Noun}
    (hx : IsMap mugF x) (hy : IsMap mugF y)
    (sx : ∀ k v, Get x k v → ∃ va vb, Get a1 k va ∧ Get b1 k vb ∧ JV jr va vb v)
    (sy : ∀ k v, Get y k v → ∃ va vb, Get a2 k va ∧ Get b2 k vb ∧ JV jr va vb v)
    (s1a : ∀ k v, Get a1 k v → Get a k v) (s1b : ∀ k v, Get b1 k v → Get b k v)
    (s2a : ∀ k v, Get a2 k v → Get a k v) (s2b : ∀ k v, Get b2 k v → Get b k v)
    (kx : ∀ k, KIn x k ↔ KIn a1 k ∧ KIn b1 k) (ky : ∀ k, KIn y k ↔ KIn a2 k ∧ KIn b2 k)
    (hk : ∀ k, (KIn a1 k ∧ KIn b1 k) ∨ (KIn a2 k ∧ KIn b2 k) ↔ KIn a k ∧ KIn b k) :
    ∃ u, UniByR mugF x y u ∧ IsMap mugF u ∧
      (∀ k v, Get u k v → ∃ va vb, Get a k va ∧ Get b k vb ∧ JV jr va vb v) ∧
      ∀ k, KIn u k ↔ KIn a k ∧ KIn b k := by
  obtain ⟨u, hu, hs, hsp, _⟩ := uniByP_of_maps _ x y (Nat.le_refl _) hx hy
  refine ⟨u, hu, hs, fun k v h => ?_, fun k => ?_⟩
  · rcases (hsp k v).1 h with h | ⟨h, -⟩
    · obtain ⟨va, vb, h1, h2, h3⟩ := sy k v h
      exact ⟨va, vb, s2a _ _ h1, s2b _ _ h2, h3⟩
    · obtain ⟨va, vb, h1, h2, h3⟩ := sx k v h
      exact ⟨va, vb, s1a _ _ h1, s1b _ _ h2, h3⟩
  · rw [uniSpec_kin hsp, kx, ky, hk]

theorem get_left {k v l r k' v' : Noun} (h : Get l k' v') : Get (C (C k v) (C l r)) k' v' :=
  Get_node.2 (Or.inr (Or.inl h))

theorem get_right {k v l r k' v' : Noun} (h : Get r k' v') : Get (C (C k v) (C l r)) k' v' :=
  Get_node.2 (Or.inr (Or.inr h))

theorem get_cutR {k v l r k' v' : Noun} (h : Get (C (C k v) (C l (A 0))) k' v') :
    Get (C (C k v) (C l r)) k' v' := by
  rcases Get_node.1 h with h | h | h
  · exact Get_node.2 (Or.inl h)
  · exact get_left h
  · exact absurd h Get_atom

theorem get_cutL {k v l r k' v' : Noun} (h : Get (C (C k v) (C (A 0) r)) k' v') :
    Get (C (C k v) (C l r)) k' v' := by
  rcases Get_node.1 h with h | h | h
  · exact Get_node.2 (Or.inl h)
  · exact absurd h Get_atom
  · exact get_right h

theorem isMap_cutR {k v l r : Noun} (h : IsMap mugF (C (C k v) (C l r))) : IsMap mugF (C (C k v) (C l (A 0))) := by
  obtain ⟨hl, -, hL, -⟩ := IsMap_node h
  exact IsMap.node hl IsMap.nil hL (fun _ _ h => absurd h Get_atom)

theorem isMap_cutL {k v l r : Noun} (h : IsMap mugF (C (C k v) (C l r))) : IsMap mugF (C (C k v) (C (A 0) r)) := by
  obtain ⟨-, hr, -, hR⟩ := IsMap_node h
  exact IsMap.node IsMap.nil hr (fun _ _ h => absurd h Get_atom) hR

theorem kin_cutR {k v l k' : Noun} : KIn (C (C k v) (C l (A 0))) k' ↔ k' = k ∨ KIn l k' := by
  rw [kin_node]; simp [kin_nil]

theorem kin_cutL {k v r k' : Noun} : KIn (C (C k v) (C (A 0) r)) k' ↔ k' = k ∨ KIn r k' := by
  rw [kin_node]; simp [kin_nil]

/-- The order facts of a node, on keys. -/
theorem kin_ord {k v l r : Noun} (h : IsMap mugF (C (C k v) (C l r))) :
    (∀ k', KIn l k' → k' ≠ k ∧ gorF mugF k' k = true) ∧ (∀ k', KIn r k' → k' ≠ k ∧ gorF mugF k k' = true) := by
  obtain ⟨-, -, hL, hR⟩ := IsMap_node h
  exact ⟨fun k' ⟨w, hw⟩ => ⟨(hL k' w hw).1, (hL k' w hw).2.1⟩, fun k' ⟨w, hw⟩ => ⟨(hR k' w hw).1, (hR k' w hw).2.1⟩⟩

/-- The same key at both roots. -/
theorem jiP_same {jr : Noun → Noun → Noun → Prop} {m : Nat}
    (ih : ∀ a b, uniSz a + uniSz b < m → IsMap mugF a → IsMap mugF b → JrOn jr a b → JIP jr a b)
    {k va la ra vb lb rb : Noun} (ha : IsMap mugF (C (C k va) (C la ra))) (hb : IsMap mugF (C (C k vb) (C lb rb)))
    (hne : C (C k va) (C la ra) ≠ C (C k vb) (C lb rb))
    (hs : uniSz (C (C k va) (C la ra)) + uniSz (C (C k vb) (C lb rb)) ≤ m)
    (hj : JrOn jr (C (C k va) (C la ra)) (C (C k vb) (C lb rb))) :
    JIP jr (C (C k va) (C la ra)) (C (C k vb) (C lb rb)) := by
  obtain ⟨hla, hra, hLa, hRa⟩ := IsMap_node ha
  obtain ⟨hlb, hrb, hLb, hRb⟩ := IsMap_node hb
  obtain ⟨oLa, oRa⟩ := kin_ord ha
  obtain ⟨oLb, oRb⟩ := kin_ord hb
  rw [uni_sz_pair, uni_sz_pair] at hs
  obtain ⟨v, hv⟩ := hj k va vb (Get_node.2 (Or.inl ⟨rfl, rfl⟩)) (Get_node.2 (Or.inl ⟨rfl, rfl⟩))
  obtain ⟨l, h1, hl, hlv, hlk⟩ := ih la lb (by omega) hla hlb
    (jrOn_sub hj (fun _ _ h => get_left h) (fun _ _ h => get_left h))
  obtain ⟨r, h2, hr, hrv, hrk⟩ := ih ra rb (by omega) hra hrb
    (jrOn_sub hj (fun _ _ h => get_right h) (fun _ _ h => get_right h))
  refine ⟨C (C k v) (C l r), JIR.same hne hv h1 h2, IsMap.node hl hr ?_ ?_, ?_, ?_⟩
  · intro k' w hw
    obtain ⟨w', -, h', -, -⟩ := hlv k' w hw
    exact hLa k' w' h'
  · intro k' w hw
    obtain ⟨w', -, h', -, -⟩ := hrv k' w hw
    exact hRa k' w' h'
  · intro k' w hw
    rcases Get_node.1 hw with ⟨rfl, rfl⟩ | hw | hw
    · exact ⟨va, vb, Get_node.2 (Or.inl ⟨rfl, rfl⟩), Get_node.2 (Or.inl ⟨rfl, rfl⟩), Or.inr hv⟩
    · obtain ⟨wa, wb, g1, g2, g3⟩ := hlv k' w hw
      exact ⟨wa, wb, get_left g1, get_left g2, g3⟩
    · obtain ⟨wa, wb, g1, g2, g3⟩ := hrv k' w hw
      exact ⟨wa, wb, get_right g1, get_right g2, g3⟩
  · intro k'
    have c1 : KIn la k' → ¬ KIn rb k' := fun h1 h2 =>
      (oLa k' h1).1 (gorF_antisymm mugF (oLa k' h1).2 (oRb k' h2).2)
    have c2 : KIn ra k' → ¬ KIn lb k' := fun h1 h2 =>
      (oLb k' h2).1 (gorF_antisymm mugF (oLb k' h2).2 (oRa k' h1).2)
    have d1 := fun h => (oLa k' h).1
    have d2 := fun h => (oRa k' h).1
    have d3 := fun h => (oLb k' h).1
    have d4 := fun h => (oRb k' h).1
    rw [kin_node, kin_node, kin_node, hlk, hrk]
    clear ih hs h1 h2 hl hr hlv hrv hlk hrk hla hra hlb hrb hLa hRa hLb hRb ha hb oLa oRa oLb oRb hj hv hne
    grind

/-- One level of the induction on the number of nodes. -/
theorem jiP_step {jr : Noun → Noun → Noun → Prop} {m : Nat}
    (ih : ∀ a b, uniSz a + uniSz b < m → IsMap mugF a → IsMap mugF b → JrOn jr a b → JIP jr a b)
    (a b : Noun) (hs : uniSz a + uniSz b ≤ m) (ha : IsMap mugF a) (hb : IsMap mugF b) (hj : JrOn jr a b) :
    JIP jr a b := by
  cases hb with
  | nil =>
    exact ⟨A 0, JIR.nilB a, IsMap.nil, fun k v h => absurd h Get_atom,
      fun k => ⟨fun h => absurd h kin_nil, fun h => absurd h.2 kin_nil⟩⟩
  | @node kb vb lb rb hlb hrb hLb hRb =>
    cases ha with
    | nil =>
      exact ⟨A 0, JIR.nilA _ (by simp), IsMap.nil, fun k v h => absurd h Get_atom,
        fun k => ⟨fun h => absurd h kin_nil, fun h => absurd h.1 kin_nil⟩⟩
    | @node ka va la ra hla hra hLa hRa =>
      have ha : IsMap mugF (C (C ka va) (C la ra)) := IsMap.node hla hra hLa hRa
      have hb : IsMap mugF (C (C kb vb) (C lb rb)) := IsMap.node hlb hrb hLb hRb
      obtain ⟨oLa, oRa⟩ := kin_ord ha
      obtain ⟨oLb, oRb⟩ := kin_ord hb
      have hs' := hs
      rw [uni_sz_pair, uni_sz_pair] at hs'
      by_cases hab : C (C ka va) (C la ra) = C (C kb vb) (C lb rb)
      · rw [hab]
        exact ⟨_, JIR.eq (by simp), hb, fun k v h => ⟨v, v, h, h, Or.inl ⟨rfl, rfl⟩⟩,
          fun k => ⟨fun h => ⟨h, h⟩, fun h => h.1⟩⟩
      by_cases mo : morF mugF ka kb = true
      · by_cases e : kb = ka
        · subst e
          exact jiP_same ih ha hb hab hs hj
        by_cases g : gorF mugF kb ka = true
        · obtain ⟨x, h1, hx, hxv, hxk⟩ := ih la (C (C kb vb) (C lb (A 0)))
            (by rw [uni_sz_pair, uni_sz_nil]; omega) hla (isMap_cutR hb)
            (jrOn_sub hj (fun _ _ h => get_left h) (fun _ _ h => get_cutR h))
          obtain ⟨y, h2, hy, hyv, hyk⟩ := ih _ rb (by rw [uni_sz_pair]; omega) ha hrb
            (jrOn_sub hj (fun _ _ h => h) (fun _ _ h => get_right h))
          obtain ⟨u, hu, ho, hov, hok⟩ := ji_comb hx hy hxv hyv (fun _ _ h => get_left h)
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
              clear h1 h2 hx hy hxv hyv hxk hyk ih hs hs' hla hra hLa hRa hlb hrb hLb hRb ha hb oLa oLb oRb hj
              grind)
          exact ⟨u, JIR.mg hab e mo g h1 h2 hu, ho, hov, hok⟩
        · have g' : gorF mugF ka kb = true := gorF_of_not mugF g
          have gf : gorF mugF kb ka = false := by simpa using g
          obtain ⟨x, h1, hx, hxv, hxk⟩ := ih ra (C (C kb vb) (C (A 0) rb))
            (by rw [uni_sz_pair, uni_sz_nil]; omega) hra (isMap_cutL hb)
            (jrOn_sub hj (fun _ _ h => get_right h) (fun _ _ h => get_cutL h))
          obtain ⟨y, h2, hy, hyv, hyk⟩ := ih _ lb (by rw [uni_sz_pair]; omega) ha hlb
            (jrOn_sub hj (fun _ _ h => h) (fun _ _ h => get_left h))
          obtain ⟨u, hu, ho, hov, hok⟩ := ji_comb hx hy hxv hyv (fun _ _ h => get_right h)
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
              clear h1 h2 hx hy hxv hyv hxk hyk ih hs hs' hla hra hLa hRa hlb hrb hLb hRb ha hb oRa oLb oRb hj
              grind)
          exact ⟨u, JIR.mn hab e mo gf h1 h2 hu, ho, hov, hok⟩
      · have mf : morF mugF ka kb = false := by simpa using mo
        have e : ka ≠ kb := fun h => by subst h; exact mo (morF_refl mugF _)
        by_cases g : gorF mugF ka kb = true
        · obtain ⟨x, h1, hx, hxv, hxk⟩ := ih (C (C ka va) (C la (A 0))) lb
            (by rw [uni_sz_pair, uni_sz_nil]; omega) (isMap_cutR ha) hlb
            (jrOn_sub hj (fun _ _ h => get_cutR h) (fun _ _ h => get_left h))
          obtain ⟨y, h2, hy, hyv, hyk⟩ := ih ra _ (by rw [uni_sz_pair]; omega) hra hb
            (jrOn_sub hj (fun _ _ h => get_right h) (fun _ _ h => h))
          obtain ⟨u, hu, ho, hov, hok⟩ := ji_comb hx hy hxv hyv (fun _ _ h => get_cutR h)
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
              clear h1 h2 hx hy hxv hyv hxk hyk ih hs hs' hla hra hLa hRa hlb hrb hLb hRb ha hb oLa oRa oLb hj
              grind)
          exact ⟨u, JIR.ng hab mf g h1 h2 hu, ho, hov, hok⟩
        · have g' : gorF mugF kb ka = true := gorF_of_not mugF g
          have gf : gorF mugF ka kb = false := by simpa using g
          obtain ⟨x, h1, hx, hxv, hxk⟩ := ih (C (C ka va) (C (A 0) ra)) rb
            (by rw [uni_sz_pair, uni_sz_nil]; omega) (isMap_cutL ha) hrb
            (jrOn_sub hj (fun _ _ h => get_cutL h) (fun _ _ h => get_right h))
          obtain ⟨y, h2, hy, hyv, hyk⟩ := ih la _ (by rw [uni_sz_pair]; omega) hla hb
            (jrOn_sub hj (fun _ _ h => get_left h) (fun _ _ h => h))
          obtain ⟨u, hu, ho, hov, hok⟩ := ji_comb hx hy hxv hyv (fun _ _ h => get_cutL h)
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
              clear h1 h2 hx hy hxv hyv hxk hyk ih hs hs' hla hra hLa hRa hlb hrb hLb hRb ha hb oLa oRa oRb hj
              grind)
          exact ⟨u, JIR.nn hab mf gf h1 h2 hu, ho, hov, hok⟩

theorem jiP_of_maps {jr : Noun → Noun → Noun → Prop} : ∀ (m : Nat) (a b : Noun), uniSz a + uniSz b ≤ m →
    IsMap mugF a → IsMap mugF b → JrOn jr a b → JIP jr a b := by
  intro m
  induction m with
  | zero => exact jiP_step (fun a b h => absurd h (Nat.not_lt_zero _))
  | succ m ih => exact jiP_step (fun a b h ha hb hj => ih a b (by omega) ha hb hj)

end Compiler
end Formalization
