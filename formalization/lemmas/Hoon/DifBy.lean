module

public import lemmas.Hoon.DelBy
import lemmas.KernelRfl
import all lemmas.Pill.Arm.By

/-!
`+bif:by` and `+dif:by` of the pill's `hoon.hoon` (`+sect` of `+comp` reads
`~(dif by cond.gen)`).

```hoon
++  bif                                               ::  splits a by b
  ~/  %bif
  |*  b=*
  |-  ^+  [l=a r=a]
  ?~  a
    [~ ~]
  ?:  =(b p.n.a)
    +.a
  ?:  (gor b p.n.a)
    =+  d=$(a l.a)
    ?>  ?=(^ d)
    [l.d a(l r.d)]
  =+  d=$(a r.a)
  ?>  ?=(^ d)
  [a(r l.d) r.d]
::
++  dif                                               ::  difference
  ~/  %dif
  |*  b=_a
  |-  ^+  a
  ?~  b
    a
  =+  c=(bif p.n.b)
  ?>  ?=(^ c)
  =+  d=$(a l.c, b l.b)
  =+  e=$(a r.c, b r.b)
  |-  ^-  [$?(~ _a)]
  ?~  d  e
  ?~  e  d
  ?:  (mor p.n.d p.n.e)
    d(r $(d r.d))
  e(l $(e l.e))
```

The `?>  ?=(^ d)` and `?>  ?=(^ c)` of a cell type compile to a `%toss`
hint on the cell test, which cannot crash.  The merge loop of `+dif` is
`mergeF` of `+del`.  `dif_by`: on two maps, `+dif:by` is a map with the pairs
of `a` whose keys `b` does not hold.
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

/-! ## The nouns of `+bif:by` -/

/-- The loop of `+bif:by`. -/
def bifByLoop : Noun := C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 62)))) (C (C (A 1) (C (A 0) (A 0))) (C (A 6) (C (C (A 5) (C (C (A 0) (A 14)) (C (A 0) (A 248)))) (C (C (A 0) (A 125)) (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 182) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 30)) (C (A 0) (A 504)))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 62) (C (A 0) (A 250))) (C (A 0) (A 1)))))) (C (A 11) (C (C (A 0x73736f74) (C (A 3) (C (A 0) (A 2)))) (C (C (A 0) (A 4)) (C (A 10) (C (C (A 6) (C (A 0) (A 5))) (C (A 0) (A 126))))))))) (C (A 8) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 62) (C (A 0) (A 251))) (C (A 0) (A 1)))))) (C (A 11) (C (C (A 0x73736f74) (C (A 3) (C (A 0) (A 2)))) (C (C (A 10) (C (C (A 7) (C (A 0) (A 4))) (C (A 0) (A 126)))) (C (A 0) (A 5)))))))))))))))

/-- The battery of the gate of `+bif:by`. -/
def bifByBattery : Noun := C (A 8) (C (C (A 1) bifByLoop) (C (A 9) (C (A 2) (C (A 0) (A 1)))))

/-- The arm `+bif` of the door `+by`. -/
def bifByArm : Noun := C (A 7) (C (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) bifByBattery) (C (A 0) (A 1))))) (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x666962) (C (C (A 0) (A 7)) (A 0))))) (C (A 0) (A 1)))))

/-- `+bif` sits at axis `342` of the door, as `+dif` reads it. -/
theorem bif_by_arm_at : ∀ x, slot? 342 (C by.battery x) = some bifByArm := by
  intro x; kernel_rfl

@[nock_exec] theorem bif_by_arm (d : Noun) :
    nock d bifByArm = some (C bifByBattery (C (A 0) d)) := by
  nock_open bifByArm; simp only [nock_exec]

/-! ## The models -/

/-- The loop of `+bif:by`: the pairs of `a` split around the key `b`
(dropped if `a` holds it). -/
def bifByF (mug : Noun → Nat) (b : Noun) : Noun → Option Noun
  | Noun.atom 0 => some (C (A 0) (A 0))
  | Noun.cell (Noun.cell p q) (Noun.cell l r) =>
    if b = p then some (C l r)
    else if gorF mug b p then
      match bifByF mug b l with
      | some (Noun.cell ld rd) => some (C ld (C (C p q) (C rd r)))
      | _ => none
    else
      match bifByF mug b r with
      | some (Noun.cell ld rd) => some (C (C (C p q) (C l ld)) rd)
      | _ => none
  | _ => none

/-- `+dif:by`: the pairs of `a` whose keys `b` does not hold. -/
def difByF (mug : Noun → Nat) : Noun → Noun → Option Noun
  | a, Noun.atom 0 => some a
  | a, Noun.cell (Noun.cell pb _) (Noun.cell lb rb) =>
    match bifByF mug pb a with
    | some (Noun.cell lc rc) =>
      match difByF mug lc lb, difByF mug rc rb with
      | some d, some e => mergeF mug d e
      | _, _ => none
    | _ => none
  | _, _ => none

/-! ## The Nock -/

theorem bif_by_loop {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx) (B b : Noun) :
    ∀ a out, bifByF mug b a = some out →
      nock (C bifByLoop (C B (C b (C by.battery (C a ctx))))) bifByLoop = some out := by
  intro a
  have hgor := gor_gate (mug := mug) ctx hc.2
  have hg := hc.1
  fun_induction bifByF mug b a
  all_goals intro out h
  all_goals first
    | (simp at h; done)
    | skip
  all_goals first
    | (cases h
       nock_open bifByLoop
       simp [nock_exec, *]
       done)
    | (nock_open bifByLoop
       simp [nock_exec, *])

theorem bif_by_gate {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx) (a b l r : Noun)
    (h : bifByF mug b a = some (C l r)) :
    nock (C bifByBattery (C b (C by.battery (C a ctx)))) bifByBattery = some (C l r) := by
  nock_open bifByBattery
  simp only [nock_exec, bif_by_loop ctx hc _ b a _ h]

theorem dif_by_merge_loop {mug : Noun → Nat} (ctx : Noun) (hc : MorIn mug ctx) (c b a : Noun) :
    ∀ d e out, mergeF mug d e = some out →
      nock (C by.dif.loop0 (C e (C d (C c (C by.dif.loop1 (C by.dif.battery (C b (C by.battery (C a ctx)))))))))
        by.dif.loop0 = some out := by
  intro d e
  have hmor := mor_gate (mug := mug) ctx hc.2
  have hm := hc.1
  fun_induction mergeF mug d e
  all_goals intro out h
  all_goals first
    | (simp at h; done)
    | skip
  all_goals first
    | (cases h
       nock_open by.dif.loop0
       simp [nock_exec, *]
       done)
    | (nock_open by.dif.loop0
       simp [nock_exec, *])

theorem dif_by_loop {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx) :
    ∀ a b out, difByF mug a b = some out →
      nock (C by.dif.loop1 (C by.dif.battery (C b (C by.battery (C a ctx))))) by.dif.loop1 = some out := by
  intro a b
  have hmerge := dif_by_merge_loop ctx hc.2
  have hbif := bif_by_gate ctx hc.1
  fun_induction difByF mug a b
  all_goals intro out h
  all_goals first
    | (simp at h; done)
    | skip
  · cases h
    nock_open by.dif.loop1
    simp [nock_exec]
  · rename_i a pb qb lb rb lc rc hb d e he hd ih2 ih1
    have h1 := hbif a pb lc rc hb
    have h2 := ih2 d hd
    have h3 := ih1 e he
    have h4 := hmerge (C lc rc) (C (C pb qb) (C lb rb)) a d e out h
    nock_open by.dif.loop1
    simp [nock_exec, bif_by_arm_at, h1, h2, h3, h4]

theorem dif_by_gate {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx)
    (a b out : Noun) (h : difByF mug a b = some out) :
    nock (C by.dif.battery (C b (C by.battery (C a ctx)))) by.dif.battery = some out := by
  nock_open by.dif.battery
  simp only [nock_exec, dif_by_loop ctx hc a b out h]

/-! ## On maps -/

/-- `+bif:by` on a map: the pairs before `b` on the left and those after it
on the right, both maps; the pair at `b` is dropped. -/
theorem bifByF_spec {mug : Noun → Nat} (b : Noun) {a : Noun} (ha : IsMap mug a) : ∃ lc rc,
    bifByF mug b a = some (C lc rc) ∧ IsMap mug lc ∧ IsMap mug rc ∧
    (∀ k v, Get lc k v ↔ Get a k v ∧ k ≠ b ∧ gorF mug k b = true) ∧
    (∀ k v, Get rc k v ↔ Get a k v ∧ k ≠ b ∧ gorF mug b k = true) := by
  induction ha with
  | nil =>
    refine ⟨A 0, A 0, by simp [bifByF], IsMap.nil, IsMap.nil, ?_, ?_⟩ <;> intro k v <;>
      simp [Get_atom]
  | @node n q l r hl hr hL hR ihl ihr =>
    by_cases e : b = n
    · subst e
      refine ⟨l, r, by simp [bifByF], hl, hr, fun k v => ?_, fun k v => ?_⟩
      · rw [Get_node]
        constructor
        · intro hk; exact ⟨Or.inr (Or.inl hk), (hL k v hk).1, (hL k v hk).2.1⟩
        · rintro ⟨⟨h, _⟩ | h | h, ne, g⟩
          · exact absurd h ne
          · exact h
          · exact absurd (gorF_antisymm mug g (hR k v h).2.1) ne
      · rw [Get_node]
        constructor
        · intro hk; exact ⟨Or.inr (Or.inr hk), (hR k v hk).1, (hR k v hk).2.1⟩
        · rintro ⟨⟨h, _⟩ | h | h, ne, g⟩
          · exact absurd h ne
          · exact absurd (gorF_antisymm mug (hL k v h).2.1 g) ne
          · exact h
    · have e' : n ≠ b := fun h => e h.symm
      by_cases g : gorF mug b n = true
      · obtain ⟨lc, rc, h1, hlc, hrc, hLc, hRc⟩ := ihl
        refine ⟨lc, C (C n q) (C rc r), by simp [bifByF, e, g, h1], hlc,
          IsMap.node hrc hr (fun k v hk => hL k v ((hRc k v).1 hk).1) hR, fun k v => ?_, fun k v => ?_⟩
        · rw [hLc, Get_node]
          constructor
          · rintro ⟨h, ne, gk⟩; exact ⟨Or.inr (Or.inl h), ne, gk⟩
          · rintro ⟨⟨h, _⟩ | h | h, ne, gk⟩
            · rw [h] at gk; exact absurd (gorF_antisymm mug g gk) e
            · exact ⟨h, ne, gk⟩
            · exact absurd (gorF_antisymm mug g (gorF_trans mug (hR k v h).2.1 gk)) e
        · rw [Get_node, hRc, Get_node]
          constructor
          · rintro (⟨h, hv⟩ | ⟨h, ne, gk⟩ | h)
            · subst h hv; exact ⟨Or.inl ⟨rfl, rfl⟩, e', g⟩
            · exact ⟨Or.inr (Or.inl h), ne, gk⟩
            · refine ⟨Or.inr (Or.inr h), fun hk => ?_, gorF_trans mug g (hR k v h).2.1⟩
              have h2 := (hR k v h).2.1
              rw [hk] at h2
              exact e (gorF_antisymm mug g h2)
          · rintro ⟨h | h | h, ne, gk⟩
            · exact Or.inl h
            · exact Or.inr (Or.inl ⟨h, ne, gk⟩)
            · exact Or.inr (Or.inr h)
      · have g' : gorF mug n b = true := gorF_of_not mug g
        obtain ⟨lc, rc, h1, hlc, hrc, hLc, hRc⟩ := ihr
        refine ⟨C (C n q) (C l lc), rc, by simp [bifByF, e, g, h1],
          IsMap.node hl hlc hL (fun k v hk => hR k v ((hLc k v).1 hk).1), hrc, fun k v => ?_, fun k v => ?_⟩
        · rw [Get_node, hLc, Get_node]
          constructor
          · rintro (⟨h, hv⟩ | h | ⟨h, ne, gk⟩)
            · subst h hv; exact ⟨Or.inl ⟨rfl, rfl⟩, e', g'⟩
            · refine ⟨Or.inr (Or.inl h), fun hk => ?_, gorF_trans mug (hL k v h).2.1 g'⟩
              have h2 := (hL k v h).2.1
              rw [hk] at h2
              exact g h2
            · exact ⟨Or.inr (Or.inr h), ne, gk⟩
          · rintro ⟨h | h | h, ne, gk⟩
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr ⟨h, ne, gk⟩)
        · rw [hRc, Get_node]
          constructor
          · rintro ⟨h, ne, gk⟩; exact ⟨Or.inr (Or.inr h), ne, gk⟩
          · rintro ⟨⟨h, _⟩ | h | h, ne, gk⟩
            · rw [h] at gk; exact absurd gk g
            · exact absurd (gorF_trans mug gk (hL k v h).2.1) g
            · exact ⟨h, ne, gk⟩

/-- `+dif:by` on two maps: a map holding the pairs of `a` whose keys `b`
does not hold. -/
theorem difByF_spec {mug : Noun → Nat} {b : Noun} (hb : IsMap mug b) : ∀ (a : Noun), IsMap mug a →
    ∃ out, difByF mug a b = some out ∧ IsMap mug out ∧
      ∀ k v, Get out k v ↔ Get a k v ∧ ∀ w, ¬ Get b k w := by
  induction hb with
  | nil =>
    intro a ha
    exact ⟨a, by simp [difByF], ha, fun k v => by simp [Get_atom]⟩
  | @node nb qb lb rb hlb hrb hLb hRb ihl ihr =>
    intro a ha
    obtain ⟨lc, rc, h1, hlc, hrc, hLc, hRc⟩ := bifByF_spec nb ha
    obtain ⟨d, hd, hds, hdk⟩ := ihl lc hlc
    obtain ⟨e, he, hes, hek⟩ := ihr rc hrc
    have hap : Apart mug d e := by
      intro kl vl kr vr h1' h2'
      obtain ⟨_, n1, g1⟩ := (hLc kl vl).1 ((hdk kl vl).1 h1').1
      obtain ⟨_, n2, g2⟩ := (hRc kr vr).1 ((hek kr vr).1 h2').1
      refine ⟨gorF_trans mug g1 g2, fun hk => ?_⟩
      rw [hk] at g1
      exact n2 (gorF_antisymm mug g1 g2)
    obtain ⟨m, hm, hmm, hmk⟩ := mergeF_spec _ d e (Nat.lt_succ_self _) hds hes hap
    refine ⟨m, by simp [difByF, h1, hd, he, hm], hmm, fun k v => ?_⟩
    rw [hmk, hdk, hek, hLc, hRc]
    constructor
    · rintro (⟨⟨h, ne, g⟩, hn⟩ | ⟨⟨h, ne, g⟩, hn⟩)
      · refine ⟨h, fun w hw => ?_⟩
        rcases Get_node.1 hw with ⟨h', _⟩ | h' | h'
        · exact ne h'
        · exact hn w h'
        · exact ne (gorF_antisymm mug g (hRb k w h').2.1)
      · refine ⟨h, fun w hw => ?_⟩
        rcases Get_node.1 hw with ⟨h', _⟩ | h' | h'
        · exact ne h'
        · exact ne (gorF_antisymm mug (hLb k w h').2.1 g)
        · exact hn w h'
    · rintro ⟨h, hn⟩
      have ne : k ≠ nb := fun h' => hn qb (by rw [h']; exact Get.here)
      rcases gorF_total mug k nb with g | g
      · exact Or.inl ⟨⟨h, ne, g⟩, fun w h' => hn w (Get.left h')⟩
      · exact Or.inr ⟨⟨h, ne, g⟩, fun w h' => hn w (Get.right h')⟩

/-- `+dif:by` on two maps, in a context with `+gor` and `+mor`. -/
theorem dif_by {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx) (a b : Noun)
    (ha : IsMap mug a) (hb : IsMap mug b) :
    ∃ out, nock (C by.dif.battery (C b (C by.battery (C a ctx)))) by.dif.battery = some out ∧
      IsMap mug out ∧ ∀ k v, Get out k v ↔ Get a k v ∧ ∀ w, ¬ Get b k w := by
  obtain ⟨out, h, hs, hk⟩ := difByF_spec hb a ha
  exact ⟨out, dif_by_gate ctx hc a b out h, hs, hk⟩

end Hoon
end Formalization

end
