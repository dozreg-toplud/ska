import lemmas.Ska.TarjanSccOf
import lemmas.Ska.TarjanSound
import lemmas.Hoon.TapIn

/-!
# The miss of `+scc-of` returns, and what it writes (track Q)

On the noun model `scoMiss` (`TarjanSccOf.lean`), with `calls` and `sccs`
maps whose values are sets (`IsMap mugF`, set values) and `b` not a key of
`sccs` (the miss):

* `ScoKids CA SC x c`: `c` is a member of `x`'s set in `calls` and not a key
  of `sccs` (the gate of `cs`); `ScoReach` its reflexive-transitive closure;
* `preorder_keys_nodup`: the keys of the pre-order of a map are distinct;
* `scoCs_spec`: `cs` is the set of the `ScoKids` of `x`;
* `scoSub_ok2` (any result) and `scoSub_ok` (a result at the measure
  `scoMeas`): `sub` is `SubIs`: a map, its keys the nouns `ScoReach`able
  from `b`, the value at `x` the set of `x`'s `ScoKids`;
* `scoRoll_spec`: the roll puts `m ↦ S` for each member `m` of each set `S`
  of a list of disjoint sets, and keeps every other pair;
* `tjReach_sub`: on the graph of a `SubIs` jug, `TjReach` from a key is
  `ScoReach`;
* **`scoMiss_total`**: the miss returns at the fuel `scoFuel`;
* **`scoMiss_spec`**: whenever it returns, it gives `[S sccs']`: `sccs'` a
  map with the old pairs, and on each new key `m` (the nouns `ScoReach`able
  from `b`) the set of the `x` with `ScoReach m x` and `ScoReach x m`; `S`
  is `b`'s.
-/

namespace Formalization
namespace Tarjan

open Nock Hoon

set_option linter.unusedSectionVars false

/-! ## Keys of a map -/

/-- **The keys of the pre-order of a map are distinct.** -/
theorem preorder_keys_nodup {mug : Noun → Nat} {a : Noun} (h : IsMap mug a) (f : Noun → Noun)
    (hf : ∀ k v, f (C k v) = k) : ((preorder a).map f).Nodup := by
  induction h with
  | nil => simp [preorder]
  | @node p q l r hl hr hL hR ihl ihr =>
    rw [preorder_node, List.map_cons, List.map_append, List.nodup_cons, List.nodup_append]
    refine ⟨?_, ihl, ihr, ?_⟩
    · intro hm
      rcases List.mem_append.1 hm with hm | hm
      · obtain ⟨x, hx, e⟩ := List.mem_map.1 hm
        obtain ⟨k, v, rfl, hg⟩ := (mem_preorder hl x).1 hx
        rw [hf, hf] at e
        exact (hL k v hg).1 e
      · obtain ⟨x, hx, e⟩ := List.mem_map.1 hm
        obtain ⟨k, v, rfl, hg⟩ := (mem_preorder hr x).1 hx
        rw [hf, hf] at e
        exact (hR k v hg).1 e
    · intro a ha b hb e
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
      obtain ⟨k, v, rfl, hg⟩ := (mem_preorder hl x).1 hx
      obtain ⟨k', v', rfl, hg'⟩ := (mem_preorder hr y).1 hy
      rw [hf, hf] at e
      subst e
      have h1 := hL k v hg
      have h2 := hR k v' hg'
      exact h1.1 (gorF_antisymm mug h1.2.1 h2.2.1)

theorem mem_preorder_set {mug : Noun → Nat} {a : Noun} (h : IsSet mug a) (x : Noun) :
    x ∈ preorder a ↔ Has a x :=
  (mem_preorder_tapList a x).trans (mem_tapList_set h x)

/-- On a map, `getF` returns. -/
theorem getF_map {mug : Noun → Nat} {a : Noun} (h : IsMap mug a) (k : Noun) :
    (∃ v, Get a k v ∧ getF mug k a = some (C (A 0) v)) ∨ ((∀ v, ¬ Get a k v) ∧ getF mug k a = some (A 0)) := by
  by_cases e : ∃ v, Get a k v
  · obtain ⟨v, hv⟩ := e
    exact Or.inl ⟨v, hv, getF_some h hv⟩
  · exact Or.inr ⟨fun v hv => e ⟨v, hv⟩, getF_none h fun v hv => e ⟨v, hv⟩⟩

theorem getF_nil_iff {mug : Noun → Nat} {a k : Noun} (h : IsMap mug a) :
    getF mug k a = some (A 0) ↔ ∀ v, ¬ Get a k v := by
  rcases getF_map h k with ⟨v, hv, e⟩ | ⟨hn, e⟩
  · rw [e]
    constructor
    · intro h'; cases h'
    · intro h'; exact absurd hv (h' v)
  · rw [e]; exact ⟨fun _ => hn, fun _ => rfl⟩

/-! ## The edges of `sub` -/

/-- `c` is a kid of `x` in `sub`: a member of `x`'s set in `calls`, not a key
of `sccs`. -/
def ScoKids (CA SC x c : Noun) : Prop := (∃ v, Get CA x v ∧ Has v c) ∧ ∀ w, ¬ Get SC c w

inductive ScoReach (CA SC : Noun) : Noun → Noun → Prop
  | refl (a : Noun) : ScoReach CA SC a a
  | step {a b c : Noun} : ScoKids CA SC a b → ScoReach CA SC b c → ScoReach CA SC a c

theorem ScoReach.trans {CA SC a b c : Noun} (h1 : ScoReach CA SC a b) (h2 : ScoReach CA SC b c) :
    ScoReach CA SC a c := by
  induction h1 with
  | refl => exact h2
  | step e _ ih => exact ScoReach.step e (ih h2)

theorem ScoReach.tail {CA SC a b c : Noun} (h1 : ScoReach CA SC a b) (e : ScoKids CA SC b c) :
    ScoReach CA SC a c := h1.trans (ScoReach.step e (ScoReach.refl c))

/-- The hypotheses on `calls` and `sccs`: maps with set values. -/
structure ScoOK (CA SC : Noun) : Prop where
  ca : IsMap mugF CA
  caSet : ∀ k v, Get CA k v → IsSet mugF v
  sc : IsMap mugF SC

/-- **`cs`** is the set of the kids of `x`. -/
theorem scoCs_spec {CA SC : Noun} (hO : ScoOK CA SC) (x : Noun) :
    ∃ cs, scoCs CA SC x = some cs ∧ IsSet mugF cs ∧ ∀ c, Has cs c ↔ ScoKids CA SC x c := by
  -- the fold over a list of candidates
  have fold : ∀ (l : List Noun) (acc : Noun), IsSet mugF acc → ∃ cs, l.foldlM (scoCsStep SC) acc = some cs ∧
      IsSet mugF cs ∧ ∀ c, Has cs c ↔ Has acc c ∨ (c ∈ l ∧ ∀ w, ¬ Get SC c w) := by
    intro l
    induction l with
    | nil => intro acc ha; exact ⟨acc, rfl, ha, fun c => by simp⟩
    | cons y ys ih =>
      intro acc ha
      rcases getF_map hO.sc y with ⟨w, hw, e⟩ | ⟨hn, e⟩
      · have hs : scoCsStep SC acc y = some acc := by
          simp [scoCsStep, e]
        obtain ⟨cs, h1, h2, h3⟩ := ih acc ha
        refine ⟨cs, by simp [List.foldlM_cons, hs, h1], h2, fun c => ?_⟩
        rw [h3 c]
        constructor
        · rintro (h | ⟨h, h'⟩)
          · exact Or.inl h
          · exact Or.inr ⟨List.mem_cons_of_mem _ h, h'⟩
        · rintro (h | ⟨h, h'⟩)
          · exact Or.inl h
          · rcases List.mem_cons.1 h with rfl | h
            · exact absurd hw (h' w)
            · exact Or.inr ⟨h, h'⟩
      · obtain ⟨o, ho, hos, hoh⟩ := putInF_spec mugF acc y ha
        have hs : scoCsStep SC acc y = some o := by
          simp [scoCsStep, e, ho]
        obtain ⟨cs, h1, h2, h3⟩ := ih o hos
        refine ⟨cs, by simp [List.foldlM_cons, hs, h1], h2, fun c => ?_⟩
        rw [h3 c, hoh c]
        constructor
        · rintro ((rfl | h) | ⟨h, h'⟩)
          · exact Or.inr ⟨List.mem_cons_self, hn⟩
          · exact Or.inl h
          · exact Or.inr ⟨List.mem_cons_of_mem _ h, h'⟩
        · rintro (h | ⟨h, h'⟩)
          · exact Or.inl (Or.inr h)
          · rcases List.mem_cons.1 h with rfl | h
            · exact Or.inl (Or.inl rfl)
            · exact Or.inr ⟨h, h'⟩
  have h0 : IsSet mugF (A 0) := by simpa [IsSet] using (IsMap.nil : IsMap mugF (A 0))
  have hn0 : ∀ c, ¬ Has (A 0) c := fun c => by unfold Has; exact Get_atom
  rcases getF_map hO.ca x with ⟨v, hv, e⟩ | ⟨hn, e⟩
  · have hvs := hO.caSet x v hv
    obtain ⟨cs, h1, h2, h3⟩ := fold (preorder v) (A 0) h0
    have hg : scoGut (C (A 0) v) = v := by simp [scoGut]
    refine ⟨cs, by simp [scoCs, e, hg, h1], h2, fun c => ?_⟩
    rw [h3 c, mem_preorder_set hvs]
    constructor
    · rintro (h | ⟨h, h'⟩)
      · exact absurd h (hn0 c)
      · exact ⟨⟨v, hv, h⟩, h'⟩
    · rintro ⟨⟨v', hv', h⟩, h'⟩
      have : v' = v := Get.unique hO.ca hv' hv
      subst this
      exact Or.inr ⟨h, h'⟩
  · refine ⟨A 0, by simp [scoCs, e, scoGut, preorder], h0, fun c => ?_⟩
    constructor
    · intro h; exact absurd h (hn0 c)
    · rintro ⟨⟨v, hv, _⟩, _⟩; exact absurd hv (hn v)

/-! ## `sub` -/

/-- **What `sub` is**: a map, its keys the nouns reachable from `B`, the
value at a key the set of its kids. -/
structure SubIs (CA SC B SUB : Noun) : Prop where
  map : IsMap mugF SUB
  val : ∀ k v, Get SUB k v → IsSet mugF v ∧ ∀ c, Has v c ↔ ScoKids CA SC k c
  keys : ∀ k, (∃ v, Get SUB k v) ↔ ScoReach CA SC B k

/-- The invariant of the trap that builds `sub`. -/
structure SubInv (CA SC B : Noun) (q : List Noun) (SUB : Noun) : Prop where
  map : IsMap mugF SUB
  val : ∀ k v, Get SUB k v → IsSet mugF v ∧ ∀ c, Has v c ↔ ScoKids CA SC k c
  reach : ∀ k v, Get SUB k v → ScoReach CA SC B k
  qreach : ∀ x ∈ q, ScoReach CA SC B x
  clo : ∀ k v, Get SUB k v → ∀ c, ScoKids CA SC k c → (∃ w, Get SUB c w) ∨ c ∈ q
  root : (∃ v, Get SUB B v) ∨ B ∈ q

theorem subInv_init (CA SC B : Noun) : SubInv CA SC B [B] (A 0) :=
  ⟨IsMap.nil, fun _ _ h => absurd h Get_atom, fun _ _ h => absurd h Get_atom,
    fun x hx => by rw [List.mem_singleton.1 hx]; exact ScoReach.refl _, fun _ _ h => absurd h Get_atom,
    Or.inr List.mem_cons_self⟩

theorem subInv_pop {CA SC B x SUB : Noun} {q : List Noun} (h : SubInv CA SC B (x :: q) SUB) {v : Noun}
    (hx : Get SUB x v) : SubInv CA SC B q SUB where
  map := h.map
  val := h.val
  reach := h.reach
  qreach := fun y hy => h.qreach y (List.mem_cons_of_mem _ hy)
  clo := fun k w hk c hc => by
    rcases h.clo k w hk c hc with h1 | h1
    · exact Or.inl h1
    · rcases List.mem_cons.1 h1 with rfl | h1
      · exact Or.inl ⟨v, hx⟩
      · exact Or.inr h1
  root := by
    rcases h.root with h1 | h1
    · exact Or.inl h1
    · rcases List.mem_cons.1 h1 with rfl | h1
      · exact Or.inl ⟨v, hx⟩
      · exact Or.inr h1

theorem subInv_push {CA SC B x SUB cs SUB' : Noun} {q : List Noun} (h : SubInv CA SC B (x :: q) SUB)
    (hcs : IsSet mugF cs) (hcm : ∀ c, Has cs c ↔ ScoKids CA SC x c)
    (hput : ∀ k' v', Get SUB' k' v' ↔ (k' = x ∧ v' = cs) ∨ (k' ≠ x ∧ Get SUB k' v')) (hm : IsMap mugF SUB') :
    SubInv CA SC B (tapList cs ++ q) SUB' where
  map := hm
  val := fun k v hk => by
    rcases (hput k v).1 hk with ⟨rfl, rfl⟩ | ⟨_, hk⟩
    · exact ⟨hcs, hcm⟩
    · exact h.val k v hk
  reach := fun k v hk => by
    rcases (hput k v).1 hk with ⟨rfl, rfl⟩ | ⟨_, hk⟩
    · exact h.qreach k List.mem_cons_self
    · exact h.reach k v hk
  qreach := fun y hy => by
    rcases List.mem_append.1 hy with hy | hy
    · have := (hcm y).1 ((mem_tapList_set hcs y).1 hy)
      exact (h.qreach x List.mem_cons_self).tail this
    · exact h.qreach y (List.mem_cons_of_mem _ hy)
  clo := fun k v hk c hc => by
    have old : ∀ w, Get SUB c w → ∃ w, Get SUB' c w := fun w hw => by
      by_cases e : c = x
      · exact ⟨cs, (hput c cs).2 (Or.inl ⟨e, rfl⟩)⟩
      · exact ⟨w, (hput c w).2 (Or.inr ⟨e, hw⟩)⟩
    rcases (hput k v).1 hk with ⟨rfl, rfl⟩ | ⟨_, hk⟩
    · exact Or.inr (List.mem_append_left _ ((mem_tapList_set hcs c).2 ((hcm c).2 hc)))
    · rcases h.clo k v hk c hc with ⟨w, hw⟩ | h1
      · exact Or.inl (old w hw)
      · rcases List.mem_cons.1 h1 with rfl | h1
        · exact Or.inl ⟨cs, (hput c cs).2 (Or.inl ⟨rfl, rfl⟩)⟩
        · exact Or.inr (List.mem_append_right _ h1)
  root := by
    rcases h.root with ⟨w, hw⟩ | h1
    · by_cases e : B = x
      · exact Or.inl ⟨cs, (hput B cs).2 (Or.inl ⟨e, rfl⟩)⟩
      · exact Or.inl ⟨w, (hput B w).2 (Or.inr ⟨e, hw⟩)⟩
    · rcases List.mem_cons.1 h1 with rfl | h1
      · exact Or.inl ⟨cs, (hput B cs).2 (Or.inl ⟨rfl, rfl⟩)⟩
      · exact Or.inr (List.mem_append_right _ h1)

theorem subIs_of_inv {CA SC B SUB : Noun} (h : SubInv CA SC B [] SUB) : SubIs CA SC B SUB where
  map := h.map
  val := h.val
  keys := fun k => by
    constructor
    · rintro ⟨v, hv⟩; exact h.reach k v hv
    · intro hr
      -- every reachable noun is a key: induction from the root
      have key : ∀ a c, ScoReach CA SC a c → (∃ v, Get SUB a v) → ∃ v, Get SUB c v := by
        intro a c hr
        induction hr with
        | refl => exact id
        | step e _ ih =>
          rintro ⟨v, hv⟩
          rcases h.clo _ v hv _ e with h1 | h1
          · exact ih h1
          · cases h1
      exact key B k hr (by rcases h.root with h1 | h1; exact h1; cases h1)

/-- **`sub`, for any result of the trap.** -/
theorem scoSub_ok2 {CA SC B : Noun} (hO : ScoOK CA SC) :
    ∀ n q SUB r, SubInv CA SC B q SUB → scoSub CA SC n q SUB = some r → SubIs CA SC B r
  | 0, _, _, _, _, h => by simp [scoSub] at h
  | n + 1, [], SUB, r, hI, h => by
    simp only [scoSub, Option.some.injEq] at h
    subst h
    exact subIs_of_inv hI
  | n + 1, x :: q, SUB, r, hI, h => by
    rcases getF_map hI.map x with ⟨v, hv, e⟩ | ⟨hn, e⟩
    · simp only [scoSub, e, Option.bind_some] at h
      rw [if_pos (by intro h'; cases h')] at h
      exact scoSub_ok2 hO n q SUB r (subInv_pop hI hv) h
    · simp only [scoSub, e, Option.bind_some] at h
      rw [if_neg (by simp)] at h
      obtain ⟨cs, hc1, hc2, hc3⟩ := scoCs_spec hO x
      obtain ⟨SUB', hp1, hp2, hp3⟩ := putF_spec mugF SUB x cs hI.map
      rw [hc1, Option.bind_some, hp1, Option.bind_some] at h
      exact scoSub_ok2 hO n _ SUB' r (subInv_push hI hc2 hc3 hp3 hp2) h

/-! ## The measure of the trap -/

/-- The candidates for keys of `sub`: `B` and the members of the sets of
`calls`. -/
def scoU (CA B : Noun) : List Noun :=
  B :: (preorder CA).flatMap fun x => match x with
    | Noun.cell _ v => preorder v
    | Noun.atom _ => []

/-- The number of kids `x` gets in `sub`. -/
def scoW (CA SC u : Noun) : Nat :=
  match scoCs CA SC u with
  | some cs => (tapList cs).length
  | none => 0

open Classical in
/-- **The measure of the trap**: for each candidate not yet a key, one and
its kids; and the length of the queue. -/
noncomputable def scoMeas (CA SC B : Noun) (q : List Noun) (SUB : Noun) : Nat :=
  ((scoU CA B).map fun u => if ∃ v, Get SUB u v then 0 else 1 + scoW CA SC u).sum + q.length

/-- **The fuel of the miss**. -/
noncomputable def scoFuel (CA SC B : Noun) : Nat := scoMeas CA SC B [B] (A 0) + 1

theorem reach_last {CA SC a c : Noun} (h : ScoReach CA SC a c) : c = a ∨ ∃ y, ScoKids CA SC y c := by
  induction h with
  | refl => exact Or.inl rfl
  | @step a b c e _ ih =>
    rcases ih with rfl | h
    · exact Or.inr ⟨a, e⟩
    · exact Or.inr h

theorem reach_mem_U {CA SC B x : Noun} (hO : ScoOK CA SC) (h : ScoReach CA SC B x) : x ∈ scoU CA B := by
  rcases reach_last h with rfl | ⟨y, ⟨v, hv, hm⟩, _⟩
  · exact List.mem_cons_self
  · refine List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨C y v, (mem_preorder hO.ca _).2 ⟨y, v, rfl, hv⟩, ?_⟩)
    exact (mem_preorder_set (hO.caSet y v hv) x).2 hm

theorem sum_map_mono {U : List Noun} {f g : Noun → Nat} (h : ∀ u ∈ U, g u ≤ f u) :
    (U.map g).sum ≤ (U.map f).sum := by
  induction U with
  | nil => simp
  | cons y U ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h y List.mem_cons_self
    have := ih fun u hu => h u (List.mem_cons_of_mem _ hu)
    omega

theorem sum_map_lt {U : List Noun} {f g : Noun → Nat} (h : ∀ u ∈ U, g u ≤ f u) {x : Noun} (hx : x ∈ U)
    {d : Nat} (hd : g x + d ≤ f x) : (U.map g).sum + d ≤ (U.map f).sum := by
  induction U with
  | nil => cases hx
  | cons y U ih =>
    simp only [List.map_cons, List.sum_cons]
    have hy := h y List.mem_cons_self
    have hm := sum_map_mono (U := U) (f := f) (g := g) fun u hu => h u (List.mem_cons_of_mem _ hu)
    rcases List.mem_cons.1 hx with rfl | hx
    · omega
    · have := ih (fun u hu => h u (List.mem_cons_of_mem _ hu)) hx
      omega

open Classical in
/-- **The trap returns** within its measure. -/
theorem scoSub_ok {CA SC B : Noun} (hO : ScoOK CA SC) :
    ∀ n q SUB, SubInv CA SC B q SUB → scoMeas CA SC B q SUB < n → ∃ r, scoSub CA SC n q SUB = some r
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, [], SUB, _, _ => ⟨SUB, rfl⟩
  | n + 1, x :: q, SUB, hI, hm => by
    rcases getF_map hI.map x with ⟨v, hv, e⟩ | ⟨hn, e⟩
    · simp only [scoSub, e, Option.bind_some]
      rw [if_pos (by intro h'; cases h')]
      refine scoSub_ok hO n q SUB (subInv_pop hI hv) ?_
      unfold scoMeas at hm ⊢
      simp only [List.length_cons] at hm
      omega
    · simp only [scoSub, e, Option.bind_some]
      rw [if_neg (by simp)]
      obtain ⟨cs, hc1, hc2, hc3⟩ := scoCs_spec hO x
      obtain ⟨SUB', hp1, hp2, hp3⟩ := putF_spec mugF SUB x cs hI.map
      rw [hc1, Option.bind_some, hp1, Option.bind_some]
      refine scoSub_ok hO n _ SUB' (subInv_push hI hc2 hc3 hp3 hp2) ?_
      have hw : scoW CA SC x = (tapList cs).length := by unfold scoW; rw [hc1]
      have hxU := reach_mem_U hO (hI.qreach x List.mem_cons_self)
      have hle := sum_map_lt (U := scoU CA B) (d := 1 + (tapList cs).length)
        (f := fun u => if ∃ v, Get SUB u v then 0 else 1 + scoW CA SC u)
        (g := fun u => if ∃ v, Get SUB' u v then 0 else 1 + scoW CA SC u)
        (fun u _ => by
          by_cases h1 : ∃ v, Get SUB' u v
          · simp only [h1, if_true]; exact Nat.zero_le _
          · have h2 : ¬ ∃ v, Get SUB u v := by
              rintro ⟨w, hw⟩
              apply h1
              by_cases e : u = x
              · exact ⟨cs, (hp3 u cs).2 (Or.inl ⟨e, rfl⟩)⟩
              · exact ⟨w, (hp3 u w).2 (Or.inr ⟨e, hw⟩)⟩
            simp only [h1, h2, if_false]; exact Nat.le_refl _)
        hxU (by
          have h1 : ∃ v, Get SUB' x v := ⟨cs, (hp3 x cs).2 (Or.inl ⟨rfl, rfl⟩)⟩
          have h2 : ¬ ∃ v, Get SUB x v := fun ⟨w, hw⟩ => hn w hw
          simp only [h1, h2, if_true, if_false, hw]; omega)
      unfold scoMeas at hm ⊢
      simp only [List.length_cons, List.length_append] at hm ⊢
      omega

/-- **`sub` is built, at the fuel `scoFuel`**, and it is `SubIs`. -/
theorem scoSub_total {CA SC B : Noun} (hO : ScoOK CA SC) :
    ∃ SUB, scoSub CA SC (scoFuel CA SC B) [B] (A 0) = some SUB ∧ SubIs CA SC B SUB := by
  obtain ⟨SUB, h⟩ := scoSub_ok hO (scoFuel CA SC B) [B] (A 0) (subInv_init CA SC B) (Nat.lt_succ_self _)
  exact ⟨SUB, h, scoSub_ok2 hO _ _ _ _ (subInv_init CA SC B) h⟩

end Tarjan
end Formalization
