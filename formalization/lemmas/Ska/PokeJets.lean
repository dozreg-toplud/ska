import lemmas.Ska.BakeGraph

/-!
# The `%jets` branch of `+poke`: which compiled forms it drops

`CompHyp.jets` (`PokeModel.lean`) asks that the `%jets` branch keep the
cache: every compiled form left in it is still the one the compiler gives
its bell after the hot jets change.  The forms it drops are those of
`+hot-stale`, and the need of a callee goes into the need of its caller, so
the set must be closed under callers in `calls.lon`.  This file models, arm
by arm, `+reverse-bell-graph` (`reverseGraph`), the loop of `+hot-stale`
(`staleLoop`, with fuel; its seeds, the bells of the rings whose drivers
differ and the bells that got a ring with a driver, are its argument
`seeds`), and `+del-bells` (`delBells`), and proves:

* `reverseGraph_has`: the reverse graph lists `c` as a caller of `b`
  exactly when `calls` lists `b` as a callee of `c`;
* `hotStale_closed`: the set `+hot-stale` returns has every seed and is
  closed under callers in `calls`;
* `delBells_get`: `+del-bells` drops exactly the bells of the set.

So the cache after `%jets` holds only forms of bells outside a set closed
under callers that contains every bell whose ring changed.  What is left of
`CompHyp.jets` is a property of the compile arms: the form the compiler
gives a bell depends on the hot jets only through the rings of the bell and
of its transitive callees in `calls.lon` (and `+ska-cole-settle` changes no
other ring).
-/

namespace Formalization
namespace SkaModel

open Nock Ana

namespace Jets

variable {M : Type → Type → Type} [Treap M]

/-- `~(put ju m) k v`. -/
def putJu (m : M Bell (M Bell Unit)) (k v : Bell) : M Bell (M Bell Unit) :=
  Treap.put m k (Treap.put (Treap.gut m k Treap.empty) v ())

/-- `~(has in (~(get ju m) k)) v`. -/
def hasJu (m : M Bell (M Bell Unit)) (k v : Bell) : Bool := Treap.has (Treap.gut m k Treap.empty) v

theorem hasJu_putJu (m : M Bell (M Bell Unit)) (k v b c : Bell) :
    hasJu (putJu m k v) b c = true ↔ hasJu m b c = true ∨ (b = k ∧ c = v) := by
  unfold hasJu putJu Treap.gut
  rw [Treap.get_put]
  by_cases e : b = k
  · subst e
    simp only [if_true, Option.getD_some, Treap.has, Treap.get_put]
    by_cases e2 : c = v
    · subst e2; simp
    · simp [e2]
  · simp [e]

/-- `+reverse-bell-graph`: callee to callers. -/
def reverseGraph (g : M Bell (M Bell Unit)) : M Bell (M Bell Unit) :=
  (Treap.rap g).foldl (fun acc e => (Treap.rap e.2).foldl (fun acc c => putJu acc c.1 e.1) acc) Treap.empty

theorem inner_has (m : Bell) : ∀ (cs : List (Bell × Unit)) (acc : M Bell (M Bell Unit)) (b c : Bell),
    hasJu (cs.foldl (fun acc c => putJu acc c.1 m) acc) b c = true ↔
      hasJu acc b c = true ∨ (c = m ∧ ∃ u, (b, u) ∈ cs)
  | [], acc, b, c => by simp
  | x :: cs, acc, b, c => by
    simp only [List.foldl_cons]
    rw [inner_has m cs, hasJu_putJu]
    constructor
    · rintro ((h | ⟨rfl, rfl⟩) | ⟨rfl, u, hu⟩)
      · exact Or.inl h
      · exact Or.inr ⟨rfl, x.2, List.mem_cons_self⟩
      · exact Or.inr ⟨rfl, u, List.mem_cons_of_mem _ hu⟩
    · rintro (h | ⟨rfl, u, hu⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp hu with e | hu
        · cases e; exact Or.inl (Or.inr ⟨rfl, rfl⟩)
        · exact Or.inr ⟨rfl, u, hu⟩

theorem outer_has : ∀ (l : List (Bell × M Bell Unit)) (acc : M Bell (M Bell Unit)) (b c : Bell),
    hasJu (l.foldl (fun acc e => (Treap.rap e.2).foldl (fun acc c => putJu acc c.1 e.1) acc) acc) b c = true ↔
      hasJu acc b c = true ∨ ∃ cs, (c, cs) ∈ l ∧ Treap.has cs b = true
  | [], acc, b, c => by simp
  | e :: l, acc, b, c => by
    simp only [List.foldl_cons]
    rw [outer_has l, inner_has]
    have hm : (∃ u, (b, u) ∈ Treap.rap e.2) ↔ Treap.has e.2 b = true := by
      rw [Bake.has_iff]
      exact ⟨fun ⟨u, hu⟩ => ⟨u, (Treap.mem_rap _ _ _).mp hu⟩, fun ⟨u, hu⟩ => ⟨u, (Treap.mem_rap _ _ _).mpr hu⟩⟩
    constructor
    · rintro ((h | ⟨rfl, hu⟩) | ⟨cs, hcs, hb⟩)
      · exact Or.inl h
      · exact Or.inr ⟨e.2, List.mem_cons_self, hm.mp hu⟩
      · exact Or.inr ⟨cs, List.mem_cons_of_mem _ hcs, hb⟩
    · rintro (h | ⟨cs, hcs, hb⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp hcs with e' | hcs
        · cases e'; exact Or.inl (Or.inr ⟨rfl, hm.mpr hb⟩)
        · exact Or.inr ⟨cs, hcs, hb⟩

/-- **The reverse graph lists the callers**: `c` is a caller of `b` in it
exactly when `calls` lists `b` as a callee of `c`. -/
theorem reverseGraph_has (g : M Bell (M Bell Unit)) (b c : Bell) :
    hasJu (reverseGraph g) b c = true ↔ hasJu g c b = true := by
  unfold reverseGraph
  rw [outer_has]
  unfold hasJu Treap.gut
  simp only [Treap.get_empty, Option.getD_none]
  constructor
  · rintro (h | ⟨cs, hcs, hb⟩)
    · simp [Treap.has, Treap.get_empty] at h
    · rw [(Treap.mem_rap _ _ _).mp hcs]; exact hb
  · intro h
    cases hg : Treap.get g c with
    | none => simp [hg, Treap.has, Treap.get_empty] at h
    | some cs =>
      rw [hg, Option.getD_some] at h
      exact Or.inr ⟨cs, (Treap.mem_rap _ _ _).mpr hg, h⟩

/-- The loop of `+hot-stale`, with fuel: the bells of the queue and their
transitive callers in `rev`. -/
def staleLoop (rev : M Bell (M Bell Unit)) : Nat → List Bell → M Bell Unit → Option (M Bell Unit)
  | 0, _, _ => none
  | _ + 1, [], out => some out
  | n + 1, b :: q, out =>
    if Treap.has out b then staleLoop rev n q out
    else staleLoop rev n ((Treap.tap (Treap.gut rev b Treap.empty)).map Prod.fst ++ q) (Treap.put out b ())

/-- `+hot-stale` from its seeds: the loop on the reverse graph of `calls`. -/
def hotStale (n : Nat) (calls : M Bell (M Bell Unit)) (seeds : List Bell) : Option (M Bell Unit) :=
  staleLoop (reverseGraph calls) n seeds Treap.empty

/-- The invariant of the loop: every caller of a bell of `out` is in `out`
or in the queue. -/
def Closed (rev : M Bell (M Bell Unit)) (out : M Bell Unit) (q : List Bell) : Prop :=
  ∀ b c, Treap.has out b = true → hasJu rev b c = true → Treap.has out c = true ∨ c ∈ q

theorem has_put_unit (s : M Bell Unit) (b c : Bell) :
    Treap.has (Treap.put s b ()) c = true ↔ c = b ∨ Treap.has s c = true := by
  simp only [Treap.has, Treap.get_put]
  by_cases e : c = b <;> simp [e]

theorem staleLoop_spec (rev : M Bell (M Bell Unit)) : ∀ (n : Nat) (q : List Bell) (out out' : M Bell Unit),
    Closed rev out q → staleLoop rev n q out = some out' →
      (∀ b ∈ q, Treap.has out' b = true) ∧ (∀ b, Treap.has out b = true → Treap.has out' b = true) ∧
        Closed rev out' []
  | 0, _, _, _, _, h => by simp [staleLoop] at h
  | n + 1, [], out, out', hc, h => by
    simp only [staleLoop, Option.some.injEq] at h
    subst h
    exact ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => h, hc⟩
  | n + 1, b :: q, out, out', hc, h => by
    simp only [staleLoop] at h
    split at h
    · rename_i hb
      have hc' : Closed rev out q := by
        intro x c hx hr
        rcases hc x c hx hr with h1 | h1
        · exact Or.inl h1
        · rcases List.mem_cons.mp h1 with rfl | h1
          · exact Or.inl hb
          · exact Or.inr h1
      obtain ⟨h1, h2, h3⟩ := staleLoop_spec rev n q out out' hc' h
      refine ⟨fun x hx => ?_, h2, h3⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h2 _ hb
      · exact h1 x hx
    · rename_i hb
      have hc' : Closed rev (Treap.put out b ()) ((Treap.tap (Treap.gut rev b Treap.empty)).map Prod.fst ++ q) := by
        intro x c hx hr
        rcases (has_put_unit out b x).mp hx with rfl | hx
        · refine Or.inr (List.mem_append_left _ ?_)
          obtain ⟨u, hu⟩ := (Bake.has_iff _ _).mp hr
          exact List.mem_map.mpr ⟨(c, u), (Treap.mem_tap _ _ _).mpr hu, rfl⟩
        · rcases hc x c hx hr with h1 | h1
          · exact Or.inl ((has_put_unit out b c).mpr (Or.inr h1))
          · rcases List.mem_cons.mp h1 with rfl | h1
            · exact Or.inl ((has_put_unit out c c).mpr (Or.inl rfl))
            · exact Or.inr (List.mem_append_right _ h1)
      obtain ⟨h1, h2, h3⟩ := staleLoop_spec rev n _ _ out' hc' h
      refine ⟨fun x hx => ?_, fun x hx => h2 x ((has_put_unit out b x).mpr (Or.inr hx)), h3⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h2 x ((has_put_unit out x x).mpr (Or.inl rfl))
      · exact h1 x (List.mem_append_right _ hx)

/-- **What `+hot-stale` returns has every seed and is closed under callers**
in `calls`. -/
theorem hotStale_closed {n : Nat} {calls : M Bell (M Bell Unit)} {seeds : List Bell} {out : M Bell Unit}
    (h : hotStale n calls seeds = some out) :
    (∀ b ∈ seeds, Treap.has out b = true) ∧
      ∀ b c, Treap.has out b = true → hasJu calls c b = true → Treap.has out c = true := by
  have hc0 : Closed (reverseGraph calls) Treap.empty seeds := by
    intro b c hb
    simp [Treap.has, Treap.get_empty] at hb
  obtain ⟨h1, -, h3⟩ := staleLoop_spec _ n seeds _ _ hc0 h
  refine ⟨h1, fun b c hb hcb => ?_⟩
  rcases h3 b c hb ((reverseGraph_has calls b c).mpr hcb) with h | h
  · exact h
  · cases h

/-- `+del-bells`. -/
def delBells {ν : Type} (m : M Bell ν) (s : M Bell Unit) : M Bell ν :=
  (Treap.rap s).foldl (fun m b => Treap.del m b.1) m

theorem delBells_go {ν : Type} : ∀ (l : List (Bell × Unit)) (m : M Bell ν) (b : Bell),
    Treap.get (l.foldl (fun m b => Treap.del m b.1) m) b = if b ∈ l.map Prod.fst then none else Treap.get m b
  | [], m, b => by simp
  | x :: l, m, b => by
    simp only [List.foldl_cons]
    rw [delBells_go l, Treap.get_del]
    by_cases e : b = x.1
    · subst e
      simp
    · have h' : b ∈ (x :: l).map Prod.fst ↔ b ∈ l.map Prod.fst := by
        rw [List.map_cons, List.mem_cons]
        exact ⟨fun h => h.resolve_left e, Or.inr⟩
      rw [if_neg e]
      by_cases hm : b ∈ l.map Prod.fst
      · rw [if_pos hm, if_pos (h'.mpr hm)]
      · rw [if_neg hm, if_neg (fun h => hm (h'.mp h))]

/-- **`+del-bells` drops exactly the bells of the set.** -/
theorem delBells_get {ν : Type} (m : M Bell ν) (s : M Bell Unit) (b : Bell) :
    Treap.get (delBells m s) b = if Treap.has s b = true then none else Treap.get m b := by
  unfold delBells
  rw [delBells_go]
  have : b ∈ (Treap.rap s).map Prod.fst ↔ Treap.has s b = true := by
    rw [Bake.has_iff, List.mem_map]
    exact ⟨fun ⟨⟨k, u⟩, hu, e⟩ => ⟨u, e ▸ (Treap.mem_rap _ _ _).mp hu⟩,
      fun ⟨u, hu⟩ => ⟨(b, u), (Treap.mem_rap _ _ _).mpr hu, rfl⟩⟩
  by_cases h : Treap.has s b = true
  · rw [if_pos (this.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (this.mp h')), if_neg h]

end Jets

end SkaModel
end Formalization
