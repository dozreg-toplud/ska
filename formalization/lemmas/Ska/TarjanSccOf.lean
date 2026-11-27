import lemmas.Ska.Tarjan
import lemmas.Hoon.Canon
import lemmas.Hoon.Maps
import lemmas.Hoon.MapModel
import lemmas.Hoon.Sets
import lemmas.Hoon.TapBy
import lemmas.Hoon.RepBy
import lemmas.Hoon.Mug

/-!
# The model of the cache miss of `++  scc-of` (track Q)

`desk/lib/nock-compilation.hoon`, `++  scc-of`, the branch where `sccs` has
no entry for `b`.  The model is on nouns, with the noun models of the arms
it calls (`getF` for `+get:by`/`+has:by`/`+gut:by`/`+got:by`, `putF` for
`+put:by`, `putInF` for `+put:in`, `tapList` for `+tap:in`, `preorder` for
the order of `+rep`), so that the pill's maps are the model's nouns:

* `scoCs CALLS SCCS k`: the kids of `k` in `sub`, `~(rep in (~(gut by calls)
  k ~))` with the gate that leaves out a callee `sccs` has
  (`scoCsStep`);
* `scoSub CALLS SCCS fuel q sub`: the trap that builds `sub` from `q = ~[b]`:
  `?~ q` returns `sub`; a key of `sub` is skipped; otherwise `i.q` gets its
  kids `cs` in `sub` and the kids go in front of `t.q` (`weld ~(tap in cs)
  t.q`).  The recursion is not structural: the fuel bounds the number of
  rounds of the trap.  A measure: the rounds that add a key are at most the
  number of bells (`b` and the callees in `calls`), every other round pops
  one element of `q`, and the pushes are at most the sum of the kid counts,
  so `2 + |keys| + Σ |cs|` rounds suffice;
* `scoSetN l`: the set noun of a list (`+put:in` from `~`), the noun of each
  set `+tarjan` returns (`isSet_ext`: a set noun is fixed by its members);
* `scoRoll SCCS Ss`: the `roll` over the components: every member `m` of a
  component `s` gets `m ↦ s` in `sccs` (`~(rep in s)` with `+put:by`);
* **`scoMiss B CALLS SCCS fuel`**: `sub`, then `tarjanM` of its pre-order
  graph (`tjGraph`), the sets, the roll, then `(~(got by sccs) b)`: the
  pair `[s sccs]`.
-/

namespace Formalization
namespace Tarjan

open Nock Hoon

/-- `(~(gut by calls) k ~)` on the lookup `out` of `k`. -/
def scoGut (out : Noun) : Noun :=
  if out = A 0 then A 0 else match out with | Noun.cell _ v => v | _ => A 0

/-- The gate of `cs`: `?:((~(has by sccs) c) acc (~(put in acc) c))`. -/
def scoCsStep (SCCS acc c : Noun) : Option Noun :=
  (getF mugF c SCCS).bind fun o => if o ≠ A 0 then some acc else putInF mugF c acc

/-- `cs`: the callees of `k` that `sccs` does not have, as a set noun. -/
def scoCs (CALLS SCCS k : Noun) : Option Noun :=
  (getF mugF k CALLS).bind fun out => (preorder (scoGut out)).foldlM (scoCsStep SCCS) (A 0)

/-- **The trap that builds `sub`.** -/
def scoSub (CALLS SCCS : Noun) : Nat → List Noun → Noun → Option Noun
  | 0, _, _ => none
  | _ + 1, [], sub => some sub
  | n + 1, x :: q, sub =>
    (getF mugF x sub).bind fun o =>
      if o ≠ A 0 then scoSub CALLS SCCS n q sub
      else (scoCs CALLS SCCS x).bind fun cs =>
        (putF mugF x cs sub).bind fun sub' => scoSub CALLS SCCS n (tapList cs ++ q) sub'

/-- The set noun of a list: `+put:in` from `~`. -/
def scoSetN (l : List Noun) : Option Noun := l.foldlM (fun a k => putInF mugF k a) (A 0)

/-- One step of the roll: every member `m` of the set `S` gets `m ↦ S`. -/
def scoRollStep (acc S : Noun) : Option Noun := (preorder S).foldlM (fun acc m => putF mugF m S acc) acc

/-- The roll over the components. -/
def scoRoll (SCCS : Noun) (Ss : List Noun) : Option Noun := Ss.foldlM scoRollStep SCCS

/-- `[(~(got by sccs) b) sccs]`. -/
def scoGot (B SC : Noun) : Option Noun :=
  match getF mugF B SC with
  | some (Noun.cell (Noun.atom 0) S) => some (C S SC)
  | _ => none

/-- **The model of the miss of `+scc-of`**: `[s sccs]`. -/
def scoMiss (B CALLS SCCS : Noun) (n : Nat) : Option Noun :=
  (scoSub CALLS SCCS n [B] (A 0)).bind fun SUB =>
    (tarjanM (tjGraphM SUB)).bind fun L =>
      (L.mapM scoSetN).bind fun Ss => (scoRoll SCCS Ss).bind fun SC' => scoGot B SC'
where
  /-- The model graph of a jug noun (`tjGraph` of `CompTarjanGate.lean`). -/
  tjGraphM (G : Noun) : Gr Noun := (preorder G).map fun x => match x with
    | Noun.cell v ks => (v, preorder ks)
    | Noun.atom _ => (A 0, [])

/-! ## Facts of the model -/

/-- `scoSetN` gives a set noun with the members of the list. -/
theorem scoSetN_spec : ∀ (l : List Noun), ∃ S, scoSetN l = some S ∧ IsSet mugF S ∧ ∀ k, Has S k ↔ k ∈ l := by
  intro l
  suffices h : ∀ (l : List Noun) (a : Noun), IsSet mugF a → ∃ S, l.foldlM (fun a k => putInF mugF k a) a = some S ∧
      IsSet mugF S ∧ ∀ k, Has S k ↔ Has a k ∨ k ∈ l by
    obtain ⟨S, h1, h2, h3⟩ := h l (A 0) (by simpa [IsSet] using (IsMap.nil : IsMap mugF (A 0)))
    refine ⟨S, h1, h2, fun k => (h3 k).trans ?_⟩
    have : ¬ Has (A 0) k := by unfold Has; exact Get_atom
    simp [this]
  intro l
  induction l with
  | nil => intro a ha; exact ⟨a, rfl, ha, fun k => by simp⟩
  | cons x xs ih =>
    intro a ha
    obtain ⟨o, ho, hs, hh⟩ := putInF_spec mugF a x ha
    obtain ⟨S, h1, h2, h3⟩ := ih o hs
    refine ⟨S, by simp [List.foldlM_cons, ho, h1], h2, fun k => ?_⟩
    rw [h3 k, hh k]
    simp only [List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h

end Tarjan
end Formalization
