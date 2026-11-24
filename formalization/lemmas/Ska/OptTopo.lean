import lemmas.Ska.Opt

/-!
# `+bb-topo` and `+rev-cfg`

`bbTopo`: the depth-first walk of `+bb-topo` from block `0`.  Each visit
puts its block in `saw`, folds (`+roll`, left to right) over `+get-jmps` of
its terminator, skips a target already in `saw`, and conses its own label in
front of the list the fold returns, so the result is the reverse post-order.
The Hoon has no fuel; `bbTopo n` is the Hoon whenever `n` exceeds the depth of
the walk (at most the number of blocks), and `none` also stands for the crash
of `got` on a missing target.  `saw` is a set in the Hoon and a list here; only
membership is used.

`revCfg`: `+rev-cfg`, a `+rep:by` over the blocks (in the order of
`MapKeys.keys`), which for each block `o` of `topo-set` adds `o` in front of
the list of every target of its jumps (`+add:ja`).  The order of each list
depends on the order of the traversal; its members with their multiplicities
do not.  `+remove-hops` uses a list only through `= ~[o]`, which depends on
the multiset alone, so the order of `+rep` does not matter there.

`TopoOK bl topo`: what the passes need of `topo` (and so of `rev`): no
duplicates, `0` first, every member a block, every block reachable from `0` a
member, and every jump of a member going to a later member.  It holds of the
result of `+bb-topo` on an acyclic CFG (not proved here).
-/

namespace Formalization
namespace SkaModel
namespace Opt

open Nock

variable {Map : Type → Type} [HoonMap Map]

/-- The walk of `+bb-topo`: `dfs bl n o (out, saw)` is `dfs-buc` at `o`. -/
def dfs (bl : Map Blob) : Nat → Nat → List Nat × List Nat → Option (List Nat × List Nat)
  | 0, _, _ => none
  | n + 1, o, (out, saw) =>
    (HoonMap.get bl o).bind fun b =>
      ((getJmps b.fin).foldlM (fun (acc : List Nat × List Nat) j =>
          if j.there ∈ acc.2 then some acc else dfs bl n j.there acc) (out, o :: saw)).map
        fun r => (o :: r.1, r.2)

/-- `+bb-topo`, with fuel. -/
def bbTopo (fuel : Nat) (bl : Map Blob) : Option (List Nat) :=
  (dfs bl fuel 0 ([], [])).map Prod.fst

/-- `+add:ja`: `o` in front of the list at `k`. -/
def addJa (acc : Map (List Nat)) (k o : Nat) : Map (List Nat) :=
  HoonMap.put acc k (o :: (HoonMap.get acc k).getD [])

/-- `+get:ja`. -/
def getJa (acc : Map (List Nat)) (k : Nat) : List Nat := (HoonMap.get acc k).getD []

/-- `+rev-cfg`, its `+rep:by` in the order of `MapKeys.keys`. -/
def revCfg [MapKeys Map] (bl : Map Blob) (topo : List Nat) : Map (List Nat) :=
  (MapKeys.keys bl).foldl (fun acc o =>
    match HoonMap.get bl o with
    | some v => if o ∈ topo then (getJmps v.fin).foldl (fun acc j => addJa acc j.there o) acc else acc
    | none => acc) HoonMap.empty

/-- The blocks reachable from `0`. -/
inductive Reach (bl : Map Blob) : Nat → Prop
  | zero : Reach bl 0
  | jump {o : Nat} {b : Blob} {j : Jmp} : Reach bl o → HoonMap.get bl o = some b → j ∈ getJmps b.fin →
      Reach bl j.there

/-- What the passes need of `topo`. -/
def TopoOK (bl : Map Blob) (topo : List Nat) : Prop :=
  topo.Nodup ∧ topo.head? = some 0 ∧ (∀ o ∈ topo, (HoonMap.get bl o).isSome) ∧
  (∀ o, Reach bl o → o ∈ topo) ∧
  (∀ (i o : Nat) (b : Blob) (j : Jmp), topo[i]? = some o → HoonMap.get bl o = some b → j ∈ getJmps b.fin →
    ∃ k : Nat, i < k ∧ topo[k]? = some j.there)

end Opt
end SkaModel
end Formalization
