import lemmas.Compiler.OptLinkAlState
import lemmas.Ska.OptAliasPerm
import lemmas.Ska.OptAliasPickRoot
import lemmas.Ska.OptAliasBrz

/-!
# `+alias`: the end of the walk, `pre` and `bob` (phases 7 and 11 of the plan, README Gaps 13)

```hoon
  ?~  topo  [folded.gen new.gen]
  =*  o  i.topo
  =/  pre=(list @uwoo)  ~(tap in (~(get ju rev.gen) o))
  ...
  =/  bob  (~(got by blocks) o)
```

* `al_end`: on `topo = ~` the walk returns `[folded new]` of the model's state.
* `al_pre`: **`pre` is a list of atoms with no duplicates and the members of
  `g.rev o`** (`+get:ju` on `JugRel`, `+tap:in`); `al_pre_perm`: with
  `RevNodup` of the model's state (`aliasM_inv`), it is a permutation of
  `g.rev o`, so the phases after it run the model on the Hoon's list and move
  to `g.rev o` by the `_perm` lemmas of `Ska/OptAliasPerm.lean`.
* `al_bob`: `bob` is the noun of the block `o` of the blocks.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- **The end of the walk**: `[folded.gen new.gen]`. -/
theorem al_end {g : Opt.AGen (TreapMap mugF)} {GEN : Noun} (hg : GenRel g GEN) (NA BL REV : Noun) :
    nock (alWS GEN NA BL REV (A 0)) alWalk = some (C (flag g.folded) (HoonMap.toNoun Blob.toNoun g.new)) := by
  obtain ⟨OLD, INFO, IMMS, LOC, IMML, R, rfl, -⟩ := hg
  unfold alWS genN
  nock_open alWalk
  simp [nock_exec]

/-- The elements of the `+tap:in` of a set of atoms are atoms. -/
theorem tapList_atoms {S : Noun} {l : List Nat} (hS : SawRel S l) :
    tapList S = ((tapList S).map OptDec.atomOf).map A := by
  rw [List.map_map]
  conv => lhs; rw [← List.map_id (tapList S)]
  apply List.map_congr_left
  intro x hx
  obtain ⟨n, -, rfl⟩ := (hS.2 x).1 ((mem_tapList_set hS.1 x).1 hx)
  rfl

/-- **`pre`**: `~(tap in (~(get ju rev.gen) o))` is a list of atoms with no
duplicates and exactly the members of `g.rev o`. -/
theorem al_pre {g : Opt.AGen (TreapMap mugF)} {GEN : Noun} (hg : GenRel g GEN) (NA BL REV T : Noun) (o : Nat) :
    ∃ pre : List Nat, nock (alWS GEN NA BL REV (C (A o) T)) alPre = some (listNoun A pre) ∧
      pre.Nodup ∧ ∀ x, x ∈ pre ↔ x ∈ g.rev o := by
  obtain ⟨OLD, INFO, IMMS, LOC, IMML, R, rfl, -, -, -, hR⟩ := hg
  obtain ⟨out, hgo, hS⟩ := hR.2 o
  have hju := ju_get_gate layer2 juIn_layer2' ju.battery (A o) R out hgo
  have htap : nock (C in.battery (C (unUnit out) layer2)) by.tap.arm = some (listN (tapList (unUnit out))) := by
    rw [tap_arm, tap_loop, show A 0 = listN [] from rfl, tapF_list (Tree.of_isSet hS.1), List.append_nil]
  have hks := tapList_atoms hS
  have hnd := tapList_set_nodup hS.1
  refine ⟨(tapList (unUnit out)).map OptDec.atomOf, ?_, ?_, fun x => ?_⟩
  · rw [listNoun_map_listN, ← hks]
    have hL := optC_layer2
    unfold alWS genN
    generalize optC = OC at hL
    generalize unUnit out = U at hju htap
    simp [nock_exec, alPre, hL, in.arm_at, in_arm, in.tap.arm_at, htap, ju.arm_at, ju_arm, ju.get.arm_at,
      ju_get_arm, hju]
  · rw [hks] at hnd
    exact (List.pairwise_map.1 hnd).imp fun h e => h (by rw [e])
  · have h1 := (mem_tapList_set hS.1 (A x)).trans (hS.2 (A x))
    rw [hks] at h1
    simp only [List.mem_map, Noun.atom.injEq, exists_eq_right] at h1
    simpa using h1

/-- With `RevNodup` of the model's state, `pre` is a permutation of `g.rev o`. -/
theorem al_pre_perm {g : Opt.AGen (TreapMap mugF)} {pre : List Nat} {o : Nat} (hn : Opt.RevNodup g.rev)
    (hd : pre.Nodup) (hm : ∀ x, x ∈ pre ↔ x ∈ g.rev o) : pre.Perm (g.rev o) :=
  Opt.perm_of_nodup hd (hn o) hm

/-- **`bob`**: `(~(got by blocks) o)` is the noun of the block. -/
theorem al_bob (X Y PRE GEN NA REV T : Noun) (bl : TreapMap mugF Blob) (o : Nat) :
    nock (C X (C Y (C PRE (alWS GEN NA (HoonMap.toNoun Blob.toNoun bl) REV (C (A o) T))))) alBob
      = (HoonMap.get bl o).map Blob.toNoun := by
  have hg := blocks_got bl o
  have hL := optC_layer2
  unfold alWS
  generalize optC = OC at hL
  generalize HoonMap.toNoun Blob.toNoun bl = BL at hg
  simp [nock_exec, alBob, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg]

end Compiler
end Formalization
