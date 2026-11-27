import lemmas.Compiler.OptLinkAlJImms
import lemmas.Compiler.OptLinkTrimLink
import lemmas.Compiler.OptLinkMiddleRd
import lemmas.Compiler.SkaCull

/-!
# `+alias`: the prelude (phase 6 of the plan, README Gaps 13)

```hoon
  =.  rev.gen  (~(run by rev) (bake silt (list @uwoo)))
```

`(bake silt (list @uwoo))` (`+bake`, arm `0xbef7f7` of `layer2`, its body
`alBakeB`) first computes the bunt `*a` of its mold `a = (list @uwoo)` by
running the mold (`+list`, arm `1407` of `layer1`, the mold's body
`alListMB`) on its own default sample `~`, which gives `~`; the gate it
makes, `alBakeInner`, slams `+silt` on its sample.  So the `+run:by` puts at
each label the set of the list of the jar (`run_by_P`, `silt_gate`).

* `al_revinit`: **the prelude makes `rev.gen` the jug of the model's start
  state**, `JugRel` to `fun o => dedupN ((get rev o).getD [])`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The elements of a list noun. -/
def nounList : Noun → List Noun
  | Noun.cell h t => h :: nounList t
  | _ => []

theorem nounList_listN : ∀ l : List Noun, nounList (listN l) = l
  | [] => rfl
  | x :: l => by rw [listN_cons]; simp only [nounList, nounList_listN l]

/-- The set `+silt` makes of a list noun. -/
def siltF (x : Noun) : Noun := (gasInF mugF (A 0) (nounList x)).getD (A 0)

theorem mem_dedupN (x : Nat) : ∀ l : List Nat, x ∈ Opt.dedupN l ↔ x ∈ l
  | [] => by simp [Opt.dedupN]
  | y :: l => by
    rw [show Opt.dedupN (y :: l) = if y ∈ Opt.dedupN l then Opt.dedupN l else y :: Opt.dedupN l from rfl]
    have ih := mem_dedupN x l
    by_cases h : y ∈ Opt.dedupN l
    · rw [if_pos h, ih]
      simp only [List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | h')
        · exact (mem_dedupN x l).1 h
        · exact h'
    · rw [if_neg h]
      simp [ih]

theorem siltF_saw (l : List Nat) :
    nock (C siltBattery (C (listNoun A l) layer2)) siltBattery = some (siltF (listNoun A l)) ∧
      SawRel (siltF (listNoun A l)) (Opt.dedupN l) := by
  obtain ⟨S, hg, hs, hh⟩ := gasInF_spec (mug := mugF) (l.map A) (A 0) isSet_nil
  have e : siltF (listNoun A l) = S := by
    unfold siltF
    rw [listNoun_map_listN, nounList_listN, hg]
    rfl
  rw [e, listNoun_map_listN]
  refine ⟨silt_gate _ _ hg, hs, fun k => ?_⟩
  rw [hh]
  simp only [List.mem_map, not_has_atom, or_false]
  constructor
  · rintro ⟨n, hn, rfl⟩; exact ⟨n, (mem_dedupN n l).2 hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩; exact ⟨n, (mem_dedupN n l).1 hn, rfl⟩

theorem bake_at : slot? 0xbef7f7 layer2 = some alBakeArm := by kernel_rfl

theorem list_at : slot? 1407 layer1 = some alListArm := by kernel_rfl

theorem bake_arm (d : Noun) : nock d alBakeArm = some (C alBakeB (C alBakeBunt d)) := by
  nock_open alBakeArm; simp only [nock_exec]

theorem list_arm (d : Noun) : nock d alListArm = some (C alListB (C (C (C (A 8) (C (C (A 0) (A 6))
    (C (A 8) (C (C (A 5) (C (C (A 0) (A 14)) (C (A 0) (A 2)))) (C (A 0) (A 6)))))) (C (A 0) d)) d)) := by
  nock_open alListArm; simp only [nock_exec]

theorem list_b (d : Noun) : nock d alListB = some (C alListMB (C (A 0) d)) := by
  nock_open alListB; simp only [nock_exec]

/-- The mold `(list item)` on its default sample `~` gives `~`. -/
theorem list_mb (d : Noun) : nock (C alListMB (C (A 0) d)) alListMB = some (A 0) := by
  nock_open alListMB; simp [nock_exec]

theorem bake_b (SG d : Noun) :
    nock (C alBakeB (C (C SG (C alListMB (C (A 0) d))) layer2)) alBakeB
      = some (C alBakeInner (C (A 0) (C alBakeB (C (C SG (C alListMB (C (A 0) d))) layer2)))) := by
  have h := list_mb d
  nock_open alBakeB
  simp [nock_exec, h]

/-- The gate of the `+run:by` on a list noun of atoms: `+silt`. -/
theorem bake_inner (d : Noun) (l : List Nat) :
    nock (C alBakeInner (C (listNoun A l) (C alBakeB (C (C (C siltBattery (C (A 0) layer2)) d) layer2))))
      alBakeInner = some (siltF (listNoun A l)) := by
  have h := (siltF_saw l).1
  nock_open alBakeInner
  simp [nock_exec, h]

/-- **The prelude**: `rev.gen` is the jug of `dedupN` of the lists of the jar `rev`. -/
theorem al_revinit (G NA BL TOPO : Noun) (rev : TreapMap mugF (List Nat)) :
    ∃ R0, nock (C G (C alBodyCut (C (C NA (C BL (C (jarN rev) TOPO))) optC))) alRevInit = some R0 ∧
      JugRel R0 (fun o => Opt.dedupN ((HoonMap.get rev o).getD [])) := by
  have hm : IsMap mugF (jarN rev) := isMap_hoonMap (listNoun A) rev
  have hp : ∀ k v, Get (jarN rev) k v → ∃ l : List Nat, v = listNoun A l := by
    intro k v hg
    obtain ⟨o, x, -, -, rfl⟩ := (get_hoonMap (listNoun A) rev k v).1 hg
    exact ⟨x, rfl⟩
  obtain ⟨out, hout, hmo, hgo⟩ := run_by_P layer2 alBakeInner (A 0)
    (C alBakeB (C (C (C siltBattery (C (A 0) layer2)) (C alListMB (C (A 0) (C alListB
      (C (C alUwooB (C (A 0) (C G (C alBodyCut (C (C NA (C BL (C (jarN rev) TOPO))) optC))))) layer1)))))
      layer2))
    (fun x => ∃ l : List Nat, x = listNoun A l) siltF
    (fun x ⟨l, hl⟩ => by subst hl; exact bake_inner _ l) hm hp
  refine ⟨out, ?_, hmo, fun p => ?_⟩
  · have hL := optC_layer2
    have hL1 := optC_layer1
    nock_open alRevInit
    generalize optC = OC at hL hL1 hout ⊢
    generalize jarN rev = REV at hout ⊢
    simp [nock_exec, hL, hL1, by.arm_at, by_arm, by.run.arm_at, by_run_arm, bake_at, bake_arm, list_at, list_arm,
      list_b, bake_b, silt_arm_at, silt_arm, hout]
  · cases e : HoonMap.get rev p with
    | none =>
      refine ⟨A 0, getF_none hmo (fun w hw => ?_), by simpa [unUnit, Opt.dedupN, e] using sawRel_nil⟩
      obtain ⟨v, hv, -⟩ := (hgo _ _).1 hw
      obtain ⟨o, x, eo, hx, -⟩ := (get_hoonMap (listNoun A) rev _ _).1 hv
      cases eo
      rw [e] at hx
      cases hx
    | some x =>
      have hv : Get (jarN rev) (A p) (listNoun A x) := (get_hoonMap (listNoun A) rev _ _).2 ⟨p, x, rfl, e, rfl⟩
      have hw : Get out (A p) (siltF (listNoun A x)) := (hgo _ _).2 ⟨_, hv, rfl⟩
      exact ⟨_, getF_some hmo hw, by simpa [unUnit, e] using (siltF_saw x).2⟩

/-- The noun of `gen` at the start of the walk: all empty, `rev` the jug `R0`, `folded` `|`. -/
def alGen0 (R0 : Noun) : Noun := C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C R0 (A 1)))))))

/-- **The gate body of `+alias`** pushes `gen` with `rev.gen` the jug of the
start state and runs the walk `alWalk` in the `|^` core. -/
theorem al_prelude (NA BL TOPO : Noun) (rev : TreapMap mugF (List Nat)) :
    ∃ R0, JugRel R0 (fun o => Opt.dedupN ((HoonMap.get rev o).getD [])) ∧
      nock (C alBodyCut (C (C NA (C BL (C (jarN rev) TOPO))) optC)) alBodyCut
        = nock (C alBat (C (alGen0 R0) (C alBodyCut (C (C NA (C BL (C (jarN rev) TOPO))) optC)))) alWalk := by
  obtain ⟨R0, hR, hJ⟩ := al_revinit alGenBunt NA BL TOPO rev
  refine ⟨R0, hJ, ?_⟩
  obtain ⟨a1, a2, a3, a4, a5, hX⟩ : ∃ a1 a2 a3 a4 a5, alBat = C a1 (C a2 (C a3 (C a4 (C a5 alWalk)))) :=
    ⟨_, _, _, _, _, rfl⟩
  nock_open alBodyCut
  rw [hX]
  unfold alGen0
  generalize C alBodyCut (C (C NA (C BL (C (jarN rev) TOPO))) optC) = S at hR ⊢
  simp [nock_exec, hR]

end Compiler
end Formalization
