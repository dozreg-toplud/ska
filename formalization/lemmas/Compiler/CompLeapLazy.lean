import lemmas.Compiler.CompLeapPass
import lemmas.Compiler.CompSplit

/-!
# `+lazy-leap` of the door of `+comp`: the fold over the looks

`+lazy-leap` (door arm `442366`, `lzlBat`) folds the looks of the root sure
need with `+rep:in` and the gate `lzlG1`: a look under the part at `p` goes to
the looks of `by` as an axis under `s`, any other stays (`leapLok`).  Linked
here: the gate (`lzl_g1`, one step `llStep`) and the fold (`lzl_lok`), on
positive `p` and `s` and looks.  The rest of the battery (`+need-cut`,
`+need-from`, the turns over the forks `lzlG2` and the bonds `lzlG3`, the two
`+lazy-prune`) is linked in `Compiler/CompLeapLazyGate.lean` (`lzl_gate`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.Ana

set_option linter.unusedSimpArgs false

variable {ctx : Noun}

/-- One step of the fold of `leapLok`, on positive axes. -/
noncomputable def llStep (p s : Nat) (acc : CSet × CSet) (a : Nat) : CSet × CSet :=
  match (gep p a).join with
  | Option.none => (acc.1, HoonSet.put acc.2 a)
  | some d => (HoonSet.put acc.1 (pegF s d), acc.2)

theorem leapLok_pos (p s : Nat) (lok : CSet) (hp : p ≠ 0) (h0 : ∀ y ∈ HoonSet.toList lok, y ≠ 0) :
    leapLok p s lok = some ((HoonSet.toList lok).foldl (llStep p s) (HoonSet.empty, HoonSet.empty)) := by
  unfold leapLok
  generalize ((HoonSet.empty, HoonSet.empty) : CSet × CSet) = acc
  generalize HoonSet.toList lok = l at h0 ⊢
  induction l generalizing acc with
  | nil => rfl
  | cons y l ih =>
    have hy : y ≠ 0 := h0 y List.mem_cons_self
    rw [List.foldl_cons, List.foldl_cons, ← ih (llStep p s acc y)
      (fun z hz => h0 z (List.mem_cons_of_mem _ hz))]
    congr 1
    obtain ⟨b, r⟩ := acc
    simp only [Option.bind_some]
    rw [gep_pos hp hy]
    unfold llStep
    cases (gep p y).join <;> rfl

/-- The gate of the `+rep:in` of `+lazy-leap`, on a positive look. -/
theorem lzl_g1 (hc : CompIn ctx) (hl : CompLib ctx) (cutN L G : Noun) (p s a : Nat) (hp : p ≠ 0)
    (hs : s ≠ 0) (ha : a ≠ 0) (acc : CSet × CSet) :
    nock (C lzlG1 (C (C (A a) (ssN acc)) (C cutN (C lzlBat (C (C (A p) (C (A s) L))
      (C comp.door (C G ctx))))))) lzlG1 = some (ssN (llStep p s acc a)) := by
  obtain ⟨K, h7, hgp, _⟩ := hl
  have hl1 := cf_layer1 hc
  have hK2 := ci_layer2_K hc h7
  have hg := gep_gate K hK2 p a
  rw [gep_pos hp ha] at hg
  obtain ⟨b, r⟩ := acc
  unfold llStep
  nock_open lzlG1
  cases e : (gep p a).join with
  | none =>
    rw [e] at hg
    have hpt := cs_put_in r a
    simp [nock_exec, ssN, h7, hgp, gepArm, hg, unitNoun, hc, in_arm, in.arm_at, put_in_arm, hpt]
  | some d =>
    rw [e] at hg
    have hpg := pi_peg hs (gep_join_pos e)
    have hpb := cs_put_in b (pegF s d)
    simp [nock_exec, ssN, h7, hgp, gepArm, hg, unitNoun, hc, in_arm, in.arm_at, put_in_arm, hpb,
      hl1, peg_arm, peg.arm_at, hpg]

/-- **The `+rep:in` of `+lazy-leap`** over the looks of the root sure need is
`leapLok`, on positive `p`, `s` and looks. -/
theorem lzl_lok (hc : CompIn ctx) (hl : CompLib ctx) (cutN L G : Noun) (p s : Nat) (hp : p ≠ 0)
    (hs : s ≠ 0) (lok : CSet) (h0 : ∀ y ∈ HoonSet.toList lok, y ≠ 0) :
    nock (C by.rep.battery (C (C lzlG1 (C (C (A 0) (ssN (HoonSet.empty, HoonSet.empty)))
      (C cutN (C lzlBat (C (C (A p) (C (A s) L)) (C comp.door (C G ctx)))))))
      (C «in».battery (C (HoonSet.toNoun lok) layer2)))) by.rep.battery
      = (leapLok p s lok).map ssN := by
  have hrep := rep_gate_on ssN (fun n acc => match n with | Noun.atom y => llStep p s acc y | _ => acc)
    «in».battery layer2 lzlG1 (A 0) (C cutN (C lzlBat (C (C (A p) (C (A s) L)) (C comp.door (C G ctx)))))
    (HoonSet.toNoun lok) (cs_tree lok) (HoonSet.empty, HoonSet.empty) (by
      intro n hn acc
      rw [cs_preorder] at hn
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hn
      exact lzl_g1 hc hl _ _ _ p s y hp hs (h0 y hy) acc)
  rw [cs_preorder, List.foldl_map] at hrep
  rw [hrep, leapLok_pos p s lok hp h0]
  rfl

end Compiler
end Formalization
