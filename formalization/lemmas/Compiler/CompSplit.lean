import lemmas.Compiler.CompFrom

/-!
# `+split-sure` of the door of `+comp`

`+split-sure` folds the looks with `+rep:in` (arm `383` of the door `+in`
of layer 2), then runs `+split-need` (arm `88062` of the door).  The gate
of the `+rep:in` (`ssRepBat`, at axis `57213` of the battery, written
here and tied by `ss_rep_bat_at`) runs `+cap`, `+mas` of layer 1 and
`+put:in` of layer 2.  Side condition: no looked-at axis is `0`, where
the gate's `?<` crashes and the model's `splitLok` is `none` (the link
of that crash is not made here).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.Ana

variable {ctx : Noun} (x : GenRest)

/-- The gate of the `+rep:in` of `+split-sure`. -/
def ssRepBat : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 12)))) (C (C (A 0) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 3)) (C (A 0) (A 12)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 12)))) (C (C (A 1) (A 0)) (C (A 5) (C (C (A 1) (A 2)) (C (A 0) (A 12)))))))))) (C (C (C (A 0) (A 26)) (C (A 0) (A 27))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 22) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 2)) (C (A 0) (A 2)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0x17d6) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 84) (C (A 10) (C (C (A 6) (C (A 0) (A 58))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 47) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (A 0) (A 27))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 3)) (C (A 0) (A 2))))) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 26)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0x17d6) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 84) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 47) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2))))))))))))))))))))))))

theorem ss_rep_bat_at : slot? 57213 comp.split_sure.battery = some ssRepBat := by kernel_rfl

/-- One step of the fold of `splitLok` on a look that is not `0`. -/
noncomputable def ssStep (y : Nat) (s : CSet × CSet) : CSet × CSet :=
  if y = 1 ∨ y = 2 ∨ y = 3 then s
  else if cap y = 2 then (HoonSet.put s.1 (mas y), s.2) else (s.1, HoonSet.put s.2 (mas y))

theorem ss_splitLok (lok : CSet) (h0 : ∀ y ∈ HoonSet.toList lok, y ≠ 0) :
    splitLok lok = some ((HoonSet.toList lok).foldl (fun s y => ssStep y s)
      (HoonSet.empty, HoonSet.empty)) := by
  unfold splitLok
  generalize ((HoonSet.empty, HoonSet.empty) : CSet × CSet) = acc
  generalize HoonSet.toList lok = l at h0 ⊢
  induction l generalizing acc with
  | nil => rfl
  | cons y l ih =>
    have hy : y ≠ 0 := h0 y List.mem_cons_self
    have ih' := ih (ssStep y acc) (fun z hz => h0 z (List.mem_cons_of_mem _ hz))
    rw [List.foldl_cons, List.foldl_cons, ← ih']
    congr 1
    obtain ⟨h, t⟩ := acc
    unfold ssStep
    by_cases e : y = 1 ∨ y = 2 ∨ y = 3
    · simp [e, hy]
    · by_cases e2 : cap y = 2 <;> simp [e, e2, hy]

/-- The noun of a pair of sets. -/
noncomputable def ssN (s : CSet × CSet) : Noun := C (HoonSet.toNoun s.1) (HoonSet.toNoun s.2)

/-- One slam of the gate on a look that is not `0`. -/
theorem ss_gate (hc : CompIn ctx) (B P G : Noun) (y : Nat) (hy : y ≠ 0) (s : CSet × CSet) :
    nock (C ssRepBat (C (C (A y) (ssN s)) (C B (C P (C comp.door (C G ctx)))))) ssRepBat
      = some (ssN (ssStep y s)) := by
  have hl1 := cf_layer1 hc
  have har := cf_arith
  obtain ⟨h, t⟩ := s
  unfold ssRepBat
  by_cases e : y = 1 ∨ y = 2 ∨ y = 3
  · have hy0 : ¬ (0 = y) := fun h' => hy h'.symm
    rcases e with rfl | rfl | rfl <;> simp [nock_exec, ssStep, ssN]
  · have h2 : 2 ≤ y := by omega
    have hcap := cap_gate layer1 har.2.2.2 y h2
    have hmas := mas_gate layer1 har y h2
    have hph := put_in_gate layer2 gorIn_morIn_layer2 _ _ _ (cs_putInF h (masF y))
    have hpt := put_in_gate layer2 gorIn_morIn_layer2 _ _ _ (cs_putInF t (masF y))
    have hy0 : ¬ (0 = y) := fun h' => hy h'.symm
    have h1 : ¬ (1 = y) := by omega
    have h2' : ¬ (2 = y) := by omega
    have h3 : ¬ (3 = y) := by omega
    rcases capF_cases y h2 with hc2 | hc3
    · simp [nock_exec, ssStep, ssN, hl1, hc, hy0, h1, h2', h3, cap_arm, cap.arm_at, hcap, hc2,
        mas_arm, mas.arm_at, hmas, in_arm, in.arm_at, put_in_arm, hph, ← capF_eq_cap,
        ← masF_eq_mas, e]
    · simp [nock_exec, ssStep, ssN, hl1, hc, hy0, h1, h2', h3, cap_arm, cap.arm_at, hcap, hc3,
        mas_arm, mas.arm_at, hmas, in_arm, in.arm_at, put_in_arm, hpt, ← capF_eq_cap,
        ← masF_eq_mas, e]

end Compiler
end Formalization

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.Ana

variable {ctx : Noun} (x : GenRest)

theorem comp_split_need_at : slot? 55294 comp.door = some comp.split_need.arm := by kernel_rfl

/-- The arm `split-need` builds its gate. -/
theorem comp_split_need_arm (d : Noun) : nock d comp.split_need.arm =
    some (C comp.split_need.battery (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) d)) := by
  nock_open comp.split_need.arm; simp only [nock_exec]

variable {x} in
/-- `+split-sure`: the looks split by `+rep:in`, then `+split-need`, with no
look at axis `0`. -/
theorem comp_split_sure (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (sur : Sure CSet) (o : Nat)
    (h0 : ∀ y ∈ HoonSet.toList sur.lok, y ≠ 0) :
    nock (C comp.split_sure.battery (C (C sur.toNoun (A o)) (compCore g x ctx)))
      comp.split_sure.battery
      = (splitSure sur o g).map fun p => C (C p.1.1.toNoun p.1.2.toNoun) (genNoun p.2 x) := by
  obtain ⟨ned, lok⟩ := sur
  simp only at h0
  have hrep := rep_gate_on ssN (fun n s => match n with | Noun.atom y => ssStep y s | _ => s)
    in.battery layer2 ssRepBat (A 0)
    (C comp.split_sure.battery (C (C (C ned.toNoun (HoonSet.toNoun lok)) (A o))
      (C comp.door (C (genNoun g x) ctx))))
    (HoonSet.toNoun lok) (cs_tree lok) (HoonSet.empty, HoonSet.empty) (by
      intro n hn s
      rw [cs_preorder] at hn
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hn
      exact ss_gate hc _ _ _ y (h0 y hy) s)
  rw [cs_preorder, List.foldl_map] at hrep
  have hsl := ss_splitLok lok h0
  generalize (HoonSet.toList lok).foldl (fun s y => ssStep y s) (HoonSet.empty, HoonSet.empty) = F
    at hrep hsl
  obtain ⟨lh, lt⟩ := F
  simp only [ssN, HoonSet.toNoun_empty, ssRepBat] at hrep
  have hsn := comp_split_need x hc g ned o
  simp only [Sure.toNoun]
  nock_open comp.split_sure.battery
  cases e : splitNeed ned o g with
  | none =>
    rw [e] at hsn
    simp [nock_exec, splitSure, hsl, e, hc, in_arm, in.arm_at, in.rep.arm_at, rep_arm, hrep,
      comp_split_need_at, comp_split_need_arm, hsn]
  | some p =>
    obtain ⟨⟨nh, nt⟩, g'⟩ := p
    rw [e] at hsn
    simp [nock_exec, splitSure, hsl, e, hc, in_arm, in.arm_at, in.rep.arm_at, rep_arm, hrep,
      comp_split_need_at, comp_split_need_arm, hsn, Sure.toNoun]
