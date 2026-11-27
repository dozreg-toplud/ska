import lemmas.Compiler.CompSccLoopSt
import lemmas.Hoon.IntIn

/-! # `kids` and `done` of `+compile-scc-in` on any SCC (README Gaps 21.12, track I)

* `csi_kids`: `kids`, the `+rep:in` over `scc` of
  `(~(put by acc) m (~(int in (~(gut by calls.long-ska) m ~)) scc))`, is a map that holds at each
  member `b` the set of its callees (`CalleeIn`) that are members.  The fold is `rep_gate_kinv`
  (`+rep` with an invariant on the accumulator indexed by the nodes visited), one step
  `kids_gate_step` (`+gut:by`, `+int:in`, `+put:by`).
* `csi_done_false`: `done` is `|` on an SCC that is not one bell, or one bell `n` with
  `~(has ju kids) n n`.
* `kids_self`: on `[n ~ ~]`, a self call in `calls.long-ska` gives `~(has ju kids) n n`. -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- `k` is a callee of `b` in `calls.long-ska`. -/
def CalleeIn (CALLS b k : Noun) : Prop := ∃ v, Get CALLS b v ∧ Has v k

/-- The gate of the `+rep:in` of `kids`: `(~(put by acc) m (~(int in (~(gut by calls) m ~)) scc))`. -/
def kidsGate : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 85) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 1531) (C (A 10) (C (C (A 6) (C (A 0) (A 2027))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 252))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))

/-- The context of that gate: the subject of `csiKids`. -/
def kidsBC (SCC LONG JH CA0 : Noun) : Noun := C (A 0) (C csiBody (C (csiSam SCC LONG JH CA0) compK))

/-- One step of the fold: the gate on `[m acc]`. -/
theorem kids_gate_step (SCC CODE JETS CALLS JH CA0 x N CB X out : Noun)
    (hgut : nock (C by.gut.battery (C (C x (A 0)) (C by.battery (C CALLS layer2)))) by.gut.battery = some CB)
    (hint : nock (C in.int.battery (C SCC (C in.battery (C CB layer2)))) in.int.battery = some X)
    (hput : nock (C by.put.battery (C (C x X) (C by.battery (C N layer2)))) by.put.battery = some out) :
    nock (C kidsGate (C (C x N) (kidsBC SCC (C CODE (C JETS CALLS)) JH CA0))) kidsGate = some out := by
  have hL := compK_layer2
  unfold kidsGate kidsBC csiSam
  generalize compK = KC at hL
  simp [nock_exec, hL, in.arm_at, in_arm, by.arm_at, by_arm, by.put.arm_at, put_arm, hput, in.int.arm_at,
    int_in_arm, hint, by.gut.arm_at, gut_arm, hgut]

/-- **`+rep` with an invariant**: `P vs N` of the accumulator `N` after the nodes `vs`; a step on a
node `x` from `P vs N` returns a noun with `P (vs ++ [x])`. -/
theorem rep_loop_kinv (P : List Noun → Noun → Prop) (B ctx bp e bc : Noun) :
    ∀ (a : Noun), Tree a → ∀ (vs : List Noun) (N : Noun), P vs N →
    (∀ x ∈ preorder a, ∀ vs N, P vs N → ∃ N', nock (C bp (C (C x N) bc)) bp = some N' ∧ P (vs ++ [x]) N') →
    ∃ N', nock (C by.rep.loop (C by.rep.battery (C (C bp (C (C e N) bc)) (C B (C a ctx)))))
      by.rep.loop = some N' ∧ P (vs ++ preorder a) N' := by
  intro a ha
  induction ha with
  | nil =>
    intro vs N hP _
    refine ⟨N, ?_, by simpa [preorder] using hP⟩
    nock_open by.rep.loop
    simp [nock_exec]
  | @node n l r _ _ ihl ihr =>
    intro vs N hP hf
    obtain ⟨N1, hn, hP1⟩ := hf n (by simp [preorder]) vs N hP
    obtain ⟨N2, hl, hP2⟩ := ihl (vs ++ [n]) N1 hP1 (fun x hx vs N h => hf x (by simp [preorder, hx]) vs N h)
    obtain ⟨N3, hr, hP3⟩ := ihr (vs ++ [n] ++ preorder l) N2 hP2
      (fun x hx vs N h => hf x (by simp [preorder, hx]) vs N h)
    refine ⟨N3, ?_, by simpa [preorder, List.append_assoc] using hP3⟩
    nock_open by.rep.loop
    simp [nock_exec, hn, hl, hr]

theorem rep_gate_kinv (P : List Noun → Noun → Prop) (B ctx bp e bc a : Noun) (ha : Tree a)
    (vs : List Noun) (N : Noun) (hP : P vs N)
    (hf : ∀ x ∈ preorder a, ∀ vs N, P vs N → ∃ N', nock (C bp (C (C x N) bc)) bp = some N' ∧ P (vs ++ [x]) N') :
    ∃ N', nock (C by.rep.battery (C (C bp (C (C e N) bc)) (C B (C a ctx)))) by.rep.battery = some N' ∧
      P (vs ++ preorder a) N' := by
  obtain ⟨N', h, hP'⟩ := rep_loop_kinv P B ctx bp e bc a ha vs N hP hf
  refine ⟨N', ?_, hP'⟩
  nock_open by.rep.battery
  simp only [nock_exec, h]

/-- `(~(gut by calls) x ~)` on a jug: a set whose members are the callees of `x`. -/
theorem kid_gut (CALLS x : Noun) (hcalls : IsMap mugF CALLS) (hjug : ∀ k v, Get CALLS k v → IsSet mugF v) :
    ∃ CB, nock (C by.gut.battery (C (C x (A 0)) (C by.battery (C CALLS layer2)))) by.gut.battery = some CB ∧
      IsSet mugF CB ∧ ∀ k, Has CB k ↔ CalleeIn CALLS x k := by
  by_cases h : ∃ v, Get CALLS x v
  · obtain ⟨v, hv⟩ := h
    have hg := getF_some hcalls hv
    have := gut_gate (mug := mugF) layer2 ⟨fall.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ x (A 0) CALLS
      (C (A 0) v) hg (Or.inr ⟨v, rfl⟩)
    refine ⟨v, by simpa using this, hjug x v hv, fun k => ⟨fun hk => ⟨v, hv, hk⟩, ?_⟩⟩
    rintro ⟨v', hv', hk⟩
    have hg' := getF_some hcalls hv'
    rw [hg] at hg'
    simp only [Option.some.injEq, Noun.cell.injEq, true_and] at hg'
    rw [hg']; exact hk
  · have hg := getF_none hcalls (fun v hv => h ⟨v, hv⟩)
    have := gut_gate (mug := mugF) layer2 ⟨fall.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ x (A 0) CALLS
      (A 0) hg (Or.inl rfl)
    refine ⟨A 0, by simpa using this, isSet_nil, fun k => ⟨fun hk => absurd hk not_has_atom, ?_⟩⟩
    rintro ⟨v, hv, _⟩; exact absurd ⟨v, hv⟩ h

/-- What `kids` holds at a member `b`: the set of the callees of `b` that are members. -/
def KidsAt (SCC CALLS N b : Noun) : Prop :=
  ∃ S, Get N b S ∧ IsSet mugF S ∧ ∀ k, Has S k ↔ Has SCC k ∧ CalleeIn CALLS b k

/-- **`kids` of any SCC** (the `+rep:in` over `scc` with `+put:by`, `+int:in`, `+gut:by`): a map
holding at each member `b` the set of the callees of `b` in `calls.long-ska` that are members. -/
theorem csi_kids (SCC CODE JETS CALLS JH CA0 : Noun) (hscc : IsSet mugF SCC) (hcalls : IsMap mugF CALLS)
    (hjug : ∀ k v, Get CALLS k v → IsSet mugF v) :
    ∃ KIDS, nock (C (A 0) (C csiBody (C (csiSam SCC (C CODE (C JETS CALLS)) JH CA0) compK))) csiKids = some KIDS ∧
      IsMap mugF KIDS ∧ ∀ b, Has SCC b → ∃ S, getF mugF b KIDS = some (C (A 0) S) ∧ IsSet mugF S ∧
        ∀ k, Has S k ↔ Has SCC k ∧ CalleeIn CALLS b k := by
  let P : List Noun → Noun → Prop := fun vs N => IsMap mugF N ∧ ∀ b ∈ vs, KidsAt SCC CALLS N b
  have hstep : ∀ x ∈ preorder SCC, ∀ vs N, P vs N → ∃ N', nock (C kidsGate (C (C x N)
      (kidsBC SCC (C CODE (C JETS CALLS)) JH CA0))) kidsGate = some N' ∧ P (vs ++ [x]) N' := by
    intro x _ vs N hP
    obtain ⟨CB, hgut, hcb, hcbk⟩ := kid_gut CALLS x hcalls hjug
    obtain ⟨X, hint, hxs, hxk⟩ := int_in (mug := mugF) layer2 gorIn_morIn_layer2 CB SCC hcb hscc
    obtain ⟨out, hput, hmap, hget⟩ := putF_spec mugF N x X hP.1
    have hpg := put_gate (mug := mugF) layer2 gorIn_morIn_layer2 x X N out hput
    refine ⟨out, kids_gate_step SCC CODE JETS CALLS JH CA0 x N CB X out hgut hint hpg, hmap, ?_⟩
    intro b hb
    by_cases e : b = x
    · subst e
      exact ⟨X, (hget b X).2 (Or.inl ⟨rfl, rfl⟩), hxs, fun k => by rw [hxk k, hcbk k]; exact And.comm⟩
    · have hbv : b ∈ vs := by simpa [e] using hb
      obtain ⟨S, hS, hss, hsk⟩ := hP.2 b hbv
      exact ⟨S, (hget b S).2 (Or.inr ⟨e, hS⟩), hss, hsk⟩
  obtain ⟨KIDS, hrep, hmap, hall⟩ := rep_gate_kinv P in.battery layer2 kidsGate
    (C (C (A 1) (A 0)) (C (A 0) (A 0))) (kidsBC SCC (C CODE (C JETS CALLS)) JH CA0) SCC (Tree.of_isSet hscc)
    [] (A 0) ⟨IsMap.nil, fun b hb => by simp at hb⟩ hstep
  refine ⟨KIDS, ?_, hmap, ?_⟩
  · have hL := compK_layer2
    unfold kidsGate kidsBC csiSam at hrep
    unfold csiKids csiSam
    generalize compK = KC at hL hrep
    simp [nock_exec, hL, in.arm_at, in_arm, in.rep.arm_at, rep_arm, by.arm_at, by_arm, hrep]
  · intro b hb
    have hbp : b ∈ preorder SCC := (mem_preorder_tapList SCC b).2 ((mem_tapList_set hscc b).2 hb)
    obtain ⟨S, hS, hss, hsk⟩ := hall b (by simpa using hbp)
    exact ⟨S, getF_some hmap hS, hss, hsk⟩

/-- **`done` is `|`** on an SCC that is not one bell, or one bell `n` with `~(has ju kids) n n`. -/
theorem csi_done_false (SCC LONG JH CA0 KIDS : Noun)
    (h : (∀ n, SCC ≠ C n (C (A 0) (A 0))) ∨ ∃ n, SCC = C n (C (A 0) (A 0)) ∧ juHasF mugF n n KIDS = some true) :
    nock (C KIDS (C (A 0) (C csiBody (C (csiSam SCC LONG JH CA0) compK)))) csiDone = some (A 1) := by
  rcases h with hne | ⟨n, rfl, hju⟩
  · unfold csiDone csiSam
    match SCC, hne with
    | Noun.atom m, _ => simp [nock_exec]
    | Noun.cell n (Noun.atom m), _ => simp [nock_exec]
    | Noun.cell n (Noun.cell l r), hne =>
      by_cases hl : l = A 0
      · subst hl
        have hr : r ≠ A 0 := fun hr => hne n (by rw [hr])
        simp [nock_exec, eqCode, Ne.symm hr]
      · simp [nock_exec, eqCode, Ne.symm hl]
  · have hL := compK_layer2
    have hjh := ju_has_gate layer2 juIn_layer2 n n KIDS true hju
    unfold csiDone csiSam
    generalize compK = KC at hL
    simp [nock_exec, hL, ju.arm_at, ju_arm, ju.has.arm_at, ju_has_arm, hjh]

/-- **A self call gives `~(has ju kids) n n`** on `kids` of `[n ~ ~]` (the spec of `csi_kids`). -/
theorem kids_self (n CALLS KIDS : Noun)
    (hk : ∀ b, Has (setOne n) b → ∃ S, getF mugF b KIDS = some (C (A 0) S) ∧ IsSet mugF S ∧
      ∀ k, Has S k ↔ Has (setOne n) k ∧ CalleeIn CALLS b k)
    (hself : CalleeIn CALLS n n) : juHasF mugF n n KIDS = some true := by
  have hn : Has (setOne n) n := has_node.2 (Or.inl rfl)
  obtain ⟨S, hg, hss, hsk⟩ := hk n hn
  obtain ⟨t, ht, htt⟩ := hasInF_spec mugF S n hss
  have : t = true := htt.2 ((hsk n).2 ⟨hn, hself⟩)
  subst this
  simp [juHasF, juGetF, hg, unUnit, ht]

end Compiler
end Formalization
