import lemmas.Compiler.CompTarjanKid

/-!
# `+tarjan`: the trap `connect` against the model's `connect` (track Q)

* `TjFinIs`, `TjStIs`: the noun of `fin` (a list of sets) and of the whole
  state `gen` against `St Noun`;
* `TjGraphAt CTX Gm`: the context `[tjBat [g ana]]` (any noun with the hoon
  core at axis `32767`) holds at axis `6` a graph `g` with a root key (axis
  `24`: the bunt of `vertex` reads it) whose `+get:ju` on every key gives a
  set noun whose pre-order is the model graph's `kidsOf`;
* `tj_ksam`: the bunt of the kids gate's sample;
* `tj_kids_loop`: the `+rep:in` fold of the kids gate is `kidsLoop`, from
  the statement at the smaller fuel;
* **`tj_connect`**: at every fuel, whenever the model's `connect` returns,
  the trap `tjConn` returns the noun of the same `lowest` and state.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel Tarjan

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The noun of `fin`: a list of set nouns with the members of the model's lists. -/
def TjFinIs : Noun → List (List Noun) → Prop
  | FIN, [] => FIN = A 0
  | FIN, l :: ls => ∃ S REST, FIN = C S REST ∧ TjSet S (fun k => k ∈ l) ∧ TjFinIs REST ls

/-- The noun of the state `gen`. -/
def TjStIs (ACC : Noun) (s : St Noun) : Prop :=
  ∃ VIS CUR FIN, ACC = tjAccN (A s.idx) VIS (listNoun id s.stk) CUR FIN ∧ TjMapIs VIS s.vis ∧
    TjSet CUR (fun k => s.cur k = true) ∧ TjFinIs FIN s.fin

/-- The graph in the context. -/
def TjGraphAt (CTX : Noun) (Gm : Gr Noun) : Prop :=
  ∃ G K0, slot? 6 CTX = some G ∧ slot? 24 CTX = some K0 ∧
    ∀ k, ∃ KS, nock (C ju.get.battery (C k (C ju.battery (C G layer2)))) ju.get.battery = some KS ∧
      Tree KS ∧ preorder KS = kidsOf Gm k

/-- The sample bunt of the kids gate: `[[*vertex index] acc]`. -/
theorem tjKSam_eq : tjKSam = (C (C (A 7) (C (C (A 7) (C (C (A 0) (A 31)) (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1)
    (C (A 8) (C (C (A 0) (A 120)) (C (A 8) (C (C (A 5) (C (C (A 0) (A 14)) (C (A 0) (A 2)))) (C (A 0) (A 6)))))))
    (C (A 0) (A 1))))))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (C (A 0) (A 2)) (C (A 0) (A 61)))) := by kernel_rfl

theorem tj_ksam {CTX K0 : Noun} (h24 : slot? 24 CTX = some K0) (IX V KS ACC : Noun) :
    nock (C IX (tjConnCore V KS ACC CTX)) tjKSam = some (C K0 (C IX ACC)) := by
  have h : slot? 120 (C (A 0) (C (A 0) CTX)) = some K0 := by
    simpa [nock_exec] using h24
  rw [tjKSam_eq]
  simp [tjConnCore, nock_exec, h24]

/-- **The fold of the kids gate is `kidsLoop`.** -/
theorem tj_kids_loop {CTX : Noun} {Gm : Gr Noun} (hL : slot? 32767 CTX = some layer2) (hg : TjGraphAt CTX Gm)
    (n : Nat) (IX V0 KIDS0 ACC0 : Noun)
    (ih : ∀ v KS, Tree KS → preorder KS = kidsOf Gm v → ∀ s r, connect Gm n v (kidsOf Gm v) s = some r →
      ∀ ACC, TjStIs ACC s → ∃ ACC', TjStIs ACC' r.2 ∧ nock (tjConnCore v KS ACC CTX) tjConn = some (C (A r.1) ACC')) :
    ∀ ks lo s r, kidsLoop Gm (connect Gm n) ks lo s = some r → ∀ ACC, TjStIs ACC s →
      ∃ ACC', TjStIs ACC' r.2 ∧
        ks.foldlM (fun N x => nock (C tjKBat (C (C x N) (C IX (tjConnCore V0 KIDS0 ACC0 CTX)))) tjKBat)
          (C (A lo) ACC) = some (C (A r.1) ACC')
  | [], lo, s, r, h, ACC, hs => by
    simp only [kidsLoop, Option.some.injEq] at h
    subst h
    exact ⟨ACC, hs, rfl⟩
  | k :: ks, lo, s, r, h, ACC, hs => by
    obtain ⟨G, K0, hG, h24, hju⟩ := hg
    obtain ⟨VIS, CUR, FIN, rfl, hv, hc, hf⟩ := hs
    simp only [kidsLoop] at h
    cases hk : s.vis k with
    | some ki =>
      rw [hk] at h
      have hstep := tj_kvis hL IX V0 KIDS0 ACC0 s (listNoun id s.stk) FIN hv hc k lo ki hk
      have := tj_kids_loop hL ⟨G, K0, hG, h24, hju⟩ n IX V0 KIDS0 ACC0 ih ks _ s r h _
        ⟨VIS, CUR, FIN, rfl, hv, hc, hf⟩
      obtain ⟨ACC', h1, h2⟩ := this
      refine ⟨ACC', h1, ?_⟩
      simp only [List.foldlM_cons]
      unfold tjKCore at hstep
      rw [hstep]
      exact h2
    | none =>
      rw [hk] at h
      obtain ⟨KS, hks, htree, hpre⟩ := hju k
      cases hc1 : connect Gm n k (kidsOf Gm k) s with
      | none => rw [hc1] at h; cases h
      | some r1 =>
        rw [hc1] at h
        obtain ⟨lk, s1⟩ := r1
        obtain ⟨ACC1, hs1, hrun⟩ := ih k KS htree hpre s (lk, s1) hc1 _ ⟨VIS, CUR, FIN, rfl, hv, hc, hf⟩
        have hstep := tj_kunvis hL hG IX V0 KIDS0 ACC0 (A s.idx) (listNoun id s.stk) CUR FIN s.vis hv k lo hk
          hks hrun
        obtain ⟨ACC', h1, h2⟩ := tj_kids_loop hL ⟨G, K0, hG, h24, hju⟩ n IX V0 KIDS0 ACC0 ih ks _ s1 r h ACC1 hs1
        refine ⟨ACC', h1, ?_⟩
        simp only [List.foldlM_cons]
        unfold tjKCore at hstep
        rw [hstep]
        exact h2

/-- The `+rep:in` of `connect` over the kids. -/
theorem tj_kidsrep_run {CTX K0 : Noun} (hL : slot? 32767 CTX = some layer2) (h24 : slot? 24 CTX = some K0)
    (IX V KS ACC : Noun) (ht : Tree KS) :
    nock (C IX (tjConnCore V KS ACC CTX)) tjKidsRep
      = (preorder KS).foldlM (fun N x => nock (C tjKBat (C (C x N) (C IX (tjConnCore V KS ACC CTX)))) tjKBat)
          (C IX ACC) := by
  have hk := tj_ksam h24 IX V KS ACC
  have hr := tj_rep_gate in.battery layer2 tjKBat K0 (C IX ACC) (C IX (tjConnCore V KS ACC CTX)) KS ht
  have hk' := hk
  simp only [tjConnCore] at hk' hr
  rw [tjKidsRep_eq, tjKGate_eq]
  simp [tjConnCore, nock_exec, hL, in.arm_at, in_arm, in.rep.arm_at, rep_arm, hk', hr]

/-- The empty set. -/
theorem tjSet_nil : TjSet (A 0) fun k => k ∈ ([] : List Noun) :=
  ⟨by simpa [IsSet] using (IsMap.nil : IsMap mugF (A 0)), fun k => ⟨fun h => absurd h Get_atom, fun h => by simp at h⟩⟩

/-- **`connect` is the model's `connect`**: at every fuel, on a kid set
noun whose pre-order is the model's kids, whenever the model returns, the
trap returns the noun of the same `lowest` and state. -/
theorem tj_connect {CTX : Noun} {Gm : Gr Noun} (hL : slot? 32767 CTX = some layer2) (hg : TjGraphAt CTX Gm) :
    ∀ n v KS, Tree KS → ∀ s r, connect Gm n v (preorder KS) s = some r →
      ∀ ACC, TjStIs ACC s → ∃ ACC', TjStIs ACC' r.2 ∧ nock (tjConnCore v KS ACC CTX) tjConn = some (C (A r.1) ACC')
  | 0, v, KS, ht, s, r, h, ACC, hs => by simp [connect] at h
  | n + 1, v, KS, ht, s, r, h, ACC, hs => by
    obtain ⟨G, K0, hG, h24, hju⟩ := hg
    obtain ⟨VIS, CUR, FIN, rfl, hv, hc, hf⟩ := hs
    have ih : ∀ v KS, Tree KS → preorder KS = kidsOf Gm v → ∀ s r, connect Gm n v (kidsOf Gm v) s = some r →
        ∀ ACC, TjStIs ACC s → ∃ ACC', TjStIs ACC' r.2 ∧
          nock (tjConnCore v KS ACC CTX) tjConn = some (C (A r.1) ACC') := by
      intro v KS ht hpre s r h ACC hs
      rw [← hpre] at h
      exact tj_connect hL ⟨G, K0, hG, h24, hju⟩ n v KS ht s r h ACC hs
    obtain ⟨VIS1, CUR1, hv1, hc1, hen⟩ := tj_enter hL v KS FIN s hv hc
    simp only [connect] at h
    cases hk : kidsLoop Gm (connect Gm n) (preorder KS) s.idx (enter v s) with
    | none => rw [hk] at h; cases h
    | some p =>
      rw [hk] at h
      obtain ⟨lo, s2⟩ := p
      have hs1 : TjStIs (tjAccN (A (s.idx + 1)) VIS1 (listNoun id (v :: s.stk)) CUR1 FIN) (enter v s) :=
        ⟨VIS1, CUR1, FIN, rfl, hv1, hc1, hf⟩
      obtain ⟨ACC2, hs2, hkl⟩ := tj_kids_loop hL ⟨G, K0, hG, h24, hju⟩ n (A s.idx) v KS
        (tjAccN (A (s.idx + 1)) VIS1 (listNoun id (v :: s.stk)) CUR1 FIN) ih (preorder KS) s.idx (enter v s)
        (lo, s2) hk _ hs1
      have hkr := tj_kidsrep_run hL h24 (A s.idx) v KS (tjAccN (A (s.idx + 1)) VIS1 (listNoun id (v :: s.stk)) CUR1 FIN) ht
      rw [hkl] at hkr
      obtain ⟨VIS2, CUR2, FIN2, rfl, hv2, hc2, hf2⟩ := hs2
      simp only [tjConnCore, tjAccN] at hen hkr
      by_cases e : s.idx = lo
      · subst e
        simp only [if_true] at h
        have hp := tj_pop hL (A s.idx) (A s.idx) v KS (A s2.idx) VIS2 FIN2 s2.stk [] s2.cur (A 0) CUR2 tjSet_nil hc2
        revert hp
        cases hpl : popLoop v s2.stk [] s2.cur with
        | none => rw [hpl] at h; cases h
        | some q =>
          rw [hpl] at h
          obtain ⟨out, stk, cur⟩ := q
          simp only [Option.some.injEq] at h
          subst h
          rintro ⟨OUT', CUR', ho', hc', hpop⟩
          simp only [tjPopCore, tjConnCore, tjAccN] at hpop
          refine ⟨tjAccN (A s2.idx) VIS2 (listNoun id stk) CUR' (C OUT' FIN2),
            ⟨VIS2, CUR', C OUT' FIN2, rfl, hv2, hc', ⟨OUT', FIN2, rfl, ho', hf2⟩⟩, ?_⟩
          conv => lhs; rw [tjConn_eq]
          simp [tjConnCore, tjAccN, nock_exec, hen, hkr, tjAfter_eq, tjPopBr_eq, hpop]
      · simp only [e, if_false, Option.some.injEq] at h
        subst h
        refine ⟨tjAccN (A s2.idx) VIS2 (listNoun id s2.stk) CUR2 FIN2, ⟨VIS2, CUR2, FIN2, rfl, hv2, hc2, hf2⟩, ?_⟩
        conv => lhs; rw [tjConn_eq]
        simp [tjConnCore, tjAccN, nock_exec, hen, hkr, tjAfter_eq, e]

end Compiler
end Formalization
