import lemmas.Compiler.CompTarjanConn

/-!
# `+tarjan`: the gate of the outer `+rep:by` and the whole battery (track Q)

* `tj_ostep`: the gate `tjOBat` of `~(rep by g)` on `[[v kids] acc]`: a
  visited `v` leaves `acc`, an unvisited one runs `connect` (`tj_connect`)
  and keeps its state (`=<  +`);
* `tj_outer`: the fold of that gate over the nodes of `g` is `outer`;
* **`tj_bat`**: the battery `tjBat` on the gate core `[tjBat [g ana]]`,
  whenever `tarjanM` of the model graph returns `L`, returns a list of set
  nouns with the members of `L` (`TjFinIs`), from three hypotheses on the
  noun `g`: `Tree g` with its nodes cells `[v kids]`, `kids` trees;
  `TjGraphAt` (the `+get:ju` of `g` is the model's `kidsOf`); the bunt of the
  rep gate's sample (`tjSamB`, the molds of `gen`, not linked) ends with
  the empty state.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel Tarjan

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- An entry of the model graph from a node `[v kids]` of the jug noun. -/
def tjEntry : Noun → Noun × List Noun
  | Noun.cell v ks => (v, preorder ks)
  | Noun.atom _ => (A 0, [])

/-- **The model graph of a jug noun**: its nodes in the pre-order of
`~(rep by g)`, each kid set in the pre-order of `~(rep in kids)`. -/
def tjGraph (G : Noun) : Gr Noun := (preorder G).map tjEntry

/-- **One step of the outer gate.** -/
theorem tj_ostep {CTX : Noun} {Gm : Gr Noun} (hL : slot? 32767 CTX = some layer2) (hg : TjGraphAt CTX Gm)
    (n : Nat) (v KS : Noun) (ht : Tree KS) (s : St Noun) (ACC : Noun) (hs : TjStIs ACC s) :
    ∀ r, outer Gm n [(v, preorder KS)] s = some r →
      ∃ ACC', TjStIs ACC' r ∧ nock (C tjOBat (C (C (C v KS) ACC) CTX)) tjOBat = some ACC' := by
  intro r h
  have hs0 := hs
  obtain ⟨VIS, CUR, FIN, rfl, hv, hc, hf⟩ := hs
  have hsg : SomeIn layer2 ∧ GorIn mugF layer2 := ⟨someIn_layer2, gorIn_morIn_layer2.1⟩
  simp only [outer] at h
  cases hk : s.vis v with
  | some i =>
    rw [hk] at h
    simp only [Option.some.injEq] at h
    subst h
    have hgv : Get VIS v (A i) := (hv.2 v (A i)).2 ⟨i, hk, rfl⟩
    have hh := has_gate layer2 hsg v VIS _ (getF_some hv.1 hgv)
    refine ⟨_, hs0, ?_⟩
    conv => lhs; arg 2; rw [tjOBat_eq]
    simp [tjHasV_eq, tjAccN, nock_exec, hL, by.arm_at, by_arm, by.has.arm_at, has_arm, hh, loob]
  | none =>
    rw [hk] at h
    have hn : ∀ u, ¬ Get VIS v u := fun u hu => by
      obtain ⟨i, hi, -⟩ := (hv.2 v u).1 hu
      rw [hk] at hi; cases hi
    have hh := has_gate layer2 hsg v VIS _ (getF_none hv.1 hn)
    cases hc1 : connect Gm n v (preorder KS) s with
    | none => rw [hc1] at h; cases h
    | some p =>
      rw [hc1] at h
      simp only [outer, Option.some.injEq] at h
      subst h
      obtain ⟨ACC', hs', hrun⟩ := tj_connect hL hg n v KS ht s p hc1 _ hs0
      refine ⟨ACC', hs', ?_⟩
      simp only [tjConnCore, tjAccN] at hrun
      conv => lhs; arg 2; rw [tjOBat_eq]
      simp [tjHasV_eq, tjElse_eq, tjAccN, nock_exec, hL, by.arm_at, by_arm, by.has.arm_at, has_arm, hh, loob, hrun]

/-- **The outer fold is `outer`.** -/
theorem tj_outer {CTX : Noun} {Gm : Gr Noun} (hL : slot? 32767 CTX = some layer2) (hg : TjGraphAt CTX Gm)
    (n : Nat) : ∀ (xs : List Noun), (∀ x ∈ xs, ∃ v KS, x = C v KS ∧ Tree KS) → ∀ s r,
      outer Gm n (xs.map tjEntry) s = some r → ∀ ACC, TjStIs ACC s →
      ∃ ACC', TjStIs ACC' r ∧ xs.foldlM (fun N x => nock (C tjOBat (C (C x N) CTX)) tjOBat) ACC = some ACC'
  | [], _, s, r, h, ACC, hs => by
    simp only [List.map_nil, outer, Option.some.injEq] at h
    subst h
    exact ⟨ACC, hs, rfl⟩
  | x :: xs, hx, s, r, h, ACC, hs => by
    obtain ⟨v, KS, rfl, ht⟩ := hx _ List.mem_cons_self
    have hxs : ∀ y ∈ xs, ∃ v KS, y = C v KS ∧ Tree KS := fun y hy => hx y (List.mem_cons_of_mem _ hy)
    simp only [List.map_cons, tjEntry] at h
    -- the first step, as `outer` on one entry
    have hsplit : ∃ s1, outer Gm n [(v, preorder KS)] s = some s1 ∧ outer Gm n (xs.map tjEntry) s1 = some r := by
      simp only [outer] at h
      cases hv : s.vis v with
      | some _ => rw [hv] at h; exact ⟨s, by simp [outer, hv], h⟩
      | none =>
        cases hc : connect Gm n v (preorder KS) s with
        | none => rw [hv, hc] at h; cases h
        | some p => rw [hv, hc] at h; exact ⟨p.2, by simp [outer, hv, hc], h⟩
    obtain ⟨s1, h1, h2⟩ := hsplit
    obtain ⟨ACC1, hs1, hst⟩ := tj_ostep hL hg n v KS ht s ACC hs s1 h1
    obtain ⟨ACC', hs', hf⟩ := tj_outer hL hg n xs hxs s1 r h2 ACC1 hs1
    refine ⟨ACC', hs', ?_⟩
    simp only [List.foldlM_cons, hst]
    exact hf

/-- The empty state. -/
theorem tjStIs_init : TjStIs (tjAccN (A 0) (A 0) (A 0) (A 0) (A 0)) St.init :=
  ⟨A 0, A 0, A 0, rfl, ⟨IsMap.nil, fun k v => ⟨fun h => absurd h Get_atom, fun ⟨_, h, _⟩ => by cases h⟩⟩,
    ⟨by simpa [IsSet] using (IsMap.nil : IsMap mugF (A 0)), fun k => ⟨fun h => absurd h Get_atom, fun h => by
      simp [St.init] at h⟩⟩, rfl⟩

/-- **The battery of `+tarjan`** on the gate core `[tjBat [g ana]]`: when
`tarjanM` returns, the battery returns the list of the same sets. -/
theorem tj_bat {G E : Noun} (hG : Tree G) (hn : ∀ x ∈ preorder G, ∃ v KS, x = C v KS ∧ Tree KS)
    (hg : TjGraphAt (C tjBat (C G ana)) (tjGraph G))
    (hb : nock (C tjBat (C G ana)) tjSamB = some (C E (tjAccN (A 0) (A 0) (A 0) (A 0) (A 0))))
    {L : List (List Noun)} (h : tarjanM (tjGraph G) = some L) :
    ∃ FIN, TjFinIs FIN L ∧ nock (C tjBat (C G ana)) tjBat = some FIN := by
  have hL : slot? 32767 (C tjBat (C G ana)) = some layer2 := by
    simpa [nock_exec] using ana_layer2'
  have hne : tjGraph G ≠ [] := by
    intro e; rw [e] at h; simp [tarjanM] at h
  have h' : (outer (tjGraph G) (fuelOf (tjGraph G)) (tjGraph G) St.init).map St.fin = some L := by
    rw [← h]
    generalize tjGraph G = Gm at hne
    cases Gm with
    | nil => exact absurd rfl hne
    | cons a l => rfl
  cases ho : outer (tjGraph G) (fuelOf (tjGraph G)) (tjGraph G) St.init with
  | none => rw [ho] at h'; cases h'
  | some r =>
    rw [ho] at h'
    simp only [Option.map_some, Option.some.injEq] at h'
    obtain ⟨ACC', hs', hf⟩ := tj_outer hL hg (fuelOf (tjGraph G)) (preorder G) hn St.init r
      (by simpa [tjGraph] using ho) _ tjStIs_init
    obtain ⟨VIS, CUR, FIN, rfl, -, -, hfin⟩ := hs'
    refine ⟨FIN, h' ▸ hfin, ?_⟩
    have hr := tj_rep_gate by.battery layer2 tjOBat E (tjAccN (A 0) (A 0) (A 0) (A 0) (A 0)) (C tjBat (C G ana)) G hG
    rw [hf] at hr
    simp only [tjAccN] at hr hb hf
    conv => lhs; arg 2; rw [tjBat_eq]
    simp [tjRun_eq, tjRepDoor_eq, tjOGate_eq, tjAccN, nock_exec, hL, by.arm_at, by_arm, by.rep.arm_at, rep_arm,
      hb, hr]

end Compiler
end Formalization
