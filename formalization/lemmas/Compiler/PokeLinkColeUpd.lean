import lemmas.Compiler.PokeLinkGood8

/-!
# `+ska-cole-update` linked (track P, README Gaps 23)

The cut of `+ska-cole-update` (arm `2746` of `ana`) and of `+cole-put`
(arm `2814`), `tools/gen/cucut.py`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeM

-- BEGIN cucut
/-- the arm `+ska-cole-update`: the gate with its `%fast` hint, 150 cells: axis `2746` of `ana`. -/
def couArm : Noun := (slot? 2746 ana).getD (A 0)
/-- the battery of the gate, 121 cells: axis `109` of `couArm`. -/
def couBat : Noun := (slot? 109 couArm).getD (A 0)
/-- the `+rep:in` of `new-bells` with its step gate, 111 cells: axis `245` of `couBat`. -/
def couRep : Noun := (slot? 245 couBat).getD (A 0)
/-- the bunt of the sample of the step gate, 10 cells: axis `4062` of `couRep`. -/
def couSam : Noun := (slot? 4062 couRep).getD (A 0)
/-- the bunt of `bell`, 8 cells: axis `2` of `couSam`. -/
def couBunt : Noun := (slot? 2 couSam).getD (A 0)
/-- the battery of the step gate, 73 cells: axis `16253` of `couRep`. -/
def couStep : Noun := (slot? 16253 couRep).getD (A 0)
/-- the push of `sek`: `got:by` of `seek.lon` under `%mean`, 25 cells: axis `6` of `couStep`. -/
def couGot : Noun := (slot? 6 couStep).getD (A 0)
/-- the push of the call of `+cole-match`, 20 cells: axis `30` of `couStep`. -/
def couCm : Noun := (slot? 30 couStep).getD (A 0)
/-- the test of the match and the call of `+cole-put`, 24 cells: axis `31` of `couStep`. -/
def couTl : Noun := (slot? 31 couStep).getD (A 0)
/-- the arm `+cole-put`: the gate, 60 cells: axis `2814` of `ana`. -/
def cputArm : Noun := (slot? 2814 ana).getD (A 0)
/-- the battery of `+cole-put`, 47 cells: axis `29` of `cputArm`. -/
def cputBat : Noun := (slot? 29 cputArm).getD (A 0)

theorem couArm_eq : couArm = (C (A 7) (C (C (A 8) (C (C (A 1) (C (C (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0)))))) (C (A 0) (A 0)))) (C (C (A 1) couBat) (C (A 0) (A 1))))) (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x6574616470752d656c6f632d616b73) (C (C (A 0) (A 4095)) (A 0))))) (C (A 0) (A 1)))))) := by kernel_rfl
theorem couBat_eq : couBat = (C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C (C (A 10) (C (C (A 799) couRep) (C (A 0) (A 1)))) (C (A 0) (A 12)))))) := by kernel_rfl
theorem couRep_eq : couRep = (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x7fff)))) (C (A 9) (C (A 383) (C (A 10) (C (C (A 6) (C (A 0) (A 58))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C couSam (C (C (A 1) couStep) (C (A 0) (A 1)))))))) (C (A 0) (A 2)))))))) := by kernel_rfl
theorem couSam_eq : couSam = (C couBunt (C (A 0) (A 799))) := by kernel_rfl
theorem couBunt_eq : couBunt = (C (A 7) (C (C (A 9) (C (A 382) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) := by kernel_rfl
theorem couStep_eq : couStep = (C (A 8) (C couGot (C (A 8) (C couCm couTl)))) := by kernel_rfl
theorem couGot_eq : couGot = (C (A 11) (C (C (A 0x6e61656d) (C (A 1) (A 0x6b6565732d616b73))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1ffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 3999))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))))) := by kernel_rfl
theorem couCm_eq : couCm = (C (A 8) (C (C (A 9) (C (A 0x57dc) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 60)) (C (C (A 0) (A 6)) (C (C (A 0) (A 2018)) (C (C (A 0) (A 8078)) (C (A 0) (A 507))))))) (C (A 0) (A 2)))))))) := by kernel_rfl
theorem couTl_eq : couTl = (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (A 0) (A 61)) (C (A 8) (C (C (A 9) (C (A 2814) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (C (A 0) (A 13)) (C (A 0) (A 125))))) (C (A 0) (A 2))))))))))) := by kernel_rfl
theorem cputArm_eq : cputArm = (C (A 8) (C (C (A 1) (C (C (C (A 1) (A 0)) (C (A 0) (A 0))) (C (C (A 0) (A 0)) (C (A 0) (A 0))))) (C (C (A 1) cputBat) (C (A 0) (A 1))))) := by kernel_rfl
theorem cputBat_eq : cputBat = (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 118))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 0) (A 58)))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 760) (C (A 0) (A 0x7fff)))) (C (A 9) (C (A 4) (C (A 10) (C (C (A 6) (C (A 0) (A 119))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 58)) (C (A 0) (A 28)))) (C (A 0) (A 2))))))))) := by kernel_rfl

theorem ana_couArm : slot? 2746 ana = some couArm := by kernel_rfl
theorem ana_cputArm : slot? 2814 ana = some cputArm := by kernel_rfl
-- END cucut

/-! ## `+cole-put` -/

/-- `put:ju` answers on a jug of sets. -/
theorem juPutF_sets_some {a b c : Noun} (h : JugSets a) : ∃ out, juPutF mugF b c a = some out := by
  obtain ⟨g, hg, hd⟩ : ∃ g, getF mugF b a = some g ∧ IsSet mugF (unUnit g) := by
    by_cases hx : ∃ s, Get a b s
    · obtain ⟨s, hs⟩ := hx
      exact ⟨_, getF_some h.1 hs, h.2 _ _ hs⟩
    · exact ⟨_, getF_none h.1 (fun v hv => hx ⟨v, hv⟩), IsMap.nil⟩
  obtain ⟨e, he, -, -⟩ := putInF_spec mugF (unUnit g) c hd
  obtain ⟨o, ho, -, -⟩ := putF_spec mugF a b e h.1
  exact ⟨o, by simp only [juPutF, juGetF, hg, Option.map_some, Option.bind_some, he, ho]⟩

set_option maxHeartbeats 2000000 in
/-- **The battery of `+cole-put`** on `[b r [ca bk]]`: `put:by` and
`put:ju`. -/
theorem cputBat_run (b r ca bk ca' bk' : Noun) (h1 : putF mugF b r ca = some ca')
    (h2 : juPutF mugF r b bk = some bk') :
    nock (C cputBat (C (C b (C r (C ca bk))) ana)) cputBat = some (C ca' bk') := by
  have hput := put_gate (mug := mugF) layer2 gorIn_morIn_layer2 b r ca ca' h1
  have hju := ju_put_gate layer2 juIn_layer2 r b bk bk' h2
  conv => lhs; arg 2; rw [cputBat_eq]
  simp [nock_exec, ana_l2, by.arm_at, by_arm, by.put.arm_at, put_arm, ju.arm_at, ju_arm, ju.put.arm_at,
    ju_put_arm, hput, hju]

/-! ## The step gate -/

/-- The answers of `+cole-match` the step reads: a crash, `~`, or `[~ ring]`
(the gate fact for `+cole-match`, open: its answer `[~ [p.n.core axe]]` is a
ring where the keys of `core` are paths). -/
def CmRing (o : Option Noun) : Prop :=
  o = none ∨ o = some (A 0) ∨ ∃ n : Ring, o = some (C (A 0) n.toNoun)

/-- The cole pair: `call` a map, `back` a jug of sets. -/
def CoPair (c : Noun) : Prop := ∃ ca bk, c = C ca bk ∧ IsMap mugF ca ∧ JugSets bk

theorem coleStepO_pair {seekN core arms hot b c out : Noun} (h : CoPair c)
    (e : coleStepO seekN core arms hot b c = some out) : CoPair out := by
  obtain ⟨ca, bk, rfl, hca, hbk⟩ := h
  unfold coleStepO at e
  split at e
  · split at e
    · cases e; exact ⟨ca, bk, rfl, hca, hbk⟩
    · unfold colePutO at e
      split at e
      · simp only at e
        obtain ⟨ca', hca', e⟩ := Option.bind_eq_some_iff.1 e
        obtain ⟨bk', hbk', rfl⟩ := Option.map_eq_some_iff.1 e
        exact ⟨ca', bk', rfl, isMap_of_putF hca hca', jugSets_put hbk hbk'⟩
      · cases e
    · cases e
  · cases e

/-- The subject of the gate of `+ska-cole-update`: `[lon new-bells hot]`
with `lon = [[j1 co j3 ar j5] mN cN caN vN sN]`. -/
def couG (j1 co j3 ar j5 mN cN caN vN sN nb hot : Noun) : Noun :=
  C couBat (C (C (C (C j1 (C co (C j3 (C ar j5)))) (C mN (C cN (C caN (C vN sN))))) (C nb hot)) ana)

set_option maxHeartbeats 2000000 in
/-- The call of `+cole-match` in the step is `coleMatchP`. -/
theorem couCm_run (sek x acc j1 co j3 ar j5 mN cN caN vN sN nb hot : Noun) :
    nock (C sek (C couStep (C (C x acc) (couG j1 co j3 ar j5 mN cN caN vN sN nb hot)))) couCm =
      coleMatchP x sek co ar hot := by
  unfold coleMatchP coleMatchCall couG
  rw [couCm_eq]
  simp [nock_exec]

set_option maxHeartbeats 2000000 in
/-- **The step gate of `+ska-cole-update`** on a bell `x` and a cole pair:
`coleStepO` at `seek = sN`, `core = co`, `arms = ar`, where `seek` is a map
and `+cole-match` answers a crash, `~` or `[~ ring]`. -/
theorem couStep_run (x acc j1 co j3 ar j5 mN cN caN vN sN nb hot : Noun) (hs : IsMap mugF sN)
    (hR : ∀ sek, CmRing (coleMatchP x sek co ar hot)) (hacc : CoPair acc) :
    nock (C couStep (C (C x acc) (couG j1 co j3 ar j5 mN cN caN vN sN nb hot))) couStep =
      coleStepO sN co ar hot x acc := by
  have hgc : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
    ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
  obtain ⟨ca, bk, rfl, hca, hbk⟩ := hacc
  by_cases hx : ∃ v, Get sN x v
  · obtain ⟨v, hv⟩ := hx
    have hg := getF_some (mug := mugF) hs hv
    have hgot := got_gate layer2 hgc x sN v hg
    have hcm := couCm_run v x (C ca bk) j1 co j3 ar j5 mN cN caN vN sN nb hot
    unfold couG at hcm ⊢
    rcases hR v with h | h | ⟨n, h⟩
    · rw [h] at hcm
      conv => lhs; arg 2; rw [couStep_eq]
      simp [nock_exec, couGot_eq, ana_l2, by.arm_at, by_arm, by.got.arm_at, got_arm, hgot, hcm,
        coleStepO, hg, h]
    · rw [h] at hcm
      conv => lhs; arg 2; rw [couStep_eq]
      simp [nock_exec, couGot_eq, couTl_eq, ana_l2, by.arm_at, by_arm, by.got.arm_at, got_arm, hgot, hcm,
        coleStepO, hg, h]
    · rw [h] at hcm
      obtain ⟨ca', h1, -, -⟩ := putF_spec mugF ca x n.toNoun hca
      obtain ⟨bk', h2⟩ := juPutF_sets_some (b := n.toNoun) (c := x) hbk
      have hcp := cputBat_run x n.toNoun ca bk ca' bk' h1 h2
      conv => lhs; arg 2; rw [couStep_eq]
      simp [nock_exec, couGot_eq, couTl_eq, ana_l2, by.arm_at, by_arm, by.got.arm_at, got_arm, hgot, hcm,
        ana_cputArm, cputArm_eq, hcp, coleStepO, hg, h, colePutO, h1, h2]
      exact ⟨n, rfl⟩
  · have hg := getF_none (mug := mugF) hs (fun v hv => hx ⟨v, hv⟩)
    have hgot := got_gate_nil layer2 hgc x sN hg
    unfold couG
    conv => lhs; arg 2; rw [couStep_eq]
    simp [nock_exec, couGot_eq, ana_l2, by.arm_at, by_arm, by.got.arm_at, got_arm, hgot, coleStepO, hg]

/-! ## The gate -/

/-- The bunt of `bell` in the sample of the step gate. -/
noncomputable def couBuntV : Noun := (evalFuel 3000 (C (A 0) (C (A 0) ana)) couBunt).getD (A 0)

theorem couBunt_run (x y : Noun) : nock (C x (C y ana)) couBunt = some couBuntV :=
  nock_of_evalFuel (fuel := 3000) (by kernel_rfl)

theorem couSam_run (x y : Noun) :
    nock (C x (C y ana)) couSam = (slot? 799 (C x (C y ana))).map fun z => C couBuntV z := by
  have h := couBunt_run x y
  rw [couBunt_eq] at h
  rw [couSam_eq, couBunt_eq, nock_cell, h, nock_op0]
  cases slot? 799 (C x (C y ana)) <;> rfl

set_option maxHeartbeats 4000000 in
/-- **The gate of `+ska-cole-update`** on `[lon new-bells hot]`, `seek.lon`
a map, `new-bells` a set at whose elements `+cole-match` answers a crash,
`~` or `[~ ring]`, and a cole pair: `+rep:in` of `coleStepO`, written back
into `cole.jets.lon`. -/
theorem couBat_run (j1 co j3 ar pd cole mN cN caN vN sN nb hot : Noun) (hs : IsMap mugF sN)
    (hnb : IsSet mugF nb) (hR : ∀ x ∈ preorder nb, ∀ sek, CmRing (coleMatchP x sek co ar hot))
    (hc : CoPair cole) :
    nock (couG j1 co j3 ar (C pd cole) mN cN caN vN sN nb hot) couBat =
      (repO (coleStepO sN co ar hot) nb cole).map fun cole' =>
        C (C j1 (C co (C j3 (C ar (C pd cole'))))) (C mN (C cN (C caN (C vN sN)))) := by
  have hrep := rep_gateP in.battery layer2 couStep couBuntV cole (couG j1 co j3 ar (C pd cole) mN cN caN vN sN nb hot)
    (coleStepO sN co ar hot) CoPair (fun x => ∀ sek, CmRing (coleMatchP x sek co ar hot))
    (fun x acc hx hacc => couStep_run x acc j1 co j3 ar (C pd cole) mN cN caN vN sN nb hot hs hx hacc)
    (fun _ _ _ _ h e => coleStepO_pair h e) nb (Tree.of_isSet hnb) hR hc
  unfold couG at hrep ⊢
  conv => lhs; arg 2; rw [couBat_eq]
  cases h : repO (coleStepO sN co ar hot) nb cole with
  | none =>
    rw [h] at hrep
    simp [nock_exec, couRep_eq, couSam_run, ana_l2, in.arm_at, in_arm, in.rep.arm_at, rep_arm, hrep]
  | some c' =>
    rw [h] at hrep
    simp [nock_exec, couRep_eq, couSam_run, ana_l2, in.arm_at, in_arm, in.rep.arm_at, rep_arm, hrep]

/-! ## The end of `spRest`: `+flop` and `+ska-cole-update` -/

set_option maxHeartbeats 4000000 in
/-- **`srEnd` on a subject with its slot facts**: `[root-bell (flop new)]`
and `+ska-cole-update` of `lon` on `~(key by new-code)` (a set `nb` of the
keys of `ncN`), where `seek` and `new-code` are maps, `+cole-match` answers
a crash, `~` or `[~ ring]` at the keys of `new-code`, and `cole` is a cole
pair. -/
theorem srEnd_run (U rootN : Noun) (l : List Noun) (j1 co j3 ar pd cole mN cN caN vN sN hot ncN : Noun)
    (hA : slot? 0xffff U = some ana) (hL2 : slot? 0xfffffff U = some layer2)
    (hR : slot? 126 U = some rootN) (hN : slot? 0x1ffdf U = some (listN l))
    (hlon : slot? 0x3fffa U = some (C (C j1 (C co (C j3 (C ar (C pd cole))))) (C mN (C cN (C caN (C vN sN))))))
    (hH : slot? 0x3fffb U = some hot) (hK : slot? 14 U = some ncN)
    (hnc : IsMap mugF ncN) (hs : IsMap mugF sN)
    (hRg : ∀ x, (∃ v, Get ncN x v) → ∀ sek, CmRing (coleMatchP x sek co ar hot)) (hc : CoPair cole) :
    ∃ nb, IsSet mugF nb ∧ (∀ k, Has nb k ↔ ∃ v, Get ncN k v) ∧
      nock U srEnd = (repO (coleStepO sN co ar hot) nb cole).map fun cole' =>
        C (C rootN (listN l.reverse)) (C (C j1 (C co (C j3 (C ar (C pd cole'))))) (C mN (C cN (C caN (C vN sN))))) := by
  obtain ⟨nb, hev, hset, hhas⟩ := key_by (mug := mugF) layer2 ⟨in.arm_at, gorIn_morIn_layer2⟩ ncN hnc
  have hkey := nock_eq_some_iff.2 hev
  have hgate := couBat_run j1 co j3 ar pd cole mN cN caN vN sN nb hot hs hset
    (fun x hx => hRg x ((hhas x).1 (((mem_preorder_tapList nb x).trans (mem_tapList_set hset x)).1 hx))) hc
  unfold couG at hgate
  have hfl := flop_gate layer2 homoIn_layer2 l
  refine ⟨nb, hset, hhas, ?_⟩
  unfold srEnd
  cases h : repO (coleStepO sN co ar hot) nb cole with
  | none =>
    rw [h] at hgate
    simp [nock_exec, hA, hL2, hR, hN, hlon, hH, hK, ana_couArm, couArm_eq, flop.arm_at, flop_arm, hfl,
      by.arm_at, by_arm, by.key.arm_at, hkey, hgate]
  | some c' =>
    rw [h] at hgate
    simp [nock_exec, hA, hL2, hR, hN, hlon, hH, hK, ana_couArm, couArm_eq, flop.arm_at, flop_arm, hfl,
      by.arm_at, by_arm, by.key.arm_at, hkey, hgate]

end Compiler
end Formalization
