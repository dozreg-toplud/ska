import lemmas.Compiler.CompRunShapeCons
import lemmas.Compiler.CompRunShapeSixSectCut
import lemmas.Compiler.CompRunShapeSixFkCut
import lemmas.Compiler.CompRunShapeSixBigCut
import lemmas.Compiler.CompRunShapeSixCaseCut

/-!
# `+run-shape`: the case `[6 p q r]` under `%done` and `%pick` (track A, 2026-11-27)

Under a goal that is not `%next`, `lep` is `~` and the kerf test is no, so the case is
`sixBranch env .. p goal`: the runs of `r` and `q` on the goal, `+laze-sect` of the two,
`+laze-past-fork` over `p`, `this` if `+laze-big`, the run of `p` under `%pick`, `+laze-copy`.

* **`lzs_gate`**: `+laze-sect` (door arm `762`) is `lazeSect` at the door of `+run-shape`.
* **`lpf_gate`**: `+laze-past-fork` (door arm `0x5557e`) is `lazePastFork`, under `CallCode`.
* **`lbg_gate`**: `+laze-big` (door arm `0xabb5e`) is `lazeBig (sofsHas st.sofs)` (with the
  trap `lbg_go`, `lbg_forks`, `lbg_bonds`; `cs_has_gate`: `+has:in` on `sofs`).
* `rsK6_eq`: the case read from the pill is `rs6Arm`.
* **`rs_n6DP`**: the case under `%done` and `%pick`.
* `sixBranch_nz`: `sixBranch` keeps `LzNZ` (`lazeSect_nz`, `lazePastFork_nz`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

theorem rs6_lmax_at : slot? 343 compK = some (C (A 1) (A 512)) := by kernel_rfl

theorem rs6_mapM_some {α β : Type} (f : α → β) : ∀ l : List α, l.mapM (fun a => some (f a)) = some (l.map f)
  | [] => rfl
  | a :: t => by simp [List.mapM_cons, rs6_mapM_some f t]

/-! ## `+laze-sect` -/

theorem lzs_arm (d : Noun) : nock d lzsArm = some (C lzsGate (C lzsBunt d)) := by
  unfold lzsArm; simp only [nock_exec]

/-- **`+laze-sect` is `lazeSect`** at the door of `+run-shape`. -/
theorem lzs_gate (st : RSt CSet) (y : RsRest) (l0 l1 : Laze CSet) :
    nock (C lzsGate (C (C l0.toNoun l1.toNoun) (rsDoor st y ctx))) lzsGate
      = (lazeSect l0 l1 st).map fun p => C p.1.toNoun (rsGenNoun p.2 y) := by
  unfold lzsGate
  simp [nock_exec, rsDoor, lzp_id_at', comp_id_at, rs_id, lazeSect, idS, bind, StateT.bind, pure,
    StateT.pure, Laze.toNoun, Laze.forksNoun, Laze.bondsNoun, SureO.toNoun, SureO.bunt, NeedOrd.toNoun,
    Tag.none, HoonSet.toNoun_empty]

/-! ## `+laze-past-fork` -/

theorem lpf_arm (d : Noun) : nock d lpfArm = some (C lpfGate (C lpfBunt d)) := by
  unfold lpfArm; simp only [nock_exec]

/-- The model's map of `+laze-past-fork` on one fork entry. -/
noncomputable def lpfE (e : (Nat × Laze CSet) × (Nat × Laze CSet)) : (Nat × Laze CSet) × (Nat × Laze CSet) :=
  ((e.1.1, Laze.mk SureO.bunt [] [(e.1.1, e.1.2)]), (e.2.1, Laze.mk SureO.bunt [] [(e.2.1, e.2.2)]))

theorem lpf_g (e : (Nat × Laze CSet) × (Nat × Laze CSet)) (bc : Noun) :
    nock (C lpfG (C (lzfE e) bc)) lpfG = some (lzfE (lpfE e)) := by
  obtain ⟨⟨oy, y⟩, ⟨on, n⟩⟩ := e
  unfold lpfG
  simp [nock_exec, lzfE, lpfE, lz_toNoun_mk, lzbE, SureO.toNoun, SureO.bunt, NeedOrd.toNoun, Tag.none,
    HoonSet.toNoun_empty, listN]

/-- **`+laze-past-fork` is `lazePastFork`** on every `laze` and every nomm whose direct calls are
in the code table at axis `52` of `ctx`, with `K` at axis `7`. -/
theorem lpf_gate (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) {cod : Noun}
    (hcode : slot? 52 ctx = some cod) (env : ShapeEnv) (nom : Nomm) (hcc : CallCode cod (shapeCE env) nom)
    (G : Noun) (laz : Laze CSet) :
    nock (C lpfGate (C (C laz.toNoun nom.toNoun) (C comp.door (C G ctx)))) lpfGate
      = (lazePastFork env laz nom).map Laze.toNoun := by
  rcases e : hinted env.pure nom with _ | b
  · exact absurd e (callCode_hinted cod (shapeCE env) nom hcc)
  have hh := hd_gateR cod (shapeCE env) nom b hcc e
  obtain ⟨s, fk, bd⟩ := laz
  have ht := turn_gate_mapT lzfE lzfE layer2 homoIn_layer2 lpfG (C (C (A 0) lneBunt) (C (A 0) lneBunt))
    (C lpfGate (C (C (Laze.mk s fk bd).toNoun nom.toNoun) (C comp.door (C G ctx)))) (fun e => some (lpfE e)) fk
    (fun e _ => by rw [lpf_g]; rfl)
  unfold lneBunt at ht
  rw [lz_toNoun_mk] at ht ⊢
  conv => { lhs; arg 2; unfold lpfGate }
  cases b
  · simp [nock_exec, lazePastFork, e, h7, hcode, compK_hd, hd_arm, hh, loob, lz_toNoun_mk]
  · simp [nock_exec, lazePastFork, e, h7, hcode, compK_hd, hd_arm, hh, loob, lz_toNoun_mk, hc, turn.arm_at,
      turn_arm, ht, rs6_mapM_some, lpfE, Laze.sure, Laze.fork, Laze.bond]

/-! ## `+laze-big` -/

theorem lbg_arm (d : Noun) : nock d lbgArm = some (C lbgGate (C lbgBunt d)) := by
  unfold lbgArm; simp only [nock_exec]

/-- `+has:in` on a set of `sofs` is `sofsHas`. -/
theorem cs_has_gate (s : CSet) (o : Nat) :
    nock (C in.has.battery (C (A o) (C in.battery (C (HoonSet.toNoun s) layer2)))) in.has.battery
      = some (loob (sofsHas s o)) := by
  obtain ⟨t, ht, hti⟩ := hasInF_spec mugF (HoonSet.toNoun s) (A o) (cs_isSet s)
  rw [has_in_gate layer2 gorIn_morIn_layer2.1 (A o) _ t ht]
  have key : t = true ↔ sofsHas s o = true := by
    rw [hti, cs_has]; simp [sofsHas]
  cases t <;> cases h : sofsHas s o <;> simp_all

section
variable (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) (st : RSt CSet) (y : RsRest)
include hc h7

mutual
/-- **The trap of `+laze-big`** from the count `c` is `cntGo`. -/
theorem lbg_go : ∀ (laz : Laze CSet) (c : Nat),
    nock (C lbgTrap (C (A c) (C lbgGate (C laz.toNoun (rsDoor st y ctx))))) lbgTrap
      = some (A (cntGo (sofsHas st.sofs) c laz))
  | Laze.mk s fk bd, c => by
    have hF := lbg_forks fk (c + 1) s.toNoun (listN (bd.map lzbE))
    have hB := lbg_bonds bd (cntF (sofsHas st.sofs) (c + 1) fk) s.toNoun (listN (fk.map lzfE))
    have hg := gth_gate layer1 arith_layer1.2.2.2.2.1 c 512
    have hl1 := cf_layer1 hc
    rw [lz_toNoun_mk]
    by_cases h : c > Lazy.lazyMax
    · have h' : 512 < c := h
      simp only [cntGo, h, if_true]
      conv => { lhs; arg 2; unfold lbgTrap }
      simp [nock_exec, rsDoor, hl1, h7, gth.arm_at, gth_arm, hg, rs6_lmax_at, h', loob]
    · have h' : ¬ 512 < c := h
      simp only [cntGo, h, if_false]
      simp only [rsDoor] at hF hB
      conv => { lhs; arg 2; unfold lbgTrap }
      simp [nock_exec, rsDoor, hl1, h7, gth.arm_at, gth_arm, hg, rs6_lmax_at, h', loob, hF, hB]

theorem lbg_forks : ∀ (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet))) (c : Nat) (s b : Noun),
    nock (C lbgFT (C lbgTrap (C (A c) (C lbgGate (C (C s (C (listN (fk.map lzfE)) b)) (rsDoor st y ctx))))))
      lbgFT = some (A (cntF (sofsHas st.sofs) c fk))
  | [], c, s, b => by
    unfold lbgFT
    simp [nock_exec, cntF]
  | ((oy, ly), (on, ln)) :: rest, c, s, b => by
    have h1 := lbg_go ly c
    have h2 := lbg_go ln (cntGo (sofsHas st.sofs) c ly)
    have h3 := lbg_forks rest (cntGo (sofsHas st.sofs) (cntGo (sofsHas st.sofs) c ly) ln) s b
    conv => { lhs; arg 2; unfold lbgFT }
    simp [nock_exec, cntF, lzfE, h1, h2, h3]

theorem lbg_bonds : ∀ (bd : List (Nat × Laze CSet)) (c : Nat) (s f : Noun),
    nock (C lbgBT (C lbgTrap (C (A c) (C lbgGate (C (C s (C f (listN (bd.map lzbE)))) (rsDoor st y ctx))))))
      lbgBT = some (A (cntB (sofsHas st.sofs) c bd))
  | [], c, s, f => by
    unfold lbgBT
    simp [nock_exec, cntB]
  | (ob, l) :: rest, c, s, f => by
    have h1 := lbg_go l c
    have hs := cs_has_gate st.sofs ob
    have hc' : slot? 262143 ctx = some layer2 := hc
    by_cases hso : sofsHas st.sofs ob = true
    · have h3 := lbg_bonds rest c s f
      simp only [rsDoor, rsGenNoun] at h1 h3
      conv => { lhs; arg 2; unfold lbgBT lbgHas }
      simp [nock_exec, cntB, lzbE, h1, h3, hso, rsDoor, rsGenNoun, hc', in_arm, in.arm_at, in.has.arm_at,
        has_in_arm, hs, loob]
    · have h3 := lbg_bonds rest (cntGo (sofsHas st.sofs) c l) s f
      simp only [Bool.not_eq_true] at hso
      simp only [rsDoor, rsGenNoun] at h1 h3
      conv => { lhs; arg 2; unfold lbgBT lbgHas }
      simp [nock_exec, cntB, lzbE, h1, h3, hso, rsDoor, rsGenNoun, hc', in_arm, in.arm_at, in.has.arm_at,
        has_in_arm, hs, loob]
end

/-- **`+laze-big` is `lazeBig`** with the blocks of `sofs` skipped. -/
theorem lbg_gate (laz : Laze CSet) :
    nock (C lbgGate (C laz.toNoun (rsDoor st y ctx))) lbgGate = some (loob (lazeBig (sofsHas st.sofs) laz)) := by
  have h := lbg_go hc h7 st y laz 0
  have hg := gth_gate layer1 arith_layer1.2.2.2.2.1 (cntGo (sofsHas st.sofs) 0 laz) 512
  have hl1 := cf_layer1 hc
  simp only [rsDoor] at h
  conv => { lhs; arg 2; unfold lbgGate }
  simp [nock_exec, rsDoor, h, hl1, h7, gth.arm_at, gth_arm, hg, rs6_lmax_at, lazeBig, loob, Lazy.lazyMax]

end

end Compiler
end Formalization
