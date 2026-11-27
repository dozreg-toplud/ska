import lemmas.Compiler.CompRunShapeSeven
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
* `sixBranch_nz`, `runShape_n6DP_nz`: the branch keeps `LzNZ` (`lazeSect_nz`,
  `lazePastFork_nz`).

Not here: `%6` under `[%next laz]` (`sixShape`: `+laze-leaps`, the kerf tests
`+laze-this-only`, `+laze-soft-fork`, `+whole`, and `+laze-branch`).
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

/-! ## The case under `%done` and `%pick` -/

theorem rsK6_eq : rsK6 = rs6Arm := by simp [rsK6, rs6_at]

theorem rs_disp_n6 (t s goal sup D : Noun) :
    nock (rsS s (C (A 6) t) goal sup D) rsDol = nock (rsS s (C (A 6) t) goal sup D) rsK6 := by
  nock_open rsDol
  simp [nock_exec, rsS, rsCoreG, rsTc, rsT]

theorem rs6_goal (goal : GoalS CSet) (hnn : goal = GoalS.done ∨ goal = GoalS.pick) :
    ∃ tag, goal.toNoun = C (A tag) (A 0) ∧ tag ≠ 0x7478656e := by
  rcases hnn with rfl | rfl
  · exact ⟨_, rfl, by decide⟩
  · exact ⟨_, rfl, by decide⟩

theorem rs6_model (env : ShapeEnv) (sup : Option Nomm) (p q r : Nomm) (goal : GoalS CSet)
    (hnn : goal = GoalS.done ∨ goal = GoalS.pick) :
    runShape env sup (Nomm.n6 p q r) goal
      = sixBranch env (runShape env sup p) (runShape env sup q) (runShape env sup r) p goal := by
  rcases hnn with rfl | rfl <;> rfl

theorem rs6_get (st : RSt CSet) : (MonadStateOf.get : SM CSet (RSt CSet)) st = some (st, st) := rfl

set_option hygiene false in
/-- The simp set of the leaves of `rs_n6DP`. -/
local macro "six_simp" " [" xs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| simp [nock_exec, rsS,
  rsCoreG, rsDoor, sixBranch, bind, StateT.bind, get, getThe, MonadState.get, StateT.get, shLiftS, pure,
  StateT.pure, rs6_get, hne, hne', rs6Lep, rs6Tk, rs6Gb, rs6Rest, GoalS.toNoun, thisL_noun, eqCode_atom, $xs,*])

section
variable (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
include hc h7 hcode

/-- **The case `[6 p q r]` under `%done` and `%pick`**: the runs of `r` and `q` on the goal,
`+laze-sect`, `+laze-past-fork` over `p`, `this` if `+laze-big`, the run of `p` under `%pick`,
`+laze-copy` (`sixBranch`). -/
theorem rs_n6DP (env : ShapeEnv) (p q r : Nomm) (sup : Option Nomm) (goal : GoalS CSet)
    (hnn : goal = GoalS.done ∨ goal = GoalS.pick) (st : RSt CSet) (hcp : CallCode cod (shapeCE env) p)
    (hr : ∀ st1, RsAt ctx env r sup goal st1)
    (hq : ∀ st1, RsAt ctx env q sup goal st1)
    (hp : ∀ st1, RsAt ctx env p sup GoalS.pick st1) :
    RsAt ctx env (Nomm.n6 p q r) sup goal st := by
  intro y
  obtain ⟨tag, htag, hne⟩ := rs6_goal goal hnn
  have hne' : ¬ (0x7478656e = tag) := fun h => hne h.symm
  rw [rs6_model env sup p q r goal hnn]
  simp only [Nomm.toNoun]
  rw [rs_push, rs_disp_n6, rsK6_eq, htag]
  unfold rs6Arm
  have hr' := hr st y
  simp only [rsCoreG, rsDoor, htag] at hr'
  cases e1 : runShape env sup r goal st with
  | none => rw [e1] at hr'; six_simp [hr', e1]
  | some r1 =>
    obtain ⟨l1, st1⟩ := r1
    rw [e1] at hr'
    have hq' := hq st1 y
    simp only [rsCoreG, rsDoor, htag] at hq'
    cases e2 : runShape env sup q goal st1 with
    | none => rw [e2] at hq'; six_simp [hr', e1, hq', e2]
    | some r2 =>
      obtain ⟨l0, st2⟩ := r2
      rw [e2] at hq'
      have hs := lzs_gate (ctx := ctx) st2 y l0 l1
      simp only [rsDoor] at hs
      cases e3 : lazeSect l0 l1 st2 with
      | none => rw [e3] at hs; six_simp [hr', e1, hq', e2, lzs_at', lzs_arm, hs, e3]
      | some r3 =>
        obtain ⟨lz, st3⟩ := r3
        rw [e3] at hs
        have hpf := lpf_gate hc h7 hcode env p hcp (rsGenNoun st3 y) lz
        cases e4 : lazePastFork env lz p with
        | none =>
          rw [e4] at hpf
          six_simp [hr', e1, hq', e2, lzs_at', lzs_arm, hs, e3, lpf_at', lpf_arm, hpf, e4]
        | some lz' =>
          rw [e4] at hpf
          have hbg := lbg_gate hc h7 st3 y lz'
          simp only [rsDoor] at hbg
          have hp' := hp st3 y
          simp only [rsCoreG, rsDoor, GoalS.toNoun] at hp'
          cases e5 : runShape env sup p GoalS.pick st3 with
          | none =>
            rw [e5] at hp'
            by_cases hb : lazeBig (sofsHas st3.sofs) lz' = true <;>
            · six_simp [hr', e1, hq', e2, lzs_at', lzs_arm, hs, e3, lpf_at', lpf_arm, hpf, e4,
                lbg_at', lbg_arm, hbg, hb, loob, hp', e5]
          | some r5 =>
            obtain ⟨lc, st4⟩ := r5
            rw [e5] at hp'
            by_cases hb : lazeBig (sofsHas st3.sofs) lz' = true
            · have hlc := lc_all hc h7 (rsGenNoun st4 y) lc thisL
              rw [thisL_noun] at hlc
              cases e6 : lazeCopy lc thisL with
              | none =>
                rw [e6] at hlc
                six_simp [hr', e1, hq', e2, lzs_at', lzs_arm, hs, e3, lpf_at', lpf_arm, hpf, e4,
                  lbg_at', lbg_arm, hbg, hb, loob, hp', e5, lc_at', lc_arm, hlc, e6]
              | some l =>
                rw [e6] at hlc
                six_simp [hr', e1, hq', e2, lzs_at', lzs_arm, hs, e3, lpf_at', lpf_arm, hpf, e4,
                  lbg_at', lbg_arm, hbg, hb, loob, hp', e5, lc_at', lc_arm, hlc, e6]
            · simp only [Bool.not_eq_true] at hb
              have hlc := lc_all hc h7 (rsGenNoun st4 y) lc lz'
              cases e6 : lazeCopy lc lz' with
              | none =>
                rw [e6] at hlc
                six_simp [hr', e1, hq', e2, lzs_at', lzs_arm, hs, e3, lpf_at', lpf_arm, hpf, e4,
                  lbg_at', lbg_arm, hbg, hb, loob, hp', e5, lc_at', lc_arm, hlc, e6]
              | some l =>
                rw [e6] at hlc
                six_simp [hr', e1, hq', e2, lzs_at', lzs_arm, hs, e3, lpf_at', lpf_arm, hpf, e4,
                  lbg_at', lbg_arm, hbg, hb, loob, hp', e5, lc_at', lc_arm, hlc, e6]

end

/-! ## `LzNZ` is kept -/

theorem lazeSect_nz (l0 l1 : Laze CSet) (st : RSt CSet) (r : Laze CSet) (st1 : RSt CSet) (h0 : LzNZ l0)
    (h1 : LzNZ l1) (e : lazeSect l0 l1 st = some (r, st1)) : LzNZ r := by
  simp [lazeSect, idS, bind, StateT.bind, pure, StateT.pure] at e
  obtain ⟨h, -⟩ := e
  subst h
  exact ⟨fun y hy => absurd hy (HoonSet.mem_empty y), ⟨h0, h1, trivial⟩, trivial⟩

theorem lpfF_nz : ∀ (f : List ((Nat × Laze CSet) × (Nat × Laze CSet))), LzNZF f → LzNZF (f.map lpfE)
  | [], _ => trivial
  | ((oy, y), (on, n)) :: rest, ⟨hy, hn, hr⟩ =>
    ⟨⟨fun z hz => absurd hz (HoonSet.mem_empty z), trivial, ⟨hy, trivial⟩⟩,
      ⟨fun z hz => absurd hz (HoonSet.mem_empty z), trivial, ⟨hn, trivial⟩⟩, lpfF_nz rest hr⟩

theorem lazePastFork_nz (env : ShapeEnv) (laz : Laze CSet) (nom : Nomm) (r : Laze CSet) (hl : LzNZ laz)
    (e : lazePastFork env laz nom = some r) : LzNZ r := by
  unfold lazePastFork at e
  obtain ⟨s, f, bd⟩ := laz
  obtain ⟨hs, hf, hb⟩ := hl
  cases eh : hinted env.pure nom with
  | none => simp [eh] at e
  | some b =>
    cases b
    · simp [eh] at e; subst e; exact ⟨hs, hf, hb⟩
    · simp [eh, Laze.sure, Laze.fork, Laze.bond] at e; subst e; exact ⟨hs, lpfF_nz f hf, hb⟩

/-- **`sixBranch` keeps `LzNZ`**, given that its three runs do. -/
theorem sixBranch_nz (env : ShapeEnv) (rp rq rr : GoalS CSet → SM CSet (Laze CSet)) (p : Nomm) (gb : GoalS CSet)
    (hrp : ∀ st l st1, rp GoalS.pick st = some (l, st1) → LzNZ l)
    (hrq : ∀ st l st1, rq gb st = some (l, st1) → LzNZ l)
    (hrr : ∀ st l st1, rr gb st = some (l, st1) → LzNZ l)
    (st : RSt CSet) (l : Laze CSet) (st1 : RSt CSet) (e : sixBranch env rp rq rr p gb st = some (l, st1)) :
    LzNZ l := by
  unfold sixBranch at e
  obtain ⟨l1, s1, e1, k1⟩ := sm_bind_some e
  obtain ⟨l0, s2, e2, k2⟩ := sm_bind_some k1
  obtain ⟨lz, s3, e3, k3⟩ := sm_bind_some k2
  obtain ⟨lz', s4, e4, k4⟩ := sm_bind_some k3
  obtain ⟨st', s5, e5, k5⟩ := sm_bind_some k4
  obtain ⟨lc, s6, e6, k6⟩ := sm_bind_some k5
  have h3 := lazeSect_nz l0 l1 s2 lz s3 (hrq _ _ _ e2) (hrr _ _ _ e1) e3
  obtain ⟨a, ea, ra⟩ := shLiftS_some e4
  simp only [Prod.mk.injEq] at ra
  have h4 : LzNZ lz' := by rw [ra.1]; exact lazePastFork_nz env lz p a h3 ea
  have hbig : LzNZ (if lazeBig (sofsHas st'.sofs) lz' = true then thisL else lz') := by
    split
    · exact lzNZ_thisL
    · exact h4
  exact lazeCopyEnd_nz (hrp _ _ _ e6) hbig k6

/-- **The case `[6 p q r]` under `%done` and `%pick` keeps `LzNZ`**, given that its three runs do. -/
theorem runShape_n6DP_nz (env : ShapeEnv) (sup : Option Nomm) (p q r : Nomm) (goal : GoalS CSet)
    (hnn : goal = GoalS.done ∨ goal = GoalS.pick)
    (hrp : ∀ st l st1, runShape env sup p GoalS.pick st = some (l, st1) → LzNZ l)
    (hrq : ∀ st l st1, runShape env sup q goal st = some (l, st1) → LzNZ l)
    (hrr : ∀ st l st1, runShape env sup r goal st = some (l, st1) → LzNZ l)
    (st : RSt CSet) (l : Laze CSet) (st1 : RSt CSet)
    (e : runShape env sup (Nomm.n6 p q r) goal st = some (l, st1)) : LzNZ l := by
  rw [rs6_model env sup p q r goal hnn] at e
  exact sixBranch_nz env _ _ _ p goal hrp hrq hrr st l st1 e

end Compiler
end Formalization
