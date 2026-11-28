import lemmas.Glue.GuardNaryPlain
import lemmas.Ska.RawInvCLKIMidU

/-!
# `RunG` over track D's corrected mid-run fact `KIMidX` (track G, fifteenth pass)

Misfit 8 of `LEDGER.md` section 10: the named hypothesis `KIMid`
(`Glue/GuardCallsB.lean`) is FALSE (track D's `kimid_false`): a goal with two
bonds at one label sharing a register meets `GD`, and `cons [0 2] [0 3]`
returns a bond whose need holds that register twice.  Its corrected form,
track D's `KIMidX` (`Ska/RawInvCLKIMidU.lean`), is a THEOREM on all of
`NoSixC` (`kimidX_noSix`, direct and indirect calls).  It asks of a goal that
the registers of the WHOLE tree be distinct and below `re` (`Raw.GX`) and that
the tree have bonds and forks at distinct labels with entries below `bo`
(`Raw.LG`).  So the run-level guard is restated here with `GU r goal :=
GX r goal ∧ LU goal` (`LU`: `LabUniq` of a `%next` goal's lazy; the "entries
below `bo`" part comes from `GFL`, `lg_of`) in place of `GD r goal`:

* `RunGX`, `RunRX` (the result keeps `GXL` and `LabUniq`), `RSB` (an `RS`
  with the `bo` bound too), `KPA.andRB`;
* `rs_runX`, `rs_splitX`, `rs_intoX`, `rs_pastX`: `KIMidX.run`, `.split`,
  `.into`, `.past` as `RSB` facts; `GU.gd`: `GU` gives `GD` (`KIMidX.dn`,
  `lzS_dn_of_gxl`), so `kerfG`, `kpa_simpleNextLG`, `kpa_monoBlocksG` are
  used as they are;
* the arms `runGX_*`, the calls `kpa_callTailGX`, `kpa_callDMGX`,
  `kpa_callLIX`;
* **`runGX_lcm env`**: every run of `runLCM env true` on `NoSixC` keeps
  `InvA`, with NO hypothesis;
* **`top_kerfAX`**, **`guardMonoC_noSixX`** (from `StraightA` alone),
  `entryMono_noSixX`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [Opt.MapKeys Map] [HoonMapKeys Map]

/-! ## The goal fact -/

/-- `LabUniq` of a `%next` goal's lazy. -/
def LU : CGoalL S → Prop
  | CGoalL.next laz _ => Raw.LabUniq laz
  | _ => True

/-- **The goal fact of `KIMidX`** at `re`: the registers of the whole tree
distinct and below `r`, the labels of each node distinct. -/
def GU (r : Nat) (goal : CGoalL S) : Prop := Raw.GX r goal ∧ LU goal

theorem GU.up {r r' : Nat} {goal : CGoalL S} (h : GU r goal) (hr : r ≤ r') : GU r' goal := by
  cases goal with
  | next laz th => exact ⟨Raw.gxl_up h.1 hr, h.2⟩
  | pick z o => exact ⟨trivial, trivial⟩
  | done => exact ⟨trivial, trivial⟩

/-- **`GU` gives `GD`** (track D's `lzS_dn_of_gxl`, the clause `KIMidX.dn`). -/
theorem GU.gd {r : Nat} {goal : CGoalL S} (h : GU r goal) : GD r goal := by
  cases goal with
  | next laz th => exact Raw.lzS_dn_of_gxl h.1
  | pick z o => trivial
  | done => trivial

theorem gxl_bunt (r : Nat) : Raw.GXL r (ofSure (Sure.bunt : Sure S)) := by
  unfold Raw.GXL; rw [Raw.sarR_ofSure]; simp [Sure.bunt, flattenNeed]

theorem gxl_reg {r x : Nat} (h : x < r) : Raw.GXL r (ofSure (lazyReg x : Sure S)) := by
  unfold Raw.GXL; rw [Raw.sarR_ofSure]; simp [lazyReg, flattenNeed]; exact h

theorem gxl_this {r x : Nat} (h : x < r) : Raw.GXL r (ofSure (⟨Need.this x, HoonSet.empty⟩ : Sure S)) := by
  unfold Raw.GXL; rw [Raw.sarR_ofSure]; simp [flattenNeed]; exact h

theorem gu_bunt (r : Nat) {th : Jmp} : GU r (CGoalL.next (ofSure (Sure.bunt : Sure S)) th) :=
  ⟨gxl_bunt r, Raw.labUniq_ofSure _⟩

theorem gu_reg {r x : Nat} (h : x < r) {th : Jmp} : GU r (CGoalL.next (ofSure (lazyReg x : Sure S)) th) :=
  ⟨gxl_reg h, Raw.labUniq_ofSure _⟩

/-- `LG` of a goal from `GFL` (its labels below `b0 ≤ bo`) and `LU`. -/
theorem lg_of {K0 : Nat → Nat → Prop} {b0 : Nat} {goal : CGoalL S} {g : Comp.Gen Map} (hg : GFL K0 b0 goal)
    (hu : LU goal) (hb : b0 ≤ g.bo) : Raw.LG goal g := by
  cases goal with
  | next laz th => exact ⟨hu, fun e he => Nat.lt_of_lt_of_le (lzL_ent laz hg.2.2 e he).1 hb⟩
  | pick z o => trivial
  | done => trivial

/-- `LL` of a lazy from its `FL` labels and `LabUniq`. -/
theorem ll_of {K0 : Nat → Nat → Prop} {b0 : Nat} {l : Lazy S} {g : Comp.Gen Map} (hl : LzL (FL K0 b0) l)
    (hu : Raw.LabUniq l) (hb : b0 ≤ g.bo) : Raw.LL l g :=
  ⟨hu, fun e he => Nat.lt_of_lt_of_le (lzL_ent l hl e he).1 hb⟩

/-! ## Facts on registers and labels beside `KPA` -/

/-- **Every run of `m` from a stage with `bo ≥ b0`, `re ≥ r0` returns a
result in `Q re'`.** -/
def RSB {α : Type} (b0 r0 : Nat) (Q : Nat → α → Prop) (m : CM Map α) : Prop :=
  ∀ (g : Comp.Gen Map) x g', b0 ≤ g.bo → r0 ≤ g.re → m g = some (x, g') → Q g'.re x

theorem KPA.andRB {α : Type} {K0 : Nat → Nat → Prop} {b0 r0 : Nat} {P : (Nat → Nat → Prop) → Nat → Nat → α → Prop}
    {Q : Nat → α → Prop} {m : CM Map α} (h : KPA K0 b0 r0 P m) (hq : RSB b0 r0 Q m) :
    KPA K0 b0 r0 (fun K b r x => P K b r x ∧ Q r x) m := by
  constructor
  intro K g x g' hI h0 hX e
  obtain ⟨K', hI', X, p⟩ := h.k K g x g' hI h0 hX e
  exact ⟨K', hI', X, p, hq g x g' hX.1 hX.2.1 e⟩

/-! ## Runs with `GU` -/

/-- **A run keeps `InvA` and returns `RN`** for every goal with `FL` jumps
that meets `GU`. -/
def RunGX (run : CGoalL S → List Nat → CM Map (NextL S)) : Prop :=
  ∀ (K0 : Nat → Nat → Prop) b0 r0 (goal : CGoalL S) region, GFL K0 b0 goal → GU r0 goal →
    KPA K0 b0 r0 RN (run goal region)

/-- **A run returns a lazy whose tree meets `GXL` and `LabUniq`.** -/
def RunRX (run : CGoalL S → List Nat → CM Map (NextL S)) : Prop :=
  ∀ (K0 : Nat → Nat → Prop) b0 r0 (goal : CGoalL S) region, GFL K0 b0 goal → GU r0 goal →
    RSB (Map := Map) b0 r0 (fun r (n : NextL S) => Raw.GXL r n.laz ∧ Raw.LabUniq n.laz) (run goal region)

/-- **`KIMidX.run` as `RunRX`.** -/
theorem rs_runX (env : CallEnv) {nm : Nomm} (hn : NoSixC nm) (sup : Option Nomm) :
    RunRX (runLCM (S := S) (Map := Map) env true sup nm) := by
  intro K0 b0 r0 goal region hg hu g x g' hb hr e
  have H := (Raw.kimidX_noSix (S := S) (Map := Map) env).run nm sup hn goal region g g' x (hu.up hr).1
    (lg_of hg hu.2 hb) e
  exact ⟨H.1, H.2.1⟩

theorem rs_splitX (env : CallEnv) {K0 : Nat → Nat → Prop} {b0 r0 : Nat} {nex : NextL S}
    (hx : Raw.GXL r0 nex.laz) (hu : Raw.LabUniq nex.laz) (hl : LzL (FL K0 b0) nex.laz) :
    RSB (Map := Map) b0 r0 (fun r (x : Lazy S × Lazy S × Nat) =>
      (Raw.GXL r x.1 ∧ Raw.LabUniq x.1) ∧ (Raw.GXL r x.2.1 ∧ Raw.LabUniq x.2.1)) (splitL nex) := by
  intro g x g' hb hr e
  obtain ⟨a1, a2, l1, l2⟩ := (Raw.kimidX_noSix (S := S) (Map := Map) env).split nex g g' x (Raw.gxl_up hx hr)
    (ll_of hl hu hb) e
  exact ⟨⟨a1, l1.1⟩, a2, l2.1⟩

theorem rs_intoX (env : CallEnv) {K0 : Nat → Nat → Prop} {b0 r0 : Nat} {nex : NextL S}
    (hx : Raw.GXL r0 nex.laz) (hu : Raw.LabUniq nex.laz) (hl : LzL (FL K0 b0) nex.laz) (axe : Nat) :
    RSB (Map := Map) b0 r0 (fun r (x : Lazy S × Lazy S × Nat) =>
      (Raw.GXL r x.1 ∧ Raw.LabUniq x.1) ∧ (Raw.GXL r x.2.1 ∧ Raw.LabUniq x.2.1)) (intoL nex axe) := by
  intro g x g' hb hr e
  obtain ⟨a1, a2, l1, l2⟩ := (Raw.kimidX_noSix (S := S) (Map := Map) env).into nex axe g g' x (Raw.gxl_up hx hr)
    (ll_of hl hu hb) e
  exact ⟨⟨a1, l1.1⟩, a2, l2.1⟩

theorem rs_pastX (env : CallEnv) (cod : Bell → Option Bool) {K0 : Nat → Nat → Prop} {b0 r0 : Nat} {nex : NextL S}
    (hx : Raw.GXL r0 nex.laz) (hu : Raw.LabUniq nex.laz) (hl : LzL (FL K0 b0) nex.laz) (nom : Nomm)
    (region : List Nat) :
    RSB (Map := Map) b0 r0 (fun r (n : NextL S) => Raw.GXL r n.laz ∧ Raw.LabUniq n.laz)
      (pastL cod nex nom region) := by
  intro g x g' hb hr e
  obtain ⟨a, l⟩ := (Raw.kimidX_noSix (S := S) (Map := Map) env).past cod nex nom region g g' x (Raw.gxl_up hx hr)
    (ll_of hl hu hb) e
  exact ⟨a, l.1⟩

/-! ## `+simple-next` and the calls -/

/-- **`+simple-next`** under a goal with `FL` jumps that meets `GU`. -/
theorem kpa_simpleNextLGX {K0 : Nat → Nat → Prop} {b0 r0 : Nat} {goal : CGoalL S} (hg : GFL K0 b0 goal)
    (hd : GU r0 goal) :
    KPA K0 b0 r0 (fun K bo r (n : NextL S) => FL K bo n.th.there ∧ JOK n.th ∧ LzL (FL K bo) n.laz ∧
      (Raw.GXL r n.laz ∧ Raw.LabUniq n.laz)) (simpleNextL goal : CM Map (NextL S)) := by
  cases goal with
  | next laz th => exact KPA.pure' fun K b r X => ⟨hg.1.up X, hg.2.1, hg.2.2.up X, Raw.gxl_up hd.1 X.2.1, hd.2⟩
  | done =>
    refine KPA.bind' KPA.re' fun r K1 b1 r1 X1 hr => KPA.bind' (KPA.emit' (blockOK_nil _ _ (by simp [getJmps]))
      (by simp [getJmps])) fun o K2 b2 r2 X2 ho => KPA.pure' fun K b r' X =>
        ⟨ho.up X, jok_jmp0 _, lzL_ofSure _ _, gxl_this (lt_up (lt_up hr.2 X2) X), Raw.labUniq_ofSure _⟩
  | pick z o =>
    refine KPA.bind' KPA.re' fun r K1 b1 r1 X1 hr => KPA.bind' (KPA.emit' (blockOK_nil _ _ ?_) ?_)
      fun o' K2 b2 r2 X2 ho => KPA.pure' fun K b r' X =>
        ⟨ho.up X, jok_jmp0 _, lzL_ofSure _ _, gxl_this (lt_up (lt_up hr.2 X2) X), Raw.labUniq_ofSure _⟩
    · intro j hj; simp only [getJmps, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact hg.2.1
      · exact hg.2.2.2
    · intro j hj; simp only [getJmps, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact hg.1.up X1
      · exact hg.2.2.1.up X1

/-- The tail of the direct call, with `RunGX` parts. -/
theorem kpa_callTailGX {K0 : Nat → Nat → Prop} {b0 r0 : Nat} (cod : Bell → Option Bool)
    {rp rq : CGoalL S → List Nat → CM Map (NextL S)} (hp : RunGX rp) (hq : RunGX rq) (p q : Nomm)
    (region : List Nat) (laz : Lazy S) (th : Jmp) (hth : FL K0 b0 th.there) (hj : JOK th) (hl : LzL (FL K0 b0) laz)
    (hd : Raw.GXL r0 laz ∧ Raw.LabUniq laz) :
    KPA K0 b0 r0 RN (do
      let nexFol ← (if safeFolFol q then pure ⟨ofSure Sure.bunt, th⟩
        else rq (CGoalL.next (ofSure Sure.bunt) th) region : CM Map (NextL S))
      let nexFol ← pastL cod nexFol p region
      let nexSub ← rp (CGoalL.next laz nexFol.th) region
      copyL nexSub nexFol.laz : CM Map (NextL S)) := by
  refine KPA.bind' (P := RN) ?_ fun n1 K1 bb1 r1 X1 h1 => ?_
  · split
    · exact KPA.pure' fun K b r X => ⟨hth.up X, hj, lzL_ofSure _ _⟩
    · exact hq _ _ _ _ _ (gfl_next hth hj (lzL_ofSure _ _)) (gu_bunt _)
  refine KPA.bind' (kpa_pastL cod h1 p region) fun n2 K2 bb2 r2 X2 h2 => ?_
  refine KPA.bind' (hp _ _ _ _ _ (gfl_next h2.1 h2.2.1 (hl.up (X1.trans X2)))
    ⟨Raw.gxl_up hd.1 (X1.trans X2).2.1, hd.2⟩) fun n3 K3 bb3 r3 X3 h3 => ?_
  exact kpa_copyL h3 (h2.2.2.up X3)

/-- **The direct call with `mono` `&` keeps `InvA`**, with `RunGX` parts. -/
theorem kpa_callDMGX (hk : KerfG S Map) (env : CallEnv) {rp rq : CGoalL S → List Nat → CM Map (NextL S)}
    (hp : RunGX rp) (hq : RunGX rq) (p q : Nomm) (bl : Bell) (key : Option Noun) {K0 : Nat → Nat → Prop}
    {b0 r0 : Nat} {goal : CGoalL S} (hg : GFL K0 b0 goal) (hd : GU r0 goal) (region : List Nat) :
    KPA K0 b0 r0 RN (callDM env rp rq p q bl key goal region : CM Map (NextL S)) := by
  have hnone : KPA K0 b0 r0 RN (match key, env.ring bl, env.need bl with
      | Option.none, Option.none, some bNed => do
        let subNed ← needOrdAllocRegs bNed
        let (subPes, callBlock) ← monoBlocks bl subNed goal
        let nexArg : NextL S := ⟨ofSure (lazyReg subPes), jmp0 callBlock⟩
        let nexFol ← (if safeFolFol q then pure ⟨ofSure Sure.bunt, nexArg.th⟩
          else rq (CGoalL.next (ofSure Sure.bunt) nexArg.th) region : CM Map (NextL S))
        let nexFol ← pastL env.cod nexFol p region
        let nexSub ← rp (CGoalL.next nexArg.laz nexFol.th) region
        copyL nexSub nexFol.laz
      | _, _, _ => fun _ => Option.none : CM Map (NextL S)) := by
    split
    · refine KPA.bind' (kpa_needOrd _) fun subNed K1 bb1 r1 X1 _ => ?_
      refine KPA.bind' (kpa_monoBlocksG hk bl subNed (hg.up X1) (hd.gd.up X1.2.1)) fun x K2 bb2 r2 X2 hx => ?_
      rcases x with ⟨sp, cb⟩
      exact kpa_callTailGX env.cod hp hq p q region _ (jmp0 cb) hx.1 (jok_jmp0 _) (lzL_ofSure _ _)
        ⟨gxl_reg hx.2, Raw.labUniq_ofSure _⟩
    · exact KPA.fail
  unfold callDM
  cases goal with
  | next laz th =>
    by_cases hc : (env.pure bl && noneEquivalentL laz) = true
    · simp only [hc, ↓reduceIte]
      exact kpa_callTailGX env.cod hp hq p q region _ th hg.1 hg.2.1 (lzL_ofSure _ _)
        ⟨gxl_bunt _, Raw.labUniq_ofSure _⟩
    · simp only [hc, ↓reduceIte, Bool.false_eq_true]
      exact hnone
  | pick z o => exact hnone
  | done => exact hnone

/-- **The indirect call keeps `InvA`**, with `RunGX` parts. -/
theorem kpa_callLIX (hk : KerfG S Map) (env : CallEnv) {rp rq : CGoalL S → List Nat → CM Map (NextL S)}
    (hp : RunGX rp) (hq : RunGX rq) (p q : Nomm) (sup : Option Nomm) {K0 : Nat → Nat → Prop} {b0 r0 : Nat}
    {goal : CGoalL S} (hg : GFL K0 b0 goal) (hd : GU r0 goal) (region : List Nat) :
    KPA K0 b0 r0 RN (callL env rp rq p q Option.none sup goal region : CM Map (NextL S)) := by
  unfold callL
  refine KPA.bind' (kpa_simpleNextLG hg hd.gd) fun nex K1 b1 r1 X1 hn => ?_
  refine KPA.bind' (hk K1 b1 r1 nex hn.1 hn.2.1 hn.2.2.1 hn.2.2.2) fun op K2 b2 r2 X2 hop => ?_
  rcases op with ⟨out, pro⟩
  refine KPA.bind' KPA.re' fun rS K3 b3 r3 X3 hS => ?_
  refine KPA.bind' KPA.re' fun rF K4 b4 r4 X4 hF => ?_
  refine KPA.bind' (KPA.emit' (blockOK_one _ _ _ rfl (by simp [getJmps, jok_jmp0])) ?_) fun o K5 b5 r5 X5 ho => ?_
  · intro j hj; simp only [getJmps, List.mem_singleton] at hj; subst hj; exact (hop.1.up X3).up X4
  refine KPA.bind' (hq _ _ _ _ _ (gfl_next ho (jok_jmp0 _) (lzL_ofSure _ _)) (gu_reg (lt_up hF.2 X5)))
    fun n1 K6 b6 r6 X6 h1 => ?_
  refine KPA.bind' (kpa_pastL env.cod h1 p region) fun n2 K7 b7 r7 X7 h2 => ?_
  refine KPA.bind' (hp _ _ _ _ _ (gfl_next h2.1 h2.2.1 (lzL_ofSure _ _))
    (gu_reg (lt_up (lt_up (lt_up (lt_up hS.2 X4) X5) X6) X7))) fun n3 K8 b8 r8 X8 h3 => ?_
  exact kpa_copyL h3 (h2.2.2.up X8)

/-! ## The arms -/

section arms

variable (env : CallEnv) (sup : Option Nomm)

theorem runGX_n0 (ax : Nat) : RunGX (runLCM (S := S) (Map := Map) env true sup (Nomm.n0 ax)) :=
  fun K0 b0 r0 goal region hg hd => runG_n0 env sup ax K0 b0 r0 goal region hg hd.gd

theorem runGX_n1 (k : Noun) : RunGX (runLCM (S := S) (Map := Map) env true sup (Nomm.n1 k)) :=
  fun K0 b0 r0 goal region hg hd => runG_n1 env sup k K0 b0 r0 goal region hg hd.gd

theorem runGX_n3 {p : Nomm} (ih : RunGX (runLCM (S := S) (Map := Map) env true sup p)) :
    RunGX (runLCM (S := S) (Map := Map) env true sup (Nomm.n3 p)) := by
  intro K0 b0 r0 goal region hg hd
  simp only [runLCM]
  cases goal with
  | next laz th =>
    refine KPA.ite' _ (fun _ => ih _ _ _ _ _ hg hd) fun _ => ?_
    refine KPA.bind' (kpa_collapseLazyAtomL (nex := ⟨laz, th⟩) hg) fun a K1 b1 r1 X1 ha => ?_
    split
    · exact KPA.fail
    · rename_i r o
      refine KPA.bind' (kpa_forl r o (ha (r, o) rfl)) fun x K2 b2 r2 X2 hx => ?_
      obtain ⟨z, o'⟩ := x
      refine KPA.bind' KPA.re' fun r' K3 b3 r3 X3 hr' => ?_
      refine KPA.bind' (KPA.emit' (blockOK_nil _ _ (jok_two rfl (jok_jmp0 _) (jok_jmp0 _)))
        (fl_two rfl (hx.1.up X3) (hx.2.up X3))) fun oc K4 b4 r4 X4 hoc => ?_
      exact ih _ _ _ _ _ (gfl_next hoc (jok_jmp0 _) (lzL_ofSure _ _)) (gu_reg (lt_up hr'.2 X4))
  | pick z o =>
    refine KPA.bind' KPA.re' fun r K1 b1 r1 X1 hr => ?_
    refine KPA.bind' (KPA.emit' (blockOK_nil _ _ (jok_two rfl hg.2.1 hg.2.2.2))
      (fl_two rfl (hg.1.up X1) (hg.2.2.1.up X1))) fun oc K2 b2 r2 X2 hoc => ?_
    exact ih _ _ _ _ _ (gfl_next hoc (jok_jmp0 _) (lzL_ofSure _ _)) (gu_reg (lt_up hr.2 X2))
  | done =>
    refine KPA.bind' kpa_doneBlocks fun x K1 b1 r1 X1 hx => ?_
    obtain ⟨o0, o1⟩ := x
    refine KPA.bind' KPA.re' fun r K2 b2 r2 X2 hr => ?_
    refine KPA.bind' (KPA.emit' (blockOK_nil _ _ (jok_two rfl (jok_jmp0 _) (jok_jmp0 _)))
      (fl_two rfl (hx.1.up X2) (hx.2.up X2))) fun oc K3 b3 r3 X3 hoc => ?_
    exact ih _ _ _ _ _ (gfl_next hoc (jok_jmp0 _) (lzL_ofSure _ _)) (gu_reg (lt_up hr.2 X3))

theorem runGX_n4 {p : Nomm} (ih : RunGX (runLCM (S := S) (Map := Map) env true sup p)) :
    RunGX (runLCM (S := S) (Map := Map) env true sup (Nomm.n4 p)) := by
  intro K0 b0 r0 goal region hg hd
  simp only [runLCM]
  cases goal with
  | done =>
    refine KPA.bind' KPA.re' fun pro K1 b1 r1 X1 _ => ?_
    refine KPA.bind' KPA.re' fun arg K2 b2 r2 X2 harg => ?_
    refine KPA.bind' (KPA.emit' (blockOK_one _ _ _ rfl (jok_none rfl)) (fl_none rfl)) fun o K3 b3 r3 X3 ho => ?_
    exact ih _ _ _ _ _ (gfl_next ho (jok_jmp0 _) (lzL_ofSure _ _)) (gu_reg (lt_up harg.2 X3))
  | pick z o =>
    refine KPA.bind' KPA.re' fun pro K1 b1 r1 X1 _ => ?_
    refine KPA.bind' KPA.re' fun arg K2 b2 r2 X2 harg => ?_
    have X12 := X1.trans X2
    refine KPA.bind' (KPA.emit' (blockOK_one _ _ _ rfl (jok_two rfl hg.2.1 hg.2.2.2))
      (fl_two rfl (hg.1.up X12) (hg.2.2.1.up X12))) fun o K3 b3 r3 X3 ho => ?_
    exact ih _ _ _ _ _ (gfl_next ho (jok_jmp0 _) (lzL_ofSure _ _)) (gu_reg (lt_up harg.2 X3))
  | next laz th =>
    refine KPA.bind' (kpa_collapseLazyAtomL (nex := ⟨laz, th⟩) hg) fun a K1 b1 r1 X1 ha => ?_
    refine KPA.bind' (P := fun K b _ (x : Nat × Nat) => FL K b x.2) ?_ fun x K2 b2 r2 X2 hx => ?_
    · split
      · rename_i x
        exact KPA.pure' fun K b r X => (ha x rfl).up X
      · refine KPA.bind' KPA.re' fun r K2 b2 r2 X2 _ => ?_
        exact KPA.ite' _ (fun _ => KPA.pure' fun K b r' X => (hg.1.up (X1.trans X2)).up X) fun _ => KPA.fail
    · obtain ⟨pro, th'⟩ := x
      refine KPA.bind' KPA.re' fun arg K3 b3 r3 X3 harg => ?_
      refine KPA.bind' (KPA.emit' (blockOK_one _ _ _ rfl (by simp [getJmps, jok_jmp0]))
        (fl_one (hx.up X3))) fun o K4 b4 r4 X4 ho => ?_
      exact ih _ _ _ _ _ (gfl_next ho (jok_jmp0 _) (lzL_ofSure _ _)) (gu_reg (lt_up harg.2 X4))

/-- The two runs, `+past` and `+copy` of `%5` and of the indirect tail. -/
theorem kpa_twoRegsX {p q : Nomm} (ihp : RunGX (runLCM (S := S) (Map := Map) env true sup p))
    (ihq : RunGX (runLCM (S := S) (Map := Map) env true sup q)) {K0 : Nat → Nat → Prop} {b0 r0 : Nat}
    {rp rq o : Nat} (hrp : rp < r0) (hrq : rq < r0) (ho : FL K0 b0 o) (region : List Nat) :
    KPA K0 b0 r0 RN (do
      let nexq ← runLCM env true sup q (CGoalL.next (ofSure (lazyReg rq)) (jmp0 o)) region
      let nexq ← pastL env.cod nexq p region
      let nexp ← runLCM env true sup p (CGoalL.next (ofSure (lazyReg rp)) nexq.th) region
      copyL nexp nexq.laz : CM Map (NextL S)) := by
  refine KPA.bind' (ihq _ _ _ _ _ (gfl_next ho (jok_jmp0 _) (lzL_ofSure _ _)) (gu_reg hrq))
    fun n1 K1 b1 r1 X1 h1 => ?_
  refine KPA.bind' (kpa_pastL env.cod h1 p region) fun n2 K2 b2 r2 X2 h2 => ?_
  refine KPA.bind' (ihp _ _ _ _ _ (gfl_next h2.1 h2.2.1 (lzL_ofSure _ _)) (gu_reg (lt_up (lt_up hrp X1) X2)))
    fun n3 K3 b3 r3 X3 h3 => ?_
  exact kpa_copyL h3 (h2.2.2.up X3)

theorem runGX_n5 {p q : Nomm} (ihp : RunGX (runLCM (S := S) (Map := Map) env true sup p))
    (ihq : RunGX (runLCM (S := S) (Map := Map) env true sup q)) :
    RunGX (runLCM (S := S) (Map := Map) env true sup (Nomm.n5 p q)) := by
  intro K0 b0 r0 goal region hg hd
  simp only [runLCM]
  refine KPA.bind' KPA.re' fun rp K1 b1 r1 X1 hrp => ?_
  refine KPA.bind' KPA.re' fun rq K2 b2 r2 X2 hrq => ?_
  have X12 := X1.trans X2
  refine KPA.bind' (P := fun K b _ (o : Nat) => FL K b o) ?_ fun o K3 b3 r3 X3 ho =>
    kpa_twoRegsX env sup ihp ihq (lt_up (lt_up hrp.2 X2) X3) (lt_up hrq.2 X3) ho region
  cases goal with
  | pick z o =>
    exact KPA.emit' (blockOK_nil _ _ (jok_two rfl hg.2.1 hg.2.2.2)) (fl_two rfl (hg.1.up X12) (hg.2.2.1.up X12))
  | done =>
    refine KPA.bind' kpa_doneBlocks fun x K3 b3 r3 X3 hx => ?_
    obtain ⟨o0, o1⟩ := x
    exact KPA.emit' (blockOK_nil _ _ (jok_two rfl (jok_jmp0 _) (jok_jmp0 _))) (fl_two rfl hx.1 hx.2)
  | next laz th =>
    refine KPA.bind' (kpa_collapseLazyAtomL (nex := ⟨laz, th⟩) (RN.up (rr := r0) (n := ⟨laz, th⟩) hg X12 r2))
      fun a K3 b3 r3 X3 ha => ?_
    split
    · refine KPA.ite' _ (fun _ => ?_) fun _ => KPA.fail
      exact KPA.emit' (blockOK_one _ _ _ rfl (by simp [getJmps, jok_jmp0])) (fl_one ((hg.1.up X12).up X3))
    · rename_i r o
      refine KPA.bind' (kpa_forl r o (ha (r, o) rfl)) fun x K4 b4 r4 X4 hx => ?_
      obtain ⟨z, o'⟩ := x
      exact KPA.emit' (blockOK_nil _ _ (jok_two rfl (jok_jmp0 _) (jok_jmp0 _))) (fl_two rfl hx.1 hx.2)

theorem runGX_n7 {p q : Nomm} (ihp : RunGX (runLCM (S := S) (Map := Map) env true sup p))
    (ihq : RunGX (runLCM (S := S) (Map := Map) env true (some p) q))
    (dq : RunRX (runLCM (S := S) (Map := Map) env true (some p) q)) :
    RunGX (runLCM (S := S) (Map := Map) env true sup (Nomm.n7 p q)) := by
  intro K0 b0 r0 goal region hg hd
  simp only [runLCM]
  refine KPA.bind' (KPA.andRB (ihq _ _ _ _ _ hg hd) (dq _ _ _ _ _ hg hd)) fun nex K1 b1 r1 X1 hn => ?_
  exact ihp _ _ _ _ _ (gfl_next hn.1.1 hn.1.2.1 hn.1.2.2) hn.2

theorem runGX_cons {p q : Nomm} (ihp : RunGX (runLCM (S := S) (Map := Map) env true sup p))
    (ihq : RunGX (runLCM (S := S) (Map := Map) env true sup q)) :
    RunGX (runLCM (S := S) (Map := Map) env true sup (Nomm.cons p q)) := by
  intro K0 b0 r0 goal region hg hd
  simp only [runLCM]
  refine KPA.bind' (P := fun K b r (goal' : CGoalL S) => GFL K b goal' ∧ GU r goal') ?_
    fun goal' K1 b1 r1 X1 hg1 => ?_
  · cases goal with
    | done =>
      refine KPA.bind' KPA.re' fun r K1 b1 r1 X1 hr => ?_
      refine KPA.bind' (KPA.emit' (blockOK_nil _ _ (jok_none rfl)) (fl_none rfl)) fun o K2 b2 r2 X2 ho => ?_
      exact KPA.pure' fun K b r' X => ⟨gfl_next (ho.up X) (jok_jmp0 _) (lzL_ofSure _ _),
        gu_reg (lt_up (lt_up hr.2 X2) X)⟩
    | pick z o => exact KPA.pure' fun K b r X => ⟨hg.up X, trivial, trivial⟩
    | next laz th => exact KPA.pure' fun K b r X => ⟨hg.up X, GU.up (goal := CGoalL.next laz th) hd X.2.1⟩
  obtain ⟨hg1, hd1⟩ := hg1
  cases goal' with
  | pick z o =>
    refine KPA.bind' (KPA.emit' (blockOK_nil _ _ (jok_none rfl)) (fl_none rfl)) fun o K2 b2 r2 X2 ho => ?_
    refine KPA.bind' (ihq _ _ _ _ _ (gfl_next ho (jok_jmp0 _) (lzL_ofSure _ _)) (gu_bunt _))
      fun n1 K3 b3 r3 X3 h1 => ?_
    refine KPA.bind' (kpa_pastL env.cod h1 p region) fun n2 K4 b4 r4 X4 h2 => ?_
    refine KPA.bind' (ihp _ _ _ _ _ (gfl_next h2.1 h2.2.1 (lzL_ofSure _ _)) (gu_bunt _))
      fun n3 K5 b5 r5 X5 h3 => ?_
    exact kpa_copyL h3 (h2.2.2.up X5)
  | next laz th =>
    refine KPA.bind' (KPA.andRB (kpa_splitL (nex := ⟨laz, th⟩) hg1)
      (rs_splitX env (nex := ⟨laz, th⟩) hd1.1 hd1.2 hg1.2.2)) fun x K2 b2 r2 X2 hx => ?_
    obtain ⟨hed, tel, o⟩ := x
    obtain ⟨⟨lh, lt, lo⟩, ⟨dh, uh⟩, ⟨dt, ut⟩⟩ := hx
    refine KPA.bind' (KPA.andRB (kpa_pastL (nex := ⟨hed, jmp0 o⟩) env.cod ⟨lo, jok_jmp0 _, lh⟩ q region)
      (rs_pastX env env.cod (nex := ⟨hed, jmp0 o⟩) dh uh lh q region)) fun nh K3 b3 r3 X3 hh => ?_
    refine KPA.bind' (ihq _ _ _ _ _ (gfl_next hh.1.1 hh.1.2.1 (lt.up X3)) ⟨Raw.gxl_up dt X3.2.1, ut⟩)
      fun n2 K4 b4 r4 X4 h2 => ?_
    refine KPA.bind' (kpa_pastL env.cod h2 p region) fun n2' K5 b5 r5 X5 h2' => ?_
    have X45 := X4.trans X5
    refine KPA.bind' (ihp _ _ _ _ _ (gfl_next h2'.1 h2'.2.1 (hh.1.2.2.up X45))
      ⟨Raw.gxl_up hh.2.1 X45.2.1, hh.2.2⟩) fun n1 K6 b6 r6 X6 h1 => ?_
    exact kpa_copyL h1 (h2'.2.2.up X6)
  | done => exact KPA.fail

theorem runGX_n10 {a : Nat} {v q : Nomm} (ihv : RunGX (runLCM (S := S) (Map := Map) env true sup v))
    (ihq : RunGX (runLCM (S := S) (Map := Map) env true sup q)) :
    RunGX (runLCM (S := S) (Map := Map) env true sup (Nomm.n10 a v q)) := by
  intro K0 b0 r0 goal region hg hd
  simp only [runLCM]
  refine KPA.bind' (kpa_simpleNextLGX hg hd) fun nex K1 b1 r1 X1 hn => ?_
  refine KPA.bind' (KPA.andRB (kpa_intoL (nex := nex) ⟨hn.1, hn.2.1, hn.2.2.1⟩ a)
    (rs_intoX env hn.2.2.2.1 hn.2.2.2.2 hn.2.2.1 a)) fun x K2 b2 r2 X2 hx => ?_
  obtain ⟨don, rec, o⟩ := x
  obtain ⟨⟨ld, lr, lo⟩, ⟨dd, ud⟩, ⟨dr, ur⟩⟩ := hx
  refine KPA.bind' (KPA.andRB (kpa_pastL (nex := ⟨rec, jmp0 o⟩) env.cod ⟨lo, jok_jmp0 _, lr⟩ v region)
    (rs_pastX env env.cod (nex := ⟨rec, jmp0 o⟩) dr ur lr v region)) fun nr K3 b3 r3 X3 hr => ?_
  refine KPA.bind' (ihv _ _ _ _ _ (gfl_next hr.1.1 hr.1.2.1 (ld.up X3)) ⟨Raw.gxl_up dd X3.2.1, ud⟩)
    fun n2 K4 b4 r4 X4 h2 => ?_
  refine KPA.bind' (kpa_pastL env.cod h2 q region) fun n2' K5 b5 r5 X5 h2' => ?_
  have X45 := X4.trans X5
  refine KPA.bind' (ihq _ _ _ _ _ (gfl_next h2'.1 h2'.2.1 (hr.1.2.2.up X45))
    ⟨Raw.gxl_up hr.2.1 X45.2.1, hr.2.2⟩) fun n1 K6 b6 r6 X6 h1 => ?_
  exact kpa_copyL h1 (h2'.2.2.up X6)

theorem runGX_n2 {p q : Nomm} (info : Option (Bell × Option Noun))
    (ihp : RunGX (runLCM (S := S) (Map := Map) env true sup p))
    (ihq : RunGX (runLCM (S := S) (Map := Map) env true sup q)) :
    RunGX (runLCM (S := S) (Map := Map) env true sup (Nomm.n2 p q info)) := by
  intro K0 b0 r0 goal region hg hd
  simp only [runLCM]
  cases info with
  | none => exact kpa_callLIX kerfG env ihp ihq p q sup hg hd region
  | some bk =>
    obtain ⟨b, key⟩ := bk
    exact kpa_callDMGX kerfG env ihp ihq p q b key hg hd region

end arms

/-! ## The induction, with no hypothesis -/

/-- **Every run of `runLCM env true` on a nomm with no `%6` keeps `InvA`**,
for a goal with `FL` jumps that meets `GU`, and returns a `RN` result: no
hypothesis (track D's `kimidX_noSix` in place of the false `KIMid`). -/
theorem runGX_lcm (env : CallEnv) :
    ∀ (nm : Nomm), NoSixC nm → ∀ sup, RunGX (runLCM (S := S) (Map := Map) env true sup nm)
  | Nomm.cons p q, h, sup => runGX_cons env sup (runGX_lcm env p h.1 sup) (runGX_lcm env q h.2 sup)
  | Nomm.n0 ax, _, sup => runGX_n0 env sup ax
  | Nomm.n1 k, _, sup => runGX_n1 env sup k
  | Nomm.n2 p q info, h, sup => runGX_n2 env sup info (runGX_lcm env p h.1 sup) (runGX_lcm env q h.2 sup)
  | Nomm.n3 p, h, sup => runGX_n3 env sup (runGX_lcm env p h sup)
  | Nomm.n4 p, h, sup => runGX_n4 env sup (runGX_lcm env p h sup)
  | Nomm.n5 p q, h, sup => runGX_n5 env sup (runGX_lcm env p h.1 sup) (runGX_lcm env q h.2 sup)
  | Nomm.n6 _ _ _, h, _ => h.elim
  | Nomm.n7 p q, h, sup => runGX_n7 env sup (runGX_lcm env p h.1 sup) (runGX_lcm env q h.2 (some p))
      (rs_runX env h.2 (some p))
  | Nomm.n10 a v q, h, sup => runGX_n10 env sup (runGX_lcm env v h.1 sup) (runGX_lcm env q h.2 sup)
  | Nomm.n11s _ _ _, _, sup => fun K0 b0 r0 goal region _ _ => by simp only [runLCM]; exact KPA.fail
  | Nomm.n11d _ _ _ _, _, sup => fun K0 b0 r0 goal region _ _ => by simp only [runLCM]; exact KPA.fail
  | Nomm.n12 _ _, _, sup => fun K0 b0 r0 goal region _ _ => by simp only [runLCM]; exact KPA.fail
  | Nomm.mean _ _ _ _ _, _, sup => fun K0 b0 r0 goal region _ _ => by simp only [runLCM]; exact KPA.fail

/-! ## The top `+kerf` -/

/-- **The state the top `+kerf` leaves**: `InvA K` and a start block
without annotation (no hypothesis: `runGX_lcm`, `kimidX_noSix`). -/
theorem top_kerfAX (env : CallEnv) {nm : Nomm} (hn : NoSixC nm) {nex : NextL S}
    {g1 g2 : Comp.Gen Map} {o sub : Nat}
    (h1 : runLCM env true Option.none nm (CGoalL.done : CGoalL S) [] gen0 = some (nex, g1))
    (h2 : kerf nex g1 = some ((o, sub), g2)) : ∃ K, InvA K g2 ∧ FL K g2.bo o := by
  obtain ⟨K1, hI1, X1, hR1⟩ := (runGX_lcm env nm hn Option.none (fun _ _ => False) 1 0 CGoalL.done [] trivial
    ⟨trivial, trivial⟩).k _ gen0 nex g1 invA_gen0 (by simp [gen0]) (XB.refl _ _ _) h1
  have hx := (Raw.kimidX_noSix (S := S) (Map := Map) env).run nm Option.none hn CGoalL.done [] gen0 g1 nex trivial
    trivial h1
  have hdn : LzS (DN g1.re) nex.laz := Raw.lzS_dn_of_gxl hx.1
  have h0 : 0 < g1.bo := Nat.lt_of_lt_of_le (by simp [gen0]) X1.1
  obtain ⟨K2, hI2, -, hfo, -⟩ := (kerfG K1 g1.bo g1.re nex hR1.1 hR1.2.1 hR1.2.2 hdn).k K1 g1 (o, sub) g2 hI1 h0
    (XB.refl _ _ _) h2
  exact ⟨K2, hI2, hfo⟩

/-- **`GuardMonoC` on code with calls and no `%6`**, from the final pass
`StraightA` alone (no `KIMid`). -/
theorem guardMonoC_noSixX (hT : ∀ env, StraightA S Map env) : GuardMonoC S Map NoSixM := by
  intro env N bl nm c hf hs
  unfold finishLUCM at hs
  obtain ⟨⟨nex, g1⟩, h1, hs⟩ := Option.bind_eq_some_iff.mp hs
  obtain ⟨⟨⟨o, sub⟩, g2⟩, h2, hs⟩ := Option.bind_eq_some_iff.mp hs
  obtain ⟨K, hI, ho⟩ := top_kerfAX env hf h1 h2
  exact hT env nm hf nex g1 g2 o sub c K h1 h2 hI ho hs

/-- **`EntryMono` on code with calls and no `%6`** from track D's two
leaves and `StraightA` (no `KIMid`). -/
theorem entryMono_noSixX (lib : Lib) (hO : OptInMono S Map NoSixM) (hR : ReadsInMono S Map NoSixM)
    (hT : ∀ env, StraightA S Map env) : EntryMono S Map lib NoSixM :=
  entryMono_of lib hO hR (guardMonoC_noSixX hT)

end Glue
end SkaModel
end Formalization
