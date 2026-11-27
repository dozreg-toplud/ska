import lemmas.Compiler.CompRunShapeTen
import lemmas.Compiler.CompRunShapeTwoCut
import lemmas.Compiler.CompRunDirectC
import lemmas.Compiler.CompSofPush
import lemmas.Compiler.CompSofSoft

/-!
# `+run-shape`: the direct `%2` case (track A, 2026-11-27)

The case `[2 p q [~ b k]]` (`rsdD`, cut in `CompRunShapeTwoCut.lean`) against `runShape` on
`Nomm.n2 p q (some (b, k))`.  The case reads the rest of `gen` through `+callee-need` (which
reads `cache`), so the statement is `RsAtE`: `RsAt` on the rests `y` of `gen` of a property `E`.

What the case reads beyond `CompIn ctx`, `K` at axis `7` and the code table `cod` at axis `52`
of `ctx`:
* `CallCode cod (shapeCE env)` of the nomm: the code entry of `b` with its `pure`
  (`CodePure`, `env.pure b ≠ none`), and the callees of `p` and `q` (for `+hinted`);
* `CodeNomms env.cod cod` (for `+sound-far`, `sf_gate`);
* `ShapeCall` at every rest of `E`: `+callee-need` returns `env.need b` and leaves `gen` as it is
  (unless the key is a cell, where it is not called), `call.cole.jets` has no ring for `b`
  (so `jet` is `|` and `sur` is `+callee-sure`), `+callee-sure` returns `env.sure b`, and the
  model's soft test returns on the needs the case reaches.

* **`rs_n2dW`**: the case, from the runs of `p` and `q` on goals of `LzNZ`.
* `twoNz`: the case keeps `LzNZ`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun}

/-- **`RsAt` on the rests `y` of `gen` of a property `E`.** -/
def RsAtE (ctx : Noun) (env : ShapeEnv) (E : RsRest → Prop) (n : Nomm) (sup : Option Nomm)
    (goal : GoalS CSet) (st : RSt CSet) : Prop :=
  ∀ y : RsRest, E y → nock (rsCoreG n.toNoun goal.toNoun (supNoun sup) (rsDoor st y ctx)) rsGate
    = (runShape env sup n goal st).map fun p => C p.1.toNoun (rsGenNoun p.2 y)

theorem rsAtE_of {env : ShapeEnv} {E : RsRest → Prop} {n : Nomm} {sup : Option Nomm} {goal : GoalS CSet}
    {st : RSt CSet} (h : RsAt ctx env n sup goal st) : RsAtE ctx env E n sup goal st :=
  fun y _ => h y

/-- Whether the key is a cell `[~ ^]` (the need is then `[%this ~]`). -/
def konstCell : Option Noun → Bool
  | some (Noun.cell _ _) => true
  | _ => false

/-- **What the direct call reads of the door and of `ctx`** for the callee `b` with the key `k`,
at the rest `y` of `gen`. -/
structure ShapeCall (ctx : Noun) (env : ShapeEnv) (p q : Nomm) (b : Bell) (k : Option Noun)
    (sup : Option Nomm) (y : RsRest) : Prop where
  need : konstCell k = false → ∃ nb, env.need b = some nb ∧ ∀ st : RSt CSet,
    nock (C cneBat (C b.toNoun (rsDoor st y ctx))) cneBat = some (C nb.toNoun (rsGenNoun st y))
  cole : ∃ cole, slot? 6846 ctx = some cole ∧ getF mugF b.toNoun cole = some (A 0)
  hot : ∃ jh, slot? 54 ctx = some jh
  jet : env.jet b = false
  sure : ∀ st : RSt CSet, nock (C csuBat (C b.toNoun (rsDoor st y ctx))) csuBat = some (env.sure b).toNoun
  soft : ∀ ned : NeedOrd, (konstCell k = true → ned = NeedOrd.this) →
    (konstCell k = false → env.need b = some ned) → softTest env p q b k ned (env.sure b) sup ≠ Option.none

/-- The need of the callee, in the model. -/
noncomputable def rsdNedM (env : ShapeEnv) (b : Bell) (k : Option Noun) : SM CSet NeedOrd :=
  match k with
  | some (Noun.cell _ _) => pure NeedOrd.this
  | _ => shLiftS (env.need b)

/-- `l-sub` of the direct case when the call is not dropped, in the model. -/
noncomputable def rsdNdM (env : ShapeEnv) (sup : Option Nomm) (p q : Nomm) (b : Bell) (k : Option Noun) :
    SM CSet (Laze CSet) := do
  let ned ← rsdNedM env b k
  let sur := if env.jet b then NeedOrd.none else env.sure b
  let soft ← shLiftS (softTest env p q b k ned sur sup)
  if !soft then runShape env sup p (GoalS.next (nedL ned)) else do
    let i ← idS
    putSofs i
    runShape env sup p (GoalS.next (Laze.mk SureO.bunt [] [(i, nedL ned)]))

/-- `l-sub` of the direct case, in the model. -/
noncomputable def rsdSubM (env : ShapeEnv) (sup : Option Nomm) (p q : Nomm) (b : Bell) (k : Option Noun)
    (drop : Bool) : SM CSet (Laze CSet) :=
  if drop then runShape env sup p (GoalS.next noneL) else rsdNdM env sup p q b k

/-- `drop` of the direct case, in the model. -/
noncomputable def rsdDrop (pu : Bool) (goal : GoalS CSet) : Bool :=
  pu && (match goal with | GoalS.next l => noneEq l | _ => false)

/-- `l-fol` of the direct case, in the model. -/
noncomputable def rsdFolM (env : ShapeEnv) (sup : Option Nomm) (q : Nomm) : SM CSet (Laze CSet) :=
  if safeFolFol q then pure noneL else runShape env sup q (GoalS.next noneL)

/-- The model's direct case in these parts. -/
theorem runShape_n2d (env : ShapeEnv) (sup : Option Nomm) (p q : Nomm) (b : Bell) (k : Option Noun)
    (goal : GoalS CSet) :
    runShape env sup (Nomm.n2 p q (some (b, k))) goal = (do
      let pu ← shLiftS (env.pure b)
      let lf ← rsdFolM env sup q
      let lf ← lazePast env lf p
      let ls ← rsdSubM env sup p q b k (rsdDrop pu goal)
      shLiftS (lazeCopy ls lf) : SM CSet (Laze CSet)) := by
  cases goal <;> rcases k with _ | (_ | ⟨_, _⟩) <;> rw [runShape] <;> first | rfl | simp [rsdSubM, rsdNdM, rsdNedM]

theorem rsK2_eq : rsK2 = rsdArm := by
  unfold rsK2; rw [rsd_at]; rfl

theorem rs_disp_n2 (t s goal sup D : Noun) :
    nock (rsS s (C (A 2) t) goal sup D) rsDol = nock (rsS s (C (A 2) t) goal sup D) rsK2 := by
  nock_open rsDol
  simp [nock_exec, rsS, rsCoreG, rsTc, rsT]

/-- The noun of the direct nomm. -/
theorem rsd_nomm (p q : Nomm) (b : Bell) (k : Option Noun) :
    (Nomm.n2 p q (some (b, k))).toNoun = C (A 2) (C p.toNoun (C q.toNoun (C (A 0) (C b.toNoun (unitNoun id k))))) :=
  rfl

/-- The `+callee-need` arm at its core axis. -/
theorem rsd_cne_at' (y : Noun) : slot? 0x55ffc (C comp.door y)
    = some (C (A 8) (C (C (A 1) (C (C (A 1) (A 0)) (C (A 0) (A 0)))) (C (C (A 1) cneBat) (C (A 0) (A 1))))) := by
  kernel_rfl

/-- The `+callee-sure` arm at its core axis. -/
theorem rsd_csu_at' (y : Noun) : slot? 0x17dc (C comp.door y)
    = some (C (A 8) (C (C (A 1) (C (C (A 1) (A 0)) (C (A 0) (A 0)))) (C (C (A 1) csuBat) (C (A 0) (A 1))))) := by
  kernel_rfl

/-- The `+sound` arm at its core axis. -/
theorem rsd_snd_at' (y : Noun) : slot? 0x5556 (C comp.door y) = some sndArm := by kernel_rfl

/-- The `+made` arm at its core axis. -/
theorem rsd_made_at' (y : Noun) : slot? 0x55f6 (C comp.door y) = some madArm := by kernel_rfl

/-- **The push `pure`**: the flag `pure` of the code entry of `b`. -/
theorem rsd_pu (hc : CompIn ctx) {cod : Noun} (hcode : slot? 52 ctx = some cod) (P Q B KN V PV SIM GN SN : Noun)
    (st : RSt CSet) (y : RsRest) (hgot : getF mugF B cod = some (C (A 0) V)) (hv : slot? 6 V = some PV) :
    nock (rsS SIM (C (A 2) (C P (C Q (C (A 0) (C B KN))))) GN SN (rsDoor st y ctx)) rsdPu = some PV := by
  have hgt := got_gate (mug := mugF) layer2 ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ B cod V hgot
  have hc' : slot? 262143 ctx = some layer2 := hc
  unfold rsdPu
  simp [nock_exec, rsS, rsCoreG, rsDoor, hc', hcode, by.arm_at, by_arm, by.got.arm_at, got_arm, hgt, hv]

/-- **The push `drop`**. -/
theorem rsd_dr (hc : CompIn ctx) (pu : Bool) (N SN : Noun) (goal : GoalS CSet) (st : RSt CSet) (y : RsRest) :
    nock (C (loob pu) (rsS (rsSimpleN goal) N goal.toNoun SN (rsDoor st y ctx))) rsdDr
      = some (loob (rsdDrop pu goal)) := by
  unfold rsdDr
  cases pu with
  | false => cases goal <;> simp [nock_exec, rsS, rsCoreG, rsDoor, GoalS.toNoun, rsdDrop, loob]
  | true =>
    cases goal with
    | next l =>
      have hl := lne_all hc (rsGenNoun st y) l
      cases e : noneEq l <;> rw [e] at hl <;>
        simp [nock_exec, rsS, rsCoreG, rsDoor, GoalS.toNoun, rsdDrop, loob, lne_at', lneArm, hl, e]
    | pick => simp [nock_exec, rsS, rsCoreG, rsDoor, GoalS.toNoun, rsdDrop, loob]
    | done => simp [nock_exec, rsS, rsCoreG, rsDoor, GoalS.toNoun, rsdDrop, loob]


/-- The subject of `l-sub`: `[lf' [lf [drop [pure S0]]]]` over the case's subject. -/
noncomputable def rsdS4 (L1 L0 DR PU SIM P Q : Noun) (b : Bell) (k : Option Noun) (GN SN : Noun) (D : Noun) : Noun :=
  C L1 (C L0 (C DR (C PU (rsS SIM (C (A 2) (C P (C Q (C (A 0) (C b.toNoun (unitNoun id k)))))) GN SN D))))

/-- **The push `ned`**: `[this+~ gen]` on a cell key, else `+callee-need`. -/
theorem rsd_ned (env : ShapeEnv) (b : Bell) (k : Option Noun) (L1 L0 DR PU SIM P Q GN SN : Noun)
    (st : RSt CSet) (y : RsRest)
    (hn : konstCell k = false → ∃ nb, env.need b = some nb ∧ ∀ st : RSt CSet,
      nock (C cneBat (C b.toNoun (rsDoor st y ctx))) cneBat = some (C nb.toNoun (rsGenNoun st y))) :
    nock (rsdS4 L1 L0 DR PU SIM P Q b k GN SN (rsDoor st y ctx)) rsdNed
      = (rsdNedM env b k st).map fun r => C r.1.toNoun (rsGenNoun r.2 y) := by
  unfold rsdNed rsdS4
  rcases k with _ | (a | ⟨a1, a2⟩)
  · obtain ⟨nb, e, h⟩ := hn rfl
    have h' := h st
    simp only [rsDoor] at h'
    simp [nock_exec, rsS, rsCoreG, rsDoor, unitNoun, rsd_cne_at', h', rsdNedM, shLiftS, e]
  · obtain ⟨nb, e, h⟩ := hn rfl
    have h' := h st
    simp only [rsDoor] at h'
    simp [nock_exec, rsS, rsCoreG, rsDoor, unitNoun, rsd_cne_at', h', rsdNedM, shLiftS, e]
  · simp [nock_exec, rsS, rsCoreG, rsDoor, unitNoun, rsdNedM, pure, StateT.pure, NeedOrd.toNoun, Tag.this]

/-- **The push `sur`**: no ring for `b`, so `+callee-sure`. -/
theorem rsd_sur (hc : CompIn ctx) (env : ShapeEnv) (b : Bell) (k : Option Noun) (NED L1 L0 DR PU SIM P Q GN SN : Noun)
    (st : RSt CSet) (y : RsRest)
    (hcole : ∃ cole, slot? 6846 ctx = some cole ∧ getF mugF b.toNoun cole = some (A 0))
    (hhot : ∃ jh, slot? 54 ctx = some jh)
    (hsu : ∀ st : RSt CSet, nock (C csuBat (C b.toNoun (rsDoor st y ctx))) csuBat = some (env.sure b).toNoun) :
    nock (C NED (rsdS4 L1 L0 DR PU SIM P Q b k GN SN (rsDoor st y ctx))) rsdSur = some (env.sure b).toNoun := by
  obtain ⟨cole, hc1, hgc⟩ := hcole
  obtain ⟨jh, hjh⟩ := hhot
  have hgt := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ b.toNoun cole (A 0) hgc
  have hc' : slot? 262143 ctx = some layer2 := hc
  have hs := hsu st
  simp only [rsDoor] at hs
  unfold rsdSur rsdS4
  simp [nock_exec, rsS, rsCoreG, rsDoor, hc', hc1, by_arm, by.arm_at, by.get.arm_at, get_arm, hgt, hjh, biff_arm,
    biff.arm_at, biff_gate_nil, rsd_csu_at', hs]

/-- `+sound` on this door: `+sound-far` on `[nom ned code.long-ska 3]`. -/
theorem rsd_snd (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (G nomN nedN : Noun) :
    nock (C sndBat (C (C nomN nedN) (C comp.door (C G ctx)))) sndBat
      = nock (C sfBat (C (C nomN (C nedN (C cod (A 3)))) compK)) sfBat := by
  have hK := compK_sf
  conv => lhs; arg 2; unfold sndBat
  simp [nock_exec, h7, hcode, hK, sf_arm]

/-- **The soft test**, where the model returns. -/
theorem rsd_st (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod) (env : ShapeEnv)
    (hcn : CodeNomms env.cod cod) (p q : Nomm) (hcp : CallCode cod (shapeCE env) p)
    (hcq : CallCode cod (shapeCE env) q) (b : Bell) (k : Option Noun) (ned sur : NeedOrd) (sup : Option Nomm)
    (soft : Bool) (hs : softTest env p q b k ned sur sup = some soft) (L1 L0 DR PU SIM GN : Noun)
    (st : RSt CSet) (y : RsRest) :
    nock (C sur.toNoun (C ned.toNoun (rsdS4 L1 L0 DR PU SIM p.toNoun q.toNoun b k GN (supNoun sup)
      (rsDoor st y ctx)))) rsdSt = some (loob soft) := by
  unfold rsdSt rsdS4
  have hu0 : unitNoun id (Option.none : Option Noun) = A 0 := rfl
  rcases k with _ | kk
  · simp only [softTest] at hs
    obtain ⟨s, e1, hs⟩ := Option.bind_eq_some_iff.mp hs
    have hsf := sf_gate env.cod cod hcn 3 (made p sup) ned s e1
    have hsn := rsd_snd h7 hcode (rsGenNoun st y) (made p sup).toNoun ned.toNoun
    have hmd := made_gate (C comp.door (C (rsGenNoun st y) ctx)) p sup
    cases s with
    | true =>
      simp only [if_true, Option.some.injEq] at hs
      subst hs
      simp [nock_exec, rsS, rsCoreG, rsDoor, hu0, supNoun, rsd_snd_at', rsd_made_at', madArm, snd_arm, hmd,
        hsn, hsf, loob]
    | false =>
      simp only [Bool.false_eq_true, if_false] at hs
      rcases e2 : needSoft ned sur b.less with _ | t
      · rw [e2] at hs; simp [orB] at hs
      have hns := ns_gate ned sur b.less t e2
      rcases e3 : hinted env.pure p with _ | h1
      · exact absurd e3 (callCode_hinted cod (shapeCE env) p hcp)
      have hh1 := hd_gateR cod (shapeCE env) p h1 hcp e3
      rcases e4 : hinted env.pure q with _ | h2
      · exact absurd e4 (callCode_hinted cod (shapeCE env) q hcq)
      have hh2 := hd_gateR cod (shapeCE env) q h2 hcq e4
      rw [e2, e3, e4] at hs
      cases t <;> cases h1 <;> cases h2 <;> simp [orB] at hs <;> subst hs <;>
        simp [nock_exec, rsS, rsCoreG, rsDoor, hu0, supNoun, rsd_snd_at', rsd_made_at', madArm, snd_arm, hmd,
          hsn, hsf, loob, h7, hcode, compK_ns, ns_arm, hns, compK_hd, hd_arm, hh1, hh2, Bell.toNoun]
  · simp only [softTest, Option.some.injEq] at hs
    subst hs
    simp [nock_exec, rsS, rsCoreG, rsDoor, unitNoun, loob]


theorem rsdNedM_spec {env : ShapeEnv} {b : Bell} {k : Option Noun} {st st1 : RSt CSet} {ned : NeedOrd}
    (h : rsdNedM env b k st = some (ned, st1)) :
    st1 = st ∧ (konstCell k = true → ned = NeedOrd.this) ∧ (konstCell k = false → env.need b = some ned) := by
  rcases k with _ | (a | ⟨a1, a2⟩)
  · cases e : env.need b <;> simp [rsdNedM, shLiftS, e] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by simp [konstCell], fun _ => rfl⟩
  · cases e : env.need b <;> simp [rsdNedM, shLiftS, e] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by simp [konstCell], fun _ => rfl⟩
  · simp [rsdNedM, pure, StateT.pure] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, fun _ => rfl, by simp [konstCell]⟩

theorem lzNZ_softL (i : Nat) (ned : NeedOrd) : LzNZ (Laze.mk SureO.bunt [] [(i, nedL ned)] : Laze CSet) :=
  ⟨fun y hy => absurd hy (HoonSet.mem_empty y), trivial, ⟨lzNZ_nedL ned, trivial⟩⟩

/-- **`l-sub` when the call is not dropped**: `rsdNdM`. -/
theorem rsd_nd (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : ShapeEnv) (hcn : CodeNomms env.cod cod) (p q : Nomm) (hcp : CallCode cod (shapeCE env) p)
    (hcq : CallCode cod (shapeCE env) q) (b : Bell) (k : Option Noun) (sup : Option Nomm) (st : RSt CSet)
    (y : RsRest) (hsc : ShapeCall ctx env p q b k sup y) (L1 L0 DR PU SIM GN : Noun)
    (hp : ∀ l st1, LzNZ l → nock (rsCoreG p.toNoun (GoalS.next l).toNoun (supNoun sup) (rsDoor st1 y ctx)) rsGate
      = (runShape env sup p (GoalS.next l) st1).map fun r => C r.1.toNoun (rsGenNoun r.2 y)) :
    nock (rsdS4 L1 L0 DR PU SIM p.toNoun q.toNoun b k GN (supNoun sup) (rsDoor st y ctx)) rsdND
      = (rsdNdM env sup p q b k st).map fun r => C r.1.toNoun (rsGenNoun r.2 y) := by
  have hned := rsd_ned env b k L1 L0 DR PU SIM p.toNoun q.toNoun GN (supNoun sup) st y hsc.need
  unfold rsdNdM
  cases e1 : rsdNedM env b k st with
  | none =>
    rw [e1] at hned
    simp only [rsdS4, rsS, rsCoreG, rsDoor] at hned
    unfold rsdND rsdS4
    simp [nock_exec, rsS, rsCoreG, rsDoor, hned, bind, StateT.bind, e1]
  | some r1 =>
    obtain ⟨ned, st1⟩ := r1
    obtain ⟨hst1, hk1, hk2⟩ := rsdNedM_spec e1
    subst st1
    rw [e1] at hned
    simp only [Option.map_some] at hned
    obtain ⟨soft, es⟩ := Option.ne_none_iff_exists'.mp (hsc.soft ned hk1 hk2)
    have hsur := rsd_sur hc env b k ned.toNoun L1 L0 DR PU SIM p.toNoun q.toNoun GN (supNoun sup) st y hsc.cole
      hsc.hot hsc.sure
    have hst := rsd_st h7 hcode env hcn p q hcp hcq b k ned (env.sure b) sup soft es L1 L0 DR PU SIM GN st y
    have hj := hsc.jet
    simp only [rsdS4, rsS, rsCoreG, rsDoor] at hned hsur hst
    unfold rsdND rsdS4
    cases soft with
    | false =>
      have hp' := hp (nedL ned) st (lzNZ_nedL ned)
      simp only [rsCoreG, rsDoor, GoalS.toNoun, nedL, Laze.toNoun, SureO.toNoun, Laze.forksNoun, Laze.bondsNoun,
        HoonSet.toNoun_empty] at hp'
      simp [nock_exec, rsS, rsCoreG, rsDoor, hned, hsur, hst, bind, StateT.bind, e1, es, hj, shLiftS, rsdSn, hp',
        nedL]
    | true =>
      have hp' := hp (Laze.mk SureO.bunt [] [(st.idg, nedL ned)])
        { idg := st.idg + 1, sofs := HoonSet.put st.sofs st.idg } (lzNZ_softL st.idg ned)
      simp only [rsCoreG, rsDoor, rsGenNoun, GoalS.toNoun, nedL, Laze.toNoun, SureO.toNoun, SureO.bunt,
        Laze.forksNoun, Laze.bondsNoun, HoonSet.toNoun_empty, NeedOrd.toNoun, Tag.none] at hp'
      have hpu := cs_put_in st.sofs st.idg
      have hid := rs_id (ctx := ctx) st y
      simp only [rsGenNoun] at hid
      have hc' : slot? 262143 ctx = some layer2 := hc
      simp only [rsGenNoun] at hned hsur hst ⊢
      simp [nock_exec, rsS, rsCoreG, rsDoor, rsGenNoun, hned, hsur, hst, bind, StateT.bind, e1, es, hj, shLiftS, rsdSy,
        hp', nedL, idS, putSofs, lzp_id_at', comp_id_at, hid, SureO.bunt, hc', in.arm_at, in_arm, in.put.arm_at, put_in_arm, hpu]


/-- **`l-fol`**: `[none gen]` when `+safe-fol-fol` holds of `q`, else the run of `q` on
`[%next none]`. -/
theorem rsd_fol (h7 : slot? 7 ctx = some compK) (env : ShapeEnv) (sup : Option Nomm) (p q : Nomm) (b : Bell)
    (k : Option Noun) (DR PU SIM GN : Noun) (st : RSt CSet) (y : RsRest)
    (hq : nock (rsCoreG q.toNoun (GoalS.next (noneL : Laze CSet)).toNoun (supNoun sup) (rsDoor st y ctx)) rsGate
      = (runShape env sup q (GoalS.next noneL) st).map fun r => C r.1.toNoun (rsGenNoun r.2 y)) :
    nock (C DR (C PU (rsS SIM (C (A 2) (C p.toNoun (C q.toNoun (C (A 0) (C b.toNoun (unitNoun id k))))))
      GN (supNoun sup) (rsDoor st y ctx)))) rsdFol
      = (rsdFolM env sup q st).map fun r => C r.1.toNoun (rsGenNoun r.2 y) := by
  have h63 := crd_ctx63 h7
  have hsa : slot? 767 ana = some safe_fol_fol.arm := safe_fol_fol.arm_at
  have hsf := safe_fol_fol_pill q
  simp only [rsCoreG, rsDoor, GoalS.toNoun, noneL_noun] at hq
  unfold rsdFol rsdFolM
  cases hs : safeFolFol q with
  | true =>
    simp [nock_exec, rsS, rsCoreG, rsDoor, h63, hsa, safe_fol_fol_arm, hsf, hs, loob, pure, StateT.pure, noneL_noun]
  | false =>
    simp [nock_exec, rsS, rsCoreG, rsDoor, h63, hsa, safe_fol_fol_arm, hsf, hs, loob, hq]

/-- **`l-sub`**: under `drop` the run of `p` on `[%next none]`, else `rsd_nd`. -/
theorem rsd_sub (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : ShapeEnv) (hcn : CodeNomms env.cod cod) (p q : Nomm) (hcp : CallCode cod (shapeCE env) p)
    (hcq : CallCode cod (shapeCE env) q) (b : Bell) (k : Option Noun) (sup : Option Nomm) (st : RSt CSet)
    (y : RsRest) (hsc : ShapeCall ctx env p q b k sup y) (dr : Bool) (L1 L0 PU SIM GN : Noun)
    (hp : ∀ l st1, LzNZ l → nock (rsCoreG p.toNoun (GoalS.next l).toNoun (supNoun sup) (rsDoor st1 y ctx)) rsGate
      = (runShape env sup p (GoalS.next l) st1).map fun r => C r.1.toNoun (rsGenNoun r.2 y)) :
    nock (rsdS4 L1 L0 (loob dr) PU SIM p.toNoun q.toNoun b k GN (supNoun sup) (rsDoor st y ctx)) rsdSub
      = (rsdSubM env sup p q b k dr st).map fun r => C r.1.toNoun (rsGenNoun r.2 y) := by
  cases dr with
  | false =>
    have hnd := rsd_nd hc h7 hcode env hcn p q hcp hcq b k sup st y hsc L1 L0 (loob false) PU SIM GN hp
    unfold rsdSubM
    unfold rsdSub
    simp only [rsdS4, loob] at hnd ⊢
    simp [nock_exec]
    exact hnd
  | true =>
    have hp' := hp noneL st lzNZ_noneL
    simp only [rsCoreG, rsDoor, GoalS.toNoun, noneL_noun] at hp'
    unfold rsdSubM rsdSub rsdS4
    simp [nock_exec, rsS, rsCoreG, rsDoor, loob, hp']


/-- **The direct case `[2 p q [~ b k]]`**, on every goal, from the runs of `p` and `q` on goals of
`LzNZ`, on the rests of `gen` of `E`, where `ShapeCall` holds at each. -/
theorem rs_n2dW (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : ShapeEnv) (hcn : CodeNomms env.cod cod) (p q : Nomm) (b : Bell) (k : Option Noun)
    (sup : Option Nomm) (goal : GoalS CSet) (st : RSt CSet) (E : RsRest → Prop)
    (hcc : CallCode cod (shapeCE env) (Nomm.n2 p q (some (b, k))))
    (hsc : ∀ y, E y → ShapeCall ctx env p q b k sup y)
    (hq : ∀ l st1, LzNZ l → RsAtE ctx env E q sup (GoalS.next l) st1)
    (hp : ∀ l st1, LzNZ l → RsAtE ctx env E p sup (GoalS.next l) st1) :
    RsAtE ctx env E (Nomm.n2 p q (some (b, k))) sup goal st := by
  intro y hy
  obtain ⟨⟨hpure, hpe⟩, hcp, hcq⟩ := hcc
  obtain ⟨V, hgot, hv⟩ := hpure
  have hpb : env.pure b = some ((env.pure b).getD false) := hpe
  have hv' : slot? 6 V = some (loob ((env.pure b).getD false)) := hv
  clear hv hpe
  generalize (env.pure b).getD false = pu at hv' hpb
  rw [runShape_n2d, rsd_nomm, rs_push, rs_disp_n2, rsK2_eq]
  have hpu := rsd_pu hc hcode p.toNoun q.toNoun b.toNoun (unitNoun id k) V (loob pu) (rsSimpleN goal) goal.toNoun
    (supNoun sup) st y hgot hv'
  have hdr := rsd_dr hc pu (C (A 2) (C p.toNoun (C q.toNoun (C (A 0) (C b.toNoun (unitNoun id k))))))
    (supNoun sup) goal st y
  have hfo := rsd_fol h7 env sup p q b k (loob (rsdDrop pu goal)) (loob pu) (rsSimpleN goal) goal.toNoun st y
    (hq noneL st lzNZ_noneL y hy)
  simp only [rsS, rsCoreG, rsDoor] at hpu hdr hfo
  unfold rsdArm rsdD
  cases e1 : rsdFolM env sup q st with
  | none =>
    rw [e1] at hfo
    simp [nock_exec, rsS, rsCoreG, rsDoor, hpu, hdr, hfo, hpb, shLiftS, bind, StateT.bind, e1]
  | some r1 =>
    obtain ⟨lf, st1⟩ := r1
    rw [e1] at hfo
    have hpa := lzp_gate h7 hcode env p hcp st1 y lf
    simp only [rsDoor] at hpa
    cases e2 : lazePast env lf p st1 with
    | none =>
      rw [e2] at hpa
      simp [nock_exec, rsS, rsCoreG, rsDoor, hpu, hdr, hfo, hpb, shLiftS, bind, StateT.bind, e1, rsdPa, lzp_at', lzpArm,
        hpa, e2]
    | some r2 =>
      obtain ⟨lf', st2⟩ := r2
      rw [e2] at hpa
      have hsb := rsd_sub hc h7 hcode env hcn p q hcp hcq b k sup st2 y (hsc y hy) (rsdDrop pu goal) lf'.toNoun
        lf.toNoun (loob pu) (rsSimpleN goal) goal.toNoun (fun l st3 hl => hp l st3 hl y hy)
      simp only [rsdS4, rsS, rsCoreG, rsDoor] at hsb
      cases e3 : rsdSubM env sup p q b k (rsdDrop pu goal) st2 with
      | none =>
        rw [e3] at hsb
        simp [nock_exec, rsS, rsCoreG, rsDoor, hpu, hdr, hfo, hpb, shLiftS, bind, StateT.bind, e1, rsdPa, lzp_at', lzpArm,
          hpa, e2, hsb, e3]
      | some r3 =>
        obtain ⟨ls, st3⟩ := r3
        rw [e3] at hsb
        have hlc := lc_all hc h7 (rsGenNoun st3 y) ls lf'
        cases e4 : lazeCopy ls lf' with
        | none =>
          rw [e4] at hlc
          simp [nock_exec, rsS, rsCoreG, rsDoor, hpu, hdr, hfo, hpb, shLiftS, bind, StateT.bind, e1, rsdPa, lzp_at', lzpArm,
            hpa, e2, hsb, e3, rsdEnd, lc_at', lc_arm, hlc, e4]
        | some l =>
          rw [e4] at hlc
          simp [nock_exec, rsS, rsCoreG, rsDoor, hpu, hdr, hfo, hpb, shLiftS, bind, StateT.bind, e1, rsdPa, lzp_at', lzpArm,
            hpa, e2, hsb, e3, rsdEnd, lc_at', lc_arm, hlc, e4]


/-- `l-sub` keeps `LzNZ`, given that the runs of `p` do. -/
theorem rsdSubM_nz (env : ShapeEnv) (sup : Option Nomm) (p q : Nomm) (b : Bell) (k : Option Noun) (dr : Bool)
    (hrp : ∀ g st l st1, GoalNZ g → runShape env sup p g st = some (l, st1) → LzNZ l)
    (st : RSt CSet) (l : Laze CSet) (st1 : RSt CSet) (e : rsdSubM env sup p q b k dr st = some (l, st1)) :
    LzNZ l := by
  unfold rsdSubM at e
  cases dr with
  | true => exact hrp (GoalS.next noneL) st l st1 lzNZ_noneL e
  | false =>
    simp only [Bool.false_eq_true, if_false, rsdNdM] at e
    obtain ⟨ned, s1, e1, e⟩ := sm_bind_some e
    obtain ⟨soft, s2, e2, e⟩ := sm_bind_some e
    cases soft with
    | false => exact hrp (GoalS.next (nedL ned)) s2 l st1 (lzNZ_nedL ned) e
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, if_false] at e
      obtain ⟨i, s3, e3, e⟩ := sm_bind_some e
      obtain ⟨u, s4, e4, e⟩ := sm_bind_some e
      exact hrp (GoalS.next (Laze.mk SureO.bunt [] [(i, nedL ned)])) s4 l st1 (lzNZ_softL i ned) e

/-- **The direct case keeps `LzNZ`**, given that the runs of `p` and `q` do. -/
theorem twoNz (env : ShapeEnv) (p q : Nomm) (b : Bell) (k : Option Noun) (sup : Option Nomm) (goal : GoalS CSet)
    (hrp : ∀ g st l st1, GoalNZ g → runShape env sup p g st = some (l, st1) → LzNZ l)
    (hrq : ∀ g st l st1, GoalNZ g → runShape env sup q g st = some (l, st1) → LzNZ l)
    (st : RSt CSet) (l : Laze CSet) (st1 : RSt CSet)
    (e : runShape env sup (Nomm.n2 p q (some (b, k))) goal st = some (l, st1)) : LzNZ l := by
  rw [runShape_n2d] at e
  obtain ⟨pu, s1, e1, e⟩ := sm_bind_some e
  obtain ⟨lf, s2, e2, e⟩ := sm_bind_some e
  obtain ⟨lf', s3, e3, e⟩ := sm_bind_some e
  obtain ⟨ls, s4, e4, e⟩ := sm_bind_some e
  have h2 : LzNZ lf := by
    unfold rsdFolM at e2
    cases hs : safeFolFol q with
    | true =>
      simp only [hs, if_true, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e2
      rw [← e2.1]; exact lzNZ_noneL
    | false =>
      simp only [hs, Bool.false_eq_true, if_false] at e2
      exact hrq (GoalS.next noneL) s1 lf s2 lzNZ_noneL e2
  have h3 := lazePast_nz env lf p s2 lf' s3 h2 e3
  have h4 := rsdSubM_nz env sup p q b k _ hrp s3 ls s4 e4
  exact lazeCopyEnd_nz h4 h3 e

end Compiler
end Formalization
