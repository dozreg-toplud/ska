import lemmas.Compiler.CompRunShapeTDefs

/-!
# `+run-shape`: the direct `%2` threading the rest, with a callee compiled inside it (track A, 2026-11-28)

The case `[2 p q [~ b k]]` (`rs_n2dW`) on `RsAtT`: the run of `q` (`l-fol`) moves the rest from `y`
to `y1`; `+laze-past` runs at `y1`; the need push (`+callee-need`) moves it from `y1` to `y2` (a miss
in `nary.cache` compiles the callee, `+callee-compiled`, and returns the bigger cache; a hit or a
member of the SCC keeps it), `+callee-sure` and the soft test run at `y2`, the run of `p` moves it to
`y3`; `+laze-copy` runs at `y3`.  On a cell key there is no need push and `+callee-sure` is read at
`y1`, where its value does not matter (the soft test is `|`).

* `rsd_nedX`: the need push from the `+callee-need` equation at `y` to `y1`.
* `rsd_surG`: the push `sur` for any `+callee-sure` value.
* `rsdNdTail`, `rsd_ndG`: `l-sub` after the need push, from the rest the push returns.
* **`rsd_ndT`**, `rsd_folT`, `rsd_subT`.
* **`rs_n2dT`**: the case on `RsAtT`, from `ShapeCallT` at every rest of `E`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun} {E : RsRest → Prop} {Rl : RsRest → RsRest → Prop}

/-- **The need push on a key that is not a cell**, from `+callee-need` taking the rest from `y`
to `y1`. -/
theorem rsd_nedX (b : Bell) (k : Option Noun) (hk : konstCell k = false) (nb : NeedOrd)
    (L1 L0 DR PU SIM P Q GN SN : Noun) (st : RSt CSet) (y y1 : RsRest)
    (hne : nock (C cneBat (C b.toNoun (rsDoor st y ctx))) cneBat = some (C nb.toNoun (rsGenNoun st y1))) :
    nock (rsdS4 L1 L0 DR PU SIM P Q b k GN SN (rsDoor st y ctx)) rsdNed = some (C nb.toNoun (rsGenNoun st y1)) := by
  unfold rsdNed rsdS4
  simp only [rsDoor] at hne
  rcases k with _ | (a | ⟨a1, a2⟩)
  · simp [nock_exec, rsS, rsCoreG, rsDoor, unitNoun, rsd_cne_at', hne]
  · simp [nock_exec, rsS, rsCoreG, rsDoor, unitNoun, rsd_cne_at', hne]
  · simp [konstCell] at hk

/-- **The push `sur`** for any value `sur` that `+callee-sure` returns. -/
theorem rsd_surG (hc : CompIn ctx) (b : Bell) (k : Option Noun) (NED L1 L0 DR PU SIM P Q GN SN : Noun)
    (st : RSt CSet) (y : RsRest) (sur : NeedOrd)
    (hcole : ∃ cole, slot? 6846 ctx = some cole ∧ getF mugF b.toNoun cole = some (A 0))
    (hhot : ∃ jh, slot? 54 ctx = some jh)
    (hsu : ∀ st : RSt CSet, nock (C csuBat (C b.toNoun (rsDoor st y ctx))) csuBat = some sur.toNoun) :
    nock (C NED (rsdS4 L1 L0 DR PU SIM P Q b k GN SN (rsDoor st y ctx))) rsdSur = some sur.toNoun := by
  obtain ⟨cole, hc1, hgc⟩ := hcole
  obtain ⟨jh, hjh⟩ := hhot
  have hgt := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ b.toNoun cole (A 0) hgc
  have hc' : slot? 262143 ctx = some layer2 := hc
  have hs := hsu st
  simp only [rsDoor] at hs
  unfold rsdSur rsdS4
  simp [nock_exec, rsS, rsCoreG, rsDoor, hc', hc1, by_arm, by.arm_at, by.get.arm_at, get_arm, hgt, hjh, biff_arm,
    biff.arm_at, biff_gate_nil, rsd_csu_at', hs]

/-- `l-sub` after the need push and the soft test, in the model. -/
noncomputable def rsdNdTail (env : ShapeEnv) (sup : Option Nomm) (p : Nomm) (ned : NeedOrd) (soft : Bool) :
    SM CSet (Laze CSet) :=
  if !soft then runShape env sup p (GoalS.next (nedL ned)) else do
    let i ← idS
    putSofs i
    runShape env sup p (GoalS.next (Laze.mk SureO.bunt [] [(i, nedL ned)]))

section
variable (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
include hc h7 hcode

/-- **`l-sub` from the rest the need push returns**: the need push takes the rest from `y` to
`y1`, `+callee-sure` returns `sur` at `y1`, the soft test returns `soft`; then the run of `p` at
`y1`. -/
theorem rsd_ndG (env : ShapeEnv) (hcn : CodeNomms env.cod cod) (p q : Nomm) (hcp : CallCode cod (shapeCE env) p)
    (hcq : CallCode cod (shapeCE env) q) (b : Bell) (k : Option Noun) (sup : Option Nomm) (st : RSt CSet)
    (y y1 : RsRest) (ned sur : NeedOrd) (soft : Bool) (L1 L0 DR PU SIM GN : Noun)
    (hned : nock (rsdS4 L1 L0 DR PU SIM p.toNoun q.toNoun b k GN (supNoun sup) (rsDoor st y ctx)) rsdNed
      = some (C ned.toNoun (rsGenNoun st y1)))
    (hcole : ∃ cole, slot? 6846 ctx = some cole ∧ getF mugF b.toNoun cole = some (A 0))
    (hhot : ∃ jh, slot? 54 ctx = some jh)
    (hsu : ∀ st : RSt CSet, nock (C csuBat (C b.toNoun (rsDoor st y1 ctx))) csuBat = some sur.toNoun)
    (es : softTest env p q b k ned sur sup = some soft)
    (hp : ∀ l st1, LzNZ l → ∃ y2, Rl y1 y2 ∧ E y2 ∧
      nock (rsCoreG p.toNoun (GoalS.next l).toNoun (supNoun sup) (rsDoor st1 y1 ctx)) rsGate
        = (runShape env sup p (GoalS.next l) st1).map fun r => C r.1.toNoun (rsGenNoun r.2 y2)) :
    ∃ y2, Rl y1 y2 ∧ E y2 ∧
      nock (rsdS4 L1 L0 DR PU SIM p.toNoun q.toNoun b k GN (supNoun sup) (rsDoor st y ctx)) rsdND
        = (rsdNdTail env sup p ned soft st).map fun r => C r.1.toNoun (rsGenNoun r.2 y2) := by
  have hsur := rsd_surG hc b k ned.toNoun L1 L0 DR PU SIM p.toNoun q.toNoun GN (supNoun sup) st y1 sur hcole hhot hsu
  have hst := rsd_st h7 hcode env hcn p q hcp hcq b k ned sur sup soft es L1 L0 DR PU SIM GN st y1
  simp only [rsdS4, rsS, rsCoreG, rsDoor] at hned hsur hst
  unfold rsdND rsdS4
  cases soft with
  | false =>
    obtain ⟨y2, hR2, hy2, hp'⟩ := hp (nedL ned) st (lzNZ_nedL ned)
    refine ⟨y2, hR2, hy2, ?_⟩
    simp only [rsCoreG, rsDoor, GoalS.toNoun, nedL, Laze.toNoun, SureO.toNoun, Laze.forksNoun, Laze.bondsNoun,
      HoonSet.toNoun_empty] at hp'
    simp [nock_exec, rsS, rsCoreG, rsDoor, hned, hsur, hst, bind, StateT.bind, rsdNdTail, rsdSn, hp', nedL]
  | true =>
    obtain ⟨y2, hR2, hy2, hp'⟩ := hp (Laze.mk SureO.bunt [] [(st.idg, nedL ned)])
      { idg := st.idg + 1, sofs := HoonSet.put st.sofs st.idg } (lzNZ_softL st.idg ned)
    refine ⟨y2, hR2, hy2, ?_⟩
    simp only [rsCoreG, rsDoor, rsGenNoun, GoalS.toNoun, nedL, Laze.toNoun, SureO.toNoun, SureO.bunt,
      Laze.forksNoun, Laze.bondsNoun, HoonSet.toNoun_empty, NeedOrd.toNoun, Tag.none] at hp'
    have hpu := cs_put_in st.sofs st.idg
    have hid := rs_id (ctx := ctx) st y1
    simp only [rsGenNoun] at hid
    have hc' : slot? 262143 ctx = some layer2 := hc
    simp only [rsGenNoun] at hned hsur hst ⊢
    simp [nock_exec, rsS, rsCoreG, rsDoor, rsGenNoun, hned, hsur, hst, bind, StateT.bind, rsdNdTail, rsdSy,
      hp', nedL, idS, putSofs, lzp_id_at', comp_id_at, hid, SureO.bunt, hc', in.arm_at, in_arm, in.put.arm_at,
      put_in_arm, hpu]

/-- **`l-sub` when the call is not dropped, threading the rest**: on a key that is not a cell the need
push moves the rest (`ShapeCallT.need`), then `rsd_ndG`; on a cell key `[this+~ gen]` and `rsd_ndG`
at the same rest with the soft test `|`. -/
theorem rsd_ndT (env : ShapeEnv) (hR : RlPre Rl) (hcn : CodeNomms env.cod cod) (p q : Nomm)
    (hcp : CallCode cod (shapeCE env) p) (hcq : CallCode cod (shapeCE env) q) (b : Bell) (k : Option Noun)
    (sup : Option Nomm) (st : RSt CSet) (y : RsRest) (hy : E y) (hsc : ShapeCallT ctx env E Rl p q b k sup y)
    (L1 L0 DR PU SIM GN : Noun)
    (hp : ∀ l st1, LzNZ l → RsAtT ctx env E Rl p sup (GoalS.next l) st1) :
    ∃ y', Rl y y' ∧ E y' ∧
      nock (rsdS4 L1 L0 DR PU SIM p.toNoun q.toNoun b k GN (supNoun sup) (rsDoor st y ctx)) rsdND
        = (rsdNdM env sup p q b k st).map fun r => C r.1.toNoun (rsGenNoun r.2 y') := by
  cases hk : konstCell k with
  | false =>
    obtain ⟨nb, e, hn⟩ := hsc.need hk
    obtain ⟨y1, hR1, hy1, hne, hsu⟩ := hn st
    have hned := rsd_nedX b k hk nb L1 L0 DR PU SIM p.toNoun q.toNoun GN (supNoun sup) st y y1 hne
    obtain ⟨soft, es⟩ := Option.ne_none_iff_exists'.mp
      (hsc.soft nb (fun h => by rw [hk] at h; cases h) (fun _ => e))
    obtain ⟨y2, hR2, hy2, h⟩ := rsd_ndG hc h7 hcode env hcn p q hcp hcq b k sup st y y1 nb (env.sure b) soft
      L1 L0 DR PU SIM GN hned hsc.cole hsc.hot hsu es (fun l st1 hl => hp l st1 hl y1 hy1)
    refine ⟨y2, hR.trans hR1 hR2, hy2, ?_⟩
    rw [h]
    have hm : rsdNedM env b k st = some (nb, st) := by
      rcases k with _ | (a | ⟨a1, a2⟩)
      · simp [rsdNedM, shLiftS, e]
      · simp [rsdNedM, shLiftS, e]
      · simp [konstCell] at hk
    congr 1
    simp [rsdNdM, hm, bind, StateT.bind, hsc.jet, shLiftS, es, rsdNdTail]
  | true =>
    obtain ⟨sur0, hsu⟩ := hsc.sureK hk
    obtain ⟨a1, a2, rfl⟩ : ∃ a1 a2, k = some (C a1 a2) := by
      rcases k with _ | (a | ⟨a1, a2⟩) <;> simp [konstCell] at hk ⊢
    have hned := rsd_ned (ctx := ctx) env b (some (C a1 a2)) L1 L0 DR PU SIM p.toNoun q.toNoun GN (supNoun sup) st y
      (fun h => by simp [konstCell] at h)
    have hm : rsdNedM env b (some (C a1 a2)) st = some (NeedOrd.this, st) := by
      simp [rsdNedM, pure, StateT.pure]
    rw [hm] at hned
    simp only [Option.map_some] at hned
    obtain ⟨y2, hR2, hy2, h⟩ := rsd_ndG hc h7 hcode env hcn p q hcp hcq b (some (C a1 a2)) sup st y y NeedOrd.this
      sur0 false L1 L0 DR PU SIM GN hned hsc.cole hsc.hot hsu (by simp [softTest])
      (fun l st1 hl => hp l st1 hl y hy)
    refine ⟨y2, hR2, hy2, ?_⟩
    rw [h]
    congr 1
    all_goals simp [rsdNdM, hm, bind, StateT.bind, hsc.jet, shLiftS, softTest, rsdNdTail]

/-- **`l-fol`, threading the rest**: `[none gen]` at the same rest when `+safe-fol-fol` holds of `q`,
else the run of `q` on `[%next none]`. -/
theorem rsd_folT (env : ShapeEnv) (hR : RlPre Rl) (sup : Option Nomm) (p q : Nomm) (b : Bell)
    (k : Option Noun) (DR PU SIM GN : Noun) (st : RSt CSet) (y : RsRest) (hy : E y)
    (hq : ∃ y1, Rl y y1 ∧ E y1 ∧
      nock (rsCoreG q.toNoun (GoalS.next (noneL : Laze CSet)).toNoun (supNoun sup) (rsDoor st y ctx)) rsGate
        = (runShape env sup q (GoalS.next noneL) st).map fun r => C r.1.toNoun (rsGenNoun r.2 y1)) :
    ∃ y1, Rl y y1 ∧ E y1 ∧
      nock (C DR (C PU (rsS SIM (C (A 2) (C p.toNoun (C q.toNoun (C (A 0) (C b.toNoun (unitNoun id k))))))
        GN (supNoun sup) (rsDoor st y ctx)))) rsdFol
        = (rsdFolM env sup q st).map fun r => C r.1.toNoun (rsGenNoun r.2 y1) := by
  have h63 := crd_ctx63 h7
  have hsa : slot? 767 ana = some safe_fol_fol.arm := safe_fol_fol.arm_at
  have hsf := safe_fol_fol_pill q
  cases hs : safeFolFol q with
  | true =>
    refine ⟨y, hR.refl y, hy, ?_⟩
    unfold rsdFol rsdFolM
    simp [nock_exec, rsS, rsCoreG, rsDoor, h63, hsa, safe_fol_fol_arm, hsf, hs, loob, pure, StateT.pure, noneL_noun]
  | false =>
    obtain ⟨y1, hR1, hy1, hq'⟩ := hq
    simp only [rsCoreG, rsDoor, GoalS.toNoun, noneL_noun] at hq'
    refine ⟨y1, hR1, hy1, ?_⟩
    unfold rsdFol rsdFolM
    simp [nock_exec, rsS, rsCoreG, rsDoor, h63, hsa, safe_fol_fol_arm, hsf, hs, loob, hq']

/-- **`l-sub`, threading the rest**: under `drop` the run of `p` on `[%next none]`, else `rsd_ndT`. -/
theorem rsd_subT (env : ShapeEnv) (hR : RlPre Rl) (hcn : CodeNomms env.cod cod) (p q : Nomm)
    (hcp : CallCode cod (shapeCE env) p) (hcq : CallCode cod (shapeCE env) q) (b : Bell) (k : Option Noun)
    (sup : Option Nomm) (st : RSt CSet) (y : RsRest) (hy : E y) (hsc : ShapeCallT ctx env E Rl p q b k sup y)
    (dr : Bool) (L1 L0 PU SIM GN : Noun)
    (hp : ∀ l st1, LzNZ l → RsAtT ctx env E Rl p sup (GoalS.next l) st1) :
    ∃ y', Rl y y' ∧ E y' ∧
      nock (rsdS4 L1 L0 (loob dr) PU SIM p.toNoun q.toNoun b k GN (supNoun sup) (rsDoor st y ctx)) rsdSub
        = (rsdSubM env sup p q b k dr st).map fun r => C r.1.toNoun (rsGenNoun r.2 y') := by
  cases dr with
  | false =>
    obtain ⟨y', hR', hy', hnd⟩ := rsd_ndT hc h7 hcode env hR hcn p q hcp hcq b k sup st y hy hsc L1 L0 (loob false)
      PU SIM GN hp
    refine ⟨y', hR', hy', ?_⟩
    unfold rsdSubM
    unfold rsdSub
    simp only [rsdS4, loob] at hnd ⊢
    simp [nock_exec]
    exact hnd
  | true =>
    obtain ⟨y', hR', hy', hp'⟩ := hp noneL st lzNZ_noneL y hy
    refine ⟨y', hR', hy', ?_⟩
    simp only [rsCoreG, rsDoor, GoalS.toNoun, noneL_noun] at hp'
    unfold rsdSubM rsdSub rsdS4
    simp [nock_exec, rsS, rsCoreG, rsDoor, loob, hp']

/-- **The direct case `[2 p q [~ b k]]`, threading the rest**: on every goal, from the runs of `p`
and `q` on goals of `LzNZ` on `RsAtT`, where `ShapeCallT` holds at every rest of `E` (the need push
may compile the callee and return a bigger cache). -/
theorem rs_n2dT (env : ShapeEnv) (hR : RlPre Rl) (hcn : CodeNomms env.cod cod) (p q : Nomm) (b : Bell)
    (k : Option Noun) (sup : Option Nomm) (goal : GoalS CSet) (st : RSt CSet)
    (hcc : CallCode cod (shapeCE env) (Nomm.n2 p q (some (b, k))))
    (hsc : ∀ y, E y → ShapeCallT ctx env E Rl p q b k sup y)
    (hq : ∀ l st1, LzNZ l → RsAtT ctx env E Rl q sup (GoalS.next l) st1)
    (hp : ∀ l st1, LzNZ l → RsAtT ctx env E Rl p sup (GoalS.next l) st1) :
    RsAtT ctx env E Rl (Nomm.n2 p q (some (b, k))) sup goal st := by
  intro y hy
  obtain ⟨⟨hpure, hpe⟩, hcp, hcq⟩ := hcc
  obtain ⟨V, hgot, hv⟩ := hpure
  have hpb : env.pure b = some ((env.pure b).getD false) := hpe
  have hv' : slot? 6 V = some (loob ((env.pure b).getD false)) := hv
  clear hv hpe
  generalize (env.pure b).getD false = pu at hv' hpb
  have hpu := rsd_pu hc hcode p.toNoun q.toNoun b.toNoun (unitNoun id k) V (loob pu) (rsSimpleN goal) goal.toNoun
    (supNoun sup) st y hgot hv'
  have hdr := rsd_dr hc pu (C (A 2) (C p.toNoun (C q.toNoun (C (A 0) (C b.toNoun (unitNoun id k))))))
    (supNoun sup) goal st y
  obtain ⟨y1, hR1, hy1, hfo⟩ := rsd_folT hc h7 hcode env hR sup p q b k (loob (rsdDrop pu goal)) (loob pu) (rsSimpleN goal)
    goal.toNoun st y hy (hq noneL st lzNZ_noneL y hy)
  simp only [rsS, rsCoreG, rsDoor] at hpu hdr hfo
  cases e1 : rsdFolM env sup q st with
  | none =>
    rw [e1] at hfo
    refine ⟨y1, hR1, hy1, ?_⟩
    rw [runShape_n2d, rsd_nomm, rs_push, rs_disp_n2, rsK2_eq]
    unfold rsdArm rsdD
    simp [nock_exec, rsS, rsCoreG, rsDoor, hpu, hdr, hfo, hpb, shLiftS, bind, StateT.bind, e1]
  | some r1 =>
    obtain ⟨lf, st1⟩ := r1
    rw [e1] at hfo
    have hpa := lzp_gate h7 hcode env p hcp st1 y1 lf
    simp only [rsDoor] at hpa
    cases e2 : lazePast env lf p st1 with
    | none =>
      rw [e2] at hpa
      refine ⟨y1, hR1, hy1, ?_⟩
      rw [runShape_n2d, rsd_nomm, rs_push, rs_disp_n2, rsK2_eq]
      unfold rsdArm rsdD
      simp [nock_exec, rsS, rsCoreG, rsDoor, hpu, hdr, hfo, hpb, shLiftS, bind, StateT.bind, e1, rsdPa, lzp_at', lzpArm,
        hpa, e2]
    | some r2 =>
      obtain ⟨lf', st2⟩ := r2
      rw [e2] at hpa
      obtain ⟨y2, hR2, hy2, hsb⟩ := rsd_subT hc h7 hcode env hR hcn p q hcp hcq b k sup st2 y1 hy1 (hsc y1 hy1)
        (rsdDrop pu goal) lf'.toNoun lf.toNoun (loob pu) (rsSimpleN goal) goal.toNoun hp
      simp only [rsdS4, rsS, rsCoreG, rsDoor] at hsb
      refine ⟨y2, hR.trans hR1 hR2, hy2, ?_⟩
      rw [runShape_n2d, rsd_nomm, rs_push, rs_disp_n2, rsK2_eq]
      unfold rsdArm rsdD
      cases e3 : rsdSubM env sup p q b k (rsdDrop pu goal) st2 with
      | none =>
        rw [e3] at hsb
        simp [nock_exec, rsS, rsCoreG, rsDoor, hpu, hdr, hfo, hpb, shLiftS, bind, StateT.bind, e1, rsdPa, lzp_at', lzpArm,
          hpa, e2, hsb, e3]
      | some r3 =>
        obtain ⟨ls, st3⟩ := r3
        rw [e3] at hsb
        have hlc := lc_all hc h7 (rsGenNoun st3 y2) ls lf'
        cases e4 : lazeCopy ls lf' with
        | none =>
          rw [e4] at hlc
          simp [nock_exec, rsS, rsCoreG, rsDoor, hpu, hdr, hfo, hpb, shLiftS, bind, StateT.bind, e1, rsdPa, lzp_at', lzpArm,
            hpa, e2, hsb, e3, rsdEnd, lc_at', lc_arm, hlc, e4]
        | some l =>
          rw [e4] at hlc
          simp [nock_exec, rsS, rsCoreG, rsDoor, hpu, hdr, hfo, hpb, shLiftS, bind, StateT.bind, e1, rsdPa, lzp_at', lzpArm,
            hpa, e2, hsb, e3, rsdEnd, lc_at', lc_arm, hlc, e4]

end

end Compiler
end Formalization
