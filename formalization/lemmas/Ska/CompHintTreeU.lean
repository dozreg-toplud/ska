import lemmas.Ska.CompHintLSU

/-!
# `CallTreeHU`: hints not kept around any member (README Gaps 24.13)

`CallTreeH` with the hints not kept (`n11s` with `hintStatic tag = false`,
`n11d` with `hintDynamic tag = false` and a safe clue) around ANY member,
pure ones included (`[11 %foo [4 [0 3]]]`).  The composition lemmas take of
each part `KindU` (`CompHintKind.lean`), the copies of `tools/gen/lokhu.py`
(`CompHintLSU.lean`); the cons's index asks `+hinted` of the tail (a tail
under a hint not kept is neither pure nor hinted).

* `CallTreeHU.kindU`: every member has `KindU` (the `TotalC` of composites).
* `lokSHU_callTreeHU`, `callTreeHU_done`, **`finishLUCH_contractCallTreeHU`**
  (both halves of the contract at the top, traces included),
  `finishLUCH_bellContractCallTreeHU`, `CallTreeH.toU` (the old class is in
  the new one).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]
variable {snd : Nomm → NeedOrd → Bool}

/-- **`CallTreeH` with the hints not kept around any member.** -/
inductive CallTreeHU (lib : Lib) (env : CallEnv) (N : Needs) : (Noun → Prop) → Bool → Noun → Nomm → Prop
  | base {P : Noun → Prop} {x : Bool} {f : Noun} {nm : Nomm} :
      CallTreeD lib env N P x f nm → nm.noHint = true → CallTreeHU lib env N P x f nm
  | cons {P : Noun → Prop} {b1 b2 : Bool} {a1 a2 b : Noun} {p q : Nomm} :
      CallTreeHU lib env N P b1 (C a1 a2) p → CallTreeHU lib env N P b2 b q →
      CallTreeHU lib env N P (b2 && (b1 || decide (hinted env.cod q = some true))) (C (C a1 a2) b) (Nomm.cons p q)
  | ind {P : Noun → Prop} {b1 b2 : Bool} {b c : Noun} {p q : Nomm} :
      CallTreeHU lib env N P b1 b p → CallTreeHU lib env N P b2 c q →
      CallTreeHU lib env N P true (n3 (A 2) b c) (Nomm.n2 p q Option.none)
  | seven {P : Noun → Prop} {b2 : Bool} {b c : Noun} {p q : Nomm} :
      CallTreeHU lib env N P true b p → CallTreeHU lib env N (Img lib P b) b2 c q →
      CallTreeHU lib env N P b2 (n3 (A 7) b c) (Nomm.n7 p q)
  | four {P : Noun → Prop} {b1 : Bool} {b : Noun} {p : Nomm} :
      CallTreeHU lib env N P b1 b p → CallTreeHU lib env N P false (n2 (A 4) b) (Nomm.n4 p)
  | three {P : Noun → Prop} {b1 : Bool} {b : Noun} {p : Nomm} :
      CallTreeHU lib env N P b1 b p → CallTreeHU lib env N P false (n2 (A 3) b) (Nomm.n3 p)
  | five {P : Noun → Prop} {b1 b2 : Bool} {b c : Noun} {p q : Nomm} :
      CallTreeHU lib env N P b1 b p → CallTreeHU lib env N P b2 c q →
      CallTreeHU lib env N P false (n3 (A 5) b c) (Nomm.n5 p q)
  | n11s {P : Noun → Prop} {x : Bool} {f : Noun} {q : Nomm} {tag : Nat} (body : Noun) :
      CallTreeHU lib env N P x f q → hintStatic tag = false →
      CallTreeHU lib env N P x (n3 (A 11) (A tag) f) (Nomm.n11s tag q body)
  | n11d {P : Noun → Prop} {x : Bool} {f fh : Noun} {q h : Nomm} {tag : Nat} (body : Noun) :
      CallTreeHU lib env N P x f q → hintDynamic tag = false → safeNomm h = true → ClueSafe lib P fh →
      hinted env.cod h = some false → sixCount h = 0 →
      CallTreeHU lib env N P x (n3 (A 11) (C (A tag) fh) f) (Nomm.n11d tag h q body)

section
variable {lib : Lib} {env : CallEnv} {N : Needs}

theorem CallTreeHU.sixCount {P : Noun → Prop} {x : Bool} {f : Noun} {nm : Nomm}
    (h : CallTreeHU lib env N P x f nm) : sixCount nm = 0 := by
  induction h with
  | base hD _ => exact hD.sixCount
  | cons _ _ ihp ihq => simp only [Comp.sixCount, ihp, ihq]
  | ind _ _ ihp ihq => simp only [Comp.sixCount, ihp, ihq]
  | seven _ _ ihp ihq => simp only [Comp.sixCount, ihp, ihq]
  | four _ ihp => simp only [Comp.sixCount, ihp]
  | three _ ihp => simp only [Comp.sixCount, ihp]
  | five _ _ ihp ihq => simp only [Comp.sixCount, ihp, ihq]
  | n11s _ _ _ ih => simp only [Comp.sixCount, ih]
  | n11d _ _ _ _ _ _ h6 ih => simp only [Comp.sixCount, ih, h6]

theorem CallTreeHU.cell {P : Noun → Prop} {x : Bool} {f : Noun} {nm : Nomm} (h : CallTreeHU lib env N P x f nm) :
    ∃ a b, f = C a b := by
  cases h with
  | base hD _ => exact hD.cell
  | _ => exact ⟨_, _, rfl⟩

theorem orB_false_false : orB (some false) (some false) = some false := rfl

/-- **Every member has `KindU`**: hinted, or not hinted with `TotalC`. -/
theorem CallTreeHU.kindU {P : Noun → Prop} {x : Bool} {f : Noun} {nm : Nomm} (h : CallTreeHU lib env N P x f nm) :
    KindU lib env.cod P f nm := by
  induction h with
  | base hD _ => exact KindU.of_kind hD.kind
  | @cons P b1 b2 a1 a2 b p q hp hq ihp ihq =>
    rcases ihp with ⟨e1, T1⟩ | e1
    · rcases ihq with ⟨e2, T2⟩ | e2
      · exact Or.inl ⟨by simp only [hinted, e1, e2]; rfl, totalC_cons ⟨_, _, rfl⟩ T1 T2⟩
      · exact Or.inr (by simp only [hinted, e1, e2]; rfl)
    · exact Or.inr (by simp only [hinted, e1]; rfl)
  | ind _ _ => exact Or.inr rfl
  | @seven P b2 b c p q hp hq ihp ihq =>
    rcases ihp with ⟨e1, T1⟩ | e1
    · rcases ihq with ⟨e2, T2⟩ | e2
      · exact Or.inl ⟨by simp only [hinted, e1, e2]; rfl, totalC_seven (minkC7_seven lib P b c) T1 T2⟩
      · exact Or.inr (by simp only [hinted, e1, e2]; rfl)
    · exact Or.inr (by simp only [hinted, e1]; rfl)
  | @four P b1 b p hp ihp =>
    rcases ihp with ⟨e1, T1⟩ | e1
    · exact Or.inl ⟨by simp only [hinted, e1], totalC_four (minkC4_four lib P b) T1⟩
    · exact Or.inr (by simp only [hinted, e1])
  | @three P b1 b p hp ihp =>
    rcases ihp with ⟨e1, T1⟩ | e1
    · exact Or.inl ⟨by simp only [hinted, e1], totalC_three (minkC3_three lib P b) T1⟩
    · exact Or.inr (by simp only [hinted, e1])
  | @five P b1 b2 b c p q hp hq ihp ihq =>
    rcases ihp with ⟨e1, T1⟩ | e1
    · rcases ihq with ⟨e2, T2⟩ | e2
      · exact Or.inl ⟨by simp only [hinted, e1, e2]; rfl, totalC_five (minkC5_five lib P b c) T1 T2⟩
      · exact Or.inr (by simp only [hinted, e1, e2]; rfl)
    · exact Or.inr (by simp only [hinted, e1]; rfl)
  | @n11s P x f q tag body hq hs ih =>
    rw [KindU, hinted_n11s hs]
    exact ih.elim (fun ⟨e, T⟩ => Or.inl ⟨e, totalC_minkAs (minkAs_n11s lib tag f) T⟩) Or.inr
  | @n11d P x f fh q h tag body hq hs hsafe hc hh h6 ih =>
    have e : hinted env.cod (Nomm.n11d tag h q body) = hinted env.cod q := by
      show orB (some (hintDynamic tag)) (orB (hinted env.cod h) (hinted env.cod q)) = _
      rw [hs, hh]; rfl
    rw [KindU, e]
    exact ih.elim (fun ⟨e, T⟩ => Or.inl ⟨e, totalC_minkAsP (minkAsP_n11d lib hs hc f) T⟩) Or.inr

/-- **The old class is in the new one** (with the same index: a member of
`CallTreeH` that is not pure is hinted, so the cons's index agrees). -/
theorem CallTreeH.toU {P : Noun → Prop} {x : Bool} {f : Noun} {nm : Nomm} (h : CallTreeH lib env N P x f nm) :
    CallTreeHU lib env N P x f nm := by
  induction h with
  | base hD hh => exact CallTreeHU.base hD hh
  | @cons P b1 b2 a1 a2 b p q hp hq ihp ihq =>
    have e : (!q.pure) = decide (hinted env.cod q = some true) := by
      cases ep : q.pure
      · simp [hq.hinted_of ep]
      · simp [hinted_pure env.cod q ep]
    rw [e]
    exact CallTreeHU.cons ihp ihq
  | ind _ _ ihp ihq => exact CallTreeHU.ind ihp ihq
  | seven _ _ ihp ihq => exact CallTreeHU.seven ihp ihq
  | four _ ihp => exact CallTreeHU.four ihp
  | three _ ihp => exact CallTreeHU.three ihp
  | five _ _ ihp ihq => exact CallTreeHU.five ihp ihq
  | n11s body _ hs _ ih => exact CallTreeHU.n11s body ih hs
  | n11d body _ hs hsafe hc hh h6 _ ih => exact CallTreeHU.n11d body ih hs hsafe hc hh h6

end

/-- **Every member of `CallTreeHU` meets `LOKSFH`** (a hinted one
`JNewLSFH`), and one of index `true` `LOKSH false` (a hinted one
`JNewLSH`): the text of `lokSH_callTreeH` with the copies for `KindU`. -/
theorem lokSHU_callTreeHU (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {x : Bool} {f : Noun}
    {nm : Nomm} (h : CallTreeHU lib env N P x f nm) :
    (LOKSFH (S := S) (Map := Map) snd lib N env P f nm ∧
        (hinted env.cod nm = some true → JNewLSFH (S := S) (Map := Map) snd env nm)) ∧
      (x = true → LOKSH (S := S) (Map := Map) snd false lib N env P f nm ∧
        (hinted env.cod nm = some true → JNewLSH (S := S) (Map := Map) snd env nm)) := by
  induction h with
  | @base P x f nm hD hh =>
    obtain ⟨⟨LF, JF⟩, LT⟩ := lokSM_callTreeD (S := S) (Map := Map) lib env hD
    refine ⟨⟨LF.toH hh, fun hc => JNewLSFM.toH (JF hc) hh⟩, fun hx => ?_⟩
    obtain ⟨L, J⟩ := LT hx
    exact ⟨L.toH hh, fun hc => JNewLSM.toH (J hc) hh⟩
  | @cons P b1 b2 a1 a2 b p q hp hq ihp ihq =>
    have Kp := hp.kindU
    have Kq := hq.kindU
    refine ⟨⟨lokS_consFMHU lib env ⟨_, _, rfl⟩ Kp Kq ihq.1.2 ihp.1.1 ihq.1.1,
      fun _ => jNewLSF_consMHU lib env ⟨_, _, rfl⟩ Kp Kq ihq.1.2 ihp.1.1 ihq.1.1⟩, fun hb => ?_⟩
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hb
    obtain ⟨Lq, Jq⟩ := ihq.2 hb.1
    rcases hb.2 with h1 | hqh
    · obtain ⟨Lp, -⟩ := ihp.2 h1
      exact ⟨lokS_consSMHU lib env ⟨_, _, rfl⟩ Kp Kq Jq Lp Lq,
        fun _ => jNewLS_consMHU lib env ⟨_, _, rfl⟩ Kp Kq Jq Lp Lq⟩
    · exact ⟨lokS_consHMHU lib env ⟨_, _, rfl⟩ Kp Kq Jq hqh ihp.1.1 Lq,
        fun _ => jNewLS_consHMHU lib env ⟨_, _, rfl⟩ Kp Kq Jq hqh ihp.1.1 Lq⟩
  | @ind P b1 b2 b c p q hp hq ihp ihq =>
    have Kp := hp.kindU
    have L := lokS_indirectFMHU lib env (minkC2_indirect lib P b c) hp.cell Kp ihp.1.1 ihq.1.1
    have J : JNewLSH (S := S) (Map := Map) snd env (Nomm.n2 p q Option.none) :=
      jNewLS_indirectFMHU lib env (minkC2_indirect lib P b c) hp.cell Kp ihp.1.1 ihq.1.1
    exact ⟨⟨L.toF, fun _ => J.toF⟩, fun _ => ⟨L, fun _ => J⟩⟩
  | @seven P b2 b c p q hp hq ihp ihq =>
    obtain ⟨Lp, Jp⟩ := ihp.2 rfl
    refine ⟨⟨lokS_sevenFMH ihq.1.1 Lp, jNewLSF_sevenMH ihq.1.1 Lp ihq.1.2 Jp⟩, fun hb => ?_⟩
    obtain ⟨Lq, Jq⟩ := ihq.2 hb
    exact ⟨lokS_sevenMH Lq Lp, jNewLS_sevenMH Lq Lp Jq Jp⟩
  | @four P b1 b p hp ihp =>
    have L := lokS_fourMH lib env (minkC4_four lib P b) ihp.1.1
    have J : JNewLSH (S := S) (Map := Map) snd env (Nomm.n4 p) := jNewLS_fourMH lib env (minkC4_four lib P b) ihp.1.1
    exact ⟨⟨L.toF, fun _ => J.toF⟩, fun h => by cases h⟩
  | @three P b1 b p hp ihp =>
    have L := lokS_threeMH lib env (minkC3_three lib P b) ihp.1.1
    have J : hinted env.cod (Nomm.n3 p) = some true → JNewLSH (S := S) (Map := Map) snd env (Nomm.n3 p) :=
      jNewLS_threeMH lib env (minkC3_three lib P b) ihp.1.1 ihp.1.2
    exact ⟨⟨L.toF, fun hh => JNewLSH.toF (J hh)⟩, fun h => by cases h⟩
  | @five P b1 b2 b c p q hp hq ihp ihq =>
    have Kp := hp.kindU
    have L := lokS_fiveMHU lib env (minkC5_five lib P b c) hp.cell Kp ihp.1.1 ihq.1.1
    have J : JNewLSH (S := S) (Map := Map) snd env (Nomm.n5 p q) :=
      jNewLS_fiveMHU (N := N) lib env (minkC5_five lib P b c) hp.cell Kp ihp.1.1 ihq.1.1
    exact ⟨⟨L.toF, fun _ => J.toF⟩, fun h => by cases h⟩
  | @n11s P x f q tag body hq hs ih =>
    rw [hinted_n11s hs]
    refine ⟨⟨ih.1.1.n11s hs body, fun hc => JNewLSFH.n11s hs body (ih.1.2 hc)⟩, fun hx => ?_⟩
    obtain ⟨L, J⟩ := ih.2 hx
    exact ⟨L.n11s hs body, fun hc => JNewLSH.n11s hs body (J hc)⟩
  | @n11d P x f fh q h tag body hq hs hsafe hc hh h6 ih =>
    have e : hinted env.cod (Nomm.n11d tag h q body) = hinted env.cod q := by
      show orB (some (hintDynamic tag)) (orB (hinted env.cod h) (hinted env.cod q)) = _
      rw [hs, hh]; rfl
    rw [e]
    refine ⟨⟨ih.1.1.n11d hs hsafe hc body h6, fun hc' => JNewLSFH.n11d hs hsafe body (ih.1.2 hc') h6⟩,
      fun hx => ?_⟩
    obtain ⟨L, J⟩ := ih.2 hx
    exact ⟨L.n11d hs hsafe hc body h6, fun hc' => JNewLSH.n11d hs hsafe body (J hc') h6⟩

/-- **Every member of `CallTreeHU` under `%done` meets `DoneOK`**: the text
of `callTreeH_done` with the copies for `KindU`. -/
theorem callTreeHU_done (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {x : Bool} {f : Noun} {nm : Nomm}
    (h : CallTreeHU lib env N P x f nm) :
    ∀ {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    runLCH env snd true sup nm CGoalL.done region g0 = some (nex, g1) →
      DoneOK (S := S) (Map := Map) lib N P f g0 g1 nex := by
  induction h with
  | @base P x f nm hD hh =>
    intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
    rw [runLCH_eq env snd true nm hh] at hr
    exact callTreeD_done lib env hD b0 d0 hu hcl hcb hr
  | @cons P b1 b2 a1 a2 b p q hp hq _ _ =>
    intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
    have hc := CallTreeHU.cons hp hq
    exact done_of_lokSFMH (lokSHU_callTreeHU lib env hc).1.1 (by rw [hc.sixCount]; omega) (Or.inl ⟨_, _, rfl⟩)
      b0 d0 hu hcl hcb hr
  | @ind P b1 b2 b c p q hp hq _ _ =>
    intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
    have hc := CallTreeHU.ind hp hq
    exact done_of_lokSFMH (lokSHU_callTreeHU lib env hc).1.1 (by rw [hc.sixCount]; omega)
      (Or.inr (Or.inl ⟨_, _, rfl⟩)) b0 d0 hu hcl hcb hr
  | @seven P b2 b c p q hp hq _ ihq =>
    intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
    rw [runLCH_n7] at hr
    obtain ⟨nx, ga, h1, h2⟩ := bind_some hr
    have D := ihq b0 d0 hu hcl hcb h1
    have Rq := D.run
    have Lp := ((lokSHU_callTreeHU (S := S) (Map := Map) (snd := snd) lib (N := N) env hp).2 rfl).1
    have hj : nx.th.args = [] := by
      rcases Rq.ent with ⟨_, _, _, ha⟩ | e
      · exact ha
      · exact e.elim
    obtain ⟨⟨Q, RS⟩, hne, -, hfl, hec⟩ := Lp.run (sup := sup) (L := nx.laz) (th := nx.th) (region := region)
      (by rw [hp.sixCount]; omega) (by have := Rq.ext.2.1; omega) (Rq.ext.2.2.1.trans d0) (Rq.grow.up hu)
      (Clear.growU hcl Rq.grow) (Rq.cfr.below hcb) Rq.lo Rq.hi hj D.nent Rq.dist
      (fun x hx => ⟨by
        rcases Rq.regs x hx with e | e
        · exact e.elim
        · exact e.2, Rq.ncond x hx⟩)
      (fun e he => ⟨(Rq.labs e he).2.1, (Rq.labs e he).2.2⟩) Rq.nodup
      (fun e he => ⟨(Rq.eregs e he).1, fun x hx => ⟨((Rq.eregs e he).2 x hx).2, Rq.econd e he x hx⟩⟩)
      D.flat D.clean D.eclean h2
    exact ⟨runOKGB_sevenL (minkC7_seven lib P b c) Rq RS.toRunOKLB (fun r hr => hr.elim), hne, hfl,
      Lp.clean (L := nx.laz) D.clean h2, hec⟩
  | @four P b1 b p hp _ =>
    intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
    exact four_doneBMH lib (lokSHU_callTreeHU lib env hp).1.1 (minkC4_four lib P b) (by rw [hp.sixCount]; omega)
      b0 d0 hu hcl hcb hr
  | @three P b1 b p hp _ =>
    intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
    exact three_doneBMH lib (lokSHU_callTreeHU lib env hp).1.1 (minkC3_three lib P b) (by rw [hp.sixCount]; omega)
      b0 d0 hu hcl hcb hr
  | @five P b1 b2 b c p q hp hq _ _ =>
    intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
    exact five_doneBMHU lib (minkC5_five lib P b c) hp.cell hp.kindU (lokSHU_callTreeHU lib env hp).1.1
      (lokSHU_callTreeHU lib env hq).1.1 (by rw [(CallTreeHU.five hp hq).sixCount]; omega) b0 d0 hu hcl hcb hr
  | @n11s P x f q tag body hq hs ih =>
    intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
    rw [runLCH_n11s env snd true hs] at hr
    exact (ih b0 d0 hu hcl hcb hr).minkAs (minkAs_n11s lib tag f)
  | @n11d P x f fh q h tag body hq hs hsafe hc hh h6 ih =>
    intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
    rw [runLCH_n11d_safe env snd true hs hsafe] at hr
    exact (ih b0 d0 hu hcl hcb hr).minkAsP (minkAsP_n11d lib hs hc f)

/-- **The contract of `CallTreeHU` at the top**: the whole-subject code with
hints (`finishLUCH`) of every member meets both halves of the contract for
its formula, traces included, on every subject of `P`. -/
theorem finishLUCH_contractCallTreeHU (lib : Lib) {env : CallEnv} {N : Needs} {P : Noun → Prop} {x : Bool}
    {f : Noun} {nm : Nomm} (h : CallTreeHU lib env N P x f nm) {c : Straight Map}
    (hc : finishLUCH (S := S) env snd nm = some c) :
    c.need = NeedOrd.this ∧ ∀ s, P s → ContractFwd lib N s f [s] c ∧ ContractBwd lib N s f [s] c :=
  finishLUCH_contractGB lib N (fun hr => (callTreeHU_done (S := S) (Map := Map) (snd := snd) lib env h
    (by simp [gen0]) rfl upBelow_gen0 clear_gen0 condBelow_gen0 hr).run) hc

/-- **The bell contract of `CallTreeHU`**, for a member at the subjects of the bell. -/
theorem finishLUCH_bellContractCallTreeHU {lib : Lib} {env : CallEnv} {N : Needs} {bl : Bell} {x : Bool} {nm : Nomm}
    (h : CallTreeHU lib env N (SkaModel.Fits bl.less) x bl.fol nm) {cd : Straight Map}
    (hc : finishLUCH (S := S) env snd nm = some cd) :
    cd.need = NeedOrd.this ∧ BellContract lib N bl true cd := by
  have H := finishLUCH_contractCallTreeHU (S := S) lib h hc
  refine ⟨H.1, fun s hs args hargs => ?_⟩
  simp only [if_true, Option.some.injEq] at hargs
  subst hargs
  exact H.2 s hs

end Comp
end SkaModel
end Formalization
