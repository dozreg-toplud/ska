import lemmas.Ska.CompDirectMLSCons
import lemmas.Ska.CompDirectMCalFour

/-!
# The class with the direct call: `CallTreeD`

README Gaps 18.14 (track J, 2026-11-27).  Track C's class `CallTreeA`
(`CompFourTop.lean`) plus the direct call `[2 p [1 k] b]`, for the run with
`mono` `&` (`runLCM env true`, what `+compile-unary` runs), so that a direct
call may sit anywhere a member of the class may: below a cons, in either part
of a `%7`, in an indirect call's operands, under `%4`, `%3`, `%5`, at the top,
and as the `p` of another direct call.

* `CallTreeD lib env N P x f nm`: the class, indexed by the subjects `P` (a
  direct call reads that the products of its `p` fit the callee's bell) and,
  as `CallTreeA`, by whether the nomm meets `LOKSM false` at every goal.  The
  constructor `direct` takes the needs hypotheses of README Gaps 18.9 (on
  `env` and the needs `N` of the contract) and a callee that is not pure
  (`env.pure b = false`, so the call is never dropped, and `env.cod b = some
  false`, so `+hinted` says the call is hinted).
* `CallTreeD.toA` (a member with no direct call is in `CallTreeA`),
  `.sixCount`, `.cell`, `.hinted_of`, `.kind`.
* `jNewLSM_direct`: the jump of a direct call's run is a new block.
* `lokSM_callTreeD`: every member meets `LOKSFM` (and `JNewLSFM` when
  hinted), one of index `true` `LOKSM false` (and `JNewLSM`); the text of
  `lokS_callTreeA` with the generated copies (`CompDirectMLS*.lean`) and
  `lokSM_directF` for the new case.
* `callTreeD_done`: every member under `%done` meets `DoneOK` (the text of
  `callTreeA_done`; the direct call at the top by `tailP_doneM`).
* `finishLUCM_contractCallTreeD`, `finishLUCM_bellContractCallTreeD`: both
  halves of the contract at the top on the real whole-subject code.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-- **The formula part of a direct call**: the nomm `q` is skipped by the
compiler (`safeFolFol`) and has no `%6`; its formula `fq` returns the
callee's formula, and nothing else, on the subjects.  `q` need not be `[1
fq]`: the analysis puts the constant `[1 b.fol]` in the nomm where the
formula fetches the callee from the subject (`[0 axe]`), which is the only
way a bell can call itself (its formula cannot contain itself). -/
structure QDirect (lib : Lib) (P : Noun → Prop) (q : Nomm) (fq : Noun) (bl : Bell) : Prop where
  safe : safeFolFol q = true
  six : sixCount q = 0
  ret : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {rc : Tone}, P s → minkF lib gul n tm s fq = some rc →
    rc = Tone.zero bl.fol
  mink : ∀ {s gul : Noun} {tm : Trace}, P s → Mink lib gul tm s fq (Tone.zero bl.fol)

/-- **`[1 b.fol]` is the formula part of a direct call.** -/
theorem QDirect.quote (lib : Lib) (P : Noun → Prop) (bl : Bell) :
    QDirect lib P (Nomm.n1 bl.fol) (C (A 1) bl.fol) bl :=
  ⟨rfl, rfl, fun _ h => quote_hq1 h, fun _ => quote_hq2⟩

/-- **`CallTreeA` with the direct call**, for the run with `mono` `&`.  The
index `P` is the set of subjects (the `q` of `[7 p q]` is in the class at the
products of `p`, `Img lib P b`); the index `x` says, as in `CallTreeA`,
whether the nomm meets `LOKSM false` at every goal.  A direct call
`[2 p q b]` has `p` of any index (it runs under `%next (lazy-from-reg
sub-pes)`, a flag-free goal), `q` skipped with a formula `fq` returning the
callee's formula (`QDirect`), the callee's needs as
in `tail_done` (`env.ring b = none`, `env.need b = some bNed` with `N b false
= some bNed`, some `N b true`), the callee not pure, and the products of `p`
on `P` fitting the callee's subject. -/
inductive CallTreeD (lib : Lib) (env : CallEnv) (N : Needs) : (Noun → Prop) → Bool → Noun → Nomm → Prop
  | n0 {P : Noun → Prop} (axe : Nat) : CallTreeD lib env N P true (slot axe) (Nomm.n0 axe)
  | cons {P : Noun → Prop} {b1 b2 : Bool} {a1 a2 b : Noun} {p q : Nomm} :
      CallTreeD lib env N P b1 (C a1 a2) p → CallTreeD lib env N P b2 b q →
      CallTreeD lib env N P (b2 && (b1 || !q.pure)) (C (C a1 a2) b) (Nomm.cons p q)
  | ind {P : Noun → Prop} {b1 b2 : Bool} {b c : Noun} {p q : Nomm} :
      CallTreeD lib env N P b1 b p → CallTreeD lib env N P b2 c q →
      CallTreeD lib env N P true (n3 (A 2) b c) (Nomm.n2 p q Option.none)
  | seven {P : Noun → Prop} {b2 : Bool} {b c : Noun} {p q : Nomm} :
      CallTreeD lib env N P true b p → CallTreeD lib env N (Img lib P b) b2 c q →
      CallTreeD lib env N P b2 (n3 (A 7) b c) (Nomm.n7 p q)
  | four {P : Noun → Prop} {b1 : Bool} {b : Noun} {p : Nomm} :
      CallTreeD lib env N P b1 b p → CallTreeD lib env N P false (n2 (A 4) b) (Nomm.n4 p)
  | three {P : Noun → Prop} {b1 : Bool} {b : Noun} {p : Nomm} :
      CallTreeD lib env N P b1 b p → CallTreeD lib env N P false (n2 (A 3) b) (Nomm.n3 p)
  | five {P : Noun → Prop} {b1 b2 : Bool} {b c : Noun} {p q : Nomm} :
      CallTreeD lib env N P b1 b p → CallTreeD lib env N P b2 c q →
      CallTreeD lib env N P false (n3 (A 5) b c) (Nomm.n5 p q)
  | n1 {P : Noun → Prop} (k : Noun) : CallTreeD lib env N P true (quote k) (Nomm.n1 k)
  | direct {P : Noun → Prop} {b1 : Bool} {fb fq : Noun} {p q : Nomm} {bl : Bell} {bNed ndT : NeedOrd} :
      CallTreeD lib env N P b1 fb p →
      env.ring bl = Option.none → env.need bl = some bNed → N bl false = some bNed → N bl true = some ndT →
      env.pure bl = false → env.cod bl = some false → QDirect lib P q fq bl →
      (∀ x gul y, P x → Mink lib gul [] x fb (Tone.zero y) → SkaModel.Fits bl.less y) →
      CallTreeD lib env N P true (n3 (A 2) fb fq) (Nomm.n2 p q (some (bl, Option.none)))

section
variable {lib : Lib} {env : CallEnv} {N : Needs}

/-- **A member with no direct call is in `CallTreeA`** (same index). -/
theorem CallTreeD.toA {P : Noun → Prop} {x : Bool} {f : Noun} {nm : Nomm} (h : CallTreeD lib env N P x f nm) :
    nm.noDirect = true → CallTreeA x f nm := by
  induction h with
  | n0 axe => exact fun _ => CallTreeA.n0 axe
  | cons _ _ ihp ihq =>
    intro hd; simp only [Nomm.noDirect, Bool.and_eq_true] at hd; exact CallTreeA.cons (ihp hd.1) (ihq hd.2)
  | ind _ _ ihp ihq =>
    intro hd; simp only [Nomm.noDirect, Option.isNone_none, Bool.true_and, Bool.and_eq_true] at hd
    exact CallTreeA.ind (ihp hd.1) (ihq hd.2)
  | seven _ _ ihp ihq =>
    intro hd; simp only [Nomm.noDirect, Bool.and_eq_true] at hd; exact CallTreeA.seven (ihp hd.1) (ihq hd.2)
  | four _ ihp => intro hd; exact CallTreeA.four (ihp hd)
  | three _ ihp => intro hd; exact CallTreeA.three (ihp hd)
  | five _ _ ihp ihq =>
    intro hd; simp only [Nomm.noDirect, Bool.and_eq_true] at hd; exact CallTreeA.five (ihp hd.1) (ihq hd.2)
  | n1 k => exact fun _ => CallTreeA.n1 k
  | direct => intro hd; simp [Nomm.noDirect] at hd

theorem CallTreeD.sixCount {P : Noun → Prop} {x : Bool} {f : Noun} {nm : Nomm} (h : CallTreeD lib env N P x f nm) :
    sixCount nm = 0 := by
  induction h with
  | n0 axe => rfl
  | cons _ _ ihp ihq => simp only [Comp.sixCount, ihp, ihq]
  | ind _ _ ihp ihq => simp only [Comp.sixCount, ihp, ihq]
  | seven _ _ ihp ihq => simp only [Comp.sixCount, ihp, ihq]
  | four _ ihp => simp only [Comp.sixCount, ihp]
  | three _ ihp => simp only [Comp.sixCount, ihp]
  | five _ _ ihp ihq => simp only [Comp.sixCount, ihp, ihq]
  | n1 k => rfl
  | direct _ _ _ _ _ _ _ hk _ ihp => simp only [Comp.sixCount, ihp, hk.six]

theorem CallTreeD.cell {P : Noun → Prop} {x : Bool} {f : Noun} {nm : Nomm} (h : CallTreeD lib env N P x f nm) :
    ∃ a b, f = C a b := by
  cases h <;> exact ⟨_, _, rfl⟩

theorem CallTreeD.hinted_of {P : Noun → Prop} {x : Bool} {f : Noun} {nm : Nomm} (h : CallTreeD lib env N P x f nm) :
    nm.pure = false → hinted env.cod nm = some true := by
  induction h with
  | n0 axe => intro e; cases e
  | @cons P b1 b2 a1 a2 b p q _ _ ihp ihq =>
    intro e
    simp only [hinted]
    cases ep : p.pure
    · rw [ihp ep]; rfl
    · rw [hinted_pure env.cod p ep]
      exact ihq (by simpa only [Nomm.pure, ep, Bool.true_and] using e)
  | ind _ _ => intro _; rfl
  | @seven P b2 b c p q _ _ ihp ihq =>
    intro e
    simp only [hinted]
    cases ep : p.pure
    · rw [ihp ep]; rfl
    · rw [hinted_pure env.cod p ep]
      exact ihq (by simpa only [Nomm.pure, ep, Bool.true_and] using e)
  | four _ ihp =>
    intro e
    simp only [hinted]
    exact ihp (by simpa only [Nomm.pure] using e)
  | three _ ihp =>
    intro e
    simp only [hinted]
    exact ihp (by simpa only [Nomm.pure] using e)
  | @five P b1 b2 b c p q _ _ ihp ihq =>
    intro e
    simp only [hinted]
    cases ep : p.pure
    · rw [ihp ep]; rfl
    · rw [hinted_pure env.cod p ep]
      exact ihq (by simpa only [Nomm.pure, ep, Bool.true_and] using e)
  | n1 k => intro e; cases e
  | direct _ _ _ _ _ _ hcod _ _ _ => intro _; simp only [hinted, hcod]; rfl

/-- **Each member is call-free with `MinkEq`, or hinted** (`CallTreeA.kind`
for a pure one, which has no direct call). -/
theorem CallTreeD.kind {P : Noun → Prop} {x : Bool} {f : Noun} {nm : Nomm} (h : CallTreeD lib env N P x f nm) :
    (nm.pure = true ∧ MinkEq lib P f nm) ∨ hinted env.cod nm = some true := by
  cases hp : nm.pure
  · exact Or.inr (h.hinted_of hp)
  · rcases (h.toA (Nomm.noDirect_of_noCall nm (Nomm.noCall_of_pure nm hp))).kind lib env.cod P with ⟨_, hm⟩ | hh
    · exact Or.inl ⟨rfl, hm⟩
    · exact Or.inr hh

end

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The jump of a direct call's run is a new block** (`callLBM_runM`), for
a callee that is not pure, under the premises of `LOKS.run`. -/
theorem jNewLSM_direct (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {p q : Nomm} {fb fq : Noun}
    {b : Bell} {bNed ndT : NeedOrd} (hring : env.ring b = Option.none) (hned : env.need b = some bNed)
    (hNf : N b false = some bNed) (hNt : N b true = some ndT) (hpure : env.pure b = false)
    (Sp : LOKSFM (S := S) (Map := Map) lib N env P fb p) (hq : safeFolFol q = true)
    (hAp : ∀ x gul y, P x → Mink lib gul [] x fb (Tone.zero y) → SkaModel.Fits b.less y)
    (hq1 : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {rc : Tone}, P s → minkF lib gul n tm s fq = some rc →
      rc = Tone.zero b.fol)
    (hq2 : ∀ {s gul : Noun} {tm : Trace}, P s → Mink lib gul tm s fq (Tone.zero b.fol)) :
    JNewLSM (S := S) (Map := Map) env (Nomm.n2 p q (some (b, Option.none))) :=
  fun hcount b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcs hce hr =>
    (callLBM_runM lib env hring hned hNf hNt Sp (by simp only [sixCount] at hcount; omega) hq hAp hq1 hq2
      (by rw [hpure]; rfl) b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcs hce hr).2.2.1

/-- **Every member of `CallTreeD` meets `LOKSFM`** (a hinted one
`JNewLSFM`), and one of index `true` `LOKSM false` (a hinted one
`JNewLSM`), with only the premises of `LOKS.run` on the starting goal and
state: the text of `lokS_callTreeA` with the copies for `runLCM env true`,
the leaves by `LOKS.toM`, the direct call by `lokSM_directF`. -/
theorem lokSM_callTreeD (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {x : Bool} {f : Noun} {nm : Nomm}
    (h : CallTreeD lib env N P x f nm) :
    (LOKSFM (S := S) (Map := Map) lib N env P f nm ∧
        (hinted env.cod nm = some true → JNewLSFM (S := S) (Map := Map) env nm)) ∧
      (x = true → LOKSM (S := S) (Map := Map) false lib N env P f nm ∧
        (hinted env.cod nm = some true → JNewLSM (S := S) (Map := Map) env nm)) := by
  induction h with
  | @n0 P axe =>
    have M := ((CallTreeA.n0 axe).kind lib env.cod P).elim (fun h => h.2) (fun h => by cases h)
    have H : LOKS (S := S) (Map := Map) false lib N env P (slot axe) (Nomm.n0 axe) := by
      rcases Nat.eq_zero_or_pos axe with rfl | ha
      · exact lokS_n00 lib env M
      · exact lokS_n0 lib env ha M
    have HM := H.toM rfl
    exact ⟨⟨HM.toF, fun h => by cases h⟩, fun _ => ⟨HM, fun h => by cases h⟩⟩
  | @cons P b1 b2 a1 a2 b p q hp hq ihp ihq =>
    have Kp := hp.kind
    have Kq := hq.kind
    refine ⟨⟨lokS_consFM lib env ⟨_, _, rfl⟩ Kp Kq ihq.1.2 ihp.1.1 ihq.1.1,
      fun _ => jNewLSF_consM lib env ⟨_, _, rfl⟩ Kp Kq ihq.1.2 ihp.1.1 ihq.1.1⟩, fun hb => ?_⟩
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hb
    obtain ⟨Lq, Jq⟩ := ihq.2 hb.1
    rcases hb.2 with h1 | h1
    · obtain ⟨Lp, -⟩ := ihp.2 h1
      exact ⟨lokS_consSM lib env ⟨_, _, rfl⟩ Kp Kq Jq Lp Lq, fun _ => jNewLS_consM lib env ⟨_, _, rfl⟩ Kp Kq Jq Lp Lq⟩
    · have hqh := hq.hinted_of h1
      exact ⟨lokS_consHM lib env ⟨_, _, rfl⟩ Kp Kq Jq hqh ihp.1.1 Lq,
        fun _ => jNewLS_consHM lib env ⟨_, _, rfl⟩ Kp Kq Jq hqh ihp.1.1 Lq⟩
  | @ind P b1 b2 b c p q hp hq ihp ihq =>
    have Kp := hp.kind
    have L := lokS_indirectFM lib env (minkC2_indirect lib P b c) hp.cell Kp ihp.1.1 ihq.1.1
    have J : JNewLSM (S := S) (Map := Map) env (Nomm.n2 p q Option.none) :=
      jNewLS_indirectFM lib env (minkC2_indirect lib P b c) hp.cell Kp ihp.1.1 ihq.1.1
    exact ⟨⟨L.toF, fun _ => J.toF⟩, fun _ => ⟨L, fun _ => J⟩⟩
  | @seven P b2 b c p q hp hq ihp ihq =>
    obtain ⟨Lp, Jp⟩ := ihp.2 rfl
    refine ⟨⟨lokS_sevenFM ihq.1.1 Lp, jNewLSF_sevenM ihq.1.1 Lp ihq.1.2 Jp⟩, fun hb => ?_⟩
    obtain ⟨Lq, Jq⟩ := ihq.2 hb
    exact ⟨lokS_sevenM Lq Lp, jNewLS_sevenM Lq Lp Jq Jp⟩
  | @four P b1 b p hp ihp =>
    have L := lokS_fourM lib env (minkC4_four lib P b) ihp.1.1
    have J : JNewLSM (S := S) (Map := Map) env (Nomm.n4 p) := jNewLS_fourM lib env (minkC4_four lib P b) ihp.1.1
    exact ⟨⟨L.toF, fun _ => J.toF⟩, fun h => by cases h⟩
  | @three P b1 b p hp ihp =>
    have L := lokS_threeM lib env (minkC3_three lib P b) ihp.1.1
    have J : hinted env.cod (Nomm.n3 p) = some true → JNewLSM (S := S) (Map := Map) env (Nomm.n3 p) :=
      jNewLS_threeM lib env (minkC3_three lib P b) ihp.1.1 ihp.1.2
    exact ⟨⟨L.toF, fun hh => JNewLSM.toF (J hh)⟩, fun h => by cases h⟩
  | @five P b1 b2 b c p q hp hq ihp ihq =>
    have Kp := hp.kind
    have L := lokS_fiveM lib env (minkC5_five lib P b c) hp.cell Kp ihp.1.1 ihq.1.1
    have J : JNewLSM (S := S) (Map := Map) env (Nomm.n5 p q) :=
      jNewLS_fiveM (N := N) lib env (minkC5_five lib P b c) hp.cell Kp ihp.1.1 ihq.1.1
    exact ⟨⟨L.toF, fun _ => J.toF⟩, fun h => by cases h⟩
  | @n1 P k =>
    have M := ((CallTreeA.n1 k).kind lib env.cod P).elim (fun h => h.2) (fun h => by cases h)
    have HM := (lokS_n1 (S := S) (Map := Map) (N := N) lib env M).toM rfl
    exact ⟨⟨HM.toF, fun h => by cases h⟩, fun _ => ⟨HM, fun h => by cases h⟩⟩
  | @direct P b1 fb fq p q bl bNed ndT hp hring hned hNf hNt hpure hcod hk hAp ihp =>
    have L := lokSM_directF (S := S) (Map := Map) lib env hring hned
      hNf hNt hpure ihp.1.1 hk.safe hAp hk.ret hk.mink
    have J : JNewLSM (S := S) (Map := Map) env (Nomm.n2 p q (some (bl, Option.none))) :=
      jNewLSM_direct (S := S) (Map := Map) lib env hring hned
      hNf hNt hpure ihp.1.1 hk.safe hAp hk.ret hk.mink
    exact ⟨⟨L.toF, fun _ => J.toF⟩, fun _ => ⟨L, fun _ => J⟩⟩

/-- **Every member of `CallTreeD` under `%done` meets `DoneOK`**: the text
of `callTreeA_done` with the copies for `runLCM env true`; the leaves by
`runLCM_true`, the direct call at the top (a tail call) by `tailP_doneM`. -/
theorem callTreeD_done (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {x : Bool} {f : Noun} {nm : Nomm}
    (h : CallTreeD lib env N P x f nm) :
    ∀ {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    runLCM env true sup nm CGoalL.done region g0 = some (nex, g1) → DoneOK (S := S) (Map := Map) lib N P f g0 g1 nex := by
  induction h with
  | @n0 P axe =>
    intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
    rw [runLCM_true env rfl] at hr
    exact callTree_done lib env P (CallTree.n0 axe) b0 d0 hu hcl hcb hr
  | @cons P b1 b2 a1 a2 b p q hp hq _ _ =>
    intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
    have hc := CallTreeD.cons hp hq
    exact done_of_lokSFM (lokSM_callTreeD lib env hc).1.1 (by rw [hc.sixCount]; omega) (Or.inl ⟨_, _, rfl⟩)
      b0 d0 hu hcl hcb hr
  | @ind P b1 b2 b c p q hp hq _ _ =>
    intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
    have hc := CallTreeD.ind hp hq
    exact done_of_lokSFM (lokSM_callTreeD lib env hc).1.1 (by rw [hc.sixCount]; omega)
      (Or.inr (Or.inl ⟨_, _, rfl⟩)) b0 d0 hu hcl hcb hr
  | @seven P b2 b c p q hp hq _ ihq =>
    intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
    rw [runLCM_n7] at hr
    obtain ⟨nx, ga, h1, h2⟩ := bind_some hr
    have D := ihq b0 d0 hu hcl hcb h1
    have Rq := D.run
    have Lp := ((lokSM_callTreeD (S := S) (Map := Map) lib (N := N) env hp).2 rfl).1
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
    exact four_doneBM lib (lokSM_callTreeD lib env hp).1.1 (minkC4_four lib P b) (by rw [hp.sixCount]; omega)
      b0 d0 hu hcl hcb hr
  | @three P b1 b p hp _ =>
    intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
    exact three_doneBM lib (lokSM_callTreeD lib env hp).1.1 (minkC3_three lib P b) (by rw [hp.sixCount]; omega)
      b0 d0 hu hcl hcb hr
  | @five P b1 b2 b c p q hp hq _ _ =>
    intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
    exact five_doneBM lib (minkC5_five lib P b c) hp.cell hp.kind (lokSM_callTreeD lib env hp).1.1
      (lokSM_callTreeD lib env hq).1.1 (by rw [(CallTreeD.five hp hq).sixCount]; omega) b0 d0 hu hcl hcb hr
  | @n1 P k =>
    intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
    rw [runLCM_true env rfl] at hr
    exact n1_doneB lib env (((CallTreeA.n1 k).kind lib env.cod P).elim (fun h => h.2) (fun h => by cases h))
      b0 d0 hu hcl hcb hr
  | @direct P b1 fb fq p q bl bNed ndT hp hring hned hNf hNt hpure hcod hk hAp _ =>
    intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
    exact tailP_doneM lib hring hned hNf hNt (lokSM_callTreeD lib env hp).1.1 (by rw [hp.sixCount]; omega) hk.safe
      hAp hk.ret hk.mink b0 d0 hu hcl hcb hr

/-- **The contract of `CallTreeD` at the top**: the whole-subject code
(`finishLUCM`) of every member meets both halves of the contract for its
formula, on every subject of `P`, for the needs `N` of the class. -/
theorem finishLUCM_contractCallTreeD (lib : Lib) {env : CallEnv} {N : Needs} {P : Noun → Prop} {x : Bool} {f : Noun}
    {nm : Nomm} (h : CallTreeD lib env N P x f nm) {c : Straight Map} (hc : finishLUCM (S := S) env nm = some c) :
    c.need = NeedOrd.this ∧ ∀ s, P s → ContractFwd lib N s f [s] c ∧ ContractBwd lib N s f [s] c :=
  finishLUCM_contractGB lib N (fun hr => (callTreeD_done (S := S) (Map := Map) lib env h (by simp [gen0]) rfl
    upBelow_gen0 clear_gen0 condBelow_gen0 hr).run) hc

/-- **The bell contract of `CallTreeD`** (`finishLUC_bellContractCallTreeA`'s
form), for a member at the subjects of the bell. -/
theorem finishLUCM_bellContractCallTreeD {lib : Lib} {env : CallEnv} {N : Needs} {bl : Bell} {x : Bool} {nm : Nomm}
    (h : CallTreeD lib env N (SkaModel.Fits bl.less) x bl.fol nm) {cd : Straight Map}
    (hc : finishLUCM (S := S) env nm = some cd) :
    cd.need = NeedOrd.this ∧ BellContract lib N bl true cd := by
  have H := finishLUCM_contractCallTreeD (S := S) lib h hc
  refine ⟨H.1, fun s hs args hargs => ?_⟩
  simp only [if_true, Option.some.injEq] at hargs
  subst hargs
  exact H.2 s hs

end Comp
end SkaModel
end Formalization
