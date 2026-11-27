import lemmas.Ska.CompHintLSCons

/-!
# The class with hints `CallTreeH` and its contract at the top (README Gaps 24.12)

* The bridges for a part without hints (`runLCH_eq`): `LOKSFM.toH`,
  `JNewLSM.toH`, `JNewLSFM.toH` (and `LOKSM.toH`, `CompHintLOKS.lean`).
* A static hint whose tag is not kept (`hintStatic tag = false`) is its
  formula for every relation (`runLCH_n11s`, `minkAs_n11s`):
  `LOKSH.n11s`, `LOKSFH.n11s`, `JNewLSH.n11s`, `JNewLSFH.n11s`.
* `CallTreeH`: `CallTreeD` (no hint) as a leaf, the cons, the indirect call,
  `[7 p q]`, `[4 p]`, `[3 p]`, `[5 p q]` with parts in `CallTreeH`, and
  `[11 tag f]` with a tag not kept around a member that is not pure (so the
  hint is `+hinted`, as `+past` reads it: a non-kept tag around a pure
  formula is neither pure nor hinted, the first blocker of the rest).
* `lokSH_callTreeH`, `callTreeH_done`, **`finishLUCH_contractCallTreeH`**
  (both halves, traces included), `finishLUCH_bellContractCallTreeH`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]
variable {snd : Nomm → NeedOrd → Bool}

/-! ## Parts without hints -/

theorem LOKSFM.toH {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (H : LOKSFM (S := S) (Map := Map) lib N env P f nm) (hh : nm.noHint = true) :
    LOKSFH (S := S) (Map := Map) snd lib N env P f nm :=
  ⟨fun hc hr => H.clean hc (by rwa [runLCH_eq env snd true nm hh] at hr),
   fun hF hc b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcs hce hr =>
    H.run hF hc b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcs hce
      (by rwa [runLCH_eq env snd true nm hh] at hr)⟩

theorem JNewLSM.toH {env : CallEnv} {nm : Nomm} (H : JNewLSM (S := S) (Map := Map) env nm) (hh : nm.noHint = true) :
    JNewLSH (S := S) (Map := Map) snd env nm :=
  fun hc b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcs hce hr =>
    H hc b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcs hce (by rwa [runLCH_eq env snd true nm hh] at hr)

theorem JNewLSFM.toH {env : CallEnv} {nm : Nomm} (H : JNewLSFM (S := S) (Map := Map) env nm)
    (hh : nm.noHint = true) : JNewLSFH (S := S) (Map := Map) snd env nm :=
  fun hF hc b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcs hce hr =>
    H hF hc b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcs hce
      (by rwa [runLCH_eq env snd true nm hh] at hr)

/-! ## A static hint not kept -/

section N11s
variable {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {q : Nomm} {tag : Nat}

theorem LOKSH.n11s {x : Bool} (hs : hintStatic tag = false) (body : Noun)
    (H : LOKSH (S := S) (Map := Map) snd x lib N env P f q) :
    LOKSH (S := S) (Map := Map) snd x lib N env P (n3 (A 11) (A tag) f) (Nomm.n11s tag q body) :=
  ⟨fun hc hr => H.clean hc (by rwa [runLCH_n11s env snd true hs] at hr),
   fun hc b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcs hce hr =>
    (fun ⟨⟨Q, R⟩, a, b, c, d⟩ => ⟨⟨Q, R.minkAs (minkAs_n11s lib tag f)⟩, a, b, c, d⟩)
      (H.run hc b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcs hce
        (by rwa [runLCH_n11s env snd true hs] at hr))⟩

theorem LOKSFH.n11s (hs : hintStatic tag = false) (body : Noun)
    (H : LOKSFH (S := S) (Map := Map) snd lib N env P f q) :
    LOKSFH (S := S) (Map := Map) snd lib N env P (n3 (A 11) (A tag) f) (Nomm.n11s tag q body) :=
  ⟨fun hc hr => H.clean hc (by rwa [runLCH_n11s env snd true hs] at hr),
   fun hF hc b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcs hce hr =>
    (fun ⟨⟨Q, R⟩, a, b, c, d⟩ => ⟨⟨Q, R.minkAs (minkAs_n11s lib tag f)⟩, a, b, c, d⟩)
      (H.run hF hc b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcs hce
        (by rwa [runLCH_n11s env snd true hs] at hr))⟩

theorem JNewLSH.n11s (hs : hintStatic tag = false) (body : Noun) (H : JNewLSH (S := S) (Map := Map) snd env q) :
    JNewLSH (S := S) (Map := Map) snd env (Nomm.n11s tag q body) :=
  fun hc b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcs hce hr =>
    H hc b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcs hce (by rwa [runLCH_n11s env snd true hs] at hr)

theorem JNewLSFH.n11s (hs : hintStatic tag = false) (body : Noun) (H : JNewLSFH (S := S) (Map := Map) snd env q) :
    JNewLSFH (S := S) (Map := Map) snd env (Nomm.n11s tag q body) :=
  fun hF hc b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcs hce hr =>
    H hF hc b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcs hce
      (by rwa [runLCH_n11s env snd true hs] at hr)

end N11s

/-! ## The class -/

/-- **`CallTreeD` with hints**: a member of `CallTreeD` without hints, the
constructors of `CallTreeD` but the leaves and the direct call over parts of
the class, and `[11 tag f]` with a tag not kept (`hintStatic tag = false`)
around a member that is not pure (index and subjects of the member). -/
inductive CallTreeH (lib : Lib) (env : CallEnv) (N : Needs) : (Noun → Prop) → Bool → Noun → Nomm → Prop
  | base {P : Noun → Prop} {x : Bool} {f : Noun} {nm : Nomm} :
      CallTreeD lib env N P x f nm → nm.noHint = true → CallTreeH lib env N P x f nm
  | cons {P : Noun → Prop} {b1 b2 : Bool} {a1 a2 b : Noun} {p q : Nomm} :
      CallTreeH lib env N P b1 (C a1 a2) p → CallTreeH lib env N P b2 b q →
      CallTreeH lib env N P (b2 && (b1 || !q.pure)) (C (C a1 a2) b) (Nomm.cons p q)
  | ind {P : Noun → Prop} {b1 b2 : Bool} {b c : Noun} {p q : Nomm} :
      CallTreeH lib env N P b1 b p → CallTreeH lib env N P b2 c q →
      CallTreeH lib env N P true (n3 (A 2) b c) (Nomm.n2 p q Option.none)
  | seven {P : Noun → Prop} {b2 : Bool} {b c : Noun} {p q : Nomm} :
      CallTreeH lib env N P true b p → CallTreeH lib env N (Img lib P b) b2 c q →
      CallTreeH lib env N P b2 (n3 (A 7) b c) (Nomm.n7 p q)
  | four {P : Noun → Prop} {b1 : Bool} {b : Noun} {p : Nomm} :
      CallTreeH lib env N P b1 b p → CallTreeH lib env N P false (n2 (A 4) b) (Nomm.n4 p)
  | three {P : Noun → Prop} {b1 : Bool} {b : Noun} {p : Nomm} :
      CallTreeH lib env N P b1 b p → CallTreeH lib env N P false (n2 (A 3) b) (Nomm.n3 p)
  | five {P : Noun → Prop} {b1 b2 : Bool} {b c : Noun} {p q : Nomm} :
      CallTreeH lib env N P b1 b p → CallTreeH lib env N P b2 c q →
      CallTreeH lib env N P false (n3 (A 5) b c) (Nomm.n5 p q)
  | n11s {P : Noun → Prop} {x : Bool} {f : Noun} {q : Nomm} {tag : Nat} (body : Noun) :
      CallTreeH lib env N P x f q → hintStatic tag = false → q.pure = false →
      CallTreeH lib env N P x (n3 (A 11) (A tag) f) (Nomm.n11s tag q body)

section
variable {lib : Lib} {env : CallEnv} {N : Needs}

theorem CallTreeH.sixCount {P : Noun → Prop} {x : Bool} {f : Noun} {nm : Nomm} (h : CallTreeH lib env N P x f nm) :
    sixCount nm = 0 := by
  induction h with
  | base hD _ => exact hD.sixCount
  | cons _ _ ihp ihq => simp only [Comp.sixCount, ihp, ihq]
  | ind _ _ ihp ihq => simp only [Comp.sixCount, ihp, ihq]
  | seven _ _ ihp ihq => simp only [Comp.sixCount, ihp, ihq]
  | four _ ihp => simp only [Comp.sixCount, ihp]
  | three _ ihp => simp only [Comp.sixCount, ihp]
  | five _ _ ihp ihq => simp only [Comp.sixCount, ihp, ihq]
  | n11s _ _ _ _ ih => simp only [Comp.sixCount, ih]

theorem CallTreeH.cell {P : Noun → Prop} {x : Bool} {f : Noun} {nm : Nomm} (h : CallTreeH lib env N P x f nm) :
    ∃ a b, f = C a b := by
  cases h with
  | base hD _ => exact hD.cell
  | _ => exact ⟨_, _, rfl⟩

/-- **A pure member is a member of `CallTreeD`** (no hint is pure). -/
theorem CallTreeH.toD {P : Noun → Prop} {x : Bool} {f : Noun} {nm : Nomm} (h : CallTreeH lib env N P x f nm) :
    nm.pure = true → CallTreeD lib env N P x f nm := by
  induction h with
  | base hD _ => exact fun _ => hD
  | cons _ _ ihp ihq =>
    intro e; simp only [Nomm.pure, Bool.and_eq_true] at e; exact CallTreeD.cons (ihp e.1) (ihq e.2)
  | ind _ _ => intro e; cases e
  | seven _ _ ihp ihq =>
    intro e; simp only [Nomm.pure, Bool.and_eq_true] at e; exact CallTreeD.seven (ihp e.1) (ihq e.2)
  | four _ ihp => intro e; exact CallTreeD.four (ihp e)
  | three _ ihp => intro e; exact CallTreeD.three (ihp e)
  | five _ _ ihp ihq =>
    intro e; simp only [Nomm.pure, Bool.and_eq_true] at e; exact CallTreeD.five (ihp e.1) (ihq e.2)
  | n11s _ _ _ _ _ => intro e; cases e

theorem CallTreeH.hinted_of {P : Noun → Prop} {x : Bool} {f : Noun} {nm : Nomm} (h : CallTreeH lib env N P x f nm) :
    nm.pure = false → hinted env.cod nm = some true := by
  induction h with
  | base hD _ => exact hD.hinted_of
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
  | n11s _ _ hs hq ih => intro _; simp only [hinted, hs, ih hq]; rfl

/-- **Each member is call-free with `MinkEq`, or hinted.** -/
theorem CallTreeH.kind {P : Noun → Prop} {x : Bool} {f : Noun} {nm : Nomm} (h : CallTreeH lib env N P x f nm) :
    (nm.pure = true ∧ MinkEq lib P f nm) ∨ hinted env.cod nm = some true := by
  cases hp : nm.pure
  · exact Or.inr (h.hinted_of hp)
  · have K := (h.toD hp).kind
    rw [hp] at K
    exact K

/-- A static hint not kept is hinted as its formula. -/
theorem hinted_n11s {cod : Bell → Option Bool} {tag : Nat} (hs : hintStatic tag = false) (q : Nomm) (body : Noun) :
    hinted cod (Nomm.n11s tag q body) = hinted cod q := by
  show orB (some (hintStatic tag)) (hinted cod q) = _
  rw [hs]; rfl

end

/-- **Every member of `CallTreeH` meets `LOKSFH`** (a hinted one
`JNewLSFH`), and one of index `true` `LOKSH false` (a hinted one
`JNewLSH`): the text of `lokSM_callTreeD` with the copies for `runLCH env snd
true`, the members without hints by `lokSM_callTreeD` and the bridges, the
hint by `LOKSH.n11s`. -/
theorem lokSH_callTreeH (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {x : Bool} {f : Noun} {nm : Nomm}
    (h : CallTreeH lib env N P x f nm) :
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
    have Kp := hp.kind
    have Kq := hq.kind
    refine ⟨⟨lokS_consFMH lib env ⟨_, _, rfl⟩ Kp Kq ihq.1.2 ihp.1.1 ihq.1.1,
      fun _ => jNewLSF_consMH lib env ⟨_, _, rfl⟩ Kp Kq ihq.1.2 ihp.1.1 ihq.1.1⟩, fun hb => ?_⟩
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hb
    obtain ⟨Lq, Jq⟩ := ihq.2 hb.1
    rcases hb.2 with h1 | h1
    · obtain ⟨Lp, -⟩ := ihp.2 h1
      exact ⟨lokS_consSMH lib env ⟨_, _, rfl⟩ Kp Kq Jq Lp Lq, fun _ => jNewLS_consMH lib env ⟨_, _, rfl⟩ Kp Kq Jq Lp Lq⟩
    · have hqh := hq.hinted_of h1
      exact ⟨lokS_consHMH lib env ⟨_, _, rfl⟩ Kp Kq Jq hqh ihp.1.1 Lq,
        fun _ => jNewLS_consHMH lib env ⟨_, _, rfl⟩ Kp Kq Jq hqh ihp.1.1 Lq⟩
  | @ind P b1 b2 b c p q hp hq ihp ihq =>
    have Kp := hp.kind
    have L := lokS_indirectFMH lib env (minkC2_indirect lib P b c) hp.cell Kp ihp.1.1 ihq.1.1
    have J : JNewLSH (S := S) (Map := Map) snd env (Nomm.n2 p q Option.none) :=
      jNewLS_indirectFMH lib env (minkC2_indirect lib P b c) hp.cell Kp ihp.1.1 ihq.1.1
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
    have Kp := hp.kind
    have L := lokS_fiveMH lib env (minkC5_five lib P b c) hp.cell Kp ihp.1.1 ihq.1.1
    have J : JNewLSH (S := S) (Map := Map) snd env (Nomm.n5 p q) :=
      jNewLS_fiveMH (N := N) lib env (minkC5_five lib P b c) hp.cell Kp ihp.1.1 ihq.1.1
    exact ⟨⟨L.toF, fun _ => J.toF⟩, fun h => by cases h⟩
  | @n11s P x f q tag body hq hs hp ih =>
    rw [hinted_n11s hs]
    refine ⟨⟨ih.1.1.n11s hs body, fun hc => JNewLSFH.n11s hs body (ih.1.2 hc)⟩, fun hx => ?_⟩
    obtain ⟨L, J⟩ := ih.2 hx
    exact ⟨L.n11s hs body, fun hc => JNewLSH.n11s hs body (J hc)⟩

/-- **Every member of `CallTreeH` under `%done` meets `DoneOK`**: the text
of `callTreeD_done` with the copies for `runLCH env snd true`; the members
without hints by `callTreeD_done` (`runLCH_eq`), the hint by `DoneOK.minkAs`. -/
theorem callTreeH_done (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {x : Bool} {f : Noun} {nm : Nomm}
    (h : CallTreeH lib env N P x f nm) :
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
    have hc := CallTreeH.cons hp hq
    exact done_of_lokSFMH (lokSH_callTreeH lib env hc).1.1 (by rw [hc.sixCount]; omega) (Or.inl ⟨_, _, rfl⟩)
      b0 d0 hu hcl hcb hr
  | @ind P b1 b2 b c p q hp hq _ _ =>
    intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
    have hc := CallTreeH.ind hp hq
    exact done_of_lokSFMH (lokSH_callTreeH lib env hc).1.1 (by rw [hc.sixCount]; omega)
      (Or.inr (Or.inl ⟨_, _, rfl⟩)) b0 d0 hu hcl hcb hr
  | @seven P b2 b c p q hp hq _ ihq =>
    intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
    rw [runLCH_n7] at hr
    obtain ⟨nx, ga, h1, h2⟩ := bind_some hr
    have D := ihq b0 d0 hu hcl hcb h1
    have Rq := D.run
    have Lp := ((lokSH_callTreeH (S := S) (Map := Map) (snd := snd) lib (N := N) env hp).2 rfl).1
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
    exact four_doneBMH lib (lokSH_callTreeH lib env hp).1.1 (minkC4_four lib P b) (by rw [hp.sixCount]; omega)
      b0 d0 hu hcl hcb hr
  | @three P b1 b p hp _ =>
    intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
    exact three_doneBMH lib (lokSH_callTreeH lib env hp).1.1 (minkC3_three lib P b) (by rw [hp.sixCount]; omega)
      b0 d0 hu hcl hcb hr
  | @five P b1 b2 b c p q hp hq _ _ =>
    intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
    exact five_doneBMH lib (minkC5_five lib P b c) hp.cell hp.kind (lokSH_callTreeH lib env hp).1.1
      (lokSH_callTreeH lib env hq).1.1 (by rw [(CallTreeH.five hp hq).sixCount]; omega) b0 d0 hu hcl hcb hr
  | @n11s P x f q tag body hq hs hp ih =>
    intro sup region g0 g1 nex b0 d0 hu hcl hcb hr
    rw [runLCH_n11s env snd true hs] at hr
    exact (ih b0 d0 hu hcl hcb hr).minkAs (minkAs_n11s lib tag f)

/-- **The contract of `CallTreeH` at the top**: the whole-subject code with
hints (`finishLUCH`) of every member meets both halves of the contract for
its formula, traces included, on every subject of `P`, for the needs `N` of
the class. -/
theorem finishLUCH_contractCallTreeH (lib : Lib) {env : CallEnv} {N : Needs} {P : Noun → Prop} {x : Bool} {f : Noun}
    {nm : Nomm} (h : CallTreeH lib env N P x f nm) {c : Straight Map} (hc : finishLUCH (S := S) env snd nm = some c) :
    c.need = NeedOrd.this ∧ ∀ s, P s → ContractFwd lib N s f [s] c ∧ ContractBwd lib N s f [s] c :=
  finishLUCH_contractGB lib N (fun hr => (callTreeH_done (S := S) (Map := Map) (snd := snd) lib env h
    (by simp [gen0]) rfl upBelow_gen0 clear_gen0 condBelow_gen0 hr).run) hc

/-- **The bell contract of `CallTreeH`**, for a member at the subjects of the bell. -/
theorem finishLUCH_bellContractCallTreeH {lib : Lib} {env : CallEnv} {N : Needs} {bl : Bell} {x : Bool} {nm : Nomm}
    (h : CallTreeH lib env N (SkaModel.Fits bl.less) x bl.fol nm) {cd : Straight Map}
    (hc : finishLUCH (S := S) env snd nm = some cd) :
    cd.need = NeedOrd.this ∧ BellContract lib N bl true cd := by
  have H := finishLUCH_contractCallTreeH (S := S) lib h hc
  refine ⟨H.1, fun s hs args hargs => ?_⟩
  simp only [if_true, Option.some.injEq] at hargs
  subst hargs
  exact H.2 s hs

end Comp
end SkaModel
end Formalization
