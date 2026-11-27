import lemmas.Compiler.CompRunTNCall
import lemmas.Compiler.CompRunTClass
import lemmas.Compiler.CompSccLoopMemDone
import lemmas.Compiler.CompUnaryDirE

/-!
# The threaded run link at `mono` `|` on the class `DirOk` (README Gaps 19 (g))

The copy of `CompRunTClass.lean` at `mono` `|` (`runLCM env false`, the rest predicate
`XN E msup`), for the member runs of `+compile-scc-in` (lines 3511 and 3531, track I).  The
cases other than the direct call are the generated `CompRunTN*.lean`; the direct call is
`comp_run_n2_directNTT` (`CompRunTNCall.lean`), which asks per call that `sof` be `|`
(`CallOkTN`: the model's `env.sof` false, the pill's push `A 1`).

* `crx_of_runLCN`, `resR_of_resN`: a nomm with no direct call, from the links against `runLC`.
* `comp_run_n7TN`, `CallOkTN`, `DirCallsTN`, `callCode_of_dirTN`, `sixRT_ofN`.
* **`comp_run_dirTN`**, `comp_run_dirXTN`, `res_dirTN`.
* **`mem_runN`**: the run of a member as track I's `mem_gate_done_R` takes it (`hrunN`), with
  `runLC env ~` (its `hrunL`), from `DirCallsTN` in the context `memDCtx`; an `example` feeds
  it to `mem_gate_done_R`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun}

/-- With `mono` `|` the link against `runLC` is one against `runLCM env false`. -/
theorem crx_of_runLCN {env : CallEnv} {msup : Option Nomm} {X : GenRest → Noun → Noun → Prop} {n : Nomm}
    (hn : n.noDirect = true) {goal : CGoalL CSet} {region : List Nat} {g : Gen (TreapMap mugF)}
    (h : CompRunAtR (runLC env msup) ctx n goal region g) :
    CompRunAtX (runLCM env false msup) ctx X n goal region g := by
  intro x mono sup hx _
  rw [runLCM_false env n msup]
  exact h x mono sup hx

/-- `ResFor` is `ResForR (runLCM env false msup)`. -/
theorem resR_of_resN {env : CallEnv} {msup : Option Nomm} {n : Nomm} {region : List Nat} (hn : n.noDirect = true)
    (h : ResFor env msup n region) : ResForR (runLCM env false msup) n region := by
  intro goal g g' nex hi e
  rw [runLCM_false env n msup] at e
  exact h goal g g' nex hi e

/-- **The case `%7` of `+run`, threaded**: `q` with `sup` set to `p` at the
rest `x`, giving `x1`, then `p` at `x1` with the goal `q` returned. -/
theorem comp_run_n7TN {X : GenRest → Noun → Noun → Prop} {Y : GenRest → GenRest → Prop} (hYk : YOk X Y)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (goal : CGoalL CSet) (region : List Nat)
    (g : Gen (TreapMap mugF)) {Xq : GenRest → Noun → Noun → Prop}
    (hq : CompRunAtXT (runLCM env false (some p)) ctx Xq Y q goal region g)
    (hXq : ∀ x mono sup, X x mono sup → Xq x mono (C (A 0) p.toNoun))
    (hp : ∀ nex g1, runLCM env false (some p) q goal region g = some (nex, g1) →
      CompRunAtXT (runLCM env false msup) ctx X Y p nex.goal region g1) :
    CompRunAtXT (runLCM env false msup) ctx X Y (Nomm.n7 p q) goal region g := by
  intro x mono sup hx hX
  obtain ⟨x1, hy1, h1⟩ := hq x mono (C (A 0) p.toNoun) hx (hXq x mono sup hX)
  simp only [crSubj, compCore] at h1
  simp only [Nomm.toNoun]
  rw [cr_disp_n7]
  cases e : runLCM (S := CSet) (Map := TreapMap mugF) env false (some p) q goal region g with
  | none =>
    rw [e] at h1
    refine ⟨x1, hy1, ?_⟩
    simp only [compCore]
    generalize comp.door = Dr at h1 ⊢
    nock_open crK7
    simp [nock_exec, crSubj, cr_bat_dol, h1, runLCM, e, bind, StateT.bind]
  | some r =>
    obtain ⟨nex, g1⟩ := r
    rw [e] at h1
    obtain ⟨x2, hy2, h2⟩ := hp nex g1 e x1 mono sup (hYk.soft hx hy1) (hYk.pres hX hy1)
    refine ⟨x2, hYk.trans hy1 hy2, ?_⟩
    simp only [crSubj, compCore] at h2 h1
    simp only [compCore]
    generalize comp.door = Dr at h1 h2 ⊢
    nock_open crK7
    simp [nock_exec, crSubj, cr_bat_dol, h1, h2, runLCM, e, bind, StateT.bind]

/-- **What one direct call takes, threaded**: the code entry, no ring,
`env.need b = some nb`, and at every rest `x` with `E` the need step to a rest
`x'` with `Y x x'` (on a miss, the compile of the callee's SCC), after which
the call reads as a hit. -/
def CallOkTN (env : CallEnv) (cod ctx : Noun) (E : GenRest → Prop) (Y : GenRest → GenRest → Prop)
    (msup : Option Nomm) (p q : Nomm) (b : Bell) : Prop :=
  CodePure cod env b ∧ env.cod b = some (env.pure b) ∧ env.ring b = Option.none ∧
    ∃ nb, env.need b = some nb ∧ env.sof (made p msup) p q b nb = false ∧ ∀ x, x.NoSoft → E x → ∃ x' sur, Y x x' ∧
      CallNounMT msup ctx p q b nb sur x x' (A 1) (A 1) ∧ CallNounM msup ctx p q b nb sur x' (A 1) (A 1)

/-- **`CallOkTN` of every direct call**, each at the `msup` its run gets,
the subject and formula of a direct call included (a call there may miss
too: the tail of the call is threaded, `comp_run_n2_directXTT`). -/
def DirCallsTN (env : CallEnv) (cod ctx : Noun) (E : GenRest → Prop) (Y : GenRest → GenRest → Prop) :
    Option Nomm → Nomm → Prop
  | ms, Nomm.cons p q => DirCallsTN env cod ctx E Y ms p ∧ DirCallsTN env cod ctx E Y ms q
  | ms, Nomm.n2 p q Option.none => DirCallsTN env cod ctx E Y ms p ∧ DirCallsTN env cod ctx E Y ms q
  | ms, Nomm.n2 p q (some (b, _)) =>
      CallOkTN env cod ctx E Y ms p q b ∧ DirCallsTN env cod ctx E Y ms p ∧ DirCallsTN env cod ctx E Y ms q
  | ms, Nomm.n3 p => DirCallsTN env cod ctx E Y ms p
  | ms, Nomm.n4 p => DirCallsTN env cod ctx E Y ms p
  | ms, Nomm.n5 p q => DirCallsTN env cod ctx E Y ms p ∧ DirCallsTN env cod ctx E Y ms q
  | ms, Nomm.n6 p q r =>
      DirCallsTN env cod ctx E Y ms p ∧ DirCallsTN env cod ctx E Y ms q ∧ DirCallsTN env cod ctx E Y ms r
  | ms, Nomm.n7 p q => DirCallsTN env cod ctx E Y ms p ∧ DirCallsTN env cod ctx E Y (some p) q
  | ms, Nomm.n10 _ v q => DirCallsTN env cod ctx E Y ms v ∧ DirCallsTN env cod ctx E Y ms q
  | _, _ => True

theorem callCode_of_dirTN {env : CallEnv} {cod : Noun} {E : GenRest → Prop} {Y : GenRest → GenRest → Prop} :
    ∀ (n : Nomm), DirOk n = true → ∀ (ms : Option Nomm), DirCallsTN env cod ctx E Y ms n → CallCode cod env n
  | Nomm.cons p q, h, ms, hd => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCallsTN] at hd; simp only [CallCode]
    exact ⟨callCode_of_dirTN p h.1 ms hd.1, callCode_of_dirTN q h.2 ms hd.2⟩
  | Nomm.n0 _, _, _, _ => trivial
  | Nomm.n1 _, _, _, _ => trivial
  | Nomm.n2 p q Option.none, h, ms, hd => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCallsTN] at hd; simp only [CallCode]
    exact ⟨trivial, callCode_of_dirTN p h.1 ms hd.1, callCode_of_dirTN q h.2 ms hd.2⟩
  | Nomm.n2 p q (some (b, Option.none)), h, ms, hd => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCallsTN] at hd; simp only [CallCode]
    exact ⟨⟨hd.1.1, hd.1.2.1⟩, callCode_of_dirTN p h.1 ms hd.2.1, callCode_of_dirTN q h.2 ms hd.2.2⟩
  | Nomm.n2 _ _ (some (_, some _)), h, _, _ => by simp [DirOk] at h
  | Nomm.n3 p, h, ms, hd => by
    simp only [DirOk] at h; simp only [DirCallsTN] at hd; simp only [CallCode]; exact callCode_of_dirTN p h ms hd
  | Nomm.n4 p, h, ms, hd => by
    simp only [DirOk] at h; simp only [DirCallsTN] at hd; simp only [CallCode]; exact callCode_of_dirTN p h ms hd
  | Nomm.n5 p q, h, ms, hd => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCallsTN] at hd; simp only [CallCode]
    exact ⟨callCode_of_dirTN p h.1 ms hd.1, callCode_of_dirTN q h.2 ms hd.2⟩
  | Nomm.n7 p q, h, ms, hd => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCallsTN] at hd; simp only [CallCode]
    exact ⟨callCode_of_dirTN p h.1 ms hd.1, callCode_of_dirTN q h.2 (some p) hd.2⟩
  | Nomm.n10 a v q, h, ms, hd => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCallsTN] at hd; simp only [CallCode]
    exact ⟨callCode_of_dirTN v h.1.2 ms hd.1, callCode_of_dirTN q h.2 ms hd.2⟩
  | Nomm.n6 p q r, h, ms, hd => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCallsTN] at hd; simp only [CallCode]
    exact ⟨callCode_of_dirTN p h.1.1 ms hd.1, callCode_of_dirTN q h.1.2 ms hd.2.1, callCode_of_dirTN r h.2 ms hd.2.2⟩
  | Nomm.n11s _ _ _, h, _, _ => by simp [DirOk] at h
  | Nomm.n11d _ _ _ _, h, _, _ => by simp [DirOk] at h
  | Nomm.n12 _ _, h, _, _ => by simp [DirOk] at h
  | Nomm.mean _ _ _ _ _, h, _, _ => by simp [DirOk] at h

theorem sixRT_ofN (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    {env : CallEnv} {msup : Option Nomm} {X : GenRest → Noun → Noun → Prop} {Y : GenRest → GenRest → Prop}
    {n : Nomm} {region : List Nat}
    (N : PartRTN env msup ctx X Y n region) (hcc : CallCode cod env n) : SixPartsRTN env msup ctx X Y n region :=
  ⟨N.link, N.res, pastForkAt_code h7 hcode env hcc⟩

/-- **The threaded run link at `mono` `|` on the class with direct calls**:
every nomm of `DirOk` whose direct calls meet `CallOkTN` is a `PartRTN` at
`XN E msup` (link threading the rest, result, `+past`), for every `Y` that is
a preorder keeping `NoSoft` and `E` (`YOk`). -/
theorem comp_run_dirTN (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (E : GenRest → Prop) (Y : GenRest → GenRest → Prop) (hY : ∀ msup, YOk (XN E msup) Y) :
    ∀ (n : Nomm), DirOk n = true → ∀ (msup : Option Nomm) (region : List Nat),
      DirCallsTN env cod ctx E Y msup n → PartRTN env msup ctx (XN E msup) Y n region
  | Nomm.cons p q, h, msup, region, hd => by
    have hc := callCode_of_dirTN (ctx := ctx) _ h msup hd
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCallsTN] at hd
    have P := comp_run_dirTN h7 hcode env E Y hY p h.1 msup region hd.1
    have Q := comp_run_dirTN h7 hcode env E Y hY q h.2 msup region hd.2
    exact ⟨fun goal g hi => comp_run_consLRTN (hY msup) h7 hcode env msup p q P Q goal g hi, res_consRN P.res Q.res,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n0 ax, _, msup, region, _ =>
    ⟨fun goal g hi => crxt_of_x (hY msup).refl
        (crx_of_runLCN rfl (crc_of_pure env rfl (comp_run_n0L h7 ax goal region g hi) msup)),
      resR_of_resN rfl (res_n0 env msup ax region), pastAt_nd h7 hcode env.cod trivial⟩
  | Nomm.n1 k, _, msup, region, _ =>
    ⟨fun goal g hi => crxt_of_x (hY msup).refl
        (crx_of_runLCN rfl (crc_of_pure env rfl (comp_run_n1L h7 k goal region g hi) msup)),
      resR_of_resN rfl (res_n1 env msup k region), pastAt_nd h7 hcode env.cod trivial⟩
  | Nomm.n2 p q Option.none, h, msup, region, hd => by
    have hc := callCode_of_dirTN (ctx := ctx) _ h msup hd
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCallsTN] at hd
    have P := comp_run_dirTN h7 hcode env E Y hY p h.1 msup region hd.1
    have Q := comp_run_dirTN h7 hcode env E Y hY q h.2 msup region hd.2
    exact ⟨fun goal g hi => comp_run_n2LRTN (hY msup) h7 hcode env msup p q P Q goal g hi, res_n2RN P.res Q.res,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n2 p q (some (b, Option.none)), h, msup, region, hd => by
    have hc := callCode_of_dirTN (ctx := ctx) _ h msup hd
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCallsTN] at hd
    obtain ⟨⟨hcd, -, hri, nb, hnb, hsof, hE⟩, hdp, hdq⟩ := hd
    have P := comp_run_dirTN h7 hcode env E Y hY p h.1 msup region hdp
    have Q := comp_run_dirTN h7 hcode env E Y hY q h.2 msup region hdq
    exact ⟨fun goal g hi => comp_run_n2_directNTT (hY msup) h7 hcode env p q P Q b hcd nb hE hri hnb hsof goal g hi,
      res_n2_directN P.res Q.res hri hnb hsof, pastAt_code h7 hcode env hc⟩
  | Nomm.n2 _ _ (some (_, some _)), h, _, _, _ => by simp [DirOk] at h
  | Nomm.n3 p, h, msup, region, hd => by
    have hc := callCode_of_dirTN (ctx := ctx) _ h msup hd
    simp only [DirOk] at h; simp only [DirCallsTN] at hd
    have P := comp_run_dirTN h7 hcode env E Y hY p h msup region hd
    exact ⟨fun goal g hi => comp_run_n3LRTN (hY msup) h7 env msup p goal region g hi P.link, res_n3RN P.res,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n4 p, h, msup, region, hd => by
    have hc := callCode_of_dirTN (ctx := ctx) _ h msup hd
    simp only [DirOk] at h; simp only [DirCallsTN] at hd
    have P := comp_run_dirTN h7 hcode env E Y hY p h msup region hd
    exact ⟨fun goal g hi => comp_run_n4LRTN (hY msup) h7 env msup p goal region g hi P.link, res_n4RN P.res,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n5 p q, h, msup, region, hd => by
    have hc := callCode_of_dirTN (ctx := ctx) _ h msup hd
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCallsTN] at hd
    have P := comp_run_dirTN h7 hcode env E Y hY p h.1 msup region hd.1
    have Q := comp_run_dirTN h7 hcode env E Y hY q h.2 msup region hd.2
    exact ⟨fun goal g hi => comp_run_n5LRTN (hY msup) h7 hcode env msup p q P Q goal g hi, res_n5RN P.res Q.res,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n7 p q, h, msup, region, hd => by
    have hc := callCode_of_dirTN (ctx := ctx) _ h msup hd
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCallsTN] at hd
    have P := comp_run_dirTN h7 hcode env E Y hY p h.1 msup region hd.1
    have Q := comp_run_dirTN h7 hcode env E Y hY q h.2 (some p) region hd.2
    exact ⟨fun goal g hi => comp_run_n7TN (hY msup) env msup p q goal region g (Q.link goal g hi)
        (fun x mono sup hX => ⟨hX.1, hX.2.1, rfl⟩)
        (fun nex g1 e => P.link nex.goal g1 (Q.res goal g g1 nex hi e).2.2.1),
      res_n7RN Q.res P.res, pastAt_code h7 hcode env hc⟩
  | Nomm.n10 a v q, h, msup, region, hd => by
    have hc := callCode_of_dirTN (ctx := ctx) _ h msup hd
    simp only [DirOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h; simp only [DirCallsTN] at hd
    have V := comp_run_dirTN h7 hcode env E Y hY v h.1.2 msup region hd.1
    have Q := comp_run_dirTN h7 hcode env E Y hY q h.2 msup region hd.2
    exact ⟨fun goal g hi => comp_run_n10LRTN (hY msup) h7 hcode env msup a h.1.1 v q V Q goal g hi,
      res_n10RN h.1.1 V.res Q.res, pastAt_code h7 hcode env hc⟩
  | Nomm.n6 p q r, h, msup, region, hd => by
    have hc := callCode_of_dirTN (ctx := ctx) _ h msup hd
    have ha := noAx0_of_dir _ h
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCallsTN] at hd; simp only [Bake.NoAx0] at ha
    have hc' := hc
    simp only [CallCode] at hc'
    have P := comp_run_dirTN h7 hcode env E Y hY p h.1.1 msup region hd.1
    have Q := fun rg => comp_run_dirTN h7 hcode env E Y hY q h.1.2 msup rg hd.2.1
    have R := fun rg => comp_run_dirTN h7 hcode env E Y hY r h.2 msup rg hd.2.2
    exact ⟨fun goal g hi => comp_run_n6_allRTN (hY msup) h7 hcode env msup p q r region (sixRT_ofN h7 hcode P hc'.1)
        (sixRT_ofN h7 hcode (Q region) hc'.2.1) (sixRT_ofN h7 hcode (R region) hc'.2.2)
        (fun rid => sixRT_ofN h7 hcode (Q (rid :: region)) hc'.2.1)
        (fun rid => sixRT_ofN h7 hcode (R (rid :: region)) hc'.2.2) ha.2.1 ha.2.2 goal g hi,
      res_n6_allRN P.res (Q region).res (R region).res (fun rid => (Q (rid :: region)).res)
        (fun rid => (R (rid :: region)).res) ha.2.1 ha.2.2,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n11s _ _ _, h, _, _, _ => by simp [DirOk] at h
  | Nomm.n11d _ _ _ _, h, _, _, _ => by simp [DirOk] at h
  | Nomm.n12 _ _, h, _, _, _ => by simp [DirOk] at h
  | Nomm.mean _ _ _ _ _, h, _, _, _ => by simp [DirOk] at h

/-- **The threaded run link on every goal with `GInv`**. -/
theorem comp_run_dirXTN (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (E : GenRest → Prop) (Y : GenRest → GenRest → Prop) (hY : ∀ msup, YOk (XN E msup) Y)
    (n : Nomm) (hn : DirOk n = true) (msup : Option Nomm) (region : List Nat)
    (hd : DirCallsTN env cod ctx E Y msup n) (goal : CGoalL CSet) (g : Gen (TreapMap mugF)) (hi : GInv g goal) :
    CompRunAtXT (runLCM env false msup) ctx (XN E msup) Y n goal region g :=
  (comp_run_dirTN h7 hcode env E Y hY n hn msup region hd).link goal g hi

/-- What a run of the class returns (threaded hypotheses). -/
theorem res_dirTN (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (E : GenRest → Prop) (Y : GenRest → GenRest → Prop) (hY : ∀ msup, YOk (XN E msup) Y)
    (n : Nomm) (hn : DirOk n = true) (msup : Option Nomm) (region : List Nat)
    (hd : DirCallsTN env cod ctx E Y msup n) : ResForR (runLCM env false msup) n region :=
  (comp_run_dirTN h7 hcode env E Y hY n hn msup region hd).res


/-! ## The per-call facts at `mono` `|` -/

/-- **The push of `sof` gives `|`** at the rest `x` (`mono` `|`): what `CallOkTN` asks of the
pill's `sof` (line 3970: no key, and `sound` or no reason for a soft call). -/
def SofRetN (env : CallEnv) (msup : Option Nomm) (ctx : Noun) (p q : Nomm) (b : Bell) (nb : NeedOrd)
    (x : GenRest) : Prop :=
  ∀ (g : Gen (TreapMap mugF)) (SV SN PV goalN regionN : Noun),
    nock (C (env.sure b).toNoun (C SV (C SN (C nb.toNoun (C (A 0) (C PV (crSubj (A 1) (crdN p q b) goalN regionN
      (unitNoun Nomm.toNoun msup) (compCore g x ctx)))))))) crDKc6 = some (A 1)

theorem callNounN_of_read (h7 : slot? 7 ctx = some compK) {env : CallEnv} {msup : Option Nomm} {p q : Nomm}
    {b : Bell} {nb : NeedOrd} {x : GenRest}
    (hcole : ∃ cole, slot? 6846 ctx = some cole ∧ getF mugF b.toNoun cole = some (A 0))
    (hhot : ∃ jh, slot? 54 ctx = some jh) (hr : NeedRead ctx x b nb) (hs : SureNoun env b x)
    (hso : SofRetN env msup ctx p q b nb x) :
    CallNounM msup ctx p q b nb (env.sure b).toNoun x (A 1) (A 1) :=
  ⟨hcole, hhot, cne_read h7 b nb x hcole hhot hr, csu_gate (comp_ctx_pill ctx h7).1 env b x hs, hso⟩

/-- **`CallOkTN` of a callee read at every rest** (a member of the SCC through `map-local` or
`top`, `NeedRead`'s `scc` case, or a hit): no miss, `x' = x`. -/
theorem callOkTN_of_read (h7 : slot? 7 ctx = some compK) {env : CallEnv} {cod : Noun} {E : GenRest → Prop}
    {Y : GenRest → GenRest → Prop} (hY : ∀ x, Y x x) {msup : Option Nomm} {p q : Nomm} {b : Bell} {nb : NeedOrd}
    (hcd : CodePure cod env b) (hc : env.cod b = some (env.pure b)) (hri : env.ring b = Option.none)
    (hnb : env.need b = some nb) (hsof : env.sof (made p msup) p q b nb = false)
    (hcole : ∃ cole, slot? 6846 ctx = some cole ∧ getF mugF b.toNoun cole = some (A 0))
    (hhot : ∃ jh, slot? 54 ctx = some jh)
    (hE : ∀ x, x.NoSoft → E x → NeedRead ctx x b nb ∧ SureNoun env b x ∧ SofRetN env msup ctx p q b nb x) :
    CallOkTN env cod ctx E Y msup p q b :=
  ⟨hcd, hc, hri, nb, hnb, hsof, fun x hx hEx => by
    obtain ⟨hr, hs, hso⟩ := hE x hx hEx
    have hm := callNounN_of_read h7 hcole hhot hr hs hso
    exact ⟨x, _, hY x, callNounMT_of_m hm, hm⟩⟩

/-- **`CallOkTN` of one call at `EnvE`** (`callOkT_of_E` at `mono` `|`): readable at the start,
or outside the SCC with `CalleeCompiled` (a miss compiles the callee's SCC). -/
theorem callOkTN_of_E (h7 : slot? 7 ctx = some compK) {env : CallEnv} {cod : Noun} {x0 : GenRest}
    {R : GenRest → Prop} {msup : Option Nomm} {p q : Nomm} {b : Bell} {nb : NeedOrd}
    (hcd : CodePure cod env b) (hc : env.cod b = some (env.pure b)) (hri : env.ring b = Option.none)
    (hnb : env.need b = some nb) (hsf : env.sof (made p msup) p q b nb = false)
    (hcole : ∃ cole, slot? 6846 ctx = some cole ∧ getF mugF b.toNoun cole = some (A 0))
    (hhot : ∃ jh, slot? 54 ctx = some jh) (hsof : ∀ x, SofRetN env msup ctx p q b nb x)
    (hca : CallAt env R ctx x0 b nb) :
    CallOkTN env cod ctx (EnvE env R x0) (ExtE (EnvE env R x0)) msup p q b := by
  refine ⟨hcd, hc, hri, nb, hnb, hsf, fun x _ hE => ?_⟩
  have hit : NeedRead ctx x b nb → SureNoun env b x → ∃ x' sur, ExtE (EnvE env R x0) x x' ∧
      CallNounMT msup ctx p q b nb sur x x' (A 1) (A 1) ∧ CallNounM msup ctx p q b nb sur x' (A 1) (A 1) := by
    intro hr hs
    have hm := callNounN_of_read h7 hcole hhot hr hs (hsof x)
    exact ⟨x, _, ⟨ext_refl x, id⟩, callNounMT_of_m hm, hm⟩
  rcases hca with ⟨hr, hs⟩ | ⟨S, hS, hin, hcc⟩
  · exact hit (needRead_ext hr hE.2.1) (sureNoun_ext hs hE.2.1 hE.1)
  · obtain ⟨_, NR, MO, SC, INL, SU, hcx, hnm, -⟩ := hE.1
    have hNR : slot? 2 x.cache = some NR := by rw [hcx]; simp [cacheN, nock_exec]
    rcases getF_cases (k := b.toNoun) hnm with h0 | ⟨u, hu⟩
    · obtain ⟨CA', hmiss, hext, hA', hR', N', u', hN', hu'⟩ := hcc x NR MO SC (C INL SU) hE.1 hE.2.2 hcx h0
      obtain ⟨hr', hs'⟩ := hit_of_agree hS hin hnb hA' hN' hu'
      have hm := callNounN_of_read h7 hcole hhot hr' hs' (hsof ⟨CA', x.soft, x.sofs⟩)
      exact ⟨_, _, agreeE_ext hext hA' hR',
        callNounMT_of h7 hcole hhot (NeedStep.miss hS hin hcx h0 hmiss) hs' (hsof ⟨CA', x.soft, x.sofs⟩), hm⟩
    · obtain ⟨hr, hs⟩ := hit_of_agree hS hin hnb hE.1 hNR hu
      exact hit hr hs

/-- **The run of a member of an SCC at `mono` `|`** (track I's `hrunN` of `mem_gate_done_R`):
in the context `memDCtx` of `member`, from the rest `cuRest CA1` with `E`, the pill's `+run` on
`[%done ~]`, region `~`, `sup` `~`, from the bunt state, returns the model's `runLC env ~`
(`hrunL`) with some rest `x1` in `Y`, when every direct call of the member's nomm meets
`CallOkTN` (`DirCallsTN`). -/
theorem mem_runN (SCC CODE LSR JH ML TOP B : Noun) (env : CallEnv) (E : GenRest → Prop)
    (Y : GenRest → GenRest → Prop) (hY : ∀ msup, YOk (XN E msup) Y) (nm : Nomm) (hn : DirOk nm = true)
    (hd : DirCallsTN env CODE (memDCtx SCC (C CODE LSR) JH ML TOP B) E Y Option.none nm)
    (CA1 : Noun) (hE : E (cuRest CA1)) (nex : NextL CSet) (g1 : Gen (TreapMap mugF))
    (hrunL : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1)) :
    ∃ x1, Y (cuRest CA1) x1 ∧ nock (crSubj (A 1) nm.toNoun (C (A 0x656e6f64) (A 0)) (A 0) (A 0)
        (compCore genEntry (cuRest CA1) (memDCtx SCC (C CODE LSR) JH ML TOP B))) crDol
      = some (C nex.goal.toNoun (genNoun g1 x1)) := by
  have h7 : slot? 7 (memDCtx SCC (C CODE LSR) JH ML TOP B) = some compK := rfl
  have h52 : slot? 52 (memDCtx SCC (C CODE LSR) JH ML TOP B) = some CODE := by
    simp [memDCtx, nock_exec]
  obtain ⟨x1, hy, h⟩ := comp_run_dirXTN h7 h52 env E Y hY nm hn Option.none [] hd CGoalL.done genEntry
    (show genEntry.drop = false from rfl) (cuRest CA1) (A 1) (unitNoun Nomm.toNoun Option.none)
    (cu_entry_nosoft CA1) ⟨hE, rfl, rfl⟩
  refine ⟨x1, hy, ?_⟩
  rw [runLCM_false] at h
  have hg : (gen0 : Gen (TreapMap mugF)) = genEntry := rfl
  rw [← hg, hrunL] at h
  exact h

/-- **`mem_runN` is track I's `hrunN`**: it instantiates `mem_gate_done_R` (the gate `member`
on `%done` for a member of a real SCC) at the rest `x1` the run leaves. -/
example (cape : Cape) (DATA FOL : Noun) (keep : Bool) (ML CACHE DN KIDS ML0 CB SCC CODE LSR JH CACHE0 : Noun)
    (nm : Nomm) (CA1 : Noun)
    (hinl : nock (C inlBody (C (C (C (C cape.toNoun DATA) FOL) (C (C CODE LSR) (C JH CACHE))) compK)) inlBody
      = some (C nm.toNoun CA1))
    (env : CallEnv) (nex : NextL CSet) (g1 : Gen (TreapMap mugF))
    (hrunL : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
    (E : GenRest → Prop) (Y : GenRest → GenRest → Prop) (hY : ∀ msup, YOk (XN E msup) Y) (hn : DirOk nm = true)
    (hd : DirCallsTN env CODE (memDCtx SCC (C CODE LSR) JH ML (A 0) (C (C cape.toNoun DATA) FOL)) E Y Option.none nm)
    (hE : E (cuRest CA1)) : True := by
  obtain ⟨x1, -, hrunN⟩ := mem_runN SCC CODE LSR JH ML (A 0) (C (C cape.toNoun DATA) FOL) env E Y hY nm hn hd CA1 hE
    nex g1 hrunL
  have := mem_gate_done_R cape DATA FOL keep ML CACHE DN KIDS ML0 CB SCC CODE LSR JH CACHE0 nm CA1 hinl env nex g1
    hrunL x1 hrunN
  trivial

end Compiler
end Formalization
