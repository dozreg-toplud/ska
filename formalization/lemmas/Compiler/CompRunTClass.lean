import lemmas.Compiler.CompRunTSixAll
import lemmas.Compiler.CompRunRClass
import lemmas.Compiler.CompRunTCall

/-!
# The threaded run link on the class `DirOk` (README Gaps 19 (g))

* `comp_run_n7T`: `%7`, `q` at the rest `x` giving `x1`, then `p` at `x1`.
* `CallOkT`: what a direct call takes, threaded: at every rest with `E` the
  need step to a rest `x'` with `Y x x'` (`CallNounMT`, a miss compiles the
  callee) where the call reads as a hit (`CallNounM`).
* `comp_run_n2_directXT`: the direct call, dropped or not, its parts linked at
  one rest each (`PartLM`).
* `DirCallsT` (`CallOkT` at every direct call, inside the subject and formula
  of another one too), `callCode_of_dirT`, `dirCallsT_of` (the old `DirCalls`
  is the case with no miss), `sixRT_of`, `dirCallsT_nested` (the shape of a
  miss in the subject of a direct call).
* **`comp_run_dirT`**: every nomm of `DirOk` whose direct calls meet `CallOkT`
  is a `PartRT` at `XM E msup`, for every `Y` with `YOk (XM E msup) Y`;
  **`comp_run_dirXT`**, `res_dirT`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-- **The case `%7` of `+run`, threaded**: `q` with `sup` set to `p` at the
rest `x`, giving `x1`, then `p` at `x1` with the goal `q` returned. -/
theorem comp_run_n7T {X : GenRest → Noun → Noun → Prop} {Y : GenRest → GenRest → Prop} (hYk : YOk X Y)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (goal : CGoalL CSet) (region : List Nat)
    (g : Gen (TreapMap mugF)) {Xq : GenRest → Noun → Noun → Prop}
    (hq : CompRunAtXT (runLCM env true (some p)) ctx Xq Y q goal region g)
    (hXq : ∀ x mono sup, X x mono sup → Xq x mono (C (A 0) p.toNoun))
    (hp : ∀ nex g1, runLCM env true (some p) q goal region g = some (nex, g1) →
      CompRunAtXT (runLCM env true msup) ctx X Y p nex.goal region g1) :
    CompRunAtXT (runLCM env true msup) ctx X Y (Nomm.n7 p q) goal region g := by
  intro x mono sup hx hX
  obtain ⟨x1, hy1, h1⟩ := hq x mono (C (A 0) p.toNoun) hx (hXq x mono sup hX)
  simp only [crSubj, compCore] at h1
  simp only [Nomm.toNoun]
  rw [cr_disp_n7]
  cases e : runLCM (S := CSet) (Map := TreapMap mugF) env true (some p) q goal region g with
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
def CallOkT (env : CallEnv) (cod ctx : Noun) (E : GenRest → Prop) (Y : GenRest → GenRest → Prop)
    (msup : Option Nomm) (p q : Nomm) (b : Bell) : Prop :=
  CodePure cod env b ∧ env.cod b = some (env.pure b) ∧ env.ring b = Option.none ∧
    ∃ nb, env.need b = some nb ∧ ∀ x, x.NoSoft → E x → ∃ x' sur SOF, Y x x' ∧
      CallNounMT msup ctx p q b nb sur x x' (A 0) SOF ∧ CallNounM msup ctx p q b nb sur x' (A 0) SOF

/-- A call with `CallOk` (a hit at every rest with `E`) has `CallOkT` for
every reflexive `Y`. -/
theorem callOkT_of {env : CallEnv} {cod : Noun} {E : GenRest → Prop} {Y : GenRest → GenRest → Prop}
    (hY : ∀ x, Y x x) {msup : Option Nomm} {p q : Nomm} {b : Bell} (h : CallOk env cod ctx E msup p q b) :
    CallOkT env cod ctx E Y msup p q b := by
  obtain ⟨h1, h2, h3, nb, h4, h5⟩ := h
  refine ⟨h1, h2, h3, nb, h4, fun x _ hE => ?_⟩
  obtain ⟨sur, SOF, hn⟩ := h5 x hE
  exact ⟨x, sur, SOF, hY x, callNounMT_of_m hn, hn⟩

/-- **The direct call under `mono` `&`, threaded at its own need step**:
dropped (no need step: the old link) or not (`comp_run_n2_callMonoT` at the
rest `x'` the step leaves), the parts `p`, `q` linked at every rest with
`E` (`PartLM`). -/
theorem comp_run_n2_directXT {E : GenRest → Prop} {Y : GenRest → GenRest → Prop} {msup : Option Nomm}
    (hYk : YOk (XM E msup) Y) (h7 : slot? 7 ctx = some compK) {cod : Noun}
    (hcode : slot? 52 ctx = some cod) (env : CallEnv) (p q : Nomm) {region : List Nat}
    (hpn : PastAt ctx env.cod p)
    (P : PartLM env msup ctx E p region) (Q : PartLM env msup ctx E q region) (b : Bell) (hcd : CodePure cod env b)
    (nb : NeedOrd) (hE : ∀ x, x.NoSoft → E x → ∃ x' sur SOF, Y x x' ∧
      CallNounMT msup ctx p q b nb sur x x' (A 0) SOF ∧ CallNounM msup ctx p q b nb sur x' (A 0) SOF)
    (hri : env.ring b = Option.none) (hnb : env.need b = some nb)
    (goal : CGoalL CSet) (g : Gen (TreapMap mugF)) (hinv : GInv g goal) :
    CompRunAtXT (runLCM env true msup) ctx (XM E msup) Y (Nomm.n2 p q (some (b, Option.none))) goal region g := by
  cases hdr : crdDrop (env.pure b) goal with
  | false =>
    rintro x mono sup hx ⟨hEx, rfl, rfl⟩
    obtain ⟨x', sur, SOF, hy, hT, hn⟩ := hE x hx hEx
    have hx' := hYk.soft hx hy
    have hE' : E x' := (hYk.pres (show XM E msup x (A 0) (unitNoun Nomm.toNoun msup) from ⟨hEx, rfl, rfl⟩) hy).1
    obtain ⟨hq, hp, hcp⟩ := crd_hpqM env msup p q P Q b nb goal g hinv x' hx' hE'
    exact ⟨x', hy, comp_run_n2_callMonoT h7 hcode env msup p q hpn b hcd nb sur SOF goal region g hinv hdr hri hnb
      x x' hx' hT hn hq hp hcp⟩
  | true =>
    refine crxt_of_x hYk.refl (crx_iff_mm.2 ?_)
    cases goal with
    | done => simp [crdDrop] at hdr
    | pick z o => simp [crdDrop] at hdr
    | next laz th =>
      simp only [crdDrop, Bool.and_eq_true] at hdr
      obtain ⟨hpu, hne⟩ := hdr
      have hd : g.drop = false := hinv.2.1
      have hj : JmpIn (· < g.re) th := hinv.2.2
      intro x hx hEx
      exact comp_run_n2_dropMono h7 hcode env msup p q hpn b Option.none hcd laz th region g hpu hne x _ _
        (Q.link _ g (ginv_bunt_j hd hj) x hx hEx)
        (fun nexF g2 nexF' g3 e e3 =>
          P.link _ _ (tail_pgoal (ginv_bunt_j hd hj) (linv_bunt _ _) (crd_fq_resR Q.res hd hj e) e3).1 x hx hEx)
        (fun nexF g2 nexF' g3 nexS g4 e e3 e4 => by
          have R2 := crd_fq_resR Q.res hd hj e
          exact (tail_copyH (ginv_bunt_j hd hj) (linv_bunt _ _) (by simp [lregs_bunt]) R2 e3
            (P.res _ _ _ _ (tail_pgoal (ginv_bunt_j hd hj) (linv_bunt _ _) R2 e3).1 e4)).1)

/-- **`CallOkT` of every direct call**, each at the `msup` its run gets,
the subject and formula of a direct call included (a call there may miss
too: the tail of the call is threaded, `comp_run_n2_directXTT`). -/
def DirCallsT (env : CallEnv) (cod ctx : Noun) (E : GenRest → Prop) (Y : GenRest → GenRest → Prop) :
    Option Nomm → Nomm → Prop
  | ms, Nomm.cons p q => DirCallsT env cod ctx E Y ms p ∧ DirCallsT env cod ctx E Y ms q
  | ms, Nomm.n2 p q Option.none => DirCallsT env cod ctx E Y ms p ∧ DirCallsT env cod ctx E Y ms q
  | ms, Nomm.n2 p q (some (b, _)) =>
      CallOkT env cod ctx E Y ms p q b ∧ DirCallsT env cod ctx E Y ms p ∧ DirCallsT env cod ctx E Y ms q
  | ms, Nomm.n3 p => DirCallsT env cod ctx E Y ms p
  | ms, Nomm.n4 p => DirCallsT env cod ctx E Y ms p
  | ms, Nomm.n5 p q => DirCallsT env cod ctx E Y ms p ∧ DirCallsT env cod ctx E Y ms q
  | ms, Nomm.n6 p q r =>
      DirCallsT env cod ctx E Y ms p ∧ DirCallsT env cod ctx E Y ms q ∧ DirCallsT env cod ctx E Y ms r
  | ms, Nomm.n7 p q => DirCallsT env cod ctx E Y ms p ∧ DirCallsT env cod ctx E Y (some p) q
  | ms, Nomm.n10 _ v q => DirCallsT env cod ctx E Y ms v ∧ DirCallsT env cod ctx E Y ms q
  | _, _ => True

/-- **The old `DirCalls` is `DirCallsT` with no miss**, for every reflexive `Y`. -/
theorem dirCallsT_of {env : CallEnv} {cod : Noun} {E : GenRest → Prop} {Y : GenRest → GenRest → Prop}
    (hY : ∀ x, Y x x) : ∀ (ms : Option Nomm) (n : Nomm), DirCalls env cod ctx E ms n → DirCallsT env cod ctx E Y ms n
  | ms, Nomm.cons p q, h => ⟨dirCallsT_of hY ms p h.1, dirCallsT_of hY ms q h.2⟩
  | _, Nomm.n0 _, _ => trivial
  | _, Nomm.n1 _, _ => trivial
  | ms, Nomm.n2 p q Option.none, h => ⟨dirCallsT_of hY ms p h.1, dirCallsT_of hY ms q h.2⟩
  | ms, Nomm.n2 p q (some (_, _)), h => ⟨callOkT_of hY h.1, dirCallsT_of hY ms p h.2.1, dirCallsT_of hY ms q h.2.2⟩
  | ms, Nomm.n3 p, h => dirCallsT_of hY ms p h
  | ms, Nomm.n4 p, h => dirCallsT_of hY ms p h
  | ms, Nomm.n5 p q, h => ⟨dirCallsT_of hY ms p h.1, dirCallsT_of hY ms q h.2⟩
  | ms, Nomm.n6 p q r, h => ⟨dirCallsT_of hY ms p h.1, dirCallsT_of hY ms q h.2.1, dirCallsT_of hY ms r h.2.2⟩
  | ms, Nomm.n7 p q, h => ⟨dirCallsT_of hY ms p h.1, dirCallsT_of hY (some p) q h.2⟩
  | ms, Nomm.n10 _ v q, h => ⟨dirCallsT_of hY ms v h.1, dirCallsT_of hY ms q h.2⟩
  | _, Nomm.n11s _ _ _, _ => trivial
  | _, Nomm.n11d _ _ _ _, _ => trivial
  | _, Nomm.n12 _ _, _ => trivial
  | _, Nomm.mean _ _ _ _ _, _ => trivial

theorem callCode_of_dirT {env : CallEnv} {cod : Noun} {E : GenRest → Prop} {Y : GenRest → GenRest → Prop} :
    ∀ (n : Nomm), DirOk n = true → ∀ (ms : Option Nomm), DirCallsT env cod ctx E Y ms n → CallCode cod env n
  | Nomm.cons p q, h, ms, hd => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCallsT] at hd; simp only [CallCode]
    exact ⟨callCode_of_dirT p h.1 ms hd.1, callCode_of_dirT q h.2 ms hd.2⟩
  | Nomm.n0 _, _, _, _ => trivial
  | Nomm.n1 _, _, _, _ => trivial
  | Nomm.n2 p q Option.none, h, ms, hd => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCallsT] at hd; simp only [CallCode]
    exact ⟨trivial, callCode_of_dirT p h.1 ms hd.1, callCode_of_dirT q h.2 ms hd.2⟩
  | Nomm.n2 p q (some (b, Option.none)), h, ms, hd => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCallsT] at hd; simp only [CallCode]
    exact ⟨⟨hd.1.1, hd.1.2.1⟩, callCode_of_dirT p h.1 ms hd.2.1, callCode_of_dirT q h.2 ms hd.2.2⟩
  | Nomm.n2 _ _ (some (_, some _)), h, _, _ => by simp [DirOk] at h
  | Nomm.n3 p, h, ms, hd => by
    simp only [DirOk] at h; simp only [DirCallsT] at hd; simp only [CallCode]; exact callCode_of_dirT p h ms hd
  | Nomm.n4 p, h, ms, hd => by
    simp only [DirOk] at h; simp only [DirCallsT] at hd; simp only [CallCode]; exact callCode_of_dirT p h ms hd
  | Nomm.n5 p q, h, ms, hd => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCallsT] at hd; simp only [CallCode]
    exact ⟨callCode_of_dirT p h.1 ms hd.1, callCode_of_dirT q h.2 ms hd.2⟩
  | Nomm.n7 p q, h, ms, hd => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCallsT] at hd; simp only [CallCode]
    exact ⟨callCode_of_dirT p h.1 ms hd.1, callCode_of_dirT q h.2 (some p) hd.2⟩
  | Nomm.n10 a v q, h, ms, hd => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCallsT] at hd; simp only [CallCode]
    exact ⟨callCode_of_dirT v h.1.2 ms hd.1, callCode_of_dirT q h.2 ms hd.2⟩
  | Nomm.n6 p q r, h, ms, hd => by
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCallsT] at hd; simp only [CallCode]
    exact ⟨callCode_of_dirT p h.1.1 ms hd.1, callCode_of_dirT q h.1.2 ms hd.2.1, callCode_of_dirT r h.2 ms hd.2.2⟩
  | Nomm.n11s _ _ _, h, _, _ => by simp [DirOk] at h
  | Nomm.n11d _ _ _ _, h, _, _ => by simp [DirOk] at h
  | Nomm.n12 _ _, h, _, _ => by simp [DirOk] at h
  | Nomm.mean _ _ _ _ _, h, _, _ => by simp [DirOk] at h

theorem sixRT_of (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    {env : CallEnv} {msup : Option Nomm} {X : GenRest → Noun → Noun → Prop} {Y : GenRest → GenRest → Prop}
    {n : Nomm} {region : List Nat}
    (N : PartRT env msup ctx X Y n region) (hcc : CallCode cod env n) : SixPartsRT env msup ctx X Y n region :=
  ⟨N.link, N.res, pastForkAt_code h7 hcode env hcc⟩

/-- **The threaded run link at `mono` `&` on the class with direct calls**:
every nomm of `DirOk` whose direct calls meet `CallOkT` is a `PartRT` at
`XM E msup` (link threading the rest, result, `+past`), for every `Y` that is
a preorder keeping `NoSoft` and `E` (`YOk`). -/
theorem comp_run_dirT (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (E : GenRest → Prop) (Y : GenRest → GenRest → Prop) (hY : ∀ msup, YOk (XM E msup) Y) :
    ∀ (n : Nomm), DirOk n = true → ∀ (msup : Option Nomm) (region : List Nat),
      DirCallsT env cod ctx E Y msup n → PartRT env msup ctx (XM E msup) Y n region
  | Nomm.cons p q, h, msup, region, hd => by
    have hc := callCode_of_dirT (ctx := ctx) _ h msup hd
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCallsT] at hd
    have P := comp_run_dirT h7 hcode env E Y hY p h.1 msup region hd.1
    have Q := comp_run_dirT h7 hcode env E Y hY q h.2 msup region hd.2
    exact ⟨fun goal g hi => comp_run_consLRT (hY msup) h7 hcode env msup p q P Q goal g hi, res_consR P.res Q.res,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n0 ax, _, msup, region, _ =>
    ⟨fun goal g hi => crxt_of_x (hY msup).refl
        (crx_of_runLC rfl (crc_of_pure env rfl (comp_run_n0L h7 ax goal region g hi) msup)),
      resR_of_res rfl (res_n0 env msup ax region), pastAt_nd h7 hcode env.cod trivial⟩
  | Nomm.n1 k, _, msup, region, _ =>
    ⟨fun goal g hi => crxt_of_x (hY msup).refl
        (crx_of_runLC rfl (crc_of_pure env rfl (comp_run_n1L h7 k goal region g hi) msup)),
      resR_of_res rfl (res_n1 env msup k region), pastAt_nd h7 hcode env.cod trivial⟩
  | Nomm.n2 p q Option.none, h, msup, region, hd => by
    have hc := callCode_of_dirT (ctx := ctx) _ h msup hd
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCallsT] at hd
    have P := comp_run_dirT h7 hcode env E Y hY p h.1 msup region hd.1
    have Q := comp_run_dirT h7 hcode env E Y hY q h.2 msup region hd.2
    exact ⟨fun goal g hi => comp_run_n2LRT (hY msup) h7 hcode env msup p q P Q goal g hi, res_n2R P.res Q.res,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n2 p q (some (b, Option.none)), h, msup, region, hd => by
    have hc := callCode_of_dirT (ctx := ctx) _ h msup hd
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCallsT] at hd
    obtain ⟨⟨hcd, -, hri, nb, hnb, hE⟩, hdp, hdq⟩ := hd
    have P := comp_run_dirT h7 hcode env E Y hY p h.1 msup region hdp
    have Q := comp_run_dirT h7 hcode env E Y hY q h.2 msup region hdq
    exact ⟨fun goal g hi => comp_run_n2_directXTT (hY msup) h7 hcode env p q P Q b hcd nb hE hri hnb goal g hi,
      res_n2_directMono P.res Q.res hri hnb, pastAt_code h7 hcode env hc⟩
  | Nomm.n2 _ _ (some (_, some _)), h, _, _, _ => by simp [DirOk] at h
  | Nomm.n3 p, h, msup, region, hd => by
    have hc := callCode_of_dirT (ctx := ctx) _ h msup hd
    simp only [DirOk] at h; simp only [DirCallsT] at hd
    have P := comp_run_dirT h7 hcode env E Y hY p h msup region hd
    exact ⟨fun goal g hi => comp_run_n3LRT (hY msup) h7 env msup p goal region g hi P.link, res_n3R P.res,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n4 p, h, msup, region, hd => by
    have hc := callCode_of_dirT (ctx := ctx) _ h msup hd
    simp only [DirOk] at h; simp only [DirCallsT] at hd
    have P := comp_run_dirT h7 hcode env E Y hY p h msup region hd
    exact ⟨fun goal g hi => comp_run_n4LRT (hY msup) h7 env msup p goal region g hi P.link, res_n4R P.res,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n5 p q, h, msup, region, hd => by
    have hc := callCode_of_dirT (ctx := ctx) _ h msup hd
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCallsT] at hd
    have P := comp_run_dirT h7 hcode env E Y hY p h.1 msup region hd.1
    have Q := comp_run_dirT h7 hcode env E Y hY q h.2 msup region hd.2
    exact ⟨fun goal g hi => comp_run_n5LRT (hY msup) h7 hcode env msup p q P Q goal g hi, res_n5R P.res Q.res,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n7 p q, h, msup, region, hd => by
    have hc := callCode_of_dirT (ctx := ctx) _ h msup hd
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCallsT] at hd
    have P := comp_run_dirT h7 hcode env E Y hY p h.1 msup region hd.1
    have Q := comp_run_dirT h7 hcode env E Y hY q h.2 (some p) region hd.2
    exact ⟨fun goal g hi => comp_run_n7T (hY msup) env msup p q goal region g (Q.link goal g hi)
        (fun x mono sup hX => ⟨hX.1, hX.2.1, rfl⟩)
        (fun nex g1 e => P.link nex.goal g1 (Q.res goal g g1 nex hi e).2.2.1),
      res_n7R Q.res P.res, pastAt_code h7 hcode env hc⟩
  | Nomm.n10 a v q, h, msup, region, hd => by
    have hc := callCode_of_dirT (ctx := ctx) _ h msup hd
    simp only [DirOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h; simp only [DirCallsT] at hd
    have V := comp_run_dirT h7 hcode env E Y hY v h.1.2 msup region hd.1
    have Q := comp_run_dirT h7 hcode env E Y hY q h.2 msup region hd.2
    exact ⟨fun goal g hi => comp_run_n10LRT (hY msup) h7 hcode env msup a h.1.1 v q V Q goal g hi,
      res_n10R h.1.1 V.res Q.res, pastAt_code h7 hcode env hc⟩
  | Nomm.n6 p q r, h, msup, region, hd => by
    have hc := callCode_of_dirT (ctx := ctx) _ h msup hd
    have ha := noAx0_of_dir _ h
    simp only [DirOk, Bool.and_eq_true] at h; simp only [DirCallsT] at hd; simp only [Bake.NoAx0] at ha
    have hc' := hc
    simp only [CallCode] at hc'
    have P := comp_run_dirT h7 hcode env E Y hY p h.1.1 msup region hd.1
    have Q := fun rg => comp_run_dirT h7 hcode env E Y hY q h.1.2 msup rg hd.2.1
    have R := fun rg => comp_run_dirT h7 hcode env E Y hY r h.2 msup rg hd.2.2
    exact ⟨fun goal g hi => comp_run_n6_allRT (hY msup) h7 hcode env msup p q r region (sixRT_of h7 hcode P hc'.1)
        (sixRT_of h7 hcode (Q region) hc'.2.1) (sixRT_of h7 hcode (R region) hc'.2.2)
        (fun rid => sixRT_of h7 hcode (Q (rid :: region)) hc'.2.1)
        (fun rid => sixRT_of h7 hcode (R (rid :: region)) hc'.2.2) ha.2.1 ha.2.2 goal g hi,
      res_n6_allR P.res (Q region).res (R region).res (fun rid => (Q (rid :: region)).res)
        (fun rid => (R (rid :: region)).res) ha.2.1 ha.2.2,
      pastAt_code h7 hcode env hc⟩
  | Nomm.n11s _ _ _, h, _, _, _ => by simp [DirOk] at h
  | Nomm.n11d _ _ _ _, h, _, _, _ => by simp [DirOk] at h
  | Nomm.n12 _ _, h, _, _, _ => by simp [DirOk] at h
  | Nomm.mean _ _ _ _ _, h, _, _, _ => by simp [DirOk] at h

/-- **The threaded run link on every goal with `GInv`**. -/
theorem comp_run_dirXT (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (E : GenRest → Prop) (Y : GenRest → GenRest → Prop) (hY : ∀ msup, YOk (XM E msup) Y)
    (n : Nomm) (hn : DirOk n = true) (msup : Option Nomm) (region : List Nat)
    (hd : DirCallsT env cod ctx E Y msup n) (goal : CGoalL CSet) (g : Gen (TreapMap mugF)) (hi : GInv g goal) :
    CompRunAtXT (runLCM env true msup) ctx (XM E msup) Y n goal region g :=
  (comp_run_dirT h7 hcode env E Y hY n hn msup region hd).link goal g hi

/-- What a run of the class returns (threaded hypotheses). -/
theorem res_dirT (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (E : GenRest → Prop) (Y : GenRest → GenRest → Prop) (hY : ∀ msup, YOk (XM E msup) Y)
    (n : Nomm) (hn : DirOk n = true) (msup : Option Nomm) (region : List Nat)
    (hd : DirCallsT env cod ctx E Y msup n) : ResForR (runLCM env true msup) n region :=
  (comp_run_dirT h7 hcode env E Y hY n hn msup region hd).res

/-- **Equality is a `YOk`**: the case with no miss. -/
theorem yOk_eq (X : GenRest → Noun → Noun → Prop) : YOk X (· = ·) :=
  ⟨fun _ => rfl, fun h1 h2 => h1.trans h2, fun hx h => h ▸ hx, fun hX h => h ▸ hX⟩

/-- **A miss in the subject of a direct call is covered** (the shape): for
`[2 [2 p0 q0 b1] q b]`, `DirCallsT` asks `CallOkT` of the inner call `b1`,
whose need step may miss and compile `b1`'s SCC (`CallNounMT` from `x` to
some `x'`), and `comp_run_dirT` links the outer call with that miss inside
the run of its subject. -/
theorem dirCallsT_nested {env : CallEnv} {cod : Noun} {E : GenRest → Prop} {Y : GenRest → GenRest → Prop}
    {ms : Option Nomm} {p0 q0 q : Nomm} {b b1 : Bell} {k k1 : Option Noun}
    (h : CallOkT env cod ctx E Y ms (Nomm.n2 p0 q0 (some (b1, k1))) q b) (h1 : CallOkT env cod ctx E Y ms p0 q0 b1)
    (hp0 : DirCallsT env cod ctx E Y ms p0) (hq0 : DirCallsT env cod ctx E Y ms q0)
    (hq : DirCallsT env cod ctx E Y ms q) :
    DirCallsT env cod ctx E Y ms (Nomm.n2 (Nomm.n2 p0 q0 (some (b1, k1))) q (some (b, k))) :=
  ⟨h, ⟨h1, hp0, hq0⟩, hq⟩

end Compiler
end Formalization
