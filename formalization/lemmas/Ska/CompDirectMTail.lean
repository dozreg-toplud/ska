import lemmas.Ska.CompDirectMGo
import lemmas.Ska.CompDirectMTop
import lemmas.Ska.CompDirect

/-!
# The direct tail call at the top, on the real whole-subject code

README Gaps 18.9 (track J, 2026-11-27).  The first contract theorem for a
nomm with a direct call.  The nomm is the tail call `[2 [0 1] [1 k] b]`
under `%done`, compiled with `mono` `&` (`runLCM env true`, the run of
`+compile-unary`): the callee's subject (the whole subject) is taken into
the register `sub-pes`, the `+mono-try-call` tree splits it along the
registers `sub` of the callee's need `bNed`, the optimistic block is
`[jmp b subV]`, the pessimistic one `[jsp b sub-pes]`, and `+copy` puts a
hop block in front.

* `nDist_of_distinct`: `NDist` is `Distinct` (so `needOrdAllocRegs_spec`
  gives the `NDist` that `monoTry_go` asks).
* `goJ_jsp`: the block `[jsp b r]`.
* `monoTryLoop_ok`: the tree grows the state as `run` does (`Grow`, every
  jump down), leaves `cond`, and its blocks are fixed by a renaming that
  fixes its registers (so by unproxying, `AgreeUB`).
* `runLCM_tail`: the run, step by step.
* `tail_done`: `DoneOK` (so `RunOKGB` under `%done`) of the run, from any
  state of a compile, with hypotheses only on the needs (`N b false = some
  bNed`, `N b true ≠ none`) and the facts of `Annot.direct`.
* `finishLUCM_contractGB`: `finishLUC_contractGB` for `finishLUCM`.
* `finishLUCM_contractTail`, `finishLUCM_bellContractTail`: both halves of
  the contract of the whole-subject code of the tail call.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {Map : Type → Type} [HoonMap Map]

theorem nDist_of_distinct : ∀ {ned : Need}, Distinct ned → NDist ned
  | Need.none, _ => trivial
  | Need.this _, _ => trivial
  | Need.pair _ _, ⟨a, b, c⟩ => ⟨nDist_of_distinct a, nDist_of_distinct b, c⟩
  | Need.both _ _ _, ⟨a, b, c, d, e⟩ => ⟨nDist_of_distinct a, nDist_of_distinct b, c, d, e⟩

section
variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun}

theorem goJ_jsp {o r : Nat} {b : Bell}
    (hb : HoonMap.get c.blocks o = some ⟨[], [], Termin.jsp b r⟩)
    (st : σ) (regs : Map (Option Noun)) (t : Trace) {v : Noun}
    (hv : SkaModel.read r regs = some v) :
    goJ lib O c gul st regs t (jmp0 o) = O.call st b true [v] t gul := by
  rw [goJ_jmp0 _ _ _ _ hb, execBlob]
  simp only [ne_eq, not_true_eq_false, or_self, if_false]
  rw [hv]
  rfl

end

theorem emitted_get_at (g : Gen Map) (b : Blob) (hd : g.drop = false) {k : Nat} (hk : k = g.bo) :
    HoonMap.get (g.emitted b).blocks k = some b := by
  subst hk; exact emitted_get_self g b hd

/-- **The tree of `+mono-try-call` grows the state as `run` does**: every
block it emits jumps down, it leaves `cond`, its result is a label in range,
and a renaming that fixes `r`, the need's registers and the registers it
allocates fixes its blocks. -/
theorem monoTryLoop_ok {fail : Nat} : ∀ (ned : Need) (r o : Nat) (g g' : Gen Map) (o' : Nat),
    monoTryLoop fail ned r o g = some (o', g') → g.drop = false → 1 ≤ fail → fail < g.bo → 1 ≤ o → o < g.bo →
    Grow g g' ∧ g'.cond = g.cond ∧ 1 ≤ o' ∧ o' < g'.bo ∧
      ∀ u : Nat → Nat, u r = r → (∀ x, NMem ned x → u x = x) → (∀ x, g.re ≤ x → x < g'.re → u x = x) →
        ∀ k, g.bo ≤ k → k < g'.bo → (HoonMap.get g'.blocks k).map (renBlob u) = HoonMap.get g'.blocks k := by
  intro ned
  induction ned with
  | none =>
    intro r o g g' o' h hd f1 f2 o1 o2
    simp only [monoTryLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Grow.refl g, rfl, o1, o2, fun _ _ _ _ k h1 h2 => by omega⟩
  | this rn =>
    intro r o g g' o' h hd f1 f2 o1 o2
    simp only [monoTryLoop] at h
    split at h
    · exact absurd h (by simp [crashM])
    rw [emit_apply] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨grow_emit (fun j hj => by simp [finJumps, jmp0] at hj; subst hj; exact ⟨o1, o2⟩), rfl,
      by omega, by simp only [emitted_bo]; omega, fun u ur un _ k h1 h2 => ?_⟩
    simp only [emitted_bo] at h2
    have hk : k = g.bo := by omega
    subst hk
    rw [emitted_get_self _ _ hd]
    simp [renBlob, renPole, renFin, renJmp, jmp0, ur, un rn rfl]
  | pair hn tn ihh iht =>
    intro r o g g' o' h hd f1 f2 o1 o2
    simp only [monoTryLoop] at h
    obtain ⟨rt, ga, h1, h⟩ := bind_some h
    rw [re_apply] at h1; simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨rh, gb, h1, h⟩ := bind_some h
    rw [re_apply] at h1; simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨ot, g1, ht, h⟩ := bind_some h
    obtain ⟨oh, g2, hh, h⟩ := bind_some h
    obtain ⟨os, g3, he, h⟩ := bind_some h
    rw [emit_apply] at he h; simp only [Option.some.injEq, Prod.mk.injEq] at he h
    obtain ⟨rfl, rfl⟩ := he; obtain ⟨rfl, rfl⟩ := h
    obtain ⟨d1, r1, b1, k1⟩ := monoTryLoop_mono _ _ _ _ _ _ ht
    obtain ⟨d2, r2, b2, k2⟩ := monoTryLoop_mono _ _ _ _ _ _ hh
    simp only at d1 r1 b1 k1
    obtain ⟨G1, C1, l1, u1, U1⟩ := iht _ _ _ _ _ ht hd f1 f2 o1 o2
    have hd1 : g1.drop = false := by rw [d1]; exact hd
    obtain ⟨G2, C2, l2, u2, U2⟩ := ihh _ _ _ _ _ hh hd1 f1 (by have := G1.bo; simp only at this; omega) l1 u1
    simp only at G1 C1 U1
    have hd2 : g2.drop = false := by rw [d2]; exact hd1
    refine ⟨(grow_re _).trans ((grow_re _).trans (G1.trans (G2.trans ((grow_emit (fun j hj => by
        simp [finJumps, jmp0] at hj; subst hj; exact ⟨l2, u2⟩)).trans (grow_emit (fun j hj => by
        simp only [finJumps, jmp0, emitted_bo, List.mem_cons, List.mem_nil_iff, or_false] at hj
        rcases hj with hj | hj <;> subst hj <;> simp only [jmp0, emitted_bo]
        · exact ⟨by omega, by omega⟩
        · exact ⟨f1, by omega⟩)))))),
      by simp only [emitted_cond, C2, C1], by simp only [emitted_bo]; omega, by simp only [emitted_bo]; omega,
      fun u ur un ua k h1 h2 => ?_⟩
    simp only [emitted_bo, emitted_re] at h2 ua
    have uh : ∀ x, NMem hn x → u x = x := fun x hx => un x (Or.inl hx)
    have ut : ∀ x, NMem tn x → u x = x := fun x hx => un x (Or.inr hx)
    by_cases e1 : k = g2.bo + 1
    · subst e1
      rw [emitted_get_at _ _ (by simp only [emitted_drop, hd2]) (by simp only [emitted_bo])]
      simp [renBlob, renFin, renJmp, jmp0, ur]
    by_cases e2 : k = g2.bo
    · subst e2
      rw [emitted_get_ne _ _ (by simp only [emitted_bo]; omega), emitted_get_self _ _ hd2]
      simp [renBlob, renPole, renFin, renJmp, jmp0, ur, ua g.re (by omega) (by omega),
        ua (g.re + 1) (by omega) (by omega)]
    rw [emitted_get_ne _ _ (by simp only [emitted_bo]; omega), emitted_get_ne _ _ (by omega)]
    by_cases e3 : g1.bo ≤ k
    · exact U2 u (ua _ (by omega) (by omega)) uh (fun x a b => ua x (by omega) (by omega)) k e3 (by omega)
    · rw [k2 k (by omega)]
      exact U1 u (ua _ (by omega) (by omega)) ut (fun x a b => ua x (by omega) (by omega)) k h1 (by omega)
  | both rn hn tn ihh iht =>
    intro r o g g' o' h hd f1 f2 o1 o2
    simp only [monoTryLoop] at h
    obtain ⟨rt, ga, h1, h⟩ := bind_some h
    rw [re_apply] at h1; simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨rh, gb, h1, h⟩ := bind_some h
    rw [re_apply] at h1; simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨ot, g1, ht, h⟩ := bind_some h
    obtain ⟨oh, g2, hh, h⟩ := bind_some h
    split at h
    · exact absurd h (by simp [crashM])
    obtain ⟨os, g3, he, h⟩ := bind_some h
    rw [emit_apply] at he h; simp only [Option.some.injEq, Prod.mk.injEq] at he h
    obtain ⟨rfl, rfl⟩ := he; obtain ⟨rfl, rfl⟩ := h
    obtain ⟨d1, r1, b1, k1⟩ := monoTryLoop_mono _ _ _ _ _ _ ht
    obtain ⟨d2, r2, b2, k2⟩ := monoTryLoop_mono _ _ _ _ _ _ hh
    simp only at d1 r1 b1 k1
    obtain ⟨G1, C1, l1, u1, U1⟩ := iht _ _ _ _ _ ht hd f1 f2 o1 o2
    have hd1 : g1.drop = false := by rw [d1]; exact hd
    obtain ⟨G2, C2, l2, u2, U2⟩ := ihh _ _ _ _ _ hh hd1 f1 (by have := G1.bo; simp only at this; omega) l1 u1
    simp only at G1 C1 U1
    have hd2 : g2.drop = false := by rw [d2]; exact hd1
    refine ⟨(grow_re _).trans ((grow_re _).trans (G1.trans (G2.trans ((grow_emit (fun j hj => by
        simp [finJumps, jmp0] at hj; subst hj; exact ⟨l2, u2⟩)).trans (grow_emit (fun j hj => by
        simp only [finJumps, jmp0, emitted_bo, List.mem_cons, List.mem_nil_iff, or_false] at hj
        rcases hj with hj | hj <;> subst hj <;> simp only [jmp0, emitted_bo]
        · exact ⟨by omega, by omega⟩
        · exact ⟨f1, by omega⟩)))))),
      by simp only [emitted_cond, C2, C1], by simp only [emitted_bo]; omega, by simp only [emitted_bo]; omega,
      fun u ur un ua k h1 h2 => ?_⟩
    simp only [emitted_bo, emitted_re] at h2 ua
    have uh : ∀ x, NMem hn x → u x = x := fun x hx => un x (Or.inr (Or.inl hx))
    have ut : ∀ x, NMem tn x → u x = x := fun x hx => un x (Or.inr (Or.inr hx))
    by_cases e1 : k = g2.bo + 1
    · subst e1
      rw [emitted_get_at _ _ (by simp only [emitted_drop, hd2]) (by simp only [emitted_bo])]
      simp [renBlob, renFin, renJmp, jmp0, ur]
    by_cases e2 : k = g2.bo
    · subst e2
      rw [emitted_get_ne _ _ (by simp only [emitted_bo]; omega), emitted_get_self _ _ hd2]
      simp [renBlob, renPole, renFin, renJmp, jmp0, ur, ua g.re (by omega) (by omega),
        ua (g.re + 1) (by omega) (by omega), un rn (Or.inl rfl)]
    rw [emitted_get_ne _ _ (by simp only [emitted_bo]; omega), emitted_get_ne _ _ (by omega)]
    by_cases e3 : g1.bo ≤ k
    · exact U2 u (ua _ (by omega) (by omega)) uh (fun x a b => ua x (by omega) (by omega)) k e3 (by omega)
    · rw [k2 k (by omega)]
      exact U1 u (ua _ (by omega) (by omega)) ut (fun x a b => ua x (by omega) (by omega)) k h1 (by omega)

/-! ## The run -/

section Run
variable {S : Type} [HoonSet S] [HoonMapKeys Map]

/-- **The run of the tail call under `%done`, with `mono` `&`**: the
callee's registers `sub`, the register `sub-pes` (`gA.re`), the blocks
`[jmp b subV]` (at `gA.bo`) and `[jsp b sub-pes]` (at `gA.bo + 1`), the
tree from `sub-pes`, and `+copy` of `[0 1]`'s result into the tree. -/
theorem runLCM_tail {env : CallEnv} {sup : Option Nomm} {k : Noun} {b : Bell} {bNed : NeedOrd}
    {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (hring : env.ring b = Option.none) (hned : env.need b = some bNed)
    (h : runLCM env true sup (Nomm.n2 (Nomm.n0 1) (Nomm.n1 k) (some (b, Option.none))) CGoalL.done region g0 =
      some (nex, g1)) :
    ∃ sub gA o' gT, needOrdAllocRegs bNed g0 = some (sub, gA) ∧
      monoTryLoop (gA.bo + 1) sub gA.re gA.bo
        (({ gA with re := gA.re + 1 }.emitted ⟨[], [], Termin.jmp b (flattenNeed sub)⟩).emitted
          ⟨[], [], Termin.jsp b gA.re⟩) = some (o', gT) ∧
      copyL ⟨ofSure (lazyReg gA.re), jmp0 o'⟩ (ofSure Sure.bunt) gT = some (nex, g1) := by
  simp only [runLCM, callLM, callDM, hring, hned, safeFolFol, if_true] at h
  obtain ⟨sub, gA, ha, h⟩ := bind_some h
  obtain ⟨⟨subPes, cb⟩, gB, hm, h⟩ := bind_some h
  simp only [monoBlocks, monoTryCall, bind_apply, re_apply, emit_apply, Option.bind_some] at hm
  obtain ⟨⟨o', gT⟩, ht, hm⟩ := Option.bind_eq_some_iff.mp hm
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hm
  simp only [pure_apply, bind_apply, Option.bind_some] at h
  rw [pastL_pure _ _ (by rfl)] at h
  simp only [pure_apply, Option.bind_some, simpleNextL, if_true] at h
  exact ⟨sub, gA, _, _, ha, ht, h⟩

/-- **`+copy` of a register into a need that asks nothing**: one hop block,
and the result is the register. -/
theorem copyL_reg_bunt {r o : Nat} {g g' : Gen Map} {nex : NextL S} (hd : g.drop = false)
    (h : copyL ⟨ofSure (lazyReg r), jmp0 o⟩ (ofSure Sure.bunt) g = some (nex, g')) :
    nex = ⟨mk ⟨Need.this r, HoonSet.uni HoonSet.empty HoonSet.empty⟩ [] [], jmp0 g.bo⟩ ∧
      g'.re = g.re ∧ g'.bo = g.bo + 1 ∧ g'.drop = false ∧ g'.cond = g.cond ∧
      ∀ k, HoonMap.get g'.blocks k = HoonMap.get (g.emitted ⟨[], [], Termin.hop (jmp0 o)⟩).blocks k := by
  unfold copyL at h
  obtain ⟨oc, ge, he, h⟩ := bind_some h
  rw [emit_apply] at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨laz, gf, hc, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have e : (copyLazyL (S := S) (Map := Map) g.bo (ofSure (lazyReg r)) (ofSure Sure.bunt) : CM Map (Lazy S)) =
      fun g2 => (addOps g.bo [] g2).bind fun x => some (mk ⟨Need.this r, HoonSet.uni HoonSet.empty HoonSet.empty⟩ [] [], x.2) := by
    funext g2; rfl
  rw [e] at hc
  obtain ⟨⟨u, gu⟩, hu, hc⟩ := Option.bind_eq_some_iff.mp hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  obtain ⟨bk, hbk, rfl⟩ := addOps_spec hu (by simp only [emitted_drop, hd])
  refine ⟨rfl, rfl, rfl, hd, rfl, fun k => ?_⟩
  simp only [HoonMap.get_put, List.nil_append]
  split
  · rename_i e; subst e; rw [hbk]
  · rfl

end Run

/-! ## `+mink` on the tail call -/

/-- The formula of the tail call, `[2 [0 1] [1 k]]`. -/
def tailFol (k : Noun) : Noun := n3 (A 2) (C (A 0) (A 1)) (C (A 1) k)

theorem minkStep_axis1 (lib : Lib) (gul : Noun) (go : Trace → Noun → Noun → Option Tone) (t : Trace) (s : Noun) :
    minkStep lib gul go t s (C (A 0) (A 1)) = some (Tone.zero s) := by
  simp [minkStep, slot?, axisPath, axisPathFuel, slotAtPath]

theorem minkStep_quote (lib : Lib) (gul : Noun) (go : Trace → Noun → Noun → Option Tone) (t : Trace) (s k : Noun) :
    minkStep lib gul go t s (C (A 1) k) = some (Tone.zero k) := by simp [minkStep]

theorem minkStep_two (lib : Lib) (gul : Noun) (go : Trace → Noun → Noun → Option Tone) (t : Trace) (s b c : Noun) :
    minkStep lib gul go t s (C (A 2) (C b c)) = tbind (go t s b) fun s' => tbind (go t s c) fun f' => go t s' f' := by
  simp [minkStep]

theorem minkF_tail_eq (lib : Lib) (gul : Noun) (m : Nat) (tm : Trace) (s k : Noun) :
    minkF lib gul (m + 2) tm s (tailFol k) = minkF lib gul (m + 1) tm s k := by
  rw [minkF_succ_eq]
  simp only [tailFol, n3, minkStep_two, minkF_succ_eq, minkStep_axis1, minkStep_quote, tbind_zero]

theorem minkF_tail {lib : Lib} {gul : Noun} {n : Nat} {tm : Trace} {s k : Noun} {r : Tone}
    (h : minkF lib gul n tm s (tailFol k) = some r) : ∃ j, j < n ∧ minkF lib gul j tm s k = some r := by
  match n, h with
  | m + 2, h => exact ⟨m + 1, by omega, by rw [← minkF_tail_eq]; exact h⟩
  | 0, h => simp [minkF] at h
  | 1, h => exact absurd h (by intro e; cases e)

theorem mink_tail_bwd {lib : Lib} {gul : Noun} {tm : Trace} {s k : Noun} {r : Tone}
    (h : Mink lib gul tm s k r) : Mink lib gul tm s (tailFol k) r := by
  obtain ⟨m, hm⟩ := h
  cases m with
  | zero => simp [minkF] at hm
  | succ m => exact ⟨m + 2, by rw [minkF_tail_eq]; exact hm⟩

theorem Grow.congr_right {g g' g'' : Gen Map} (h : Grow g g') (hb : g''.bo = g'.bo) (hd : g''.drop = g'.drop)
    (hk : ∀ k, HoonMap.get g''.blocks k = HoonMap.get g'.blocks k) : Grow g g'' where
  bo := hb ▸ h.bo
  drop := hd.trans h.drop
  keep := fun k x hk' hx => by rw [hk]; exact h.keep k x hk' hx
  new := fun k x hx => by rw [hk] at hx; rw [hb]; exact h.new k x hx

/-! ## The run meets `DoneOK` -/

section Top
variable {S : Type} [HoonSet S] [HoonMapKeys Map]

/-- **The tail call under `%done` meets `DoneOK`** (so `RunOKGB`), from any
state of a compile: the hypotheses are on the needs (the callee's n-ary
need `bNed`, which the compile used and `N` holds, and some need for the
call by subject) and the facts `Annot.direct` gives (`[0 1]`'s products fit
the bell, `[1 k]` gives its formula).  No hypothesis about the run.  The
optimistic path is `tailStep_fwd` / `tailStep_bwd`; the pessimistic path,
taken where the subject does not have the cells `bNed` splits, asks the
oracle for the call by subject, which `OracleFwd` / `OracleBwd` answer for
`N b true`. -/
theorem tail_done (lib : Lib) {N : Needs} {env : CallEnv} {P : Noun → Prop} {k : Noun} {b : Bell}
    {bNed ndT : NeedOrd} (hring : env.ring b = Option.none) (hned : env.need b = some bNed)
    (hNf : N b false = some bNed) (hNt : N b true = some ndT)
    (hAp : ∀ x gul y, P x → Mink lib gul [] x (C (A 0) (A 1)) (Tone.zero y) → SkaModel.Fits b.less y)
    (hAq : ∀ x gul g, P x → Mink lib gul [] x (C (A 1) k) (Tone.zero g) → g = b.fol)
    {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcb : CondBelow g0)
    (hr : runLCM env true sup (Nomm.n2 (Nomm.n0 1) (Nomm.n1 k) (some (b, Option.none))) CGoalL.done region g0 =
      some (nex, g1)) :
    DoneOK lib N P (tailFol k) g0 g1 nex := by
  obtain ⟨sub, gA, o', gT, ha, ht, hc⟩ := runLCM_tail hring hned hr
  obtain ⟨⟨kA, rfl⟩, la, dA, ma⟩ := needOrdAllocRegs_spec bNed _ _ _ ha
  simp only at la ma ht hc
  -- the state after the two call blocks
  have qre : ((({ g0 with re := kA + 1 } : Gen Map).emitted ⟨[], [], Termin.jmp b (flattenNeed sub)⟩).emitted
      ⟨[], [], Termin.jsp b kA⟩).re = kA + 1 := rfl
  have qbo : ((({ g0 with re := kA + 1 } : Gen Map).emitted ⟨[], [], Termin.jmp b (flattenNeed sub)⟩).emitted
      ⟨[], [], Termin.jsp b kA⟩).bo = g0.bo + 2 := rfl
  have qdr : ((({ g0 with re := kA + 1 } : Gen Map).emitted ⟨[], [], Termin.jmp b (flattenNeed sub)⟩).emitted
      ⟨[], [], Termin.jsp b kA⟩).drop = false := d0
  have qcn : ((({ g0 with re := kA + 1 } : Gen Map).emitted ⟨[], [], Termin.jmp b (flattenNeed sub)⟩).emitted
      ⟨[], [], Termin.jsp b kA⟩).cond = g0.cond := rfl
  have qb : ∀ x, HoonMap.get ((({ g0 with re := kA + 1 } : Gen Map).emitted
      ⟨[], [], Termin.jmp b (flattenNeed sub)⟩).emitted ⟨[], [], Termin.jsp b kA⟩).blocks x =
      if x = g0.bo + 1 then some ⟨[], [], Termin.jsp b kA⟩ else
      if x = g0.bo then some ⟨[], [], Termin.jmp b (flattenNeed sub)⟩ else HoonMap.get g0.blocks x := by
    intro x; simp [Gen.emitted, d0, HoonMap.get_put]
  have GQ : Grow g0 ((({ g0 with re := kA + 1 } : Gen Map).emitted ⟨[], [], Termin.jmp b (flattenNeed sub)⟩).emitted
      ⟨[], [], Termin.jsp b kA⟩) :=
    (grow_reg g0 (kA + 1)).trans ((grow_emit (fun j hj => by simp [finJumps] at hj)).trans
      (grow_emit (fun j hj => by simp [finJumps] at hj)))
  generalize ((({ g0 with re := kA + 1 } : Gen Map).emitted ⟨[], [], Termin.jmp b (flattenNeed sub)⟩).emitted
      ⟨[], [], Termin.jsp b kA⟩) = gQ at qre qbo qdr qcn qb GQ ht
  obtain ⟨GT, CT, lo', hi', UT⟩ := monoTryLoop_ok _ _ _ _ _ _ ht qdr (by omega) (by omega) b0 (by omega)
  obtain ⟨dT, rT, bT, kT⟩ := monoTryLoop_mono _ _ _ _ _ _ ht
  obtain ⟨rfl, r1, b1, d1, c1, k1⟩ := copyL_reg_bunt (by rw [dT]; exact qdr) hc
  have e0 : entries (⟨mk ⟨Need.this kA, HoonSet.uni HoonSet.empty HoonSet.empty⟩ [] [], jmp0 gT.bo⟩ :
      NextL S).laz = [] := entries_ofSure _
  have g1c : g1.cond = g0.cond := by rw [c1, CT, qcn]
  have hb1 : ∀ x, HoonMap.get g1.blocks x =
      if x = gT.bo then some ⟨[], [], Termin.hop (jmp0 o')⟩ else HoonMap.get gT.blocks x := by
    intro x; rw [k1 x]; simp [Gen.emitted, dT, qdr, HoonMap.get_put]
  have hl : ∀ x, x < g0.bo → HoonMap.get g1.blocks x = HoonMap.get g0.blocks x := by
    intro x hx
    rw [hb1, if_neg (by omega), kT x (by omega), qb, if_neg (by omega), if_neg (by omega)]
  -- the blocks of the code, unproxied
  have blocks : ∀ (cf : Map (Nat × List Nat)), (∀ x, x < g1.re → HoonMap.get cf x = HoonMap.get g1.cond x) →
      ∀ (c : Straight Map), (∀ o, g0.bo ≤ o → o < g1.bo →
        HoonMap.get c.blocks o = (HoonMap.get g1.blocks o).map (unproxyBlob cf)) →
      HoonMap.get c.blocks gT.bo = some ⟨[], [], Termin.hop (jmp0 o')⟩ ∧
      HoonMap.get c.blocks g0.bo = some ⟨[], [], Termin.jmp b (flattenNeed sub)⟩ ∧
      HoonMap.get c.blocks (g0.bo + 1) = some ⟨[], [], Termin.jsp b kA⟩ ∧
      ∀ x, gQ.bo ≤ x → x < gT.bo → HoonMap.get c.blocks x = HoonMap.get gT.blocks x := by
    intro cf hcf c ag
    have hu' : ∀ x, g0.re ≤ x → x < g1.re → unproxy cf x = x := fun x h1 h2 =>
      unproxy_none (by rw [hcf x h2, g1c]; exact condBelow_none hcb h1)
    have hsub : ∀ x, NMem sub x → unproxy cf x = x := fun x hx =>
      hu' x (ma x hx).1 (by have := (ma x hx).2; omega)
    have hkA : unproxy cf kA = kA := hu' kA la (by omega)
    refine ⟨?_, ?_, ?_, fun x h1 h2 => ?_⟩
    · rw [ag _ (by omega) (by omega), hb1, if_pos rfl]
      simp [unproxyBlob, renBlob, renFin, renJmp, jmp0]
    · rw [ag _ (Nat.le_refl _) (by omega), hb1, if_neg (by omega), kT _ (by omega), qb, if_neg (by omega),
        if_pos rfl]
      simp only [Option.map_some, unproxyBlob, renBlob, renFin, List.map_nil]
      rw [List.map_congr_left (g := id) (fun x hx => hsub x ((mem_flatten sub x).mp hx)), List.map_id]
    · rw [ag _ (by omega) (by omega), hb1, if_neg (by omega), kT _ (by omega), qb, if_pos rfl]
      simp [unproxyBlob, renBlob, renFin, hkA]
    · rw [ag _ (by omega) (by omega), hb1, if_neg (by omega)]
      exact UT (unproxy cf) hkA hsub (fun y a b => hu' y (by omega) (by omega)) x h1 h2
  -- `+mink` on the call
  have hfit : ∀ s gul, P s → SkaModel.Fits b.less s := fun s gul hs =>
    hAp s gul s hs ⟨1, minkStep_axis1 _ _ _ _ _⟩
  have hk : ∀ s gul, P s → k = b.fol := fun s gul hs => hAq s gul k hs ⟨1, minkStep_quote _ _ _ _ _ _⟩
  refine ⟨⟨⟨by omega, by omega, by rw [d1, d0], hl⟩,
    (GQ.trans (GT.trans (Grow.congr_right (grow_emit (fun j hj => by
      simp [finJumps, jmp0] at hj; subst hj; exact ⟨lo', hi'⟩)) b1 (by rw [d1, emitted_drop, dT, qdr]) k1))).toU hu,
    condFresh_of_eq (by omega) g1c, (by simp only [jmp0]; omega), (by simp only [jmp0]; omega),
    Or.inl ⟨_, (by simp only [jmp0]; rw [hb1, if_pos rfl]), rfl, rfl⟩,
    fun r hr => Or.inr (by simp only [NMem] at hr; subst hr; omega), trivial,
    fun e he => (by rw [e0] at he; cases he), fun e he => (by rw [e0] at he; cases he), (by rw [e0]; simp),
    fun s hs hf => absurd ⟨trivial, (looks_uni _ _ _).mpr ⟨looks_empty _, looks_empty _⟩⟩ hf,
    fun r hr => (by simp only [NMem] at hr; subst hr; rw [g1c]; exact condBelow_none hcb la),
    fun e he => (by rw [e0] at he; cases he), ?_, ?_⟩, (by rw [e0]; simp), ⟨rfl, fun e he => (by cases he)⟩, trivial,
    fun e he => (by rw [e0] at he; cases he)⟩
  · -- forward
    intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    obtain ⟨Bh, Bo, Bp, Bt⟩ := blocks cf hcf c (fun o h1 h2 => (ag st).1 o h1 h2 (by rw [e0]; simp))
    have hv : SkaModel.read kA regs = some s := hh.1
    have e1 : goJ lib O c gul st regs t (jmp0 gT.bo) = goJ lib O c gul st regs t (jmp0 o') := by
      rw [goJ_jmp0 _ _ _ _ Bh, execBlob_hop]
    obtain ⟨regs', keep, res⟩ := monoTry_go (lib := lib) (O := O) (c := c) (gul := gul) (st := st)
      sub kA g0.bo gQ gT o' ht qdr Bt (nDist_of_distinct dA) (fun x hx => by have := (ma x hx).2; omega)
      (by omega) (fun hx => by have := (ma kA hx).2; omega) regs t s hv
    obtain ⟨j, hj, hm'⟩ := minkF_tail hm
    rw [hk s gul hs] at hm'
    show ReturnsC lib O c gul Inv ν st regs t (jmp0 gT.bo) r
    rcases res with ⟨fit, hold, e2⟩ | ⟨nfit, e2⟩
    · obtain ⟨ton, st', a1, a2, a3, a4⟩ := tailStep_fwd hS hF hNf ha Bo hI (hN st hI) hold (hfit s gul hs) htr hj hm'
      exact ⟨ton, st', a1, a2, by rw [e1, e2, a3], a4⟩
    · have hv' : SkaModel.read kA regs' = some s := by
        rw [keep kA (by omega) (fun hx => by have := (ma kA hx).2; omega)]; exact hv
      have J := goJ_jsp (lib := lib) (O := O) (gul := gul) Bp st regs' t hv'
      have hargs : argsFor (ν st) b true s = some [s] := by simp [argsFor, hN st hI b true ndT hNt]
      obtain ⟨ton, st', hc', hrel⟩ := hF.call st b true [s] t tm gul s j r hI hj (hfit s gul hs) hargs htr hm'
      obtain ⟨hI', hle⟩ := hS.call st b true [s] t gul ton st' hI hc'
      exact ⟨ton, st', hI', hle, by rw [e1, e2, J, hc'], hrel⟩
  · -- backward
    intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨Bh, Bo, Bp, Bt⟩ := blocks cf hcf c (fun o h1 h2 => (ag st).1 o h1 h2 (by rw [e0]; simp))
    have hv : SkaModel.read kA regs = some s := hh.1
    have e1 : goJ lib O c gul st regs t (jmp0 gT.bo) = goJ lib O c gul st regs t (jmp0 o') := by
      rw [goJ_jmp0 _ _ _ _ Bh, execBlob_hop]
    obtain ⟨regs', keep, res'⟩ := monoTry_go (lib := lib) (O := O) (c := c) (gul := gul) (st := st)
      sub kA g0.bo gQ gT o' ht qdr Bt (nDist_of_distinct dA) (fun x hx => by have := (ma x hx).2; omega)
      (by omega) (fun hx => by have := (ma kA hx).2; omega) regs t s hv
    have hk' := hk s gul hs
    rcases res' with ⟨fit, hold, e2⟩ | ⟨nfit, e2⟩
    · rw [e1, e2] at hres
      obtain ⟨r, hmk, ton, st', a1, a2, a3, a4⟩ := tailStep_bwd hS hB hNf ha Bo hI (hN st hI) hold (hfit s gul hs) htr hres
      exact ⟨r, mink_tail_bwd (hk' ▸ hmk), ton, st', a1, a2, by rw [e1, e2, a3], a4⟩
    · have hv' : SkaModel.read kA regs' = some s := by
        rw [keep kA (by omega) (fun hx => by have := (ma kA hx).2; omega)]; exact hv
      have J := goJ_jsp (lib := lib) (O := O) (gul := gul) Bp st regs' t hv'
      have hargs : argsFor (ν st) b true s = some [s] := by simp [argsFor, hN st hI b true ndT hNt]
      rw [e1, e2, J] at hres
      obtain ⟨ton, st'⟩ := res
      obtain ⟨r, hmk, hrel⟩ := hB.call st b true [s] t gul ton st' hI hres s tm (hfit s gul hs) hargs htr
      obtain ⟨hI', hle⟩ := hS.call st b true [s] t gul ton st' hI hres
      exact ⟨r, mink_tail_bwd (hk' ▸ hmk), ton, st', hI', hle, by rw [e1, e2, J, hres], hrel⟩

/-! ## The top -/

/-- **`finishLUC_contractGB` for `finishLUCM`** (its text, with `runLCM env
true`): the whole-subject code of a nomm whose run for `%done` from
`gen0` meets `RunOKGB` at the needs `N` has the need `this` and meets both
halves of the contract for `N` on the subjects of `P`. -/
theorem finishLUCM_contractGB (lib : Lib) {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm} (N : Needs)
    (hR : ∀ {nex : NextL S} {gE : Gen Map}, runLCM env true Option.none nm (CGoalL.done : CGoalL S) [] (gen0 : Gen Map) =
      some (nex, gE) → RunOKGB lib N P f (CGoal.done : CGoal S) gen0 gE nex)
    {c : Straight Map} (h : finishLUCM (S := S) env nm = some c) :
    c.need = NeedOrd.this ∧ ∀ s, P s → ContractFwd lib N s f [s] c ∧ ContractBwd lib N s f [s] c := by
  unfold finishLUCM at h
  obtain ⟨⟨nex, gE⟩, hr, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨⟨o', sub⟩, g8⟩, hk, hts⟩ := Option.bind_eq_some_iff.mp h
  simp only at hts
  have R : RunOKGB lib N P f (CGoal.done : CGoal S) gen0 gE nex := hR hr
  have T : TopSB gE nex :=
    { ext := R.ext
      grow := R.grow
      cfr := R.cfr
      lo := R.lo
      hi := R.hi
      args := by
        rcases R.ent with ⟨b, _, _, ha⟩ | e
        · exact ha
        · exact e.elim
      regs := fun r hr => by
        rcases R.regs r hr with e | e
        · exact e.elim
        · exact e
      dist := R.dist
      eregs := fun e he => ⟨(R.eregs e he).1, fun r hr => ⟨by
        rcases ((R.eregs e he).2 r hr).1 with a | a
        · exact a.elim
        · exact a, ((R.eregs e he).2 r hr).2⟩⟩
      labs := R.labs
      nodup := R.nodup
      ncond := R.ncond
      econd := R.econd }
  have bad : ∀ {tm : Trace} {r : Tone}, BadC (CGoal.done : CGoal S) tm r → r = Tone.two tm := fun hb => by
    rcases hb with e | ⟨_, _, hp⟩
    · exact e
    · exact hp.elim
  have F := finishTop_genB lib T (fwdPhi lib N P f)
    (fun cf hcf c ned σ O st t gul s ag hned regs hh hn Inv ν n tm r hs hN hS hF hm hI htr => by
      obtain ⟨ton, st', -, -, he, hrel⟩ :=
        R.sem cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s s r hI htr hs hm ag hned regs hh hn
      exact ⟨ton, st', he, hrel⟩)
    (fun σ O st t gul s hfs Inv ν n tm r hs _ _ _ hm _ htr =>
      ⟨Tone.two t, st, rfl, by rw [bad ((R.nec s hs hfs).1 gul n tm r hm)]; exact ToneRel.two htr⟩) hk hts
  have B := finishTop_genB lib T (bwdPhi lib N P f)
    (fun cf hcf c ned σ O st t gul s ag hned regs hh hn Inv ν tm hs hN hS hB hI htr ton st'' hx => by
      obtain ⟨r, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s s hI htr hs ag hned regs hh hn _ hx
      obtain ⟨ton', st', -, -, he, hrel⟩ := G
      rw [he] at hx
      cases hx
      exact ⟨r, hm, hrel⟩)
    (fun σ O st t gul s hfs Inv ν tm hs _ _ _ _ htr ton st' hx => by
      cases hx
      obtain ⟨r, hm, hb⟩ := (R.nec s hs hfs).2 gul tm
      rw [bad hb] at hm
      exact ⟨_, hm, ToneRel.two htr⟩) hk hts
  refine ⟨F.1, fun s hs => ⟨fun σ Inv ν O n gul ti tm r hN hS hF hm st hI htr => ?_,
    fun σ Inv ν O gul ti tm hN hS hB st ton st' hI htr hx => ?_⟩⟩
  · exact F.2 σ O st s ti gul Inv ν n tm r hs hN hS hF hm hI htr
  · exact B.2 σ O st s ti gul Inv ν tm hs hN hS hB hI htr ton st' hx

/-- **The direct tail call at the top meets both halves of the contract**
on the real whole-subject code (`finishLUCM`), for the needs `N` that hold
the callee's n-ary need `bNed` (the one the compile used) and some need for
its call by subject, on the subjects of `P` where `Annot.direct`'s facts
hold.  No hypothesis about the run. -/
theorem finishLUCM_contractTail (lib : Lib) {env : CallEnv} {P : Noun → Prop} {k : Noun} {b : Bell}
    {N : Needs} {bNed ndT : NeedOrd} (hring : env.ring b = Option.none) (hned : env.need b = some bNed)
    (hNf : N b false = some bNed) (hNt : N b true = some ndT)
    (hAp : ∀ x gul y, P x → Mink lib gul [] x (C (A 0) (A 1)) (Tone.zero y) → SkaModel.Fits b.less y)
    (hAq : ∀ x gul g, P x → Mink lib gul [] x (C (A 1) k) (Tone.zero g) → g = b.fol)
    {c : Straight Map} (hc : finishLUCM (S := S) env (Nomm.n2 (Nomm.n0 1) (Nomm.n1 k) (some (b, Option.none))) = some c) :
    c.need = NeedOrd.this ∧ ∀ s, P s → ContractFwd lib N s (tailFol k) [s] c ∧ ContractBwd lib N s (tailFol k) [s] c :=
  finishLUCM_contractGB lib N (fun hr => (tail_done lib hring hned hNf hNt hAp hAq (by simp [gen0]) rfl
    upBelow_gen0 condBelow_gen0 hr).run) hc

/-- **The bell contract of the direct tail call** (`finishLUC_contractNC`'s
form): the code `finishLUCM` makes for a bell `bl` whose formula is
`[2 [0 1] [1 k]]` with the callee `b` meets `BellContract`, given the facts
`Annot.direct` gives on the subjects that fit `bl`. -/
theorem finishLUCM_bellContractTail {lib : Lib} {bl b : Bell} {k : Noun} (hf : bl.fol = tailFol k)
    {env : CallEnv} {N : Needs} {bNed ndT : NeedOrd} (hring : env.ring b = Option.none)
    (hned : env.need b = some bNed) (hNf : N b false = some bNed) (hNt : N b true = some ndT)
    (hAp : ∀ x gul y, SkaModel.Fits bl.less x → Mink lib gul [] x (C (A 0) (A 1)) (Tone.zero y) →
      SkaModel.Fits b.less y)
    (hAq : ∀ x gul g, SkaModel.Fits bl.less x → Mink lib gul [] x (C (A 1) k) (Tone.zero g) → g = b.fol)
    {cd : Straight Map} (hc : finishLUCM (S := S) env (Nomm.n2 (Nomm.n0 1) (Nomm.n1 k) (some (b, Option.none))) = some cd) :
    cd.need = NeedOrd.this ∧ BellContract lib N bl true cd := by
  have H := finishLUCM_contractTail (S := S) lib (P := SkaModel.Fits bl.less) hring hned hNf hNt hAp hAq hc
  refine ⟨H.1, fun s hs args hargs => ?_⟩
  simp only [if_true, Option.some.injEq] at hargs
  subst hargs
  rw [hf]
  exact H.2 s hs

end Top

end Comp
end SkaModel
end Formalization
