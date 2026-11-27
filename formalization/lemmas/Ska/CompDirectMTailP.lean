import lemmas.Ska.CompDirectMTail
import lemmas.Ska.CompSevenLS
import lemmas.Ska.CompFourTop

/-!
# The direct tail call `[2 p q b]` at the top, `p` in the class

README Gaps 18.11 (track J, 2026-11-27).  The direct call under `%done`,
compiled with `mono` `&` (`runLCM env true`), whose subject part `p` meets
`LOKS false` (track C's class: `CallTree7`, `CallTreeA` with index `true`)
and whose formula part `q` is skipped (`safeFolFol q`) and returns the
callee's formula on every subject.  The run: `+need-ord-alloc-regs`, the
blocks `[jmp b subV]`, `[jsp b sub-pes]`, the `+mono-try-call` tree from
`sub-pes`, then `p` under `%next (lazy-from-reg sub-pes) (jmp0 tree)`, then
`+copy` of `p`'s result into the need that asks nothing (one hop block in
front).

The proof reads the call as `[7 p [2 [0 1] [1 b.fol]]]` (`minkC7_direct`):
the tree and the two call blocks meet `RunOKGB` under `%done` on the
products of `p` (`treeX_run`, `tail_done` without the copy), `p` followed by
the copy meets `RunOKLB` under the tree's result (`LOKS.run` and
`RunOKLB.copyBunt`), and `runOKGB_sevenL` composes.

* `copyL_bunt`, `RunOKLB.copyBunt`: `+copy` into the need that asks nothing
  keeps `RunOKLB` (a hop block in front of the result's jump).
* `monoTryLoop_root`: the tree's root block has no parameters.
* `minkC7_direct`: `+mink` on `[2 fb fq]` is that of `[7 fb [2 [0 1] [1
  k]]]` when `fq` returns `k` and never crashes.
* `treeX_run`, `runLCM_tailP`, `tailP_done`: `DoneOK` of the run.
* `finishLUCM_contractTailP`, `finishLUCM_bellContractTailP`: both halves
  of the contract on the real whole-subject code.
* `consTail_contract`: the instance `[2 [[0 a] [0 b']] [1 k] b]`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## `+copy` into the need that asks nothing -/

theorem copyNeed_none_r (l : Need) (ops : List Pole) :
    (copyNeed l Need.none ops : CM Map (Need × List Pole)) = pure (l, ops) := by
  cases l <;> rfl

/-- **`+copy` of a result into the need that asks nothing**: one hop block
to the result's jump, and the same lazy need (its `lok` joined with the
empty set). -/
theorem copyL_bunt {first : NextL S} {g g' : Gen Map} {nex : NextL S} (hd : g.drop = false)
    (h : copyL first (ofSure Sure.bunt) g = some (nex, g')) :
    nex = ⟨mk ⟨first.laz.sure.ned, HoonSet.uni first.laz.sure.lok HoonSet.empty⟩ first.laz.fork first.laz.bond,
      jmp0 g.bo⟩ ∧
      g'.re = g.re ∧ g'.bo = g.bo + 1 ∧ g'.drop = false ∧ g'.cond = g.cond ∧
      ∀ k, HoonMap.get g'.blocks k = HoonMap.get (g.emitted ⟨[], [], Termin.hop first.th⟩).blocks k := by
  unfold copyL at h
  obtain ⟨oc, ge, he, h⟩ := bind_some h
  rw [emit_apply] at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨laz, gf, hc, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rcases first with ⟨⟨s1, f1, b1⟩, th1⟩
  have e : (copyLazyL (S := S) (Map := Map) g.bo (mk s1 f1 b1) (ofSure Sure.bunt) : CM Map (Lazy S)) =
      fun g2 => (addOps g.bo [] g2).bind fun x => some (mk ⟨s1.ned, HoonSet.uni s1.lok HoonSet.empty⟩ f1 b1, x.2) := by
    funext g2
    simp only [copyLazyL, copyNeed_none_r, bind_apply, pure_apply, Option.bind_some, ofSure, Sure.bunt, fork_mk,
      bond_mk, sure_mk, List.isEmpty_nil, if_true]
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

section
variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {Inv : σ → Prop} {ν : σ → Needs}

/-- `GoalSemCMD` depends on its jump only through `goJ`. -/
theorem goalSemCMD_congr {K : Nat → Prop} {st : σ} {regs : Map (Option Noun)} {t tm : Trace} {je je' : Jmp}
    {sur : Sure S} {th : Jmp} {Q : Noun → Need → Noun → Prop}
    (e : goJ lib O c gul st regs t je' = goJ lib O c gul st regs t je) :
    ∀ {r : Tone}, GoalSemCMD lib O c gul Inv ν K st regs t tm je sur th Q r →
      GoalSemCMD lib O c gul Inv ν K st regs t tm je' sur th Q r
  | Tone.zero p, h => ⟨fun fs => by
      obtain ⟨st', regs', d, w, a1, a2, a3, a4, a5, a6, a7⟩ := h.1 fs
      exact ⟨st', regs', d, w, a1, a2, a3, a4, a5, a6, e.trans a7⟩, fun nf => by
      obtain ⟨ton, st', a1, a2, a3, a4⟩ := h.2 nf
      exact ⟨ton, st', a1, a2, e.trans a3, a4⟩⟩
  | Tone.one _, h => by obtain ⟨ton, st', a1, a2, a3, a4⟩ := h; exact ⟨ton, st', a1, a2, e.trans a3, a4⟩
  | Tone.two _, h => by obtain ⟨ton, st', a1, a2, a3, a4⟩ := h; exact ⟨ton, st', a1, a2, e.trans a3, a4⟩

end

/-- **`+copy` into the need that asks nothing keeps `RunOKLB`**: the hop
block in front of the result's jump runs as the jump itself. -/
theorem RunOKLB.copyBunt {lib : Lib} {N : Needs} {P : Noun → Prop} {f : Noun} {L : Lazy S} {th : Jmp} {Q : Wit}
    {x : Bool} {g0 g1 g2 : Gen Map} {nex nex' : NextL S} (R : RunOKLB (Map := Map) lib N P f L th Q x g0 g1 nex)
    (hu : UpBelow g0) (d1 : g1.drop = false) (hta : th.args = []) (hL : ∀ e ∈ entries L, e.1 < g0.bo)
    (hc : copyL nex (ofSure Sure.bunt) g1 = some (nex', g2)) :
    RunOKLB lib N P f L th Q x g0 g2 nex' := by
  obtain ⟨rfl, r2, b2, d2, c2, k2⟩ := copyL_bunt d1 hc
  rcases nex with ⟨⟨s1, f1, b1⟩, th1⟩
  have hb2 : ∀ k, HoonMap.get g2.blocks k =
      if k = g1.bo then some ⟨[], [], Termin.hop th1⟩ else HoonMap.get g1.blocks k := by
    intro k; rw [k2 k]; simp [Gen.emitted, d1, HoonMap.get_put]
  have rb := R.bo
  have hargs : th1.args = [] := nextArgs_nil R.ent hta
  have lab : ∀ e ∈ entries (Lazy.mk s1 f1 b1), e.1 < g1.bo := fun e he => by
    rcases (R.labs e he).1 with h | h
    · obtain ⟨e', he', ee⟩ := List.mem_map.mp h; have := hL e' he'; omega
    · exact h.2
  have GG : Grow g1 g2 := Grow.congr_right (grow_emit (g := g1) (b := ⟨[], [], Termin.hop th1⟩) (fun j hj => by
    simp [finJumps] at hj; subst hj; exact ⟨R.lo, R.hi⟩)) b2 (by rw [d2, emitted_drop, d1]) k2
  have ag' : ∀ {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
      {cf : Map (Nat × List Nat)} {ned : Need} {s0 s : Noun},
      AgreeLB lib O c gul st t cf ned g0 g2 (Lazy.mk ⟨s1.ned, HoonSet.uni s1.lok HoonSet.empty⟩ f1 b1) s0 s →
      AgreeLB lib O c gul st t cf ned g0 g1 (Lazy.mk s1 f1 b1) s0 s := fun ag =>
    ⟨fun o h0 h1 hn => by rw [ag.1 o h0 (by omega) hn, hb2, if_neg (by omega)],
     fun e he l => by
      obtain ⟨A, B, th', a, b, c'⟩ := ag.2 e he l
      rw [hb2, if_neg (by have := lab e he; omega)] at a
      rw [r2] at c'
      exact ⟨A, B, th', a, b, c'⟩⟩
  have blk : ∀ {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
      {cf : Map (Nat × List Nat)} {ned : Need} {s0 s : Noun},
      AgreeLB lib O c gul st t cf ned g0 g2 (Lazy.mk ⟨s1.ned, HoonSet.uni s1.lok HoonSet.empty⟩ f1 b1) s0 s →
      ∀ regs, goJ lib O c gul st regs t (jmp0 g1.bo) = goJ lib O c gul st regs t th1 := by
    intro σ O c gul st t cf ned s0 s ag regs
    have hb : HoonMap.get c.blocks g1.bo = some ⟨[], [], Termin.hop th1⟩ := by
      rw [ag.1 g1.bo (by omega) (by omega) (fun hm => by
        obtain ⟨e, he, ee⟩ := List.mem_map.mp hm; have := lab e he; omega), hb2, if_pos rfl]
      simp [unproxyBlob, renBlob, renFin, renJmp_nil _ hargs]
    rw [goJ_jmp0 _ _ _ _ hb, execBlob_hop]
  refine ⟨by rw [r2]; exact R.re, by rw [b2]; omega, d2.trans (d1.symm.trans R.drop),
    fun o ho hn => by rw [hb2, if_neg (by omega)]; exact R.keep o ho hn, R.grow.trans (GG.toU (R.grow.up hu)),
    R.cfr.trans (condFresh_of_eq (by omega) c2), (by simp only [jmp0]; have := R.lo; have := R.hi; omega),
    (by simp only [jmp0]; omega), Or.inl ⟨_, (by simp only [jmp0]; rw [hb2, if_pos rfl]), rfl, rfl⟩,
    fun r hr => (R.regs r hr).imp id (fun h => ⟨h.1, by rw [r2]; exact h.2⟩), R.dist,
    fun e he => ⟨(R.eregs e he).1, fun r hr => ((R.eregs e he).2 r hr).imp id
      (fun h => h.imp id (fun h => ⟨h.1, by rw [r2]; exact h.2⟩))⟩,
    fun e he => ⟨(R.labs e he).1.imp id (fun h => ⟨h.1, by omega⟩), by
      obtain ⟨B, th', hb⟩ := (R.labs e he).2
      exact ⟨B, th', by rw [hb2, if_neg (by have := lab e he; omega)]; exact hb⟩⟩,
    R.nodup, fun s v d w r hq hr => by rw [r2]; exact R.dreg s v d w r hq hr,
    fun s hs hf => R.nec s hs (fun h => hf ⟨h.1, (looks_uni _ _ _).mpr ⟨h.2, looks_empty _⟩⟩),
    fun r hr => by rw [c2]; exact R.ncond r hr, fun e he r hr => by rw [c2]; exact R.econd e he r hr,
    fun e he => ?_, ?_, ?_⟩
  · obtain ⟨F, h1, h2⟩ := R.front e he
    refine ⟨F, fun B fin hb => ?_, fun cf hcf => ?_⟩
    · have hlt : e.1 < g0.bo := hL e he
      rw [hb2, if_neg (by omega)]; exact h1 B fin hb
    · rw [r2]
      exact h2 cf (fun k hk => by rw [hcf k (by rw [r2]; exact hk), c2])
  · intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    have G := R.sem cf (fun k hk => by rw [hcf k (by rw [r2]; exact hk), c2]) c ned σ Inv ν O n gul hN hS hF
      st t tm s0 s r hI htr hs hm (fun st' => ag' (ag st')) (fun y hy => by rw [← r2]; exact hned y hy) regs
      ⟨hh.1, ((looks_uni _ _ _).mp hh.2).1⟩ hn
    exact goalSemCMD_congr (blk (ag st) regs) G
  · intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    rw [blk (ag st) regs] at hres
    obtain ⟨r, hm, G⟩ := R.semB cf (fun k hk => by rw [hcf k (by rw [r2]; exact hk), c2]) c ned σ Inv ν O gul
      hN hS hB st t tm s0 s hI htr hs (fun st' => ag' (ag st')) (fun y hy => by rw [← r2]; exact hned y hy) regs
      ⟨hh.1, ((looks_uni _ _ _).mp hh.2).1⟩ hn res hres
    exact ⟨r, hm, goalSemCMD_congr (blk (ag st) regs) G⟩

/-! ## The root of the tree -/

/-- **The tree's root is the block it was given or a block it made with no
parameters.** -/
theorem monoTryLoop_root {fail : Nat} (ned : Need) (r o : Nat) {g g' : Gen Map} {o' : Nat}
    (h : monoTryLoop fail ned r o g = some (o', g')) (hd : g.drop = false) :
    (o' = o ∧ g' = g) ∨ ∃ bk, HoonMap.get g'.blocks o' = some bk ∧ bk.par = [] := by
  cases ned with
  | none =>
    simp only [monoTryLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    exact Or.inl ⟨h.1.symm, h.2.symm⟩
  | this rn =>
    simp only [monoTryLoop] at h
    split at h
    · exact absurd h (by simp [crashM])
    rw [emit_apply] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inr ⟨_, emitted_get_self _ _ hd, rfl⟩
  | pair hn tn =>
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
    obtain ⟨d1, -, -, -⟩ := monoTryLoop_mono _ _ _ _ _ _ ht
    obtain ⟨d2, -, -, -⟩ := monoTryLoop_mono _ _ _ _ _ _ hh
    simp only at d1 d2
    exact Or.inr ⟨_, emitted_get_self _ _ (by simp only [emitted_drop, d2, d1, hd]), rfl⟩
  | both rn hn tn =>
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
    obtain ⟨d1, -, -, -⟩ := monoTryLoop_mono _ _ _ _ _ _ ht
    obtain ⟨d2, -, -, -⟩ := monoTryLoop_mono _ _ _ _ _ _ hh
    simp only at d1 d2
    exact Or.inr ⟨_, emitted_get_self _ _ (by simp only [emitted_drop, d2, d1, hd]), rfl⟩

/-! ## `+mink` -/

/-- **The direct call `[2 fb fq]` as `[7 fb [2 [0 1] [1 k]]]`**, when `fq`
returns `k` on every subject of `P` and nothing else. -/
theorem minkC7_direct (lib : Lib) (P : Noun → Prop) (fb fq k : Noun)
    (hq1 : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {rc : Tone}, P s → minkF lib gul n tm s fq = some rc →
      rc = Tone.zero k)
    (hq2 : ∀ {s gul : Noun} {tm : Trace}, P s → Mink lib gul tm s fq (Tone.zero k)) :
    MinkC7 lib P (n3 (A 2) fb fq) fb (tailFol k) where
  fwd := fun {s gul n tm r} hs h => by
    obtain ⟨n', hn, rb, hb, H⟩ := (minkC2_indirect lib P fb fq).fwd hs h
    refine ⟨n', by omega, rb, hb, ?_⟩
    rcases H with H | ⟨x, rfl, rc, hc, H⟩
    · exact Or.inl H
    · have ek := hq1 hs hc
      subst ek
      rcases H with ⟨hnz, _⟩ | ⟨y, ey, hy⟩
      · exact absurd rfl (hnz k)
      · cases ey
        refine Or.inr ⟨x, rfl, n' + 1, by omega, ?_⟩
        cases n' with
        | zero => simp [minkF] at hy
        | succ m => rw [minkF_tail_eq]; exact hy
  bwd := fun {s gul tm rb} hs hb => by
    have B := (minkC2_indirect lib P fb fq).bwd hs hb
    refine ⟨B.1, fun u r eu hr => ?_⟩
    obtain ⟨m, hm⟩ := hr
    obtain ⟨j, -, hj⟩ := minkF_tail hm
    exact ((B.2 u _ eu (hq2 hs)).2 k r rfl ⟨j, hj⟩)

/-- `[1 k]` returns `k` and nothing else. -/
theorem quote_hq1 {lib : Lib} {k s gul : Noun} {n : Nat} {tm : Trace} {rc : Tone}
    (h : minkF lib gul n tm s (C (A 1) k) = some rc) : rc = Tone.zero k := by
  cases n with
  | zero => simp [minkF] at h
  | succ m => rw [minkF_succ_eq, minkStep_quote] at h; exact (Option.some.inj h).symm

theorem quote_hq2 {lib : Lib} {k s gul : Noun} {tm : Trace} : Mink lib gul tm s (C (A 1) k) (Tone.zero k) :=
  ⟨1, by rw [minkF_succ_eq, minkStep_quote]⟩

/-! ## The tree and the call blocks under `%done`, before the copy -/

/-- **The tree and the two call blocks under `%done` meet `RunOKGB`** with
the result `[lazy-from-reg sub-pes, tree]` (`tail_done` without `+copy`),
for the tail formula `[2 [0 1] [1 b.fol]]` on subjects that fit the bell. -/
theorem treeX_run (lib : Lib) {N : Needs} {P : Noun → Prop} {b : Bell} {bNed ndT : NeedOrd}
    (hNf : N b false = some bNed) (hNt : N b true = some ndT)
    (hfit : ∀ s, P s → SkaModel.Fits b.less s)
    {g0 gA gT : Gen Map} {sub : Need} {o' : Nat}
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcb : CondBelow g0)
    (ha : needOrdAllocRegs bNed g0 = some (sub, gA))
    (ht : monoTryLoop (gA.bo + 1) sub gA.re gA.bo
        (({ gA with re := gA.re + 1 }.emitted ⟨[], [], Termin.jmp b (flattenNeed sub)⟩).emitted
          ⟨[], [], Termin.jsp b gA.re⟩) = some (o', gT)) :
    RunOKGB lib N P (tailFol b.fol) (CGoal.done : CGoal S) g0 gT ⟨ofSure (lazyReg gA.re), jmp0 o'⟩ ∧
      g0.re ≤ gA.re ∧ gA.re < gT.re := by
  obtain ⟨⟨kA, rfl⟩, la, dA, ma⟩ := needOrdAllocRegs_spec bNed _ _ _ ha
  simp only at la ma ht ⊢
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
  have root := monoTryLoop_root _ _ _ ht qdr
  have e0 : entries (ofSure (lazyReg kA : Sure S)) = [] := entries_ofSure _
  have gTc : gT.cond = g0.cond := by rw [CT, qcn]
  have hl : ∀ x, x < g0.bo → HoonMap.get gT.blocks x = HoonMap.get g0.blocks x := by
    intro x hx
    rw [kT x (by omega), qb, if_neg (by omega), if_neg (by omega)]
  have ent : ∃ bk, HoonMap.get gT.blocks o' = some bk ∧ bk.par = [] := by
    rcases root with ⟨rfl, rfl⟩ | h
    · exact ⟨_, by rw [qb, if_neg (by omega), if_pos rfl], rfl⟩
    · exact h
  obtain ⟨bk, hbk, hpar⟩ := ent
  -- the blocks of the code, unproxied
  have blocks : ∀ (cf : Map (Nat × List Nat)), (∀ x, x < gT.re → HoonMap.get cf x = HoonMap.get gT.cond x) →
      ∀ (c : Straight Map), (∀ o, g0.bo ≤ o → o < gT.bo →
        HoonMap.get c.blocks o = (HoonMap.get gT.blocks o).map (unproxyBlob cf)) →
      HoonMap.get c.blocks g0.bo = some ⟨[], [], Termin.jmp b (flattenNeed sub)⟩ ∧
      HoonMap.get c.blocks (g0.bo + 1) = some ⟨[], [], Termin.jsp b kA⟩ ∧
      ∀ x, gQ.bo ≤ x → x < gT.bo → HoonMap.get c.blocks x = HoonMap.get gT.blocks x := by
    intro cf hcf c ag
    have hu' : ∀ x, g0.re ≤ x → x < gT.re → unproxy cf x = x := fun x h1 h2 =>
      unproxy_none (by rw [hcf x h2, gTc]; exact condBelow_none hcb h1)
    have hsub : ∀ x, NMem sub x → unproxy cf x = x := fun x hx =>
      hu' x (ma x hx).1 (by have := (ma x hx).2; omega)
    have hkA : unproxy cf kA = kA := hu' kA la (by omega)
    refine ⟨?_, ?_, fun x h1 h2 => ?_⟩
    · rw [ag _ (Nat.le_refl _) (by omega), kT _ (by omega), qb, if_neg (by omega), if_pos rfl]
      simp only [Option.map_some, unproxyBlob, renBlob, renFin, List.map_nil]
      rw [List.map_congr_left (g := id) (fun x hx => hsub x ((mem_flatten sub x).mp hx)), List.map_id]
    · rw [ag _ (by omega) (by omega), kT _ (by omega), qb, if_pos rfl]
      simp [unproxyBlob, renBlob, renFin, hkA]
    · rw [ag _ (by omega) (by omega)]
      exact UT (unproxy cf) hkA hsub (fun y a b => hu' y (by omega) (by omega)) x h1 h2
  refine ⟨⟨⟨by omega, by omega, by rw [dT, qdr, d0], hl⟩, (GQ.trans GT).toU hu, condFresh_of_eq (by omega) gTc,
    (by simp only [jmp0]; omega), (by simp only [jmp0]; omega), Or.inl ⟨bk, hbk, hpar, rfl⟩,
    fun r hr => Or.inr (by simp only [ofSure, sure_mk, lazyReg, NMem] at hr; subst hr; omega), trivial,
    fun e he => (by rw [e0] at he; cases he), fun e he => (by rw [e0] at he; cases he), (by rw [e0]; simp),
    fun s hs hf => absurd (fitsS_lazyReg kA s) hf,
    fun r hr => (by simp only [ofSure, sure_mk, lazyReg, NMem] at hr; subst hr; rw [gTc]; exact condBelow_none hcb la),
    fun e he => (by rw [e0] at he; cases he), ?_, ?_⟩, la, by omega⟩
  · -- forward
    intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    obtain ⟨Bo, Bp, Bt⟩ := blocks cf hcf c (fun o h1 h2 => (ag st).1 o h1 h2 (by rw [e0]; simp))
    have hv : SkaModel.read kA regs = some s := hh.1
    obtain ⟨regs', keep, res⟩ := monoTry_go (lib := lib) (O := O) (c := c) (gul := gul) (st := st)
      sub kA g0.bo gQ gT o' ht qdr Bt (nDist_of_distinct dA) (fun x hx => by have := (ma x hx).2; omega)
      (by omega) (fun hx => by have := (ma kA hx).2; omega) regs t s hv
    obtain ⟨j, hj, hm'⟩ := minkF_tail hm
    show ReturnsC lib O c gul Inv ν st regs t (jmp0 o') r
    rcases res with ⟨fit, hold, e2⟩ | ⟨nfit, e2⟩
    · obtain ⟨ton, st', a1, a2, a3, a4⟩ := tailStep_fwd hS hF hNf ha Bo hI (hN st hI) hold (hfit s hs) htr hj hm'
      exact ⟨ton, st', a1, a2, by rw [e2, a3], a4⟩
    · have hv' : SkaModel.read kA regs' = some s := by
        rw [keep kA (by omega) (fun hx => by have := (ma kA hx).2; omega)]; exact hv
      have J := goJ_jsp (lib := lib) (O := O) (gul := gul) Bp st regs' t hv'
      have hargs : argsFor (ν st) b true s = some [s] := by simp [argsFor, hN st hI b true ndT hNt]
      obtain ⟨ton, st', hc', hrel⟩ := hF.call st b true [s] t tm gul s j r hI hj (hfit s hs) hargs htr hm'
      obtain ⟨hI', hle⟩ := hS.call st b true [s] t gul ton st' hI hc'
      exact ⟨ton, st', hI', hle, by rw [e2, J, hc'], hrel⟩
  · -- backward
    intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨Bo, Bp, Bt⟩ := blocks cf hcf c (fun o h1 h2 => (ag st).1 o h1 h2 (by rw [e0]; simp))
    have hv : SkaModel.read kA regs = some s := hh.1
    obtain ⟨regs', keep, res'⟩ := monoTry_go (lib := lib) (O := O) (c := c) (gul := gul) (st := st)
      sub kA g0.bo gQ gT o' ht qdr Bt (nDist_of_distinct dA) (fun x hx => by have := (ma x hx).2; omega)
      (by omega) (fun hx => by have := (ma kA hx).2; omega) regs t s hv
    rcases res' with ⟨fit, hold, e2⟩ | ⟨nfit, e2⟩
    · rw [e2] at hres
      obtain ⟨r, hmk, ton, st', a1, a2, a3, a4⟩ := tailStep_bwd hS hB hNf ha Bo hI (hN st hI) hold (hfit s hs) htr hres
      exact ⟨r, mink_tail_bwd hmk, ton, st', a1, a2, by rw [e2, a3], a4⟩
    · have hv' : SkaModel.read kA regs' = some s := by
        rw [keep kA (by omega) (fun hx => by have := (ma kA hx).2; omega)]; exact hv
      have J := goJ_jsp (lib := lib) (O := O) (gul := gul) Bp st regs' t hv'
      have hargs : argsFor (ν st) b true s = some [s] := by simp [argsFor, hN st hI b true ndT hNt]
      rw [e2, J] at hres
      obtain ⟨ton, st'⟩ := res
      obtain ⟨r, hmk, hrel⟩ := hB.call st b true [s] t gul ton st' hI hres s tm (hfit s hs) hargs htr
      obtain ⟨hI', hle⟩ := hS.call st b true [s] t gul ton st' hI hres
      exact ⟨r, mink_tail_bwd hmk, ton, st', hI', hle, by rw [e2, J, hres], hrel⟩

/-! ## The run -/

theorem pastL_bunt (cod : Bell → Option Bool) (th : Jmp) (nom : Nomm) (region : List Nat) :
    (pastL cod (⟨ofSure Sure.bunt, th⟩ : NextL S) nom region : CM Map (NextL S)) = pure ⟨ofSure Sure.bunt, th⟩ := by
  unfold pastL
  rw [if_pos ⟨rfl, (HoonSet.small_iff _).2 fun x hx => absurd hx (HoonSet.mem_empty x), rfl⟩]

/-- **The run of the direct call under `%done` with `mono` `&`, `q`
skipped**: the callee's registers, the two call blocks, the tree, `p` under
`%next (lazy-from-reg sub-pes) (jmp0 tree)`, `+copy` into the need that asks
nothing. -/
theorem runLCM_tailP {env : CallEnv} {sup : Option Nomm} {p q : Nomm} {b : Bell} {bNed : NeedOrd}
    {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (hring : env.ring b = Option.none) (hned : env.need b = some bNed) (hq : safeFolFol q = true)
    (h : runLCM env true sup (Nomm.n2 p q (some (b, Option.none))) CGoalL.done region g0 = some (nex, g1)) :
    ∃ sub gA o' gT nexS g5, needOrdAllocRegs bNed g0 = some (sub, gA) ∧
      monoTryLoop (gA.bo + 1) sub gA.re gA.bo
        (({ gA with re := gA.re + 1 }.emitted ⟨[], [], Termin.jmp b (flattenNeed sub)⟩).emitted
          ⟨[], [], Termin.jsp b gA.re⟩) = some (o', gT) ∧
      runLCM env true sup p (CGoalL.next (ofSure (lazyReg gA.re)) (jmp0 o')) region gT = some (nexS, g5) ∧
      copyL nexS (ofSure Sure.bunt) g5 = some (nex, g1) := by
  simp only [runLCM, callLM, callDM, hring, hned, hq, if_true] at h
  obtain ⟨sub, gA, ha, h⟩ := bind_some h
  obtain ⟨⟨subPes, cb⟩, gB, hm, h⟩ := bind_some h
  simp only [monoBlocks, monoTryCall, bind_apply, re_apply, emit_apply, Option.bind_some] at hm
  obtain ⟨⟨o', gT⟩, ht, hm⟩ := Option.bind_eq_some_iff.mp hm
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hm
  simp only [pure_apply, bind_apply, Option.bind_some] at h
  rw [pastL_bunt] at h
  simp only [pure_apply, Option.bind_some] at h
  obtain ⟨⟨nexS, g5⟩, hp, hc⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨sub, gA, _, _, _, _, ha, ht, hp, hc⟩

/-! ## The run meets `DoneOK` -/

/-- **The direct call `[2 p q b]` under `%done` meets `DoneOK`** (so
`RunOKGB`), from any state of a compile: `p` meets `LOKS false` and has no
direct call, `q` is skipped and returns the callee's formula (and nothing
else) on every subject, the products of `p` fit the bell (`Annot.direct`),
and the needs are those of `tail_done`. -/
theorem tailP_done (lib : Lib) {N : Needs} {env : CallEnv} {P : Noun → Prop} {p q : Nomm} {fb fq : Noun}
    {b : Bell} {bNed ndT : NeedOrd} (hring : env.ring b = Option.none) (hned : env.need b = some bNed)
    (hNf : N b false = some bNed) (hNt : N b true = some ndT)
    (Sp : LOKS (S := S) (Map := Map) false lib N env P fb p) (hpd : p.noDirect = true) (hcount : sixCount p ≤ 255)
    (hq : safeFolFol q = true)
    (hAp : ∀ x gul y, P x → Mink lib gul [] x fb (Tone.zero y) → SkaModel.Fits b.less y)
    (hq1 : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {rc : Tone}, P s → minkF lib gul n tm s fq = some rc →
      rc = Tone.zero b.fol)
    (hq2 : ∀ {s gul : Noun} {tm : Trace}, P s → Mink lib gul tm s fq (Tone.zero b.fol))
    {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (hr : runLCM env true sup (Nomm.n2 p q (some (b, Option.none))) CGoalL.done region g0 = some (nex, g1)) :
    DoneOK lib N P (n3 (A 2) fb fq) g0 g1 nex := by
  obtain ⟨sub, gA, o', gT, nexS, g5, ha, ht, hp, hc⟩ := runLCM_tailP hring hned hq hr
  rw [runLCM_true env hpd] at hp
  have hfit : ∀ s, Img lib P fb s → SkaModel.Fits b.less s := fun s ⟨x, gul, hx, hm⟩ => hAp x gul s hx hm
  obtain ⟨Rq, l1, l2⟩ := treeX_run (S := S) lib (P := Img lib P fb) hNf hNt hfit b0 d0 hu hcb ha ht
  have e3 : entries (ofSure (lazyReg gA.re : Sure S)) = [] := entries_ofSure _
  have dT : gT.drop = false := Rq.ext.2.2.1.trans d0
  obtain ⟨⟨Qh, Rp⟩, hne, -, hfl, hec⟩ := Sp.run (sup := sup) (region := region)
    (L := ofSure (lazyReg gA.re)) (th := jmp0 o') hcount (by have := Rq.ext.2.1; omega) dT (Rq.grow.up hu)
    (Clear.growU hcl Rq.grow) (Rq.cfr.below hcb) Rq.lo Rq.hi rfl (by rw [e3]; simp) trivial
    (fun x hx => by
      simp only [ofSure, sure_mk, lazyReg, NMem] at hx; subst hx
      exact ⟨l2, Rq.ncond _ (by simp [ofSure, lazyReg, NMem])⟩)
    (fun e he => by rw [e3] at he; cases he) (by rw [e3]; simp) (fun e he => by rw [e3] at he; cases he)
    (flat_ofSure _) trivial (fun e he => by rw [e3] at he; cases he) hp
  have cS := Sp.clean (L := ofSure (lazyReg gA.re)) trivial hp
  have d5 : g5.drop = false := Rp.drop.trans dT
  have Rp' := Rp.toRunOKLB.copyBunt (Rq.grow.up hu) d5 rfl (fun e he => by rw [e3] at he; cases he) hc
  have R := runOKGB_sevenL (minkC7_direct lib P fb fq b.fol hq1 hq2) Rq Rp' (fun r hr => hr.elim)
  have labS : ∀ e ∈ entries nexS.laz, e.1 < g5.bo := fun e he => by
    rcases (Rp.labs e he).1 with h | h
    · rw [e3] at h; cases h
    · exact h.2
  obtain ⟨rfl, -, -, -, -, -⟩ := copyL_bunt d5 hc
  rcases nexS with ⟨⟨s1, f1, b1⟩, th1⟩
  exact ⟨R, fun hm => by
    obtain ⟨e, he, ee⟩ := List.mem_map.mp hm
    have := labS e he; simp only [jmp0] at ee; omega, ⟨hfl.1, hfl.2⟩, cS, hec⟩

/-! ## The top -/

/-- **The direct call `[2 p q b]` at the top meets both halves of the
contract** on the real whole-subject code (`finishLUCM`), with `p` meeting
`LOKS false` (track C's class) and `q` skipped and returning the callee's
formula; no hypothesis about the run. -/
theorem finishLUCM_contractTailP (lib : Lib) {env : CallEnv} {P : Noun → Prop} {p q : Nomm} {fb fq : Noun}
    {b : Bell} {N : Needs} {bNed ndT : NeedOrd} (hring : env.ring b = Option.none) (hned : env.need b = some bNed)
    (hNf : N b false = some bNed) (hNt : N b true = some ndT)
    (Sp : LOKS (S := S) (Map := Map) false lib N env P fb p) (hpd : p.noDirect = true) (hcount : sixCount p ≤ 255)
    (hq : safeFolFol q = true)
    (hAp : ∀ x gul y, P x → Mink lib gul [] x fb (Tone.zero y) → SkaModel.Fits b.less y)
    (hq1 : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {rc : Tone}, P s → minkF lib gul n tm s fq = some rc →
      rc = Tone.zero b.fol)
    (hq2 : ∀ {s gul : Noun} {tm : Trace}, P s → Mink lib gul tm s fq (Tone.zero b.fol))
    {c : Straight Map} (hc : finishLUCM (S := S) env (Nomm.n2 p q (some (b, Option.none))) = some c) :
    c.need = NeedOrd.this ∧
      ∀ s, P s → ContractFwd lib N s (n3 (A 2) fb fq) [s] c ∧ ContractBwd lib N s (n3 (A 2) fb fq) [s] c :=
  finishLUCM_contractGB lib N (fun hr => (tailP_done lib hring hned hNf hNt Sp hpd hcount hq hAp hq1 hq2
    (by simp [gen0]) rfl upBelow_gen0 clear_gen0 condBelow_gen0 hr).run) hc

/-- **The bell contract of the direct call `[2 p [1 k] b]` with `p` in
`CallTreeA` at index `true`** (which holds `CallTree7`, `CallTree` and
`TopTree`): the code `finishLUCM` makes for a bell `bl` whose formula is
`[2 fb [1 k]]` meets `BellContract`, given the two facts `Annot.direct`
gives on the subjects that fit `bl`. -/
theorem finishLUCM_bellContractTailP {lib : Lib} {bl b : Bell} {fb k : Noun} {p : Nomm}
    (hpA : CallTreeA true fb p) (hf : bl.fol = n3 (A 2) fb (C (A 1) k))
    {env : CallEnv} {N : Needs} {bNed ndT : NeedOrd} (hring : env.ring b = Option.none)
    (hned : env.need b = some bNed) (hNf : N b false = some bNed) (hNt : N b true = some ndT)
    (hAp : ∀ x gul y, SkaModel.Fits bl.less x → Mink lib gul [] x fb (Tone.zero y) → SkaModel.Fits b.less y)
    (hAq : ∀ x gul g, SkaModel.Fits bl.less x → Mink lib gul [] x (C (A 1) k) (Tone.zero g) → g = b.fol)
    {cd : Straight Map} (hc : finishLUCM (S := S) env (Nomm.n2 p (Nomm.n1 k) (some (b, Option.none))) = some cd) :
    cd.need = NeedOrd.this ∧ BellContract lib N bl true cd := by
  have hk : ∀ s, SkaModel.Fits bl.less s → k = b.fol := fun s hs => hAq s s k hs quote_hq2
  have H := finishLUCM_contractTailP (S := S) lib (P := SkaModel.Fits bl.less) (fq := C (A 1) k) hring hned hNf
    hNt ((lokS_callTreeA (S := S) (Map := Map) lib (N := N) env hpA (SkaModel.Fits bl.less)).2 rfl).1
    hpA.noDirect (by rw [hpA.sixCount]; omega) rfl hAp
    (fun {s gul n tm rc} hs h => by rw [quote_hq1 h, hk s hs])
    (fun {s gul tm} hs => by rw [← hk s hs]; exact quote_hq2) hc
  refine ⟨H.1, fun s hs args hargs => ?_⟩
  simp only [if_true, Option.some.injEq] at hargs
  subst hargs
  rw [hf]
  exact H.2 s hs

/-- **Instance: `p` a cons.**  The direct call `[2 [[0 a] [0 a']] [1 k] b]`
at the top: the whole-subject code meets both halves of the contract for
`[2 [[0 a] [0 a']] [1 k]]`, with the hypotheses only on the needs and the
facts of `Annot.direct`. -/
theorem consTail_contract (lib : Lib) {env : CallEnv} {P : Noun → Prop} {a a' : Nat} {k : Noun} {b : Bell}
    {N : Needs} {bNed ndT : NeedOrd} (hring : env.ring b = Option.none) (hned : env.need b = some bNed)
    (hNf : N b false = some bNed) (hNt : N b true = some ndT)
    (hAp : ∀ x gul y, P x → Mink lib gul [] x (C (slot a) (slot a')) (Tone.zero y) → SkaModel.Fits b.less y)
    (hAq : ∀ x gul g, P x → Mink lib gul [] x (C (A 1) k) (Tone.zero g) → g = b.fol)
    {c : Straight Map}
    (hc : finishLUCM (S := S) env (Nomm.n2 (Nomm.cons (Nomm.n0 a) (Nomm.n0 a')) (Nomm.n1 k) (some (b, Option.none))) =
      some c) :
    c.need = NeedOrd.this ∧ ∀ s, P s →
      ContractFwd lib N s (n3 (A 2) (C (slot a) (slot a')) (C (A 1) k)) [s] c ∧
      ContractBwd lib N s (n3 (A 2) (C (slot a) (slot a')) (C (A 1) k)) [s] c := by
  have hpA : CallTree7 (C (slot a) (slot a')) (Nomm.cons (Nomm.n0 a) (Nomm.n0 a')) :=
    CallTree7.cons (CallTree7.n0 a) (CallTree7.n0 a')
  have hk : ∀ s, P s → k = b.fol := fun s hs => hAq s s k hs quote_hq2
  exact finishLUCM_contractTailP (S := S) lib (fq := C (A 1) k) hring hned hNf hNt
    ((lokS_callTree7 (S := S) (Map := Map) lib (N := N) env hpA P).1) hpA.noDirect (by rw [hpA.sixCount]; omega)
    rfl hAp (fun {s gul n tm rc} hs h => by rw [quote_hq1 h, hk s hs])
    (fun {s gul tm} hs => by rw [← hk s hs]; exact quote_hq2) hc

end Comp
end SkaModel
end Formalization
