import lemmas.Ska.CompDirectMCalK
import lemmas.Ska.CompDirectMTailP

/-!
# The direct call under `%next` with `mono` `&`: `callLBM`

README Gaps 18.13 (track J, 2026-11-27).  The whole-subject version of a
direct call `[2 p q b]` under `%next L th` (`monoBlocks`, the `%cal` form):
from the state `g0` before `+need-ord-alloc-regs`,

* the callee's registers `sub` (`g0.re` to `k`), `+kerf` from
  `{g0 with re := k}` (`out`, `pro = k`), the registers `merged`, `sub-pes`,
  the merge block `[~[merged] [mov merged pro] hop out]`, `pro-opt`,
  `pro-pes`, the blocks `opt` `[cal b subV pro-opt] hop [pro-opt] merge` and
  `pes` `[csl b sub-pes pro-pes] hop [pro-pes] merge`, the tree of
  `+mono-try-call`, `p` under `%next (lazy-from-reg sub-pes) (jmp0 tree)`,
  `+copy` into the need that asks nothing.

The proof reads the call as `[7 p [2 [0 1] [1 b.fol]]]` (`minkC7_direct`)
under `%next (lazy-from-reg pro) (jmp0 out)`, then lifts it through `+kerf`:

* `callOut_goal`: a call block's step (`optStep_*`, `pesStep_*`) meets
  `GoalSemCM` of `%next (lazy-from-reg pro) (jmp0 out)`.
* `treeN_run`: the merge block, the two call blocks and the tree meet
  `RunOKGB` under that goal from the state after `+kerf` with its registers
  lowered to `g0.re` (the tree writes `sub`, which lies below `+kerf`).
* `runLCM_cal`: the run, step by step.
* `callLBM_run`: `RunOKLS` of the whole case under `%next L th` from `g0`
  (`runOKGB_sevenLW`, `kerfLBM`), and the facts `LOKS.run` asks of a
  result.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

section
variable {lib : Lib} {σ : Type} {Inv : σ → Prop} {ν : σ → Needs} {O : Oracle σ} {c : Straight Map} {gul : Noun}

/-- **A call block's step meets the goal `%next (lazy-from-reg pro) (jmp0
out)`**: the step stores the product in `a`, `merged` and `pro` and goes to
`out`, or returns the callee's `%1` / `%2`. -/
theorem callOut_goal {K : Nat → Prop} {pro out merged a : Nat} {st st' : σ} {regs R : Map (Option Noun)}
    {t tm : Trace} {je : Jmp} {ton r : Tone} (hI' : Inv st') (hle : ν st ≤ ν st')
    (E : goJ lib O c gul st regs t je = (match ton with
         | Tone.zero p => goJ lib O c gul st' (store pro p (store merged p (store a p R))) t (jmp0 out)
         | ton => some (ton, st')))
    (hrel : ToneRel lib (ν st') ton r) (htr : Forall2 (FrameRel lib (ν st)) t tm)
    (hk : ∀ x, K x → x ≠ pro ∧ x ≠ merged ∧ x ≠ a ∧ SkaModel.read x R = SkaModel.read x regs) :
    GoalSemCM lib O c gul Inv ν K st regs t tm je (CGoal.next (lazyReg pro : Sure S) (jmp0 out)) r := by
  cases hrel with
  | zero p =>
    exact goalSemCM_step hle (fun z hz => by
        obtain ⟨a1, a2, a3, a4⟩ := hk z hz
        rw [read_store_ne a1, read_store_ne a2, read_store_ne a3, a4]) E _ _
      (outGoal_self (S := S) st' _ t tm p hI' (frames_mono hle htr) (read_store_eq pro p _))
  | one p => exact goalSemCM_ret _ _ (fun _ h => by cases h) ⟨Tone.one p, st', hI', hle, E, ToneRel.one p⟩
  | two hl => exact goalSemCM_ret _ _ (fun _ h => by cases h) ⟨_, st', hI', hle, E, ToneRel.two hl⟩

end

/-! ## The merge block, the call blocks and the tree -/

/-- The state after the merge block and the two call blocks (`monoBlocks`
under `%next`, from the state `g2` after `+kerf`). -/
def callBlocksGen (g2 : Gen Map) (b : Bell) (sub : Need) (pro out : Nat) : Gen Map :=
  (({ ({ g2 with re := g2.re + 2 }.emitted ⟨[g2.re], [Pole.mov g2.re pro], Termin.hop (jmp0 out)⟩) with
      re := g2.re + 4 }.emitted ⟨[], [Pole.cal b (flattenNeed sub) (g2.re + 2)], Termin.hop ⟨[some (g2.re + 2)], g2.bo⟩⟩).emitted
    ⟨[], [Pole.csl b (g2.re + 1) (g2.re + 3)], Termin.hop ⟨[some (g2.re + 3)], g2.bo⟩⟩)

/-- **The merge block, the two call blocks and the tree under `%next
(lazy-from-reg pro) (jmp0 out)` meet `RunOKGB`** with the result
`[lazy-from-reg sub-pes, tree]`, for the tail formula `[2 [0 1] [1 b.fol]]`
on subjects that fit the bell, from the state `g2` after `+kerf` with its
registers lowered to `g0.re`, the state before `+need-ord-alloc-regs`. -/
theorem treeN_run (lib : Lib) {N : Needs} {P : Noun → Prop} {b : Bell} {bNed ndT : NeedOrd}
    (hNf : N b false = some bNed) (hNt : N b true = some ndT) (hfit : ∀ s, P s → SkaModel.Fits b.less s)
    {g0 gA g2 gT : Gen Map} {sub : Need} {o' pro out : Nat}
    (ha : needOrdAllocRegs bNed g0 = some (sub, gA)) (hA2 : gA.re ≤ g2.re)
    (hpro0 : g0.re ≤ pro) (hpro : pro < g2.re) (hout : 1 ≤ out) (hout2 : out < g2.bo)
    (d2 : g2.drop = false) (hu : UpBelow g2) (hcb : CondBelow g2)
    (hcs : ∀ x, NMem sub x → HoonMap.get g2.cond x = Option.none) (hcp : HoonMap.get g2.cond pro = Option.none)
    (ht : monoTryLoop (g2.bo + 2) sub (g2.re + 1) (g2.bo + 1) (callBlocksGen g2 b sub pro out) = some (o', gT)) :
    RunOKGB lib N P (tailFol b.fol) (CGoal.next (lazyReg pro : Sure S) (jmp0 out)) ({ g2 with re := g0.re } : Gen Map)
      gT ⟨ofSure (lazyReg (g2.re + 1)), jmp0 o'⟩ ∧ g2.re + 4 ≤ gT.re ∧ gT.cond = g2.cond ∧ g2.bo + 3 ≤ gT.bo := by
  obtain ⟨⟨kA, rfl⟩, la, dA, ma⟩ := needOrdAllocRegs_spec bNed _ _ _ ha
  simp only at la ma hA2
  have qre : (callBlocksGen g2 b sub pro out).re = g2.re + 4 := rfl
  have qbo : (callBlocksGen g2 b sub pro out).bo = g2.bo + 3 := rfl
  have qdr : (callBlocksGen g2 b sub pro out).drop = false := d2
  have qcn : (callBlocksGen g2 b sub pro out).cond = g2.cond := rfl
  have qb : ∀ x, HoonMap.get (callBlocksGen g2 b sub pro out).blocks x =
      if x = g2.bo + 2 then some ⟨[], [Pole.csl b (g2.re + 1) (g2.re + 3)], Termin.hop ⟨[some (g2.re + 3)], g2.bo⟩⟩ else
      if x = g2.bo + 1 then some ⟨[], [Pole.cal b (flattenNeed sub) (g2.re + 2)], Termin.hop ⟨[some (g2.re + 2)], g2.bo⟩⟩
      else if x = g2.bo then some ⟨[g2.re], [Pole.mov g2.re pro], Termin.hop (jmp0 out)⟩ else
      HoonMap.get g2.blocks x := by
    intro x; simp [callBlocksGen, Gen.emitted, d2, HoonMap.get_put]
  have GQ : Grow g2 (callBlocksGen g2 b sub pro out) :=
    (grow_reg g2 (g2.re + 2)).trans ((grow_emit (fun j hj => by
      simp [finJumps] at hj; subst hj; simp only [jmp0]; omega)).trans ((grow_reg _ (g2.re + 4)).trans
      ((grow_emit (fun j hj => by simp [finJumps] at hj; subst hj; simp only [emitted_bo]; omega)).trans
      (grow_emit (fun j hj => by simp [finJumps] at hj; subst hj; simp only [emitted_bo]; omega)))))
  generalize callBlocksGen g2 b sub pro out = gQ at qre qbo qdr qcn qb GQ ht
  obtain ⟨GT, CT, lo', hi', UT⟩ := monoTryLoop_ok _ _ _ _ _ _ ht qdr (by omega) (by omega) (by omega) (by omega)
  obtain ⟨dT, rT, bT, kT⟩ := monoTryLoop_mono _ _ _ _ _ _ ht
  have root := monoTryLoop_root _ _ _ ht qdr
  have e0 : entries (ofSure (lazyReg (g2.re + 1) : Sure S)) = [] := entries_ofSure _
  have gTc : gT.cond = g2.cond := by rw [CT, qcn]
  have hl : ∀ x, x < g2.bo → HoonMap.get gT.blocks x = HoonMap.get g2.blocks x := by
    intro x hx
    rw [kT x (by omega), qb, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have ent : ∃ bk, HoonMap.get gT.blocks o' = some bk ∧ bk.par = [] := by
    rcases root with ⟨rfl, rfl⟩ | h
    · exact ⟨_, by rw [qb, if_neg (by omega), if_pos rfl], rfl⟩
    · exact h
  obtain ⟨bk, hbk, hpar⟩ := ent
  -- the blocks of the code, unproxied
  have blocks : ∀ (cf : Map (Nat × List Nat)), (∀ x, x < gT.re → HoonMap.get cf x = HoonMap.get gT.cond x) →
      ∀ (c : Straight Map), (∀ o, g2.bo ≤ o → o < gT.bo →
        HoonMap.get c.blocks o = (HoonMap.get gT.blocks o).map (unproxyBlob cf)) →
      HoonMap.get c.blocks g2.bo = some ⟨[g2.re], [Pole.mov g2.re pro], Termin.hop (jmp0 out)⟩ ∧
      HoonMap.get c.blocks (g2.bo + 1) =
        some ⟨[], [Pole.cal b (flattenNeed sub) (g2.re + 2)], Termin.hop ⟨[some (g2.re + 2)], g2.bo⟩⟩ ∧
      HoonMap.get c.blocks (g2.bo + 2) =
        some ⟨[], [Pole.csl b (g2.re + 1) (g2.re + 3)], Termin.hop ⟨[some (g2.re + 3)], g2.bo⟩⟩ ∧
      ∀ x, gQ.bo ≤ x → x < gT.bo → HoonMap.get c.blocks x = HoonMap.get gT.blocks x := by
    intro cf hcf c ag
    have hu' : ∀ x, g2.re ≤ x → x < gT.re → unproxy cf x = x := fun x h1 h2 =>
      unproxy_none (by rw [hcf x h2, gTc]; exact condBelow_none hcb h1)
    have hsub : ∀ x, NMem sub x → unproxy cf x = x := fun x hx =>
      unproxy_none (by rw [hcf x (by have := (ma x hx).2; omega), gTc]; exact hcs x hx)
    have hp : unproxy cf pro = pro := unproxy_none (by rw [hcf pro (by omega), gTc]; exact hcp)
    refine ⟨?_, ?_, ?_, fun x h1 h2 => ?_⟩
    · rw [ag _ (Nat.le_refl _) (by omega), kT _ (by omega), qb, if_neg (by omega), if_neg (by omega), if_pos rfl]
      simp [unproxyBlob, renBlob, renFin, renJmp, renPole, jmp0, hp, hu' g2.re (Nat.le_refl _) (by omega)]
    · rw [ag _ (by omega) (by omega), kT _ (by omega), qb, if_neg (by omega), if_pos rfl]
      simp only [Option.map_some, unproxyBlob, renBlob, renFin, renJmp, List.map_nil, List.map_cons, renPole,
        Option.map_some, hu' (g2.re + 2) (by omega) (by omega)]
      rw [List.map_congr_left (g := id) (fun x hx => hsub x ((mem_flatten sub x).mp hx)), List.map_id]
    · rw [ag _ (by omega) (by omega), kT _ (by omega), qb, if_pos rfl]
      simp [unproxyBlob, renBlob, renFin, renJmp, renPole, hu' (g2.re + 1) (by omega) (by omega),
        hu' (g2.re + 3) (by omega) (by omega)]
    · rw [ag _ (by omega) (by omega)]
      exact UT (unproxy cf) (hu' _ (by omega) (by omega)) hsub (fun y a b => hu' y (by omega) (by omega)) x h1 h2
  have GU := (GQ.trans GT).toU hu
  -- the registers the goal keeps
  have hK : ∀ (ned : Need), (∀ x, NMem ned x → gT.re ≤ x) → ∀ (regs regs' : Map (Option Noun)),
      (∀ x, (x < gQ.re ∨ gT.re ≤ x) → ¬ NMem sub x → SkaModel.read x regs' = SkaModel.read x regs) →
      ∀ (a : Nat), g2.re ≤ a → a < g2.re + 4 → ∀ x,
      ((x < ({ g2 with re := g0.re } : Gen Map).re ∨ NMem ned x) ∧
        ¬ GMem (CGoal.next (lazyReg pro : Sure S) (jmp0 out)) x) →
      x ≠ pro ∧ x ≠ g2.re ∧ x ≠ a ∧ SkaModel.read x regs' = SkaModel.read x regs := by
    intro ned hned regs regs' keep a a1 a2 x ⟨x1, x2⟩
    simp only [GMem, lazyReg, NMem] at x1 x2
    rcases x1 with h | h
    · exact ⟨x2, by omega, by omega, keep x (Or.inl (by omega)) (fun hm => by have := (ma x hm).1; omega)⟩
    · have := hned x h
      exact ⟨x2, by omega, by omega, keep x (Or.inr this) (fun hm => by have := (ma x hm).2; omega)⟩
  refine ⟨⟨⟨by simp only; omega, by simp only; omega, by simp only; rw [dT, qdr, d2], fun o ho => hl o ho⟩,
    ⟨GU.bo, GU.drop, GU.keep, GU.new⟩, condFresh_of_eq (by simp only; omega) gTc,
    (by simp only [jmp0]; omega), (by simp only [jmp0]; omega), Or.inl ⟨bk, hbk, hpar, rfl⟩,
    fun r hr => Or.inr (by simp only [ofSure, sure_mk, lazyReg, NMem] at hr; subst hr; simp only; omega), trivial,
    fun e he => (by rw [e0] at he; cases he), fun e he => (by rw [e0] at he; cases he), (by rw [e0]; simp),
    fun s hs hf => absurd (fitsS_lazyReg _ s) hf,
    fun r hr => (by simp only [ofSure, sure_mk, lazyReg, NMem] at hr; subst hr; rw [gTc]; exact condBelow_none hcb (by omega)),
    fun e he => (by rw [e0] at he; cases he), ?_, ?_⟩, by omega, gTc, by omega⟩
  · -- forward
    intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    obtain ⟨Bm, Bo, Bp, Bt⟩ := blocks cf hcf c (fun o h1 h2 => (ag st).1 o h1 h2 (by rw [e0]; simp))
    have hv : SkaModel.read (g2.re + 1) regs = some s := hh.1
    obtain ⟨regs', keep, res⟩ := monoTry_goW (lib := lib) (O := O) (c := c) (gul := gul) (st := st)
      sub (g2.re + 1) (g2.bo + 1) gQ gT o' ht qdr Bt (nDist_of_distinct dA)
      (fun x hx => by have := (ma x hx).2; omega) (by omega) (fun hx => by have := (ma _ hx).2; omega) regs t s hv
    obtain ⟨j, hj, hm'⟩ := minkF_tail hm
    rcases res with ⟨fit, hold, e2⟩ | ⟨nfit, e2⟩
    · obtain ⟨ton, st', hI', hle, hrel, E⟩ := optStep_fwd hS hF hNf ha Bo Bm (by omega) hI (hN st hI) hold
        (hfit s hs) htr hj hm'
      exact callOut_goal hI' hle (e2.trans E) hrel htr (hK ned hned regs regs' keep (g2.re + 2) (by omega) (by omega))
    · have hv' : SkaModel.read (g2.re + 1) regs' = some s := by
        rw [keep _ (Or.inl (by omega)) (fun hx => by have := (ma _ hx).2; omega)]; exact hv
      obtain ⟨ton, st', hI', hle, hrel, E⟩ := pesStep_fwd hS hF hNt Bp Bm (by omega) hI (hN st hI) hv'
        (hfit s hs) htr hj hm'
      exact callOut_goal hI' hle (e2.trans E) hrel htr (hK ned hned regs regs' keep (g2.re + 3) (by omega) (by omega))
  · -- backward
    intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨Bm, Bo, Bp, Bt⟩ := blocks cf hcf c (fun o h1 h2 => (ag st).1 o h1 h2 (by rw [e0]; simp))
    have hv : SkaModel.read (g2.re + 1) regs = some s := hh.1
    obtain ⟨regs', keep, res'⟩ := monoTry_goW (lib := lib) (O := O) (c := c) (gul := gul) (st := st)
      sub (g2.re + 1) (g2.bo + 1) gQ gT o' ht qdr Bt (nDist_of_distinct dA)
      (fun x hx => by have := (ma x hx).2; omega) (by omega) (fun hx => by have := (ma _ hx).2; omega) regs t s hv
    rcases res' with ⟨fit, hold, e2⟩ | ⟨nfit, e2⟩
    · rw [e2] at hres
      obtain ⟨r, ton, st', hmk, hI', hle, hrel, E⟩ := optStep_bwd hS hB hNf ha Bo Bm (by omega) hI (hN st hI) hold
        (hfit s hs) htr hres
      exact ⟨r, mink_tail_bwd hmk, callOut_goal hI' hle (e2.trans E) hrel htr
        (hK ned hned regs regs' keep (g2.re + 2) (by omega) (by omega))⟩
    · have hv' : SkaModel.read (g2.re + 1) regs' = some s := by
        rw [keep _ (Or.inl (by omega)) (fun hx => by have := (ma _ hx).2; omega)]; exact hv
      rw [e2] at hres
      obtain ⟨r, ton, st', hmk, hI', hle, hrel, E⟩ := pesStep_bwd hS hB hNt Bp Bm (by omega) hI (hN st hI) hv'
        (hfit s hs) htr hres
      exact ⟨r, mink_tail_bwd hmk, callOut_goal hI' hle (e2.trans E) hrel htr
        (hK ned hned regs regs' keep (g2.re + 3) (by omega) (by omega))⟩

end Comp
end SkaModel
end Formalization
