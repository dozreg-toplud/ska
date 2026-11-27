import lemmas.Ska.CompNaryTopDirect
import lemmas.Ska.CompDirectMCal

/-!
# The n-ary direct call under `%next`: the `%cal` form

README Gaps 18.15 (c), its `%cal` half.  In the n-ary code (`runLC`, `mono`
`|`, the case `callL`), a direct call `[2 p q b]` under a goal `%next L th`
allocates the callee's registers `sub` from the state `g0`, runs `+kerf` of
`[L th]` from the state after them (`out`, `pro`), emits `[cal b sub pro] hop
out`, and runs `p` under `%next (ofSure sub) (jmp0 that block)`.  The shape
was checked first (`CompNaryTopCalEx.lean`).

* `callOutN_goal`: the call block's step meets `GoalSemCM` of `%next
  (lazy-from-reg pro) (jmp0 out)` (`callOut_goal` without the merge).
* `callN_run`: the block meets `RunOKGB` under that goal, for `[2 [0 1] [1
  b.fol]]` on subjects that fit the bell and split by its need, from the
  state after `+kerf` with its registers lowered to `g0.re`
  (`callStep_fwd`, `callStep_bwd`; `nec` from the split, as `jmpN_run`).
* `runLC_cal`: the run, step by step.
* `callLBN_run`: `RunOKLS` of the whole case under `%next L th` from `g0`
  (`runOKGB_sevenLW`, `kerfLBM`), and the facts `LOKS.run` asks of a result,
  for `p` meeting `LOKS false`; `lokS_directN`: the direct call meets `LOKS
  false`, under `SplitsLess`.
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

/-- **The call block's step meets the goal `%next (lazy-from-reg pro) (jmp0
out)`**: the step stores the product in `pro` and goes to `out`, or returns
the callee's `%1` / `%2`. -/
theorem callOutN_goal {K : Nat → Prop} {pro out : Nat} {st st' : σ} {regs : Map (Option Noun)}
    {t tm : Trace} {je : Jmp} {ton r : Tone} (hI' : Inv st') (hle : ν st ≤ ν st')
    (E : goJ lib O c gul st regs t je = (match ton with
         | Tone.zero p => goJ lib O c gul st' (store pro p regs) t (jmp0 out)
         | ton => some (ton, st')))
    (hrel : ToneRel lib (ν st') ton r) (htr : Forall2 (FrameRel lib (ν st)) t tm)
    (hk : ∀ x, K x → x ≠ pro) :
    GoalSemCM lib O c gul Inv ν K st regs t tm je (CGoal.next (lazyReg pro : Sure S) (jmp0 out)) r := by
  cases hrel with
  | zero p =>
    exact goalSemCM_step hle (fun z hz => by rw [read_store_ne (hk z hz)]) E _ _
      (outGoal_self (S := S) st' _ t tm p hI' (frames_mono hle htr) (read_store_eq pro p _))
  | one p => exact goalSemCM_ret _ _ (fun _ h => by cases h) ⟨Tone.one p, st', hI', hle, E, ToneRel.one p⟩
  | two hl => exact goalSemCM_ret _ _ (fun _ h => by cases h) ⟨_, st', hI', hle, E, ToneRel.two hl⟩

end

/-- **The block `[cal b sub pro] hop out` under `%next (lazy-from-reg pro)
(jmp0 out)` meets `RunOKGB`** with the result `[ofSure sub, jmp0 block]`,
for the tail formula `[2 [0 1] [1 b.fol]]` on subjects that fit the bell and
split by its need, from the state `g2` after `+kerf` with its registers
lowered to `g0.re`, the state before `+need-ord-alloc-regs`. -/
theorem callN_run (lib : Lib) {N : Needs} {P : Noun → Prop} {b : Bell} {bNed : NeedOrd}
    (hNf : N b false = some bNed) (hfit : ∀ s, P s → SkaModel.Fits b.less s)
    (hspl : ∀ s, P s → ∃ vs, SkaModel.split bNed s = some vs)
    {g0 gA g2 : Gen Map} {sub : Need} {pro out : Nat}
    (ha : needOrdAllocRegs bNed g0 = some (sub, gA)) (hA2 : gA.re ≤ g2.re)
    (hpro0 : g0.re ≤ pro) (hpro : pro < g2.re) (hout : 1 ≤ out) (hout2 : out < g2.bo) (b2 : 1 ≤ g2.bo)
    (d2 : g2.drop = false) (hu : UpBelow g2)
    (hcs : ∀ x, NMem sub x → HoonMap.get g2.cond x = Option.none) (hcp : HoonMap.get g2.cond pro = Option.none) :
    RunOKGB lib N P (tailFol b.fol) (CGoal.next (lazyReg pro : Sure S) (jmp0 out)) ({ g2 with re := g0.re } : Gen Map)
      (g2.emitted ⟨[], [Pole.cal b (flattenNeed sub) pro], Termin.hop (jmp0 out)⟩)
      ⟨ofSure ⟨sub, HoonSet.empty⟩, jmp0 g2.bo⟩ := by
  have hsub := fits_of_split bNed g0 gA sub ha
  obtain ⟨⟨kA, rfl⟩, la, dA, ma⟩ := needOrdAllocRegs_spec bNed _ _ _ ha
  simp only at la ma hA2
  have qb : ∀ x, HoonMap.get (g2.emitted ⟨[], [Pole.cal b (flattenNeed sub) pro], Termin.hop (jmp0 out)⟩).blocks x =
      if x = g2.bo then some ⟨[], [Pole.cal b (flattenNeed sub) pro], Termin.hop (jmp0 out)⟩
      else HoonMap.get g2.blocks x := by
    intro x; simp [Gen.emitted, d2, HoonMap.get_put]
  have GQ : Grow g2 (g2.emitted ⟨[], [Pole.cal b (flattenNeed sub) pro], Termin.hop (jmp0 out)⟩) :=
    grow_emit (fun j hj => by simp [finJumps] at hj; subst hj; simp only [jmp0]; omega)
  have GU := GQ.toU hu
  have e0 : entries (ofSure ⟨sub, HoonSet.empty⟩ : Lazy S) = [] := entries_ofSure _
  have hl : ∀ x, x < g2.bo → HoonMap.get (g2.emitted
      ⟨[], [Pole.cal b (flattenNeed sub) pro], Termin.hop (jmp0 out)⟩).blocks x = HoonMap.get g2.blocks x := by
    intro x hx; rw [qb, if_neg (by omega)]
  have ofs : (ofSure (⟨sub, HoonSet.empty⟩ : Sure S)).sure = ⟨sub, HoonSet.empty⟩ := by simp [ofSure, sure_mk]
  have qc : (g2.emitted ⟨[], [Pole.cal b (flattenNeed sub) pro], Termin.hop (jmp0 out)⟩).cond = g2.cond := by
    simp only [Gen.emitted, d2]
  -- the block of the code, unproxied
  have blocks : ∀ (cf : Map (Nat × List Nat)), (∀ x, x < g2.re → HoonMap.get cf x = HoonMap.get g2.cond x) →
      ∀ (c : Straight Map), (∀ o, g2.bo ≤ o → o < g2.bo + 1 →
        HoonMap.get c.blocks o = (HoonMap.get (g2.emitted
          ⟨[], [Pole.cal b (flattenNeed sub) pro], Termin.hop (jmp0 out)⟩).blocks o).map (unproxyBlob cf)) →
      HoonMap.get c.blocks g2.bo = some ⟨[], [Pole.cal b (flattenNeed sub) pro], Termin.hop (jmp0 out)⟩ := by
    intro cf hcf c ag
    have hs : ∀ x, NMem sub x → unproxy cf x = x := fun x hx =>
      unproxy_none (by rw [hcf x (by have := (ma x hx).2; omega)]; exact hcs x hx)
    have hp : unproxy cf pro = pro := unproxy_none (by rw [hcf pro hpro]; exact hcp)
    rw [ag _ (Nat.le_refl _) (by omega), qb, if_pos rfl]
    simp only [Option.map_some, unproxyBlob, renBlob, renFin, renJmp, List.map_nil, List.map_cons, renPole, hp, jmp0]
    rw [List.map_congr_left (g := id) (fun x hx => hs x ((mem_flatten sub x).mp hx)), List.map_id]
  refine ⟨⟨by simp only [Gen.emitted]; omega, by simp only [Gen.emitted]; omega, by simp only [Gen.emitted], hl⟩,
    ⟨GU.bo, GU.drop, GU.keep, GU.new⟩, condFresh_of_eq (by simp only [Gen.emitted]; omega) qc,
    (by simp only [jmp0]; omega), (by simp only [jmp0, Gen.emitted]; omega),
    Or.inl ⟨_, (qb _).trans (if_pos rfl), rfl, rfl⟩,
    fun r hr => Or.inr (by rw [ofs] at hr; have := ma r hr; simp only [Gen.emitted]; omega), (by rw [ofs]; exact dA),
    fun e he => (by rw [e0] at he; cases he), fun e he => (by rw [e0] at he; cases he), (by rw [e0]; simp),
    fun s hs hf => absurd (by
      rw [ofs]
      obtain ⟨vs, hv⟩ := hspl s hs
      exact ⟨hsub s vs hv, looks_empty _⟩) hf,
    fun r hr => (by rw [ofs] at hr; rw [qc]; exact hcs r hr),
    fun e he => (by rw [e0] at he; cases he), ?_, ?_⟩
  · -- forward
    intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    have Bo := blocks cf (fun x hx => by rw [hcf x (by simp only [Gen.emitted]; omega), qc]) c
      (fun o h1 h2 => (ag st).1 o h1 (by simp only [Gen.emitted]; omega) (by rw [e0]; simp))
    have hold : HoldsN sub regs s := by have := hh.1; rwa [ofs] at this
    obtain ⟨j, hj, hm'⟩ := minkF_tail hm
    obtain ⟨ton, st', hI', hle, hrel, E⟩ := callStep_fwd hS hF hNf ha Bo hI (hN st hI) hold (hfit s hs) htr hj hm'
    exact callOutN_goal hI' hle E hrel htr (fun x hx => by
      have := hx.2; simp only [GMem, lazyReg, NMem] at this; exact this)
  · -- backward
    intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    have Bo := blocks cf (fun x hx => by rw [hcf x (by simp only [Gen.emitted]; omega), qc]) c
      (fun o h1 h2 => (ag st).1 o h1 (by simp only [Gen.emitted]; omega) (by rw [e0]; simp))
    have hold : HoldsN sub regs s := by have := hh.1; rwa [ofs] at this
    obtain ⟨r, ton, st', hmk, hI', hle, hrel, E⟩ := callStep_bwd hS hB hNf ha Bo hI (hN st hI) hold (hfit s hs) htr hres
    exact ⟨r, mink_tail_bwd hmk, callOutN_goal hI' hle E hrel htr (fun x hx => by
      have := hx.2; simp only [GMem, lazyReg, NMem] at this; exact this)⟩

/-- **The run of the n-ary direct call under `%next L th`, `q` skipped, not
dropped**: the callee's registers, `+kerf`, the block `[cal b sub pro] hop
out`, `p` under `%next (ofSure sub) (jmp0 block)`, `+copy` into the need
that asks nothing. -/
theorem runLC_cal {env : CallEnv} {sup : Option Nomm} {p q : Nomm} {b : Bell} {bNed : NeedOrd} {L : Lazy S}
    {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (hring : env.ring b = Option.none) (hned : env.need b = some bNed)
    (hsof : env.sof (made p sup) p q b bNed = false) (hq : safeFolFol q = true)
    (hpure : (env.pure b && noneEquivalentL L) = false)
    (h : runLC env sup (Nomm.n2 p q (some (b, Option.none))) (CGoalL.next L th) region g0 = some (nex, g1)) :
    ∃ sub gA out pro g2 nexS g5, needOrdAllocRegs bNed g0 = some (sub, gA) ∧
      kerf (⟨L, th⟩ : NextL S) gA = some ((out, pro), g2) ∧
      runLC env sup p (CGoalL.next (ofSure ⟨sub, HoonSet.empty⟩) (jmp0 g2.bo)) region
        (g2.emitted ⟨[], [Pole.cal b (flattenNeed sub) pro], Termin.hop (jmp0 out)⟩) = some (nexS, g5) ∧
      copyL nexS (ofSure Sure.bunt) g5 = some (nex, g1) := by
  simp only [runLC, callL, hring, hned, hsof, hq, hpure, Bool.false_eq_true, if_false, if_true] at h
  obtain ⟨sub, gA, ha, h⟩ := bind_some h
  obtain ⟨o, g3, hc, h⟩ := bind_some h
  simp only [simpleNextL, bind_apply, pure_apply, Option.bind_some] at hc
  obtain ⟨⟨⟨out, pro⟩, g2⟩, hk, hc⟩ := Option.bind_eq_some_iff.mp hc
  rw [emit_apply] at hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [pure_apply, bind_apply, Option.bind_some] at h
  rw [pastL_bunt] at h
  simp only [pure_apply, Option.bind_some] at h
  obtain ⟨⟨nexS, g5⟩, hp, hc⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨sub, gA, out, pro, g2, nexS, g5, ha, hk, hp, hc⟩

/-- **The n-ary direct call `[2 p q b]` under a flat lazy goal** (the `%cal`
form), from a state as `LOKS.run` asks: `RunOKLS` with the witness `kernWit
re` of `+kerf`, the jump a new block at none of the result's entries, the
result flat with clean entries.  `p` meets `LOKS false`, `q` is skipped and
returns the callee's formula (and nothing else) on the subjects, the
products of `p` fit the bell, the need read is `N b false`, the call is not
soft and not dropped, and every noun that fits the bell splits by its need
(`SplitsLess`). -/
theorem callLBN_run (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {p q : Nomm} {fb fq : Noun}
    {b : Bell} {bNed : NeedOrd} (hring : env.ring b = Option.none) (hned : env.need b = some bNed)
    (hsof : ∀ m, env.sof m p q b bNed = false) (hNf : N b false = some bNed) (hspl : SplitsLess b bNed)
    (Sp : LOKS (S := S) (Map := Map) false lib N env P fb p) (hcount : sixCount p ≤ 255)
    (hq : safeFolFol q = true)
    (hAp : ∀ x gul y, P x → Mink lib gul [] x fb (Tone.zero y) → SkaModel.Fits b.less y)
    (hq1 : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {rc : Tone}, P s → minkF lib gul n tm s fq = some rc →
      rc = Tone.zero b.fol)
    (hq2 : ∀ {s gul : Noun} {tm : Trace}, P s → Mink lib gul tm s fq (Tone.zero b.fol))
    {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (hpure : (env.pure b && noneEquivalentL L) = false)
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0)
    (hcl0 : Clear g0) (hcb : CondBelow g0) (h1 : 1 ≤ th.there) (h2 : th.there < g0.bo) (hta : th.args = [])
    (ht : th.there ∉ (entries L).map Prod.fst) (hsd : Distinct L.sure.ned)
    (hsl : ∀ x, NMem L.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none)
    (hlab : ∀ e ∈ entries L, e.1 < g0.bo ∧ ∃ B th', HoonMap.get g0.blocks e.1 = some ⟨[], B, Termin.hop th'⟩)
    (hnd : ((entries L).map Prod.fst).Nodup)
    (hed : ∀ e ∈ entries L, Distinct e.2.sure.ned ∧
      ∀ x, NMem e.2.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none)
    (hfl : Flat L) (hcs : Clean L.sure.ned) (hce : ∀ e ∈ entries L, Clean e.2.sure.ned)
    (hr : runLC env sup (Nomm.n2 p q (some (b, Option.none))) (CGoalL.next L th) region g0 = some (nex, g1)) :
    (∃ Q, RunOKLS (Map := Map) lib N P (n3 (A 2) fb fq) L th Q false g0 g1 nex) ∧
      nex.th.there ∉ (entries nex.laz).map Prod.fst ∧ g0.bo ≤ nex.th.there ∧ Flat nex.laz ∧
      (∀ e ∈ entries nex.laz, Clean e.2.sure.ned) := by
  obtain ⟨sub, gA, out, pro, g2, nexS, g5, ha, hk, hp, hc⟩ := runLC_cal hring hned (hsof _) hq hpure hr
  have cl := needOrdAllocRegs_clean bNed g0 gA sub ha
  obtain ⟨⟨kA, rfl⟩, la, dA, ma⟩ := needOrdAllocRegs_spec bNed _ _ _ ha
  simp only at la ma
  have hcbk : CondBelow ({ g0 with re := kA } : Gen Map) := fun x hx => by
    have := hcb x hx; show x < kA; omega
  have hlab' : ∀ e ∈ entries L, e.1 < g0.bo ∧ ∃ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩ :=
    fun e he => ⟨(hlab e he).1, by obtain ⟨B, th', h⟩ := (hlab e he).2; exact ⟨B, _, h⟩⟩
  obtain ⟨eo, ep, b2, dr2, l2, PF, G2, -, -, -, c0, -⟩ := kerf_specL hk d0 hcbk hu h1 h2 hlab' hnd
  simp only at eo ep b2 dr2 l2 c0
  subst out pro
  have hfit : ∀ s, Img lib P fb s → SkaModel.Fits b.less s := fun s ⟨x, gul, hx, hm⟩ => hAp x gul s hx hm
  have G2' : GrowU g0 g2 := ⟨G2.bo, G2.drop, G2.keep, G2.new⟩
  have hu2 : UpBelow g2 := G2'.up hu
  have hcb2 : CondBelow g2 := PF.1.below hcbk
  have d2 : g2.drop = false := dr2.trans d0
  have hcs2 : ∀ x, NMem sub x → HoonMap.get g2.cond x = Option.none := fun x hx => by
    rw [PF.1.get_lt (show x < kA from (ma x hx).2)]; exact condBelow_none hcb (ma x hx).1
  have Rq := callN_run (S := S) lib (P := Img lib P fb) hNf hfit (fun s hs => hspl s (hfit s hs)) ha
    (by simp only; omega) la (by omega) b0 (by omega) (by omega) d2 hu2 hcs2 c0
  generalize hg3 : g2.emitted ⟨[], [Pole.cal b (flattenNeed sub) kA], Termin.hop (jmp0 g0.bo)⟩ = g3 at Rq hp
  have ofs : (ofSure (⟨sub, HoonSet.empty⟩ : Sure S)).sure = ⟨sub, HoonSet.empty⟩ := by simp [ofSure, sure_mk]
  have e3 : entries (ofSure ⟨sub, HoonSet.empty⟩ : Lazy S) = [] := entries_ofSure _
  have dT : g3.drop = false := Rq.ext.2.2.1.trans d2
  have GqU : GrowU g2 g3 := ⟨Rq.grow.bo, Rq.grow.drop, Rq.grow.keep, Rq.grow.new⟩
  have huT : UpBelow g3 := GqU.up hu2
  have hclT : Clear g3 := Clear.growU (Clear.growU hcl0 G2') GqU
  have r3 : g3.re = g2.re := by rw [← hg3]; rfl
  have c3 : g3.cond = g2.cond := by rw [← hg3]; simp only [Gen.emitted, d2]
  have hcbT : CondBelow g3 := fun x hx => by rw [c3] at hx; have := hcb2 x hx; omega
  obtain ⟨⟨Qh, Rp⟩, hne, -, hfl', hec⟩ := Sp.run (sup := sup) (region := region)
    (L := ofSure ⟨sub, HoonSet.empty⟩) (th := jmp0 g2.bo) hcount (by have := Rq.hi; simp only [jmp0] at this; omega) dT huT
    hclT hcbT Rq.lo Rq.hi rfl (by rw [e3]; simp) (by rw [ofs]; exact dA)
    (fun x hx => by
      rw [ofs] at hx
      exact ⟨by have := (ma x hx).2; omega, Rq.ncond _ (by rw [ofs]; exact hx)⟩)
    (fun e he => by rw [e3] at he; cases he) (by rw [e3]; simp) (fun e he => by rw [e3] at he; cases he)
    (flat_ofSure _) (by rw [ofs]; exact cl) (fun e he => by rw [e3] at he; cases he) hp
  have d5 : g5.drop = false := Rp.drop.trans dT
  have Rp' := Rp.toRunOKLB.copyBunt huT d5 rfl (fun e he => by rw [e3] at he; cases he) hc
  have R7 := runOKGB_sevenLW (minkC7_direct lib P fb fq b.fol hq1 hq2) Rq Rp' (fun r hr => by
    simp only [GMem, lazyReg, NMem] at hr; subst hr; omega)
  have r1 := Rp'.re
  have K := kerfLBM hk la d0 hcb hu hta h1 h2 hsd hsl hlab' hnd hed (by omega)
    ((condFresh_of_eq (by omega) c3).trans Rp'.cfr) R7
  have labS : ∀ e ∈ entries nexS.laz, e.1 < g5.bo := fun e he => by
    rcases (Rp.labs e he).1 with h | h
    · rw [e3] at h; cases h
    · exact h.2
  have b5 := Rp.bo
  obtain ⟨rfl, -, -, -, -, -⟩ := copyL_bunt d5 hc
  rcases nexS with ⟨⟨s1, f1, b1⟩, th1⟩
  exact ⟨⟨_, K⟩, fun hm => by
    obtain ⟨e, he, ee⟩ := List.mem_map.mp hm
    have := labS e he; simp only [jmp0] at ee; omega, by simp only [jmp0]; have := Rq.ext.2.1; simp only at this; omega,
    ⟨hfl'.1, hfl'.2⟩, hec⟩

/-- **The n-ary direct call `[2 p q b]` meets `LOKS false`** (`callLBN_run`),
for a callee that is not pure (so the call is never dropped), `p` meeting
`LOKS false`, `q` skipped and returning the callee's formula, the products of
`p` fitting the bell, the need read `N b false`, no soft call, and
`SplitsLess`. -/
theorem lokS_directN (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {p q : Nomm} {fb fq : Noun}
    {b : Bell} {bNed : NeedOrd} (hring : env.ring b = Option.none) (hned : env.need b = some bNed)
    (hsof : ∀ m, env.sof m p q b bNed = false) (hNf : N b false = some bNed) (hspl : SplitsLess b bNed)
    (hpure : env.pure b = false)
    (Sp : LOKS (S := S) (Map := Map) false lib N env P fb p)
    (hq : safeFolFol q = true)
    (hAp : ∀ x gul y, P x → Mink lib gul [] x fb (Tone.zero y) → SkaModel.Fits b.less y)
    (hq1 : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {rc : Tone}, P s → minkF lib gul n tm s fq = some rc →
      rc = Tone.zero b.fol)
    (hq2 : ∀ {s gul : Noun} {tm : Trace}, P s → Mink lib gul tm s fq (Tone.zero b.fol)) :
    LOKS (S := S) (Map := Map) false lib N env P (n3 (A 2) fb fq) (Nomm.n2 p q (some (b, Option.none))) := by
  refine ⟨fun {sup L th region g0 g1 nex} hc hr => ?_, fun {sup L th region g0 g1 nex} hcount b0 d0 hu hcl0 hcb h1
    h2 hta ht hsd hsl hlab hnd hed hfl hcs hce hr => ?_⟩
  · have hp' : (env.pure b && noneEquivalentL L) = false := by rw [hpure]; rfl
    obtain ⟨sub, gA, out, pro, g2, nexS, g5, ha, -, hp, hc'⟩ := runLC_cal hring hned (hsof _) hq hp' hr
    exact clean_copyL hc' (Sp.clean (L := ofSure ⟨sub, HoonSet.empty⟩)
      (by simp only [ofSure, sure_mk]; exact needOrdAllocRegs_clean bNed g0 gA sub ha) hp) trivial
  · have hp' : (env.pure b && noneEquivalentL L) = false := by rw [hpure]; rfl
    have hc6 : sixCount p ≤ 255 := by simp only [sixCount] at hcount; omega
    obtain ⟨A, B, C', D, E⟩ := callLBN_run lib env hring hned hsof hNf hspl Sp hc6 hq hAp hq1 hq2 hp' b0 d0 hu hcl0
      hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcs hce hr
    exact ⟨A, B, Or.inr C', D, E⟩

end Comp
end SkaModel
end Formalization
