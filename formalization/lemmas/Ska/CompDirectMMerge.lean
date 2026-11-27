import lemmas.Ska.CompDirectMTail

/-!
# The call blocks of `mono` `&` under `%next`, and their merge block

README Gaps 18.11 (track J, 2026-11-27).  Under `%next` (or `%pick`) the
whole-subject version of a direct call (`monoBlocks`, `+mono-try-call`)
ends in two call blocks that hop with an argument into a merge block with a
parameter:

* `opt`: `[cal b subV pro-opt]`, `hop [pro-opt] merge`;
* `pes`: `[csl b sub-pes pro-pes]`, `hop [pro-pes] merge`;
* `merge`: `par [merged]`, `[mov merged pro]`, `hop out`.

What the interpreter does from `opt` and `pes` to `out`, against an oracle
with `OracleFwd` / `OracleBwd`: the block part of `callLBM` (Gaps 18.10 (3)).

* `goJ_cal_j`, `goJ_csl_j`: a call block hopping to any jump.
* `goJ_hop_par`: the hop with one argument into the merge block binds the
  parameter (`evalPass`) and copies it to `pro`.
* `optStep_fwd`, `optStep_bwd`: from `opt` (registers holding the split of
  the callee's subject by its n-ary need) to `out` with the callee's
  product in `pro`, or the callee's `%1` / `%2`.
* `pesStep_fwd`, `pesStep_bwd`: the same from `pes`, the call by subject.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {Map : Type → Type} [HoonMap Map]

section
variable {lib : Lib} {σ : Type} {Inv : σ → Prop} {ν : σ → Needs} {O : Oracle σ} {c : Straight Map} {gul : Noun}

/-- **A `%cal` block hopping to any jump.** -/
theorem goJ_cal_j {o pro : Nat} {b : Bell} {subV : List Nat} {j : Jmp}
    (hb : HoonMap.get c.blocks o = some ⟨[], [Pole.cal b subV pro], Termin.hop j⟩)
    (st : σ) (regs : Map (Option Noun)) (t : Trace) {vs : List Noun}
    (hvs : subV.mapM (fun r => SkaModel.read r regs) = some vs) :
    goJ lib O c gul st regs t (jmp0 o) = (O.call st b false vs t gul).bind fun (ton, st') =>
      match ton with
      | Tone.zero p => goJ lib O c gul st' (store pro p regs) t j
      | ton => some (ton, st') := by
  rw [goJ_jmp0 _ _ _ _ hb, execBlob_cons]
  simp only [execPole]
  rw [show (subV.mapM (SkaModel.read · regs)) = some vs from hvs, Option.bind_some]
  cases O.call st b false vs t gul with
  | none => rfl
  | some x =>
    obtain ⟨ton, st'⟩ := x
    cases ton <;> simp [afterCall, execBlob_hop]

/-- **A `%csl` block hopping to any jump**: the call by subject. -/
theorem goJ_csl_j {o r pro : Nat} {b : Bell} {j : Jmp}
    (hb : HoonMap.get c.blocks o = some ⟨[], [Pole.csl b r pro], Termin.hop j⟩)
    (st : σ) (regs : Map (Option Noun)) (t : Trace) {v : Noun} (hv : SkaModel.read r regs = some v) :
    goJ lib O c gul st regs t (jmp0 o) = (O.call st b true [v] t gul).bind fun (ton, st') =>
      match ton with
      | Tone.zero p => goJ lib O c gul st' (store pro p regs) t j
      | ton => some (ton, st') := by
  rw [goJ_jmp0 _ _ _ _ hb, execBlob_cons]
  simp only [execPole]
  rw [show SkaModel.read r regs = some v from hv, Option.bind_some]
  cases O.call st b true [v] t gul with
  | none => rfl
  | some x =>
    obtain ⟨ton, st'⟩ := x
    cases ton <;> simp [afterCall, execBlob_hop]

/-- **The hop with an argument into the merge block**: the argument's value
is bound to the parameter `merged` and copied to `pro`. -/
theorem goJ_hop_par {m out merged pro a : Nat}
    (hm : HoonMap.get c.blocks m = some ⟨[merged], [Pole.mov merged pro], Termin.hop (jmp0 out)⟩)
    (hne : a ≠ merged) (st : σ) (regs : Map (Option Noun)) (t : Trace) {v : Noun}
    (hv : SkaModel.read a regs = some v) :
    goJ lib O c gul st regs t ⟨[some a], m⟩ =
      goJ lib O c gul st (store pro v (store merged v regs)) t (jmp0 out) := by
  have hg : HoonMap.get regs a = some (some v) := read_eq_some.mp hv
  have hp : evalPass [some a] [merged] regs = some (store merged v regs) := by
    simp [evalPass, evalPassLoop, move, hg, hne, store]
  simp only [goJ, hm, Option.bind_some]
  rw [execBlob, if_pos (Or.inl (by simp)), hp]
  show execBlob lib O c gul st (store merged v regs) t ⟨[], [Pole.mov merged pro], Termin.hop (jmp0 out)⟩ [] = _
  rw [execBlob_cons]
  have hmv : execPole lib O gul st (Pole.mov merged pro) (store merged v regs) t =
      some (Tone.zero (A 0), store pro v (store merged v regs), t, st) := by
    simp [execPole, localPole, move, store, HoonMap.get_put]
  rw [hmv, Option.bind_some]
  simp only
  rw [execBlob_hop]
  rfl

/-- **From the optimistic call block to `out`, forward** (`callStep_fwd`
with the merge block): on registers holding the split of the callee's
subject by its n-ary need, the oracle's answer stands for `+mink` on the
callee's formula; a product is in `pro` (through `pro-opt` and `merged`)
when the code reaches `out`. -/
theorem optStep_fwd (hS : OracleSteps Inv ν O) {n : Nat} (hF : OracleFwd lib Inv ν O n)
    {o m out merged pro proOpt : Nat} {b : Bell} {N : Needs} {nd : NeedOrd} (hN : N b false = some nd)
    {g g' : Gen Map} {sub : Need} (halloc : needOrdAllocRegs nd g = some (sub, g'))
    (hb : HoonMap.get c.blocks o = some ⟨[], [Pole.cal b (flattenNeed sub) proOpt], Termin.hop ⟨[some proOpt], m⟩⟩)
    (hm : HoonMap.get c.blocks m = some ⟨[merged], [Pole.mov merged pro], Termin.hop (jmp0 out)⟩)
    (hne : proOpt ≠ merged)
    {st : σ} (hI : Inv st) (hNle : N ≤ ν st) {regs : Map (Option Noun)} {s' : Noun}
    (hs : HoldsN sub regs s') (hfit : SkaModel.Fits b.less s') {ti tm : Trace}
    (htr : Forall2 (FrameRel lib (ν st)) ti tm) {j : Nat} {r : Tone} (hj : j < n)
    (hmk : minkF lib gul j tm s' b.fol = some r) :
    ∃ ton st', Inv st' ∧ ν st ≤ ν st' ∧ ToneRel lib (ν st') ton r ∧
      goJ lib O c gul st regs ti (jmp0 o) =
        (match ton with
         | Tone.zero p => goJ lib O c gul st' (store pro p (store merged p (store proOpt p regs))) ti (jmp0 out)
         | ton => some (ton, st')) := by
  obtain ⟨vs, ton, st', hvs, hc, hI', hle, hrel⟩ :=
    oracle_call_alloc hS hF hN halloc hI hNle hs hfit htr hj hmk
  refine ⟨ton, st', hI', hle, hrel, ?_⟩
  rw [goJ_cal_j hb st regs ti hvs, hc, Option.bind_some]
  cases ton with
  | zero p => exact goJ_hop_par hm hne st' _ ti (read_store_self _ _ _)
  | one _ => rfl
  | two _ => rfl

/-- **From the optimistic call block to `out`, backward.** -/
theorem optStep_bwd (hS : OracleSteps Inv ν O) (hB : OracleBwd lib Inv ν O)
    {o m out merged pro proOpt : Nat} {b : Bell} {N : Needs} {nd : NeedOrd} (hN : N b false = some nd)
    {g g' : Gen Map} {sub : Need} (halloc : needOrdAllocRegs nd g = some (sub, g'))
    (hb : HoonMap.get c.blocks o = some ⟨[], [Pole.cal b (flattenNeed sub) proOpt], Termin.hop ⟨[some proOpt], m⟩⟩)
    (hm : HoonMap.get c.blocks m = some ⟨[merged], [Pole.mov merged pro], Termin.hop (jmp0 out)⟩)
    (hne : proOpt ≠ merged)
    {st : σ} (hI : Inv st) (hNle : N ≤ ν st) {regs : Map (Option Noun)} {s' : Noun}
    (hs : HoldsN sub regs s') (hfit : SkaModel.Fits b.less s') {ti tm : Trace}
    (htr : Forall2 (FrameRel lib (ν st)) ti tm) {res : Tone × σ}
    (hres : goJ lib O c gul st regs ti (jmp0 o) = some res) :
    ∃ r ton st', Mink lib gul tm s' b.fol r ∧ Inv st' ∧ ν st ≤ ν st' ∧ ToneRel lib (ν st') ton r ∧
      goJ lib O c gul st regs ti (jmp0 o) =
        (match ton with
         | Tone.zero p => goJ lib O c gul st' (store pro p (store merged p (store proOpt p regs))) ti (jmp0 out)
         | ton => some (ton, st')) := by
  obtain ⟨vs, hvs⟩ := holds_mapM sub regs s' hs
  have hargs : argsFor (ν st) b false s' = some vs := by
    rw [← argsFor_of_alloc (hNle b false nd hN) halloc hs, hvs]
  have J := goJ_cal_j (lib := lib) (O := O) (gul := gul) hb st regs ti hvs
  rw [J] at hres
  obtain ⟨⟨ton, st'⟩, hc, -⟩ := Option.bind_eq_some_iff.mp hres
  obtain ⟨r, hmk, hrel⟩ := hB.call st b false vs ti gul ton st' hI hc s' tm hfit hargs htr
  obtain ⟨hI', hle⟩ := hS.call st b false vs ti gul ton st' hI hc
  refine ⟨r, ton, st', hmk, hI', hle, hrel, ?_⟩
  rw [J, hc, Option.bind_some]
  cases ton with
  | zero p => exact goJ_hop_par hm hne st' _ ti (read_store_self _ _ _)
  | one _ => rfl
  | two _ => rfl

/-- **From the pessimistic call block to `out`, forward**: the call by
subject (`N b true`) on the register holding the callee's whole subject. -/
theorem pesStep_fwd (hS : OracleSteps Inv ν O) {n : Nat} (hF : OracleFwd lib Inv ν O n)
    {o m out merged pro proPes subPes : Nat} {b : Bell} {N : Needs} {ndT : NeedOrd} (hNt : N b true = some ndT)
    (hb : HoonMap.get c.blocks o = some ⟨[], [Pole.csl b subPes proPes], Termin.hop ⟨[some proPes], m⟩⟩)
    (hm : HoonMap.get c.blocks m = some ⟨[merged], [Pole.mov merged pro], Termin.hop (jmp0 out)⟩)
    (hne : proPes ≠ merged)
    {st : σ} (hI : Inv st) (hNle : N ≤ ν st) {regs : Map (Option Noun)} {s' : Noun}
    (hs : SkaModel.read subPes regs = some s') (hfit : SkaModel.Fits b.less s') {ti tm : Trace}
    (htr : Forall2 (FrameRel lib (ν st)) ti tm) {j : Nat} {r : Tone} (hj : j < n)
    (hmk : minkF lib gul j tm s' b.fol = some r) :
    ∃ ton st', Inv st' ∧ ν st ≤ ν st' ∧ ToneRel lib (ν st') ton r ∧
      goJ lib O c gul st regs ti (jmp0 o) =
        (match ton with
         | Tone.zero p => goJ lib O c gul st' (store pro p (store merged p (store proPes p regs))) ti (jmp0 out)
         | ton => some (ton, st')) := by
  have hargs : argsFor (ν st) b true s' = some [s'] := by simp [argsFor, hNle b true ndT hNt]
  obtain ⟨ton, st', hc, hrel⟩ := hF.call st b true [s'] ti tm gul s' j r hI hj hfit hargs htr hmk
  obtain ⟨hI', hle⟩ := hS.call st b true [s'] ti gul ton st' hI hc
  refine ⟨ton, st', hI', hle, hrel, ?_⟩
  rw [goJ_csl_j hb st regs ti hs, hc, Option.bind_some]
  cases ton with
  | zero p => exact goJ_hop_par hm hne st' _ ti (read_store_self _ _ _)
  | one _ => rfl
  | two _ => rfl

/-- **From the pessimistic call block to `out`, backward.** -/
theorem pesStep_bwd (hS : OracleSteps Inv ν O) (hB : OracleBwd lib Inv ν O)
    {o m out merged pro proPes subPes : Nat} {b : Bell} {N : Needs} {ndT : NeedOrd} (hNt : N b true = some ndT)
    (hb : HoonMap.get c.blocks o = some ⟨[], [Pole.csl b subPes proPes], Termin.hop ⟨[some proPes], m⟩⟩)
    (hm : HoonMap.get c.blocks m = some ⟨[merged], [Pole.mov merged pro], Termin.hop (jmp0 out)⟩)
    (hne : proPes ≠ merged)
    {st : σ} (hI : Inv st) (hNle : N ≤ ν st) {regs : Map (Option Noun)} {s' : Noun}
    (hs : SkaModel.read subPes regs = some s') (hfit : SkaModel.Fits b.less s') {ti tm : Trace}
    (htr : Forall2 (FrameRel lib (ν st)) ti tm) {res : Tone × σ}
    (hres : goJ lib O c gul st regs ti (jmp0 o) = some res) :
    ∃ r ton st', Mink lib gul tm s' b.fol r ∧ Inv st' ∧ ν st ≤ ν st' ∧ ToneRel lib (ν st') ton r ∧
      goJ lib O c gul st regs ti (jmp0 o) =
        (match ton with
         | Tone.zero p => goJ lib O c gul st' (store pro p (store merged p (store proPes p regs))) ti (jmp0 out)
         | ton => some (ton, st')) := by
  have hargs : argsFor (ν st) b true s' = some [s'] := by simp [argsFor, hNle b true ndT hNt]
  have J := goJ_csl_j (lib := lib) (O := O) (gul := gul) hb st regs ti hs
  rw [J] at hres
  obtain ⟨⟨ton, st'⟩, hc, -⟩ := Option.bind_eq_some_iff.mp hres
  obtain ⟨r, hmk, hrel⟩ := hB.call st b true [s'] ti gul ton st' hI hc s' tm hfit hargs htr
  obtain ⟨hI', hle⟩ := hS.call st b true [s'] ti gul ton st' hI hc
  refine ⟨r, ton, st', hmk, hI', hle, hrel, ?_⟩
  rw [J, hc, Option.bind_some]
  cases ton with
  | zero p => exact goJ_hop_par hm hne st' _ ti (read_store_self _ _ _)
  | one _ => rfl
  | two _ => rfl

end

end Comp
end SkaModel
end Formalization
