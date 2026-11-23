import lemmas.Ska.CompDown
import lemmas.Ska.CompCoerce

/-!
# The final pass meets the contract, with no assumption about the model

`finish_bellContract` of `CompTopOK.lean` with its two hypotheses about the
model discharged: `RunDown` by `runDown` (`CompDown.lean`) and `CoerceSpec`
by `coerceSpec` (`CompCoerce.lean`).  What it still assumes: the nomm is on
the fragment `Frag` and pure, nothing is baked, and the bell's cape has no
cell whose halves both know nothing (`CapeNorm`).
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- **The final pass meets the relation at the entry**, on the fragment,
when nothing is baked. -/
theorem finish_compDone' [HoonMapKeys Map] (lib : Lib) {nm : Nomm} (hf : Frag nm (CGoal.done : CGoal S))
    {ord : NeedOrd} {less : Cape} {bake : Need → Need × List (Nat × Noun)} {c' : Straight Map}
    (hbake : ∀ ned, bake ned = (ned, [])) (h : finish (S := S) nm ord less bake = some c') :
    CompDoneOn lib c' nm (CapeAxes less) :=
  finish_compDone lib hf hbake (runDown nm) coerceSpec h

/-- **The final pass meets the contract** of its bell, on the fragment, for
every shape `ord` for which it does not crash, when nothing is baked and the
bell's cape has no `[| |]`. -/
theorem finish_bellContract' [HoonMapKeys Map] {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {b : Bell} {nm : Nomm} (hp : nm.pure = true) (hA : Annot lib code (SkaModel.Fits b.less) b.fol nm)
    (hf : Frag nm (CGoal.done : CGoal S)) {cape : Cape} {data : Noun} (hb : b.less = Sock.mk cape data)
    (hn : CapeNorm cape) {ord : NeedOrd} {bake : Need → Need × List (Nat × Noun)}
    (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map} (h : finish (S := S) nm ord cape bake = some c')
    (N : Needs) : BellContract lib N b false c' :=
  finish_bellContract hok hp hA hf hb hn hbake (runDown nm) coerceSpec h N


/-! ## The inputs are a run -/

/-- `+need-ord-alloc-regs` allocates the registers of the need in the order
`+flatten-need` lists them, one after the other. -/
theorem flatten_needOrdAllocRegs : ∀ (ord : NeedOrd) (g g' : Gen Map) (ned : Need),
    needOrdAllocRegs ord g = some (ned, g') → flattenNeed ned = List.range' g.re (g'.re - g.re)
  | NeedOrd.none, g, g', ned, h => by
    simp only [needOrdAllocRegs, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [flattenNeed]
  | NeedOrd.this, g, g', ned, h => by
    simp only [needOrdAllocRegs, bind_apply, re_apply, pure_apply, Option.bind_some, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [flattenNeed]
  | NeedOrd.pair p q, g, g', ned, h => by
    obtain ⟨hn, ga, h1, h⟩ := bind_some h
    obtain ⟨tn, gb, h2, h⟩ := bind_some h
    have la := (needOrdAllocRegs_spec p _ _ _ h1).2.1
    have lb := (needOrdAllocRegs_spec q _ _ _ h2).2.1
    have fa := flatten_needOrdAllocRegs p _ _ _ h1
    have fb := flatten_needOrdAllocRegs q _ _ _ h2
    split at h
    · cases h
    · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [flattenNeed, fa, fb]
      rw [show gb.re - g.re = (ga.re - g.re) + (gb.re - ga.re) by omega, ← List.range'_append_1,
        show g.re + (ga.re - g.re) = ga.re by omega]
  | NeedOrd.both p q, g, g', ned, h => by
    obtain ⟨r0, g0', h0, h⟩ := bind_some h
    simp only [re_apply, Option.some.injEq, Prod.mk.injEq] at h0
    obtain ⟨rfl, rfl⟩ := h0
    obtain ⟨hn, ga, h1, h⟩ := bind_some h
    obtain ⟨tn, gb, h2, h⟩ := bind_some h
    have la := (needOrdAllocRegs_spec p _ _ _ h1).2.1
    have lb := (needOrdAllocRegs_spec q _ _ _ h2).2.1
    have fa := flatten_needOrdAllocRegs p _ _ _ h1
    have fb := flatten_needOrdAllocRegs q _ _ _ h2
    simp only at la fa
    split at h
    · cases h
    · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [flattenNeed, fa, fb]
      rw [show gb.re - g.re = ((ga.re - (g.re + 1)) + (gb.re - ga.re)) + 1 by omega, List.range'_succ,
        ← List.range'_append_1, show g.re + 1 + (ga.re - (g.re + 1)) = ga.re by omega]

/-- So the input registers that `+to-straight` sees, when nothing is baked,
are the run `[r0, r0+n)`: it takes its renaming path, never the other. -/
theorem isRun_needOrdAllocRegs {ord : NeedOrd} {g g' : Gen Map} {ned : Need}
    (h : needOrdAllocRegs ord g = some (ned, g')) :
    isRun (flattenNeed ned) ((flattenNeed ned).headD 0) 0 = true := by
  rw [isRun_iff, flatten_needOrdAllocRegs ord g g' ned h]
  cases e : g'.re - g.re with
  | zero => simp
  | succ n => simp [List.range'_succ]

end Comp
end SkaModel
end Formalization
