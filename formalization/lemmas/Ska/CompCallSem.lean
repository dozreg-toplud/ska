import lemmas.Ska.CompRunLCEq

/-!
# What the call blocks do, and the arguments of a call

README Gaps 12.9 (twelfth session).  The blocks the case `%2` of `+run`
emits (`callL`), run by the interpreter's `execBlob` against an oracle.

* `goJ_cal`: the block `[%cal b subV pro]`, `%hop out` of a direct call
  under `%next` or `%pick`: the oracle's `call` on the arguments' values with
  the caller's trace `t`, for `mono` `|`; a product goes to `pro` and the
  code hops to `out` with the trace `t` and the state the oracle left; a
  `%1` or a `%2` is returned as the oracle gave it, at that state (with its
  own trace: the callee's, not the caller's).  `callBlockSem`: this is
  `CallBlockSem` of `CompCall.lean`.
* `goJ_jmp`: the tail call `[%jmp b subV]`: the oracle's answer is the
  function's.
* `goJ_nok`: the indirect call `[%nok rSub rFol pro]`, `%hop out`: the
  oracle's `nok` on the subject and the formula (no trace is passed, the
  scry gate is); a product goes to `pro`, a `%1` is returned, a `%2` is
  returned with the caller's trace below the callee's (`tr ++ t`).
* `allocSplit`: **`AllocSplit` holds**: the registers `+need-ord-alloc-regs`
  allocates for the callee's need `nd`, held by the noun `s`, read in the
  order of `+flatten-need` the split of `s` by `nd` (`argsFor` when `nd` is
  the callee's need in the table).  `argsFor_of_alloc`: so the values a call
  block passes are `argsFor N b false s` when `N b false = some nd`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {Map : Type → Type} [HoonMap Map]

section Exec
variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun}

/-- **The block of a direct call** (`%cal`, then a hop). -/
theorem goJ_cal {o out pro : Nat} {b : Bell} {subV : List Nat}
    (hb : HoonMap.get c.blocks o = some ⟨[], [Pole.cal b subV pro], Termin.hop (jmp0 out)⟩)
    (st : σ) (regs : Map (Option Noun)) (t : Trace) {vs : List Noun}
    (hvs : subV.mapM (fun r => SkaModel.read r regs) = some vs) :
    goJ lib O c gul st regs t (jmp0 o) = (O.call st b false vs t gul).bind fun (ton, st') =>
      match ton with
      | Tone.zero p => goJ lib O c gul st' (store pro p regs) t (jmp0 out)
      | ton => some (ton, st') := by
  rw [goJ_jmp0 _ _ _ _ hb, execBlob_cons]
  simp only [execPole]
  rw [show (subV.mapM (SkaModel.read · regs)) = some vs from hvs, Option.bind_some]
  cases O.call st b false vs t gul with
  | none => rfl
  | some x =>
    obtain ⟨ton, st'⟩ := x
    cases ton <;> simp [afterCall, execBlob_hop]

/-- `CallBlockSem` of `CompCall.lean` holds. -/
theorem callBlockSem : CallBlockSem lib O c gul := by
  intro o out pro b subV hb st regs t vs hvs
  exact goJ_cal hb st regs t hvs

/-- **The block of a tail call** (`%jmp`): the oracle's answer is the
function's. -/
theorem goJ_jmp {o : Nat} {b : Bell} {subV : List Nat}
    (hb : HoonMap.get c.blocks o = some ⟨[], [], Termin.jmp b subV⟩)
    (st : σ) (regs : Map (Option Noun)) (t : Trace) {vs : List Noun}
    (hvs : subV.mapM (fun r => SkaModel.read r regs) = some vs) :
    goJ lib O c gul st regs t (jmp0 o) = O.call st b false vs t gul := by
  rw [goJ_jmp0 _ _ _ _ hb, execBlob]
  simp only [ne_eq, not_true_eq_false, or_self, if_false]
  rw [show (subV.mapM (SkaModel.read · regs)) = some vs from hvs]
  rfl

/-- **The block of an indirect call** (`%nok`, then a hop): the oracle's
`nok` on the subject and the formula; a crash's trace goes on top of the
caller's. -/
theorem goJ_nok {o out rSub rFol pro : Nat}
    (hb : HoonMap.get c.blocks o = some ⟨[], [Pole.nok rSub rFol pro], Termin.hop (jmp0 out)⟩)
    (st : σ) (regs : Map (Option Noun)) (t : Trace) {u f : Noun}
    (hu : SkaModel.read rSub regs = some u) (hf : SkaModel.read rFol regs = some f) :
    goJ lib O c gul st regs t (jmp0 o) = (O.nok st u f gul).bind fun (ton, st') =>
      match ton with
      | Tone.zero p => goJ lib O c gul st' (store pro p regs) t (jmp0 out)
      | Tone.one b => some (Tone.one b, st')
      | Tone.two tr => some (Tone.two (tr ++ t), st') := by
  rw [goJ_jmp0 _ _ _ _ hb, execBlob_cons]
  simp only [execPole, hu, hf, Option.bind_some]
  cases O.nok st u f gul with
  | none => rfl
  | some x =>
    obtain ⟨ton, st'⟩ := x
    cases ton <;> simp [execBlob_hop]

end Exec

/-! ## The arguments -/

/-- **`AllocSplit` holds**: the registers of `+need-ord-alloc-regs` read the
split of the noun they hold. -/
theorem allocSplit_go : ∀ (nd : NeedOrd) (g g' : Gen Map) (sub : Need), needOrdAllocRegs nd g = some (sub, g') →
    ∀ (regs : Map (Option Noun)) (s : Noun), HoldsN sub regs s →
      (flattenNeed sub).mapM (fun r => SkaModel.read r regs) = SkaModel.split nd s
  | NeedOrd.none, g, g', sub, h, regs, s, _ => by
    simp only [needOrdAllocRegs, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [flattenNeed, SkaModel.split]
  | NeedOrd.this, g, g', sub, h, regs, s, hs => by
    simp only [needOrdAllocRegs, bind_apply, re_apply, pure_apply, Option.bind_some, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [HoldsN] at hs
    simp [flattenNeed, SkaModel.split, hs]
  | NeedOrd.pair p q, g, g', sub, h, regs, s, hs => by
    obtain ⟨hn, ga, h1, h⟩ := bind_some h
    obtain ⟨tn, gb, h2, h⟩ := bind_some h
    split at h
    · cases h
    · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      cases s with
      | atom _ => simp [HoldsN] at hs
      | cell sh st =>
        obtain ⟨hh, ht⟩ := hs
        simp only [flattenNeed, List.mapM_append, allocSplit_go p _ _ _ h1 regs sh hh,
          allocSplit_go q _ _ _ h2 regs st ht, SkaModel.split]
        cases SkaModel.split p sh <;> cases SkaModel.split q st <;> rfl
  | NeedOrd.both p q, g, g', sub, h, regs, s, hs => by
    obtain ⟨r0, g0', h0, h⟩ := bind_some h
    simp only [re_apply, Option.some.injEq, Prod.mk.injEq] at h0
    obtain ⟨rfl, rfl⟩ := h0
    obtain ⟨hn, ga, h1, h⟩ := bind_some h
    obtain ⟨tn, gb, h2, h⟩ := bind_some h
    split at h
    · cases h
    · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      cases s with
      | atom _ => simp [HoldsN] at hs
      | cell sh st =>
        obtain ⟨hr, hh, ht⟩ := hs
        simp only [flattenNeed, List.mapM_cons, List.mapM_append, hr, allocSplit_go p _ _ _ h1 regs sh hh,
          allocSplit_go q _ _ _ h2 regs st ht, SkaModel.split]
        cases SkaModel.split p sh <;> cases SkaModel.split q st <;> rfl

theorem allocSplit : AllocSplit Map := allocSplit_go

/-- **The values a call block passes are the callee's arguments**: when the
table answers the callee's need `nd` (`CalleeNeeds`), they are `argsFor`. -/
theorem argsFor_of_alloc {N : Needs} {b : Bell} {nd : NeedOrd} (hN : N b false = some nd)
    {g g' : Gen Map} {sub : Need} (h : needOrdAllocRegs nd g = some (sub, g'))
    {regs : Map (Option Noun)} {s : Noun} (hs : HoldsN sub regs s) :
    (flattenNeed sub).mapM (fun r => SkaModel.read r regs) = argsFor N b false s := by
  rw [allocSplit_go nd g g' sub h regs s hs]
  simp [argsFor, hN]

end Comp
end SkaModel
end Formalization
