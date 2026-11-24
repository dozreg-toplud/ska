import lemmas.Ska.CompCallSem

/-!
# One call against an oracle that answers as `+mink` does

README Gaps 12.9 (twelfth session).  The step of a run relation for code
that calls: the call block of `callL` entered with the callee's subject held
in the registers of its need.

* `holds_mapM`: registers that hold a noun as a need read a value at every
  register of the need.
* `frames_mono`: the frames of a trace stand for `+mink`'s under bigger
  needs too (how `FrameRel` moves with the needs: monotone, so the trace
  handed to a call at a later state still stands for `+mink`'s).
* `callStep_fwd`: **the direct call under `%next` or `%pick`**.  When the
  table at the call's state answers the callee's need `nd` (it does when it
  includes `N` and `N b false = some nd`, which `CalleeNeeds` gives), the
  registers that `+need-ord-alloc-regs` allocated for `nd` hold the
  callee's subject `s'`, `s'` fits the callee's sock, the caller's trace
  stands for `+mink`'s, and `+mink` returns `r` on `[s' b.fol]` with fuel
  below the oracle's bound: the oracle answers with a tone that stands for
  `r` at a state where `Inv` holds and the needs grew, and the code goes on
  at `out` with the product in `pro` (a `%0`) or returns that tone (a crash
  or a block, passed up unchanged: `+mink` of `[2 b c]` returns the callee's
  tone as it is).
* `tailStep_fwd`: **the tail call under `%done`** meets `ReturnsC`.

The fuel.  `OracleFwd lib Inv ν O n` asks for `+mink`'s fuel on the
callee's formula, below `n`.  `SemC` of `CompCall.lean` couples that bound
with the fuel of `nommF` on the caller's nomm, and the two do not match: a
callee's nomm may take fewer steps than `+mink` on its formula (`Annot.fold`
makes a whole computation the literal `[1 v]`, `Annot.n9` and `Annot.n8`
change the shape), so from `nommF` with fuel `n` on `[2 p q]` the callee's
formula may need `+mink` fuel `n` or more, which `OracleFwd` with `n` does
not cover.  The forward relation for code that calls must therefore be
indexed by `+mink`'s fuel on the caller's formula (as `ContractFwd` is):
`+mink` of `[2 b c]` with fuel `j + 1` runs the callee's formula with fuel
`j`, which `OracleFwd` with `j + 1` covers.  `SemCM` is that statement.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {Map : Type → Type} [HoonMap Map]

/-- Registers that hold a noun as a need read a value at each of its
registers. -/
theorem holds_mapM : ∀ (sub : Need) (regs : Map (Option Noun)) (s : Noun), HoldsN sub regs s →
    ∃ vs, (flattenNeed sub).mapM (fun r => SkaModel.read r regs) = some vs
  | Need.none, _, _, _ => ⟨[], rfl⟩
  | Need.this r, regs, s, hs => ⟨[s], by simp only [HoldsN] at hs; simp [flattenNeed, hs]⟩
  | Need.pair p q, regs, Noun.cell h t, hs => by
    obtain ⟨a, ha⟩ := holds_mapM p regs h hs.1
    obtain ⟨b, hb⟩ := holds_mapM q regs t hs.2
    exact ⟨a ++ b, by simp [flattenNeed, List.mapM_append, ha, hb]⟩
  | Need.both r p q, regs, Noun.cell h t, hs => by
    obtain ⟨a, ha⟩ := holds_mapM p regs h hs.2.1
    obtain ⟨b, hb⟩ := holds_mapM q regs t hs.2.2
    exact ⟨C h t :: (a ++ b), by simp [flattenNeed, List.mapM_cons, List.mapM_append, hs.1, ha, hb]⟩
  | Need.pair _ _, _, Noun.atom _, hs => hs.elim
  | Need.both _ _ _, _, Noun.atom _, hs => hs.elim

/-- **How `FrameRel` moves with the needs**: a trace that stands for
`+mink`'s under `N` does under every `N'` that includes `N`. -/
theorem frames_mono {lib : Lib} {N N' : Needs} (h : N ≤ N') {ti tm : Trace}
    (hf : Forall2 (FrameRel lib N) ti tm) : Forall2 (FrameRel lib N') ti tm :=
  hf.imp fun _ _ => FrameRel.mono h

section
variable {lib : Lib} {σ : Type} {Inv : σ → Prop} {ν : σ → Needs} {O : Oracle σ} {n : Nat} {gul : Noun}
  {c : Straight Map}

/-- The oracle's answer to a call on the registers of the callee's need. -/
theorem oracle_call_alloc (hS : OracleSteps Inv ν O) (hF : OracleFwd lib Inv ν O n)
    {N : Needs} {b : Bell} {nd : NeedOrd} (hN : N b false = some nd) {g g' : Gen Map} {sub : Need}
    (halloc : needOrdAllocRegs nd g = some (sub, g')) {st : σ} (hI : Inv st) (hNle : N ≤ ν st)
    {regs : Map (Option Noun)} {s' : Noun} (hs : HoldsN sub regs s') (hfit : SkaModel.Fits b.less s')
    {ti tm : Trace} (htr : Forall2 (FrameRel lib (ν st)) ti tm) {j : Nat} {r : Tone} (hj : j < n)
    (hm : minkF lib gul j tm s' b.fol = some r) :
    ∃ vs ton st', (flattenNeed sub).mapM (fun x => SkaModel.read x regs) = some vs ∧
      O.call st b false vs ti gul = some (ton, st') ∧ Inv st' ∧ ν st ≤ ν st' ∧ ToneRel lib (ν st') ton r := by
  obtain ⟨vs, hvs⟩ := holds_mapM sub regs s' hs
  have hargs : argsFor (ν st) b false s' = some vs := by
    rw [← argsFor_of_alloc (hNle b false nd hN) halloc hs, hvs]
  obtain ⟨ton, st', hc, hrel⟩ := hF.call st b false vs ti tm gul s' j r hI hj hfit hargs htr hm
  obtain ⟨hI', hle⟩ := hS.call st b false vs ti gul ton st' hI hc
  exact ⟨vs, ton, st', hvs, hc, hI', hle, hrel⟩

/-- **The direct call under `%next` or `%pick`**: the call block of
`callL`, entered with the callee's subject held in the registers allocated
for its need. -/
theorem callStep_fwd (hS : OracleSteps Inv ν O) (hF : OracleFwd lib Inv ν O n)
    {o out pro : Nat} {b : Bell} {N : Needs} {nd : NeedOrd} (hN : N b false = some nd)
    {g g' : Gen Map} {sub : Need} (halloc : needOrdAllocRegs nd g = some (sub, g'))
    (hb : HoonMap.get c.blocks o = some ⟨[], [Pole.cal b (flattenNeed sub) pro], Termin.hop (jmp0 out)⟩)
    {st : σ} (hI : Inv st) (hNle : N ≤ ν st) {regs : Map (Option Noun)} {s' : Noun}
    (hs : HoldsN sub regs s') (hfit : SkaModel.Fits b.less s') {ti tm : Trace}
    (htr : Forall2 (FrameRel lib (ν st)) ti tm) {j : Nat} {r : Tone} (hj : j < n)
    (hm : minkF lib gul j tm s' b.fol = some r) :
    ∃ ton st', Inv st' ∧ ν st ≤ ν st' ∧ ToneRel lib (ν st') ton r ∧
      goJ lib O c gul st regs ti (jmp0 o) =
        (match ton with
         | Tone.zero p => goJ lib O c gul st' (store pro p regs) ti (jmp0 out)
         | ton => some (ton, st')) := by
  obtain ⟨vs, ton, st', hvs, hc, hI', hle, hrel⟩ :=
    oracle_call_alloc hS hF hN halloc hI hNle hs hfit htr hj hm
  refine ⟨ton, st', hI', hle, hrel, ?_⟩
  rw [goJ_cal hb st regs ti hvs, hc, Option.bind_some]
  cases ton <;> rfl

/-- **The tail call under `%done`** meets `ReturnsC`. -/
theorem tailStep_fwd (hS : OracleSteps Inv ν O) (hF : OracleFwd lib Inv ν O n)
    {o : Nat} {b : Bell} {N : Needs} {nd : NeedOrd} (hN : N b false = some nd)
    {g g' : Gen Map} {sub : Need} (halloc : needOrdAllocRegs nd g = some (sub, g'))
    (hb : HoonMap.get c.blocks o = some ⟨[], [], Termin.jmp b (flattenNeed sub)⟩)
    {st : σ} (hI : Inv st) (hNle : N ≤ ν st) {regs : Map (Option Noun)} {s' : Noun}
    (hs : HoldsN sub regs s') (hfit : SkaModel.Fits b.less s') {ti tm : Trace}
    (htr : Forall2 (FrameRel lib (ν st)) ti tm) {j : Nat} {r : Tone} (hj : j < n)
    (hm : minkF lib gul j tm s' b.fol = some r) :
    ReturnsC lib O c gul Inv ν st regs ti (jmp0 o) r := by
  obtain ⟨vs, ton, st', hvs, hc, hI', hle, hrel⟩ :=
    oracle_call_alloc hS hF hN halloc hI hNle hs hfit htr hj hm
  exact ⟨ton, st', hI', hle, by rw [goJ_jmp hb st regs ti hvs, hc], hrel⟩

end

/-! ## The forward relation indexed by `+mink`'s fuel -/

section
variable {S : Type} [HoonSet S]

/-- **The run relation of a nomm with calls, indexed by `+mink`'s fuel**
(stated, the replacement of `SemC`): as `SemC`, but the hypothesis on the
nomm is that it stands for the formula `f` on the subjects of `P`
(`Annot`), `s` is one of them, and `+mink` returns `r` on `[s f]` with fuel
`n`, the bound of `OracleFwd`; a direct call inside then runs its callee's
formula with less fuel (`callStep_fwd`, `tailStep_fwd`). -/
def SemCM (lib : Lib) (env : CallEnv) (N : Needs) (code : Bell → Option Nomm) (P : Noun → Prop) (f : Noun)
    (nm : Nomm) (goal : CGoal S) (g0 g1 : Gen Map) (nex : NextL S) : Prop :=
  CalleeNeeds env N → CodeOK lib code → Annot lib code P f nm →
  ∀ (c : Straight Map) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) (n : Nat) (gul : Noun)
    (ti tm : Trace) (s s0 : Noun) (r : Tone) (cf : Map (Nat × List Nat)) (ned : Need),
    (∀ st, Inv st → N ≤ ν st) → OracleSteps Inv ν O → OracleFwd lib Inv ν O n →
    P s → minkF lib gul n tm s f = some r →
    (∀ st, AgreeU lib O c gul st ti cf ned g0 g1 nex.laz s0 s) → (∀ x, NMem ned x → g1.re ≤ x) →
    ∀ st, Inv st → Forall2 (FrameRel lib (ν st)) ti tm →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    GoalSemC lib O c gul Inv ν (fun x => x < g0.re ∨ NMem ned x) st regs ti nex.th goal r

end

end Comp
end SkaModel
end Formalization
