import lemmas.Compiler.CompCalleeComp
import lemmas.Ska.CompRingRun

/-!
# The direct call of `%2` through a ring: steps `0` to `6` (track K, README Gaps 19 (h))

The links of the direct call (`CompRunDirect{C,MonoB}.lean`, `CompCalleeComp.lean`) push `rin`
(step `1`, `(~(get by call-cole) b-callee)`) as `A 0`: they ask the callee's `call.cole` entry to
be `~`.  Here `rin` is any unit `unitNoun id rin`: `~`, or `[~ u]` for a ring `u` with no
`jets-hot` entry (no hot driver: then `b-sur` (step `5`, `(biff rin ~(get by jets-hot))`) is
`+callee-sure` as with no ring, and `+callee-need` reads as with no ring, `cne_readR`).

* `crdS6mR`: the subject of step `7` with `rin` the noun `RIN` (`crdS6m` is `RIN = A 0`).
* `RinAt ctx b rin`: the `call.cole` entry of `b` is `unitNoun id rin`; a ring has no `jets-hot`
  entry.  `rinAt_none`: the old hypothesis (`~`, any `jets-hot`).
* `CallNounMTG`: `CallNounMT` with `RinAt` for its `cole` and `hot`, the push of `sof` on the
  subject with `rin`.  `callNounMTG_of_mt`: the old one is the case `rin = none`.
* **`crd_head6MTG`**: steps `0` to `6` of the call with the rest threaded, `rin` any unit with no
  hot driver.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-- The subject of step `7` with `rin` the noun `RIN`. -/
abbrev crdS6mR (SOF V5 SV SN V2 RIN PV S : Noun) : Noun :=
  C SOF (C V5 (C SV (C SN (C V2 (C RIN (C PV S))))))

theorem crdS6mR_none (SOF V5 SV SN V2 PV S : Noun) :
    crdS6mR SOF V5 SV SN V2 (A 0) PV S = crdS6m SOF V5 SV SN V2 PV S := rfl

/-- **The callee's `call.cole` entry is the unit `rin`** (ctx axis `6846`), and a ring has no
`jets-hot` entry (ctx axis `54`). -/
def RinAt (ctx : Noun) (b : Bell) (rin : Option Noun) : Prop :=
  ∃ cole jh, slot? 6846 ctx = some cole ∧ slot? 54 ctx = some jh ∧
    getF mugF b.toNoun cole = some (unitNoun id rin) ∧ ∀ u, rin = some u → getF mugF u jh = some (A 0)

/-- The old hypotheses (`~` entry, any `jets-hot`) are `RinAt` at `none`. -/
theorem rinAt_none {b : Bell} (hcole : ∃ cole, slot? 6846 ctx = some cole ∧ getF mugF b.toNoun cole = some (A 0))
    (hhot : ∃ jh, slot? 54 ctx = some jh) : RinAt ctx b Option.none := by
  obtain ⟨cole, h1, h2⟩ := hcole
  obtain ⟨jh, h3⟩ := hhot
  exact ⟨cole, jh, h1, h3, h2, fun _ h => by cases h⟩

/-- `RinAt` is `ColeAt` (`CompRingNeed.lean`) with the entry named. -/
theorem rinAt_some {b : Bell} {u cole jh : Noun} (h1 : slot? 6846 ctx = some cole) (h2 : slot? 54 ctx = some jh)
    (h3 : getF mugF b.toNoun cole = some (C (A 0) u)) (h4 : getF mugF u jh = some (A 0)) :
    RinAt ctx b (some u) :=
  ⟨cole, jh, h1, h2, h3, fun _ h => by cases h; exact h4⟩

/-- **`CallNounMT` through a ring**: the entry `rin` with no hot driver (`RinAt`), the need step
from `x` to `x'`, `+callee-sure` at `x'`, and the push of `sof` on the subject with `rin`. -/
structure CallNounMTG (msup : Option Nomm) (ctx : Noun) (p q : Nomm) (b : Bell) (nb : NeedOrd) (sur : Noun)
    (x x' : GenRest) (mono SOF : Noun) (rin : Option Noun) : Prop where
  cole : RinAt ctx b rin
  need : ∀ g : Gen (TreapMap mugF),
    nock (C cneBat (C b.toNoun (compCore g x ctx))) cneBat = some (C nb.toNoun (genNoun g x'))
  sure : ∀ g : Gen (TreapMap mugF), nock (C csuBat (C b.toNoun (compCore g x' ctx))) csuBat = some sur
  sof : ∀ (g : Gen (TreapMap mugF)) (SV SN PV goalN regionN : Noun),
    nock (C sur (C SV (C SN (C nb.toNoun (C (unitNoun id rin) (C PV (crSubj mono (crdN p q b) goalN regionN
      (unitNoun Nomm.toNoun msup) (compCore g x' ctx)))))))) crDKc6 = some SOF

/-- The old `CallNounMT` is the case with no ring. -/
theorem callNounMTG_of_mt {msup : Option Nomm} {p q : Nomm} {b : Bell} {nb : NeedOrd} {sur : Noun}
    {x x' : GenRest} {mono SOF : Noun} (h : CallNounMT msup ctx p q b nb sur x x' mono SOF) :
    CallNounMTG msup ctx p q b nb sur x x' mono SOF Option.none :=
  ⟨rinAt_none h.cole h.hot, h.need, h.sure, h.sof⟩

/-- **Steps `0` to `6` through a ring, the rest threaded**: `crd_head6MT` with `rin` any unit
with no hot driver; the subject of step `7` holds `rin`. -/
theorem crd_head6MTG (h7 : slot? 7 ctx = some compK) (msup : Option Nomm) (p q : Nomm) (b : Bell) (nb : NeedOrd)
    (sur : Noun) (x x' : GenRest) (mono SOF : Noun) (rin : Option Noun)
    (hn : CallNounMTG msup ctx p q b nb sur x x' mono SOF rin) (PV goalN : Noun)
    (region : List Nat) (g : Gen (TreapMap mugF)) :
    nock (C PV (crSubj mono (crdN p q b) goalN (listNoun A region) (unitNoun Nomm.toNoun msup) (compCore g x ctx)))
      crDCall
      = (needOrdAllocRegs nb g).bind fun r => nock (crdS6mR SOF sur (listNoun A (flattenNeed r.1)) r.1.toNoun
          nb.toNoun (unitNoun id rin) PV
          (crSubj mono (crdN p q b) goalN (listNoun A region) (unitNoun Nomm.toNoun msup) (compCore r.2 x' ctx)))
          crDKr7 := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  obtain ⟨cole, jh, hcole, hjh, hgc, hu⟩ := hn.cole
  have hgt := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ b.toNoun cole _ hgc
  have hne := hn.need g
  have hnoar := noar_gate ctx x' nb g
  have hD1 := cne_at
  have hD2 := noar_at
  have hD3 := comp_fn_at
  have hD4 := csu_at
  rw [crdk_eq]
  simp only [crSubj, compCore, crdS6mR] at hne hnoar ⊢
  cases e : needOrdAllocRegs nb g with
  | none =>
    rw [e] at hnoar
    generalize comp.door = Dr at hne hnoar hD1 hD2 hD3 hD4 ⊢
    unfold crDKr0 crDKr1 crDKc1 crDKr2 crDKc2 crDKr3 crDKc3
    simp [nock_exec, crdN, hc, hcole, by_arm, by.arm_at, by.get.arm_at, get_arm, hgt, hD1, hne, hD2, noarHint, h7, hnoar, e]
  | some r =>
    obtain ⟨subNed, g1⟩ := r
    rw [e] at hnoar
    simp only [Option.map_some] at hnoar
    have hfn := comp_flatten_need hc (genNoun g1 x') subNed
    have hsu := hn.sure g1
    have hsof := hn.sof g1 (listNoun A (flattenNeed subNed)) subNed.toNoun PV goalN (listNoun A region)
    simp only [crSubj, compCore] at hsu hsof
    cases rin with
    | none =>
      simp only [unitNoun] at hgt hsof
      generalize comp.door = Dr at hne hnoar hD1 hD2 hD3 hD4 hfn hsu hsof ⊢
      unfold crDKr0 crDKr1 crDKc1 crDKr2 crDKc2 crDKr3 crDKc3 crDKr4 crDKc4 crDKr5 crDKc5 crDKr6
      simp [nock_exec, crdN, hc, hcole, by_arm, by.arm_at, by.get.arm_at, get_arm, hgt, hD1, hne, hD2, noarHint, h7,
        hnoar, hD3, comp_fn_arm, hfn, hjh, biff_arm, biff.arm_at, biff_gate_nil, hD4, hsu, hsof, unitNoun]
    | some u =>
      have hgj := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ u jh _ (hu u rfl)
      simp only [unitNoun, id] at hgt hsof
      generalize comp.door = Dr at hne hnoar hD1 hD2 hD3 hD4 hfn hsu hsof ⊢
      unfold crDKr0 crDKr1 crDKc1 crDKr2 crDKc2 crDKr3 crDKc3 crDKr4 crDKc4 crDKr5 crDKc5 crDKr6
      simp [nock_exec, crdN, hc, hcole, by_arm, by.arm_at, by.get.arm_at, get_arm, hgt, hD1, hne, hD2, noarHint, h7,
        hnoar, hD3, comp_fn_arm, hfn, hjh, biff_arm, biff.arm_at, biff_gate_some, hgj, hD4, hsu, hsof, unitNoun]

end Compiler
end Formalization
