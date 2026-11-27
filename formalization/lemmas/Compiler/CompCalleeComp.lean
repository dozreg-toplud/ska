import lemmas.Compiler.CompRunDirectS
import lemmas.Compiler.CompRunRBase

/-!
# The compile case of `+callee-need`: a miss in `nary.cache` (README Gaps 19 (g))

Measured (`tools/hoon/calleecomp.py`): the miss is the normal way a callee outside
the SCC gets compiled, and in the whole-subject run of `+compile-unary` it fires on
the callees `+inlined` had inlined.  So the run link must thread the rest of the state.

* `cccSccF`, `cccCsiF`: the pushes of `+scc-of` and `+compile-scc-in` in the miss
  branch `cccBig` of `+callee-compiled` (door arm `13791`), `ccc_big` its cut.
* **`ccc_miss`**: given the two gates on the subjects of the branch (named, in the
  shape of `hcsi`), `+callee-compiled` returns `[nb gen']`, where `gen'` is `gen`
  with `cache` the cache `+compile-scc-in` returned.
* `CccMiss` (those hypotheses as one fact), `NeedStep` (the read-only cases with the
  rest unchanged, or a miss with the new rest), **`cne_step`**: `+callee-need` on
  every case with no ring returns `nb` and the new rest.
* `CallNounMT`, **`crd_head6MT`**: steps `0` to `6` of the call with the need push
  changing the rest from `x` to `x'` (`crd_head6M` when `x' = x`).
* `CompRunAtXT`: the run link threading the rest; `crxt_of_x`: every
  `CompRunAtX` is one with `x' = x`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-! ## The miss branch of `+callee-compiled` -/

/-- The push of `+scc-of` (arm `0x1777f` of axis `255`) on `[b-callee
calls.long-ska sccs.cache.gen]`. -/
def cccSccF : Noun :=
  C (A 8) (C (C (A 9) (C (A 0x1777f) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C
    (C (A 0) (A 30)) (C (C (A 0) (A 8171)) (C (A 0) (A 0x3f7f6))))) (C (A 0) (A 2)))))))

/-- The push of `+compile-scc-in` (`K` arm `2732`) on `[new-scc long-ska
jets-hot cache.gen]`. -/
def cccCsiF : Noun :=
  C (A 8) (C (C (A 9) (C (A 2732) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C
    (C (A 0) (A 6)) (C (C (A 0) (A 4090)) (C (C (A 0) (A 8182)) (C (A 0) (A 0xfefe))))))
    (C (A 0) (A 2)))))))

/-- `need:(~(got by m) b-callee)`: `got:by` (arm `701` of `by`) of the map
at axis `2`, then the head. -/
def cccGotF : Noun :=
  C (A 7) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 701)
    (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6)
    (C (A 0) (A 126))) (C (A 0) (A 2)))))))) (C (A 0) (A 2)))

theorem ccc_big : cccBig =
    C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) cccSccF)) (C (A 7) (C (C (A 10) (C
      (C (A 0x3f7f6) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3)))
      (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) cccCsiF)) (C (A 7) (C (C (A 10)
      (C (C (A 0xfefe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3)))
      (C cccGotF (C (A 0) (A 254)))))))))))))))))) := by
  kernel_rfl

/-- The subject of the miss branch: `s` is `~`, then the gate's core. -/
noncomputable def cccS0 (b : Bell) (g : Gen (TreapMap mugF)) (x : GenRest) (ctx : Noun) : Noun :=
  C (A 0) (C cccBat (C b.toNoun (compCore g x ctx)))

/-- The rest with `cache` a cell `[nary mono sccs rest]` (`sccs` at axis `14`). -/
def ccRest (NR MO SC RS SO SS : Noun) : GenRest := ⟨C NR (C MO (C SC RS)), SO, SS⟩

/-- **`+callee-compiled` on a miss** (README Gaps 19 (g)), given the gates of
`+scc-of` (`hscc`: `[NS SC']`) and `+compile-scc-in` (`hcsi`: `[M CA']`, on
`new-scc` `NS` with `sccs.cache` set to `SC'`) on the subjects of the
branch, and the entry of `b` in `M`: `[nb gen]` with `cache` set to `CA'`. -/
theorem ccc_miss (hc : CompIn ctx) (b : Bell) (g : Gen (TreapMap mugF)) {NR MO SC RS SO SS NS SC' M CA' u nd : Noun}
    (hmiss : getF mugF b.toNoun NR = some (A 0))
    (hscc : nock (cccS0 b g (ccRest NR MO SC RS SO SS) ctx) cccSccF = some (C NS SC'))
    (hcsi : nock (C NS (cccS0 b g (ccRest NR MO SC' RS SO SS) ctx)) cccCsiF = some (C M CA'))
    (hg : getF mugF b.toNoun M = some (C (A 0) u)) (hu : slot? 2 u = some nd) :
    nock (C cccBat (C b.toNoun (compCore g (ccRest NR MO SC RS SO SS) ctx))) cccBat
      = some (C nd (genNoun g ⟨CA', SO, SS⟩)) := by
  have hgt := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ b.toNoun NR _ hmiss
  have hgo := got_gate (mug := mugF) layer2 ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ b.toNoun M u hg
  unfold cccS0 at hscc hcsi
  simp only [compCore, genNoun, ccRest] at hscc hcsi ⊢
  conv => lhs; arg 2; rw [ccc_bat, ccc_big]
  generalize cccSccF = SF at hscc ⊢
  generalize cccCsiF = CF at hcsi ⊢
  simp [nock_exec, hc, by_arm, by.arm_at, by.get.arm_at, get_arm, hgt, hscc, hcsi, by.got.arm_at, got_arm, hgo, hu,
    cccGotF]

/-- **The compile of a miss, as one fact**: the gates of `+scc-of` and
`+compile-scc-in` on the subjects of the branch, for every `gen`, and the
entry of `b` with need `nb` in the map `+compile-scc-in` returns. -/
def CccMiss (ctx : Noun) (b : Bell) (nb : NeedOrd) (NR MO SC RS SO SS CA' : Noun) : Prop :=
  ∃ NS SC' M u, (∀ g, nock (cccS0 b g (ccRest NR MO SC RS SO SS) ctx) cccSccF = some (C NS SC')) ∧
    (∀ g, nock (C NS (cccS0 b g (ccRest NR MO SC' RS SO SS) ctx)) cccCsiF = some (C M CA')) ∧
    getF mugF b.toNoun M = some (C (A 0) u) ∧ slot? 2 u = some nb.toNoun

/-- **What `+callee-need` does with no ring**: a read-only case (`NeedRead`)
with the rest unchanged, or `b` outside `scc` with a miss in `nary.cache`
(axis `2` of `cache`) and the compile `CccMiss`, with the new `cache`. -/
inductive NeedStep (ctx : Noun) (x : GenRest) (b : Bell) (nb : NeedOrd) : GenRest → Prop where
  | read : NeedRead ctx x b nb → NeedStep ctx x b nb x
  | miss {S NR MO SC RS CA' : Noun} : slot? 12 ctx = some S → hasInF mugF b.toNoun S = some false →
      x.cache = C NR (C MO (C SC RS)) → getF mugF b.toNoun NR = some (A 0) →
      CccMiss ctx b nb NR MO SC RS x.soft x.sofs CA' → NeedStep ctx x b nb ⟨CA', x.soft, x.sofs⟩

/-- **`+callee-need` with no ring on every case**: `nb` and the rest `x'` of
`NeedStep` (`cne_read` on the read-only cases, `ccc_miss` on a miss). -/
theorem cne_step (h7 : slot? 7 ctx = some compK) (b : Bell) (nb : NeedOrd) (x x' : GenRest)
    (hcole : ∃ cole, slot? 6846 ctx = some cole ∧ getF mugF b.toNoun cole = some (A 0))
    (hhot : ∃ jh, slot? 54 ctx = some jh) (hs : NeedStep ctx x b nb x') (g : Gen (TreapMap mugF)) :
    nock (C cneBat (C b.toNoun (compCore g x ctx))) cneBat = some (C nb.toNoun (genNoun g x')) := by
  cases hs with
  | read hr => exact cne_read h7 b nb x hcole hhot hr g
  | @miss S NR MO SC RS CA' hS hh hx hmiss hm =>
    obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
    obtain ⟨cole, hcl, hgc⟩ := hcole
    obtain ⟨jh, hjh⟩ := hhot
    obtain ⟨NS, SC', M, u, hscc, hcsi, hg, hu⟩ := hm
    have hgt := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ b.toNoun cole (A 0) hgc
    have hhs := has_in_gate (mug := mugF) layer2 gorIn_morIn_layer2.1 b.toNoun S false hh
    obtain ⟨xc, xs, xf⟩ := x
    simp only at hx
    subst hx
    have hcc := ccc_miss hc b g hmiss (hscc g) (hcsi g) hg hu
    have hD := ccc_at
    simp only [compCore, ccRest] at hcc
    conv => lhs; rw [cne_bat]
    generalize cccBat = CB at hcc hD
    simp only [compCore]
    generalize comp.door = Dr at hcc hD ⊢
    simp [nock_exec, hc, hcl, by_arm, by.arm_at, by.get.arm_at, get_arm, hgt, hjh, biff_arm,
      biff.arm_at, biff_gate_nil, hS, in_arm, in.arm_at, in.has.arm_at, has_in_arm, hhs, loob, hD, hcc]

/-! ## Steps `0` to `6` of the call with the rest threaded -/

/-- **What the call reads, with `+callee-need` changing the rest** from `x`
to `x'`: `CallNounM` with `need` returning `genNoun g x'`, and `sure`, `sof`
read at `x'` (they run after the need push). -/
structure CallNounMT (msup : Option Nomm) (ctx : Noun) (p q : Nomm) (b : Bell) (nb : NeedOrd) (sur : Noun)
    (x x' : GenRest) (mono SOF : Noun) : Prop where
  cole : ∃ cole, slot? 6846 ctx = some cole ∧ getF mugF b.toNoun cole = some (A 0)
  hot : ∃ jh, slot? 54 ctx = some jh
  need : ∀ g : Gen (TreapMap mugF),
    nock (C cneBat (C b.toNoun (compCore g x ctx))) cneBat = some (C nb.toNoun (genNoun g x'))
  sure : ∀ g : Gen (TreapMap mugF), nock (C csuBat (C b.toNoun (compCore g x' ctx))) csuBat = some sur
  sof : ∀ (g : Gen (TreapMap mugF)) (SV SN PV goalN regionN : Noun),
    nock (C sur (C SV (C SN (C nb.toNoun (C (A 0) (C PV (crSubj mono (crdN p q b) goalN regionN
      (unitNoun Nomm.toNoun msup) (compCore g x' ctx)))))))) crDKc6 = some SOF

/-- With the rest unchanged it is `CallNounM`. -/
theorem callNounMT_of_m {msup : Option Nomm} {p q : Nomm} {b : Bell} {nb : NeedOrd} {sur : Noun} {x : GenRest}
    {mono SOF : Noun} (h : CallNounM msup ctx p q b nb sur x mono SOF) : CallNounMT msup ctx p q b nb sur x x mono SOF :=
  ⟨h.cole, h.hot, h.need, h.sure, h.sof⟩

/-- **Steps `0` to `6` with the rest threaded**: `crd_head6M` where the need
push moves the rest to `x'`; the steps after it see `x'`. -/
theorem crd_head6MT (h7 : slot? 7 ctx = some compK) (msup : Option Nomm) (p q : Nomm) (b : Bell) (nb : NeedOrd)
    (sur : Noun) (x x' : GenRest) (mono SOF : Noun) (hn : CallNounMT msup ctx p q b nb sur x x' mono SOF) (PV goalN : Noun)
    (region : List Nat) (g : Gen (TreapMap mugF)) :
    nock (C PV (crSubj mono (crdN p q b) goalN (listNoun A region) (unitNoun Nomm.toNoun msup) (compCore g x ctx)))
      crDCall
      = (needOrdAllocRegs nb g).bind fun r => nock (crdS6m SOF sur (listNoun A (flattenNeed r.1)) r.1.toNoun nb.toNoun PV
          (crSubj mono (crdN p q b) goalN (listNoun A region) (unitNoun Nomm.toNoun msup) (compCore r.2 x' ctx)))
          crDKr7 := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  obtain ⟨cole, hcole, hgc⟩ := hn.cole
  obtain ⟨jh, hjh⟩ := hn.hot
  have hgt := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ b.toNoun cole (A 0) hgc
  have hne := hn.need g
  have hnoar := noar_gate ctx x' nb g
  have hD1 := cne_at
  have hD2 := noar_at
  have hD3 := comp_fn_at
  have hD4 := csu_at
  rw [crdk_eq]
  simp only [crSubj, compCore, crdS6m] at hne hnoar ⊢
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
    generalize comp.door = Dr at hne hnoar hD1 hD2 hD3 hD4 hfn hsu hsof ⊢
    unfold crDKr0 crDKr1 crDKc1 crDKr2 crDKc2 crDKr3 crDKc3 crDKr4 crDKc4 crDKr5 crDKc5 crDKr6
    simp [nock_exec, crdN, hc, hcole, by_arm, by.arm_at, by.get.arm_at, get_arm, hgt, hD1, hne, hD2, noarHint, h7, hnoar, hD3,
      comp_fn_arm, hfn, hjh, biff_arm, biff.arm_at, biff_gate_nil, hD4, hsu, hsof]

/-- `CallNounMT` from the facts: no ring, `jets-hot`, `NeedStep` to `x'`,
`SureNoun` at `x'`, and the push of `sof` at `x'`. -/
theorem callNounMT_of (h7 : slot? 7 ctx = some compK) {env : CallEnv} {msup : Option Nomm} {p q : Nomm} {b : Bell}
    {nb : NeedOrd} {x x' : GenRest} {mono SOF : Noun}
    (hcole : ∃ cole, slot? 6846 ctx = some cole ∧ getF mugF b.toNoun cole = some (A 0))
    (hhot : ∃ jh, slot? 54 ctx = some jh) (hs : NeedStep ctx x b nb x') (hsu : SureNoun env b x')
    (hsof : ∀ (g : Gen (TreapMap mugF)) (SV SN PV goalN regionN : Noun),
      nock (C (env.sure b).toNoun (C SV (C SN (C nb.toNoun (C (A 0) (C PV (crSubj mono (crdN p q b) goalN regionN
        (unitNoun Nomm.toNoun msup) (compCore g x' ctx)))))))) crDKc6 = some SOF) :
    CallNounMT msup ctx p q b nb (env.sure b).toNoun x x' mono SOF :=
  ⟨hcole, hhot, cne_step h7 b nb x x' hcole hhot hs, csu_gate (comp_ctx_pill ctx h7).1 env b x' hsu, hsof⟩

/-! ## The run link threading the rest -/

/-- **The run link against `R` threading the rest** (README Gaps 19 (g)): at
every rest `x` with `X x mono sup` the pill's run returns the model's result
with some rest `x'` in the relation `Y x x'` (the rest a miss leaves). -/
def CompRunAtXT (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)) (ctx : Noun)
    (X : GenRest → Noun → Noun → Prop) (Y : GenRest → GenRest → Prop) (n : Nomm) (goal : CGoalL CSet)
    (region : List Nat) (g : Gen (TreapMap mugF)) : Prop :=
  ∀ (x : GenRest) (mono sup : Noun), x.NoSoft → X x mono sup → ∃ x', Y x x' ∧
    nock (crSubj mono n.toNoun goal.toNoun (listNoun A region) sup (compCore g x ctx)) crDol
      = (R n goal region g).map fun p => C p.1.goal.toNoun (genNoun p.2 x')

/-- **A run with no miss is a threaded run with `x' = x`**: every
`CompRunAtX` is a `CompRunAtXT` for a reflexive `Y`. -/
theorem crxt_of_x {R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)}
    {X : GenRest → Noun → Noun → Prop} {Y : GenRest → GenRest → Prop} (hY : ∀ x, Y x x) {n : Nomm}
    {goal : CGoalL CSet} {region : List Nat} {g : Gen (TreapMap mugF)} (h : CompRunAtX R ctx X n goal region g) :
    CompRunAtXT R ctx X Y n goal region g :=
  fun x mono sup hx hX => ⟨x, hY x, h x mono sup hx hX⟩

/-- A threaded run whose `Y` is equality is the old link. -/
theorem crx_of_xt_eq {R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)}
    {X : GenRest → Noun → Noun → Prop} {n : Nomm} {goal : CGoalL CSet} {region : List Nat}
    {g : Gen (TreapMap mugF)} (h : CompRunAtXT R ctx X (· = ·) n goal region g) : CompRunAtX R ctx X n goal region g := by
  intro x mono sup hx hX
  obtain ⟨x', rfl, e⟩ := h x mono sup hx hX
  exact e

end Compiler
end Formalization
