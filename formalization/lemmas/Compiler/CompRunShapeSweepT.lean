import lemmas.Compiler.CompRunShapeClassF
import lemmas.Compiler.CompRunShapeTMiss
import lemmas.Compiler.CompSccLoopSweepA
import lemmas.Compiler.CompUnaryDirE

/-!
# The sweep call of `member` with callees compiled inside `+run-shape` (track A, 2026-11-28)

Track I's `memSweepCall_of_A` (`CompSccLoopSweepA.lean`) links one `%must` / `%may` call of
`member` through the old branch theorem, whose direct calls must HIT `nary.cache` at the cache
`CA1` of `+inlined` (`SweepCallLeft.callee`).  Here the call is linked through the threaded branch
`memShape_branchTF`, with the rests

* `E := SwE env RR P S x CA1`: the rest is the bunt rest `memY CA2` of a cache `CA2` with track
  K's `SweepMissK env RR P S x CA1 CA2` (`Ext`, `AgreeIP` with the bells in progress and `S`, the
  rest predicate `RR`, the keys of `S` in `nary` / `sure` as at `CA1`);
* `Rl := fun _ _ => True` (everything is carried by `E`, whose base point is `CA1`).

`SweepMissK` is reflexive at a `QK` cache and transitive (`sweepMiss_refl`, `sweepMiss_trans`).
What is left of `ShapeOKM` per callee outside the SCC is K's leaf **`SweepMissStep`**: at a cache
`CA2` of `E`, a miss of `b` in `nary.cache` is compiled (`CccMiss` at the rest of the run, `soft`
`~` and `sofs` of the run's state) to a cache `CA'` with `SweepMissK env RR P S x CA2 CA'` and a hit
of `b`.  A member reads `map-local` / `top`; a hit reads the cache (`hit_of_agreeIP` at `QK` of
`CA2`, `sweepMiss_keeps`).

* `pureKnown_of_callCode`: `CallCode` gives `PureKnown`, so the soft test returns
  (`softTest_total`) from `SfClosed (made p sup)` and `less ≠ %void` alone.
* `ShapeOKQT Q Qm`: `ShapeOKM` with per-call predicates; **`shapeOKM_of_QT`**.
* `SweepCallee`, `SweepCallLeftT`, `MeanLeftT`: what one direct call / `%mean` takes.
* **`needStep_sweep`**, `sureK_sweep`, **`shapeCallT_sweep`**, **`meanNeedT_sweep`**.
* `SweepLeftT`, **`memSweepCall_of_AT`**: track I's `MemSweepCall` at `RK` (the cache the branch
  leaves is `CA2`, with `QK` and the members' `sure` entries by `sweepMiss_keeps`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## K's `SweepMissK` as the rests of the run -/

theorem sweepMiss_refl {env : CallEnv} {RR : GenRest → Prop} {P : Noun → Prop} {S : Noun} {x : GenRest} {CA : Noun}
    (hQ : QK env RR P S x CA) : SweepMissK env RR P S x CA CA :=
  ⟨ext_refl _, hQ.1, hQ.2.2.1, fun NR1 REST1 h => ⟨NR1, REST1, h, fun _ _ => rfl⟩,
    fun SU1 h => ⟨SU1, h, fun _ _ => rfl⟩⟩

theorem sweepMiss_trans {env : CallEnv} {RR : GenRest → Prop} {P : Noun → Prop} {S : Noun} {x : GenRest}
    {CA1 CA2 CA3 : Noun} (h1 : SweepMissK env RR P S x CA1 CA2) (h2 : SweepMissK env RR P S x CA2 CA3) :
    SweepMissK env RR P S x CA1 CA3 := by
  obtain ⟨e1, -, -, n1, s1⟩ := h1
  obtain ⟨e2, a2, r2, n2, s2⟩ := h2
  refine ⟨ext_trans e1 e2, a2, r2, fun NR1 REST1 hc => ?_, fun SU1 hs => ?_⟩
  · obtain ⟨NR2, REST2, hc2, hk2⟩ := n1 NR1 REST1 hc
    obtain ⟨NR3, REST3, hc3, hk3⟩ := n2 NR2 REST2 hc2
    exact ⟨NR3, REST3, hc3, fun k hk => (hk3 k hk).trans (hk2 k hk)⟩
  · obtain ⟨SU2, hs2, hk2⟩ := s1 SU1 hs
    obtain ⟨SU3, hs3, hk3⟩ := s2 SU2 hs2
    exact ⟨SU3, hs3, fun k hk => (hk3 k hk).trans (hk2 k hk)⟩

/-- **The rests of a sweep's member run**: the bunt rest of a cache `CA2` that `SweepMissK`
relates to the cache `CA1` of `+inlined`. -/
abbrev SwE (env : CallEnv) (RR : GenRest → Prop) (P : Noun → Prop) (S : Noun) (x : GenRest) (CA1 : Noun) :
    RsRest → Prop :=
  fun y => ∃ CA2, y = memY CA2 ∧ SweepMissK env RR P S x CA1 CA2

/-- **Track K's leaf for a miss inside a sweep call** (the outside callee `b`, its need `nb`): at
every cache `CA2` of `SwE .. CA1`, a miss of `b` in `nary.cache` is compiled (`CccMiss` at the
rest of the run: `soft` `~`, `sofs` of the run's state) to a cache `CA'` with `SweepMissK` from
`CA2` (`Ext`, `AgreeIP`, `RR`, the keys of `S` unchanged) and a hit of `b`. -/
def SweepMissStep (ctx : Noun) (env : CallEnv) (RR : GenRest → Prop) (P : Noun → Prop) (S : Noun) (x : GenRest)
    (CA1 : Noun) (b : Bell) (nb : NeedOrd) : Prop :=
  ∀ (CA2 : Noun) (st : RSt CSet) (NR MO SC RS : Noun), SweepMissK env RR P S x CA1 CA2 →
    CA2 = C NR (C MO (C SC RS)) → getF mugF b.toNoun NR = some (A 0) →
    ∃ CA', CccMiss ctx b nb NR MO SC RS (A 0) (HoonSet.toNoun st.sofs) CA' ∧ SweepMissK env RR P S x CA2 CA' ∧
      ∃ N' u, slot? 2 CA' = some N' ∧ getF mugF b.toNoun N' = some (C (A 0) u)

/-! ## `CallCode` gives `PureKnown` -/

/-- **The callees on `+hinted`'s walk have `pure` flags** when they have code entries. -/
theorem pureKnown_of_callCode (cod : Noun) (env : ShapeEnv) :
    ∀ n, CallCode cod (shapeCE env) n → PureKnown env.pure n
  | Nomm.n0 _, _ => trivial
  | Nomm.n1 _, _ => trivial
  | Nomm.n3 p, h => pureKnown_of_callCode cod env p h
  | Nomm.n4 p, h => pureKnown_of_callCode cod env p h
  | Nomm.cons p q, ⟨hp, hq⟩ => ⟨pureKnown_of_callCode cod env p hp, pureKnown_of_callCode cod env q hq⟩
  | Nomm.n5 p q, ⟨hp, hq⟩ => ⟨pureKnown_of_callCode cod env p hp, pureKnown_of_callCode cod env q hq⟩
  | Nomm.n6 p q r, ⟨hp, hq, hr⟩ =>
    ⟨pureKnown_of_callCode cod env p hp, pureKnown_of_callCode cod env q hq, pureKnown_of_callCode cod env r hr⟩
  | Nomm.n7 p q, ⟨hp, hq⟩ => ⟨pureKnown_of_callCode cod env p hp, pureKnown_of_callCode cod env q hq⟩
  | Nomm.n10 _ v q, ⟨hv, hq⟩ => ⟨pureKnown_of_callCode cod env v hv, pureKnown_of_callCode cod env q hq⟩
  | Nomm.n2 p q Option.none, _ => trivial
  | Nomm.n2 p q (some (b, k)), ⟨h0, hp, hq⟩ => by
    refine ⟨fun e => ?_, pureKnown_of_callCode cod env p hp, pureKnown_of_callCode cod env q hq⟩
    have h2 := h0.2
    simp [shapeCE, e] at h2
  | Nomm.n11s _ q _, h => pureKnown_of_callCode cod env q h
  | Nomm.n11d _ hh q _, ⟨h1, h2⟩ => ⟨pureKnown_of_callCode cod env hh h1, pureKnown_of_callCode cod env q h2⟩
  | Nomm.n12 _ _, _ => trivial
  | Nomm.mean _ _ _ _ _, _ => trivial

/-! ## `ShapeOKM` from per-call predicates -/

/-- `ShapeOKM` with a per-call predicate `Q` (direct calls) and `Qm` (`%mean`). -/
def ShapeOKQT (Q : Nomm → Nomm → Bell → Option Noun → Option Nomm → Prop) (Qm : Bell → Prop) :
    Option Nomm → Nomm → Prop
  | sup, Nomm.n2 p q (some (b, k)) => Q p q b k sup ∧ ShapeOKQT Q Qm sup p ∧ ShapeOKQT Q Qm sup q
  | sup, Nomm.n2 p q Option.none => ShapeOKQT Q Qm sup p ∧ ShapeOKQT Q Qm sup q
  | sup, Nomm.n7 p q => ShapeOKQT Q Qm sup p ∧ ShapeOKQT Q Qm (some p) q
  | sup, Nomm.n6 p q r => ShapeOKQT Q Qm sup p ∧ ShapeOKQT Q Qm sup q ∧ ShapeOKQT Q Qm sup r
  | sup, Nomm.n3 p => ShapeOKQT Q Qm sup p
  | sup, Nomm.n4 p => ShapeOKQT Q Qm sup p
  | sup, Nomm.cons p q => ShapeOKQT Q Qm sup p ∧ ShapeOKQT Q Qm sup q
  | sup, Nomm.n5 p q => ShapeOKQT Q Qm sup p ∧ ShapeOKQT Q Qm sup q
  | sup, Nomm.n10 _ v q => ShapeOKQT Q Qm sup v ∧ ShapeOKQT Q Qm sup q
  | sup, Nomm.n11s _ q _ => ShapeOKQT Q Qm sup q
  | sup, Nomm.n11d _ h q _ => ShapeOKQT Q Qm sup h ∧ ShapeOKQT Q Qm sup q
  | sup, Nomm.n12 p q => ShapeOKQT Q Qm sup p ∧ ShapeOKQT Q Qm sup q
  | sup, Nomm.mean p b q _ _ => Qm b ∧ ShapeOKQT Q Qm sup p ∧ ShapeOKQT Q Qm sup q
  | _, _ => True

/-- **`ShapeOKM` from the per-call predicates**, on the class `RsClsF` and `CallCode` (which give
`PureKnown` of the subterms of each direct call). -/
theorem shapeOKM_of_QT {ctx : Noun} {env : ShapeEnv} {cod : Noun} {E : RsRest → Prop}
    {Rl : RsRest → RsRest → Prop} {Q : Nomm → Nomm → Bell → Option Noun → Option Nomm → Prop} {Qm : Bell → Prop}
    (hQ : ∀ p q b k sup, Q p q b k sup → PureKnown env.pure p → PureKnown env.pure q →
      ∀ y, E y → ShapeCallT ctx env E Rl p q b k sup y)
    (hQm : ∀ b k, Qm b → ∀ y, E y → MeanNeedT ctx env E Rl b k y) :
    ∀ (n : Nomm) (sup : Option Nomm), RsClsF env cod n → CallCode cod (shapeCE env) n → ShapeOKQT Q Qm sup n →
      ShapeOKM ctx env E Rl sup n
  | Nomm.n0 _, _, _, _, _ => trivial
  | Nomm.n1 _, _, _, _, _ => trivial
  | Nomm.n3 p, sup, hn, hc, h => shapeOKM_of_QT hQ hQm p sup hn hc h
  | Nomm.n4 p, sup, hn, hc, h => shapeOKM_of_QT hQ hQm p sup hn hc h
  | Nomm.n7 p q, sup, ⟨hp, hq⟩, ⟨cp, cq⟩, ⟨h1, h2⟩ =>
    ⟨shapeOKM_of_QT hQ hQm p sup hp cp h1, shapeOKM_of_QT hQ hQm q (some p) hq cq h2⟩
  | Nomm.cons p q, sup, ⟨hp, hq⟩, ⟨cp, cq⟩, ⟨h1, h2⟩ =>
    ⟨shapeOKM_of_QT hQ hQm p sup hp cp h1, shapeOKM_of_QT hQ hQm q sup hq cq h2⟩
  | Nomm.n5 p q, sup, ⟨hp, hq⟩, ⟨cp, cq⟩, ⟨h1, h2⟩ =>
    ⟨shapeOKM_of_QT hQ hQm p sup hp cp h1, shapeOKM_of_QT hQ hQm q sup hq cq h2⟩
  | Nomm.n10 _ v q, sup, ⟨hv, hq⟩, ⟨cv, cq⟩, ⟨h1, h2⟩ =>
    ⟨shapeOKM_of_QT hQ hQm v sup hv cv h1, shapeOKM_of_QT hQ hQm q sup hq cq h2⟩
  | Nomm.n6 p q r, sup, ⟨hp, hq, hr, _⟩, ⟨cp, cq, cr⟩, ⟨h1, h2, h3⟩ =>
    ⟨shapeOKM_of_QT hQ hQm p sup hp cp h1, shapeOKM_of_QT hQ hQm q sup hq cq h2,
      shapeOKM_of_QT hQ hQm r sup hr cr h3⟩
  | Nomm.n2 p q Option.none, sup, ⟨hp, hq⟩, ⟨_, cp, cq⟩, ⟨h1, h2⟩ =>
    ⟨shapeOKM_of_QT hQ hQm p sup hp cp h1, shapeOKM_of_QT hQ hQm q sup hq cq h2⟩
  | Nomm.n2 p q (some (b, k)), sup, ⟨hp, hq⟩, ⟨_, cp, cq⟩, ⟨h0, h1, h2⟩ =>
    ⟨hQ p q b k sup h0 (pureKnown_of_callCode cod env p cp) (pureKnown_of_callCode cod env q cq),
      shapeOKM_of_QT hQ hQm p sup hp cp h1, shapeOKM_of_QT hQ hQm q sup hq cq h2⟩
  | Nomm.n11s _ q _, sup, ⟨hq, _⟩, cq, h => shapeOKM_of_QT hQ hQm q sup hq cq h
  | Nomm.n11d _ hh q _, sup, ⟨h1, h2, _⟩, ⟨c1, c2⟩, ⟨g1, g2⟩ =>
    ⟨shapeOKM_of_QT hQ hQm hh sup h1 c1 g1, shapeOKM_of_QT hQ hQm q sup h2 c2 g2⟩
  | Nomm.n12 p q, sup, ⟨hp, hq, cp, cq⟩, _, ⟨h1, h2⟩ =>
    ⟨shapeOKM_of_QT hQ hQm p sup hp cp h1, shapeOKM_of_QT hQ hQm q sup hq cq h2⟩
  | Nomm.mean p b q _ k, sup, ⟨hp, hq, _, cp, cq, _⟩, _, ⟨hm, h1, h2⟩ =>
    ⟨hQm b k hm, shapeOKM_of_QT hQ hQm p sup hp cp h1, shapeOKM_of_QT hQ hQm q sup hq cq h2⟩

/-! ## One callee of a sweep's member run -/

/-- **The callee of a direct call or `%mean` in a sweep's member run**: a member, or a bell not in
progress (`¬ P`) with a need `nb` in `env` and track K's miss leaf `SweepMissStep` for it. -/
def SweepCallee (scc : List Noun) (ctx : Noun) (env : CallEnv) (RR : GenRest → Prop) (P : Noun → Prop) (S : Noun)
    (x : GenRest) (CA1 : Noun) (b : Bell) : Prop :=
  b.toNoun ∈ scc ∨ (¬ P b.toNoun ∧ ∃ nb, env.need b = some nb ∧ SweepMissStep ctx env RR P S x CA1 b nb)

/-- **What one direct call of a sweep's member run takes**: its callee (`SweepCallee`), no ring
(`cole`), not jetted (`jet`), and on a key `~` `SfClosed` of `(made p sup)` and `less ≠ %void`
(the soft test then returns, `softTest_total`). -/
structure SweepCallLeftT (scc : List Noun) (jet : Bell → Bool) (xcod : Bell → Option Nomm) (env : CallEnv)
    (RR : GenRest → Prop) (P : Noun → Prop) (S : Noun) (x : GenRest) (CA1 ctx : Noun)
    (p q : Nomm) (b : Bell) (k : Option Noun) (sup : Option Nomm) : Prop where
  callee : SweepCallee scc ctx env RR P S x CA1 b
  cole : ∃ cole, slot? 6846 ctx = some cole ∧ getF mugF b.toNoun cole = some (A 0)
  jet : jet b = false
  soft : k = Option.none → SfClosed xcod 3 (made p sup) ∧ b.less ≠ Sock.void

/-- **What one `%mean` of a sweep's member run takes**: its callee and no ring. -/
structure MeanLeftT (scc : List Noun) (env : CallEnv) (RR : GenRest → Prop) (P : Noun → Prop) (S : Noun)
    (x : GenRest) (CA1 ctx : Noun) (b : Bell) : Prop where
  callee : SweepCallee scc ctx env RR P S x CA1 b
  cole : ∃ cole, slot? 6846 ctx = some cole ∧ getF mugF b.toNoun cole = some (A 0)

section
variable {r : RealCfg} {xs : ShapeX} {order : List Noun} {kids : Noun → List Noun} {env : CallEnv}
  {RR : GenRest → Prop} {P : Noun → Prop} {S : Noun} {x : GenRest} {ls : St Noun NeedOrd}
  {top : Noun → NeedOrd} {SCC LONG JH ML TOP B CA1 : Noun}

/-- **The need push of a sweep's callee at a rest of `SwE`**: a member reads `map-local` / `top`; a
callee outside hits at `CA2` (`QK` there) or misses and is compiled (K's `SweepMissStep`); the rest
it returns is in `SwE`, and `+callee-sure` there reads `envSw`'s `sure`. -/
theorem needStep_sweep (hre : r.env = env) (hrs : r.scc = tapList S)
    (hset : ∀ k, hasInF mugF k SCC = some (decide (k ∈ r.scc)))
    (hml : MlExact ls.ml ML) (hT : TopH top TOP)
    (hQ1 : QK env RR P S x CA1) (hS1 : SureHolds r.scc ls.sure CA1)
    {b : Bell} (hb : SweepCallee r.scc (memDCtx SCC LONG JH ML TOP B) env RR P S x CA1 b)
    {CA2 : Noun} (hM : SweepMissK env RR P S x CA1 CA2) :
    ∃ nb, (envSw r xs order kids top ls).need b = some nb ∧ ∀ st : RSt CSet, ∃ x',
      NeedStep (memDCtx SCC LONG JH ML TOP B) (memX CA2 st) b nb x' ∧ SweepMissK env RR P S x CA1 x'.cache ∧
      ∀ st' : RSt CSet, SureNoun (envSw r xs order kids top ls) b (memX x'.cache st') := by
  have hS12 : slot? 12 (memDCtx SCC LONG JH ML TOP B) = some SCC := by simp [memDCtx, nock_exec]
  have hS1' : SureHolds (tapList S) ls.sure CA1 := by rw [← hrs]; exact hS1
  obtain ⟨hQ2, hS2⟩ := sweepMiss_keeps hQ1 hS1' hM
  by_cases hbm : b.toNoun ∈ r.scc
  · have hin : hasInF mugF b.toNoun SCC = some true := by rw [hset]; simp [hbm]
    refine ⟨(ls.ml b.toNoun).getD (top b.toNoun), by simp [envSw, envView, hbm, viewN], fun st =>
      ⟨memX CA2 st, NeedStep.read (needRead_memberT hml hT hin _), hM, fun st' => ?_⟩⟩
    obtain ⟨S0, h31, hall⟩ := hS2
    refine ⟨S0, h31, ?_⟩
    have hs : (envSw r xs order kids top ls).sure b = (ls.sure b.toNoun).getD NeedOrd.none := by
      simp [envSw, envView, hbm, viewS, cfgRealShape, cfgReal]
    rw [hs]
    rcases hall _ (by rw [← hrs]; exact hbm) with ⟨v, hv, hg⟩ | ⟨hv, hg⟩
    · left; rw [hv]; exact hg
    · right; rw [hv]; exact ⟨hg, rfl⟩
  · rcases hb with hm | ⟨hnp, nb, hnb, hleaf⟩
    · exact absurd hm hbm
    have hin : hasInF mugF b.toNoun SCC = some false := by rw [hset]; simp [hbm]
    have hag : (envSw r xs order kids top ls).need b = env.need b ∧
        (envSw r xs order kids top ls).sure b = env.sure b := by
      simp [envSw, envView, hbm, hre]
    have hnbR : (envSw r xs order kids top ls).need b = some nb := by rw [hag.1, hnb]
    have hnot : ¬ (P b.toNoun ∨ b.toNoun ∈ tapList S) := by
      rintro (h1 | h1)
      · exact hnp h1
      · exact hbm (hrs ▸ h1)
    have hit : ∀ CA, QK env RR P S x CA → ∀ NR u, slot? 2 CA = some NR → getF mugF b.toNoun NR = some (C (A 0) u) →
        ∀ st : RSt CSet, NeedRead (memDCtx SCC LONG JH ML TOP B) (memX CA st) b nb ∧
          SureNoun (envSw r xs order kids top ls) b (memX CA st) := by
      intro CA hQ NR u hNR hu st
      obtain ⟨hr, hs⟩ := hit_of_agreeIP (x := ⟨CA, x.soft, x.sofs⟩) hS12 hin hnbR hag hQ.1 hnot hNR hu
      exact ⟨needRead_cache (x := ⟨CA, x.soft, x.sofs⟩) rfl hr, sureNoun_cache (x := ⟨CA, x.soft, x.sofs⟩) rfl hs⟩
    refine ⟨nb, hnbR, fun st => ?_⟩
    obtain ⟨-, NR, MO, SC, INL, SU, hc, hnr, -, -, -⟩ := hQ2.1
    change CA2 = cacheN NR MO SC INL SU at hc
    have hNR : slot? 2 CA2 = some NR := by rw [hc, cacheN_slot2]
    rcases getF_cases (k := b.toNoun) hnr with h0 | ⟨u, hu⟩
    · obtain ⟨CA', hmiss, hM', N', u', hN', hu'⟩ := hleaf CA2 st NR MO SC (C INL SU) hM hc h0
      have hM2 := sweepMiss_trans hM hM'
      obtain ⟨hQ3, -⟩ := sweepMiss_keeps hQ1 hS1' hM2
      exact ⟨memX CA' st, NeedStep.miss hS12 hin hc h0 hmiss, hM2, fun st' => (hit CA' hQ3 N' u' hN' hu' st').2⟩
    · exact ⟨memX CA2 st, NeedStep.read (hit CA2 hQ2 NR u hNR hu st).1, hM,
        fun st' => (hit CA2 hQ2 NR u hNR hu st').2⟩

/-- **`+callee-sure` on a cell key at a rest of `SwE`** returns some `need-ordered`: a member's
`sure` entry, an outside entry (`AgreeIP`: `env.sure`), or none (`[%none ~]`). -/
theorem sureK_sweep (hrs : r.scc = tapList S) (hQ1 : QK env RR P S x CA1) (hS1 : SureHolds r.scc ls.sure CA1)
    {b : Bell} (hb : SweepCallee r.scc (memDCtx SCC LONG JH ML TOP B) env RR P S x CA1 b)
    {CA2 : Noun} (hM : SweepMissK env RR P S x CA1 CA2) :
    ∃ sur : NeedOrd, ∀ st : RSt CSet,
      nock (C csuBat (C b.toNoun (rsDoor st (memY CA2) (memDCtx SCC LONG JH ML TOP B)))) csuBat
        = some sur.toNoun := by
  have h7 : slot? 7 (memDCtx SCC LONG JH ML TOP B) = some compK := rfl
  have hc : CompIn (memDCtx SCC LONG JH ML TOP B) := (comp_ctx_pill _ h7).1
  have hS1' : SureHolds (tapList S) ls.sure CA1 := by rw [← hrs]; exact hS1
  obtain ⟨hQ2, hS2⟩ := sweepMiss_keeps hQ1 hS1' hM
  by_cases hbm : b.toNoun ∈ tapList S
  · obtain ⟨S0, h31, hall⟩ := hS2
    let e0 : CallEnv := { env with sure := fun _ => (ls.sure b.toNoun).getD NeedOrd.none }
    refine ⟨e0.sure b, fun st => rsSure_of hc e0 b CA2 (fun st' => ⟨S0, h31, ?_⟩) st⟩
    rcases hall _ hbm with ⟨v, hv, hg⟩ | ⟨hv, hg⟩
    · left
      have e : e0.sure b = v := by simp [e0, hv]
      rw [e]; exact hg
    · right; exact ⟨hg, by simp [e0, hv]⟩
  · have hnp : ¬ P b.toNoun := by
      rcases hb with hm | ⟨hnp, -⟩
      · exact absurd (hrs ▸ hm) hbm
      · exact hnp
    obtain ⟨-, NR, MO, SC, INL, SU, hcc, -, hsu, -, hsa⟩ := hQ2.1
    have h31 : slot? 31 CA2 = some SU := by
      change CA2 = cacheN NR MO SC INL SU at hcc; rw [hcc, cacheN_slot31]
    rcases getF_cases (k := b.toNoun) hsu with h0 | ⟨v, hv⟩
    · let e0 : CallEnv := { env with sure := fun _ => NeedOrd.none }
      exact ⟨e0.sure b, fun st => rsSure_of hc e0 b CA2 (fun st' => ⟨SU, h31, Or.inr ⟨h0, rfl⟩⟩) st⟩
    · have hv' := (hsa b v hv (fun h => h.elim hnp hbm)).1
      refine ⟨env.sure b, fun st => rsSure_of hc env b CA2 (fun st' => ⟨SU, h31, Or.inl ?_⟩) st⟩
      rw [hv, hv']

/-- **`ShapeCallT` at every rest of `SwE`** from `SweepCallLeftT` and `PureKnown` of the subterms. -/
theorem shapeCallT_sweep (hre : r.env = env) (hrs : r.scc = tapList S)
    (hset : ∀ k, hasInF mugF k SCC = some (decide (k ∈ r.scc)))
    (hml : MlExact ls.ml ML) (hT : TopH top TOP)
    (hQ1 : QK env RR P S x CA1) (hS1 : SureHolds r.scc ls.sure CA1)
    {p q : Nomm} {b : Bell} {k : Option Noun} {sup : Option Nomm}
    (h : SweepCallLeftT r.scc xs.jet xs.cod env RR P S x CA1 (memDCtx SCC LONG JH ML TOP B) p q b k sup)
    (hpp : PureKnown (shapeEnvOfA xs.jet xs.cod (envSw r xs order kids top ls)).pure p)
    (hpq : PureKnown (shapeEnvOfA xs.jet xs.cod (envSw r xs order kids top ls)).pure q) :
    ∀ y, SwE env RR P S x CA1 y →
      ShapeCallT (memDCtx SCC LONG JH ML TOP B) (shapeEnvOfA xs.jet xs.cod (envSw r xs order kids top ls))
        (SwE env RR P S x CA1) (fun _ _ => True) p q b k sup y := by
  rintro y ⟨CA2, rfl, hM⟩
  have h7 : slot? 7 (memDCtx SCC LONG JH ML TOP B) = some compK := rfl
  have hhot : ∃ jh, slot? 54 (memDCtx SCC LONG JH ML TOP B) = some jh := ⟨JH, by simp [memDCtx, nock_exec]⟩
  refine shapeCallT_of_step h7 h.cole hhot h.jet (fun _ => ?_) (fun _ => sureK_sweep hrs hQ1 hS1 h.callee hM)
    (fun ned _ _ => softTest_total _ p q b k ned _ sup fun hk => ⟨(h.soft hk).1, (h.soft hk).2, hpp, hpq⟩)
  obtain ⟨nb, hnb, hst⟩ := needStep_sweep (xs := xs) (order := order) (kids := kids) hre hrs hset hml hT hQ1 hS1
    h.callee hM
  exact ⟨nb, hnb, fun st => by
    obtain ⟨x', h1, h2, h3⟩ := hst st
    exact ⟨x', h1, trivial, ⟨x'.cache, rfl, h2⟩, h3⟩⟩

/-- **`MeanNeedT` at every rest of `SwE`** from `MeanLeftT`. -/
theorem meanNeedT_sweep (hre : r.env = env) (hrs : r.scc = tapList S)
    (hset : ∀ k, hasInF mugF k SCC = some (decide (k ∈ r.scc)))
    (hml : MlExact ls.ml ML) (hT : TopH top TOP)
    (hQ1 : QK env RR P S x CA1) (hS1 : SureHolds r.scc ls.sure CA1)
    {b : Bell} (h : MeanLeftT r.scc env RR P S x CA1 (memDCtx SCC LONG JH ML TOP B) b) (k : Option Noun) :
    ∀ y, SwE env RR P S x CA1 y →
      MeanNeedT (memDCtx SCC LONG JH ML TOP B) (shapeEnvOfA xs.jet xs.cod (envSw r xs order kids top ls))
        (SwE env RR P S x CA1) (fun _ _ => True) b k y := by
  rintro y ⟨CA2, rfl, hM⟩ _
  have h7 : slot? 7 (memDCtx SCC LONG JH ML TOP B) = some compK := rfl
  have hhot : ∃ jh, slot? 54 (memDCtx SCC LONG JH ML TOP B) = some jh := ⟨JH, by simp [memDCtx, nock_exec]⟩
  obtain ⟨nb, hnb, hst⟩ := needStep_sweep (xs := xs) (order := order) (kids := kids) hre hrs hset hml hT hQ1 hS1
    h.callee hM
  refine ⟨nb, hnb, fun st => ?_⟩
  obtain ⟨x', h1, h2, -⟩ := hst st
  exact ⟨memY x'.cache, trivial, ⟨x'.cache, rfl, h2⟩, rsNeed_of_step h7 b nb CA2 st h.cole hhot h1⟩

end

/-! ## One sweep call of `member` -/

/-- **What one `%must` / `%may` call of `member` takes, a callee compiled inside the run allowed**
(`SweepLeft` with the class `RsClsF`, and per call `SweepCallLeftT` / `MeanLeftT` at the cache
`CA1` of `+inlined`). -/
def SweepLeftT (r : RealCfg) (xs : ShapeX) (order : List Noun) (kids : Noun → List Noun) (inl : Noun → Option Nomm)
    (env : CallEnv) (RR : GenRest → Prop) (P : Noun → Prop) (S : Noun) (x : GenRest)
    (mode : Mode) (top : Noun → NeedOrd) (TOP : Noun) (st : St Noun NeedOrd)
    (SCC CODE LSR JH b ML CACHE : Noun) : Prop :=
  ∃ (cape : Cape) (DATA FOL : Noun) (nm : Nomm) (fuel : Nat), b = C (C cape.toNoun DATA) FOL ∧
    r.info b = ⟨nm, cape, DATA, fuel⟩ ∧ ∃ CA1,
    nock (C inlBody (C (C b (C (C CODE LSR) (C JH CACHE))) compK)) inlBody = some (C nm.toNoun CA1) ∧
    InlKeep inl CACHE CA1 ∧
    RsClsF (shapeEnvOfA xs.jet xs.cod (envSw r xs order kids top st)) CODE nm ∧
    CallCode CODE (shapeCE (shapeEnvOfA xs.jet xs.cod (envSw r xs order kids top st))) nm ∧
    ShapeOKQT (SweepCallLeftT r.scc xs.jet xs.cod env RR P S x CA1 (memDCtx SCC (C CODE LSR) JH ML TOP b))
      (MeanLeftT r.scc env RR P S x CA1 (memDCtx SCC (C CODE LSR) JH ML TOP b)) Option.none nm ∧
    (lazeReal xs mode (envSw r xs order kids top st) ⟨nm, cape, DATA, fuel⟩).isSome

/-- **`MemSweepCall` from the threaded branch** (`RK`, `outC := fun _ => []`): the run's rests are
`SwE env (RK SC0 inl) P S x CA1` (`QK` at `CA1` by `eM_start`), `memShape_branchTF` returns at a
cache `CA2` with `SweepMissK` from `CA1`, and `sweepMiss_keeps` gives `QK` and the members' `sure`
entries there. -/
theorem memSweepCall_of_AT {r : RealCfg} {xs : ShapeX} {order : List Noun} {kids : Noun → List Noun}
    {nout : Noun → NeedOrd} {env : CallEnv} {SC0 : Noun} {inl : Noun → Option Nomm} {P : Noun → Prop}
    {S : Noun} {x : GenRest} {mode : Mode} {top : Noun → NeedOrd} {TOP : Noun} {st : St Noun NeedOrd} {keep : Bool}
    {DN KIDS ML0 CB SCC CODE LSR JH CACHE0 b ML CACHE : Noun}
    (hm : mode = Mode.must ∨ mode = Mode.may)
    (hrs : r.scc = tapList S) (hPS : ∀ k ∈ tapList S, ¬ P k) (hre : r.env = env)
    (hset : ∀ k, hasInF mugF k SCC = some (decide (k ∈ r.scc)))
    (hcn : CodeNomms xs.cod CODE) (hT : TopH top TOP)
    (hR : LoopRS r.scc (fun _ => []) nout (QK env (RK SC0 inl) P S x) st.ml st.sure ML CACHE)
    (h : SweepLeftT r xs order kids inl env (RK SC0 inl) P S x mode top TOP st SCC CODE LSR JH b ML CACHE) :
    MemSweepCall r xs order kids (fun _ => []) nout env (RK SC0 inl) P S x mode top TOP st keep DN KIDS ML0 CB
      SCC CODE LSR JH CACHE0 b ML CACHE := by
  obtain ⟨cape, DATA, FOL, nm, fuel, hb, hinfo, CA1, hinl, hik, hcls, hcc, hcalls, hlr⟩ := h
  subst hb
  have hsh : SureHolds (tapList S) st.sure CACHE := by rw [← hrs]; exact hR.1.2.1
  have hQ0 : QK env (RKP SC0 inl (fun _ => False)) P S x CACHE :=
    qK_congr (fun y => rKP_empty.symm) hR.1.2.2.2
  obtain ⟨-, -, hQ1', hS1⟩ := eM_start (Pf := fun _ => False) hPS hQ0 hsh hik
  have hQ1 : QK env (RK SC0 inl) P S x CA1 := qK_congr (fun y => rKP_empty) hQ1'
  have hS1' : SureHolds r.scc st.sure CA1 := by rw [hrs]; exact hS1
  have hml : MlExact st.ml ML := hR.1.1
  obtain ⟨⟨col, sur⟩, hlr'⟩ := Option.isSome_iff_exists.1 hlr
  have hs := shapeOKM_of_QT (E := SwE env (RK SC0 inl) P S x CA1) (Rl := fun _ _ => True)
    (fun p q b' k sup hq hpp hpq => shapeCallT_sweep hre hrs hset hml hT hQ1 hS1' hq hpp hpq)
    (fun b' k hq => meanNeedT_sweep hre hrs hset hml hT hQ1 hS1' hq k) nm Option.none hcls hcc hcalls
  obtain ⟨st1, y1, -, ⟨CA2, rfl, hM⟩, hbr⟩ := memShape_branchTF mode hm xs.jet xs.cod (envSw r xs order kids top st)
    cape DATA FOL nm fuel keep SCC (C CODE LSR) JH ML TOP CA1 (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0) rfl
    (cod := CODE) (by simp [nock_exec]) hcn hcls hcc (SwE env (RK SC0 inl) P S x CA1) (fun _ _ => True)
    ⟨fun _ => trivial, fun _ _ => trivial⟩ ⟨CA1, rfl, sweepMiss_refl hQ1⟩ hs col sur hlr'
  obtain ⟨hQ2, hS2⟩ := sweepMiss_keeps hQ1 hS1 hM
  obtain ⟨-, C1, C2, C3, C4, SU, hc2, -⟩ := hQ2.1
  change CA2 = cacheN C1 C2 C3 C4 SU at hc2
  subst hc2
  exact ⟨cape, DATA, FOL, nm, fuel, rfl, hinfo, CA1, hinl, col, sur, _,
    (memShapeBranch_iffA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).2 hbr, C1, C2, C3, C4, SU, memY_cache st1 _, hQ2,
    by rw [hrs]; exact hS2, fun b' _ k hk => by simp at hk⟩

end Compiler
end Formalization
