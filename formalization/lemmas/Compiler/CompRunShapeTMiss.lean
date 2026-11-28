import lemmas.Compiler.CompRunShapeMemberT
import lemmas.Compiler.CompCalleeComp

/-!
# `ShapeCallT` from track K's `NeedStep` on the rests of the bunt `gen` (track A, 2026-11-28)

The sweeps run `+run-shape` on the bunt `gen` with a cache `CA` (the rest `memY CA`).  Its noun is
track K's `genNoun` of `memG st` (the bunt with `id-gen` from `st`) at the rest `memX CA st`
(`memY_genNoun`), so K's `cne_step` (`+callee-need` on a read, or on a miss whose compile `CccMiss`
returns the cache `x'.cache`) is the need push of `ShapeCallT` with `y' = memY x'.cache`, and K's
`SureNoun` at `x'` is `+callee-sure` there.

* `memG`, `memX`, `memY_genNoun`, `needStep_rest` (a `NeedStep` keeps `soft` and `sofs`).
* **`rsNeed_of_step`**: the need push from `NeedStep`.
* `rsSure_of`: `+callee-sure` on `memY CA` from `SureNoun`.
* **`shapeCallT_of_step`**: `ShapeCallT` at `memY CA` from `NeedStep` at every state, with the rest
  it returns in `E` and `Rl`, `SureNoun` there, and the clauses of `ShapeCall` that do not read `gen`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun}

/-- The bunt `gen` with `id-gen` from `st`. -/
def memG (st : RSt CSet) : Gen (TreapMap mugF) := { genEntry with id := st.idg }

/-- The rest of track K of the bunt with the cache `CA` and `sofs` from `st`. -/
noncomputable def memX (CA : Noun) (st : RSt CSet) : GenRest := ⟨CA, A 0, HoonSet.toNoun st.sofs⟩

theorem memY_genNoun (CA : Noun) (st : RSt CSet) : rsGenNoun st (memY CA) = genNoun (memG st) (memX CA st) := by
  simp [rsGenNoun, genNoun, memY, memG, memX, genEntry]

theorem memY_door (CA : Noun) (st : RSt CSet) : rsDoor st (memY CA) ctx = compCore (memG st) (memX CA st) ctx := by
  simp only [rsDoor, compCore, memY_genNoun]

theorem needStep_rest {x x' : GenRest} {b : Bell} {nb : NeedOrd} (h : NeedStep ctx x b nb x') :
    x'.soft = x.soft ∧ x'.sofs = x.sofs := by
  cases h <;> exact ⟨rfl, rfl⟩

theorem memX_of_step {CA : Noun} {st : RSt CSet} {x' : GenRest} {b : Bell} {nb : NeedOrd}
    (h : NeedStep ctx (memX CA st) b nb x') : x' = memX x'.cache st := by
  obtain ⟨h1, h2⟩ := needStep_rest h
  obtain ⟨c, s, f⟩ := x'
  simp only [memX] at h1 h2 ⊢
  rw [h1, h2]

/-- **The need push from track K's `NeedStep`**: a read keeps the rest, a miss returns the bunt
`gen` with the cache the compile returned. -/
theorem rsNeed_of_step (h7 : slot? 7 ctx = some compK) (b : Bell) (nb : NeedOrd) (CA : Noun) (st : RSt CSet)
    {x' : GenRest} (hcole : ∃ cole, slot? 6846 ctx = some cole ∧ getF mugF b.toNoun cole = some (A 0))
    (hhot : ∃ jh, slot? 54 ctx = some jh) (hs : NeedStep ctx (memX CA st) b nb x') :
    nock (C cneBat (C b.toNoun (rsDoor st (memY CA) ctx))) cneBat
      = some (C nb.toNoun (rsGenNoun st (memY x'.cache))) := by
  have h := cne_step h7 b nb (memX CA st) x' hcole hhot hs (memG st)
  rw [memY_door, h, memY_genNoun, ← memX_of_step hs]

/-- `+callee-sure` on the bunt `gen` with the cache `CA` from track K's `SureNoun` (it reads
`sure.cache` only). -/
theorem rsSure_of (hc : CompIn ctx) (env : CallEnv) (b : Bell) (CA : Noun) (hsu : ∀ st, SureNoun env b (memX CA st))
    (st : RSt CSet) :
    nock (C csuBat (C b.toNoun (rsDoor st (memY CA) ctx))) csuBat = some (env.sure b).toNoun := by
  rw [memY_door]
  exact csu_gate hc env b _ (hsu st) (memG st)

/-- **`ShapeCallT` at the bunt `gen` with the cache `CA` from track K's facts**: at every state the
need push is a `NeedStep` (a read, or a miss with its compile) to a rest `x'` whose bunt rest is in
`E` and `Rl`, with `SureNoun` there; the other clauses are those of `ShapeCall`. -/
theorem shapeCallT_of_step (h7 : slot? 7 ctx = some compK) {env : CallEnv} {jet : Bell → Bool}
    {xcod : Bell → Option Nomm} {E : RsRest → Prop} {Rl : RsRest → RsRest → Prop} {p q : Nomm} {b : Bell}
    {k : Option Noun} {sup : Option Nomm} {CA : Noun}
    (hcole : ∃ cole, slot? 6846 ctx = some cole ∧ getF mugF b.toNoun cole = some (A 0))
    (hhot : ∃ jh, slot? 54 ctx = some jh) (hjet : jet b = false)
    (hneed : konstCell k = false → ∃ nb, env.need b = some nb ∧ ∀ st : RSt CSet, ∃ x',
      NeedStep ctx (memX CA st) b nb x' ∧ Rl (memY CA) (memY x'.cache) ∧ E (memY x'.cache) ∧
      ∀ st' : RSt CSet, SureNoun env b (memX x'.cache st'))
    (hsk : konstCell k = true → ∃ sur : NeedOrd, ∀ st : RSt CSet,
      nock (C csuBat (C b.toNoun (rsDoor st (memY CA) ctx))) csuBat = some sur.toNoun)
    (hsoft : ∀ ned : NeedOrd, (konstCell k = true → ned = NeedOrd.this) →
      (konstCell k = false → env.need b = some ned) →
      softTest (shapeEnvOfA jet xcod env) p q b k ned (env.sure b) sup ≠ Option.none) :
    ShapeCallT ctx (shapeEnvOfA jet xcod env) E Rl p q b k sup (memY CA) where
  need hk := by
    obtain ⟨nb, e, hn⟩ := hneed hk
    refine ⟨nb, e, fun st => ?_⟩
    obtain ⟨x', hs, hR, hE, hsu⟩ := hn st
    exact ⟨memY x'.cache, hR, hE, rsNeed_of_step h7 b nb CA st hcole hhot hs,
      rsSure_of (comp_ctx_pill ctx h7).1 env b x'.cache hsu⟩
  sureK := hsk
  cole := hcole
  hot := hhot
  jet := hjet
  soft := hsoft

end Compiler
end Formalization
