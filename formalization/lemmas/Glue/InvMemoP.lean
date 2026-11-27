import lemmas.Glue.InvMemo
import lemmas.Compiler.PokeLink

/-!
# Glue: `InvSM` on track P's route (`anaArmP`, `enc fl`, `cor`)

Track P replaced `anaArm` by `anaArmP` (`+ska-cole-update`, mismatch P2; no
answer on an atom formula, P4) and `gap_of_comp` by `gap_of_armP`.  The
memo part of the analysis is the same, so the M8 reconciliation of
`Glue/InvMemo.lean` carries over:

* `anaArmP_memo`, `pokeS_memoP`: every poke keeps `MemoNoCallees`;
* `gap_of_armPM`: the shapes of `contract`, `invKept`, `invStart` for
  `liftPoke (enc fl) (pokeS A)` on `liftInv (enc fl) (InvSM lib ref)`, with
  `invStart` at the pill's `cor` (`cor_enc`);
* `fullAnswers_of_cgMP`: `FullAnswers (pokeS A) (InvSM lib ref)` from
  `CgHalts`, `BakeEnds`, `RootAnswers` at the fuel `anaFuel`, and
  `halting_of_cgMP` its lift by `enc fl`: so all four model fields of `Gap`
  are on ONE invariant on this route.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Ana Bake PokeM Compiler Pill Hoon

section
variable {M : Type → Type → Type} [Treap M] {Map : Type → Type} [HoonMap Map] {J H CR R : Type}
variable (A : Arms M Map J H CR)

/-- **`anaArmP` keeps `MemoNoCallees`** (`memoNoCallees_skaPoke`). -/
theorem anaArmP_memo {env : Env R} {jet : H → J → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB M → J → Nat} {bf : BEnv M → Nat} {regOf : J → R}
    {jetsOf : H → J → R → LongB M → LongB M → J} {newOf : R → Noun} {s f : Noun} {L : LongB M} {j : J} {hot : H}
    {r : Bell × LongB M × J × Noun}
    (hm : MemoNoCallees L.memo) (h : anaArmP env jet fold frozen fuel bf regOf jetsOf newOf s f L j hot = some r) :
    MemoNoCallees r.2.1.memo := by
  unfold anaArmP at h
  cases f with
  | atom _ => cases h
  | cell _ _ =>
    simp only [skaPokeB] at h
    obtain ⟨r1, h1, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨⟨pr, dats, memo', rd, reg'⟩, h2, h3⟩ := Option.bind_eq_some_iff.mp h1
    obtain ⟨bg, -, rfl⟩ := Option.map_eq_some_iff.mp h3
    exact memoNoCallees_skaPoke hm h2

/-- **Every poke of the model keeps `MemoNoCallees`**, on track P's arm. -/
theorem pokeS_memoP {env : Env R} {jet : H → J → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB M → J → Nat} {bf : BEnv M → Nat} {regOf : J → R}
    {jetsOf : H → J → R → LongB M → LongB M → J} {newOf : R → Noun}
    (hA : A.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf) :
    ∀ (st : CSt M Map J H CR) ov p st', MemoNoCallees st.long.memo → pokeS A st ov = some (p, st') →
      MemoNoCallees st'.long.memo := by
  intro st ov p st' hm h
  cases ov with
  | full s f =>
    simp only [pokeS] at h
    obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
    rw [hA] at hr
    have hm' : MemoNoCallees r.2.1.memo := anaArmP_memo hm hr
    split at h
    · cases h; exact hm'
    · obtain ⟨q, hq, he⟩ := Option.map_eq_some_iff.mp h
      cases he
      rw [compileStep_long A hq]
      exact hm'
  | dire b m =>
    simp only [pokeS] at h
    obtain ⟨q, hq, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    rw [compileStep_long A hq]
    exact hm
  | jets q =>
    simp only [pokeS] at h
    obtain ⟨r, -, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    exact hm
  | fast rs q =>
    simp only [pokeS] at h
    obtain ⟨r, -, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    exact hm

/-- `anaArm_someN` for `anaArmP` on a cell formula. -/
theorem anaArmP_someN {lib : Lib} {env : Env R} {jet : H → J → (Bell → Option Datum) → R → Bell → Bool}
    {fold frozen : Bool} {fuel : Noun → Noun → LongB M → J → Nat} {bf : BEnv M → Nat} {regOf : J → R}
    (jetsOf : H → J → R → LongB M → LongB M → J) (newOf : R → Noun)
    (ha : AnaEndsN lib env fuel regOf) (hb : BakeEnds lib env jet fold frozen fuel bf regOf)
    (hf : FinalEnds lib env jet fold frozen fuel regOf) {s f1 f2 : Noun} {L : LongB M} {j : J} (hot : H)
    (hI : InvB lib L) (hm : MemoNoCallees L.memo) :
    ∃ r, anaArmP env jet fold frozen fuel bf regOf jetsOf newOf s (C f1 f2) L j hot = some r := by
  obtain ⟨⟨pr, dats, memo', rd, reg'⟩, h1⟩ := ha s (C f1 f2) L j hI hm
  obtain ⟨stb, h2⟩ := hb s (C f1 f2) L j hot pr dats memo' rd reg' hI h1
  obtain ⟨out, h3⟩ := hf s (C f1 f2) L j hot pr dats memo' rd reg' hI h1 _ stb h2
  simp only [anaEnv] at h2 h3
  simp only [anaArmP, skaPokeB, h1, Option.bind_some, bakeGraph, h2, h3, Option.map_some]
  exact ⟨_, rfl⟩

/-- **`FullAnswers` on `InvSM` on track P's arm**, with the analysis fuel
`anaFuel`, from `CgHalts`, `BakeEnds` and `RootAnswers`. -/
theorem fullAnswers_of_cgMP {lib : Lib} {ref : Ref M Map J H} {env : Env R}
    {jet : H → J → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool} {bf : BEnv M → Nat}
    {regOf : J → R} {jetsOf : H → J → R → LongB M → LongB M → J} {newOf : R → Noun}
    (hC : CompHyp A lib ref)
    (hA : A.skaPoke = anaArmP env jet fold frozen (anaFuel env regOf) bf regOf jetsOf newOf)
    (hcg : CgHalts (M := M) lib env regOf)
    (hb : BakeEnds lib env jet fold frozen (anaFuel env regOf) bf regOf) (hr : RootAnswers lib A ref) :
    FullAnswers (pokeS A) (InvSM lib ref) := by
  intro st s f1 f2 hI
  obtain ⟨r, hk⟩ := anaArmP_someN jetsOf newOf (anaEndsN_of_halts (anaHalts_of_cgHalts hcg)) hb
    (finalEnds_always lib env jet fold frozen _ regOf) st.hot hI.1.1 hI.2 (s := s) (f1 := f1) (f2 := f2)
    (j := st.jets)
  rw [← hA] at hk
  have hAna := anaHyp_of_armP A (lib := lib) hA
  obtain ⟨hB, -, -⟩ := hAna.ana s (C f1 f2) st.long st.jets st.hot r hk hI.1.1
  have hok1 : CacheOK ref r.2.1 r.2.2.1 st.hot st.cache :=
    ⟨fun b x hx => hC.stable s (C f1 f2) _ _ _ r b true x hk hI.1.1 (hI.1.2.1 b x hx),
     fun b x hx => hC.stable s (C f1 f2) _ _ _ r b false x hk hI.1.1 (hI.1.2.2 b x hx)⟩
  have hI1 : InvS lib ref ({ st with long := r.2.1, jets := r.2.2.1 } : CSt M Map J H CR) := ⟨hB, hok1⟩
  simp only [pokeS, hk, Option.bind_some]
  split
  · exact ⟨_, rfl⟩
  · rename_i hj
    obtain ⟨x, hx⟩ := hr st s (C f1 f2) r hI.1 hk hj
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (hC.answers _ r.1 true x hI1 hx)
    exact ⟨_, by rw [hp]; rfl⟩

end

/-- **The shapes of `contract`, `invKept`, `invStart` on `InvSM`** for
`liftPoke (enc fl) (pokeS A)` with `anaArmP` (`gap_of_armP` with the memo's
lack of callees in the invariant); `invStart` at the pill's `cor`. -/
theorem gap_of_armPM (A : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)) {lib : Lib}
    {ref : Ref FinMap (TreapMap mugF) Noun Noun} {R : Type} {env : Env R}
    {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → R}
    {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}
    (hC : CompHyp A lib ref) (hA : A.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf)
    (fl : Flags) :
    Sound lib (liftPoke (enc fl) (pokeS A)) (liftInv (enc fl) (InvSM lib ref)) ∧
    (∀ t ov p t', liftInv (enc fl) (InvSM lib ref) t → ¬ HotOvum ov →
      liftPoke (enc fl) (pokeS A) t ov = some (p, t') → liftInv (enc fl) (InvSM lib ref) t') ∧
    liftInv (enc fl) (InvSM lib ref) cor := by
  have hS : Sound lib (pokeS A) (InvSM lib ref) :=
    sound_and (pokeS_sound A hC (anaHyp_of_armP A hA)) (pokeS_memoP A hA)
  have hK : ∀ st ov p st', InvSM lib ref st → ¬ HotOvum ov → pokeS A st ov = some (p, st') →
      InvSM lib ref st' := fun st ov p st' hI hh hp =>
    ⟨pokeS_invKept A hC (anaHyp_of_armP A hA) st ov p st' hI.1 hh hp, pokeS_memoP A hA st ov p st' hI.2 hp⟩
  exact ⟨sound_lift (enc_inj fl) hS, invKept_lift (enc_inj fl) hK,
    ⟨emptySt, (cor_enc fl).symm, invSM_init lib ref jets0 (Noun.atom 0) (Noun.atom 0, Noun.atom 0)⟩⟩

/-- **`halting` on `InvSM` for `enc fl`**: `fullAnswers_of_cgMP` lifted. -/
theorem halting_of_cgMP (A : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)) {lib : Lib}
    {ref : Ref FinMap (TreapMap mugF) Noun Noun} {R : Type} {env : Env R}
    {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
    {bf : BEnv FinMap → Nat} {regOf : Noun → R}
    {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}
    (hC : CompHyp A lib ref)
    (hA : A.skaPoke = anaArmP env jet fold frozen (anaFuel env regOf) bf regOf jetsOf newOf)
    (hcg : CgHalts (M := FinMap) lib env regOf)
    (hb : BakeEnds lib env jet fold frozen (anaFuel env regOf) bf regOf) (hr : RootAnswers lib A ref) (fl : Flags) :
    FullAnswers (liftPoke (enc fl) (pokeS A)) (liftInv (enc fl) (InvSM lib ref)) :=
  fullAnswers_lift (enc_inj fl) (fullAnswers_of_cgMP A hC hA hcg hb hr)

end Glue
end SkaModel
end Formalization
