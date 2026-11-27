import lemmas.Ska.AnaEnds
import lemmas.Ska.PokeAna

/-!
# Glue: the invariant with `MemoNoCallees` (mismatch M8 of `LEDGER.md`)

`CgHalts`, `AnaHalts` and `AnaEndsN` assume that the memo has no callees
(`MemoNoCallees`), but it is not a field of `InvB` or `InvS`, so
`fullAnswers_of_cg` took `∀ L, InvB lib L → MemoNoCallees L.memo` as a
hypothesis (false in general: `InvB` does not say it).  Here:

* `InvSM lib ref st`: `InvS lib ref st` and `MemoNoCallees st.long.memo`;
* `invSM_init`: it holds of the bunt state (`invS_init`,
  `memoNoCallees_empty`);
* `pokeS_memo`: every poke of the model keeps `MemoNoCallees` (`%full`
  through `memoNoCallees_skaPoke`, the other ovums do not touch the memo),
  so `sound_and` gives `Sound` on `InvSM` from `Sound` on `InvS`;
* `gap_of_compM`: the three shapes of `gap_of_comp` on `InvSM`;
* `fullAnswers_of_cgM`: `FullAnswers (pokeS A) (InvSM lib ref)` from
  `CgHalts`, `BakeEnds`, `RootAnswers`, without the extra hypothesis.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Ana Bake PokeM

variable {M : Type → Type → Type} [Treap M] {Map : Type → Type} [HoonMap Map] {J H CR R : Type}

/-- **The invariant with the memo's lack of callees.** -/
def InvSM (lib : Lib) (ref : Ref M Map J H) (st : CSt M Map J H CR) : Prop :=
  InvS lib ref st ∧ MemoNoCallees st.long.memo

/-- **`InvSM` holds of the bunt state.** -/
theorem invSM_init (lib : Lib) (ref : Ref M Map J H) (jets : J) (hot : H) (rest : CR) :
    InvSM lib ref (⟨⟨Treap.empty, Treap.empty, Treap.empty⟩, jets, hot,
      ⟨Treap.empty, Treap.empty, Treap.empty, rest⟩⟩ : CSt M Map J H CR) :=
  ⟨invS_init lib ref jets hot rest, memoNoCallees_empty⟩

/-- **A conjunct kept by every poke is added to a sound invariant.** -/
theorem sound_and {σ : Type} {Map' : Type → Type} [HoonMap Map'] {lib : Lib}
    {poke : σ → Ovum → Option (Prod Map' × σ)} {Inv Q : σ → Prop}
    (h : Sound lib poke Inv) (hq : ∀ st ov p st', Q st → poke st ov = some (p, st') → Q st') :
    Sound lib poke (fun st => Inv st ∧ Q st) where
  dire := fun st b m p st' hI hp =>
    ⟨⟨(h.dire st b m p st' hI.1 hp).1, hq st _ p st' hI.2 hp⟩, (h.dire st b m p st' hI.1 hp).2⟩
  full := fun st s f p st' hI hp =>
    ⟨⟨(h.full st s f p st' hI.1 hp).1, hq st _ p st' hI.2 hp⟩, (h.full st s f p st' hI.1 hp).2⟩
  dire_code := fun st b m p st' hI hp => h.dire_code st b m p st' hI.1 hp
  full_code := fun st s f p st' hI hp => h.full_code st s f p st' hI.1 hp

variable (A : Arms M Map J H CR)

/-- `compileStep` changes the cache only. -/
theorem compileStep_long {st : CSt M Map J H CR} {b : Bell} {m : Bool} {x : Straight Map × CSt M Map J H CR}
    (h : compileStep A st b m = some x) : x.2.long = st.long := by
  unfold compileStep at h
  obtain ⟨r, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.mp h
  rfl

/-- **The analysis arm keeps `MemoNoCallees`** (`memoNoCallees_skaPoke`). -/
theorem anaArm_memo {env : Env R} {jet : H → J → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB M → J → Nat} {bf : BEnv M → Nat} {regOf : J → R} {jetsOf : J → R → J}
    {newOf : R → Noun} {s f : Noun} {L : LongB M} {j : J} {hot : H} {r : Bell × LongB M × J × Noun}
    (hm : MemoNoCallees L.memo) (h : anaArm env jet fold frozen fuel bf regOf jetsOf newOf s f L j hot = some r) :
    MemoNoCallees r.2.1.memo := by
  unfold anaArm skaPokeB at h
  obtain ⟨r1, h1, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨⟨pr, dats, memo', rd, reg'⟩, h2, h3⟩ := Option.bind_eq_some_iff.mp h1
  obtain ⟨bg, -, rfl⟩ := Option.map_eq_some_iff.mp h3
  exact memoNoCallees_skaPoke hm h2

/-- **Every poke of the model keeps `MemoNoCallees`.** -/
theorem pokeS_memo {env : Env R} {jet : H → J → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB M → J → Nat} {bf : BEnv M → Nat} {regOf : J → R} {jetsOf : J → R → J}
    {newOf : R → Noun} (hA : A.skaPoke = anaArm env jet fold frozen fuel bf regOf jetsOf newOf) :
    ∀ (st : CSt M Map J H CR) ov p st', MemoNoCallees st.long.memo → pokeS A st ov = some (p, st') →
      MemoNoCallees st'.long.memo := by
  intro st ov p st' hm h
  cases ov with
  | full s f =>
    simp only [pokeS] at h
    obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
    rw [hA] at hr
    have hm' : MemoNoCallees r.2.1.memo := anaArm_memo hm hr
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

/-- **The shapes of `Gap.contract`, `Gap.invKept`, `Gap.invStart` on
`InvSM`**: `gap_of_comp` with the memo's lack of callees in the invariant. -/
theorem gap_of_compM {lib : Lib} {ref : Ref M Map J H} {env : Env R}
    {jet : H → J → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB M → J → Nat} {bf : BEnv M → Nat} {regOf : J → R} {jetsOf : J → R → J}
    {newOf : R → Noun}
    (hC : CompHyp A lib ref) (hA : A.skaPoke = anaArm env jet fold frozen fuel bf regOf jetsOf newOf)
    (enc : CSt M Map J H CR → Noun) (henc : ∀ a b, enc a = enc b → a = b) :
    Sound lib (liftPoke enc (pokeS A)) (liftInv enc (InvSM lib ref)) ∧
    (∀ t ov p t', liftInv enc (InvSM lib ref) t → ¬ HotOvum ov → liftPoke enc (pokeS A) t ov = some (p, t') →
      liftInv enc (InvSM lib ref) t') ∧
    ∀ jets hot rest, liftInv enc (InvSM lib ref)
      (enc ⟨⟨Treap.empty, Treap.empty, Treap.empty⟩, jets, hot, ⟨Treap.empty, Treap.empty, Treap.empty, rest⟩⟩) := by
  have hS : Sound lib (pokeS A) (InvSM lib ref) :=
    sound_and (pokeS_sound A hC (anaHyp_of_arm A hA)) (pokeS_memo A hA)
  have hK : ∀ st ov p st', InvSM lib ref st → ¬ HotOvum ov → pokeS A st ov = some (p, st') →
      InvSM lib ref st' := fun st ov p st' hI hh hp =>
    ⟨pokeS_invKept A hC (anaHyp_of_arm A hA) st ov p st' hI.1 hh hp, pokeS_memo A hA st ov p st' hI.2 hp⟩
  exact ⟨sound_lift henc hS, invKept_lift henc hK, fun jets hot rest => ⟨_, rfl, invSM_init lib ref jets hot rest⟩⟩

/-- `anaArm_some` with `AnaEndsN` and the memo's lack of callees. -/
theorem anaArm_someN {lib : Lib} {env : Env R} {jet : H → J → (Bell → Option Datum) → R → Bell → Bool}
    {fold frozen : Bool} {fuel : Noun → Noun → LongB M → J → Nat} {bf : BEnv M → Nat} {regOf : J → R}
    (jetsOf : J → R → J) (newOf : R → Noun)
    (ha : AnaEndsN lib env fuel regOf) (hb : BakeEnds lib env jet fold frozen fuel bf regOf)
    (hf : FinalEnds lib env jet fold frozen fuel regOf) {s f : Noun} {L : LongB M} {j : J} (hot : H)
    (hI : InvB lib L) (hm : MemoNoCallees L.memo) :
    ∃ r, anaArm env jet fold frozen fuel bf regOf jetsOf newOf s f L j hot = some r := by
  obtain ⟨⟨pr, dats, memo', rd, reg'⟩, h1⟩ := ha s f L j hI hm
  obtain ⟨stb, h2⟩ := hb s f L j hot pr dats memo' rd reg' hI h1
  obtain ⟨out, h3⟩ := hf s f L j hot pr dats memo' rd reg' hI h1 _ stb h2
  simp only [anaEnv] at h2 h3
  simp only [anaArm, skaPokeB, h1, Option.bind_some, bakeGraph, h2, h3, Option.map_some]
  exact ⟨_, rfl⟩

/-- **`FullAnswers` on `InvSM`** with the analysis fuel `anaFuel`, from
`CgHalts`, `BakeEnds` and `RootAnswers` (the proof of `fullAnswers_of`, with
`AnaEndsN` at the memo the invariant carries). -/
theorem fullAnswers_of_cgM {lib : Lib} {ref : Ref M Map J H} {env : Env R}
    {jet : H → J → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool} {bf : BEnv M → Nat}
    {regOf : J → R} {jetsOf : J → R → J} {newOf : R → Noun}
    (hC : CompHyp A lib ref)
    (hA : A.skaPoke = anaArm env jet fold frozen (anaFuel env regOf) bf regOf jetsOf newOf)
    (hcg : CgHalts (M := M) lib env regOf)
    (hb : BakeEnds lib env jet fold frozen (anaFuel env regOf) bf regOf) (hr : RootAnswers lib A ref) :
    FullAnswers (pokeS A) (InvSM lib ref) := by
  intro st s f1 f2 hI
  obtain ⟨r, hk⟩ := anaArm_someN jetsOf newOf (anaEndsN_of_halts (anaHalts_of_cgHalts hcg)) hb
    (finalEnds_always lib env jet fold frozen _ regOf) st.hot hI.1.1 hI.2 (s := s) (f := C f1 f2) (j := st.jets)
  rw [← hA] at hk
  have hAna := anaHyp_of_arm A (lib := lib) hA
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

end Glue
end SkaModel
end Formalization
