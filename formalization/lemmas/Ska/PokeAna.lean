import lemmas.Ska.PokeModel

/-!
# `+ska-poke` as the analysis arm of `+poke`

`PokeModel.lean` takes `+ska-poke` as the parameter `Arms.skaPoke` and asks
`AnaHyp` of it.  This file gives that parameter as the model: `anaArm` is
`skaPokeB` (`PokeBake.lean`) on the root identity `[&+sub fol]`, as `+poke`
makes it for `%full`, with the registrations read from and written back into
the jets state (`regOf`, `jetsOf`, `newOf`, which this file leaves abstract,
as `PokeModel.lean` leaves the jets state) and the fuel of the fuelled model
as a parameter.

`anaHyp_of_bakes` proves `AnaHyp` for it from `PokeBakes`, HImp of every
poke from a state that satisfies `InvB`; `anaHyp_of_meet` from `PokeSites`,
the same with `SitesMeet` (`BakeImp.lean`) in place of HImp.  What it needs
besides `skaPokeB_sound`: the root sock `&+sub` is well formed, normal and
not `%void`, the root bell has the poke's formula by construction, and the
root datum's code requirement holds of `sub` (`skaPoke_root_fits`: a run's
code requirement is `+app:ca` of its want on its subject sock, a memo hit's
is one the subject sock provides).

So `pokeS_sound_of_meet`, `pokeS_invKept_of_meet` and `gap_of_meet` give
the shapes of `Gap.contract`, `Gap.invKept` and `Gap.invStart` from
`CompHyp` and `PokeSites` alone.
-/

namespace Formalization
namespace SkaModel

open Nock Ana Bake

namespace Bake

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-- **The root datum's code requirement holds of every noun of the root's
sock.** -/
theorem skaPoke_root_fits {lib : Lib} (env : Env R) {n : Nat} {root : Ident} {memo memo' : Memo M}
    {reg reg' : R} {code : Bell → Option Nomm} {pruned : Callgraph M} {dats : M Bell (FDatum M)}
    {rd : FDatum M} (hinv : PokeInv lib memo code) (hw : WellFormed root.1) (hnr : NormSock root.1)
    (hnvr : root.1 ≠ Sock.void) (h : skaPoke env n root memo reg = some (pruned, dats, memo', rd, reg')) :
    ∀ x, Fits root.1 x → Fits rd.less x := by
  unfold skaPoke at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨⟨g, regG⟩, hg, pr, hpr, rd', hrd, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, -, -, rfl, -⟩ := he
  obtain ⟨G, hG, hcovP, -, -, -⟩ := skaCallgraph_prunedM (lib := lib) (code := code) env memo hinv.wf
    hinv.memoNorm hinv.keys hinv.ok hw hnr hnvr hg hpr
  have he := hcovP root rd' hrd
  intro x hx
  show Fits (entOf root rd').d.less x
  rcases hG _ he with ⟨_, _, _, _, gen', _, _, _, _, hle, _⟩ | ⟨m, _, _, _, ht, _, hd⟩
  · rw [hle]
    exact app_fits _ _ _ hx
  · simp only [hitTest, Option.bind_eq_some_iff] at ht
    obtain ⟨h1, hh, ht⟩ := ht
    cases h1 with
    | false => simp at ht
    | true =>
      rw [hd]
      exact huge_sound hh hx

end Bake

namespace PokeM

variable {M : Type → Type → Type} [Treap M] {Map : Type → Type} [HoonMap Map] {J H CR R : Type}

/-- **`+ska-poke` as `+poke` calls it**: `skaPokeB` on the root identity
`[&+sub fol]`, with the fuel `fuel` of the analysis and `bf` of the
worklist of `+bake-graph`, the registrations of the jets state
(`regOf`), and the jets state and the noun of `new` made from the
registrations it ends with (`jetsOf`, `newOf`).  `jet` is the `jetted` gate,
which reads the hot jets and the jets state. -/
def anaArm (env : Env R) (jet : H → J → (Bell → Option Datum) → R → Bell → Bool) (fold frozen : Bool)
    (fuel : Noun → Noun → LongB M → J → Nat) (bf : BEnv M → Nat) (regOf : J → R) (jetsOf : J → R → J)
    (newOf : R → Noun) : Noun → Noun → LongB M → J → H → Option (Bell × LongB M × J × Noun) :=
  fun s f L j hot =>
    (skaPokeB env (jet hot j) fold frozen (fuel s f L j) bf (Sock.mk Cape.yes s, f) L (regOf j)).map fun r =>
      (r.1, r.2.1, jetsOf j r.2.2, newOf r.2.2)

/-- The `+bake-graph` environment of the poke `[&+sub fol]` from the state
`L`, once the analysis has given `dats`, `memo'`, `rd` and `reg'`. -/
def anaEnv (jet : H → J → (Bell → Option Datum) → R → Bell → Bool) (fold frozen : Bool) (s f : Noun)
    (L : LongB M) (j : J) (hot : H) (dats : M Bell (FDatum M)) (memo' : Memo M) (rd : FDatum M) (reg' : R) :
    BEnv M :=
  pokeEnv (jet hot j (pokeDat dats memo') reg') fold frozen L.vars (Sock.mk Cape.yes s, f) dats memo' rd

/-- **HImp of every poke** from a state that satisfies `InvB`: every bake
`+bake-graph` ends with implies its code bell's code requirement. -/
def PokeBakes (lib : Lib) (env : Env R) (jet : H → J → (Bell → Option Datum) → R → Bell → Bool)
    (fold frozen : Bool) (fuel : Noun → Noun → LongB M → J → Nat) (regOf : J → R) : Prop :=
  ∀ s f (L : LongB M) j hot pr dats memo' rd reg', InvB lib L →
    skaPoke env (fuel s f L j) (Sock.mk Cape.yes s, f) L.memo (regOf j) = some (pr, dats, memo', rd, reg') →
    BakesImply (anaEnv jet fold frozen s f L j hot dats memo' rd reg')

/-- **`SitesMeet` of every poke** from a state that satisfies `InvB`
(`BakeImp.lean`).  **False on the real compiler** for the poke of
`bakeDropWitness` (`SitesMeetFalse.lean`), and so is `PokeBakes`; the
theorems that assume either cannot be used. -/
def PokeSites (lib : Lib) (env : Env R) (jet : H → J → (Bell → Option Datum) → R → Bell → Bool)
    (fold frozen : Bool) (fuel : Noun → Noun → LongB M → J → Nat) (regOf : J → R) : Prop :=
  ∀ s f (L : LongB M) j hot pr dats memo' rd reg', InvB lib L →
    skaPoke env (fuel s f L j) (Sock.mk Cape.yes s, f) L.memo (regOf j) = some (pr, dats, memo', rd, reg') →
    SitesMeet (anaEnv jet fold frozen s f L j hot dats memo' rd reg')

theorem pokeBakes_of_sites {lib : Lib} {env : Env R} {jet : H → J → (Bell → Option Datum) → R → Bell → Bool}
    {fold frozen : Bool} {fuel : Noun → Noun → LongB M → J → Nat} {regOf : J → R}
    (h : PokeSites lib env jet fold frozen fuel regOf) : PokeBakes lib env jet fold frozen fuel regOf :=
  fun s f L j hot pr dats memo' rd reg' hI hs => bakesImply_of_meet (h s f L j hot pr dats memo' rd reg' hI hs)

theorem fits_yes (s : Noun) : Fits (Sock.mk Cape.yes s) s := rfl

/-- **`AnaHyp` from HImp**: the model of `+ska-poke` keeps `InvB`, and its
root bell has the poke's formula and a code requirement that the poke's
subject fits. -/
theorem anaHyp_of_bakes (A : Arms M Map J H CR) {lib : Lib} {env : Env R}
    {jet : H → J → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB M → J → Nat} {bf : BEnv M → Nat} {regOf : J → R} {jetsOf : J → R → J}
    {newOf : R → Noun}
    (hA : A.skaPoke = anaArm env jet fold frozen fuel bf regOf jetsOf newOf)
    (hb : PokeBakes lib env jet fold frozen fuel regOf) : AnaHyp A lib where
  ana := by
    intro s f long jets hot r h hinv
    rw [hA] at h
    simp only [anaArm, Option.map_eq_some_iff] at h
    obtain ⟨⟨rb, L', reg'⟩, hk, rfl⟩ := h
    have hroot : (Sock.mk Cape.yes s, f).1 ≠ Sock.void := Sock.noConfusion
    have h1 := skaPokeB_sound env hinv (wf_root s) (normSock_yes s) hroot
      (fun pr dats memo' rd reg'' hs => hb s f long jets hot pr dats memo' rd reg'' hinv hs) hk
    refine ⟨h1.1, ?_⟩
    obtain ⟨code, hpi⟩ := hinv.ghost
    unfold skaPokeB at hk
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hk
    obtain ⟨⟨pr, dats, memo', rd, reg''⟩, hsk, ⟨baked, vars'⟩, -, he⟩ := hk
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, -, -⟩ := he
    exact ⟨rfl, skaPoke_root_fits env hpi (wf_root s) (normSock_yes s) hroot hsk s (fits_yes s)⟩

/-- **`AnaHyp` from `SitesMeet`.** -/
theorem anaHyp_of_meet (A : Arms M Map J H CR) {lib : Lib} {env : Env R}
    {jet : H → J → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB M → J → Nat} {bf : BEnv M → Nat} {regOf : J → R} {jetsOf : J → R → J}
    {newOf : R → Noun}
    (hA : A.skaPoke = anaArm env jet fold frozen fuel bf regOf jetsOf newOf)
    (hs : PokeSites lib env jet fold frozen fuel regOf) : AnaHyp A lib :=
  anaHyp_of_bakes A hA (pokeBakes_of_sites hs)

/-- **`Sound` of the model of `+poke`** from `CompHyp` and `PokeSites`. -/
theorem pokeS_sound_of_meet (A : Arms M Map J H CR) {lib : Lib} {ref : Ref M Map J H} {env : Env R}
    {jet : H → J → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB M → J → Nat} {bf : BEnv M → Nat} {regOf : J → R} {jetsOf : J → R → J}
    {newOf : R → Noun}
    (hC : CompHyp A lib ref) (hA : A.skaPoke = anaArm env jet fold frozen fuel bf regOf jetsOf newOf)
    (hs : PokeSites lib env jet fold frozen fuel regOf) : Sound lib (pokeS A) (InvS lib ref) :=
  pokeS_sound A hC (anaHyp_of_meet A hA hs)

/-- **The model of `+poke` keeps its invariant** from `CompHyp` and
`PokeSites`. -/
theorem pokeS_invKept_of_meet (A : Arms M Map J H CR) {lib : Lib} {ref : Ref M Map J H} {env : Env R}
    {jet : H → J → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB M → J → Nat} {bf : BEnv M → Nat} {regOf : J → R} {jetsOf : J → R → J}
    {newOf : R → Noun}
    (hC : CompHyp A lib ref) (hA : A.skaPoke = anaArm env jet fold frozen fuel bf regOf jetsOf newOf)
    (hs : PokeSites lib env jet fold frozen fuel regOf) :
    ∀ st ov p st', InvS lib ref st → ¬ HotOvum ov → pokeS A st ov = some (p, st') → InvS lib ref st' :=
  pokeS_invKept A hC (anaHyp_of_meet A hA hs)

/-- **The shapes of `Gap.contract`, `Gap.invKept` and `Gap.invStart`** from
`CompHyp` and `PokeSites` alone. -/
theorem gap_of_meet (A : Arms M Map J H CR) {lib : Lib} {ref : Ref M Map J H} {env : Env R}
    {jet : H → J → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB M → J → Nat} {bf : BEnv M → Nat} {regOf : J → R} {jetsOf : J → R → J}
    {newOf : R → Noun}
    (hC : CompHyp A lib ref) (hA : A.skaPoke = anaArm env jet fold frozen fuel bf regOf jetsOf newOf)
    (hs : PokeSites lib env jet fold frozen fuel regOf)
    (enc : CSt M Map J H CR → Noun) (henc : ∀ a b, enc a = enc b → a = b) :
    Sound lib (liftPoke enc (pokeS A)) (liftInv enc (InvS lib ref)) ∧
    (∀ t ov p t', liftInv enc (InvS lib ref) t → ¬ HotOvum ov → liftPoke enc (pokeS A) t ov = some (p, t') →
      liftInv enc (InvS lib ref) t') ∧
    ∀ jets hot rest, liftInv enc (InvS lib ref)
      (enc ⟨⟨Treap.empty, Treap.empty, Treap.empty⟩, jets, hot, ⟨Treap.empty, Treap.empty, Treap.empty, rest⟩⟩) :=
  gap_of A hC (anaHyp_of_meet A hA hs) enc henc

end PokeM

end SkaModel
end Formalization
