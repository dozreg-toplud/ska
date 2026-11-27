import lemmas.Ska.PokeEnc
import lemmas.Ska.AnaEnds

/-!
# The pill's `+poke` on `%full` as the model's poke, up to the callees

With `enc` of `Ska/PokeEnc.lean`, `liftPoke (enc fl) (pokeS A)` on the
encoding of a state is the model's poke with the new state encoded
(`liftPoke_enc_fl`).  Here the `%full` branch of the pill's inner `+poke` is
written as a chain of its callees on the compiler's core (`pillFull`): the
call of `+ska-poke` that replaces `long-ska`, the jetted-root test
(`~(get by call.cole)` and `~(has by jets-hot)`), `+scc-of` that replaces
`sccs.cache`, `+compiled-mono` that replaces `cache`, and `+optimize`.  The
theorem `pokeN_full_of` composes named links, one per callee, each stated on
encoded states (`SkaLink`, `JetRootLink`, `SccLink`, `MonoLink`, `OptLink`),
with `FullBranchIs`, the Nock of the branch itself (validation, dispatch and
the 272 cells of the `%full` branch, open), into the field `pokeModel` on
`%full`.

Mismatch P2 of README Gaps 23: `+ska-poke` ends with `+ska-cole-update`,
which reads the new bells and their `seek`, so the new jets state is not a
function of the registrations alone, as `anaArm` has it.  `anaArmP` gives
`jetsOf` the old and the new table and the hot jets; `AnaHyp` holds of it
with the proof of `anaHyp_of_arm` (`anaHyp_of_armP`), and the shapes of
`Gap.contract`, `Gap.invKept` and `Gap.invStart` follow for `enc fl`
(`gap_of_armP`), `invStart` on the pill's `cor` itself (`invStart_cor`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeM

/-! ## `+ska-poke` with `+ska-cole-update` (mismatch P2) -/

section AnaP

variable {M : Type → Type → Type} [Treap M] {Map : Type → Type} [HoonMap Map] {J H CR R : Type}

/-- **`+ska-poke` as `+poke` calls it**, as `anaArm`, but the new jets state
is made from the hot jets, the old jets state, the registrations, and the old
and new tables (`+ska-cole-update` reads the new bells and their `seek`). -/
def anaArmP (env : Env R) (jet : H → J → (Bell → Option Datum) → R → Bell → Bool) (fold frozen : Bool)
    (fuel : Noun → Noun → LongB M → J → Nat) (bf : BEnv M → Nat) (regOf : J → R)
    (jetsOf : H → J → R → LongB M → LongB M → J)
    (newOf : R → Noun) : Noun → Noun → LongB M → J → H → Option (Bell × LongB M × J × Noun) :=
  fun s f L j hot =>
    (skaPokeB env (jet hot j) fold frozen (fuel s f L j) bf (Sock.mk Cape.yes s, f) L (regOf j)).map fun r =>
      (r.1, r.2.1, jetsOf hot j r.2.2 L r.2.1, newOf r.2.2)

/-- **`AnaHyp` of `anaArmP`**, with no hypothesis (the proof of
`anaHyp_of_bakes`: the jets state plays no part). -/
theorem anaHyp_of_armP (A : Arms M Map J H CR) {lib : Lib} {env : Env R}
    {jet : H → J → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB M → J → Nat} {bf : BEnv M → Nat} {regOf : J → R}
    {jetsOf : H → J → R → LongB M → LongB M → J} {newOf : R → Noun}
    (hA : A.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf) : AnaHyp A lib where
  ana := by
    intro s f long jets hot r h hinv
    rw [hA] at h
    simp only [anaArmP, Option.map_eq_some_iff] at h
    obtain ⟨⟨rb, L', reg'⟩, hk, rfl⟩ := h
    have hroot : (Sock.mk Cape.yes s, f).1 ≠ Sock.void := Sock.noConfusion
    have h1 := skaPokeB_sound env hinv (wf_root s) (normSock_yes s) hroot hk
    refine ⟨h1.1, ?_⟩
    obtain ⟨code, hpi⟩ := hinv.ghost
    unfold skaPokeB at hk
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hk
    obtain ⟨⟨pr, dats, memo', rd, reg''⟩, hsk, ⟨baked, vars'⟩, -, he⟩ := hk
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, -, -⟩ := he
    exact ⟨rfl, Bake.skaPoke_root_fits env hpi (wf_root s) (normSock_yes s) hroot hsk s (fits_yes s)⟩

/-- **The fuel of the analysis is a good one** (mismatch P3, the analysis
side of M9): wherever the analysis answers at some fuel, it answers the same
at `fuel`.  Then the `∃ n` of `ska_poke_ana_iff_pill` is the fuel `fuel` of
`anaArmP`. -/
def FuelOK (env : Env R) (regOf : J → R) (fuel : Noun → Noun → LongB M → J → Nat) : Prop :=
  ∀ s f (L : LongB M) j n r, Ana.skaPoke env n (Sock.mk Cape.yes s, f) L.memo (regOf j) = some r →
    Ana.skaPoke env (fuel s f L j) (Sock.mk Cape.yes s, f) L.memo (regOf j) = some r

/-- **`anaFuel` is a good fuel**, with no hypothesis: the fuel `CgHalts`
gives `fullAnswers_of_cg` (M9) is one at which the analysis answers as at
every fuel that answers (`skaPoke_fuel_le`). -/
theorem fuelOK_anaFuel (env : Env R) (regOf : J → R) : FuelOK (M := M) env regOf (anaFuel env regOf) := by
  intro s f L j n r h
  have hex : ∃ n r, Ana.skaPoke env n (Sock.mk Cape.yes s, f) L.memo (regOf j) = some r := ⟨n, r, h⟩
  unfold anaFuel
  rw [dif_pos hex]
  obtain ⟨r0, h0⟩ := Classical.choose_spec hex
  have a := Ana.skaPoke_fuel_le env (Nat.le_max_left n (Classical.choose hex)) _ _ _ r h
  have b := Ana.skaPoke_fuel_le env (Nat.le_max_right n (Classical.choose hex)) _ _ _ r0 h0
  rw [a] at b
  cases b
  exact h0

end AnaP

/-! ## The shapes of the fields of `Gap` for `enc fl` -/

/-- **`Gap.contract`, `Gap.invKept`, and `Gap.invStart` on the pill's `cor`**
for `liftPoke (enc fl) (pokeS A)`, from `CompHyp` and `A.skaPoke = anaArmP …`
(no hypothesis on `enc`: `enc_inj`, `cor_enc`). -/
theorem gap_of_armP (A : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)) {lib : Lib}
    {ref : Ref FinMap (TreapMap mugF) Noun Noun} {R : Type} {env : Env R}
    {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → R}
    {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}
    (hC : CompHyp A lib ref) (hA : A.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf)
    (fl : Flags) :
    Sound lib (liftPoke (enc fl) (pokeS A)) (liftInv (enc fl) (InvS lib ref)) ∧
    (∀ t ov p t', liftInv (enc fl) (InvS lib ref) t → ¬ HotOvum ov →
      liftPoke (enc fl) (pokeS A) t ov = some (p, t') → liftInv (enc fl) (InvS lib ref) t') ∧
    liftInv (enc fl) (InvS lib ref) cor := by
  obtain ⟨h1, h2, h3⟩ := gap_of A hC (anaHyp_of_armP A hA) (enc fl) (enc_inj fl)
  refine ⟨h1, h2, ?_⟩
  rw [cor_enc fl]
  exact h3 jets0 (Noun.atom 0) (Noun.atom 0, Noun.atom 0)

/-- **`invStart` closed** for `enc fl`: the invariant holds of the pill's `cor`. -/
theorem invStart_cor {lib : Lib} {ref : Ref FinMap (TreapMap mugF) Noun Noun} (fl : Flags) :
    liftInv (enc fl) (InvS lib ref) cor :=
  ⟨emptySt, (cor_enc fl).symm, invS_init lib ref jets0 (Noun.atom 0) (Noun.atom 0, Noun.atom 0)⟩

/-! ## The `%full` branch as a chain of its callees -/

section Full

variable (fl : Flags) (A : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))

theorem liftPoke_enc_fl (st : PSt) (ov : Ovum) :
    liftPoke (enc fl) (pokeS A) (enc fl st) ov = (pokeS A st ov).map fun r => (r.1, enc fl r.2) :=
  liftPoke_enc (enc_inj fl) st ov

/-- **The `%full` branch of the pill's inner `+poke`, by its callees**, each on
the compiler's core `cr` (the ones that change the state return the core with
it changed):

* `ska cr s f`: `(ska-poke [&+s f] long-ska ~(key by jets-hot))` under `%ska`
  (arm `20` of `ana` at axis `511` of `cr`), giving `func`, `new`, and `cr`
  with `long-ska` (axis `58`) replaced;
* `jr cr func`: the jetted-root test, `(~(get by call.cole.jets.long-ska)
  func)` then `(~(has by jets-hot) u.rin)`, giving the `%jsf` straight-out
  (`[[%this ~] 1 (~(put by ~) 0 [~ ~ [%jsf func 0 u.rin]])]`) or `~`;
* `scc cr func`: `(scc-of func calls sccs)` (arm `96127` at axis `63` of
  `cr`), giving the SCC and `cr` with `sccs.cache` (axis `958`) replaced;
* `mono cr func scc`: `(compiled-mono func scc)` under `%ska` (arm `10` at
  axis `3` of `cr`), giving the straight and `cr` with `cache` replaced;
* `opt str`: `(optimize str)` under `%ska`.

The product is `[[%ir func out new] cr']`. -/
def pillFull (ska : Noun → Noun → Noun → Option (Noun × Noun × Noun)) (jr : Noun → Noun → Option (Option Noun))
    (scc : Noun → Noun → Option (Noun × Noun)) (mono : Noun → Noun → Noun → Option (Noun × Noun))
    (opt : Noun → Option Noun) (cr s f : Noun) : Option Noun :=
  (ska cr s f).bind fun r =>
  (jr r.2.2 r.1).bind fun o =>
  match o with
  | some out => some (C (C (Noun.atom Tag.ir) (C r.1 (C out r.2.1))) r.2.2)
  | none =>
    (scc r.2.2 r.1).bind fun q =>
    (mono q.2 r.1 q.1).bind fun p =>
    (opt p.1).map fun out => C (C (Noun.atom Tag.ir) (C r.1 (C out r.2.1))) p.2

/-- **The Nock of the branch** (open): on every encoded state and every
`%full` with a cell formula, the pill's inner `+poke` is `pillFull` of its
callees.  What it takes: `+validate-ovum` returning a `%full` unchanged, the
dispatch of `ipokeR` (the `%full` test is the third), and the 272 cells of
the branch, with each call as the parameter that names it. -/
def FullBranchIs (ska : Noun → Noun → Noun → Option (Noun × Noun × Noun))
    (jr : Noun → Noun → Option (Option Noun)) (scc : Noun → Noun → Option (Noun × Noun))
    (mono : Noun → Noun → Noun → Option (Noun × Noun)) (opt : Noun → Option Noun) : Prop :=
  ∀ (st : PSt) (s f₁ f₂ : Noun),
    pokeN (enc fl st) (Ovum.full s (C f₁ f₂)).toNoun = pillFull ska jr scc mono opt (enc fl st) s (C f₁ f₂)

/-- **Leaf 1.2, the link of `+ska-poke`** on encoded states: the pill's call
returns exactly when the model's `A.skaPoke` does, with the root bell, `new`,
and the core with the new `long-ska`.  With `A.skaPoke = anaArmP …`, this is
`ska_poke_ana_iff_pill` (the analysis part), the link of `spRest` (the
baking part, open) and of `~(key by jets-hot)`, at the fuel of M9. -/
def SkaLink (ska : Noun → Noun → Noun → Option (Noun × Noun × Noun)) : Prop :=
  ∀ (st : PSt) s f, ska (enc fl st) s f = (A.skaPoke s f st.long st.jets st.hot).map fun r =>
    (r.1.toNoun, r.2.2.2, enc fl { st with long := r.2.1, jets := r.2.2.1 })

/-- The jetted-root test is `A.jetRoot` (it always returns). -/
def JetRootLink (jr : Noun → Noun → Option (Option Noun)) : Prop :=
  ∀ (st : PSt) b, jr (enc fl st) b.toNoun = some ((A.jetRoot st.jets st.hot b).map Straight.toNoun)

/-- `+scc-of` is `A.sccOf`. -/
def SccLink (scc : Noun → Noun → Option (Noun × Noun)) : Prop :=
  ∀ (st : PSt) b, scc (enc fl st) b.toNoun = (A.sccOf b st.long st.cache.sccs).map fun r =>
    (FinMap.setNoun r.1, enc fl { st with cache := { st.cache with sccs := r.2 } })

/-- `+compiled-mono` is `compiledMono A` (it calls `+compile-unary`, whose
link is `A.compileUnary`: tracks A, I, K). -/
def MonoLink (mono : Noun → Noun → Noun → Option (Noun × Noun)) : Prop :=
  ∀ (st : PSt) b sc, mono (enc fl st) b.toNoun (FinMap.setNoun sc) = (compiledMono A st b sc).map fun p =>
    (p.1.toNoun, enc fl { st with cache := p.2 })

/-- `+optimize` is `A.optimize` (track H, on `FragX`). -/
def OptLink (opt : Noun → Option Noun) : Prop :=
  ∀ s : Straight (TreapMap mugF), opt s.toNoun = some (A.optimize s).toNoun

/-- **`pokeModel` on `%full`, from the named links**: on every encoded state
and every `%full` with a cell formula, the pill's inner `+poke` computes
`liftPoke (enc fl) (pokeS A)`, as `PokeModel` asks. -/
theorem pokeN_full_of {ska : Noun → Noun → Noun → Option (Noun × Noun × Noun)}
    {jr : Noun → Noun → Option (Option Noun)} {scc : Noun → Noun → Option (Noun × Noun)}
    {mono : Noun → Noun → Noun → Option (Noun × Noun)} {opt : Noun → Option Noun}
    (hB : FullBranchIs fl ska jr scc mono opt) (hS : SkaLink fl A ska) (hJ : JetRootLink fl A jr)
    (hC : SccLink fl A scc) (hM : MonoLink fl A mono) (hO : OptLink A opt)
    (st : PSt) (s f₁ f₂ : Noun) :
    pokeN (enc fl st) (Ovum.full s (C f₁ f₂)).toNoun =
      (liftPoke (enc fl) (pokeS A) (enc fl st) (Ovum.full s (C f₁ f₂))).map fun r => C r.1.toNoun r.2 := by
  rw [hB, liftPoke_enc_fl]
  unfold pillFull
  rw [hS]
  simp only [pokeS]
  cases e1 : A.skaPoke s (C f₁ f₂) st.long st.jets st.hot with
  | none => rfl
  | some r =>
    simp only [Option.map_some, Option.bind_some]
    rw [hJ]
    simp only [Option.bind_some]
    cases e2 : A.jetRoot r.2.2.1 st.hot r.1 with
    | some out => simp [Prod.toNoun]
    | none =>
      simp only [Option.map_none]
      unfold compileStep
      rw [hC]
      cases e3 : A.sccOf r.1 r.2.1 st.cache.sccs with
      | none => rfl
      | some q =>
        simp only [Option.map_some, Option.bind_some, if_true]
        rw [hM]
        cases e4 : compiledMono A { st with long := r.2.1, jets := r.2.2.1, cache := { st.cache with sccs := q.2 } } r.1 q.1 with
        | none => rfl
        | some p =>
          simp only [Option.map_some, Option.bind_some]
          rw [hO]
          simp [Prod.toNoun]

end Full

end Compiler
end Formalization
