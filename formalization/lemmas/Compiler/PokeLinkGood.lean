import lemmas.Compiler.PokeLinkSka
import lemmas.Compiler.PokeLinkScc
import lemmas.Hoon.MapFolds

/-!
# `pokeModel` on `%full` at every reachable core, from an invariant `PGood`

The per-state lemmas (`pokeN_fullAt2`, `skaLinkAt_of`, `jrP_enc`,
`OptInAt`) need facts of the state the model does not give for every
state: the jets noun's shape, `call.cole` and `jets-hot` maps, and the mono
cache holding only straights of the class where `+optimize` returns.  Here:

* `keyRaw_enc`: `~(key by jets-hot)` (arm `188` of `by`) returns on every
  encoded state whose `hot` is a map, a set of exactly its keys (`key_by`);
* `PGood Cls st`: the invariant: `JetsMaps` (the jets noun is `[root core
  batt arms pend [call back]]`, seven `IsMap mugF` nouns), `JetsGood`
  (`call.cole` a map with ring values, `jets-hot` a map), `MonoIn Cls` (every
  straight of the mono cache is in `Cls`).  Every other map `enc` writes is
  `FinMap.toNoun` or `TreapMap` of the model, so a map for free;
* `good_empty`: `PGood Cls emptySt`, so `PGood` holds at `cor` (`cor_enc`);
* `good_full_step`: a `%full` poke of the model keeps `PGood`, from
  `SkaKeeps` (the model's `+ska-poke` returns jets with `JetsMaps` and
  `JetsGood`; for `anaArmP` it is `JetsOfGood` of `jetsOf`,
  `skaKeeps_of_armP`) and `UnaryKeeps Cls` (`+compile-unary`'s straight
  and the mono cache it returns are in `Cls`);
* `optInAt_of_good`: `OptInAt` at every `PGood` state;
* `pokeModel_fullGood`: `pokeModel` on `%full` at every `PGood` state from
  the links stated on `PGood` states only (`SpRestGood`, `MonoLinkGood`);
* `pokeReachGood`: every `PokeReach` core is `enc fl st` with `PGood st`,
  the `%full` case proved, the other pokes as `OtherKeeps`;
* `pokeModel_fullReach`: the form of `PokeModel` on `%full`, every core
  with `CorIn`, and `pokeModel_fullReachP` with `anaArmP`, `optimizeP`,
  `sccOfP`, `jetRootP`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeM

/-! ## `~(key by jets-hot)` -/

theorem inIn_layer2 : InIn mugF layer2 := ⟨in.arm_at, gorIn_morIn_layer2.1, gorIn_morIn_layer2.2⟩

/-- **`~(key by jets-hot)` on an encoded core whose `hot` is a map**: the
set of its keys. -/
theorem keyRaw_enc (fl : Flags) (st : PSt) (h : IsMap mugF st.hot) :
    ∃ key, keyRaw (enc fl st) = some key ∧ IsSet mugF key ∧ ∀ k, Has key k ↔ ∃ v, Get st.hot k v := by
  obtain ⟨out, he, hs, hh⟩ := key_by layer2 inIn_layer2 st.hot h
  refine ⟨out, ?_, hs, hh⟩
  have hn := nock_of_eval he
  simp [keyRaw, byArmO, gateAt, enc_hoon, enc_hot, by.arm_at, by_arm, by.key.arm_at, nock_exec, hn]

/-! ## The invariant -/

/-- **The jets noun**: `[root core batt arms pend [call back]]`, seven maps. -/
def JetsMaps (j : Noun) : Prop :=
  ∃ r1 r2 r3 r4 pd ca bk, j = C r1 (C r2 (C r3 (C r4 (C pd (C ca bk))))) ∧
    IsMap mugF r1 ∧ IsMap mugF r2 ∧ IsMap mugF r3 ∧ IsMap mugF r4 ∧ IsMap mugF pd ∧ IsMap mugF ca ∧
    IsMap mugF bk

/-- Every straight of the mono cache is in `Cls`. -/
def MonoIn (Cls : Straight (TreapMap mugF) → Prop) (c : Cache FinMap (TreapMap mugF) (Noun × Noun)) : Prop :=
  ∀ b s, Treap.get c.mono b = some s → Cls s

/-- **The invariant on the model's states** that the per-state links need. -/
structure PGood (Cls : Straight (TreapMap mugF) → Prop) (st : PSt) : Prop where
  maps : JetsMaps st.jets
  jets : JetsGood st.jets st.hot
  mono : MonoIn Cls st.cache

theorem jets0_maps : JetsMaps jets0 :=
  ⟨A 0, A 0, A 0, A 0, A 0, A 0, A 0, rfl, IsMap.nil, IsMap.nil, IsMap.nil, IsMap.nil, IsMap.nil, IsMap.nil,
    IsMap.nil⟩

/-- **`PGood` at the start.** -/
theorem good_empty (Cls : Straight (TreapMap mugF) → Prop) : PGood Cls emptySt where
  maps := jets0_maps
  jets := ⟨⟨A 0, rfl, IsMap.nil, fun _ _ h => absurd h Get_atom⟩, IsMap.nil⟩
  mono := fun b s h => by
    have e : Treap.get (Treap.empty : FinMap Bell (Straight (TreapMap mugF))) b = none := Treap.get_empty b
    exact absurd (e.symm.trans h) (by simp)

section Keep

variable (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)) (Cls : Straight (TreapMap mugF) → Prop)

/-- **The model's `+ska-poke` keeps the jet maps** (with the old hot noun). -/
def SkaKeeps : Prop :=
  ∀ (st : PSt) s f r, JetsMaps st.jets → JetsGood st.jets st.hot →
    Ar.skaPoke s f st.long st.jets st.hot = some r → JetsMaps r.2.2.1 ∧ JetsGood r.2.2.1 st.hot

/-- **`jetsOf` (the model of `+ska-cole-update` after the edit of
`jets.lon`) keeps the jet maps.** -/
def JetsOfGood {R : Type} (jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun) : Prop :=
  ∀ hot j reg L L', JetsMaps j → JetsGood j hot →
    JetsMaps (jetsOf hot j reg L L') ∧ JetsGood (jetsOf hot j reg L L') hot

theorem skaKeeps_of_armP {R : Type} {env : Env R}
    {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → R}
    {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf) (h : JetsOfGood jetsOf) :
    SkaKeeps Ar := by
  intro st s f r hm hg e
  rw [hA] at e
  unfold anaArmP at e
  split at e
  · cases e
  · obtain ⟨r', _, rfl⟩ := Option.map_eq_some_iff.1 e
    exact h _ _ _ _ _ hm hg

/-- **`+compile-unary` keeps the class**: on a `PGood` state its straight
and every straight of the mono cache it returns are in `Cls` (track D's
`OptTotalMono` on the class of the compile, for `Cls = OptTotal`). -/
def UnaryKeeps : Prop :=
  ∀ (st : PSt) b sc r, PGood Cls st →
    Ar.compileUnary b sc st.long st.jets st.hot st.cache = some r → Cls r.1.1 ∧ MonoIn Cls r.2

variable {Ar Cls}

theorem compiledMono_good (hU : UnaryKeeps Ar Cls) (st : PSt) (hg : PGood Cls st) (b : Bell)
    (sc : FinMap Bell Unit) (p : Straight (TreapMap mugF) × Cache FinMap (TreapMap mugF) (Noun × Noun))
    (h : compiledMono Ar st b sc = some p) : Cls p.1 ∧ MonoIn Cls p.2 := by
  unfold compiledMono at h
  split at h
  · rename_i s hs
    cases h
    exact ⟨hg.mono b s hs, hg.mono⟩
  · obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨h1, h2⟩ := hU st b sc r hg hr
    refine ⟨h1, fun b' s' hs' => ?_⟩
    have e : Treap.get (Treap.put r.2.mono b r.1.1) b' = some s' := hs'
    rw [Treap.get_put] at e
    split at e
    · cases e; exact h1
    · exact h2 b' s' e

/-- **The model's `%full` keeps `PGood`.** -/
theorem good_full_step (hK : SkaKeeps Ar) (hU : UnaryKeeps Ar Cls) (st : PSt) (s f : Noun)
    (pr : SkaModel.Prod (TreapMap mugF)) (st' : PSt) (hg : PGood Cls st)
    (h : pokeS Ar st (Ovum.full s f) = some (pr, st')) : PGood Cls st' := by
  simp only [pokeS] at h
  obtain ⟨r, e1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨hm', hj'⟩ := hK st s f r hg.maps hg.jets e1
  split at h
  · cases h
    exact ⟨hm', hj', hg.mono⟩
  · obtain ⟨p, hp, e⟩ := Option.map_eq_some_iff.1 h
    cases e
    unfold compileStep at hp
    obtain ⟨q, _, hp⟩ := Option.bind_eq_some_iff.1 hp
    obtain ⟨p', hp', e⟩ := Option.map_eq_some_iff.1 hp
    cases e
    simp only [if_true] at hp'
    have hg1 : PGood Cls { st with long := r.2.1, jets := r.2.2.1, cache := { st.cache with sccs := q.2 } } :=
      ⟨hm', hj', hg.mono⟩
    exact ⟨hm', hj', (compiledMono_good hU _ hg1 r.1 q.1 p' hp').2⟩

/-- **`OptInAt` at every `PGood` state.** -/
theorem optInAt_of_good (hK : SkaKeeps Ar) (hU : UnaryKeeps Ar Cls) (st : PSt) (s f : Noun)
    (hg : PGood Cls st) : OptInAt Ar Cls st s f := by
  intro r q p e1 _ _ e4
  obtain ⟨hm', hj'⟩ := hK st s f r hg.maps hg.jets e1
  refine (compiledMono_good hU _ ?_ r.1 q.1 p e4).1
  exact ⟨hm', hj', hg.mono⟩

end Keep

/-! ## The links on `PGood` states -/

section Links

variable (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
  (Cls : Straight (TreapMap mugF) → Prop)

/-- **The baking half `spRest` linked at every `PGood` state** (open: 1,120
cells, README Gaps 23), on a cell formula. -/
def SpRestGood (env : Env Noun) : Prop :=
  ∀ (st : PSt) s f₁ f₂ r1 r2 r3 r4 jRest key, PGood Cls st → st.jets = C r1 (C r2 (C r3 (C r4 jRest))) →
    keyRaw (enc fl st) = some key → SpRestAt fl Ar env st s (C f₁ f₂) r1 r2 r3 r4 jRest key

/-- `MonoLink`'s equation at one state. -/
def MonoLinkAt (st : PSt) (b : Bell) (sc : FinMap Bell Unit) : Prop :=
  monoP (enc fl st) b.toNoun (FinMap.setNoun sc) = (compiledMono Ar st b sc).map fun p =>
    (p.1.toNoun, enc fl { st with cache := p.2 })

/-- **`+compiled-mono` linked at every `PGood` state** (open: 115 cells and
`+compile-unary`, tracks A, I, K). -/
def MonoLinkGood : Prop := ∀ (st : PSt) b sc, PGood Cls st → MonoLinkAt fl Ar st b sc

theorem monoLinkGood_of (h : MonoLink fl Ar monoP) : MonoLinkGood fl Ar Cls := fun st b sc _ => h st b sc

/-- **`SkaLink`'s equation at a `PGood` state**, from `SpRestGood`: the
shape from `JetsMaps`, `keyRaw` from `keyRaw_enc`. -/
theorem skaLinkAt_good (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP)
    (hR : SpRestGood fl Ar Cls env) (st : PSt) (s f₁ f₂ : Noun) (hg : PGood Cls st) :
    SkaLinkAt fl Ar st s (C f₁ f₂) := by
  obtain ⟨r1, r2, r3, r4, pd, ca, bk, hj, -⟩ := hg.maps
  obtain ⟨key, hk, -, -⟩ := keyRaw_enc fl st hg.jets.2
  exact skaLinkAt_of fl Ar env hhe hth hsoft hrf st s (C f₁ f₂) r1 r2 r3 r4 (C pd (C ca bk)) key hj hk
    (hR st s f₁ f₂ r1 r2 r3 r4 _ key hg hj hk)

/-- **`pokeN_fullAt2` with `MonoLink` at the state it is used on.** -/
theorem pokeN_fullAt3 (hC : SccLink fl Ar sccP) (hO : OptLinkOn Cls Ar optP) (st : PSt) (s f₁ f₂ : Noun)
    (hS : SkaLinkAt fl Ar st s (C f₁ f₂))
    (hJ : ∀ r, Ar.skaPoke s (C f₁ f₂) st.long st.jets st.hot = some r →
      jrP (enc fl { st with long := r.2.1, jets := r.2.2.1 }) r.1.toNoun =
        some ((Ar.jetRoot r.2.2.1 st.hot r.1).map Straight.toNoun))
    (hM : ∀ r (q : FinMap Bell Unit × FinMap Bell (FinMap Bell Unit)), Ar.skaPoke s (C f₁ f₂) st.long st.jets st.hot = some r →
      MonoLinkAt fl Ar { st with long := r.2.1, jets := r.2.2.1, cache := { st.cache with sccs := q.2 } } r.1 q.1)
    (hIn : OptInAt Ar Cls st s (C f₁ f₂)) :
    pokeN (enc fl st) (Ovum.full s (C f₁ f₂)).toNoun =
      (liftPoke (enc fl) (pokeS Ar) (enc fl st) (Ovum.full s (C f₁ f₂))).map fun r => C r.1.toNoun r.2 := by
  rw [fullBranchIs fl st s f₁ f₂, liftPoke_enc_fl]
  unfold pillFull
  rw [hS]
  simp only [pokeS]
  cases e1 : Ar.skaPoke s (C f₁ f₂) st.long st.jets st.hot with
  | none => rfl
  | some r =>
    simp only [Option.map_some, Option.bind_some]
    rw [hJ r e1]
    simp only [Option.bind_some]
    cases e2 : Ar.jetRoot r.2.2.1 st.hot r.1 with
    | some out => simp [Prod.toNoun]
    | none =>
      simp only [Option.map_none]
      unfold compileStep
      rw [hC]
      cases e3 : Ar.sccOf r.1 r.2.1 st.cache.sccs with
      | none => rfl
      | some q =>
        simp only [Option.map_some, Option.bind_some, if_true]
        have hMq := hM r q e1
        unfold MonoLinkAt at hMq
        rw [hMq]
        cases e4 : compiledMono Ar { st with long := r.2.1, jets := r.2.2.1, cache := { st.cache with sccs := q.2 } } r.1 q.1 with
        | none => rfl
        | some p =>
          simp only [Option.map_some, Option.bind_some]
          rw [hO p.1 (hIn r q p e1 e2 e3 e4)]
          simp [Prod.toNoun]

/-- **`pokeModel` on every `%full` at a `PGood` state**, from the links on
`PGood` states. -/
theorem pokeModel_fullGood (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP)
    (hJA : Ar.jetRoot = jetRootP) (hR : SpRestGood fl Ar Cls env) (hC : SccLink fl Ar sccP)
    (hM : MonoLinkGood fl Ar Cls) (hO : OptLinkOn Cls Ar optP) (hK : SkaKeeps Ar) (hU : UnaryKeeps Ar Cls)
    (hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none) (st : PSt) (hg : PGood Cls st) (s f : Noun) :
    pokeN (enc fl st) (Ovum.full s f).toNoun =
      (liftPoke (enc fl) (pokeS Ar) (enc fl st) (Ovum.full s f)).map fun r => C r.1.toNoun r.2 := by
  cases f with
  | atom a => rw [pokeN_full_atom, liftPoke_enc_fl]; simp [pokeS, hAt]
  | cell f₁ f₂ =>
    refine pokeN_fullAt3 fl Ar Cls hC hO st s f₁ f₂ (skaLinkAt_good fl Ar Cls env hhe hth hsoft hrf hR st s f₁ f₂ hg)
      (fun r e => ?_) (fun r q e => ?_) (optInAt_of_good hK hU st s _ hg)
    · obtain ⟨_, hj'⟩ := hK st s _ r hg.maps hg.jets e
      exact jetRootLinkG_of fl Ar hJA st s _ r e hj'
    · obtain ⟨hm', hj'⟩ := hK st s _ r hg.maps hg.jets e
      refine hM _ r.1 q.1 ?_
      exact ⟨hm', hj', hg.mono⟩

/-! ## The reachable cores -/

/-- **Every core the pill reaches by pokes is an encoded `PGood` state**
(`PokeReachEnc` with the invariant). -/
def PokeReachGood : Prop := ∀ cr, PokeReach cr → ∃ st, PGood Cls st ∧ enc fl st = cr

/-- **The pokes other than `%full` keep `PGood`** (open: the `%dire`,
`%jets`, `%fast` branches; a noun that is no ovum crashes, `pokeValid`). -/
def OtherKeeps : Prop :=
  ∀ (st : PSt) ovo p c', PGood Cls st → pokeN (enc fl st) ovo = some (C p c') → ¬ Ska.Hot ovo →
    (∀ s f, ovo ≠ (Ovum.full s f).toNoun) → ∃ st', PGood Cls st' ∧ enc fl st' = c'

/-- **The `%full` case of `PokeReachGood`**: from an encoded `PGood` state,
the core the pill returns is `enc fl` of the model's new state, `PGood`. -/
theorem full_step_good (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP)
    (hJA : Ar.jetRoot = jetRootP) (hR : SpRestGood fl Ar Cls env) (hC : SccLink fl Ar sccP)
    (hM : MonoLinkGood fl Ar Cls) (hO : OptLinkOn Cls Ar optP) (hK : SkaKeeps Ar) (hU : UnaryKeeps Ar Cls)
    (hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none) (st : PSt) (hg : PGood Cls st) (s f : Noun)
    {p c' : Noun} (hp : pokeN (enc fl st) (Ovum.full s f).toNoun = some (C p c')) :
    ∃ st', PGood Cls st' ∧ enc fl st' = c' := by
  rw [pokeModel_fullGood fl Ar Cls env hhe hth hsoft hrf hJA hR hC hM hO hK hU hAt st hg s f,
    liftPoke_enc_fl] at hp
  cases e : pokeS Ar st (Ovum.full s f) with
  | none => rw [e] at hp; cases hp
  | some q =>
    rw [e] at hp
    simp only [Option.map_some, Option.some.injEq, Noun.cell.injEq] at hp
    exact ⟨q.2, good_full_step hK hU st s f q.1 q.2 hg e, hp.2⟩

/-- **`PokeReachGood`**: the start by `good_empty` and `cor_enc`, the `%full`
pokes by `full_step_good`, the others by `OtherKeeps`. -/
theorem pokeReachGood (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP)
    (hJA : Ar.jetRoot = jetRootP) (hR : SpRestGood fl Ar Cls env) (hC : SccLink fl Ar sccP)
    (hM : MonoLinkGood fl Ar Cls) (hO : OptLinkOn Cls Ar optP) (hK : SkaKeeps Ar) (hU : UnaryKeeps Ar Cls)
    (hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none) (hX : OtherKeeps fl Cls) : PokeReachGood fl Cls := by
  intro cr h
  induction h with
  | start => exact ⟨emptySt, good_empty Cls, (cor_enc fl).symm⟩
  | @poke c ovo p c' _ hp hh ih =>
    obtain ⟨st, hg, rfl⟩ := ih
    by_cases e : ∃ s f, ovo = (Ovum.full s f).toNoun
    · obtain ⟨s, f, rfl⟩ := e
      exact full_step_good fl Ar Cls env hhe hth hsoft hrf hJA hR hC hM hO hK hU hAt st hg s f hp
    · exact hX st ovo p c' hg hp hh fun s f h => e ⟨s, f, h⟩

/-- **`pokeModel` on `%full` at every reachable core**, in the form of
`PokeModel` (every core with `CorIn`): from the links on `PGood` states. -/
theorem pokeModel_fullReach (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP)
    (hJA : Ar.jetRoot = jetRootP) (hR : SpRestGood fl Ar Cls env) (hC : SccLink fl Ar sccP)
    (hM : MonoLinkGood fl Ar Cls) (hO : OptLinkOn Cls Ar optP) (hK : SkaKeeps Ar) (hU : UnaryKeeps Ar Cls)
    (hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none) (hX : OtherKeeps fl Cls) :
    ∀ cr, CorIn cr → ∀ s f, pokeN cr (Ovum.full s f).toNoun =
      (liftPoke (enc fl) (pokeS Ar) cr (Ovum.full s f)).map fun r => C r.1.toNoun r.2 := by
  intro cr hc s f
  obtain ⟨st, hg, rfl⟩ :=
    pokeReachGood fl Ar Cls env hhe hth hsoft hrf hJA hR hC hM hO hK hU hAt hX cr hc.2.2
  exact pokeModel_fullGood fl Ar Cls env hhe hth hsoft hrf hJA hR hC hM hO hK hU hAt st hg s f

end Links

/-- **`pokeModel_fullReach` on track P's route**: `A.skaPoke = anaArmP …`,
`A.optimize = optimizeP`, `A.sccOf = sccOfP`, `A.jetRoot = jetRootP`, the
class `OptTotal`.  Left: `SpRestGood` (pill, 1,120 cells), `SccImage` (pill,
409 cells), `MonoLinkGood` (pill, `+compiled-mono` and `+compile-unary`),
`JetsOfGood jetsOf` (model), `UnaryKeeps OptTotal` (model, track D),
`OtherKeeps` (pill, the other branches). -/
theorem pokeModel_fullReachP (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
    (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP)
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → Noun}
    {jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun} {newOf : Noun → Noun}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf)
    (hJA : Ar.jetRoot = jetRootP) (hOA : Ar.optimize = optimizeP) (hSA : Ar.sccOf = sccOfP)
    (hR : SpRestGood fl Ar OptTotal env) (hI : SccImage) (hM : MonoLinkGood fl Ar OptTotal)
    (hJ : JetsOfGood jetsOf) (hU : UnaryKeeps Ar OptTotal) (hX : OtherKeeps fl OptTotal) :
    ∀ cr, CorIn cr → ∀ s f, pokeN cr (Ovum.full s f).toNoun =
      (liftPoke (enc fl) (pokeS Ar) cr (Ovum.full s f)).map fun r => C r.1.toNoun r.2 :=
  pokeModel_fullReach fl Ar OptTotal env hhe hth hsoft hrf hJA hR (sccLink_of fl hSA hI) hM
    (optLinkOn_optimizeP hOA) (skaKeeps_of_armP Ar hA hJ) hU
    (fun s a L j h => by rw [hA]; exact anaArmP_atom env jet fold frozen fuel bf regOf jetsOf newOf s a L j h) hX

end Compiler
end Formalization
