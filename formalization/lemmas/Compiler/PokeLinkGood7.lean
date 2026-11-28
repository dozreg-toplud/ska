import lemmas.Compiler.PokeLinkJetsCole
import lemmas.Hoon.Canon

/-!
# `PGood7`: `PGood6` with `back` and `pend` jugs of sets (track P, README Gaps 23)

Two of the guards of `jetsOfP` as facts of the reachable states:

* `BackSets` (`back.cole` is a jug of sets) and `PendSets` (`pend.jets` is a
  jug of sets): `+put:ju` of `+cole-put` and `+uni:in` of `+uni-ju` are
  modelled on sets only.  Checked first on the real compiler:
  `tools/hoon/jetsmodel.hoon`, `%bset` and `%pset` hold after all 32 pokes of
  `invdump2` (`~(apt by ..)` of the jug and `~(apt in ..)` of every value).
* **`jetsOfSets_P`**: `jetsOfP` keeps both (`juPutF_spec`, `uniP_of_sets`
  with `uniR_det`: the loop of `+uni:in` is a function);
* `PGood7`, `good7_empty`, **`good7_full_step`**, `good7_mid`.

The third guard, `RegsMaps` of the regs the analysis returns, is not a state
fact: it is `AnaRegsMaps` (the analysis keeps the four maps of the regs it
is given: `+register-fast` writes them with `put:by` and `put:ju`; checked
`%rmap` at the 16 `%full` pokes), and the jets leaf is asked only where it
holds (`SpLeavesAt7`).

The top over `PGood7`: `SpRestGood7`, `OtherKeeps7`, `pokeModel_fullGood7`,
`pokeReachGood7`, `pokeModel_fullReachG7`, `SpLeavesGood7`,
`spRestGood7_of_leaves`, and **`pokeModel_fullReachP10`** at `jetsOfP`,
`newOfP`: the leaves asked on `PGood7` states, the tail only where the regs
are maps.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF SkaModel.PokeM FinMap

/-! ## Jugs of sets -/

/-- A map whose every value is a set. -/
def JugSets (a : Noun) : Prop := IsMap mugF a ∧ ∀ k v, Get a k v → IsSet mugF v

theorem jugSets_nil : JugSets (A 0) := ⟨IsMap.nil, fun _ _ h => absurd h Get_atom⟩

theorem jugSets_put {a b c out : Noun} (h : JugSets a) (e : juPutF mugF b c a = some out) : JugSets out := by
  obtain ⟨E, hE, -, hm, hg⟩ := juPutF_spec h.1 h.2 e
  refine ⟨hm, fun k v hk => ?_⟩
  rcases (hg k v).1 hk with ⟨-, rfl⟩ | ⟨-, hk'⟩
  · exact hE
  · exact h.2 k v hk'

theorem jugSets_gas : ∀ (ps : List (Noun × Noun)) (a out : Noun), JugSets a → juGasF mugF a ps = some out →
    JugSets out
  | [], a, out, h, e => by simp only [juGasF, Option.some.injEq] at e; exact e ▸ h
  | (b, c) :: rest, a, out, h, e => by
    simp only [juGasF] at e
    split at e
    · rename_i a' ha'
      exact jugSets_gas rest a' out (jugSets_put h ha') e
    · cases e

/-- `new-cores` is a jug of sets. -/
theorem newCoresO_sets {nw nco : Noun} (e : newCoresO nw = some nco) : JugSets nco := by
  unfold newCoresO at e
  obtain ⟨l, -, e⟩ := Option.bind_eq_some_iff.1 e
  obtain ⟨ps, -, e⟩ := Option.bind_eq_some_iff.1 e
  exact jugSets_gas ps _ _ jugSets_nil e

/-- **The loop of `+uni:in` is a function** (it is the run of one Nock
formula, `uni_loop`). -/
theorem uniR_det {a b o1 o2 : Noun} (h1 : UniR mugF a b o1) (h2 : UniR mugF a b o2) : o1 = o2 := by
  have e1 := uni_loop (mug := mugF) layer2 gorIn_morIn_layer2 h1
  rw [uni_loop (mug := mugF) layer2 gorIn_morIn_layer2 h2] at e1
  exact (Option.some.inj e1).symm

/-- `uni:in` of two sets is a set. -/
theorem uniInO_set {d q u : Noun} (hd : IsSet mugF d) (hq : IsSet mugF q) (e : uniInO d q = some u) :
    IsSet mugF u := by
  obtain ⟨out, hR, hS, -, -⟩ := uniP_of_sets _ d q (Nat.le_refl _) hd hq
  unfold uniInO at e
  split at e
  · rename_i hx
    rw [Option.some.injEq] at e
    subst e
    split
    · exact hd
    · rw [uniR_det (Classical.choose_spec hx) hR]; exact hS
  · cases e

/-- The step of `+uni-ju` keeps a jug of sets, on a node whose value is a
set. -/
theorem uniJuStep_sets {n acc out : Noun} (h : JugSets acc) (hn : ∃ p q, n = C p q ∧ IsSet mugF q)
    (e : uniJuStep n acc = some out) : JugSets out := by
  obtain ⟨p, q, rfl, hq⟩ := hn
  simp only [uniJuStep] at e
  obtain ⟨d, hd, e⟩ := Option.bind_eq_some_iff.1 e
  obtain ⟨u, hu, e⟩ := Option.bind_eq_some_iff.1 e
  rw [juGetF_some h.1, Option.some.injEq] at hd
  have hds : IsSet mugF d := by
    rw [← hd]; split
    · rename_i hx; exact h.2 _ _ hx.choose_spec
    · exact IsMap.nil
  have hus := uniInO_set hds hq hu
  obtain ⟨o, ho, hm, hg⟩ := putF_spec mugF acc p u h.1
  rw [ho, Option.some.injEq] at e
  subst e
  refine ⟨hm, fun k v hk => ?_⟩
  rcases (hg k v).1 hk with ⟨-, rfl⟩ | ⟨-, hk'⟩
  · exact hus
  · exact h.2 k v hk'

/-- The cole pair's `back` is a jug of sets. -/
def ColeBack (c : Noun) : Prop := ∃ ca bk, c = C ca bk ∧ JugSets bk

theorem coleStepO_back {seekN core arms hot b c out : Noun} (h : ColeBack c)
    (e : coleStepO seekN core arms hot b c = some out) : ColeBack out := by
  obtain ⟨ca, bk, rfl, hbk⟩ := h
  unfold coleStepO at e
  split at e
  · split at e
    · cases e; exact ⟨ca, bk, rfl, hbk⟩
    · unfold colePutO at e
      split at e
      · simp only at e
        obtain ⟨ca', -, e⟩ := Option.bind_eq_some_iff.1 e
        obtain ⟨bk', hbk', rfl⟩ := Option.map_eq_some_iff.1 e
        exact ⟨ca', bk', rfl, jugSets_put hbk hbk'⟩
      · cases e
    · cases e
  · cases e

/-! ## The clauses and `jetsOfP` -/

/-- `pend.jets` is a jug of sets. -/
def PendSets (j : Noun) : Prop :=
  ∀ r1 r2 r3 r4 pd ca bk, j = C r1 (C r2 (C r3 (C r4 (C pd (C ca bk))))) → ∀ k v, Get pd k v → IsSet mugF v

/-- The step of the jets keeps `BackSets` and `PendSets`. -/
def JetsOfSets {R : Type} (jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun) : Prop :=
  ∀ hot j reg (L L' : LongB FinMap), BackSets j → PendSets j →
    BackSets (jetsOf hot j reg L L') ∧ PendSets (jetsOf hot j reg L L')

/-- **`jetsOfP` keeps `back` and `pend` jugs of sets.** -/
theorem jetsOfSets_P : JetsOfSets jetsOfP := by
  intro hot j reg L L' hb hp
  unfold jetsOfP
  split
  · rename_i hG
    obtain ⟨⟨ro, co, ba, ar, nw, rfl, -, -, -, -⟩, hm, -⟩ := hG
    obtain ⟨r1, r2, r3, r4, pd, ca, bk, rfl, -, -, -, -, hpd, -, hbk⟩ := hm
    cases e : jetsOfO hot (C r1 (C r2 (C r3 (C r4 (C pd (C ca bk)))))) (C ro (C co (C ba (C ar nw)))) L L' with
    | none => exact ⟨hb, hp⟩
    | some j' =>
      simp only [Option.getD_some]
      simp only [jetsOfO] at e
      obtain ⟨nco, hnco, e⟩ := Option.bind_eq_some_iff.1 e
      obtain ⟨pd', hpd', e⟩ := Option.bind_eq_some_iff.1 e
      obtain ⟨cole', hc', rfl⟩ := Option.map_eq_some_iff.1 e
      have hP0 : JugSets pd := ⟨hpd, hp _ _ _ _ _ _ _ rfl⟩
      have hB0 : ColeBack (C ca bk) := ⟨ca, bk, rfl, hbk, hb _ _ _ _ _ _ _ rfl⟩
      have hN := newCoresO_sets hnco
      have hP1 : JugSets pd' :=
        repO_keeps_on uniJuStep JugSets (fun n => ∃ p q, n = C p q ∧ IsSet mugF q)
          (fun _ _ _ hq h e => uniJuStep_sets h hq e) nco pd pd'
          (fun n hn => by
            obtain ⟨k, v, rfl, hk⟩ := (mem_preorder hN.1 n).1 hn
            exact ⟨k, v, rfl, hN.2 k v hk⟩) hP0 hpd'
      obtain ⟨ca', bk', rfl, hB1⟩ :=
        repO_keeps _ ColeBack (fun _ _ _ h e => coleStepO_back h e) _ _ _ hB0 hc'
      refine ⟨fun x1 x2 x3 x4 xp xc xb hx k v hk => ?_, fun x1 x2 x3 x4 xp xc xb hx k v hk => ?_⟩
      · simp only [Noun.cell.injEq] at hx
        obtain ⟨-, -, -, -, -, -, rfl⟩ := hx
        exact hB1.2 k v hk
      · simp only [Noun.cell.injEq] at hx
        obtain ⟨-, -, -, -, rfl, -, -⟩ := hx
        exact hP1.2 k v hk
  · exact ⟨hb, hp⟩

/-- **The invariant**: `PGood6`, `back` and `pend` jugs of sets. -/
structure PGood7 (Cls : Straight (TreapMap mugF) → Prop) (st : PSt) : Prop where
  good6 : PGood6 Cls st
  backSets : BackSets st.jets
  pendSets : PendSets st.jets

theorem good7_empty (Cls : Straight (TreapMap mugF) → Prop) (lib : Lib) : PGood7 Cls emptySt where
  good6 := good6_empty Cls lib
  backSets := fun r1 r2 r3 r4 pd ca bk h k v hk => by
    simp only [emptySt, jets0, Noun.cell.injEq] at h
    obtain ⟨-, -, -, -, -, -, rfl⟩ := h
    exact absurd hk Get_atom
  pendSets := fun r1 r2 r3 r4 pd ca bk h k v hk => by
    simp only [emptySt, jets0, Noun.cell.injEq] at h
    obtain ⟨-, -, -, -, rfl, -, -⟩ := h
    exact absurd hk Get_atom

section Keep

variable {Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)} {Cls : Straight (TreapMap mugF) → Prop}

/-- The jets after a `%full` the model answers are the analysis' jets. -/
theorem pokeS_full_jets {st : PSt} {s f : Noun} {pr : SkaModel.Prod (TreapMap mugF)} {st' : PSt}
    (h : pokeS Ar st (Ovum.full s f) = some (pr, st')) :
    ∃ r, Ar.skaPoke s f st.long st.jets st.hot = some r ∧ st'.jets = r.2.2.1 := by
  simp only [pokeS] at h
  obtain ⟨r, e1, h⟩ := Option.bind_eq_some_iff.1 h
  refine ⟨r, e1, ?_⟩
  split at h
  · cases h; rfl
  · obtain ⟨p, hp, e⟩ := Option.map_eq_some_iff.1 h
    cases e
    unfold compileStep at hp
    obtain ⟨q, e3, hp⟩ := Option.bind_eq_some_iff.1 hp
    obtain ⟨p', hp', e⟩ := Option.map_eq_some_iff.1 hp
    cases e
    rfl

variable {R : Type} {env : Env R}
  {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
  {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → R}
  {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}

theorem sets_poke (hA : Ar.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf)
    (hJS : JetsOfSets jetsOf) (st : PSt) (s f : Noun) (hg : PGood7 Cls st) (r : Bell × LongB FinMap × Noun × Noun)
    (e1 : Ar.skaPoke s f st.long st.jets st.hot = some r) : BackSets r.2.2.1 ∧ PendSets r.2.2.1 := by
  rw [hA] at e1
  obtain ⟨E, n, bg, reg', -, -, -, hjets⟩ := anaArmP_bake e1
  rw [hjets]
  exact hJS _ _ _ _ _ hg.backSets hg.pendSets

/-- **The model's `%full` keeps `PGood7`.** -/
theorem good7_full_step (hA : Ar.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf)
    (hK : SkaKeeps Ar) (hU : UnaryKeeps Ar Cls) (hO : SccOfKeeps Ar) (hC : UnaryCacheKeeps Ar Cls)
    (hSI : SccOfIsK Ar) (hUS : UnarySccsIs Ar) (hTE : TarjanExists) (hJC : JetsOfCole6 jetsOf)
    (hJS : JetsOfSets jetsOf)
    (st : PSt) (s f : Noun) (pr : SkaModel.Prod (TreapMap mugF)) (st' : PSt)
    (hg : PGood7 Cls st) (h : pokeS Ar st (Ovum.full s f) = some (pr, st')) : PGood7 Cls st' := by
  have h6 := good6_full_step hA hK hU hO hC hSI hUS hTE hJC st s f pr st' hg.good6 h
  obtain ⟨r, e1, hj⟩ := pokeS_full_jets h
  obtain ⟨hb, hp⟩ := sets_poke hA hJS st s f hg r e1
  rw [← hj] at hb hp
  exact ⟨h6, hb, hp⟩

/-- **`PGood7` at the state `+compiled-mono` runs on.** -/
theorem good7_mid (hA : Ar.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf)
    (hK : SkaKeeps Ar) (hO : SccOfKeeps Ar) (hSI : SccOfIsK Ar) (hTE : TarjanExists) (hJC : JetsOfCole6 jetsOf)
    (hJS : JetsOfSets jetsOf)
    (st : PSt) (s f : Noun) (hg : PGood7 Cls st) (r : Bell × LongB FinMap × Noun × Noun)
    (e1 : Ar.skaPoke s f st.long st.jets st.hot = some r)
    (q : FinMap Bell Unit × FinMap Bell (FinMap Bell Unit)) (e3 : Ar.sccOf r.1 r.2.1 st.cache.sccs = some q) :
    PGood7 Cls { st with long := r.2.1, jets := r.2.2.1, cache := { st.cache with sccs := q.2 } } := by
  obtain ⟨hb, hp⟩ := sets_poke hA hJS st s f hg r e1
  exact ⟨good6_mid hA hK hO hSI hTE hJC st s f hg.good6 r e1 q e3, hb, hp⟩

end Keep

/-! ## The top over `PGood7` -/

section Links

variable (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
  (Cls : Straight (TreapMap mugF) → Prop)

/-- `SpRestGood` on `PGood7` states. -/
def SpRestGood7 (env : Env Noun) : Prop :=
  ∀ (st : PSt) s f₁ f₂ r1 r2 r3 r4 jRest key, PGood7 Cls st → st.jets = C r1 (C r2 (C r3 (C r4 jRest))) →
    keyRaw (enc fl st) = some key → SpRestAt fl Ar env st s (C f₁ f₂) r1 r2 r3 r4 jRest key

/-- **The pokes other than `%full` keep `PGood7`** (pill: `%dire`, `%jets`,
`%fast`; checked by `jetsmodel.hoon`, `%bset` and `%pset` included). -/
def OtherKeeps7 : Prop :=
  ∀ (st : PSt) ovo p c', PGood7 Cls st → pokeN (enc fl st) ovo = some (C p c') → ¬ Ska.Hot ovo →
    (∀ s f, ovo ≠ (Ovum.full s f).toNoun) → ∃ st', PGood7 Cls st' ∧ enc fl st' = c'

variable {R : Type} {envR : Env R}
  {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
  {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → R}
  {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}

/-- **`pokeModel` on every `%full` at a `PGood7` state.** -/
theorem pokeModel_fullGood7 (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP)
    (hA : Ar.skaPoke = anaArmP envR jet fold frozen fuel bf regOf jetsOf newOf)
    (hJA : Ar.jetRoot = jetRootP) (hR : SpRestGood7 fl Ar Cls env) (hC : SccLink fl Ar sccP)
    (hM : MonoLinkGood6 fl Ar Cls) (hO : OptLinkOn Cls Ar optP) (hK : SkaKeeps Ar) (hU : UnaryKeeps Ar Cls)
    (hSc : SccOfKeeps Ar) (hSI : SccOfIsK Ar) (hTE : TarjanExists) (hJC : JetsOfCole6 jetsOf)
    (hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none) (st : PSt) (hg : PGood7 Cls st) (s f : Noun) :
    pokeN (enc fl st) (Ovum.full s f).toNoun =
      (liftPoke (enc fl) (pokeS Ar) (enc fl st) (Ovum.full s f)).map fun r => C r.1.toNoun r.2 := by
  have hg2 := hg.good6.good5.good4.good3.good2
  cases f with
  | atom a => rw [pokeN_full_atom, liftPoke_enc_fl]; simp [pokeS, hAt]
  | cell f₁ f₂ =>
    refine pokeN_fullAt4 fl Ar Cls hC hO st s f₁ f₂ ?_ (fun r e => ?_) (fun r q e e3 => ?_)
      (optInAt_of_good hK hU st s _ hg2.good)
    · obtain ⟨r1, r2, r3, r4, pd, ca, bk, hj, -⟩ := hg2.good.maps
      obtain ⟨key, hk, -, -⟩ := keyRaw_enc fl st hg2.good.jets.2
      exact skaLinkAt_of fl Ar env hhe hth hsoft hrf st s (C f₁ f₂) r1 r2 r3 r4 (C pd (C ca bk)) key hj hk
        (hR st s f₁ f₂ r1 r2 r3 r4 _ key hg hj hk)
    · obtain ⟨_, hj'⟩ := hK st s _ r hg2.good.maps hg2.good.jets e
      exact jetRootLinkG_of fl Ar hJA st s _ r e hj'
    · exact hM _ r.1 q.1 (good6_mid hA hK hSc hSI hTE hJC st s _ hg.good6 r e q e3)

/-- **Every core the pill reaches is an encoded `PGood7` state.** -/
theorem pokeReachGood7 (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP) (lib : Lib)
    (hA : Ar.skaPoke = anaArmP envR jet fold frozen fuel bf regOf jetsOf newOf)
    (hJA : Ar.jetRoot = jetRootP) (hR : SpRestGood7 fl Ar Cls env) (hC : SccLink fl Ar sccP)
    (hM : MonoLinkGood6 fl Ar Cls) (hO : OptLinkOn Cls Ar optP) (hK : SkaKeeps Ar) (hU : UnaryKeeps Ar Cls)
    (hSc : SccOfKeeps Ar) (hCK : UnaryCacheKeeps Ar Cls) (hSI : SccOfIsK Ar) (hUS : UnarySccsIs Ar)
    (hTE : TarjanExists) (hJC : JetsOfCole6 jetsOf) (hJS : JetsOfSets jetsOf)
    (hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none) (hX : OtherKeeps7 fl Cls) :
    ∀ cr, PokeReach cr → ∃ st, PGood7 Cls st ∧ enc fl st = cr := by
  intro cr h
  induction h with
  | start => exact ⟨emptySt, good7_empty Cls lib, (cor_enc fl).symm⟩
  | @poke c ovo p c' _ hp hh ih =>
    obtain ⟨st, hg, rfl⟩ := ih
    by_cases e : ∃ s f, ovo = (Ovum.full s f).toNoun
    · obtain ⟨s, f, rfl⟩ := e
      rw [pokeModel_fullGood7 fl Ar Cls env hhe hth hsoft hrf hA hJA hR hC hM hO hK hU hSc hSI hTE hJC hAt st hg s f,
        liftPoke_enc_fl] at hp
      cases e' : pokeS Ar st (Ovum.full s f) with
      | none => rw [e'] at hp; cases hp
      | some q =>
        rw [e'] at hp
        simp only [Option.map_some, Option.some.injEq, Noun.cell.injEq] at hp
        exact ⟨q.2, good7_full_step hA hK hU hSc hCK hSI hUS hTE hJC hJS st s f q.1 q.2 hg e', hp.2⟩
    · exact hX st ovo p c' hg hp hh fun s f h => e ⟨s, f, h⟩

end Links

/-- **`pokeModel` on `%full` at every reachable core, over `PGood7`** (as
`pokeModel_fullReachP6`, the links asked on `PGood7` states). -/
theorem pokeModel_fullReachG7 (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
    (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP) (lib : Lib)
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → Noun}
    {jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun} {newOf : Noun → Noun}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf)
    (hJA : Ar.jetRoot = jetRootP) (hOA : Ar.optimize = optimizeP) (hSA : Ar.sccOf = sccOfP)
    (hUA : Ar.compileUnary = compileUnaryP fl)
    (hR : SpRestGood7 fl Ar OptTotal env)
    (hG : ∀ st b sc, PGood6 OptTotal st → ∃ (NM CA V COLE SC0 : Noun) (env : Comp.CallEnv) (inl : Noun → Option Nomm)
      (n : Nomm) (ht : Noun → Nat) (D : Bell → Prop), UnaryGateAt fl st b sc NM CA V COLE SC0 env inl n ht D)
    (hJ : JetsOfGood jetsOf) (hJC : JetsOfCole6 jetsOf) (hJS : JetsOfSets jetsOf)
    (hU : UnaryKeeps Ar OptTotal) (hCK : UnaryCacheKeeps Ar OptTotal) (hUS : UnarySccsIs Ar)
    (hX : OtherKeeps7 fl OptTotal) :
    ∀ cr, CorIn cr → ∀ s f, pokeN cr (Ovum.full s f).toNoun =
      (liftPoke (enc fl) (pokeS Ar) cr (Ovum.full s f)).map fun r => C r.1.toNoun r.2 := by
  have hM := monoLinkGood6_of_gate fl Ar OptTotal hUA hG
  have hI : SccImage := sccImage
  have hSc : SccOfKeeps Ar := sccOfKeeps_of hSA
  have hSI : SccOfIsK Ar := sccOfIsK_of hSA
  have hTE : TarjanExists := tarjanExists
  have hK := skaKeeps_of_armP Ar hA hJ
  have hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none := fun s a L j h => by
    rw [hA]; exact anaArmP_atom env jet fold frozen fuel bf regOf jetsOf newOf s a L j h
  intro cr hc s f
  obtain ⟨st, hg, rfl⟩ := pokeReachGood7 fl Ar OptTotal env hhe hth hsoft hrf lib hA hJA hR (sccLink_of fl hSA hI)
    hM (optLinkOn_optimizeP hOA) hK hU hSc hCK hSI hUS hTE hJC hJS hAt hX cr hc.2.2
  exact pokeModel_fullGood7 fl Ar OptTotal env hhe hth hsoft hrf hA hJA hR (sccLink_of fl hSA hI) hM
    (optLinkOn_optimizeP hOA) hK hU hSc hSI hTE hJC hAt st hg s f

/-! ## The leaves on `PGood7` states, the tail where the regs are maps -/

/-- **The analysis keeps the regs' maps** (analysis owner; `+register-fast`
writes `root`, `core`, `batt`, `arms` with `put:by` and `put:ju`; checked
`%rmap` at the 16 `%full` pokes of `jetsmodel.hoon`). -/
def AnaRegsMaps (env : Env Noun) : Prop :=
  ∀ n root memo reg (r : Callgraph FinMap × FinMap Bell (FDatum FinMap) × Memo FinMap × FDatum FinMap × Noun),
    RegsMaps reg → Ana.skaPoke env n root memo reg = some r → RegsMaps r.2.2.2.2

/-- The leaves of `spRest` at a state, the jets leaf asked only where the
regs the analysis returns are maps. -/
def SpLeavesAt7 (env : Env Noun) (jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool)
    (fold frozen : Bool) (bf : BEnv FinMap → Nat)
    (jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun) (newOf : Noun → Noun)
    (st : PSt) (s f r1 r2 r3 r4 jRest key : Noun) : Prop :=
  ∀ n gr r, Ana.skaCallgraph env n (Sock.mk Cape.yes s, f) st.long.memo (C r1 (C r2 (C r3 (C r4 (A 0))))) = some gr →
    Ana.skaPoke env n (Sock.mk Cape.yes s, f) st.long.memo (C r1 (C r2 (C r3 (C r4 (A 0))))) = some r →
    BakeLinkAt (Sock.mk Cape.yes s, f) r1 r2 r3 r4 jRest (codeNoun flagsOf st.long.code)
        (st.long.code.toNoun fun e => FinMap.setNoun e.calls) (st.long.vars.toNoun FinMap.setNoun)
        (st.long.code.toNoun fun e => e.seek.toNoun) key gr r
        (spE jet fold frozen st (Sock.mk Cape.yes s, f) r) (bf (spE jet fold frozen st (Sock.mk Cape.yes s, f) r)) ∧
    (RegsMaps r.2.2.2.2 → ∀ bg, bakeGraph (spE jet fold frozen st (Sock.mk Cape.yes s, f) r)
        (bf (spE jet fold frozen st (Sock.mk Cape.yes s, f) r)) = some bg →
      TailEndAt (Sock.mk Cape.yes s, f) r1 r2 r3 r4 jRest (codeNoun flagsOf st.long.code)
        (st.long.vars.toNoun FinMap.setNoun) key gr r flagsOf st.long.code (newCode st.long.code bg.1)
        (bg.1.toNoun varEntryNoun) (bg.2.toNoun FinMap.setNoun)
        (jetsOf st.hot st.jets r.2.2.2.2 st.long (spL st r bg)) (newOf r.2.2.2.2))

/-- **The leaves on `PGood7` states** (P: `+bake-graph` and the jets). -/
def SpLeavesGood7 (Cls : Straight (TreapMap mugF) → Prop) (env : Env Noun)
    (jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool)
    (fold frozen : Bool) (bf : BEnv FinMap → Nat)
    (jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun) (newOf : Noun → Noun) : Prop :=
  ∀ (st : PSt) s f₁ f₂ r1 r2 r3 r4 jRest key, PGood7 Cls st → st.jets = C r1 (C r2 (C r3 (C r4 jRest))) →
    keyRaw (enc flagsOf st) = some key →
    SpLeavesAt7 env jet fold frozen bf jetsOf newOf st s (C f₁ f₂) r1 r2 r3 r4 jRest key

/-- The regs the poke starts from are maps at a `PGood6` state. -/
theorem regsMaps_start {Cls : Straight (TreapMap mugF) → Prop} {st : PSt} (hg : PGood6 Cls st)
    {r1 r2 r3 r4 jRest : Noun} (hj : st.jets = C r1 (C r2 (C r3 (C r4 jRest)))) :
    RegsMaps (C r1 (C r2 (C r3 (C r4 (A 0))))) := by
  obtain ⟨x1, x2, x3, x4, pd, ca, bk, hx, h1, h2, h3, h4, -⟩ := hg.good5.good4.good3.good2.good.maps
  rw [hj] at hx
  simp only [Noun.cell.injEq] at hx
  obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hx
  exact ⟨_, _, _, _, A 0, rfl, h1, h2, h3, h4⟩

/-- **`SpRestGood7` at `flagsOf` from the leaves.** -/
theorem spRestGood7_of_leaves (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
    (Cls : Straight (TreapMap mugF) → Prop) (env : Env Noun)
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → Noun}
    {jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun} {newOf : Noun → Noun}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf) (hF : FuelOK env regOf fuel)
    (hreg : ∀ r1 r2 r3 r4 jRest, regOf (C r1 (C r2 (C r3 (C r4 jRest)))) = C r1 (C r2 (C r3 (C r4 (A 0)))))
    (hRM : AnaRegsMaps env)
    (hL : SpLeavesGood7 Cls env jet fold frozen bf jetsOf newOf) : SpRestGood7 flagsOf Ar Cls env :=
  fun st s f₁ f₂ r1 r2 r3 r4 jRest key hg hj hk =>
    spRestAt_of_leaves Ar Cls env hA hF hreg st hg.good6 s f₁ f₂ r1 r2 r3 r4 jRest key hj
      fun n gr r hcg hsp =>
        ⟨(hL st s f₁ f₂ r1 r2 r3 r4 jRest key hg hj hk n gr r hcg hsp).1,
          (hL st s f₁ f₂ r1 r2 r3 r4 jRest key hg hj hk n gr r hcg hsp).2
            (hRM _ _ _ _ r (regsMaps_start hg.good6 hj) hsp)⟩

/-- **`pokeModel` on `%full` at every reachable core, over `PGood7`, at the
model's jets** (`jetsOfP`, `newOfP`), the fuel `anaFuel env regOfP`, the
regs `regOfP`, the flags `flagsOf`.  `JetsOfGood`, `JetsOfCole6`,
`JetsOfSets` of `jetsOfP` proved.  Left, with owners: `SpLeavesGood7` (P:
`BakeLinkAt`, and `TailEndAt` at `PGood7` states where the regs are maps),
`AnaRegsMaps` (the analysis keeps the regs' maps: analysis owner), the gate
at `PGood6` states (K), `UnaryKeeps OptTotal` (D), `UnaryCacheKeeps`,
`UnarySccsIs` (K / Q), `OtherKeeps7` (P: `%dire`, `%jets`, `%fast`), the
four `env` equations. -/
theorem pokeModel_fullReachP10 (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
    (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP) (lib : Lib)
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    {bf : BEnv FinMap → Nat}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen (anaFuel env regOfP) bf regOfP jetsOfP newOfP)
    (hJA : Ar.jetRoot = jetRootP) (hOA : Ar.optimize = optimizeP) (hSA : Ar.sccOf = sccOfP)
    (hUA : Ar.compileUnary = compileUnaryP flagsOf)
    (hL : SpLeavesGood7 OptTotal env jet fold frozen bf jetsOfP newOfP) (hRM : AnaRegsMaps env)
    (hG : ∀ st b sc, PGood6 OptTotal st → ∃ (NM CA V COLE SC0 : Noun) (env : Comp.CallEnv) (inl : Noun → Option Nomm)
      (n : Nomm) (ht : Noun → Nat) (D : Bell → Prop), UnaryGateAt flagsOf st b sc NM CA V COLE SC0 env inl n ht D)
    (hU : UnaryKeeps Ar OptTotal) (hCK : UnaryCacheKeeps Ar OptTotal) (hUS : UnarySccsIs Ar)
    (hX : OtherKeeps7 flagsOf OptTotal) :
    ∀ cr, CorIn cr → ∀ s f, pokeN cr (Ovum.full s f).toNoun =
      (liftPoke (enc flagsOf) (pokeS Ar) cr (Ovum.full s f)).map fun r => C r.1.toNoun r.2 :=
  pokeModel_fullReachG7 flagsOf Ar env hhe hth hsoft hrf lib hA hJA hOA hSA hUA
    (spRestGood7_of_leaves Ar OptTotal env hA (fuelOK_anaFuel env regOfP) regOfP_shape hRM hL) hG
    jetsOfGood_P jetsOfCole6_P jetsOfSets_P hU hCK hUS hX

end Compiler
end Formalization
