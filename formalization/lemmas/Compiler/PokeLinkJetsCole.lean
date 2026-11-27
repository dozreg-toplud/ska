import lemmas.Compiler.PokeLinkJetsP

/-!
# `JetsOfCole6 jetsOfP` (track P, README Gaps 23)

The fold of `+ska-cole-update` in the model (`coleStepO` over the keys of the
new table that the old one lacks) keeps `ColeCoh` and `ColeDom`, on nouns:

* `getF_iff_get`, `juPutF_spec` (`+put:ju` on a jug of sets: the set under
  the key gains the element);
* `ringOfO`: the ring the step puts for a bell noun, a function of the bell
  alone (its `seek`, `core`, `arms`, `hot`), so a bell met twice would get
  the same ring; `coleStepO_cases`;
* the invariant `ColeInv`: `call` and `back` maps, `back` a jug of sets,
  `CohN` (`call` maps `c` to `r` iff `c` is in `back` of `r`), and every key
  of `call` an old key or a new one put with its `ringOfO` (`coleInv_put`:
  `+cole-put` of a new bell with its ring keeps it: a bell with another ring
  would be old, `coleCohM_put_bad`);
* `repO_keeps_on` (a fold over the nodes of a tree with a property of the
  nodes), `newKeys_nodes`;
* **`jetsOfCole6_P`**: `JetsOfCole6 jetsOfP`;
* **`pokeModel_fullReachP9`**: the top at `jetsOfP`, `newOfP` with no
  hypothesis on them left but the leaf `SpLeavesGood`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF SkaModel.PokeM

/-- `+get:by` finds `v` iff the map holds `[k v]`. -/
theorem getF_iff_get {a k v : Noun} (h : IsMap mugF a) : getF mugF k a = some (C (A 0) v) ↔ Get a k v := by
  constructor
  · intro H
    by_cases hx : ∃ v', Get a k v'
    · obtain ⟨v', hv'⟩ := hx
      rw [getF_some h hv', Option.some.injEq, Noun.cell.injEq] at H
      exact H.2 ▸ hv'
    · rw [getF_none h (fun v' hv' => hx ⟨v', hv'⟩)] at H
      cases H
  · exact getF_some h

open Classical in
/-- **`+put:ju` on a jug of sets.** -/
theorem juPutF_spec {a b c out : Noun} (h : IsMap mugF a) (hs : ∀ k v, Get a k v → IsSet mugF v)
    (e : juPutF mugF b c a = some out) :
    ∃ E, IsSet mugF E ∧ (∀ k, Has E k ↔ k = c ∨ ∃ s, Get a b s ∧ Has s k) ∧ IsMap mugF out ∧
      ∀ k v, Get out k v ↔ (k = b ∧ v = E) ∨ (k ≠ b ∧ Get a k v) := by
  unfold juPutF at e
  rw [juGetF_some h, Option.bind_some] at e
  -- the set under `b`
  have hd : ∃ d, IsSet mugF d ∧ (∀ k, Has d k ↔ ∃ s, Get a b s ∧ Has s k) ∧
      d = (if hx : ∃ s, Get a b s then hx.choose else A 0) := by
    by_cases hx : ∃ s, Get a b s
    · refine ⟨hx.choose, hs _ _ hx.choose_spec, fun k => ⟨fun hk => ⟨_, hx.choose_spec, hk⟩, ?_⟩, by rw [dif_pos hx]⟩
      rintro ⟨s, hs', hk⟩
      rw [Get.unique h hx.choose_spec hs']
      exact hk
    · refine ⟨A 0, IsMap.nil, fun k => ⟨fun hk => absurd hk Get_atom, fun ⟨s, hs', _⟩ => absurd ⟨s, hs'⟩ hx⟩,
        by rw [dif_neg hx]⟩
  obtain ⟨d, hdS, hdH, hdE⟩ := hd
  rw [← hdE] at e
  obtain ⟨E, hE, hES, hEH⟩ := putInF_spec mugF d c hdS
  rw [hE, Option.bind_some] at e
  obtain ⟨o, ho, hm, hg⟩ := putF_spec mugF a b E h
  rw [ho, Option.some.injEq] at e
  subst e
  exact ⟨E, hES, fun k => by rw [hEH, hdH], hm, hg⟩

/-- The ring the gate of `+ska-cole-update` puts for a bell noun, if any. -/
noncomputable def ringOfO (seekN core arms hot x : Noun) : Option Noun :=
  match getF mugF x seekN with
  | some (Noun.cell (Noun.atom 0) sek) =>
    match coleMatchP x sek core arms hot with
    | some (Noun.cell (Noun.atom 0) r) => some r
    | _ => none
  | _ => none

theorem coleStepO_cases {seekN core arms hot x c out : Noun} (e : coleStepO seekN core arms hot x c = some out) :
    out = c ∨ ∃ r, ringOfO seekN core arms hot x = some r ∧ colePutO x r c = some out := by
  unfold coleStepO at e
  split at e
  · rename_i sek hsk
    split at e
    · cases e; exact Or.inl rfl
    · rename_i r hr
      exact Or.inr ⟨r, by simp only [ringOfO, hsk, hr], e⟩
    · cases e
  · cases e

/-- `call` maps `c` to `r` iff `c` is in `back` of `r`. -/
def CohN (ca bk : Noun) : Prop := ∀ c r, Get ca c r ↔ ∃ S, Get bk r S ∧ Has S c

/-- A bell noun of the fold: a new key. -/
def NewKeyN (L L' : LongB FinMap) (n : Noun) : Prop :=
  ∃ b : Bell, n = TKey.enc b ∧ FinMap.get L.code b = none ∧ FinMap.get L'.code b ≠ none

/-- The invariant of the fold. -/
def ColeInv (L L' : LongB FinMap) (rg : Noun → Option Noun) (c : Noun) : Prop :=
  ∃ ca bk, c = C ca bk ∧ IsMap mugF ca ∧ IsMap mugF bk ∧ (∀ k v, Get bk k v → IsSet mugF v) ∧ CohN ca bk ∧
    ∀ k r, Get ca k r → (∃ b : Bell, k = TKey.enc b ∧ FinMap.get L.code b ≠ none) ∨ (rg k = some r ∧ NewKeyN L L' k)

/-- **`+cole-put` of a new bell with its ring keeps the invariant.** -/
theorem coleInv_put {L L' : LongB FinMap} {rg : Noun → Option Noun} {x r c out : Noun} (hQ : NewKeyN L L' x)
    (hrx : rg x = some r) (hI : ColeInv L L' rg c) (e : colePutO x r c = some out) : ColeInv L L' rg out := by
  obtain ⟨ca, bk, rfl, hca, hbk, hbs, hcoh, hdom⟩ := hI
  unfold colePutO at e
  split at e
  · simp only at e
    obtain ⟨ca', hca', e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨bk', hbk', rfl⟩ := Option.map_eq_some_iff.1 e
    obtain ⟨o, ho, hm, hcg⟩ := putF_spec mugF ca x r hca
    rw [ho, Option.some.injEq] at hca'
    subst hca'
    obtain ⟨E, hES, hEH, hbm, hbg⟩ := juPutF_spec hbk hbs hbk'
    refine ⟨o, bk', rfl, hm, hbm, ?_, ?_, ?_⟩
    · intro k v hg
      rcases (hbg k v).1 hg with ⟨-, rfl⟩ | ⟨-, hg'⟩
      · exact hES
      · exact hbs k v hg'
    · intro k v
      rw [hcg]
      constructor
      · rintro (⟨rfl, rfl⟩ | ⟨hk, hg⟩)
        · exact ⟨E, (hbg _ _).2 (Or.inl ⟨rfl, rfl⟩), (hEH _).2 (Or.inl rfl)⟩
        · obtain ⟨S, hS, hSk⟩ := (hcoh k v).1 hg
          by_cases hv : v = r
          · subst hv; exact ⟨E, (hbg _ _).2 (Or.inl ⟨rfl, rfl⟩), (hEH _).2 (Or.inr ⟨S, hS, hSk⟩)⟩
          · exact ⟨S, (hbg _ _).2 (Or.inr ⟨hv, hS⟩), hSk⟩
      · rintro ⟨S, hS, hSk⟩
        rcases (hbg _ _).1 hS with ⟨e1, e2⟩ | ⟨hv, hS'⟩
        · subst e2
          rcases (hEH _).1 hSk with hk | ⟨s, hs, hsk⟩
          · exact Or.inl ⟨hk, e1⟩
          · have hg := (hcoh k r).2 ⟨s, hs, hsk⟩
            by_cases hk : k = x
            · exact Or.inl ⟨hk, e1⟩
            · exact Or.inr ⟨hk, e1 ▸ hg⟩
        · have hg := (hcoh k v).2 ⟨S, hS', hSk⟩
          by_cases hk : k = x
          · exfalso
            subst hk
            obtain ⟨b, hb, hnew, -⟩ := hQ
            rcases hdom k v hg with ⟨b', hb', hold⟩ | ⟨hrg, -⟩
            · rw [hb] at hb'
              exact hold (TKey.enc_inj _ _ hb' ▸ hnew)
            · rw [hrx, Option.some.injEq] at hrg
              exact hv hrg.symm
          · exact Or.inr ⟨hk, hg⟩
    · intro k v hg
      rcases (hcg k v).1 hg with ⟨rfl, rfl⟩ | ⟨-, hg'⟩
      · exact Or.inr ⟨hrx, hQ⟩
      · exact hdom k v hg'
  · cases e

/-- A fold keeps a property that each step keeps at the tree's nodes. -/
theorem repO_keeps_on (f : Noun → Noun → Option Noun) (P Q : Noun → Prop)
    (hf : ∀ n acc out, Q n → P acc → f n acc = some out → P out) :
    ∀ t acc out, (∀ n ∈ preorder t, Q n) → P acc → repO f t acc = some out → P out
  | Noun.atom 0, acc, out, _, h, e => by
    simp only [repO, Option.some.injEq] at e
    exact e ▸ h
  | Noun.atom (_ + 1), _, _, _, _, e => by simp [repO] at e
  | Noun.cell _ (Noun.atom _), _, _, _, _, e => by simp [repO] at e
  | Noun.cell n (Noun.cell l r), acc, out, hq, h, e => by
    simp only [repO] at e
    obtain ⟨a, ha, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨b, hb, e⟩ := Option.bind_eq_some_iff.1 e
    have hq' : ∀ m, m ∈ preorder (C n (C l r)) → Q m := hq
    simp only [preorder, List.mem_cons, List.mem_append] at hq'
    exact repO_keeps_on f P Q hf r b out (fun m hm => hq' m (Or.inr (Or.inr hm)))
      (repO_keeps_on f P Q hf l a b (fun m hm => hq' m (Or.inr (Or.inl hm)))
        (hf _ _ _ (hq' n (Or.inl rfl)) h ha) hb) e

/-- The nodes of the set noun of `newKeysM` are new keys. -/
theorem newKeys_nodes (L L' : LongB FinMap) : ∀ n ∈ preorder (FinMap.setNoun (newKeysM L L')), NewKeyN L L' n := by
  intro n hn
  rw [FinMap.preorder_setNoun'] at hn
  obtain ⟨⟨b, u⟩, hm, rfl⟩ := List.mem_map.1 hn
  have h := (FinMap.mem_rap _ _ _).1 hm
  simp only [newKeysM] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Option.isSome_iff_ne_none] at hc
    exact ⟨b, rfl, hc.1, hc.2⟩
  · cases h

/-- **`jetsOfP` keeps `ColeCoh` and `ColeDom`.** -/
theorem jetsOfCole6_P : JetsOfCole6 jetsOfP := by
  intro hot j reg L L' hcoh hdom hkeep
  have fallback : ColeCoh j ∧ ColeDom j L'.code := ⟨hcoh, fun r1 r2 r3 r4 pd ca bk he c r hc => by
    obtain ⟨b, rfl, hb⟩ := hdom r1 r2 r3 r4 pd ca bk he c r hc
    exact ⟨b, rfl, hkeep b hb⟩⟩
  unfold jetsOfP
  split
  · rename_i hG
    obtain ⟨⟨ro, co, ba, ar, nw, rfl, -, -, -, -⟩, ⟨r1, r2, r3, r4, pd, ca, bk, rfl, -, -, -, -, -, hca, hbk⟩, hbs⟩ := hG
    cases e : jetsOfO hot (C r1 (C r2 (C r3 (C r4 (C pd (C ca bk)))))) (C ro (C co (C ba (C ar nw)))) L L' with
    | none => simpa only [Option.getD_none] using fallback
    | some j' =>
      simp only [Option.getD_some]
      simp only [jetsOfO] at e
      obtain ⟨nco, -, e⟩ := Option.bind_eq_some_iff.1 e
      obtain ⟨pd', -, e⟩ := Option.bind_eq_some_iff.1 e
      obtain ⟨cole', hc', rfl⟩ := Option.map_eq_some_iff.1 e
      have h0 : ColeInv L L' (ringOfO (L'.code.toNoun fun e => e.seek.toNoun) co ar hot) (C ca bk) := by
        refine ⟨ca, bk, rfl, hca, hbk, hbs r1 r2 r3 r4 pd ca bk rfl, fun c r => ?_, fun k r hg => ?_⟩
        · rw [← getF_iff_get hca, hcoh r1 r2 r3 r4 pd ca bk rfl c r]
          simp only [getF_iff_get hbk]
        · obtain ⟨b, hb, hold⟩ := hdom r1 r2 r3 r4 pd ca bk rfl k r ((getF_iff_get hca).2 hg)
          exact Or.inl ⟨b, hb, hold⟩
      have hI := repO_keeps_on _ (ColeInv L L' (ringOfO (L'.code.toNoun fun e => e.seek.toNoun) co ar hot))
        (NewKeyN L L') (fun n acc out hq h e => by
          rcases coleStepO_cases e with rfl | ⟨r, hr, hp⟩
          · exact h
          · exact coleInv_put hq hr h hp) _ _ _ (newKeys_nodes L L') h0 hc'
      obtain ⟨ca', bk', rfl, hca', hbk', -, hcoh', hdom'⟩ := hI
      constructor
      · intro a1 a2 a3 a4 apd aca abk he c r
        simp only [Noun.cell.injEq] at he
        obtain ⟨-, -, -, -, -, rfl, rfl⟩ := he
        rw [getF_iff_get hca', hcoh' c r]
        simp only [getF_iff_get hbk']
      · intro a1 a2 a3 a4 apd aca abk he c r hc
        simp only [Noun.cell.injEq] at he
        obtain ⟨-, -, -, -, -, rfl, rfl⟩ := he
        rcases hdom' c r ((getF_iff_get hca').1 hc) with ⟨b, hb, hold⟩ | ⟨-, b, hb, -, hnew⟩
        · exact ⟨b, hb, hkeep b hold⟩
        · exact ⟨b, hb, hnew⟩
  · exact fallback

/-- **`pokeModel` on `%full` at every reachable core, at the model's jets,
with `JetsOfGood` and `JetsOfCole6` discharged.**  Left, with owners:
`SpLeavesGood` at `jetsOfP`, `newOfP` (P: `BakeLinkAt` and the tail
`TailEndAt`, which carries the guards of `jetsOfP`), the gate at `PGood6`
states (K; P's fields `got`, `nomm`, `cole` proved), `UnaryKeeps OptTotal`
(D), `UnaryCacheKeeps`, `UnarySccsIs` (K / Q), `OtherKeeps6` (P), the four
`env` equations. -/
theorem pokeModel_fullReachP9 (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
    (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP) (lib : Lib)
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    {bf : BEnv FinMap → Nat}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen (anaFuel env regOfP) bf regOfP jetsOfP newOfP)
    (hJA : Ar.jetRoot = jetRootP) (hOA : Ar.optimize = optimizeP) (hSA : Ar.sccOf = sccOfP)
    (hUA : Ar.compileUnary = compileUnaryP flagsOf)
    (hL : SpLeavesGood OptTotal env jet fold frozen bf jetsOfP newOfP)
    (hG : ∀ st b sc, PGood6 OptTotal st → ∃ (NM CA V COLE SC0 : Noun) (env : Comp.CallEnv) (inl : Noun → Option Nomm)
      (n : Nomm) (ht : Noun → Nat) (D : Bell → Prop), UnaryGateAt flagsOf st b sc NM CA V COLE SC0 env inl n ht D)
    (hU : UnaryKeeps Ar OptTotal) (hCK : UnaryCacheKeeps Ar OptTotal) (hUS : UnarySccsIs Ar)
    (hX : OtherKeeps6 flagsOf OptTotal) :
    ∀ cr, CorIn cr → ∀ s f, pokeN cr (Ovum.full s f).toNoun =
      (liftPoke (enc flagsOf) (pokeS Ar) cr (Ovum.full s f)).map fun r => C r.1.toNoun r.2 :=
  pokeModel_fullReachP8 Ar env hhe hth hsoft hrf lib hA hJA hOA hSA hUA hL hG jetsOfCole6_P hU hCK hUS hX

end Compiler
end Formalization
