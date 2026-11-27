import lemmas.Compiler.PokeLinkTop7
import lemmas.Hoon.Ju
import lemmas.Hoon.UniIn
import lemmas.Hoon.RepBy

/-!
# The model of the jets after `+ska-poke`: `jetsOfP`, `newOfP` (track P, README Gaps 23)

The tail of `+ska-poke` (pushes 10, 11 and the end of `spRest`):

    =/  new-cores  (~(gas ju *(jug path sock)) (turn new.regs |=([p=path s=sock *] [p s])))
    =.  jets.lon  jets.lon(root root.regs, core core.regs, batt batt.regs, arms arms.regs,
                           pend ((uni-ju pend.jets.lon) new-cores))
    ..
    :-  [root-bell (flop new.regs)]
    (ska-cole-update lon ~(key by new-code) hot)

The model, on nouns (`regs = [root core batt arms new]`, the jets noun
`[root core batt arms pend [call back]]`):

* `newCoresO`: `+gas:ju` from `~` of the pairs `[p s]` of the list `new`;
* `uniJuO`: `+uni-ju`, the fold `repO` (the order of `+rep:by`: node, left,
  right) of `put:by` of `uni:in` of `get:ju` (`uniInO`: the product of the
  pill's `uni:in`, `uni_in_gate`);
* `coleMatchP`: the pill's `+cole-match` (arm `0x57dc` of `ana`) read back as
  a function: the gate slammed on `[b sek core arms hot]`;
* `coleStepO`: the gate of `+ska-cole-update`: `got:by` of `seek`, the match,
  and on `[~ r]` `+cole-put` (`put:by` on `call`, `put:ju` on `back`), the
  ring checked to be a `Ring`;
* `jetsOfO`: the whole tail on the jets, the bells those of `newKeysM L L'`
  (the keys of the new table that the old one lacks, which are the keys of
  `new-code`), in the order of `+rep:in` on their set noun;
* **`jetsOfP`**: `jetsOfO` where the regs' four maps are maps, the jets noun
  is `JetsMaps` with `back` a jug of sets (`BackSets`), and `jetsOfO`
  answers; else the old jets.  At a reachable state these hold (the link
  `TailEndAt` at `jetsOfP` asks for the pill's product, so it asks for them).
* **`newOfP`**: `(flop new.regs)`.

Checked first on the real compiler: `tools/hoon/jetsmodel.hoon` (the 32
pokes of `invdump2.hoon`), `%jmod` (the jets after each `%full` equal this
model, computed from the old state, the regs of `+ska-callgraph` rerun, and
the new `code` and `seek`) and `%nnew` (the poke's list is `(flop new.regs)`)
hold at all 16 `%full` pokes, `call.cole` growing at four of them.

* **`jetsOfGood_P`**: `JetsOfGood jetsOfP`.
* **`pokeModel_fullReachP8`**: the top at `jetsOfP`, `newOfP`, with
  `JetsOfGood` discharged.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF SkaModel.PokeM FinMap

/-- `+rep` with a step that may crash, in the order of `repF` (node, left,
right). -/
def repO (f : Noun → Noun → Option Noun) : Noun → Noun → Option Noun
  | Noun.atom 0, acc => some acc
  | Noun.cell n (Noun.cell l r), acc => (f n acc).bind fun a => (repO f l a).bind (repO f r)
  | _, _ => none

/-- A property every step keeps is kept by the fold. -/
theorem repO_keeps (f : Noun → Noun → Option Noun) (P : Noun → Prop)
    (hf : ∀ n acc out, P acc → f n acc = some out → P out) :
    ∀ t acc out, P acc → repO f t acc = some out → P out
  | Noun.atom 0, acc, out, h, e => by
    simp only [repO, Option.some.injEq] at e
    exact e ▸ h
  | Noun.atom (_ + 1), _, _, _, e => by simp [repO] at e
  | Noun.cell _ (Noun.atom _), _, _, _, e => by simp [repO] at e
  | Noun.cell n (Noun.cell l r), acc, out, h, e => by
    simp only [repO] at e
    obtain ⟨a, ha, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨b, hb, e⟩ := Option.bind_eq_some_iff.1 e
    exact repO_keeps f P hf r b out (repO_keeps f P hf l a b (hf _ _ _ h ha) hb) e

/-- `put:by` keeps a map a map. -/
theorem isMap_of_putF {a k v out : Noun} (h : IsMap mugF a) (e : putF mugF k v a = some out) : IsMap mugF out := by
  obtain ⟨o, ho, hm, -⟩ := putF_spec mugF a k v h
  rw [ho, Option.some.injEq] at e
  exact e ▸ hm

/-- `put:ju` keeps a map a map. -/
theorem isMap_of_juPutF {a b c out : Noun} (h : IsMap mugF a) (e : juPutF mugF b c a = some out) :
    IsMap mugF out := by
  unfold juPutF at e
  obtain ⟨d, -, e⟩ := Option.bind_eq_some_iff.1 e
  obtain ⟨x, -, e⟩ := Option.bind_eq_some_iff.1 e
  exact isMap_of_putF h e

/-! ## The parts -/

/-- The pair `[p s]` of an element `[p s clue]` of `new.regs` (the gate of
`+turn`). -/
def turnPairO : Noun → Option (Noun × Noun)
  | Noun.cell p (Noun.cell s _) => some (p, s)
  | _ => none

/-- `new-cores`: `+gas:ju` from `~` of the pairs of the list `new`. -/
def newCoresO (nw : Noun) : Option Noun :=
  (nounList? nw).bind fun l => (l.mapM turnPairO).bind fun ps => juGasF mugF (A 0) ps

open Classical in
/-- `~(uni in a) b`: the product of the pill's gate where `uni:in` returns
(`uni_in_gate`: `UniR`), else a crash. -/
noncomputable def uniInO (a b : Noun) : Option Noun :=
  if h : ∃ out, UniR mugF a b out then some (if a = b then a else Classical.choose h) else none

/-- The step of `+uni-ju`: `(~(put by acc) p (~(uni in (~(get ju acc) p)) q))`. -/
noncomputable def uniJuStep : Noun → Noun → Option Noun
  | Noun.cell p q, acc => (juGetF mugF p acc).bind fun d => (uniInO d q).bind fun u => putF mugF p u acc
  | _, _ => none

/-- `((uni-ju a) b)`. -/
noncomputable def uniJuO (a b : Noun) : Option Noun := repO uniJuStep b a

/-- The call of the pill's `+cole-match` on `[sam ana]`: the gate (arm
`0x57dc` of `ana`) with its sample replaced. -/
def coleMatchCall : Noun :=
  C (A 8) (C (C (A 9) (C (A 0x57dc) (C (A 0) (A 3))))
    (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))

/-- **`+cole-match` read back**: the pill's gate slammed on
`[b sek core arms hot]`. -/
noncomputable def coleMatchP (b sek core arms hot : Noun) : Option Noun :=
  nock (C (C b (C sek (C core (C arms hot)))) ana) coleMatchCall

open Classical in
/-- `+cole-put` of `b` with ring `r` into `[call back]`, the ring checked to
be a `Ring` (the pill does not check: where `+cole-match` returns no ring
noun, the model has no answer). -/
noncomputable def colePutO (b r c : Noun) : Option Noun :=
  if ∃ n : Ring, r = n.toNoun then
    match c with
    | Noun.cell ca bk => (putF mugF b r ca).bind fun ca' => (juPutF mugF r b bk).map fun bk' => C ca' bk'
    | _ => none
  else none

/-- The gate of `+ska-cole-update` on a bell noun `b`: `got:by` of `seek`,
the match on `core`, `arms`, `hot`, and `+cole-put` on a ring. -/
noncomputable def coleStepO (seekN core arms hot : Noun) (b c : Noun) : Option Noun :=
  match getF mugF b seekN with
  | some (Noun.cell (Noun.atom 0) sek) =>
    match coleMatchP b sek core arms hot with
    | some (Noun.atom 0) => some c
    | some (Noun.cell (Noun.atom 0) r) => colePutO b r c
    | _ => none
  | _ => none

/-- The keys of `L'.code` that `L.code` lacks (the keys of `new-code`). -/
noncomputable def newKeysM (L L' : LongB FinMap) : FinMap Bell Unit :=
  ⟨fun b => if (FinMap.get L.code b).isNone && (FinMap.get L'.code b).isSome then some () else none,
    L'.code.supp, fun k hk => by
      apply FinMap.mem_supp
      intro h
      apply hk
      simp [FinMap.get, h]⟩

/-- **The tail on the jets**: the edit from the regs and `+uni-ju`, then
`+ska-cole-update` on the new keys at the new `seek`. -/
noncomputable def jetsOfO (hot j reg : Noun) (L L' : LongB FinMap) : Option Noun :=
  match j, reg with
  | Noun.cell _ (Noun.cell _ (Noun.cell _ (Noun.cell _ (Noun.cell pd cole)))),
    Noun.cell ro (Noun.cell co (Noun.cell ba (Noun.cell ar nw))) =>
    (newCoresO nw).bind fun nco => (uniJuO pd nco).bind fun pd' =>
      (repO (coleStepO (L'.code.toNoun fun e => e.seek.toNoun) co ar hot) (FinMap.setNoun (newKeysM L L')) cole).map
        fun cole' => C ro (C co (C ba (C ar (C pd' cole'))))
  | _, _ => none

/-- The regs' four maps are maps. -/
def RegsMaps (reg : Noun) : Prop :=
  ∃ ro co ba ar nw, reg = C ro (C co (C ba (C ar nw))) ∧ IsMap mugF ro ∧ IsMap mugF co ∧ IsMap mugF ba ∧
    IsMap mugF ar

/-- `back.cole` is a jug of sets. -/
def BackSets (j : Noun) : Prop :=
  ∀ r1 r2 r3 r4 pd ca bk, j = C r1 (C r2 (C r3 (C r4 (C pd (C ca bk))))) → ∀ k v, Get bk k v → IsSet mugF v

open Classical in
/-- **The model of the jets after `+ska-poke`.** -/
noncomputable def jetsOfP (hot j reg : Noun) (L L' : LongB FinMap) : Noun :=
  if RegsMaps reg ∧ JetsMaps j ∧ BackSets j then (jetsOfO hot j reg L L').getD j else j

/-- **The poke's list**: `(flop new.regs)`. -/
def newOfP : Noun → Noun
  | Noun.cell _ (Noun.cell _ (Noun.cell _ (Noun.cell _ nw))) => ((nounList? nw).map fun l => listN l.reverse).getD (A 0)
  | _ => A 0

/-! ## `JetsOfGood` -/

/-- The cole pair keeps its maps and ring values. -/
def ColePairGood (c : Noun) : Prop :=
  ∃ ca bk, c = C ca bk ∧ IsMap mugF ca ∧ IsMap mugF bk ∧ ∀ k v, Get ca k v → ∃ n : Ring, v = n.toNoun

theorem colePutO_good {b r c out : Noun} (h : ColePairGood c) (e : colePutO b r c = some out) :
    ColePairGood out := by
  obtain ⟨ca, bk, rfl, hca, hbk, hv⟩ := h
  unfold colePutO at e
  split at e
  · rename_i hr
    simp only at e
    obtain ⟨ca', hca', e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨bk', hbk', rfl⟩ := Option.map_eq_some_iff.1 e
    obtain ⟨o, ho, hm, hg⟩ := putF_spec mugF ca b r hca
    rw [ho, Option.some.injEq] at hca'
    subst hca'
    refine ⟨o, bk', rfl, hm, isMap_of_juPutF hbk hbk', fun k v hk => ?_⟩
    rcases (hg k v).1 hk with ⟨-, rfl⟩ | ⟨-, hk'⟩
    · exact hr
    · exact hv k v hk'
  · cases e

theorem coleStepO_good (seekN core arms hot : Noun) (b c out : Noun) (h : ColePairGood c)
    (e : coleStepO seekN core arms hot b c = some out) : ColePairGood out := by
  unfold coleStepO at e
  split at e
  · split at e
    · cases e; exact h
    · exact colePutO_good h e
    · cases e
  · cases e

theorem uniJuStep_map (n acc out : Noun) (h : IsMap mugF acc) (e : uniJuStep n acc = some out) : IsMap mugF out := by
  match n, e with
  | Noun.cell p q, e =>
    simp only [uniJuStep] at e
    obtain ⟨d, -, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨u, -, e⟩ := Option.bind_eq_some_iff.1 e
    exact isMap_of_putF h e

/-- **`jetsOfP` keeps the jet maps.** -/
theorem jetsOfGood_P : JetsOfGood jetsOfP := by
  intro hot j reg L L' hm hg
  unfold jetsOfP
  split
  · rename_i hG
    obtain ⟨⟨ro, co, ba, ar, nw, rfl, hro, hco, hba, har⟩, -, -⟩ := hG
    obtain ⟨r1, r2, r3, r4, pd, ca, bk, rfl, h1, h2, h3, h4, hpd, hca, hbk⟩ := hm
    cases e : jetsOfO hot (C r1 (C r2 (C r3 (C r4 (C pd (C ca bk)))))) (C ro (C co (C ba (C ar nw)))) L L' with
    | none => exact ⟨⟨r1, r2, r3, r4, pd, ca, bk, rfl, h1, h2, h3, h4, hpd, hca, hbk⟩, hg⟩
    | some j' =>
      simp only [Option.getD_some]
      simp only [jetsOfO] at e
      obtain ⟨nco, -, e⟩ := Option.bind_eq_some_iff.1 e
      obtain ⟨pd', hpd', e⟩ := Option.bind_eq_some_iff.1 e
      obtain ⟨cole', hc', rfl⟩ := Option.map_eq_some_iff.1 e
      have hpdm : IsMap mugF pd' := repO_keeps uniJuStep (IsMap mugF) uniJuStep_map nco pd pd' hpd hpd'
      obtain ⟨⟨cm, hcm, -, hcv⟩, hhot⟩ := hg
      have hcm' : cm = ca := by simp [nock_exec] at hcm; exact hcm.symm
      rw [hcm'] at hcv
      have h0 : ColePairGood (C ca bk) := ⟨ca, bk, rfl, hca, hbk, hcv⟩
      obtain ⟨ca', bk', rfl, hca', hbk', hv'⟩ :=
        repO_keeps _ ColePairGood (fun n acc out h e => coleStepO_good _ _ _ _ n acc out h e) _ _ _ h0 hc'
      exact ⟨⟨ro, co, ba, ar, pd', ca', bk', rfl, hro, hco, hba, har, hpdm, hca', hbk'⟩,
        ⟨ca', by simp [nock_exec], hca', hv'⟩, hhot⟩
  · exact ⟨hm, hg⟩

/-! ## The top at the model -/

/-- **`pokeModel` on `%full` at every reachable core, at the model's jets**
(`jetsOfP`, `newOfP`), the fuel `anaFuel env regOfP`, the regs `regOfP`, the
flags `flagsOf`, over `PGood6`.  Left, with owners: `SpLeavesGood` at
`jetsOfP`, `newOfP` (P: `BakeLinkAt` and the tail `TailEndAt`),
`JetsOfCole6 jetsOfP` (P), the gate at `PGood6` states (K; P's fields
`got`, `nomm`, `cole`: `gateGot_of_key`, `gateCole_of_good`),
`UnaryKeeps OptTotal` (D), `UnaryCacheKeeps`, `UnarySccsIs` (K / Q),
`OtherKeeps6` (P), the four `env` equations. -/
theorem pokeModel_fullReachP8 (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
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
    (hJC : JetsOfCole6 jetsOfP)
    (hU : UnaryKeeps Ar OptTotal) (hCK : UnaryCacheKeeps Ar OptTotal) (hUS : UnarySccsIs Ar)
    (hX : OtherKeeps6 flagsOf OptTotal) :
    ∀ cr, CorIn cr → ∀ s f, pokeN cr (Ovum.full s f).toNoun =
      (liftPoke (enc flagsOf) (pokeS Ar) cr (Ovum.full s f)).map fun r => C r.1.toNoun r.2 :=
  pokeModel_fullReachP7 Ar env hhe hth hsoft hrf lib hA hJA hOA hSA hUA hL hG jetsOfGood_P hJC hU hCK hUS hX

end Compiler
end Formalization
