import lemmas.Compiler.PokeLinkTailJets

/-!
# The jets leaf reduced to `srEnd` (track P, README Gaps 23)

`TailEndAt` has three parts: `new-cores` (`srCores`), the edit of
`jets.lon` (`srJetsF`) and `srEnd`.  The first two are linked
(`srCores_run`, `srJetsF_run`), so the leaf is `SrEndAt`: `srEnd`, on the
subject with the model's `new-cores` and edited jets pushed, returns the
product.  They need, of the regs the analysis returns, the maps
(`RegsMaps`) and `new` a list of `[p s *]` (`NewOK`): `AnaRegsGood`, the
analysis keeps both (analysis owner; checked `%rmap` and `%jmod`, which
computes `new-cores`, at the 16 `%full` pokes of `jetsmodel.hoon`).

* `repO_some`, **`uniJuO_some`**: `+uni-ju` answers on jugs of sets;
* `NewOK`, `AnaRegsGood`, `SrEndAt`;
* **`tailEndAt_of_end`**: `TailEndAt` from `SrEndAt`;
* `SpLeavesAt8`, `SpLeavesGood8` (the jets leaf is `SrEndAt`),
  `spLeavesGood7_of_8`;
* **`pokeModel_fullReachP11`**: the top with `SpLeavesGood8` and
  `AnaRegsGood`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF SkaModel.PokeM FinMap

/-- A fold whose every step answers and keeps `P` answers. -/
theorem repO_some (f : Noun → Noun → Option Noun) (P Q : Noun → Prop)
    (hf : ∀ n acc, Q n → P acc → ∃ out, f n acc = some out ∧ P out) :
    ∀ t, Tree t → ∀ acc, (∀ n ∈ preorder t, Q n) → P acc → ∃ out, repO f t acc = some out ∧ P out := by
  intro t ht
  induction ht with
  | nil => intro acc _ h; exact ⟨acc, rfl, h⟩
  | @node n l r _ _ ihl ihr =>
    intro acc hQ hP
    obtain ⟨a, ha, hPa⟩ := hf n acc (hQ n (by simp [preorder])) hP
    obtain ⟨b, hb, hPb⟩ := ihl a (fun m hm => hQ m (by simp [preorder, hm])) hPa
    obtain ⟨c, hc, hPc⟩ := ihr b (fun m hm => hQ m (by simp [preorder, hm])) hPb
    exact ⟨c, by simp [repO, ha, hb, hc], hPc⟩

/-- **`+uni-ju` answers on jugs of sets.** -/
theorem uniJuO_some {pd nco : Noun} (hp : JugSets pd) (hn : JugSets nco) : ∃ pd', uniJuO pd nco = some pd' := by
  have hQ : ∀ n ∈ preorder nco, ∃ p q, n = C p q ∧ IsSet mugF q := fun n hn' => by
    obtain ⟨k, v, rfl, hk⟩ := (mem_preorder hn.1 n).1 hn'
    exact ⟨k, v, rfl, hn.2 k v hk⟩
  obtain ⟨out, h, -⟩ := repO_some uniJuStep JugSets (fun n => ∃ p q, n = C p q ∧ IsSet mugF q)
    (fun n acc hq hacc => by
      obtain ⟨p, q, rfl, hq⟩ := hq
      obtain ⟨g, hg, hd⟩ : ∃ g, getF mugF p acc = some g ∧ IsSet mugF (unUnit g) := by
        by_cases hx : ∃ s, Get acc p s
        · obtain ⟨s, hs⟩ := hx
          exact ⟨_, getF_some hacc.1 hs, hacc.2 _ _ hs⟩
        · exact ⟨_, getF_none hacc.1 (fun v hv => hx ⟨v, hv⟩), IsMap.nil⟩
      obtain ⟨o, hR, -, -, -⟩ := uniP_of_sets _ (unUnit g) q (Nat.le_refl _) hd hq
      have hx : ∃ o, UniR mugF (unUnit g) q o := ⟨o, hR⟩
      obtain ⟨o', ho', -, -⟩ := putF_spec mugF acc p
        (if unUnit g = q then unUnit g else Classical.choose hx) hacc.1
      have e : uniJuStep (C p q) acc = some o' := by
        simp only [uniJuStep, juGetF, hg, Option.map_some, Option.bind_some, uniInO, dif_pos hx, ho']
      exact ⟨o', e, uniJuStep_sets hacc ⟨p, q, rfl, hq⟩ e⟩)
    nco (Tree.of_isMap hn.1) pd hQ hp
  exact ⟨out, h⟩

/-- `new` of the regs is a list of `[p s *]`: `new-cores` answers. -/
def NewOK (reg : Noun) : Prop :=
  ∃ ro co ba ar nw, reg = C ro (C co (C ba (C ar nw))) ∧ ∃ nco, newCoresO nw = some nco

/-- **The analysis keeps the regs' maps and `new` a list of `[p s *]`**
(analysis owner: `+register-fast` writes the maps with `put:by`/`put:ju`
and pushes `[path sock clue]` onto `new`; checked `%rmap`, `%jmod`). -/
def AnaRegsGood (env : Env Noun) : Prop :=
  ∀ n root memo reg (r : Callgraph FinMap × FinMap Bell (FDatum FinMap) × Memo FinMap × FDatum FinMap × Noun),
    RegsMaps reg → NewOK reg → Ana.skaPoke env n root memo reg = some r → RegsMaps r.2.2.2.2 ∧ NewOK r.2.2.2.2

theorem anaRegsMaps_of_good {env : Env Noun} (h : AnaRegsGood env) :
    ∀ n root memo reg (r : Callgraph FinMap × FinMap Bell (FDatum FinMap) × Memo FinMap × FDatum FinMap × Noun),
      RegsMaps reg → NewOK reg → Ana.skaPoke env n root memo reg = some r → RegsMaps r.2.2.2.2 :=
  fun n root memo reg r h1 h2 h3 => (h n root memo reg r h1 h2 h3).1

section Parts

variable (root : Ident) (r1 r2 r3 r4 jRest codeN varsN hotN : Noun)
  (gr : Callgraph FinMap × Noun)
  (r : Callgraph FinMap × FinMap Bell (FDatum FinMap) × Memo FinMap × FDatum FinMap × Noun)

/-- **The leaf of `srEnd`** (open: `+flop` and `+ska-cole-update`): on every
`sccs` noun `q`, with `new-cores` `nco` and the edited jets `jE` pushed,
`srEnd` returns `[[root-bell newN] [j' rest]]`. -/
def SrEndAt (fl : Flags) (code nc : FinMap Bell (VarEntry FinMap)) (bkN vr j' newN nco jE : Noun) : Prop :=
  ∀ q, nock (srTS nco q (nc.toNoun varEntryNoun) bkN
      (srS0 root r1 r2 r3 r4 jRest codeN (code.toNoun fun e => FinMap.setNoun e.calls) varsN
        (code.toNoun fun e => e.seek.toNoun) hotN gr r) (srRootN root r)
      (Treap.toNoun FDatum.toNoun r.2.1) r.2.2.2.1.toNoun (Treap.toNoun FDatum.toNoun r.1)
      (C (Treap.toNoun FDatum.toNoun gr.1) gr.2) (identNoun root) (identNoun root) jE
      (memoNoun r.2.2.1) (codeNoun fl (addCode code nc)) ((addCode code nc).toNoun fun e => FinMap.setNoun e.calls) vr
      ((addCode code nc).toNoun fun e => e.seek.toNoun) hotN) srEnd =
    some (C (C (srRootN root r) newN) (C j' (C (memoNoun r.2.2.1) (C (codeNoun fl (addCode code nc))
      (C ((addCode code nc).toNoun fun e => FinMap.setNoun e.calls)
        (C vr ((addCode code nc).toNoun fun e => e.seek.toNoun)))))))

/-- **`TailEndAt` from the leaf of `srEnd`**: `new-cores` and the edit are
linked. -/
theorem tailEndAt_of_end (fl : Flags) (code nc : FinMap Bell (VarEntry FinMap)) (bkN vr j' newN : Noun)
    (ro co ba ar nw pd cole nco pd' : Noun) (hreg : gr.2 = C ro (C co (C ba (C ar nw))))
    (hj : jRest = C pd cole) (hnco : newCoresO nw = some nco) (hp : JugSets pd) (hpd : uniJuO pd nco = some pd')
    (hE : SrEndAt root r1 r2 r3 r4 jRest codeN varsN hotN gr r fl code nc bkN vr j' newN nco
      (C ro (C co (C ba (C ar (C pd' cole)))))) :
    TailEndAt root r1 r2 r3 r4 jRest codeN varsN hotN gr r fl code nc bkN vr j' newN := by
  intro q
  refine ⟨nco, C ro (C co (C ba (C ar (C pd' cole)))), ?_, ?_, hE q⟩
  · unfold srT10At
    rw [hreg]
    exact srCores_run _ _ _ _ _ _ _ _ _ ro co ba ar nw _ _ _ _ _ _ _ _ _ nco hnco
  · unfold srT10At
    rw [hreg, hj]
    exact srJetsF_run nco _ _ _ _ _ _ _ _ _ ro co ba ar nw _ _ r1 r2 r3 r4 pd cole _ _ _ _ _ _ pd' hp
      (newCoresO_sets hnco) hpd

end Parts

/-! ## The leaves with the jets leaf `SrEndAt` -/

/-- The leaves of `spRest` at a state: `BakeLinkAt`, and `SrEndAt` where the
regs are maps with `new` a list of `[p s *]`, at the model's `new-cores`
and edit. -/
def SpLeavesAt8 (env : Env Noun) (jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool)
    (fold frozen : Bool) (bf : BEnv FinMap → Nat)
    (jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun) (newOf : Noun → Noun)
    (st : PSt) (s f r1 r2 r3 r4 jRest key : Noun) : Prop :=
  ∀ n gr r, Ana.skaCallgraph env n (Sock.mk Cape.yes s, f) st.long.memo (C r1 (C r2 (C r3 (C r4 (A 0))))) = some gr →
    Ana.skaPoke env n (Sock.mk Cape.yes s, f) st.long.memo (C r1 (C r2 (C r3 (C r4 (A 0))))) = some r →
    BakeLinkAt (Sock.mk Cape.yes s, f) r1 r2 r3 r4 jRest (codeNoun flagsOf st.long.code)
        (st.long.code.toNoun fun e => FinMap.setNoun e.calls) (st.long.vars.toNoun FinMap.setNoun)
        (st.long.code.toNoun fun e => e.seek.toNoun) key gr r
        (spE jet fold frozen st (Sock.mk Cape.yes s, f) r) (bf (spE jet fold frozen st (Sock.mk Cape.yes s, f) r)) ∧
    ∀ ro co ba ar nw pd cole nco pd', r.2.2.2.2 = C ro (C co (C ba (C ar nw))) → RegsMaps r.2.2.2.2 →
      jRest = C pd cole → newCoresO nw = some nco → uniJuO pd nco = some pd' →
      ∀ bg, bakeGraph (spE jet fold frozen st (Sock.mk Cape.yes s, f) r)
        (bf (spE jet fold frozen st (Sock.mk Cape.yes s, f) r)) = some bg →
      SrEndAt (Sock.mk Cape.yes s, f) r1 r2 r3 r4 jRest (codeNoun flagsOf st.long.code)
        (st.long.vars.toNoun FinMap.setNoun) key gr r flagsOf st.long.code (newCode st.long.code bg.1)
        (bg.1.toNoun varEntryNoun) (bg.2.toNoun FinMap.setNoun)
        (jetsOf st.hot st.jets r.2.2.2.2 st.long (spL st r bg)) (newOf r.2.2.2.2) nco
        (C ro (C co (C ba (C ar (C pd' cole)))))

/-- **The leaves on `PGood7` states, the jets leaf `SrEndAt`** (P). -/
def SpLeavesGood8 (Cls : Straight (TreapMap mugF) → Prop) (env : Env Noun)
    (jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool)
    (fold frozen : Bool) (bf : BEnv FinMap → Nat)
    (jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun) (newOf : Noun → Noun) : Prop :=
  ∀ (st : PSt) s f₁ f₂ r1 r2 r3 r4 jRest key, PGood7 Cls st → st.jets = C r1 (C r2 (C r3 (C r4 jRest))) →
    keyRaw (enc flagsOf st) = some key →
    SpLeavesAt8 env jet fold frozen bf jetsOf newOf st s (C f₁ f₂) r1 r2 r3 r4 jRest key

/-- **`SpLeavesGood7` from `SpLeavesGood8`**, the analysis keeping the
regs good. -/
theorem spLeavesGood7_of_8 {Cls : Straight (TreapMap mugF) → Prop} {env : Env Noun}
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    {bf : BEnv FinMap → Nat}
    {jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun} {newOf : Noun → Noun}
    (hRG : AnaRegsGood env) (hL : SpLeavesGood8 Cls env jet fold frozen bf jetsOf newOf) :
    SpLeavesGood7 Cls env jet fold frozen bf jetsOf newOf := by
  intro st s f₁ f₂ r1 r2 r3 r4 jRest key hg hj hk n gr r hcg hsp
  obtain ⟨hB, hT⟩ := hL st s f₁ f₂ r1 r2 r3 r4 jRest key hg hj hk n gr r hcg hsp
  refine ⟨hB, fun hm bg hbg => ?_⟩
  have hnew0 : NewOK (C r1 (C r2 (C r3 (C r4 (A 0))))) := ⟨r1, r2, r3, r4, A 0, rfl, A 0, rfl⟩
  obtain ⟨-, ro, co, ba, ar, nw, hreg, nco, hnco⟩ := hRG _ _ _ _ r (regsMaps_start hg.good6 hj) hnew0 hsp
  obtain ⟨x1, x2, x3, x4, pd, ca, bk, hx, -, -, -, -, hpdm, -, -⟩ := hg.good6.good5.good4.good3.good2.good.maps
  rw [hj] at hx
  simp only [Noun.cell.injEq] at hx
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hx
  have hp : JugSets pd := ⟨hpdm, hg.pendSets _ _ _ _ _ _ _ (hj.trans rfl)⟩
  obtain ⟨pd', hpd⟩ := uniJuO_some hp (newCoresO_sets hnco)
  have hgr : gr.2 = r.2.2.2.2 := (skaPoke_regs hcg hsp).symm
  exact tailEndAt_of_end _ _ _ _ _ _ _ _ _ gr r flagsOf _ _ _ _ _ _ ro co ba ar nw pd (C ca bk) nco pd'
    (hgr.trans hreg) rfl hnco hp hpd (hT ro co ba ar nw pd (C ca bk) nco pd' hreg hm rfl hnco hpd bg hbg)

/-- **`SpRestGood7` at `flagsOf` from `SpLeavesGood8`.** -/
theorem spRestGood7_of_leaves8 (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
    (Cls : Straight (TreapMap mugF) → Prop) (env : Env Noun)
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → Noun}
    {jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun} {newOf : Noun → Noun}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf) (hF : FuelOK env regOf fuel)
    (hreg : ∀ r1 r2 r3 r4 jRest, regOf (C r1 (C r2 (C r3 (C r4 jRest)))) = C r1 (C r2 (C r3 (C r4 (A 0)))))
    (hRG : AnaRegsGood env)
    (hL : SpLeavesGood8 Cls env jet fold frozen bf jetsOf newOf) : SpRestGood7 flagsOf Ar Cls env :=
  fun st s f₁ f₂ r1 r2 r3 r4 jRest key hg hj hk =>
    spRestAt_of_leaves Ar Cls env hA hF hreg st hg.good6 s f₁ f₂ r1 r2 r3 r4 jRest key hj
      fun n gr r hcg hsp =>
        ⟨(spLeavesGood7_of_8 hRG hL st s f₁ f₂ r1 r2 r3 r4 jRest key hg hj hk n gr r hcg hsp).1,
          (spLeavesGood7_of_8 hRG hL st s f₁ f₂ r1 r2 r3 r4 jRest key hg hj hk n gr r hcg hsp).2
            (hRG _ _ _ _ r (regsMaps_start hg.good6 hj) ⟨r1, r2, r3, r4, A 0, rfl, A 0, rfl⟩ hsp).1⟩

/-- **`pokeModel` on `%full` at every reachable core, over `PGood7`, at the
model's jets, with the jets leaf reduced to `srEnd`** (`SpLeavesGood8`).
`new-cores` and the edit of `jets.lon` are linked.  Left, with owners:
`SpLeavesGood8` (P: `BakeLinkAt`; `SrEndAt`, i.e. `+flop` and
`+ska-cole-update`), `AnaRegsGood` (analysis owner), the gate at `PGood6`
states (K), `UnaryKeeps OptTotal` (D), `UnaryCacheKeeps`, `UnarySccsIs`
(K / Q), `OtherKeeps7` (P), the four `env` equations. -/
theorem pokeModel_fullReachP11 (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
    (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP) (lib : Lib)
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    {bf : BEnv FinMap → Nat}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen (anaFuel env regOfP) bf regOfP jetsOfP newOfP)
    (hJA : Ar.jetRoot = jetRootP) (hOA : Ar.optimize = optimizeP) (hSA : Ar.sccOf = sccOfP)
    (hUA : Ar.compileUnary = compileUnaryP flagsOf)
    (hL : SpLeavesGood8 OptTotal env jet fold frozen bf jetsOfP newOfP) (hRG : AnaRegsGood env)
    (hG : ∀ st b sc, PGood6 OptTotal st → ∃ (NM CA V COLE SC0 : Noun) (env : Comp.CallEnv) (inl : Noun → Option Nomm)
      (n : Nomm) (ht : Noun → Nat) (D : Bell → Prop), UnaryGateAt flagsOf st b sc NM CA V COLE SC0 env inl n ht D)
    (hU : UnaryKeeps Ar OptTotal) (hCK : UnaryCacheKeeps Ar OptTotal) (hUS : UnarySccsIs Ar)
    (hX : OtherKeeps7 flagsOf OptTotal) :
    ∀ cr, CorIn cr → ∀ s f, pokeN cr (Ovum.full s f).toNoun =
      (liftPoke (enc flagsOf) (pokeS Ar) cr (Ovum.full s f)).map fun r => C r.1.toNoun r.2 :=
  pokeModel_fullReachG7 flagsOf Ar env hhe hth hsoft hrf lib hA hJA hOA hSA hUA
    (spRestGood7_of_leaves8 Ar OptTotal env hA (fuelOK_anaFuel env regOfP) regOfP_shape hRG hL) hG
    jetsOfGood_P jetsOfCole6_P jetsOfSets_P hU hCK hUS hX

end Compiler
end Formalization
