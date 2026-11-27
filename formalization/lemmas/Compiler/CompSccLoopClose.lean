import lemmas.Compiler.CompSccLoopUse
import lemmas.Compiler.CompSccLoopDfs
import lemmas.Compiler.CompSccLoopKids
import lemmas.Compiler.CompCalleeComp
import lemmas.Ska.SccLoopTotal
import lemmas.Ska.SccLoopKeys

/-! # `csi_gate_loop` with its side hypotheses discharged (README Gaps 21.13)

* `csi_levy_miss`: the cache test is `|` when a member misses `nary.cache`.
* The configuration of the model is the pill's (`CfgOf`): `scc` is `~(tap in scc)`, `kids` the
  lists `~(tap in (~(get ju kids) b))` of the pill's `kids` (`kidsOf`, `csi_kids`), `order` the
  DFS of the pill (`dfsOrder`, `csf_order`).
* The concrete relation `LoopR`: `map-local` holds the model's `ml` exactly (`MlExact`),
  `sure.cache` holds `sure` at the bells `bs` (`SureHolds`), the outside callees `outC b` of
  every member that has an entry have entries in `nary.cache` with the needs `nout`
  (`OutsHeld`), and the cache meets an invariant `Q` (for track K: `AgreeE` with `Ext`).
* `top_of_exact`: the `TOP` of `csfTop` holds the `%may` needs (`TopN`), so the `%must` member
  gate is asked for every `TOP` with `TopN` only.
* **`csi_gate_loop_d`**: the gate on a cache miss of an SCC that is not a lone bell without a self
  call, with the hypotheses about `+run` only (`MemGate` on the three modes for `LoopR`), the
  print (`PrintId`), the start, and the run of the model.
* **`csi_gate_ranked`**: the same with no model fuel, under `Ranked`.
* Consumers: `loop_entry` (every member has an entry of `M` with its final need),
  `csiNeeds_of_loopR` (both disjuncts of `CsiNeeds`), `ccc_csi_open`, `cccMiss_of_loop`. -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The cache test -/

theorem getF_map_some {M k : Noun} (hm : IsMap mugF M) : ∃ out, getF mugF k M = some out := by
  by_cases h : ∃ v, Get M k v
  · obtain ⟨v, hg⟩ := h; exact ⟨_, getF_some hm hg⟩
  · exact ⟨_, getF_none hm fun v hg => h ⟨v, hg⟩⟩

/-- **The cache test on a miss**: some member `b` has no entry in `nary.cache` (a map), so
`(levy ~(tap in scc) ~(has by nary.cache))` is `|`. -/
theorem csi_levy_miss (SCC LONG JH NARY CR : Noun) (hs : Tree SCC) (hnm : IsMap mugF NARY)
    (b : Noun) (hb : b ∈ tapList SCC) (hmiss : getF mugF b NARY = some (A 0)) :
    nock (C csiBody (C (csiSam SCC LONG JH (C NARY CR)) compK)) csiLevy = some (A 1) := by
  have hL := compK_layer2
  have htap : tapF SCC (A 0) = some (listN (tapList SCC)) := by simpa [listN] using tapF_list hs []
  let pr : Noun → Bool := fun x => match getF mugF x NARY with
    | some out => decide (out ≠ A 0)
    | none => true
  have hlevy := levy_gate layer2 by.has.battery (A 0) (C by.battery (C NARY layer2)) pr (tapList SCC)
    (fun x hx => by
      obtain ⟨out, ho⟩ := getF_map_some (k := x) hnm
      rw [has_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ x NARY _ ho]
      simp [pr, ho])
  have hall : (tapList SCC).all pr = false :=
    List.all_eq_false.mpr ⟨b, hb, by simp [pr, hmiss]⟩
  have hl1 : loob false = A 1 := rfl
  rw [hall, hl1] at hlevy
  unfold csiSam
  generalize csiBody = CB
  generalize compK = KC at hL
  simp [nock_exec, hL, csiLevy, levy.arm_at, levy_arm, in.arm_at, in_arm, in.tap.arm_at, tap_arm, tap_loop, htap,
    by.arm_at, by_arm, by.has.arm_at, has_arm, hlevy]

/-! ## The concrete relation -/

/-- `map-local` holds the model's needs exactly: a map whose entries are at the bells where `ml`
has a need, each a cell (a straight) whose head is that need. -/
def MlExact (ml : Noun → Option NeedOrd) (ML : Noun) : Prop :=
  IsMap mugF ML ∧ (∀ k v, Get ML k v → ∃ n t, ml k = some n ∧ v = C n.toNoun t) ∧
    ∀ k n, ml k = some n → ∃ t, Get ML k (C n.toNoun t)

theorem mlExact_none : MlExact (fun _ => none) (A 0) :=
  ⟨IsMap.nil, fun k v h => absurd h (by simp [get_nil]), fun k n h => by simp at h⟩

theorem mlNeeds_of_exact {ml : Noun → Option NeedOrd} {ML : Noun} (h : MlExact ml ML) :
    MlNeeds ml ML := by
  intro b n hb
  obtain ⟨t, hg⟩ := h.2.2 b n hb
  exact ⟨_, getF_some h.1 hg, by simp [nock_exec]⟩

/-- The outside callees `outC b` of every member with an entry have entries in `nary.cache`
(the head of the cache) whose needs are `nout`. -/
def OutsHeld (outC : Noun → List Noun) (nout : Noun → NeedOrd) (ml : Noun → Option NeedOrd)
    (CA : Noun) : Prop :=
  ∀ b, (ml b).isSome → ∀ k ∈ outC b, ∃ NR u, slot? 2 CA = some NR ∧
    getF mugF k NR = some (C (A 0) u) ∧ slot? 2 u = some (nout k).toNoun

/-- **The relation of the loop**: `MlExact`, `SureHolds` at `bs`, `OutsHeld`, and an invariant
`Q` of the cache. -/
def LoopR (bs : List Noun) (outC : Noun → List Noun) (nout : Noun → NeedOrd) (Q : Noun → Prop)
    (ml sure : Noun → Option NeedOrd) (ML CA : Noun) : Prop :=
  MlExact ml ML ∧ SureHolds bs sure CA ∧ OutsHeld outC nout ml CA ∧ Q CA

theorem loopR_reset (bs : List Noun) (outC : Noun → List Noun) (nout : Noun → NeedOrd)
    (Q : Noun → Prop) : ∀ ml sure ML CA, LoopR bs outC nout Q ml sure ML CA →
      LoopR bs outC nout Q (fun _ => none) sure (A 0) CA :=
  fun _ _ _ _ h => ⟨mlExact_none, h.2.1, fun b hb => by simp at hb, h.2.2.2⟩

/-- `top` as a noun: a map at the bells where `ml` has a need, holding that need. -/
def TopN (ml : Noun → Option NeedOrd) (TOP : Noun) : Prop :=
  IsMap mugF TOP ∧ ∀ k w, Get TOP k w ↔ ∃ n, ml k = some n ∧ w = n.toNoun

/-- **`top` from the `%may` sweep**: `csfTop` on a `map-local` that holds `ml` exactly gives a
`TOP` that holds the needs of `ml` (`top_gate`). -/
theorem top_of_exact (p : LoopP) (ORD CA : Noun) {ml : Noun → Option NeedOrd} {MAY : Noun}
    (h : MlExact ml MAY) :
    ∃ TOP, nock (C MAY (C ORD (p.subj (A 0) CA))) csfTop = some TOP ∧ TopN ml TOP := by
  obtain ⟨TOP, ht, hm, hg⟩ := top_gate p MAY ORD (A 0) CA h.1 (fun k v hv => by
    obtain ⟨n, t, -, rfl⟩ := h.2.1 k v hv; exact ⟨_, _, rfl⟩)
  refine ⟨TOP, ht, hm, fun k w => ?_⟩
  rw [hg]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨n, t, hn, rfl⟩ := h.2.1 k v hv
    exact ⟨n, hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨t, hg'⟩ := h.2.2 k n hn
    exact ⟨_, hg', rfl⟩

/-! ## The configuration of the model from the pill -/

/-- `kids` as the pill computes it (`csiKids` on the subject of the gate). -/
noncomputable def kidsOf (SCC LONG JH CA0 : Noun) : Noun :=
  (nock (C (A 0) (C csiBody (C (csiSam SCC LONG JH CA0) compK))) csiKids).getD (A 0)

/-- **The model's configuration is the pill's**: `scc` the `+tap:in` of `scc`, `kids` the lists
of the pill's `kids`, `order` the pill's DFS over them. -/
structure CfgOf {N : Type} (c : Cfg Noun N) (SCC KIDS : Noun) : Prop where
  scc : c.scc = tapList SCC
  kids : c.kids = kidsL KIDS
  order : c.order = dfsOrder c.kids c.scc

/-- The sample's sets: `scc` a set, `calls.long-ska` a jug, `nary.cache` a map. -/
structure SamOK (SCC CALLS NARY : Noun) : Prop where
  scc : IsSet mugF SCC
  calls : IsMap mugF CALLS
  jug : ∀ k v, Get CALLS k v → IsSet mugF v
  nary : IsMap mugF NARY

theorem preorder_length_tap : ∀ a : Noun, (preorder a).length = (tapList a).length
  | Noun.atom _ => rfl
  | Noun.cell _ (Noun.atom _) => rfl
  | Noun.cell n (Noun.cell l r) => by
    simp only [preorder, tapList, List.length_cons, List.length_append, preorder_length_tap l,
      preorder_length_tap r]
    omega

/-- **What the pill's `kids` gives the model**: on `SamOK`, the nouns `kids` of `csi_kids`
meet `KidsN`, the hypotheses of `csf_order`, and the kids are members. -/
theorem kids_facts {N : Type} (c : Cfg Noun N) (SCC CALLS KIDS : Noun) (hs : IsSet mugF SCC)
    (hspec : ∀ b, Has SCC b → ∃ S, getF mugF b KIDS = some (C (A 0) S) ∧ IsSet mugF S ∧
      ∀ k, Has S k ↔ Has SCC k ∧ CalleeIn CALLS b k)
    (hcs : c.scc = tapList SCC) (hck : c.kids = kidsL KIDS) :
    KidsN c KIDS ∧ (∀ b ∈ tapList SCC, ∃ out, getF mugF b KIDS = some out ∧ Tree (unUnit out)) ∧
      (∀ b ∈ tapList SCC, ∀ k ∈ kidsL KIDS b, k ∈ tapList SCC) := by
  have hget : ∀ b ∈ tapList SCC, ∃ S, getF mugF b KIDS = some (C (A 0) S) ∧ IsSet mugF S ∧
      ∀ k, k ∈ kidsL KIDS b ↔ Has SCC k ∧ CalleeIn CALLS b k := by
    intro b hb
    obtain ⟨S, hg, hS, hk⟩ := hspec b ((mem_tapList_set hs b).1 hb)
    refine ⟨S, hg, hS, fun k => ?_⟩
    rw [kidsL_of hg, show unUnit (C (A 0) S) = S from rfl, mem_tapList_set hS, hk]
  refine ⟨fun b hb => ?_, fun b hb => ?_, fun b hb k hk => ?_⟩
  · rw [hcs] at hb
    obtain ⟨S, hg, hS, hk⟩ := hget b hb
    refine ⟨_, hg, Tree.of_isSet hS, fun k => ?_⟩
    rw [hck, mem_preorder_tapList, kidsL_of hg]
  · obtain ⟨S, hg, hS, -⟩ := hget b hb
    exact ⟨_, hg, Tree.of_isSet hS⟩
  · obtain ⟨S, hg, hS, hkk⟩ := hget b hb
    exact (mem_tapList_set hs k).2 ((hkk k).1 hk).1

/-! ## The gate, discharged -/

/-- **`csi_gate_loop` with its side hypotheses discharged.**  On a sample `[SCC [CODE JETS
CALLS] JH [NARY CR]]` whose sets are sets (`SamOK`), with a member missing in `nary.cache`
(`hmiss`) and an SCC that is not one bell without a self call (`hnd`), for the model whose
configuration is the pill's (`CfgOf` with `kidsOf`), wherever `compileSccIn c false fuel st0`
returns `s` from a start with no entry (`hml0`), `sure.cache` held at `bs` and `Q` of the cache,
the gate returns `[M [NARYU REST]]` with `LoopR` of `s` on `M` and the last member run's cache
`[NR REST]`, and `NARYU` the `+uni:by` of `NR` and `M` (`UniSpec`).  Left as hypotheses: the
member gate on the three modes for `LoopR` (`%must` for every `TOP` with `TopN` of the `%may`
needs), `hQ` (`Q` makes the cache a cell with a map at its head), and the print (`PrintId`). -/
theorem csi_gate_loop_d (c : Cfg Noun NeedOrd) (bs : List Noun) (outC : Noun → List Noun)
    (nout : Noun → NeedOrd) (Q : Noun → Prop)
    (SCC CODE JETS CALLS JH NARY CR : Noun) (hsam : SamOK SCC CALLS NARY)
    (hmiss : ∃ b ∈ tapList SCC, getF mugF b NARY = some (A 0))
    (hnd : (∀ n, SCC ≠ C n (C (A 0) (A 0))) ∨ ∃ n, SCC = C n (C (A 0) (A 0)) ∧ CalleeIn CALLS n n)
    (hcfg : CfgOf c SCC (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR)))
    (hmay : MemGate c (LoopR bs outC nout Q) (csiCtx (A 1) (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR))
      SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) (fun _ => c.none) (A 0) Mode.may (A 0x79616d))
    (hdone : MemGate c (LoopR bs outC nout Q) (csiCtx (A 1) (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR))
      SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) (fun _ => c.none) (A 0) Mode.done (A 0x656e6f64))
    (st0 : St Noun NeedOrd)
    (hmust : ∀ TOP, TopN (maySweep c st0).ml TOP → MemGate c (LoopR bs outC nout Q)
      (csiCtx (A 1) (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) SCC (C CODE (C JETS CALLS)) JH (C NARY CR))
      (topOf c (maySweep c st0)) TOP Mode.must (A 0x7473756d))
    (hQ : ∀ CA, Q CA → ∃ NR REST, CA = C NR REST ∧ IsMap mugF NR)
    (hpr : ∀ TOP MAY, PrintId ⟨A 1, kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR), SCC,
      C CODE (C JETS CALLS), JH, C NARY CR, TOP, MAY, listN c.order⟩)
    (hml0 : ∀ b, st0.ml b = none) (hsu0 : SureHolds bs st0.sure (C NARY CR)) (hq0 : Q (C NARY CR))
    (fuel : Nat) (s : St Noun NeedOrd) (hs : compileSccIn c false fuel st0 = some s) :
    (∀ b ∈ c.scc, (s.ml b).isSome) ∧ (∀ k, k ∉ c.scc → s.ml k = none) ∧
    ∃ M NR REST NARYU, LoopR bs outC nout Q s.ml s.sure M (C NR REST) ∧ IsMap mugF NR ∧
      IsMap mugF NARYU ∧ UniSpec NR M NARYU ∧
      nock (C csiBody (C (csiSam SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) compK)) csiBody
        = some (C M (C NARYU REST)) := by
  obtain ⟨KIDS, hK, -, hspec⟩ := csi_kids SCC CODE JETS CALLS JH (C NARY CR) hsam.scc hsam.calls hsam.jug
  have hKo : kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR) = KIDS := by
    unfold kidsOf; rw [hK]; rfl
  rw [hKo] at hcfg hmay hdone hmust hpr
  have htree : Tree SCC := Tree.of_isSet hsam.scc
  obtain ⟨b0, hb0, hm0⟩ := hmiss
  have hlevy := csi_levy_miss SCC (C CODE (C JETS CALLS)) JH NARY CR htree hsam.nary b0 hb0 hm0
  have hdn := csi_done_false SCC (C CODE (C JETS CALLS)) JH (C NARY CR) KIDS (by
    rcases hnd with h | ⟨n, hn, hself⟩
    · exact Or.inl h
    · refine Or.inr ⟨n, hn, kids_self n CALLS KIDS (fun b hb => ?_) hself⟩
      rw [← show SCC = setOne n from hn]; exact hspec b (by rw [hn]; exact hb))
  obtain ⟨hkN, hk, hin⟩ := kids_facts c SCC CALLS KIDS hsam.scc hspec hcfg.scc hcfg.kids
  have hscc : SccN c SCC := ⟨htree, hcfg.scc.symm, by rw [preorder_length_tap, hcfg.scc]⟩
  have hin' : ∀ b ∈ c.scc, ∀ k ∈ c.kids b, k ∈ c.scc := by
    intro b hb k hk; rw [hcfg.scc] at hb ⊢; rw [hcfg.kids] at hk; exact hin b hb k hk
  have hsub : ∀ b ∈ c.order, b ∈ c.scc := by
    rw [hcfg.order]; exact dfsOrder_sub c.kids c.scc hin'
  let p : LoopP := ⟨A 1, KIDS, SCC, C CODE (C JETS CALLS), JH, C NARY CR, A 0, A 0, listN c.order⟩
  have hdfs : nock (p.subj (A 0) (C NARY CR)) csfOrder = some (listN c.order) := by
    have := csf_order p (C NARY CR) hsam.scc hk hin
    rw [this, hcfg.order, hcfg.kids, hcfg.scc]
  have hml0' : st0.ml = fun _ => none := funext hml0
  have hR : LoopR bs outC nout Q st0.ml st0.sure (A 0) (C NARY CR) :=
    ⟨hml0' ▸ mlExact_none, hsu0, fun b hb => by rw [hml0'] at hb; simp at hb, hq0⟩
  obtain ⟨M, CA', hR', hgo⟩ := csi_gate_loop c (LoopR bs outC nout Q) SCC (C CODE (C JETS CALLS)) JH
    (C NARY CR) KIDS (listN c.order) hlevy hK hdn p rfl (loopR_reset bs outC nout Q) hmay hdone st0
    (fun MAY CA1 hR1 => by
      obtain ⟨TOP, ht, htn⟩ := top_of_exact p (listN c.order) CA1 hR1.1
      exact ⟨TOP, ht, hmust TOP htn⟩)
    hkN hscc rfl hsub hdfs hpr hR fuel s hs
  obtain ⟨NR, REST, rfl, hNR⟩ := hQ CA' hR'.2.2.2
  obtain ⟨NARYU, hu, hum, hus⟩ := uni_by (mug := mugF) layer2 gorIn_morIn_layer2 NR M hNR hR'.1.1
  exact ⟨compileSccIn_ml_some c fuel st0 s hs, compileSccIn_ml_out c hsub fuel st0 s hs,
    M, NR, REST, NARYU, hR', hNR, hum, hus, hgo NR REST NARYU rfl hu⟩

/-- **The gate with no model fuel**: under `Ranked` (`compileSccIn_total`), the model returns at
the fuel `4 * |scc| + |order| * (H + 1) + 2`, so the gate returns, with the conclusion of
`csi_gate_loop_d` on that run. -/
theorem csi_gate_ranked (c : Cfg Noun NeedOrd) (r : Ranked c) (bs : List Noun)
    (outC : Noun → List Noun) (nout : Noun → NeedOrd) (Q : Noun → Prop)
    (SCC CODE JETS CALLS JH NARY CR : Noun) (hsam : SamOK SCC CALLS NARY)
    (hmiss : ∃ b ∈ tapList SCC, getF mugF b NARY = some (A 0))
    (hnd : (∀ n, SCC ≠ C n (C (A 0) (A 0))) ∨ ∃ n, SCC = C n (C (A 0) (A 0)) ∧ CalleeIn CALLS n n)
    (hcfg : CfgOf c SCC (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR)))
    (hmay : MemGate c (LoopR bs outC nout Q) (csiCtx (A 1) (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR))
      SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) (fun _ => c.none) (A 0) Mode.may (A 0x79616d))
    (hdone : MemGate c (LoopR bs outC nout Q) (csiCtx (A 1) (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR))
      SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) (fun _ => c.none) (A 0) Mode.done (A 0x656e6f64))
    (st0 : St Noun NeedOrd)
    (hmust : ∀ TOP, TopN (maySweep c st0).ml TOP → MemGate c (LoopR bs outC nout Q)
      (csiCtx (A 1) (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) SCC (C CODE (C JETS CALLS)) JH (C NARY CR))
      (topOf c (maySweep c st0)) TOP Mode.must (A 0x7473756d))
    (hQ : ∀ CA, Q CA → ∃ NR REST, CA = C NR REST ∧ IsMap mugF NR)
    (hpr : ∀ TOP MAY, PrintId ⟨A 1, kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR), SCC,
      C CODE (C JETS CALLS), JH, C NARY CR, TOP, MAY, listN c.order⟩)
    (hml0 : ∀ b, st0.ml b = none) (hsu0 : SureHolds bs st0.sure (C NARY CR)) (hq0 : Q (C NARY CR)) :
    ∃ s, compileSccIn c false (4 * c.scc.length + c.order.length * (r.H + 1) + 2) st0 = some s ∧
      (∀ b ∈ c.scc, (s.ml b).isSome) ∧ (∀ k, k ∉ c.scc → s.ml k = none) ∧
      ∃ M NR REST NARYU, LoopR bs outC nout Q s.ml s.sure M (C NR REST) ∧ IsMap mugF NR ∧
        IsMap mugF NARYU ∧ UniSpec NR M NARYU ∧
        nock (C csiBody (C (csiSam SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) compK)) csiBody
          = some (C M (C NARYU REST)) := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (compileSccIn_total r false st0 _ (Nat.le_refl _))
  exact ⟨s, hs, csi_gate_loop_d c bs outC nout Q SCC CODE JETS CALLS JH NARY CR hsam ⟨_, hmiss.choose_spec.1,
    hmiss.choose_spec.2⟩ hnd hcfg hmay hdone st0 hmust hQ hpr hml0 hsu0 hq0 _ s hs⟩

/-! ## The consumers -/

/-- On a map, a hit of `getF` is an entry. -/
theorem getF_get_map {M k u : Noun} (hm : IsMap mugF M) (h : getF mugF k M = some (C (A 0) u)) :
    Get M k u := by
  by_cases hx : ∃ v, Get M k v
  · obtain ⟨v, hg⟩ := hx
    rw [getF_some hm hg] at h
    simp only [Option.some.injEq, Noun.cell.injEq] at h
    rw [← h.2]; exact hg
  · rw [getF_none hm fun v hg => hx ⟨v, hg⟩] at h; cases h

/-- **`CsiNeeds`, both disjuncts, from `LoopR`**: a callee in the SCC has the entry of `M` whose
need is the model's final `ml` (`MlExact`); a callee outside has the entry of `nary.cache` of
the last member run's cache (`OutsHeld` at some member `b0` that has an entry, among whose
outside callees it is), which `+uni:by` keeps since `M` has no entry outside the SCC (`hout`,
from `compileSccIn_ml_out`). -/
theorem csiNeeds_of_loopR (env : CallEnv) (n : Nomm) (SCC M NR REST NARYU : Noun)
    (bs : List Noun) (outC : Noun → List Noun) (nout : Noun → NeedOrd) (Q : Noun → Prop)
    (ml sure : Noun → Option NeedOrd) (scc : List Noun) (hs : IsSet mugF SCC) (hcs : scc = tapList SCC)
    (hR : LoopR bs outC nout Q ml sure M (C NR REST)) (hnr : IsMap mugF NR) (hum : IsMap mugF NARYU)
    (hus : UniSpec NR M NARYU) (hout : ∀ k, k ∉ scc → ml k = none)
    (b0 : Noun) (hb0 : (ml b0).isSome)
    (hin : ∀ b ∈ dirBells n, b.toNoun ∈ scc → ∃ nb, env.need b = some nb ∧ ml b.toNoun = some nb)
    (hex : ∀ b ∈ dirBells n, b.toNoun ∉ scc → b.toNoun ∈ outC b0 ∧ env.need b = some (nout b.toNoun)) :
    CsiNeeds env SCC M (C NARYU REST) n := by
  intro b hb
  obtain ⟨t, ht, htk⟩ := hasInF_spec mugF SCC b.toNoun hs
  by_cases hm : b.toNoun ∈ scc
  · obtain ⟨nb, he, hml⟩ := hin b hb hm
    obtain ⟨u, hg, hu⟩ := mlNeeds_of_exact hR.1 _ _ hml
    have htt : t = true := htk.2 ((mem_tapList_set hs _).1 (hcs ▸ hm))
    exact ⟨nb, he, Or.inl ⟨by rw [ht, htt], u, hg, hu⟩⟩
  · obtain ⟨hk, he⟩ := hex b hb hm
    obtain ⟨NR', u, h2, hg, hu⟩ := hR.2.2.1 b0 hb0 _ hk
    have e : NR' = NR := by simpa [nock_exec] using h2.symm
    subst e
    have htf : t = false := by
      cases t
      · rfl
      · exact absurd (hcs ▸ (mem_tapList_set hs _).2 (htk.1 rfl)) hm
    have hnk : ¬ KIn M b.toNoun := by
      rintro ⟨v, hv⟩
      obtain ⟨n', t', hn', -⟩ := hR.1.2.1 _ _ hv
      rw [hout _ hm] at hn'; cases hn'
    have hgu : Get NARYU b.toNoun u := (hus _ _).2 (Or.inr ⟨getF_get_map hnr hg, hnk⟩)
    exact ⟨nout b.toNoun, he, Or.inr ⟨by rw [ht, htf], NARYU, u, by simp [nock_exec],
      getF_some hum hgu, hu⟩⟩

/-- `+compile-scc-in` called from `+callee-compiled` on a miss (`cccCsiF`) is the gate on
`[new-scc long-ska jets-hot cache]` (the same statement as track K's `ccc_csi_eq`). -/
theorem ccc_csi_open {ctx LONG JH : Noun} (h7 : slot? 7 ctx = some compK) (hl : slot? 26 ctx = some LONG)
    (hj : slot? 54 ctx = some JH) (NS : Noun) (b : Bell) (g : Gen (TreapMap mugF)) (x : GenRest) :
    nock (C NS (cccS0 b g x ctx)) cccCsiF = nock (C csiBody (C (csiSam NS LONG JH x.cache) compK)) csiBody := by
  have ha := csi_at
  unfold cccS0 cccCsiF csiSam
  simp only [compCore, genNoun]
  generalize compK = KC at ha h7 ⊢
  simp [nock_exec, ha, csi_arm, h7, hl, hj]

/-- **`CccMiss` from the loop**: given the gate of `+scc-of` (`hscc`, its first conjunct), the
gate `+compile-scc-in` on the callee's SCC returning `[M CA']` (`hcsi`: the conclusion of
`csi_gate_loop_d` on that SCC) and `M` holding the model's needs exactly with the need `nb` at
`b` (`MlExact`: `LoopR`'s first clause, `nb` the final `ml b`). -/
theorem cccMiss_of_loop {ctx LONG JH : Noun} (h7 : slot? 7 ctx = some compK) (hl : slot? 26 ctx = some LONG)
    (hj : slot? 54 ctx = some JH) (b : Bell) (nb : NeedOrd) {NR MO SC RS SO SS NS SC' M CA' : Noun}
    (hscc : ∀ g, nock (cccS0 b g (ccRest NR MO SC RS SO SS) ctx) cccSccF = some (C NS SC'))
    (hcsi : nock (C csiBody (C (csiSam NS LONG JH (C NR (C MO (C SC' RS)))) compK)) csiBody = some (C M CA'))
    {ml : Noun → Option NeedOrd} (hml : MlExact ml M) (hb : ml b.toNoun = some nb) :
    CccMiss ctx b nb NR MO SC RS SO SS CA' := by
  obtain ⟨t, hg⟩ := hml.2.2 _ _ hb
  exact ⟨NS, SC', M, C nb.toNoun t, hscc, fun g => (ccc_csi_open h7 hl hj NS b g _).trans hcsi,
    getF_some hml.1 hg, by simp [nock_exec]⟩

end Compiler
end Formalization
