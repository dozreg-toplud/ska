import lemmas.Compiler.CompRunShapeSplit
import lemmas.Compiler.CompRunShapeLeapCut
import lemmas.Compiler.CompRunShapeLeapsCut
import lemmas.Compiler.CompLeapGate

/-!
# The link of `+laze-leap` and `+laze-leaps` (track A, 2026-11-27)

`+laze-leaps` (door arm `0x1556`, `llsGate`, cut in `CompRunShapeLeapsCut.lean`) against
`lazeLeaps` of `Ska/RunShape.lean`, and `+laze-leap` (door arm `0x2ab`, `llpGate`,
`CompRunShapeLeapCut.lean`) against `lazeLeap`, on every `laze` (forks and bonds to any depth)
whose looks are not `0` (`LzNZ`), on every noun `G` of `gen` (neither arm reads it), under
`CompIn ctx` and `K` at axis `7` of `ctx`.

The two batteries are the nouns of `+lazy-leap` (`lzlBat`) and `+leap` (`lpxBat`,
`CompLeapN.lean`) with six arm numbers changed (the cut files say which), so the proofs follow
`CompLeapLazy.lean`, `CompLeapLazyGate.lean` and `CompLeapGate.lean` step by step:
* `noc_gate`: `+need-ord-cut` (door arm `0x17df`, the same noun `ndcArm` as `+need-cut`,
  `noc_at`) is `needOrdCut` on every axis and shape; `nof_gate`: `+need-ord-from` (door arm
  `0xabb7`, the noun `ndfArm` of `+need-from`, `nof_at`) is `needOrdFrom`.
* `llp_g1`, `llp_lok`: the `+rep:in` over the looks is `leapLok` (as `lzl_g1`, `lzl_lok`).
* `llp_pr`, `llp_sur`, `llp_r2`: the prunes (`+laze-prune`, `lpr_mk`), the `?~ cut`, the turns.
* **`llp_all`** (`llp_allN`, `llp_forks`, `llp_bonds`): the gate is `lazeLeap`, on positive
  `p` and `s`.
* `lls_loop`: the trap over the parts is `leapsLoop`; **`lls_all`**: the gate of `+laze-leaps`
  is `lazeLeaps`, on nomms with no `%10` at axis `0` (`Bake.NoAx0`, for `+pass-both`,
  `pbt_gate`).
* `lazeLeap_nz`, **`lazeLeaps_nz`** (model only): what they return keeps `LzNZ`, `rest` and
  every `by`.

The model takes the same steps in the same order.  No departure.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.Ana

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-! ## `+need-ord-cut` and `+need-ord-from` -/

/-- `+need-ord-cut` is the noun of `+need-cut`. -/
theorem noc_at : slot? 4063 comp.door = some ndcArm := by kernel_rfl

theorem noc_at' (y : Noun) : slot? 0x17df (C comp.door y) = some ndcArm := by kernel_rfl

/-- `+need-ord-from` is the noun of `+need-from`. -/
theorem nof_at : slot? 27575 comp.door = some ndfArm := by kernel_rfl

theorem nof_at' (y : Noun) : slot? 0xabb7 (C comp.door y) = some ndfArm := by kernel_rfl

/-- The trap of `+need-ord-from` down the axis. -/
theorem nof_loop (hc : CompIn ctx) (B G : Noun) (ned : NeedOrd) :
    ∀ axe, 1 ≤ axe →
    nock (C ndfL1 (C B (C (C (A axe) ned.toNoun) (C comp.door (C G ctx))))) ndfL1
      = (fromOrd axe ned).map NeedOrd.toNoun := by
  have hl1 := cf_layer1 hc
  have har := cf_arith
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
    intro ha
    by_cases a1 : axe = 1
    · subst a1
      nock_open ndfL1
      rw [fromOrd.eq_def]
      simp [nock_exec]
    · have h2 : 2 ≤ axe := by omega
      have hcap := cap_gate layer1 har.2.2.2 axe h2
      have hmas := mas_gate layer1 har axe h2
      have hm1 : 1 ≤ masF axe := masF_pos axe h2
      have ihm := ih (masF axe) (by rw [masF_eq_mas]; exact mas_lt axe h2) hm1
      have hne : ¬ (1 = axe) := by omega
      nock_open ndfL1
      rw [fromOrd.eq_def]
      rcases capF_cases axe h2 with hc2 | hc3
      · simp [nock_exec, hl1, hne, a1, cap_arm, cap.arm_at, hcap, hc2, mas_arm, mas.arm_at, hmas, ihm,
          show ¬ axe = 0 by omega, ← capF_eq_cap, ← masF_eq_mas, NeedOrd.toNoun, Tag.none]
        cases fromOrd (masF axe) ned <;> simp [NeedOrd.toNoun, Tag.none]
      · simp [nock_exec, hl1, hne, a1, cap_arm, cap.arm_at, hcap, hc3, mas_arm, mas.arm_at, hmas, ihm,
          show ¬ axe = 0 by omega, ← capF_eq_cap, ← masF_eq_mas, NeedOrd.toNoun, Tag.none]
        cases fromOrd (masF axe) ned <;> simp [NeedOrd.toNoun, Tag.none]

/-- **`+need-ord-from`** is `needOrdFrom` on every axis and shape, in every door core whose
context has layer 2. -/
theorem nof_gate (hc : CompIn ctx) (G : Noun) (axe : Nat) (ned : NeedOrd) :
    nock (C ndfBat (C (C (A axe) ned.toNoun) (C comp.door (C G ctx)))) ndfBat
      = (needOrdFrom axe ned).map NeedOrd.toNoun := by
  have hl1 := cf_layer1 hc
  by_cases hn : ned = NeedOrd.none
  · subst hn
    nock_open ndfBat
    simp [nock_exec, needOrdFrom, NeedOrd.toNoun, Tag.none]
  by_cases a0 : axe = 0
  · subst a0
    have hl := cap_gate_lt layer1 0 (by decide)
    have hf : fromOrd 0 ned = Option.none := by rw [fromOrd.eq_def]; simp
    conv => lhs; arg 2; unfold ndfBat
    cases ned with
    | none => exact absurd rfl hn
    | pair p q =>
      obtain ⟨a, b, hp⟩ := no_cell p
      unfold ndfL1
      simp [nock_exec, needOrdFrom, NeedOrd.toNoun, hp, hl1, cap_arm, cap.arm_at, hl, hf]
    | this =>
      unfold ndfL1
      simp [nock_exec, needOrdFrom, NeedOrd.toNoun, Tag.this, Tag.none, hl1, cap_arm, cap.arm_at, hl, hf]
    | both h t =>
      unfold ndfL1
      simp [nock_exec, needOrdFrom, NeedOrd.toNoun, Tag.both, Tag.none, hl1, cap_arm, cap.arm_at, hl, hf]
  have hlp := nof_loop hc ndfBat G ned axe (by omega)
  conv => lhs; arg 2; unfold ndfBat
  cases ned with
  | none => exact absurd rfl hn
  | pair p q =>
    obtain ⟨a, b, hp⟩ := no_cell p
    simp only [NeedOrd.toNoun, hp] at hlp
    simp [nock_exec, needOrdFrom, NeedOrd.toNoun, hp, hlp, a0]
  | this =>
    simp only [NeedOrd.toNoun, Tag.this] at hlp
    simp [nock_exec, needOrdFrom, NeedOrd.toNoun, Tag.this, Tag.none, hlp, a0]
  | both h t =>
    simp only [NeedOrd.toNoun, Tag.both] at hlp
    simp [nock_exec, needOrdFrom, NeedOrd.toNoun, Tag.both, Tag.none, hlp, a0]

/-- The noun of what `+need-ord-cut` returns. -/
def cutONoun : Option (NeedOrd × NeedOrd) → Noun := unitNoun fun e => C e.1.toNoun e.2.toNoun

/-- **`+need-ord-cut`** is `needOrdCut` on every axis and shape, in every door core whose context
has layer 2 and `+cons-need` in `K` (`CompLib`). -/
theorem noc_gate (hc : CompIn ctx) (hl : CompLib ctx) (G : Noun) :
    ∀ (ned : NeedOrd) (axe : Nat),
    nock (C ndcBat (C (C (A axe) ned.toNoun) (C comp.door (C G ctx)))) ndcBat
      = (needOrdCut axe ned).map cutONoun := by
  obtain ⟨K, h7, _, hcn⟩ := hl
  have hl1 := cf_layer1 hc
  have har := cf_arith
  intro ned
  induction ned with
  | none =>
    intro axe
    nock_open ndcBat
    rw [needOrdCut.eq_def]
    by_cases a1 : axe = 1
    · subst a1; simp [nock_exec, NeedOrd.toNoun, cutONoun, unitNoun, Tag.none]
    · have a1' : ¬ (1 = axe) := fun h => a1 h.symm
      simp [nock_exec, NeedOrd.toNoun, cutONoun, unitNoun, a1, a1', Tag.none]
  | this =>
    intro axe
    nock_open ndcBat
    rw [needOrdCut.eq_def]
    by_cases a1 : axe = 1
    · subst a1; simp [nock_exec, NeedOrd.toNoun, cutONoun, unitNoun, Tag.none]
    · have a1' : ¬ (1 = axe) := fun h => a1 h.symm
      simp [nock_exec, NeedOrd.toNoun, cutONoun, unitNoun, a1, a1', Tag.none, Tag.this]
  | both h t _ _ =>
    intro axe
    nock_open ndcBat
    rw [needOrdCut.eq_def]
    by_cases a1 : axe = 1
    · subst a1; simp [nock_exec, NeedOrd.toNoun, cutONoun, unitNoun, Tag.none]
    · have a1' : ¬ (1 = axe) := fun h => a1 h.symm
      simp [nock_exec, NeedOrd.toNoun, cutONoun, unitNoun, a1, a1', Tag.none, Tag.this, Tag.both]
  | pair p q ihp ihq =>
    intro axe
    obtain ⟨a, b, hp⟩ := no_cell p
    by_cases a1 : axe = 1
    · subst a1
      nock_open ndcBat
      rw [needOrdCut.eq_def]
      simp [nock_exec, NeedOrd.toNoun, cutONoun, unitNoun, Tag.none]
    have a1' : ¬ (1 = axe) := fun h => a1 h.symm
    by_cases a0 : axe = 0
    · subst a0
      have hl := cap_gate_lt layer1 0 (by decide)
      nock_open ndcBat
      rw [needOrdCut.eq_def]
      simp [nock_exec, NeedOrd.toNoun, hp, hl1, cap_arm, cap.arm_at, hl]
    have h2 : 2 ≤ axe := by omega
    have hcap := cap_gate layer1 har.2.2.2 axe h2
    have hmas := mas_gate layer1 har axe h2
    have ip := ihp (masF axe)
    have iq := ihq (masF axe)
    rw [hp] at ip
    nock_open ndcBat
    rw [needOrdCut.eq_def]
    rcases capF_cases axe h2 with hc2 | hc3
    · have hcm : cap axe = 2 := by rw [← capF_eq_cap]; exact hc2
      cases e : needOrdCut (masF axe) p with
      | none =>
        rw [e] at ip
        simp [nock_exec, NeedOrd.toNoun, hp, hl1, cap_arm, cap.arm_at, hcap, hc2, hcm,
          mas_arm, mas.arm_at, hmas, ip, a0, a1, a1', ← masF_eq_mas, e]
      | some k =>
        rw [e] at ip
        cases k with
        | none =>
          simp [nock_exec, NeedOrd.toNoun, hp, hl1, cap_arm, cap.arm_at, hcap, hc2, hcm,
            mas_arm, mas.arm_at, hmas, ip, a0, a1, a1', ← masF_eq_mas, e, cutONoun, unitNoun]
        | some dr =>
          obtain ⟨d, r⟩ := dr
          simp [nock_exec, NeedOrd.toNoun, hp, hl1, cap_arm, cap.arm_at, hcap, hc2, hcm,
            mas_arm, mas.arm_at, hmas, ip, a0, a1, a1', ← masF_eq_mas, e, cutONoun, unitNoun, h7,
            hcn, cnArm, cn_gate_ord]
    · have hcm : cap axe = 3 := by rw [← capF_eq_cap]; exact hc3
      cases e : needOrdCut (masF axe) q with
      | none =>
        rw [e] at iq
        simp [nock_exec, NeedOrd.toNoun, hp, hl1, cap_arm, cap.arm_at, hcap, hc3, hcm,
          mas_arm, mas.arm_at, hmas, iq, a0, a1, a1', ← masF_eq_mas, e]
      | some k =>
        rw [e] at iq
        cases k with
        | none =>
          simp [nock_exec, NeedOrd.toNoun, hp, hl1, cap_arm, cap.arm_at, hcap, hc3, hcm,
            mas_arm, mas.arm_at, hmas, iq, a0, a1, a1', ← masF_eq_mas, e, cutONoun, unitNoun]
        | some dr =>
          obtain ⟨d, r⟩ := dr
          have hcg := cn_gate_ord K p r
          rw [hp] at hcg
          simp [nock_exec, NeedOrd.toNoun, hp, hl1, cap_arm, cap.arm_at, hcap, hc3, hcm,
            mas_arm, mas.arm_at, hmas, iq, a0, a1, a1', ← masF_eq_mas, e, cutONoun, unitNoun, h7,
            hcn, cnArm, hcg]

/-! ## `+laze-leap`: the looks -/

theorem llp_arm (d : Noun) : nock d llpArm = some (C llpGate (C llpBunt d)) := by
  unfold llpArm; simp only [nock_exec]

/-- The gate of the `+rep:in` of `+laze-leap`, on a positive look. -/
theorem llp_g1 (hc : CompIn ctx) (hl : CompLib ctx) (cutN L G : Noun) (p s a : Nat) (hp : p ≠ 0)
    (hs : s ≠ 0) (ha : a ≠ 0) (acc : CSet × CSet) :
    nock (C llpG1 (C (C (A a) (ssN acc)) (C cutN (C llpGate (C (C (A p) (C (A s) L))
      (C comp.door (C G ctx))))))) llpG1 = some (ssN (llStep p s acc a)) := by
  obtain ⟨K, h7, hgp, _⟩ := hl
  have hl1 := cf_layer1 hc
  have hK2 := ci_layer2_K hc h7
  have hg := gep_gate K hK2 p a
  rw [gep_pos hp ha] at hg
  obtain ⟨b, r⟩ := acc
  unfold llStep
  nock_open llpG1
  cases e : (gep p a).join with
  | none =>
    rw [e] at hg
    have hpt := cs_put_in r a
    simp [nock_exec, ssN, h7, hgp, gepArm, hg, unitNoun, hc, in_arm, in.arm_at, put_in_arm, hpt]
  | some d =>
    rw [e] at hg
    have hpg := pi_peg hs (gep_join_pos e)
    have hpb := cs_put_in b (pegF s d)
    simp [nock_exec, ssN, h7, hgp, gepArm, hg, unitNoun, hc, in_arm, in.arm_at, put_in_arm, hpb,
      hl1, peg_arm, peg.arm_at, hpg]

/-- **The `+rep:in` of `+laze-leap`** over the looks of the root sure need is `leapLok`, on
positive `p`, `s` and looks. -/
theorem llp_lok (hc : CompIn ctx) (hl : CompLib ctx) (cutN L G : Noun) (p s : Nat) (hp : p ≠ 0)
    (hs : s ≠ 0) (lok : CSet) (h0 : ∀ y ∈ HoonSet.toList lok, y ≠ 0) :
    nock (C by.rep.battery (C (C llpG1 (C (C (A 0) (ssN (HoonSet.empty, HoonSet.empty)))
      (C cutN (C llpGate (C (C (A p) (C (A s) L)) (C comp.door (C G ctx)))))))
      (C «in».battery (C (HoonSet.toNoun lok) layer2)))) by.rep.battery
      = (leapLok p s lok).map ssN := by
  have hrep := rep_gate_on ssN (fun n acc => match n with | Noun.atom y => llStep p s acc y | _ => acc)
    «in».battery layer2 llpG1 (A 0) (C cutN (C llpGate (C (C (A p) (C (A s) L)) (C comp.door (C G ctx)))))
    (HoonSet.toNoun lok) (cs_tree lok) (HoonSet.empty, HoonSet.empty) (by
      intro n hn acc
      rw [cs_preorder] at hn
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hn
      exact llp_g1 hc hl _ _ _ p s y hp hs (h0 y hy) acc)
  rw [cs_preorder, List.foldl_map] at hrep
  rw [hrep, leapLok_pos p s lok hp h0]
  rfl

/-! ## The model, as `mapM` -/

/-- The fork gate of `+laze-leap`, in the model. -/
noncomputable def llpFE (p s : Nat) (e : (Nat × Laze CSet) × (Nat × Laze CSet)) :
    Option (((Nat × Laze CSet) × (Nat × Laze CSet)) × ((Nat × Laze CSet) × (Nat × Laze CSet))) :=
  (lazeLeap p s e.1.2).bind fun yy => (lazeLeap p s e.2.2).map fun nn =>
    (((e.1.1, yy.1), (e.2.1, nn.1)), ((e.1.1, yy.2), (e.2.1, nn.2)))

/-- The bond gate of `+laze-leap`, in the model. -/
noncomputable def llpBE (p s : Nat) (e : Nat × Laze CSet) : Option ((Nat × Laze CSet) × (Nat × Laze CSet)) :=
  (lazeLeap p s e.2).map fun bb => ((e.1, bb.1), (e.1, bb.2))

theorem leapSF_mapM (p s : Nat) : ∀ fk : List ((Nat × Laze CSet) × (Nat × Laze CSet)),
    leapSF p s fk = fk.mapM (llpFE p s)
  | [] => rfl
  | ((oy, y), (on, n)) :: rest => by
    simp only [leapSF, List.mapM_cons, llpFE, leapSF_mapM p s rest]
    cases lazeLeap p s y <;> cases lazeLeap p s n <;> cases rest.mapM (llpFE p s) <;> rfl

theorem leapSB_mapM (p s : Nat) : ∀ bd : List (Nat × Laze CSet),
    leapSB p s bd = bd.mapM (llpBE p s)
  | [] => rfl
  | (ob, l) :: rest => by
    simp only [leapSB, List.mapM_cons, llpBE, leapSB_mapM p s rest]
    cases lazeLeap p s l <;> cases rest.mapM (llpBE p s) <;> rfl

/-- The sure needs of `by` and `rec` in the model, from the cut. -/
noncomputable def llpSurM (p s : Nat) (sur : SureO CSet) :
    Option (NeedOrd × NeedOrd) → Option (SureO CSet × SureO CSet)
  | Option.none => some ((SureO.bunt : SureO CSet), sur)
  | some (don, rec) => (leapLok p s sur.lok).bind fun (lb, lr) =>
      (needOrdFrom s don).map fun nf => ((⟨nf, lb⟩ : SureO CSet), (⟨rec, lr⟩ : SureO CSet))

/-- `lazeLeap` on a `laze` written out, its turns as `mapM`. -/
theorem lazeLeap_eq (p s : Nat) (sur : SureO CSet) (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet)))
    (bd : List (Nat × Laze CSet)) :
    lazeLeap p s (Laze.mk sur fk bd) = (needOrdCut p sur.ned).bind fun cut => (llpSurM p s sur cut).bind fun ss =>
      (fk.mapM (llpFE p s)).bind fun fs => (bd.mapM (llpBE p s)).map fun bs =>
        (lazePrune (Laze.mk ss.1 (fs.map Prod.fst) (bs.map Prod.fst)),
         lazePrune (Laze.mk ss.2 (fs.map Prod.snd) (bs.map Prod.snd))) := by
  rw [lazeLeap, leapSF_mapM, leapSB_mapM]
  simp only [Option.bind_eq_bind, Option.pure_def]
  cases needOrdCut p sur.ned with
  | none => rfl
  | some cut =>
    cases cut with
    | none =>
      simp only [Option.bind_some, llpSurM]
      cases fk.mapM (llpFE p s) <;> cases bd.mapM (llpBE p s) <;> rfl
    | some dr =>
      obtain ⟨don, rec⟩ := dr
      simp only [Option.bind_some, llpSurM]
      cases leapLok p s sur.lok with
      | none => rfl
      | some lb =>
        obtain ⟨lb, lr⟩ := lb
        simp only [Option.bind_some]
        cases needOrdFrom s don <;> simp only [Option.bind_some, Option.bind_none, Option.map_some,
          Option.map_none] <;> cases fk.mapM (llpFE p s) <;> cases bd.mapM (llpBE p s) <;> rfl

/-! ## The prunes, the `?~ cut`, the turns -/

/-- **The two `+laze-prune`** of `+laze-leap` (`llpPr`), on the turns of `+head` and `+tail`
over the forks and the bonds. -/
theorem llp_pr (hc : CompIn ctx) (G B X cutN : Noun) (sb sr : SureO CSet)
    (fs : List (((Nat × Laze CSet) × (Nat × Laze CSet)) × ((Nat × Laze CSet) × (Nat × Laze CSet))))
    (bs : List ((Nat × Laze CSet) × (Nat × Laze CSet))) :
    nock (C (listN (bs.map lzb2N)) (C (listN (fs.map lzf2N)) (C (C sb.toNoun sr.toNoun)
      (C cutN (C B (C X (C comp.door (C G ctx)))))))) llpPr
      = some (lzpN (lazePrune (Laze.mk sb (fs.map Prod.fst) (bs.map Prod.fst)),
          lazePrune (Laze.mk sr (fs.map Prod.snd) (bs.map Prod.snd)))) := by
  have hF1 := turn_head lzfE lzfE fs
  have hF2 := turn_tail lzfE lzfE fs
  have hB1 := turn_head lzbE lzbE bs
  have hB2 := turn_tail lzbE lzbE bs
  have hP1 := lpr_mk hc sb (fs.map Prod.fst) (bs.map Prod.fst) G
  have hP2 := lpr_mk hc sr (fs.map Prod.snd) (bs.map Prod.snd) G
  have hlp := lpr_at
  have e1 : (fs.map lzf2N) = fs.map fun x => C (lzfE x.1) (lzfE x.2) := rfl
  have e2 : (bs.map lzb2N) = bs.map fun x => C (lzbE x.1) (lzbE x.2) := rfl
  rw [e1, e2]
  generalize comp.door = Dr at hP1 hP2 hlp ⊢
  generalize (fs.map fun x => C (lzfE x.1) (lzfE x.2)) = FN at hF1 hF2 ⊢
  generalize (bs.map fun x => C (lzbE x.1) (lzbE x.2)) = BN at hB1 hB2 ⊢
  generalize ((fs.map Prod.fst).map lzfE) = F1 at hF1 hP1
  generalize ((fs.map Prod.snd).map lzfE) = F2 at hF2 hP2
  generalize ((bs.map Prod.fst).map lzbE) = B1 at hB1 hP1
  generalize ((bs.map Prod.snd).map lzbE) = B2 at hB2 hP2
  unfold llpPr
  simp [nock_exec, lzpN, hc, turn.arm_at, turn_arm, head_at, head_arm, tail_at, tail_arm, hF1, hF2,
    hB1, hB2, hlp, lpr_arm, hP1, hP2, buntGate]

/-- **The `?~ cut` of `+laze-leap`** (`llpSur`): the bunt sure need and the whole one when the
cut is `~`, else the `+rep:in` over the looks and `+need-ord-from` of the part. -/
theorem llp_sur (hc : CompIn ctx) (hl : CompLib ctx) (G : Noun) (p s : Nat) (hp : p ≠ 0) (hs : s ≠ 0)
    (sur : SureO CSet) (FK BK : Noun) (h0 : ∀ y ∈ HoonSet.toList sur.lok, y ≠ 0)
    (cut : Option (NeedOrd × NeedOrd)) :
    nock (C (cutONoun cut) (C llpGate (C (C (A p) (C (A s) (C sur.toNoun (C FK BK)))) (C comp.door (C G ctx)))))
      llpSur = (llpSurM p s sur cut).map fun ss => C ss.1.toNoun ss.2.toNoun := by
  cases cut with
  | none =>
    unfold llpSur
    simp [nock_exec, cutONoun, unitNoun, llpSurM, SureO.toNoun, SureO.bunt, NeedOrd.toNoun, Tag.none,
      HoonSet.toNoun_empty]
  | some dr =>
    obtain ⟨don, rec⟩ := dr
    have hk := llp_lok hc hl (cutONoun (some (don, rec))) (C sur.toNoun (C FK BK)) G p s hp hs sur.lok h0
    have hf := nof_gate hc G s don
    have hD := nof_at
    simp only [ssN, HoonSet.toNoun_empty, cutONoun, unitNoun] at hk
    simp only [SureO.toNoun] at hk ⊢
    generalize comp.door = Dr at hk hf hD ⊢
    cases e1 : leapLok p s sur.lok with
    | none =>
      rw [e1] at hk
      unfold llpSur
      simp [nock_exec, cutONoun, unitNoun, llpSurM, e1, hc, in_arm, in.arm_at, in.rep.arm_at, rep_arm, hk]
    | some lb =>
      obtain ⟨lb, lr⟩ := lb
      rw [e1] at hk
      simp only [Option.map_some, ssN] at hk
      cases e2 : needOrdFrom s don with
      | none =>
        rw [e2] at hf
        unfold llpSur
        simp [nock_exec, cutONoun, unitNoun, llpSurM, e1, e2, hc, in_arm, in.arm_at, in.rep.arm_at, rep_arm,
          hk, hD, ndf_arm, hf]
      | some nf =>
        rw [e2] at hf
        unfold llpSur
        simp [nock_exec, cutONoun, unitNoun, llpSurM, e1, e2, hc, in_arm, in.arm_at, in.rep.arm_at, rep_arm,
          hk, hD, ndf_arm, hf]

/-- **The turns of `+laze-leap`** over the forks (gate `llpG2`) and the bonds (gate `llpG3`),
then the prunes (`llpR2`), given the gates. -/
theorem llp_r2 (hc : CompIn ctx) (G : Noun) (p s : Nat) (sur sb sr : SureO CSet)
    (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet))) (bd : List (Nat × Laze CSet)) (cutN : Noun)
    (hF : ∀ e ∈ fk, ∀ SS cN : Noun, nock (C llpG2 (C (lzfE e) (C SS (C cN (C llpGate
      (C (C (A p) (C (A s) (C sur.toNoun (C (listN (fk.map lzfE)) (listN (bd.map lzbE))))))
        (C comp.door (C G ctx)))))))) llpG2 = (llpFE p s e).map lzf2N)
    (hB : ∀ e ∈ bd, ∀ FS SS cN : Noun, nock (C llpG3 (C (lzbE e) (C FS (C SS (C cN (C llpGate
      (C (C (A p) (C (A s) (C sur.toNoun (C (listN (fk.map lzfE)) (listN (bd.map lzbE))))))
        (C comp.door (C G ctx))))))))) llpG3 = (llpBE p s e).map lzb2N) :
    nock (C (C sb.toNoun sr.toNoun) (C cutN (C llpGate
      (C (C (A p) (C (A s) (C sur.toNoun (C (listN (fk.map lzfE)) (listN (bd.map lzbE))))))
        (C comp.door (C G ctx)))))) llpR2
      = (fk.mapM (llpFE p s)).bind fun fs => (bd.mapM (llpBE p s)).map fun bs =>
          lzpN (lazePrune (Laze.mk sb (fs.map Prod.fst) (bs.map Prod.fst)),
            lazePrune (Laze.mk sr (fs.map Prod.snd) (bs.map Prod.snd))) := by
  have hFk := turn_gate_mapT lzfE lzf2N layer2 homoIn_layer2 llpG2 (C (C (A 0) lzBunt) (C (A 0) lzBunt))
    (C (C sb.toNoun sr.toNoun) (C cutN (C llpGate
      (C (C (A p) (C (A s) (C sur.toNoun (C (listN (fk.map lzfE)) (listN (bd.map lzbE))))))
        (C comp.door (C G ctx)))))) (llpFE p s) fk (fun e he => hF e he _ _)
  unfold lzBunt at hFk
  cases e1 : fk.mapM (llpFE p s) with
  | none =>
    rw [e1] at hFk
    unfold llpR2
    simp [nock_exec, hc, turn.arm_at, turn_arm, hFk, buntGate]
  | some fs =>
    rw [e1] at hFk
    have hBd := turn_gate_mapT lzbE lzb2N layer2 homoIn_layer2 llpG3 (C (A 0) lzBunt)
      (C (listN (fs.map lzf2N)) (C (C sb.toNoun sr.toNoun) (C cutN (C llpGate
        (C (C (A p) (C (A s) (C sur.toNoun (C (listN (fk.map lzfE)) (listN (bd.map lzbE))))))
          (C comp.door (C G ctx)))))))
      (llpBE p s) bd (fun e he => hB e he _ _ _)
    unfold lzBunt at hBd
    cases e2 : bd.mapM (llpBE p s) with
    | none =>
      rw [e2] at hBd
      unfold llpR2
      simp [nock_exec, hc, turn.arm_at, turn_arm, hFk, hBd, buntGate]
    | some bs =>
      rw [e2] at hBd
      have hP := llp_pr hc G llpGate
        (C (A p) (C (A s) (C sur.toNoun (C (listN (fk.map lzfE)) (listN (bd.map lzbE)))))) cutN sb sr fs bs
      generalize comp.door = Dr at hP hFk hBd ⊢
      unfold llpR2
      simp [nock_exec, hc, turn.arm_at, turn_arm, hFk, hBd, buntGate, hP]

/-! ## `+laze-leap` on every `laze` -/

section
variable (hc : CompIn ctx) (hl : CompLib ctx) (G : Noun) (p s : Nat) (hp : p ≠ 0) (hs : s ≠ 0)
include hc hl hp hs

mutual
/-- `+laze-leap` on every `laze` whose looks are not `0`. -/
theorem llp_allN : ∀ (laz : Laze CSet), LzNZ laz →
    nock (C llpGate (C (C (A p) (C (A s) laz.toNoun)) (C comp.door (C G ctx)))) llpGate
      = (lazeLeap p s laz).map lzpN
  | Laze.mk sur fk bd, ⟨hs0, hfk, hbd⟩ => by
    have hcut := noc_gate hc hl G sur.ned p
    have hD := noc_at
    rw [lazeLeap_eq, lz_toNoun_mk]
    have hr2 := fun sb sr cutN => llp_r2 hc G p s sur sb sr fk bd cutN
      (fun e he SS cN => llp_forks fk hfk e he SS cN _) (fun e he FS SS cN => llp_bonds bd hbd e he FS SS cN _)
    have hsur := fun cut => llp_sur hc hl G p s hp hs sur (listN (fk.map lzfE)) (listN (bd.map lzbE)) hs0 cut
    simp only [SureO.toNoun] at hr2 hsur ⊢
    generalize comp.door = Dr at hcut hD hr2 hsur ⊢
    cases e1 : needOrdCut p sur.ned with
    | none =>
      rw [e1] at hcut
      conv => lhs; arg 2; unfold llpGate
      simp [nock_exec, hD, ndc_arm, hcut]
    | some cut =>
      rw [e1] at hcut
      have hs1 := hsur cut
      cases e2 : llpSurM p s sur cut with
      | none =>
        rw [e2] at hs1
        conv => lhs; arg 2; unfold llpGate
        simp [nock_exec, hD, ndc_arm, hcut, hs1, e2]
      | some ss =>
        obtain ⟨sb, sr⟩ := ss
        rw [e2] at hs1
        conv => lhs; arg 2; unfold llpGate
        simp [nock_exec, hD, ndc_arm, hcut, hs1, e2, hr2]
        cases fk.mapM (llpFE p s) <;> cases bd.mapM (llpBE p s) <;> rfl

theorem llp_forks : ∀ (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet))), LzNZF fk → ∀ e ∈ fk,
    ∀ SS cN L : Noun,
    nock (C llpG2 (C (lzfE e) (C SS (C cN (C llpGate (C (C (A p) (C (A s) L)) (C comp.door (C G ctx))))))))
      llpG2 = (llpFE p s e).map lzf2N
  | [], _, e, he => absurd he List.not_mem_nil
  | ((oy, y), (on, n)) :: rest, ⟨hy, hn, hr⟩, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro SS cN L
      have ihy := llp_allN y hy
      have ihn := llp_allN n hn
      unfold llpG2
      cases e1 : lazeLeap p s y with
      | none => rw [e1] at ihy; simp [nock_exec, lzfE, ihy, llpFE, e1]
      | some yy =>
        rw [e1] at ihy
        cases e2 : lazeLeap p s n with
        | none => rw [e2] at ihn; simp [nock_exec, lzfE, ihy, ihn, llpFE, e1, e2]
        | some nn => rw [e2] at ihn; simp [nock_exec, lzfE, ihy, ihn, llpFE, e1, e2, lzpN, lzf2N]
    · exact llp_forks rest hr e he'

theorem llp_bonds : ∀ (bd : List (Nat × Laze CSet)), LzNZB bd → ∀ e ∈ bd,
    ∀ FS SS cN L : Noun,
    nock (C llpG3 (C (lzbE e) (C FS (C SS (C cN (C llpGate (C (C (A p) (C (A s) L)) (C comp.door (C G ctx)))))))))
      llpG3 = (llpBE p s e).map lzb2N
  | [], _, e, he => absurd he List.not_mem_nil
  | (ob, l) :: rest, ⟨hl', hr⟩, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro FS SS cN L
      have ihl := llp_allN l hl'
      unfold llpG3
      cases e1 : lazeLeap p s l with
      | none => rw [e1] at ihl; simp [nock_exec, lzbE, ihl, llpBE, e1]
      | some bb => rw [e1] at ihl; simp [nock_exec, lzbE, ihl, llpBE, e1, lzpN, lzb2N]
    · exact llp_bonds rest hr e he'
end

end

/-- **`+laze-leap`** is `lazeLeap` on every `laze` whose looks are not `0`, on positive `p` and
`s`, crashes included, on every `gen`, under `CompIn ctx` and `K` at axis `7`. -/
theorem llp_all (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) (G : Noun) {p s : Nat}
    (hp : p ≠ 0) (hs : s ≠ 0) (laz : Laze CSet) (h : LzNZ laz) :
    nock (C llpGate (C (C (A p) (C (A s) laz.toNoun)) (C comp.door (C G ctx)))) llpGate
      = (lazeLeap p s laz).map fun x => C x.1.toNoun x.2.toNoun :=
  llp_allN hc ⟨compK, h7, compK_gep, compK_cn⟩ G p s hp hs laz h

/-! ## What `+laze-leap` returns (the model) -/

theorem llpSurM_nz {p s : Nat} (hp : p ≠ 0) (hs : s ≠ 0) {sur sb sr : SureO CSet}
    {cut : Option (NeedOrd × NeedOrd)} (h0 : ∀ y ∈ HoonSet.toList sur.lok, y ≠ 0)
    (h : llpSurM p s sur cut = some (sb, sr)) :
    (∀ y ∈ HoonSet.toList sb.lok, y ≠ 0) ∧ (∀ y ∈ HoonSet.toList sr.lok, y ≠ 0) := by
  cases cut with
  | none =>
    simp only [llpSurM, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun y hy => absurd hy (HoonSet.mem_empty y), h0⟩
  | some dr =>
    obtain ⟨don, rec⟩ := dr
    simp only [llpSurM] at h
    cases e1 : leapLok p s sur.lok with
    | none => simp [e1] at h
    | some lb =>
      obtain ⟨lb, lr⟩ := lb
      cases e2 : needOrdFrom s don with
      | none => simp [e1, e2] at h
      | some nf =>
        simp only [e1, e2, Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact leapLok_lok hp hs h0 e1

section
variable {p s : Nat} (hp : p ≠ 0) (hs : s ≠ 0)
include hp hs

mutual
/-- **What `+laze-leap` returns looks at no axis `0`** when its `laze` does not. -/
theorem lazeLeap_nz : ∀ (laz b r : Laze CSet), LzNZ laz → lazeLeap p s laz = some (b, r) → LzNZ b ∧ LzNZ r
  | Laze.mk sur fk bd, b, r, ⟨hs0, hfk, hbd⟩, h => by
    rw [lazeLeap_eq] at h
    cases e1 : needOrdCut p sur.ned with
    | none => simp [e1] at h
    | some cut =>
      cases e2 : llpSurM p s sur cut with
      | none => simp [e1, e2] at h
      | some ss =>
        obtain ⟨sb, sr⟩ := ss
        cases e3 : fk.mapM (llpFE p s) with
        | none => simp [e1, e2, e3] at h
        | some fs =>
          cases e4 : bd.mapM (llpBE p s) with
          | none => simp [e1, e2, e3, e4] at h
          | some bs =>
            simp only [e1, e2, e3, e4, Option.bind_some, Option.map_some, Option.some.injEq,
              Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hss := llpSurM_nz hp hs hs0 e2
            obtain ⟨hf1, hf2⟩ := llpF_nz fk hfk fs e3
            obtain ⟨hb1, hb2⟩ := llpB_nz bd hbd bs e4
            exact ⟨lazePrune_nz _ ⟨hss.1, hf1, hb1⟩, lazePrune_nz _ ⟨hss.2, hf2, hb2⟩⟩

theorem llpF_nz : ∀ (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet))), LzNZF fk →
    ∀ fs, fk.mapM (llpFE p s) = some fs → LzNZF (fs.map Prod.fst) ∧ LzNZF (fs.map Prod.snd)
  | [], _, fs, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; exact ⟨trivial, trivial⟩
  | ((oy, y), (on, n)) :: rest, ⟨hy, hn, hr⟩, fs, h => by
    simp only [List.mapM_cons] at h
    cases e1 : lazeLeap p s y with
    | none => simp [llpFE, e1] at h
    | some yy =>
      obtain ⟨yb, yr⟩ := yy
      cases e2 : lazeLeap p s n with
      | none => simp [llpFE, e1, e2] at h
      | some nn =>
        obtain ⟨nb, nr⟩ := nn
        cases e3 : rest.mapM (llpFE p s) with
        | none => simp [llpFE, e1, e2, e3] at h
        | some rs =>
          simp [llpFE, e1, e2, e3] at h
          subst h
          obtain ⟨y1, y2⟩ := lazeLeap_nz y yb yr hy e1
          obtain ⟨n1, n2⟩ := lazeLeap_nz n nb nr hn e2
          obtain ⟨r1, r2⟩ := llpF_nz rest hr rs e3
          exact ⟨⟨y1, n1, r1⟩, ⟨y2, n2, r2⟩⟩

theorem llpB_nz : ∀ (bd : List (Nat × Laze CSet)), LzNZB bd →
    ∀ bs, bd.mapM (llpBE p s) = some bs → LzNZB (bs.map Prod.fst) ∧ LzNZB (bs.map Prod.snd)
  | [], _, bs, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; exact ⟨trivial, trivial⟩
  | (ob, l) :: rest, ⟨hl', hr⟩, bs, h => by
    simp only [List.mapM_cons] at h
    cases e1 : lazeLeap p s l with
    | none => simp [llpBE, e1] at h
    | some bb =>
      obtain ⟨lb, lr⟩ := bb
      cases e3 : rest.mapM (llpBE p s) with
      | none => simp [llpBE, e1, e3] at h
      | some rs =>
        simp [llpBE, e1, e3] at h
        subst h
        obtain ⟨l1, l2⟩ := lazeLeap_nz l lb lr hl' e1
        obtain ⟨r1, r2⟩ := llpB_nz rest hr rs e3
        exact ⟨⟨l1, r1⟩, ⟨l2, r2⟩⟩
end

end

/-! ## `+laze-leaps` -/

/-- The noun of what `+laze-leaps` returns. -/
noncomputable def llsN : Option (Laze CSet × List (Laze CSet)) → Noun :=
  unitNoun fun x => C x.1.toNoun (listN (x.2.map Laze.toNoun))

theorem listN_laze_cons (b : Laze CSet) (l : List (Laze CSet)) :
    listN ((b :: l).map Laze.toNoun) = C b.toNoun (listN (l.map Laze.toNoun)) := rfl

theorem lls_arm (d : Noun) : nock d llsArm = some (C llsGate (C llsBunt d)) := by
  unfold llsArm; simp only [nock_exec]

/-- **The loop of `+laze-leaps`** (`llsL1`) is `leapsLoop`, on lists of parts with no axis `0`
and `laze`s whose looks are not `0`. -/
theorem lls_loop (hc : CompIn ctx) (hl : CompLib ctx) (G B X Y : Noun) (sur : SureO CSet) :
    ∀ (pas : List (Nat × Nat)) (lab : Laze CSet) (bys : List (Laze CSet)), PosL pas → LzNZ lab →
    nock (C llsL1 (C (listN (bys.map Laze.toNoun)) (C lab.toNoun (C (lN pas)
      (C B (C (C (C sur.toNoun Y) X) (C comp.door (C G ctx)))))))) llsL1
      = (leapsLoop sur pas lab bys).map llsN := by
  have hz := llp_at
  have he := lem_at
  intro pas
  induction pas with
  | nil =>
    intro lab bys _ _
    obtain ⟨ls, lf, lb⟩ := lab
    rw [lN_nil, lz_toNoun_mk]
    generalize comp.door = Dr at hz he ⊢
    nock_open llsL1
    cases bys with
    | nil => simp [nock_exec, leapsLoop, llsN, unitNoun]
    | cons b bs =>
      rw [listN_laze_cons]
      simp [nock_exec, leapsLoop, llsN, unitNoun, lz_toNoun_mk, Laze.fork, Laze.bond]
  | cons e rest ih =>
    intro lab bys hpos hlab
    obtain ⟨p, s⟩ := e
    have hp : p ≠ 0 := (hpos (p, s) List.mem_cons_self).1
    have hs : s ≠ 0 := (hpos (p, s) List.mem_cons_self).2
    have hrest : PosL rest := fun x hx => hpos x (List.mem_cons_of_mem _ hx)
    have hg := llp_allN hc hl G p s hp hs lab hlab
    rw [lN_cons]
    cases e1 : lazeLeap p s lab with
    | none =>
      rw [e1] at hg
      generalize comp.door = Dr at hz he hg ⊢
      nock_open llsL1
      simp [nock_exec, hz, llp_arm, hg, leapsLoop, e1]
    | some br =>
      obtain ⟨b, r⟩ := br
      rw [e1] at hg
      simp only [Option.map_some, lzpN] at hg
      have hle := lem_gate b (C comp.door (C G ctx))
      have ih1 := ih lab bys hrest hlab
      have ih2 := ih r (b :: bys) hrest (lazeLeap_nz hp hs lab b r hlab e1).2
      rw [listN_laze_cons] at ih2
      generalize comp.door = Dr at hz he hg hle ih1 ih2 ⊢
      nock_open llsL1
      cases eb : lazeEmpty b with
      | true =>
        rw [eb] at hle
        simp [nock_exec, hz, llp_arm, hg, he, lem_arm, hle, loob, ih1, leapsLoop, e1, eb]
      | false =>
        rw [eb] at hle
        simp [nock_exec, hz, llp_arm, hg, he, lem_arm, hle, loob, ih2, leapsLoop, e1, eb]

/-- **`+laze-leaps`** is `lazeLeaps` on every `laze` whose looks are not `0` and nomms with no
`%10` at axis `0`, crashes included, on every `gen`, in every door core whose context has `K` at
`7`.  `~` is `A 0`, `[~ rest bys]` is `[0 rest bys]` (`llsN`). -/
theorem lls_all (h7 : slot? 7 ctx = some compK) (G : Noun) (laz : Laze CSet) (q r : Nomm)
    (hl : LzNZ laz) (hq : Bake.NoAx0 q) (hr : Bake.NoAx0 r) :
    nock (C llsGate (C (C laz.toNoun (C q.toNoun r.toNoun)) (C comp.door (C G ctx)))) llsGate
      = (lazeLeaps laz q r).map llsN := by
  obtain ⟨hc, hcl, -⟩ := comp_ctx_pill ctx h7
  obtain ⟨pas, hpb, hpos, hpn⟩ := pbt_gate passIn_compK q r hq hr
  obtain ⟨sur, fk, bd⟩ := laz
  have hlab : LzNZ (Laze.mk SureO.bunt fk bd) :=
    ⟨fun y hy => absurd hy (HoonSet.mem_empty y), hl.2.1, hl.2.2⟩
  have hb : (Laze.mk (SureO.bunt : SureO CSet) fk bd).toNoun
      = C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (listN (fk.map lzfE)) (listN (bd.map lzbE))) := by
    rw [lz_toNoun_mk]; simp [SureO.toNoun, SureO.bunt, NeedOrd.toNoun, Tag.none, HoonSet.toNoun_empty]
  have hlp := lls_loop hc hcl G llsGate (C q.toNoun r.toNoun) (C (listN (fk.map lzfE)) (listN (bd.map lzbE)))
    sur pas (Laze.mk SureO.bunt fk bd) [] hpos hlab
  rw [hb, List.map_nil, show listN ([] : List Noun) = A 0 from rfl] at hlp
  have hpa := pbt_at
  rw [lz_toNoun_mk]
  generalize comp.door = Dr at hlp ⊢
  have tF := lz_test lzfE fk
  have tB := lz_test lzbE bd
  conv => lhs; arg 2; unfold llsGate
  rcases tF with ⟨t1, t2, t3⟩ | ⟨t1, t2, t3⟩ <;> rcases tB with ⟨t4, t5, t6⟩ | ⟨t4, t5, t6⟩
  · subst t1; subst t4
    simp [nock_exec, lazeLeaps, llsN, unitNoun, Laze.fork, Laze.bond]
  all_goals
    first | replace t1 := eq_false t1 | replace t1 := eq_true t1
    first | replace t4 := eq_false t4 | replace t4 := eq_true t4
    simp [nock_exec, lazeLeaps, Laze.fork, Laze.bond, Laze.sure, t1, t2, t3, t4, t5, t6, List.isEmpty_iff, h7,
      hpa, pbt_arm, hpn, hpb, hlp]

/-- The arm `+laze-leaps` on the door gives the gate `llsGate`. -/
theorem lls_door (y : Noun) : nock (C comp.door y) (C (A 9) (C (A 0x1556) (C (A 0) (A 1))))
    = some (C llsGate (C llsBunt (C comp.door y))) := by
  simp [nock_exec, lls_at', lls_arm]

/-! ## What `+laze-leaps` returns (the model) -/

/-- The loop of `+laze-leaps` keeps `LzNZ`, of `rest` and of every `by`. -/
theorem leapsLoop_nz (sur : SureO CSet) (hsur : ∀ y ∈ HoonSet.toList sur.lok, y ≠ 0) :
    ∀ (pas : List (Nat × Nat)) (lab : Laze CSet) (bys : List (Laze CSet)) (res : Laze CSet × List (Laze CSet)),
    PosL pas → LzNZ lab → (∀ b ∈ bys, LzNZ b) → leapsLoop sur pas lab bys = some (some res) →
    LzNZ res.1 ∧ ∀ b ∈ res.2, LzNZ b
  | [], lab, bys, res, _, hl, hb, h => by
    obtain ⟨ls, lf, lb⟩ := lab
    simp only [leapsLoop] at h
    split at h
    · cases h
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨⟨hsur, hl.2.1, hl.2.2⟩, hb⟩
  | (p, s) :: rest, lab, bys, res, hpos, hl, hb, h => by
    have hp : p ≠ 0 := (hpos (p, s) List.mem_cons_self).1
    have hs : s ≠ 0 := (hpos (p, s) List.mem_cons_self).2
    have hrest : PosL rest := fun x hx => hpos x (List.mem_cons_of_mem _ hx)
    simp only [leapsLoop] at h
    cases e : lazeLeap p s lab with
    | none => simp [e] at h
    | some br =>
      obtain ⟨b, r⟩ := br
      obtain ⟨h1, h2⟩ := lazeLeap_nz hp hs lab b r hl e
      simp only [e, Option.bind_some] at h
      split at h
      · exact leapsLoop_nz sur hsur rest lab bys res hrest hl hb h
      · refine leapsLoop_nz sur hsur rest r (b :: bys) res hrest h2 ?_ h
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact h1
        · exact hb y hy

/-- **What `+laze-leaps` returns looks at no axis `0`**: `rest` and every `by`. -/
theorem lazeLeaps_nz {laz : Laze CSet} {q r : Nomm} {res : Laze CSet × List (Laze CSet)} (hl : LzNZ laz)
    (hq : Bake.NoAx0 q) (hr : Bake.NoAx0 r) (h : lazeLeaps laz q r = some (some res)) :
    LzNZ res.1 ∧ ∀ b ∈ res.2, LzNZ b := by
  obtain ⟨pas, hpb, hpos, -⟩ := pbt_gate passIn_compK q r hq hr
  obtain ⟨sur, fk, bd⟩ := laz
  simp only [lazeLeaps] at h
  split at h
  · cases h
  · rw [hpb, Option.bind_some] at h
    exact leapsLoop_nz sur hl.1 pas (Laze.mk SureO.bunt fk bd) [] res hpos
      ⟨fun y hy => absurd hy (HoonSet.mem_empty y), hl.2.1, hl.2.2⟩ (fun _ hb => absurd hb List.not_mem_nil) h

end Compiler
end Formalization
