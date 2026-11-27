import lemmas.Compiler.CompRunShapeSplit
import lemmas.Compiler.CompRunShapeIntoCut
import lemmas.Compiler.CompInto
import lemmas.Compiler.CompShapeColUni

/-!
# The link of `+laze-into` (track A, 2026-11-27)

`+laze-into` (door arm `0x2afffd`, cut in `CompRunShapeIntoCut.lean`) against `lazeInto` of
`Ska/RunShape.lean`, on every axis and every `laze` (forks and bonds to any depth) whose looks
are not `0` (`LzNZ`), on every noun `G` of `gen` (the arm reads none of it), under `CompIn ctx`
and `K` at axis `7` of `ctx` (the arm pulls `+gep` and `+cons-need` of `K`).  The `+into` of
`need-lazy` (`CompInto.lean`, `CompIntoGen.lean`) without registers and blocks, with the turns
and prunes of `+laze-split` (`CompRunShapeSplit.lean`).

* `lzi_rep`: the gate of the `+rep:in` over the looks is the gate of `+into-sure` (`isG0`)
  after its `?<` (`isG0_eq`), so `is_gate` gives it; `lzi_lok`: the looks (`intoLokS`).
* `lzi_trap`: the trap down the axis with the stack is `intoGo` (the `+roll` at the end,
  `lzi_roll`, with `+cons-need` of `K`; the `%both` case through `+laze-must`, `lmu_gate`);
  `lzi_ned`: the needs (`intoNed`).
* `lzi_pr`, `lzi_r`: the turns and the two `+laze-prune` (as `lsp_pr`, `lsp_r`).
* **`lzi_all`** (`lzi_allN`, with `lzi_forks`, `lzi_bonds`): the gate is `lazeInto`.
* `lzi_door`: the arm on the door gives the gate.
* **`lazeInto_nz`** (model only): both halves are `LzNZ`.

The sample is `[axe laz]`, as `rsK10` slams it.  The model takes the same steps in the same order
(the looks in the order of `HoonSet.toList`, which `+rep:in` walks, `cs_preorder`).  No departure.
On `axe = 0` both crash (the `?<`, the `none` of `lazeInto`), and `lzi_all` covers it; on a look
`0` both crash too (`+gep` of `0`), which is not linked here (`LzNZ`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

theorem lzi_arm (d : Noun) : nock d lziArm = some (C lziGate (C lziBunt d)) := by
  unfold lziArm lziHint; simp only [nock_exec]

/-- **The arm `+laze-into` on the door gives the gate `lziGate`**. -/
theorem lzi_door (y : Noun) : nock (C comp.door y) (C (A 9) (C (A 0x2afffd) (C (A 0) (A 1))))
    = some (C lziGate (C lziBunt (C comp.door y))) := by
  simp [nock_exec, lzi_at', lzi_arm]

theorem lzi_compLib (h7 : slot? 7 ctx = some compK) : CompLib ctx := ⟨compK, h7, compK_gep, compK_cn⟩

/-! ## The looks -/

/-- The gate of the `+rep:in` of `+into-sure` is the `?<  =(0 axe)` and then `lziRep`. -/
theorem isG0_eq : isG0 = C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 60)))) (C (C (A 0) (A 0)) lziRep)) := by
  kernel_rfl

/-- One slam of the gate of the `+rep:in` over the looks. -/
theorem lzi_rep (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) (B R G : Noun) (axe l : Nat)
    (ha : axe ≠ 0) (hl0 : l ≠ 0) (s : CSet × CSet) :
    nock (C lziRep (C (C (A l) (ssN s)) (C B (C (C (A axe) R) (C comp.door (C G ctx)))))) lziRep
      = some (ssN (isStep axe l s)) := by
  obtain ⟨K, hK, hgep, _⟩ := lzi_compLib h7
  have hgg := gep_gate K (ci_layer2_K hc hK) axe l
  obtain ⟨d, r⟩ := s
  unfold lziRep
  cases e : gep axe l with
  | none =>
    rcases gep_crash.1 e with h | h
    · exact absurd h ha
    · exact absurd h hl0
  | some u =>
    rw [e] at hgg
    have hpd := fun (m : CSet) (y : Nat) => put_in_gate layer2 gorIn_morIn_layer2 _ _ _ (cs_putInF m y)
    cases u with
    | none =>
      simp [nock_exec, hK, hgep, gepArm, hgg, unitNoun, isStep, e, ssN, hc, in_arm, in.arm_at,
        put_in_arm, hpd]
    | some r =>
      by_cases r1 : r = 1
      · subst r1
        simp [nock_exec, hK, hgep, gepArm, hgg, unitNoun, isStep, e, ssN, eqCode_atom]
      · have r1' : ¬ (1 = r) := fun h => r1 h.symm
        simp [nock_exec, hK, hgep, gepArm, hgg, unitNoun, isStep, e, ssN, hc, in_arm, in.arm_at,
          put_in_arm, hpd, eqCode_atom, r1, r1']

/-- The end of the looks: `axe` put in the recipient's looks unless it is `1`. -/
noncomputable def lziFinS (axe : Nat) (s : CSet × CSet) : CSet × CSet :=
  (s.1, if axe = 1 then s.2 else HoonSet.put s.2 axe)

theorem intoLokS_eq (axe : Nat) (ha : axe ≠ 0) (lok : CSet) (h0 : ∀ y ∈ HoonSet.toList lok, y ≠ 0) :
    intoLokS axe lok = some (lziFinS axe ((HoonSet.toList lok).foldl (fun s y => isStep axe y s)
      (HoonSet.empty, HoonSet.empty))) := by
  unfold intoLokS
  generalize ((HoonSet.empty, HoonSet.empty) : CSet × CSet) = acc
  generalize HoonSet.toList lok = l at h0 ⊢
  induction l generalizing acc with
  | nil => rfl
  | cons y l ih =>
    have hy : y ≠ 0 := h0 y List.mem_cons_self
    have ih' := fun acc => ih acc (fun z hz => h0 z (List.mem_cons_of_mem _ hz))
    rw [List.foldl_cons, List.foldl_cons]
    obtain ⟨d, r⟩ := acc
    have hg : gep axe y ≠ Option.none := fun h => by
      rcases gep_crash.1 h with h | h
      · exact ha h
      · exact hy h
    cases e : gep axe y with
    | none => exact absurd e hg
    | some u =>
      cases u with
      | none =>
        simp only [Option.bind_some, e, Option.map_some]
        rw [ih']; simp [isStep, e]
      | some r' =>
        by_cases r1 : r' = 1
        · subst r1
          simp only [Option.bind_some, e, Option.map_some, ↓reduceIte]
          rw [ih']; simp [isStep, e]
        · simp only [Option.bind_some, e, Option.map_some, r1, if_false]
          rw [ih']; simp [isStep, e, r1]

/-- **The looks** (`lziLok`): the `+rep:in`, then `lziFinS`, for `axe` not `0` and looks not `0`. -/
theorem lzi_lok (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) (G : Noun) (axe : Nat) (ha : axe ≠ 0)
    (s : SureO CSet) (FB : Noun) (h0 : ∀ y ∈ HoonSet.toList s.lok, y ≠ 0) :
    nock (C lziGate (C (C (A axe) (C s.toNoun FB)) (C comp.door (C G ctx)))) lziLok
      = some (ssN (lziFinS axe ((HoonSet.toList s.lok).foldl (fun s y => isStep axe y s)
          (HoonSet.empty, HoonSet.empty)))) := by
  obtain ⟨ned, lok⟩ := s
  simp only at h0
  have hrep := rep_gate_on ssN (fun n s => match n with | Noun.atom y => isStep axe y s | _ => s)
    in.battery layer2 lziRep (A 0)
    (C lziGate (C (C (A axe) (C (C ned.toNoun (HoonSet.toNoun lok)) FB)) (C comp.door (C G ctx))))
    (HoonSet.toNoun lok) (cs_tree lok) (HoonSet.empty, HoonSet.empty) (by
      intro n hn s
      rw [cs_preorder] at hn
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hn
      exact lzi_rep hc h7 _ _ _ axe y ha (h0 y hy) s)
  rw [cs_preorder, List.foldl_map] at hrep
  generalize (HoonSet.toList lok).foldl (fun s y => isStep axe y s) (HoonSet.empty, HoonSet.empty) = F at hrep ⊢
  obtain ⟨ld, lr⟩ := F
  simp only [ssN, HoonSet.toNoun_empty] at hrep
  have hpt := put_in_gate layer2 gorIn_morIn_layer2 _ _ _ (cs_putInF lr axe)
  simp only [SureO.toNoun]
  unfold lziLok lziFin
  by_cases a1 : axe = 1
  · subst a1
    simp [nock_exec, hc, in_arm, in.arm_at, in.rep.arm_at, rep_arm, hrep, ssN, lziFinS]
  · have a1' : ¬ (1 = axe) := fun h => a1 h.symm
    simp [nock_exec, hc, in_arm, in.arm_at, in.rep.arm_at, rep_arm, hrep, ssN, lziFinS, a1, a1',
      put_in_arm, hpt]

/-! ## The needs -/

/-- An entry `[h n]` of the stack. -/
def lziTackE (e : Bool × NeedOrd) : Noun := C (loob e.1) e.2.toNoun

/-- The gate of the `+roll` at the end of the trap. -/
theorem lzi_rg (L : Noun) (hL : slot? 2047 L = some compK) (e : Bool × NeedOrd) (acc : NeedOrd) :
    nock (C lziRG (C (C (lziTackE e) acc.toNoun) L)) lziRG
      = some (if e.1 then consOrd acc e.2 else consOrd e.2 acc).toNoun := by
  obtain ⟨h, n⟩ := e
  unfold lziRG
  cases h <;> simp [nock_exec, lziTackE, loob, hL, compK_cn, cnArm, cn_gate_ord]

theorem lzi_roll (L : Noun) (hL : slot? 2047 L = some compK) (tack : List (Bool × NeedOrd)) :
    nock (C roll.battery (C (C (listNoun lziTackE tack) (C lziRG (C (C (C (A 0) (C (A 0x656e6f6e)
      (A 0))) (C (A 0x656e6f6e) (A 0))) L))) layer2)) roll.battery
      = some (tack.foldl (fun acc (e : Bool × NeedOrd) => if e.1 then consOrd acc e.2 else consOrd e.2 acc)
          NeedOrd.none).toNoun := by
  have h := ci_roll_gate lziTackE NeedOrd.toNoun layer2 lziRG (C (A 0) (C (A 0x656e6f6e) (A 0))) L
    (fun e acc => if e.1 then consOrd acc e.2 else consOrd e.2 acc) tack NeedOrd.none
    (fun e _ acc => lzi_rg L hL e acc)
  simp only [NeedOrd.toNoun, Tag.none] at h
  exact h


/-- **The trap down the axis** (`lziTrap`, on the core `[lziTrap tack ned lok gate]`, with `axe`
in the gate's sample): `intoGo`. -/
theorem lzi_trap (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) (LOK L G : Noun) :
    ∀ axe, 1 ≤ axe → ∀ (ned : NeedOrd) (tack : List (Bool × NeedOrd)),
    nock (C lziTrap (C (listNoun lziTackE tack) (C ned.toNoun (C LOK (C lziGate (C (C (A axe) L)
      (C comp.door (C G ctx)))))))) lziTrap
      = (intoGo axe ned tack).map fun p => C p.1.toNoun p.2.toNoun := by
  have hl1 := cf_layer1 hc
  have har := cf_arith
  have hm := lmu_at' (C G ctx)
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
    intro ha ned tack
    by_cases a1 : axe = 1
    · subst a1
      have hTS : slot? 2047 (C lziTrap (C (listNoun lziTackE tack) (C ned.toNoun (C LOK (C lziGate (C (C (A 1) L)
          (C comp.door (C G ctx)))))))) = some compK := by simp [nock_exec, h7]
      have hr := lzi_roll _ hTS tack
      nock_open lziTrap
      rw [intoGo.eq_def]
      simp [nock_exec, hc, roll_arm, roll.arm_at, hr]
    · have h2 : 2 ≤ axe := by omega
      have hcap := cap_gate layer1 har.2.2.2 axe h2
      have hmas := mas_gate layer1 har axe h2
      have hm1 : 1 ≤ masF axe := masF_pos axe h2
      have ihm := ih (masF axe) (by rw [masF_eq_mas]; exact mas_lt axe h2) hm1
      have hne : ¬ (1 = axe) := by omega
      have a0 : ¬ axe = 0 := by omega
      nock_open lziTrap
      rw [intoGo.eq_def]
      simp only [a1, a0, if_false]
      rcases capF_cases axe h2 with hc2 | hc3
      · cases ned with
        | none =>
          have IH := ihm NeedOrd.none ((true, NeedOrd.none) :: tack)
          simp only [listNoun, lziTackE, NeedOrd.toNoun, loob, Tag.none, Tag.this, Tag.both, Bool.false_eq_true, ite_true, ite_false] at IH
          simp [nock_exec, hl1, hne, a1, cap_arm, cap.arm_at, hcap, mas_arm, mas.arm_at, hmas, ← capF_eq_cap, ← masF_eq_mas, NeedOrd.toNoun, Tag.none, Tag.this, Tag.both, listNoun, lziTackE, loob, eqCode_atom, eqCode, lmu_at', lmu_arm, lmu_gate, IH, hc2]
        | this =>
          have IH := ihm NeedOrd.this ((true, NeedOrd.this) :: tack)
          simp only [listNoun, lziTackE, NeedOrd.toNoun, loob, Tag.none, Tag.this, Tag.both, Bool.false_eq_true, ite_true, ite_false] at IH
          simp [nock_exec, hl1, hne, a1, cap_arm, cap.arm_at, hcap, mas_arm, mas.arm_at, hmas, ← capF_eq_cap, ← masF_eq_mas, NeedOrd.toNoun, Tag.none, Tag.this, Tag.both, listNoun, lziTackE, loob, eqCode_atom, eqCode, lmu_at', lmu_arm, lmu_gate, IH, hc2]
        | pair p q =>
          obtain ⟨u, v, hp⟩ := no_cell p
          have IH := ihm p ((true, q) :: tack)
          simp only [listNoun, lziTackE, NeedOrd.toNoun, loob, Tag.none, Tag.this, Tag.both, Bool.false_eq_true, ite_true, ite_false, hp] at IH
          simp [nock_exec, hl1, hne, a1, cap_arm, cap.arm_at, hcap, mas_arm, mas.arm_at, hmas, ← capF_eq_cap, ← masF_eq_mas, NeedOrd.toNoun, Tag.none, Tag.this, Tag.both, listNoun, lziTackE, loob, eqCode_atom, eqCode, lmu_at', lmu_arm, lmu_gate, IH, hc2, hp]
        | both l r =>
          have IH := ihm (lazeMust l) ((true, lazeMust r) :: tack)
          simp only [listNoun, lziTackE, NeedOrd.toNoun, loob, Tag.none, Tag.this, Tag.both, Bool.false_eq_true, ite_true, ite_false] at IH
          generalize comp.door = Dr at hm IH ⊢
          simp [nock_exec, hl1, hne, a1, cap_arm, cap.arm_at, hcap, mas_arm, mas.arm_at, hmas, ← capF_eq_cap, ← masF_eq_mas, NeedOrd.toNoun, Tag.none, Tag.this, Tag.both, listNoun, lziTackE, loob, eqCode_atom, eqCode, lmu_at', lmu_arm, lmu_gate, IH, hc2, hm]
      · cases ned with
        | none =>
          have IH := ihm NeedOrd.none ((false, NeedOrd.none) :: tack)
          simp only [listNoun, lziTackE, NeedOrd.toNoun, loob, Tag.none, Tag.this, Tag.both, Bool.false_eq_true, ite_true, ite_false] at IH
          simp [nock_exec, hl1, hne, a1, cap_arm, cap.arm_at, hcap, mas_arm, mas.arm_at, hmas, ← capF_eq_cap, ← masF_eq_mas, NeedOrd.toNoun, Tag.none, Tag.this, Tag.both, listNoun, lziTackE, loob, eqCode_atom, eqCode, lmu_at', lmu_arm, lmu_gate, IH, hc3]
        | this =>
          have IH := ihm NeedOrd.this ((false, NeedOrd.this) :: tack)
          simp only [listNoun, lziTackE, NeedOrd.toNoun, loob, Tag.none, Tag.this, Tag.both, Bool.false_eq_true, ite_true, ite_false] at IH
          simp [nock_exec, hl1, hne, a1, cap_arm, cap.arm_at, hcap, mas_arm, mas.arm_at, hmas, ← capF_eq_cap, ← masF_eq_mas, NeedOrd.toNoun, Tag.none, Tag.this, Tag.both, listNoun, lziTackE, loob, eqCode_atom, eqCode, lmu_at', lmu_arm, lmu_gate, IH, hc3]
        | pair p q =>
          obtain ⟨u, v, hp⟩ := no_cell p
          have IH := ihm q ((false, p) :: tack)
          simp only [listNoun, lziTackE, NeedOrd.toNoun, loob, Tag.none, Tag.this, Tag.both, Bool.false_eq_true, ite_true, ite_false, hp] at IH
          simp [nock_exec, hl1, hne, a1, cap_arm, cap.arm_at, hcap, mas_arm, mas.arm_at, hmas, ← capF_eq_cap, ← masF_eq_mas, NeedOrd.toNoun, Tag.none, Tag.this, Tag.both, listNoun, lziTackE, loob, eqCode_atom, eqCode, lmu_at', lmu_arm, lmu_gate, IH, hc3, hp]
        | both l r =>
          have IH := ihm (lazeMust r) ((false, lazeMust l) :: tack)
          simp only [listNoun, lziTackE, NeedOrd.toNoun, loob, Tag.none, Tag.this, Tag.both, Bool.false_eq_true, ite_true, ite_false] at IH
          generalize comp.door = Dr at hm IH ⊢
          simp [nock_exec, hl1, hne, a1, cap_arm, cap.arm_at, hcap, mas_arm, mas.arm_at, hmas, ← capF_eq_cap, ← masF_eq_mas, NeedOrd.toNoun, Tag.none, Tag.this, Tag.both, listNoun, lziTackE, loob, eqCode_atom, eqCode, lmu_at', lmu_arm, lmu_gate, IH, hc3, hm]


/-- **The needs** (`lziNed`): `intoNed`, on the subject `[lok gate]`. -/
theorem lzi_ned (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) (G LOK FB : Noun) (axe : Nat)
    (ha : 1 ≤ axe) (ned : NeedOrd) (LK : Noun) :
    nock (C LOK (C lziGate (C (C (A axe) (C (C ned.toNoun LK) FB)) (C comp.door (C G ctx))))) lziNed
      = (intoNed axe ned).map fun p => C p.1.toNoun p.2.toNoun := by
  unfold lziNed
  by_cases a1 : axe = 1
  · subst a1; simp [nock_exec, intoNed, NeedOrd.toNoun, Tag.none]
  · have a1' : ¬ (1 = axe) := fun h => a1 h.symm
    have hlp := lzi_trap hc h7 LOK (C (C ned.toNoun LK) FB) G axe ha ned []
    simp only [listNoun] at hlp
    simp [nock_exec, intoNed, a1, a1', hlp]

/-! ## The turns and the prunes -/

/-- The fork gate of `+laze-into`, in the model. -/
noncomputable def liF (axe : Nat) (e : (Nat × Laze CSet) × (Nat × Laze CSet)) :
    Option (((Nat × Laze CSet) × (Nat × Laze CSet)) × ((Nat × Laze CSet) × (Nat × Laze CSet))) :=
  (lazeInto axe e.1.2).bind fun yy => (lazeInto axe e.2.2).map fun nn =>
    (((e.1.1, yy.1), (e.2.1, nn.1)), ((e.1.1, yy.2), (e.2.1, nn.2)))

/-- The bond gate of `+laze-into`, in the model. -/
noncomputable def liB (axe : Nat) (e : Nat × Laze CSet) : Option ((Nat × Laze CSet) × (Nat × Laze CSet)) :=
  (lazeInto axe e.2).map fun bb => ((e.1, bb.1), (e.1, bb.2))

theorem intoF_mapM (axe : Nat) : ∀ fk : List ((Nat × Laze CSet) × (Nat × Laze CSet)),
    intoF axe fk = fk.mapM (liF axe)
  | [] => rfl
  | ((oy, y), (on, n)) :: rest => by
    simp only [intoF, List.mapM_cons, liF, intoF_mapM axe rest]
    cases lazeInto axe y <;> cases lazeInto axe n <;> cases rest.mapM (liF axe) <;> rfl

theorem intoB_mapM (axe : Nat) : ∀ bd : List (Nat × Laze CSet), intoB axe bd = bd.mapM (liB axe)
  | [] => rfl
  | (ob, l) :: rest => by
    simp only [intoB, List.mapM_cons, liB, intoB_mapM axe rest]
    cases lazeInto axe l <;> cases rest.mapM (liB axe) <;> rfl

/-- **The two `+laze-prune`** (`lziPr`, the same noun as `lspPr`). -/
theorem lzi_pr (hc : CompIn ctx) (G L : Noun) (nh nt : NeedOrd) (lh lt : CSet)
    (fs : List (((Nat × Laze CSet) × (Nat × Laze CSet)) × ((Nat × Laze CSet) × (Nat × Laze CSet))))
    (bs : List ((Nat × Laze CSet) × (Nat × Laze CSet))) :
    nock (C (listN (bs.map lzb2N)) (C (listN (fs.map lzf2N)) (C (C nh.toNoun nt.toNoun)
      (C (C (HoonSet.toNoun lh) (HoonSet.toNoun lt)) (C lziGate (C L (C comp.door (C G ctx)))))))) lziPr
      = some (lzpN (lazePrune (Laze.mk ⟨nh, lh⟩ (fs.map Prod.fst) (bs.map Prod.fst)),
          lazePrune (Laze.mk ⟨nt, lt⟩ (fs.map Prod.snd) (bs.map Prod.snd)))) := by
  have hF1 := turn_head lzfE lzfE fs
  have hF2 := turn_tail lzfE lzfE fs
  have hB1 := turn_head lzbE lzbE bs
  have hB2 := turn_tail lzbE lzbE bs
  have hP1 := lpr_mk hc ⟨nh, lh⟩ (fs.map Prod.fst) (bs.map Prod.fst) G
  have hP2 := lpr_mk hc ⟨nt, lt⟩ (fs.map Prod.snd) (bs.map Prod.snd) G
  have hlp := lpr_at
  have e1 : (fs.map lzf2N) = fs.map fun x => C (lzfE x.1) (lzfE x.2) := rfl
  have e2 : (bs.map lzb2N) = bs.map fun x => C (lzbE x.1) (lzbE x.2) := rfl
  rw [e1, e2]
  simp only [SureO.toNoun] at hP1 hP2
  generalize comp.door = Dr at hP1 hP2 hlp ⊢
  generalize (fs.map fun x => C (lzfE x.1) (lzfE x.2)) = FN at hF1 hF2 ⊢
  generalize (bs.map fun x => C (lzbE x.1) (lzbE x.2)) = BN at hB1 hB2 ⊢
  generalize ((fs.map Prod.fst).map lzfE) = F1 at hF1 hP1
  generalize ((fs.map Prod.snd).map lzfE) = F2 at hF2 hP2
  generalize ((bs.map Prod.fst).map lzbE) = B1 at hB1 hP1
  generalize ((bs.map Prod.snd).map lzbE) = B2 at hB2 hP2
  unfold lziPr
  simp [nock_exec, lzpN, hc, turn.arm_at, turn_arm, head_at, head_arm, tail_at, tail_arm, hF1, hF2,
    hB1, hB2, hlp, lpr_arm, hP1, hP2, buntGate]

/-- **The turns over the forks and the bonds, then the prunes** (`lziR`), given the gates. -/
theorem lzi_r (hc : CompIn ctx) (G SN : Noun) (axe : Nat) (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet)))
    (bd : List (Nat × Laze CSet)) (nh nt : NeedOrd) (lh lt : CSet)
    (hF : ∀ e ∈ fk, ∀ NP LP L : Noun,
      nock (C lziGF (C (lzfE e) (C NP (C LP (C lziGate (C (C (A axe) L) (C comp.door (C G ctx)))))))) lziGF
        = (liF axe e).map lzf2N)
    (hB : ∀ e ∈ bd, ∀ FS NP LP L : Noun,
      nock (C lziGB (C (lzbE e) (C FS (C NP (C LP (C lziGate (C (C (A axe) L) (C comp.door (C G ctx))))))))) lziGB
        = (liB axe e).map lzb2N) :
    nock (C (C nh.toNoun nt.toNoun) (C (C (HoonSet.toNoun lh) (HoonSet.toNoun lt)) (C lziGate
      (C (C (A axe) (C SN (C (listN (fk.map lzfE)) (listN (bd.map lzbE))))) (C comp.door (C G ctx)))))) lziR
      = (fk.mapM (liF axe)).bind fun fs => (bd.mapM (liB axe)).map fun bs =>
          lzpN (lazePrune (Laze.mk ⟨nh, lh⟩ (fs.map Prod.fst) (bs.map Prod.fst)),
            lazePrune (Laze.mk ⟨nt, lt⟩ (fs.map Prod.snd) (bs.map Prod.snd))) := by
  have hFk := turn_gate_mapT lzfE lzf2N layer2 homoIn_layer2 lziGF (C lziBunt lziBunt)
    (C (C nh.toNoun nt.toNoun) (C (C (HoonSet.toNoun lh) (HoonSet.toNoun lt)) (C lziGate
      (C (C (A axe) (C SN (C (listN (fk.map lzfE)) (listN (bd.map lzbE))))) (C comp.door (C G ctx))))))
    (liF axe) fk (fun e he => hF e he _ _ _)
  cases e1 : fk.mapM (liF axe) with
  | none =>
    rw [e1] at hFk
    unfold lziR
    simp [nock_exec, hc, turn.arm_at, turn_arm, hFk, buntGate]
  | some fs =>
    rw [e1] at hFk
    have hBd := turn_gate_mapT lzbE lzb2N layer2 homoIn_layer2 lziGB lziBunt
      (C (listN (fs.map lzf2N)) (C (C nh.toNoun nt.toNoun) (C (C (HoonSet.toNoun lh) (HoonSet.toNoun lt))
        (C lziGate (C (C (A axe) (C SN (C (listN (fk.map lzfE)) (listN (bd.map lzbE))))) (C comp.door (C G ctx)))))))
      (liB axe) bd (fun e he => hB e he _ _ _ _)
    cases e2 : bd.mapM (liB axe) with
    | none =>
      rw [e2] at hBd
      unfold lziR
      simp [nock_exec, hc, turn.arm_at, turn_arm, hFk, hBd, buntGate]
    | some bs =>
      rw [e2] at hBd
      have hP := lzi_pr hc G (C (A axe) (C SN (C (listN (fk.map lzfE)) (listN (bd.map lzbE))))) nh nt lh lt fs bs
      generalize comp.door = Dr at hP hFk hBd ⊢
      unfold lziR
      simp [nock_exec, hc, turn.arm_at, turn_arm, hFk, hBd, buntGate, hP]

/-! ## `+laze-into` on every `laze` -/

/-- The looks of `+laze-into`, on looks that are not `0`. -/
noncomputable def lziF (axe : Nat) (lok : CSet) : CSet × CSet :=
  lziFinS axe ((HoonSet.toList lok).foldl (fun s y => isStep axe y s) (HoonSet.empty, HoonSet.empty))

/-- `lazeInto` on a `laze` written out, its turns as `mapM`, for `axe` not `0` and looks not `0`. -/
theorem lazeInto_eq (axe : Nat) (ha : axe ≠ 0) (s : SureO CSet) (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet)))
    (bd : List (Nat × Laze CSet)) (h0 : ∀ y ∈ HoonSet.toList s.lok, y ≠ 0) :
    lazeInto axe (Laze.mk s fk bd) = (intoNed axe s.ned).bind fun nn =>
      if fk.isEmpty && bd.isEmpty then
        some (Laze.mk ⟨nn.1, (lziF axe s.lok).1⟩ [] [], Laze.mk ⟨nn.2, (lziF axe s.lok).2⟩ [] [])
      else (fk.mapM (liF axe)).bind fun fs => (bd.mapM (liB axe)).map fun bs =>
        (lazePrune (Laze.mk ⟨nn.1, (lziF axe s.lok).1⟩ (fs.map Prod.fst) (bs.map Prod.fst)),
         lazePrune (Laze.mk ⟨nn.2, (lziF axe s.lok).2⟩ (fs.map Prod.snd) (bs.map Prod.snd))) := by
  rw [lazeInto, if_neg ha, intoLokS_eq axe ha s.lok h0, intoF_mapM, intoB_mapM]
  rfl

section
variable (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) (G : Noun) (axe : Nat)
include hc h7

mutual
/-- **`+laze-into` on every `laze`** (forks and bonds to any depth) whose sure needs look at
no axis `0`: `lazeInto axe`, on every axis and every noun `G` of `gen`. -/
theorem lzi_allN : ∀ (laz : Laze CSet), LzNZ laz →
    nock (C lziGate (C (C (A axe) laz.toNoun) (C comp.door (C G ctx)))) lziGate = (lazeInto axe laz).map lzpN
  | Laze.mk s fk bd, ⟨hs, hfk, hbd⟩ => by
    rw [lz_toNoun_mk]
    by_cases a0 : axe = 0
    · subst a0
      conv => { lhs; arg 2; unfold lziGate }
      simp [nock_exec, lazeInto]
    have a0' : ¬ (0 = axe) := fun h => a0 h.symm
    rw [lazeInto_eq axe a0 s fk bd hs]
    have hl := lzi_lok hc h7 G axe a0 s (C (listN (fk.map lzfE)) (listN (bd.map lzbE))) hs
    have hlF : lziF axe s.lok = lziFinS axe ((HoonSet.toList s.lok).foldl (fun s y => isStep axe y s)
      (HoonSet.empty, HoonSet.empty)) := rfl
    rw [← hlF] at hl
    generalize lziF axe s.lok = F at hl ⊢
    obtain ⟨lh, lt⟩ := F
    have hn := lzi_ned hc h7 G (ssN (lh, lt)) (C (listN (fk.map lzfE)) (listN (bd.map lzbE))) axe
      (Nat.pos_of_ne_zero a0) s.ned (HoonSet.toNoun s.lok)
    have tF := lz_test lzfE fk
    have tB := lz_test lzbE bd
    simp only [ssN] at hl hn
    obtain ⟨ned, lok⟩ := s
    simp only [SureO.toNoun] at hl hn ⊢
    cases en : intoNed axe ned with
    | none =>
      rw [en] at hn
      conv => { lhs; arg 2; unfold lziGate }
      simp [nock_exec, hl, hn, eqCode_atom, a0']
    | some nn =>
      obtain ⟨nh, nt⟩ := nn
      rw [en] at hn
      have hr := lzi_r hc G (C ned.toNoun (HoonSet.toNoun lok)) axe fk bd nh nt lh lt
        (fun e he NP LP L => lzi_forks fk hfk e he NP LP L)
        (fun e he FS NP LP L => lzi_bonds bd hbd e he FS NP LP L)
      have hif : (fk.isEmpty && bd.isEmpty) = decide (fk = [] ∧ bd = []) := by cases fk <;> cases bd <;> rfl
      simp only [Option.bind_some]
      rw [hif]
      generalize hFN : listN (fk.map lzfE) = FN at hl hn hr tF ⊢
      generalize hBN : listN (bd.map lzbE) = BN at hl hn hr tB ⊢
      conv => { lhs; arg 2; unfold lziGate }
      by_cases hb : fk = [] ∧ bd = []
      · obtain ⟨rfl, rfl⟩ := hb
        have e0 : listN ([] : List Noun) = A 0 := rfl
        simp only [List.map_nil, e0] at hFN hBN
        subst hFN; subst hBN
        simp [nock_exec, hl, hn, eqCode_atom, a0', lziTest, lziLeaf, lzpN, lz_toNoun_mk, SureO.toNoun, listN]
      · rw [if_neg (by simpa using hb)]
        have tt : (eqCode (A 0) FN = A 0 ∧ (A 0 = FN) = True ∧ eqCode (A 0) BN = A 1 ∧ (A 0 = BN) = False) ∨
            (eqCode (A 0) FN = A 1 ∧ (A 0 = FN) = False) := by
          rcases tF with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
          · rcases tB with ⟨h4, h5, h6⟩ | ⟨h4, h5, h6⟩
            · exact absurd ⟨h1, h4⟩ hb
            · exact Or.inl ⟨h2, h3, h5, h6⟩
          · exact Or.inr ⟨h2, h3⟩
        rcases tt with ⟨t2, t3, t5, t6⟩ | ⟨t2, t3⟩
        · simp [nock_exec, hl, hn, eqCode_atom, a0', lziTest, t2, t3, t5, t6, hr]
          cases fk.mapM (liF axe) <;> cases bd.mapM (liB axe) <;> simp [lzpN]
        · simp [nock_exec, hl, hn, eqCode_atom, a0', lziTest, t2, t3, hr]
          cases fk.mapM (liF axe) <;> cases bd.mapM (liB axe) <;> simp [lzpN]

theorem lzi_forks : ∀ (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet))), LzNZF fk → ∀ e ∈ fk,
    ∀ NP LP L : Noun,
    nock (C lziGF (C (lzfE e) (C NP (C LP (C lziGate (C (C (A axe) L) (C comp.door (C G ctx)))))))) lziGF
      = (liF axe e).map lzf2N
  | [], _, e, he => absurd he List.not_mem_nil
  | ((oy, y), (on, n)) :: rest, ⟨hy, hn, hr⟩, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro NP LP L
      have ihy := lzi_allN y hy
      have ihn := lzi_allN n hn
      unfold lziGF
      cases e1 : lazeInto axe y with
      | none => rw [e1] at ihy; simp [nock_exec, lzfE, ihy, liF, e1, lzi_at, lzi_at', lzi_arm]
      | some yy =>
        rw [e1] at ihy
        cases e2 : lazeInto axe n with
        | none => rw [e2] at ihn; simp [nock_exec, lzfE, ihy, ihn, liF, e1, e2, lzi_at, lzi_at', lzi_arm]
        | some nn =>
          rw [e2] at ihn
          simp [nock_exec, lzfE, ihy, ihn, liF, e1, e2, lzi_at, lzi_at', lzi_arm, lzpN, lzf2N]
    · exact lzi_forks rest hr e he'

theorem lzi_bonds : ∀ (bd : List (Nat × Laze CSet)), LzNZB bd → ∀ e ∈ bd, ∀ FS NP LP L : Noun,
    nock (C lziGB (C (lzbE e) (C FS (C NP (C LP (C lziGate (C (C (A axe) L) (C comp.door (C G ctx))))))))) lziGB
      = (liB axe e).map lzb2N
  | [], _, e, he => absurd he List.not_mem_nil
  | (ob, l) :: rest, ⟨hl, hr⟩, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro FS NP LP L
      have ihl := lzi_allN l hl
      unfold lziGB
      cases e1 : lazeInto axe l with
      | none => rw [e1] at ihl; simp [nock_exec, lzbE, ihl, liB, e1, lzi_at, lzi_at', lzi_arm]
      | some bb => rw [e1] at ihl; simp [nock_exec, lzbE, ihl, liB, e1, lzi_at, lzi_at', lzi_arm, lzpN, lzb2N]
    · exact lzi_bonds rest hr e he'
end

end

/-- **`+laze-into` is `lazeInto`** on every axis and every `laze` whose sure needs look at no
axis `0` (`LzNZ`), on every noun `G` of `gen`, under `CompIn ctx` and `K` at axis `7` of `ctx`. -/
theorem lzi_all (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) (G : Noun) (axe : Nat) :
    ∀ (laz : Laze CSet), LzNZ laz →
    nock (C lziGate (C (C (A axe) laz.toNoun) (C comp.door (C G ctx)))) lziGate
      = (lazeInto axe laz).map fun p => C p.1.toNoun p.2.toNoun :=
  lzi_allN hc h7 G axe

/-! ## What `+laze-into` returns (the model) -/

/-- The fold of the looks keeps them positive: a remainder of `+gep` is at least `1`. -/
theorem isFold_nz (axe : Nat) : ∀ (l : List Nat) (acc : CSet × CSet), (∀ y ∈ l, y ≠ 0) →
    (∀ y ∈ HoonSet.toList acc.1, y ≠ 0) → (∀ y ∈ HoonSet.toList acc.2, y ≠ 0) →
    (∀ y ∈ HoonSet.toList (l.foldl (fun s y => isStep axe y s) acc).1, y ≠ 0) ∧
      (∀ y ∈ HoonSet.toList (l.foldl (fun s y => isStep axe y s) acc).2, y ≠ 0)
  | [], acc, _, h1, h2 => ⟨h1, h2⟩
  | a :: l, acc, hl, h1, h2 => by
    rw [List.foldl_cons]
    have ha : a ≠ 0 := hl a List.mem_cons_self
    refine isFold_nz axe l _ (fun y hy => hl y (List.mem_cons_of_mem _ hy)) ?_ ?_ <;>
    · unfold isStep
      cases e : gep axe a with
      | none =>
        simp only
        first
        | exact h1
        | intro y hy; rcases (HoonSet.mem_put _ _ _).1 hy with rfl | hy; exact ha; exact h2 y hy
      | some u =>
        cases u with
        | none =>
          simp only
          first
          | exact h1
          | intro y hy; rcases (HoonSet.mem_put _ _ _).1 hy with rfl | hy; exact ha; exact h2 y hy
        | some r =>
          have hr : r ≠ 0 := by have := (gep_some e).2.1; omega
          simp only
          by_cases r1 : r = 1
          · simp only [r1, if_true]; first | exact h1 | exact h2
          · simp only [r1, if_false]
            first
            | exact h2
            | intro y hy; rcases (HoonSet.mem_put _ _ _).1 hy with rfl | hy; exact hr; exact h1 y hy

theorem lziF_nz (axe : Nat) (ha : axe ≠ 0) (lok : CSet) (h0 : ∀ y ∈ HoonSet.toList lok, y ≠ 0) :
    (∀ y ∈ HoonSet.toList (lziF axe lok).1, y ≠ 0) ∧ (∀ y ∈ HoonSet.toList (lziF axe lok).2, y ≠ 0) := by
  obtain ⟨n1, n2⟩ := isFold_nz axe (HoonSet.toList lok) (HoonSet.empty, HoonSet.empty) h0
    (fun y hy => absurd hy (HoonSet.mem_empty y)) (fun y hy => absurd hy (HoonSet.mem_empty y))
  refine ⟨n1, ?_⟩
  unfold lziF lziFinS
  by_cases a1 : axe = 1
  · subst a1; simp only [if_true]; exact n2
  · simp only [a1, if_false]
    intro y hy
    rcases (HoonSet.mem_put _ _ _).1 hy with rfl | hy
    · exact ha
    · exact n2 y hy

mutual
/-- **What `+laze-into` returns looks at no axis `0`** when its `laze` does not. -/
theorem lazeInto_nz (axe : Nat) : ∀ (l : Laze CSet), LzNZ l → ∀ d r, lazeInto axe l = some (d, r) → LzNZ d ∧ LzNZ r
  | Laze.mk s fk bd, ⟨hs, hfk, hbd⟩, d, r, e => by
    by_cases a0 : axe = 0
    · subst a0; simp [lazeInto] at e
    rw [lazeInto_eq axe a0 s fk bd hs] at e
    obtain ⟨n1, n2⟩ := lziF_nz axe a0 s.lok hs
    cases en : intoNed axe s.ned with
    | none => simp [en] at e
    | some nn =>
      simp only [en, Option.bind_some] at e
      split at e
      · simp only [Option.some.injEq, Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        exact ⟨⟨n1, trivial, trivial⟩, ⟨n2, trivial, trivial⟩⟩
      · cases e3 : fk.mapM (liF axe) with
        | none => simp [e3] at e
        | some fs =>
          cases e4 : bd.mapM (liB axe) with
          | none => simp [e3, e4] at e
          | some bs =>
            simp only [e3, e4, Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
            obtain ⟨rfl, rfl⟩ := e
            obtain ⟨hf1, hf2⟩ := liF_nz axe fk hfk fs e3
            obtain ⟨hb1, hb2⟩ := liB_nz axe bd hbd bs e4
            exact ⟨lazePrune_nz _ ⟨n1, hf1, hb1⟩, lazePrune_nz _ ⟨n2, hf2, hb2⟩⟩

theorem liF_nz (axe : Nat) : ∀ (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet))), LzNZF fk →
    ∀ fs, fk.mapM (liF axe) = some fs → LzNZF (fs.map Prod.fst) ∧ LzNZF (fs.map Prod.snd)
  | [], _, fs, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; exact ⟨trivial, trivial⟩
  | ((oy, y), (on, n)) :: rest, ⟨hy, hn, hr⟩, fs, h => by
    simp only [List.mapM_cons] at h
    cases e1 : lazeInto axe y with
    | none => simp [liF, e1] at h
    | some yy =>
      obtain ⟨yb, yr⟩ := yy
      cases e2 : lazeInto axe n with
      | none => simp [liF, e1, e2] at h
      | some nn =>
        obtain ⟨nb, nr⟩ := nn
        cases e3 : rest.mapM (liF axe) with
        | none => simp [liF, e1, e2, e3] at h
        | some rs =>
          simp [liF, e1, e2, e3] at h
          subst h
          obtain ⟨y1, y2⟩ := lazeInto_nz axe y hy yb yr e1
          obtain ⟨n1, n2⟩ := lazeInto_nz axe n hn nb nr e2
          obtain ⟨r1, r2⟩ := liF_nz axe rest hr rs e3
          exact ⟨⟨y1, n1, r1⟩, ⟨y2, n2, r2⟩⟩

theorem liB_nz (axe : Nat) : ∀ (bd : List (Nat × Laze CSet)), LzNZB bd →
    ∀ bs, bd.mapM (liB axe) = some bs → LzNZB (bs.map Prod.fst) ∧ LzNZB (bs.map Prod.snd)
  | [], _, bs, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; exact ⟨trivial, trivial⟩
  | (ob, l) :: rest, ⟨hl, hr⟩, bs, h => by
    simp only [List.mapM_cons] at h
    cases e1 : lazeInto axe l with
    | none => simp [liB, e1] at h
    | some bb =>
      obtain ⟨lb, lr⟩ := bb
      cases e3 : rest.mapM (liB axe) with
      | none => simp [liB, e1, e3] at h
      | some rs =>
        simp [liB, e1, e3] at h
        subst h
        obtain ⟨l1, l2⟩ := lazeInto_nz axe l hl lb lr e1
        obtain ⟨r1, r2⟩ := liB_nz axe rest hr rs e3
        exact ⟨⟨l1, r1⟩, ⟨l2, r2⟩⟩
end

end Compiler
end Formalization
