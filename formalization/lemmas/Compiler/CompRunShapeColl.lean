import lemmas.Compiler.CompRunShapeCollCut
import lemmas.Compiler.CompShapeColL2i
import lemmas.Compiler.CompRunShapeFrom
import lemmas.Compiler.CompSccLoopMemShape

/-!
# `+laze-to-inter1` and `+laze-collapse` (README Gaps 26, track A)

`lzt_gate`: the gate body of `+laze-to-inter1` (arm `5598` of `K`, `lztBody` of
`CompRunShapeCollCut.lean`) on `[laz K]` is `lazeToI1 laz` (`Ska/RunShape.lean`) for every
`laze` over `CSet`, forks and bonds to any depth.  The proof is the one of `l2i_gate`
(`CompShapeColL2i.lean`) without `+need-to-ordered`: the `+turn` over `fork.laz` (gate
`lztTG`, `lzt_fgate`, `lzt_forks`), the `+roll` over `bond.laz` (gate `lztBG`, `lzt_bstep`,
`lzt_bonds`) from `[sure.laz fork-new]`; the three are one `mutual` block over `Laze`.

`lco_gate`: `+laze-collapse` (arm `0x15d7a`) on `[laz less]` is `lazeCollapse fuel laz less`
whenever the model returns at some fuel (as `sc_gate`: `lzt_gate`, `i12_gate`, `ic_gate`);
`lco_gate_none`: it crashes when `+inter1-to-inter2` does in the model.  `lco_call`,
`lco_call_none`: the formula `msMust` of `member` (`CompSccLoopMemShape.lean`), on a subject
`S` with `K` at axis `8191`, the `laze` at axis `2` and the cape at axis `2032` (the formula's
`[0 6]` and `[0 4080]` are read after the push of the gate).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The bunt of `laze` -/

/-- The bunt of `laze` computed from `K`: the mold at arm `0xaebde` of `K`, slammed on its own
sample. -/
def lztLzbF : Noun := C (A 7) (C (C (A 9) (C (A 0xaebde) (C (A 0) (A 1)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))

noncomputable def lztLzbV : Noun := (evalFuel 2000 compK lztLzbF).getD (A 0)

theorem lzt_lzb : nock compK lztLzbF = some lztLzbV := nock_of_evalFuel (fuel := 2000) (by kernel_rfl)

/-- `lztLzb` on a subject whose axis `15` is `K`. -/
theorem lzt_lzb_at (T : Noun) (h : slot? 15 T = some compK) : nock T lztLzb = some lztLzbV := by
  have hb := lzt_lzb
  unfold lztLzbF at hb
  unfold lztLzb
  simp only [nock_op7, nock_op9, nock_op0, h, slot?_one, Option.bind_some] at hb ⊢
  exact hb

/-! ## The gates -/

/-- **The gate of the `+turn`** on a fork entry: `+laze-to-inter1` again on both branches. -/
theorem lzt_fgate (LAZ : Noun) (oy on : Nat) (y n : Laze CSet)
    (hy : nock (C lztBody (C y.toNoun compK)) lztBody = some (I1.toNounC (lazeToI1 y)))
    (hn : nock (C lztBody (C n.toNoun compK)) lztBody = some (I1.toNounC (lazeToI1 n))) :
    nock (C lztTG (C (lzfE ((oy, y), (on, n))) (C lztBody (C LAZ compK)))) lztTG
      = some (I1.forkN (lazeToI1 y, lazeToI1 n)) := by
  unfold lztTG lzfE I1.forkN
  generalize lztBody = B at hy hn ⊢
  generalize compK = KC at hy hn ⊢
  simp [nock_exec, hy, hn]

/-- **The gate of the `+roll`** on a bond and the accumulator `[sur fork]`. -/
theorem lzt_bstep (FN LAZ : Noun) (o : Nat) (i : Laze CSet) (ned : NeedOrd) (lok : CSet)
    (fk : List (I1 CSet × I1 CSet))
    (hi : nock (C lztBody (C i.toNoun compK)) lztBody = some (I1.toNounC (lazeToI1 i))) :
    nock (C lztBG (C (C (lzbE (o, i)) (I1.toNounC (I1.mk ned lok fk))) (C FN (C lztBody (C LAZ compK))))) lztBG
      = some (I1.toNounC (I1.mk (uniOrd (lazeToI1 i).ned ned) (HoonSet.uni lok (lazeToI1 i).lok)
          ((lazeToI1 i).fork ++ fk))) := by
  generalize lazeToI1 i = J at hi ⊢
  obtain ⟨n', l', f'⟩ := J
  have hu := uno_gate compK compK_cn n' ned
  have hua := uno_at
  have hL := compK_layer2
  have huni := cs_uni_is lok l'
  have hw := weld_gate_list layer2 (f'.map I1.forkN) (fk.map I1.forkN)
  simp only [I1.toNounC_mk, I1.forksNounC_eq, I1.ned, I1.lok, I1.fork, List.map_append] at hi hw ⊢
  unfold lztBG lzbE
  generalize lztBody = B at hi ⊢
  generalize compK = KC at hu hua hL hi ⊢
  simp [nock_exec, hi, hua, uno_arm, hu, hL, in_arm, in.arm_at, in.uni.arm_at, cl_uni_arm, huni,
    weld_arm, weld.arm_at, hw]

/-- **The branch with a fork or a bond**, given the `+turn` and the `+roll`. -/
theorem lzt_no (s : SureO CSet) (f : List ((Nat × Laze CSet) × (Nat × Laze CSet))) (b : List (Nat × Laze CSet))
    (hf : (f.map lzfE).mapM (fun x => nock (C lztTG (C x (C lztBody (C (Laze.mk s f b).toNoun compK)))) lztTG)
      = some ((lazeToI1F f).map I1.forkN))
    (hb : (b.map lzbE).foldlM (fun acc x => nock (C lztBG (C (C x acc)
        (C (listN ((lazeToI1F f).map I1.forkN)) (C lztBody (C (Laze.mk s f b).toNoun compK))))) lztBG)
        (I1.toNounC (I1.mk s.ned s.lok (lazeToI1F f)))
      = some (I1.toNounC (lazeToI1B b s.ned s.lok (lazeToI1F f)))) :
    nock (C lztBody (C (Laze.mk s f b).toNoun compK)) lztNo
      = some (I1.toNounC (lazeToI1B b s.ned s.lok (lazeToI1F f))) := by
  have hL := compK_layer2
  have ht := turn_gate_mapM layer2 homoIn_layer2 lztTG lztTB (C lztBody (C (Laze.mk s f b).toNoun compK))
    (fun x => nock (C lztTG (C x (C lztBody (C (Laze.mk s f b).toNoun compK)))) lztTG)
    (f.map lzfE) (fun _ _ => rfl)
  rw [hf] at ht
  have hr := roll_gate_M layer2 lztBG (C (A 0) lztLzbV)
    (I1.toNounC (I1.mk s.ned s.lok (lazeToI1F f)))
    (C (listN ((lazeToI1F f).map I1.forkN)) (C lztBody (C (Laze.mk s f b).toNoun compK)))
    (fun x acc => nock (C lztBG (C (C x acc)
        (C (listN ((lazeToI1F f).map I1.forkN)) (C lztBody (C (Laze.mk s f b).toNoun compK))))) lztBG)
    (b.map lzbE) (fun _ _ _ => rfl)
  rw [hb] at hr
  have hz := lzt_lzb_at (C (listN ((lazeToI1F f).map I1.forkN)) (C lztBody (C (Laze.mk s f b).toNoun compK))) rfl
  simp only [I1.toNounC_mk, I1.forksNounC_eq] at hr
  unfold lztNo lztTurn
  simp only [lz_toNoun_mk, SureO.toNoun] at ht hr hz ⊢
  generalize lztBody = B at ht hr hz ⊢
  generalize compK = KC at hL ht hr hz ⊢
  simp [nock_exec, hL, turn.arm_at, turn_arm, ht, roll.arm_at, roll_arm, hr, hz]

/-- The first test of `+laze-to-inter1`: with a fork or a bond, the branch `lztNo`. -/
theorem lzt_body_no (LAZ KC : Noun) (h : ∃ SURE FK BD, LAZ = C SURE (C FK BD) ∧
    ((∃ u v, FK = C u v) ∨ (FK = A 0 ∧ ∃ u v, BD = C u v))) :
    nock (C lztBody (C LAZ KC)) lztBody = nock (C lztBody (C LAZ KC)) lztNo := by
  obtain ⟨SURE, FK, BD, rfl, h⟩ := h
  conv => { lhs; arg 2; unfold lztBody }
  generalize lztNo = NO
  generalize lztBody = B
  rcases h with ⟨u, v, rfl⟩ | ⟨rfl, u, v, rfl⟩ <;> simp [nock_exec]

/-- With no fork and no bond, `[sure.laz ~]`. -/
theorem lzt_body_sure (s : SureO CSet) :
    nock (C lztBody (C (Laze.mk s [] []).toNoun compK)) lztBody = some (C s.toNoun (A 0)) := by
  simp only [lz_toNoun_mk, List.map_nil, listN]
  conv => { lhs; arg 2; unfold lztBody }
  generalize lztNo = NO
  generalize lztBody = B
  generalize compK = KC
  simp [nock_exec]

mutual
/-- **`+laze-to-inter1`** on every `laze` over `CSet`: `lazeToI1`. -/
theorem lzt_gate : ∀ laz : Laze CSet,
    nock (C lztBody (C laz.toNoun compK)) lztBody = some (I1.toNounC (lazeToI1 laz))
  | Laze.mk s f b => by
    have hf := lzt_forks (Laze.mk s f b).toNoun f
    have hb := lzt_bonds (listN ((lazeToI1F f).map I1.forkN)) (Laze.mk s f b).toNoun b s.ned s.lok (lazeToI1F f)
    have hno := lzt_no s f b hf hb
    rcases f with _ | ⟨⟨⟨oy, y⟩, ⟨on, n⟩⟩, r⟩
    · rcases b with _ | ⟨⟨o, l⟩, r'⟩
      · rw [lzt_body_sure s]
        simp [lazeToI1, lazeToI1B, lazeToI1F, I1.toNounC_mk, I1.forksNounC, SureO.toNoun]
      · rw [lzt_body_no (Laze.mk s [] ((o, l) :: r')).toNoun compK
          ⟨_, _, _, by simp only [lz_toNoun_mk]; rfl, Or.inr ⟨by simp only [List.map_nil]; rfl, _, _, rfl⟩⟩, lazeToI1]
        exact hno
    · rw [lzt_body_no (Laze.mk s (((oy, y), on, n) :: r) b).toNoun compK
        ⟨_, _, _, by simp only [lz_toNoun_mk]; rfl, Or.inl ⟨_, _, rfl⟩⟩, lazeToI1]
      exact hno

/-- The gate of the `+turn` over the forks, on every fork list. -/
theorem lzt_forks (LAZ : Noun) : ∀ f : List ((Nat × Laze CSet) × (Nat × Laze CSet)),
    (f.map lzfE).mapM (fun x => nock (C lztTG (C x (C lztBody (C LAZ compK)))) lztTG)
      = some ((lazeToI1F f).map I1.forkN)
  | [] => rfl
  | ((oy, y), (on, n)) :: r => by
    have hg := lzt_fgate LAZ oy on y n (lzt_gate y) (lzt_gate n)
    have hr := lzt_forks LAZ r
    simp only [List.map_cons, List.mapM_cons, hg, hr, lazeToI1F]
    rfl

/-- The `+roll` over the bonds, on every bond list and accumulator. -/
theorem lzt_bonds (FN LAZ : Noun) : ∀ (b : List (Nat × Laze CSet)) (ned : NeedOrd) (lok : CSet)
    (fk : List (I1 CSet × I1 CSet)),
    (b.map lzbE).foldlM (fun acc x => nock (C lztBG (C (C x acc) (C FN (C lztBody (C LAZ compK))))) lztBG)
      (I1.toNounC (I1.mk ned lok fk)) = some (I1.toNounC (lazeToI1B b ned lok fk))
  | [], ned, lok, fk => rfl
  | (o, i) :: r, ned, lok, fk => by
    have hs := lzt_bstep FN LAZ o i ned lok fk (lzt_gate i)
    have hr := lzt_bonds FN LAZ r (uniOrd (lazeToI1 i).ned ned) (HoonSet.uni lok (lazeToI1 i).lok)
      ((lazeToI1 i).fork ++ fk)
    simp only [lazeToI1B]
    rw [List.map_cons, List.foldlM_cons, hs]
    exact hr
end

/-! ## `+laze-collapse` -/

/-- **`+laze-collapse` on every `laze`** on which the model returns at some fuel: its product is
the model's. -/
theorem lco_gate (laz : Laze CSet) (less : Cape) (fuel : Nat) (r : NeedOrd)
    (h : lazeCollapse fuel laz less = some r) :
    nock (C lcoBody (C (C laz.toNoun less.toNoun) compK)) lcoBody = some r.toNoun := by
  unfold lazeCollapse at h
  cases e : i12 less (lazeToI1 laz) with
  | none => rw [e] at h; cases h
  | some intr =>
    rw [e, Option.bind_some] at h
    have hla := lzt_at
    have hl := lzt_gate laz
    have hia := i2_at
    have hi := i12_gate less (lazeToI1 laz)
    rw [e, Option.map_some] at hi
    have hca := ic_at
    have hc := ic_gate less intr fuel r h
    unfold lcoBody
    generalize I1.toNounC (lazeToI1 laz) = L at hl hi
    generalize compK = KC at hla hl hia hi hca hc ⊢
    simp [nock_exec, hla, lzt_arm, hl, hia, i2_arm, hi, hca, ic_arm, hc]

/-- **`+laze-collapse` crashes** when `+inter1-to-inter2` does in the model. -/
theorem lco_gate_none (laz : Laze CSet) (less : Cape) (e : i12 less (lazeToI1 laz) = Option.none) :
    nock (C lcoBody (C (C laz.toNoun less.toNoun) compK)) lcoBody = Option.none := by
  have hla := lzt_at
  have hl := lzt_gate laz
  have hia := i2_at
  have hi := i12_gate less (lazeToI1 laz)
  rw [e] at hi
  unfold lcoBody
  generalize I1.toNounC (lazeToI1 laz) = L at hl hi
  generalize compK = KC at hla hl hia hi ⊢
  simp [nock_exec, hla, lzt_arm, hl, hia, i2_arm, hi]

/-- **The call `(laze-collapse l cape.less.b)` of `member`** (`msMust`): on a subject with `K` at
axis `8191`, `l` at axis `2` and the cape at axis `2032`, the model's product whenever it returns
at some fuel. -/
theorem lco_call (S : Noun) (laz : Laze CSet) (less : Cape) (fuel : Nat) (r : NeedOrd)
    (h : lazeCollapse fuel laz less = some r) (hk : slot? 8191 S = some compK)
    (hl : slot? 2 S = some laz.toNoun) (hc : slot? 2032 S = some less.toNoun) :
    nock S msMust = some r.toNoun := by
  have hg := lco_gate laz less fuel r h
  have ha := lco_at
  unfold msMust
  generalize compK = KC at hg ha hk
  simp [nock_exec, hk, ha, lco_arm, hl, hc]
  exact hg

/-- **The call crashes** when `+inter1-to-inter2` does in the model. -/
theorem lco_call_none (S : Noun) (laz : Laze CSet) (less : Cape) (e : i12 less (lazeToI1 laz) = Option.none)
    (hk : slot? 8191 S = some compK) (hl : slot? 2 S = some laz.toNoun) (hc : slot? 2032 S = some less.toNoun) :
    nock S msMust = Option.none := by
  have hg := lco_gate_none laz less e
  have ha := lco_at
  unfold msMust
  generalize compK = KC at hg ha hk
  simp [nock_exec, hk, ha, lco_arm, hl, hc]
  exact hg

end Compiler
end Formalization
