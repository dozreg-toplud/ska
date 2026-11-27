import lemmas.Compiler.CompShapeColLoop
import lemmas.Compiler.CompWalkGen

/-!
# `+lazy-to-inter1` with forks and bonds, and `+shape-collapse` in full

`l2i_gate`: the gate body of `+lazy-to-inter1` (arm `6006` of `K`, `l2iBody`
of `CompShapeCol.lean`) on `[laz K]` is `l2i laz` (`Ska/ShapeCol.lean`) for
every lazy need over `CSet`, forks and bonds to any depth.  The branch with a
fork or a bond (`l2iNo`, cut by `tools/gen/shapecoll2i.py` into `l2iNoN`) is
a `+roll` over `bond.laz` from `[[(need-to-ordered ned) lok] fork-new]`,
`fork-new` the `+turn` over `fork.laz` whose gate (`l2iTG`) recurses at axis
`15` of its subject on both branches (`l2i_fgate`, `l2i_forks`); the gate of
the roll (`l2iBG`) recurses at axis `63` on the bond's need, then makes
`[[(uni-need-ord ned.sure.i ned.sur) (~(uni in lok.sur) lok.sure.i)] (weld
fork.i fork)]` (`l2i_bstep`, by `uno_gate`, `cs_uni_is`, `weld_gate_list`;
`l2i_bonds`).  The three are one `mutual` block over `Lazy`.

`sc_gate`: `+shape-collapse` (arm `682`) on `[laz less]` is the `ord` of the
model, `shapeCol fuel laz less`, whenever the model returns at some fuel
(`l2i_gate`, `i12_gate`, `ic_gate`).  `sc_gate_none`: when `+inter1-to-inter2`
crashes in the model (a look at `0`), `+shape-collapse` crashes.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The nouns (`tools/gen/shapecoll2i.py`) -/

/-- The sample bunt of the gate of the `+turn` over `fork.laz`. -/
def l2iTB : Noun :=
  (C (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))))

/-- The gate of the `+turn` over `fork.laz`: `[(lazy-to-inter laz-y) (lazy-to-inter laz-n)]`. -/
def l2iTG : Noun :=
  (C (C (A 8) (C (C (A 0) (A 15)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 57))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 15)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2)))))))))

/-- `fork-new`: the `+turn` over `fork.laz`. -/
def l2iTurn : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x7ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 122)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) l2iTB) (C (C (A 1) l2iTG) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))

/-- The bunt of `need-lazy` in the sample of the gate of the `+roll`. -/
def l2iLzb : Noun :=
  (C (A 7) (C (C (A 9) (C (A 191) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))

/-- The gate of the `+roll` over `bond.laz`. -/
def l2iBG : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 0) (A 63)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 57))) (C (A 0) (A 2)))))))) (C (C (C (A 8) (C (C (A 9) (C (A 2794) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 24)) (C (A 0) (A 244)))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 174) (C (A 10) (C (C (A 6) (C (A 0) (A 245))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 25))) (C (A 0) (A 2))))))))) (C (A 8) (C (C (A 9) (C (A 0xbef7f4) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 13)) (C (A 0) (A 123)))) (C (A 0) (A 2)))))))))))

/-- `l2iNo` with its parts named. -/
def l2iNoN : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 59)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0xaebc) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 56))) (C (A 0) (A 2)))))))) (C (A 8) (C l2iTurn (C (A 8) (C (C (C (A 0) (A 6)) (C (A 0) (A 121))) (C (A 8) (C (C (C (C (A 1) (A 0)) l2iLzb) (C (C (A 0) (A 2)) (C (A 0) (A 6)))) (C (C (A 1) l2iBG) (C (A 0) (A 1))))))))))))))) (C (A 0) (A 2))))))))

theorem l2iNo_eq : l2iNo = l2iNoN := rfl

/-! ## The bunt of `need-lazy` -/

/-- The bunt of `need-lazy` computed from `K`: the mold at arm `191` of the
core at axis `3` of `K`, slammed on its own sample. -/
def l2iLzbF : Noun := C (A 7) (C (C (A 9) (C (A 191) (C (A 0) (A 3)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))

noncomputable def l2iLzbV : Noun := (evalFuel 2000 compK l2iLzbF).getD (A 0)

theorem l2i_lzb : nock compK l2iLzbF = some l2iLzbV := nock_of_evalFuel (fuel := 2000) (by kernel_rfl)

/-- `l2iLzb` on a subject whose axis `127` is axis `3` of `K`. -/
theorem l2i_lzb_at (T : Noun) (h : slot? 127 T = slot? 3 compK) : nock T l2iLzb = some l2iLzbV := by
  have hb := l2i_lzb
  unfold l2iLzbF at hb
  unfold l2iLzb
  simp only [nock_op7, nock_op9, nock_op0, h] at hb ⊢
  exact hb

/-! ## The gates -/

/-- The context of the gate of the `+roll`. -/
def l2iCtx (SN FN NSN LAZ KC : Noun) : Noun := C SN (C FN (C NSN (C l2iBody (C LAZ KC))))

/-- **The gate of the `+turn`** on a fork entry: `+lazy-to-inter1` again on
both branches. -/
theorem l2i_fgate (NSN LAZ : Noun) (oy on : Nat) (y n : Lazy CSet)
    (hy : nock (C l2iBody (C y.toNoun compK)) l2iBody = some (I1.toNounC (l2i y)))
    (hn : nock (C l2iBody (C n.toNoun compK)) l2iBody = some (I1.toNounC (l2i n))) :
    nock (C l2iTG (C (forkE ((oy, y), (on, n))) (C NSN (C l2iBody (C LAZ compK))))) l2iTG
      = some (I1.forkN (l2i y, l2i n)) := by
  unfold l2iTG forkE I1.forkN
  generalize l2iBody = B at hy hn ⊢
  generalize compK = KC at hy hn ⊢
  simp [nock_exec, hy, hn]

/-- **The gate of the `+roll`** on a bond and the accumulator `[sur fork]`. -/
theorem l2i_bstep (SN FN NSN LAZ : Noun) (o : Nat) (i : Lazy CSet) (ned : NeedOrd) (lok : CSet)
    (fk : List (I1 CSet × I1 CSet))
    (hi : nock (C l2iBody (C i.toNoun compK)) l2iBody = some (I1.toNounC (l2i i))) :
    nock (C l2iBG (C (C (bondE (o, i)) (I1.toNounC (I1.mk ned lok fk))) (l2iCtx SN FN NSN LAZ compK))) l2iBG
      = some (I1.toNounC (I1.mk (uniOrd (l2i i).ned ned) (HoonSet.uni lok (l2i i).lok) ((l2i i).fork ++ fk))) := by
  generalize l2i i = J at hi ⊢
  obtain ⟨n', l', f'⟩ := J
  have hu := uno_gate compK compK_cn n' ned
  have hua := uno_at
  have hL := compK_layer2
  have huni := cs_uni_is lok l'
  have hw := weld_gate_list layer2 (f'.map I1.forkN) (fk.map I1.forkN)
  simp only [I1.toNounC_mk, I1.forksNounC_eq, I1.ned, I1.lok, I1.fork, List.map_append] at hi hw ⊢
  unfold l2iCtx l2iBG bondE
  generalize l2iBody = B at hi ⊢
  generalize compK = KC at hu hua hL hi ⊢
  simp [nock_exec, hi, hua, uno_arm, hu, hL, in_arm, in.arm_at, in.uni.arm_at, cl_uni_arm, huni,
    weld_arm, weld.arm_at, hw]

/-- **The branch with a fork or a bond**, given the `+turn` and the `+roll`. -/
theorem l2i_no (s : Sure CSet) (f : List (Lazy.ForkE CSet)) (b : List (Nat × Lazy CSet))
    (hf : (f.map forkE).mapM (fun x => nock (C l2iTG (C x (C (needToOrd s.ned).toNoun
        (C l2iBody (C (Lazy.mk s f b).toNoun compK))))) l2iTG) = some ((l2iForks f).map I1.forkN))
    (hb : (b.map bondE).foldlM (fun acc x => nock (C l2iBG (C (C x acc) (l2iCtx
        (C (needToOrd s.ned).toNoun (HoonSet.toNoun s.lok)) (listN ((l2iForks f).map I1.forkN))
        (needToOrd s.ned).toNoun (Lazy.mk s f b).toNoun compK))) l2iBG)
        (I1.toNounC (I1.mk (needToOrd s.ned) s.lok (l2iForks f)))
      = some (I1.toNounC (l2iBonds b (needToOrd s.ned) s.lok (l2iForks f)))) :
    nock (C l2iBody (C (Lazy.mk s f b).toNoun compK)) l2iNo
      = some (I1.toNounC (l2iBonds b (needToOrd s.ned) s.lok (l2iForks f))) := by
  have hL := compK_layer2
  have hn := nta_gate compK s.ned
  have hna := nta_at
  have ht := turn_gate_mapM layer2 homoIn_layer2 l2iTG l2iTB
    (C (needToOrd s.ned).toNoun (C l2iBody (C (Lazy.mk s f b).toNoun compK)))
    (fun x => nock (C l2iTG (C x (C (needToOrd s.ned).toNoun (C l2iBody (C (Lazy.mk s f b).toNoun compK))))) l2iTG)
    (f.map forkE) (fun _ _ => rfl)
  rw [hf] at ht
  have hr := roll_gate_M layer2 l2iBG (C (A 0) l2iLzbV)
    (I1.toNounC (I1.mk (needToOrd s.ned) s.lok (l2iForks f)))
    (l2iCtx (C (needToOrd s.ned).toNoun (HoonSet.toNoun s.lok)) (listN ((l2iForks f).map I1.forkN))
        (needToOrd s.ned).toNoun (Lazy.mk s f b).toNoun compK)
    (fun x acc => nock (C l2iBG (C (C x acc) (l2iCtx
        (C (needToOrd s.ned).toNoun (HoonSet.toNoun s.lok)) (listN ((l2iForks f).map I1.forkN))
        (needToOrd s.ned).toNoun (Lazy.mk s f b).toNoun compK))) l2iBG)
    (b.map bondE) (fun _ _ _ => rfl)
  rw [hb] at hr
  have hz := l2i_lzb_at (C (C (needToOrd s.ned).toNoun (HoonSet.toNoun s.lok))
    (C (listN ((l2iForks f).map I1.forkN)) (C (needToOrd s.ned).toNoun (C l2iBody (C (Lazy.mk s f b).toNoun compK)))))
    rfl
  simp only [I1.toNounC_mk, I1.forksNounC_eq] at hr
  unfold l2iCtx at hr
  rw [l2iNo_eq]
  unfold l2iNoN l2iTurn
  simp only [Lazy.toNoun, Sure.toNoun] at ht hr hz ⊢
  simp only [forksNoun_eq, bondsNoun_eq] at ht hr hz ⊢
  generalize l2iBody = B at ht hr hz ⊢
  generalize compK = KC at hL hn hna ht hr hz ⊢
  simp [nock_exec, hL, hna, ntaHint, hn, turn.arm_at, turn_arm, ht, roll.arm_at, roll_arm, hr, hz]

/-! ## `+lazy-to-inter1` on every lazy need -/

/-- The first test of `+lazy-to-inter1`: with a fork or a bond, the branch
`l2iNo`. -/
theorem l2i_body_no (LAZ KC : Noun) (h : ∃ SURE FK BD, LAZ = C SURE (C FK BD) ∧
    ((∃ u v, FK = C u v) ∨ (FK = A 0 ∧ ∃ u v, BD = C u v))) :
    nock (C l2iBody (C LAZ KC)) l2iBody = nock (C l2iBody (C LAZ KC)) l2iNo := by
  obtain ⟨SURE, FK, BD, rfl, h⟩ := h
  conv => { lhs; arg 2; unfold l2iBody }
  generalize l2iNo = NO
  generalize l2iYes = Y
  generalize l2iBody = B
  rcases h with ⟨u, v, rfl⟩ | ⟨rfl, u, v, rfl⟩ <;> simp [nock_exec]

mutual
/-- **`+lazy-to-inter1`** on every lazy need over `CSet`: `l2i`. -/
theorem l2i_gate : ∀ laz : Lazy CSet,
    nock (C l2iBody (C laz.toNoun compK)) l2iBody = some (I1.toNounC (l2i laz))
  | Lazy.mk s f b => by
    have hf := l2i_forks (needToOrd s.ned).toNoun (Lazy.mk s f b).toNoun f
    have hb := l2i_bonds (C (needToOrd s.ned).toNoun (HoonSet.toNoun s.lok)) (listN ((l2iForks f).map I1.forkN))
      (needToOrd s.ned).toNoun (Lazy.mk s f b).toNoun b (needToOrd s.ned) s.lok (l2iForks f)
    have hno := l2i_no s f b hf hb
    rcases f with _ | ⟨⟨⟨oy, y⟩, ⟨on, n⟩⟩, r⟩
    · rcases b with _ | ⟨⟨o, l⟩, r'⟩
      · have h := l2i_gate_sure s.ned (HoonSet.toNoun s.lok)
        simpa [Lazy.toNoun, Lazy.forksNoun, Lazy.bondsNoun, Sure.toNoun, l2i, l2iBonds, l2iForks, I1.toNounC_mk,
          I1.forksNounC] using h
      · rw [l2i_body_no (Lazy.mk s [] ((o, l) :: r')).toNoun compK ⟨_, _, _, rfl, Or.inr ⟨rfl, _, _, rfl⟩⟩, l2i]
        exact hno
    · rw [l2i_body_no (Lazy.mk s (((oy, y), on, n) :: r) b).toNoun compK ⟨_, _, _, rfl, Or.inl ⟨_, _, rfl⟩⟩, l2i]
      exact hno

/-- The gate of the `+turn` over the forks, on every fork list. -/
theorem l2i_forks (NSN LAZ : Noun) : ∀ f : List (Lazy.ForkE CSet),
    (f.map forkE).mapM (fun x => nock (C l2iTG (C x (C NSN (C l2iBody (C LAZ compK))))) l2iTG)
      = some ((l2iForks f).map I1.forkN)
  | [] => rfl
  | ((oy, y), (on, n)) :: r => by
    have hg := l2i_fgate NSN LAZ oy on y n (l2i_gate y) (l2i_gate n)
    have hr := l2i_forks NSN LAZ r
    simp only [List.map_cons, List.mapM_cons, hg, hr, l2iForks]
    rfl

/-- The `+roll` over the bonds, on every bond list and accumulator. -/
theorem l2i_bonds (SN FN NSN LAZ : Noun) : ∀ (b : List (Nat × Lazy CSet)) (ned : NeedOrd) (lok : CSet)
    (fk : List (I1 CSet × I1 CSet)),
    (b.map bondE).foldlM (fun acc x => nock (C l2iBG (C (C x acc) (l2iCtx SN FN NSN LAZ compK))) l2iBG)
      (I1.toNounC (I1.mk ned lok fk)) = some (I1.toNounC (l2iBonds b ned lok fk))
  | [], ned, lok, fk => rfl
  | (o, i) :: r, ned, lok, fk => by
    have hs := l2i_bstep SN FN NSN LAZ o i ned lok fk (l2i_gate i)
    have hr := l2i_bonds SN FN NSN LAZ r (uniOrd (l2i i).ned ned) (HoonSet.uni lok (l2i i).lok) ((l2i i).fork ++ fk)
    simp only [l2iBonds]
    rw [List.map_cons, List.foldlM_cons, hs]
    exact hr
end

/-! ## `+shape-collapse` -/

/-- **`+shape-collapse` on every lazy need** on which the model returns at
some fuel: its product is the model's `ord`. -/
theorem sc_gate (laz : Lazy CSet) (less : Cape) (fuel : Nat) (r : NeedOrd)
    (h : shapeCol fuel laz less = some r) :
    nock (C scBody (C (C laz.toNoun less.toNoun) compK)) scBody = some r.toNoun := by
  unfold shapeCol at h
  cases e : i12 less (l2i laz) with
  | none => rw [e] at h; cases h
  | some intr =>
    rw [e, Option.bind_some] at h
    have hla := l2i_at
    have hl := l2i_gate laz
    have hia := i2_at
    have hi := i12_gate less (l2i laz)
    rw [e, Option.map_some] at hi
    have hca := ic_at
    have hc := ic_gate less intr fuel r h
    rw [scBody_eq]
    conv => { lhs; arg 2; unfold scBodyN }
    generalize I1.toNounC (l2i laz) = L at hl hi
    generalize compK = KC at hla hl hia hi hca hc ⊢
    simp [nock_exec, hla, l2i_arm, hl, hia, i2_arm, hi, hca, ic_arm, hc]

/-- **`+shape-collapse` crashes** when `+inter1-to-inter2` does in the model. -/
theorem sc_gate_none (laz : Lazy CSet) (less : Cape) (e : i12 less (l2i laz) = Option.none) :
    nock (C scBody (C (C laz.toNoun less.toNoun) compK)) scBody = Option.none := by
  have hla := l2i_at
  have hl := l2i_gate laz
  have hia := i2_at
  have hi := i12_gate less (l2i laz)
  rw [e] at hi
  rw [scBody_eq]
  conv => { lhs; arg 2; unfold scBodyN }
  generalize I1.toNounC (l2i laz) = L at hl hi
  generalize compK = KC at hla hl hia hi ⊢
  simp [nock_exec, hla, l2i_arm, hl, hia, i2_arm, hi]

end Compiler
end Formalization
