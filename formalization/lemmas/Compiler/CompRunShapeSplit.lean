import lemmas.Compiler.CompRunShapeFrom
import lemmas.Compiler.CompRunShapeSplitCut
import lemmas.Compiler.CompRunShapePruneCut
import lemmas.Compiler.CompRunShapeEmptyCut
import lemmas.Compiler.CompRunShapeMustCut
import lemmas.Compiler.CompLeapLazyGate
import lemmas.Compiler.CompSplitGen

/-!
# The link of `+laze-split` (track A, 2026-11-27)

`+laze-split` (door arm `0xabfe`, cut in `CompRunShapeSplitCut.lean`) against `lazeSplit` of
`Ska/RunShape.lean`, on every `laze` (forks and bonds to any depth) whose looks are not `0`
(`LzNZ`), on every noun `G` of `gen` (the arm reads none of it), under `CompIn ctx`.  The
`+split` of `need-lazy` (`CompSplitGen.lean`) without registers and blocks, with the turns and
prunes of `+lazy-leap` (`CompLeapLazyGate.lean`).

* `lmu_gate`: `+laze-must` (door arm `0x2aaee`) is `lazeMust`.
* `lem_gate`: `+laze-empty` (door arm `0x2ffa`) is `lazeEmpty`.
* `lpr_gate`: `+laze-prune` (door arm `0x55de`, with `+skip`) is `lazePrune`.
* `lsp_lok`: the `+rep:in` over the looks (its gate is `ssRepBat` of `+split-sure`, `lspRep_eq`)
  is `splitLokS`; `lsp_ned`: the halves of the sure need are `splitNed`.
* **`lsp_all`** (`lsp_allN`, with `lsp_forks`, `lsp_bonds`): the gate is `lazeSplit`.
* `lsp_door`: the arm on the door gives the gate.
* `lazeSplit_some`, **`lazeSplit_nz`** (model only): under `LzNZ` the split returns, and both
  halves are `LzNZ` (a look `mas axe` of a look not in `0 1 2 3` is at least `1`).

The model takes the same steps in the same order (the looks in the order of `HoonSet.toList`,
which is the `preorder` that `+rep:in` walks, `cs_preorder`).  No departure.  On a look `0` both
crash (the `?<` of the gate, the `none` of `splitLokS`); that case is not linked here (`LzNZ`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-! ## `+laze-must` -/

/-- **`+laze-must`** is `lazeMust`, on every shape and context. -/
theorem lmu_gate (n : NeedOrd) (D : Noun) :
    nock (C lmuGate (C n.toNoun D)) lmuGate = some (lazeMust n).toNoun := by
  unfold lmuGate
  cases n with
  | pair p q =>
    obtain ⟨a, b, hp⟩ := no_cell p
    simp [nock_exec, NeedOrd.toNoun, hp, lazeMust, eqCode, Tag.both, Tag.this, Tag.none]
  | both h t => simp [nock_exec, NeedOrd.toNoun, lazeMust, Tag.both]
  | this => simp [nock_exec, NeedOrd.toNoun, lazeMust, eqCode_atom, Tag.this, Tag.both]
  | none => simp [nock_exec, NeedOrd.toNoun, lazeMust, eqCode_atom, Tag.this, Tag.both, Tag.none]

theorem lmu_arm (d : Noun) : nock d lmuArm = some (C lmuGate (C lmuBunt d)) := by
  unfold lmuArm; simp only [nock_exec]

/-! ## `+laze-empty` -/

theorem lem_arm (d : Noun) : nock d lemArm = some (C lemGate (C lemBunt d)) := by
  unfold lemArm; simp only [nock_exec]

/-- The tests of the forks and bonds of `+laze-empty`. -/
theorem lem_lists (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet))) (bd : List (Nat × Laze CSet)) :
    (fk = [] ∧ listN (fk.map lzfE) = A 0 ∨ fk ≠ [] ∧ eqCode (A 0) (listN (fk.map lzfE)) = A 1) ∧
    (bd = [] ∧ listN (bd.map lzbE) = A 0 ∨ bd ≠ [] ∧ eqCode (A 0) (listN (bd.map lzbE)) = A 1) := by
  constructor
  · by_cases h : fk = []
    · left; subst h; exact ⟨rfl, rfl⟩
    · right; exact ⟨h, wl_eq_nil _ (by simpa using h)⟩
  · by_cases h : bd = []
    · left; subst h; exact ⟨rfl, rfl⟩
    · right; exact ⟨h, wl_eq_nil _ (by simpa using h)⟩

/-- **`+laze-empty`** is `lazeEmpty`, on every `laze` and context. -/
theorem lem_gate (laz : Laze CSet) (D : Noun) :
    nock (C lemGate (C laz.toNoun D)) lemGate = some (loob (lazeEmpty laz)) := by
  obtain ⟨⟨ned, lok⟩, fk, bd⟩ := laz
  rw [lz_toNoun_mk]
  obtain ⟨hf, hb⟩ := lem_lists fk bd
  unfold lemGate
  cases ned with
  | pair p q =>
    obtain ⟨a, b, hp⟩ := no_cell p
    simp [nock_exec, SureO.toNoun, NeedOrd.toNoun, hp, lazeEmpty, loob, eqCode, Laze.sure]
  | this => simp [nock_exec, SureO.toNoun, NeedOrd.toNoun, lazeEmpty, loob, eqCode_atom, Tag.this, Laze.sure]
  | both h t => simp [nock_exec, SureO.toNoun, NeedOrd.toNoun, lazeEmpty, loob, eqCode_atom, Tag.both,
      Laze.sure]
  | none =>
    rcases cs_small_cases lok with ⟨hsm, hl | hl⟩ | ⟨hsm, n, l, r, hl, hne⟩
    · rcases hf with ⟨hf0, hf⟩ | ⟨hf0, hf⟩ <;> rcases hb with ⟨hb0, hb⟩ | ⟨hb0, hb⟩ <;>
        simp [nock_exec, SureO.toNoun, NeedOrd.toNoun, Tag.none, hl, hsm, lazeEmpty, loob, hf, hb,
          hf0, hb0, List.isEmpty_iff, Laze.sure, Laze.fork, Laze.bond]
    · rcases hf with ⟨hf0, hf⟩ | ⟨hf0, hf⟩ <;> rcases hb with ⟨hb0, hb⟩ | ⟨hb0, hb⟩ <;>
        simp [nock_exec, SureO.toNoun, NeedOrd.toNoun, Tag.none, hl, hsm, lazeEmpty, loob, hf, hb,
          hf0, hb0, List.isEmpty_iff, Laze.sure, Laze.fork, Laze.bond]
    · rcases n with k | ⟨n1, n2⟩
      · by_cases hk : k = 1
        · subst hk
          rcases l with l | ⟨l1, l2⟩
          · by_cases hl0 : l = 0
            · subst hl0
              rcases r with r | ⟨r1, r2⟩
              · have hr0 : r ≠ 0 := fun e => hne ⟨rfl, rfl, by rw [e]⟩
                simp [nock_exec, SureO.toNoun, NeedOrd.toNoun, hl, lazeEmpty, hsm, loob,
                  eqCode_atom, Tag.none, Ne.symm hr0, Laze.sure]
              · simp [nock_exec, SureO.toNoun, NeedOrd.toNoun, hl, lazeEmpty, hsm, loob,
                  eqCode_atom, eqCode, Tag.none, Laze.sure]
            · simp [nock_exec, SureO.toNoun, NeedOrd.toNoun, hl, lazeEmpty, hsm, loob,
                eqCode_atom, Tag.none, Ne.symm hl0, Laze.sure]
          · simp [nock_exec, SureO.toNoun, NeedOrd.toNoun, hl, lazeEmpty, hsm, loob,
              eqCode_atom, eqCode, Tag.none, Laze.sure]
        · simp [nock_exec, SureO.toNoun, NeedOrd.toNoun, hl, lazeEmpty, hsm, loob,
            eqCode_atom, Tag.none, Ne.symm hk, Laze.sure]
      · simp [nock_exec, SureO.toNoun, NeedOrd.toNoun, hl, lazeEmpty, hsm, loob,
          eqCode_atom, eqCode, Tag.none, Laze.sure]

/-! ## `+laze-prune` -/

theorem lpr_arm (d : Noun) : nock d lprArm = some (C lprGate (C lprBunt d)) := by
  unfold lprArm; simp only [nock_exec]

/-- **`+laze-prune`** is `lazePrune`, on every `laze`, in every door core whose context has
layer 2 (`CompIn`). -/
theorem lpr_gate (hc : CompIn ctx) (laz : Laze CSet) (G : Noun) :
    nock (C lprGate (C laz.toNoun (C comp.door (C G ctx)))) lprGate = some (lazePrune laz).toNoun := by
  obtain ⟨s, fk, bd⟩ := laz
  have hle := lem_at' (C G ctx)
  have hF := skip_gate_map lzfE layer2 lprGF (C (C (A 0) lprBunt) (C (A 0) lprBunt))
    (C lprGate (C (Laze.mk s fk bd).toNoun (C comp.door (C G ctx))))
    (fun e : (Nat × Laze CSet) × (Nat × Laze CSet) => lazeEmpty e.1.2 && lazeEmpty e.2.2)
    fk (fun e _ => by
      obtain ⟨⟨oy, y⟩, ⟨on, n⟩⟩ := e
      have hy := lem_gate y (C comp.door (C G ctx))
      have hn := lem_gate n (C comp.door (C G ctx))
      unfold lprGF
      generalize comp.door = Dr at hle hy hn ⊢
      cases hey : lazeEmpty y <;> cases hen : lazeEmpty n <;>
        simp [nock_exec, lzfE, hle, lem_arm, hy, hn, hey, hen, loob])
  have hB := skip_gate_map lzbE layer2 lprGB (C (A 0) lprBunt)
    (C lprGate (C (Laze.mk s fk bd).toNoun (C comp.door (C G ctx))))
    (fun e : Nat × Laze CSet => lazeEmpty e.2)
    bd (fun e _ => by
      obtain ⟨ob, l⟩ := e
      have hl := lem_gate l (C comp.door (C G ctx))
      unfold lprGB
      generalize comp.door = Dr at hle hl ⊢
      simp [nock_exec, lzbE, hle, lem_arm, hl])
  simp only [lz_toNoun_mk] at hF hB ⊢
  unfold lprBunt lprGF at hF
  unfold lprBunt lprGB at hB
  conv => { lhs; arg 2; unfold lprGate }
  simp [nock_exec, hc, skip.arm_at, hF, hB, lazePrune, lz_toNoun_mk, lprBunt, lprGF, lprGB]

/-- `+laze-prune` on the noun of a `laze` written out. -/
theorem lpr_mk (hc : CompIn ctx) (s : SureO CSet) (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet)))
    (bd : List (Nat × Laze CSet)) (G : Noun) :
    nock (C lprGate (C (C s.toNoun (C (listN (fk.map lzfE)) (listN (bd.map lzbE)))) (C comp.door (C G ctx))))
      lprGate = some (lazePrune (Laze.mk s fk bd)).toNoun := by
  rw [← lz_toNoun_mk]; exact lpr_gate hc _ G

/-! ## The model, as `mapM` -/

/-- The fork gate of `+laze-split`, in the model. -/
noncomputable def lsF (e : (Nat × Laze CSet) × (Nat × Laze CSet)) :
    Option (((Nat × Laze CSet) × (Nat × Laze CSet)) × ((Nat × Laze CSet) × (Nat × Laze CSet))) :=
  (lazeSplit e.1.2).bind fun yy => (lazeSplit e.2.2).map fun nn =>
    (((e.1.1, yy.1), (e.2.1, nn.1)), ((e.1.1, yy.2), (e.2.1, nn.2)))

/-- The bond gate of `+laze-split`, in the model. -/
noncomputable def lsB (e : Nat × Laze CSet) : Option ((Nat × Laze CSet) × (Nat × Laze CSet)) :=
  (lazeSplit e.2).map fun bb => ((e.1, bb.1), (e.1, bb.2))

theorem splitF_mapM : ∀ fk : List ((Nat × Laze CSet) × (Nat × Laze CSet)), splitF fk = fk.mapM lsF
  | [] => rfl
  | ((oy, y), (on, n)) :: rest => by
    simp only [splitF, List.mapM_cons, lsF, splitF_mapM rest]
    cases lazeSplit y <;> cases lazeSplit n <;> cases rest.mapM lsF <;> rfl

theorem splitB_mapM : ∀ bd : List (Nat × Laze CSet), splitB bd = bd.mapM lsB
  | [] => rfl
  | (ob, l) :: rest => by
    simp only [splitB, List.mapM_cons, lsB, splitB_mapM rest]
    cases lazeSplit l <;> cases rest.mapM lsB <;> rfl

/-- The fold of `splitLokS` on looks that are not `0`. -/
theorem splitLokS_eq (lok : CSet) (h0 : ∀ y ∈ HoonSet.toList lok, y ≠ 0) :
    splitLokS lok = some ((HoonSet.toList lok).foldl (fun s y => ssStep y s)
      (HoonSet.empty, HoonSet.empty)) := by
  unfold splitLokS
  generalize ((HoonSet.empty, HoonSet.empty) : CSet × CSet) = acc
  generalize HoonSet.toList lok = l at h0 ⊢
  induction l generalizing acc with
  | nil => rfl
  | cons y l ih =>
    have hy : y ≠ 0 := h0 y List.mem_cons_self
    have ih' := ih (ssStep y acc) (fun z hz => h0 z (List.mem_cons_of_mem _ hz))
    rw [List.foldl_cons, List.foldl_cons, ← ih']
    congr 1
    obtain ⟨h, t⟩ := acc
    unfold ssStep
    by_cases e : y = 1 ∨ y = 2 ∨ y = 3
    · simp [e, hy]
    · by_cases e2 : cap y = 2 <;> simp [e, e2, hy]

/-- The noun of a pair of fork entries. -/
noncomputable def lzf2N (x : ((Nat × Laze CSet) × (Nat × Laze CSet)) × ((Nat × Laze CSet) × (Nat × Laze CSet))) :
    Noun := C (lzfE x.1) (lzfE x.2)

/-- The noun of a pair of bond entries. -/
noncomputable def lzb2N (x : (Nat × Laze CSet) × (Nat × Laze CSet)) : Noun := C (lzbE x.1) (lzbE x.2)

/-- The noun of a pair of `laze`s. -/
noncomputable def lzpN (x : Laze CSet × Laze CSet) : Noun := C x.1.toNoun x.2.toNoun

/-! ## The parts of the gate -/

theorem lsp_arm (d : Noun) : nock d lspArm = some (C lspGate (C lspBunt d)) := by
  unfold lspArm lspHint; simp only [nock_exec]

/-- **The arm `+laze-split` on the door gives the gate `lspGate`**. -/
theorem lsp_door (y : Noun) : nock (C comp.door y) (C (A 9) (C (A 0xabfe) (C (A 0) (A 1))))
    = some (C lspGate (C lspBunt (C comp.door y))) := by
  simp [nock_exec, lsp_at', lsp_arm]

theorem lspRep_eq : lspRep = ssRepBat := by unfold lspRep ssRepBat; rfl

/-- **The `+rep:in` over the looks** (`lspLok`), on looks that are not `0`. -/
theorem lsp_lok (hc : CompIn ctx) (G : Noun) (s : SureO CSet) (FB : Noun)
    (h0 : ∀ y ∈ HoonSet.toList s.lok, y ≠ 0) :
    nock (C lspGate (C (C s.toNoun FB) (C comp.door (C G ctx)))) lspLok
      = some (ssN ((HoonSet.toList s.lok).foldl (fun s y => ssStep y s) (HoonSet.empty, HoonSet.empty))) := by
  obtain ⟨ned, lok⟩ := s
  simp only at h0
  have hrep := rep_gate_on ssN (fun n s => match n with | Noun.atom y => ssStep y s | _ => s)
    in.battery layer2 ssRepBat (A 0)
    (C lspGate (C (C (C ned.toNoun (HoonSet.toNoun lok)) FB) (C comp.door (C G ctx))))
    (HoonSet.toNoun lok) (cs_tree lok) (HoonSet.empty, HoonSet.empty) (by
      intro n hn s
      rw [cs_preorder] at hn
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hn
      exact ss_gate hc _ _ _ y (h0 y hy) s)
  rw [cs_preorder, List.foldl_map] at hrep
  generalize (HoonSet.toList lok).foldl (fun s y => ssStep y s) (HoonSet.empty, HoonSet.empty) = F at hrep ⊢
  simp only [ssN, HoonSet.toNoun_empty] at hrep
  simp only [SureO.toNoun]
  unfold lspLok
  rw [lspRep_eq]
  simp [nock_exec, hc, in_arm, in.arm_at, in.rep.arm_at, rep_arm, hrep, ssN]

/-- **The halves of the sure need** (`lspNed`): `splitNed`, the `%both` case through
`+laze-must`. -/
theorem lsp_ned (ned : NeedOrd) (LP LK FB Y : Noun) :
    nock (C LP (C lspGate (C (C (C ned.toNoun LK) FB) (C comp.door Y)))) lspNed
      = some (C (splitNed ned).1.toNoun (splitNed ned).2.toNoun) := by
  have hm := lmu_at' Y
  unfold lspNed
  cases ned with
  | pair p q =>
    obtain ⟨a, b, hp⟩ := no_cell p
    simp [nock_exec, NeedOrd.toNoun, hp, splitNed]
  | none => simp [nock_exec, NeedOrd.toNoun, splitNed, Tag.none, Tag.this, Tag.both]
  | this => simp [nock_exec, NeedOrd.toNoun, splitNed, Tag.none, Tag.this, Tag.both, eqCode_atom]
  | both h t =>
    generalize comp.door = Dr at hm ⊢
    simp [nock_exec, NeedOrd.toNoun, splitNed, Tag.none, Tag.this, Tag.both, eqCode_atom, hm, lmu_arm,
      lmu_gate]

/-- **The two `+laze-prune`** (`lspPr`), on the turns of `+head` and `+tail` over the forks and
the bonds. -/
theorem lsp_pr (hc : CompIn ctx) (G L : Noun) (nh nt : NeedOrd) (lh lt : CSet)
    (fs : List (((Nat × Laze CSet) × (Nat × Laze CSet)) × ((Nat × Laze CSet) × (Nat × Laze CSet))))
    (bs : List ((Nat × Laze CSet) × (Nat × Laze CSet))) :
    nock (C (listN (bs.map lzb2N)) (C (listN (fs.map lzf2N)) (C (C nh.toNoun nt.toNoun)
      (C (C (HoonSet.toNoun lh) (HoonSet.toNoun lt)) (C lspGate (C L (C comp.door (C G ctx)))))))) lspPr
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
  unfold lspPr
  simp [nock_exec, lzpN, hc, turn.arm_at, turn_arm, head_at, head_arm, tail_at, tail_arm, hF1, hF2,
    hB1, hB2, hlp, lpr_arm, hP1, hP2, buntGate]

/-- **The turns over the forks and the bonds, then the prunes** (`lspR`), given the gates. -/
theorem lsp_r (hc : CompIn ctx) (G SN : Noun) (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet)))
    (bd : List (Nat × Laze CSet)) (nh nt : NeedOrd) (lh lt : CSet)
    (hF : ∀ e ∈ fk, ∀ NP LP L : Noun,
      nock (C lspGF (C (lzfE e) (C NP (C LP (C lspGate (C L (C comp.door (C G ctx)))))))) lspGF
        = (lsF e).map lzf2N)
    (hB : ∀ e ∈ bd, ∀ FS NP LP L : Noun,
      nock (C lspGB (C (lzbE e) (C FS (C NP (C LP (C lspGate (C L (C comp.door (C G ctx))))))))) lspGB
        = (lsB e).map lzb2N) :
    nock (C (C nh.toNoun nt.toNoun) (C (C (HoonSet.toNoun lh) (HoonSet.toNoun lt)) (C lspGate
      (C (C SN (C (listN (fk.map lzfE)) (listN (bd.map lzbE)))) (C comp.door (C G ctx)))))) lspR
      = (fk.mapM lsF).bind fun fs => (bd.mapM lsB).map fun bs =>
          lzpN (lazePrune (Laze.mk ⟨nh, lh⟩ (fs.map Prod.fst) (bs.map Prod.fst)),
            lazePrune (Laze.mk ⟨nt, lt⟩ (fs.map Prod.snd) (bs.map Prod.snd))) := by
  have hFk := turn_gate_mapT lzfE lzf2N layer2 homoIn_layer2 lspGF (C (C (A 0) lspBunt) (C (A 0) lspBunt))
    (C (C nh.toNoun nt.toNoun) (C (C (HoonSet.toNoun lh) (HoonSet.toNoun lt)) (C lspGate
      (C (C SN (C (listN (fk.map lzfE)) (listN (bd.map lzbE)))) (C comp.door (C G ctx))))))
    lsF fk (fun e he => hF e he _ _ _)
  unfold lspBunt at hFk
  cases e1 : fk.mapM lsF with
  | none =>
    rw [e1] at hFk
    unfold lspR
    simp [nock_exec, hc, turn.arm_at, turn_arm, hFk, buntGate, lspBunt]
  | some fs =>
    rw [e1] at hFk
    have hBd := turn_gate_mapT lzbE lzb2N layer2 homoIn_layer2 lspGB (C (A 0) lspBunt)
      (C (listN (fs.map lzf2N)) (C (C nh.toNoun nt.toNoun) (C (C (HoonSet.toNoun lh) (HoonSet.toNoun lt))
        (C lspGate (C (C SN (C (listN (fk.map lzfE)) (listN (bd.map lzbE)))) (C comp.door (C G ctx)))))))
      lsB bd (fun e he => hB e he _ _ _ _)
    unfold lspBunt at hBd
    cases e2 : bd.mapM lsB with
    | none =>
      rw [e2] at hBd
      unfold lspR
      simp [nock_exec, hc, turn.arm_at, turn_arm, hFk, hBd, buntGate, lspBunt]
    | some bs =>
      rw [e2] at hBd
      have hP := lsp_pr hc G (C SN (C (listN (fk.map lzfE)) (listN (bd.map lzbE)))) nh nt lh lt fs bs
      generalize comp.door = Dr at hP hFk hBd ⊢
      unfold lspR
      simp [nock_exec, hc, turn.arm_at, turn_arm, hFk, hBd, buntGate, hP, lspBunt]

/-! ## `+laze-split` on every `laze` -/

/-- `lazeSplit` on a `laze` written out, its turns as `mapM`, on looks that are not `0`. -/
theorem lazeSplit_eq (s : SureO CSet) (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet)))
    (bd : List (Nat × Laze CSet)) (h0 : ∀ y ∈ HoonSet.toList s.lok, y ≠ 0) :
    lazeSplit (Laze.mk s fk bd) =
      (if fk.isEmpty && bd.isEmpty then
        some (Laze.mk ⟨(splitNed s.ned).1, ((HoonSet.toList s.lok).foldl (fun s y => ssStep y s)
            (HoonSet.empty, HoonSet.empty)).1⟩ [] [],
          Laze.mk ⟨(splitNed s.ned).2, ((HoonSet.toList s.lok).foldl (fun s y => ssStep y s)
            (HoonSet.empty, HoonSet.empty)).2⟩ [] [])
      else (fk.mapM lsF).bind fun fs => (bd.mapM lsB).map fun bs =>
        (lazePrune (Laze.mk ⟨(splitNed s.ned).1, ((HoonSet.toList s.lok).foldl (fun s y => ssStep y s)
            (HoonSet.empty, HoonSet.empty)).1⟩ (fs.map Prod.fst) (bs.map Prod.fst)),
         lazePrune (Laze.mk ⟨(splitNed s.ned).2, ((HoonSet.toList s.lok).foldl (fun s y => ssStep y s)
            (HoonSet.empty, HoonSet.empty)).2⟩ (fs.map Prod.snd) (bs.map Prod.snd)))) := by
  rw [lazeSplit, splitLokS_eq s.lok h0, splitF_mapM, splitB_mapM]
  rfl

section
variable (hc : CompIn ctx) (G : Noun)
include hc

mutual
/-- **`+laze-split` on every `laze`** (forks and bonds to any depth) whose sure needs look at
no axis `0`: `lazeSplit`, on every noun `G` of `gen`. -/
theorem lsp_allN : ∀ (laz : Laze CSet), LzNZ laz →
    nock (C lspGate (C laz.toNoun (C comp.door (C G ctx)))) lspGate = (lazeSplit laz).map lzpN
  | Laze.mk s fk bd, ⟨hs, hfk, hbd⟩ => by
    rw [lazeSplit_eq s fk bd hs, lz_toNoun_mk]
    have hl := lsp_lok hc G s (C (listN (fk.map lzfE)) (listN (bd.map lzbE))) hs
    generalize (HoonSet.toList s.lok).foldl (fun s y => ssStep y s) (HoonSet.empty, HoonSet.empty) = F at hl ⊢
    obtain ⟨lh, lt⟩ := F
    have hn := lsp_ned s.ned (ssN (lh, lt)) (HoonSet.toNoun s.lok) (C (listN (fk.map lzfE)) (listN (bd.map lzbE)))
      (C G ctx)
    have hr := lsp_r hc G s.toNoun fk bd (splitNed s.ned).1 (splitNed s.ned).2 lh lt
      (fun e he NP LP L => lsp_forks fk hfk e he NP LP L) (fun e he FS NP LP L => lsp_bonds bd hbd e he FS NP LP L)
    have tF := lz_test lzfE fk
    have tB := lz_test lzbE bd
    simp only [ssN] at hl hn
    obtain ⟨ned, lok⟩ := s
    simp only [SureO.toNoun] at hl hn hr ⊢
    have hif : (fk.isEmpty && bd.isEmpty) = decide (fk = [] ∧ bd = []) := by cases fk <;> cases bd <;> rfl
    rw [hif]
    generalize hFN : listN (fk.map lzfE) = FN at hl hn hr tF ⊢
    generalize hBN : listN (bd.map lzbE) = BN at hl hn hr tB ⊢
    conv => { lhs; arg 2; unfold lspGate }
    by_cases hb : fk = [] ∧ bd = []
    · obtain ⟨rfl, rfl⟩ := hb
      have e0 : listN ([] : List Noun) = A 0 := rfl
      simp only [List.map_nil, e0] at hFN hBN
      subst hFN; subst hBN
      simp [nock_exec, hl, hn, lspTest, lspLeaf, lzpN, lz_toNoun_mk, SureO.toNoun, listN]
    · rw [if_neg (by simpa using hb)]
      have tt : (eqCode (A 0) FN = A 0 ∧ (A 0 = FN) = True ∧ eqCode (A 0) BN = A 1 ∧ (A 0 = BN) = False) ∨
          (eqCode (A 0) FN = A 1 ∧ (A 0 = FN) = False) := by
        rcases tF with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · rcases tB with ⟨h4, h5, h6⟩ | ⟨h4, h5, h6⟩
          · exact absurd ⟨h1, h4⟩ hb
          · exact Or.inl ⟨h2, h3, h5, h6⟩
        · exact Or.inr ⟨h2, h3⟩
      rcases tt with ⟨t2, t3, t5, t6⟩ | ⟨t2, t3⟩
      · simp [nock_exec, hl, hn, lspTest, t2, t3, t5, t6, hr]
        cases fk.mapM lsF <;> cases bd.mapM lsB <;> simp [lzpN]
      · simp [nock_exec, hl, hn, lspTest, t2, t3, hr]
        cases fk.mapM lsF <;> cases bd.mapM lsB <;> simp [lzpN]

theorem lsp_forks : ∀ (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet))), LzNZF fk → ∀ e ∈ fk,
    ∀ NP LP L : Noun,
    nock (C lspGF (C (lzfE e) (C NP (C LP (C lspGate (C L (C comp.door (C G ctx)))))))) lspGF
      = (lsF e).map lzf2N
  | [], _, e, he => absurd he List.not_mem_nil
  | ((oy, y), (on, n)) :: rest, ⟨hy, hn, hr⟩, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro NP LP L
      have ihy := lsp_allN y hy
      have ihn := lsp_allN n hn
      unfold lspGF
      cases e1 : lazeSplit y with
      | none => rw [e1] at ihy; simp [nock_exec, lzfE, ihy, lsF, e1, lsp_at, lsp_at', lsp_arm]
      | some yy =>
        rw [e1] at ihy
        cases e2 : lazeSplit n with
        | none => rw [e2] at ihn; simp [nock_exec, lzfE, ihy, ihn, lsF, e1, e2, lsp_at, lsp_at', lsp_arm]
        | some nn =>
          rw [e2] at ihn
          simp [nock_exec, lzfE, ihy, ihn, lsF, e1, e2, lsp_at, lsp_at', lsp_arm, lzpN, lzf2N]
    · exact lsp_forks rest hr e he'

theorem lsp_bonds : ∀ (bd : List (Nat × Laze CSet)), LzNZB bd → ∀ e ∈ bd, ∀ FS NP LP L : Noun,
    nock (C lspGB (C (lzbE e) (C FS (C NP (C LP (C lspGate (C L (C comp.door (C G ctx))))))))) lspGB
      = (lsB e).map lzb2N
  | [], _, e, he => absurd he List.not_mem_nil
  | (ob, l) :: rest, ⟨hl, hr⟩, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro FS NP LP L
      have ihl := lsp_allN l hl
      unfold lspGB
      cases e1 : lazeSplit l with
      | none => rw [e1] at ihl; simp [nock_exec, lzbE, ihl, lsB, e1, lsp_at, lsp_at', lsp_arm]
      | some bb => rw [e1] at ihl; simp [nock_exec, lzbE, ihl, lsB, e1, lsp_at, lsp_at', lsp_arm, lzpN, lzb2N]
    · exact lsp_bonds rest hr e he'
end

end

/-- **`+laze-split` is `lazeSplit`** on every `laze` whose sure needs look at no axis `0`
(`LzNZ`), on every noun `G` of `gen`, under `CompIn ctx` (`lsp_allN` with the pair noun
written out). -/
theorem lsp_all (hc : CompIn ctx) (G : Noun) : ∀ (laz : Laze CSet), LzNZ laz →
    nock (C lspGate (C laz.toNoun (C comp.door (C G ctx)))) lspGate
      = (lazeSplit laz).map fun p => C p.1.toNoun p.2.toNoun :=
  lsp_allN hc G

/-! ## What `+laze-split` returns (the model) -/

/-- The fold of the looks keeps them positive: a look `mas y` of a look `y` not in `0 1 2 3` is
at least `1`. -/
theorem ssFold_nz : ∀ (l : List Nat) (acc : CSet × CSet), (∀ y ∈ l, y ≠ 0) →
    (∀ y ∈ HoonSet.toList acc.1, y ≠ 0) → (∀ y ∈ HoonSet.toList acc.2, y ≠ 0) →
    (∀ y ∈ HoonSet.toList (l.foldl (fun s y => ssStep y s) acc).1, y ≠ 0) ∧
      (∀ y ∈ HoonSet.toList (l.foldl (fun s y => ssStep y s) acc).2, y ≠ 0)
  | [], acc, _, h1, h2 => ⟨h1, h2⟩
  | a :: l, acc, hl, h1, h2 => by
    rw [List.foldl_cons]
    have ha : a ≠ 0 := hl a List.mem_cons_self
    have hm : mas a ≠ 0 → True := fun _ => trivial
    refine ssFold_nz l _ (fun y hy => hl y (List.mem_cons_of_mem _ hy)) ?_ ?_ <;>
    · unfold ssStep
      by_cases e : a = 1 ∨ a = 2 ∨ a = 3
      · simp only [e, if_true]; first | exact h1 | exact h2
      · have h2a : 2 ≤ a := by omega
        have hp : mas a ≠ 0 := by
          have := masF_pos a h2a
          rw [masF_eq_mas] at this
          omega
        simp only [e, if_false]
        by_cases e2 : cap a = 2
        · simp only [e2, if_true]
          first
          | exact h2
          | intro y hy; rcases (HoonSet.mem_put _ _ _).1 hy with rfl | hy; exact hp; exact h1 y hy
        · simp only [e2, if_false]
          first
          | exact h1
          | intro y hy; rcases (HoonSet.mem_put _ _ _).1 hy with rfl | hy; exact hp; exact h2 y hy

theorem lzNZF_filter (p : (Nat × Laze CSet) × (Nat × Laze CSet) → Bool) :
    ∀ f : List ((Nat × Laze CSet) × (Nat × Laze CSet)), LzNZF f → LzNZF (f.filter p)
  | [], _ => trivial
  | ((oy, y), (on, n)) :: r, ⟨hy, hn, hr⟩ => by
    rw [List.filter_cons]
    split
    · exact ⟨hy, hn, lzNZF_filter p r hr⟩
    · exact lzNZF_filter p r hr

theorem lzNZB_filter (p : Nat × Laze CSet → Bool) :
    ∀ b : List (Nat × Laze CSet), LzNZB b → LzNZB (b.filter p)
  | [], _ => trivial
  | (o, l) :: r, ⟨hl, hr⟩ => by
    rw [List.filter_cons]
    split
    · exact ⟨hl, lzNZB_filter p r hr⟩
    · exact lzNZB_filter p r hr

/-- `+laze-prune` keeps `LzNZ`. -/
theorem lazePrune_nz : ∀ l : Laze CSet, LzNZ l → LzNZ (lazePrune l)
  | Laze.mk s f b, ⟨hs, hf, hb⟩ => ⟨hs, lzNZF_filter _ f hf, lzNZB_filter _ b hb⟩

mutual
/-- **What `+laze-split` returns looks at no axis `0`** when its `laze` does not. -/
theorem lazeSplit_nz : ∀ (l : Laze CSet), LzNZ l → ∀ h t, lazeSplit l = some (h, t) → LzNZ h ∧ LzNZ t
  | Laze.mk s fk bd, ⟨hs, hfk, hbd⟩, h, t, e => by
    rw [lazeSplit_eq s fk bd hs] at e
    obtain ⟨n1, n2⟩ := ssFold_nz (HoonSet.toList s.lok) (HoonSet.empty, HoonSet.empty) hs
      (fun y hy => absurd hy (HoonSet.mem_empty y)) (fun y hy => absurd hy (HoonSet.mem_empty y))
    split at e
    · simp only [Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨⟨n1, trivial, trivial⟩, ⟨n2, trivial, trivial⟩⟩
    · cases e3 : fk.mapM lsF with
      | none => simp [e3] at e
      | some fs =>
        cases e4 : bd.mapM lsB with
        | none => simp [e3, e4] at e
        | some bs =>
          simp only [e3, e4, Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
          obtain ⟨rfl, rfl⟩ := e
          obtain ⟨hf1, hf2⟩ := lsF_nz fk hfk fs e3
          obtain ⟨hb1, hb2⟩ := lsB_nz bd hbd bs e4
          exact ⟨lazePrune_nz _ ⟨n1, hf1, hb1⟩, lazePrune_nz _ ⟨n2, hf2, hb2⟩⟩

theorem lsF_nz : ∀ (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet))), LzNZF fk →
    ∀ fs, fk.mapM lsF = some fs → LzNZF (fs.map Prod.fst) ∧ LzNZF (fs.map Prod.snd)
  | [], _, fs, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; exact ⟨trivial, trivial⟩
  | ((oy, y), (on, n)) :: rest, ⟨hy, hn, hr⟩, fs, h => by
    simp only [List.mapM_cons] at h
    cases e1 : lazeSplit y with
    | none => simp [lsF, e1] at h
    | some yy =>
      obtain ⟨yb, yr⟩ := yy
      cases e2 : lazeSplit n with
      | none => simp [lsF, e1, e2] at h
      | some nn =>
        obtain ⟨nb, nr⟩ := nn
        cases e3 : rest.mapM lsF with
        | none => simp [lsF, e1, e2, e3] at h
        | some rs =>
          simp [lsF, e1, e2, e3] at h
          subst h
          obtain ⟨y1, y2⟩ := lazeSplit_nz y hy yb yr e1
          obtain ⟨n1, n2⟩ := lazeSplit_nz n hn nb nr e2
          obtain ⟨r1, r2⟩ := lsF_nz rest hr rs e3
          exact ⟨⟨y1, n1, r1⟩, ⟨y2, n2, r2⟩⟩

theorem lsB_nz : ∀ (bd : List (Nat × Laze CSet)), LzNZB bd →
    ∀ bs, bd.mapM lsB = some bs → LzNZB (bs.map Prod.fst) ∧ LzNZB (bs.map Prod.snd)
  | [], _, bs, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; exact ⟨trivial, trivial⟩
  | (ob, l) :: rest, ⟨hl, hr⟩, bs, h => by
    simp only [List.mapM_cons] at h
    cases e1 : lazeSplit l with
    | none => simp [lsB, e1] at h
    | some bb =>
      obtain ⟨lb, lr⟩ := bb
      cases e3 : rest.mapM lsB with
      | none => simp [lsB, e1, e3] at h
      | some rs =>
        simp [lsB, e1, e3] at h
        subst h
        obtain ⟨l1, l2⟩ := lazeSplit_nz l hl lb lr e1
        obtain ⟨r1, r2⟩ := lsB_nz rest hr rs e3
        exact ⟨⟨l1, r1⟩, ⟨l2, r2⟩⟩
end

mutual
/-- Under `LzNZ` the split returns (the `?<` never fires). -/
theorem lazeSplit_ex : ∀ (l : Laze CSet), LzNZ l → ∃ h t, lazeSplit l = some (h, t)
  | Laze.mk s fk bd, ⟨hs, hfk, hbd⟩ => by
    rw [lazeSplit_eq s fk bd hs]
    split
    · exact ⟨_, _, rfl⟩
    · obtain ⟨fs, e3⟩ := lsF_some fk hfk
      obtain ⟨bs, e4⟩ := lsB_some bd hbd
      rw [e3, e4]; exact ⟨_, _, rfl⟩

theorem lsF_some : ∀ (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet))), LzNZF fk →
    ∃ fs, fk.mapM lsF = some fs
  | [], _ => ⟨[], rfl⟩
  | ((oy, y), (on, n)) :: rest, ⟨hy, hn, hr⟩ => by
    obtain ⟨yh, yt, e1⟩ := lazeSplit_ex y hy
    obtain ⟨nh, nt, e2⟩ := lazeSplit_ex n hn
    obtain ⟨rs, e3⟩ := lsF_some rest hr
    simp [List.mapM_cons, lsF, e1, e2, e3]

theorem lsB_some : ∀ (bd : List (Nat × Laze CSet)), LzNZB bd → ∃ bs, bd.mapM lsB = some bs
  | [], _ => ⟨[], rfl⟩
  | (ob, l) :: rest, ⟨hl, hr⟩ => by
    obtain ⟨lh, lt, e1⟩ := lazeSplit_ex l hl
    obtain ⟨rs, e3⟩ := lsB_some rest hr
    simp [List.mapM_cons, lsB, e1, e3]
end

/-- Under `LzNZ` the split does not crash. -/
theorem lazeSplit_some (l : Laze CSet) (h : LzNZ l) : lazeSplit l ≠ none := by
  obtain ⟨a, b, e⟩ := lazeSplit_ex l h
  rw [e]; exact Option.some_ne_none _

end Compiler
end Formalization
