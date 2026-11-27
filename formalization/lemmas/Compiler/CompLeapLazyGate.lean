import lemmas.Compiler.CompLeapLazy
import lemmas.Compiler.CompFromGen
import lemmas.Compiler.CompRunInvL

/-!
# `+lazy-leap` of the door of `+comp` on every lazy need

`+lazy-leap` (door arm `442366`, `lzlBat`) on `[p s laz]`:

    =/  cut  (need-cut p ned.sure.laz)
    =/  [sur-by sur-rec]  ?~(cut [*sure sure.laz] ..rep:in.., need-from..)
    =/  forks  (turn fork.laz |=(e (loop y) (loop n) ..))
    =/  bonds  (turn bond.laz |=(e (loop l) ..))
    :-  (lazy-prune sur-by (turn forks head) (turn bonds head))
    (lazy-prune sur-rec (turn forks tail) (turn bonds tail))

The battery is cut by `tools/gen/leap.py` into the push of `cut` (by
`+need-cut`, `ndc_gate`), the `?~ cut` (`lzlSur`: the bunt sure need, or the
`+rep:in` over the looks, `lzl_lok`, then `+need-from`, `ndf_gate`), the two
turns with the gates `lzlG2` (forks) and `lzlG3` (bonds), each of which
slams the battery again with `laz` replaced (`[9 2 10 [27 ..] 0 31]`, the
subject the theorem is stated on), and the two `+lazy-prune` (`lzlPr`,
`lp_mk`) on turns of `+head` and `+tail` of layer 2 (arms `0xbedd` and
`0x5f6be`, the gates `[0 12]` and `[0 13]`).

`lzl_gate`: the battery is `lazyLeap` on every lazy need whose looks are not
`0` (`LAll CrLok`) and positive `p` and `s`, crashes included.  The model
takes the same branches in the same order; a crash anywhere is `none` in
both.  Compared with the Hoon part by part: no departure.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.Ana

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-! ## `+head` and `+tail` of layer 2 -/

/-- The arm `+head` of layer 2, `|*(^ ,:+<-)`. -/
def headArm : Noun := C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) (C (A 0) (A 12))) (C (A 0) (A 1))))

/-- The arm `+tail` of layer 2, `|*(^ ,:+<+)`. -/
def tailArm : Noun := C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) (C (A 0) (A 13))) (C (A 0) (A 1))))

theorem head_at : slot? 0xbedd layer2 = some headArm := by kernel_rfl

theorem tail_at : slot? 0x5f6be layer2 = some tailArm := by kernel_rfl

theorem head_arm (d : Noun) : nock d headArm = some (C (C (A 0) (A 12)) (C (C (A 0) (A 0)) d)) := by
  unfold headArm; simp only [nock_exec]

theorem tail_arm (d : Noun) : nock d tailArm = some (C (C (A 0) (A 13)) (C (C (A 0) (A 0)) d)) := by
  unfold tailArm; simp only [nock_exec]

/-- `+turn` of `+head` over a list of pairs. -/
theorem turn_head {α β : Type} (F1 : α → Noun) (F2 : β → Noun) (l : List (α × β)) :
    nock (C turn.battery (C (C (listN (l.map fun x => C (F1 x.1) (F2 x.2)))
      (C (C (A 0) (A 12)) (C (C (A 0) (A 0)) layer2))) layer2)) turn.battery
      = some (listN ((l.map Prod.fst).map F1)) :=
  lq_turn_gate (fun x => C (F1 x.1) (F2 x.2)) F1 layer2 homoIn_layer2 _ _ _ Prod.fst l
    (fun a _ => by simp [nock_exec])

/-- `+turn` of `+tail` over a list of pairs. -/
theorem turn_tail {α β : Type} (F1 : α → Noun) (F2 : β → Noun) (l : List (α × β)) :
    nock (C turn.battery (C (C (listN (l.map fun x => C (F1 x.1) (F2 x.2)))
      (C (C (A 0) (A 13)) (C (C (A 0) (A 0)) layer2))) layer2)) turn.battery
      = some (listN ((l.map Prod.snd).map F2)) :=
  lq_turn_gate (fun x => C (F1 x.1) (F2 x.2)) F2 layer2 homoIn_layer2 _ _ _ Prod.snd l
    (fun a _ => by simp [nock_exec])

/-! ## The model, as `mapM` -/

/-- The fork gate of `+lazy-leap`, in the model. -/
noncomputable def lfF (p s : Nat) (e : Lazy.ForkE CSet) : Option (Lazy.ForkE CSet × Lazy.ForkE CSet) :=
  (lazyLeap p s e.1.2).bind fun yy => (lazyLeap p s e.2.2).map fun nn =>
    (((e.1.1, yy.1), (e.2.1, nn.1)), ((e.1.1, yy.2), (e.2.1, nn.2)))

/-- The bond gate of `+lazy-leap`, in the model. -/
noncomputable def lbF (p s : Nat) (e : Nat × Lazy CSet) : Option ((Nat × Lazy CSet) × (Nat × Lazy CSet)) :=
  (lazyLeap p s e.2).map fun bb => ((e.1, bb.1), (e.1, bb.2))

theorem leapForks_mapM (p s : Nat) : ∀ fk : List (Lazy.ForkE CSet),
    leapForks p s fk = fk.mapM (lfF p s)
  | [] => rfl
  | ((oy, y), (on, n)) :: rest => by
    simp only [leapForks, List.mapM_cons, lfF, leapForks_mapM p s rest]
    cases lazyLeap p s y <;> cases lazyLeap p s n <;> cases rest.mapM (lfF p s) <;> rfl

theorem leapBonds_mapM (p s : Nat) : ∀ bd : List (Nat × Lazy CSet),
    leapBonds p s bd = bd.mapM (lbF p s)
  | [] => rfl
  | (ob, l) :: rest => by
    simp only [leapBonds, List.mapM_cons, lbF, leapBonds_mapM p s rest]
    cases lazyLeap p s l <;> cases rest.mapM (lbF p s) <;> rfl

/-- The noun of a pair of fork entries. -/
noncomputable def f2N (x : Lazy.ForkE CSet × Lazy.ForkE CSet) : Noun := C (forkE x.1) (forkE x.2)

/-- The noun of a pair of bond entries. -/
noncomputable def b2N (x : (Nat × Lazy CSet) × (Nat × Lazy CSet)) : Noun := C (bondE x.1) (bondE x.2)

/-- The noun of a pair of lazy needs. -/
noncomputable def lpN (x : Lazy CSet × Lazy CSet) : Noun := C x.1.toNoun x.2.toNoun

/-! ## The two prunes -/

/-- **The two `+lazy-prune`** of `+lazy-leap` (`lzlPr`), on the turns of
`+head` and `+tail` over the forks and the bonds. -/
theorem lzl_pr (hc : CompIn ctx) (G B X cutN : Noun) (sb sr : Sure CSet)
    (fs : List (Lazy.ForkE CSet × Lazy.ForkE CSet)) (bs : List ((Nat × Lazy CSet) × (Nat × Lazy CSet))) :
    nock (C (listN (bs.map b2N)) (C (listN (fs.map f2N)) (C (C sb.toNoun sr.toNoun)
      (C cutN (C B (C X (C comp.door (C G ctx)))))))) lzlPr
      = some (lpN (Lazy.lazyPrune (Lazy.mk sb (fs.map Prod.fst) (bs.map Prod.fst)),
          Lazy.lazyPrune (Lazy.mk sr (fs.map Prod.snd) (bs.map Prod.snd)))) := by
  have hF1 := turn_head forkE forkE fs
  have hF2 := turn_tail forkE forkE fs
  have hB1 := turn_head bondE bondE bs
  have hB2 := turn_tail bondE bondE bs
  have hP1 := lp_mk hc sb (fs.map Prod.fst) (bs.map Prod.fst) G
  have hP2 := lp_mk hc sr (fs.map Prod.snd) (bs.map Prod.snd) G
  have hlp := comp_lp_at
  have e1 : (fs.map f2N) = fs.map fun x => C (forkE x.1) (forkE x.2) := rfl
  have e2 : (bs.map b2N) = bs.map fun x => C (bondE x.1) (bondE x.2) := rfl
  rw [e1, e2]
  generalize comp.door = Dr at hP1 hP2 hlp ⊢
  generalize (fs.map fun x => C (forkE x.1) (forkE x.2)) = FN at hF1 hF2 ⊢
  generalize (bs.map fun x => C (bondE x.1) (bondE x.2)) = BN at hB1 hB2 ⊢
  generalize ((fs.map Prod.fst).map forkE) = F1 at hF1 hP1
  generalize ((fs.map Prod.snd).map forkE) = F2 at hF2 hP2
  generalize ((bs.map Prod.fst).map bondE) = B1 at hB1 hP1
  generalize ((bs.map Prod.snd).map bondE) = B2 at hB2 hP2
  unfold lzlPr
  simp [nock_exec, lpN, hc, turn.arm_at, turn_arm, head_at, head_arm, tail_at, tail_arm, hF1, hF2,
    hB1, hB2, hlp, comp_lp_arm, hP1, hP2, buntGate]

/-! ## The `?~ cut` -/

/-- The sure needs of `by` and `rec` in the model, from the cut. -/
noncomputable def lzSur (p s : Nat) (sur : Sure CSet) : Option (Need × Need) → Option (Sure CSet × Sure CSet)
  | Option.none => some ((Sure.bunt : Sure CSet), sur)
  | some (don, rec) => (leapLok p s sur.lok).bind fun (lb, lr) =>
      (needFrom s don).map fun nf => ((⟨nf, lb⟩ : Sure CSet), (⟨rec, lr⟩ : Sure CSet))

/-- `lazyLeap` on a lazy need written out, its turns as `mapM`. -/
theorem lazyLeap_eq (p s : Nat) (sur : Sure CSet) (fk : List (Lazy.ForkE CSet)) (bd : List (Nat × Lazy CSet)) :
    lazyLeap p s (Lazy.mk sur fk bd) = (needCut p sur.ned).bind fun cut => (lzSur p s sur cut).bind fun ss =>
      (fk.mapM (lfF p s)).bind fun fs => (bd.mapM (lbF p s)).map fun bs =>
        (Lazy.lazyPrune (Lazy.mk ss.1 (fs.map Prod.fst) (bs.map Prod.fst)),
         Lazy.lazyPrune (Lazy.mk ss.2 (fs.map Prod.snd) (bs.map Prod.snd))) := by
  rw [lazyLeap, leapForks_mapM, leapBonds_mapM]
  cases needCut p sur.ned with
  | none => rfl
  | some cut =>
    cases cut with
    | none => rfl
    | some dr =>
      obtain ⟨don, rec⟩ := dr
      simp only [Option.bind_some, lzSur]

/-- **The `?~ cut` of `+lazy-leap`** (`lzlSur`): the bunt sure need and the
whole one when the cut is `~`, else the `+rep:in` over the looks and
`+need-from` of the part. -/
theorem lzl_sur (hc : CompIn ctx) (hl : CompLib ctx) (G : Noun) (p s : Nat) (hp : p ≠ 0) (hs : s ≠ 0)
    (sur : Sure CSet) (FK BK : Noun) (h0 : CrLok sur) (cut : Option (Need × Need)) :
    nock (C (cutNoun cut) (C lzlBat (C (C (A p) (C (A s) (C sur.toNoun (C FK BK)))) (C comp.door (C G ctx)))))
      lzlSur = (lzSur p s sur cut).map fun ss => C ss.1.toNoun ss.2.toNoun := by
  cases cut with
  | none =>
    unfold lzlSur
    simp [nock_exec, cutNoun, unitNoun, lzSur, Sure.toNoun, Sure.bunt, Need.toNoun, Tag.none,
      HoonSet.toNoun_empty]
  | some dr =>
    obtain ⟨don, rec⟩ := dr
    have hk := lzl_lok hc hl (cutNoun (some (don, rec))) (C sur.toNoun (C FK BK)) G p s hp hs sur.lok h0
    have hf := ndf_gate hc G s don
    have hD := ndf_at
    simp only [ssN, HoonSet.toNoun_empty, cutNoun, unitNoun] at hk
    simp only [Sure.toNoun] at hk ⊢
    generalize comp.door = Dr at hk hf hD ⊢
    cases e1 : leapLok p s sur.lok with
    | none =>
      rw [e1] at hk
      unfold lzlSur
      simp [nock_exec, cutNoun, unitNoun, lzSur, e1, hc, in_arm, in.arm_at, in.rep.arm_at, rep_arm, hk]
    | some lb =>
      obtain ⟨lb, lr⟩ := lb
      rw [e1] at hk
      simp only [Option.map_some, ssN] at hk
      cases e2 : needFrom s don with
      | none =>
        rw [e2] at hf
        unfold lzlSur
        simp [nock_exec, cutNoun, unitNoun, lzSur, e1, e2, hc, in_arm, in.arm_at, in.rep.arm_at, rep_arm, hk,
          hD, ndf_arm, hf]
      | some nf =>
        rw [e2] at hf
        unfold lzlSur
        simp [nock_exec, cutNoun, unitNoun, lzSur, e1, e2, hc, in_arm, in.arm_at, in.rep.arm_at, rep_arm, hk,
          hD, ndf_arm, hf]

/-! ## The turns -/

/-- **The turns of `+lazy-leap`** over the forks (gate `lzlG2`) and the
bonds (gate `lzlG3`), then the prunes (`lzlR2`), given the gates. -/
theorem lzl_r2 (hc : CompIn ctx) (G : Noun) (p s : Nat) (sur sb sr : Sure CSet)
    (fk : List (Lazy.ForkE CSet)) (bd : List (Nat × Lazy CSet)) (cutN : Noun)
    (hF : ∀ e ∈ fk, ∀ SS cN : Noun, nock (C lzlG2 (C (forkE e) (C SS (C cN (C lzlBat
      (C (C (A p) (C (A s) (C sur.toNoun (C (listN (fk.map forkE)) (listN (bd.map bondE))))))
        (C comp.door (C G ctx)))))))) lzlG2 = (lfF p s e).map f2N)
    (hB : ∀ e ∈ bd, ∀ FS SS cN : Noun, nock (C lzlG3 (C (bondE e) (C FS (C SS (C cN (C lzlBat
      (C (C (A p) (C (A s) (C sur.toNoun (C (listN (fk.map forkE)) (listN (bd.map bondE))))))
        (C comp.door (C G ctx))))))))) lzlG3 = (lbF p s e).map b2N) :
    nock (C (C sb.toNoun sr.toNoun) (C cutN (C lzlBat
      (C (C (A p) (C (A s) (C sur.toNoun (C (listN (fk.map forkE)) (listN (bd.map bondE))))))
        (C comp.door (C G ctx)))))) lzlR2
      = (fk.mapM (lfF p s)).bind fun fs => (bd.mapM (lbF p s)).map fun bs =>
          lpN (Lazy.lazyPrune (Lazy.mk sb (fs.map Prod.fst) (bs.map Prod.fst)),
            Lazy.lazyPrune (Lazy.mk sr (fs.map Prod.snd) (bs.map Prod.snd))) := by
  have hFk := turn_gate_mapT forkE f2N layer2 homoIn_layer2 lzlG2 (C (C (A 0) lzBunt) (C (A 0) lzBunt))
    (C (C sb.toNoun sr.toNoun) (C cutN (C lzlBat
      (C (C (A p) (C (A s) (C sur.toNoun (C (listN (fk.map forkE)) (listN (bd.map bondE))))))
        (C comp.door (C G ctx)))))) (lfF p s) fk (fun e he => hF e he _ _)
  unfold lzBunt at hFk
  cases e1 : fk.mapM (lfF p s) with
  | none =>
    rw [e1] at hFk
    unfold lzlR2
    simp [nock_exec, hc, turn.arm_at, turn_arm, hFk, buntGate]
  | some fs =>
    rw [e1] at hFk
    have hBd := turn_gate_mapT bondE b2N layer2 homoIn_layer2 lzlG3 (C (A 0) lzBunt)
      (C (listN (fs.map f2N)) (C (C sb.toNoun sr.toNoun) (C cutN (C lzlBat
        (C (C (A p) (C (A s) (C sur.toNoun (C (listN (fk.map forkE)) (listN (bd.map bondE))))))
          (C comp.door (C G ctx)))))))
      (lbF p s) bd (fun e he => hB e he _ _ _)
    unfold lzBunt at hBd
    cases e2 : bd.mapM (lbF p s) with
    | none =>
      rw [e2] at hBd
      unfold lzlR2
      simp [nock_exec, hc, turn.arm_at, turn_arm, hFk, hBd, buntGate]
    | some bs =>
      rw [e2] at hBd
      have hP := lzl_pr hc G lzlBat
        (C (A p) (C (A s) (C sur.toNoun (C (listN (fk.map forkE)) (listN (bd.map bondE)))))) cutN sb sr fs bs
      generalize comp.door = Dr at hP hFk hBd ⊢
      unfold lzlR2
      simp [nock_exec, hc, turn.arm_at, turn_arm, hFk, hBd, buntGate, hP]

/-! ## `+lazy-leap` on every lazy need -/

section
variable (hc : CompIn ctx) (hl : CompLib ctx) (G : Noun) (p s : Nat) (hp : p ≠ 0) (hs : s ≠ 0)
include hc hl hp hs

mutual
/-- `+lazy-leap` on every lazy need whose looks are not `0`, from any block. -/
theorem lzl_all : ∀ (laz : Lazy CSet) (o : Nat), WalkP (fun _ s => CrLok s) o laz →
    nock (C lzlBat (C (C (A p) (C (A s) laz.toNoun)) (C comp.door (C G ctx)))) lzlBat
      = (lazyLeap p s laz).map lpN
  | Lazy.mk sur fk bd, o, ⟨hs0, hfk, hbd⟩ => by
    have hcut := ndc_gate hc hl G sur.ned p
    have hD := ndc_at
    rw [lazyLeap_eq, lazy_toNoun_mk]
    have hr2 := fun sb sr cutN => lzl_r2 hc G p s sur sb sr fk bd cutN
      (fun e he SS cN => lzl_forks fk hfk e he SS cN _) (fun e he FS SS cN => lzl_bonds bd hbd e he FS SS cN _)
    have hsur := fun cut => lzl_sur hc hl G p s hp hs sur (listN (fk.map forkE)) (listN (bd.map bondE)) hs0 cut
    simp only [Sure.toNoun] at hr2 hsur ⊢
    generalize comp.door = Dr at hcut hD hr2 hsur ⊢
    cases e1 : needCut p sur.ned with
    | none =>
      rw [e1] at hcut
      conv => lhs; arg 2; unfold lzlBat
      simp [nock_exec, hD, ndc_arm, hcut]
    | some cut =>
      rw [e1] at hcut
      have hs1 := hsur cut
      cases e2 : lzSur p s sur cut with
      | none =>
        rw [e2] at hs1
        conv => lhs; arg 2; unfold lzlBat
        simp [nock_exec, hD, ndc_arm, hcut, hs1, e2]
      | some ss =>
        obtain ⟨sb, sr⟩ := ss
        rw [e2] at hs1
        conv => lhs; arg 2; unfold lzlBat
        simp [nock_exec, hD, ndc_arm, hcut, hs1, e2, hr2]
        cases fk.mapM (lfF p s) <;> cases bd.mapM (lbF p s) <;> rfl

theorem lzl_forks : ∀ (fk : List (Lazy.ForkE CSet)), WalkPF (fun _ s => CrLok s) fk → ∀ e ∈ fk, ∀ SS cN L : Noun,
    nock (C lzlG2 (C (forkE e) (C SS (C cN (C lzlBat (C (C (A p) (C (A s) L)) (C comp.door (C G ctx))))))))
      lzlG2 = (lfF p s e).map f2N
  | [], _, e, he => absurd he List.not_mem_nil
  | ((oy, y), (on, n)) :: rest, ⟨hy, hn, hr⟩, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro SS cN L
      have ihy := lzl_all y oy hy
      have ihn := lzl_all n on hn
      unfold lzlG2
      cases e1 : lazyLeap p s y with
      | none => rw [e1] at ihy; simp [nock_exec, forkE, ihy, lfF, e1]
      | some yy =>
        rw [e1] at ihy
        cases e2 : lazyLeap p s n with
        | none => rw [e2] at ihn; simp [nock_exec, forkE, ihy, ihn, lfF, e1, e2]
        | some nn => rw [e2] at ihn; simp [nock_exec, forkE, ihy, ihn, lfF, e1, e2, lpN, f2N]
    · exact lzl_forks rest hr e he'

theorem lzl_bonds : ∀ (bd : List (Nat × Lazy CSet)), WalkPB (fun _ s => CrLok s) bd → ∀ e ∈ bd,
    ∀ FS SS cN L : Noun,
    nock (C lzlG3 (C (bondE e) (C FS (C SS (C cN (C lzlBat (C (C (A p) (C (A s) L)) (C comp.door (C G ctx)))))))))
      lzlG3 = (lbF p s e).map b2N
  | [], _, e, he => absurd he List.not_mem_nil
  | (ob, l) :: rest, ⟨hl', hr⟩, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro FS SS cN L
      have ihl := lzl_all l ob hl'
      unfold lzlG3
      cases e1 : lazyLeap p s l with
      | none => rw [e1] at ihl; simp [nock_exec, bondE, ihl, lbF, e1]
      | some bb => rw [e1] at ihl; simp [nock_exec, bondE, ihl, lbF, e1, lpN, b2N]
    · exact lzl_bonds rest hr e he'
end

end

/-- **`+lazy-leap`** is `lazyLeap` on every lazy need whose looks are not
`0`, on positive `p` and `s`, crashes included, in every door core whose
context has layer 2 and `+cons-need` and `+gep` in `K` (`CompLib`). -/
theorem lzl_gate (hc : CompIn ctx) (hl : CompLib ctx) (G : Noun) {p s : Nat} {laz : Lazy CSet}
    (h : LAll CrLok laz) (hp : p ≠ 0) (hs : s ≠ 0) :
    nock (C lzlBat (C (C (A p) (C (A s) laz.toNoun)) (C comp.door (C G ctx)))) lzlBat
      = (lazyLeap p s laz).map (fun x => C x.1.toNoun x.2.toNoun) :=
  lzl_all hc hl G p s hp hs laz 0 h

/-! ## The looks of what `+lazy-leap` returns -/

/-- The fold of `leapLok` keeps the looks positive. -/
theorem llFold_pos {p s : Nat} (hs : s ≠ 0) : ∀ (l : List Nat) (acc : CSet × CSet), (∀ y ∈ l, y ≠ 0) →
    (∀ y ∈ HoonSet.toList acc.1, y ≠ 0) → (∀ y ∈ HoonSet.toList acc.2, y ≠ 0) →
    (∀ y ∈ HoonSet.toList (l.foldl (llStep p s) acc).1, y ≠ 0) ∧
      (∀ y ∈ HoonSet.toList (l.foldl (llStep p s) acc).2, y ≠ 0)
  | [], acc, _, h1, h2 => ⟨h1, h2⟩
  | a :: l, acc, hl, h1, h2 => by
    rw [List.foldl_cons]
    have ha : a ≠ 0 := hl a List.mem_cons_self
    refine llFold_pos hs l _ (fun y hy => hl y (List.mem_cons_of_mem _ hy)) ?_ ?_ <;>
    · unfold llStep
      cases e : (gep p a).join with
      | none =>
        simp only
        first
        | exact h1
        | intro y hy; rcases (HoonSet.mem_put _ _ _).1 hy with rfl | hy; exact ha; exact h2 y hy
      | some d =>
        simp only
        first
        | exact h2
        | intro y hy; rcases (HoonSet.mem_put _ _ _).1 hy with rfl | hy
          · exact pegF_ne hs (gep_join_pos e)
          · exact h1 y hy

theorem leapLok_lok {p s : Nat} {lok lb lr : CSet} (hp : p ≠ 0) (hs : s ≠ 0)
    (h0 : ∀ y ∈ HoonSet.toList lok, y ≠ 0) (h : leapLok p s lok = some (lb, lr)) :
    (∀ y ∈ HoonSet.toList lb, y ≠ 0) ∧ (∀ y ∈ HoonSet.toList lr, y ≠ 0) := by
  rw [leapLok_pos p s lok hp h0, Option.some.injEq] at h
  have := llFold_pos (p := p) hs (HoonSet.toList lok) (HoonSet.empty, HoonSet.empty) h0
    (fun y hy => absurd hy (HoonSet.mem_empty y)) (fun y hy => absurd hy (HoonSet.mem_empty y))
  rw [h] at this
  exact this

theorem lzSur_lok {p s : Nat} (hp : p ≠ 0) (hs : s ≠ 0) {sur sb sr : Sure CSet} {cut : Option (Need × Need)}
    (h0 : CrLok sur) (h : lzSur p s sur cut = some (sb, sr)) : CrLok sb ∧ CrLok sr := by
  cases cut with
  | none =>
    simp only [lzSur, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun y hy => absurd hy (HoonSet.mem_empty y), h0⟩
  | some dr =>
    obtain ⟨don, rec⟩ := dr
    simp only [lzSur] at h
    cases e1 : leapLok p s sur.lok with
    | none => simp [e1] at h
    | some lb =>
      obtain ⟨lb, lr⟩ := lb
      cases e2 : needFrom s don with
      | none => simp [e1, e2] at h
      | some nf =>
        simp only [e1, e2, Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact leapLok_lok hp hs h0 e1

section
variable {p s : Nat} (hp : p ≠ 0) (hs : s ≠ 0)
include hp hs

mutual
theorem lzl_lall_all : ∀ (laz : Lazy CSet) (o : Nat) (b r : Lazy CSet), WalkP (fun _ s => CrLok s) o laz →
    lazyLeap p s laz = some (b, r) → LAll CrLok b ∧ LAll CrLok r
  | Lazy.mk sur fk bd, o, b, r, ⟨hs0, hfk, hbd⟩, h => by
    rw [lazyLeap_eq] at h
    cases e1 : needCut p sur.ned with
    | none => simp [e1] at h
    | some cut =>
      cases e2 : lzSur p s sur cut with
      | none => simp [e1, e2] at h
      | some ss =>
        obtain ⟨sb, sr⟩ := ss
        cases e3 : fk.mapM (lfF p s) with
        | none => simp [e1, e2, e3] at h
        | some fs =>
          cases e4 : bd.mapM (lbF p s) with
          | none => simp [e1, e2, e3, e4] at h
          | some bs =>
            simp only [e1, e2, e3, e4, Option.bind_some, Option.map_some, Option.some.injEq,
              Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hss := lzSur_lok hp hs hs0 e2
            obtain ⟨hf1, hf2⟩ := lzl_lall_forks fk hfk fs e3
            obtain ⟨hb1, hb2⟩ := lzl_lall_bonds bd hbd bs e4
            exact ⟨walkP_prune 0 _ ⟨hss.1, hf1, hb1⟩, walkP_prune 0 _ ⟨hss.2, hf2, hb2⟩⟩

theorem lzl_lall_forks : ∀ (fk : List (Lazy.ForkE CSet)), WalkPF (fun _ s => CrLok s) fk →
    ∀ fs, fk.mapM (lfF p s) = some fs →
    WalkPF (fun _ s => CrLok s) (fs.map Prod.fst) ∧ WalkPF (fun _ s => CrLok s) (fs.map Prod.snd)
  | [], _, fs, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; exact ⟨trivial, trivial⟩
  | ((oy, y), (on, n)) :: rest, ⟨hy, hn, hr⟩, fs, h => by
    simp only [List.mapM_cons] at h
    cases e1 : lazyLeap p s y with
    | none => simp [lfF, e1] at h
    | some yy =>
      obtain ⟨yb, yr⟩ := yy
      cases e2 : lazyLeap p s n with
      | none => simp [lfF, e1, e2] at h
      | some nn =>
        obtain ⟨nb, nr⟩ := nn
        cases e3 : rest.mapM (lfF p s) with
        | none => simp [lfF, e1, e2, e3] at h
        | some rs =>
          simp [lfF, e1, e2, e3] at h
          subst h
          obtain ⟨y1, y2⟩ := lzl_lall_all y oy yb yr hy e1
          obtain ⟨n1, n2⟩ := lzl_lall_all n on nb nr hn e2
          obtain ⟨r1, r2⟩ := lzl_lall_forks rest hr rs e3
          exact ⟨⟨Eq.mp (walkP_irrel CrLok 0 oy yb) y1, Eq.mp (walkP_irrel CrLok 0 on nb) n1, r1⟩,
            ⟨Eq.mp (walkP_irrel CrLok 0 oy yr) y2, Eq.mp (walkP_irrel CrLok 0 on nr) n2, r2⟩⟩

theorem lzl_lall_bonds : ∀ (bd : List (Nat × Lazy CSet)), WalkPB (fun _ s => CrLok s) bd →
    ∀ bs, bd.mapM (lbF p s) = some bs →
    WalkPB (fun _ s => CrLok s) (bs.map Prod.fst) ∧ WalkPB (fun _ s => CrLok s) (bs.map Prod.snd)
  | [], _, bs, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; exact ⟨trivial, trivial⟩
  | (ob, l) :: rest, ⟨hl', hr⟩, bs, h => by
    simp only [List.mapM_cons] at h
    cases e1 : lazyLeap p s l with
    | none => simp [lbF, e1] at h
    | some bb =>
      obtain ⟨lb, lr⟩ := bb
      cases e3 : rest.mapM (lbF p s) with
      | none => simp [lbF, e1, e3] at h
      | some rs =>
        simp [lbF, e1, e3] at h
        subst h
        obtain ⟨l1, l2⟩ := lzl_lall_all l ob lb lr hl' e1
        obtain ⟨r1, r2⟩ := lzl_lall_bonds rest hr rs e3
        exact ⟨⟨Eq.mp (walkP_irrel CrLok 0 ob lb) l1, r1⟩, ⟨Eq.mp (walkP_irrel CrLok 0 ob lr) l2, r2⟩⟩
end

end

/-- What `+lazy-leap` returns looks at no axis `0`. -/
theorem lzl_lall {p s : Nat} (hp : p ≠ 0) (hs : s ≠ 0) {laz b r : Lazy CSet} (hl : LAll CrLok laz)
    (h : lazyLeap p s laz = some (b, r)) : LAll CrLok b ∧ LAll CrLok r :=
  lzl_lall_all hp hs laz 0 b r hl h

end Compiler
end Formalization
