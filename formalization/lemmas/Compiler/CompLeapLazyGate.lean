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

end Compiler
end Formalization
