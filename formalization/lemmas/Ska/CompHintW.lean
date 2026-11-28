import lemmas.Ska.CompHintCls
import lemmas.Ska.CompHintWMeanK
import lemmas.Ska.CompHintWShape
import lemmas.Ska.CompHintWSix

/-!
# The wider class of hinted nomms (README Gaps 24.23): the definitions

`hcW snd f nm` is `hcV snd f nm` (`CompHintCls.lean`, unchanged) with the
record `HW`: the fields of `HV` and one more, `st` (`SixTopD`: the run
under `%done` with a bound on its entries, what a branch of a `%6` at the
top asks), and these rules more:

* **the `%mean` with a constant** (`meanKonst = some`, the pure trap of
  `%hcp`/`%hce`): the check is the one of the `%mean` with no constant
  (the trap a leaf with `hcNB`, `+sound` of `%this` for the formula), the
  proof splits on `meanKonst` (`regGBT_meanK`, `surGBT_meanK`,
  `doneNext_meanK`, `shapeH_meanK`); the frame `(%meac, n)` stands for
  `(%mean, trap)` by the hypothesis `FitHW` gives at the `%mean` (the
  `konst` field of `MeanOK`: `+mack` of every trap is `n`), so `HintTabW`
  no longer asks the trap impure;
* **the direct call at the top** (`dall`, `top`: `tailP_doneMH`, a tail call);
* **`%6` at the top** (`st`, `top`: `sixTopD_six`), the test a pure
  fragment (`sixTopLeafB true`), each branch with `st`: a pure fragment
  (`sixTopD_leaf`), a member of `reg` with `sh` whose `%done` run is the
  `%next` one (`sixTopD_of_next`: kept dynamic hints, `%mean`), a `%6`;
* **`ShapeH`** of a kept dynamic hint or a `%mean` whose clue is in `hcNB`
  (`shapeH_n11dLeafShapeW`, `shapeH_meanLeafShapeW`, `shapeH_meanK`), of
  the `S3` body at any axis (`isS3BodyShapeW`), of a `[4 p]` leaf (`p`'s).

The hypotheses: `HintTabW` (`TabOK` of every direct callee) and `FitHW`
(`FitH`'s facts and, at a `%mean` with a constant, `+mack` of the traps).
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-- The fields of the wider class: `HV`'s and `st`. -/
structure HW where
  leaf : Option Bool := Option.none
  clue : Bool := false
  sur : Bool := false
  reg : Bool := false
  ft : Bool := false
  zc : Bool := false
  dall : Bool := false
  top : Bool := false
  sh : Option Nat := Option.none
  st : Option Nat := Option.none
  deriving Repr, DecidableEq

/-- A leaf: every kind; `sh` of `[0 a]`, `2 ≤ a`; `st` of a pure fragment. -/
def hwLeaf (x : Bool) (f : Noun) (nm : Nomm) : HW :=
  { leaf := some x, sur := true, reg := true, ft := true, dall := true, top := true,
    sh := match nm with
      | Nomm.n0 a => if 2 ≤ a then some 0 else Option.none
      | _ => Option.none,
    st := if sixTopLeafB false f nm then some 0 else Option.none }

/-- A kept dynamic hint, or a `%mean` (`stop` `|`), over `q` with the clue `h`. -/
def hwKeptD (snd : Nomm → NeedOrd → Bool) (fh : Noun) (h q : Nomm) (vq : HW) (stop : Bool) : HW :=
  let ok := (hcLeaf fh h).isSome && hcNB h && snd q NeedOrd.this
  let sh := if hcNB h && snd q NeedOrd.this then vq.sh.map (· + 1) else Option.none
  { sur := ok && vq.sur, reg := ok && vq.reg, top := ok && vq.reg,
    dall := ok && stop && vq.leaf.isSome && hcNB q,
    sh := sh, st := if ok && vq.reg then sh else Option.none }

/-- A branch of a `%6` (`hcBranch` on `HW`). -/
def hwBranch (fa : Noun) (a : Nomm) (va : HW) : Option Nat :=
  match fa, a with
  | Noun.cell (Noun.atom 1) k, Nomm.n1 k' => if k = k' then some 0 else Option.none
  | _, Nomm.n1 k' => if hcDropK fa k' then some 0 else Option.none
  | _, _ => if va.reg then va.sh else Option.none

/-- `hv7G` on `HW`, `sh` of the `S3` body at any axis. -/
def hw7G (snd : Nomm → NeedOrd → Bool) (f : Noun) (nm : Nomm) (b : Noun) (p : Nomm) (vp vq : HW) : HW :=
  let ft := hcLeaf b p == some true && vq.ft
  let da := hcLeaf b p == some true && vq.dall
  { ft := ft, reg := ft || (vp.sur && vq.zc), dall := da, top := da || hcTopKF snd f nm,
    sh := if isS3BodyShapeW snd nm then some 2 else Option.none }

/-- A dropped hint over a constant. -/
def hwDrop : HW := { sur := true, reg := true, ft := true, dall := true, top := true }

/-- **The wider class**: the fields of `(f, nm)`, by recursion on `nm`. -/
def hcW (snd : Nomm → NeedOrd → Bool) : Noun → Nomm → HW
  | f, nm@(Nomm.n0 _) => match hcLeaf f nm with | some x => hwLeaf x f nm | Option.none => {}
  | f, nm@(Nomm.n1 k) => match hcLeaf f nm with
      | some x => hwLeaf x f nm
      | Option.none => if hcDropK f k then hwDrop else {}
  | f, nm@(Nomm.cons p q) =>
      match hcLeaf f nm with
      | some x => { hwLeaf x f nm with clue := hcNB nm }
      | Option.none => {}
  | f, nm@(Nomm.n5 p q) =>
      match hcLeaf f nm with | some x => hwLeaf x f nm | Option.none => {}
  | f, nm@(Nomm.n4 p) =>
      match f with
      | Noun.cell (Noun.atom 4) fb =>
          let vp := hcW snd fb p
          match hcLeaf f nm with
          | some x => { hwLeaf x f nm with sh := vp.sh }
          | Option.none => { sur := vp.reg, reg := vp.reg, top := vp.reg, sh := vp.sh }
      | _ => {}
  | f, nm@(Nomm.n3 p) =>
      match f with
      | Noun.cell (Noun.atom 3) fb =>
          let vp := hcW snd fb p
          match hcLeaf f nm with
          | some x => hwLeaf x f nm
          | Option.none => { sur := vp.reg, reg := vp.reg }
      | _ => {}
  | f, nm@(Nomm.n2 p q info) =>
      match f with
      | Noun.cell (Noun.atom 2) (Noun.cell fb fq) =>
          let vp := hcW snd fb p
          match info with
          | Option.none => match hcLeaf f nm with | some x => hwLeaf x f nm | Option.none => {}
          | some (b, Option.none) =>
              let ok := (hcLeaf fb p).isSome && safeFolFol q && decide (sixCount nm ≤ 255) &&
                (match fq, q with
                  | Noun.cell (Noun.atom 1) F, Nomm.n1 F' => F = F' && F = b.fol
                  | Noun.cell (Noun.atom 0) (Noun.atom _), Nomm.n1 F' => F' = b.fol
                  | _, _ => false)
              { ft := ok, reg := ok, zc := ok && (match p with | Nomm.n0 1 => true | _ => false),
                dall := ok, top := ok }
          | some (_, some _) => {}
      | _ => {}
  | f, nm@(Nomm.n7 p q) =>
      match f with
      | Noun.cell (Noun.atom 7) (Noun.cell b c) =>
          let vp := hcW snd b p
          let vq := hcW snd c q
          match hcLeaf f nm with
          | some x => hwLeaf x f nm
          | Option.none =>
              match p, b with
              | Nomm.n0 1, Noun.cell (Noun.atom 0) (Noun.atom 1) =>
                  { sur := vq.sur, reg := vq.reg || vq.ft, ft := vq.ft, top := vq.top }
              | _, _ => hw7G snd f nm b p vp vq
      | Noun.cell (Noun.atom 9) (Noun.cell (Noun.atom a) c) =>
          hw7G snd f nm c p (hcW snd c p)
            (hcW snd (Noun.cell (Noun.atom 2) (Noun.cell (Noun.cell (Noun.atom 0) (Noun.atom 1))
              (Noun.cell (Noun.atom 0) (Noun.atom a)))) q)
      | Noun.cell (Noun.atom 8) (Noun.cell (Noun.cell a1 a2) c) =>
          let b := Noun.cell (Noun.cell a1 a2) (Noun.cell (Noun.atom 0) (Noun.atom 1))
          hw7G snd f nm b p (hcW snd b p) (hcW snd c q)
      | _ => {}
  | f, nm@(Nomm.n10 a v q) =>
      match f with
      | Noun.cell (Noun.atom 10) (Noun.cell (Noun.cell (Noun.atom a') fv) fq) =>
          let vv := hcW snd fv v
          let ok := a = a' && 2 ≤ a && hinted (fun _ => Option.none) v == some true &&
            (match q, fq with
              | Nomm.n0 1, Noun.cell (Noun.atom 0) (Noun.atom 1) => true
              | _, _ => false) && vv.sur
          { sur := ok, reg := ok, top := ok }
      | _ => {}
  | f, nm@(Nomm.n6 c a b) =>
      match f with
      | Noun.cell (Noun.atom 6) (Noun.cell fc (Noun.cell fa fb)) =>
          let va := hcW snd fa a
          let vb := hcW snd fb b
          let reg := match hwBranch fa a va, hwBranch fb b vb with
            | some ka, some kb => hcTest fc c && decide (5 + ka + kb ≤ lazyMax) && decide (sixCount nm ≤ 255)
            | _, _ => false
          let st := match va.st, vb.st with
            | some ka, some kb =>
                if sixTopLeafB true fc c && decide (ka + kb + 5 ≤ lazyMax) then some (0 + ka + kb + 4)
                else Option.none
            | _, _ => Option.none
          { reg := reg, top := st.isSome, st := st }
      | _ => {}
  | f, nm@(Nomm.n11s tag q body) =>
      match hcLeaf f nm with
      | some x => hwLeaf x f nm
      | Option.none =>
      match f with
      | Noun.cell (Noun.atom 11) (Noun.cell (Noun.atom tag') fq) =>
          let vq := hcW snd fq q
          let ok := tag = tag' && hintStatic tag && snd q NeedOrd.this
          { sur := ok && vq.sur, reg := ok && vq.reg, top := ok && vq.reg }
      | _ => {}
  | f, nm@(Nomm.n11d tag h q _) =>
      match hcLeaf f nm with
      | some x => hwLeaf x f nm
      | Option.none =>
      match f with
      | Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom tag') fh) fq) =>
          let vq := hcW snd fq q
          if tag = tag' && hintDynamic tag then hwKeptD snd fh h q vq (stopTag tag) else {}
      | _ => {}
  | f, Nomm.mean p _ q _ _ =>
      match f with
      | Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom tag') fp) fq) =>
          let vq := hcW snd fq q
          if tag' = Tag.mean then hwKeptD snd fp p q vq false else {}
      | _ => {}
  | _, Nomm.n12 _ _ => {}

/-- **The hypothesis on the code table**: `TabOK` of every direct callee
(the traps of `%mean` are not asked impure any more). -/
def HintTabW (env : CallEnv) (N : Needs) (nm : Nomm) : Prop := ∀ b ∈ callBells nm, TabOK env N b

/-- **`FitH` with the constants of `%mean`**: at a `%mean` whose constant
`+mean-konst` keeps, `+mack` of every trap the trap formula makes is the
constant (the `konst` field of `MeanOK`, from the analysis). -/
def FitHW (lib : Lib) (env : CallEnv) : (Noun → Prop) → Noun → Nomm → Prop
  | P, Noun.cell (Noun.atom 7) (Noun.cell b c), Nomm.n7 p q => FitHW lib env P b p ∧ FitHW lib env (Img lib P b) c q
  | P, Noun.cell (Noun.atom 9) (Noun.cell (Noun.atom a) c), Nomm.n7 p q =>
      FitHW lib env P c p ∧ FitHW lib env (Img lib P c) (n3 (A 2) (slot 1) (slot a)) q
  | P, Noun.cell (Noun.atom 8) (Noun.cell (Noun.cell a1 a2) c), Nomm.n7 p q =>
      FitHW lib env P (C (C a1 a2) (slot 1)) p ∧ FitHW lib env (Img lib P (C (C a1 a2) (slot 1))) c q
  | P, Noun.cell (Noun.atom 2) (Noun.cell fb fq), Nomm.n2 p _ (some (bl, _)) =>
      (∀ x gul y, P x → Mink lib gul [] x fb (Tone.zero y) → SkaModel.Fits bl.less y) ∧ FitHW lib env P fb p ∧
        (∀ a, fq = slot a → ∀ s, P s → slot? a s = some bl.fol)
  | P, Noun.cell (Noun.atom 10) (Noun.cell (Noun.cell _ fv) _), Nomm.n10 _ v _ => FitHW lib env P fv v
  | P, Noun.cell (Noun.atom 11) (Noun.cell _ fq), Nomm.n11s _ q _ => FitHW lib env P fq q
  | P, Noun.cell (Noun.atom 11) (Noun.cell _ fq), Nomm.n11d _ _ q _ => FitHW lib env P fq q
  | P, Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell _ fp) fq), Nomm.mean _ b q _ k =>
      FitHW lib env P fq q ∧ ∀ n, meanKonst env b k = some n →
        ∀ {s gul : Noun} {tm : Trace} {trap : Noun}, P s → Mink lib gul tm s fp (Tone.zero trap) → MackRel lib trap n
  | P, Noun.cell (Noun.atom 4) fb, Nomm.n4 p => FitHW lib env P fb p
  | P, Noun.cell (Noun.atom 3) fb, Nomm.n3 p => FitHW lib env P fb p
  | P, Noun.cell (Noun.atom 6) (Noun.cell _ (Noun.cell fa fb)), Nomm.n6 _ a b => FitHW lib env P fa a ∧ FitHW lib env P fb b
  | _, _, _ => True

end Comp
end SkaModel
end Formalization
