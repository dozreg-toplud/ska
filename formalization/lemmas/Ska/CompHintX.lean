import lemmas.Ska.CompHintW

/-!
# The class `hcX`: the inlined call (README Gaps 24.24), the definitions

`hcX snd bat f nm` is `hcW snd f nm` (`CompHintW.lean`, unchanged) with one
more argument, `bat` (what the check knows of the subject: the formula at
an axis, from the bell's `less`), passed to every part that runs on the
same subject (`noBat` under a `%7` whose subject formula is not `[0 1]`),
and these rules more:

* **the inlined call**: the formula `[2 [0 1] [0 a]]` with the nomm
  `[7 [0 1] X]` (`Annot.inline`: the arm is inlined), `bat a = some F`:
  `X` is checked against `F`; its fields pass through the `[0 1]`
  (`hw01`: `+mink` runs the formula as `F` on the subjects whose axis `a`
  is `F`, `BatOK`);
* **`[9 a [0 1]]` with the nomm `[7 [0 1] q]`**: the fields of `hw7G`, or
  those of `q` through the `[0 1]` (`hwOr`, `hw01`);
* `[7 [0 1] c]`: `hw01` (the rule of `hcW`, and `dall`);
* **`ShapeH` `0` of every `hcNB` leaf** (`hwLeafX`; a `%6` branch that is a
  cons of fragments).

The hypotheses: `HintTabW` (unchanged), `FitHX` (the facts of `FitHW`, and
at an inlined call those of `X` against `F`), `BatOK` (what `bat` says
holds of every subject: the glue's `Fits bl.less` gives it, `batOK_less`).
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-- What the check knows of the subject's battery: the formula at an axis. -/
abbrev Bat := Nat → Option Noun

/-- Nothing known. -/
def noBat : Bat := fun _ => Option.none

/-- `bat` for the subject made by the formula `b`: `bat` itself when `b` is `[0 1]`. -/
def batAt (bat : Bat) (b : Noun) : Bat := if b = Noun.cell (Noun.atom 0) (Noun.atom 1) then bat else noBat

/-- **What `bat` says holds of every subject of `P`.** -/
def BatOK (bat : Bat) (P : Noun → Prop) : Prop := ∀ a F, bat a = some F → ∀ s, P s → slot? a s = some F

/-- The fields of `[7 [0 1] q]` from those of `q` (the run is that of `q`, `runLCH_seven01`). -/
def hw01 (vq : HW) : HW := { sur := vq.sur, reg := vq.reg || vq.ft, ft := vq.ft, dall := vq.dall, top := vq.top }

/-- A leaf: `hwLeaf`, and `sh` `0` of every `hcNB` leaf (`clue_tagShapeW`: no entry). -/
def hwLeafX (x : Bool) (f : Noun) (nm : Nomm) : HW :=
  { hwLeaf x f nm with sh := (hwLeaf x f nm).sh.or (if hcNB nm then some 0 else Option.none) }

/-- Either set of fields. -/
def hwOr (v w : HW) : HW :=
  { leaf := v.leaf.or w.leaf, clue := v.clue || w.clue, sur := v.sur || w.sur, reg := v.reg || w.reg,
    ft := v.ft || w.ft, zc := v.zc || w.zc, dall := v.dall || w.dall, top := v.top || w.top,
    sh := v.sh.or w.sh, st := v.st.or w.st }

/-- **The class `hcX`**: the rules of `hcW` (with `bat` passed to the parts on the same subject)
and the inlined call; the fields of `(f, nm)`, by recursion on `nm`. -/
def hcX (snd : Nomm → NeedOrd → Bool) (bat : Bat) : Noun → Nomm → HW
  | f, nm@(Nomm.n0 _) => match hcLeaf f nm with | some x => hwLeafX x f nm | Option.none => {}
  | f, nm@(Nomm.n1 k) => match hcLeaf f nm with
      | some x => hwLeafX x f nm
      | Option.none => if hcDropK f k then hwDrop else {}
  | f, nm@(Nomm.cons p q) =>
      match hcLeaf f nm with
      | some x => { hwLeafX x f nm with clue := hcNB nm }
      | Option.none => {}
  | f, nm@(Nomm.n5 p q) =>
      match hcLeaf f nm with | some x => hwLeafX x f nm | Option.none => {}
  | f, nm@(Nomm.n4 p) =>
      match f with
      | Noun.cell (Noun.atom 4) fb =>
          let vp := hcX snd bat fb p
          match hcLeaf f nm with
          | some x => { hwLeafX x f nm with sh := vp.sh.or (hwLeafX x f nm).sh }
          | Option.none => { sur := vp.reg, reg := vp.reg, top := vp.reg, sh := vp.sh }
      | _ => {}
  | f, nm@(Nomm.n3 p) =>
      match f with
      | Noun.cell (Noun.atom 3) fb =>
          let vp := hcX snd bat fb p
          match hcLeaf f nm with
          | some x => hwLeafX x f nm
          | Option.none => { sur := vp.reg, reg := vp.reg }
      | _ => {}
  | f, nm@(Nomm.n2 p q info) =>
      match f with
      | Noun.cell (Noun.atom 2) (Noun.cell fb fq) =>
          let vp := hcX snd bat fb p
          match info with
          | Option.none => match hcLeaf f nm with | some x => hwLeafX x f nm | Option.none => {}
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
          match hcLeaf f nm with
          | some x => hwLeafX x f nm
          | Option.none =>
              match p, b with
              | Nomm.n0 1, Noun.cell (Noun.atom 0) (Noun.atom 1) => hw01 (hcX snd bat c q)
              | _, _ => hw7G snd f nm b p (hcX snd bat b p) (hcX snd (batAt bat b) c q)
      | Noun.cell (Noun.atom 9) (Noun.cell (Noun.atom a) c) =>
          match p, c with
          | Nomm.n0 1, Noun.cell (Noun.atom 0) (Noun.atom 1) =>
              hwOr (hw7G snd f nm c p (hcX snd bat c p) (hcX snd bat (Noun.cell (Noun.atom 2)
                  (Noun.cell (Noun.cell (Noun.atom 0) (Noun.atom 1)) (Noun.cell (Noun.atom 0) (Noun.atom a)))) q))
                (hw01 (hcX snd bat (Noun.cell (Noun.atom 2) (Noun.cell (Noun.cell (Noun.atom 0) (Noun.atom 1))
                  (Noun.cell (Noun.atom 0) (Noun.atom a)))) q))
          | _, _ =>
              hw7G snd f nm c p (hcX snd bat c p)
                (hcX snd (batAt bat c) (Noun.cell (Noun.atom 2) (Noun.cell (Noun.cell (Noun.atom 0) (Noun.atom 1))
                  (Noun.cell (Noun.atom 0) (Noun.atom a)))) q)
      | Noun.cell (Noun.atom 8) (Noun.cell (Noun.cell a1 a2) c) =>
          let b := Noun.cell (Noun.cell a1 a2) (Noun.cell (Noun.atom 0) (Noun.atom 1))
          hw7G snd f nm b p (hcX snd bat b p) (hcX snd noBat c q)
      | Noun.cell (Noun.atom 2) (Noun.cell (Noun.cell (Noun.atom 0) (Noun.atom 1)) (Noun.cell (Noun.atom 0) (Noun.atom a))) =>
          match p, bat a with
          | Nomm.n0 1, some F => hw01 (hcX snd bat F q)
          | _, _ => {}
      | _ => {}
  | f, nm@(Nomm.n10 a v q) =>
      match f with
      | Noun.cell (Noun.atom 10) (Noun.cell (Noun.cell (Noun.atom a') fv) fq) =>
          let vv := hcX snd bat fv v
          let ok := a = a' && 2 ≤ a && hinted (fun _ => Option.none) v == some true &&
            (match q, fq with
              | Nomm.n0 1, Noun.cell (Noun.atom 0) (Noun.atom 1) => true
              | _, _ => false) && vv.sur
          { sur := ok, reg := ok, top := ok }
      | _ => {}
  | f, nm@(Nomm.n6 c a b) =>
      match f with
      | Noun.cell (Noun.atom 6) (Noun.cell fc (Noun.cell fa fb)) =>
          let va := hcX snd bat fa a
          let vb := hcX snd bat fb b
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
      | some x => hwLeafX x f nm
      | Option.none =>
      match f with
      | Noun.cell (Noun.atom 11) (Noun.cell (Noun.atom tag') fq) =>
          let vq := hcX snd bat fq q
          let ok := tag = tag' && hintStatic tag && snd q NeedOrd.this
          { sur := ok && vq.sur, reg := ok && vq.reg, top := ok && vq.reg }
      | _ => {}
  | f, nm@(Nomm.n11d tag h q _) =>
      match hcLeaf f nm with
      | some x => hwLeafX x f nm
      | Option.none =>
      match f with
      | Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom tag') fh) fq) =>
          let vq := hcX snd bat fq q
          if tag = tag' && hintDynamic tag then hwKeptD snd fh h q vq (stopTag tag) else {}
      | _ => {}
  | f, Nomm.mean p _ q _ _ =>
      match f with
      | Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom tag') fp) fq) =>
          let vq := hcX snd bat fq q
          if tag' = Tag.mean then hwKeptD snd fp p q vq false else {}
      | _ => {}
  | _, Nomm.n12 _ _ => {}

/-- **`FitHW` for `hcX`**: the same facts, with `bat` as `hcX` passes it,
and at an inlined call the facts of `X` against `F`. -/
def FitHX (lib : Lib) (env : CallEnv) : Bat → (Noun → Prop) → Noun → Nomm → Prop
  | bat, P, Noun.cell (Noun.atom 7) (Noun.cell b c), Nomm.n7 p q =>
      FitHX lib env bat P b p ∧
        FitHX lib env (batAt bat b) (Img lib P b) c q
  | bat, P, Noun.cell (Noun.atom 9) (Noun.cell (Noun.atom a) c), Nomm.n7 p q =>
      FitHX lib env bat P c p ∧
        FitHX lib env (batAt bat c) (Img lib P c)
          (n3 (A 2) (slot 1) (slot a)) q
  | bat, P, Noun.cell (Noun.atom 8) (Noun.cell (Noun.cell a1 a2) c), Nomm.n7 p q =>
      FitHX lib env bat P (C (C a1 a2) (slot 1)) p ∧ FitHX lib env noBat (Img lib P (C (C a1 a2) (slot 1))) c q
  | bat, P, Noun.cell (Noun.atom 2) (Noun.cell (Noun.cell (Noun.atom 0) (Noun.atom 1))
      (Noun.cell (Noun.atom 0) (Noun.atom a))), Nomm.n7 _ q =>
      ∀ F, bat a = some F → FitHX lib env bat P F q
  | bat, P, Noun.cell (Noun.atom 2) (Noun.cell fb fq), Nomm.n2 p _ (some (bl, _)) =>
      (∀ x gul y, P x → Mink lib gul [] x fb (Tone.zero y) → SkaModel.Fits bl.less y) ∧ FitHX lib env bat P fb p ∧
        (∀ a, fq = slot a → ∀ s, P s → slot? a s = some bl.fol)
  | bat, P, Noun.cell (Noun.atom 10) (Noun.cell (Noun.cell _ fv) _), Nomm.n10 _ v _ => FitHX lib env bat P fv v
  | bat, P, Noun.cell (Noun.atom 11) (Noun.cell _ fq), Nomm.n11s _ q _ => FitHX lib env bat P fq q
  | bat, P, Noun.cell (Noun.atom 11) (Noun.cell _ fq), Nomm.n11d _ _ q _ => FitHX lib env bat P fq q
  | bat, P, Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell _ fp) fq), Nomm.mean _ b q _ k =>
      FitHX lib env bat P fq q ∧ ∀ n, meanKonst env b k = some n →
        ∀ {s gul : Noun} {tm : Trace} {trap : Noun}, P s → Mink lib gul tm s fp (Tone.zero trap) → MackRel lib trap n
  | bat, P, Noun.cell (Noun.atom 4) fb, Nomm.n4 p => FitHX lib env bat P fb p
  | bat, P, Noun.cell (Noun.atom 3) fb, Nomm.n3 p => FitHX lib env bat P fb p
  | bat, P, Noun.cell (Noun.atom 6) (Noun.cell _ (Noun.cell fa fb)), Nomm.n6 _ a b =>
      FitHX lib env bat P fa a ∧ FitHX lib env bat P fb b
  | _, _, _, _ => True

end Comp
end SkaModel
end Formalization
