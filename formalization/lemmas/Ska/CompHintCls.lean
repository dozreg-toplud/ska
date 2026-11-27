import lemmas.Ska.CompHintClsAux
import lemmas.Ska.CompHintClsMean

/-!
# The class of hinted nomms (README Gaps 24.22): the definitions

One computable check `hcV snd f nm` over a formula `f` and the nomm `nm`
compiled from it, by recursion on `nm`, returning a record `HV` with one
field per goal kind (each field is what one family of constructors needs):

* `leaf`: direct-free `CallTreeHU` (hints not kept: a static tag that is not
  `hintStatic`, a dynamic one that is not `hintDynamic` with a `[1 k]` clue), its index `x`;
* `clue`: `NoBondH` by `hcNB` (`[0 a]`, `[1 k]`, `[4 p]`, a cons of those);
* `dall`: `DoneAllT` (a leaf, a kept `stopTag` hint over a leaf, `[7 leaf dall]`);
* `sur`: `SurGBT RegLike` (runs under `%next (ofSure sur)`, `sur` a register);
* `reg`: `RegGBT` (runs under `%next (lazy-from-reg r)`);
* `ft`: `RegFT` (plus the flat result);
* `zc`: a direct call `[2 [0 1] [1 F] b]` in `RegFT` (its result, `directZ_shape`);
* `top`: `DoneG` (runs under `%done`: the contract at the top);
* `sh`: `ShapeH IsReg` with its count of entries (a branch of a `%6`).

The side conditions are decidable checks inside `hcV` (`+sound` through
`snd`, the hint-free test of a `%6`, `sixCount`, `+hinted` with no table).
What is not decidable from the nomm is in two named hypotheses: `HintTab`
(the code table at the callees: `TabOK` of every direct callee, `pure` `|`
of every `%mean` trap with a constant) and `FitH` (the products of the
subject formula of every direct call fit the callee's `less`, at the
subject predicate the path gives it).  The theorem is in
`CompHintClsSound.lean`, the tally on real arms in `CompHintClsTally.lean`.
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-- The fields of the class, one per goal kind. -/
structure HV where
  leaf : Option Bool := Option.none
  clue : Bool := false
  sur : Bool := false
  reg : Bool := false
  ft : Bool := false
  zc : Bool := false
  dall : Bool := false
  top : Bool := false
  sh : Option Nat := Option.none
  deriving Repr, DecidableEq

/-- `+hinted` with no table (a direct call is `~`, `hinted_crash`). -/
def hinted0 (nm : Nomm) : Option Bool := hinted (fun _ => Option.none) nm

/-- **The leaf check**: direct-free `CallTreeHU`, its index. -/
def hcLeaf : Noun → Nomm → Option Bool
  | Noun.cell (Noun.atom 0) (Noun.atom a), Nomm.n0 a' => if a = a' then some true else Option.none
  | Noun.cell (Noun.atom 1) k, Nomm.n1 k' => if k = k' then some true else Option.none
  | Noun.cell (Noun.cell a1 a2) b, Nomm.cons p q =>
      match hcLeaf (Noun.cell a1 a2) p, hcLeaf b q with
      | some x1, some x2 => some (x2 && (x1 || decide (hinted0 q = some true)))
      | _, _ => Option.none
  | Noun.cell (Noun.atom 2) (Noun.cell b c), Nomm.n2 p q Option.none =>
      match hcLeaf b p, hcLeaf c q with
      | some _, some _ => some true
      | _, _ => Option.none
  | Noun.cell (Noun.atom 7) (Noun.cell b c), Nomm.n7 p q =>
      match hcLeaf b p with
      | some true => hcLeaf c q
      | _ => Option.none
  | Noun.cell (Noun.atom 4) b, Nomm.n4 p => (hcLeaf b p).map fun _ => false
  | Noun.cell (Noun.atom 3) b, Nomm.n3 p => (hcLeaf b p).map fun _ => false
  | Noun.cell (Noun.atom 5) (Noun.cell b c), Nomm.n5 p q =>
      match hcLeaf b p, hcLeaf c q with
      | some _, some _ => some false
      | _, _ => Option.none
  | Noun.cell (Noun.atom 11) (Noun.cell (Noun.atom tag') fq), Nomm.n11s tag q _ =>
      if tag = tag' && !hintStatic tag then hcLeaf fq q else Option.none
  | Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom tag') (Noun.cell (Noun.atom 1) k')) fq),
    Nomm.n11d tag (Nomm.n1 k) q _ =>
      if tag = tag' && k = k' && !hintDynamic tag then hcLeaf fq q else Option.none
  | _, _ => Option.none

/-- **`NoBondH` by shape**: `[0 a]`, `[1 k]`, `[4 p]`, a cons of unhinted parts. -/
def hcNB : Nomm → Bool
  | Nomm.n0 _ => true
  | Nomm.n1 _ => true
  | Nomm.n4 p => hcNB p
  | Nomm.cons p q => hcNB p && hcNB q && hinted0 p != some true && hinted0 q != some true
  | _ => false

/-- The value of a leaf: every kind (the `sh` of `[0 a]`, `2 ≤ a`, is `0`). -/
def hvLeaf (x : Bool) (nm : Nomm) : HV :=
  { leaf := some x, sur := true, reg := true, ft := true, dall := true, top := true,
    sh := match nm with
      | Nomm.n0 a => if 2 ≤ a then some 0 else Option.none
      | _ => Option.none }

/-- A kept dynamic hint (or a `%mean` with no constant) over `q` with the
clue `h`: `sur`, `reg`, `top` from `q`'s `sur`, `reg`; `sh` with a `[1 k]` clue. -/
def hvKeptD (snd : Nomm → NeedOrd → Bool) (fh : Noun) (h q : Nomm) (vq : HV) (clue1 stop : Bool) : HV :=
  let ok := (hcLeaf fh h).isSome && hcNB h && snd q NeedOrd.this
  { sur := ok && vq.sur, reg := ok && vq.reg, top := ok && (vq.reg || (stop && vq.dall)),
    dall := ok && stop && vq.leaf.isSome && hcNB q,
    sh := if clue1 && snd q NeedOrd.this then vq.sh.map (· + 1) else Option.none }

/-- The test of a `%6` the class takes: `[0 a]`, `[3 [0 a]]`, `?@` at `a`, with `2 ≤ a`. -/
def hcTest : Noun → Nomm → Bool
  | Noun.cell (Noun.atom 0) (Noun.atom a), Nomm.n0 a' => a = a' && 2 ≤ a
  | Noun.cell (Noun.atom 3) (Noun.cell (Noun.atom 0) (Noun.atom a)), Nomm.n3 (Nomm.n0 a') => a = a' && 2 ≤ a
  | Noun.cell (Noun.atom 6) (Noun.cell (Noun.cell (Noun.atom 3) (Noun.cell (Noun.atom 0) (Noun.atom a)))
      (Noun.cell (Noun.cell (Noun.atom 1) (Noun.atom 1)) (Noun.cell (Noun.atom 1) (Noun.atom 0)))),
    Nomm.n6 (Nomm.n3 (Nomm.n0 a')) (Nomm.n1 (Noun.atom 1)) (Nomm.n1 (Noun.atom 0)) => a = a' && 2 ≤ a
  | _, _ => false

/-- A branch of a `%6`: a constant (count `0`) or a `reg` member with `sh`. -/
def hcBranch (fa : Noun) (a : Nomm) (va : HV) : Option Nat :=
  match fa, a with
  | Noun.cell (Noun.atom 1) k, Nomm.n1 k' => if k = k' then some 0 else Option.none
  | _, _ => if va.reg then va.sh else Option.none

/-- `spotArm`'s `S3` body, `[7 [10 6 [spot [1 k] [0 13]] [0 1]] [2 [0 1] [1 F] b]]`
(`shapeH_s3body`, count 2). -/
def isS3Body : Nomm → Bool
  | Nomm.n7 (Nomm.n10 6 (Nomm.n11d tag (Nomm.n1 _) (Nomm.n0 13) body) (Nomm.n0 1))
      (Nomm.n2 (Nomm.n0 1) (Nomm.n1 _) (some (_, Option.none))) =>
      tag = 1953460339 && body = Noun.cell (Noun.atom 0) (Noun.atom 13)
  | _ => false

/-- `[7 [tag h p'] [4 [0 a]]]` at the top, `a` `2` or `3` (`d13`): a kept
dynamic hint over a hint-free cons (its products are cells), `+sound` of
`p'` at the need of `[0 a]`. -/
def hcTopKF (snd : Nomm → NeedOrd → Bool) : Noun → Nomm → Bool
  | Noun.cell (Noun.atom 7) (Noun.cell (Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom tag') fh)
        (Noun.cell (Noun.cell x y) z))) (Noun.cell (Noun.atom 4) (Noun.cell (Noun.atom 0) (Noun.atom a)))),
    Nomm.n7 (Nomm.n11d tag h p' _) (Nomm.n4 (Nomm.n0 a')) =>
      tag = tag' && hintDynamic tag && a = a' && (a = 2 || a = 3) && (hcLeaf fh h).isSome && hcNB h &&
        (hcLeaf (Noun.cell (Noun.cell x y) z) p').isSome &&
        snd p' (if a = 2 then NeedOrd.pair NeedOrd.this NeedOrd.none else NeedOrd.pair NeedOrd.none NeedOrd.this)
  | _, _ => false

/-- **The class**: the fields of `(f, nm)`, by recursion on `nm`. -/
def hcV (snd : Nomm → NeedOrd → Bool) : Noun → Nomm → HV
  | f, nm@(Nomm.n0 _) => match hcLeaf f nm with | some x => hvLeaf x nm | Option.none => {}
  | f, nm@(Nomm.n1 _) => match hcLeaf f nm with | some x => hvLeaf x nm | Option.none => {}
  | f, nm@(Nomm.cons p q) =>
      match hcLeaf f nm with
      | some x => { hvLeaf x nm with clue := hcNB nm }
      | Option.none => {}
  | f, nm@(Nomm.n5 p q) =>
      match hcLeaf f nm with | some x => hvLeaf x nm | Option.none => {}
  | f, nm@(Nomm.n4 p) =>
      match f with
      | Noun.cell (Noun.atom 4) fb =>
          let vp := hcV snd fb p
          match hcLeaf f nm with
          | some x => hvLeaf x nm
          | Option.none => { sur := vp.reg, reg := vp.reg, top := vp.reg, sh := vp.sh }
      | _ => {}
  | f, nm@(Nomm.n3 p) =>
      match f with
      | Noun.cell (Noun.atom 3) fb =>
          let vp := hcV snd fb p
          match hcLeaf f nm with
          | some x => hvLeaf x nm
          | Option.none => { sur := vp.reg, reg := vp.reg }
      | _ => {}
  | f, nm@(Nomm.n2 p q info) =>
      match f with
      | Noun.cell (Noun.atom 2) (Noun.cell fb fq) =>
          let vp := hcV snd fb p
          match info with
          | Option.none => match hcLeaf f nm with | some x => hvLeaf x nm | Option.none => {}
          | some (b, Option.none) =>
              let ok := (hcLeaf fb p).isSome && safeFolFol q && decide (sixCount nm ≤ 255) &&
                (match fq, q with
                  | Noun.cell (Noun.atom 1) F, Nomm.n1 F' => F = F' && F = b.fol
                  | _, _ => false)
              { ft := ok, reg := ok, zc := ok && (match p with | Nomm.n0 1 => true | _ => false) }
          | some (_, some _) => {}
      | _ => {}
  | f, nm@(Nomm.n7 p q) =>
      match f with
      | Noun.cell (Noun.atom 7) (Noun.cell b c) =>
          let vp := hcV snd b p
          let vq := hcV snd c q
          match hcLeaf f nm with
          | some x => hvLeaf x nm
          | Option.none =>
              match p, b with
              | Nomm.n0 1, Noun.cell (Noun.atom 0) (Noun.atom 1) =>
                  { sur := vq.sur, reg := vq.reg || vq.ft, ft := vq.ft, top := vq.top }
              | _, _ =>
                  let ft := hcLeaf b p == some true && vq.ft
                  let da := hcLeaf b p == some true && vq.dall
                  { ft := ft, reg := ft || (vp.sur && vq.zc), dall := da, top := da || hcTopKF snd f nm,
                    sh := if isS3Body nm && snd (Nomm.n0 13) NeedOrd.this then some 2 else Option.none }
      | _ => {}
  | f, nm@(Nomm.n10 a v q) =>
      match f with
      | Noun.cell (Noun.atom 10) (Noun.cell (Noun.cell (Noun.atom a') fv) fq) =>
          let vv := hcV snd fv v
          let ok := a = a' && 2 ≤ a && hinted (fun _ => Option.none) v == some true &&
            (match q, fq with
              | Nomm.n0 1, Noun.cell (Noun.atom 0) (Noun.atom 1) => true
              | _, _ => false) && vv.sur
          { sur := ok, reg := ok, top := ok }
      | _ => {}
  | f, nm@(Nomm.n6 c a b) =>
      match f with
      | Noun.cell (Noun.atom 6) (Noun.cell fc (Noun.cell fa fb)) =>
          let va := hcV snd fa a
          let vb := hcV snd fb b
          match hcBranch fa a va, hcBranch fb b vb with
          | some ka, some kb =>
              { reg := hcTest fc c && decide (5 + ka + kb ≤ lazyMax) && decide (sixCount nm ≤ 255) }
          | _, _ => {}
      | _ => {}
  | f, nm@(Nomm.n11s tag q body) =>
      match hcLeaf f nm with
      | some x => hvLeaf x nm
      | Option.none =>
      match f with
      | Noun.cell (Noun.atom 11) (Noun.cell (Noun.atom tag') fq) =>
          let vq := hcV snd fq q
          let ok := tag = tag' && hintStatic tag && snd q NeedOrd.this
          { sur := ok && vq.sur, reg := ok && vq.reg, top := ok && vq.reg }
      | _ => {}
  | f, nm@(Nomm.n11d tag h q _) =>
      match hcLeaf f nm with
      | some x => hvLeaf x nm
      | Option.none =>
      match f with
      | Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom tag') fh) fq) =>
          let vq := hcV snd fq q
          if tag = tag' && hintDynamic tag then
            hvKeptD snd fh h q vq (match h with | Nomm.n1 _ => true | _ => false) (stopTag tag)
          else {}
      | _ => {}
  | f, Nomm.mean p _ q _ _ =>
      match f with
      | Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom tag') fp) fq) =>
          let vq := hcV snd fq q
          if tag' = Tag.mean then { hvKeptD snd fp p q vq false false with dall := false } else {}
      | _ => {}
  | _, Nomm.n12 _ _ => {}

/-- The bells of the direct calls, anywhere. -/
def callBells : Nomm → List Bell
  | Nomm.cons p q => callBells p ++ callBells q
  | Nomm.n2 p q info => (match info with | some (b, _) => [b] | Option.none => []) ++ callBells p ++ callBells q
  | Nomm.n3 p => callBells p
  | Nomm.n4 p => callBells p
  | Nomm.n5 p q => callBells p ++ callBells q
  | Nomm.n6 p q r => callBells p ++ callBells q ++ callBells r
  | Nomm.n7 p q => callBells p ++ callBells q
  | Nomm.n10 _ v q => callBells v ++ callBells q
  | Nomm.n11s _ q _ => callBells q
  | Nomm.n11d _ h q _ => callBells h ++ callBells q
  | Nomm.n12 p q => callBells p ++ callBells q
  | Nomm.mean p _ q _ _ => callBells p ++ callBells q
  | _ => []

/-- The traps of the `%mean`s with a constant. -/
def meanBells : Nomm → List Bell
  | Nomm.cons p q => meanBells p ++ meanBells q
  | Nomm.n2 p q _ => meanBells p ++ meanBells q
  | Nomm.n3 p => meanBells p
  | Nomm.n4 p => meanBells p
  | Nomm.n5 p q => meanBells p ++ meanBells q
  | Nomm.n6 p q r => meanBells p ++ meanBells q ++ meanBells r
  | Nomm.n7 p q => meanBells p ++ meanBells q
  | Nomm.n10 _ v q => meanBells v ++ meanBells q
  | Nomm.n11s _ q _ => meanBells q
  | Nomm.n11d _ h q _ => meanBells h ++ meanBells q
  | Nomm.n12 p q => meanBells p ++ meanBells q
  | Nomm.mean p b q _ k => (if k.isSome then [b] else []) ++ meanBells p ++ meanBells q
  | _ => []

/-- The table entry of a direct callee, as `regFT_direct` asks it. -/
def TabOK (env : CallEnv) (N : Needs) (b : Bell) : Prop :=
  env.ring b = Option.none ∧ (∃ bNed, env.need b = some bNed ∧ N b false = some bNed) ∧
    (∃ ndT, N b true = some ndT) ∧ env.pure b = false

/-- **The hypothesis on the code table.** -/
def HintTab (env : CallEnv) (N : Needs) (nm : Nomm) : Prop :=
  (∀ b ∈ callBells nm, TabOK env N b) ∧ (∀ b ∈ meanBells nm, env.pure b = false)

/-- **The fit of the callees' `less`**: at every direct call, the products
of its subject formula on the subjects the path gives it fit the callee's
`less` (the premise `hAp` of `regFT_direct`); `q` of a `%7` at `Img lib P b`. -/
def FitH (lib : Lib) : (Noun → Prop) → Noun → Nomm → Prop
  | P, Noun.cell (Noun.atom 7) (Noun.cell b c), Nomm.n7 p q => FitH lib P b p ∧ FitH lib (Img lib P b) c q
  | P, Noun.cell (Noun.atom 2) (Noun.cell fb _), Nomm.n2 p _ (some (bl, _)) =>
      (∀ x gul y, P x → Mink lib gul [] x fb (Tone.zero y) → SkaModel.Fits bl.less y) ∧ FitH lib P fb p
  | P, Noun.cell (Noun.atom 10) (Noun.cell (Noun.cell _ fv) _), Nomm.n10 _ v _ => FitH lib P fv v
  | P, Noun.cell (Noun.atom 11) (Noun.cell _ fq), Nomm.n11s _ q _ => FitH lib P fq q
  | P, Noun.cell (Noun.atom 11) (Noun.cell _ fq), Nomm.n11d _ _ q _ => FitH lib P fq q
  | P, Noun.cell (Noun.atom 11) (Noun.cell _ fq), Nomm.mean _ _ q _ _ => FitH lib P fq q
  | P, Noun.cell (Noun.atom 4) fb, Nomm.n4 p => FitH lib P fb p
  | P, Noun.cell (Noun.atom 3) fb, Nomm.n3 p => FitH lib P fb p
  | P, Noun.cell (Noun.atom 6) (Noun.cell _ (Noun.cell fa fb)), Nomm.n6 _ a b => FitH lib P fa a ∧ FitH lib P fb b
  | _, _, _ => True

end Comp
end SkaModel
end Formalization
