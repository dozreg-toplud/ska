import lemmas.Ska.SccLoopReal
import lemmas.Ska.RunShape

/-! # The sweeps' compile of a member: `RealCfg.laze` from track A's `+run-shape` (README Gaps 21.18)

`RealCfg.laze mode env m` (`Ska/SccLoopReal.lean`) is `(collapsed, sur)` of the branch `?.  done`
of `member` (lines 3524 to 3533 of `desk/lib/nock-compilation.hoon`):

    =^  l=laze  gen  (~(run-shape comp gen) nomm [%done ~] ~)
    =/  collapsed  ?:(?=(%must mode) (laze-collapse l cape.less.b) (laze-may l cape.less.b))
    [(bake-need-ord collapsed less.b) *need-lazy *need *baked 0 (sure-of sure.l cape.less.b)]

Here it is instantiated with track A's models (`Ska/RunShape.lean`): `runShape` on `[%done ~]`
with `sup` `~` from the state of the bunt `line-short` (`id-gen` `0`, `sofs` `~`), then
`lazeCollapse` (`%must`, at the member's fuel `m.fuel`) or `lazeMay` (`%may`), and `sureOfS` of
`sure.l` (`sureOf` over `CSet`, `sureOfS_eq`).  `+run-shape` reads, beside the views of the
member's call environment (`need`, `sure`, and `cod` as the code table's `pure`), whether a callee
is a hot jet (`jet`) and the code table's nomms (`cod`, for `+sound-far`): `ShapeX`.

* `shapeEnvOf x env`: the `ShapeEnv` of a `CallEnv`;
* `lazeRealG` (any set, computable over a computable one: the corpus check), `lazeReal` (`CSet`);
* **`cfgRealShape r x order kids`**: `cfgReal` with `laze := lazeReal x`. -/

namespace Formalization.SkaModel.SccLoop

open Nock Formalization.Hoon Formalization.SkaModel Formalization.SkaModel.Comp Formalization.Compiler

/-- What `+run-shape` reads beside the call environment: whether a callee is a hot jet
(`(biff (~(get by call.cole.jets.long-ska) b) ~(get by jets-hot))` is a `^`), and the nomm of the
code table's entry (`+sound-far`). -/
structure ShapeX where
  jet : Bell → Bool
  cod : Bell → Option Nomm

/-- The `ShapeEnv` of a member compile: `need` and `sure` the views (`+callee-need`,
`+callee-sure`), `pure` the code table's flag as `+hinted` reads it (`env.cod`). -/
def shapeEnvOf (x : ShapeX) (env : CallEnv) : ShapeEnv :=
  ⟨env.need, env.sure, x.jet, env.cod, x.cod⟩

/-- The start state of `+run-shape`: `id-gen` and `sofs` of the bunt `line-short`. -/
def rsSt0 {S : Type} [HoonSet S] : RSt S := ⟨0, HoonSet.empty⟩

/-- `collapsed`: `+laze-collapse` on `%must`, `+laze-may` otherwise. -/
def collapseOf {S : Type} [HoonSet S] (mode : Mode) (fuel : Nat) (l : Laze S) (cape : Cape) : Option NeedOrd :=
  match mode with
  | Mode.must => lazeCollapse fuel l cape
  | _ => lazeMay l cape

/-- **`(collapsed, sur)` of the sweeps' compile**, over any set. -/
def lazeRealG {S : Type} [HoonSet S] (x : ShapeX) (mode : Mode) (env : CallEnv) (m : MemInfo) :
    Option (NeedOrd × NeedOrd) :=
  (runShape (S := S) (shapeEnvOf x env) Option.none m.nm GoalS.done rsSt0).bind fun p =>
    (collapseOf mode m.fuel p.1 m.cape).bind fun col =>
      (sureOfS p.1.sure.ned p.1.sure.lok m.cape).map fun sur => (col, sur)

/-- `lazeRealG` over `CSet`, the sets of the pill's nouns. -/
noncomputable def lazeReal (x : ShapeX) : Mode → CallEnv → MemInfo → Option (NeedOrd × NeedOrd) :=
  lazeRealG (S := CSet) x

/-- **The model of a real SCC with the sweeps modelled**: `cfgReal` with `laze := lazeReal x`. -/
noncomputable def cfgRealShape (r : RealCfg) (x : ShapeX) (order : List Noun) (kids : Noun → List Noun) :
    Cfg Noun NeedOrd :=
  cfgReal { r with laze := lazeReal x } order kids

/-- The sweeps' compile of `cfgRealShape` from the pieces of `lazeReal`. -/
theorem compReal_sweep (r : RealCfg) (x : ShapeX) (b : Noun) (mode : Mode) (hm : mode ≠ Mode.done)
    (vn vs : Noun → NeedOrd) (col sur : NeedOrd)
    (h : lazeReal x mode (envView r.env r.scc vn vs) (r.info b) = some (col, sur)) :
    compReal { r with laze := lazeReal x } b mode vn vs
      = ⟨bakeNeedOrd col (Sock.mk (r.info b).cape (r.info b).data), sur⟩ := by
  cases mode with
  | done => exact absurd rfl hm
  | must => simp [compReal, sweepM, h]
  | may => simp [compReal, sweepM, h]

/-- `lazeReal` from the pieces: the run, `collapsed`, `sure-of`. -/
theorem lazeReal_eq (x : ShapeX) (mode : Mode) (env : CallEnv) (m : MemInfo) (l : Laze CSet) (st : RSt CSet)
    (hrun : runShape (shapeEnvOf x env) Option.none m.nm GoalS.done rsSt0 = some (l, st))
    (col : NeedOrd) (hcol : collapseOf mode m.fuel l m.cape = some col)
    (sur : NeedOrd) (hsur : sureOfS l.sure.ned l.sure.lok m.cape = some sur) :
    lazeReal x mode env m = some (col, sur) := by
  simp [lazeReal, lazeRealG, hrun, hcol, hsur]

end Formalization.SkaModel.SccLoop
