import lemmas.Compiler.CompSccLoopMemShape
import lemmas.Compiler.CompSccLoopMemDone
import lemmas.Ska.SccLoopShape

/-! # The gate `member` on `%must` and `%may`: shared nouns (README Gaps 21.18)

Off `%done` (`mode` `%must` or `%may`, `done` `|`) the gate `member` runs the branch `memShape`
(`CompSccLoopMemShape.lean`) in place of `memFinal`, and `finish` returns the placeholder
`[np 0 ~]` (`placeholder_straight`).  The nouns shared by the pill side
(`CompSccLoopMemSweep.lean`) and the model side (`CompSccLoopSweepStep.lean`):

* `memS0X DN MODE ..`: the subject after the push of `done` for any mode (`memS0` is
  `memS0X (A 0) (A 0x656e6f64)`, `memS0X_done`);
* `shapeResN SH SUR`: the tuple `[shape *need-lazy *need *baked 0 sur]` of the branch;
* `memChgTN`: `chg` with no entry, `top` any map (`(~(gut by top) b [%none ~])` is `TG`);
* **`MemShapeBranch`**: the branch's pill computation, as the ONE hypothesis on `+run-shape`,
  `+laze-collapse` / `+laze-may` and `+bake-need-ord` (track A's): from the subject after the entry
  (`gen` the bunt with `cache` the product `CA1` of `+inlined`), `memShape` returns
  `[[(bake-need-ord collapsed less.b) *need-lazy *need *baked 0 sur] gen']` with `(collapsed, sur)`
  the model's `lazeReal`, and `gen'` holding a cache `[C1 C2 C3 C4 SURE]` at axis `510`. -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop

/-- The subject after the push of `done` (`DN`), for the mode `MODE`. -/
def memS0X (DN MODE B KEEP ML TOP CACHE CTX : Noun) : Noun :=
  C DN (C memBody (C (memSam B MODE KEEP ML TOP CACHE) CTX))

theorem memS0X_done (B KEEP ML TOP CACHE CTX : Noun) :
    memS0X (A 0) (A 0x656e6f64) B KEEP ML TOP CACHE CTX = memS0 B KEEP ML TOP CACHE CTX := rfl

/-- The noun of `%must`. -/
abbrev mustN : Noun := A 0x7473756d
/-- The noun of `%may`. -/
abbrev mayN : Noun := A 0x79616d

/-- The noun of a sweep's mode. -/
def modeN : Mode → Noun
  | Mode.must => mustN
  | Mode.may => mayN
  | Mode.done => A 0x656e6f64

/-- `[shape *need-lazy *need *baked 0 sur]`. -/
def shapeResN (SH SUR : Noun) : Noun :=
  C SH (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))
    (C (C (A 0x656e6f6e) (A 0)) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) SUR))))

/-- `chg` with no entry of `b`: `|(moved !?=([%none ~] need-new) !?=([%none ~] TG))`, `TG` the
`+gut:by` of `top` at `b`. -/
def memChgTN (MOVED NN TG : Noun) : Noun :=
  if MOVED = A 0 then A 0 else
  if C (A 0x656e6f6e) (A 0) = NN then (if C (A 0x656e6f6e) (A 0) = TG then A 1 else A 0) else A 0

/-- The subject at the branch: the bunt `gen` with the cache `CA1` of `+inlined`, the nomm, the
door `comp` on `[scc long-ska jets-hot map-local top b]`, and `memS0X` with `done` `|`. -/
def memShapeSubj (MODE : Noun) (keep : Bool) (NM SCC LONG JH ML TOP B CA1 CTX : Noun) : Noun :=
  C (genNoun (genEntry : Gen (TreapMap mugF)) (cuRest CA1))
    (memS3 NM (memDCtx SCC LONG JH ML TOP B) (memS0X (A 1) MODE B (loob keep) ML TOP CA1 CTX))

/-- **The branch of the sweeps in the pill** (the hypothesis for track A): on the member
`b = [[cape DATA] FOL]` with nomm `nm`, in the mode `mode` (`%must` or `%may`), with the call
environment `env` (the views of the state, `envView`) and the code table read through `x`,
`memShape` returns `[[shape *need-lazy *need *baked 0 sur] gen']` where `(collapsed, sur)` is
`lazeReal x mode env ⟨nm, cape, DATA, fuel⟩`, `shape` is `bakeNeedOrd collapsed [cape DATA]`, and
`gen'` holds the cache `cacheN C1 C2 C3 C4 SURE` at axis `510` (the cache after the run:
`=.  cache  cache.gen`). -/
def MemShapeBranch (x : ShapeX) (mode : Mode) (env : CallEnv) (cape : Cape) (DATA FOL : Noun) (nm : Nomm)
    (fuel : Nat) (keep : Bool) (SCC LONG JH ML TOP CA1 CTX : Noun) (col sur : NeedOrd) (G2 : Noun) : Prop :=
  lazeReal x mode env ⟨nm, cape, DATA, fuel⟩ = some (col, sur) ∧
  nock (memShapeSubj (modeN mode) keep nm.toNoun SCC LONG JH ML TOP (C (C cape.toNoun DATA) FOL) CA1 CTX) memShape
    = some (C (shapeResN (bakeNeedOrd col (Sock.mk cape DATA)).toNoun sur.toNoun) G2)

end Compiler
end Formalization
