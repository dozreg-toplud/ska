import lemmas.Ska.CompRunLCEq

/-!
# The whole-subject version (`+compile-unary`)

README Gaps 12.10.  `%full` and `%dire` with `mono` `&` run the code of
`+compiled-mono`, which is `+compile-unary` (line 3390 of
`nock-compilation.hoon`); `%dire` with `mono` `|` runs `+compiled-nary`, the
final pass of `member` in `+compile-scc-in` (`finishLF`, `finishLFC`).
`+eval-top` (`topBody`) runs the code of `%full` only when
`c.nargs = 1 ∧ c.need = NeedOrd.this`, so the statements of `core/` need
the whole-subject version.

## How the two versions differ for a call-free nomm

1. The run.  Both run `+run` from an empty `line-short` for `[%done ~]` in
   the region `~` with `sup` `~`; the whole-subject version passes `mono`
   `&` (line 3414), the n-ary one `|` (line 3505).  `mono` is read only by
   the cases `%2` (direct calls, lines 3998, 4010, 4032) and `%mean`
   (line 4306), and `$(...)` keeps it, so for a nomm without `%2` and
   `%mean` the run is the same (`runL`).  The nomm differs in one place:
   the n-ary version compiles the nomm of `+inlined` (line 3480), the
   whole-subject one the nomm of the code table (line 3414); without `%2`
   `+inlined` changes nothing, and the model takes the nomm it is given.
2. The end.  The n-ary version allocates the input registers
   (`+collapse-shape`: `+need-ord-alloc-regs` of the collapsed shape,
   asserting that the entry jump has no arguments), takes them apart at the
   entry block of the run and at every lazy block by `+coerce-lazy` (whose
   looks drop the axes the bell's cape knows and the axes inside the input
   need), runs `+soft-done`, loads the baked registers, and ends with
   `+to-straight` of `[%next [[ned.bak ~] ~ ~] ~ o]` with `o` the run's
   entry.  The whole-subject version ends with `+kerf` (line 3417): a new
   block `[~ ~ [%hop then.nex]]` (the jump keeps its arguments), then
   `+kern` of the run's lazy need from one fresh register `sub`: at the new
   block the ops of `+kern-need` from `sub` into `+sure-require-look` of the
   sure need (all its looks, the cape is not read), at every other lazy
   block the same from a fresh proxy for `sub` (`+proxy`), walked forks
   before bonds (`+walk-lazy`); then `+to-straight` of
   `[%next [[this+sub ~] ~ ~] ~ o]` with `o` the new block.
3. The output.  The input need is `[%this ~]` with one argument (register
   `0`, `sub` renamed); the entry block `0w0` is the new block with the
   taking apart in front of its hop.  `+to-straight` takes the map path
   whenever a lazy block other than the root wants something (the proxies
   are keys of `cond`), and unproxying puts `sub` back in their ops.

## Raw blocks (`tools/hoon/wholedump.hoon`, subject sock unknown, 2026-11-24)

`[4 [0 3]]`, nomm `[4 [0 3]]`.  Whole subject (`need [%this ~]`, 1 arg):
`0w0 mov v0 v3, cel v3, tal v3 v4, mov v4 v2, hop 1`; `0w1 inc v2 v1, don
v1`.  N-ary (`need [~ this]`, 1 arg): `0w0 mov v0 v2, inc v2 v1, don v1`.

`[6 [3 0 1] [0 2] [1 0]]`, nomm the same.  Whole subject: `0w0 mov v0 v3,
hop 5`; `0w1 imm 0 v1, don v1`; `0w2 don v2`; `0w3 mov v0 v5, cel v5, hed
v5 v7, mov v7 v2, hop 2` (the proxy unproxied to `v0`); `0w5 clq v3 3 1`.
N-ary (`need this`): the same but `0w3 mov v0 v4, cel v4, hed v4 v6, mov v6
v2, hop 2` (no proxy register allocated).

`[[0 2] [0 3]]`, nomm the same.  Whole subject: `0w0 mov v0 v4, cel v4, hed
v4 v6, mov v6 v2, tal v4 v5, mov v5 v3, hop 2`; `0w1 don v1`; `0w2 con v2 v3
v1, hop 1`.  N-ary (`need [this this]`, 2 args): `0w0 mov v1 v4, mov v0 v3,
hop 2`; `0w1 don v2`; `0w2 con v3 v4 v2, hop 1`.

`[7 [0 2] [4 [0 3]]]`, nomm the same.  Whole subject: `0w0 mov v0 v3, cel
v3, hed v3 v5, mov v5 v6, cel v6, tal v6 v7, mov v7 v2, hop 1`; `0w1 inc v2
v1, don v1`.  N-ary (`need [[~ this] ~]`, 1 arg): `0w0 mov v0 v2, inc v2 v1,
don v1`.

The `#guard` lines below check `finishLU` against the whole-subject blocks
and `finishLF` against the n-ary ones, all equal.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **`+compile-unary`** of a function whose nomm is `nm`, after the n-ary
map (lines 3407 to 3419): `run` for `[%done ~]` from an empty state,
`+kerf` of its result, `+to-straight` of `[%next [[this+sub ~] ~ ~] ~ o]`.
The run is `runL`, which is `+run` with `mono` `&` on a nomm without `%2`
and `%mean`. -/
def finishLU (nm : Nomm) : Option (Straight Map) :=
  (runL nm (CGoalL.done : CGoalL S) [] gen0).bind fun (nex, g1) =>
    (kerf nex g1).bind fun ((o, sub), g2) =>
      toStraightF g2.cond g2.blocks (Need.this sub) o

/-- `+compile-unary` with `runLC`: exact on nomms whose calls are all
indirect (`callL` does not read `mono` there), not on direct calls (the
whole-subject version calls through `+mono-try-call`). -/
def finishLUC (env : CallEnv) (nm : Nomm) : Option (Straight Map) :=
  (runLC env Option.none nm (CGoalL.done : CGoalL S) [] gen0).bind fun (nex, g1) =>
    (kerf nex g1).bind fun ((o, sub), g2) =>
      toStraightF g2.cond g2.blocks (Need.this sub) o

/-- **Without `%2`, `finishLUC` is `finishLU`.** -/
theorem finishLUC_eq (env : CallEnv) {nm : Nomm} (h : nm.noCall = true) :
    finishLUC (S := S) (Map := Map) env nm = finishLU (S := S) nm := by
  unfold finishLUC finishLU
  rw [runLC_eq env nm h]

/-! ## Checks against the raw blocks -/

/-- The need, the argument count and the blocks `0 ..< n` of the
whole-subject code of `nm`. -/
def monoOut (nm : Nomm) (n : Nat) : Option (NeedOrd × Nat × List (Nat × Option Blob)) :=
  (finishLU (S := LS) (Map := FM) nm).map fun c =>
    (c.need, c.nargs, (List.range n).map fun k => (k, c.blocks.f k))

/-- The same for the n-ary code with the input need `ord`. -/
def naryOut (nm : Nomm) (ord : NeedOrd) (n : Nat) : Option (NeedOrd × Nat × List (Nat × Option Blob)) :=
  (finishLF (S := LS) (Map := FM) nm ord Cape.no (fun ned => (ned, []))).map fun c =>
    (c.need, c.nargs, (List.range n).map fun k => (k, c.blocks.f k))

/- `[4 [0 3]]`, whole subject. -/
#guard monoOut (Nomm.n4 (Nomm.n0 3)) 3 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 3, Pole.cel 3, Pole.tal 3 4, Pole.mov 4 2] (hp 1)),
    (1, bk [Pole.inc 2 1] (Termin.don 1)), (2, none)])

/- `[4 [0 3]]`, n-ary. -/
#guard naryOut (Nomm.n4 (Nomm.n0 3)) (NeedOrd.pair NeedOrd.none NeedOrd.this) 2 ==
  some (NeedOrd.pair NeedOrd.none NeedOrd.this, 1, [(0, bk [Pole.mov 0 2, Pole.inc 2 1] (Termin.don 1)),
    (1, none)])

/- `[6 [3 0 1] [0 2] [1 0]]`, whole subject: the lazy block `0w3` gets the
ops from a proxy, unproxied to `v0`. -/
#guard monoOut (Nomm.n6 (Nomm.n3 (Nomm.n0 1)) (Nomm.n0 2) (Nomm.n1 (A 0))) 7 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 3] (hp 5)), (1, bk [Pole.imm (A 0) 1] (Termin.don 1)),
    (2, bk [] (Termin.don 2)), (3, bk [Pole.mov 0 5, Pole.cel 5, Pole.hed 5 7, Pole.mov 7 2] (hp 2)),
    (4, none), (5, bk [] (Termin.clq 3 (jmp0 3) (jmp0 1))), (6, none)])

/- `[6 [3 0 1] [0 2] [1 0]]`, n-ary. -/
#guard naryOut (Nomm.n6 (Nomm.n3 (Nomm.n0 1)) (Nomm.n0 2) (Nomm.n1 (A 0))) NeedOrd.this 7 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 3] (hp 5)), (1, bk [Pole.imm (A 0) 1] (Termin.don 1)),
    (2, bk [] (Termin.don 2)), (3, bk [Pole.mov 0 4, Pole.cel 4, Pole.hed 4 6, Pole.mov 6 2] (hp 2)),
    (4, none), (5, bk [] (Termin.clq 3 (jmp0 3) (jmp0 1))), (6, none)])

/- `[[0 2] [0 3]]`, whole subject. -/
#guard monoOut (Nomm.cons (Nomm.n0 2) (Nomm.n0 3)) 4 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 4, Pole.cel 4, Pole.hed 4 6, Pole.mov 6 2, Pole.tal 4 5,
      Pole.mov 5 3] (hp 2)),
    (1, bk [] (Termin.don 1)), (2, bk [Pole.con 2 3 1] (hp 1)), (3, none)])

/- `[[0 2] [0 3]]`, n-ary. -/
#guard naryOut (Nomm.cons (Nomm.n0 2) (Nomm.n0 3)) (NeedOrd.pair NeedOrd.this NeedOrd.this) 4 ==
  some (NeedOrd.pair NeedOrd.this NeedOrd.this, 2, [(0, bk [Pole.mov 1 4, Pole.mov 0 3] (hp 2)),
    (1, bk [] (Termin.don 2)), (2, bk [Pole.con 3 4 2] (hp 1)), (3, none)])

/- `[7 [0 2] [4 [0 3]]]`, whole subject. -/
#guard monoOut (Nomm.n7 (Nomm.n0 2) (Nomm.n4 (Nomm.n0 3))) 3 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 3, Pole.cel 3, Pole.hed 3 5, Pole.mov 5 6, Pole.cel 6,
      Pole.tal 6 7, Pole.mov 7 2] (hp 1)),
    (1, bk [Pole.inc 2 1] (Termin.don 1)), (2, none)])

/- `[7 [0 2] [4 [0 3]]]`, n-ary. -/
#guard naryOut (Nomm.n7 (Nomm.n0 2) (Nomm.n4 (Nomm.n0 3)))
    (NeedOrd.pair (NeedOrd.pair NeedOrd.none NeedOrd.this) NeedOrd.none) 2 ==
  some (NeedOrd.pair (NeedOrd.pair NeedOrd.none NeedOrd.this) NeedOrd.none, 1,
    [(0, bk [Pole.mov 0 2, Pole.inc 2 1] (Termin.don 1)), (1, none)])

end Comp
end SkaModel
end Formalization
