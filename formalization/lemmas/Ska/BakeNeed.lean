import lemmas.Ska.CompRunLCEq
import lemmas.Ska.Sock

/-!
# `+bake-need`, `+need-fits`, `+bake-need-ord`: a model

From the Hoon text (`desk/lib/nock-compilation.hoon`, `++  bake-need` line
3724, `++  need-fits` 3769, `++  known-sock` 3787, `++  bake-need-ord` 3794;
README Gaps 9, the MAP of 2026-11-27).

* `needFits`: `+need-fits` on a need (`%none` and `%this` fit anything; a
  cell and a `%both` ask for a cell and fit by halves).
* `bakeAll`: the trap `all` of `+bake-need`, which bakes a whole part: a
  `%this r` puts `[r data]` on the front of `imm`, a `%both r` puts its own
  pair first, then its halves, the head before the tail.  `+known-sock`
  crashes on `~`; the trap is entered on a cell sock only and `hed:so`,
  `tel:so` of a cell sock are cell socks, so `sockData` never meets `~`.
* `bakeGo`: the loop.  At a node whose sock is a cell with a wholly known
  cape and data that fit the need, the node is `%none` and `bakeAll` runs;
  else `%none` and `%this` stay, a cell is rebuilt with `+cons-need`, and a
  `%both` keeps its register: `[%both r x]` when `x` is a cell, `[%this r]`
  when both halves were baked away.
* `bakeNeed ned know`: the gate, `imm` starting at `~`.
* `bakeNeedOrd`: `+bake-need-ord`, the same walk on a shape.

`finishLFB env nm ord less` is the n-ary final pass with the real bake:
`finishLFC` with `bake := fun n => bakeNeed n less` and the cape of
`less`.
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

/-- `+need-fits` on a need. -/
def needFits : Need → Noun → Bool
  | Need.pair p q, Noun.cell a b => needFits p a && needFits q b
  | Need.pair _ _, Noun.atom _ => false
  | Need.both _ h t, Noun.cell a b => needFits h a && needFits t b
  | Need.both _ _ _, Noun.atom _ => false
  | Need.none, _ => true
  | Need.this _, _ => true

/-- `+need-fits` on a shape. -/
def ordFits : NeedOrd → Noun → Bool
  | NeedOrd.pair p q, Noun.cell a b => ordFits p a && ordFits q b
  | NeedOrd.pair _ _, Noun.atom _ => false
  | NeedOrd.both h t, Noun.cell a b => ordFits h a && ordFits t b
  | NeedOrd.both _ _, Noun.atom _ => false
  | NeedOrd.none, _ => true
  | NeedOrd.this, _ => true

/-- `data:(known-sock j)` on a cell sock. -/
def sockData : Sock → Noun
  | Sock.mk _ d => d
  | Sock.void => A 0

/-- The test of a node: a cell sock, wholly known, whose data fits. -/
def bakeTest (fits : Noun → Bool) : Sock → Bool
  | Sock.mk c d => Ca.all c && fits d
  | Sock.void => false

/-- The trap `all` of `+bake-need`. -/
def bakeAll : Need → Sock → List (Nat × Noun) → List (Nat × Noun)
  | Need.none, _, imm => imm
  | Need.this r, j, imm => (r, sockData j) :: imm
  | Need.pair p q, j, imm => bakeAll q (So.tel j) (bakeAll p (So.hed j) imm)
  | Need.both r h t, j, imm => bakeAll t (So.tel j) (bakeAll h (So.hed j) ((r, sockData j) :: imm))

/-- The loop of `+bake-need`. -/
def bakeGo : Need → Sock → List (Nat × Noun) → Need × List (Nat × Noun)
  | Need.none, _, imm => (Need.none, imm)
  | Need.this r, k, imm =>
    if bakeTest (needFits (Need.this r)) k then (Need.none, (r, sockData k) :: imm) else (Need.this r, imm)
  | Need.pair p q, k, imm =>
    if bakeTest (needFits (Need.pair p q)) k then (Need.none, bakeAll (Need.pair p q) k imm) else
    let l := bakeGo p (So.hed k) imm
    let r := bakeGo q (So.tel k) l.2
    (consNeed l.1 r.1, r.2)
  | Need.both r h t, k, imm =>
    if bakeTest (needFits (Need.both r h t)) k then (Need.none, bakeAll (Need.both r h t) k imm) else
    let a := bakeGo h (So.hed k) imm
    let b := bakeGo t (So.tel k) a.2
    match consNeed a.1 b.1 with
    | Need.pair x y => (Need.both r x y, b.2)
    | _ => (Need.this r, b.2)

/-- **`+bake-need`**: the residual need and the baked registers with their
values, in the Hoon's order (each put on the front). -/
def bakeNeed (ned : Need) (know : Sock) : Need × List (Nat × Noun) := bakeGo ned know []

/-- `+cons-need` on shapes. -/
def consOrdB (a b : NeedOrd) : NeedOrd :=
  if a = NeedOrd.none ∧ b = NeedOrd.none then NeedOrd.none else NeedOrd.pair a b

/-- **`+bake-need-ord`**. -/
def bakeNeedOrd : NeedOrd → Sock → NeedOrd
  | NeedOrd.none, _ => NeedOrd.none
  | NeedOrd.this, k => if bakeTest (ordFits NeedOrd.this) k then NeedOrd.none else NeedOrd.this
  | NeedOrd.pair p q, k =>
    if bakeTest (ordFits (NeedOrd.pair p q)) k then NeedOrd.none else
    consOrdB (bakeNeedOrd p (So.hed k)) (bakeNeedOrd q (So.tel k))
  | NeedOrd.both h t, k =>
    if bakeTest (ordFits (NeedOrd.both h t)) k then NeedOrd.none else
    match consOrdB (bakeNeedOrd h (So.hed k)) (bakeNeedOrd t (So.tel k)) with
    | NeedOrd.pair x y => NeedOrd.both x y
    | _ => NeedOrd.this

/-- The cape of a sock (`cape.less.b`; `|` on `~`). -/
def sockCape : Sock → Cape
  | Sock.mk c _ => c
  | Sock.void => Cape.no

/-- **The n-ary final pass with the real bake** of `less.b`. -/
def finishLFB {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]
    (env : CallEnv) (nm : Nomm) (ord : NeedOrd) (less : Sock) : Option (Straight Map) :=
  finishLFC (S := S) env nm ord (sockCape less) (fun n => bakeNeed n less)

/-- `$baked` as a noun. -/
def bakedNoun (b : Need × List (Nat × Noun)) : Noun :=
  C b.1.toNoun (listNoun (fun p : Nat × Noun => C (A p.1) p.2) b.2)

/-! ## Facts -/

/-- On a sock that is not wholly known, the test of a node fails. -/
theorem bakeTest_quiet (fits : Noun → Bool) (c : Cape) (d : Noun) (h : Ca.all c = false) :
    bakeTest fits (Sock.mk c d) = false := by
  simp [bakeTest, h]

/-- `So.hed` and `So.tel` of a cell sock are cell socks. -/
theorem so_hed_mk (c : Cape) (d : Noun) : ∃ c' d', So.hed (Sock.mk c d) = Sock.mk c' d' := by
  cases c <;> cases d <;> simp [So.hed, Sock.dunno]

theorem so_tel_mk (c : Cape) (d : Noun) : ∃ c' d', So.tel (Sock.mk c d) = Sock.mk c' d' := by
  cases c <;> cases d <;> simp [So.tel, Sock.dunno]

end Comp
end SkaModel
end Formalization
