import lemmas.Ska.CompHintTreeUEx
import lemmas.Ska.CompHintFlat

/-!
# Bonds inside bonds: unwrappable at the top, not to distinct labels (README Gaps 24.13)

A kept hint (`+lazy-bound`) puts its formula's whole lazy need in one bond.
When the goal of the hint has bonds, or `+past-if` parks the product's need
in a bond of its own, the formula's need carries them, and the result has
a bond inside a bond (`nested`).  The checks, on the model (`envH`, `sndH`):

* Of the 39 dumped formulas, 7 are nested at the top: `s07`, `d10`, `d12`,
  `d16`, `d17`, `d18`, `m04` (`s04`, `s06` are not).
* `unwrapOK`: the final pass (`+kerf`, `toStraightF`) of the result equals
  that of its flattening `flattenL` (every bond's inner bonds hoisted to the
  top, `bondEntries`): on all 39 and on 22 more shapes (`shapes`, 17 of them
  nested).  So at the top a nested bond is unwrappable.
* `dup`: in 4 of the 22 shapes the result's `entries` repeat a label: a bond
  of the goal goes into the kept hint's formula (nested by `+lazy-bound`) and
  into a sibling part (at the top), and `+copy` merges bonds by label only at
  the top.  So the flattening is not a lazy with distinct labels, while every
  relation (`LOKS*`, `DoneOK`) asks `Nodup` of the entries' labels: the
  widening is not track C's `Unwraps` (which keeps the bonds and unwraps
  forks), it needs the invariants on entries (`hnd`, `hlab`, `hed`) restated
  for labels that repeat (the takes at a label being the union).
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

namespace HintNest

def flattenL (l : Lazy LS) : Lazy LS :=
  mk l.sure l.fork ((bondEntries l.bond).map fun (o, e) => (o, mk e.sure e.fork []))
def topOf (nex : NextL LS) (g1 : Gen FM) : Option Noun :=
  (kerf nex g1).bind fun ((o, sub), g2) => (toStraightF g2.cond g2.blocks (Need.this sub) o).map outN
def unwrapOK (nm : Nomm) : Option (Bool × Bool) :=
  (runLCH (S := LS) (Map := FM) envH sndH true Option.none nm CGoalL.done [] gen0).map fun (nex, g1) =>
    (nested nm == some true, topOf nex g1 == topOf ⟨flattenL nex.laz, nex.th⟩ g1)
def nm39 : List (String × Nomm) :=
  HintData.all.filterMap fun (n, j) => ((parts j).bind fun (nmN, _, _, _) => nommOf 300 nmN).map (n, ·)

def bo (q : Nomm) : Nomm := Nomm.n11s HintTag.bout q (A 0)
def sp (q : Nomm) : Nomm := Nomm.n11d tagSpot (Nomm.n1 (A 0)) q (A 0)
def dup (nm : Nomm) : Option (List Nat) :=
  (runLCH (S := LS) (Map := FM) envH sndH true Option.none nm CGoalL.done [] gen0).map fun (nex, _) =>
    (entries nex.laz).map Prod.fst
def c (p q : Nomm) := Nomm.cons p q
def z (a : Nat) := Nomm.n0 a
def shapes : List Nomm := [
  Nomm.n7 (c (bo (z 2)) (z 3)) (bo (z 1)), Nomm.n7 (c (z 2) (bo (z 3))) (bo (z 1)),
  Nomm.n7 (c (sp (z 2)) (z 3)) (sp (z 1)), Nomm.n7 (bo (z 3)) (bo (z 1)), Nomm.n7 (bo (z 3)) (c (bo (z 2)) (z 3)),
  bo (c (bo (z 2)) (Nomm.n4 (z 3))), bo (bo (z 3)), bo (c (bo (z 2)) (bo (z 3))), c (bo (z 2)) (bo (z 3)),
  Nomm.n7 (bo (c (z 2) (z 3))) (c (bo (z 2)) (z 3)), sp (c (sp (z 2)) (z 3)), sp (sp (z 3)),
  Nomm.n7 (sp (z 3)) (Nomm.n4 (z 1)), Nomm.n4 (bo (c (bo (z 2)) (z 3))), Nomm.n7 (z 3) (bo (c (bo (z 2)) (z 3))),
  c (bo (c (bo (z 2)) (z 3))) (z 1), Nomm.n7 (c (bo (z 2)) (bo (z 3))) (bo (c (z 2) (z 3))),
  Nomm.n5 (bo (z 2)) (bo (z 3)), Nomm.n7 (Nomm.n5 (bo (z 2)) (z 3)) (bo (z 1)),
  Nomm.n7 (c (bo (z 2)) (z 3)) (c (bo (z 2)) (bo (z 3))), Nomm.n2 (bo (z 2)) (bo (z 3)) Option.none,
  Nomm.n7 (Nomm.n2 (z 2) (z 3) Option.none) (bo (c (bo (z 2)) (z 3)))]

#guard nm39.length == 39
#guard (nm39.filter fun (_, nm) => nested nm == some true).map Prod.fst ==
  ["s07", "d10", "d12", "d16", "d17", "d18", "m04"]
#guard nm39.all fun (_, nm) => (unwrapOK nm).map Prod.snd == some true
#guard shapes.length == 22
#guard (shapes.filter fun nm => nested nm == some true).length == 17
#guard shapes.all fun nm => (unwrapOK nm).map Prod.snd == some true
#guard (shapes.filter fun nm => (dup nm).map (fun l => l.length != l.eraseDups.length) == some true).length == 4
#guard (dup (Nomm.n7 (c (bo (z 2)) (z 3)) (bo (z 1)))).map (fun l => (l.length, l.eraseDups.length)) == some (4, 3)

end HintNest

end Comp
end SkaModel
end Formalization
