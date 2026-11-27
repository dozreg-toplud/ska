import lemmas.Ska.RawInvCLCheck

/-!
# Single assignment of the top state with calls, checked

README Gaps 14 (b), track D.  The open facts `TopSAR` (`RawInvCLTopN.lean`)
and `TopSAU` (`RawInvCLTopU.lean`) on all 2,856 `PlainN` nomms of `enumCX`:
at the end of the top run (`chkSARun`) and after its `+kerf` (`chkSA`),
every register has at most one definition in the whole map (`defOnceB`),
no op is a trace hint (`noTrB`) and every jump argument is defined by its
own block (`argsHereB`).  Not vacuous: 528 of the runs have a jump with an
argument, 1,927 have proxies after `+kerf`.
-/

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

def argsHereB (m : FM Blob) : Bool :=
  (blocksOf m).all fun (_, b) => (getJmps b.fin).all fun j =>
    j.args.all fun a => match a with | some r => (blockDefs b).contains r | none => false

def kerfTop (nm : Nomm) : Option (Comp.Gen FM) :=
  (runC nm).bind fun (nex, g) => ((kerf nex : CM FM (Nat × Nat)) g).map fun (_, g2) => g2

def chkSA (nm : Nomm) : Option Bool :=
  (kerfTop nm).map fun g2 => defOnceB g2.blocks && noTrB g2.blocks && argsHereB g2.blocks

def chkSARun (nm : Nomm) : Option Bool :=
  (runC nm).map fun (_, g) => defOnceB g.blocks && noTrB g.blocks && argsHereB g.blocks

#guard cnt chkSA (enumCX.filter isPlain) == (2856, 0, 0)
#guard cnt chkSARun (enumCX.filter isPlain) == (2856, 0, 0)
#guard ((enumCX.filter isPlain).filter fun nm => match kerfTop nm with
  | some g2 => (blocksOf g2.blocks).any fun (_, b) => (getJmps b.fin).any fun j => !j.args.isEmpty
  | none => false).length == 528
#guard ((enumCX.filter isPlain).filter fun nm => match kerfTop nm with
  | some g2 => (HoonMapKeys.keys g2.cond).length > 0
  | none => false).length == 1927

end Raw
end SkaModel
end Formalization
