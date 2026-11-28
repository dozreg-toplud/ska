import lemmas.Ska.CompGenCheckB
import lemmas.Ska.RawInvCLCheckIJ

/-!
# The class `NextGC` of the one induction, checked before any proof

README Gaps 12.39, item 12.  The induction over call-free, hint-free nomms
carries a class of runs: `RunOKGen` at every goal of the class, and of the
result `Raw.LabUniq` and `Clean` needs (what `+copy` asks of both its inputs,
`CopyPreAt`, and what a parent's next part asks of its goal).  Before any
proof, every clause is evaluated here at EVERY sub-run that the compiler
makes through the cons, `%7` and their parts (`chk` follows `runLC`'s cons
and `%7` cases and checks that its reassembly is `runLC`'s own result):

* `res`: the result is `LabUniq` (`Raw.labUniqB`) with `Clean` needs, and
  its sure need is apart from its entries' needs (`SureApart`, what the copy's
  apartness across the two halves reads: no goal of the families and no
  result shares a register between the two);
* `eregsAt`: an entry's registers are a goal entry's AT ITS LABEL, the goal's
  sure ones, or fresh (`FrameG.eregs` per label);
* `prem:q`, `prem:p`, `prem:7`: the goal each part gets meets the class's
  premises (`GoalG`, `LabUniq`, `Clean`, registers no keys of `cond`, a jump
  without arguments, `drop` off);
* `copy`: `CopyPreAt` of the copy's two inputs at the copy's start: at every
  label (the copy's root included) the needs of both inputs are clean,
  distinct, below `re` and pairwise apart;
* `recon`: the reassembly is not `runLC`'s result (none: the walker is
  exact).

Families: famA (the 245 `%6` under the 30 flat goals, 2 jumps, 2 states),
famB (`all6` under the 30 flat goals), famC (the `%6` and the branches under
`goalsP`), famD (conses and `%7` of two call-free `%6`, under the flat goals
and `goalsP`).
-/

namespace Formalization
namespace SkaModel
namespace Comp
namespace GenCheck

open Nock Lazy SixCheck

/-- The sure need is apart from every entry's need (`SureApart`). -/
def sureApartB (l : Lazy LS) : Bool :=
  (entries l).all fun e => (regsOf e.2.sure.ned).all fun r => !(regsOf l.sure.ned).contains r

/-- The result side of the class: `LabUniq`, `Clean` needs, `SureApart`. -/
def resB (l : Lazy LS) : Bool :=
  Raw.labUniqB 30 l && SixNxCheck.cleanB l.sure.ned && (entries l).all (fun e => SixNxCheck.cleanB e.2.sure.ned) &&
  sureApartB l

/-- `EregsAt`: the registers of a result entry are those of a goal entry AT
ITS LABEL, the goal's sure ones, or fresh. -/
def eregsAtB (L : Lazy LS) (g0 g1 : Gen FM) (l : Lazy LS) : Bool :=
  (entries l).all fun e => (regsOf e.2.sure.ned).all fun r =>
    ((entries L).any fun e0 => e0.1 == e.1 && (regsOf e0.2.sure.ned).contains r) ||
    (regsOf L.sure.ned).contains r || (decide (g0.re ≤ r) && decide (r < g1.re))

/-- The premises of the class at a goal. -/
def premB (L : Lazy LS) (th : Jmp) (g : Gen FM) : Bool :=
  goalOK L g && decide (1 ≤ th.there) && decide (th.there < g.bo) && resB L && th.args.isEmpty &&
  (regsOf L.sure.ned).all (fun r => HoonMap.get g.cond r == Option.none) &&
  (entries L).all (fun e => (regsOf e.2.sure.ned).all fun r => HoonMap.get g.cond r == Option.none) &&
  !g.drop && decide (1 ≤ g.bo)

def atLB (es : List (Nat × Lazy LS)) (k : Nat) : List (Sure LS) := (es.filter (·.1 == k)).map (·.2.sure)

/-- `CopyPreAt` of the copy's inputs at the copy's start `g` (root at `g.bo`). -/
def copyPreB (g : Gen FM) (a b : Lazy LS) : Bool :=
  let fs := (g.bo, a) :: entries a
  let ss := (g.bo, b) :: entries b
  ((fs ++ ss).map (·.1)).eraseDups.all fun k =>
    let Ns := atLB fs k ++ atLB ss k
    Ns.all (fun F => SixNxCheck.cleanB F.ned && (regsOf F.ned).Nodup && (regsOf F.ned).all (· < g.re)) &&
    (Ns.flatMap fun F => regsOf F.ned).Nodup

/-- The parts of a cons under `%next L th`, as `runLC` makes them: `q`'s goal
and state, `q`'s result, `p`'s goal and state, `p`'s result, the copy's
start and its second input. -/
def consParts (p q : Nomm) (L : Lazy LS) (th : Jmp) (g0 : Gen FM) :
    Option ((Lazy LS × Jmp × Gen FM) × (Lazy LS × Jmp × Gen FM) × (NextL LS × Gen FM) × Lazy LS) := do
  let ((hed, tel, o), gS) ← splitL (Map := FM) ⟨L, th⟩ g0
  let (nexh, gS') ← pastL (Map := FM) envR.cod ⟨hed, jmp0 o⟩ q [] gS
  let (nex2, g2) ← runP q (CGoalL.next tel nexh.th) gS'
  let (nex2', g2') ← pastL (Map := FM) envR.cod nex2 p [] g2
  let (nex1, g3) ← runP p (CGoalL.next nexh.laz nex2'.th) g2'
  pure ((tel, nexh.th, gS'), (nexh.laz, nex2'.th, g2'), (nex1, g3), nex2'.laz)

/-- A comparable key of a lazy need. -/
def lzKey (l : Lazy LS) : Need × List (Nat × Need) := (l.sure.ned, (entries l).map fun e => (e.1, e.2.sure.ned))

/-- The top run's result side. -/
def topB (nm : Nomm) (L : Lazy LS) (th : Jmp) (g0 : Gen FM) : List String :=
  match runP nm (CGoalL.next L th) g0 with
  | some (nx, g1) => (if resB nx.laz && goalOK nx.laz g1 then [] else ["res"]) ++
      (if eregsAtB L g0 g1 nx.laz then [] else ["eregsAt"])
  | Option.none => []

/-- Every clause at every sub-run through the cons and `%7`, each failure
tagged with whether the nomm is call-free. -/
def chk : Nomm → Lazy LS → Jmp → Gen FM → List (String × Bool)
  | Nomm.cons p q, L, th, g0 =>
    let pu := (Nomm.cons p q).pure
    (topB (Nomm.cons p q) L th g0).map (·, pu) ++
    (match consParts p q L th g0 with
     | some ((tel, thq, gq), (hed, thp, gp), (nex1, g3), lz2) =>
       (if premB tel thq gq then [] else [("prem:q", pu)]) ++ chk q tel thq gq ++
       (if premB hed thp gp then [] else [("prem:p", pu)]) ++ chk p hed thp gp ++
       (if copyPreB g3 nex1.laz lz2 then [] else [("copy", pu)]) ++
       (if (copyL (Map := FM) nex1 lz2 g3).map (fun (nx, g) => (lzKey nx.laz, nx.th, g.bo, g.re)) ==
           (runP (Nomm.cons p q) (CGoalL.next L th) g0).map (fun (nx, g) => (lzKey nx.laz, nx.th, g.bo, g.re))
        then [] else [("recon", pu)])
     | Option.none => [])
  | Nomm.n7 p q, L, th, g0 =>
    let pu := (Nomm.n7 p q).pure
    (topB (Nomm.n7 p q) L th g0).map (·, pu) ++ chk q L th g0 ++
    (match runP q (CGoalL.next L th) g0 with
     | some (nx, g1) => (if premB nx.laz nx.th g1 then [] else [("prem:7", pu)]) ++ chk p nx.laz nx.th g1
     | Option.none => [])
  | nm, L, th, g0 => (topB nm L th g0).map (·, nm.pure)

/-- `(top runs, failures of each tag among call-free nomms, among the
others)`; only the goals that meet the class's premises. -/
def tallyC (nms : List Nomm) (gs : List Goal) : Nat × List (String × Nat) × List (String × Nat) :=
  let gs' := gs.filter fun (L, th, g) => premB L th g
  let fs := nms.flatMap fun nm => gs'.flatMap fun (L, th, g) => chk nm L th g
  let tags := ["res", "eregsAt", "prem:q", "prem:p", "prem:7", "copy", "recon"]
  (nms.length * gs'.length,
   (tags.map fun t => (t, (fs.filter (· == (t, true))).length)).filter (·.2 != 0),
   (tags.map fun t => (t, (fs.filter (· == (t, false))).length)).filter (·.2 != 0))

def brsP : List Nomm := brs.filter (·.pure)
def testsP : List Nomm := tests.filter (·.pure)
def sixesP : List Nomm := testsP.flatMap fun c => brsP.flatMap fun a => brsP.map fun b => Nomm.n6 c a b
/-- famD: conses and `%7` of two call-free `%6` (and of a `%6` and a leaf). -/
def famD : List Nomm :=
  (sixesP.take 6).flatMap fun a => ((sixesP.drop 6).take 6 ++ brsP).flatMap fun b =>
    [Nomm.cons a b, Nomm.cons b a, Nomm.n7 a b, Nomm.cons (Nomm.cons a b) (Nomm.n4 a)]

#guard (sixesP.length, famD.length, (goalsP.filter fun (L, th, g) => premB L th g).length,
  ((flatGoals LSXCheck.jumps statesH).filter fun (L, th, g) => premB L th g).length) == (32, 240, 300, 90)

/- famD under `goalsP` and the flat goals, famA: no clause fails at any
sub-run. -/
#guard tallyC famD goalsP == (72000, [], [])
#guard tallyC famD (flatGoals LSXCheck.jumps statesH) == (21600, [], [])
#guard tallyC sixes (flatGoals LSXCheck.jumps statesH) == (22050, [], [])

/- famB and famC (run in a scratch copy, 77 s, not repeated at every build):
`tallyC all6 (flatGoals [jmp0 1] [genAtH 4 4]) = (154350, [], [])` and
`tallyC (sixes ++ brs) goalsP = (75600, [], [])`. -/

end GenCheck
end Comp
end SkaModel
end Formalization
