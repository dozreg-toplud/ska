import lemmas.Ska.CompSixNxCheck

/-!
# The tag clause of the calling class, checked before any proof

README Gaps 12.38, step 1.  Two checks on the executable model, as
`#guard`s:

* `tagTallyP`: the exact statement of `TagLSP` (`CompSixNxRun.lean`) on the
  123,648 runs of `tagTally` (`CompSixNxCheck.lean`), with each of its
  premises evaluated on each run (no entry, `1 ≤ bo`, `drop` false, the
  goal's jump without arguments, the goal's registers below `re`): every run
  meets every premise, and no run adds a key outside the region.
* `tagCTally`: the statement proved by induction on `CallTreeA`
  (`TagCA`, `CompSixNxTag.lean`) at goals WITH entries: in region `[7]`,
  from states whose blocks below `bo` have the tag `[7]` (or `[3, 7]`),
  under the 30 flat lazy goals of `LSXCheck` (entries at labels 1, 2) and
  2 jumps, every run of the 75 + 49 nomms of `LSXCheck` and the 7 branches
  of `SixCheck` adds to `cond` only keys whose tags have `[7]` as a suffix,
  sets only such tags, and leaves a result whose entries' blocks have such
  tags.  Under the states of `statesH` (tags `[]`, which have not `[7]` as a
  suffix) the same runs that make a proxy at a goal entry give a key with
  the tag `[]`: the premise on the goal's entries is needed.
* `cleanSix` (step 4, the clean clause of `LOKTE` for a `%6`): under the 6
  goals with no entry, the 5,880 phase-S runs of the 245 `%6` nomms leave a
  clean sure need, and the 20 runs of their 5 tests under `%pick` leave a
  clean sure need (the `%6`'s sure need is `+copy` of the test's with the
  bunt, so the property the test needs is `PickC`: its sure need under
  `%pick` is clean, which `PickD` does not give).
-/

namespace Formalization
namespace SkaModel
namespace Comp
namespace SixNxTagCheck

open Nock Lazy SixCheck

/-- `genAtH` with the tag `t` on the blocks below `bo`. -/
def genAtT (re bo : Nat) (t : List Nat) : Gen FM :=
  let g := genAtH re bo
  { g with tags := ⟨fun k => if 1 ≤ k ∧ k < bo then some t else Option.none,
    (List.range bo).filter (1 ≤ ·), fun k => by
      by_cases h : 1 ≤ k ∧ k < bo
      · simp [h, List.mem_filter, List.mem_range]
      · simp only [h, if_false, Option.isSome_none, List.mem_filter, List.mem_range, decide_eq_true_eq]
        constructor
        · intro ⟨a, b⟩; exact absurd ⟨b, a⟩ h
        · intro e; cases e⟩ }

def statesT : List (Gen FM) := [genAtT 4 4 [7], genAtT 10 3 [3, 7]]

def regsOf := LSXCheck.regsOf

/-- `CondTag [7] c0 c1`, decided. -/
def condTagB (c0 c1 : FM (Nat × List Nat)) : Bool :=
  (HoonMapKeys.keys c1).all fun k => match HoonMap.get c1 k with
    | some (_, t) => (match HoonMap.get c0 k with | some (_, t') => t' == t | _ => false) || [7].isSuffixOf t
    | Option.none => true

/-- `TagStep [7] g0 g1`, decided on the labels below `g1.bo`. -/
def tagStepB (g0 g1 : Gen FM) : Bool :=
  (List.range g1.bo).all fun o => match HoonMap.get g1.tags o with
    | some t => HoonMap.get g0.tags o == some t || [7].isSuffixOf t
    | Option.none => true

/-- `TagOK [7] g o`, decided. -/
def tagOKB (g : Gen FM) (o : Nat) : Bool :=
  match HoonMap.get g.tags o with
  | some t => [7].isSuffixOf t
  | Option.none => true

/-- One run of `TagLSP`: `(premises all hold, CondTag)`. -/
def oneP (nm : Nomm) (s : Sure LS) (th : Jmp) (g0 : Gen FM) : Option (Bool × Bool) :=
  (runLC envR Option.none nm (CGoalL.next (ofSure s) th) [7] g0).map fun (_, g1) =>
    ((entries (ofSure s : Lazy LS)).isEmpty && decide (1 ≤ g0.bo) && !g0.drop && th.args.isEmpty &&
      (regsOf s.ned).all (· < g0.re), condTagB g0.cond g1.cond)

/-- `(runs, model fails, a premise fails, CondTag fails)`. -/
def tagTallyP (nms : List Nomm) : Nat × Nat × Nat × Nat :=
  let rs := nms.flatMap fun nm => LSXCheck.sures.flatMap fun s => LSXCheck.jumps.flatMap fun th =>
    statesH.map fun g => oneP nm s th g
  (rs.length, (rs.filter (·.isNone)).length, (rs.filter fun x => x.map (!·.1) == some true).length,
    (rs.filter fun x => x.map (!·.2) == some true).length)

-- The 123,648 runs of `tagTally`: every premise of `TagLSP` holds and so
-- does its conclusion.
#guard tagTallyP (brs ++ all6) == (123648, 0, 0, 0)

/-- One run of `TagCA` at a goal with entries: `(the goal's entries tagged,
CondTag, TagStep, the result's entries tagged)`. -/
def oneC (nm : Nomm) (L : Lazy LS) (th : Jmp) (g0 : Gen FM) : Option (Bool × Bool × Bool × Bool) :=
  (runLC envR Option.none nm (CGoalL.next L th) [7] g0).map fun (nex, g1) =>
    ((entries L).all (fun e => tagOKB g0 e.1), condTagB g0.cond g1.cond, tagStepB g0 g1,
      (entries nex.laz).all fun e => tagOKB g1 e.1)

def calls : List Nomm := LSXCheck.cls ++ LSXCheck.cls57 ++ brs

/-- `(runs, compiled, premise, CondTag fails, TagStep fails, result entries fail, runs whose cond grew)`. -/
def tagCTally (sts : List (Gen FM)) : Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  let rs := calls.flatMap fun nm => LSXCheck.lazies.flatMap fun L => LSXCheck.jumps.flatMap fun th =>
    sts.map fun g => ((oneC nm L th g),
      (runLC envR Option.none nm (CGoalL.next L th) [7] g).map fun (_, g1) =>
        (HoonMapKeys.keys g1.cond).length)
  (rs.length, (rs.filter (·.1.isSome)).length,
    (rs.filter fun x => x.1.map (·.1) == some true).length,
    (rs.filter fun x => x.1.map (!·.2.1) == some true).length,
    (rs.filter fun x => x.1.map (!·.2.2.1) == some true).length,
    (rs.filter fun x => x.1.map (!·.2.2.2) == some true).length,
    (rs.filter fun x => x.2.getD 0 != 0).length)

-- 131 nomms, 30 goals, 2 jumps, 2 states with tags `[7]`, `[3, 7]`: 15,720
-- runs, all compiled, every goal's entries tagged, no failure; 8,844 make
-- proxies.
#guard tagCTally statesT == (15720, 15720, 15720, 0, 0, 0, 8844)

-- The same runs from the states of `statesH` (tags `[]`): only the 3,144
-- runs at goals with no entry meet the premise, and 8,688 runs add a key
-- with the tag `[]`.
#guard tagCTally statesH == (15720, 15720, 3144, 8688, 0, 5952, 8844)


/-! ## The clean clause of `LOKTE` for a `%6` (step 4) -/

/-- Under the 6 goals with no entry: `(runs, result's sure clean)` for the
245 `%6` nomms of `SixCheck`, and `(runs, sure clean)` for their 5 tests
under `%pick`. -/
def cleanSix : (Nat × Nat) × (Nat × Nat) :=
  let rs := sixes.flatMap fun nm => LSXCheck.sures.flatMap fun s => LSXCheck.jumps.flatMap fun th =>
    statesH.filterMap fun g => (runLC envR Option.none nm (CGoalL.next (ofSure s) th : CGoalL LS) [7] g).map fun (nex, _) =>
      SixNxCheck.cleanB nex.laz.sure.ned
  let ts := tests.flatMap fun c => LSXCheck.jumps.flatMap fun z => statesH.filterMap fun g =>
    (runLC envR Option.none c (CGoalL.pick z (jmp0 2) : CGoalL LS) [7] g).map fun (nex, _) => SixNxCheck.cleanB nex.laz.sure.ned
  ((rs.length, (rs.filter id).length), (ts.length, (ts.filter id).length))

-- Every one of the 5,880 phase-S runs leaves a clean sure need, and so does
-- every one of the 20 runs of the tests under `%pick`.
#guard cleanSix == ((5880, 5880), (20, 20))

end SixNxTagCheck
end Comp
end SkaModel
end Formalization
