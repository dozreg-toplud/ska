import lemmas.Ska.CompHintCheck

/-!
# The kept dynamic `stopTag` hint at the top, run on chosen subjects (README Gaps 24.15)

Step 1 of the frame case: on the dumped `d01`, `d02`, `d08`, `d21`, `d23`,
`m01` (a `%spot`, `%hunk` or `%mean` hint at the top with a safe clue), the
whole-subject code of `finishLUCH` (`envH`, `sndH`) under the model of the
interpreter (`execEntry`, `oracleD`, no scry gate) against `minkF` on the
formula, at the entry trace `[]` and at a non-empty entry trace
`[(%spot, 7)]`, on subjects chosen so that at least one crashes inside the
hinted formula (after the frame is pushed) and one crashes in the clue
(before it is pushed) where the clue can crash.  The tones are compared with
`toneOK` (traces frame by frame); `crashIn` checks that the inner crash
carries the hint's frame on both sides, `crashOut` that a crash in the
clue carries none.
-/

set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-- The code of a dumped case, and its formula. -/
def codeOf (j : Noun) : Option (Straight FM × Noun) :=
  match parts j with
  | some (nmN, _, _, f) => do
      let nm ← nommOf 300 nmN
      let c ← (finishLUCH (S := LS) (Map := FM) envH sndH nm : Option (Straight FM))
      pure (c, f)
  | Option.none => Option.none

/-- Both tones on a subject at an entry trace. -/
def bothTones (j : Noun) (t : Trace) (s : Noun) : Option (Option Tone × Option Tone) :=
  (codeOf j).map fun (c, f) =>
    ((execEntry libT oracleD () c [s] t (A 0)).map Prod.fst, minkF libT (A 0) 500 t s f)

/-- The two tones agree, traces frame by frame. -/
def agreeOn (j : Noun) (t : Trace) (s : Noun) : Bool :=
  match bothTones j t s with
  | some (a, b) => toneOK a b
  | Option.none => false

/-- Both sides crash with the frame `(tag, v)` on top of the entry trace. -/
def crashIn (j : Noun) (t : Trace) (s : Noun) (tag : Nat) (v : Noun) : Bool :=
  match bothTones j t s with
  | some (some (Tone.two ti), some (Tone.two tm)) => ti == (tag, v) :: t && tm == (tag, v) :: t
  | _ => false

/-- Both sides crash with the entry trace (a crash in the clue). -/
def crashOut (j : Noun) (t : Trace) (s : Noun) : Bool :=
  match bothTones j t s with
  | some (some (Tone.two ti), some (Tone.two tm)) => ti == t && tm == t
  | _ => false

def trSpot : Trace := [(Tag.spot, A 7)]

/-- The subjects: a cell whose tail is an atom, one whose tail is a cell,
one whose head is a cell, an atom. -/
def subjF : List Noun := [C (A 1) (A 2), C (A 1) (C (A 2) (A 3)), C (C (A 5) (A 6)) (A 3), A 4]

def caseNames : List String := ["d01", "d02", "d08", "d21", "d23", "m01"]

def caseJ (n : String) : Noun := ((HintData.all.lookup n).getD (A 0))

-- The six are the hint at the top with a `stopTag` tag.
#guard caseNames.all fun n => (HintData.all.lookup n).isSome
#guard caseNames.all fun n => (codeOf (caseJ n)).isSome

-- Results and traces agree on every subject, at both entry traces.
#guard caseNames.all fun n => subjF.all fun s => agreeOn (caseJ n) [] s && agreeOn (caseJ n) trSpot s

-- `d01` `[11 [%spot [1 [1 2] 3]] [0 3]]`: the atom crashes inside, under the frame.
#guard crashIn HintData.jd01 [] (A 4) Tag.spot (C (C (A 1) (A 2)) (A 3))
#guard crashIn HintData.jd01 trSpot (A 4) Tag.spot (C (C (A 1) (A 2)) (A 3))
#guard bothTones HintData.jd01 [] (C (A 1) (A 2)) == some (some (Tone.zero (A 2)), some (Tone.zero (A 2)))
-- `d02` `[11 [%spot [0 2]] [4 [0 3]]]`: a cell tail crashes inside; the atom in the clue.
#guard crashIn HintData.jd02 [] (C (A 1) (C (A 2) (A 3))) Tag.spot (A 1)
#guard crashIn HintData.jd02 trSpot (C (C (A 5) (A 6)) (C (A 2) (A 3))) Tag.spot (C (A 5) (A 6))
#guard crashOut HintData.jd02 trSpot (A 4)
#guard bothTones HintData.jd02 [] (C (A 1) (A 2)) == some (some (Tone.zero (A 3)), some (Tone.zero (A 3)))
-- `d08` `[11 [%hunk [0 2]] [4 [0 3]]]`
#guard crashIn HintData.jd08 trSpot (C (A 1) (C (A 2) (A 3))) Tag.hunk (A 1)
#guard crashOut HintData.jd08 [] (A 4)
-- `d21` `[11 [%spot [1 0]] [2 [0 3] [0 2]]]`: the called formula crashes, and
-- a called formula with a `%spot` of its own crashes under two frames.
#guard crashIn HintData.jd21 [] (C (C (A 0) (A 5)) (A 1)) Tag.spot (A 0)
#guard agreeOn HintData.jd21 trSpot (C (n3 (A 11) (C (A Tag.spot) (C (A 1) (A 9))) (C (A 0) (A 5))) (A 1))
#guard bothTones HintData.jd21 [] (C (n3 (A 11) (C (A Tag.spot) (C (A 1) (A 9))) (C (A 0) (A 5))) (A 1)) ==
  some (some (Tone.two [(Tag.spot, A 9), (Tag.spot, A 0)]), some (Tone.two [(Tag.spot, A 9), (Tag.spot, A 0)]))
#guard bothTones HintData.jd21 [] (C (C (A 0) (A 1)) (A 8)) == some (some (Tone.zero (A 8)), some (Tone.zero (A 8)))
-- `d23` `[11 [%spot [0 6]] [0 3]]`: a crash inside cannot happen (the clue
-- reads inside the tail); a crash in the clue carries no frame.
#guard crashOut HintData.jd23 trSpot (C (A 1) (A 2))
#guard bothTones HintData.jd23 [] (C (A 1) (C (A 2) (A 3))) ==
  some (some (Tone.zero (C (A 2) (A 3))), some (Tone.zero (C (A 2) (A 3))))
-- `m01` `[11 [%mean [1 [1 %leaf 120]]] [4 [0 3]]]`: the `%mean` frame holds the trap.
#guard crashIn HintData.jm01 [] (C (A 1) (C (A 2) (A 3))) Tag.mean (C (A 1) (C (A 1717658988) (A 120)))
#guard crashIn HintData.jm01 trSpot (A 4) Tag.mean (C (A 1) (C (A 1717658988) (A 120)))

end Comp
end SkaModel
end Formalization
