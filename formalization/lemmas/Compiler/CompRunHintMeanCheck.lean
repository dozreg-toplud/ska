import lemmas.Ska.CompHintCheck
import lemmas.Compiler.CompRunHintMeanData

/-!
# `%mean` on the real compiler against `runLCH` (README Gaps 25)

The data (`CompRunHintMeanData.lean`, `tools/gen/runhintmean.py --lean`) is
the output of `tools/hoon/hintmean.hoon`: 36 entries of `code.long-ska`
holding a `%mean` hint, one per case: 31 formulas on a subject that knows
nothing (the trap's arm a constant, computed from constants, read from a
known payload, reading the subject, crashing, forking, hinted, calling `R`;
a constant clue, a clue with an unknown battery; the hint around `%4`, a
`%6`, a cons with a `%6`, a direct call of `R`, a `%spot`; the hint in a
branch of a `%6`, in its test, under a `%spot`, in either half of a cons,
under `%7`, `%10`, under another `%mean`) and the arms of five real gates
on an unknown sample (`~_` with a constant tank and with one that reads the
sample, under `!:` and not, around a recursive call).  Per entry: the
nomm, the raw blocks of the whole-subject version (`mono` `&`) and of the
n-ary version (`mono` `|`), the formula, the subjects run, and a table of
the bells the nomm names (`pure`, nomm, n-ary need).

* `monoOKM`: `finishLUCH` of the decoded nomm, with the environment of the
  table (`envM`, `sndM`), gives the need, the argument count and every
  block of the whole-subject version, registers and labels as the Hoon's.
* `naryOKM`: the same for `finishLFCH` and the n-ary version (cape `|`):
  every entry whose `%mean`s all have a constant; on the 18 with a
  `%mean` and no constant the model is `none` (the soft calls).
* `semOKM`: the model's whole-subject code under `execEntry` against
  `minkF` on the entry's subjects, traces frame by frame (`frameOK`): all
  but the two recursive gates (the oracle has no code for their arm).
* `konstOK`: every `%mean` with a constant (`meanKonst` `some`) has
  `sndM p [%none ~]`, so the model's constant case never returns `none`
  for it (and the Hoon's `+soft-new`/`+soft-bond` are never reached at
  `mono` `&`).

On the real compiler (`runhintmean.py --sum`) the raw whole-subject code of
the 36 entries agrees with `+mink` on all 360 runs (five subjects, with and
without a scry gate).
-/

set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-- An entry of the dumped table. -/
structure MEnt where
  bell : Bell
  pure : Bool
  nomm : Nomm
  need : Option NeedOrd

def nounList : Nat → Noun → List Noun
  | 0, _ => []
  | n + 1, Noun.cell h t => h :: nounList n t
  | _ + 1, Noun.atom _ => []

def mentOf (e : Noun) : Option MEnt :=
  match e with
  | Noun.cell b (Noun.cell p (Noun.cell nm u)) => do
      let b ← Bell.ofNoun? b
      let nm ← nommOf 300 nm
      let ned ← (match u with
        | Noun.atom 0 => some Option.none
        | Noun.cell (Noun.atom 0) v => (needOrdOf 100 v).map some
        | _ => Option.none)
      pure ⟨b, p == A 0, nm, ned⟩
  | _ => Option.none

def tabOf (t : Noun) : List MEnt := (nounList 1000 t).filterMap mentOf

def tabGet (tab : List MEnt) (b : Bell) : Option MEnt := tab.find? fun e => decide (e.bell = b)

/-- The environment of an entry: `pure` and the callee needs from the table
(`R`, `R2` as in `envD` when absent). -/
def envM (tab : List MEnt) : CallEnv :=
  { envD with
    need := fun b => match (tabGet tab b).bind (·.need) with
      | some n => some n
      | Option.none => envD.need b
    pure := fun b => ((tabGet tab b).map (·.pure)).getD false
    cod := fun b => (tabGet tab b).map (·.pure) }

/-- `+sound` with the nomms of the table. -/
def sndM (tab : List MEnt) (nm : Nomm) (ned : NeedOrd) : Bool :=
  (soundFar (fun b => (tabGet tab b).map (·.nomm)) 3 nm ned).getD false

/-- The parts of an entry. -/
def partsM (j : Noun) : Option (Noun × Noun × Noun × Noun × Noun × List MEnt) :=
  match j with
  | Noun.cell nm (Noun.cell mo (Noun.cell na (Noun.cell f (Noun.cell subs tab)))) =>
      some (nm, mo, na, f, subs, tabOf tab)
  | _ => Option.none

def monoOKM (j : Noun) : Bool :=
  match partsM j with
  | some (nmN, mo, _, _, _, tab) =>
      match nommOf 300 nmN with
      | some nm => nm.toNoun == nmN &&
          ((finishLUCH (S := LS) (Map := FM) (envM tab) (sndM tab) nm).map outN == some mo)
      | Option.none => false
  | Option.none => false

def naryOutM (j : Noun) : Option Noun :=
  match partsM j with
  | some (nmN, _, Noun.cell ned _, _, _, tab) => do
      let nm ← nommOf 300 nmN
      let ord ← needOrdOf 100 ned
      let c ← finishLFCH (S := LS) (Map := FM) (envM tab) (sndM tab) nm ord Cape.no (fun ned => (ned, []))
      pure (outN c)
  | _ => Option.none

def naryOKM (j : Noun) : Bool :=
  match partsM j with
  | some (_, _, na, _, _, _) => naryOutM j == some na
  | Option.none => false

def semOKM (j : Noun) : Bool :=
  match partsM j with
  | some (nmN, _, _, f, subs, tab) =>
      match nommOf 300 nmN with
      | some nm =>
          match (finishLUCH (S := LS) (Map := FM) (envM tab) (sndM tab) nm : Option (Straight FM)) with
          | some c => (nounList 10 subs).all fun s =>
              toneOK ((execEntry libT oracleD () c [s] [] (A 0)).map Prod.fst) (minkF libT (A 0) 2000 [] s f)
          | Option.none => false
      | Option.none => false
  | Option.none => false

/-- Per `%mean` node: whether `+mean-konst` gives a constant, and `+sound`
of the trap on `[%none ~]`. -/
def meanNodes (env : CallEnv) (snd : Nomm → NeedOrd → Bool) : Nomm → List (Bool × Bool)
  | Nomm.cons p q => meanNodes env snd p ++ meanNodes env snd q
  | Nomm.n2 p q _ => meanNodes env snd p ++ meanNodes env snd q
  | Nomm.n3 p => meanNodes env snd p
  | Nomm.n4 p => meanNodes env snd p
  | Nomm.n5 p q => meanNodes env snd p ++ meanNodes env snd q
  | Nomm.n6 p q r => meanNodes env snd p ++ meanNodes env snd q ++ meanNodes env snd r
  | Nomm.n7 p q => meanNodes env snd p ++ meanNodes env snd q
  | Nomm.n10 _ v q => meanNodes env snd v ++ meanNodes env snd q
  | Nomm.n11s _ q _ => meanNodes env snd q
  | Nomm.n11d _ h q _ => meanNodes env snd h ++ meanNodes env snd q
  | Nomm.n12 p q => meanNodes env snd p ++ meanNodes env snd q
  | Nomm.mean p b q _ k =>
      ((meanKonst env b k).isSome, snd p NeedOrd.none) :: (meanNodes env snd p ++ meanNodes env snd q)
  | _ => []

def nodesM (j : Noun) : List (Bool × Bool) :=
  match partsM j with
  | some (nmN, _, _, _, _, tab) =>
      match nommOf 300 nmN with
      | some nm => meanNodes (envM tab) (sndM tab) nm
      | Option.none => []
  | Option.none => []

def konstOK (j : Noun) : Bool := (nodesM j).all fun (k, s) => !k || s

def failingM (chk : Noun → Bool) : List String :=
  (MeanData.all.filter fun (_, j) => !(chk j)).map Prod.fst

/-- The entries with a `%mean` node: with a constant, without. -/
def withKonst : List String := (MeanData.all.filter fun (_, j) => (nodesM j).any (·.1)).map Prod.fst
def withoutKonst : List String := (MeanData.all.filter fun (_, j) => (nodesM j).any (!·.1)).map Prod.fst

#guard MeanData.all.length == 36
#guard withKonst == ["m01", "m05", "m12", "m14", "m16", "m18", "m20", "m22", "m24", "m26", "m28", "m29", "m30",
  "m31", "g01", "g03", "g04"]
#guard withoutKonst == ["m02", "m03", "m04", "m06", "m09", "m10", "m11", "m13", "m15", "m17", "m19", "m21", "m23",
  "m25", "m27", "m29", "g02", "g05"]
/- The whole-subject version (`mono` `&`): every entry, constants or not. -/
#guard failingM monoOKM == []
/- The n-ary version (`mono` `|`): every entry but those with a `%mean` and
no constant, where the model is `none` (the soft calls), not a wrong output. -/
#guard failingM naryOKM == withoutKonst
#guard (MeanData.all.filter fun (_, j) => (naryOutM j).isSome && !(naryOKM j)) == []
/- The model's code against `minkF`: all but the two recursive gates, whose
arm calls itself, a bell the interpreter's oracle `oracleD` has no code for. -/
#guard failingM semOKM == ["g04", "g05"]
/- Every constant `%mean` has `+sound p [%none ~]`. -/
#guard failingM konstOK == []

end Comp
end SkaModel
end Formalization
