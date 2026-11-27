import lemmas.Ska.CompHintEq
import lemmas.Ska.CompHintData
import lemmas.Ska.CompDirectMCheck
import lemmas.Ska.SofModel

/-!
# `runLCH` against the real compiler, and its code against `+mink` (README Gaps 24)

The data (`CompHintData.lean`, `tools/gen/hintcheck.py --lean`) is the
output of `tools/hoon/hintdump.hoon`: for 39 formulas with hints (static
`%bout`, `%xray`, `%spot`, an unknown tag; dynamic `%spot`, `%slog`,
`%memo`, `%hunk`, `%xray`, an unknown tag with a safe and an unsafe clue, a
cell tag; `%mean` with a safe clue, with a constant arm, with an arm that
reads the subject; `%12`; inside cons, `%4`, `%5`, `%6` (test and
branches), `%7` (both sides), `%10`, an indirect call, a direct call of
`R`, nested), the nomm after the analysis, the raw blocks of the
whole-subject version (`+compiled-mono`) and of the n-ary version, and
the formula.

* `monoOK`: `finishLUCH` of the decoded nomm gives the need, the argument
  count and every block of the whole-subject version, registers and labels
  as the Hoon's: all 39 cases.
* `hNaryEq`: `finishLFCH` with the n-ary need of the dump and the cape `|`
  gives the n-ary blocks: every case but `m03`, the deferred `%mean` with
  `mono` `|` and no constant, which `runLCH` does not model (`none`).
* `semOK`: the whole-subject code `finishLUCH` makes, run by the model of
  the interpreter (`execEntry`, oracle `oracleD`, no scry gate), against
  `minkF` on the formula, on five subjects: the tones agree, traces
  included, frame by frame (`frameOK`: equal, or a `%meac` frame whose
  noun is `+mack` of the `%mean` frame's trap, `FrameRel.meac`).

On the real compiler the same 39 formulas on the same five subjects, with
no scry gate and with a gate, agree with `+mink` (390 runs, 21 of them a
crash with a non-empty trace; `hintcheck.py --sum`).
-/

set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-- The noun of a `need-ordered`, decoded. -/
def needOrdOf : Nat → Noun → Option NeedOrd
  | 0, _ => Option.none
  | n + 1, Noun.cell (Noun.atom t) r =>
      if t = Tag.none then some NeedOrd.none
      else if t = Tag.this then some NeedOrd.this
      else if t = Tag.both then
        match r with
        | Noun.cell h tl => do pure (NeedOrd.both (← needOrdOf n h) (← needOrdOf n tl))
        | _ => Option.none
      else Option.none
  | n + 1, Noun.cell p q => do pure (NeedOrd.pair (← needOrdOf n p) (← needOrdOf n q))
  | _ + 1, Noun.atom _ => Option.none

/-- The noun of a nomm, decoded. -/
def nommOf : Nat → Noun → Option Nomm
  | 0, _ => Option.none
  | n + 1, Noun.cell (Noun.cell a b) q => do
      pure (Nomm.cons (← nommOf n (Noun.cell a b)) (← nommOf n q))
  | n + 1, Noun.cell (Noun.atom t) r =>
      match t, r with
      | 0, Noun.atom p => some (Nomm.n0 p)
      | 1, k => some (Nomm.n1 k)
      | 2, Noun.cell p (Noun.cell q info) => do
          let p ← nommOf n p
          let q ← nommOf n q
          let info ← (match info with
            | Noun.atom 0 => some Option.none
            | Noun.cell (Noun.atom 0) (Noun.cell b k) => do
                let b ← Bell.ofNoun? b
                let k ← (match k with
                  | Noun.atom 0 => some Option.none
                  | Noun.cell (Noun.atom 0) v => some (some v)
                  | _ => Option.none)
                some (some (b, k))
            | _ => Option.none)
          pure (Nomm.n2 p q info)
      | 3, p => do pure (Nomm.n3 (← nommOf n p))
      | 4, p => do pure (Nomm.n4 (← nommOf n p))
      | 5, Noun.cell p q => do pure (Nomm.n5 (← nommOf n p) (← nommOf n q))
      | 6, Noun.cell p (Noun.cell q r) => do
          pure (Nomm.n6 (← nommOf n p) (← nommOf n q) (← nommOf n r))
      | 7, Noun.cell p q => do pure (Nomm.n7 (← nommOf n p) (← nommOf n q))
      | 10, Noun.cell (Noun.cell (Noun.atom a) v) q => do pure (Nomm.n10 a (← nommOf n v) (← nommOf n q))
      | 11, Noun.cell (Noun.atom tag) (Noun.cell q body) => do pure (Nomm.n11s tag (← nommOf n q) body)
      | 11, Noun.cell (Noun.cell (Noun.atom tag) h) (Noun.cell q body) => do
          pure (Nomm.n11d tag (← nommOf n h) (← nommOf n q) body)
      | 12, Noun.cell p q => do pure (Nomm.n12 (← nommOf n p) (← nommOf n q))
      | t, Noun.cell p (Noun.cell b (Noun.cell q (Noun.cell body k))) =>
          if t = Tag.mean then do
            let p ← nommOf n p
            let b ← Bell.ofNoun? b
            let q ← nommOf n q
            let k ← (match k with
              | Noun.atom 0 => some Option.none
              | Noun.cell (Noun.atom 0) v => some (some v)
              | _ => Option.none)
            pure (Nomm.mean p b q body k)
          else Option.none
      | _, _ => Option.none
  | _ + 1, Noun.atom _ => Option.none

/-- The environment of the dump: `R` and `R2` of `CompDirectMCheck.lean`,
impure; every other bell (the arms of the `%mean` traps) pure. -/
def envH : CallEnv := { envD with pure := fun b => !(decide (b = bellR) || decide (b = bellR2)) }

/-- `+sound`: `soundFar` at depth `3` with the nomm of `R`. -/
def sndH (nm : Nomm) (ned : NeedOrd) : Bool :=
  (soundFar (fun b => if b = bellR then some nommR else Option.none) 3 nm ned).getD false

def insertK (k : Nat) : List Nat → List Nat
  | [] => [k]
  | x :: xs => if k = x then x :: xs else if k < x then k :: x :: xs else x :: insertK k xs

def sortK (l : List Nat) : List Nat := l.foldr insertK []

/-- `[need nargs blocks]` of a code, its blocks sorted by label. -/
def outN (c : Straight FM) : Noun :=
  C c.need.toNoun (C (A c.nargs)
    (listNoun (fun (kb : Nat × Blob) => C (A kb.1) kb.2.toNoun)
      ((sortK c.blocks.ks).filterMap fun k => (c.blocks.f k).map fun b => (k, b))))

/-- The parts of a case: nomm, whole-subject output, n-ary output, formula. -/
def parts (j : Noun) : Option (Noun × Noun × Noun × Noun) :=
  match j with
  | Noun.cell nm (Noun.cell mo (Noun.cell na f)) => some (nm, mo, na, f)
  | _ => Option.none

def monoOK (j : Noun) : Bool :=
  match parts j with
  | some (nmN, mo, _, _) =>
      match nommOf 300 nmN with
      | some nm => nm.toNoun == nmN && ((finishLUCH (S := LS) (Map := FM) envH sndH nm).map outN == some mo)
      | Option.none => false
  | Option.none => false

def hNaryOut (j : Noun) : Option Noun :=
  match parts j with
  | some (nmN, _, Noun.cell ned _, _) => do
      let nm ← nommOf 300 nmN
      let ord ← needOrdOf 100 ned
      let c ← finishLFCH (S := LS) (Map := FM) envH sndH nm ord Cape.no (fun ned => (ned, []))
      pure (outN c)
  | _ => Option.none

def hNaryEq (j : Noun) : Bool :=
  match parts j with
  | some (_, _, na, _) => hNaryOut j == some na
  | Option.none => false

/-- A frame of the code against a frame of `+mink`: equal, or a constant
`%mean` whose noun is `+mack` of the trap. -/
def frameOK (fi fm : Frame) : Bool :=
  fi == fm ||
  (fi.1 == Tag.meac && fm.1 == Tag.mean &&
    match fm.2 with
    | Noun.cell h _ => minkF libT (A 0) 500 [] fm.2 h == some (Tone.zero fi.2)
    | _ => false)

def traceOK : Trace → Trace → Bool
  | [], [] => true
  | a :: as, b :: bs => frameOK a b && traceOK as bs
  | _, _ => false

def toneOK : Option Tone → Option Tone → Bool
  | some (Tone.two ti), some (Tone.two tm) => traceOK ti tm
  | a, b => a == b

def subjects : List Noun :=
  [C (A 1) (A 2), C (A 1) (C (A 2) (A 3)), C (C (A 1) (A 2)) (A 3), C (A 0) (A 1), C (C (A 0) (A 1)) (A 0)]

/-- The model's whole-subject code against `+mink`, on the five subjects. -/
def semOK (j : Noun) : Bool :=
  match parts j with
  | some (nmN, _, _, f) =>
      match nommOf 300 nmN with
      | some nm =>
          match (finishLUCH (S := LS) (Map := FM) envH sndH nm : Option (Straight FM)) with
          | some c => subjects.all fun s =>
              toneOK ((execEntry libT oracleD () c [s] [] (A 0)).map Prod.fst) (minkF libT (A 0) 500 [] s f)
          | Option.none => false
      | Option.none => false
  | Option.none => false

/-- The case names where a check fails. -/
def failing (chk : Noun → Bool) : List String :=
  (HintData.all.filter fun (_, j) => !(chk j)).map Prod.fst

#guard HintData.all.length == 39
#guard failing monoOK == []
#guard failing hNaryEq == ["m03"]
#guard hNaryOut HintData.jm03 == Option.none
#guard failing semOK == []

end Comp
end SkaModel
end Formalization
