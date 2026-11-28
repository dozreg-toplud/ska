import lemmas.Ska.CompHintCls
import lemmas.Ska.CompHintClsData
import lemmas.Compiler.CompRunHintMeanCheck
import lemmas.Ska.CompHintTreeUEx

/-!
# The class of hinted nomms on real code: the tally (README Gaps 24.22)

Membership of the class `hcV … |>.top` (`CompHintCls.lean`) evaluated on
three dumps, with `+sound` from each entry's own table:

* the 21 entries of `code.long-ska` after the 16 pokes of
  `tools/hoon/hintdump3.hoon` (6 real `!:` gates on an unknown sample, then
  the 10 `%full` pokes; `HintClsData`, `[nomm formula table]`);
* the 36 entries of `tools/hoon/hintmean.hoon` with a `%mean` (31 formulas,
  5 arms of real `~_` gates; `MeanData`, decoded by track Q's `partsM`);
* the 39 hand formulas of `tools/hoon/hintdump.hoon` (`HintData`, `sndH`,
  the environment `envH`).

`+sound` of an entry is `sndM tab` (`soundFar` at depth `3` with the
nomms of the entry's table).  An entry is IN when the class holds and the
decidable part of `HintTab` holds on the dumped table: every direct callee
(`callBells`) and every trap of a `%mean` with a constant (`meanBells`)
is in the table with `pure` `|`.  The rest of `HintTab` (`ring`, `need`,
`N`) is not dumped; `FitH` (the products of a direct call's subject
formula fit the callee's `less`) is not decidable: `fitList` lists the
in-class entries where it is a real premise (a callee `less` whose cape is
not `|`).

`hcWhy` gives the first construct that puts an entry out (outermost first,
then left to right, following `hcV`'s rules); it is not proved, but its
`isNone` is `#guard`ed equal to membership on every entry.
-/

set_option maxRecDepth 8000

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-- The goal kinds of `HV`. -/
inductive HKind | top | reg | sur | ft | zc | dall | sh
  deriving DecidableEq, Repr

def fieldOK : HKind → HV → Bool
  | HKind.top, v => v.top
  | HKind.reg, v => v.reg
  | HKind.sur, v => v.sur
  | HKind.ft, v => v.ft
  | HKind.zc, v => v.zc
  | HKind.dall, v => v.dall
  | HKind.sh, v => v.sh.isSome

def kName : HKind → String
  | HKind.top => "top" | HKind.reg => "reg" | HKind.sur => "sur" | HKind.ft => "ft"
  | HKind.zc => "zc" | HKind.dall => "dall" | HKind.sh => "ShapeH"

/-- The head of a formula and the constructor of a nomm, for a mismatch. -/
def fHead : Noun → String
  | Noun.cell (Noun.atom t) _ => toString t
  | Noun.cell (Noun.cell _ _) _ => "cons"
  | Noun.atom _ => "atom"

def nCtor : Nomm → String
  | Nomm.cons _ _ => "cons" | Nomm.n0 _ => "0" | Nomm.n1 _ => "1" | Nomm.n2 _ _ _ => "2" | Nomm.n3 _ => "3"
  | Nomm.n4 _ => "4" | Nomm.n5 _ _ => "5" | Nomm.n6 _ _ _ => "6" | Nomm.n7 _ _ => "7" | Nomm.n10 _ _ _ => "10"
  | Nomm.n11s _ _ _ => "11s" | Nomm.n11d _ _ _ _ => "11d" | Nomm.n12 _ _ => "12" | Nomm.mean _ _ _ _ _ => "mean"

/-- A formula that is not the nomm's own shape (a `%8`, `%9` desugared by `+fol-loop`). -/
def fMis (f : Noun) (nm : Nomm) : String := "formula %" ++ fHead f ++ " for nomm %" ++ nCtor nm

/-- Why a nomm is not a leaf: its first construct the leaf check has no case for. -/
def leafWhy : Noun → Nomm → String
  | Noun.cell (Noun.cell a1 a2) b, Nomm.cons p q =>
      if (hcLeaf (Noun.cell a1 a2) p).isNone then leafWhy (Noun.cell a1 a2) p else leafWhy b q
  | Noun.cell (Noun.atom 2) (Noun.cell b c), Nomm.n2 p q Option.none =>
      if (hcLeaf b p).isNone then leafWhy b p else leafWhy c q
  | _, Nomm.n2 _ _ (some _) => "direct call"
  | Noun.cell (Noun.atom 7) (Noun.cell b c), Nomm.n7 p q =>
      match hcLeaf b p with
      | some true => leafWhy c q
      | some false => "%7 with p of index |"
      | Option.none => leafWhy b p
  | Noun.cell (Noun.atom 4) b, Nomm.n4 p => leafWhy b p
  | Noun.cell (Noun.atom 3) b, Nomm.n3 p => leafWhy b p
  | Noun.cell (Noun.atom 5) (Noun.cell b c), Nomm.n5 p q =>
      if (hcLeaf b p).isNone then leafWhy b p else leafWhy c q
  | _, Nomm.n6 _ _ _ => "%6"
  | _, Nomm.n10 _ _ _ => "%10"
  | Noun.cell (Noun.atom 11) (Noun.cell (Noun.atom _) fq), Nomm.n11s tag q _ =>
      if hintStatic tag then "kept static hint" else leafWhy fq q
  | Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom _) _) fq), Nomm.n11d tag h q _ =>
      if hintDynamic tag then "kept dynamic hint"
      else match h with
        | Nomm.n1 _ => leafWhy fq q
        | _ => "unkept dynamic hint with a clue not [1 k]"
  | _, Nomm.mean _ _ _ _ _ => "%mean"
  | _, Nomm.n12 _ _ => "%12"
  | f, nm => fMis f nm

mutual
/-- **The first construct that puts `(f, nm)` out of the field `k`** (an
evaluator only: `partial`, never unfolded in a proof). -/
partial def hcWhyK (snd : Nomm → NeedOrd → Bool) (k : HKind) (f : Noun) (nm : Nomm) : Option String :=
  if fieldOK k (hcV snd f nm) then Option.none else some <|
  match hcLeaf f nm with
  | some _ => match k with
      | HKind.zc => "zc: not a direct call [2 [0 1] [1 F] b]"
      | _ => "ShapeH: a leaf other than [0 a]"
  | Option.none =>
  match nm with
  | Nomm.n0 _ => fMis f nm
  | Nomm.n1 _ => fMis f nm
  | Nomm.cons p q => "cons: " ++ leafWhy f (Nomm.cons p q)
  | Nomm.n5 p q => "%5: " ++ leafWhy f (Nomm.n5 p q)
  | Nomm.n4 p =>
      match f with
      | Noun.cell (Noun.atom 4) fb =>
          match k with
          | HKind.sur | HKind.reg | HKind.top => ((hcWhyK snd HKind.reg fb p).getD "?")
          | HKind.sh => ((hcWhyK snd HKind.sh fb p).getD "?")
          | _ => "%4: no " ++ kName k ++ " rule"
      | _ => fMis f nm
  | Nomm.n3 p =>
      match f with
      | Noun.cell (Noun.atom 3) fb =>
          match k with
          | HKind.sur | HKind.reg => ((hcWhyK snd HKind.reg fb p).getD "?")
          | HKind.top => "%3 at the top"
          | _ => "%3: no " ++ kName k ++ " rule"
      | _ => fMis f nm
  | Nomm.n2 p q info =>
      match f, info with
      | Noun.cell (Noun.atom 2) (Noun.cell fb fq), some (b, Option.none) =>
          match k with
          | HKind.top => "direct call at the top"
          | HKind.sur => "direct call under a sure need"
          | HKind.dall | HKind.sh => "direct call: no " ++ kName k ++ " rule"
          | _ =>
            if (hcLeaf fb p).isNone then "direct call: subject formula " ++ leafWhy fb p
            else if !(safeFolFol q && decide (sixCount (Nomm.n2 p q info) ≤ 255) &&
                (match fq, q with
                  | Noun.cell (Noun.atom 1) F, Nomm.n1 F' => F = F' && F = b.fol
                  | _, _ => false)) then "direct call: formula not [1 b.fol]"
            else "zc: direct call with a subject not [0 1]"
      | _, some (_, some _) => "direct call with a constant"
      | _, Option.none => "indirect call: " ++ leafWhy f nm
      | _, _ => fMis f nm
  | Nomm.n7 p q =>
      match f with
      | Noun.cell (Noun.atom 7) (Noun.cell b c) =>
          match p, b with
          | Nomm.n0 1, Noun.cell (Noun.atom 0) (Noun.atom 1) =>
              match k with
              | HKind.sur => (hcWhyK snd HKind.sur c q).getD "?"
              | HKind.reg => (hcWhyK snd HKind.reg c q).getD "?"
              | HKind.ft => (hcWhyK snd HKind.ft c q).getD "?"
              | HKind.top => (hcWhyK snd HKind.top c q).getD "?"
              | _ => "[7 [0 1] q]: no " ++ kName k ++ " rule"
          | _, _ =>
              let pl := hcLeaf b p == some true
              match k with
              | HKind.ft => if pl then (hcWhyK snd HKind.ft c q).getD "?" else "%7: p not a leaf of index &"
              | HKind.reg =>
                  if pl then (hcWhyK snd HKind.ft c q).getD "?"
                  else if !(hcV snd b p).sur then (hcWhyK snd HKind.sur b p).getD "?"
                  else (hcWhyK snd HKind.zc c q).getD "?"
              | HKind.dall => if pl then (hcWhyK snd HKind.dall c q).getD "?" else "%7: p not a leaf of index &"
              | HKind.top =>
                  if pl then (hcWhyK snd HKind.dall c q).getD "?"
                  else "%7 at the top: p not a leaf (nor the [7 kept [4 [0 a]]] form)"
              | HKind.sh => if isS3Body nm then "+sound fails" else "ShapeH: a %7 other than S3"
              | HKind.sur => "%7 under a sure need"
              | HKind.zc => "zc: a %7"
      | _ => fMis f nm
  | Nomm.n10 a v q =>
      match f with
      | Noun.cell (Noun.atom 10) (Noun.cell (Noun.cell (Noun.atom a') fv) fq) =>
          match k with
          | HKind.sur | HKind.reg | HKind.top =>
              if !(a = a' && 2 ≤ a) then "%10 at an axis below 2"
              else if hinted (fun _ => Option.none) v != some true then "%10: value unhinted"
              else if !(match q, fq with
                  | Nomm.n0 1, Noun.cell (Noun.atom 0) (Noun.atom 1) => true
                  | _, _ => false) then "%10: q not [0 1]"
              else (hcWhyK snd HKind.sur fv v).getD "?"
          | _ => "%10: no " ++ kName k ++ " rule"
      | _ => fMis f nm
  | Nomm.n6 c a b =>
      match f with
      | Noun.cell (Noun.atom 6) (Noun.cell fc (Noun.cell fa fb)) =>
          match k with
          | HKind.reg =>
              let va := hcV snd fa a
              let vb := hcV snd fb b
              let brWhy := fun (fx : Noun) (x : Nomm) (vx : HV) =>
                if !vx.reg then "%6 branch: " ++ ((hcWhyK snd HKind.reg fx x).getD "?")
                else "%6 branch: " ++ ((hcWhyK snd HKind.sh fx x).getD "?")
              match hcBranch fa a va, hcBranch fb b vb with
              | Option.none, _ => brWhy fa a va
              | _, Option.none => brWhy fb b vb
              | some _, some _ =>
                  if !hcTest fc c then
                    (if hinted (fun _ => Option.none) c == some true then "%6: hinted test"
                     else "%6: test not [0 a], [3 [0 a]], ?@")
                  else "%6: entry count or sixCount"
          | HKind.top => "%6 at the top"
          | _ => "%6: no " ++ kName k ++ " rule"
      | _ => fMis f nm
  | Nomm.n11s tag q _ =>
      match f with
      | Noun.cell (Noun.atom 11) (Noun.cell (Noun.atom _) fq) =>
          if !hintStatic tag then "unkept static hint over " ++ leafWhy fq q
          else if !snd q NeedOrd.this then "+sound fails"
          else match k with
            | HKind.sur => (hcWhyK snd HKind.sur fq q).getD "?"
            | HKind.reg | HKind.top => (hcWhyK snd HKind.reg fq q).getD "?"
            | _ => "kept static hint: no " ++ kName k ++ " rule"
      | _ => fMis f nm
  | Nomm.n11d tag h q _ =>
      match f with
      | Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom _) fh) fq) =>
          if !hintDynamic tag then
            (match h with
              | Nomm.n1 _ => "unkept dynamic hint over " ++ leafWhy fq q
              | _ => "unkept dynamic hint with a clue not [1 k]")
          else keptWhy snd k fh h q fq (match h with | Nomm.n1 _ => true | _ => false) (stopTag tag)
      | _ => fMis f nm
  | Nomm.mean p _ q _ _ =>
      match f with
      | Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom _) fp) fq) =>
          match k with
          | HKind.dall => "dall: %mean"
          | HKind.sh => "ShapeH: %mean"
          | _ => keptWhy snd k fp p q fq false false
      | _ => fMis f nm
  | Nomm.n12 _ _ => "%12"

/-- The reason at a kept dynamic hint (or a `%mean` with no constant). -/
partial def keptWhy (snd : Nomm → NeedOrd → Bool) (k : HKind) (fh : Noun) (h q : Nomm) (fq : Noun) (clue1 stop : Bool) :
    String :=
    if (hcLeaf fh h).isNone then "kept hint: clue " ++ leafWhy fh h
    else if !hcNB h then "kept hint: clue without NoBondH rule"
    else if !snd q NeedOrd.this then "+sound fails"
    else match k with
      | HKind.sur => (hcWhyK snd HKind.sur fq q).getD "?"
      | HKind.reg | HKind.top => (hcWhyK snd HKind.reg fq q).getD "?"
      | HKind.dall =>
          if !stop then "dall: quiet tag" else if (hcLeaf fq q).isNone then "dall: kept hint over a non-leaf"
          else "dall: body without NoBondH rule"
      | HKind.sh => if !clue1 then "ShapeH: clue not [1 k]" else (hcWhyK snd HKind.sh fq q).getD "?"
      | _ => "kept hint: no " ++ kName k ++ " rule"
end

/-- An entry decoded: name, nomm, formula, its table. -/
structure TEnt where
  name : String
  nomm : Nomm
  fol : Noun
  tab : List MEnt

/-- The 21 code-table entries (`HintClsData`, `[nomm formula table]`). -/
def tEnts : List TEnt :=
  HintClsData.all.filterMap fun (n, j) => match j with
    | Noun.cell nmN (Noun.cell f tab) => (nommOf 300 nmN).map fun nm => ⟨n, nm, f, tabOf tab⟩
    | _ => Option.none

/-- The 36 `%mean` entries (`MeanData`, `partsM`). -/
def mEnts : List TEnt :=
  MeanData.all.filterMap fun (n, j) => match partsM j with
    | some (nmN, _, _, f, _, tab) => (nommOf 300 nmN).map fun nm => ⟨n, nm, f, tab⟩
    | Option.none => Option.none

#guard tEnts.length == 21
#guard mEnts.length == 36

/-- The decidable part of `HintTab` on the dumped table: the first callee
not in the table with `pure` `|`. -/
def tabWhy (tab : List MEnt) (nm : Nomm) : Option String :=
  if (meanBells nm).any fun b => (tabGet tab b).isNone then some "%mean: trap not in the table"
  else if (meanBells nm).any fun b => (tabGet tab b).map (·.pure) != some false then some "%mean: constant (pure trap)"
  else if (callBells nm).any fun b => (tabGet tab b).map (·.pure) != some false then some "direct callee pure or absent"
  else Option.none

def entWhy (e : TEnt) : Option String :=
  match tabWhy e.tab e.nomm with
  | some r => some r
  | Option.none => hcWhyK (sndM e.tab) HKind.top e.fol e.nomm

def entIn (e : TEnt) : Bool := (hcV (sndM e.tab) e.fol e.nomm).top && (tabWhy e.tab e.nomm).isNone

def real : List TEnt := tEnts ++ mEnts

-- consistency of `hcWhy` with the class
#guard real.all fun e => (entWhy e).isNone == entIn e
#guard real.all fun e => (hcWhyK (sndM e.tab) HKind.top e.fol e.nomm).isNone == (hcV (sndM e.tab) e.fol e.nomm).top

/-- Count of each reason, most first. -/
def tallyOf (rs : List String) : List (String × Nat) :=
  let keys := rs.foldl (fun acc r => if acc.contains r then acc else acc ++ [r]) []
  let cnt := keys.map fun r => (r, (rs.filter (· == r)).length)
  cnt.mergeSort fun a b => a.2 > b.2 || (a.2 == b.2 && decide (a.1 ≤ b.1))

def inReal : List String := (real.filter entIn).map (·.name)
def realReasons : List (String × Nat) := tallyOf (real.filterMap entWhy)

/-! ## The tally on the 57 real entries -/

#guard inReal == ["t01", "t03", "t06", "t07", "t15", "t19", "m02", "m03", "m04", "m06", "m07", "m08", "m09", "m10",
  "m11", "m13", "m19", "m23"]
#guard (inReal.length, (tEnts.filter entIn).length, (mEnts.filter entIn).length) == (18, 6, 12)
-- none of the six code-table entries with a kept hint is in
#guard HintClsData.kept.filter inReal.contains == []
-- the five arms of real `~_` gates: none is in
#guard ["g01", "g02", "g03", "g04", "g05"].filter inReal.contains == []

-- **The reasons, most first** (39 out of 57).
#guard realReasons == [("%mean: constant (pure trap)", 17), ("formula %9 for nomm %7", 7), ("%6 at the top", 3),
  ("formula %8 for nomm %7", 3), ("%6 branch: formula %11 for nomm %1", 2), ("%6 branch: formula %9 for nomm %7", 2),
  ("%6 branch: cons: kept dynamic hint", 1), ("%7 at the top: p not a leaf (nor the [7 kept [4 [0 a]]] form)", 1),
  ("cons: %6", 1), ("cons: %mean", 1), ("direct call at the top", 1)]

/-- The reason of each real entry out. -/
def realWhy : List (String × String) := real.filterMap fun e => (entWhy e).map fun r => (e.name, r)

#guard realWhy == [("t02", "formula %9 for nomm %7"), ("t04", "formula %9 for nomm %7"),
  ("t05", "%6 branch: formula %9 for nomm %7"), ("t08", "formula %9 for nomm %7"),
  ("t09", "%6 branch: formula %9 for nomm %7"), ("t10", "%6 at the top"), ("t11", "direct call at the top"),
  ("t12", "formula %9 for nomm %7"), ("t13", "%6 at the top"), ("t14", "%6 branch: cons: kept dynamic hint"),
  ("t16", "formula %9 for nomm %7"), ("t17", "formula %9 for nomm %7"), ("t18", "formula %8 for nomm %7"),
  ("t20", "formula %8 for nomm %7"), ("t21", "%6 branch: formula %11 for nomm %1"),
  ("m01", "%mean: constant (pure trap)"), ("m05", "%mean: constant (pure trap)"),
  ("m12", "%mean: constant (pure trap)"), ("m14", "%mean: constant (pure trap)"), ("m15", "cons: %6"),
  ("m16", "%mean: constant (pure trap)"), ("m17", "formula %8 for nomm %7"),
  ("m18", "%mean: constant (pure trap)"), ("m20", "%mean: constant (pure trap)"), ("m21", "%6 at the top"),
  ("m22", "%mean: constant (pure trap)"), ("m24", "%mean: constant (pure trap)"), ("m25", "cons: %mean"),
  ("m26", "%mean: constant (pure trap)"), ("m27", "%7 at the top: p not a leaf (nor the [7 kept [4 [0 a]]] form)"),
  ("m28", "%mean: constant (pure trap)"), ("m29", "%mean: constant (pure trap)"),
  ("m30", "%mean: constant (pure trap)"), ("m31", "%mean: constant (pure trap)"),
  ("g01", "%mean: constant (pure trap)"), ("g02", "formula %9 for nomm %7"),
  ("g03", "%mean: constant (pure trap)"), ("g04", "%mean: constant (pure trap)"),
  ("g05", "%6 branch: formula %11 for nomm %1")]

/-- The entries out only by the table (a constant `%mean`): the class
itself holds of their nomm. -/
def structOnly : List String :=
  (real.filter fun e => (hcV (sndM e.tab) e.fol e.nomm).top && (tabWhy e.tab e.nomm).isSome).map (·.name)

#guard structOnly == ["m01", "m05", "m12", "m18", "m22", "m28", "m29"]

/-- In-class real entries with a direct callee whose `less` cape is not `|`
(their `FitH` is a premise about the subject). -/
def fitList : List String :=
  (real.filter fun e => entIn e && (callBells e.nomm).any fun b => match b.less with
    | Sock.mk Cape.no _ => false
    | _ => true).map (·.name)

-- no in-class real entry has a direct call, so `FitH` is `True` on all of them
#guard fitList == []
#guard (real.filter fun e => entIn e && !(callBells e.nomm).isEmpty).isEmpty

/-! ## The 39 hand formulas -/

def hEnts : List (String × Nomm × Noun) :=
  HintData.all.filterMap fun (n, _) => (dumped n).bind fun (nmN, f) => (nommOf 300 nmN).map fun nm => (n, nm, f)

#guard hEnts.length == 39

/-- `HintTab`'s decidable part at `envH`: every callee and constant trap impure. -/
def hTabWhy (nm : Nomm) : Option String :=
  if (meanBells nm).any fun b => envH.pure b then some "%mean: constant (pure trap)"
  else if (callBells nm).any fun b => envH.pure b then some "direct callee pure"
  else Option.none

def hIn (e : String × Nomm × Noun) : Bool := (hcV sndH e.2.2 e.2.1).top
def hWhy (e : String × Nomm × Noun) : Option String := hcWhyK sndH HKind.top e.2.2 e.2.1

#guard hEnts.all fun e => (hWhy e).isNone == hIn e

-- The class on the 39 (`sndH`): 22, the 20 of `outReasonTen` and `m02`, `m03`.
#guard (hEnts.filter hIn).map (·.1) == ["s01", "s02", "s03", "s05", "s06", "d01", "d02", "d03", "d06", "d08", "d09",
  "d10", "d13", "d14", "d18", "d19", "d20", "d21", "d23", "m01", "m02", "m03"]
-- With `HintTab` at `envH` (every trap of `envH` pure): 21, `m02`'s `%mean` has a constant there.
#guard (hEnts.filter fun e => hIn e && (hTabWhy e.2.1).isNone).map (·.1) == ["s01", "s02", "s03", "s05", "s06",
  "d01", "d02", "d03", "d06", "d08", "d09", "d10", "d13", "d14", "d18", "d19", "d20", "d21", "d23", "m01", "m03"]
#guard (hEnts.filter fun e => hIn e && (hTabWhy e.2.1).isSome).map (fun e => (e.1, hTabWhy e.2.1)) ==
  [("m02", some "%mean: constant (pure trap)")]

-- **The reasons on the 39, most first** (17 out of the class).
#guard tallyOf (hEnts.filterMap hWhy) == [("%12", 4),
  ("%7 at the top: p not a leaf (nor the [7 kept [4 [0 a]]] form)", 3), ("%6 at the top", 2),
  ("unkept dynamic hint with a clue not [1 k]", 2), ("%5: kept dynamic hint", 1), ("cons: %12", 1),
  ("cons: kept dynamic hint", 1), ("cons: kept static hint", 1), ("formula %11 for nomm %11d", 1),
  ("formula %8 for nomm %7", 1)]
#guard (hEnts.filter fun e => !hIn e).map (fun e => (e.1, (hWhy e).getD "")) ==
  [("s04", "cons: kept static hint"), ("s07", "%7 at the top: p not a leaf (nor the [7 kept [4 [0 a]]] form)"),
  ("d04", "unkept dynamic hint with a clue not [1 k]"), ("d05", "unkept dynamic hint with a clue not [1 k]"),
  ("d07", "formula %11 for nomm %11d"), ("d11", "cons: kept dynamic hint"),
  ("d12", "%7 at the top: p not a leaf (nor the [7 kept [4 [0 a]]] form)"), ("d15", "%5: kept dynamic hint"),
  ("d16", "%6 at the top"), ("d17", "%6 at the top"), ("d22", "formula %8 for nomm %7"),
  ("m04", "%7 at the top: p not a leaf (nor the [7 kept [4 [0 a]]] form)"), ("c01", "%12"), ("c02", "%12"),
  ("c03", "cons: %12"), ("c04", "%12"), ("c05", "%12")]

end Comp
end SkaModel
end Formalization
