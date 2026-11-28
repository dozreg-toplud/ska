import lemmas.Ska.CompHintW
import lemmas.Ska.CompHintClsTally

/-!
# The wider class on real code: the tally (README Gaps 24.23)

Membership of `hcW … |>.top` (`CompHintW.lean`) on the same three dumps as
`CompHintClsTally.lean` (the 21 code-table entries, the 36 `%mean` entries,
the 39 hand formulas), with `+sound` from each entry's own table.  An entry
is IN when the class holds and the decidable part of `HintTabW` holds on the
dumped table (every direct callee in the table with `pure` `|`; the traps of
`%mean` are no longer asked impure).  `FitHW` (the fit of the callees'
`less`, the battery read, and `+mack` of the constant `%mean`'s traps) is a
premise about the subject, not decided here.

`hcWhyW` names the first construct that puts an entry out (an evaluator,
`partial`, never unfolded in a proof); its `isNone` is `#guard`ed equal to
membership on every entry.
-/

set_option maxRecDepth 8000

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-- The goal kinds of `HW`. -/
inductive WKind | top | reg | sur | ft | zc | dall | sh | st
  deriving DecidableEq, Repr

def fieldW : WKind → HW → Bool
  | WKind.top, v => v.top
  | WKind.reg, v => v.reg
  | WKind.sur, v => v.sur
  | WKind.ft, v => v.ft
  | WKind.zc, v => v.zc
  | WKind.dall, v => v.dall
  | WKind.sh, v => v.sh.isSome
  | WKind.st, v => v.st.isSome

def wName : WKind → String
  | WKind.top => "top" | WKind.reg => "reg" | WKind.sur => "sur" | WKind.ft => "ft"
  | WKind.zc => "zc" | WKind.dall => "dall" | WKind.sh => "ShapeH" | WKind.st => "st"

mutual
/-- **The first construct that puts `(f, nm)` out of the field `k`** (an
evaluator only: `partial`, never unfolded in a proof). -/
partial def hcWhyW (snd : Nomm → NeedOrd → Bool) (k : WKind) (f : Noun) (nm : Nomm) : Option String :=
  if fieldW k (hcW snd f nm) then Option.none else some <|
  match hcLeaf f nm with
  | some _ => match k with
      | WKind.zc => "zc: not a direct call [2 [0 1] [1 F] b]"
      | WKind.st => "%6 at the top, branch: a leaf not a pure fragment"
      | _ => "ShapeH: a leaf other than [0 a]"
  | Option.none =>
  match nm with
  | Nomm.n0 _ => fMis f nm
  | Nomm.n1 k' => if hcDropK f k' then "dropped hint over a constant: no " ++ wName k ++ " rule" else fMis f nm
  | Nomm.cons p q => "cons: " ++ leafWhy f (Nomm.cons p q)
  | Nomm.n5 p q => "%5: " ++ leafWhy f (Nomm.n5 p q)
  | Nomm.n4 p =>
      match f with
      | Noun.cell (Noun.atom 4) fb =>
          match k with
          | WKind.sur | WKind.reg | WKind.top => ((hcWhyW snd WKind.reg fb p).getD "?")
          | WKind.sh => ((hcWhyW snd WKind.sh fb p).getD "?")
          | _ => "%4: no " ++ wName k ++ " rule"
      | _ => fMis f nm
  | Nomm.n3 p =>
      match f with
      | Noun.cell (Noun.atom 3) fb =>
          match k with
          | WKind.sur | WKind.reg => ((hcWhyW snd WKind.reg fb p).getD "?")
          | WKind.top => "%3 at the top"
          | _ => "%3: no " ++ wName k ++ " rule"
      | _ => fMis f nm
  | Nomm.n2 p q info =>
      match f, info with
      | Noun.cell (Noun.atom 2) (Noun.cell fb fq), some (b, Option.none) =>
          match k with
          | WKind.sur => "direct call under a sure need"
          | WKind.sh | WKind.st => "direct call: no " ++ wName k ++ " rule"
          | _ =>
            if (hcLeaf fb p).isNone then "direct call: subject formula " ++ leafWhy fb p
            else if !(safeFolFol q && decide (sixCount (Nomm.n2 p q info) ≤ 255) &&
                (match fq, q with
                  | Noun.cell (Noun.atom 1) F, Nomm.n1 F' => F = F' && F = b.fol
                  | Noun.cell (Noun.atom 0) (Noun.atom _), Nomm.n1 F' => F' = b.fol
                  | _, _ => false)) then "direct call: formula not [1 b.fol] or [0 a]"
            else "zc: direct call with a subject not [0 1]"
      | _, some (_, some _) => "direct call with a constant"
      | _, Option.none => "indirect call: " ++ leafWhy f nm
      | _, _ => fMis f nm
  | Nomm.n7 p q =>
      let gen := fun (b c : Noun) =>
        let pl := hcLeaf b p == some true
        match k with
        | WKind.ft => if pl then (hcWhyW snd WKind.ft c q).getD "?" else "%7: p not a leaf of index &"
        | WKind.reg =>
            if pl then (hcWhyW snd WKind.ft c q).getD "?"
            else if !(hcW snd b p).sur then (hcWhyW snd WKind.sur b p).getD "?"
            else (hcWhyW snd WKind.zc c q).getD "?"
        | WKind.dall => if pl then (hcWhyW snd WKind.dall c q).getD "?" else "%7: p not a leaf of index &"
        | WKind.top =>
            if pl then (hcWhyW snd WKind.dall c q).getD "?"
            else "%7 at the top: p not a leaf (nor the [7 kept [4 [0 a]]] form)"
        | WKind.sh => "ShapeH: a %7 other than S3 (any axis)"
        | WKind.st => "%6 at the top, branch: a %7"
        | WKind.sur => "%7 under a sure need"
        | WKind.zc => "zc: a %7"
      match f with
      | Noun.cell (Noun.atom 7) (Noun.cell b c) =>
          match p, b with
          | Nomm.n0 1, Noun.cell (Noun.atom 0) (Noun.atom 1) =>
              match k with
              | WKind.sur => (hcWhyW snd WKind.sur c q).getD "?"
              | WKind.reg => (hcWhyW snd WKind.reg c q).getD "?"
              | WKind.ft => (hcWhyW snd WKind.ft c q).getD "?"
              | WKind.top => (hcWhyW snd WKind.top c q).getD "?"
              | _ => "[7 [0 1] q]: no " ++ wName k ++ " rule"
          | _, _ => gen b c
      | Noun.cell (Noun.atom 9) (Noun.cell (Noun.atom a) c) =>
          gen c (Noun.cell (Noun.atom 2) (Noun.cell (Noun.cell (Noun.atom 0) (Noun.atom 1)) (Noun.cell (Noun.atom 0) (Noun.atom a))))
      | Noun.cell (Noun.atom 8) (Noun.cell (Noun.cell a1 a2) c) =>
          gen (Noun.cell (Noun.cell a1 a2) (Noun.cell (Noun.atom 0) (Noun.atom 1))) c
      | _ => fMis f nm
  | Nomm.n10 a v q =>
      match f with
      | Noun.cell (Noun.atom 10) (Noun.cell (Noun.cell (Noun.atom a') fv) fq) =>
          match k with
          | WKind.sur | WKind.reg | WKind.top =>
              if !(a = a' && 2 ≤ a) then "%10 at an axis below 2"
              else if hinted (fun _ => Option.none) v != some true then "%10: value unhinted"
              else if !(match q, fq with
                  | Nomm.n0 1, Noun.cell (Noun.atom 0) (Noun.atom 1) => true
                  | _, _ => false) then "%10: q not [0 1]"
              else (hcWhyW snd WKind.sur fv v).getD "?"
          | _ => "%10: no " ++ wName k ++ " rule"
      | _ => fMis f nm
  | Nomm.n6 c a b =>
      match f with
      | Noun.cell (Noun.atom 6) (Noun.cell fc (Noun.cell fa fb)) =>
          match k with
          | WKind.reg =>
              let va := hcV snd fa a
              let vb := hcV snd fb b
              let brWhy := fun (fx : Noun) (x : Nomm) (vx : HV) =>
                if !vx.reg then "%6 branch: " ++ ((hcWhyW snd WKind.reg fx x).getD "?")
                else "%6 branch: " ++ ((hcWhyW snd WKind.sh fx x).getD "?")
              match hcBranch fa a va, hcBranch fb b vb with
              | Option.none, _ => brWhy fa a va
              | _, Option.none => brWhy fb b vb
              | some _, some _ =>
                  if !hcTest fc c then
                    (if hinted (fun _ => Option.none) c == some true then "%6: hinted test"
                     else "%6: test not [0 a], [3 [0 a]], ?@")
                  else "%6: entry count or sixCount"
          | WKind.top | WKind.st =>
              if !(sixTopLeafB true fc c) then "%6 at the top: test not a pure fragment"
              else match (hcW snd fa a).st, (hcW snd fb b).st with
                | Option.none, _ => (hcWhyW snd WKind.st fa a).getD "?"
                | _, Option.none => (hcWhyW snd WKind.st fb b).getD "?"
                | _, _ => "%6 at the top: entry count"
          | _ => "%6: no " ++ wName k ++ " rule"
      | _ => fMis f nm
  | Nomm.n11s tag q _ =>
      match f with
      | Noun.cell (Noun.atom 11) (Noun.cell (Noun.atom _) fq) =>
          if !hintStatic tag then "unkept static hint over " ++ leafWhy fq q
          else if !snd q NeedOrd.this then "+sound fails"
          else match k with
            | WKind.sur => (hcWhyW snd WKind.sur fq q).getD "?"
            | WKind.reg | WKind.top => (hcWhyW snd WKind.reg fq q).getD "?"
            | _ => "kept static hint: no " ++ wName k ++ " rule"
      | _ => fMis f nm
  | Nomm.n11d tag h q _ =>
      match f with
      | Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom _) fh) fq) =>
          if !hintDynamic tag then
            (match h with
              | Nomm.n1 _ => "unkept dynamic hint over " ++ leafWhy fq q
              | _ => "unkept dynamic hint with a clue not [1 k]")
          else keptWhyW snd k fh h q fq (match h with | Nomm.n1 _ => true | _ => false) (stopTag tag)
      | _ => fMis f nm
  | Nomm.mean p _ q _ _ =>
      match f with
      | Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom _) fp) fq) =>
          match k with
          | WKind.dall => "dall: %mean"
          | _ => keptWhyW snd k fp p q fq false false
      | _ => fMis f nm
  | Nomm.n12 _ _ => "%12"

/-- The reason at a kept dynamic hint (or a `%mean` with no constant). -/
partial def keptWhyW (snd : Nomm → NeedOrd → Bool) (k : WKind) (fh : Noun) (h q : Nomm) (fq : Noun) (_clue1 stop : Bool) :
    String :=
    if (hcLeaf fh h).isNone then "kept hint: clue " ++ leafWhy fh h
    else if !hcNB h then "kept hint: clue without NoBondH rule"
    else if !snd q NeedOrd.this then "+sound fails"
    else match k with
      | WKind.sur => (hcWhyW snd WKind.sur fq q).getD "?"
      | WKind.reg | WKind.top => (hcWhyW snd WKind.reg fq q).getD "?"
      | WKind.dall =>
          if !stop then "dall: quiet tag" else if (hcLeaf fq q).isNone then "dall: kept hint over a non-leaf"
          else "dall: body without NoBondH rule"
      | WKind.sh => if !hcNB h then "ShapeH: clue without NoBondH rule" else (hcWhyW snd WKind.sh fq q).getD "?"
      | WKind.st => if !(hcW snd fq q).reg then (hcWhyW snd WKind.reg fq q).getD "?" else (hcWhyW snd WKind.sh fq q).getD "?"
      | _ => "kept hint: no " ++ wName k ++ " rule"
end

/-- The decidable part of `HintTabW` on the dumped table. -/
def tabWhyW (tab : List MEnt) (nm : Nomm) : Option String :=
  if (callBells nm).any fun b => (tabGet tab b).map (·.pure) != some false then some "direct callee pure or absent"
  else Option.none

def entWhyW (e : TEnt) : Option String :=
  match tabWhyW e.tab e.nomm with
  | some r => some r
  | Option.none => hcWhyW (sndM e.tab) WKind.top e.fol e.nomm

def entInW (e : TEnt) : Bool := (hcW (sndM e.tab) e.fol e.nomm).top && (tabWhyW e.tab e.nomm).isNone

#guard real.all fun e => (entWhyW e).isNone == entInW e
#guard real.all fun e => (hcWhyW (sndM e.tab) WKind.top e.fol e.nomm).isNone == (hcW (sndM e.tab) e.fol e.nomm).top

def inRealW : List String := (real.filter entInW).map (·.name)
def realWhyW : List (String × String) := real.filterMap fun e => (entWhyW e).map fun r => (e.name, r)

#guard inRealW == ["t01", "t03", "t04", "t05", "t06", "t07", "t08", "t11", "t13", "t15", "t16", "t17", "t18", "t19",
  "t21", "m01", "m02", "m03", "m04", "m05", "m06", "m07", "m08", "m09", "m10", "m11", "m12", "m13", "m16", "m17", "m18",
  "m19", "m20", "m21", "m22", "m23", "m28", "m29", "g04", "g05"]
-- **40 of the 57 real arms** (15 of the 21 code-table entries, 25 of the 36 of `hintmean`)
#guard (inRealW.length, (tEnts.filter entInW).length, (mEnts.filter entInW).length) == (40, 15, 25)
-- of the six code-table entries with a kept hint: `t05` (the `S3` body at axis 12) and `t21`
#guard HintClsData.kept.filter inRealW.contains == ["t05", "t21"]
-- of the five arms of real `~_` gates: `g04` (constant `%mean`) and `g05`
#guard ["g01", "g02", "g03", "g04", "g05"].filter inRealW.contains == ["g04", "g05"]
-- **The reasons, most first** (17 out of 57).  "formula %2 for nomm %7" is the
-- inlined call (`[2 [0 1] [0 2]]` whose nomm is the arm: the arm's formula is not in the
-- check); "%6 at the top, branch: a %7" is `t10`'s `[7 [10 6 ..] call]` (no `st` rule for `%7`).
#guard tallyOf (real.filterMap entWhyW) == [("formula %2 for nomm %7", 5),
  ("%7 at the top: p not a leaf (nor the [7 kept [4 [0 a]]] form)", 3), ("cons: %mean", 3),
  ("%6 branch: cons: kept dynamic hint", 2), ("cons: %6", 2), ("%6 at the top, branch: a %7", 1),
  ("%6 at the top: test not a pure fragment", 1)]
#guard realWhyW == [("t02", "formula %2 for nomm %7"), ("t09", "%6 branch: cons: kept dynamic hint"),
  ("t10", "%6 at the top, branch: a %7"), ("t12", "formula %2 for nomm %7"),
  ("t14", "%6 branch: cons: kept dynamic hint"),
  ("t20", "%7 at the top: p not a leaf (nor the [7 kept [4 [0 a]]] form)"), ("m14", "cons: %6"), ("m15", "cons: %6"),
  ("m24", "cons: %mean"), ("m25", "cons: %mean"),
  ("m26", "%7 at the top: p not a leaf (nor the [7 kept [4 [0 a]]] form)"),
  ("m27", "%7 at the top: p not a leaf (nor the [7 kept [4 [0 a]]] form)"),
  ("m30", "%6 at the top: test not a pure fragment"), ("m31", "cons: %mean"), ("g01", "formula %2 for nomm %7"),
  ("g02", "formula %2 for nomm %7"), ("g03", "formula %2 for nomm %7")]
-- every entry of the old class is in the new one
#guard real.all fun e => !entIn e || entInW e
-- in-class real entries whose `FitHW` asks a callee `less` that knows the battery
#guard (real.filter fun e => entInW e && (callBells e.nomm).any fun b => match b.less with
    | Sock.mk Cape.no _ => false
    | _ => true).map (·.name) == ["t04", "t05", "t08", "t16", "t17", "t18", "t21", "m16", "m17", "g04", "g05"]
-- in-class real entries with a constant `%mean` (pure trap: `FitHW` asks `+mack` of the traps)
#guard (real.filter fun e => entInW e && !(meanBells e.nomm).isEmpty &&
    (meanBells e.nomm).any fun b => (tabGet e.tab b).map (·.pure) == some true).map (·.name) ==
  ["m01", "m05", "m12", "m16", "m18", "m20", "m22", "m28", "m29", "g04"]

def hInW (e : String × Nomm × Noun) : Bool := (hcW sndH e.2.2 e.2.1).top
def hWhyW (e : String × Nomm × Noun) : Option String := hcWhyW sndH WKind.top e.2.2 e.2.1
#guard hEnts.all fun e => (hWhyW e).isNone == hInW e
-- the 39 hand formulas: 24 (the 23 of `hcV` and `d17`, a `%6` at the top)
#guard (hEnts.filter hInW).map (·.1) == ["s01", "s02", "s03", "s05", "s06", "d01", "d02", "d03", "d06", "d08", "d09",
  "d10", "d13", "d14", "d17", "d18", "d19", "d20", "d21", "d22", "d23", "m01", "m02", "m03"]
#guard tallyOf (hEnts.filterMap hWhyW) == [("%12", 4),
  ("%7 at the top: p not a leaf (nor the [7 kept [4 [0 a]]] form)", 3),
  ("unkept dynamic hint with a clue not [1 k]", 2), ("%5: kept dynamic hint", 1),
  ("%6 at the top: test not a pure fragment", 1), ("cons: %12", 1), ("cons: kept dynamic hint", 1),
  ("cons: kept static hint", 1), ("formula %11 for nomm %11d", 1)]
#guard hEnts.all fun e => !hIn e || hInW e

end Comp
end SkaModel
end Formalization
