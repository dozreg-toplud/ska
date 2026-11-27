import lemmas.Assembly

/-!
# Glue: a concrete `lib` (sections 6, 7, 8 of `LEDGER.md`)

`Gap` asks of the free `lib : Lib` that it slams as Nock (`LibSlam`) and
that its formatting fields are what the pill's `+mook` computes at layer 4
(`LibFormat`, `MookFormat`).  Here `libP` is one `lib` built from the pill:

* `slam := slamGate nock`;
* `rendBase`: `+scow %p` of the pill on `%hand`, the pill's `+rend:mook` at
  the trace `~` on `%spot` and on `%hunk` of a cell, `rendLeaf` elsewhere;
* `softTank`: the unit `(soft tank)` of the pill returns at layer 4;
* `skipMsg n`: the cord of `+skip` of the pill at `yel = n + 1024`, the
  trace `~`.

PROVED for it: `libP_slam` (`LibSlam`), `libP_rendLeaf` (`RendLeafIs`),
`libP_hand` (`HandIs`).  The other format leaves become statements about the
pill alone, with no `lib` in them:

* `RendRestTonFree`: `+rend:mook` on `%spot` and `%hunk` of a cell does not
  depend on the trace (the pill's `+smyt` through `(soft path)`,
  `(soft spot)`, `+scow %ud`);
* `SoftTankUnit`: the pill's `(soft tank)` returns a unit on every noun;
* `SkipMsgTonFree`: the cord of `+skip` returns and does not depend on the
  trace;
* `EvalMookSame`: the cord of `+eval-mook` on every `CorIn` core is that
  of `+skip` at layer 4.

`libP_format`, `libP_mookFormat`: `LibFormat libP`, `MookFormat libP` from
them.
-/

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Pill Hoon Compiler

/-- `+scow %p` of the pill on the hash of the datum, in a leaf. -/
noncomputable def handTank (dat : Noun) : Option Noun :=
  (nock (C scow.battery (C (C (A 112) (A (mugF dat))) layer4)) scow.battery).map (C (A Tag.leaf))

/-- The base of `+rend:mook` of `libP`. -/
noncomputable def rendBaseP (tag : Nat) (dat : Noun) : Option Noun :=
  if tag = Tag.hand then handTank dat
  else if tag = Tag.spot then rendSlam (C (A tag) dat) (A 0) layer4
  else if tag = Tag.hunk then
    (match dat with
     | Noun.cell _ _ => rendSlam (C (A tag) dat) (A 0) layer4
     | Noun.atom _ => rendLeaf tag dat)
  else rendLeaf tag dat

/-- The noun the pill's `(soft tank)` slams to at layer 4. -/
noncomputable def softTankN (n : Noun) : Option Noun :=
  nock (C soft.gate.battery (C n (C soft.battery (C (C tank.battery (C tankBunt layer2)) layer4))))
    soft.gate.battery

/-- `(soft tank)` of `libP`: the unit the pill returns, read back. -/
noncomputable def softTankP (n : Noun) : Option Noun :=
  match softTankN n with
  | some (Noun.cell (Noun.atom 0) x) => some x
  | _ => none

/-- The cord of `+skip` of the pill at `yel`, the trace `~`. -/
noncomputable def skipN (yel : Nat) : Option Noun := nock (C (A yel) (mookCore (A 0) layer4)) mook.skip.msg

/-- `+skip`'s cord of `libP`. -/
noncomputable def skipMsgP (n : Nat) : Noun := (skipN (n + 1024)).getD (A 0)

/-- **The `lib` of the pill.** -/
noncomputable def libP : Lib := ⟨slamGate nock, softTankP, rendBaseP, skipMsgP⟩

/-- **`LibSlam` of `libP`.** -/
theorem libP_slam : Assembly.LibSlam libP := fun _ _ => rfl

theorem rendLeaf_hand (dat : Noun) : rendLeaf Tag.hand dat = none := by
  simp [rendLeaf, Tag.hand, Tag.hunk, Tag.lose]

theorem rendLeaf_spot (dat : Noun) : rendLeaf Tag.spot dat = none := by
  simp [rendLeaf, Tag.spot, Tag.hunk, Tag.lose, Tag.hand, Tag.mean]

theorem rendLeaf_hunk_cell (h t : Noun) : rendLeaf Tag.hunk (C h t) = none := by
  simp [rendLeaf]

/-- **`RendLeafIs` of `libP`.** -/
theorem libP_rendLeaf : RendLeafIs libP := by
  intro tag dat y h
  show rendBaseP tag dat = some y
  unfold rendBaseP
  by_cases e1 : tag = Tag.hand
  · subst e1; rw [rendLeaf_hand] at h; cases h
  · rw [if_neg e1]
    by_cases e2 : tag = Tag.spot
    · subst e2; rw [rendLeaf_spot] at h; cases h
    · rw [if_neg e2]
      by_cases e3 : tag = Tag.hunk
      · subst e3
        rw [if_pos rfl]
        cases dat with
        | cell a b => rw [rendLeaf_hunk_cell] at h; cases h
        | atom a => exact h
      · rw [if_neg e3]; exact h

/-- **`HandIs` of `libP`.** -/
theorem libP_hand : HandIs libP mugF layer4 := by
  intro dat
  show _ = rendBaseP Tag.hand dat
  unfold rendBaseP handTank
  rw [if_pos rfl]

/-- **Leaf: `+rend:mook` of the pill on `%spot` and on `%hunk` of a cell
does not depend on the trace.** -/
def RendRestTonFree : Prop :=
  (∀ h t ton, rendSlam (C (A Tag.hunk) (C h t)) ton layer4 = rendSlam (C (A Tag.hunk) (C h t)) (A 0) layer4) ∧
    ∀ dat ton, rendSlam (C (A Tag.spot) dat) ton layer4 = rendSlam (C (A Tag.spot) dat) (A 0) layer4

/-- **Leaf: the pill's `(soft tank)` returns a unit on every noun.** -/
def SoftTankUnit : Prop := ∀ n, ∃ u, softTankN n = some (unitN u)

/-- **Leaf: the cord of `+skip` returns and does not depend on the trace.** -/
def SkipMsgTonFree : Prop :=
  ∀ yel ton, 1024 < yel →
    nock (C (A yel) (mookCore ton layer4)) mook.skip.msg = skipN yel ∧ (skipN yel).isSome

/-- **Leaf: the cord of `+eval-mook` on every `CorIn` core is that of
`+skip` at layer 4.** -/
def EvalMookSame : Prop :=
  ∀ (yel : Nat) (ton cr : Noun), CorIn cr → 1024 < yel →
    nock (C (A yel) (C eval_mook.battery (C ton (icore cr)))) mookMsgF = skipN yel

theorem libP_rendRest (h : RendRestTonFree) : RendRestIs libP layer4 := by
  refine ⟨fun hh t ton => ?_, fun dat ton => ?_⟩
  · show _ = rendBaseP Tag.hunk (C hh t)
    unfold rendBaseP
    rw [if_neg (by simp [Tag.hunk, Tag.hand]), if_neg (by simp [Tag.hunk, Tag.spot]), if_pos rfl]
    exact h.1 hh t ton
  · show _ = rendBaseP Tag.spot dat
    unfold rendBaseP
    rw [if_neg (by simp [Tag.spot, Tag.hand]), if_pos rfl]
    exact h.2 dat ton

theorem libP_softTank (h : SoftTankUnit) : SoftTankIs libP layer4 := by
  intro l2 hl2 n
  rw [mook.layer2.arm_at] at hl2
  cases hl2
  obtain ⟨u, hu⟩ := h n
  show softTankN n = some (unitN (softTankP n))
  unfold softTankP
  rw [hu]
  cases u <;> rfl

theorem skipMsgP_eq {yel : Nat} (hy : 1024 < yel) (hs : (skipN yel).isSome) :
    skipN yel = some (skipMsgP (yel - 1024)) := by
  unfold skipMsgP
  rw [Nat.sub_add_cancel (Nat.le_of_lt hy)]
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
  rw [hx]
  rfl

theorem libP_skipMsg (h : SkipMsgTonFree) : SkipMsgIs libP layer4 := by
  intro yel ton hy
  obtain ⟨e, hs⟩ := h yel ton hy
  rw [e]
  exact skipMsgP_eq hy hs

theorem libP_evalMook (h : EvalMookSame) (hs : SkipMsgTonFree) : Assembly.MookFormat libP := by
  intro yel ton cr hc hy
  rw [h yel ton cr hc hy]
  exact skipMsgP_eq hy (hs yel (A 0) hy).2

/-- **`LibFormat` of `libP`** from the three leaves about the pill. -/
theorem libP_format (h1 : RendRestTonFree) (h2 : SoftTankUnit) (h3 : SkipMsgTonFree) :
    Assembly.LibFormat libP :=
  ⟨libP_rendLeaf, libP_hand, libP_rendRest h1, libP_softTank h2, libP_skipMsg h3⟩

end Glue
end SkaModel
end Formalization
