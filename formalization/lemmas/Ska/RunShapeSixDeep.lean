import lemmas.Ska.RunShape
import lemmas.Ska.CompLeapTwice

/-!
# `+laze-leaps` never leaps twice (track A, 2026-11-28)

The hypothesis of `sixDeep_of_idem` (`Compiler/CompRunShapeSixN.lean`), which gives `SixDeep q r
sixFuel laz` for every `laz`: a `rest` that `lazeLeaps` returns does not leap again.  It is
`leap_twice` (`CompLeapTwice.lean`, the same fact of `+leap` of `+run`) carried over: a `laze` is a
`need-lazy` whose registers are all `0` (`lzL`), and `+laze-leap` / `+laze-leaps` are `+lazy-leap` /
`+leap` on that image (`lzL_leap`, `lzL_leaps`), because `+need-ord-cut` and `+need-ord-from` are
`+need-cut` and `+need-from` there (`ordN_cut`, `ordN_needFrom`) and the looks are the same sets.

* `ordN`, `lzL` (`lzF`, `lzB`): the images.
* `ordN_cons`, `ordN_cut`, `ordN_fromOrd`, `ordN_needFrom`, `lzL_empty`, `lzL_prune`.
* **`lzL_leap`** (`lzF_leap`, `lzB_leap`), `lzL_loop`, **`lzL_leaps`**.
* **`lazeLeaps_idem`**: under the hypothesis of `leap_twice` (the passes of the branches have
  nonzero product axes; `Bake.NoAx0` of the branches gives it, as in `leapTwice_noAx0`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Compiler Lazy

variable {S : Type} [HoonSet S]

/-! ## `need-ordered` as a `need` with register `0` -/

/-- A `need-ordered` as a `need` whose registers are `0`. -/
def ordN : NeedOrd → Need
  | NeedOrd.pair p q => Need.pair (ordN p) (ordN q)
  | NeedOrd.both p q => Need.both 0 (ordN p) (ordN q)
  | NeedOrd.this => Need.this 0
  | NeedOrd.none => Need.none

theorem ordN_none_iff (n : NeedOrd) : ordN n = Need.none ↔ n = NeedOrd.none := by
  cases n <;> simp [ordN]

theorem ordN_cons (a b : NeedOrd) : consNeed (ordN a) (ordN b) = ordN (consOrd a b) := by
  cases a <;> cases b <;> simp [consNeed, consOrd, ordN]

theorem ordN_cut : ∀ (ned : NeedOrd) (axe : Nat),
    needCut axe (ordN ned) = (needOrdCut axe ned).map (Option.map fun e => (ordN e.1, ordN e.2))
  | NeedOrd.none, axe => by
    rw [needOrdCut]; by_cases h : axe = 1 <;> simp [needCut, ordN, h]
  | NeedOrd.this, axe => by
    rw [needOrdCut]; by_cases h : axe = 1 <;> simp [needCut, ordN, h]
  | NeedOrd.both p q, axe => by
    rw [needOrdCut]; by_cases h : axe = 1 <;> simp [needCut, ordN, h]
  | NeedOrd.pair p q, axe => by
    rw [needOrdCut]
    by_cases h1 : axe = 1
    · simp [needCut, ordN, h1]
    by_cases h0 : axe = 0
    · subst h0; simp [needCut, ordN]
    by_cases hc : cap axe = 2
    · simp only [needCut, ordN, h1, h0, hc, if_false, if_true, ordN_cut p (mas axe)]
      cases needOrdCut (mas axe) p with
      | none => rfl
      | some k => cases k <;> simp [ordN_cons]
    · simp only [needCut, ordN, h1, h0, hc, if_false, ordN_cut q (mas axe)]
      cases needOrdCut (mas axe) q with
      | none => rfl
      | some k => cases k <;> simp [ordN_cons]

theorem ordN_fromOrd (ned : NeedOrd) : ∀ axe : Nat, 1 ≤ axe →
    (fromOrd axe ned).map ordN = some (fromPath (ordN ned) axe) := by
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
    intro h1
    by_cases ha : axe = 1
    · subst ha; rw [fromOrd, fromPath]; simp
    · have h2 : 2 ≤ axe := by omega
      have hm := mas_pos axe h2
      have hlt := mas_lt axe (by omega)
      rw [fromOrd, fromPath]
      have hn : ¬ axe ≤ 1 := by omega
      simp only [ha, if_false, show axe ≠ 0 by omega, hn, dif_neg, not_false_eq_true]
      have := ih (mas axe) hlt hm
      by_cases hc : cap axe = 2
      · simp only [hc, if_true]
        cases e : fromOrd (mas axe) ned with
        | none => rw [e] at this; cases this
        | some x => rw [e] at this; simp at this; simp [ordN, this]
      · simp only [hc, if_false]
        cases e : fromOrd (mas axe) ned with
        | none => rw [e] at this; cases this
        | some x => rw [e] at this; simp at this; simp [ordN, this]

theorem ordN_needFrom (s : Nat) (don : NeedOrd) : needFrom s (ordN don) = (needOrdFrom s don).map ordN := by
  unfold needFrom needOrdFrom
  by_cases hd : don = NeedOrd.none
  · subst hd; simp [ordN]
  · have hd' : ordN don ≠ Need.none := fun h => hd ((ordN_none_iff don).1 h)
    simp only [hd, hd', if_false]
    by_cases hs : s = 0
    · subst hs; rw [fromOrd]; simp
    · simp only [hs, if_false]
      rw [ordN_fromOrd don s (by omega)]

/-! ## `laze` as a `need-lazy` -/

/-- The sure need of a `laze` as a `sure`. -/
def lzSO (s : SureO S) : Sure S := ⟨ordN s.ned, s.lok⟩

mutual
/-- A `laze` as a `need-lazy` whose registers are `0`. -/
def lzL : Laze S → Lazy S
  | Laze.mk s f b => Lazy.mk (lzSO s) (lzF f) (lzB b)
def lzF : List ((Nat × Laze S) × (Nat × Laze S)) → List ((Nat × Lazy S) × (Nat × Lazy S))
  | [] => []
  | ((oy, y), (on, n)) :: rest => ((oy, lzL y), (on, lzL n)) :: lzF rest
def lzB : List (Nat × Laze S) → List (Nat × Lazy S)
  | [] => []
  | (o, l) :: rest => (o, lzL l) :: lzB rest
end

/-- The image of a fork entry. -/
def lzFe (e : (Nat × Laze S) × (Nat × Laze S)) : (Nat × Lazy S) × (Nat × Lazy S) :=
  ((e.1.1, lzL e.1.2), (e.2.1, lzL e.2.2))

/-- The image of a bond entry. -/
def lzBe (e : Nat × Laze S) : Nat × Lazy S := (e.1, lzL e.2)

theorem lzF_eq : ∀ f : List ((Nat × Laze S) × (Nat × Laze S)), lzF f = f.map lzFe
  | [] => by simp [lzF]
  | ((oy, y), (on, n)) :: rest => by simp [lzF, lzFe, lzF_eq rest]

theorem lzB_eq : ∀ b : List (Nat × Laze S), lzB b = b.map lzBe
  | [] => by simp [lzB]
  | (o, l) :: rest => by simp [lzB, lzBe, lzB_eq rest]

theorem lzL_mk (s : SureO S) (f : List ((Nat × Laze S) × (Nat × Laze S))) (b : List (Nat × Laze S)) :
    lzL (Laze.mk s f b) = Lazy.mk (lzSO s) (f.map lzFe) (b.map lzBe) := by
  rw [lzL, lzF_eq, lzB_eq]

theorem lzS_bunt : lzSO (SureO.bunt : SureO S) = Sure.bunt := by
  simp [lzSO, SureO.bunt, Sure.bunt, ordN]

theorem lzL_empty (l : Laze S) : lazyEmpty (lzL l) = lazeEmpty l := by
  obtain ⟨s, f, b⟩ := l
  rw [lzL_mk]
  by_cases h : s.ned = NeedOrd.none
  · simp [lazyEmpty, lazeEmpty, lzSO, Lazy.sure, Lazy.fork, Lazy.bond, Laze.sure, Laze.fork, Laze.bond, h, ordN]
  · have h' : ordN s.ned ≠ Need.none := fun e => h ((ordN_none_iff _).1 e)
    simp [lazyEmpty, lazeEmpty, lzSO, Lazy.sure, Lazy.fork, Lazy.bond, Laze.sure, Laze.fork, Laze.bond, h, h']

theorem lzL_prune (l : Laze S) : lazyPrune (lzL l) = lzL (lazePrune l) := by
  obtain ⟨s, f, b⟩ := l
  rw [lzL_mk, lazePrune, lzL_mk]
  simp [lazyPrune, Lazy.sure, Lazy.fork, Lazy.bond, List.filter_map, Function.comp_def, lzFe, lzBe, lzL_empty]

/-! ## `+laze-leap` is `+lazy-leap` on the image -/

section
variable (p s : Nat)

/-- The image of a pair of fork entries. -/
def lzFF (x : ((Nat × Laze S) × (Nat × Laze S)) × ((Nat × Laze S) × (Nat × Laze S))) :
    ((Nat × Lazy S) × (Nat × Lazy S)) × ((Nat × Lazy S) × (Nat × Lazy S)) := (lzFe x.1, lzFe x.2)

/-- The image of a pair of bond entries. -/
def lzBB (x : (Nat × Laze S) × (Nat × Laze S)) : (Nat × Lazy S) × (Nat × Lazy S) := (lzBe x.1, lzBe x.2)

mutual
theorem lzL_leap : ∀ l : Laze S, lazyLeap p s (lzL l) = (lazeLeap p s l).map fun x => (lzL x.1, lzL x.2)
  | Laze.mk sur fk bd => by
    have hf := lzF_leap fk
    have hb := lzB_leap bd
    rw [lzF_eq] at hf
    rw [lzB_eq] at hb
    rw [lzL_mk, lazyLeap, lazeLeap]
    simp only [lzSO, ordN_cut, hf, hb]
    cases e1 : needOrdCut p sur.ned with
    | none => simp
    | some cut =>
      cases cut with
      | none =>
        simp only [Option.map_some, Option.map_none, Option.bind_some, Option.bind_eq_bind, Option.pure_def]
        cases e3 : leapSF p s fk with
        | none => simp
        | some fs =>
          cases e4 : leapSB p s bd with
          | none => simp
          | some bs =>
            simp [lzFF, lzBB, ← lzL_prune, lzL_mk, List.map_map, Function.comp_def, lzS_bunt, lzSO, Sure.bunt,
              SureO.bunt, ordN]
      | some dr =>
        obtain ⟨don, rec⟩ := dr
        simp only [Option.map_some, Option.bind_some, Option.bind_eq_bind, Option.pure_def]
        cases e2 : leapLok p s sur.lok with
        | none => simp
        | some lr =>
          obtain ⟨lb, lr⟩ := lr
          simp only [Option.bind_some, ordN_needFrom]
          cases e5 : needOrdFrom s don with
          | none => simp
          | some nf =>
            simp only [Option.map_some, Option.bind_some]
            cases e3 : leapSF p s fk with
            | none => simp
            | some fs =>
              cases e4 : leapSB p s bd with
              | none => simp
              | some bs =>
                simp [lzFF, lzBB, ← lzL_prune, lzL_mk, List.map_map, Function.comp_def, lzSO]

theorem lzF_leap : ∀ f : List ((Nat × Laze S) × (Nat × Laze S)),
    leapForks p s (lzF f) = (leapSF p s f).map (List.map lzFF)
  | [] => by simp [lzF, leapForks, leapSF]
  | ((oy, y), (on, n)) :: rest => by
    simp only [lzF, leapForks, leapSF, lzL_leap y, lzL_leap n, lzF_leap rest]
    cases lazeLeap p s y with
    | none => simp
    | some yy =>
      cases lazeLeap p s n with
      | none => simp
      | some nn =>
        cases leapSF p s rest with
        | none => simp
        | some rs => simp [lzFF, lzFe]

theorem lzB_leap : ∀ b : List (Nat × Laze S), leapBonds p s (lzB b) = (leapSB p s b).map (List.map lzBB)
  | [] => by simp [lzB, leapBonds, leapSB]
  | (o, l) :: rest => by
    simp only [lzB, leapBonds, leapSB, lzL_leap l, lzB_leap rest]
    cases lazeLeap p s l with
    | none => simp
    | some ll =>
      cases leapSB p s rest with
      | none => simp
      | some rs => simp [lzBB, lzBe]
end

end

/-! ## `+laze-leaps` is `+leap` on the image -/

/-- The image of a result of the loop. -/
def lzRes (x : Option (Laze S × List (Laze S))) : Option (Lazy S × List (Lazy S)) :=
  x.map fun r => (lzL r.1, r.2.map lzL)

theorem lzL_loop (sur : SureO S) : ∀ (pas : List (Nat × Nat)) (lab : Laze S) (bys : List (Laze S)),
    leapLoop (lzSO sur) pas (lzL lab) (bys.map lzL) = (leapsLoop sur pas lab bys).map lzRes
  | [], lab, bys => by
    obtain ⟨s0, f, b⟩ := lab
    cases bys <;> simp [leapLoop, leapsLoop, lzRes, lzL_mk, Lazy.fork, Lazy.bond, Laze.fork, Laze.bond]
  | (p, s) :: rest, lab, bys => by
    simp only [leapLoop, leapsLoop, lzL_leap]
    cases lazeLeap p s lab with
    | none => simp
    | some br =>
      obtain ⟨b, r⟩ := br
      simp only [Option.map_some, Option.bind_some, lzL_empty]
      cases lazeEmpty b with
      | true => simp only [if_true]; exact lzL_loop sur rest lab bys
      | false =>
        simp only [Bool.false_eq_true, if_false]
        have := lzL_loop sur rest r (b :: bys)
        simpa using this

/-- **`+laze-leaps` is `+leap` on the image.** -/
theorem lzL_leaps (laz : Laze S) (q r : Nomm) : leap (lzL laz) q r = (lazeLeaps laz q r).map lzRes := by
  obtain ⟨s0, f, b⟩ := laz
  unfold leap lazeLeaps
  simp only [lzL_mk, Lazy.fork, Lazy.bond, Lazy.sure, Laze.fork, Laze.bond, Laze.sure, List.isEmpty_map]
  by_cases hc : (f.isEmpty && b.isEmpty) = true
  · simp [hc, lzRes]
  · simp only [hc, if_false, Bool.false_eq_true]
    cases passBoth q r with
    | none => rfl
    | some pas =>
      simp only [Option.bind_some]
      have := lzL_loop s0 pas (Laze.mk SureO.bunt f b) []
      rw [lzL_mk, lzS_bunt] at this
      simpa [lzSO] using this

/-- **A `rest` of `+laze-leaps` does not leap again**, when the passes of the branches have nonzero
product axes (the hypothesis of `leap_twice`; `Bake.NoAx0` of `q` and `r` gives it, as in
`leapTwice_noAx0`). -/
theorem lazeLeaps_idem {q r : Nomm} (hpos : ∀ pas, passBoth q r = some pas → ∀ e ∈ pas, e.1 ≠ 0)
    {laz rest : Laze S} {bys : List (Laze S)} (h : lazeLeaps laz q r = some (some (rest, bys))) :
    lazeLeaps rest q r = some Option.none := by
  have h1 : leap (lzL laz) q r = some (some (lzL rest, bys.map lzL)) := by
    rw [lzL_leaps, h]; rfl
  have h2 := leap_twice hpos (lzL rest) (bys.map lzL) h1
  rw [lzL_leaps] at h2
  cases e : lazeLeaps rest q r with
  | none => rw [e] at h2; cases h2
  | some x =>
    rw [e] at h2
    cases x with
    | none => rfl
    | some y => simp [lzRes] at h2

/-- The form `sixDeep_of_idem` takes. -/
theorem lazeLeaps_idem' {q r : Nomm} (hpos : ∀ pas, passBoth q r = some pas → ∀ e ∈ pas, e.1 ≠ 0) :
    ∀ (laz rest : Laze S) bys, lazeLeaps laz q r = some (some (rest, bys)) →
      ∀ (rest' : Laze S) bys', lazeLeaps rest q r ≠ some (some (rest', bys')) := by
  intro laz rest bys h rest' bys' h'
  rw [lazeLeaps_idem hpos h] at h'
  cases h'

end Comp
end SkaModel
end Formalization
