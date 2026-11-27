import lemmas.Ska.PassLoop

/-!
# The measure of the pass loop of `+analyze` on the real compiler (track F)

## 1. What was measured

`tools/hoon/passmeasure.py` writes a copy of the library that prints, at the
end of every `+run`, how each field of the entry changed against the old one
(`less-code` and the product compared by `+huge:so` both ways, `indi` and
`seek` by inclusion of capes, the map by equality), every pass of every pass
loop, every function analysed afresh (with the depth of the stack), and every
member that `+cull` drops.  Over 2,269 calls of `+ska-callgraph` (2026-11-27:
the 162 formulas of `thread-a/b/c` with an unknown and a known subject, 621
self-calls with swapped and rotated samples, mutual recursions and calls
whose product is run as a formula or used as a subject, 1,300 random
recursive cores, and 21 calls of library gates with the library as a known
subject, `(ream '(add 1 2)')` among them) there were 6,473 runs after the
first one of an entry, 5,156 passes and 6,838 functions analysed:

* `less-code` never shrank and never became incomparable.  It grew strictly
  (by `+huge:so`) or stayed, except 6 runs where it changed with the same
  nouns: its cape went from `[[& &] |]` to `[& |]`.  A mask that `+distribute`
  builds over a cell of axes is the denormalized `[& &]`, and `+uni:ca` with a
  later `&` there turns it into `&` (`uni_denorm_example`).  So "the cape size
  of `less-code` grows" is not the measure: the cape rises in the order
  `CapeLe` below, where `&` is above every cell, and `+uni:ca` only rises in
  it (`capeLe_uni_right`).
* The product never gained knowledge and never changed without losing some.
* Open point (a) happens: 151 runs changed the map and nothing else.  In 100
  of them the product was `|+~` and the map went from an axis to `~`; that is
  the only change `+double-int` and `+msg-anno` can make there, once
  (`mergeProd_dunno_old`, `runDatum_dunno_prod`).  In the other 51 the product
  knew a cell and the map either lost the provenance of a part the product
  does not know (`1` to `[2 0]`, `[2 [6 7]]` to `[2 [0 7]]`) or was spelled
  out along the cells of the product's cape (`1` to `[2 [6 7]]`, the same
  provenance).  Both are bounded by the cape of the fixed product (a measure
  for them is in section 2, not proved).
* With the less-code change counted by `CapeLe`, every run that changed its
  entry moved the lexicographic measure (`less-code` up, else the product
  down, else the map down, else `indi` up, else `seek` up) the right way, and
  every run that changed nothing left all five fields equal: no exception.
* Open point (b) never happens: 21 members were culled (all in the self-calls
  whose product is called on the product of a recursive call, `[2 [2 R [0 2]]
  [0 1]]`), and no culled identity was ever analysed again.
* The longest pass loop took 62 passes, on a random core whose recursion grows
  the sample (`[9 2 [10 [6 [0 7] [4 0 6]] 0 1]]`): every other pass found one
  new function, up to the 32 of `he-threshold`, so there the loop goes on by
  finding functions, not by changing entries.  The deepest stack at a new
  function was 366 (`(ream '(add 1 2)')`), 31 in the random cores.

No poke on which the pass loop does not end was found, and no pass on which
the measure fails while the loop goes on.

## 2. The measure, corrected, and what is open

Per entry, lexicographically: the cape of `less-code` in `CapeLe` (rising,
below the cape and nouns of `bus`, finitely many), the knowledge of the
product (falling), the map (for a fixed product: the number of leaves of the
product's cape whose map is not `~`, falling, then the number of cells of the
cape at which the map is an atom, falling), `indi`, then `seek` (rising under
`+msg-ca` within the cells of the first one and of `dark`).  Then the
functions found (finitely many by the argument of `AnaEnds.lean`).  Proved
here: the step of the mask (`capeLe_uni_right`), and the map for an unknown
product (`mergeProd_dunno_old`).  Open: the map for a product that knows a
cell, the mask through `+app:ca` against `bus`, and (b), which the data says
does not occur but which no invariant excludes yet: a culled member's entry
starts from the bunt, so a proof needs that the call sites of the component
do not come back to an identity they left.
-/

namespace Formalization
namespace SkaModel

open Nock

/-- A cape that knows nothing: `|`, or a cell of such (`[| |]`, which `+con:ca`
never makes). -/
inductive CapeNo : Cape → Prop
  | no : CapeNo Cape.no
  | cell {a b : Cape} : CapeNo a → CapeNo b → CapeNo (Cape.cell a b)

/-- The order in which the mask of `less-code` rises: a cape that knows
nothing is below every cape, every cape is below `&` (so `[& &]` is below
`&`), and cells compare by parts. -/
inductive CapeLe : Cape → Cape → Prop
  | no {c : Cape} (h : CapeNo c) (d : Cape) : CapeLe c d
  | yes (c : Cape) : CapeLe c Cape.yes
  | cell {a b c d : Cape} : CapeLe a c → CapeLe b d → CapeLe (Cape.cell a b) (Cape.cell c d)

theorem capeLe_refl : ∀ c : Cape, CapeLe c c
  | Cape.yes => CapeLe.yes _
  | Cape.no => CapeLe.no CapeNo.no _
  | Cape.cell a b => CapeLe.cell (capeLe_refl a) (capeLe_refl b)

theorem capeLe_no_inv {c : Cape} (h : CapeLe c Cape.no) : CapeNo c := by
  cases h with
  | no h => exact h

/-- **`+uni:ca` only rises in `CapeLe`** over its second argument, the old
cape of `less-code` in `+run`. -/
theorem capeLe_uni_right : ∀ a b : Cape, CapeLe b (Ca.uni a b)
  | a, b => by
    unfold Ca.uni
    split
    · rename_i h; subst h; exact capeLe_refl _
    · split
      · exact CapeLe.yes _
      · exact capeLe_refl _
      · exact CapeLe.yes _
      · exact CapeLe.no CapeNo.no _
      · rename_i ah aT bh bT _
        have ih1 := capeLe_uni_right ah bh
        have ih2 := capeLe_uni_right aT bT
        unfold Ca.con
        split
        · rename_i hc
          rw [hc.1] at ih1; rw [hc.2] at ih2
          exact CapeLe.no (CapeNo.cell (capeLe_no_inv ih1) (capeLe_no_inv ih2)) _
        · exact CapeLe.cell ih1 ih2

/-- The six runs where `less-code` changed with the same nouns: the old mask
`[[& &] |]` (from `+distribute` over a cell of axes) united with a `want`
of `[& |]` is `[& |]`. -/
theorem uni_denorm_example :
    Ca.uni (Cape.cell Cape.yes Cape.no) (Cape.cell (Cape.cell Cape.yes Cape.yes) Cape.no) =
      Cape.cell Cape.yes Cape.no := by
  decide

/-- **`+double-int` with an unknown old product** keeps it or gives
`Anno.dunno`: the map can only go to `~`. -/
theorem doubleInt_dunno_old (new : Anno) (r : Noun) :
    doubleInt new ⟨Sock.dunno, r⟩ = ⟨Sock.dunno, r⟩ ∨ doubleInt new ⟨Sock.dunno, r⟩ = Anno.dunno := by
  by_cases he : new = ⟨Sock.dunno, r⟩
  · subst he; exact Or.inl (doubleInt_self _)
  obtain ⟨s, ra⟩ := new
  cases s with
  | void => exact Or.inl (doubleInt_void_left rfl he)
  | mk ca da =>
    right
    unfold Sock.dunno at he ⊢
    rw [doubleInt_mk he]
    simp

/-- **`+msg-anno` with an unknown old product** keeps it or gives
`Anno.dunno`. -/
theorem msgAnno_dunno_old (new : Anno) (r : Noun) :
    msgAnno new ⟨Sock.dunno, r⟩ = ⟨Sock.dunno, r⟩ ∨ msgAnno new ⟨Sock.dunno, r⟩ = Anno.dunno := by
  by_cases he : new = ⟨Sock.dunno, r⟩
  · subst he; unfold msgAnno; exact Or.inl (if_pos rfl)
  obtain ⟨s, ra⟩ := new
  cases s with
  | void =>
    left; unfold msgAnno; rw [if_neg he]
  | mk ca da =>
    right; unfold msgAnno; rw [if_neg he]
    cases ca <;> rfl

/-- **Open point (a) for an unknown product**: the merge of `+run` keeps the
old entry's product and map, or gives `|+~` with the map `~`. -/
theorem mergeProd_dunno_old (moved : Bool) (new : Anno) (r : Noun) :
    mergeProd moved new ⟨Sock.dunno, r⟩ = ⟨Sock.dunno, r⟩ ∨
      mergeProd moved new ⟨Sock.dunno, r⟩ = Anno.dunno := by
  unfold mergeProd
  split
  · exact msgAnno_dunno_old new r
  · exact doubleInt_dunno_old new r

/-- So an entry whose product is `|+~` keeps it, and its map changes at most
once, to `~`, after which it stays. -/
theorem runDatum_dunno_prod (moved : Bool) (bus : Sock) (out : FolOut) (gen' : Gen) (old : Datum)
    (h : old.prod = Sock.dunno) :
    (runDatum moved bus out gen' old).1.prod = Sock.dunno ∧
      ((runDatum moved bus out gen' old).1.map = old.map ∨ (runDatum moved bus out gen' old).1.map = A 0) := by
  have e := mergeProd_dunno_old moved out.prod old.map
  rw [← h] at e
  simp only [runDatum]
  rcases e with e | e
  · rw [e]; exact ⟨h, Or.inl rfl⟩
  · rw [e]; exact ⟨rfl, Or.inr rfl⟩

end SkaModel
end Formalization
