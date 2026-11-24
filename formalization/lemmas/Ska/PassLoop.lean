import lemmas.Ska.RunStep

/-!
# The pass loop of `+analyze`: a poke on which it did not end, and what is monotone

## 1. The witness, and the fix of 1813f09

The pass loop of `+analyze` goes on while a pass changed an entry
(`[less-code prod map indi seek]`) or found a new function.  Up to 1813f09
`less-code` was `(app:ca want bus)` of the last run, not merged with the old
entry, and a change of it alone kept the loop going.  On that compiler this
loop did not end on

```
F = [6 [3 0 6] [0 6] [2 [1 0] [2 [[0 2] [0 7] [0 6]] [0 2]]]]
(poke [%full [F [1 0] [1 0]] F])
```

(`formalization/tools/hoon/swaploop.hoon`).  The function `[&+[F [1 0] [1 0]] F]`
calls itself with its sample swapped (`[[0 2] [0 7] [0 6]]`), which is the
same identity since both halves of the sample are `[1 0]`, and calls the
product of that call as a formula on `0`.  In its first run the recursive
call reads the bunt entry, `%void`, so the product is the base branch `[0 6]`.
In the next run that product, patched for the swapped subject, is `[1 0]` with
provenance axis `7`: a direct call, so `want` requires axis `7` and the
product becomes `|+~` (the join of `[1 0]` and `0`).  From then on the call is
indirect and requires nothing, and the recursive call contributes the entry's
`less-code` pulled back through the swap.  So `less-code` alternated between
`[& [| &]]` and `[& [& |]]` (the battery and one half of the sample), every
pass changed the entry, and the loop never exited: the instrumented library
counted 53,345 passes in 60 s, and the unmodified `+poke` had not answered
after 300 s.  `CgHalts` of `AnaEnds.lean`, `AnaEnds` of `PokeHalt.lean` and
the hypothesis `Halting` of `Assembly.lean` were false of that pill.

Since 1813f09 `+run` unites `want` with the cape of the old entry's
`less-code` before the mask, `(app:ca (uni:ca want old) bus)` with
`old=?@(less-code.data | cape.less-code.data)`, and the model follows it
(`runDatum_less`: the code requirement is `app:ca` of `uni:ca want
(darkOf old.less)` and `bus`).  The mask only grows (`runDatum_less_mask`),
so on the witness `less-code` goes from `[& [| &]]` to `[& [& &]]` and stays.
On the compiler of 1813f09 (the pill of this branch) the poke above returns
(`runhoon.sh swaploop.hoon`, 2026-11-24: `[%poke-returned %.y]`).  A change
of `less-code` still sets `changed` (`runDatum_changed_of_less`), but it can
now happen only finitely often per identity (section 3).

## 2. The data

The library instrumented to compare, at the end of each pass, every member's
entry with the one it had when the pass began (`huge:so` both ways for
`less-code` and the product, inclusion of capes for `indi` and `seek`) found,
over the 19 pokes of `he2.hoon`, `sitesmeet4.hoon` and `voidscc.hoon`
(2026-11-24): `less-code` only grew (1,075 growths, no shrinking, no
incomparable change), the product only lost knowledge (339 losses, no gain),
`indi` and `seek` only grew (11 and 14 growths), no member was culled, and
the member set changed after the first pass only by new members (51 in four
passes, none removed).  The largest pass count stayed 6.  The witness above
is the first poke where `less-code` changes in a way other than growth.

## 3. What is monotone, and the measure a proof of `CgHalts` would use

The product an entry keeps only loses knowledge across runs: every noun the
old product holds of, the new one holds of (`runDatum_prod_old`, from
`mergeProd_fits_old`, for both `+double-int` and `+msg-anno`).  The mask of
`less-code` only grows: every axis of the old entry's cape is in the new
mask (`runDatum_less_mask`), and the subject sock `bus` of an identity is
fixed, so the cape of `less-code` grows inside the cape of `bus`.  `indi`
and `seek` are merged by `+msg-ca` (which only adds `&`) when the fields
before them did not change, and are recomputed otherwise.

So a proof of `CgHalts` (not attempted) would now use, per identity, the
lexicographic measure of the cape size of `less-code` (growing, at most
`cape-size` of `bus`), the `heMeasure` of the product (shrinking, by
`runDatum_prod_old`), then `indi` and `seek` (growing under `+msg-ca`, at
most the cape of `bus`), summed over the identities of the graph, which are
finitely many by the argument of `AnaEnds.lean` (callable formulas and
`+he-sock`).  The provenance `map` is the point this sketch leaves open: it
is compared by `changed` and can change while the product sock does not.
-/

namespace Formalization
namespace SkaModel

open Nock

theorem msgAnno_blank_right' : ∀ (k : Nat) (a b : Anno), Sock.msr a.sock + Sock.msr b.sock < k →
    b.sock.Blank → (msgAnno a b).sock.Blank := by
  intro k
  induction k with
  | zero => intro _ _ h; omega
  | succ k ih =>
  intro a b hk hb
  obtain ⟨sa, ra⟩ := a
  obtain ⟨sb, rb⟩ := b
  obtain ⟨c, d, hs, hc⟩ := hb
  simp only at hs
  subst hs
  unfold msgAnno
  split
  · rename_i heq
    simp only [Anno.mk.injEq] at heq
    rw [heq.1]; exact ⟨c, d, rfl, hc⟩
  · split
    · exact ⟨c, d, rfl, hc⟩
    · exfalso
      rename_i hh _
      simp only [Anno.mk.injEq] at hh
      exact Sock.noConfusion hh.1
    · rename_i ah aT da ra' bh bT db rb' heq1 heq2
      simp only [Anno.mk.injEq, Sock.mk.injEq] at heq1 heq2
      obtain ⟨rfl, rfl⟩ := heq1
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq2
      simp only [Cape.isNo, Bool.and_eq_true] at hc
      simp only at hk
      exact knit_blank
        (ih _ _ (by have := msr_hed_lt (c := Cape.cell ah aT) (by simp) da
                    have := msr_hed_lt (c := Cape.cell bh bT) (by simp) d; simp only at hk ⊢; omega)
          (hed_blank ⟨_, _, rfl, by simp [Cape.isNo, hc.1, hc.2]⟩))
        (ih _ _ (by have := msr_tel_lt (c := Cape.cell ah aT) (by simp) da
                    have := msr_tel_lt (c := Cape.cell bh bT) (by simp) d; simp only at hk ⊢; omega)
          (tel_blank ⟨_, _, rfl, by simp [Cape.isNo, hc.1, hc.2]⟩))
    · exact dunno_blank

/-- **`+msg-anno` knows no more than the old product.** -/
theorem msgAnno_fits_right' : ∀ (k : Nat) (a b : Anno), Sock.msr a.sock + Sock.msr b.sock < k →
    ∀ n, Fits b.sock n → Fits (msgAnno a b).sock n := by
  intro k
  induction k with
  | zero => intro _ _ h; omega
  | succ k ih =>
  intro a b hk n hf
  obtain ⟨sa, ra⟩ := a
  obtain ⟨sb, rb⟩ := b
  unfold msgAnno
  split
  · rename_i heq
    simp only [Anno.mk.injEq] at heq
    rw [heq.1]; exact hf
  · split
    · exact hf
    · rename_i hh _
      simp only [Anno.mk.injEq] at hh
      rw [hh.1] at hf; exact absurd hf id
    · rename_i ah aT da ra' bh bT db rb' heq1 heq2
      simp only [Anno.mk.injEq] at heq1 heq2
      obtain ⟨rfl, rfl⟩ := heq1
      obtain ⟨rfl, rfl⟩ := heq2
      simp only at hk hf
      have h1 := msr_hed_lt (c := Cape.cell ah aT) (by simp) da
      have h2 := msr_hed_lt (c := Cape.cell bh bT) (by simp) db
      have h3 := msr_tel_lt (c := Cape.cell ah aT) (by simp) da
      have h4 := msr_tel_lt (c := Cape.cell bh bT) (by simp) db
      cases n with
      | cell n1 n2 =>
        exact knit_fits (ih _ _ (by simp only; omega) _ (hed_fits hf))
          (ih _ _ (by simp only; omega) _ (tel_fits hf))
      | atom m =>
        obtain ⟨bh', bt'⟩ := hed_tel_blank_of_atom (k := m) hf
        exact (knit_blank (msgAnno_blank_right' _ _ _ (Nat.lt_succ_self _) bh')
          (msgAnno_blank_right' _ _ _ (Nat.lt_succ_self _) bt')).fits _
    · exact fits_dunno _

/-- **The product an entry keeps knows no more than the entry's old
product**, by `+msg-anno` and by `+double-int`. -/
theorem mergeProd_fits_old (moved : Bool) (new old : Anno) {n : Noun} (h : Fits old.sock n) :
    Fits (mergeProd moved new old).sock n := by
  unfold mergeProd
  split
  · exact msgAnno_fits_right' _ new old (Nat.lt_succ_self _) n h
  · exact doubleInt_fits_right new old h

/-- **A run only loses knowledge of the product**: every noun the old entry's
product holds of, the new entry's product holds of. -/
theorem runDatum_prod_old (moved : Bool) (bus : Sock) (out : FolOut) (gen' : Gen) (old : Datum)
    {n : Noun} (h : Fits old.prod n) : Fits (runDatum moved bus out gen' old).1.prod n :=
  mergeProd_fits_old moved out.prod ⟨old.prod, old.map⟩ h

/-- **`less-code` is the run's `want` united with the old entry's cape**,
then masked on `bus`: `(app:ca (uni:ca want old) bus)` (1813f09). -/
theorem runDatum_less (moved : Bool) (bus : Sock) (out : FolOut) (gen' : Gen) (old : Datum) :
    (runDatum moved bus out gen' old).1.less = Ca.app (Ca.uni gen'.want (darkOf old.less)) bus := rfl

/-- **The mask of `less-code` only grows**: every axis of the old entry's
cape is in the mask of the new one, and so is every axis of `want`. -/
theorem runDatum_less_mask (gen' : Gen) (old : Datum) (r : List Bool) :
    ((darkOf old.less).Has r ∨ gen'.want.Has r) → (Ca.uni gen'.want (darkOf old.less)).Has r :=
  fun h => (uni_has _ _ r).mpr (h.elim Or.inr Or.inl)

/-- **A change of `less-code` alone sets `changed`**, which keeps the pass
loop going. -/
theorem runDatum_changed_of_less (moved : Bool) (bus : Sock) (out : FolOut) (gen' : Gen) (old : Datum)
    (h : Ca.app (Ca.uni gen'.want (darkOf old.less)) bus ≠ old.less) :
    (runDatum moved bus out gen' old).2.2 = true := by
  simp only [runDatum, decide_eq_true_eq, ne_eq, Prod.mk.injEq, not_and]
  intro e
  exact absurd e h

end SkaModel
end Formalization
