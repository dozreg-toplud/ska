import lemmas.Ska.ConvergeRel

/-!
# Memo hits from earlier pokes

`+analyze` answers an identity that the persistent memo hits (`+git:mi` on
`memo-final`) with the memo entry's datum patched for the identity's subject
sock, and puts that under the identity in the graph.  Such an entry was not
written by a run on its identity, so it is not `RunEntryR`; and the memo
entry itself, as `+memo-final-entry` stores it, has its identity's subject
masked to `app:ca indi more`, on which it is not `RunEntryR` either.

What a memo entry needs is less (`MemoEntryOK`): a well-formed product, the
provenance invariant of its product on the subjects of its code requirement,
and the invariant `Annot` of its nomm there.  The entry `+analyze` makes
from a hit (`HitEntry`) then satisfies what the graph's entries must
(`lessRel_hit`, `prodRel_hit`), and `ConvergedGraphM` is `ConvergedGraphR`
with these entries as a third kind.  `agree_pokeM`: agreement for a poke
whose memo hits, given the memo's entries sound for the poke's code table.

Across pokes (`memoEntryOK_final`): the entry `+memo-final-entry` makes from
a final entry of a poke is `MemoEntryOK` for every code table that has the
bells the entry calls (`Annot.mono_code`).
-/

namespace Formalization
namespace SkaModel

open Nock

/-- **A sound memo entry** for the code table `code`. -/
structure MemoEntryOK (lib : Lib) (code : Bell → Option Nomm) (m : Entry) : Prop where
  wf : WellFormed m.d.prod
  prov : ∀ y gul p, Fits m.d.less y → Mink lib gul [] y m.fol (Tone.zero p) → ProvR y m.d.prod m.d.map p
  annot : Annot lib code (Fits m.d.less) m.fol m.d.nomm

/-- **The entry of a memo hit**: a sound memo entry `m` of `Mem` that the
identity's subject sock hits, patched for it, as `+analyze` puts it. -/
def HitEntry (lib : Lib) (code : Bell → Option Nomm) (Mem : Entry → Prop) (e : Entry) : Prop :=
  ∃ m, Mem m ∧ MemoEntryOK lib code m ∧ e.more ≠ Sock.void ∧ hitTest m e.more = some true ∧
    e.fol = m.fol ∧ e.d = patchDatum m.d e.more

theorem lessRel_hit {lib : Lib} {code : Bell → Option Nomm} {Mem : Entry → Prop} {e : Entry}
    (h : HitEntry lib code Mem e) :
    ∀ lc dl, e.d.less = Sock.mk lc dl → ∀ y, Fits (Ca.app lc e.more) y → Fits e.d.less y := by
  obtain ⟨m, _, _, hq, ht, _, hd⟩ := h
  intro lc dl hl y hy
  have hl' : m.d.less = Sock.mk lc dl := by rw [← hl, hd]; rfl
  rw [hd]
  exact huge_less hq ht hl' hy

theorem prodRel_hit {lib : Lib} {code : Bell → Option Nomm} {Mem : Entry → Prop} {e : Entry}
    (h : HitEntry lib code Mem e) :
    ∀ y gul p, Fits e.d.less y → Mink lib gul [] y e.fol (Tone.zero p) →
      ProvR y e.d.prod e.d.map p ∧ StatOK e.more e.d.prod e.d.map := by
  obtain ⟨m, _, hm, hq, _, hf, hd⟩ := h
  intro y gul p hy hk
  rw [hd] at hy ⊢
  rw [hf] at hk
  have hR := hm.prov y gul p hy hk
  exact ⟨provO_iff.mp (provO_patchProd hq _ _ _ (provO_iff.mpr hR)), statOK_patchProd _ _⟩

theorem wf_hit {lib : Lib} {code : Bell → Option Nomm} {Mem : Entry → Prop} {e : Entry}
    (h : HitEntry lib code Mem e) (hs : WellFormed e.more) : WellFormed e.d.prod := by
  obtain ⟨m, _, hm, _, _, _, hd⟩ := h
  rw [hd]
  exact wf_patchDatum hm.wf hs

/-- **What the final graph of a poke gives, with memo hits**: every entry was
written by a run whose answers come from the graph, or is a memo hit. -/
def ConvergedGraphM (lib : Lib) (code : Bell → Option Nomm) (Mem G : Entry → Prop) : Prop :=
  ∀ e, G e → (∃ P : Sock → Noun → TabEntry → Prop, (∀ s f a, P s f a → Answers G s f a) ∧ RunEntryR P e) ∨
    HitEntry lib code Mem e

theorem ConvergedGraphR.toM {lib : Lib} {code : Bell → Option Nomm} {Mem G : Entry → Prop}
    (h : ConvergedGraphR G) : ConvergedGraphM lib code Mem G := fun e he => Or.inl (h e he)

section Graph

variable {lib : Lib} {code : Bell → Option Nomm} {Mem G : Entry → Prop}

theorem lessRel_of_graphM (hG : ConvergedGraphM lib code Mem G) : LessRel G := by
  intro e lc dl he hl y hy
  rcases hG e he with hr | hh
  · obtain ⟨_, _, _, _, gen', _, _, _, _, hle, _⟩ := hr
    rw [hle] at hl ⊢
    exact app_cape_fits gen'.want e.more lc dl (some y) hl hy
  · exact lessRel_hit hh lc dl hl y hy

theorem prodRelN_of_graphM (hG : ConvergedGraphM lib code Mem G)
    (hwf : ∀ e, G e → WellFormed e.more) : ∀ K, ProdRelN lib G K := by
  have hL := lessRel_of_graphM hG
  intro K
  induction K with
  | zero => intro e _ y gul p _ hm; simp [minkF] at hm
  | succ K ih =>
    intro e he y gul p hy hm
    rcases hG e he with hr | hh
    · obtain ⟨P, hPA, n, out, gen', moved, old, h, _, hl, hpm⟩ := hr
      rw [hl] at hy
      have R := mergeProd_rel moved out.prod old
        (folTopR_relProdN (fun tab ht => rtabL_of_answers hL (fun s f a h => hPA _ _ _ (ht s f a h)))
          (fun tab ht => rtabP_of_answers ih (fun s f a h => hPA _ _ _ (ht s f a h))) (hwf e he) h hy hm)
      rw [← hpm] at R
      exact R
    · exact prodRel_hit hh y gul p hy ⟨K + 1, hm⟩

theorem prodRel_of_graphM (hG : ConvergedGraphM lib code Mem G)
    (hwf : ∀ e, G e → WellFormed e.more) : ProdRel lib G := by
  intro e he y gul p hy hm
  obtain ⟨n, hm⟩ := hm
  exact prodRelN_of_graphM hG hwf n e he y gul p hy hm

/-- Every entry of the graph satisfies `Annot` on its code requirement. -/
theorem annot_of_graphM (hG : ConvergedGraphM lib code Mem G) (hhas : CodeHas code G)
    (hwf : ∀ e, G e → WellFormed e.more) {e : Entry} (he : G e) :
    Annot lib code (Fits e.d.less) e.fol e.d.nomm := by
  have hL := lessRel_of_graphM hG
  have hP := prodRel_of_graphM hG hwf
  rcases hG e he with hr | hh
  · obtain ⟨P, hPA, n, out, gen', _, _, h, hn, hl, _⟩ := hr
    rw [hn, hl]
    exact folTopR_wantSound (fun tab ht => rtab_of_answers hL hP hhas (fun s f a h => hPA _ _ _ (ht s f a h)))
      (hwf e he) h
  · obtain ⟨m, _, hm, _, _, hf, hd⟩ := hh
    rw [hd, hf]
    exact hm.annot

/-- **`CodeOK` from the final graph and the memo**: the code table holds
nomms of the graph's entries and of sound memo entries. -/
theorem codeOK_of_graphM (hG : ConvergedGraphM lib code Mem G)
    (hc : CodeIs code (fun e => G e ∨ Mem e)) (hmem : ∀ m, Mem m → MemoEntryOK lib code m)
    (hhas : CodeHas code G) (hwf : ∀ e, G e → WellFormed e.more) : CodeOK lib code := by
  refine codeOK_of_entries hc fun e he => ?_
  rcases he with he | he
  · exact annot_of_graphM hG hhas hwf he
  · exact (hmem e he).annot

/-- **Agreement from the final graph of a poke with memo hits.** -/
theorem agree_converged_graphM (hG : ConvergedGraphM lib code Mem G)
    (hc : CodeIs code (fun e => G e ∨ Mem e)) (hmem : ∀ m, Mem m → MemoEntryOK lib code m)
    (hhas : CodeHas code G) (hwf : ∀ e, G e → WellFormed e.more) {e : Entry} (he : G e) {x : Noun}
    (hx : Fits e.d.less x) (gul : Noun) (t : Trace) (r : Tone) :
    Mink lib gul t x e.fol r ↔ ∃ m, nommF lib gul code m t x e.d.nomm = some r :=
  nomm_agree lib gul code (codeOK_of_graphM hG hc hmem hhas hwf) (annot_of_graphM hG hhas hwf he) hx t r

end Graph

/-! ## Across pokes -/

/-- `Annot` needs of the code table only that the bells it calls have a
nomm: a table with more bells keeps it. -/
theorem Annot.mono_code {lib : Lib} {code code' : Bell → Option Nomm}
    (hcc : ∀ bl nb, code bl = some nb → ∃ nb', code' bl = some nb')
    {P : Noun → Prop} {f : Noun} {n : Nomm} (h : Annot lib code P f n) : Annot lib code' P f n := by
  induction h with
  | cons _ _ ih1 ih2 => exact Annot.cons ih1 ih2
  | n0 => exact Annot.n0
  | n1 => exact Annot.n1
  | indirect _ _ ih1 ih2 => exact Annot.indirect ih1 ih2
  | direct _ _ hb hl hf ih1 ih2 =>
    obtain ⟨nb', hb'⟩ := hcc _ _ hb
    exact Annot.direct ih1 ih2 hb' hl hf
  | inline _ hc _ ih1 ih2 => exact Annot.inline ih1 hc ih2
  | n3 _ ih => exact Annot.n3 ih
  | n4 _ ih => exact Annot.n4 ih
  | n5 _ _ ih1 ih2 => exact Annot.n5 ih1 ih2
  | n6 _ _ _ ih1 ih2 ih3 => exact Annot.n6 ih1 ih2 ih3
  | n7 _ _ ih1 ih2 => exact Annot.n7 ih1 ih2
  | n8 _ _ ih1 ih2 => exact Annot.n8 ih1 ih2
  | n9 _ _ ih1 ih2 => exact Annot.n9 ih1 ih2
  | n10 hx _ _ ih1 ih2 => exact Annot.n10 hx ih1 ih2
  | n11s _ ih => exact Annot.n11s ih
  | n11d _ _ ih1 ih2 => exact Annot.n11d ih1 ih2
  | mean _ _ ih1 ih2 => exact Annot.mean ih1 ih2
  | n12 _ _ ih1 ih2 => exact Annot.n12 ih1 ih2
  | bare hb => exact Annot.bare hb
  | memo hs _ ih => exact Annot.memo hs ih
  | crash hc => exact Annot.crash hc
  | fold hv => exact Annot.fold hv
  | six0 hb _ ih => exact Annot.six0 hb ih
  | six1 hb _ ih => exact Annot.six1 hb ih
  | n8g _ _ _ ih1 ih2 ih3 => exact Annot.n8g ih1 ih2 ih3
  | n8l hb _ ih => exact Annot.n8l hb ih
  | bareLit hb hd => exact Annot.bareLit hb hd

/-- `+memo-final-entry` on the entries of `Entry`: the subject of the
identity masked down to `indi` (the callees, which `Entry` does not keep,
are dropped). -/
def memoFinal (e : Entry) : Entry := ⟨Ca.app e.d.indi e.more, e.fol, e.d⟩

/-- **The memo entry of a final entry is sound** for every code table that
has the bells of this poke's code table. -/
theorem memoEntryOK_final {lib : Lib} {code code' : Bell → Option Nomm} {Mem G : Entry → Prop}
    (hG : ConvergedGraphM lib code Mem G) (hhas : CodeHas code G)
    (hwf : ∀ e, G e → WellFormed e.more ∧ WellFormed e.d.prod) {e : Entry} (he : G e)
    (hcc : ∀ bl nb, code bl = some nb → ∃ nb', code' bl = some nb') :
    MemoEntryOK lib code' (memoFinal e) where
  wf := (hwf e he).2
  prov := fun y gul p hy hk =>
    (prodRel_of_graphM hG (fun e he => (hwf e he).1) e he y gul p hy hk).1
  annot := (annot_of_graphM hG hhas (fun e he => (hwf e he).1) he).mono_code hcc

/-- **The invariant of the persistent memo across pokes**: every entry is
sound for every code table that has the memo's bells. -/
def MemoInv (lib : Lib) (Mem : Entry → Prop) : Prop :=
  ∀ code : Bell → Option Nomm, (∀ m, Mem m → ∃ nb, code ⟨m.d.less, m.fol⟩ = some nb) →
    ∀ m, Mem m → MemoEntryOK lib code m

theorem memoInv_empty (lib : Lib) : MemoInv lib (fun _ => False) := fun _ _ _ h => h.elim

theorem MemoInv.ok {lib : Lib} {Mem : Entry → Prop} {code : Bell → Option Nomm} (h : MemoInv lib Mem)
    (hc : ∀ m, Mem m → ∃ nb, code ⟨m.d.less, m.fol⟩ = some nb) : ∀ m, Mem m → MemoEntryOK lib code m :=
  h code hc

/-- **Every poke keeps the memo's invariant.**  The poke's code table `code`
has the bells of the old memo `Mem` (`hmc`) and its every bell is a bell of
the new memo `Mem'` (`hdom`: the memo keeps entries by bell, a `put`
replacing the entry of a bell); the new memo's entries are old ones or the
`+memo-final-entry` of final entries of the poke (`hnew`). -/
theorem memoInv_poke {lib : Lib} {code : Bell → Option Nomm} {Mem Mem' G : Entry → Prop}
    (hinv : MemoInv lib Mem) (hG : ConvergedGraphM lib code Mem G) (hhas : CodeHas code G)
    (hwf : ∀ e, G e → WellFormed e.more ∧ WellFormed e.d.prod)
    (hmc : ∀ m, Mem m → ∃ nb, code ⟨m.d.less, m.fol⟩ = some nb)
    (hdom : ∀ bl nb, code bl = some nb → ∃ m, Mem' m ∧ bl = ⟨m.d.less, m.fol⟩)
    (hnew : ∀ m, Mem' m → Mem m ∨ ∃ e, G e ∧ m = memoFinal e) : MemoInv lib Mem' := by
  intro code' hcov m hm
  have hcc : ∀ bl nb, code bl = some nb → ∃ nb', code' bl = some nb' := by
    intro bl nb h
    obtain ⟨m', hm', rfl⟩ := hdom bl nb h
    exact hcov m' hm'
  rcases hnew m hm with hold | ⟨e, he, rfl⟩
  · refine hinv code' (fun m' hm' => ?_) m hold
    obtain ⟨nb, h⟩ := hmc m' hm'
    exact hcc _ _ h
  · exact memoEntryOK_final hG hhas hwf he hcc

/-- **Agreement for a poke whose memo hits**: as `agree_pokeR`, with the
entries of the final graph written by runs or memo hits
(`ConvergedGraphM`), the code table `code` holding nomms of the graph's
entries and of the memo's (`hc`, `hhas`, `hmc`), and the memo's invariant. -/
theorem agree_pokeM {lib : Lib} {g : Graph} {code : Bell → Option Nomm} {Mem G : Entry → Prop}
    (hinv : MemoInv lib Mem) (hs : GStepsR (fun _ => none) g)
    (hin : ∀ e, G e → ∃ d, g (e.more, e.fol) = some d) (hG : ConvergedGraphM lib code Mem G)
    (hc : CodeIs code (fun e => G e ∨ Mem e)) (hhas : CodeHas code G)
    (hmc : ∀ m, Mem m → ∃ nb, code ⟨m.d.less, m.fol⟩ = some nb)
    {e : Entry} (he : G e) {x : Noun} (hx : Fits e.d.less x) (gul : Noun) (t : Trace) (r : Tone) :
    Mink lib gul t x e.fol r ↔ ∃ m, nommF lib gul code m t x e.d.nomm = some r := by
  have hgw := graphWF_stepsR hs graphWF_empty
  have hwf : ∀ e, G e → WellFormed e.more := fun e he => by
    obtain ⟨d, hd⟩ := hin e he
    exact (hgw _ _ hd).1
  exact agree_converged_graphM hG hc (hinv.ok hmc) hhas hwf he hx gul t r

end SkaModel
end Formalization
