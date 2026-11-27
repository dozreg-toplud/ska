import lemmas.Ska.AnnotSBase
import lemmas.Ska.MemoPoke

/-!
# `InvBSR`: the memo strand with `AnnotK` (track Q, README Gaps 27)

The `annot` strand of `MemoPoke.lean` with `AnnotK` in place of `Annot`; the
other strands (`LessRel`, `ProdRel`, `MemoEntryOK`) are the old ones.

What the analysis gives of a run (`folTopR_annotK`, `AnnotSFol.lean`) is
taken here as the hypothesis `FolTopK lib`, which that theorem discharges.

* `annotK_of_graphM`: every entry of the final graph of a poke satisfies
  `AnnotK` on its code requirement, given that the memo's entries do (a hit
  keeps the memo entry's code requirement and nomm, `patchDatum` changes only
  the product);
* `codeOKK_of_graphM`, `memoFinal_annotK` (the entry `+memo-final-entry`
  makes, for every table that has the bells of the poke's table);
* `MemoInvK` (the `AnnotK` half of `MemoInv`), `memoInvK_empty`,
  `memoInvK_poke`.
-/

namespace Formalization
namespace SkaModel

open Nock AnnotSF

/-- **What the analysis gives of a run, with `AnnotK`**: the statement of
`folTopR_annotK` (`AnnotSFol.lean`), as a hypothesis of this file. -/
def FolTopK (lib : Lib) : Prop :=
  ∀ (P : Sock → Noun → TabEntry → Prop) (code : Bell → Option Nomm),
    (∀ tab, TabIn P tab → RTab lib code tab) → ∀ n bus fol out gen', WellFormed bus →
      FolTopR P n bus fol out gen' → AnnotK lib code (Fits (Ca.app gen'.want bus)) fol out.nomm

section Graph

variable {lib : Lib} {code : Bell → Option Nomm} {Mem G : Entry → Prop}

/-- **Every entry of the graph satisfies `AnnotK`** on its code requirement,
given that the memo's entries do. -/
theorem annotK_of_graphM (hK : FolTopK lib) (hG : ConvergedGraphM lib code Mem G) (hhas : CodeHas code G)
    (hwf : ∀ e, G e → WellFormed e.more)
    (hmemK : ∀ m, Mem m → AnnotK lib code (Fits m.d.less) m.fol m.d.nomm) {e : Entry} (he : G e) :
    AnnotK lib code (Fits e.d.less) e.fol e.d.nomm := by
  have hL := lessRel_of_graphM hG
  have hP := prodRel_of_graphM hG hwf
  rcases hG e he with hr | hh
  · obtain ⟨P, hPA, n, out, gen', _, _, h, hn, ⟨w, hl⟩, _⟩ := hr
    rw [hn, hl]
    exact (hK P code (fun tab ht => rtab_of_answers hL hP hhas (fun s f a h => hPA _ _ _ (ht s f a h)))
      n _ _ _ _ (hwf e he) h).mono (fun x hx => fits_app_uni (hwf e he) hx)
  · obtain ⟨m, hmM, _, _, _, hf, hd⟩ := hh
    rw [hd, hf]
    exact hmemK m hmM

/-- **`CodeOKK` from the final graph and the memo.** -/
theorem codeOKK_of_graphM (hK : FolTopK lib) (hG : ConvergedGraphM lib code Mem G)
    (hc : CodeIs code (fun e => G e ∨ Mem e))
    (hmemK : ∀ m, Mem m → AnnotK lib code (Fits m.d.less) m.fol m.d.nomm)
    (hhas : CodeHas code G) (hwf : ∀ e, G e → WellFormed e.more) : CodeOKK lib code := by
  intro bl nb h
  obtain ⟨e, he, rfl, rfl⟩ := hc bl nb h
  rcases he with he | he
  · exact annotK_of_graphM hK hG hhas hwf hmemK he
  · exact hmemK e he

end Graph

/-! ## Across pokes -/

/-- **The entry of `+memo-final-entry` satisfies `AnnotK`** for every code
table that has the bells of this poke's code table. -/
theorem memoFinal_annotK {lib : Lib} {code code' : Bell → Option Nomm} {Mem G : Entry → Prop}
    (hK : FolTopK lib) (hG : ConvergedGraphM lib code Mem G) (hhas : CodeHas code G)
    (hwf : ∀ e, G e → WellFormed e.more ∧ WellFormed e.d.prod)
    (hmemK : ∀ m, Mem m → AnnotK lib code (Fits m.d.less) m.fol m.d.nomm) {e : Entry} (he : G e)
    (hcc : ∀ bl nb, code bl = some nb → ∃ nb', code' bl = some nb') :
    AnnotK lib code' (Fits (memoFinal e).d.less) (memoFinal e).fol (memoFinal e).d.nomm :=
  (annotK_of_graphM hK hG hhas (fun e he => (hwf e he).1) hmemK he).mono_code hcc

/-- **The `AnnotK` half of `MemoInv`**: every entry satisfies `AnnotK` for
every code table that has the memo's bells. -/
def MemoInvK (lib : Lib) (Mem : Entry → Prop) : Prop :=
  ∀ code : Bell → Option Nomm, (∀ m, Mem m → ∃ nb, code ⟨m.d.less, m.fol⟩ = some nb) →
    ∀ m, Mem m → AnnotK lib code (Fits m.d.less) m.fol m.d.nomm

theorem memoInvK_empty (lib : Lib) : MemoInvK lib (fun _ => False) := fun _ _ _ h => h.elim

/-- **Every poke keeps `MemoInvK`**, on the hypotheses of `memoInv_poke`. -/
theorem memoInvK_poke {lib : Lib} {code : Bell → Option Nomm} {Mem Mem' G : Entry → Prop}
    (hK : FolTopK lib) (hinv : MemoInvK lib Mem) (hG : ConvergedGraphM lib code Mem G)
    (hhas : CodeHas code G) (hwf : ∀ e, G e → WellFormed e.more ∧ WellFormed e.d.prod)
    (hmc : ∀ m, Mem m → ∃ nb, code ⟨m.d.less, m.fol⟩ = some nb)
    (hdom : ∀ bl nb, code bl = some nb → ∃ m, Mem' m ∧ bl = ⟨m.d.less, m.fol⟩)
    (hnew : ∀ m, Mem' m → Mem m ∨ ∃ e, G e ∧ m = memoFinal e) : MemoInvK lib Mem' := by
  have hmemK := hinv code hmc
  intro code' hcov m hm
  have hcc : ∀ bl nb, code bl = some nb → ∃ nb', code' bl = some nb' := by
    intro bl nb h
    obtain ⟨m', hm', rfl⟩ := hdom bl nb h
    exact hcov m' hm'
  rcases hnew m hm with hold | ⟨e, he, rfl⟩
  · refine hinv code' (fun m' hm' => ?_) m hold
    obtain ⟨nb, h⟩ := hmc m' hm'
    exact hcc _ _ h
  · exact memoFinal_annotK hK hG hhas hwf hmemK he hcc

end SkaModel
end Formalization
