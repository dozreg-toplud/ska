import lemmas.Ska.AnnotSMemo
import lemmas.Ska.PokeBake

/-!
# `InvBSR`: a poke of the analysis with `AnnotK` (track Q, README Gaps 27)

The `AnnotK` strand of `PokeConv.lean` (generated from `skaPoke_sound` by
`tools/gen/annots_memo.py`).  `PokeInvK` is `PokeInv` with the memo's
entries and the table's nomms satisfying `AnnotK`.  `skaPoke_soundK`: a poke
keeps `PokeInvK` (the `PokeInv` half is `skaPoke_sound`), and every datum of
the poke satisfies `AnnotK` on its bell with the extended table (what the
bake reads).  `pokeDat_annotK` (from `pokeDat_ok` of `PokeBake.lean`): every
datum the `dat` gate of the bake gives satisfies `AnnotK`.  Both take
`FolTopK lib` (`AnnotSMemo.lean`), the statement of `folTopR_annotK`.
-/

namespace Formalization
namespace SkaModel

open Nock AnnotSF

namespace Ana

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-- **`PokeInv` with `AnnotK`**: the memo's entries and the table's nomms
satisfy `AnnotK` on their code requirements. -/
structure PokeInvK (lib : Lib) (memo : Memo M) (code : Bell → Option Nomm) : Prop where
  base : PokeInv lib memo code
  okK : ∀ m, MemEnt memo m → AnnotK lib code (Fits m.d.less) m.fol m.d.nomm
  codeOKK : CodeOKK lib code

/-- Before the first poke: an empty memo and an empty table. -/
theorem PokeInvK.init (lib : Lib) : PokeInvK lib (Treap.empty : Memo M) (fun _ => none) where
  base := PokeInv.init lib
  okK := fun _ ⟨_, _, _, _, h, _⟩ => by simp [Treap.get_empty] at h
  codeOKK := fun _ _ h => by cases h

/-- **A poke of the analysis keeps `PokeInvK`**, and its datums satisfy
`AnnotK` on their bells with the table of the earlier pokes extended by the
datums. -/
theorem skaPoke_soundK {lib : Lib} (hK : FolTopK lib) (env : Env R) {n : Nat} {root : Ident} {memo memo' : Memo M} {reg reg' : R}
    {code : Bell → Option Nomm} {pruned : Callgraph M} {dats : M Bell (FDatum M)} {rd : FDatum M}
    (hinv : PokeInvK lib memo code) (hw : WellFormed root.1) (hnr : NormSock root.1) (hnvr : root.1 ≠ Sock.void)
    (h : skaPoke env n root memo reg = some (pruned, dats, memo', rd, reg')) :
    PokeInvK lib memo' (extendCode code dats) ∧
    ∀ bl d, Treap.get dats bl = some d → AnnotK lib (extendCode code dats) (Fits bl.less) bl.fol d.nomm := by
  have hbase := (skaPoke_sound env hinv.base hw hnr hnvr h).1
  unfold skaPoke at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨⟨g, regG⟩, hg, pr, hpr, rd', _, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, hdats, hmemo, _, _⟩ := he
  subst hdats hmemo
  generalize hcd : extendCode code (pokeMemo pr memo).1 = code' at hbase ⊢
  have hcc : ∀ bl nb, code bl = some nb → ∃ nb', code' bl = some nb' := by
    rw [← hcd]; exact extendCode_has
  have hok' : ∀ m, MemEnt memo m → MemoEntryOK lib code' m := fun m hm => (hinv.base.ok m hm).mono_code hcc
  have hokK' : ∀ m, MemEnt memo m → AnnotK lib code' (Fits m.d.less) m.fol m.d.nomm :=
    fun m hm => (hinv.okK m hm).mono_code hcc
  obtain ⟨G, hG, hcovP, hGp, hwfG, hnP⟩ := skaCallgraph_prunedM (lib := lib) (code := code') env memo hinv.base.wf
    hinv.base.memoNorm hinv.base.keys hok' hw hnr hnvr hg hpr
  obtain ⟨d1, d2, d3⟩ := pokeMemo_spec pr memo
  have hdat : ∀ i d, Treap.get pr i = some d → ∃ nb, code' ⟨d.less, i.2⟩ = some nb := by
    intro i d hd
    rw [← hcd]
    unfold extendCode
    have := d2 i d hd
    split
    · exact ⟨_, rfl⟩
    · cases hn : Treap.get (pokeMemo pr memo).1 ⟨d.less, i.2⟩ with
      | none => rw [hn] at this; cases this
      | some d' => exact ⟨d'.nomm, rfl⟩
  have hhas : CodeHas code' G := by
    intro e he
    obtain ⟨d, hd, hl⟩ := hGp e he
    rw [hl]
    exact hdat _ d hd
  have hwf1 : ∀ e, G e → WellFormed e.more := fun e he => (hwfG e he).1
  have hcode : CodeOKK lib code' := by
    intro bl nb hb
    have hb' := hb
    rw [← hcd] at hb'
    unfold extendCode at hb'
    split at hb'
    · rename_i nb0 hc0
      cases hb'
      exact (hinv.codeOKK bl _ hc0).mono_code hcc
    · obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hb'
      obtain ⟨i, hi, rfl⟩ := d1 bl d hd
      exact annotK_of_graphM hK hG hhas hwf1 hokK' (hcovP i d hi)
  refine ⟨⟨hbase, fun m hm => ?_, hcode⟩, ?_⟩
  · obtain ⟨f, ms, s, ent, h1, h2, rfl⟩ := hm
    rcases d3 f ms s ent h1 h2 with ⟨ms', e1, e2⟩ | ⟨i, d, hd, rfl, rfl⟩
    · exact hokK' _ ⟨f, ms', s, ent, e1, e2, rfl⟩
    · exact memoFinal_annotK hK hG hhas hwfG hokK' (hcovP i d hd) (fun bl nb h => ⟨nb, h⟩)
  · intro bl d hd
    obtain ⟨i, hi, rfl⟩ := d1 bl d hd
    exact annotK_of_graphM hK hG hhas hwf1 hokK' (hcovP i d hi)

end Ana

namespace Bake

open Ana

variable {M : Type → Type → Type} [Treap M]

/-- **Every datum of the bake's `dat` gate satisfies `AnnotK`** on its code
requirement, with the ghost table after the poke. -/
theorem pokeDat_annotK {lib : Lib} {code : Bell → Option Nomm} {dats : M Bell (FDatum M)} {memo : Memo M}
    (hinv : Ana.PokeInvK lib memo code) (hlk : LessKeys memo)
    (hd : ∀ bl d, Treap.get dats bl = some d → AnnotK lib code (Fits bl.less) bl.fol d.nomm) :
    ∀ t d, pokeDat dats memo t = some d → AnnotK lib code (Fits t.less) t.fol d.nomm := by
    intro t d h
    unfold pokeDat at h
    split at h
    · rename_i d' hd'
      cases h
      exact hd t d' hd'
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨ent, he, rfl⟩ := h
      unfold gutMi Treap.gut at he
      cases hm : Treap.get memo t.fol with
      | none => simp [hm, Treap.get_empty] at he
      | some ms =>
        simp only [hm, Option.getD_some] at he
        have hmem : MemEnt memo (entOf ent.1 ent.2) := ⟨t.fol, ms, t.less, ent, hm, he, rfl⟩
        have ha := hinv.okK _ hmem
        have hf : ent.1.2 = t.fol := hinv.base.keys _ _ _ _ hm he
        have hl : ent.2.less = t.less := hlk _ _ _ _ hm he
        simp only [entOf] at ha
        rw [hf] at ha
        rw [show (FDatum.core ent.2).less = t.less from hl] at ha
        exact ha

end Bake

end SkaModel
end Formalization
