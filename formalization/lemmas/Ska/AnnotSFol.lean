import lemmas.Ska.AnnotSFolLoop

/-!
# `InvBSR`, the analysis half: `fol-loop` with answers that change gives `RGoodK`

`folR_rgoodK` is `folR_rgood` (`FolRel.lean`) for `RGoodK`: every result in
`FolR P` whose `want` `W` covers is `RGoodK`, given that every table with
answers in `P` satisfies `RTab`.  The old `RGood` of the recursion comes from
`folR_rgood` itself; the rewritten cases `%8`, `%9`, `%bare` are done again
by taking `FolR` apart (`rgoodK_op8R`, `rgoodK_op9R`, `rgoodK_bareR`).

`folTopR_annotK`: the nomm of a function satisfies `AnnotK` on its code
requirement (`folTopR_wantSound` with `AnnotK`).
-/

namespace Formalization
namespace SkaModel
namespace AnnotSF

open Nock

variable {P : Sock → Noun → TabEntry → Prop}

section Rewritten

variable {lib : Lib} {code : Bell → Option Nomm} {bus : Sock} {W : Cape}
  {sub : Anno} {mk : Option Noun} {bc df : Bool} {gen gen' : Gen} {out : FolOut}

theorem rgoodK_op9R {m : Nat}
    (IH' : ∀ k, k < m → ∀ fol sub mk bc df gen out gen', FolR P k fol sub mk bc df gen out gen' →
      WCov W gen' → RGood lib code bus W fol sub out)
    (IHK' : ∀ k, k < m → ∀ fol sub mk bc df gen out gen', FolR P k fol sub mk bc df gen out gen' →
      WCov W gen' → RGoodK lib code bus W fol sub out)
    {p : Nat} {a b : Noun}
    (h : FolR P m (n3 (A 7) (C a b) (n3 (A 2) (slot 1) (slot p))) sub mk bc df gen out gen')
    (hW : WCov W gen') : RGoodK lib code bus W (C (A 9) (C (A p) (C a b))) sub out := by
  cases m with
  | zero => exact h.elim
  | succ k =>
  obtain ⟨tab1, go1, g1, _, hgo1, h1, he1⟩ := h
  simp only [folStep, shape_op7_eq, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq] at h1
  obtain ⟨⟨o1, gA⟩, hA, ⟨o2, gB⟩, hB, rfl, rfl⟩ := h1
  have FB := hgo1 _ _ _ _ _ _ _ _ hB
  have hW' : WCov W gB := wcov_erase he1 hW
  have K2 := IHK' k (by omega) _ _ _ _ _ _ _ _ FB hW'
  have G1 := IH' k (by omega) _ _ _ _ _ _ _ _ (hgo1 _ _ _ _ _ _ _ _ hA)
    (hW'.of_le (folR_mono k FB))
  have K1 := IHK' k (by omega) _ _ _ _ _ _ _ _ (hgo1 _ _ _ _ _ _ _ _ hA)
    (hW'.of_le (folR_mono k FB))
  refine ⟨AnnotK.n9 K1.annot (K2.annot.mono (rsub_img G1.prod)), fun _ _ _ => trivial,
    fun h => (by cases h), ?_⟩
  intro hv hpv
  by_cases hp : o1.prod.sock = Sock.void
  · exact Or.inl (K1.kc hv hp)
  · exact Or.inr (K2.kc hp hpv)

theorem rgoodK_op8R {m : Nat}
    (IH' : ∀ k, k < m → ∀ fol sub mk bc df gen out gen', FolR P k fol sub mk bc df gen out gen' →
      WCov W gen' → RGood lib code bus W fol sub out)
    (IHK' : ∀ k, k < m → ∀ fol sub mk bc df gen out gen', FolR P k fol sub mk bc df gen out gen' →
      WCov W gen' → RGoodK lib code bus W fol sub out)
    {a b q : Noun}
    (h : FolR P m (n3 (A 7) (C (C a b) (slot 1)) q) sub mk bc df gen out gen')
    (hW : WCov W gen') : RGoodK lib code bus W (C (A 8) (C (C a b) q)) sub out := by
  cases m with
  | zero => exact h.elim
  | succ k =>
  obtain ⟨tab1, go1, g1, _, hgo1, h1, he1⟩ := h
  simp only [folStep, shape_op7_eq, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq] at h1
  obtain ⟨⟨o1, gA⟩, hA, ⟨o2, gB⟩, hB, rfl, rfl⟩ := h1
  have FB := hgo1 _ _ _ _ _ _ _ _ hB
  have hW' : WCov W gB := wcov_erase he1 hW
  have K2 := IHK' k (by omega) _ _ _ _ _ _ _ _ FB hW'
  have W1 : WCov W gA := hW'.of_le (folR_mono k FB)
  have FA := hgo1 _ _ _ _ _ _ _ _ hA
  cases k with
  | zero => exact FA.elim
  | succ j =>
  obtain ⟨tab2, go2, g2, _, hgo2, h2, he2⟩ := FA
  simp only [folStep, shape_cons_eq, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq] at h2
  obtain ⟨⟨ob, gb⟩, hb, ⟨oz, gz⟩, hz, rfl, rfl⟩ := h2
  obtain ⟨rfl, hgz⟩ := folR_slot1 (hgo2 _ _ _ _ _ _ _ _ hz)
  have Wb : WCov W gb := wcov_erase hgz.symm (wcov_erase he2 W1)
  have Gb := IH' j (by omega) _ _ _ _ _ _ _ _ (hgo2 _ _ _ _ _ _ _ _ hb) Wb
  have Kb := IHK' j (by omega) _ _ _ _ _ _ _ _ (hgo2 _ _ _ _ _ _ _ _ hb) Wb
  rw [consProd_unsafe rfl] at K2
  have hsub : ∀ X' x gul y, RP bus W sub X' x → Mink lib gul [] x (C a b) (Tone.zero y) →
      RP bus W ⟨So.knit ob.prod.sock sub.sock, Pi.cons ob.prod.src sub.src⟩ X' (C y x) := by
    intro X' x gul y hx hm
    have R := Gb.prod X' x gul y hx hm
    refine ⟨hx.req, provO_iff.mp (provO_knit ?_ ?_), statOK_knit R.stat hx.stat⟩
    · rw [slotO_some_cell_false]; exact provO_iff.mpr R.prov
    · rw [slotO_some_cell_true]; exact provO_iff.mpr hx.prov
  refine ⟨AnnotK.n8 Kb.annot (K2.annot.mono ?_), fun _ _ _ => trivial, fun h => (by cases h), ?_⟩
  · intro z ⟨x, y, gul, ⟨X', hx⟩, hm, hz⟩
    subst hz
    exact ⟨X', hsub X' x gul y hx hm⟩
  · intro hv hpv
    by_cases hk : So.knit ob.prod.sock sub.sock = Sock.void
    · rcases knit_void hk with e | e
      · exact Or.inl (Or.inl (Kb.kc hv e))
      · exact absurd e hv
    · exact Or.inr (K2.kc hk hpv)

theorem rgoodK_bareR {m : Nat} {a b : Noun}
    (G' : RGoodK lib code bus W (n3 (A 2) (slot 1) (quote (C (A 11) (C (A Tag.bare) (C a b))))) sub out)
    (h : FolR P m (n3 (A 2) (slot 1) (quote (C (A 11) (C (A Tag.bare) (C a b))))) sub mk true df gen out gen') :
    RGoodK lib code bus W (C (A 11) (C (A Tag.bare) (C a b))) sub out :=
  ⟨by rw [bare_nommR h]; exact AnnotK.bare (by simp [isBare]), G'.detK, G'.safK, G'.kc⟩

end Rewritten

/-- **`folR_rgood` for `RGoodK`**: every result in `FolR P` whose `want` `W`
covers is `RGoodK`, given that every table with answers in `P` satisfies
`RTab`. -/
theorem folR_rgoodK {lib : Lib} {code : Bell → Option Nomm} {bus : Sock} {W : Cape}
    (hT : ∀ tab, TabIn P tab → RTab lib code tab) (hwf : WellFormed bus) :
    ∀ n fol sub mk bc df gen out gen', FolR P n fol sub mk bc df gen out gen' → WCov W gen' →
      RGoodK lib code bus W fol sub out := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro fol sub mk bc df gen out gen' h hW
  cases n with
  | zero => exact h.elim
  | succ m =>
  obtain ⟨tab, go, g', ht, hgo, h, he⟩ := h
  have hW' : WCov W g' := wcov_erase he hW
  have IH : GoRGood lib code bus W go := fun _ _ _ _ _ _ _ _ hg hw =>
    folR_rgood hT hwf m _ _ _ _ _ _ _ _ (hgo _ _ _ _ _ _ _ _ hg) hw
  have IHK : GoRGoodK lib code bus W go := fun _ _ _ _ _ _ _ _ hg hw =>
    ih m (by omega) _ _ _ _ _ _ _ _ (hgo _ _ _ _ _ _ _ _ hg) hw
  have hM : GoMono go := goMono_of_goR hgo
  have IH' : ∀ k, k < m + 1 → ∀ fol sub mk bc df gen out gen', FolR P k fol sub mk bc df gen out gen' →
      WCov W gen' → RGood lib code bus W fol sub out := fun k _ => folR_rgood hT hwf k
  have IHK' : ∀ k, k < m + 1 → ∀ fol sub mk bc df gen out gen', FolR P k fol sub mk bc df gen out gen' →
      WCov W gen' → RGoodK lib code bus W fol sub out := fun k hk => ih k hk
  cases hs : shape fol with
  | cons a b q => exact rgoodK_cons IHK hM hs h hW'
  | op0 p => exact rgoodK_op0 hs h
  | op1 p => exact rgoodK_op1 hs h
  | op2 a b q => exact rgoodK_op2 (hT tab ht) hwf IH IHK hM hs h hW'
  | op3 a b => exact rgoodK_op3 IHK hs h hW'
  | op4 a b => exact rgoodK_op4 IHK hs h hW'
  | op5 a b q => exact rgoodK_op5 IHK hM hs h hW'
  | op6 a b q r => exact rgoodK_op6 IHK hM hs h hW'
  | op7 a b q => exact rgoodK_op7 IH IHK hM hs h hW'
  | op8 a b q =>
    have hf := shape_eq hs (by simp)
    simp only [Shape.fol] at hf
    subst hf
    simp only [folStep, hs] at h
    exact rgoodK_op8R (fun k hk => IH' k (by omega)) (fun k hk => IHK' k (by omega))
      (hgo _ _ _ _ _ _ _ _ h) hW'
  | op9 p a b =>
    have hf := shape_eq hs (by simp)
    simp only [Shape.fol] at hf
    subst hf
    simp only [folStep, hs] at h
    exact rgoodK_op9R (fun k hk => IH' k (by omega)) (fun k hk => IHK' k (by omega))
      (hgo _ _ _ _ _ _ _ _ h) hW'
  | op10 ax don r1 r2 => exact rgoodK_op10 IHK hM hs h hW'
  | op11s p a b =>
    by_cases hp : p = Tag.bare
    · subst hp
      have hf := shape_eq hs (by simp)
      simp only [Shape.fol] at hf
      subst hf
      simp only [folStep, hs, if_true] at h
      exact rgoodK_bareR (IHK _ _ _ _ _ _ _ _ h hW') (hgo _ _ _ _ _ _ _ _ h)
    · exact rgoodK_op11s_plain IHK hs hp h hW'
  | op11d tag h1 h2 f => exact rgoodK_op11d IH IHK hM hs h hW'
  | op11c x y h1 h2 f => exact rgoodK_op11c IHK hs h hW'
  | op12 a b q => exact rgoodK_op12 IHK hM hs h hW'
  | other => exact rgoodK_other hs h

/-- **The nomm of a function satisfies `AnnotK` on its code requirement**
(`folTopR_wantSound` with `AnnotK`). -/
theorem folTopR_annotK {P : Sock → Noun → TabEntry → Prop} {lib : Lib} {code : Bell → Option Nomm}
    (hT : ∀ tab, TabIn P tab → RTab lib code tab) {n : Nat} {bus : Sock} {fol : Noun} {out : FolOut}
    {gen' : Gen} (hwf : WellFormed bus) (h : FolTopR P n bus fol out gen') :
    AnnotK lib code (Fits (Ca.app gen'.want bus)) fol out.nomm :=
  ((folR_rgoodK (W := gen'.want) hT hwf n _ _ _ _ _ _ _ _ h (fun _ h => h)).annot).mono
    fun x hx => ⟨x, rp_top hx⟩

end AnnotSF
end SkaModel
end Formalization
