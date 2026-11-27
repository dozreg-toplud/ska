import lemmas.Glue.InlineAnnot
import lemmas.Ska.KnowSound

/-!
# `InvBS` (track F, README Gaps 27): what the analysis knows at a direct call

`InvBS` (`Glue/InlineAnnot.lean`) asks that the code table of EVERY `InvB`
state meet `CodeOKS`: at a direct call with no memo key whose formula part
passes `+safe-fol-fol`, the formula part returns on every subject.

FINDING (`invBS_false`): as stated, `InvBS` is false, for every `M` and
`lib`.  `InvB` carries `CodeOK` only, and `CodeOK` does not give `CodeOKS`
(`witCode_codeOK`, `witCode_not_codeOKS`: track G's argued witness of M19,
now in Lean), and the witness table is the table of an `InvB` state with an
empty memo and no variants (`witLong_invB`).  So `InvBS` can only hold of
the states the pokes reach, as a stronger invariant (`InvB` with `CodeOKS`
and the memo's entries with `AnnotS`) that the analysis and the bake keep.
`inlAnnot_of` and the fields of `CompRest` that quantify over `InvB` states
then need that invariant in place of `InvB`.

On the real compiler (`tools/hoon/annots.hoon`, 28 pokes, 38 bells): 33
direct calls, 31 with no memo key and a `+safe-fol-fol` formula part, every
one of the 31 a literal `[%1 f]` (the bake's `+know` folds the reads of the
formula, whose provenance the analysis put in `want`), none that can crash;
the witness's call is indirect (`info` is `~`).

What the analysis knows at a direct call (the `%2` case of `+run`,
`rgood_op2` in `FolLoopRel.lean`): the product sock of the formula part is
`&` with the formula (`f.prod.sock = Sock.mk Cape.yes (C fa fb)`), and
`want` covers that product's provenance (`distribute & src.prod.f`), so
`RGood.sff` of the formula part gives the return on every noun the run
reaches (`rgood_direct_ret`).

PROVED here:
* `annot_sff_returns`: a formula whose nomm passes `+safe-fol-fol` returns
  on every subject of `P` on which `P` determines it (`SffOn`), by the cases
  of `+safe-fol-fol`: `[%0 a]` needs the axis present in every subject of
  `P` (`AxisIn`), `%1` nothing, a cons both parts, a hint its body (the clue
  of a dynamic hint and the trap of `%mean` pass `+safe-nomm`, which needs
  nothing: `sffOn_of_safeNomm`); a crash `[%0 0]` is determined on no
  inhabited `P`;
* `sockHas_axisIn`: the sock test of `annots.hoon` (every step to the axis
  goes through a cell the sock knows is a cell) gives `AxisIn`;
* `rgood_direct_ret`: the analysis's fact at a direct call, from `RGood`;
* the finding: `witCode_codeOK`, `witCode_not_codeOKS`, `witLong_invB`,
  `invBS_false`.
-/

namespace Formalization
namespace SkaModel
namespace AnnotSF

open Nock Bake

/-! ## A `+safe-fol-fol` formula returns where its reads are present -/

/-- The axis `a` is present in every subject of `P`. -/
def AxisIn (P : Noun → Prop) (a : Nat) : Prop := ∀ x, P x → ∃ v, slot? a x = some v

/-- `P` determines the crash points of a `+safe-fol-fol` nomm: each `[%0 a]`
it reads, outside clues, has its axis in every subject. -/
def SffOn (P : Noun → Prop) : Nomm → Prop
  | Nomm.n0 a => AxisIn P a
  | Nomm.cons p q => SffOn P p ∧ SffOn P q
  | Nomm.n1 _ => True
  | Nomm.n11s _ q _ => SffOn P q
  | Nomm.n11d _ _ q _ => SffOn P q
  | Nomm.mean _ _ q _ _ => SffOn P q
  | Nomm.n2 _ _ _ => False
  | Nomm.n3 _ => False
  | Nomm.n4 _ => False
  | Nomm.n5 _ _ => False
  | Nomm.n6 _ _ _ => False
  | Nomm.n7 _ _ => False
  | Nomm.n10 _ _ _ => False
  | Nomm.n12 _ _ => False

theorem sffOn_of_safeNomm {P : Noun → Prop} : ∀ {q : Nomm}, safeNomm q = true → SffOn P q
  | Nomm.cons p q, h => by
    simp only [safeNomm, Bool.and_eq_true] at h
    exact ⟨sffOn_of_safeNomm h.1, sffOn_of_safeNomm h.2⟩
  | Nomm.n1 _, _ => trivial
  | Nomm.n11s _ q _, h => by
    simp only [safeNomm, Bool.and_eq_true] at h; exact sffOn_of_safeNomm (q := q) h.2
  | Nomm.n11d _ _ q _, h => by
    simp only [safeNomm, Bool.and_eq_true] at h; exact sffOn_of_safeNomm (q := q) h.2
  | Nomm.mean _ _ q _ _, h => by
    simp only [safeNomm, Bool.and_eq_true] at h; exact sffOn_of_safeNomm (q := q) h.2
  | Nomm.n0 _, h | Nomm.n2 _ _ _, h | Nomm.n3 _, h | Nomm.n4 _, h | Nomm.n5 _ _, h
  | Nomm.n6 _ _ _, h | Nomm.n7 _ _, h | Nomm.n10 _ _ _, h | Nomm.n12 _ _, h => by
    simp [safeNomm] at h

theorem safeFolFol_of_safeNomm : ∀ {q : Nomm}, safeNomm q = true → safeFolFol q = true
  | Nomm.cons p q, h => by
    simp only [safeNomm, Bool.and_eq_true] at h
    simp only [safeFolFol, safeFolFol_of_safeNomm h.1, safeFolFol_of_safeNomm h.2, Bool.and_self]
  | Nomm.n1 _, _ => rfl
  | Nomm.n11s _ q _, h => by
    simp only [safeNomm, Bool.and_eq_true] at h
    simp only [safeFolFol, h.1, safeFolFol_of_safeNomm (q := q) h.2, Bool.and_self]
  | Nomm.n11d _ _ q _, h => by
    simp only [safeNomm, Bool.and_eq_true] at h
    simp only [safeFolFol, h.1.1, h.1.2, safeFolFol_of_safeNomm (q := q) h.2, Bool.and_self]
  | Nomm.mean _ _ q _ _, h => by
    simp only [safeNomm, Bool.and_eq_true] at h
    simp only [safeFolFol, h.1, safeFolFol_of_safeNomm (q := q) h.2, Bool.and_self]
  | Nomm.n0 _, h | Nomm.n2 _ _ _, h | Nomm.n3 _, h | Nomm.n4 _, h | Nomm.n5 _ _, h
  | Nomm.n6 _ _ _, h | Nomm.n7 _ _, h | Nomm.n10 _ _ _, h | Nomm.n12 _ _, h => by
    simp [safeNomm] at h

/-- **A `+safe-fol-fol` formula returns on every subject that determines
it**, by the cases of `+safe-fol-fol` (and the forms `Annot` gives them:
a folded literal, a `%6` whose test is constant, a `%memo` hint, a hint
whose tag is a cell). -/
theorem annot_sff_returns {lib : Lib} {code : Bell → Option Nomm} {P : Noun → Prop} {f : Noun}
    {q : Nomm} (h : Annot lib code P f q) :
    safeFolFol q = true → SffOn P q → ∀ x gul, P x → ∃ g, Mink lib gul [] x f (Tone.zero g) := by
  induction h with
  | cons _ _ i1 i2 =>
    intro hs ho x gul hx
    simp only [safeFolFol, Bool.and_eq_true] at hs
    obtain ⟨g1, m1⟩ := i1 hs.1 ho.1 x gul hx
    obtain ⟨g2, m2⟩ := i2 hs.2 ho.2 x gul hx
    exact ⟨_, mink_mk_cons m1 m2⟩
  | n0 => intro _ ho x gul hx; obtain ⟨v, hv⟩ := ho x hx; exact ⟨v, mink_mk_n0 hv⟩
  | n1 => intro _ _ x gul _; exact ⟨_, mink_mk_n1 x _⟩
  | indirect => intro hs; simp [safeFolFol] at hs
  | direct => intro hs; simp [safeFolFol] at hs
  | inline => intro hs; simp [safeFolFol] at hs
  | n3 => intro hs; simp [safeFolFol] at hs
  | n4 => intro hs; simp [safeFolFol] at hs
  | n5 => intro hs; simp [safeFolFol] at hs
  | n6 => intro hs; simp [safeFolFol] at hs
  | n7 => intro hs; simp [safeFolFol] at hs
  | n8 => intro hs; simp [safeFolFol] at hs
  | n9 => intro hs; simp [safeFolFol] at hs
  | n10 => intro hs; simp [safeFolFol] at hs
  | n11s _ i =>
    intro hs ho x gul hx
    simp only [safeFolFol, Bool.and_eq_true] at hs
    obtain ⟨g, m⟩ := i hs.2 ho x gul hx
    exact ⟨g, mink_mk_n11s _ m⟩
  | n11d _ _ i1 i2 =>
    intro hs ho x gul hx
    simp only [safeFolFol, Bool.and_eq_true] at hs
    obtain ⟨c, mc⟩ := i1 (safeFolFol_of_safeNomm hs.1.2) (sffOn_of_safeNomm hs.1.2) x gul hx
    obtain ⟨g, mg⟩ := i2 hs.2 ho x gul hx
    exact ⟨g, mink_mk_n11d _ mc mg⟩
  | n11c _ _ i1 i2 =>
    intro hs ho x gul hx
    simp only [safeFolFol, Bool.and_eq_true] at hs
    obtain ⟨c, mc⟩ := i1 (safeFolFol_of_safeNomm hs.1.2) (sffOn_of_safeNomm hs.1.2) x gul hx
    obtain ⟨g, mg⟩ := i2 hs.2 ho x gul hx
    exact ⟨g, mink_ctag_iff.mpr (mink_mk_n11d _ mc mg)⟩
  | mean _ _ i1 i2 =>
    intro hs ho x gul hx
    simp only [safeFolFol, Bool.and_eq_true] at hs
    obtain ⟨c, mc⟩ := i1 (safeFolFol_of_safeNomm hs.1) (sffOn_of_safeNomm hs.1) x gul hx
    obtain ⟨g, mg⟩ := i2 hs.2 ho x gul hx
    exact ⟨g, mink_mk_n11d _ mc mg⟩
  | n12 => intro hs; simp [safeFolFol] at hs
  | bare => intro hs; simp [safeFolFol] at hs
  | memo hh _ i =>
    intro hs ho x gul hx
    obtain ⟨g, m⟩ := i hs ho x gul hx
    obtain ⟨c, mc⟩ := hh x gul hx
    exact ⟨g, mink_mk_n11d _ mc (mink_self_call.mp m)⟩
  | crash =>
    intro _ ho x _ hx
    obtain ⟨v, hv⟩ := ho x hx
    simp [slot?, axisPath, axisPathFuel] at hv
  | fold hf => intro _ _ x gul hx; exact ⟨_, hf x gul hx⟩
  | six0 hb _ i =>
    intro hs ho x gul hx
    obtain ⟨g, m⟩ := i hs ho x gul hx
    exact ⟨g, mink_mk_six0 (hb x gul hx) m⟩
  | six1 hb _ i =>
    intro hs ho x gul hx
    obtain ⟨g, m⟩ := i hs ho x gul hx
    exact ⟨g, mink_mk_six1 (hb x gul hx) m⟩
  | n8g => intro hs; simp [safeFolFol] at hs
  | n8l => intro hs; simp [safeFolFol] at hs
  | bareLit => intro hs; simp [safeFolFol] at hs

/-! ## The sock test of `annots.hoon` -/

/-- Every noun that fits `[c d]` has a node at the path: each step goes
through a cell the cape knows is a cell (a cell cape that is not `[| |]`),
or through known data. -/
def capeHas : Cape → Noun → List Bool → Bool
  | _, _, [] => true
  | Cape.yes, d, b :: rest => (slotAtPath d (b :: rest)).isSome
  | Cape.no, _, _ :: _ => false
  | Cape.cell h t, Noun.cell dh _, false :: rest => !(h.isNo && t.isNo) && capeHas h dh rest
  | Cape.cell h t, Noun.cell _ dt, true :: rest => !(h.isNo && t.isNo) && capeHas t dt rest
  | Cape.cell _ _, Noun.atom _, _ :: _ => false

/-- The test `node` of `annots.hoon`: axis `a` is in every noun of the sock. -/
def sockHas : Sock → Nat → Bool
  | Sock.void, _ => true
  | Sock.mk c d, a => match axisPath a with
    | none => false
    | some p => capeHas c d p

theorem capeHas_slot : ∀ (p : List Bool) (c : Cape) (d n : Noun), capeHas c d p = true →
    FitsCape c d n → ∃ v, slotAtPath n p = some v
  | [], _, _, n, _, _ => ⟨n, by simp [slotAtPath]⟩
  | b :: rest, Cape.yes, d, n, h, hf => by
    simp only [FitsCape] at hf
    subst hf
    simp only [capeHas, Option.isSome_iff_exists] at h
    exact h
  | _ :: _, Cape.no, _, _, h, _ => by simp [capeHas] at h
  | _ :: _, Cape.cell _ _, Noun.atom _, _, h, _ => by simp [capeHas] at h
  | false :: rest, Cape.cell h t, Noun.cell dh dt, n, hc, hf => by
    simp only [capeHas, Bool.and_eq_true, Bool.not_eq_true'] at hc
    simp only [FitsCape] at hf
    rcases hf with hf | ⟨dh', dt', nh, nt, e, rfl, f1, _⟩
    · rw [hc.1] at hf; cases hf
    · simp only [Noun.cell.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      obtain ⟨v, hv⟩ := capeHas_slot rest h _ nh hc.2 f1
      exact ⟨v, by simpa [slotAtPath] using hv⟩
  | true :: rest, Cape.cell h t, Noun.cell dh dt, n, hc, hf => by
    simp only [capeHas, Bool.and_eq_true, Bool.not_eq_true'] at hc
    simp only [FitsCape] at hf
    rcases hf with hf | ⟨dh', dt', nh, nt, e, rfl, _, f2⟩
    · rw [hc.1] at hf; cases hf
    · simp only [Noun.cell.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      obtain ⟨v, hv⟩ := capeHas_slot rest t _ nt hc.2 f2
      exact ⟨v, by simpa [slotAtPath] using hv⟩

theorem sockHas_axisIn {s : Sock} {a : Nat} (h : sockHas s a = true) : AxisIn (Fits s) a := by
  intro x hx
  cases s with
  | void => exact hx.elim
  | mk c d =>
    simp only [sockHas] at h
    split at h
    · cases h
    · rename_i p hp
      obtain ⟨v, hv⟩ := capeHas_slot p c d x h hx
      exact ⟨v, by simp [slot?, hp, hv]⟩

/-! ## What the analysis knows at a direct call -/

/-- **The analysis's fact at a direct call** (`rgood_op2`, the branch that
makes the call direct): the formula part `c` (result `out`, nomm `q`) has a
product sock `&` with the formula, and `W` covers its provenance (the
analysis put `distribute & src.prod.f` in `want`).  Then, if `q` passes
`+safe-fol-fol`, `c` returns on every noun the run reaches: the conjunct
`AnnotS.direct` adds to `Annot.direct`. -/
theorem rgood_direct_ret {lib : Lib} {code : Bell → Option Nomm} {bus : Sock} {W : Cape}
    {c : Noun} {sub : Anno} {out : FolOut} {fa fb : Noun} (Gf : RGood lib code bus W c sub out)
    (hfp : out.prod.sock = Sock.mk Cape.yes (C fa fb))
    (hWf : ∀ q, (distribute Cape.yes out.prod.src).Has q → W.Has q) :
    safeFolFol out.nomm = true → ∀ x gul, RSub bus W sub x → ∃ g, Mink lib gul [] x c (Tone.zero g) :=
  fun hq x gul hx => ⟨_, Gf.sff hq _ hfp hWf x gul hx⟩

/-! ## The finding: `CodeOK` does not give `CodeOKS` -/

/-- `[0 0 1 0]`, whose axis `7` is `[1 0]`. -/
def witW : Noun := C (A 0) (C (A 0) (C (A 1) (A 0)))

/-- `[6 [3 0 1] [1 0 0 1 0] [1 5]]`: `[0 0 1 0]` on a cell, `5` on an atom. -/
def witB : Noun := n4 (A 6) (n2 (A 3) (slot 1)) (quote witW) (quote (A 5))

/-- The callee: `[1 0]` on any subject. -/
def witC : Bell := ⟨Sock.mk Cape.no (A 0), quote (A 0)⟩

/-- The caller: `[7 witB [2 [0 1] [0 7]]]` on any subject. -/
def witBl : Bell := ⟨Sock.mk Cape.no (A 0), n3 (A 7) witB (n3 (A 2) (slot 1) (slot 7))⟩

/-- The caller's nomm, with the call of `[0 7]` direct. -/
def witNb : Nomm :=
  Nomm.n7 (Nomm.n6 (Nomm.n3 (Nomm.n0 1)) (Nomm.n1 witW) (Nomm.n1 (A 5)))
    (Nomm.n2 (Nomm.n0 1) (Nomm.n0 7) (some (witC, none)))

def witCode : Bell → Option Nomm := fun bl =>
  if bl = witBl then some witNb else if bl = witC then some (Nomm.n1 (A 0)) else none

theorem witC_ne : witC ≠ witBl := by
  intro h
  have := congrArg Bell.fol h
  simp [witC, witBl, quote, n3, C, A] at this

theorem witCode_c : witCode witC = some (Nomm.n1 (A 0)) := by
  simp [witCode, witC_ne]

theorem witCode_b : witCode witBl = some witNb := by simp [witCode]

theorem witB_img {lib : Lib} {y : Noun} (h : Img lib (Fits witBl.less) witB y) : y = witW ∨ y = A 5 := by
  obtain ⟨x, gul, _, hm⟩ := h
  rcases mink_inv_n6 hm with m | m
  · exact Or.inl (mink_inv_n1 m)
  · exact Or.inr (mink_inv_n1 m)

theorem witCode_codeOK (lib : Lib) : CodeOK lib witCode := by
  intro bl nb hb
  by_cases e1 : bl = witBl
  · subst e1
    rw [witCode_b] at hb
    cases hb
    refine Annot.n7 (Annot.n6 (Annot.n3 Annot.n0) Annot.n1 Annot.n1)
      (Annot.direct Annot.n0 Annot.n0 witCode_c (fun _ _ _ _ _ => trivial) ?_)
    intro y gul g hy hm
    have hs := mink_inv_n0 hm
    rcases witB_img hy with rfl | rfl
    · simp [witW, slot?, axisPath, axisPathFuel, slotAtPath, C, A] at hs
      subst hs; rfl
    · simp [slot?, axisPath, axisPathFuel, slotAtPath, A] at hs
  · by_cases e2 : bl = witC
    · subst e2
      rw [witCode_c] at hb
      cases hb
      exact Annot.n1
    · simp [witCode, e1, e2] at hb

/-- **`CodeOKS` fails on the witness**: the call of `[0 7]` passes
`+safe-fol-fol` with no memo key, and `[0 7]` crashes on `5`, a subject of
the call (from the subject `0`). -/
theorem witCode_not_codeOKS (lib : Lib) : ¬ Glue.CodeOKS lib witCode := by
  intro hS
  have hA := hS witBl witNb witCode_b
  generalize hF : witBl.fol = F at hA
  generalize hN : witNb = N at hA
  generalize hP : Fits witBl.less = P at hA
  cases hA with
  | n7 _ h2 =>
    simp only [witBl, n3, witB, Noun.cell.injEq] at hF
    obtain ⟨-, rfl, rfl⟩ := hF
    simp only [witNb, Nomm.n7.injEq] at hN
    obtain ⟨-, rfl⟩ := hN
    generalize hF2 : n3 (A 2) (slot 1) (slot 7) = F2 at h2
    generalize hN2 : Nomm.n2 (Nomm.n0 1) (Nomm.n0 7) (some (witC, none)) = N2 at h2
    cases h2 with
    | direct _ _ _ _ _ hret =>
      simp only [n3, Noun.cell.injEq] at hF2
      obtain ⟨-, rfl, rfl⟩ := hF2
      simp only [Nomm.n2.injEq, Option.some.injEq, Prod.mk.injEq] at hN2
      obtain ⟨rfl, rfl, -, rfl⟩ := hN2
      have hx : Img lib P witB (A 5) := by
        refine ⟨A 0, A 0, by rw [← hP]; trivial, ?_⟩
        exact mink_mk_six1 (by simpa [wut] using mink_mk_n3 (lib := lib) (gul := A 0) (mink_mk_n0 (x := A 0) (ax := 1) rfl)) (mink_mk_n1 _ _)
      obtain ⟨g, hg⟩ := hret rfl rfl (A 5) (A 0) hx
      have := mink_inv_n0 hg
      simp [slot?, axisPath, axisPathFuel, slotAtPath, A] at this
    | _ => first
      | (simp only [n3, n4, slot, quote, Noun.cell.injEq, Noun.atom.injEq] at hF2; omega)
      | (simp only [n3, n4, slot, quote, Noun.cell.injEq, Noun.atom.injEq] at hF2; simp_all)
      | (cases hN2)
      | simp_all
  | _ => first
    | (simp only [witBl, n3, n4, Noun.cell.injEq, Noun.atom.injEq] at hF; omega)
    | (cases hN)
    | simp_all [witBl, witNb, n3, n4]

/-! ## The witness is the table of an `InvB` state -/

section State
open Ana Bake PokeM

variable {M : Type → Type → Type} [Treap M]

/-- An `InvB` state with the witness table: no memo, no variants. -/
def witLong : LongB M :=
  ⟨Treap.empty,
   Treap.put (Treap.put Treap.empty witC ⟨Nomm.n1 (A 0), Treap.empty, Cape.no⟩) witBl
     ⟨witNb, Treap.empty, Cape.no⟩,
   Treap.empty⟩

theorem witLong_real : realOf (witLong (M := M)).code = witCode := by
  funext bl
  simp only [realOf, witLong, Treap.get_put, Treap.get_empty, witCode]
  by_cases e1 : bl = witBl
  · simp [e1]
  · by_cases e2 : bl = witC
    · simp [e2, witC_ne]
    · simp [e1, e2]

theorem witLong_invB (lib : Lib) : InvB lib (witLong (M := M)) where
  ghost := ⟨_, PokeInv.init lib⟩
  lessKeys := fun _ _ _ _ h _ => by simp [witLong, Treap.get_empty] at h
  codeOK := by rw [witLong_real]; exact witCode_codeOK lib
  vars := fun c v h => by simp [witLong, Treap.has, Treap.gut, Treap.get_empty] at h
  bellNorm := fun bl nb h => by
    rw [witLong_real] at h
    simp only [witCode] at h
    split at h
    · rename_i e; subst e; exact trivial
    · split at h
      · rename_i e; subst e; exact trivial
      · cases h
  varsSub := fun c v h => by simp [witLong, Treap.has, Treap.gut, Treap.get_empty] at h

/-- **`InvBS` is false as stated**: the witness state meets `InvB` and its
table does not meet `CodeOKS`. -/
theorem invBS_false (M : Type → Type → Type) [Treap M] (lib : Lib) : ¬ Glue.InvBS M lib := by
  intro h
  have := h (witLong (M := M)) (witLong_invB lib)
  rw [witLong_real] at this
  exact witCode_not_codeOKS lib this

/-- **The leaf, restated truthfully** (not proved): an invariant `I` of the
states the pokes reach (`Step`, for the real compiler a `skaPokeB` poke on
the hypotheses of `skaPokeB_sound`), inside `InvB`, true of the empty state,
kept by every step, and giving `CodeOKS`.  The first open case is `keep`:
the copy of the analysis's `Annot` proofs with `AnnotS` (README Gaps 27). -/
def InvBSR (M : Type → Type → Type) [Treap M] (lib : Lib) (Step : LongB M → LongB M → Prop) : Prop :=
  ∃ I : LongB M → Prop, (∀ L, I L → InvB lib L) ∧ I ⟨Treap.empty, Treap.empty, Treap.empty⟩ ∧
    (∀ L L', I L → Step L L' → I L') ∧ ∀ L, I L → Glue.CodeOKS lib (realOf L.code)

/-- `inlAnnot` on the states of the invariant, from `InlPill` and `InvBSR`. -/
theorem inlAnnot_of_inv {lib : Lib} {Map : Type → Type} [HoonMap Map] {J H : Type}
    {D : CompData M Map J H} (hP : Glue.InlPill lib D) {I : LongB M → Prop}
    (hI : ∀ L, I L → InvB lib L) (hS : ∀ L, I L → Glue.CodeOKS lib (realOf L.code)) :
    ∀ long jets hot b nm, I long → D.inl long jets hot b = some nm →
      Annot lib (realOf long.code) (Fits b.less) b.fol nm := by
  intro long jets hot b nm hL hinl
  obtain ⟨fuel, calls, hotf, single, h⟩ := hP long jets hot b nm (hI long hL) hinl
  exact Glue.inlinedM_annot (hS long hL) calls hotf single fuel b nm h

end State

end AnnotSF
end SkaModel
end Formalization
