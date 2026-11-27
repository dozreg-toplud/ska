import lemmas.Ska.FolLoopProd
import lemmas.Ska.WellFormedFacts

/-!
# `fol-loop` with answers that change during the run

The fixed-table model `folLoopF tab n` answers every direct call from one
table.  The Hoon's `resolve` reads the state at the time of the call, and the
same call can be answered differently within one run (a `done` entry `e1`
first, and after a callee analysed in between has added `e2` with the same
formula, `e2`, which `~(tap by ...)` can list first).  `FolR P n` is the
closure of one level of `fol-loop` (`folStep`) under answers in `P` at each
call and a recursion whose results are again in the closure: each level
takes its own table and its own recursion, so two calls with the same
arguments can have different results.  The `ghost` of `Gen` lets one
recursion function tell such calls apart; results are compared without it
(`Gen.erase`).

The soundness results of the fixed-table model hold of `FolR` with only the
answers in `P` sound: `folR_mono`, `folR_wf`, `folR_rgood`, `folR_rprod`.
They reuse the case lemmas of `WantMono.lean`, `WellFormedFacts.lean`,
`FolLoopRel.lean` and `FolLoopProd.lean`, which are generic in the
recursion; the rewritten cases `%8`, `%9` and `%bare`, whose lemmas look two
levels into `folLoopF`, are done again here by taking `FolR` apart.
`folLoopF_folR`: every run of the fixed-table model is in `FolR`.
-/

namespace Formalization
namespace SkaModel

open Nock

/-- The answers of a table are in `P`. -/
def TabIn (P : Sock → Noun → TabEntry → Prop) (tab : Tab) : Prop :=
  ∀ s f a, tab s f = some a → P s f a

/-- `gen` without its ghost. -/
def Gen.erase (g : Gen) : Gen := { g with ghost := 0 }

theorem Gen.erase_want {g g' : Gen} (h : g.erase = g'.erase) : g.want = g'.want := by
  have e := congrArg Gen.want h
  exact e

theorem wcov_erase {W : Cape} {g g' : Gen} (he : g.erase = g'.erase) (h : WCov W g') : WCov W g :=
  fun q hq => h q (by rw [← Gen.erase_want he]; exact hq)

/-- **The results of `fol-loop` with answers in `P`**, with `n` levels: one
level of `fol-loop` with a table whose answers are in `P`, over a recursion
whose every result is a result with `n - 1` levels; the `gen` it returns is
compared without the ghost. -/
def FolR (P : Sock → Noun → TabEntry → Prop) :
    Nat → Noun → Anno → Option Noun → Bool → Bool → Gen → FolOut → Gen → Prop
  | 0, _, _, _, _, _, _, _, _ => False
  | n + 1, fol, sub, mk, bc, df, gen, out, gen' =>
    ∃ (tab : Tab) (go : FolGo) (g' : Gen), TabIn P tab ∧
      (∀ fol sub mk bc df gen out gen', go fol sub mk bc df gen = some (out, gen') →
        FolR P n fol sub mk bc df gen out gen') ∧
      folStep tab go fol sub mk bc df gen = some (out, g') ∧ g'.erase = gen'.erase

/-- Every result of the recursion is in `FolR P n`. -/
def GoR (P : Sock → Noun → TabEntry → Prop) (n : Nat) (go : FolGo) : Prop :=
  ∀ fol sub mk bc df gen out gen', go fol sub mk bc df gen = some (out, gen') →
    FolR P n fol sub mk bc df gen out gen'

variable {P : Sock → Noun → TabEntry → Prop}

/-- **The fixed-table model is a special case.** -/
theorem folLoopF_folR {tab : Tab} (ht : TabIn P tab) :
    ∀ n, GoR P n (folLoopF tab n)
  | 0 => fun _ _ _ _ _ _ _ _ h => by cases h
  | n + 1 => fun _ _ _ _ _ _ _ _ h => ⟨tab, folLoopF tab n, _, ht, folLoopF_folR ht n, h, rfl⟩

theorem folR_slot1 {k : Nat} {sub : Anno} {mk : Option Noun} {bc df : Bool} {gen gen' : Gen}
    {out : FolOut} (h : FolR P k (slot 1) sub mk bc df gen out gen') :
    out = ⟨Nomm.n0 1, sub, false⟩ ∧ gen'.erase = gen.erase := by
  cases k with
  | zero => exact h.elim
  | succ k =>
    obtain ⟨tab, go, g', _, _, h, he⟩ := h
    simp only [folStep, shape_slot1, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨pr, hpr, rfl, rfl⟩ := h
    simp at hpr
    subst hpr
    exact ⟨rfl, he.symm⟩

theorem folR_quote {k : Nat} {g : Noun} {sub : Anno} {mk : Option Noun} {bc df : Bool}
    {gen gen' : Gen} {out : FolOut} (h : FolR P k (quote g) sub mk bc df gen out gen') :
    out = ⟨Nomm.n1 g, ⟨Sock.mk Cape.yes g, A 0⟩, true⟩ := by
  cases k with
  | zero => exact h.elim
  | succ k =>
    obtain ⟨tab, go, g', _, _, h, _⟩ := h
    simp only [folStep, shape_quote, Option.some.injEq, Prod.mk.injEq] at h
    exact h.1.symm

/-! ## `want` grows, products are well formed -/

theorem folR_mono : ∀ (n : Nat) {fol : Noun} {sub : Anno} {mk : Option Noun} {bc df : Bool}
    {gen gen' : Gen} {out : FolOut}, FolR P n fol sub mk bc df gen out gen' → WantLe gen gen'
  | 0, _, _, _, _, _, _, _, _, h => h.elim
  | n + 1, _, _, _, _, _, _, _, _, h => by
    obtain ⟨tab, go, g', _, hgo, h, he⟩ := h
    have hl := folStep_mono (tab := tab) (fun _ _ _ _ _ _ _ _ hg => folR_mono n (hgo _ _ _ _ _ _ _ _ hg))
      _ _ _ _ _ _ _ _ h
    intro p hp
    rw [← Gen.erase_want he]
    exact hl p hp

theorem goMono_of_goR {n : Nat} {go : FolGo} (h : GoR P n go) : GoMono go :=
  fun _ _ _ _ _ _ _ _ hg => folR_mono n (h _ _ _ _ _ _ _ _ hg)

theorem folR_wf (hP : ∀ tab, TabIn P tab → TabWF tab) :
    ∀ (n : Nat) {fol : Noun} {sub : Anno} {mk : Option Noun} {bc df : Bool} {gen gen' : Gen}
      {out : FolOut}, WellFormed sub.sock → FolR P n fol sub mk bc df gen out gen' →
      WellFormed out.prod.sock
  | 0, _, _, _, _, _, _, _, _, _, h => h.elim
  | n + 1, _, _, _, _, _, _, _, _, hs, h => by
    obtain ⟨tab, go, g', ht, hgo, h, _⟩ := h
    have IH : GoWF go go := fun _ _ _ _ _ _ _ _ hs' hg =>
      ⟨folR_wf hP n hs' (hgo _ _ _ _ _ _ _ _ hg), hg⟩
    exact (folStep_wf (hP tab ht) IH (fun _ _ _ _ _ _ _ _ _ hg => hg) _ _ _ _ _ _ _ _ hs h).1

/-! ## The rewritten cases, relative to the code requirement -/

section Rewritten

variable {lib : Lib} {code : Bell → Option Nomm} {bus : Sock} {W : Cape}
  {sub : Anno} {mk : Option Noun} {bc df : Bool} {gen gen' : Gen} {out : FolOut}

theorem rgood_op9R {m : Nat}
    (IH' : ∀ k, k < m → ∀ fol sub mk bc df gen out gen', FolR P k fol sub mk bc df gen out gen' →
      WCov W gen' → RGood lib code bus W fol sub out)
    {p : Nat} {a b : Noun}
    (h : FolR P m (n3 (A 7) (C a b) (n3 (A 2) (slot 1) (slot p))) sub mk bc df gen out gen')
    (hW : WCov W gen') : RGood lib code bus W (C (A 9) (C (A p) (C a b))) sub out := by
  cases m with
  | zero => exact h.elim
  | succ k =>
  obtain ⟨tab1, go1, g1, _, hgo1, h1, he1⟩ := h
  simp only [folStep, shape_op7_eq, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq] at h1
  obtain ⟨⟨o1, gA⟩, hA, ⟨o2, gB⟩, hB, rfl, rfl⟩ := h1
  have FB := hgo1 _ _ _ _ _ _ _ _ hB
  have hW' : WCov W gB := wcov_erase he1 hW
  have G2 := IH' k (by omega) _ _ _ _ _ _ _ _ FB hW'
  have G1 := IH' k (by omega) _ _ _ _ _ _ _ _ (hgo1 _ _ _ _ _ _ _ _ hA)
    (hW'.of_le (folR_mono k FB))
  refine RGood.of_plain (Annot.n9 G1.annot (G2.annot.mono (rsub_img G1.prod))) ?_ rfl rfl rfl
  intro X' x gul y hx hm
  obtain ⟨core, arm, m1, hsl, m2⟩ := mink_inv_n9 hm
  exact G2.prod X' core gul y (G1.prod X' x gul core hx m1)
    (mink_mk_n2 (mink_mk_n0 (slot?_one core)) (mink_mk_n0 hsl) m2)

theorem rgood_op8R {m : Nat}
    (IH' : ∀ k, k < m → ∀ fol sub mk bc df gen out gen', FolR P k fol sub mk bc df gen out gen' →
      WCov W gen' → RGood lib code bus W fol sub out)
    {a b q : Noun}
    (h : FolR P m (n3 (A 7) (C (C a b) (slot 1)) q) sub mk bc df gen out gen')
    (hW : WCov W gen') : RGood lib code bus W (C (A 8) (C (C a b) q)) sub out := by
  cases m with
  | zero => exact h.elim
  | succ k =>
  obtain ⟨tab1, go1, g1, _, hgo1, h1, he1⟩ := h
  simp only [folStep, shape_op7_eq, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq] at h1
  obtain ⟨⟨o1, gA⟩, hA, ⟨o2, gB⟩, hB, rfl, rfl⟩ := h1
  have FB := hgo1 _ _ _ _ _ _ _ _ hB
  have hW' : WCov W gB := wcov_erase he1 hW
  have G2 := IH' k (by omega) _ _ _ _ _ _ _ _ FB hW'
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
  have Gb := IH' j (by omega) _ _ _ _ _ _ _ _ (hgo2 _ _ _ _ _ _ _ _ hb)
    (wcov_erase hgz.symm (wcov_erase he2 W1))
  rw [consProd_unsafe rfl] at G2
  have hsub : ∀ X' x gul y, RP bus W sub X' x → Mink lib gul [] x (C a b) (Tone.zero y) →
      RP bus W ⟨So.knit ob.prod.sock sub.sock, Pi.cons ob.prod.src sub.src⟩ X' (C y x) := by
    intro X' x gul y hx hm
    have R := Gb.prod X' x gul y hx hm
    refine ⟨hx.req, provO_iff.mp (provO_knit ?_ ?_), statOK_knit R.stat hx.stat⟩
    · rw [slotO_some_cell_false]; exact provO_iff.mpr R.prov
    · rw [slotO_some_cell_true]; exact provO_iff.mpr hx.prov
  refine RGood.of_plain (Annot.n8 Gb.annot (G2.annot.mono ?_)) ?_ rfl rfl rfl
  · intro z ⟨x, y, gul, ⟨X', hx⟩, hm, hz⟩
    subst hz
    exact ⟨X', hsub X' x gul y hx hm⟩
  · intro X' x gul p hx hm
    obtain ⟨y, m1, m2⟩ := mink_inv_n8 hm
    exact G2.prod X' (C y x) gul p (hsub X' x gul y hx m1) m2

/-- The nomm of a `%bare` call. -/
theorem bare_nommR {m : Nat} {g : Noun}
    (h : FolR P m (n3 (A 2) (slot 1) (quote g)) sub mk true df gen out gen') :
    out.nomm = Nomm.n2 (Nomm.n0 1) (Nomm.n1 g) none := by
  cases m with
  | zero => exact h.elim
  | succ m =>
  obtain ⟨tab1, go1, g1, _, hgo1, h1, _⟩ := h
  simp only [folStep, shape_self_call, Option.bind_eq_some_iff] at h1
  obtain ⟨⟨s', g1'⟩, h1a, ⟨f', g2'⟩, h1b, h1c⟩ := h1
  obtain ⟨rfl, _⟩ := folR_slot1 (hgo1 _ _ _ _ _ _ _ _ h1a)
  have hf := folR_quote (hgo1 _ _ _ _ _ _ _ _ h1b)
  subst hf
  exact callStep_bare h1c

theorem rgood_bareR {m : Nat} {a b : Noun}
    (G' : RGood lib code bus W (n3 (A 2) (slot 1) (quote (C (A 11) (C (A Tag.bare) (C a b))))) sub out)
    (h : FolR P m (n3 (A 2) (slot 1) (quote (C (A 11) (C (A Tag.bare) (C a b))))) sub mk true df gen out gen') :
    RGood lib code bus W (C (A 11) (C (A Tag.bare) (C a b))) sub out := by
  refine G'.transfer (fun x gul p => mink_self_call.symm) ?_
  rw [bare_nommR h]
  exact Annot.bare (by simp [isBare])

end Rewritten

/-! ## Soundness relative to the code requirement -/

/-- **`folLoop_rgood` for answers that change during the run**: every
result in `FolR P` whose `want` `W` covers is `RGood`, given that every table
with answers in `P` satisfies `RTab`. -/
theorem folR_rgood {lib : Lib} {code : Bell → Option Nomm} {bus : Sock} {W : Cape}
    (hT : ∀ tab, TabIn P tab → RTab lib code tab) (hwf : WellFormed bus) :
    ∀ n fol sub mk bc df gen out gen', FolR P n fol sub mk bc df gen out gen' → WCov W gen' →
      RGood lib code bus W fol sub out := by
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
    ih m (by omega) _ _ _ _ _ _ _ _ (hgo _ _ _ _ _ _ _ _ hg) hw
  have hM : GoMono go := goMono_of_goR hgo
  have IH' : ∀ k, k < m + 1 → ∀ fol sub mk bc df gen out gen', FolR P k fol sub mk bc df gen out gen' →
      WCov W gen' → RGood lib code bus W fol sub out := fun k hk => ih k hk
  cases hs : shape fol with
  | cons a b q => exact rgood_cons IH hM hs h hW'
  | op0 p => exact rgood_op0 hs h
  | op1 p => exact rgood_op1 hs h
  | op2 a b q => exact rgood_op2 (hT tab ht) hwf IH hM hs h hW'
  | op3 a b => exact rgood_op3 IH hM hs h hW'
  | op4 a b => exact rgood_op4 IH hs h hW'
  | op5 a b q => exact rgood_op5 IH hM hs h hW'
  | op6 a b q r => exact rgood_op6 IH hM hs h hW'
  | op7 a b q => exact rgood_op7 IH hM hs h hW'
  | op8 a b q =>
    have hf := shape_eq hs (by simp)
    simp only [Shape.fol] at hf
    subst hf
    simp only [folStep, hs] at h
    exact rgood_op8R (fun k hk => IH' k (by omega)) (hgo _ _ _ _ _ _ _ _ h) hW'
  | op9 p a b =>
    have hf := shape_eq hs (by simp)
    simp only [Shape.fol] at hf
    subst hf
    simp only [folStep, hs] at h
    exact rgood_op9R (fun k hk => IH' k (by omega)) (hgo _ _ _ _ _ _ _ _ h) hW'
  | op10 ax don r1 r2 => exact rgood_op10 IH hM hs h hW'
  | op11s p a b =>
    by_cases hp : p = Tag.bare
    · subst hp
      have hf := shape_eq hs (by simp)
      simp only [Shape.fol] at hf
      subst hf
      simp only [folStep, hs, if_true] at h
      exact rgood_bareR (IH _ _ _ _ _ _ _ _ h hW') (hgo _ _ _ _ _ _ _ _ h)
    · exact rgood_op11s_plain IH hs hp h hW'
  | op11d tag h1 h2 f => exact rgood_op11d IH hM hs h hW'
  | op11c x y h1 h2 f => exact rgood_op11c IH hs h hW'
  | op12 a b q => exact rgood_op12 IH hM hs h hW'
  | other => exact rgood_other hs h

/-! ## The product half, with the fuel of `+mink` -/

section RewrittenProd

variable {lib : Lib} {bus : Sock} {W : Cape} {K : Nat}
  {sub : Anno} {mk : Option Noun} {bc df : Bool} {gen gen' : Gen} {out : FolOut}

theorem rprod_op9R {m : Nat}
    (IH' : ∀ k, k < m → ∀ fol sub mk bc df gen out gen', FolR P k fol sub mk bc df gen out gen' →
      WCov W gen' → RProd lib bus W K fol sub out)
    {p : Nat} {a b : Noun}
    (h : FolR P m (n3 (A 7) (C a b) (n3 (A 2) (slot 1) (slot p))) sub mk bc df gen out gen')
    (hW : WCov W gen') : RProd lib bus W K (C (A 9) (C (A p) (C a b))) sub out := by
  cases m with
  | zero => exact h.elim
  | succ k =>
  obtain ⟨tab1, go1, g1, _, hgo1, h1, he1⟩ := h
  simp only [folStep, shape_op7_eq, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq] at h1
  obtain ⟨⟨o1, gA⟩, hA, ⟨o2, gB⟩, hB, rfl, rfl⟩ := h1
  have FB := hgo1 _ _ _ _ _ _ _ _ hB
  have hW' : WCov W gB := wcov_erase he1 hW
  have G2 := IH' k (by omega) _ _ _ _ _ _ _ _ FB hW'
  have G1 := IH' k (by omega) _ _ _ _ _ _ _ _ (hgo1 _ _ _ _ _ _ _ _ hA)
    (hW'.of_le (folR_mono k FB))
  refine RProd.of_plain ?_ rfl
  intro X' x gul y hx hm
  obtain ⟨core, arm, m1, hsl, m2⟩ := minkF_inv_n9 hm
  exact G2.prod X' core gul y (G1.prod X' x gul core hx (minkF_up m1)) (minkF_mk_arm hsl m2)

theorem rprod_op8R {m : Nat}
    (IH' : ∀ k, k < m → ∀ fol sub mk bc df gen out gen', FolR P k fol sub mk bc df gen out gen' →
      WCov W gen' → RProd lib bus W K fol sub out)
    {a b q : Noun}
    (h : FolR P m (n3 (A 7) (C (C a b) (slot 1)) q) sub mk bc df gen out gen')
    (hW : WCov W gen') : RProd lib bus W K (C (A 8) (C (C a b) q)) sub out := by
  cases m with
  | zero => exact h.elim
  | succ k =>
  obtain ⟨tab1, go1, g1, _, hgo1, h1, he1⟩ := h
  simp only [folStep, shape_op7_eq, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq] at h1
  obtain ⟨⟨o1, gA⟩, hA, ⟨o2, gB⟩, hB, rfl, rfl⟩ := h1
  have FB := hgo1 _ _ _ _ _ _ _ _ hB
  have hW' : WCov W gB := wcov_erase he1 hW
  have G2 := IH' k (by omega) _ _ _ _ _ _ _ _ FB hW'
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
  have Gb := IH' j (by omega) _ _ _ _ _ _ _ _ (hgo2 _ _ _ _ _ _ _ _ hb)
    (wcov_erase hgz.symm (wcov_erase he2 W1))
  rw [consProd_unsafe rfl] at G2
  refine RProd.of_plain ?_ rfl
  intro X' x gul p hx hm
  obtain ⟨y, m1, m2⟩ := minkF_inv_n8 hm
  have R := Gb.prod X' x gul y hx (minkF_up m1)
  have hsub : RP bus W ⟨So.knit ob.prod.sock sub.sock, Pi.cons ob.prod.src sub.src⟩ X' (C y x) := by
    refine ⟨hx.req, provO_iff.mp (provO_knit ?_ ?_), statOK_knit R.stat hx.stat⟩
    · rw [slotO_some_cell_false]; exact provO_iff.mpr R.prov
    · rw [slotO_some_cell_true]; exact provO_iff.mpr hx.prov
  exact G2.prod X' (C y x) gul p hsub (minkF_up m2)

theorem rprod_bareR {m : Nat} {a b : Noun}
    (h : FolR P m (n3 (A 2) (slot 1) (quote (C (A 11) (C (A Tag.bare) (C a b))))) sub mk true df gen out gen') :
    RProd lib bus W K (C (A 11) (C (A Tag.bare) (C a b))) sub out := by
  cases m with
  | zero => exact h.elim
  | succ m =>
  obtain ⟨tab1, go1, g1, _, hgo1, h1, _⟩ := h
  simp only [folStep, shape_self_call, Option.bind_eq_some_iff] at h1
  obtain ⟨⟨s', g1'⟩, h1a, ⟨f', g2'⟩, h1b, h1c⟩ := h1
  obtain ⟨rfl, _⟩ := folR_slot1 (hgo1 _ _ _ _ _ _ _ _ h1a)
  have hf := folR_quote (hgo1 _ _ _ _ _ _ _ _ h1b)
  subst hf
  obtain ⟨hsaf, hd⟩ := callStep_bare_prod h1c
  rcases hd with hd | hd | hd
  · exact RProd.of_dunno hd hsaf
  · exact RProd.of_plain (fun X' z gul y hz _ => absurd hd hz.prov.nonvoid) hsaf
  · exact absurd hd (by simp)

end RewrittenProd

/-- **`folLoop_rprod` for answers that change during the run.** -/
theorem folR_rprod {lib : Lib} {bus : Sock} {W : Cape} {K : Nat}
    (hL : ∀ tab, TabIn P tab → RTabL tab) (hP : ∀ tab, TabIn P tab → RTabP lib tab K)
    (hwf : WellFormed bus) :
    ∀ n fol sub mk bc df gen out gen', FolR P n fol sub mk bc df gen out gen' → WCov W gen' →
      RProd lib bus W K fol sub out := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro fol sub mk bc df gen out gen' h hW
  cases n with
  | zero => exact h.elim
  | succ m =>
  obtain ⟨tab, go, g', ht, hgo, h, he⟩ := h
  have hW' : WCov W g' := wcov_erase he hW
  have IH : GoRProd lib bus W K go := fun _ _ _ _ _ _ _ _ hg hw =>
    ih m (by omega) _ _ _ _ _ _ _ _ (hgo _ _ _ _ _ _ _ _ hg) hw
  have hM : GoMono go := goMono_of_goR hgo
  have IH' : ∀ k, k < m + 1 → ∀ fol sub mk bc df gen out gen', FolR P k fol sub mk bc df gen out gen' →
      WCov W gen' → RProd lib bus W K fol sub out := fun k hk => ih k hk
  cases hs : shape fol with
  | cons a b q => exact rprod_cons IH hM hs h hW'
  | op0 p => exact rprod_op0 hs h
  | op1 p => exact rprod_op1 hs h
  | op2 a b q => exact rprod_op2 (hL tab ht) (hP tab ht) hwf IH hM hs h hW'
  | op3 a b => exact rprod_op3 hs h
  | op4 a b => exact rprod_op4 hs h
  | op5 a b q => exact rprod_op5 hs h
  | op6 a b q r => exact rprod_op6 IH hM hs h hW'
  | op7 a b q => exact rprod_op7 IH hM hs h hW'
  | op8 a b q =>
    have hf := shape_eq hs (by simp)
    simp only [Shape.fol] at hf
    subst hf
    simp only [folStep, hs] at h
    exact rprod_op8R (fun k hk => IH' k (by omega)) (hgo _ _ _ _ _ _ _ _ h) hW'
  | op9 p a b =>
    have hf := shape_eq hs (by simp)
    simp only [Shape.fol] at hf
    subst hf
    simp only [folStep, hs] at h
    exact rprod_op9R (fun k hk => IH' k (by omega)) (hgo _ _ _ _ _ _ _ _ h) hW'
  | op10 ax don r1 r2 => exact rprod_op10 IH hM hs h hW'
  | op11s p a b =>
    by_cases hp : p = Tag.bare
    · subst hp
      have hf := shape_eq hs (by simp)
      simp only [Shape.fol] at hf
      subst hf
      simp only [folStep, hs, if_true] at h
      exact rprod_bareR (hgo _ _ _ _ _ _ _ _ h)
    · exact rprod_op11s_plain IH hs hp h hW'
  | op11d tag h1 h2 f => exact rprod_op11d IH hM hs h hW'
  | op11c x y h1 h2 f => exact rprod_op11c IH hs h hW'
  | op12 a b q => exact rprod_op12 hs h
  | other => exact rprod_other hs h

/-! ## For a function -/

/-- `fol-loop` as `+run` starts it, with answers in `P`. -/
def FolTopR (P : Sock → Noun → TabEntry → Prop) (n : Nat) (bus : Sock) (fol : Noun) (out : FolOut)
    (gen' : Gen) : Prop :=
  FolR P n fol ⟨bus, A 1⟩ none false false Gen.init out gen'

theorem folTopR_wantSound {lib : Lib} {code : Bell → Option Nomm}
    (hT : ∀ tab, TabIn P tab → RTab lib code tab) {n : Nat} {bus : Sock} {fol : Noun} {out : FolOut}
    {gen' : Gen} (hwf : WellFormed bus) (h : FolTopR P n bus fol out gen') :
    Annot lib code (Fits (Ca.app gen'.want bus)) fol out.nomm :=
  ((folR_rgood (W := gen'.want) hT hwf n _ _ _ _ _ _ _ _ h (fun _ h => h)).annot).mono
    fun x hx => ⟨x, rp_top hx⟩

theorem folTopR_relProdN {lib : Lib} {K : Nat} (hL : ∀ tab, TabIn P tab → RTabL tab)
    (hP : ∀ tab, TabIn P tab → RTabP lib tab K)
    {n : Nat} {bus : Sock} {fol : Noun} {out : FolOut} {gen' : Gen}
    (hwf : WellFormed bus) (h : FolTopR P n bus fol out gen')
    {x : Noun} (hx : Fits (Ca.app gen'.want bus) x) {gul p : Noun}
    (hm : minkF lib gul (K + 1) [] x fol = some (Tone.zero p)) :
    ProvR x out.prod.sock out.prod.src p ∧ StatOK bus out.prod.sock out.prod.src := by
  have R := (folR_rprod (W := gen'.want) hL hP hwf n _ _ _ _ _ _ _ _ h (fun _ h => h)).prod
    x x gul p (rp_top hx) hm
  exact ⟨R.prov, R.stat⟩

theorem folTopR_wf (hP : ∀ tab, TabIn P tab → TabWF tab) {n : Nat} {bus : Sock} {fol : Noun}
    {out : FolOut} {gen' : Gen} (hb : WellFormed bus) (h : FolTopR P n bus fol out gen') :
    WellFormed out.prod.sock :=
  folR_wf hP n hb h

end SkaModel
end Formalization
