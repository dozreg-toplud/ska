import lemmas.Ska.CompGenClassS
import lemmas.Ska.CompGenClassL

/-!
# The cons and `[7 p q]` at entry-free goals (`NextGC0`), no premise

README Gaps 12.39, item 12 (g).  The texts of `closedS_cons_of` and
`closedS_n7` with the fronts vacuous: the halves of a cons at an entry-free
goal have no entry (`ConsGAt.labH`, `labT`), so the parts' `FrontsSG` and
no-re-pointing hold vacuously; `q` of `[7 p q]` runs at the goal itself, `p`
at `q`'s result in `NextGCS`.  `+mink` on a `Frag0` formula is its nomm's
pure value (`frag0_minkEq`, through `Annot.n6`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **`GenFrag6` is annotated** at every subject predicate, for any code. -/
theorem ck6_annot {lib : Lib} {code : Bell → Option Nomm} {f : Noun} {nm : Nomm} (h : GenFrag6 f nm) :
    ∀ P, Annot lib code P f nm := by
  induction h with
  | n0 _ => exact fun _ => Annot.n0
  | n1 k => exact fun _ => Annot.n1
  | n3 _ ih => exact fun P => Annot.n3 (ih P)
  | n4 _ ih => exact fun P => Annot.n4 (ih P)
  | n5 _ _ ihp ihq => exact fun P => Annot.n5 (ihp P) (ihq P)
  | cons hp _ ihp ihq =>
    intro P
    cases hp <;> exact Annot.cons (ihp P) (ihq P)
  | @n7 fb fc p q _ _ ihp ihq => exact fun P => Annot.n7 (ihp P) (ihq (Img lib P fb))
  | n6 hc _ _ iha ihb => exact fun P => Annot.n6 (ck2_annot hc P) (iha P) (ihb P)

/-- **`+mink` on a `GenFrag6` formula is its nomm's pure value.** -/
theorem genFrag6_minkEq {f : Noun} {nm : Nomm} (h : GenFrag6 f nm) (lib : Lib) (P : Noun → Prop) :
    MinkEq lib P f nm := fun s hs gul tm r =>
  mink_pure (codeOK_none lib) (genFrag6_pure h) (ck6_annot h P) hs gul tm r

theorem genFrag6_cell {f : Noun} {nm : Nomm} (h : GenFrag6 f nm) : ∃ a b, f = C a b := by
  cases h <;> exact ⟨_, _, rfl⟩

/-- **The cons at entry-free goals, no premise.** -/
theorem closed0_cons (lib : Lib) (N : Needs) (env : CallEnv) : Closed0Cons S Map lib N env := by
  intro fp fq p q hp hq Hp Hq P sup region g0 g1 L th nex G hL h
  have hpp := genFrag6_pure hp.to6
  have hqp := genFrag6_pure hq.to6
  obtain ⟨hed, tel, gS, g2, g3, nq, np, CA⟩ := consGAt_of_run env sup hpp hqp G h
  have eT : entries tel = [] := by
    cases e : entries tel with
    | nil => rfl
    | cons x xs =>
      have := CA.labT x (by rw [e]; exact List.mem_cons_self ..)
      rw [hL] at this; cases this
  have eH : entries hed = [] := by
    cases e : entries hed with
    | nil => rfl
    | cons x xs =>
      have := CA.labH x (by rw [e]; exact List.mem_cons_self ..)
      rw [hL] at this; cases this
  have Pq := premG_tel CA G
  obtain ⟨Qq, Rq, Gq, Resq⟩ := Hq P Pq eT CA.rq
  have Nq : ∀ a ∈ (entries tel).map Prod.fst, ¬ RepointG gS g2 a := by rw [eT]; simp
  have FSq : FrontsSG (Map := Map) Qq gS g2 tel nq := fun a ha => by rw [eT] at ha; simp at ha
  have Pp := premG_hed CA G Rq.toFrameG Gq
  obtain ⟨Qp, Rp, Gp, Resp⟩ := Hp P Pp eH CA.rp
  have Np : ∀ a ∈ (entries hed).map Prod.fst, ¬ RepointG g2 g3 a := by rw [eH]; simp
  have FSp : FrontsSG (Map := Map) Qp g2 g3 hed np := fun a ha => by rw [eH] at ha; simp at ha
  have d3 : g3.drop = false := Rp.drop.trans (Rq.drop.trans CA.dS)
  have CO := CA.copyOK d3 Resp.lu Resq.lu
  have HA := halvesApart_split CA G
  obtain ⟨RG, LD⟩ := resG_copy Rq.toFrameG Rp.toFrameG Pq Pp Resq Resp HA (CA.halfH G) (CA.halfT G) CA.reS d3
    CA.cp CA.hc CO
  have CP : CopyPreAt (Map := Map) (g3.emitted ⟨[], [], Termin.hop np.th⟩) ((g3.bo, np.laz) :: entries np.laz)
      ((g3.bo, nq.laz) :: entries nq.laz) :=
    cc_copyPreAt_re (emitted_re _ _).symm (copyPreG Rq.toFrameG Rp.toFrameG Pq Pp Resq Resp HA)
  obtain ⟨Fr, GU, NR⟩ := frameG_consG CA G Rq.toFrameG Gq Nq Rp.toFrameG Gp Np Resp.lu Resq.lu
    (CopyOKL.runAt CO) CP LD
  have X := consSemPre_of lib CA G Rq.toFrameG Gq Nq Resq Rp.toFrameG Gp Np Resp
  obtain ⟨sem, semB, nec⟩ := semCoreG_consG (genFrag6_cell hp.to6) (genFrag6_minkEq hp.to6 lib P)
    (genFrag6_minkEq hq.to6 lib P) Rq Rp X
  refine ⟨consWit Qp Qq, { toFrameG := Fr, nec := nec, front := ?_, sem := sem, semB := semB }, GU, RG⟩
  intro a ha
  rw [hL] at ha; simp at ha

/-- **`[7 p q]` at entry-free goals**: `q` in `NextGC0`, `p` in `NextGCS`
at `q`'s result. -/
theorem closed0_n7 (lib : Lib) (N : Needs) (env : CallEnv) : Closed0N7 S Map lib N env := by
  intro fb fc p q _ _ Hp Hq P sup region g0 g2 L th nex H hL h
  rw [runLC_n7] at h
  obtain ⟨nx, g1, h1, h2⟩ := bind_some h
  obtain ⟨Qq, Rq, guq, Resq⟩ := Hq (Img lib P fb) H hL h1
  simp only [NextL.goal] at h2
  have hta : nx.th.args = [] := by
    rcases Rq.ent with ⟨_, _, _, ha⟩ | e
    · exact ha
    · have e' : nx.th = th := e
      rw [e']; exact H.ta
  have Hp' : PremG (Map := Map) nx.laz nx.th g1 :=
    { goal := Rq.toFrameG.goalOut H.goal, nc := Rq.ncond, ec := Rq.econd, lu := Resq.lu, cl := Resq.cl,
      ecl := Resq.ecl, sa := Resq.sa, ta := hta, bo := Nat.le_trans H.bo Rq.bo, drop := Rq.drop.trans H.drop,
      up := guq.up H.up, clr := H.clr.growU guq, cb := Rq.cfr.below H.cb }
  obtain ⟨Qp, Rp, gup, nrp, Resp, FSp⟩ := Hp P Hp' h2
  have hre1 := Rq.re
  have hre2 := Rp.re
  have hbo1 := Rq.bo
  refine ⟨sevenWit Qp Qq, runOKGen_sevenGF Rq Rp gup nrp H.goal.sregs (fun e he => (H.goal.lab e he).2.1),
    guq.trans gup, ⟨Resp.lu, Resp.cl, Resp.ecl, Resp.sa, ?_⟩⟩
  intro e he r hr
  rcases Resp.eat e he r hr with ⟨e0, he0, hl0, hm0⟩ | hs | hf
  · rcases Resq.eat e0 he0 r hm0 with ⟨e1, he1, hl1, hm1⟩ | hs1 | hf1
    · exact Or.inl ⟨e1, he1, hl1.trans hl0, hm1⟩
    · exact Or.inr (Or.inl hs1)
    · exact Or.inr (Or.inr ⟨hf1.1, by omega⟩)
  · rcases Rq.regs r hs with hs1 | hf1
    · exact Or.inr (Or.inl hs1)
    · exact Or.inr (Or.inr ⟨hf1.1, by omega⟩)
  · exact Or.inr (Or.inr ⟨by omega, hf.2⟩)

/-- **The contract on `Frag0` at a cons or `[0 a]` root, with only the
`%6` closure as a premise.** -/
theorem contract_frag0_of6 (lib : Lib) (env : CallEnv) (N : Needs) (h6 : Closed0N6 S Map lib N env)
    {f : Noun} {nm : Nomm} (hf : Frag0 f nm) (hs : (∃ p q, nm = Nomm.cons p q) ∨ (∃ ax, 2 ≤ ax ∧ nm = Nomm.n0 ax))
    {c : Straight Map} (h : finishLUC (S := S) (Map := Map) env nm = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s f [s] c ∧ ContractBwd lib N s f [s] c :=
  contract_frag0_of lib env N (closed0_cons lib N env) (closed0_n7 lib N env) h6 hf hs h

end Comp
end SkaModel
end Formalization
