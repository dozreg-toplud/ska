import lemmas.Ska.CompGenClass

/-!
# The class `NextGC`: the leaves and `[7 p q]`

README Gaps 12.39, item 12.  `[0 a]` (`a ≥ 2`, `closedN0`) and `[1 k]`
(`closedN1`) are in the class at every `P`, and `[7 p q]` with both parts in
it is (`closedN7`: `q` at the goal, `p` at `q`'s result, `runOKGen_sevenGF`;
no goal entry re-pointed since `GrowU` keeps every old block's `fin` and an
old block hops up only below `bo`).  `nextGC_all`: the induction with these
three closures, the cons, `[3 p]`, `[4 p]` and `[5 p q]` as hypotheses.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The result of `+from` is in the class's result side**: the moved needs
read the registers of the original ones at the same label. -/
theorem ca_resG_fromL {axe : Nat} {L L' : Lazy S} {g : Gen Map} (hf : fromL axe L = some L')
    (lu : Raw.LabUniq L) (cl : Clean L.sure.ned) (ecl : ∀ e ∈ entries L, Clean e.2.sure.ned)
    (sa : SureApart L) : ResG (Map := Map) L g g L' := by
  have hs := fromL_sure hf
  have E := fromL_ent axe _ _ hf
  refine ⟨Raw.lu_fromL axe L L' hf lu, clean_fromSure hs cl, fun e he => ?_, fun e he r hr hs' => ?_,
    fun e he r hr => ?_⟩
  · obtain ⟨l, h1, h2⟩ := E.mem_right he
    exact clean_fromSure (fromL_sure h1) (ecl _ h2)
  · obtain ⟨e0, he0, -, hm, -⟩ := Raw.fromEnt_back E he
    exact sa e0 he0 r (hm r hr) (Raw.fromSure_nmem_back hs hs')
  · obtain ⟨e0, he0, h1, hm, -⟩ := Raw.fromEnt_back E he
    exact Or.inl ⟨e0, he0, h1, hm r hr⟩

/-- **`[0 a]` is in the class** (`a ≥ 2`), at every `P`. -/
theorem closedN0 (lib : Lib) (N : Needs) (env : CallEnv) : ClosedN0 S Map lib N env := by
  intro a ha P sup region g0 g1 L th nex H h
  rw [runLC_n0_next_from env sup ha] at h
  obtain ⟨L', hf, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have M0 : MinkEq lib P (slot a) (Nomm.n0 a) := fun s hs gul tm r =>
    mink_pure (codeOK_none lib) rfl ((CallTreeA.n0 a).annot P) hs gul tm r
  exact ⟨_, runOKGen_n0 (N := N) lib M0 hf H.goal H.nc H.ec id, GrowU.refl _, fun _ _ => not_repointG_refl,
    ca_resG_fromL hf H.lu H.cl H.ecl H.sa⟩

/-- **The result `ofSure s` is in the class's result side** when `s` is
clean. -/
theorem ca_resG_ofSure {L : Lazy S} {g0 g1 : Gen Map} {s : Sure S} (hc : Clean s.ned) :
    ResG (Map := Map) L g0 g1 (ofSure s) :=
  ⟨Raw.labUniq_ofSure s, hc, fun e he => by simp [entries_ofSure] at he,
    fun e he => by simp [entries_ofSure] at he, fun e he => by simp [entries_ofSure] at he⟩

/-- **`[1 k]` is in the class**, at every `P`. -/
theorem closedN1 (lib : Lib) (N : Needs) (env : CallEnv) : ClosedN1 S Map lib N env := by
  intro k P sup region g0 g1 L th nex H h
  have M1 : MinkEq lib P (quote k) (Nomm.n1 k) := fun s hs gul tm r =>
    mink_pure (codeOK_none lib) rfl ((CallTreeA.n1 k).annot P) hs gul tm r
  obtain ⟨hn, R, hgu, hnr⟩ := runOKGen_n1 (N := N) lib M1 H.goal H.nc H.ec H.drop H.up H.cb H.ta h id
  subst hn
  exact ⟨_, R, hgu, hnr, ca_resG_ofSure (by simp [Sure.bunt, Clean])⟩

/-- **`GrowU` re-points no goal entry**: the old block of a goal entry hops,
`GrowU` keeps its `fin`, and below `UpBelow` an old block hops up only below
`bo`, while a re-pointed one hops to a fresh label. -/
theorem ca_not_repoint {L : Lazy S} {th : Jmp} {g0 g2 : Gen Map} (G : GoalG (Map := Map) L th g0)
    (hu : UpBelow g0) (hg : GrowU g0 g2) : ∀ a ∈ (entries L).map Prod.fst, ¬ RepointG g0 g2 a := by
  intro a ha ⟨B, fin, F, o1, o2, F2, h0, h2, l1, _, _, _, _⟩
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
  obtain ⟨_, hlt, B', th', hb⟩ := G.lab e he
  obtain ⟨b', hb', _, hfin⟩ := hg.keep _ _ hlt hb
  rw [h2] at hb'
  cases hb'
  have : th' = ⟨[], o1⟩ := by
    simp only at hfin
    exact (Termin.hop.inj hfin).symm
  subst this
  have := hu e.1 o1 ⟨_, ⟨[], o1⟩, hb, rfl, rfl, by omega⟩
  omega

/-- **`[7 p q]` is in the class** when both parts are, at every `P`. -/
theorem closedN7 (lib : Lib) (N : Needs) (env : CallEnv) : ClosedN7 S Map lib N env := by
  intro fb fc p q _ _ Hp Hq P sup region g0 g2 L th nex H h
  rw [runLC_n7] at h
  obtain ⟨nx, g1, h1, h2⟩ := bind_some h
  obtain ⟨Qq, Rq, guq, nrq, Resq⟩ := Hq (Img lib P fb) H h1
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
  obtain ⟨Qp, Rp, gup, nrp, Resp⟩ := Hp P Hp' h2
  have hre1 := Rq.re
  have hre2 := Rp.re
  refine ⟨sevenWit Qp Qq, runOKGen_sevenGF Rq Rp gup nrp H.goal.sregs (fun e he => (H.goal.lab e he).2.1),
    guq.trans gup, ca_not_repoint H.goal H.up (guq.trans gup), ⟨Resp.lu, Resp.cl, Resp.ecl, Resp.sa, ?_⟩⟩
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

/-- **The one induction** with the leaves and `[7 p q]` proved: every nomm of
`GenFrag` is in the class at every `P`, given the closures of the cons,
`[3 p]`, `[4 p]` and `[5 p q]`. -/
theorem nextGC_all (lib : Lib) (N : Needs) (env : CallEnv) (h3 : ClosedN3 S Map lib N env)
    (h4 : ClosedN4 S Map lib N env) (h5 : ClosedN5 S Map lib N env) (hc : ClosedCons S Map lib N env)
    {f : Noun} {nm : Nomm} (hf : GenFrag f nm) : ∀ P, NextGC (S := S) (Map := Map) lib N env P f nm :=
  nextGC_all_of (closedN0 lib N env) (closedN1 lib N env) h3 h4 h5 hc (closedN7 lib N env) hf

end Comp
end SkaModel
end Formalization
