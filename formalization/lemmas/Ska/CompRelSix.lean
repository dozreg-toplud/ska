import lemmas.Ska.CompLeafRel

/-!
# The relaxed `sem` over `FragP` and `FragN`

README Gaps 12.2.  The relations `RunOKP` and `RunOKN` keep their strict
`sem`; the relaxed one (`SemPR`, `SemNR` of `CompLeafRel.lean`) is proved
beside them, by the same induction, from the relations of the parts and the
relaxed `sem` of the parts.  This is so because the leaf conversion
(`CompLeafKeep.lean`) and the footprints (`CompFootX.lean`) come after the
files that define and build the relations, so the relations' own proofs
cannot use them.

`OKPR`: what the induction proves for `%done` and `%pick`, `OKP` with
`LeafJ` (the goal's jumps pass no arguments) and `Clear` (no block at or
above `bo`) and `SemPR` as the conclusion.  `sixP_semR`: the case `%6`, the
`sem` part of `sixP_ok` with the relaxed hypothesis passed on: the test gets
it as it is, since the sure need of the result is the test's; the lazy
blocks of the branches get it because a register of the test's sure need
lies at or above `g2.re` (`Rc.regs`), above the branches' runs.
`runP_semR`: every run on `FragP`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

theorem LeafJ.mono {bo bo' : Nat} (h : bo ≤ bo') : ∀ {goal : CGoal S}, LeafJ bo goal → LeafJ bo' goal
  | CGoal.next _ _, ⟨a, b⟩ => ⟨a, Nat.lt_of_lt_of_le b h⟩
  | CGoal.pick _ _, ⟨⟨a, b⟩, c, d⟩ => ⟨⟨a, Nat.lt_of_lt_of_le b h⟩, c, Nat.lt_of_lt_of_le d h⟩
  | CGoal.done, _ => trivial

/-- **What the induction proves for `%done` and `%pick`**: the relaxed
`sem`. -/
abbrev OKPR (lib : Lib) (goal : CGoal S) (nm : Nomm) : Prop :=
  ∀ {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}, NotNext goal → GJ g0.bo goal → LeafJ g0.bo goal →
    sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 →
    runL nm (CGoal.toL goal) region g0 = some (nex, g1) → SemPR (Map := Map) lib nm goal g0 g1 nex

/-- **`[6 c a b]` for `%done` or `%pick` with the relaxed `sem`.** -/
theorem sixP_semR (lib : Lib) {goal : CGoal S} {c a b : Nomm} (hcp : c.pure = true)
    (okc : ∀ z o : Jmp, z.args = [] → o.args = [] → OKP (Map := Map) lib (CGoal.pick z o : CGoal S) c)
    (oka : OKP (Map := Map) lib goal a) (okb : OKP (Map := Map) lib goal b)
    (ihc : ∀ z o : Jmp, z.args = [] → o.args = [] → OKPR (Map := Map) lib (CGoal.pick z o : CGoal S) c)
    (iha : OKPR (Map := Map) lib goal a) (ihb : OKPR (Map := Map) lib goal b) :
    OKPR (Map := Map) lib goal (Nomm.n6 c a b) := by
  intro region g0 g4 nex hg hj hl hcount b0 d0 hu hcl h
  rw [runL_n6_body c a b hg] at h
  obtain ⟨x1, x0, xc, g1, g2, g3, h1, h2, _, _, h3, hrest⟩ := sixBody_apart hcp h
  simp only [sixCount] at hcount
  have Rb := okb hg hj (by omega) b0 d0 hu h1
  have Sb := ihb hg hj hl (by omega) b0 d0 hu hcl h1
  have c1 : Clear g1 := hcl.growU Rb.grow
  have u1 : UpBelow g1 := Rb.grow.up hu
  have d1 : g1.drop = false := Rb.ext.2.2.1.trans d0
  have b01 : g0.bo ≤ g1.bo := Rb.ext.2.1
  have b1 : 1 ≤ g1.bo := Nat.le_trans b0 b01
  have Ra := oka hg (hj.mono b01) (by omega) b1 d1 u1 h2
  have Sa := iha hg (hj.mono b01) (hl.mono b01) (by omega) b1 d1 u1 c1 h2
  have c2 : Clear g2 := c1.growU Ra.grow
  have u2 : UpBelow g2 := Ra.grow.up u1
  have d2 : g2.drop = false := Ra.ext.2.2.1.trans d1
  have b12 : g1.bo ≤ g2.bo := Ra.ext.2.1
  have GU : GrowU g2 (sixGenL g2 x0.th x1.th region) := (grow_sixGenL region (jumpsBelow_hop Ra.lo Ra.hi)
    (jumpsBelow_hop Rb.lo (by have := Rb.hi; omega))).toU u2
  have uG : UpBelow (sixGenL g2 x0.th x1.th region) := GU.up u2
  have hbig : lazyBig (mk (Sure.bunt : Sure S) [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))] []) = false := by
    apply lazyBig_entries
    rw [entries_six]; simp only [List.length_append, List.length_cons]
    have := Ra.size; have := Rb.size; simp only [lazyMax]; omega
  -- the test
  have dG : (sixGenL g2 x0.th x1.th region).drop = false := by simp [d2]
  have Rc := okc (jmp0 g2.bo) (jmp0 (g2.bo + 1)) rfl rfl trivial
    ⟨⟨by simp only [jmp0]; omega, by simp only [jmp0, sixGenL_bo]; omega⟩,
      by simp only [jmp0]; omega, by simp only [jmp0, sixGenL_bo]; omega⟩ (by omega)
    (by simp only [sixGenL_bo]; omega) dG uG h3
  have Sc := ihc (jmp0 g2.bo) (jmp0 (g2.bo + 1)) rfl rfl trivial
    ⟨⟨by simp only [jmp0]; omega, by simp only [jmp0, sixGenL_bo]; omega⟩,
      by simp only [jmp0]; omega, by simp only [jmp0, sixGenL_bo]; omega⟩
    ⟨⟨rfl, by simp only [jmp0, sixGenL_bo]; omega⟩, rfl, by simp only [jmp0, sixGenL_bo]; omega⟩ (by omega)
    (by simp only [sixGenL_bo]; omega) dG uG (c2.growU GU) h3
  have u3 : UpBelow g3 := Rc.grow.up uG
  have d3 : g3.drop = false := Rc.ext.2.2.1.trans dG
  have bG3 : g2.bo + 2 ≤ g3.bo := by have := Rc.ext.2.1; simpa using this
  have hap : ∀ e ∈ xc.laz.fork, e.1.1 ≠ g2.bo := fun e he => by
    have hm : e.1 ∈ entries xc.laz := by rw [entries_eq]; exact List.mem_append_right _ (fork_mem_entries he)
    have := (Rc.labs _ hm).1; simp only [sixGenL_bo] at this; omega
  have hcp := hrest hbig
  rw [copyL_six_apart xc x0.laz x1.laz g2.bo (g2.bo + 1) g3 hap] at hcp
  obtain ⟨⟨u, g4'⟩, hadd, e4⟩ := Option.map_eq_some_iff.mp hcp
  simp only [Prod.mk.injEq] at e4
  obtain ⟨rfl, rfl⟩ := e4
  obtain ⟨A4, r4, bo4, _⟩ := addOps_nil hadd
  simp only [emitted_re, emitted_bo] at r4 bo4
  -- the states
  have E2 : Ext g2 (sixGenL g2 x0.th x1.th region) := ext_sixGenL _ _ _ _
  have E4 : Ext g3 g4' := (ext_emit g3 _).trans (ext_addOps_nil hadd)
  have E24 : Ext g2 g4' := E2.trans (Rc.ext.trans E4)
  have E14 : Ext g1 g4' := Ra.ext.trans E24
  have E04 : Ext g0 g4' := Rb.ext.trans E14
  have re01 := Rb.ext.1
  have re12 := Ra.ext.1
  have re2G : g2.re ≤ g3.re := by have := Rc.ext.1; simpa using this
  have h4k : ∀ k, k ≠ g3.bo → HoonMap.get g4'.blocks k = HoonMap.get g3.blocks k := fun k hk =>
    (A4 k).trans (get_emitted_ne hk)
  have h4o : HoonMap.get g4'.blocks g3.bo = some ⟨[], [], Termin.hop xc.th⟩ :=
    (A4 g3.bo).trans (emitted_get g3 _ d3)
  have hG3 : ∀ k, k < g2.bo + 2 → HoonMap.get g3.blocks k =
      HoonMap.get (sixGenL g2 x0.th x1.th region).blocks k := fun k hk => Rc.ext.2.2.2 k (by simpa using hk)
  have h4y : HoonMap.get g4'.blocks g2.bo = some ⟨[], [], Termin.hop x0.th⟩ := by
    rw [h4k _ (by omega), hG3 _ (by omega)]; exact sixGenL_get_y _ _ _ d2
  have h4n : HoonMap.get g4'.blocks (g2.bo + 1) = some ⟨[], [], Termin.hop x1.th⟩ := by
    rw [h4k _ (by omega), hG3 _ (by omega)]; exact sixGenL_get_n _ _ _ d2
  have h42 : ∀ k, k < g2.bo → HoonMap.get g4'.blocks k = HoonMap.get g2.blocks k := E24.2.2.2
  have h41 : ∀ k, k < g1.bo → HoonMap.get g4'.blocks k = HoonMap.get g1.blocks k := E14.2.2.2
  -- the labels
  have lc : ∀ e ∈ entries xc.laz, g2.bo + 2 ≤ e.1 ∧ e.1 < g3.bo := fun e he => by
    have := Rc.labs e he; have := Rc.hi; simp only [sixGenL_bo] at *; omega
  have la : ∀ e ∈ entries x0.laz, g1.bo ≤ e.1 ∧ e.1 < g2.bo := fun e he =>
    ⟨(Ra.labs e he).1, Nat.lt_trans (Ra.labs e he).2.1 Ra.hi⟩
  have lb : ∀ e ∈ entries x1.laz, g0.bo ≤ e.1 ∧ e.1 < g1.bo := fun e he =>
    ⟨(Rb.labs e he).1, Nat.lt_trans (Rb.labs e he).2.1 Rb.hi⟩
  have lc' := labels_bound (P := fun o => g2.bo + 2 ≤ o ∧ o < g3.bo) lc
  have la' := labels_bound (P := fun o => g1.bo ≤ o ∧ o < g2.bo) la
  have lb' := labels_bound (P := fun o => g0.bo ≤ o ∧ o < g1.bo) lb
  have en := entries_copy_six xc.laz (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
    g2.bo (g2.bo + 1) x0.laz x1.laz
  have memE : ∀ e, e ∈ entries (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
      (xc.laz.fork ++ [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))]) xc.laz.bond) ↔
      e ∈ entries xc.laz ∨ e = (g2.bo, x0.laz) ∨ e ∈ entries x0.laz ∨ e = (g2.bo + 1, x1.laz) ∨
        e ∈ entries x1.laz := by
    intro e; rw [en]; simp only [List.mem_append, List.mem_cons]
    constructor
    · rintro (h | (h | h) | (h | h))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · rintro (h | h | h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl (Or.inl h))
      · exact Or.inr (Or.inl (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  have labAll : ∀ e ∈ entries (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
      (xc.laz.fork ++ [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))]) xc.laz.bond),
      (g2.bo + 2 ≤ e.1 ∧ e.1 < g3.bo ∧ e ∈ entries xc.laz) ∨ e.1 = g2.bo ∨
      (g1.bo ≤ e.1 ∧ e.1 < g2.bo ∧ e ∈ entries x0.laz) ∨ e.1 = g2.bo + 1 ∨
      (g0.bo ≤ e.1 ∧ e.1 < g1.bo ∧ e ∈ entries x1.laz) := by
    intro e he
    rcases (memE e).mp he with h | h | h | h | h
    · exact Or.inl ⟨(lc e h).1, (lc e h).2, h⟩
    · exact Or.inr (Or.inl (by rw [h]))
    · exact Or.inr (Or.inr (Or.inl ⟨(la e h).1, (la e h).2, h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [h]))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨(lb e h).1, (lb e h).2, h⟩)))
  have reC : ∀ r, g2.re ≤ r → r < g3.re → g0.re ≤ r ∧ r < g4'.re := fun r h1 h2 => ⟨by omega, by omega⟩
  have reB : ∀ r, g1.re ≤ r → r < g2.re → g0.re ≤ r ∧ r < g4'.re := fun r h1 h2 => ⟨by omega, by omega⟩
  have reA : ∀ r, g0.re ≤ r → r < g1.re → g0.re ≤ r ∧ r < g4'.re := fun r h1 h2 => ⟨h1, by omega⟩
  show SemPR lib (Nomm.n6 c a b) goal g0 g4' _
  · -- sem
    intro cc ned σ O st t gul s0 s ag hned regs hh hn
    have notLab : ∀ o, g0.bo ≤ o → o < g4'.bo → (g3.bo ≤ o ∨
        (g2.bo + 2 ≤ o ∧ o < g3.bo ∧ o ∉ (entries xc.laz).map Prod.fst) ∨
        (g1.bo ≤ o ∧ o < g2.bo ∧ o ∉ (entries x0.laz).map Prod.fst) ∨
        (o < g1.bo ∧ o ∉ (entries x1.laz).map Prod.fst)) →
        HoonMap.get cc.blocks o = HoonMap.get g4'.blocks o := by
      intro o h0 h1 hc'
      refine ag.1 o h0 h1 fun hm => ?_
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
      rcases labAll e he with ⟨x1', x2', x3'⟩ | x | ⟨x1', x2', x3'⟩ | x | ⟨x1', x2', x3'⟩
      · rcases hc' with y | ⟨_, _, y⟩ | y | y
        · omega
        · exact y (List.mem_map_of_mem x3')
        · omega
        · omega
      · rcases hc' with y | y | y | y <;> omega
      · rcases hc' with y | y | ⟨_, _, y⟩ | y
        · omega
        · omega
        · exact y (List.mem_map_of_mem x3')
        · omega
      · rcases hc' with y | y | y | y <;> omega
      · rcases hc' with y | y | y | ⟨_, y⟩
        · omega
        · omega
        · omega
        · exact y (List.mem_map_of_mem x3')
    have hc3 : HoonMap.get cc.blocks g3.bo = some ⟨[], [], Termin.hop xc.th⟩ :=
      (notLab g3.bo (by omega) (by omega) (Or.inl (Nat.le_refl _))).trans h4o
    have agC : AgreeP lib O cc gul st t ned (sixGenL g2 x0.th x1.th region) g3 xc.laz s0 s := by
      refine ⟨fun o h0 h1 hnl => ?_, fun e he => ?_⟩
      · simp only [sixGenL_bo] at h0
        rw [notLab o (by omega) (by omega) (Or.inr (Or.inl ⟨h0, h1, hnl⟩)), h4k o (by omega)]
      · obtain ⟨A, th, hg, hcb, hF⟩ := ag.2 e ((memE e).mpr (Or.inl he))
        exact ⟨A, th, (h4k _ (by have := lc e he; omega)).symm.trans hg, hcb, hF.mono (by omega)⟩
    have agA : AgreeP lib O cc gul st t ned g1 g2 x0.laz s0 s := by
      refine ⟨fun o h0 h1 hnl => ?_, fun e he => ?_⟩
      · rw [notLab o (by omega) (by omega) (Or.inr (Or.inr (Or.inl ⟨h0, h1, hnl⟩))), h42 o h1]
      · obtain ⟨A, th, hg, hcb, hF⟩ := ag.2 e ((memE e).mpr (Or.inr (Or.inr (Or.inl he))))
        exact ⟨A, th, (h42 _ (la e he).2).symm.trans hg, hcb, hF.mono (by omega)⟩
    have agB : AgreeP lib O cc gul st t ned g0 g1 x1.laz s0 s := by
      refine ⟨fun o h0 h1 hnl => ?_, fun e he => ?_⟩
      · rw [notLab o (by omega) (by omega) (Or.inr (Or.inr (Or.inr ⟨h1, hnl⟩))), h41 o h1]
      · obtain ⟨A, th, hg, hcb, hF⟩ := ag.2 e ((memE e).mpr (Or.inr (Or.inr (Or.inr (Or.inr he)))))
        exact ⟨A, th, (h41 _ (lb e he).2).symm.trans hg, hcb, hF.mono (by omega)⟩
    -- a lazy block
    have lazyBlk : ∀ (o : Nat) (x : NextL S) (nm' : Nomm) (gA gB : Gen Map),
        (o, x.laz) ∈ entries (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
          (xc.laz.fork ++ [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))]) xc.laz.bond) →
        HoonMap.get g4'.blocks o = some ⟨[], [], Termin.hop x.th⟩ → RunOKP (Map := Map) lib nm' goal gA gB x →
        SemPR (Map := Map) lib nm' goal gA gB x →
        AgreeP lib O cc gul st t ned gA gB x.laz s0 s → g0.re ≤ gA.re →
        (∀ r, NMem ned r → InR goal gA gB x.laz.sure.ned r) → (∀ y, NMem ned y → ¬ NMem x.laz.sure.ned y) →
        ∀ R2, HoldsN ned R2 s0 →
          GoalSem lib O cc gul st (fun r => r < g0.re ∨ NMem ned r) R2 t (jmp0 o) goal (pureEval nm' s) := by
      intro o x nm' gA gB hm hb R SR agX hlo hIn dj R2 hR2
      obtain ⟨A, th, hg, hcb, hF⟩ := ag.2 _ hm
      rw [hb] at hg
      simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at hg
      subst hg
      have e0 : goJ lib O cc gul st R2 t (jmp0 o) =
          execBlob lib O cc gul st R2 t ⟨[], A, Termin.hop x.th⟩ [] := goJ_jmp0 _ _ _ _ hcb
      by_cases f : FitsS x.laz.sure s
      · obtain ⟨R3, hh3, k3, e3⟩ := (fillSem_runK hF hR2 x.th).1 f
        have hn3 : HoldsN ned R3 s0 := HoldsN.agree ned (fun y hy => k3 y (Or.inl hy) (dj y hy)) hR2
        have S3 := SR cc ned σ O st t gul s0 s agX hIn R3 hh3 hn3
        refine goalSem_pre (fun r hr => ?_) (e0.trans e3) goal _
          (goalSem_mono (fun r hr => hr.elim (fun h => Or.inl (by omega)) Or.inr) goal _ S3)
        rcases hr with hr | hr
        · exact k3 r (Or.inr (by omega)) (fun h => by have := (R.regs r h).1; omega)
        · exact k3 r (Or.inl hr) (dj r hr)
      · rw [R.nec s f]
        exact goalSem_none goal (e0.trans ((fillSem_runK hF hR2 x.th).2 f))
    have hN : ∀ r, NMem ned r → g4'.re ≤ r ∨ (r < g0.re ∧ ¬ GMem goal r) ∨ NMem xc.laz.sure.ned r := hned
    have Hc := Sc cc ned σ O st t gul s0 s agC (fun r hr => by
        rcases hN r hr with e | ⟨e, _⟩ | e
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl ⟨by simp only [sixGenL_re]; omega, id⟩)
        · exact Or.inr (Or.inr e)) regs
      ⟨hh.1, (looks_uni_empty _ _).mp hh.2⟩ hn
    have e0 : goJ lib O cc gul st regs t (jmp0 g3.bo) = goJ lib O cc gul st regs t xc.th := by
      rw [goJ_jmp0 _ _ _ _ hc3, execBlob_hop]
    have kk : ∀ R2 : Map (Option Noun), (∀ r, (r < (sixGenL g2 x0.th x1.th region).re ∨ NMem ned r) →
        SkaModel.read r R2 = SkaModel.read r regs) →
        ∀ r, (r < g0.re ∨ NMem ned r) → SkaModel.read r R2 = SkaModel.read r regs :=
      fun R2 k2 r hr => k2 r (hr.elim (fun h => Or.inl (by simp only [sixGenL_re]; omega)) Or.inr)
    show GoalSem lib O cc gul st (fun r => r < g0.re ∨ NMem ned r) regs t (jmp0 g3.bo) goal
      (pureEval (Nomm.n6 c a b) s)
    rw [pureEval_n6]
    cases ec : pureEval c s with
    | none => rw [ec] at Hc; exact goalSem_none goal (e0.trans Hc)
    | some v =>
      rw [ec] at Hc
      rcases v with ⟨_ | _ | k⟩ | ⟨x, y⟩
      · obtain ⟨R2, k2, e2⟩ := Hc
        exact goalSem_pre (kk R2 k2) (e0.trans e2) goal _
          (lazyBlk g2.bo x0 a g1 g2 ((memE _).mpr (Or.inr (Or.inl rfl))) h4y Ra Sa agA (by omega)
            (fun r hr => by
              rcases hN r hr with e | ⟨e, e'⟩ | e
              · exact Or.inl (by omega)
              · exact Or.inr (Or.inl ⟨by omega, e'⟩)
              · have := (Rc.regs r e).1; simp only [sixGenL_re] at this; exact Or.inl this)
            (fun y hy hy' => by
              have := Ra.regs y hy'
              rcases hN y hy with e | ⟨e, _⟩ | e
              · omega
              · omega
              · have := (Rc.regs y e).1; simp only [sixGenL_re] at this; omega) R2
            (HoldsN.agree ned (fun x hx => k2 x (Or.inr hx)) hn))
      · obtain ⟨R2, k2, e2⟩ := Hc
        exact goalSem_pre (kk R2 k2) (e0.trans e2) goal _
          (lazyBlk (g2.bo + 1) x1 b g0 g1 ((memE _).mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) h4n Rb Sb agB
            (Nat.le_refl _)
            (fun r hr => by
              rcases hN r hr with e | e | e
              · exact Or.inl (by omega)
              · exact Or.inr (Or.inl e)
              · have := (Rc.regs r e).1; simp only [sixGenL_re] at this; exact Or.inl (by omega))
            (fun y hy hy' => by
              have := Rb.regs y hy'
              rcases hN y hy with e | ⟨e, _⟩ | e
              · omega
              · omega
              · have := (Rc.regs y e).1; simp only [sixGenL_re] at this; omega) R2 (HoldsN.agree ned (fun x hx => k2 x (Or.inr hx)) hn))
      · exact goalSem_none goal (e0.trans Hc)
      · exact goalSem_none goal (e0.trans Hc)

/-- **The relaxed `sem` on `FragP`** for `%done` and `%pick`, when the nomm
has at most 255 `%6`. -/
theorem runP_semR (lib : Lib) {goal : CGoal S} {nm : Nomm} (hf : FragP goal nm) : OKPR (Map := Map) lib goal nm := by
  induction hf with
  | frag hf =>
    intro region g0 g1 nex hg hj hl _ b0 d0 _ hc h
    exact runOKP_frag_semR lib hf hg hj hl b0 d0 hc h
  | @six goal c a b hc ha hb ihc iha ihb =>
    exact sixP_semR lib (fragP_pure (hc (jmp0 0) (jmp0 0))) (fun z o _ _ => runP_ok lib (hc z o))
      (runP_ok lib ha) (runP_ok lib hb) (fun z o _ _ => ihc z o) iha ihb

/-! ## Fork-free `%next` -/

/-- **What the induction proves for a fork-free `%next`**: the relaxed `sem`. -/
abbrev OKNR (lib : Lib) (nm : Nomm) : Prop :=
  ∀ {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    GJ g0.bo (CGoal.next sur th) → th.args = [] → GoalOK g0 (CGoal.next sur th) → Clean sur.ned →
    sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 →
    runL nm (CGoalL.next (ofSure sur) th) region g0 = some (nex, g1) → SemNR (Map := Map) lib nm sur th g0 g1 nex

/-- **A lazy block of `%6` under `%next`**: entering it does for the goal
`%next sur th` what its branch does, through the fork block `ob` and the
join `barg`. -/
theorem lazyBlkNR {lib : Lib} {σ : Type} {O : Oracle σ} {cc : Straight Map} {gul : Noun} {st : σ} {t : Trace}
    {ned : Need} {sur : Sure S} {th : Jmp} (hth : th.args = []) (dsur : Distinct sur.ned)
    {g0 g9 : Gen Map} (hsur : ∀ r, NMem sur.ned r → r < g0.re) (dsn : ∀ r, NMem ned r → ¬ NMem sur.ned r)
    {barg : Nat} (hbarg : HoonMap.get cc.blocks barg = some ⟨flattenNeed sur.ned, [], Termin.hop (jmp0 th.there)⟩)
    {o ob : Nat} {x : NextL S} {nm' : Nomm} {u : Sure S} {gA gB : Gen Map} {A : List Pole} {s0 s : Noun}
    (hcb : HoonMap.get cc.blocks o = some ⟨[], A, Termin.hop x.th⟩)
    (hF : FillSem lib O cc gul st t ned g9.re x.laz.sure A s0 s)
    (R : RunOKN (Map := Map) lib nm' u (jmp0 ob) gA gB x) (SR : SemNR (Map := Map) lib nm' u (jmp0 ob) gA gB x)
    (agX : AgreeP lib O cc gul st t ned gA gB x.laz s0 s) (hre : gB.re ≤ g9.re) (hlo : g0.re ≤ gA.re)
    (hIn : ∀ r, NMem ned r → InR (CGoal.next u (jmp0 ob)) gA gB x.laz.sure.ned r)
    (dj : ∀ y, NMem ned y → ¬ NMem x.laz.sure.ned y)
    (hl : u.lok = sur.lok) (hcp : NCopy sur.ned u.ned) (hu : ∀ r, NMem u.ned r → g0.re ≤ r ∧ r < gA.re)
    (hob : HoonMap.get cc.blocks ob = some ⟨[], [], Termin.hop ⟨(flattenNeed u.ned).map some, barg⟩⟩)
    (R2 : Map (Option Noun)) (hR2 : HoldsN ned R2 s0) :
    GoalSem lib O cc gul st (KeepI (CGoal.next sur th) g0 ned) R2 t (jmp0 o)
      (CGoal.next sur th) (pureEval nm' s) := by
  have e0 : goJ lib O cc gul st R2 t (jmp0 o) = execBlob lib O cc gul st R2 t ⟨[], A, Termin.hop x.th⟩ [] :=
    goJ_jmp0 _ _ _ _ hcb
  have fitsIff : ∀ p, FitsS u p ↔ FitsS sur p := fun p => by
    simp only [FitsS, hl, hcp.fits p]
  have ujs : ∀ y, NMem u.ned y → ¬ NMem sur.ned y := fun y h1 h2 => by
    have := (hu y h1).1; have := hsur y h2; omega
  have eAB := R.ext.1
  by_cases f : FitsS x.laz.sure s
  · obtain ⟨R3, hh3, k3, e3⟩ := (fillSem_runK hF hR2 x.th).1 f
    have hn3 : HoldsN ned R3 s0 := HoldsN.agree ned (fun y hy => k3 y (Or.inl hy) (dj y hy)) hR2
    have S3 := SR cc ned σ O st t gul s0 s agX hIn R3 hh3 hn3
    have keep3 : ∀ r, KeepI (CGoal.next sur th) g0 ned r → SkaModel.read r R3 = SkaModel.read r R2 := by
      intro r hr
      rcases hr with ⟨h, _⟩ | h
      · refine k3 r (Or.inr (by omega)) (fun hx => ?_)
        rcases R.regs r hx with e | e
        · have := (hu r e).1; omega
        · omega
      · exact k3 r (Or.inl h) (dj r h)
    cases ev : pureEval nm' s with
    | none =>
      rw [ev] at S3
      exact goalSem_none (CGoal.next sur th) ((e0.trans e3).trans S3)
    | some p =>
      rw [ev] at S3
      refine ⟨fun fp => ?_, fun fp => (e0.trans e3).trans (S3.2 fun fu => fp ((fitsIff p).mp fu))⟩
      obtain ⟨R4, hh4, k4, e4⟩ := S3.1 ((fitsIff p).mpr fp)
      obtain ⟨R5, hh5, k5, e5⟩ := goJ_fork (lib := lib) (O := O) (gul := gul) (st := st) hth hob hbarg hcp dsur
        ujs hh4 t
      refine ⟨R5, hh5, fun r hr => ?_, (e0.trans e3).trans (e4.trans e5)⟩
      have hs : ¬ NMem sur.ned r := by
        rcases hr with ⟨_, h⟩ | h
        · exact h
        · exact dsn r h
      rw [k5 r hs, k4 r ?_, keep3 r hr]
      rcases hr with ⟨h, _⟩ | h
      · exact Or.inl ⟨by omega, fun hu' => by have := (hu r hu').1; omega⟩
      · exact Or.inr h
  · have crash := e0.trans ((fillSem_runK hF hR2 x.th).2 f)
    rcases R.nec s f with ev | ⟨p, ev, nf⟩
    · rw [ev]; exact goalSem_none _ crash
    · rw [ev]
      exact ⟨fun fp => absurd ((fitsIff p).mpr fp) nf, fun _ => crash⟩

/-- **`%6` under a fork-free `%next` meets `RunOKN`**, from the relations of
its test and branches. -/
theorem sixNext_semR (lib : Lib) {c a b : Nomm} (hcp : c.pure = true)
    (okc : ∀ (z o : Jmp), z.args = [] → o.args = [] → ∀ {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
      GJ g0.bo (CGoal.pick z o : CGoal S) → sixCount c ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 →
      runL c (CGoal.toL (CGoal.pick z o : CGoal S)) region g0 = some (nex, g1) →
      RunOKP (Map := Map) lib c (CGoal.pick z o) g0 g1 nex)
    (oka : ∀ {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
      GJ g0.bo (CGoal.next sur th) → th.args = [] → GoalOK g0 (CGoal.next sur th) → Clean sur.ned →
      sixCount a ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 →
      runL a (CGoalL.next (ofSure sur) th) region g0 = some (nex, g1) → RunOKN (Map := Map) lib a sur th g0 g1 nex)
    (okb : ∀ {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
      GJ g0.bo (CGoal.next sur th) → th.args = [] → GoalOK g0 (CGoal.next sur th) → Clean sur.ned →
      sixCount b ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 →
      runL b (CGoalL.next (ofSure sur) th) region g0 = some (nex, g1) → RunOKN (Map := Map) lib b sur th g0 g1 nex)
    (ihc : ∀ z o : Jmp, z.args = [] → o.args = [] → OKPR (Map := Map) lib (CGoal.pick z o : CGoal S) c)
    (iha : OKNR (S := S) (Map := Map) lib a) (ihb : OKNR (S := S) (Map := Map) lib b)
    {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g9 : Gen Map} {nex : NextL S}
    (hj : GJ g0.bo (CGoal.next sur th)) (hth : th.args = []) (hok : GoalOK g0 (CGoal.next sur th))
    (hcl : Clean sur.ned) (hcount : sixCount (Nomm.n6 c a b) ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false)
    (hu : UpBelow g0) (hcl0 : Clear g0)
    (h : runL (Nomm.n6 c a b) (CGoalL.next (ofSure sur) th) region g0 = some (nex, g9)) :
    SemNR (Map := Map) lib (Nomm.n6 c a b) sur th g0 g9 nex := by
  rw [runL_n6_next, sixNextL_ofSure] at h
  obtain ⟨u0, u1, x1, x0, xc, lz, yes, nuh, gF, gR, gQ, gS, gC, hF, hR, hQ, hS, hC, hrest⟩ :=
    sixNextSimple_apart hcp h
  have hF' : forkSure sur th.there g0.bo (g0.bo + 1) { g0 with bo := g0.bo + 2 } = some ((u0, u1), gF) := hF
  obtain ⟨l0, l1, cp0, cp1, du0, du1, j01, r01, reF, boF, drF, cnF, idF, bk0, bk1, bk2, keepF⟩ :=
    forkSure_spec hF' d0
  simp only [sixCount] at hcount
  have dF : gF.drop = false := drF.trans d0
  have GF : GrowU g0 gF := growU_forkSure hF' d0 hj.1 hj.2 hu
  have uF : UpBelow { gF with id := gF.id + 1 } := GF.up hu
  -- the no branch
  have Rb := okb (sur := u1) (th := jmp0 (g0.bo + 1)) (region := gF.id :: region)
    (g0 := { gF with id := gF.id + 1 }) ⟨by simp [jmp0], by simp [jmp0]; omega⟩ rfl
    ⟨du1, fun r hr => (r01 r (Or.inr hr)).2⟩ (cp1.clean hcl) (by omega) (by simp; omega) dF uF hR
  have cF : Clear { gF with id := gF.id + 1 } := fun k hk => hcl0.growU GF k hk
  have Sb := ihb (sur := u1) (th := jmp0 (g0.bo + 1)) (region := gF.id :: region)
    (g0 := { gF with id := gF.id + 1 }) ⟨by simp [jmp0], by simp [jmp0]; omega⟩ rfl
    ⟨du1, fun r hr => (r01 r (Or.inr hr)).2⟩ (cp1.clean hcl) (by omega) (by simp; omega) dF uF cF hR
  have cR : Clear gR := cF.growU Rb.grow
  have dR : gR.drop = false := Rb.ext.2.2.1.trans dF
  have bFR : gF.bo ≤ gR.bo := Rb.ext.2.1
  have rFR : gF.re ≤ gR.re := Rb.ext.1
  have uR : UpBelow gR := Rb.grow.up uF
  -- the yes branch
  have Ra := oka (sur := u0) (th := jmp0 g0.bo) (region := gF.id :: region) (g0 := gR)
    ⟨by simp [jmp0]; omega, by simp [jmp0]; omega⟩ rfl
    ⟨du0, fun r hr => by have := (r01 r (Or.inl hr)).2; omega⟩ (cp0.clean hcl) (by omega) (by omega) dR uR hQ
  have Sa := iha (sur := u0) (th := jmp0 g0.bo) (region := gF.id :: region) (g0 := gR)
    ⟨by simp [jmp0]; omega, by simp [jmp0]; omega⟩ rfl
    ⟨du0, fun r hr => by have := (r01 r (Or.inl hr)).2; omega⟩ (cp0.clean hcl) (by omega) (by omega) dR uR cR hQ
  have cQ' : Clear gQ := cR.growU Ra.grow
  have dQ : gQ.drop = false := Ra.ext.2.2.1.trans dR
  have bRQ : gR.bo ≤ gQ.bo := Ra.ext.2.1
  have rRQ : gR.re ≤ gQ.re := Ra.ext.1
  -- `+sect`
  have cRc : gR.cond = gF.cond := Rb.cnd
  have cQ : gQ.cond = gF.cond := Ra.cnd.trans cRc
  rw [cRc] at hS
  obtain ⟨rfl, rfl, a0, a1, rfl, SB⟩ := sect_spec dQ cQ hS
  have dS : gS.drop = false := SB.2.2.2.1.trans (by simp [dQ])
  have boS : gS.bo = gQ.bo + 2 := SB.2.1.trans (sixGenL_bo _ _ _ _)
  have reS : gS.re = gQ.re := SB.1.trans (sixGenL_re _ _ _ _)
  have cS : gS.cond = gQ.cond := SB.2.2.2.2.2.1.trans (sixGenL_cond _ _ _ _)
  have blkS := SB.2.2.2.2.2.2
  have uQ : UpBelow gQ := Ra.grow.up uR
  have GQS : GrowU gQ gS := ((grow_sixGenL (gF.id :: region) (jumpsBelow_hop Ra.lo Ra.hi)
    (jumpsBelow_hop Rb.lo (by have := Rb.hi; omega))).toU uQ).trans
    (growU_same SB.2.1 SB.2.2.2.1 SB.2.2.2.2.2.2)
  have uS : UpBelow gS := GQS.up uQ
  -- the test
  have Rc := okc (jmp0 gQ.bo) (jmp0 (gQ.bo + 1)) rfl rfl (region := region)
    ⟨⟨by simp only [jmp0]; omega, by simp only [jmp0]; omega⟩, by simp only [jmp0]; omega,
      by simp only [jmp0]; omega⟩ (by omega) (by omega) dS uS hC
  have Sc := ihc (jmp0 gQ.bo) (jmp0 (gQ.bo + 1)) rfl rfl (region := region) trivial
    ⟨⟨by simp only [jmp0]; omega, by simp only [jmp0]; omega⟩, by simp only [jmp0]; omega,
      by simp only [jmp0]; omega⟩ ⟨⟨rfl, by simp only [jmp0]; omega⟩, rfl, by simp only [jmp0]; omega⟩
    (by omega) (by omega) dS uS (cQ'.growU GQS) hC
  have uC : UpBelow gC := Rc.grow.up uS
  have dC : gC.drop = false := Rc.ext.2.2.1.trans dS
  have bSC : gQ.bo + 2 ≤ gC.bo := by have := Rc.ext.2.1; omega
  have rSC : gQ.re ≤ gC.re := by have := Rc.ext.1; omega
  -- `+copy`
  have hbig : lazyBig (mk (Sure.bunt : Sure S) [((gQ.bo, x0.laz), (gQ.bo + 1, x1.laz))] []) = false := by
    apply lazyBig_entries
    rw [entries_six]; simp only [List.length_append, List.length_cons]
    have := Ra.size; have := Rb.size; simp only [lazyMax]; omega
  have hap : ∀ e ∈ xc.laz.fork, e.1.1 ≠ gQ.bo := fun e he => by
    have hm : e.1 ∈ entries xc.laz := by rw [entries_eq]; exact List.mem_append_right _ (fork_mem_entries he)
    have := (Rc.labs _ hm).1; omega
  have hcpy := hrest hbig
  rw [copyL_six_apart xc x0.laz x1.laz gQ.bo (gQ.bo + 1) gC hap] at hcpy
  obtain ⟨⟨u, g9'⟩, hadd, e9⟩ := Option.map_eq_some_iff.mp hcpy
  simp only [Prod.mk.injEq] at e9
  obtain ⟨rfl, rfl⟩ := e9
  obtain ⟨A9, r9, bo9, _⟩ := addOps_nil hadd
  simp only [emitted_re, emitted_bo] at r9 bo9
  -- the states
  have EF : Ext g0 gF := ⟨reF, by omega, drF, keepF⟩
  have EF' : Ext gF { gF with id := gF.id + 1 } := ⟨Nat.le_refl _, Nat.le_refl _, rfl, fun _ _ => rfl⟩
  have EQS : Ext gQ gS := ⟨by omega, by omega, dS.trans dQ.symm, fun o ho =>
    (blkS o).trans ((ext_sixGenL gQ x0.th x1.th (gF.id :: region)).2.2.2 o ho)⟩
  have E9 : Ext gC g9' := (ext_emit gC _).trans (ext_addOps_nil hadd)
  have EQ9 : Ext gQ g9' := EQS.trans (Rc.ext.trans E9)
  have ER9 : Ext gR g9' := Ra.ext.trans EQ9
  have EF9 : Ext gF g9' := EF'.trans (Rb.ext.trans ER9)
  have E09 : Ext g0 g9' := EF.trans EF9
  have h9k : ∀ k, k ≠ gC.bo → HoonMap.get g9'.blocks k = HoonMap.get gC.blocks k := fun k hk =>
    (A9 k).trans (get_emitted_ne hk)
  have h9o : HoonMap.get g9'.blocks gC.bo = some ⟨[], [], Termin.hop xc.th⟩ :=
    (A9 gC.bo).trans (emitted_get gC _ dC)
  have hGC : ∀ k, k < gQ.bo + 2 → HoonMap.get gC.blocks k =
      HoonMap.get (sixGenL gQ x0.th x1.th (gF.id :: region)).blocks k := fun k hk =>
    (Rc.ext.2.2.2 k (by omega)).trans (blkS k)
  have h9y : HoonMap.get g9'.blocks gQ.bo = some ⟨[], [], Termin.hop x0.th⟩ := by
    rw [h9k _ (by omega), hGC _ (by omega)]; exact sixGenL_get_y _ _ _ dQ
  have h9n : HoonMap.get g9'.blocks (gQ.bo + 1) = some ⟨[], [], Termin.hop x1.th⟩ := by
    rw [h9k _ (by omega), hGC _ (by omega)]; exact sixGenL_get_n _ _ _ dQ
  have h9Q : ∀ k, k < gQ.bo → HoonMap.get g9'.blocks k = HoonMap.get gQ.blocks k := EQ9.2.2.2
  have h9R : ∀ k, k < gR.bo → HoonMap.get g9'.blocks k = HoonMap.get gR.blocks k := ER9.2.2.2
  have h9F : ∀ k, k < gF.bo → HoonMap.get g9'.blocks k = HoonMap.get gF.blocks k := EF9.2.2.2
  -- the labels
  have lc : ∀ e ∈ entries xc.laz, gQ.bo + 2 ≤ e.1 ∧ e.1 < gC.bo := fun e he => by
    have := Rc.labs e he; have := Rc.hi; simp only [jmp0] at *; omega
  have la : ∀ e ∈ entries x0.laz, gR.bo ≤ e.1 ∧ e.1 < gQ.bo := fun e he =>
    ⟨(Ra.labs e he).1, Nat.lt_trans (Ra.labs e he).2.1 Ra.hi⟩
  have lb : ∀ e ∈ entries x1.laz, gF.bo ≤ e.1 ∧ e.1 < gR.bo := fun e he =>
    ⟨(Rb.labs e he).1, Nat.lt_trans (Rb.labs e he).2.1 Rb.hi⟩
  have lc' := labels_bound (P := fun o => gQ.bo + 2 ≤ o ∧ o < gC.bo) lc
  have la' := labels_bound (P := fun o => gR.bo ≤ o ∧ o < gQ.bo) la
  have lb' := labels_bound (P := fun o => gF.bo ≤ o ∧ o < gR.bo) lb
  have en := entries_copy_six xc.laz (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
    gQ.bo (gQ.bo + 1) x0.laz x1.laz
  have memE : ∀ e, e ∈ entries (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
      (xc.laz.fork ++ [((gQ.bo, x0.laz), (gQ.bo + 1, x1.laz))]) xc.laz.bond) ↔
      e ∈ entries xc.laz ∨ e = (gQ.bo, x0.laz) ∨ e ∈ entries x0.laz ∨ e = (gQ.bo + 1, x1.laz) ∨
        e ∈ entries x1.laz := by
    intro e; rw [en]; simp only [List.mem_append, List.mem_cons]
    constructor
    · rintro (h | (h | h) | (h | h))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · rintro (h | h | h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl (Or.inl h))
      · exact Or.inr (Or.inl (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  have labAll : ∀ e ∈ entries (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
      (xc.laz.fork ++ [((gQ.bo, x0.laz), (gQ.bo + 1, x1.laz))]) xc.laz.bond),
      (gQ.bo + 2 ≤ e.1 ∧ e.1 < gC.bo ∧ e ∈ entries xc.laz) ∨ e.1 = gQ.bo ∨
      (gR.bo ≤ e.1 ∧ e.1 < gQ.bo ∧ e ∈ entries x0.laz) ∨ e.1 = gQ.bo + 1 ∨
      (gF.bo ≤ e.1 ∧ e.1 < gR.bo ∧ e ∈ entries x1.laz) := by
    intro e he
    rcases (memE e).mp he with h | h | h | h | h
    · exact Or.inl ⟨(lc e h).1, (lc e h).2, h⟩
    · exact Or.inr (Or.inl (by rw [h]))
    · exact Or.inr (Or.inr (Or.inl ⟨(la e h).1, (la e h).2, h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [h]))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨(lb e h).1, (lb e h).2, h⟩)))
  have GE := growU_emit (b := ⟨[], [], Termin.hop xc.th⟩) (jumpsBelow_hop Rc.lo Rc.hi) uC
  have G09 : GrowU g0 g9' := GF.trans ((growU_same (g := gF) (g' := { gF with id := gF.id + 1 }) rfl rfl (fun _ => rfl)).trans (Rb.grow.trans
    (Ra.grow.trans (GQS.trans (Rc.grow.trans (GE.trans (growU_addOps hadd (GE.up uC))))))))
  show SemNR lib (Nomm.n6 c a b) sur th g0 g9' _
  · -- sem
    intro cc ned σ O st t gul s0 s ag hned regs hh hn
    have notLab : ∀ o, g0.bo ≤ o → o < g9'.bo → (gC.bo ≤ o ∨ o < gF.bo ∨
        (gQ.bo + 2 ≤ o ∧ o < gC.bo ∧ o ∉ (entries xc.laz).map Prod.fst) ∨
        (gR.bo ≤ o ∧ o < gQ.bo ∧ o ∉ (entries x0.laz).map Prod.fst) ∨
        (o < gR.bo ∧ o ∉ (entries x1.laz).map Prod.fst)) →
        HoonMap.get cc.blocks o = HoonMap.get g9'.blocks o := by
      intro o h0 h1 hc'
      refine ag.1 o h0 h1 fun hm => ?_
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
      rcases labAll e he with ⟨x1', x2', x3'⟩ | x | ⟨x1', x2', x3'⟩ | x | ⟨x1', x2', x3'⟩
      · rcases hc' with y | y | ⟨_, _, y⟩ | y | y
        · omega
        · omega
        · exact y (List.mem_map_of_mem x3')
        · omega
        · omega
      · rcases hc' with y | y | y | y | y <;> omega
      · rcases hc' with y | y | y | ⟨_, _, y⟩ | y
        · omega
        · omega
        · omega
        · exact y (List.mem_map_of_mem x3')
        · omega
      · rcases hc' with y | y | y | y | y <;> omega
      · rcases hc' with y | y | y | y | ⟨_, y⟩
        · omega
        · omega
        · omega
        · omega
        · exact y (List.mem_map_of_mem x3')
    have hc3 : HoonMap.get cc.blocks gC.bo = some ⟨[], [], Termin.hop xc.th⟩ :=
      (notLab gC.bo (by omega) (by omega) (Or.inl (Nat.le_refl _))).trans h9o
    have hcF : ∀ k, g0.bo ≤ k → k < gF.bo → HoonMap.get cc.blocks k = HoonMap.get gF.blocks k := fun k h0 h1 =>
      (notLab k h0 (by omega) (Or.inr (Or.inl h1))).trans (h9F k h1)
    have hob0 : HoonMap.get cc.blocks g0.bo =
        some ⟨[], [], Termin.hop ⟨(flattenNeed u0.ned).map some, g0.bo + 2⟩⟩ :=
      (hcF _ (Nat.le_refl _) (by omega)).trans bk0
    have hob1 : HoonMap.get cc.blocks (g0.bo + 1) =
        some ⟨[], [], Termin.hop ⟨(flattenNeed u1.ned).map some, g0.bo + 2⟩⟩ :=
      (hcF _ (by omega) (by omega)).trans bk1
    have hbarg : HoonMap.get cc.blocks (g0.bo + 2) = some ⟨flattenNeed sur.ned, [], Termin.hop (jmp0 th.there)⟩ :=
      (hcF _ (by omega) (by omega)).trans bk2
    have agC : AgreeP lib O cc gul st t ned gS gC xc.laz s0 s := by
      refine ⟨fun o h0 h1 hnl => ?_, fun e he => ?_⟩
      · rw [notLab o (by omega) (by omega) (Or.inr (Or.inr (Or.inl ⟨by omega, h1, hnl⟩))), h9k o (by omega)]
      · obtain ⟨A, th', hg, hcb, hF⟩ := ag.2 e ((memE e).mpr (Or.inl he))
        exact ⟨A, th', (h9k _ (by have := lc e he; omega)).symm.trans hg, hcb, hF.mono (by omega)⟩
    have agA : AgreeP lib O cc gul st t ned gR gQ x0.laz s0 s := by
      refine ⟨fun o h0 h1 hnl => ?_, fun e he => ?_⟩
      · rw [notLab o (by omega) (by omega) (Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, h1, hnl⟩)))), h9Q o h1]
      · obtain ⟨A, th', hg, hcb, hF⟩ := ag.2 e ((memE e).mpr (Or.inr (Or.inr (Or.inl he))))
        exact ⟨A, th', (h9Q _ (la e he).2).symm.trans hg, hcb, hF.mono (by omega)⟩
    have agB : AgreeP lib O cc gul st t ned { gF with id := gF.id + 1 } gR x1.laz s0 s := by
      refine ⟨fun o h0 h1 hnl => ?_, fun e he => ?_⟩
      · simp only at h0
        rw [notLab o (by omega) (by omega) (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, hnl⟩)))), h9R o h1]
      · obtain ⟨A, th', hg, hcb, hF⟩ := ag.2 e ((memE e).mpr (Or.inr (Or.inr (Or.inr (Or.inr he)))))
        exact ⟨A, th', (h9R _ (lb e he).2).symm.trans hg, hcb, hF.mono (by omega)⟩
    have hsur : ∀ r, NMem sur.ned r → r < g0.re := hok.2
    have hN : ∀ r, NMem ned r → g9'.re ≤ r ∨ (r < g0.re ∧ ¬ NMem sur.ned r) ∨ NMem xc.laz.sure.ned r := hned
    have dsn : ∀ r, NMem ned r → ¬ NMem sur.ned r := fun r hr hs => by
      have := hsur r hs
      rcases hN r hr with e | ⟨_, e⟩ | e
      · omega
      · exact e hs
      · have := (Rc.regs r e).1; omega
    have Hc := Sc cc ned σ O st t gul s0 s agC (fun r hr => by
        rcases hN r hr with e | ⟨e, _⟩ | e
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl ⟨by omega, id⟩)
        · exact Or.inr (Or.inr e)) regs
      ⟨hh.1, (looks_uni_empty _ _).mp hh.2⟩ hn
    have e0 : goJ lib O cc gul st regs t (jmp0 gC.bo) = goJ lib O cc gul st regs t xc.th := by
      rw [goJ_jmp0 _ _ _ _ hc3, execBlob_hop]
    have kk : ∀ R2 : Map (Option Noun), (∀ r, (r < gS.re ∨ NMem ned r) → SkaModel.read r R2 = SkaModel.read r regs) →
        ∀ r, KeepI (CGoal.next sur th) g0 ned r → SkaModel.read r R2 = SkaModel.read r regs :=
      fun R2 k2 r hr => k2 r (hr.elim (fun h => Or.inl (by have := h.1; omega)) Or.inr)
    show GoalSem lib O cc gul st (KeepI (CGoal.next sur th) g0 ned) regs t (jmp0 gC.bo)
      (CGoal.next sur th) (pureEval (Nomm.n6 c a b) s)
    rw [pureEval_n6]
    cases ec : pureEval c s with
    | none => rw [ec] at Hc; exact goalSem_none _ (e0.trans Hc)
    | some v =>
      rw [ec] at Hc
      rcases v with ⟨_ | _ | k⟩ | ⟨x, y⟩
      · obtain ⟨R2, k2, e2⟩ := Hc
        obtain ⟨A, th', hg, hcb, hFl⟩ := ag.2 _ ((memE _).mpr (Or.inr (Or.inl rfl)))
        rw [h9y] at hg; simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at hg
        subst hg
        exact goalSem_pre (kk R2 k2) (e0.trans e2) _ _
          (lazyBlkNR hth hok.1 hsur dsn hbarg hcb hFl Ra Sa agA (by omega) (by omega)
            (fun r hr => by
              rcases hN r hr with e | ⟨e, _⟩ | e
              · exact Or.inl (by omega)
              · exact Or.inr (Or.inl ⟨by omega, fun hu' => by have := (r01 r (Or.inl hu')).1; omega⟩)
              · exact Or.inl (by have := (Rc.regs r e).1; omega))
            (fun y hy hy' => by
              have hb := Ra.regs y hy'
              rcases hN y hy with e | ⟨e, _⟩ | e
              · rcases hb with hb | hb
                · have := (r01 y (Or.inl hb)).2; omega
                · omega
              · rcases hb with hb | hb
                · have := (r01 y (Or.inl hb)).1; omega
                · omega
              · have := (Rc.regs y e).1
                rcases hb with hb | hb
                · have := (r01 y (Or.inl hb)).2; omega
                · omega) l0 cp0
            (fun r hr => ⟨(r01 r (Or.inl hr)).1, by have := (r01 r (Or.inl hr)).2; omega⟩) hob0 R2
            (HoldsN.agree ned (fun x hx => k2 x (Or.inr hx)) hn))
      · obtain ⟨R2, k2, e2⟩ := Hc
        obtain ⟨A, th', hg, hcb, hFl⟩ := ag.2 _ ((memE _).mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
        rw [h9n] at hg; simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at hg
        subst hg
        exact goalSem_pre (kk R2 k2) (e0.trans e2) _ _
          (lazyBlkNR hth hok.1 hsur dsn hbarg hcb hFl Rb Sb agB (by omega) (by simp; omega)
            (fun r hr => by
              rcases hN r hr with e | ⟨e, _⟩ | e
              · exact Or.inl (by omega)
              · exact Or.inr (Or.inl ⟨by simp; omega, fun hu' => by have := (r01 r (Or.inr hu')).1; omega⟩)
              · exact Or.inl (by have := (Rc.regs r e).1; omega))
            (fun y hy hy' => by
              have hb := Rb.regs y hy'
              rcases hN y hy with e | ⟨e, _⟩ | e
              · rcases hb with hb | hb
                · have := (r01 y (Or.inr hb)).2; omega
                · simp only at hb; omega
              · rcases hb with hb | hb
                · have := (r01 y (Or.inr hb)).1; omega
                · simp only at hb; omega
              · have := (Rc.regs y e).1
                rcases hb with hb | hb
                · have := (r01 y (Or.inr hb)).2; omega
                · simp only at hb; omega) l1 cp1
            (fun r hr => ⟨(r01 r (Or.inr hr)).1, (r01 r (Or.inr hr)).2⟩) hob1 R2
            (HoldsN.agree ned (fun x hx => k2 x (Or.inr hx)) hn))
      · exact goalSem_none _ (e0.trans Hc)
      · exact goalSem_none _ (e0.trans Hc)


/-- **The relaxed `sem` on `FragN`** for a fork-free goal `%next` whose jump
has no arguments, when the nomm has at most 255 `%6`. -/
theorem runN_semR (lib : Lib) {nm : Nomm} (hf : FragN (S := S) nm) : OKNR (S := S) (Map := Map) lib nm := by
  induction hf with
  | frag hf =>
    intro sur th region g0 g1 nex hj hth hok hcl _ b0 d0 _ hc h
    exact runOKN_frag_semR lib (hf sur th) hj hth b0 d0 hc hok hcl h
  | @six c a b hc ha hb iha ihb =>
    intro sur th region g0 g1 nex hj hth hok hcl hcount b0 d0 hu hc0 h
    exact sixNext_semR lib (fragP_pure (hc (jmp0 0) (jmp0 0)))
      (fun z o _ _ => runP_ok lib (hc z o) trivial) (runN_ok lib ha) (runN_ok lib hb)
      (fun z o _ _ => runP_semR lib (hc z o)) iha ihb hj hth hok hcl hcount b0 d0 hu hc0 h

end Comp
end SkaModel
end Formalization
