import lemmas.Ska.CompCollapseRun

/-!
# `[3 p]` under a goal with entries: `AboveX` and the run

README Gaps 12.2, the collapse case for `%3`.  Under `%next laz th`, when the
goal's lazy need is not equivalent to `none`, the `%3` case of `run` runs
`+collapse-lazy-atom` (the same first half as the `%4` case, through
`collapsePre_spec` with `collPick th (some x) = pure x`), then `+forl r o`
(the block `barg` with the parameter `r` and a hop to `o`, and the blocks
`if0`, `if1` that put `0` or `1` in a fresh register and pass it to `barg`),
then a block `[%clq r' if0 if1]` with a fresh `r'`, and runs `p` for
`this r'`.  Checked against the raw blocks of a temporary copy of
`tools/hoon/proxy-dump.hoon` (2026-11-24, second session): for
`[7 [3 [0 3]] [0 1]]` the blocks are `0w2 [par ~[0v1]] hop 0w1`,
`0w3 imm 0 v2, hop [v2] 0w2`, `0w4 imm 1 v3, hop [v3] 0w2`,
`0w5 clq v4 0w3 0w4`; for `[7 [3 [0 3]] [6 [5 [0 1] [1 6]] [0 1] [1 5]]]`
`barg` is `0w9 [par ~[0v3]] hop 0w6` with `v3` the `rp` of the `%5` (the
register of `q`'s sure need), the walk puts `mov v3 v2` (unproxied) at the
lazy block `0w3` of the branch `[0 1]`, and the clq block is `0wc`.

`forl_above`: the blocks of `+forl` mention `r` and fresh registers only.
`aboveX_n3`: `[3 p]` meets `AboveX` when `p` does.  `aboveX_n01`: `[0 1]`
meets `AboveX` (no block).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- **The blocks of `+forl r o`** mention only `r` and the two registers it
allocates, so every register they mention satisfies `P` when `r` and every
register from the start's `re` on do. -/
theorem forl_above {r o : Nat} {P : Nat → Prop} {g g' : Gen Map} {x : Nat × Nat} (h : forl r o g = some (x, g'))
    (hd : g.drop = false) (hr : P r) (hm : ∀ y, g.re ≤ y → y < g.re + 2 → P y) :
    g'.re = g.re + 2 ∧ g'.bo = g.bo + 3 ∧ g'.drop = g.drop ∧ g'.cond = g.cond ∧
    (∀ o', o' < g.bo → HoonMap.get g'.blocks o' = HoonMap.get g.blocks o') ∧
    ∀ o' b, g.bo ≤ o' → o' < g'.bo → HoonMap.get g'.blocks o' = some b → BlobIn P b := by
  simp only [forl, bind_apply, re_apply, emit_apply, Option.bind_some, pure_apply, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨rfl, rfl, rfl, rfl, fun o' ho => ?_, fun o' b l u hb => ?_⟩
  · simp only [Gen.emitted, hd, Bool.false_eq_true, if_false, HoonMap.get_put]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · simp only [Gen.emitted, hd, Bool.false_eq_true, if_false, HoonMap.get_put] at hb u
    by_cases e2 : o' = g.bo + 1 + 1
    · rw [if_pos e2] at hb; cases hb
      refine ⟨fun x hx => absurd hx List.not_mem_nil, regsIn_one (fun x hx => ?_), jmpIn_one (hm _ (by omega) (by omega))⟩
      simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; rw [hx]; exact hm _ (by omega) (by omega)
    rw [if_neg e2] at hb
    by_cases e1 : o' = g.bo + 1
    · rw [if_pos e1] at hb; cases hb
      refine ⟨fun x hx => absurd hx List.not_mem_nil, regsIn_one (fun x hx => ?_), jmpIn_one (hm _ (by omega) (by omega))⟩
      simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; rw [hx]; exact hm _ (by omega) (by omega)
    rw [if_neg e1] at hb
    have e0 : o' = g.bo := by omega
    rw [if_pos e0] at hb; cases hb
    refine ⟨fun x hx => ?_, RegsIn.nil _, jmpIn_jmp0 _ _⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx; rw [hx]; exact hr

section Run
variable [HoonMapKeys Map]

/-- **`[0 1]` meets `AboveX`**: for a goal `%next` it emits no block. -/
theorem aboveX_n01 : AboveX S Map (Nomm.n0 1) := by
  intro a th region g g' nex h _ _ _ _ _ _ _ _ _ o b l u hb
  have e : (runL (Nomm.n0 1) (CGoalL.next (ofSure (lazyReg a : Sure S)) th) region : CM Map (NextL S)) =
      pure ⟨ofSure (lazyReg a : Sure S), th⟩ := by
    unfold runL; simp [simpleNextL]
  rw [e, pure_apply] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  omega

/-- **`[3 p]` meets `AboveX` when `p` does**: the collapse of the goal
`this a` emits no block (every atom fits `this a`) and returns a register `d`
with `a ≤ d`, `+forl d th.there` emits three blocks that mention `d` and two
fresh registers (`forl_above`), the `%clq` block mentions a fresh register,
and the blocks of `p` lie above that register. -/
theorem aboveX_n3 {lib : Lib} {p : Nomm} (hp : NextOK (S := S) (Map := Map) lib p) (ap : AboveX S Map p) :
    AboveX S Map (Nomm.n3 p) := by
  intro a th region g g' nex h ha ea h1 h2 d0 hu hcb hka hcount o b l u hb
  have e3 : (runL (Nomm.n3 p) (CGoalL.next (ofSure (lazyReg a)) th) region : CM Map (NextL S)) =
      if noneEquivalentL (ofSure (lazyReg a : Sure S)) then runL p (CGoalL.next (ofSure (lazyReg a)) th) region
      else (do
        let x ← collapseLazyAtomL ⟨ofSure (lazyReg a : Sure S), th⟩
        match x with
        | Option.none => fun _ => Option.none
        | some (r, o) => do
            let (z, o') ← forl r o
            let r' ← re
            let oc ← emit ⟨[], [], Termin.clq r' (jmp0 z) (jmp0 o')⟩
            runL p (CGoalL.next (ofSure (lazyReg r')) (jmp0 oc)) region) := by
    conv => lhs; unfold runL
    rfl
  have hne : noneEquivalentL (ofSure (lazyReg a : Sure S)) = false := by
    rw [noneEquivalentL_ofSure]; simp [noneEquivalent, lazyReg]
  rw [e3, hne] at h
  simp only [Bool.false_eq_true, if_false] at h
  obtain ⟨x, gA, hc2, h⟩ := bind_some h
  rcases x with _ | ⟨d, th'⟩
  · cases h
  have hm : collPick th (some (d, th')) gA = some ((d, th'), gA) := rfl
  have hne' : ∀ y, NMem (ofSure (lazyReg a) : Lazy S).sure.ned y → y = a := fun y hy => hy
  have P := collapsePre_spec hc2 hm d0 hcb (fun y hy => by rw [hne' y hy]; exact ha)
    (fun y hy => by rw [hne' y hy]; exact hka) (by simp [entries_ofSure]) (by simp [entries_ofSure])
    (by simp [entries_ofSure])
  obtain ⟨eth, ebo⟩ : th' = th.there ∧ gA.bo = g.bo := by
    rcases P.shape with ⟨e1, e2, -⟩ | ⟨-, -, hnf, -⟩
    · exact ⟨e1, e2⟩
    · exact absurd ⟨trivial, looks_empty _⟩ (hnf 0)
  have hda : a ≤ d := by
    rcases P.rreg with e | e
    · exact Nat.le_of_eq (hne' d e).symm
    · omega
  have Ple := P.le
  have dA : gA.drop = false := P.drop.trans d0
  simp only at h
  obtain ⟨⟨z, o'⟩, g3, h3, h⟩ := bind_some h
  obtain ⟨r3, b3, dr3, cn3, old3, F3⟩ := forl_above (P := (a ≤ ·)) h3 dA hda (fun y hy _ => by omega)
  have Fd := forl_down h3 (by rw [eth]; exact h1) (by rw [eth, ebo]; exact h2) (by omega)
  simp only [bind_apply, pure_apply, Option.bind_some, re_apply, emit_apply] at h
  obtain ⟨g4, hg4⟩ : ∃ g4 : Gen Map, g4 = { g3 with re := g3.re + 1 } := ⟨_, rfl⟩
  obtain ⟨blk, hblk⟩ : ∃ blk : Blob, blk = ⟨[], [], Termin.clq g3.re (jmp0 z) (jmp0 o')⟩ := ⟨_, rfl⟩
  obtain ⟨gE, hgE⟩ : ∃ gE : Gen Map, gE = g4.emitted blk := ⟨_, rfl⟩
  have hbo4 : g4.bo = g3.bo := by rw [hg4]
  have hre4 : g4.re = g3.re + 1 := by rw [hg4]
  have hcn4 : g4.cond = g3.cond := by rw [hg4]
  have hbl4 : g4.blocks = g3.blocks := by rw [hg4]
  have hdr4 : g4.drop = false := by rw [hg4]; exact dr3.trans dA
  rw [← hg4, ← hblk, ← hgE] at h
  have hboE : gE.bo = g3.bo + 1 := by rw [hgE, emitted_bo, hbo4]
  have hreE : gE.re = g3.re + 1 := by rw [hgE, emitted_re, hre4]
  have hcnE : gE.cond = gA.cond := by rw [hgE, ← cn3, ← hcn4]; rfl
  have hdE : gE.drop = false := by rw [hgE, emitted_drop]; exact hdr4
  have hbE : HoonMap.get gE.blocks g3.bo = some blk := by rw [hgE, ← hbo4]; exact emitted_get g4 blk hdr4
  have oE : ∀ o, o ≠ g3.bo → HoonMap.get gE.blocks o = HoonMap.get g3.blocks o := fun o ho => by
    rw [hgE, ← hbl4]; simp [Gen.emitted, hdr4, HoonMap.get_put, hbo4, ho]
  have G : Grow g gE := by
    have g34 : Grow g3 g4 := by rw [hg4]; exact grow_re g3
    have g4E : Grow g4 gE := by
      rw [hgE]; refine grow_emit ?_
      rw [hblk, hbo4]
      exact jumpsBelow_two rfl Fd.2.1 Fd.2.2
    exact P.grow.trans (Fd.1.trans (g34.trans g4E))
  have GU : GrowU g gE := G.toU hu
  have Rp := hp (sur := lazyReg g3.re) (th := jmp0 g3.bo) ⟨by simp only [jmp0]; omega, by simp only [jmp0]; omega⟩
    rfl (by exact ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; omega⟩) (by exact trivial)
    (by simpa only [sixCount] using hcount) (by omega) hdE (GU.up hu) h
  obtain ⟨Rre, Rbo, Rdr, Rold⟩ := Rp.ext
  have cb2 : CondBelow gA := P.pfor.1.below hcb
  have Ap := ap h (show g3.re < gE.re by omega) rfl (by simp only [jmp0]; omega) (by simp only [jmp0]; omega) hdE
    (GU.up hu) (fun x hx => by rw [hcnE] at hx; have := cb2 x hx; omega)
    (by
      rw [hcnE]
      cases e' : HoonMap.get gA.cond g3.re with
      | none => rfl
      | some _ => have := cb2 g3.re (by simp [e']); omega) (by simpa only [sixCount] using hcount)
  by_cases hlo : o < gE.bo
  · rw [Rold o (by omega)] at hb
    by_cases eo : o = g3.bo
    · rw [eo, hbE] at hb
      cases hb
      rw [hblk]
      exact blobIn_fin (f := Termin.clq g3.re (jmp0 z) (jmp0 o')) ⟨by omega, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩
    · rw [oE o eo] at hb
      exact F3 o b (by omega) (by omega) hb
  · exact (Ap o b (by omega) u hb).mono fun y hy => by omega

/-- **`[3 p]` for a goal `%next laz th` with entries, when the goal's lazy
need is not equivalent to `none`**, for every shape of the goal's sure need:
`CollRunU` with `d` the register `+collapse-lazy-atom` returns, which the
block `barg` of `+forl` writes through its parameter.  The proof is that of
`collRun_n4` with the three blocks of `+forl` (`forl_above`, `forl_ok`) and
the `%clq` block in place of the increment block: a cell product goes through
`if0` and leaves `0` in `d`, an atom through `if1` and leaves `1`. -/
theorem collRun_n3 (lib : Lib) {p : Nomm} (hp : NextOK (S := S) (Map := Map) lib p)
    (sp : OKNR (S := S) (Map := Map) lib p) (kp : KeepX S Map p) (ap : AboveX S Map p)
    {laz : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (h : runL (Nomm.n3 p) (CGoalL.next laz th) region g0 = some (nex, g1))
    (hne : noneEquivalentL laz = false)
    (hcount : sixCount p ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl0 : Clear g0)
    (h1 : 1 ≤ th.there) (h2 : th.there < g0.bo)
    (hnr : ∀ x, NMem laz.sure.ned x → x < g0.re)
    (hnc : ∀ x, NMem laz.sure.ned x → HoonMap.get g0.cond x = Option.none)
    (hcb : CondBelow g0) (hnd : (th.there :: (entries laz).map Prod.fst).Nodup)
    (hlab : ∀ e ∈ entries laz, e.1 < g0.bo ∧ ∃ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩)
    (hen : ∀ e ∈ entries laz, ∀ x, NMem e.2.sure.ned x → x < g0.re) :
    ∃ d, CollRunU lib (Nomm.n3 p) laz th d g0 g1 nex := by
  have e3 : (runL (Nomm.n3 p) (CGoalL.next laz th) region : CM Map (NextL S)) =
      if noneEquivalentL laz then runL p (CGoalL.next laz th) region
      else (do
        let x ← collapseLazyAtomL ⟨laz, th⟩
        match x with
        | Option.none => fun _ => Option.none
        | some (r, o) => do
            let (z, o') ← forl r o
            let r' ← re
            let oc ← emit ⟨[], [], Termin.clq r' (jmp0 z) (jmp0 o')⟩
            runL p (CGoalL.next (ofSure (lazyReg r')) (jmp0 oc)) region) := by
    conv => lhs; unfold runL
    rfl
  rw [e3, hne] at h
  simp only [Bool.false_eq_true, if_false] at h
  obtain ⟨a, gA, hc2, h⟩ := bind_some h
  rcases a with _ | ⟨d, th'⟩
  · cases h
  have hm : collPick th (some (d, th')) gA = some ((d, th'), gA) := rfl
  have P := collapsePre_spec hc2 hm d0 hcb hnr hnc hnd hlab hen
  refine ⟨d, ?_⟩
  simp only at h
  obtain ⟨⟨z, o'⟩, g3, h3, h⟩ := bind_some h
  have dA : gA.drop = false := P.drop.trans d0
  have Pbo := P.bo1
  have Ple := P.le
  have Plt := P.rlt
  have hth' : 1 ≤ th' ∧ th' < gA.bo := by
    rcases P.shape with ⟨e, eb, -⟩ | ⟨e, eb, -⟩ <;> (rw [e]; omega)
  obtain ⟨r3, b3, dr3, cn3, old3, F3⟩ := forl_above (P := fun x => x = d ∨ (gA.re ≤ x ∧ x < gA.re + 2)) h3 dA
    (Or.inl rfl) (fun y hy hy' => Or.inr ⟨hy, hy'⟩)
  have Fd := forl_down h3 hth'.1 hth'.2 (by omega)
  obtain ⟨E3, -, -, F⟩ := forl_ok h3 Plt
  have K3f := keeps_forl dA Plt h3
  simp only [bind_apply, pure_apply, Option.bind_some, re_apply, emit_apply] at h
  obtain ⟨g4, hg4⟩ : ∃ g4 : Gen Map, g4 = { g3 with re := g3.re + 1 } := ⟨_, rfl⟩
  obtain ⟨blk, hblk⟩ : ∃ blk : Blob, blk = ⟨[], [], Termin.clq g3.re (jmp0 z) (jmp0 o')⟩ := ⟨_, rfl⟩
  obtain ⟨gE, hgE⟩ : ∃ gE : Gen Map, gE = g4.emitted blk := ⟨_, rfl⟩
  have hbo4 : g4.bo = g3.bo := by rw [hg4]
  have hre4 : g4.re = g3.re + 1 := by rw [hg4]
  have hcn4 : g4.cond = g3.cond := by rw [hg4]
  have hbl4 : g4.blocks = g3.blocks := by rw [hg4]
  have hdr4 : g4.drop = false := by rw [hg4]; exact dr3.trans dA
  rw [← hg4, ← hblk, ← hgE] at h
  have hboE : gE.bo = g3.bo + 1 := by rw [hgE, emitted_bo, hbo4]
  have hreE : gE.re = g3.re + 1 := by rw [hgE, emitted_re, hre4]
  have hcnE : gE.cond = gA.cond := by rw [hgE, ← cn3, ← hcn4]; rfl
  have hdE : gE.drop = false := by rw [hgE, emitted_drop]; exact hdr4
  have hbE : HoonMap.get gE.blocks g3.bo = some blk := by rw [hgE, ← hbo4]; exact emitted_get g4 blk hdr4
  have oE : ∀ o, o ≠ g3.bo → HoonMap.get gE.blocks o = HoonMap.get g3.blocks o := fun o ho => by
    rw [hgE, ← hbl4]; simp [Gen.emitted, hdr4, HoonMap.get_put, hbo4, ho]
  have G : Grow g0 gE := by
    have g34 : Grow g3 g4 := by rw [hg4]; exact grow_re g3
    have g4E : Grow g4 gE := by
      rw [hgE]; refine grow_emit ?_
      rw [hblk, hbo4]
      exact jumpsBelow_two rfl Fd.2.1 Fd.2.2
    exact P.grow.trans (Fd.1.trans (g34.trans g4E))
  have GU : GrowU g0 gE := G.toU hu
  have Rp := hp (sur := lazyReg g3.re) (th := jmp0 g3.bo) ⟨by simp only [jmp0]; omega, by simp only [jmp0]; omega⟩
    rfl (by exact ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; omega⟩) (by exact trivial)
    hcount (by omega) hdE (GU.up hu) h
  have Sp := sp (sur := lazyReg g3.re) (th := jmp0 g3.bo) ⟨by simp only [jmp0]; omega, by simp only [jmp0]; omega⟩
    rfl (by exact ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; omega⟩) (by exact trivial)
    hcount (by omega) hdE (GU.up hu) (hcl0.growU GU) h
  have hbIn : BlobIn (· < g4.re) blk := by
    rw [hblk, hre4]
    exact blobIn_fin (f := Termin.clq g3.re (jmp0 z) (jmp0 o')) ⟨by omega, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩
  have Kp : KeepR g4 g1 nex (sixCount p) := keepX_tail (arg := g3.re) kp hdr4 hbIn
    (o := g3.bo) (by omega) hcount (by rw [emit_apply, hbo4, ← hgE]) h
  have cbA : CondBelow gA := P.pfor.1.below hcb
  have Ap := ap h (show g3.re < gE.re by omega) rfl (by simp only [jmp0]; omega) (by simp only [jmp0]; omega) hdE
    (GU.up hu) (fun x hx => by rw [hcnE] at hx; have := cbA x hx; omega)
    (by
      rw [hcnE]
      cases e' : HoonMap.get gA.cond g3.re with
      | none => rfl
      | some _ => have := cbA g3.re (by simp [e']); omega) hcount
  obtain ⟨Rre, Rbo, Rdr, Rold⟩ := Rp.ext
  have hcn1 : g1.cond = gA.cond := Rp.cnd.trans hcnE
  have nk1 : ∀ x, gA.re ≤ x → HoonMap.get g1.cond x = Option.none := fun x hx => by
    rw [hcn1]
    rcases P.pfor.1.2 x with e | ⟨_, l⟩
    · rw [e]
      cases e' : HoonMap.get g0.cond x with
      | none => rfl
      | some _ => have := hcb x (by simp [e']); omega
    · omega
  have hg1o : HoonMap.get g1.blocks g3.bo = some blk := (Rold _ (by omega)).trans hbE
  have g1F : ∀ o, gA.bo ≤ o → o < g3.bo → HoonMap.get g1.blocks o = HoonMap.get g3.blocks o := fun o _ ho =>
    (Rold o (by omega)).trans (oE o (by omega))
  have keep1 : ∀ o, o < g0.bo → HoonMap.get g1.blocks o = HoonMap.get gA.blocks o := fun o ho =>
    (Rold o (by omega)).trans ((oE o (by omega)).trans (old3 o (by omega)))
  have bel1 : BelowIn gE.bo g1 := Kp.keeps.bel gE.bo (fun o _ l u _ => absurd u (by omega))
  have semAll : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s0 s : Noun),
      AgreeU lib O c gul st t cf ned g0 g1 nex.laz s0 s →
      (∀ r, NMem ned r → InR (CGoal.next laz.sure th) g0 g1 nex.laz.sure.ned r) →
      ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
      GoalSem lib O c gul st (KeepI (CGoal.next laz.sure th) g0 ned) regs t nex.th (CGoal.next laz.sure th)
        (pureEval (Nomm.n3 p) s) ∧
      ((∀ v, FitsS laz.sure (A v)) → GoalSem lib O c gul st (KeepI (CGoal.next laz.sure th) g0 ned) regs t nex.th
        (CGoal.next (⟨Need.this d, HoonSet.empty⟩ : Sure S) th) (pureEval (Nomm.n3 p) s)) := by
    intro cf hcf c ned σ O st t gul s0 s ag hned regs hh hn
    have hu1 : ∀ x, x < g1.re → unproxy cf x = unproxy g1.cond x := unproxy_agree hcf
    have hu2 : ∀ x, gA.re ≤ x → unproxy g1.cond x = id x := fun x hx => unproxy_none (nk1 x hx)
    have hu3 : ∀ x, g3.re ≤ x → unproxy g1.cond x = id x := fun x hx => hu2 x (by omega)
    have pb : ∀ o b, gE.bo ≤ o → o < g1.bo → HoonMap.get g1.blocks o = some b → unproxyBlob cf b = b :=
      fun o b l u hb => by
        rw [unproxyBlob, renBlob_congr hu1 (bel1 o b l u hb), renBlob_congr hu3 (Ap o b l u hb), renBlob_id]
    have agP : AgreeP lib O c gul st t ned gE g1 nex.laz s0 s := by
      refine ⟨fun o l u hnl => ?_, fun e he => ?_⟩
      · rw [ag.1 o (by omega) u hnl]
        cases hg : HoonMap.get g1.blocks o with
        | none => rfl
        | some b => simp only [Option.map_some, pb o b l u hg]
      · obtain ⟨A, th'', hb1, hc1, hfs⟩ := ag.2 e he
        obtain ⟨l, lt, -⟩ := Rp.labs e he
        have hb := bel1 e.1 _ l (by have := Rp.hi; omega) hb1
        have ha := Ap e.1 _ l (by have := Rp.hi; omega) hb1
        refine ⟨A, th'', hb1, ?_, hfs⟩
        rw [hc1, renJmp_congr hu1 hb.2.2, renJmp_congr hu3 ha.2.2, renJmp_id]
    have inP : ∀ r, NMem ned r → InR (CGoal.next (lazyReg g3.re : Sure S) (jmp0 g3.bo)) gE g1 nex.laz.sure.ned r := by
      intro r hr
      show g1.re ≤ r ∨ (r < gE.re ∧ ¬ NMem (Need.this g3.re) r) ∨ NMem nex.laz.sure.ned r
      rcases hned r hr with e | ⟨e, _⟩ | e
      · exact Or.inl e
      · exact Or.inr (Or.inl ⟨by omega, fun hm => by simp only [NMem] at hm; omega⟩)
      · exact Or.inr (Or.inr e)
    have Hp := Sp c ned σ O st t gul s0 s agP inP regs hh hn
    have ud : unproxy cf d = d :=
      (hu1 d (by omega)).trans (unproxy_none (by rw [hcn1]; exact P.rkey))
    have ua : unproxy cf g3.re = g3.re := (hu1 _ (by omega)).trans (hu3 _ (Nat.le_refl _))
    have hnl : ∀ o, o < gE.bo → o ∉ (entries nex.laz).map Prod.fst := fun o lo hm => by
      obtain ⟨e, he, e1⟩ := List.mem_map.mp hm; have := (Rp.labs e he).1; omega
    have hco : HoonMap.get c.blocks g3.bo = some blk := by
      rw [ag.1 g3.bo (by omega) (by omega) (hnl _ (by omega)), hg1o]
      simp [unproxyBlob, renBlob, hblk, renPole, renFin, renJmp, jmp0, ua]
    have agF : Agree c gA g3 := fun o lo ho => by
      rw [ag.1 o (by omega) (by omega) (hnl o (by omega)), g1F o lo ho]
      cases hg : HoonMap.get g3.blocks o with
      | none => rfl
      | some b =>
        have hb := F3 o b lo ho hg
        simp only [Option.map_some, Option.some.injEq]
        rw [unproxyBlob]
        refine (renBlob_congr (P := fun x => x = d ∨ (gA.re ≤ x ∧ x < gA.re + 2)) (v := id) (fun x hx => ?_) hb).trans (renBlob_id b)
        rcases hx with rfl | hx
        · exact ud
        · exact (hu1 x (by omega)).trans (hu2 x hx.1)
    have F' := F dA c agF lib σ O st
    have nd : ∀ r, KeepI (CGoal.next laz.sure th) g0 ned r → r ≠ d ∧ r ≠ gA.re ∧ r ≠ gA.re + 1 ∧
        KeepI (CGoal.next (lazyReg g3.re : Sure S) (jmp0 g3.bo)) gE ned r := by
      intro r hr
      rcases hr with ⟨h1', h2'⟩ | h1'
      · refine ⟨fun e => ?_, by omega, by omega, Or.inl ⟨by omega, ?_⟩⟩
        · rcases P.rreg with hm' | hm'
          · exact h2' (by rw [e]; exact hm')
          · omega
        · show ¬ NMem (Need.this g3.re) r
          simp only [NMem]; omega
      · have hx : r ≠ d ∧ r ≠ gA.re ∧ r ≠ gA.re + 1 := by
          rcases hned r h1' with e2 | ⟨e1, e2⟩ | e2
          · omega
          · refine ⟨fun e => ?_, by omega, by omega⟩
            rcases P.rreg with hm' | hm'
            · exact e2 (by rw [e]; exact hm')
            · omega
          · rcases Rp.regs r e2 with e' | e'
            · simp only [lazyReg, NMem] at e'; omega
            · omega
        exact ⟨hx.1, hx.2.1, hx.2.2, Or.inr h1'⟩
    -- the end of the code for a product `x` of `p`, which leaves `w` in `d`
    have fin : ∀ (R : Map (Option Noun)) (w k : Nat), (k = gA.re ∨ k = gA.re + 1) →
        (∀ r, KeepI (CGoal.next (lazyReg g3.re : Sure S) (jmp0 g3.bo)) gE ned r →
          SkaModel.read r R = SkaModel.read r regs) →
        goJ lib O c gul st regs t nex.th = goJ lib O c gul st (store d (A w) (store k (A w) R)) t (jmp0 th') →
        GoalSem lib O c gul st (KeepI (CGoal.next laz.sure th) g0 ned) regs t nex.th (CGoal.next laz.sure th)
          (some (A w)) ∧
        ((∀ v, FitsS laz.sure (A v)) → GoalSem lib O c gul st (KeepI (CGoal.next laz.sure th) g0 ned) regs t nex.th
          (CGoal.next (⟨Need.this d, HoonSet.empty⟩ : Sure S) th) (some (A w))) := by
      intro R w k hk kR hj
      have kk : ∀ r, KeepI (CGoal.next laz.sure th) g0 ned r →
          SkaModel.read r (store d (A w) (store k (A w) R)) = SkaModel.read r regs := fun r hr => by
        obtain ⟨rd, r0, r1, kr⟩ := nd r hr
        rw [read_store_ne rd, read_store_ne (by rcases hk with rfl | rfl <;> assumption)]
        exact kR r kr
      rcases P.shape with ⟨eth, -, hfa, hfit⟩ | ⟨eth, ebo, hnf, Fo, hF, hPF⟩
      · rw [eth] at hj
        have gj : goJ lib O c gul st regs t nex.th = goJ lib O c gul st (store d (A w) (store k (A w) R)) t th := by
          rw [hj, jmp0_of_args P.args]
        exact ⟨⟨fun _ => ⟨store d (A w) (store k (A w) R), (hfit _ _ (read_store_eq _ _ _)).1, kk, gj⟩,
            fun nf => absurd (hfa _) nf⟩,
          fun _ => ⟨fun _ => ⟨store d (A w) (store k (A w) R), read_store_eq _ _ _, kk, gj⟩,
            fun nf => absurd ⟨trivial, looks_empty _⟩ nf⟩⟩
      · rw [eth] at hj
        refine ⟨⟨fun f => absurd f (hnf _), fun _ => ?_⟩, fun hf => absurd (hf w) (hnf _)⟩
        have hcb0 : HoonMap.get c.blocks g0.bo =
            some ⟨[], Fo.map (renPole (unproxy cf)), Termin.bom Option.none⟩ := by
          rw [ag.1 g0.bo (Nat.le_refl _) (by omega) (hnl _ (by omega)), (Rold _ (by omega)).trans ((oE _ (by omega)).trans (old3 _ (by omega))), hF]
          · simp [unproxyBlob, renBlob, renFin]
        rw [hj, goJ_jmp0 _ _ _ _ hcb0]
        obtain ⟨S1, S2⟩ := hPF (unproxy cf) ud (fun x hx => by simp only [NMem] at hx; rw [hx]; exact ud)
          (fun x hx => by rw [hu1 x (by omega), hcn1]) lib σ O c gul st t (store d (A w) (store k (A w) R)) w
          (read_store_eq _ _ _)
        rw [← List.append_nil (Fo.map (renPole (unproxy cf)))]
        by_cases fT : FitsS (⟨Need.this d, laz.sure.lok⟩ : Sure S) (A w)
        · obtain ⟨R', hr', -, -⟩ := S1 fT
          rw [hr', execBlob_bom']
        · exact S2 fT [] _
    rw [pureEval_n3]
    cases ev : pureEval p s with
    | none => rw [ev] at Hp; exact ⟨goalSem_none _ Hp, fun _ => goalSem_none _ Hp⟩
    | some x =>
      rw [ev] at Hp
      obtain ⟨R, hR, k, he⟩ := Hp.1 ⟨trivial, looks_empty x⟩
      have hR' : SkaModel.read g3.re R = some x := hR
      have hj' := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) R t _ _ hco
      rw [hblk, execBlob_clq, hR', Option.bind_some] at hj'
      cases x with
      | cell u v =>
        simp only [Option.bind_some, wut]
        exact fin R 0 gA.re (Or.inl rfl) k (he.trans (hj'.trans (F' R t gul).1))
      | atom n =>
        simp only [Option.bind_some, wut]
        exact fin R 1 (gA.re + 1) (Or.inr rfl) k (he.trans (hj'.trans (F' R t gul).2))
  refine ⟨by omega, by omega, Rdr.trans (hdE.trans d0.symm), fun o ho hn => (keep1 o ho).trans (P.other o ho hn),
    GU.trans Rp.grow, P.pfor.trans (ProxyFor.of_eq (by omega) hcn1), Rp.lo, Rp.hi, ?ent, ?hregs, Rp.dist, ?eregs,
    ?labs, Rp.nodup, by simpa only [sixCount] using Rp.size, ?front, ?ncond, ?econd, ?below, ?nec,
    fun cf hcf c ned σ O st t gul s0 s ag hned regs hh hn => (semAll cf hcf c ned σ O st t gul s0 s ag hned regs hh hn).1,
    P.rreg, by rw [hcn1]; exact P.rkey, ?dich, ?dhold,
    fun hf cf hcf c ned σ O st t gul s0 s ag hned regs hh hn =>
      (semAll cf hcf c ned σ O st t gul s0 s ag hned regs hh hn).2 hf⟩
  case ent =>
    rcases Rp.ent with f | e
    · exact f
    · simp only [GoalJ] at e
      rw [e]
      have fr : Fresh gE (jmp0 g3.bo) := by
        rw [hgE]; exact fresh_emitted (b := blk) hdr4 (by rw [hblk]) (by simp [jmp0, hbo4]) rfl
      exact fr.growU (by simp only [jmp0]; omega) Rp.grow
  case hregs =>
    intro r hr
    rcases Rp.regs r hr with e | e
    · simp only [lazyReg, NMem] at e; subst e; omega
    · omega
  case eregs =>
    intro e he
    exact ⟨(Rp.eregs e he).1, fun r hr => by have := (Rp.eregs e he).2 r hr; omega⟩
  case labs =>
    intro e he
    obtain ⟨x, y, z⟩ := Rp.labs e he
    exact ⟨by omega, y, z⟩
  case front =>
    intro e he
    obtain ⟨A, hA, hP⟩ := P.at_ e he
    have lt := (hlab e he).1
    refine ⟨A, fun B fin hb => (keep1 _ lt).trans (hA B fin hb), ?_⟩
    exact collP_mono d _ _ _ _ _ _ _ _ _ hP (fun k hk => by rw [hcn1]) (Nat.le_refl _) (by omega)
  case ncond =>
    intro r hr
    rcases Rp.regs r hr with e | e
    · simp only [lazyReg, NMem] at e; subst e; exact nk1 _ (by omega)
    · exact nk1 r (by omega)
  case econd =>
    intro e he r hr
    exact nk1 r (by have := (Rp.eregs e he).2 r hr; omega)
  case below =>
    have K4 : Keeps g0 g4 := by rw [hg4]; exact P.keeps.trans (K3f.trans (keeps_reg g3 _ (Nat.le_succ _)))
    exact Kp.keeps.bel g0.bo (K4.bel g0.bo (fun o _ l u _ => absurd u (by omega)))
  case nec =>
    intro s hs'
    rw [pureEval_n3]
    rcases Rp.nec s hs' with e | ⟨x, _, e⟩
    · rw [e]; rfl
    · exact absurd ⟨trivial, looks_empty x⟩ e
  case dich =>
    rcases P.shape with ⟨-, -, hf, -⟩ | ⟨-, -, hf, -⟩
    · exact Or.inl hf
    · exact Or.inr hf
  case dhold =>
    intro hf R v hR
    rcases P.shape with ⟨-, -, -, hfit⟩ | ⟨-, -, hnf, -⟩
    · exact hfit R v hR
    · exact absurd (hf v) (hnf v)

/-- **`[7 [3 p] q]` for `%done` from `gen0` meets `RunOKU`**, for every `q`
in `FragX` whose run for `%done` returns a lazy need not equivalent to `none`
(`hq3`), by the proof of `runOKU_seven4` with `collRun_n3`: the product of
`[3 p]` is the atom `0` or `1`. -/
theorem runOKU_seven3 (lib : Lib) {p q : Nomm} (hp : NextOK (S := S) (Map := Map) lib p)
    (sp : OKNR (S := S) (Map := Map) lib p) (kp : KeepX S Map p) (ap : AboveX S Map p)
    (hq : FragX (S := S) q) (hcount : sixCount (Nomm.n7 (Nomm.n3 p) q) ≤ 255) {region : List Nat}
    {g2 : Gen Map} {nex : NextL S}
    (hq3 : ∀ {nx : NextL S} {g1 : Gen Map}, runL q (CGoalL.done : CGoalL S) region (gen0 : Gen Map) = some (nx, g1) →
      noneEquivalentL nx.laz = false)
    (h : runL (Nomm.n7 (Nomm.n3 p) q) (CGoalL.done : CGoalL S) region (gen0 : Gen Map) = some (nex, g2)) :
    RunOKU (Map := Map) lib (Nomm.n7 (Nomm.n3 p) q) CGoal.done gen0 g2 nex := by
  have hc : sixCount p ≤ 255 ∧ sixCount q ≤ 255 := by simp only [sixCount] at hcount; omega
  have p7 : ∀ s, pureEval (Nomm.n7 (Nomm.n3 p) q) s = (pureEval (Nomm.n3 p) s).bind (pureEval q) := fun _ => rfl
  rw [runL_n7] at h
  obtain ⟨nx, g1, h1, h2⟩ := bind_some h
  have Rq := (runX_ok (Map := Map) lib hq).1 trivial trivial hc.2 (by simp [gen0]) rfl upBelow_gen0 h1
  have Sq := SemPR.toG ((runX_semR (Map := Map) lib hq).1 trivial trivial trivial hc.2 (by simp [gen0]) rfl
    upBelow_gen0 clear_gen0 h1)
  have Bq : BelowIn (gen0 : Gen Map).bo g1 := runX_below (goal := CGoal.done) hq rfl trivial hc.2 h1
  have cq : ∀ k, HoonMap.get g1.cond k = Option.none := fun k => by rw [Rq.cnd]; exact gen0_cond_none k
  obtain ⟨q1, q2, q3, q4⟩ := Rq.ext
  have qlo := Rq.lo
  have qhi := Rq.hi
  obtain ⟨d, CR⟩ := collRun_n3 lib hp sp kp ap h2 (hq3 h1) hc.1 (by omega) (q3.trans rfl) (Rq.grow.up upBelow_gen0)
    (clear_gen0.growU Rq.grow) Rq.lo Rq.hi (fun x hx => (Rq.regs x hx).2) (fun x _ => cq x)
    (fun k hk => by simp [cq k] at hk)
    (List.nodup_cons.mpr ⟨fun hm => by
      obtain ⟨e, he, e1⟩ := List.mem_map.mp hm
      have := (Rq.labs e he).2.1; omega, Rq.nodup⟩)
    (fun e he => by obtain ⟨a, b, th, hb⟩ := Rq.labs e he; exact ⟨by omega, [], _, hb⟩)
    (fun e he x hx => ((Rq.eregs e he).2 x hx).2)
  have Cre := CR.re
  have Cbo := CR.bo
  refine ⟨⟨by omega, by omega, CR.drop.trans q3, fun o ho => (CR.keep o (by omega) (fun hm => ?_)).trans (q4 o ho)⟩,
    Rq.grow.trans CR.grow, (condFresh_of_eq q1 Rq.cnd).trans CR.pfor.1, CR.lo, CR.hi, Or.inl CR.ent,
    fun r hr => ⟨by have := (CR.regs r hr).1; omega, (CR.regs r hr).2⟩, CR.dist,
    fun e he => ⟨(CR.eregs e he).1, fun r hr => ⟨by have := ((CR.eregs e he).2 r hr).1; omega,
      ((CR.eregs e he).2 r hr).2⟩⟩,
    fun e he => ⟨by have := (CR.labs e he).1; omega, (CR.labs e he).2⟩, CR.nodup,
    by have := CR.size; simp only [sixCount] at this ⊢; omega,
    fun s hs' => by rw [p7, CR.nec s hs']; rfl, CR.ncond, CR.econd, ?_⟩
  · obtain ⟨e, he, e1⟩ := List.mem_map.mp hm
    have := (Rq.labs e he).1; omega
  intro c ned σ O st t gul s0 s ag hned regs hh hn
  have agC : AgreeU lib O c gul st t g2.cond ned g1 g2 nex.laz s0 s :=
    ⟨fun o l u hnl => ag.1 o (by omega) u hnl, ag.2⟩
  have Sp := CR.sem g2.cond (fun _ _ => rfl) c ned σ O st t gul s0 s agC (fun r hr => Or.inl (hned r hr)) regs hh hn
  have u1 : ∀ x, x < g1.re → unproxy g2.cond x = id x := fun x hx =>
    unproxy_none (by rw [ProxyFor.get_lt CR.pfor hx]; exact cq x)
  show GoalSem lib O c gul st _ regs t nex.th CGoal.done (pureEval (Nomm.n7 (Nomm.n3 p) q) s)
  cases ev : pureEval (Nomm.n3 p) s with
  | none =>
    rw [ev] at Sp
    have e7 : pureEval (Nomm.n7 (Nomm.n3 p) q) s = none := by rw [p7, ev]; rfl
    rw [e7]; exact goalSem_none _ Sp
  | some v =>
    rw [ev] at Sp
    have e7 : pureEval (Nomm.n7 (Nomm.n3 p) q) s = pureEval q v := by rw [p7, ev]; rfl
    rw [e7]
    obtain ⟨m, rfl⟩ : ∃ m, v = A m := by
      rw [pureEval_n3] at ev
      cases ep : pureEval p s with
      | none => rw [ep] at ev; cases ev
      | some x =>
        rw [ep] at ev
        cases x with
        | atom n => simp [wut] at ev; exact ⟨1, ev.symm⟩
        | cell _ _ => simp [wut] at ev; exact ⟨0, ev.symm⟩
    by_cases fit : FitsS nx.laz.sure (A m)
    · have hfa : ∀ v, FitsS nx.laz.sure (A v) := CR.dich.elim id (fun hn' => absurd fit (hn' m))
      have SpT := CR.semT hfa g2.cond (fun _ _ => rfl) c ned σ O st t gul s0 s agC
        (fun r hr => Or.inl (hned r hr)) regs hh hn
      rw [ev] at SpT
      obtain ⟨R, hR, kR, eR⟩ := SpT.1 ⟨trivial, looks_empty _⟩
      have hR' : SkaModel.read d R = some (A m) := hR
      have agQ : AgreeP lib O c gul st t (Need.pair ned (Need.this d)) gen0 g1 nx.laz (C s0 (A m)) (A m) := by
        refine ⟨fun o l u hnl => ?_, fun e he => ?_⟩
        · have hn2 : o ∉ (entries nex.laz).map Prod.fst := fun hm => by
            obtain ⟨e', he', e1⟩ := List.mem_map.mp hm; have := (CR.labs e' he').1; omega
          rw [ag.1 o l (by omega) hn2, CR.keep o u hnl]
          cases hg : HoonMap.get g1.blocks o with
          | none => rfl
          | some b => simp only [Option.map_some, unproxyBlob, renBlob_congr u1 (Bq o b l u hg), renBlob_id]
        · obtain ⟨l, lt, th, hb⟩ := Rq.labs e he
          obtain ⟨F, hF, hP⟩ := CR.front e he
          have hb2 := hF [] (Termin.hop th) hb
          rw [List.append_nil] at hb2
          have hn2 : e.1 ∉ (entries nex.laz).map Prod.fst := fun hm => by
            obtain ⟨e', he', e1⟩ := List.mem_map.mp hm; have := (CR.labs e' he').1; omega
          refine ⟨F.map (renPole (unproxy g2.cond)), th, hb, ?_, ?_⟩
          · rw [ag.1 e.1 l (by omega) hn2, hb2]
            have hj := (Bq e.1 _ l (by omega) hb).2.2
            simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, renFin, renJmp_congr u1 hj, renJmp_id]
          · exact collP_fillSem hP CR.dkey
              (fun x hx => by rw [ProxyFor.get_lt CR.pfor ((Rq.eregs e he).2 x hx).2]; exact cq x)
              (fun k hk => rfl) lib O c gul st t ned g1.re s0 m
      have inQ : ∀ r, NMem (Need.pair ned (Need.this d)) r → InR (CGoal.done : CGoal S) gen0 g1 nx.laz.sure.ned r := by
        intro r hr
        rcases hr with hr | hr
        · exact Or.inl (by have := hned r hr; omega)
        · have hr' : r = d := hr
          rw [hr']
          rcases CR.dreg with e | e
          · exact Or.inr (Or.inr e)
          · exact Or.inl e
      have hnR : HoldsN (Need.pair ned (Need.this d)) R (C s0 (A m)) :=
        ⟨HoldsN.agree ned (fun r hr => kR r (Or.inr hr)) hn, hR'⟩
      have Sq' := Sq c _ σ O st t gul _ _ agQ inQ R (CR.dhold hfa R m hR') hnR
      exact eR.trans Sq'
    · have cr := Sp.2 fit
      rw [Rq.nec (A m) fit]
      exact goalSem_crash _ cr

/-- **The final pass meets the contract on `[7 [3 p] q]`**, with `p` and `q`
in `FragX`, `p` meeting `AboveX`, the run of `q` for `%done` returning a lazy
need not equivalent to `none` (`hq3`), at most 255 `%6`, when nothing is baked
and the bell's cape has no `[| |]`. -/
theorem finishLF_bellContract73U {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {bl : Bell} {p q : Nomm} (hp : (Nomm.n7 (Nomm.n3 p) q).pure = true)
    (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol (Nomm.n7 (Nomm.n3 p) q))
    (hfp : FragX (S := S) p) (ap : AboveX S Map p) (hfq : FragX (S := S) q)
    (hq3 : ∀ {nx : NextL S} {g1 : Gen Map}, runL q (CGoalL.done : CGoalL S) [] (gen0 : Gen Map) = some (nx, g1) →
      noneEquivalentL nx.laz = false)
    (hcount : sixCount (Nomm.n7 (Nomm.n3 p) q) ≤ 255)
    {cape : Cape} {data : Noun} (hbl : bl.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) (Nomm.n7 (Nomm.n3 p) q) ord cape bake = some c') (N : Needs) :
    BellContract lib N bl false c' :=
  finishLF_bellContractU hok hp hA (fun h1 => runOKU_seven3 lib (runX_ok lib hfp).2.1 (runX_semR lib hfp).2.1
    (runX_keeps hfp) ap hfq hcount hq3 h1) hbl hn hbake h N

/-- The run of `[0 1]` for `%done` returns the sure need `this r` with `r` the
start's `re`, no entries: so it meets `hq3`. -/
theorem runL_n01_done_ne {region : List Nat} {g g' : Gen Map} {nx : NextL S}
    (h : runL (Nomm.n0 1) (CGoalL.done : CGoalL S) region g = some (nx, g')) : noneEquivalentL nx.laz = false := by
  have e : (runL (Nomm.n0 1) (CGoalL.done : CGoalL S) region : CM Map (NextL S)) = simpleNextL CGoalL.done := by
    unfold runL; simp
  rw [e] at h
  simp only [simpleNextL, bind_apply, re_apply, emit_apply, Option.bind_some, pure_apply, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  rw [noneEquivalentL_ofSure]; simp [noneEquivalent]

/-- **`[7 [3 [0 3]] [0 1]]` meets the contract** with no hypothesis beyond
the usual ones. -/
theorem finishLF_bellContract_three {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {bl : Bell}
    (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol (Nomm.n7 (Nomm.n3 (Nomm.n0 3)) (Nomm.n0 1)))
    {cape : Cape} {data : Noun} (hbl : bl.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) (Nomm.n7 (Nomm.n3 (Nomm.n0 3)) (Nomm.n0 1)) ord cape bake = some c')
    (N : Needs) : BellContract lib N bl false c' :=
  finishLF_bellContract73U hok rfl hA (FragX.frag fun _ => trivial) (aboveX_n0 (by decide))
    (FragX.frag fun _ => trivial) (fun h1 => runL_n01_done_ne h1) (by decide) hbl hn hbake h N

end Run

end Comp
end SkaModel
end Formalization
