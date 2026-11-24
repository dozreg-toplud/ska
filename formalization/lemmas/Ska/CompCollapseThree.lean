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
allocates, so every register they mention is at least `m` when `r` and the
start's `re` are. -/
theorem forl_above {r o m : Nat} {g g' : Gen Map} {x : Nat × Nat} (h : forl r o g = some (x, g'))
    (hd : g.drop = false) (hr : m ≤ r) (hm : m ≤ g.re) :
    g'.re = g.re + 2 ∧ g'.bo = g.bo + 3 ∧ g'.drop = g.drop ∧ g'.cond = g.cond ∧
    (∀ o', o' < g.bo → HoonMap.get g'.blocks o' = HoonMap.get g.blocks o') ∧
    ∀ o' b, g.bo ≤ o' → o' < g'.bo → HoonMap.get g'.blocks o' = some b → BlobIn (m ≤ ·) b := by
  simp only [forl, bind_apply, re_apply, emit_apply, Option.bind_some, pure_apply, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨rfl, rfl, rfl, rfl, fun o' ho => ?_, fun o' b l u hb => ?_⟩
  · simp only [Gen.emitted, hd, Bool.false_eq_true, if_false, HoonMap.get_put]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · simp only [Gen.emitted, hd, Bool.false_eq_true, if_false, HoonMap.get_put] at hb u
    by_cases e2 : o' = g.bo + 1 + 1
    · rw [if_pos e2] at hb; cases hb
      refine ⟨fun x hx => absurd hx List.not_mem_nil, regsIn_one (fun x hx => ?_), jmpIn_one (by omega)⟩
      simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; omega
    rw [if_neg e2] at hb
    by_cases e1 : o' = g.bo + 1
    · rw [if_pos e1] at hb; cases hb
      refine ⟨fun x hx => absurd hx List.not_mem_nil, regsIn_one (fun x hx => ?_), jmpIn_one (by omega)⟩
      simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; omega
    rw [if_neg e1] at hb
    have e0 : o' = g.bo := by omega
    rw [if_pos e0] at hb; cases hb
    refine ⟨fun x hx => ?_, RegsIn.nil _, jmpIn_jmp0 _ _⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx; omega

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
  obtain ⟨r3, b3, dr3, cn3, old3, F3⟩ := forl_above h3 dA hda (by omega)
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

end Run

end Comp
end SkaModel
end Formalization
