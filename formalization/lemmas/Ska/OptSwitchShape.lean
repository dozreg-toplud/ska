import lemmas.Ska.OptSwitchTag

/-!
# `+switch-chains`: the shape `test-of` and `chain-of` check

Toward the fields of `TagHyp` (`OptSwitchTag.lean`) from the pass's own
checks.  `testOf_spec`: a test found at `p` has the `%clq s` at `p` to its
yes side `y` and its no side, `y` is listed with the one predecessor `p`, and
the block at `y` has no parameters, a `%hed s d` and an `%imm c r` in either
order, and an `%eqq` of `d` and `r` to its hit and the same no side, with
`uses = 2` for `d` and `r`.  `test_regs`: then `d`, `r` and `s` are three
registers (`uses_ge`: a block's mentions of a register are among its
`uses`; for example `d = r` would be mentioned four times in the block at
`y`).  **`chainOf_spec`**: a chain that `chainOf` returns meets `TagBlocks`
and its first block ends in the `%clq` of the first test, which are the
fields `blocks` and `headFin` of `TagHyp` (`tagHyp_shape`).
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

set_option linter.unusedSimpArgs false

theorem hedImm2 {i0 i1 : Pole} {hs hd md : Nat} {mn : Noun} (e1 : hedOf2 i0 i1 = some (hs, hd))
    (e2 : immOf2 i0 i1 = some (mn, md)) :
    [i0, i1] = [Pole.hed hs hd, Pole.imm mn md] ∨ [i0, i1] = [Pole.imm mn md, Pole.hed hs hd] := by
  cases i0 <;> cases i1 <;> simp [hedOf2, immOf2] at e1 e2 <;>
    (try (obtain ⟨rfl, rfl⟩ := e1)) <;> (try (obtain ⟨rfl, rfl⟩ := e2)) <;> simp

theorem smallAtom_eq {mn : Noun} {c : Nat} (h : smallAtom mn = some c) : mn = A c ∧ c < 2 ^ 31 := by
  cases mn with
  | cell _ _ => simp [smallAtom] at h
  | atom a =>
    simp only [smallAtom] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, by assumption⟩
    · simp at h

/-- **The shape `test-of` checks.** -/
theorem testOf_spec {bl : Map Blob} {rev : Map (List Nat)} {p : Nat} {t : STest}
    (h : testOf bl rev p = some (some t)) :
    ∃ b yb l r, HoonMap.get bl p = some b ∧ b.fin = Termin.clq t.s ⟨[], t.y⟩ ⟨[], t.miss⟩ ∧
      getJa rev t.y = [p] ∧ HoonMap.get bl t.y = some yb ∧ yb.par = [] ∧
      yb.fin = Termin.eqq l r ⟨[], t.hit⟩ ⟨[], t.miss⟩ ∧ ((l = t.d ∧ r = t.r) ∨ (l = t.r ∧ r = t.d)) ∧
      (yb.body = [Pole.hed t.s t.d, Pole.imm (A t.c) t.r] ∨ yb.body = [Pole.imm (A t.c) t.r, Pole.hed t.s t.d]) ∧
      usesOf bl t.d = 2 ∧ usesOf bl t.r = 2 := by
  unfold testOf at h
  obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  all_goals try (simp at h; done)
  rename_i s y n heq
  split at h
  · simp at h
  rename_i hrev
  obtain ⟨yb, hyb, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · simp at h
  rename_i hpar
  split at h
  all_goals try (simp at h; done)
  rename_i l r hit n' heq2
  split at h
  · simp at h
  rename_i hnn
  split at h
  all_goals try (simp at h; done)
  rename_i i0 i1 heq3
  split at h
  all_goals try (simp at h; done)
  rename_i hs hd mn md e1 e2
  split at h
  · simp at h
  rename_i hhs
  split at h
  all_goals try (simp at h; done)
  rename_i cc e3
  split at h
  · simp at h
  rename_i hlr
  split at h
  · simp at h
  rename_i hu
  simp only [Option.some.injEq] at h
  subst h
  simp only [ne_eq, Decidable.not_not] at hrev hpar hnn hhs hlr hu
  subst hnn hhs
  obtain ⟨rfl, -⟩ := smallAtom_eq e3
  refine ⟨b, yb, l, r, hb, heq, hrev, hyb, hpar, heq2, ?_, ?_, hu.1, hu.2⟩
  · rcases hlr with h1 | h1 <;> simp only [Prod.mk.injEq] at h1 <;> simp [h1]
  · rw [heq3]; exact hedImm2 e1 e2

theorem le_sum_of_mem' : ∀ {l : List Nat} {a : Nat}, a ∈ l → a ≤ l.sum
  | _ :: t, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have := le_sum_of_mem' h; simp; omega

/-- A block's mentions of a register are among its `uses`. -/
theorem uses_ge {bl : Map Blob} {y : Nat} {yb : Blob} (hy : HoonMap.get bl y = some yb) (r : Nat) :
    (blobMentions yb).count r ≤ usesOf bl r := by
  unfold usesOf
  rw [List.count_flatMap]
  apply le_sum_of_mem'
  refine List.mem_map.mpr ⟨y, (MapKeys.mem_keys bl y).mpr (by simp [hy]), ?_⟩
  simp [hy]

/-- The registers of a test are distinct from each other and from `s`
(`uses = 2`). -/
theorem test_regs {bl : Map Blob} {rev : Map (List Nat)} {p : Nat} {t : STest}
    (h : testOf bl rev p = some (some t)) : t.d ≠ t.r ∧ t.s ≠ t.d ∧ t.s ≠ t.r := by
  obtain ⟨b, yb, l, r, -, -, -, hyb, hpar, hfin, hlr, hbody, hud, hur⟩ := testOf_spec h
  have cd := uses_ge hyb t.d
  have cr := uses_ge hyb t.r
  rw [hud] at cd; rw [hur] at cr
  have e : yb = ⟨yb.par, yb.body, yb.fin⟩ := rfl
  rw [e, hpar, hfin] at cd cr
  refine ⟨fun hx => ?_, fun hx => ?_, fun hx => ?_⟩ <;>
    rcases hlr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hbody with hb | hb <;> rw [hb] at cd cr <;>
    simp [blobMentions, finRegs, jmpRegs, poleRegs, List.count_cons, hx] at cd cr <;>
    (try split at cd) <;> (try split at cr) <;> omega

/-- The step of `chain-of`: the chain stops after `t`, or goes on at its no
side, an empty block whose test is on the same `s`. -/
theorem chainOf_step {bl : Map Blob} {rev : Map (List Nat)} {n p : Nat} {t : STest} {rest : List STest}
    (h : ((HoonMap.get bl t.miss).bind fun nb =>
        if ¬ (nb.par = [] ∧ nb.body = []) then some [] else
        let rm := getJa rev t.miss
        if ¬ (rm = [p, t.y] ∨ rm = [t.y, p]) then some [] else
        (testOf bl rev t.miss).bind fun t2 =>
        match t2 with
        | none => some []
        | some t2 => if t2.s ≠ t.s then some [] else chainOf bl rev n t.miss) = some rest) :
    rest = [] ∨ ∃ nb t2, HoonMap.get bl t.miss = some nb ∧ nb.par = [] ∧ nb.body = [] ∧
      testOf bl rev t.miss = some (some t2) ∧ t2.s = t.s ∧ chainOf bl rev n t.miss = some rest := by
  obtain ⟨nb, hnb, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · simp at h; first | exact Or.inl h | exact Or.inl h.symm
  rename_i hnb2
  simp only [Decidable.not_not] at hnb2
  dsimp only at h
  split at h
  · simp at h; first | exact Or.inl h | exact Or.inl h.symm
  obtain ⟨t2o, ht2o, h⟩ := Option.bind_eq_some_iff.mp h
  cases t2o with
  | none => simp at h; first | exact Or.inl h | exact Or.inl h.symm
  | some t2 =>
    simp only at h
    split at h
    · simp at h; first | exact Or.inl h | exact Or.inl h.symm
    · rename_i hs
      simp only [ne_eq, Decidable.not_not] at hs
      exact Or.inr ⟨nb, t2, hnb, hnb2.1, hnb2.2, ht2o, hs, h⟩

/-- **The shape `chain-of` checks**: the head's `%clq` and `TagBlocks`. -/
theorem chainOf_spec {bl : Map Blob} {rev : Map (List Nat)} : ∀ (n p : Nat) (t0 : STest) (tl : List STest),
    chainOf bl rev n p = some (t0 :: tl) →
    (∃ b, HoonMap.get bl p = some b ∧ b.fin = Termin.clq t0.s ⟨[], t0.y⟩ ⟨[], t0.miss⟩) ∧
      TagBlocks bl t0.s (tagMiss t0 tl) (t0 :: tl)
  | 0, _, _, _, h => by simp [chainOf] at h
  | n + 1, p, t0, tl, h => by
    unfold chainOf at h
    obtain ⟨to, hto, h⟩ := Option.bind_eq_some_iff.mp h
    cases to with
    | none => simp at h
    | some t =>
    simp only at h
    obtain ⟨rest, hin, hcs⟩ := Option.map_eq_some_iff.mp h
    simp only [List.cons.injEq] at hcs
    obtain ⟨rfl, rfl⟩ := hcs
    obtain ⟨b, yb, l, r, hb, hfin, -, hyb, hpar, hyf, hlr, hbody, -, -⟩ := testOf_spec hto
    obtain ⟨hdr, hsd, hsr⟩ := test_regs hto
    have hyb' : HoonMap.get bl t.y = some ⟨[], yb.body, Termin.eqq l r ⟨[], t.hit⟩ ⟨[], t.miss⟩⟩ := by
      rw [hyb, ← hpar, ← hyf]
    refine ⟨⟨b, hb, hfin⟩, rfl, hdr, hsd, hsr, ⟨l, r, yb.body, hyb', hlr, hbody⟩, ?_⟩
    rcases chainOf_step hin with rfl | ⟨nb, t2, hnb, hnp, hnbd, ht2, hs2, hch⟩
    · exact ⟨rfl, fun h => absurd rfl h⟩
    · cases rest with
      | nil =>
        -- a chain that goes on is not empty
        cases n with
        | zero => simp [chainOf] at hch
        | succ n =>
          unfold chainOf at hch
          rw [ht2] at hch
          simp only [Option.bind_some] at hch
          obtain ⟨a, -, ha⟩ := Option.map_eq_some_iff.mp hch
          cases ha
      | cons t2' tl' =>
        obtain ⟨⟨b', hb', hf'⟩, htb⟩ := chainOf_spec n t.miss t2' tl' hch
        obtain ⟨b'', -, -, -, -, -, -, -, -, -⟩ := testOf_spec ht2
        obtain ⟨b3, -, -, -, hb3, hf3, -, -, -, -, -, -, -, -⟩ := testOf_spec ht2
        rw [hnb] at hb'; cases hb'
        rw [hnb] at hb3; cases hb3
        rw [hf'] at hf3
        simp only [Termin.clq.injEq, Jmp.mk.injEq, true_and] at hf3
        obtain ⟨e1, e2, e3⟩ := hf3
        have e : t2'.s = t.s := by rw [e1, hs2]
        refine ⟨?_, fun _ => ?_⟩
        · show HoonMap.get bl t.miss = some ⟨[], [], Termin.clq t.s ⟨[], t2'.y⟩ ⟨[], t2'.miss⟩⟩
          rw [hnb, ← e]
          have : nb = ⟨nb.par, nb.body, nb.fin⟩ := rfl
          rw [this, hnp, hnbd, hf']
        · rw [← e]
          have em : tagMiss t (t2' :: tl') = tagMiss t2' tl' := by
            simp [tagMiss, List.getLast_cons]
          rw [em]; exact htb

/-- The fields `blocks` and `headFin` of `TagHyp`, from `chainOf`. -/
theorem tagHyp_shape {bl : Map Blob} {rev : Map (List Nat)} {n o : Nat} {t0 : STest} {tl : List STest}
    (h : chainOf bl rev n o = some (t0 :: tl)) :
    TagBlocks bl t0.s (tagMiss t0 tl) (t0 :: tl) ∧
      ∃ b, HoonMap.get bl o = some b ∧ b.fin = Termin.clq t0.s ⟨[], t0.y⟩ ⟨[], t0.miss⟩ :=
  ⟨(chainOf_spec n o t0 tl h).2, (chainOf_spec n o t0 tl h).1⟩

end Opt
end SkaModel
end Formalization
