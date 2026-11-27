import lemmas.Compiler.CompRunHintKD

/-!
# The kept hints of `+run`: the invariant and the results (README Gaps 25)

* `hop_tag_keep`, `lazyBound_eq`, `pastIfL_eq`: what `+lazy-bound` and
  `+past-if` return (the `%hop` block at `g.bo`, `+set-tag`).
* `linv_bound`, `linv_pastIf`: `LInv` of the needs they return, one label
  more; `pastIfL_inv`: `+past-if` keeps `LInv`, the jump and the registers.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-- The `%hop` block and `+set-tag`. -/
theorem hop_tag_keep {th : Jmp} {region : List Nat} {g g1 g2 : Gen (TreapMap mugF)} {o : Nat} {u : Unit}
    (e1 : emit ⟨[], [], Termin.hop th⟩ g = some (o, g1)) (e2 : setTag o region g1 = some (u, g2)) :
    o = g.bo ∧ g2.re = g.re ∧ g2.bo = g.bo + 1 ∧ g2.drop = g.drop := by
  rw [cf_emit_g] at e1
  simp only [Option.some.injEq, Prod.mk.injEq] at e1
  obtain ⟨rfl, rfl⟩ := e1
  simp only [setTag, Option.some.injEq, Prod.mk.injEq] at e2
  obtain ⟨-, rfl⟩ := e2
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> split <;> simp [cf_emitG_bo, cf_emitG_re, cf_emitG_drop]

theorem lazyBound_eq {nex nex' : NextL CSet} {region : List Nat} {g g' : Gen (TreapMap mugF)}
    (h : lazyBound nex region g = some (nex', g')) :
    nex' = ⟨Lazy.mk Sure.bunt [] [(g.bo, nex.laz)], jmp0 g.bo⟩ ∧ g'.re = g.re ∧ g'.bo = g.bo + 1 ∧
      g'.drop = g.drop := by
  simp only [lazyBound] at h
  obtain ⟨o, g1, e1, h⟩ := bind_some h
  obtain ⟨u, g2, e2, h⟩ := bind_some h
  obtain ⟨rfl, r, b, d⟩ := hop_tag_keep e1 e2
  split at h
  · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, r, b, d⟩
  · simp at h

theorem pastIfL_eq {snd : Nomm → NeedOrd → Bool} {nex nex' : NextL CSet} {nom : Nomm} {region : List Nat}
    {g g' : Gen (TreapMap mugF)} (h : pastIfL snd nex nom region g = some (nex', g')) :
    (nex' = nex ∧ g' = g) ∨
    (nex' = ⟨Lazy.mk Sure.bunt nex.laz.fork ((g.bo, Lazy.mk nex.laz.sure [] []) :: nex.laz.bond), jmp0 g.bo⟩ ∧
      g'.re = g.re ∧ g'.bo = g.bo + 1 ∧ g'.drop = g.drop) := by
  simp only [pastIfL] at h
  split at h
  · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    exact Or.inl ⟨h.1.symm, h.2.symm⟩
  · obtain ⟨o, g1, e1, h⟩ := bind_some h
    obtain ⟨u, g2, e2, h⟩ := bind_some h
    obtain ⟨rfl, r, b, d⟩ := hop_tag_keep e1 e2
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inr ⟨rfl, r, b, d⟩

theorem mem_blabs : ∀ (b : List (Nat × Lazy CSet)), ∀ e ∈ b, e.1 ∈ blabs b
  | [], e, he => by simp at he
  | (o, l) :: rest, e, he => by
    simp only [List.mem_cons] at he
    simp only [blabs, List.mem_cons, List.mem_append]
    rcases he with rfl | he
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (mem_blabs rest e he))

/-- **`LInv` of the bond of `+lazy-bound`**, one label more. -/
theorem linv_bound {kr kb : Nat} {laz : Lazy CSet} (h : LInv kr kb laz) :
    LInv kr (kb + 1) (Lazy.mk Sure.bunt [] [(kb, laz)]) ∧ lregs (Lazy.mk Sure.bunt [] [(kb, laz)]) = lregs laz := by
  obtain ⟨w, nd, k, l⟩ := h
  have hb := (linv_bunt kr (kb + 1)).1.1
  have hr : lregs (Lazy.mk Sure.bunt [] [(kb, laz)]) = lregs laz := by
    simp [lregs, fregs, bregs, Sure.bunt, flattenNeed]
  refine ⟨⟨⟨hb, trivial, ?_, trivial⟩, hr ▸ nd, ?_, ?_⟩, hr⟩
  · obtain ⟨s, f, b⟩ := laz
    exact ⟨w.1, w.2.1, w.2.2⟩
  · simp only [LKeys, FKeys, BKeys, List.map, List.nodup_nil, List.nodup_cons, List.not_mem_nil,
      not_false_eq_true, and_true, true_and, k]
  · intro o ho
    simp only [llabs, flabs, blabs, List.nil_append, List.append_nil, List.mem_cons] at ho
    rcases ho with rfl | ho
    · omega
    · have := l o ho; omega

/-- **`LInv` of the need of `+past-if`** with its block, one label more. -/
theorem linv_pastIf {kr kb : Nat} {s : Sure CSet} {f : List (Lazy.ForkE CSet)} {b : List (Nat × Lazy CSet)}
    (h : LInv kr kb (Lazy.mk s f b)) :
    LInv kr (kb + 1) (Lazy.mk Sure.bunt f ((kb, Lazy.mk s [] []) :: b)) ∧
      ∀ r, r ∈ lregs (Lazy.mk Sure.bunt f ((kb, Lazy.mk s [] []) :: b)) ↔ r ∈ lregs (Lazy.mk s f b) := by
  obtain ⟨w, nd, k, l⟩ := h
  have hb := (linv_bunt kr (kb + 1)).1.1
  have hr : lregs (Lazy.mk Sure.bunt f ((kb, Lazy.mk s [] []) :: b)) = fregs f ++ (flattenNeed s.ned ++ bregs b) := by
    simp [lregs, fregs, bregs, Sure.bunt, flattenNeed]
  have hp : (lregs (Lazy.mk Sure.bunt f ((kb, Lazy.mk s [] []) :: b))).Perm (lregs (Lazy.mk s f b)) := by
    rw [hr]
    simp only [lregs]
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.perm_append_comm.append_right _
  have hbl : ∀ e ∈ b, e.1 < kb := fun e he => l e.1 (by
    simp only [llabs, List.mem_append]; exact Or.inr (mem_blabs b e he))
  obtain ⟨k1, k2, k3, k4⟩ := k
  refine ⟨⟨⟨hb, w.2.1, ⟨w.1, trivial, trivial⟩, w.2.2⟩, hp.nodup_iff.2 nd, ⟨k1, ?_, k3, ?_, k4⟩, ?_⟩,
    fun r => hp.mem_iff⟩
  · simp only [List.map, List.nodup_cons, List.mem_map]
    refine ⟨fun ⟨e, he, ee⟩ => ?_, k2⟩
    have := hbl e he; omega
  · simp [LKeys, FKeys, BKeys]
  · intro o ho
    simp only [llabs, flabs, blabs, List.nil_append, List.append_nil, List.mem_cons, List.mem_append] at ho l
    rcases ho with ho | rfl | ho
    · have := l o (Or.inl ho); omega
    · omega
    · have := l o (Or.inr ho); omega

/-- **`+past-if` keeps `LInv`**, the jump below the counter and the
registers (as sets). -/
theorem pastIfL_inv {snd : Nomm → NeedOrd → Bool} {nex nex' : NextL CSet} {nom : Nomm} {region : List Nat}
    {g g' : Gen (TreapMap mugF)} (hl : LInv g.re g.bo nex.laz) (hj : JmpIn (· < g.re) nex.th)
    (h : pastIfL snd nex nom region g = some (nex', g')) :
    g.re = g'.re ∧ g.bo ≤ g'.bo ∧ g'.drop = g.drop ∧ LInv g'.re g'.bo nex'.laz ∧ JmpIn (· < g'.re) nex'.th ∧
      ∀ r, r ∈ lregs nex'.laz ↔ r ∈ lregs nex.laz := by
  rcases pastIfL_eq h with ⟨rfl, rfl⟩ | ⟨rfl, r, b, d⟩
  · exact ⟨rfl, Nat.le_refl _, rfl, hl, hj, fun _ => Iff.rfl⟩
  · obtain ⟨⟨s, f, bd⟩, th⟩ := nex
    obtain ⟨L, M⟩ := linv_pastIf hl
    refine ⟨r.symm, by omega, d, ?_, jmpIn_jmp0 _ _, M⟩
    rw [r, b]; exact L

end Compiler
end Formalization
