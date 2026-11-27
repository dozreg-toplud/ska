import lemmas.Compiler.OptLinkTotalHops

/-!
# The structural loop of `+optimize-once` returns

**`structLoop_total`**: on blocks with `StInv ρ L` and `topo`, `rev` with
`TopoInv`, there is a bound `F` and a result `r` such that `structLoop fuel
n` returns `r` for every `fuel` and count `n` from `F` on; the result's blocks
have `StInv ρ L`, with its `topo` and `rev` `TopoInv`, and its measure is at
most that of the input.  The proof is an induction along the lexicographic
order of the measure `mu ρ L` (`lex_induction`): each pass returns past a
bound on the fuel with a result that no longer depends on it
(`removeHops_stable`, `rub_isSome`, `removeEmptyMiddle_stable`,
`bbTopo_stable`), keeps `StInv` and does not raise the measure
(`hops_inv_step`, `rub_inv_step`, `mid_inv_step`), and a round that reports a
change lowers it, so the next round is covered by the induction.

**`structEntry_total`**: the same for the entry of `+optimize-once`, which
computes `topo` by `+bb-topo` and `rev` by `+rev-cfg` first.
-/

namespace Formalization
namespace Compiler

open Nock SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

section
variable {Map : Type → Type} [HoonMap Map] [Opt.MapKeys Map]

/-- What the structural loop returns. -/
def LoopOK (ρ : Nat → Nat) (L : List Nat) (bl : Map Blob) (r : List Nat × Map (List Nat) × Map Blob) : Prop :=
  StInv ρ L r.2.2 ∧ Opt.TopoInv r.2.2 r.1 r.2.1 ∧ LexLe (mu ρ L r.2.2) (mu ρ L bl)

/-- **The structural loop returns**, past a bound on the fuel and the count. -/
theorem structLoop_total (ρ : Nat → Nat) (L : List Nat) : ∀ (bl : Map Blob) (topo : List Nat)
    (rev : Map (List Nat)), StInv ρ L bl → Opt.TopoInv bl topo rev →
    ∃ F r, ∀ fuel n, F ≤ fuel → F ≤ n → Opt.structLoop fuel n bl topo rev = some r ∧ LoopOK ρ L bl r := by
  suffices H : ∀ x (bl : Map Blob) (topo : List Nat) (rev : Map (List Nat)), mu ρ L bl = x → StInv ρ L bl →
      Opt.TopoInv bl topo rev →
      ∃ F r, ∀ fuel n, F ≤ fuel → F ≤ n → Opt.structLoop fuel n bl topo rev = some r ∧ LoopOK ρ L bl r from
    fun bl topo rev => H _ bl topo rev rfl
  refine lex_induction _ fun x ih bl topo rev hx hI hi => ?_
  obtain ⟨F1, ⟨c1, b1⟩, hF1⟩ := removeHops_stable hi hI.acyclic hI.arity
  obtain ⟨I1, l1, s1⟩ := hops_inv_step hI hi (hF1 F1 (Nat.le_refl _))
  obtain ⟨⟨c2, b2⟩, h2⟩ := Option.isSome_iff_exists.1 (rub_isSome I1.closed I1.two)
  obtain ⟨I2, l2, s2⟩ := rub_inv_step I1 h2
  obtain ⟨F3, ⟨c3, b3⟩, hF3⟩ := removeEmptyMiddle_stable I2.acyclic I2.closed I2.arity
  obtain ⟨I3, l3, s3⟩ := mid_inv_step I2 (hF3 F3 (Nat.le_refl _))
  have l13 : LexLe (mu ρ L b3) (mu ρ L bl) := lexLe_trans l3 (lexLe_trans l2 l1)
  by_cases hc : (c1 || c2 || c3) = false
  · simp only [Bool.or_eq_false_iff] at hc
    obtain ⟨⟨e1, e2⟩, e3⟩ := hc
    subst e1 e2 e3
    have t1 := Opt.hops_topoInv hi (hF1 F1 (Nat.le_refl _))
    have t3 := Opt.mid_topoInv (hF3 F3 (Nat.le_refl _)) (Opt.rub_topoInv h2 t1)
    refine ⟨F1 + F3 + 1, (topo, rev, b3), fun fuel n hf hn => ⟨?_, I3, t3, l13⟩⟩
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [Opt.structLoop, hF1 fuel (by omega), Option.bind_some, h2, hF3 fuel (by omega)]
    rfl
  · have hc' : (c1 || c2 || c3) = true := by
      cases h : (c1 || c2 || c3)
      · exact absurd h hc
      · rfl
    have hlt : LexLt (mu ρ L b3) (mu ρ L bl) := by
      simp only [Bool.or_eq_true] at hc'
      rcases hc' with (h | h) | h
      · exact lexLt_of_le_lt (lexLe_trans l3 l2) (s1 h)
      · exact lexLt_of_le_lt l3 (lexLt_of_lt_le (s2 h) l1)
      · exact lexLt_of_lt_le (s3 h) (lexLe_trans l2 l1)
    obtain ⟨F4, topo', hF4⟩ := bbTopo_stable I3.acyclic I3.closed I3.zero
    have t4 : Opt.TopoInv b3 topo' (Opt.revCfg b3 topo') :=
      Opt.topoInv_revCfg (Opt.bbTopo_ok I3.acyclic (hF4 F4 (Nat.le_refl _)))
    obtain ⟨F5, r, hF5⟩ := ih (mu ρ L b3) (hx ▸ hlt) b3 topo' _ rfl I3 t4
    refine ⟨F1 + F3 + F4 + F5 + 1, r, fun fuel n hf hn => ?_⟩
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨e5, I5, t5, l5⟩ := hF5 fuel n' (by omega) (by omega)
    refine ⟨?_, I5, t5, lexLe_trans l5 l13⟩
    simp only [Opt.structLoop, hF1 fuel (by omega), Option.bind_some, h2, hF3 fuel (by omega), hc',
      Bool.not_true, Bool.false_eq_true, if_false, hF4 fuel (by omega), e5]

/-- **The entry of the structural loop returns**: `+bb-topo`, `+rev-cfg` and
the loop, with the same fuel for the count, as `+optimize-once` runs them. -/
theorem structEntry_total (ρ : Nat → Nat) (L : List Nat) (bl : Map Blob) (hI : StInv ρ L bl) :
    ∃ F r, ∀ fuel, F ≤ fuel →
      ((Opt.bbTopo fuel bl).bind fun topo0 => Opt.structLoop fuel fuel bl topo0 (Opt.revCfg bl topo0)) = some r ∧
      LoopOK ρ L bl r := by
  obtain ⟨F0, topo0, hF0⟩ := bbTopo_stable hI.acyclic hI.closed hI.zero
  have t0 := Opt.topoInv_revCfg (Opt.bbTopo_ok hI.acyclic (hF0 F0 (Nat.le_refl _)))
  obtain ⟨F, r, hF⟩ := structLoop_total ρ L bl topo0 _ hI t0
  refine ⟨F0 + F, r, fun fuel hf => ?_⟩
  obtain ⟨e, ok⟩ := hF fuel fuel (by omega) (by omega)
  rw [hF0 fuel (by omega), Option.bind_some]
  exact ⟨e, ok⟩

end

end Compiler
end Formalization
