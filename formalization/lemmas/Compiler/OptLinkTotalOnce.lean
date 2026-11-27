import lemmas.Compiler.OptLinkTotalLoop
import lemmas.Ska.OptAliasSSA

/-!
# `+optimize-once` and `+optimize` return, given what `+alias` and
`+trim-trace-hints` owe

`dead_step`: `+remove-dead-code` on `topo` reversed returns on blocks with
`StInv` and `TopoInv` (`dead_isSome`), keeps both and does not raise the
measure (a block it drops lowers the number of blocks, the others keep their
ends).

`PassTotal P ρ L J`: **what the converse of `+optimize` needs of the passes
that are parameters of the driver**, over a block invariant `J` (meant as
`DInvR`, the invariant of raw `+comp` output, `OptIn`): `DriverHyp` with `J`
and `TopoInvR` at every fuel (every pass keeps `J`, and `topo`, `rev` keep
`TopoInvR`; `driverHypR_of`), `+alias` returns on blocks with `StInv`, `J`
and `TopoInvR`, keeps `StInv`, does not raise the measure and lowers it when
it reports a change; `+trim-trace-hints` returns, keeps `StInv` and does not
raise the measure; `+switch-chains` returns.  `passTotal_of`
(`OptLinkTotalPass.lean`) builds it for the passes of the Hoon.

`optimizeOnce_total`, `optLoop_total` (induction along `LexLt` of the
measure: a turn that reports a change lowers it), **`optimizeF_total`**: under
`PassTotal`, `+optimize` returns on blocks with `StInv` and `J`, with a result
that does not depend on the fuel past a bound.
-/

namespace Formalization
namespace Compiler

open Nock SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

section
variable {Map : Type → Type} [HoonMap Map]

/-! ## `+remove-dead-code` -/

theorem deadFold_keys (bl : Map Blob) : ∀ (l : List Nat) (acc r : Map Blob × List Nat),
    l.foldlM (fun (acc : Map Blob × List Nat) o =>
      (HoonMap.get bl o).map fun b =>
        let r := Opt.deadBody b.body.reverse [] (Opt.finRegs b.fin ++ acc.2)
        (HoonMap.put acc.1 o { b with body := r.1 }, r.2)) acc = some r →
    ∀ k, (HoonMap.get r.1 k).isSome → (HoonMap.get acc.1 k).isSome ∨ k ∈ l
  | [], acc, r, h, k, hk => by simp only [List.foldlM_nil] at h; cases h; exact Or.inl hk
  | o :: l, acc, r, h, k, hk => by
    rw [List.foldlM_cons] at h
    obtain ⟨acc1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h1
    rcases deadFold_keys bl l _ r h k hk with h2 | h2
    · simp only [HoonMap.get_put] at h2
      split at h2
      · rename_i e; exact Or.inr (by simp [e])
      · exact Or.inl h2
    · exact Or.inr (List.mem_cons_of_mem _ h2)

theorem dead_isSome {bl : Map Blob} {revTopo : List Nat} (h : ∀ o ∈ revTopo, (HoonMap.get bl o).isSome) :
    (Opt.removeDeadCode bl revTopo).isSome := by
  unfold Opt.removeDeadCode
  rw [Option.isSome_map]
  exact foldlM_isSome _ _ _ fun o ho acc => by rw [Option.isSome_map]; exact h o ho

/-- **`+remove-dead-code` keeps `StInv`, `TopoInv` and does not raise the
measure.** -/
theorem dead_step {ρ : Nat → Nat} {L : List Nat} {bl bd : Map Blob} {topo : List Nat} {rev : Map (List Nat)}
    (hI : StInv ρ L bl) (hi : Opt.TopoInv bl topo rev) (h : Opt.removeDeadCode bl topo.reverse = some bd) :
    StInv ρ L bd ∧ Opt.TopoInv bd topo rev ∧ LexLe (mu ρ L bd) (mu ρ L bl) := by
  obtain ⟨hs, hall⟩ := Opt.dead_shape h
  have hkeys : ∀ k, (HoonMap.get bd k).isSome → k ∈ topo := by
    intro k hk
    unfold Opt.removeDeadCode at h
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
    rcases deadFold_keys bl _ _ r hr k hk with h1 | h1
    · simp [HoonMap.get_empty] at h1
    · exact List.mem_reverse.mp h1
  have hpres : ∀ k, (HoonMap.get bd k).isSome → HoonMap.get bd k = HoonMap.get bl k ∨ True := fun _ _ => Or.inr trivial
  have hsub : Opt.TargetsSub bl bd := fun k b' hb' => by
    obtain ⟨b, hb, -, hfin⟩ := hs k b' hb'
    exact ⟨b, hb, fun j' hj' => ⟨j', by rw [← hfin]; exact hj', rfl⟩⟩
  have hti : Opt.TopoInv bd topo rev :=
    Opt.topoInv_sub hi hsub fun o ho => hall o (List.mem_reverse.mpr ho)
  -- pointwise: a block is kept with its parameters and end, or dropped
  have hpw : ∀ o, (presN (HoonMap.get bd o) ≤ presN (HoonMap.get bl o) ∧
      twoCnt (HoonMap.get bd o) ≤ twoCnt (HoonMap.get bl o) ∧ rkN ρ (HoonMap.get bd o) ≤ rkN ρ (HoonMap.get bl o)) ∧
      ((HoonMap.get bd o).isSome → presN (HoonMap.get bd o) = presN (HoonMap.get bl o) ∧
        twoCnt (HoonMap.get bd o) = twoCnt (HoonMap.get bl o) ∧ rkN ρ (HoonMap.get bd o) = rkN ρ (HoonMap.get bl o)) := by
    intro o
    cases e1 : HoonMap.get bd o with
    | none => simp [presN, twoCnt, rkN]
    | some b' =>
      obtain ⟨b, hb, -, hfin⟩ := hs o b' e1
      rw [hb]
      simp [presN, twoCnt, rkN, hfin]
  refine ⟨⟨rank_sub hI.rank hsub, fun o b' j hb' hj => ?_, fun o b' j b2' hb' hj hb2' => ?_, ?_,
    fun o b' j hb' ht hj => ?_, fun o ho => ?_⟩, hti, ?_⟩
  · obtain ⟨b, hb, -, hfin⟩ := hs o b' hb'
    rw [hfin] at hj
    obtain ⟨i, hi'⟩ := List.mem_iff_getElem?.1 (hkeys o (by simp [hb']))
    obtain ⟨k, -, hk⟩ := hi.1.2.2.2.2 i o b j hi' hb hj
    exact hall _ (List.mem_reverse.mpr (List.mem_iff_getElem?.2 ⟨k, hk⟩))
  · obtain ⟨b, hb, -, hfin⟩ := hs o b' hb'
    obtain ⟨b2, hb2, hpar, -⟩ := hs j.there b2' hb2'
    rw [hfin] at hj; rw [hpar]
    exact hI.arity o b j b2 hb hj hb2
  · exact hall 0 (List.mem_reverse.mpr (List.mem_of_mem_head? hi.1.2.1))
  · obtain ⟨b, hb, -, hfin⟩ := hs o b' hb'
    rw [hfin] at ht hj
    exact hI.two o b j hb ht hj
  · obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 ho
    obtain ⟨b, hb, -⟩ := hs o b' hb'
    exact hI.keys o (by simp [hb])
  · by_cases hdrop : ∃ k ∈ L, (HoonMap.get bd k).isSome = false ∧ (HoonMap.get bl k).isSome = true
    · obtain ⟨k, hk, h1, h2⟩ := hdrop
      refine Or.inl (mu_lt1 (fun o _ => (hpw o).1.1) hk ?_)
      cases e1 : HoonMap.get bd k with
      | some _ => rw [e1] at h1; cases h1
      | none =>
        cases e2 : HoonMap.get bl k with
        | none => rw [e2] at h2; cases h2
        | some _ => simp [presN]
    · refine Or.inr (mu_eq fun o ho => ?_)
      cases e1 : HoonMap.get bd o with
      | some b' => have := (hpw o).2 (by simp [e1]); rw [e1] at this; exact this
      | none =>
        cases e2 : HoonMap.get bl o with
        | none => exact ⟨rfl, rfl, rfl⟩
        | some _ => exact absurd ⟨o, ho, by simp [e1], by simp [e2]⟩ hdrop

/-! ## What the parameters of the driver owe -/

/-- `topo` filtered by the blocks that remain, as `+optimize-once` does after
`+alias`. -/
def topoF (bl : Map Blob) (topo : List Nat) : List Nat := topo.filter fun o => (HoonMap.get bl o).isSome

variable [Opt.MapKeys Map]

/-- **What the converse of `+optimize` assumes of `+alias`,
`+trim-trace-hints`, `+switch-chains`**, over a block invariant `J`: the
driver's hypothesis `DriverHyp` at every fuel with `J` and `TopoInvR` (each
pass keeps `J` and `TopoInvR`, which `driverHypR_of` proves for `J = DInvR`
and the passes of the Hoon), and that `+alias` and `+trim-trace-hints` return,
keep `StInv` and do not raise the measure, `+alias` lowering it when it
reports a change, and that `+switch-chains` returns. -/
structure PassTotal (P : Opt.Passes Map) (ρ : Nat → Nat) (L : List Nat) (J : Map Blob → Prop) : Prop where
  drv : ∀ fuel, Opt.DriverHyp fuel P J Opt.TopoInvR
  alias : ∀ n bl topo rev, StInv ρ L bl → J bl → Opt.TopoInvR bl topo rev →
    ∃ f bl', P.alias n bl rev topo = some (f, bl') ∧ StInv ρ L bl' ∧
      LexLe (mu ρ L bl') (mu ρ L bl) ∧ (f = true → LexLt (mu ρ L bl') (mu ρ L bl))
  trim : ∀ bl topo rev, StInv ρ L bl → J bl → Opt.TopoInvR bl topo rev →
    ∃ bl', P.trim bl topo rev = some bl' ∧ StInv ρ L bl' ∧ LexLe (mu ρ L bl') (mu ρ L bl)
  switch : ∀ bl, StInv ρ L bl → J bl → (P.switch bl).isSome

variable {P : Opt.Passes Map} {ρ : Nat → Nat} {L : List Nat} {J : Map Blob → Prop}

/-- **`+optimize-once` returns**, past a bound on the fuel, keeps `StInv`
and `J`, does not raise the measure and lowers it when it reports a change. -/
theorem optimizeOnce_total (H : PassTotal P ρ L J) (s : Straight Map) (hI : StInv ρ L s.blocks) (hJ : J s.blocks) :
    ∃ F r, ∀ fuel, F ≤ fuel → Opt.optimizeOnce fuel P s = some r ∧ StInv ρ L r.2.blocks ∧ J r.2.blocks ∧
      LexLe (mu ρ L r.2.blocks) (mu ρ L s.blocks) ∧ (r.1 = true → LexLt (mu ρ L r.2.blocks) (mu ρ L s.blocks)) ∧
      r.2 = Opt.withBlocks s r.2.blocks := by
  obtain ⟨F0, topo0, hF0⟩ := bbTopo_stable hI.acyclic hI.closed hI.zero
  have t0 := Opt.topoInv_revCfg (Opt.bbTopo_ok hI.acyclic (hF0 F0 (Nat.le_refl _)))
  obtain ⟨Fl, ⟨tp, rv, bs⟩, hFl⟩ := structLoop_total ρ L s.blocks topo0 _ hI t0
  obtain ⟨el, Il, tl, ll⟩ := hFl (F0 + Fl) (F0 + Fl) (by omega) (by omega)
  obtain ⟨-, Jl, tRl⟩ := Opt.structLoop_keeps (H.drv (F0 + Fl)) (F0 + Fl) s.blocks topo0 _ _ hJ
    ((H.drv (F0 + Fl)).topo _ _ hJ (hF0 _ (by omega))) el
  obtain ⟨fa, ba, ea, Ia, la, sa⟩ := H.alias s.nargs bs tp rv Il Jl tRl
  obtain ⟨-, Ja, tRa⟩ := (H.drv 0).alias _ _ _ _ _ _ Jl tRl ea
  obtain ⟨bt, et, It, lt⟩ := H.trim ba (topoF ba tp) _ Ia Ja tRa
  obtain ⟨-, Jt, tRt⟩ := (H.drv 0).trim _ _ _ _ Ja tRa et
  obtain ⟨bd, ed⟩ := Option.isSome_iff_exists.1
    (dead_isSome (bl := bt) (revTopo := (topoF ba tp).reverse) fun o ho => tRt.1.1.2.2.1 o (List.mem_reverse.mp ho))
  obtain ⟨Id, td, ld⟩ := dead_step It tRt.1 ed
  obtain ⟨-, Jd, tRd⟩ := (H.drv 0).dead _ _ _ _ Jt tRt ed
  obtain ⟨Fh, ⟨c1, b1⟩, hFh⟩ := removeHops_stable td Id.acyclic Id.arity
  obtain ⟨I1, l1, s1⟩ := hops_inv_step Id td (hFh Fh (Nat.le_refl _))
  obtain ⟨⟨c2, b2⟩, h2⟩ := Option.isSome_iff_exists.1 (rub_isSome I1.closed I1.two)
  obtain ⟨I2, l2, s2⟩ := rub_inv_step I1 h2
  obtain ⟨Fm, ⟨c3, b3⟩, hFm⟩ := removeEmptyMiddle_stable I2.acyclic I2.closed I2.arity
  obtain ⟨I3, l3, s3⟩ := mid_inv_step I2 (hFm Fm (Nat.le_refl _))
  obtain ⟨-, J1, -⟩ := (H.drv Fh).hops _ _ _ _ _ Jd tRd (hFh Fh (Nat.le_refl _))
  obtain ⟨-, J2, -⟩ := (H.drv 0).rub _ [] HoonMap.empty _ _ J1 h2
  obtain ⟨-, J3, -⟩ := (H.drv Fm).middle _ [] HoonMap.empty _ _ J2 (hFm Fm (Nat.le_refl _))
  have lpost : LexLe (mu ρ L b3) (mu ρ L ba) := lexLe_trans l3 (lexLe_trans l2 (lexLe_trans l1 (lexLe_trans ld lt)))
  refine ⟨F0 + Fl + Fh + Fm, (fa || c1 || c2 || c3, Opt.withBlocks s b3), fun fuel hf => ?_⟩
  obtain ⟨el', -⟩ := hFl fuel fuel (by omega) (by omega)
  refine ⟨?_, I3, J3, lexLe_trans lpost (lexLe_trans la ll), fun hc => ?_, rfl⟩
  · simp only [Opt.optimizeOnce, hF0 fuel (by omega), Option.bind_some, el', ea]
    simp only [topoF] at et ed hFh
    simp only [et, Option.bind_some, ed, hFh fuel (by omega), h2, hFm fuel (by omega), Option.map_some]
  · simp only [Bool.or_eq_true] at hc
    rcases hc with ((h | h) | h) | h
    · exact lexLt_of_lt_le (lexLt_of_le_lt lpost (sa h)) ll
    · exact lexLt_of_lt_le (lexLt_of_le_lt (lexLe_trans l3 l2) (lexLt_of_lt_le (s1 h)
        (lexLe_trans ld (lexLe_trans lt la)))) ll
    · exact lexLt_of_lt_le (lexLt_of_le_lt l3 (lexLt_of_lt_le (s2 h)
        (lexLe_trans l1 (lexLe_trans ld (lexLe_trans lt la))))) ll
    · exact lexLt_of_lt_le (lexLt_of_lt_le (s3 h)
        (lexLe_trans l2 (lexLe_trans l1 (lexLe_trans ld (lexLe_trans lt la))))) ll

/-- **The loop of `+optimize` returns**, past a bound on the fuel and the
count. -/
theorem optLoop_total (H : PassTotal P ρ L J) : ∀ (s : Straight Map), StInv ρ L s.blocks → J s.blocks →
    ∃ F r, ∀ fuel n, F ≤ fuel → F ≤ n → Opt.optLoop fuel P n s = some r ∧ StInv ρ L r.blocks ∧ J r.blocks := by
  suffices K : ∀ x (s : Straight Map), mu ρ L s.blocks = x → StInv ρ L s.blocks → J s.blocks →
      ∃ F r, ∀ fuel n, F ≤ fuel → F ≤ n → Opt.optLoop fuel P n s = some r ∧ StInv ρ L r.blocks ∧ J r.blocks from
    fun s => K _ s rfl
  refine lex_induction _ fun x ih s hx hI hJ => ?_
  obtain ⟨F1, ⟨c, s1⟩, hF1⟩ := optimizeOnce_total H s hI hJ
  obtain ⟨e1, I1, J1, -, lt1, -⟩ := hF1 F1 (Nat.le_refl _)
  cases c with
  | false =>
    refine ⟨F1 + 1, s1, fun fuel n hf hn => ⟨?_, I1, J1⟩⟩
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [Opt.optLoop, (hF1 fuel (by omega)).1, Option.bind_some, Bool.false_eq_true, if_false]
  | true =>
    obtain ⟨F2, r, hF2⟩ := ih _ (hx ▸ lt1 rfl) s1 rfl I1 J1
    refine ⟨F1 + F2 + 1, r, fun fuel n hf hn => ?_⟩
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨e2, I2, J2⟩ := hF2 fuel n' (by omega) (by omega)
    refine ⟨?_, I2, J2⟩
    simp only [Opt.optLoop, (hF1 fuel (by omega)).1, Option.bind_some, if_true, e2]

/-- **`+optimize` returns** on blocks with `StInv` and `J`, given
`PassTotal`, with a result that does not depend on the fuel past a bound. -/
theorem optimizeF_total (H : PassTotal P ρ L J) (s : Straight Map) (hI : StInv ρ L s.blocks) (hJ : J s.blocks) :
    ∃ F s', ∀ fuel, F ≤ fuel → Opt.optimizeF fuel P s = some s' := by
  obtain ⟨F, r, hF⟩ := optLoop_total H s hI hJ
  obtain ⟨-, Ir, Jr⟩ := hF F F (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.1 (H.switch r.blocks Ir Jr)
  refine ⟨F, Opt.withBlocks r bs, fun fuel hf => ?_⟩
  simp only [Opt.optimizeF, (hF fuel fuel hf hf).1, Option.bind_some, hbs, Option.map_some]

theorem optHalts_of (H : PassTotal P ρ L J) (s : Straight Map) (hI : StInv ρ L s.blocks) (hJ : J s.blocks) :
    Opt.OptHalts P s := by
  obtain ⟨F, s', hF⟩ := optimizeF_total H s hI hJ
  exact ⟨F, by rw [hF F (Nat.le_refl _)]; rfl⟩

end

end Compiler
end Formalization
