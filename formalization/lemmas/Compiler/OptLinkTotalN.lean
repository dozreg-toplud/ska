import lemmas.Compiler.OptLinkTotalWalkStep

/-!
# The converse of `+optimize` at one `N = nargs`

`PassTotal` (`OptLinkTotalOnce.lean`) asks `+alias` to return at every `n`,
which is false (`not_aliasRet`); `AliasRetN` (`aliasRetN_of`) asks
`ReadsIn n` besides.  The driver calls `+alias` at `s.nargs` only, and the
loop keeps `nargs` (`withBlocks`), so here everything is at one `N`:

* `ReadsKeep P N J`: every pass the driver runs keeps `ReadsIn N` on blocks
  with `J` (and `TopoInvR` where the driver gives it);
* `PassTotalN P ρ L N J`: `PassTotal` with the field `alias` at `N` only,
  on blocks with `ReadsIn N`, and `ReadsKeep` as a field;
* `structLoop_reads`, **`optimizeOnce_totalN`**, **`optLoop_totalN`**,
  **`optimizeF_totalN`**: the old proofs, carrying `ReadsIn N` and
  `s.nargs = N`;
* **`passTotalN_of`**: `PassTotalN` at `DInvR` for the passes of the Hoon,
  from `aliasRetN_of` and `switchRet_of`, given `ReadsKeep`;
* **`opt_gate_totalN_of`**: the pill's `+optimize` returns.
-/

namespace Formalization
namespace Compiler

open Nock SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

section
variable {Map : Type → Type} [HoonMap Map] [Opt.MapKeys Map]

/-- **Every pass of the driver keeps `ReadsIn N`** on blocks with `J`, with
`TopoInvR` where the driver has it. -/
structure ReadsKeep (P : Opt.Passes Map) (N : Nat) (J : Map Blob → Prop) : Prop where
  hops : ∀ fuel bl topo rev ch bl', J bl → Opt.TopoInvR bl topo rev → ReadsIn N bl →
    Opt.removeHops fuel bl rev topo = some (ch, bl') → ReadsIn N bl'
  rub : ∀ bl ch bl', J bl → ReadsIn N bl → Opt.removeUselessBranching bl = some (ch, bl') → ReadsIn N bl'
  middle : ∀ fuel bl ch bl', J bl → ReadsIn N bl → Opt.removeEmptyMiddle fuel bl = some (ch, bl') →
    ReadsIn N bl'
  alias : ∀ bl topo rev f bl', J bl → Opt.TopoInvR bl topo rev → ReadsIn N bl →
    P.alias N bl rev topo = some (f, bl') → ReadsIn N bl'
  trim : ∀ bl topo rev bl', J bl → Opt.TopoInvR bl topo rev → ReadsIn N bl → P.trim bl topo rev = some bl' →
    ReadsIn N bl'
  dead : ∀ bl topo rev bl', J bl → Opt.TopoInvR bl topo rev → ReadsIn N bl →
    Opt.removeDeadCode bl topo.reverse = some bl' → ReadsIn N bl'

/-- **`PassTotal` at one `N`**: `+alias` is asked to return at `N` only, on
blocks with `ReadsIn N`, and every pass keeps `ReadsIn N`. -/
structure PassTotalN (P : Opt.Passes Map) (ρ : Nat → Nat) (L : List Nat) (N : Nat) (J : Map Blob → Prop) :
    Prop where
  drv : ∀ fuel, Opt.DriverHyp fuel P J Opt.TopoInvR
  alias : ∀ bl topo rev, StInv ρ L bl → J bl → ReadsIn N bl → Opt.TopoInvR bl topo rev →
    ∃ f bl', P.alias N bl rev topo = some (f, bl') ∧ StInv ρ L bl' ∧
      LexLe (mu ρ L bl') (mu ρ L bl) ∧ (f = true → LexLt (mu ρ L bl') (mu ρ L bl))
  trim : ∀ bl topo rev, StInv ρ L bl → J bl → Opt.TopoInvR bl topo rev →
    ∃ bl', P.trim bl topo rev = some bl' ∧ StInv ρ L bl' ∧ LexLe (mu ρ L bl') (mu ρ L bl)
  switch : ∀ bl, StInv ρ L bl → J bl → (P.switch bl).isSome
  keep : ReadsKeep P N J

variable {P : Opt.Passes Map} {ρ : Nat → Nat} {L : List Nat} {N : Nat} {J : Map Blob → Prop}

/-- The structural loop keeps `ReadsIn N`. -/
theorem structLoop_reads {fuel : Nat} (H : Opt.DriverHyp fuel P J Opt.TopoInvR) (K : ReadsKeep P N J) :
    ∀ (n : Nat) (bl : Map Blob) topo rev r, J bl → Opt.TopoInvR bl topo rev → ReadsIn N bl →
      Opt.structLoop fuel n bl topo rev = some r → ReadsIn N r.2.2
  | 0, _, _, _, _, _, _, _, h => by cases h
  | n + 1, bl, topo, rev, r, hb, hi, hR, h => by
    simp only [Opt.structLoop, Option.bind_eq_some_iff] at h
    obtain ⟨⟨c1, b1⟩, h1, ⟨c2, b2⟩, h2, ⟨c3, b3⟩, h3, h⟩ := h
    obtain ⟨-, j1, -⟩ := H.hops _ _ _ _ _ hb hi h1
    obtain ⟨-, j2, -⟩ := H.rub b1 topo rev _ _ j1 h2
    obtain ⟨-, j3, -⟩ := H.middle b2 topo rev _ _ j2 h3
    have R1 := K.hops _ _ _ _ _ _ hb hi hR h1
    have R2 := K.rub _ _ _ j1 R1 h2
    have R3 := K.middle _ _ _ _ j2 R2 h3
    simp only at h
    by_cases hc : (c1 || c2 || c3) = false
    · simp only [hc, Bool.not_false, if_true, Option.some.injEq] at h
      subst h
      exact R3
    · simp only [Bool.not_eq_false] at hc
      simp only [hc, Bool.not_true, if_false, Bool.false_eq_true] at h
      obtain ⟨topo', ht, h⟩ := Option.bind_eq_some_iff.mp h
      exact structLoop_reads H K n b3 topo' _ r j3 (H.topo _ _ j3 ht) R3 h

/-- **`+optimize-once` returns at `N = nargs`**, past a bound on the fuel,
keeps `StInv`, `J` and `ReadsIn N`, does not raise the measure and lowers it
when it reports a change. -/
theorem optimizeOnce_totalN (H : PassTotalN P ρ L N J) (s : Straight Map) (hN : s.nargs = N)
    (hI : StInv ρ L s.blocks) (hJ : J s.blocks) (hR : ReadsIn N s.blocks) :
    ∃ F r, ∀ fuel, F ≤ fuel → Opt.optimizeOnce fuel P s = some r ∧ StInv ρ L r.2.blocks ∧ J r.2.blocks ∧
      ReadsIn N r.2.blocks ∧
      LexLe (mu ρ L r.2.blocks) (mu ρ L s.blocks) ∧ (r.1 = true → LexLt (mu ρ L r.2.blocks) (mu ρ L s.blocks)) ∧
      r.2 = Opt.withBlocks s r.2.blocks := by
  obtain ⟨F0, topo0, hF0⟩ := bbTopo_stable hI.acyclic hI.closed hI.zero
  have t0 := Opt.topoInv_revCfg (Opt.bbTopo_ok hI.acyclic (hF0 F0 (Nat.le_refl _)))
  obtain ⟨Fl, ⟨tp, rv, bs⟩, hFl⟩ := structLoop_total ρ L s.blocks topo0 _ hI t0
  obtain ⟨el, Il, tl, ll⟩ := hFl (F0 + Fl) (F0 + Fl) (by omega) (by omega)
  have tR0 := (H.drv (F0 + Fl)).topo _ _ hJ (hF0 _ (by omega))
  obtain ⟨-, Jl, tRl⟩ := Opt.structLoop_keeps (H.drv (F0 + Fl)) (F0 + Fl) s.blocks topo0 _ _ hJ tR0 el
  have Rl := structLoop_reads (H.drv (F0 + Fl)) H.keep (F0 + Fl) s.blocks topo0 _ _ hJ tR0 hR el
  obtain ⟨fa, ba, ea, Ia, la, sa⟩ := H.alias bs tp rv Il Jl Rl tRl
  obtain ⟨-, Ja, tRa⟩ := (H.drv 0).alias _ _ _ _ _ _ Jl tRl ea
  have Ra := H.keep.alias _ _ _ _ _ Jl tRl Rl ea
  obtain ⟨bt, et, It, lt⟩ := H.trim ba (topoF ba tp) _ Ia Ja tRa
  obtain ⟨-, Jt, tRt⟩ := (H.drv 0).trim _ _ _ _ Ja tRa et
  have Rt := H.keep.trim _ _ _ _ Ja tRa Ra et
  obtain ⟨bd, ed⟩ := Option.isSome_iff_exists.1
    (dead_isSome (bl := bt) (revTopo := (topoF ba tp).reverse) fun o ho => tRt.1.1.2.2.1 o (List.mem_reverse.mp ho))
  obtain ⟨Id, td, ld⟩ := dead_step It tRt.1 ed
  obtain ⟨-, Jd, tRd⟩ := (H.drv 0).dead _ _ _ _ Jt tRt ed
  have Rd := H.keep.dead _ _ _ _ Jt tRt Rt ed
  obtain ⟨Fh, ⟨c1, b1⟩, hFh⟩ := removeHops_stable td Id.acyclic Id.arity
  obtain ⟨I1, l1, s1⟩ := hops_inv_step Id td (hFh Fh (Nat.le_refl _))
  obtain ⟨⟨c2, b2⟩, h2⟩ := Option.isSome_iff_exists.1 (rub_isSome I1.closed I1.two)
  obtain ⟨I2, l2, s2⟩ := rub_inv_step I1 h2
  obtain ⟨Fm, ⟨c3, b3⟩, hFm⟩ := removeEmptyMiddle_stable I2.acyclic I2.closed I2.arity
  obtain ⟨I3, l3, s3⟩ := mid_inv_step I2 (hFm Fm (Nat.le_refl _))
  obtain ⟨-, J1, -⟩ := (H.drv Fh).hops _ _ _ _ _ Jd tRd (hFh Fh (Nat.le_refl _))
  obtain ⟨-, J2, -⟩ := (H.drv 0).rub _ [] HoonMap.empty _ _ J1 h2
  obtain ⟨-, J3, -⟩ := (H.drv Fm).middle _ [] HoonMap.empty _ _ J2 (hFm Fm (Nat.le_refl _))
  have R1 := H.keep.hops _ _ _ _ _ _ Jd tRd Rd (hFh Fh (Nat.le_refl _))
  have R2 := H.keep.rub _ _ _ J1 R1 h2
  have R3 := H.keep.middle _ _ _ _ J2 R2 (hFm Fm (Nat.le_refl _))
  have lpost : LexLe (mu ρ L b3) (mu ρ L ba) := lexLe_trans l3 (lexLe_trans l2 (lexLe_trans l1 (lexLe_trans ld lt)))
  refine ⟨F0 + Fl + Fh + Fm, (fa || c1 || c2 || c3, Opt.withBlocks s b3), fun fuel hf => ?_⟩
  obtain ⟨el', -⟩ := hFl fuel fuel (by omega) (by omega)
  refine ⟨?_, I3, J3, R3, lexLe_trans lpost (lexLe_trans la ll), fun hc => ?_, rfl⟩
  · subst hN
    simp only [Opt.optimizeOnce, hF0 fuel (by omega), Option.bind_some, el', ea]
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

/-- **The loop of `+optimize` returns at `N = nargs`.** -/
theorem optLoop_totalN (H : PassTotalN P ρ L N J) : ∀ (s : Straight Map), s.nargs = N → StInv ρ L s.blocks →
    J s.blocks → ReadsIn N s.blocks →
    ∃ F r, ∀ fuel n, F ≤ fuel → F ≤ n → Opt.optLoop fuel P n s = some r ∧ StInv ρ L r.blocks ∧ J r.blocks := by
  suffices K : ∀ x (s : Straight Map), mu ρ L s.blocks = x → s.nargs = N → StInv ρ L s.blocks → J s.blocks →
      ReadsIn N s.blocks →
      ∃ F r, ∀ fuel n, F ≤ fuel → F ≤ n → Opt.optLoop fuel P n s = some r ∧ StInv ρ L r.blocks ∧ J r.blocks from
    fun s => K _ s rfl
  refine lex_induction _ fun x ih s hx hN hI hJ hR => ?_
  obtain ⟨F1, ⟨c, s1⟩, hF1⟩ := optimizeOnce_totalN H s hN hI hJ hR
  obtain ⟨e1, I1, J1, R1, -, lt1, ew⟩ := hF1 F1 (Nat.le_refl _)
  have hN1 : s1.nargs = N := by
    have : s1 = Opt.withBlocks s s1.blocks := ew
    rw [this]; exact hN
  cases c with
  | false =>
    refine ⟨F1 + 1, s1, fun fuel n hf hn => ⟨?_, I1, J1⟩⟩
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [Opt.optLoop, (hF1 fuel (by omega)).1, Option.bind_some, Bool.false_eq_true, if_false]
  | true =>
    obtain ⟨F2, r, hF2⟩ := ih _ (hx ▸ lt1 rfl) s1 rfl hN1 I1 J1 R1
    refine ⟨F1 + F2 + 1, r, fun fuel n hf hn => ?_⟩
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨e2, I2, J2⟩ := hF2 fuel n' (by omega) (by omega)
    refine ⟨?_, I2, J2⟩
    simp only [Opt.optLoop, (hF1 fuel (by omega)).1, Option.bind_some, if_true, e2]

/-- **`+optimize` returns at `N = nargs`** on blocks with `StInv`, `J` and
`ReadsIn N`, given `PassTotalN`. -/
theorem optimizeF_totalN (H : PassTotalN P ρ L N J) (s : Straight Map) (hN : s.nargs = N)
    (hI : StInv ρ L s.blocks) (hJ : J s.blocks) (hR : ReadsIn N s.blocks) :
    ∃ F s', ∀ fuel, F ≤ fuel → Opt.optimizeF fuel P s = some s' := by
  obtain ⟨F, r, hF⟩ := optLoop_totalN H s hN hI hJ hR
  obtain ⟨-, Ir, Jr⟩ := hF F F (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.1 (H.switch r.blocks Ir Jr)
  refine ⟨F, Opt.withBlocks r bs, fun fuel hf => ?_⟩
  simp only [Opt.optimizeF, (hF fuel fuel hf hf).1, Option.bind_some, hbs, Option.map_some]

/-- **`PassTotalN` at `DInvR`** for the model of `+alias` (any `pick` that
picks a member), the real `+trim-trace-hints` and the model of
`+switch-chains`, given `SwitchRet` and `ReadsKeep`; `+alias` returns by
`aliasRetN_of`. -/
theorem passTotalN_of {P : Opt.Passes Map} {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l)
    (ha : P.alias = Opt.aliasM pick) (ht : P.trim = Opt.trimTraceHints) {sfuel : Nat}
    (hsw : P.switch = Opt.switchChains sfuel) {ρ : Nat → Nat} {L : List Nat} {N : Nat}
    (hS : SwitchRet (Map := Map) sfuel ρ L) (hK : ReadsKeep P N Opt.DInvR) : PassTotalN P ρ L N Opt.DInvR where
  drv := fun _ => Opt.driverHypR_of hpick ha ht hsw
  alias := fun bl topo rev hI hJ hR hT => by
    obtain ⟨⟨f, bl'⟩, e⟩ := Option.isSome_iff_exists.1 (aliasRetN_of pick hpick ρ L N bl topo rev hI hJ hR hT)
    obtain ⟨I', l', s'⟩ := aliasM_step hI hT e
    exact ⟨f, bl', by rw [ha]; exact e, I', l', s'⟩
  trim := fun bl topo rev hI hJ hT => by
    obtain ⟨bl', e, I', l'⟩ := trim_step (rev := rev) hI hT.1.1
    exact ⟨bl', by rw [ht]; exact e, I', l'⟩
  switch := fun bl hI hJ => by rw [hsw]; exact hS bl hI hJ
  keep := hK

end

/-! ## The total link at `N` -/

open Pill Hoon in
/-- **The pill's `+optimize` returns at `N = nargs`**: for the passes of the
Hoon, on blocks with `StInv ρ L`, `DInvR` and `ReadsIn nargs`, given
`ReadsKeep` at `nargs`, there are fuels and `s'` with `optimizeF` returning
`s'`, and the pill's `+optimize` returns the noun of `s'`. -/
theorem opt_gate_totalN_of {ρ : Nat → Nat} {L : List Nat} (s : Straight (TreapMap mugF))
    (hK : ∀ sfuel, ReadsKeep (Map := TreapMap mugF)
      ⟨Opt.aliasM (Ana.pickR FinMap), Opt.trimTraceHints, Opt.switchChains sfuel⟩ s.nargs Opt.DInvR)
    (hI : StInv ρ L s.blocks) (hJ : Opt.DInvR s.blocks) (hR : ReadsIn s.nargs s.blocks) :
    ∃ sfuel fuel s', Opt.optimizeF fuel ⟨Opt.aliasM (Ana.pickR FinMap), Opt.trimTraceHints,
      Opt.switchChains sfuel⟩ s = some s' ∧ nock (C optBody (C s.toNoun optC)) optBody = some s'.toNoun := by
  let sfuel := (L.map ρ).foldr max 0 + 1
  have hf : ∀ o ∈ L, ρ o < sfuel := fun o ho => by
    have : ρ o ≤ (L.map ρ).foldr max 0 := by
      clear hK hI hJ hR
      induction L with
      | nil => cases ho
      | cons a l ih =>
        simp only [List.map_cons, List.foldr_cons]
        rcases List.mem_cons.mp ho with rfl | h
        · exact Nat.le_max_left _ _
        · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)
    omega
  have H := passTotalN_of (Map := TreapMap mugF) (fun l hl => Ana.pickR_mem l hl) rfl rfl (sfuel := sfuel) rfl
    (switchRet_of hf) (hK sfuel)
  obtain ⟨F, s', hF⟩ := optimizeF_totalN H s rfl hI hJ hR
  exact ⟨sfuel, F, s', hF F (Nat.le_refl _), opt_gate_alias _ rfl (fun _ _ _ => rfl) sfuel (fun _ => rfl) F s s'
    (noLti_of_opt hJ.2.2.1) (hF F (Nat.le_refl _))⟩

end Compiler
end Formalization
