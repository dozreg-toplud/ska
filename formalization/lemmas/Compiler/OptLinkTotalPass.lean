import lemmas.Compiler.OptLinkTotalGate
import lemmas.Ska.OptAliasPlainDriver

/-!
# What `+alias` and `+trim-trace-hints` owe the converse, where they return

`afin_facts`: the end `+alias` makes of an end (`aliasFin`) has jumps to
targets of the old end with the old number of arguments, its two-way ends
pass no arguments, its weight (`twoW`) and rank sum (`finRk`) are at most the
old ones, and it reports a change only when the weight falls (a fold to a
hop, a `%brn` on a known loob to a `%brz`) or the flag was already set.

**`aliasM_step`**: where the model of `+alias` returns on blocks with
`StInv` and `TopoInvR`, its result has `StInv` with the same rank and list,
a measure no higher, and a lower one when it reports a change (a block it
drops lowers the number of blocks, a fold lowers the weight).

**`trim_step`**: `+trim-trace-hints` returns on `topo` with `TopoOK`
(`trimWalk_isSome`), and keeps `StInv` and the measure (`trim_shape`).

**`passTotal_of`**: `PassTotal` for the passes of the Hoon at `J = DInvR`,
given two named facts still to prove: `AliasRet` (the model of `+alias`
returns on blocks with `StInv`, `DInvR` and `TopoInvR`) and `SwitchRet`
(`+switch-chains` with the fuel `sfuel` returns on blocks with `StInv` and
`DInvR`).
-/

namespace Formalization
namespace Compiler

open Nock SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

section
variable {Map : Type → Type} [HoonMap Map]

/-! ## Pointwise comparisons of the measure -/

theorem mu_le_pw {ρ : Nat → Nat} {L : List Nat} {bl bl' : Map Blob}
    (h : ∀ o ∈ L, presN (HoonMap.get bl' o) ≤ presN (HoonMap.get bl o) ∧
      twoCnt (HoonMap.get bl' o) ≤ twoCnt (HoonMap.get bl o) ∧ rkN ρ (HoonMap.get bl' o) ≤ rkN ρ (HoonMap.get bl o)) :
    LexLe (mu ρ L bl') (mu ρ L bl) := by
  have h1 := sumL_le (L := L) fun o ho => (h o ho).1
  have h2 := sumL_le (L := L) fun o ho => (h o ho).2.1
  have h3 := sumL_le (L := L) fun o ho => (h o ho).2.2
  simp only [LexLe, LexLt, mu, Prod.mk.injEq]
  omega

theorem mu_lt_pw2 {ρ : Nat → Nat} {L : List Nat} {bl bl' : Map Blob}
    (h : ∀ o ∈ L, presN (HoonMap.get bl' o) ≤ presN (HoonMap.get bl o) ∧
      twoCnt (HoonMap.get bl' o) ≤ twoCnt (HoonMap.get bl o)) {x : Nat} (hx : x ∈ L)
    (hlt : twoCnt (HoonMap.get bl' x) < twoCnt (HoonMap.get bl x)) : LexLt (mu ρ L bl') (mu ρ L bl) := by
  have h1 := sumL_le (L := L) fun o ho => (h o ho).1
  have h2 := sumL_lt (L := L) (fun o ho => (h o ho).2) x hx hlt
  simp only [LexLt, mu]
  omega

/-! ## The end `+alias` makes -/

theorem afold_facts {ρ : Nat → Nat} {rev : Nat → List Nat} {o : Nat} {z o' : Jmp} {fin : Termin}
    (hz : z.args = []) (hj : Opt.getJmps fin = [z, o']) (hw : 1 ≤ twoW fin) (go cut : Nat)
    (hg : (go = z.there ∧ cut = o'.there) ∨ (go = o'.there ∧ cut = z.there)) (ho : o'.args = []) :
    let r := Opt.aliasFold rev o go cut
    (∀ j' ∈ Opt.getJmps r.1, ∃ j ∈ Opt.getJmps fin, j.there = j'.there ∧ j'.args.length = j.args.length) ∧
    (twoWay r.1 = true → ∀ j ∈ Opt.getJmps r.1, j.args = []) ∧
    twoW r.1 < twoW fin ∧ finRk ρ r.1 ≤ finRk ρ fin := by
  refine ⟨fun j' hj' => ?_, fun h => by simp [Opt.aliasFold, twoWay] at h, by
    have : twoW (Opt.aliasFold rev o go cut).1 = 0 := rfl
    omega, ?_⟩
  · simp only [Opt.aliasFold, Opt.getJmps, List.mem_singleton] at hj'
    subst hj'
    rw [hj]
    rcases hg with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact ⟨z, by simp, rfl, by simp [hz]⟩
    · exact ⟨o', by simp, rfl, by simp [ho]⟩
  · have e1 : finRk ρ fin = ρ z.there + ρ o'.there := by
      simp only [finRk, hj, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    have e2 : finRk ρ (Opt.aliasFold rev o go cut).1 = ρ go := by simp [finRk, Opt.aliasFold, Opt.getJmps]
    rw [e1, e2]
    rcases hg with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> omega

/-- **The end `+alias` makes.** -/
theorem afin_facts (ρ : Nat → Nat) {old : Nat → Nat} {loc : Opt.AInfo} {rev : Nat → List Nat} {f : Bool} {o : Nat}
    {fin : Termin} {r : Termin × (Nat → List Nat) × Bool} (h : Opt.aliasFin old loc rev f o fin = some r) :
    (∀ j' ∈ Opt.getJmps r.1, ∃ j ∈ Opt.getJmps fin, j.there = j'.there ∧ j'.args.length = j.args.length) ∧
    (twoWay r.1 = true → ∀ j ∈ Opt.getJmps r.1, j.args = []) ∧
    twoW r.1 ≤ twoW fin ∧ finRk ρ r.1 ≤ finRk ρ fin ∧ (r.2.2 = true → f = true ∨ twoW r.1 < twoW fin) := by
  cases fin with
  | clq s z o' =>
    simp only [Opt.aliasFin] at h
    by_cases ha : z.args ≠ [] ∨ o'.args ≠ []
    · simp only [ha, if_true] at h; cases h
    · simp only [ha, if_false] at h
      have hz : z.args = [] := Classical.byContradiction fun e => ha (Or.inl e)
      have ho : o'.args = [] := Classical.byContradiction fun e => ha (Or.inr e)
      obtain ⟨ic, -, rfl⟩ := Option.map_eq_some_iff.mp h
      have hj : Opt.getJmps (Termin.clq s z o') = [z, o'] := rfl
      by_cases c1 : (ic.isCell || ic.cellImm) = true
      · simp only [c1, if_true]
        obtain ⟨a1, a2, a3, a4⟩ := afold_facts (ρ := ρ) (rev := rev) (o := o) hz hj (by simp [twoW]) z.there o'.there
          (Or.inl ⟨rfl, rfl⟩) ho
        exact ⟨a1, a2, Nat.le_of_lt a3, a4, fun _ => Or.inr a3⟩
      · simp only [c1, Bool.false_eq_true, if_false]
        by_cases c2 : (ic.isLoob || ic.atomImm) = true
        · simp only [c2, if_true]
          obtain ⟨a1, a2, a3, a4⟩ := afold_facts (ρ := ρ) (rev := rev) (o := o) hz hj (by simp [twoW]) o'.there z.there
            (Or.inr ⟨rfl, rfl⟩) ho
          exact ⟨a1, a2, Nat.le_of_lt a3, a4, fun _ => Or.inr a3⟩
        · simp only [c2, Bool.false_eq_true, if_false]
          refine ⟨fun j' hj' => ⟨j', hj', rfl, rfl⟩, fun _ j hj => ?_, Nat.le_refl _, Nat.le_refl _, fun e => Or.inl e⟩
          simp only [Opt.getJmps, List.mem_cons, List.not_mem_nil, or_false] at hj
          rcases hj with rfl | rfl <;> assumption
  | eqq l rr z o' =>
    simp only [Opt.aliasFin] at h
    by_cases ha : z.args ≠ [] ∨ o'.args ≠ []
    · simp only [ha, if_true] at h; cases h
    · simp only [ha, if_false] at h
      have hz : z.args = [] := Classical.byContradiction fun e => ha (Or.inl e)
      have ho : o'.args = [] := Classical.byContradiction fun e => ha (Or.inr e)
      have hj : Opt.getJmps (Termin.eqq l rr z o') = [z, o'] := rfl
      by_cases c1 : old l = old rr
      · simp only [c1, ne_eq, not_true_eq_false, if_false, Option.some.injEq] at h
        subst h
        obtain ⟨a1, a2, a3, a4⟩ := afold_facts (ρ := ρ) (rev := rev) (o := o) hz hj (by simp [twoW]) z.there o'.there
          (Or.inl ⟨rfl, rfl⟩) ho
        exact ⟨a1, a2, Nat.le_of_lt a3, a4, fun _ => Or.inr a3⟩
      · simp only [c1, ne_eq, not_false_eq_true, if_true, Option.some.injEq] at h
        subst h
        refine ⟨fun j' hj' => ⟨j', hj', rfl, rfl⟩, fun _ j hj => ?_, Nat.le_refl _, Nat.le_refl _, fun e => Or.inl e⟩
        simp only [Opt.getJmps, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl <;> assumption
  | brn s z o' =>
    simp only [Opt.aliasFin] at h
    by_cases ha : z.args ≠ [] ∨ o'.args ≠ []
    · simp only [ha, if_true] at h; cases h
    · simp only [ha, if_false] at h
      have hz : z.args = [] := Classical.byContradiction fun e => ha (Or.inl e)
      have ho : o'.args = [] := Classical.byContradiction fun e => ha (Or.inr e)
      have hj : Opt.getJmps (Termin.brn s z o') = [z, o'] := rfl
      have hsame : ∀ c, (∀ j' ∈ Opt.getJmps (Termin.brz c z o'), ∃ j ∈ Opt.getJmps (Termin.brn s z o'),
          j.there = j'.there ∧ j'.args.length = j.args.length) ∧
          (twoWay (Termin.brz c z o') = true → ∀ j ∈ Opt.getJmps (Termin.brz c z o'), j.args = []) := by
        intro c
        refine ⟨fun j' hj' => ⟨j', hj', rfl, rfl⟩, fun _ j hj => ?_⟩
        simp only [Opt.getJmps, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl <;> assumption
      have hsame' : ∀ c, (∀ j' ∈ Opt.getJmps (Termin.brn c z o'), ∃ j ∈ Opt.getJmps (Termin.brn s z o'),
          j.there = j'.there ∧ j'.args.length = j.args.length) ∧
          (twoWay (Termin.brn c z o') = true → ∀ j ∈ Opt.getJmps (Termin.brn c z o'), j.args = []) := by
        intro c
        refine ⟨fun j' hj' => ⟨j', hj', rfl, rfl⟩, fun _ j hj => ?_⟩
        simp only [Opt.getJmps, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl <;> assumption
      obtain ⟨ic, -, rfl⟩ := Option.map_eq_some_iff.mp h
      cases hh : ic.hasImm with
      | none =>
        by_cases hl : ic.isLoob = true
        · simp only [hl, if_true]
          exact ⟨(hsame _).1, (hsame _).2, by simp [twoW], by simp [finRk, Opt.getJmps], fun _ => Or.inr (by simp [twoW])⟩
        · simp only [hl, Bool.false_eq_true, if_false]
          exact ⟨(hsame' _).1, (hsame' _).2, Nat.le_refl _, by simp [finRk, Opt.getJmps], fun e => Or.inl e⟩
      | some v =>
        rcases v with (_ | _ | n) | ⟨a, b⟩
        · obtain ⟨a1, a2, a3, a4⟩ := afold_facts (ρ := ρ) (rev := rev) (o := o) hz hj (by simp [twoW]) z.there o'.there
            (Or.inl ⟨rfl, rfl⟩) ho
          exact ⟨a1, a2, Nat.le_of_lt a3, a4, fun _ => Or.inr a3⟩
        · obtain ⟨a1, a2, a3, a4⟩ := afold_facts (ρ := ρ) (rev := rev) (o := o) hz hj (by simp [twoW]) o'.there z.there
            (Or.inr ⟨rfl, rfl⟩) ho
          exact ⟨a1, a2, Nat.le_of_lt a3, a4, fun _ => Or.inr a3⟩
        · refine ⟨fun j' hj' => by simp [Opt.getJmps] at hj', fun h => by simp [twoWay] at h, by simp [twoW],
            by simp [finRk, Opt.getJmps], fun e => Or.inl e⟩
        · refine ⟨fun j' hj' => by simp [Opt.getJmps] at hj', fun h => by simp [twoWay] at h, by simp [twoW],
            by simp [finRk, Opt.getJmps], fun e => Or.inl e⟩
  | brz s z o' =>
    simp only [Opt.aliasFin] at h
    by_cases ha : z.args ≠ [] ∨ o'.args ≠ []
    · simp only [ha, if_true] at h; cases h
    · simp only [ha, if_false] at h
      have hz : z.args = [] := Classical.byContradiction fun e => ha (Or.inl e)
      have ho : o'.args = [] := Classical.byContradiction fun e => ha (Or.inr e)
      have hj : Opt.getJmps (Termin.brz s z o') = [z, o'] := rfl
      obtain ⟨ic, -, rfl⟩ := Option.map_eq_some_iff.mp h
      have hkeep : (∀ j' ∈ Opt.getJmps (Termin.brz (old s) z o'), ∃ j ∈ Opt.getJmps (Termin.brz s z o'),
          j.there = j'.there ∧ j'.args.length = j.args.length) ∧
          (twoWay (Termin.brz (old s) z o') = true → ∀ j ∈ Opt.getJmps (Termin.brz (old s) z o'), j.args = []) := by
        refine ⟨fun j' hj' => ⟨j', hj', rfl, rfl⟩, fun _ j hj => ?_⟩
        simp only [Opt.getJmps, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl <;> assumption
      have F1 := afold_facts (ρ := ρ) (rev := rev) (o := o) hz hj (by simp [twoW]) o'.there z.there
        (Or.inr ⟨rfl, rfl⟩) ho
      have F0 := afold_facts (ρ := ρ) (rev := rev) (o := o) hz hj (by simp [twoW]) z.there o'.there
        (Or.inl ⟨rfl, rfl⟩) ho
      cases hh : ic.hasImm with
      | none =>
        by_cases hc : ic.isCell = true
        · simp only [hc, if_true]
          exact ⟨F1.1, F1.2.1, Nat.le_of_lt F1.2.2.1, F1.2.2.2, fun _ => Or.inr F1.2.2.1⟩
        · simp only [hc, Bool.false_eq_true, if_false]
          exact ⟨hkeep.1, hkeep.2, Nat.le_refl _, by simp [finRk, Opt.getJmps], fun e => Or.inl e⟩
      | some v =>
        by_cases hv : v = Noun.atom 0
        · simp only [hv, decide_true]
          exact ⟨F0.1, F0.2.1, Nat.le_of_lt F0.2.2.1, F0.2.2.2, fun _ => Or.inr F0.2.2.1⟩
        · simp only [hv, decide_false]
          exact ⟨F1.1, F1.2.1, Nat.le_of_lt F1.2.2.1, F1.2.2.2, fun _ => Or.inr F1.2.2.1⟩
  | hop t =>
    simp only [Opt.aliasFin, Option.some.injEq] at h
    subst h
    refine ⟨fun j' hj' => ?_, fun h => by simp [twoWay] at h, Nat.le_refl _, by simp [finRk, Opt.getJmps],
      fun e => Or.inl e⟩
    simp only [Opt.getJmps, List.mem_singleton] at hj'
    subst hj'
    exact ⟨t, by simp [Opt.getJmps], rfl, by simp⟩
  | _ =>
    simp only [Opt.aliasFin, Option.some.injEq] at h
    subst h
    exact ⟨fun j' hj' => ⟨j', hj', rfl, rfl⟩, fun h => by simp [twoWay] at h, Nat.le_refl _,
      by simp [finRk, Opt.getJmps], fun e => Or.inl e⟩

end

section
variable {Map : Type → Type} [HoonMap Map] [Opt.MapKeys Map]

/-! ## The walk of `+alias` -/

/-- **A change of the walk**: the flag was set before, or a block of the walk
was dropped or got an end of lower weight. -/
theorem aw_flag {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} : ∀ (l : List Nat) (g g' : Opt.AGen Map),
    l.Nodup → (∀ o ∈ l, HoonMap.get g.new o = none) → Opt.aliasWalk pick nargs bl l g = some g' →
    g'.folded = true → g.folded = true ∨ ∃ o ∈ l, ∃ b, HoonMap.get bl o = some b ∧
      (HoonMap.get g'.new o = none ∨ ∃ b', HoonMap.get g'.new o = some b' ∧ twoW b'.fin < twoW b.fin)
  | [], g, g', _, _, h, hf => by
    simp only [Opt.aliasWalk, Option.some.injEq] at h; subst h; exact Or.inl hf
  | o :: l, g, g', hnd, hnone, h, hf => by
    simp only [Opt.aliasWalk] at h
    obtain ⟨g1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    have hol : o ∉ l := (List.nodup_cons.mp hnd).1
    have hfr : HoonMap.get g'.new o = HoonMap.get g1.new o := ((Opt.awk_walk l g1 g' h2).2 o hol).2.2
    by_cases hw : g.rev o = [] ∧ o ≠ 0
    · obtain ⟨b, hb, rfl⟩ := Opt.aliasBlock_dropped h1 hw
      exact Or.inr ⟨o, List.mem_cons_self, b, hb, Or.inl (by rw [hfr]; exact hnone o List.mem_cons_self)⟩
    · obtain ⟨b, rb, rf, hb, hrf, rfl⟩ := Opt.aliasBlock_walked h1 hw
      have hnone1 : ∀ x ∈ l, HoonMap.get (HoonMap.put g.new o { par := b.par, body := rb.1, fin := rf.1 }) x = none := by
        intro x hx
        have hxo : x ≠ o := fun e => hol (e ▸ hx)
        rw [HoonMap.get_put, if_neg hxo]
        exact hnone x (List.mem_cons_of_mem _ hx)
      rcases aw_flag l _ g' (List.nodup_cons.mp hnd).2 hnone1 h2 hf with h0 | ⟨x, hx, b2, hb2, hh⟩
      · rcases (afin_facts (fun _ => 0) hrf).2.2.2.2 h0 with h0 | h0
        · exact Or.inl h0
        · refine Or.inr ⟨o, List.mem_cons_self, b, hb, Or.inr ⟨{ par := b.par, body := rb.1, fin := rf.1 }, ?_, h0⟩⟩
          rw [hfr]; simp [HoonMap.get_put]
      · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, b2, hb2, hh⟩

theorem alias_zero {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} {topo : List Nat} {rev : Map (List Nat)}
    {g : Opt.AGen Map} (hT : Opt.TopoInvR bl topo rev)
    (h : Opt.aliasWalk pick nargs bl topo (Opt.aliasInit rev) = some g) : (HoonMap.get g.new 0).isSome := by
  have ht := hT.1.1
  have h0 : 0 ∈ topo := List.mem_of_mem_head? ht.2.1
  obtain ⟨pre, l, g1, g2, hto, h1, h2, h3⟩ := Opt.alias_start_parts (c := ⟨NeedOrd.none, 0, bl⟩) h h0
  have hnd := ht.1
  rw [hto] at hnd
  have hol : 0 ∉ l := fun h' => ((List.nodup_append.mp hnd).2.1 |> List.nodup_cons.mp).1 h'
  obtain ⟨b, rb, rf, hb, hrf, rfl⟩ := Opt.aliasBlock_walked h2 (fun hw => hw.2 rfl)
  rw [((Opt.awk_walk l _ g h3).2 0 hol).2.2]
  simp [HoonMap.get_put]

/-- **The model of `+alias` keeps `StInv` and lowers the measure when it
reports a change**, where it returns. -/
theorem aliasM_step {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} {topo : List Nat} {rev : Map (List Nat)}
    {f : Bool} {bl' : Map Blob} {ρ : Nat → Nat} {L : List Nat} (hI : StInv ρ L bl) (hT : Opt.TopoInvR bl topo rev)
    (h : Opt.aliasM pick nargs bl rev topo = some (f, bl')) :
    StInv ρ L bl' ∧ LexLe (mu ρ L bl') (mu ρ L bl) ∧ (f = true → LexLt (mu ρ L bl') (mu ρ L bl)) := by
  unfold Opt.aliasM at h
  obtain ⟨g, hg, he⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hg' : Opt.aliasWalk pick nargs bl topo (Opt.aliasInit rev) = some g := hg
  have hsh : ∀ o b', HoonMap.get g.new o = some b' → ∃ b, HoonMap.get bl o = some b ∧ b'.par = b.par ∧
      (∀ j' ∈ Opt.getJmps b'.fin, ∃ j ∈ Opt.getJmps b.fin, j.there = j'.there ∧ j'.args.length = j.args.length) ∧
      (twoWay b'.fin = true → ∀ j ∈ Opt.getJmps b'.fin, j.args = []) ∧
      twoW b'.fin ≤ twoW b.fin ∧ finRk ρ b'.fin ≤ finRk ρ b.fin := by
    intro o b' hb'
    obtain ⟨_pre, _l, _g1, _g2, b, _st0, rb, rf, -, -, -, -, -, hb, -, -, hrf, -, rfl⟩ := Opt.aw_new hT.1.1 hT.2 hg' hb'
    obtain ⟨a1, a2, a3, a4, -⟩ := afin_facts ρ hrf
    exact ⟨b, hb, rfl, a1, a2, a3, a4⟩
  have hpw : ∀ o, presN (HoonMap.get g.new o) ≤ presN (HoonMap.get bl o) ∧
      twoCnt (HoonMap.get g.new o) ≤ twoCnt (HoonMap.get bl o) ∧ rkN ρ (HoonMap.get g.new o) ≤ rkN ρ (HoonMap.get bl o) := by
    intro o
    cases e1 : HoonMap.get g.new o with
    | none => simp [presN, twoCnt, rkN]
    | some b' =>
      obtain ⟨b, hb, -, -, -, k3, k4⟩ := hsh o b' e1
      rw [hb]; exact ⟨Nat.le_refl _, k3, k4⟩
  refine ⟨⟨rank_sub hI.rank (Opt.alias_targetsSub hT hg'), fun o b' j' hb' hj' => Opt.alias_closed hT hg' hb' hj',
    fun o b' j' b2' hb' hj' hb2' => ?_, alias_zero hT hg', fun o b' j' hb' ht hj' => by
      obtain ⟨_, _, _, _, k2, _⟩ := hsh o b' hb'; exact k2 ht j' hj',
    fun o ho => ?_⟩, mu_le_pw fun o _ => hpw o, fun hf => ?_⟩
  · obtain ⟨b, hb, -, k1, -⟩ := hsh o b' hb'
    obtain ⟨j, hj, e1, e2⟩ := k1 j' hj'
    obtain ⟨b2, hb2, e3, -⟩ := hsh _ b2' hb2'
    rw [e2, e3]
    exact hI.arity o b j b2 hb hj (by rw [e1]; exact hb2)
  · obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 ho
    obtain ⟨b, hb, -⟩ := hsh o b' hb'
    exact hI.keys o (by simp [hb])
  · rcases aw_flag topo (Opt.aliasInit rev) g hT.1.1.1 (fun o _ => by simp [Opt.aliasInit, HoonMap.get_empty]) hg' hf with
      h0 | ⟨o, -, b, hb, hh⟩
    · simp [Opt.aliasInit] at h0
    · have hoL := hI.keys o (by simp [hb])
      rcases hh with hh | ⟨b', hb', hlt⟩
      · exact mu_lt1 (fun o _ => (hpw o).1) hoL (by simp [hh, hb, presN])
      · exact mu_lt_pw2 (fun o _ => ⟨(hpw o).1, (hpw o).2.1⟩) hoL (by simp [hb', hb, twoCnt, hlt])

/-! ## `+trim-trace-hints` -/

theorem trimWalk_isSome {bl : Map Blob} {rev : Map (List Nat)} : ∀ (topo : List Nat) (out : Map Opt.Cnt) (uns : Opt.Uns),
    (∀ o ∈ topo, (HoonMap.get bl o).isSome) → (Opt.trimWalk bl rev topo out uns).isSome
  | [], _, _, _ => rfl
  | o :: t, out, uns, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (h o List.mem_cons_self)
    simp only [Opt.trimWalk, hb, Option.bind_some]
    exact trimWalk_isSome t _ _ fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- A pass that keeps the parameters and the end of every block, and the
labels, keeps `StInv` and the measure. -/
theorem stInv_shape {ρ : Nat → Nat} {L : List Nat} {bl bl' : Map Blob} (hI : StInv ρ L bl) (hs : Opt.SameShape bl bl')
    (hk : ∀ k, (HoonMap.get bl' k).isSome = (HoonMap.get bl k).isSome) : StInv ρ L bl' ∧ mu ρ L bl' = mu ρ L bl := by
  have hsub : Opt.TargetsSub bl bl' := fun k b' hb' => by
    obtain ⟨b, hb, -, hfin⟩ := hs k b' hb'
    exact ⟨b, hb, fun j' hj' => ⟨j', by rw [← hfin]; exact hj', rfl⟩⟩
  refine ⟨⟨rank_sub hI.rank hsub, fun o b' j hb' hj => ?_, fun o b' j b2' hb' hj hb2' => ?_, by rw [hk]; exact hI.zero,
    fun o b' j hb' ht hj => ?_, fun o ho => hI.keys o (by rw [← hk]; exact ho)⟩, mu_eq fun o _ => ?_⟩
  · obtain ⟨b, hb, -, hfin⟩ := hs o b' hb'
    rw [hfin] at hj; rw [hk]; exact hI.closed o b j hb hj
  · obtain ⟨b, hb, -, hfin⟩ := hs o b' hb'
    obtain ⟨b2, hb2, hpar, -⟩ := hs j.there b2' hb2'
    rw [hfin] at hj; rw [hpar]
    exact hI.arity o b j b2 hb hj hb2
  · obtain ⟨b, hb, -, hfin⟩ := hs o b' hb'
    rw [hfin] at ht hj
    exact hI.two o b j hb ht hj
  · cases e1 : HoonMap.get bl' o with
    | none =>
      have : HoonMap.get bl o = none := by
        have := hk o; rw [e1] at this
        cases e2 : HoonMap.get bl o with
        | none => rfl
        | some _ => rw [e2] at this; cases this
      rw [this]; exact ⟨rfl, rfl, rfl⟩
    | some b' =>
      obtain ⟨b, hb, -, hfin⟩ := hs o b' e1
      rw [hb]; simp [presN, twoCnt, rkN, hfin]

/-- **`+trim-trace-hints` returns** on a `topo` with `TopoOK`, keeps `StInv`
and the measure. -/
theorem trim_step {ρ : Nat → Nat} {L : List Nat} {bl : Map Blob} {topo : List Nat} {rev : Map (List Nat)}
    (hI : StInv ρ L bl) (ht : Opt.TopoOK bl topo) :
    ∃ bl', Opt.trimTraceHints bl topo rev = some bl' ∧ StInv ρ L bl' ∧ LexLe (mu ρ L bl') (mu ρ L bl) := by
  obtain ⟨uns, hu⟩ := Option.isSome_iff_exists.1
    (trimWalk_isSome (rev := rev) topo HoonMap.empty (fun _ => false) ht.2.2.1)
  have e : Opt.trimTraceHints bl topo rev = some (Opt.trimRun bl uns (Opt.trimOpened bl)) := by
    simp only [Opt.trimTraceHints, hu, Option.map_some]
  obtain ⟨hs, hk⟩ := Opt.trim_shape e
  obtain ⟨I', m'⟩ := stInv_shape hI hs hk
  exact ⟨_, e, I', Or.inr m'⟩

/-! ## The input -/

/-- **`StInv` from what the input owes**: an acyclic CFG (a field of
`OptIn`), `Closed`, `ArityOK`, a block `0` and `TwoNA`, with the keys of the
map as the list. -/
theorem stInv_of {bl : Map Blob} (ha : Opt.Acyclic bl) (hc : Closed bl) (har : ArityOK bl)
    (h0 : (HoonMap.get bl 0).isSome) (h2 : TwoNA bl) : ∃ ρ, StInv ρ (Opt.MapKeys.keys bl) bl := by
  obtain ⟨ρ, hr⟩ := ha
  exact ⟨ρ, ⟨hr, hc, har, h0, h2, fun o ho => (Opt.MapKeys.mem_keys bl o).2 ho⟩⟩

/-! ## `PassTotal` for the passes of the Hoon -/

/-- **`+alias` returns** (open): the model returns on blocks with `StInv`,
`DInvR` and `TopoInvR`. -/
def AliasRet (pick : List Nat → Nat) (ρ : Nat → Nat) (L : List Nat) : Prop :=
  ∀ n (bl : Map Blob) topo rev, StInv ρ L bl → Opt.DInvR bl → Opt.TopoInvR bl topo rev →
    (Opt.aliasM pick n bl rev topo).isSome

/-- **`+switch-chains` returns** with the fuel `sfuel` (open). -/
def SwitchRet (sfuel : Nat) (ρ : Nat → Nat) (L : List Nat) : Prop :=
  ∀ bl : Map Blob, StInv ρ L bl → Opt.DInvR bl → (Opt.switchChains sfuel bl).isSome

/-- **`PassTotal` at `DInvR`** for the model of `+alias` (any `pick` that
picks a member), the real `+trim-trace-hints` and the model of
`+switch-chains`, given `AliasRet` and `SwitchRet`. -/
theorem passTotal_of {P : Opt.Passes Map} {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l)
    (ha : P.alias = Opt.aliasM pick) (ht : P.trim = Opt.trimTraceHints) {sfuel : Nat}
    (hsw : P.switch = Opt.switchChains sfuel) {ρ : Nat → Nat} {L : List Nat}
    (hA : AliasRet (Map := Map) pick ρ L) (hS : SwitchRet (Map := Map) sfuel ρ L) : PassTotal P ρ L Opt.DInvR where
  drv := fun _ => Opt.driverHypR_of hpick ha ht hsw
  alias := fun n bl topo rev hI hJ hT => by
    obtain ⟨⟨f, bl'⟩, e⟩ := Option.isSome_iff_exists.1 (hA n bl topo rev hI hJ hT)
    obtain ⟨I', l', s'⟩ := aliasM_step hI hT e
    exact ⟨f, bl', by rw [ha]; exact e, I', l', s'⟩
  trim := fun bl topo rev hI hJ hT => by
    obtain ⟨bl', e, I', l'⟩ := trim_step (rev := rev) hI hT.1.1
    exact ⟨bl', by rw [ht]; exact e, I', l'⟩
  switch := fun bl hI hJ => by rw [hsw]; exact hS bl hI hJ

end

/-! ## The total link -/

open Pill Hoon in
/-- **The link of `+optimize` where `+alias` and `+switch-chains` return**:
for the passes of the Hoon, on blocks with `StInv ρ L` and `DInvR`, given
`AliasRet` and `SwitchRet` (the only conditions left on the model), there are
a fuel and `s'` with `optimizeF fuel P s = some s'`, and the pill's
`+optimize` returns the noun of `s'`. -/
theorem opt_gate_total (sfuel : Nat) {ρ : Nat → Nat} {L : List Nat}
    (hA : AliasRet (Map := TreapMap mugF) (Ana.pickR FinMap) ρ L) (hS : SwitchRet (Map := TreapMap mugF) sfuel ρ L)
    (s : Straight (TreapMap mugF)) (hI : StInv ρ L s.blocks) (hJ : Opt.DInvR s.blocks) :
    ∃ fuel s', Opt.optimizeF fuel ⟨Opt.aliasM (Ana.pickR FinMap), Opt.trimTraceHints, Opt.switchChains sfuel⟩ s =
      some s' ∧ nock (C optBody (C s.toNoun optC)) optBody = some s'.toNoun :=
  opt_gate_total_of ⟨Opt.aliasM (Ana.pickR FinMap), Opt.trimTraceHints, Opt.switchChains sfuel⟩ rfl
    (fun _ _ _ => rfl) sfuel (fun _ => rfl)
    (passTotal_of (fun l hl => Ana.pickR_mem l hl) rfl rfl rfl hA hS) s hI hJ (noLti_of_opt hJ.2.2.1)

end Compiler
end Formalization
