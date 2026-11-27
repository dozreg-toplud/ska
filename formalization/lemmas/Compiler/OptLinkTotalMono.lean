import lemmas.Compiler.OptLinkFuel

/-!
# The fuelled passes are monotone in the fuel

The models of `+bb-topo`, `+remove-hops` and `+remove-empty-middle` take fuel
where the Hoon has none.  A result found with some fuel is found with any
more fuel (`dfs_mono`, `hopChain_mono`, `rewriteJump_mono`, `rewriteHop_mono`,
and the passes `bbTopo_mono`, `removeHops_mono`, `removeEmptyMiddle_mono`).
So the converses of `OptLinkFuel.lean` give a result that does not depend on
the fuel past a bound (`bbTopo_stable`, `removeHops_stable`,
`removeEmptyMiddle_stable`): what a loop of the driver needs, since the
driver runs every pass and every loop with the same fuel.
-/

namespace Formalization
namespace Compiler

open Nock SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

section
variable {Map : Type → Type} [HoonMap Map]

/-- A fuelled function is monotone: what it returns with some fuel it returns
with more. -/
def FuelMono {α : Type} (f : Nat → Option α) : Prop := ∀ n m r, n ≤ m → f n = some r → f m = some r

/-- A monotone function that returns past a bound returns one value past it. -/
theorem stable_of_mono {α : Type} {f : Nat → Option α} (hm : FuelMono f) (h : ∃ F, ∀ n, F ≤ n → (f n).isSome) :
    ∃ F r, ∀ n, F ≤ n → f n = some r := by
  obtain ⟨F, hF⟩ := h
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (hF F (Nat.le_refl _))
  exact ⟨F, r, fun n hn => hm F n r hn hr⟩

theorem foldlM_mono {α σ : Type} (g g' : σ → α → Option σ) :
    ∀ (l : List α) (s r : σ), (∀ x ∈ l, ∀ s r, g s x = some r → g' s x = some r) →
      l.foldlM g s = some r → l.foldlM g' s = some r
  | [], s, r, _, h => h
  | x :: l, s, r, hg, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨s1, h1, h⟩ := Option.bind_eq_some_iff.1 h
    simp only [List.foldlM_cons, hg x (by simp) s s1 h1, Option.bind_some]
    exact foldlM_mono g g' l s1 r (fun y hy => hg y (by simp [hy])) h

theorem foldl_bind_none {α σ : Type} (g : σ → α → Option σ) :
    ∀ l : List α, l.foldl (fun acc x => acc.bind fun s => g s x) none = none
  | [] => rfl
  | _ :: l => by simp only [List.foldl_cons, Option.bind_none]; exact foldl_bind_none g l

theorem foldl_bind_mono {α σ : Type} (g g' : σ → α → Option σ) :
    ∀ (l : List α) (s r : σ), (∀ x ∈ l, ∀ s r, g s x = some r → g' s x = some r) →
      l.foldl (fun acc x => acc.bind fun s => g s x) (some s) = some r →
      l.foldl (fun acc x => acc.bind fun s => g' s x) (some s) = some r
  | [], s, r, _, h => h
  | x :: l, s, r, hg, h => by
    simp only [List.foldl_cons, Option.bind_some] at h ⊢
    cases e : g s x with
    | none => rw [e, foldl_bind_none] at h; cases h
    | some s1 =>
      rw [e] at h
      rw [hg x (by simp) s s1 e]
      exact foldl_bind_mono g g' l s1 r (fun y hy => hg y (by simp [hy])) h

theorem dfs_mono (bl : Map Blob) : ∀ (n m o : Nat) (acc r : List Nat × List Nat), n ≤ m →
    Opt.dfs bl n o acc = some r → Opt.dfs bl m o acc = some r
  | 0, _, _, _, _, _, h => by simp [Opt.dfs] at h
  | n + 1, 0, _, _, _, hn, _ => by omega
  | n + 1, m + 1, o, (out, saw), r, hn, h => by
    simp only [Opt.dfs] at h ⊢
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.1 h
    rw [hb, Option.bind_some]
    obtain ⟨r1, h1, rfl⟩ := Option.map_eq_some_iff.1 h
    refine Option.map_eq_some_iff.2 ⟨r1, ?_, rfl⟩
    refine foldlM_mono _ _ _ _ _ (fun j _ acc r2 h2 => ?_) h1
    by_cases hj : j.there ∈ acc.2
    · simp only [hj, if_true] at h2 ⊢; exact h2
    · simp only [hj, if_false] at h2 ⊢; exact dfs_mono bl n m j.there acc r2 (by omega) h2

theorem bbTopo_mono (bl : Map Blob) : FuelMono fun n => Opt.bbTopo n bl := by
  intro n m r hn h
  simp only [Opt.bbTopo, Option.map_eq_some_iff] at h ⊢
  obtain ⟨r1, h1, e⟩ := h
  exact ⟨r1, dfs_mono bl n m 0 _ r1 hn h1, e⟩

theorem hopChain_mono (bl : Map Blob) (rev : Map (List Nat)) : ∀ (n m o : Nat) (bnew : Blob)
    (segs : List (List Pole)) (saw : List Nat) (r : Blob × List Nat), n ≤ m →
    Opt.hopChain bl rev n o bnew segs saw = some r → Opt.hopChain bl rev m o bnew segs saw = some r
  | 0, _, _, _, _, _, _, _, h => by simp [Opt.hopChain] at h
  | n + 1, 0, _, _, _, _, _, hn, _ => by omega
  | n + 1, m + 1, o, bnew, segs, saw, r, hn, h => by
    simp only [Opt.hopChain] at h ⊢
    cases e : bnew.fin with
    | hop t =>
      simp only [e] at h ⊢
      by_cases h1 : Opt.getJa rev t.there = []
      · simp [h1] at h
      · by_cases h2 : Opt.getJa rev t.there = [o]
        · simp only [h1, h2, if_false, ne_eq, not_true_eq_false] at h ⊢
          obtain ⟨b1, hb1, h⟩ := Option.bind_eq_some_iff.1 h
          obtain ⟨seg, hseg, h⟩ := Option.bind_eq_some_iff.1 h
          rw [hb1, Option.bind_some, hseg, Option.bind_some]
          exact hopChain_mono bl rev n m _ _ _ _ r (by omega) h
        · simp only [h1, h2, if_false, ne_eq, not_false_eq_true, if_true] at h ⊢; exact h
    | _ => simp only [e] at h ⊢; exact h

theorem removeHops_mono (bl : Map Blob) (rev : Map (List Nat)) (topo : List Nat) :
    FuelMono fun n => Opt.removeHops n bl rev topo := by
  intro n m r hn h
  simp only [Opt.removeHops, Option.map_eq_some_iff] at h ⊢
  obtain ⟨r1, h1, e⟩ := h
  refine ⟨r1, foldlM_mono _ _ _ _ _ (fun o _ acc r2 h2 => ?_) h1, e⟩
  simp only [Opt.hopsStep] at h2 ⊢
  by_cases ho : o ∈ acc.2
  · simp only [ho, if_true] at h2 ⊢; exact h2
  · simp only [ho, if_false] at h2 ⊢
    obtain ⟨b, hb, h2⟩ := Option.bind_eq_some_iff.1 h2
    rw [hb, Option.bind_some]
    obtain ⟨r3, h3, e3⟩ := Option.map_eq_some_iff.1 h2
    exact Option.map_eq_some_iff.2 ⟨r3, hopChain_mono bl rev n m o b [] acc.2 r3 hn h3, e3⟩

theorem rewriteJump_mono (bl : Map Blob) : ∀ (n m : Nat) (j r : Jmp), n ≤ m →
    Opt.rewriteJump bl n j = some r → Opt.rewriteJump bl m j = some r
  | 0, _, _, _, _, h => by simp [Opt.rewriteJump] at h
  | n + 1, 0, _, _, hn, _ => by omega
  | n + 1, m + 1, j, r, hn, h => by
    simp only [Opt.rewriteJump] at h ⊢
    by_cases ha : j.args = []
    · simp only [ha, ne_eq, not_true_eq_false, if_false] at h ⊢
      obtain ⟨nex, hnex, h⟩ := Option.bind_eq_some_iff.1 h
      rw [hnex, Option.bind_some]
      by_cases hp : nex.par = []
      · by_cases hb : nex.body = []
        · simp only [hp, hb, ne_eq, not_true_eq_false, if_false] at h ⊢
          cases e : nex.fin with
          | hop t =>
            simp only [e] at h ⊢
            by_cases hta : t.args = []
            · simp only [hta, ne_eq, not_true_eq_false, if_false] at h ⊢
              exact rewriteJump_mono bl n m t r (by omega) h
            · simp only [hta, ne_eq, not_false_eq_true, if_true] at h ⊢; exact h
          | _ => simp only [e] at h ⊢; exact h
        · simp only [hp, hb, ne_eq, not_true_eq_false, not_false_eq_true, if_false, if_true] at h ⊢; exact h
      · simp [hp] at h
    · simp only [ha, ne_eq, not_false_eq_true, if_true] at h ⊢; exact h

theorem rewriteHop_mono (bl : Map Blob) (rd : Nat → List Nat) : ∀ (n m : Nat) (j r : Jmp), n ≤ m →
    Opt.rewriteHop bl rd n j = some r → Opt.rewriteHop bl rd m j = some r
  | 0, _, _, _, _, h => by simp [Opt.rewriteHop] at h
  | n + 1, 0, _, _, hn, _ => by omega
  | n + 1, m + 1, j, r, hn, h => by
    simp only [Opt.rewriteHop] at h ⊢
    obtain ⟨nex, hnex, h⟩ := Option.bind_eq_some_iff.1 h
    rw [hnex, Option.bind_some]
    by_cases hb : nex.body = []
    · simp only [hb, ne_eq, not_true_eq_false, if_false] at h ⊢
      cases e : nex.fin with
      | hop t =>
        simp only [e] at h ⊢
        by_cases hp : (nex.par.all fun p => (rd p).all (· = j.there)) = true
        · simp only [hp, Bool.not_true, Bool.false_eq_true, if_false] at h ⊢
          obtain ⟨s, hs, h⟩ := Option.bind_eq_some_iff.1 h
          rw [hs, Option.bind_some]
          exact rewriteHop_mono bl rd n m _ r (by omega) h
        · simp only [Bool.not_eq_true] at hp
          simp only [hp, Bool.not_false, if_true] at h ⊢; exact h
      | _ => simp only [e] at h ⊢; exact h
    · simp only [hb, ne_eq, not_false_eq_true, if_true] at h ⊢; exact h

theorem middleFin_mono (bl : Map Blob) (rd : Nat → List Nat) (n m : Nat) (f f' : Termin) (hn : n ≤ m)
    (h : Opt.middleFin bl rd n f = some f') : Opt.middleFin bl rd m f = some f' := by
  cases f with
  | clq s z o | eqq _ s z o | brn s z o | brz s z o =>
    simp only [Opt.middleFin, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
    obtain ⟨z', hz, o', ho, e⟩ := h
    exact ⟨z', rewriteJump_mono bl n m z z' hn hz, o', rewriteJump_mono bl n m o o' hn ho, e⟩
  | hop t =>
    simp only [Opt.middleFin, Option.map_eq_some_iff] at h ⊢
    obtain ⟨t', ht, e⟩ := h
    exact ⟨t', rewriteHop_mono bl rd n m t t' hn ht, e⟩
  | _ => simpa [Opt.middleFin] using h

variable [Opt.MapKeys Map]

theorem removeEmptyMiddle_mono (bl : Map Blob) : FuelMono fun n => Opt.removeEmptyMiddle n bl := by
  intro n m r hn h
  dsimp only at h ⊢
  rw [Opt.removeEmptyMiddle_eq] at h ⊢
  exact foldl_bind_mono (fun acc o => Opt.midStep n bl (some acc) o) (fun acc o => Opt.midStep m bl (some acc) o)
    _ _ _ (fun o _ acc r2 h2 => by
      simp only [Opt.midStep, Option.bind_some] at h2 ⊢
      obtain ⟨b, hb, h2⟩ := Option.bind_eq_some_iff.1 h2
      rw [hb, Option.bind_some]
      obtain ⟨f', hf, e⟩ := Option.map_eq_some_iff.1 h2
      exact Option.map_eq_some_iff.2 ⟨f', middleFin_mono bl _ n m _ _ hn hf, e⟩) h

end

/-! ## Results that do not depend on the fuel past a bound -/

section
variable {Map : Type → Type} [HoonMap Map]

theorem bbTopo_stable {bl : Map Blob} (ha : Opt.Acyclic bl) (hc : Closed bl) (h0 : (HoonMap.get bl 0).isSome) :
    ∃ F t, ∀ fuel, F ≤ fuel → Opt.bbTopo fuel bl = some t :=
  stable_of_mono (bbTopo_mono bl) (bbTopo_some ha hc h0)

theorem removeHops_stable {bl : Map Blob} {topo : List Nat} {rev : Map (List Nat)} (hi : Opt.TopoInv bl topo rev)
    (ha : Opt.Acyclic bl) (har : ArityOK bl) :
    ∃ F r, ∀ fuel, F ≤ fuel → Opt.removeHops fuel bl rev topo = some r :=
  stable_of_mono (removeHops_mono bl rev topo) (removeHops_some hi ha har)

theorem removeEmptyMiddle_stable [Opt.MapKeys Map] {bl : Map Blob} (ha : Opt.Acyclic bl) (hc : Closed bl)
    (har : ArityOK bl) : ∃ F r, ∀ fuel, F ≤ fuel → Opt.removeEmptyMiddle fuel bl = some r :=
  stable_of_mono (removeEmptyMiddle_mono bl) (removeEmptyMiddle_some ha hc har)

end

end Compiler
end Formalization
