import lemmas.Ska.CompPairLS

/-!
# The hypothesis `LOKS` and its leaves: `[0 axe]`

README Gaps 12.24.  `LOKS x` is the hypothesis of the induction over the
plain class under a lazy goal: from a state as `LOKB` asks it, under a FLAT
goal with clean entries, every run meets `RunOKLS` (`RunOKLB` with the
fronts at the state level, `CompFrontS.lean`), its jump is the goal's or a
block it made and at none of its entries, and its result is flat with clean
entries.

* `LOKS`, `LOKS.toB` (`LOKB` on flat goals).
* `fromBonds_flat`, `fromL_flat`: `+from` of a flat need is flat, entry by
  entry.
* `lokS_n0`: `[0 axe]` for every `axe ≥ 1` (`[0 1]` keeps the goal, the
  others `+from` it; no op at any entry: `F = []`, the result entry is the
  goal entry seen at `axe`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The hypothesis under a flat lazy goal**: `LOKB` with `RunOKLS`, flat
goals and results with clean entries, and the run's jump the goal's or a
block it made. -/
structure LOKS (x : Bool) (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop) (f : Noun) (nm : Nomm) : Prop where
  clean : ∀ {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    Clean L.sure.ned → runLC env sup nm (CGoalL.next L th) region g0 = some (nex, g1) → Clean nex.laz.sure.ned
  run : ∀ {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    1 ≤ th.there → th.there < g0.bo → th.args = [] → th.there ∉ (entries L).map Prod.fst → Distinct L.sure.ned →
    (∀ x, NMem L.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) →
    (∀ e ∈ entries L, e.1 < g0.bo ∧ ∃ B th', HoonMap.get g0.blocks e.1 = some ⟨[], B, Termin.hop th'⟩) →
    ((entries L).map Prod.fst).Nodup →
    (∀ e ∈ entries L, Distinct e.2.sure.ned ∧
      ∀ x, NMem e.2.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) →
    Flat L → Clean L.sure.ned → (∀ e ∈ entries L, Clean e.2.sure.ned) →
    runLC env sup nm (CGoalL.next L th) region g0 = some (nex, g1) →
    (∃ Q, RunOKLS (Map := Map) lib N P f L th Q x g0 g1 nex) ∧ nex.th.there ∉ (entries nex.laz).map Prod.fst ∧
      (nex.th = th ∨ g0.bo ≤ nex.th.there) ∧ Flat nex.laz ∧ (∀ e ∈ entries nex.laz, Clean e.2.sure.ned)

/-! ## `+from` of a flat need -/

theorem fromBonds_flat (axe : Nat) : ∀ (b b' : List (Nat × Lazy S)), FlatB b → fromBonds axe b = some b' →
    b'.map Prod.fst = b.map Prod.fst ∧ FlatB b' ∧
    ∀ e ∈ b, ∃ s', fromSure axe e.2.sure = some s' ∧ (e.1, ofSure s') ∈ b'
  | [], b', _, h => by
    simp only [fromBonds, Option.some.injEq] at h
    subst h
    exact ⟨rfl, flatB_nil, fun e he => by cases he⟩
  | (o, l) :: rest, b', hf, h => by
    have el : l = ofSure l.sure := hf (o, l) List.mem_cons_self
    simp only [fromBonds] at h
    obtain ⟨l', h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r, h2, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [el, fromL_ofSure] at h1
    obtain ⟨s', h3, rfl⟩ := Option.map_eq_some_iff.mp h1
    obtain ⟨e1, f1, m1⟩ := fromBonds_flat axe rest r (fun e he => hf e (List.mem_cons_of_mem _ he)) h2
    refine ⟨by simp [e1], fun e he => ?_, fun e he => ?_⟩
    · rcases List.mem_cons.mp he with rfl | he
      · rfl
      · exact f1 e he
    · rcases List.mem_cons.mp he with rfl | he
      · exact ⟨s', h3, List.mem_cons_self⟩
      · obtain ⟨s'', h4, h5⟩ := m1 e he
        exact ⟨s'', h4, List.mem_cons_of_mem _ h5⟩

/-- **`+from` of a flat need is flat, entry by entry.** -/
theorem fromL_flat {axe : Nat} {L L' : Lazy S} (hL : Flat L) (h : fromL axe L = some L') :
    Flat L' ∧ L'.bond.map Prod.fst = L.bond.map Prod.fst ∧
    ∀ e ∈ L.bond, ∃ s', fromSure axe e.2.sure = some s' ∧ (e.1, ofSure s') ∈ L'.bond := by
  rcases L with ⟨s, f, b⟩
  obtain ⟨hf, hb⟩ := hL
  simp only [fork_mk] at hf
  subst hf
  simp only [bond_mk] at hb ⊢
  unfold fromL at h
  by_cases e : b = []
  · subst e
    simp only [List.isEmpty_nil, Bool.and_self, if_true] at h
    obtain ⟨s', _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨flat_ofSure _, rfl, fun e he => by cases he⟩
  · have e' : (List.isEmpty ([] : List (ForkE S)) && b.isEmpty) = false := by
      simp only [List.isEmpty_nil, Bool.true_and]; exact List.isEmpty_eq_false_iff.mpr e
    simp only [e', Bool.false_eq_true, if_false] at h
    obtain ⟨s', _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨f', hf', h⟩ := Option.bind_eq_some_iff.mp h
    simp only [fromForks, Option.some.injEq] at hf'
    subst hf'
    obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨e1, f1, m1⟩ := fromBonds_flat axe b b' hb hb'
    exact ⟨flat_mk f1, e1, m1⟩

/-! ## `[0 axe]` -/

/-- **`[0 axe]` under a flat lazy goal, `axe ≥ 1`**: `RunOKLS` with the
witness relation of the call-free run, no op at any goal entry. -/
theorem lokS_n0 (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {f : Noun} {axe : Nat} (ha : 1 ≤ axe)
    (M : MinkEq lib P f (Nomm.n0 axe)) : LOKS (S := S) (Map := Map) false lib N env P f (Nomm.n0 axe) := by
  refine ⟨(lokc_n0 (S := S) (Map := Map) lib env ha M).clean, fun {sup L th region g0 g1 nex} _ b0 d0 hu hcl hcb
    h1 h2 hta ht hsd hsl hlab hnd hed hfl _ hce hr => ?_⟩
  rw [runLC_eq env _ rfl] at hr
  have eL : entries L = L.bond := entries_flat hfl
  -- the result
  obtain ⟨L', hL', rfl, rfl⟩ : ∃ L', ((axe = 1 ∧ L' = L) ∨ (2 ≤ axe ∧ fromL axe L = some L')) ∧
      nex = ⟨L', th⟩ ∧ g0 = g1 := by
    rcases Nat.lt_or_ge axe 2 with lt | ge
    · obtain rfl : axe = 1 := by omega
      rw [runL_n01_next] at hr
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨L, Or.inl ⟨rfl, rfl⟩, rfl, rfl⟩
    · rw [runL_n0_next ge] at hr
      cases hf : fromL axe L with
      | none => rw [hf] at hr; cases hr
      | some L' =>
        rw [hf] at hr
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact ⟨L', Or.inr ⟨ge, rfl⟩, rfl, rfl⟩
  -- the result's entries, entry by entry
  have hres : Flat L' ∧ L'.bond.map Prod.fst = L.bond.map Prod.fst ∧
      ∀ e ∈ L.bond, ∃ s', (axe = 1 ∧ s' = e.2.sure ∨ fromSure axe e.2.sure = some s') ∧
        (e.1, ofSure s') ∈ L'.bond := by
    rcases hL' with ⟨_, rfl⟩ | ⟨_, hf⟩
    · exact ⟨hfl, rfl, fun e he => ⟨e.2.sure, Or.inl ⟨by assumption, rfl⟩, by rw [← hfl.2 e he]; exact he⟩⟩
    · obtain ⟨f1, e1, m1⟩ := fromL_flat hfl hf
      exact ⟨f1, e1, fun e he => by obtain ⟨s', h1', h2'⟩ := m1 e he; exact ⟨s', Or.inr h1', h2'⟩⟩
  obtain ⟨fL', lL', mL'⟩ := hres
  have eL' : entries L' = L'.bond := entries_flat fL'
  -- `RunOKLB` from the stripped state (`LOKC.toB` with the witness relation in view)
  let X := (entries L).map Prod.fst
  have hX : ∀ o ∈ X, o < g0.bo := fun o ho => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
    exact (hlab e he).1
  have s0 := simB_strip (Map := Map) hX
  have hemp : ∀ e ∈ entries L, ∃ th', HoonMap.get (stripG X g0).blocks e.1 = some ⟨[], [], Termin.hop th'⟩ :=
    fun e he => by
      obtain ⟨_, B, th', hb⟩ := hlab e he
      exact ⟨th', stripG_get_mem (List.mem_map_of_mem he) hb⟩
  have RL : RunOKL (Map := Map) lib (Nomm.n0 axe) L th (fun _ => Need.none) (fun _ => A 0) (stripG X g0)
      (stripG X g0) ⟨L', th⟩ := by
    rcases hL' with ⟨rfl, rfl⟩ | ⟨_, hf⟩
    · exact runOKL_n01 (g := stripG X g0) lib h1 h2 hsd (fun e he => (hed e he).1) hnd hemp (fun r hr => (hsl r hr).2)
        (fun e he r hr => ((hed e he).2 r hr).2) _
    · exact runOKL_n0 (g := stripG X g0) lib hf h1 h2 hsd (fun e he => (hed e he).1) hnd hemp (fun r hr => (hsl r hr).2)
        (fun e he r hr => ((hed e he).2 r hr).2) _
  have RB := RunOKLB.ofSim (N := N) s0 s0 (fun o ho => stripBd_out ho) (RL.toLC M).toB
  -- the fronts: no op, the result's entry seen at `axe`
  have FS : FrontsS (Map := Map) (pureWit (Nomm.n0 axe) (fun _ => Need.none) (fun _ => A 0)) false g0 g0 L ⟨L', th⟩ := by
    intro e he
    refine ⟨[], fun B fin hb => by simpa using hb, fun cf hcf => Or.inl ?_⟩
    rw [eL] at he
    obtain ⟨s', hs', hm⟩ := mL' e he
    have ee : e.2 = ofSure e.2.sure := hfl.2 e he
    refine ⟨ofSure s', by rw [eL']; exact hm, ?_⟩
    simp only [List.map_nil]
    have hreg := (hed e (by rw [eL]; exact he)).2
    rcases hs' with ⟨rfl, rfl⟩ | hs'
    · refine ⟨fun r hr => ⟨(hreg r hr).1, fun _ => hr⟩, fun s v d w hq r hd => by
        obtain ⟨_, rfl, _⟩ := hq; exact absurd hd (by simp [NMem]), fun s v d w hq fit => ?_, ?_⟩
      · obtain ⟨hv, _, _⟩ := hq
        have : v = s := by simpa [pureEval] using hv.symm
        subst this; exact fit
      · intro lib σ O c gul st t R s v d w hq hL hd hE
        obtain ⟨hv, _, _⟩ := hq
        have : v = s := by simpa [pureEval] using hv.symm
        subst this
        exact ⟨fun _ => ⟨R, Runs.nil R, hL, fun _ _ _ => rfl⟩, fun nf => absurd (fitsS_of_holdsS hL) nf⟩
    · obtain ⟨_, hhold, hfit, hmem⟩ := fromSure_spec (Map := Map) hs'
      have hv : ∀ s v, pureEval (Nomm.n0 axe) s = some v → slot? axe s = some v := fun s v h => by
        simpa [pureEval] using h
      refine ⟨fun r hr => ⟨(hreg r (hmem r hr)).1, fun _ => hmem r hr⟩, fun s v d w hq r hd => by
        obtain ⟨_, rfl, _⟩ := hq; exact absurd hd (by simp [NMem]), fun s v d w hq fit => ?_, ?_⟩
      · obtain ⟨h', _, _⟩ := hq
        exact hfit s v (hv s v h') fit
      · intro lib σ O c gul st t R s v d w hq hL hd hE
        obtain ⟨h', _, _⟩ := hq
        obtain ⟨p, hp, hh⟩ := hhold R s hL
        rw [hv s v h'] at hp
        cases hp
        exact ⟨fun _ => ⟨R, Runs.nil R, hh, fun _ _ _ => rfl⟩, fun nf => absurd (fitsS_of_holdsS hh) nf⟩
  refine ⟨⟨_, { toRunOKLB := RB, fs := FS }⟩, ?_, Or.inl rfl, fL', fun e he => ?_⟩
  · show th.there ∉ (entries L').map Prod.fst
    rw [eL', lL', ← eL]; exact ht
  · rw [eL'] at he
    have hk : e.1 ∈ L.bond.map Prod.fst := by rw [← lL']; exact List.mem_map_of_mem he
    obtain ⟨e0, he0, ee⟩ := List.mem_map.mp hk
    obtain ⟨s', hs', hm⟩ := mL' e0 he0
    have : e = (e0.1, ofSure s') := eq_of_label (by rw [lL', ← eL]; exact hnd) he hm ee.symm
    subst this
    have c0 := hce e0 (by rw [eL]; exact he0)
    rcases hs' with ⟨_, rfl⟩ | hs'
    · exact c0
    · exact clean_fromSure hs' c0

end Comp
end SkaModel
end Formalization
