import lemmas.Ska.CompUnproxyEntry

/-!
# The registers the ops of `+kern-need` mention

A first piece of the register facts that `finishLF_compDoneU` needs (README,
Gaps 12.2): the fill ops of `+coerce-lazy` mention only registers that are no
key of `cond`, so unproxying leaves them unchanged.

* `poleRegs`: every register an op mentions, read or written.
* `RegsIn P A`: every register of every op of `A` satisfies `P`.
* `renPole_fix`, `renOps_fix`: a renaming that fixes every register of the
  ops leaves them unchanged; `unproxy_ops`: so `unproxy cond` leaves ops
  alone whose registers are no keys of `cond`.
* `kernLoop_regs`: the ops of the loop of `+kern-need` from `r` into `tgt`
  mention only `r`, registers of `tgt` and registers allocated in the loop
  (at or above the start's `re`), for any predicate that holds of those.

Tested on the real compiler (2026-11-24, an instrumented copy of the library,
the 74 formulas of `thread-a.hoon` and the two cases of `proxy-dump.hoon`,
2930 runs of `run` in `%run` mode, 352 of which make a proxy): no register of
the sure need or of a lazy entry's need of a run's result is a key of `cond`
after the run; the ops the run emits (new blocks, ops put in front of old
blocks, parameters written by new jumps) write no register of its result's
sure need nor of its lazy entries' needs; and the sure need and the entries'
needs share no register.  No failure.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {Map : Type → Type} [HoonMap Map]

/-- Every register an op mentions. -/
def poleRegs : Pole → List Nat
  | Pole.imm _ d => [d]
  | Pole.mov s d => [s, d]
  | Pole.inc s d => [s, d]
  | Pole.con h t d => [h, t, d]
  | Pole.hed s d => [s, d]
  | Pole.tal s d => [s, d]
  | Pole.cel p => [p]
  | Pole.lob p => [p]
  | Pole.equ l r => [l, r]
  | Pole.hsp _ _ => []
  | Pole.hse _ _ => []
  | Pole.hdp _ p _ => [p]
  | Pole.hde _ p _ => [p]
  | Pole.hmp _ v _ => v
  | Pole.hme _ v _ => v
  | Pole.hcp _ _ => []
  | Pole.hce _ _ => []
  | Pole.spy e p d => [e, p, d]
  | Pole.nok u f d => [u, f, d]
  | Pole.cal _ v d => d :: v
  | Pole.caf _ v d _ => d :: v
  | Pole.cam _ v d _ => d :: v
  | Pole.csl _ s d => [s, d]
  | Pole.csf _ s d _ => [s, d]
  | Pole.csm _ s d _ => [s, d]

/-- Every register of every op of `A` satisfies `P`. -/
def RegsIn (P : Nat → Prop) (A : List Pole) : Prop := ∀ p ∈ A, ∀ x ∈ poleRegs p, P x

theorem RegsIn.nil (P : Nat → Prop) : RegsIn P [] := fun _ h => absurd h (List.not_mem_nil)

theorem RegsIn.cons {P : Nat → Prop} {p : Pole} {A : List Pole} (hp : ∀ x ∈ poleRegs p, P x) (hA : RegsIn P A) :
    RegsIn P (p :: A) := fun q hq => (List.mem_cons.mp hq).elim (fun e => e ▸ hp) (hA q)

theorem RegsIn.append {P : Nat → Prop} {A B : List Pole} (hA : RegsIn P A) (hB : RegsIn P B) :
    RegsIn P (A ++ B) := fun q hq => (List.mem_append.mp hq).elim (hA q) (hB q)

theorem RegsIn.mono {P Q : Nat → Prop} (h : ∀ x, P x → Q x) {A : List Pole} (hA : RegsIn P A) : RegsIn Q A :=
  fun q hq x hx => h x (hA q hq x hx)

theorem map_fix {u : Nat → Nat} : ∀ {v : List Nat}, (∀ x ∈ v, u x = x) → v.map u = v
  | [], _ => rfl
  | a :: v, h => by
    simp only [List.map_cons, h a List.mem_cons_self, map_fix (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- **A renaming that fixes every register of an op leaves it unchanged.** -/
theorem renPole_fix {u : Nat → Nat} {p : Pole} (h : ∀ x ∈ poleRegs p, u x = x) : renPole u p = p := by
  cases p <;> simp_all [renPole, poleRegs, map_fix]

theorem renOps_fix {u : Nat → Nat} {P : Nat → Prop} (hu : ∀ x, P x → u x = x) {A : List Pole} (hA : RegsIn P A) :
    A.map (renPole u) = A := by
  induction A with
  | nil => rfl
  | cons p A ih =>
    simp only [List.map_cons]
    rw [renPole_fix (fun x hx => hu x (hA p List.mem_cons_self x hx)),
      ih (fun q hq => hA q (List.mem_cons_of_mem _ hq))]

/-- **Unproxying leaves ops alone whose registers are no keys of `cond`.** -/
theorem unproxy_ops {cond : Map (Nat × List Nat)} {A : List Pole}
    (hA : RegsIn (fun x => HoonMap.get cond x = Option.none) A) : A.map (renPole (unproxy cond)) = A :=
  renOps_fix (fun _ h => unproxy_none h) hA

/-! ## The ops of `+kern-need` -/

/-- **The case `%both` of `+kern-need` mentions only `r`, `d`, the registers
of the halves and fresh registers**, given the same of the calls for the
halves. -/
theorem kernBoth_regs (P : Nat → Prop) {r d : Nat} {kh kt : Nat → List Pole → CM Map (List Pole)}
    (sh : ∀ r' acc (g g' : Gen Map) ops, kh r' acc g = some (ops, g') → g.re ≤ g'.re ∧
      (P r' → (∀ x, g.re ≤ x → P x) → RegsIn P acc → RegsIn P ops))
    (st : ∀ r' acc (g g' : Gen Map) ops, kt r' acc g = some (ops, g') → g.re ≤ g'.re ∧
      (P r' → (∀ x, g.re ≤ x → P x) → RegsIn P acc → RegsIn P ops))
    {acc : List Pole} {g g' : Gen Map} {ops : List Pole} (hk : kernBoth r d kh kt acc g = some (ops, g')) :
    g.re ≤ g'.re ∧ (P r → P d → (∀ x, g.re ≤ x → P x) → RegsIn P acc → RegsIn P ops) := by
  unfold kernBoth at hk
  obtain ⟨rt, g1, h1, hk⟩ := bind_some hk
  rw [re_apply] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  obtain ⟨o1, g2, h2, hk⟩ := bind_some hk
  obtain ⟨le2, R2⟩ := st _ _ _ _ _ h2
  obtain ⟨rh, g3, h3, hk⟩ := bind_some hk
  rw [re_apply] at h3
  simp only [Option.some.injEq, Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  obtain ⟨o2, g4, h4, hk⟩ := bind_some hk
  obtain ⟨le4, R4⟩ := sh _ _ _ _ _ h4
  simp only at le2 le4
  by_cases e : r = d
  · rw [if_pos e] at hk; cases hk
  rw [if_neg e] at hk
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  refine ⟨by omega, fun hr hd hg ha => ?_⟩
  have hg1 : ∀ x, g.re + 1 ≤ x → P x := fun x hx => hg x (by omega)
  have hg3 : ∀ x, g2.re + 1 ≤ x → P x := fun x hx => hg x (by omega)
  have A2 : RegsIn P o1 := R2 (hg g.re (Nat.le_refl _)) hg1 ha
  have A2' : RegsIn P (if o1 ≠ acc then Pole.tal d g.re :: o1 else o1) := by
    split
    · exact RegsIn.cons (p := Pole.tal d g.re) (fun x hx => by
        simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with hx | hx
        · rw [hx]; exact hd
        · rw [hx]; exact hg _ (Nat.le_refl _)) A2
    · exact A2
  have A4 := R4 (hg g2.re (by omega)) hg3 A2'
  have A4' : RegsIn P (Pole.cel d :: if o2 ≠ (if o1 ≠ acc then Pole.tal d g.re :: o1 else o1) then
      Pole.hed d g2.re :: o2 else o2) := by
    refine RegsIn.cons (p := Pole.cel d) (fun x hx => by simp only [poleRegs, List.mem_singleton] at hx; rw [hx]; exact hd) ?_
    by_cases e2 : o2 ≠ (if o1 ≠ acc then Pole.tal d g.re :: o1 else o1)
    · rw [if_pos e2]
      exact RegsIn.cons (p := Pole.hed d g2.re) (fun x hx => by
        simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with hx | hx
        · rw [hx]; exact hd
        · rw [hx]; exact hg _ (by omega)) A4
    · rw [if_neg e2]; exact A4
  refine RegsIn.cons (p := Pole.mov r d) (fun x hx => ?_) A4'
  simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with hx | hx
  · rw [hx]; exact hr
  · rw [hx]; exact hd

/-- **The ops of the loop of `+kern-need` from `r` into `tgt` mention only
`r`, the registers of `tgt` and registers allocated in the loop.** -/
theorem kernLoop_regs (P : Nat → Prop) : ∀ (tgt : Need) (r : Nat) (acc : List Pole) (g g' : Gen Map)
    (ops : List Pole), kernLoop r tgt acc g = some (ops, g') →
      P r → (∀ x, NMem tgt x → P x) → (∀ x, g.re ≤ x → P x) → RegsIn P acc → RegsIn P ops := by
  intro tgt
  induction tgt with
  | none =>
    intro r acc g g' ops h _ _ _ ha
    simp only [kernLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ha
  | this d =>
    intro r acc g g' ops h hr ht _ ha
    simp only [kernLoop] at h
    by_cases e : r = d
    · rw [if_pos e] at h; cases h
    rw [if_neg e] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine RegsIn.cons (p := Pole.mov r d) (fun x hx => ?_) ha
    simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with hx | hx
    · rw [hx]; exact hr
    · rw [hx]; exact ht _ rfl
  | pair p q ihp ihq =>
    intro r acc g g' ops h hr ht hg ha
    simp only [kernLoop] at h
    obtain ⟨rn, g1, h1, h⟩ := bind_some h
    rw [re_apply] at h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    exact (kernBoth_regs P
      (fun r' acc g g' ops h => ⟨(kernLoop_spec p r' acc g g' ops h).choose_spec.2.le,
        fun a b c => ihp r' acc g g' ops h a (fun x hx => ht x (Or.inl hx)) b c⟩)
      (fun r' acc g g' ops h => ⟨(kernLoop_spec q r' acc g g' ops h).choose_spec.2.le,
        fun a b c => ihq r' acc g g' ops h a (fun x hx => ht x (Or.inr hx)) b c⟩)
      h).2 hr (hg _ (Nat.le_refl _)) (fun x hx => hg x (by simp only at hx; omega)) ha
  | both d h t ihh iht =>
    intro r acc g g' ops hk hr ht hg ha
    simp only [kernLoop] at hk
    exact (kernBoth_regs P
      (fun r' acc g g' ops h' => ⟨(kernLoop_spec h r' acc g g' ops h').choose_spec.2.le,
        fun a b c => ihh r' acc g g' ops h' a (fun x hx => ht x (Or.inr (Or.inl hx))) b c⟩)
      (fun r' acc g g' ops h' => ⟨(kernLoop_spec t r' acc g g' ops h').choose_spec.2.le,
        fun a b c => iht r' acc g g' ops h' a (fun x hx => ht x (Or.inr (Or.inr hx))) b c⟩)
      hk).2 hr (ht d (Or.inl rfl)) hg ha

end Comp
end SkaModel
end Formalization
