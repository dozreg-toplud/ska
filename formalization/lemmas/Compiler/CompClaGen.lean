import lemmas.Compiler.CompKernGen

/-!
# `+none-equivalent` and `+collapse-lazy-atom` on every lazy need

`+none-equivalent` (arm `2811` of `K`, `neBat`) is

    ?&  ?=([%none ~] ned.sure.laz)
        ?=(?(~ [%1 ~ ~]) lok.sure.laz)
        (levy fork.laz |=([[* a] * b] &((none a) (none b))))
        (levy bond.laz |=([* n] (none n)))
    ==

with `none` the gate itself (`=*  none  .`).  The model `noneEquivalentL`
of `Ska/CompLazyArms.lean` (with `noneForks`, `noneBonds`) is the same
conjunction in the same order.  No departure.  `ne_all`: on every lazy
need.

`+collapse-lazy-atom` (`claBat` of `CompClaLink.lean`) then walks the lazy
need with `ned.sure` set to `[%this r]` from the block `there`, with the gate
`claG` (`cla_gate`, through `+proxy` at the blocks other than `there`).
`comp_collapse_lazy_atom_all`: the arm on every lazy need.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

variable {ctx : Noun}

def neGF : Noun :=
  (C (A 6) (C (C (A 8) (C (C (A 0) (A 7)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 57))) (C (A 0) (A 2)))))))) (C (C (A 6) (C (C (A 8) (C (C (A 0) (A 7)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1)))))

def neGB : Noun :=
  (C (A 8) (C (C (A 0) (A 7)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2))))))))

def neBatS : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 24))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 48)))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 49)))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 25)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 3) (C (A 0) (A 25))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 50)))) (C (C (A 6) (C (C (A 3) (C (A 0) (A 51))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 102)))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 103)))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1)))))))) (C (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 0x2fbc) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 58)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))))) (C (C (A 1) neGF) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 0x2fbc) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 59)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))))) (C (C (A 1) neGB) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1)))))))

theorem ne_bat_eq : neBat = neBatS := by kernel_rfl

theorem all_congr_mem {β : Type} (l : List β) (f g : β → Bool) (h : ∀ a ∈ l, f a = g a) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.all_cons, h a (by simp), ih (fun b hb => h b (by simp [hb]))]

/-- `+levy` over the nouns `E a` of a list, with a gate that says `p a`. -/
theorem levy_gate_map {α : Type} (E : α → Noun) (c bp bs bc : Noun) (p : α → Bool) (l : List α)
    (hf : ∀ a ∈ l, nock (C bp (C (E a) bc)) bp = some (loob (p a))) :
    nock (C levy.battery (C (C (listN (l.map E)) (C bp (C bs bc))) c)) levy.battery
      = some (loob (l.all p)) := by
  classical
  let p' : Noun → Bool := fun x => match l.find? (fun a => decide (E a = x)) with
    | some a => p a
    | none => false
  have hp : ∀ a ∈ l, p' (E a) = p a := by
    intro a ha
    have hfa := hf a ha
    cases e : l.find? (fun b => decide (E b = E a)) with
    | none =>
      exfalso
      have := List.find?_eq_none.1 e a ha
      simp at this
    | some b =>
      have hb := List.mem_of_find?_eq_some e
      have hbe : E b = E a := by simpa using List.find?_some e
      have hfb := hf b hb
      rw [hbe, hfa] at hfb
      have : p a = p b := by
        cases h1 : p a <;> cases h2 : p b <;> simp_all [loob]
      simp only [p', e, this]
  rw [levy_gate c bp bs bc p' (l.map E) (fun x hx => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    rw [hp a ha]; exact hf a ha)]
  congr 2
  rw [List.all_map]
  exact all_congr_mem l _ _ (fun a ha => by simp [Function.comp_def, hp a ha])

theorem noneForks_all : ∀ f : List (Lazy.ForkE CSet),
    Lazy.noneForks f = f.all fun e => Lazy.noneEquivalentL e.1.2 && Lazy.noneEquivalentL e.2.2
  | [] => rfl
  | ((oy, y), (on, n)) :: rest => by simp [Lazy.noneForks, noneForks_all rest]

theorem noneBonds_all : ∀ b : List (Nat × Lazy CSet),
    Lazy.noneBonds b = b.all fun e => Lazy.noneEquivalentL e.2
  | [] => rfl
  | (o, l) :: rest => by simp [Lazy.noneBonds, noneBonds_all rest]

mutual
/-- **`+none-equivalent` on every lazy need** (forks and bonds to any
depth). -/
theorem ne_all : ∀ laz : Lazy CSet,
    nock (C neBat (C laz.toNoun compK)) neBat = some (loob (Lazy.noneEquivalentL laz))
  | Lazy.mk ⟨ned, lok⟩ fk bd => by
    have hL := compK_layer2
    have hLF := levy_gate_map forkE layer2 neGF (C (C (A 0) lzBunt) (C (A 0) lzBunt))
      (C neBat (C (C (Sure.toNoun ⟨ned, lok⟩) (C (listN (fk.map forkE)) (listN (bd.map bondE)))) compK))
      (fun e => Lazy.noneEquivalentL e.1.2 && Lazy.noneEquivalentL e.2.2) fk
      (fun e he => ne_forks fk e he _)
    have hLB := levy_gate_map bondE layer2 neGB (C (A 0) lzBunt)
      (C neBat (C (C (Sure.toNoun ⟨ned, lok⟩) (C (listN (fk.map forkE)) (listN (bd.map bondE)))) compK))
      (fun e => Lazy.noneEquivalentL e.2) bd
      (fun e he => ne_bonds bd e he _)
    unfold lzBunt at hLF hLB
    rw [lazy_toNoun_mk]
    conv => { lhs; arg 2; rw [ne_bat_eq]; unfold neBatS }
    simp only [Lazy.noneEquivalentL, ← noneForks_all, ← noneBonds_all] at hLF hLB ⊢
    have other : ∀ (ned : Need), ned ≠ Need.none → ∀ (L : Noun),
        nock (C neBat (C (C (C ned.toNoun L) (C (listN (fk.map forkE)) (listN (bd.map bondE)))) compK))
          (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 24))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 48)))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 49)))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 25)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 3) (C (A 0) (A 25))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 50)))) (C (C (A 6) (C (C (A 3) (C (A 0) (A 51))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 102)))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 103)))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1)))))))) (C (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 0x2fbc) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 58)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))))) (C (C (A 1) neGF) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 0x2fbc) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 59)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))))) (C (C (A 1) neGB) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))))) = some (A 1) := by
      intro ned hn L
      cases ned with
      | none => exact absurd rfl hn
      | pair p q =>
        obtain ⟨a, b, hp⟩ := cd_need_cell p
        simp [nock_exec, Need.toNoun, hp, eqCode]
      | this r => simp [nock_exec, Need.toNoun, eqCode_atom, Tag.this]
      | both r h t => simp [nock_exec, Need.toNoun, eqCode_atom, Tag.both]
    by_cases hn : ned = Need.none
    · subst hn
      simp only [Sure.toNoun, Need.toNoun, Tag.none] at hLF hLB
      simp only [Sure.toNoun]
      rcases cs_small_cases lok with ⟨hsm, hl | hl⟩ | ⟨hsm, n, l, r, hl, hne⟩
      · rw [hl] at hLF hLB ⊢
        cases hb1 : Lazy.noneForks fk <;> cases hb2 : Lazy.noneBonds bd <;>
          simp [nock_exec, Need.toNoun, hL, levy_arm, levy.arm_at, hLF, hLB, hsm, Tag.none, loob, hb1, hb2]
      · rw [hl] at hLF hLB ⊢
        cases hb1 : Lazy.noneForks fk <;> cases hb2 : Lazy.noneBonds bd <;>
          simp [nock_exec, Need.toNoun, hL, levy_arm, levy.arm_at, hLF, hLB, hsm, Tag.none, loob, hb1, hb2]
      · rw [hl]
        rcases n with k | ⟨n1, n2⟩
        · by_cases hk : k = 1
          · subst hk
            rcases l with l | ⟨l1, l2⟩
            · by_cases hl0 : l = 0
              · subst hl0
                rcases r with r | ⟨r1, r2⟩
                · have hr0 : r ≠ 0 := fun e => hne ⟨rfl, rfl, by rw [e]⟩
                  simp [nock_exec, Need.toNoun, hsm, loob, eqCode_atom, Tag.none, Ne.symm hr0]
                · simp [nock_exec, Need.toNoun, hsm, loob, eqCode_atom, eqCode, Tag.none]
              · simp [nock_exec, Need.toNoun, hsm, loob, eqCode_atom, Tag.none, Ne.symm hl0]
            · simp [nock_exec, Need.toNoun, hsm, loob, eqCode_atom, eqCode, Tag.none]
          · simp [nock_exec, Need.toNoun, hsm, loob, eqCode_atom, Tag.none, Ne.symm hk]
        · simp [nock_exec, Need.toNoun, hsm, loob, eqCode_atom, eqCode, Tag.none]
    · simp only [Sure.toNoun]
      rw [other ned hn]
      simp [hn, loob]

theorem ne_forks : ∀ (fk : List (Lazy.ForkE CSet)), ∀ e ∈ fk, ∀ L : Noun,
    nock (C neGF (C (forkE e) (C neBat (C L compK)))) neGF
      = some (loob (Lazy.noneEquivalentL e.1.2 && Lazy.noneEquivalentL e.2.2))
  | [], e, he => absurd he List.not_mem_nil
  | ((oy, y), (on, n)) :: rest, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro L
      have hy := ne_all y
      have hn := ne_all n
      unfold neGF
      cases ey : Lazy.noneEquivalentL y <;> cases en : Lazy.noneEquivalentL n <;>
        simp [nock_exec, forkE, hy, hn, ey, en, loob]
    · exact ne_forks rest e he'

theorem ne_bonds : ∀ (bd : List (Nat × Lazy CSet)), ∀ e ∈ bd, ∀ L : Noun,
    nock (C neGB (C (bondE e) (C neBat (C L compK)))) neGB = some (loob (Lazy.noneEquivalentL e.2))
  | [], e, he => absurd he List.not_mem_nil
  | (ob, l) :: rest, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro L
      have hl := ne_all l
      unfold neGB
      simp [nock_exec, bondE, hl]
    · exact ne_bonds rest e he'
end

end Compiler
end Formalization
