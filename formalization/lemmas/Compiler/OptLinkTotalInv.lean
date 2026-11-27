import lemmas.Compiler.OptLinkTotalMono
import lemmas.Ska.OptDriverTopo

/-!
# The invariant and the measure of the structural loop

`StInv ρ L bl`, what every round of the structural loop of `+optimize-once`
needs of its blocks so that its passes return: the rank `ρ` falls along every
jump (`RkDown`, `Acyclic` with a named rank), every jump goes to a block
(`Closed`), with the arity of its target (`ArityOK`), there is a block `0`,
the two-way ends pass no arguments (`TwoNA`, the `?>` of
`+remove-useless-branching`), and every label is in the list `L`.

The measure `mu ρ L bl` is the triple (number of blocks, the weight of the
two-way ends, sum over the jumps of every block of `ρ` of the target), each a
sum over `L`, ordered lexicographically (`LexLt`, `LexLe`).  The weight of an
end (`twoW`) is `2` for a `%brn`, `1` for the other two-way ends and `0`
otherwise: `+alias` reports a change when it turns a `%brn` on a known loob
into a `%brz` (`AuditOptTotal.lean`, `xbBlocks`), which only this weight
sees.  The structural passes keep the kind of every end they do not fold to a
hop (`mf_facts`), so they keep the weight.

Here, for `+remove-useless-branching` (`rub_inv_step`) and
`+remove-empty-middle` (`mid_inv_step`): the pass keeps `StInv` with the same `ρ`
and `L`, does not raise the measure, and lowers it when it reports a change.
`rub_isSome`: `+remove-useless-branching` returns on `Closed` blocks with
`TwoNA`.  `+remove-hops` is in `OptLinkTotalHops.lean`.
-/

namespace Formalization
namespace Compiler

open Nock SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## The lexicographic order on triples -/

/-- The lexicographic order on triples. -/
def LexLt : Nat × Nat × Nat → Nat × Nat × Nat → Prop
  | (a', b', c'), (a, b, c) => a' < a ∨ (a' = a ∧ (b' < b ∨ (b' = b ∧ c' < c)))

def LexLe (x y : Nat × Nat × Nat) : Prop := LexLt x y ∨ x = y

theorem lexLt_trans {x y z : Nat × Nat × Nat} (h1 : LexLt x y) (h2 : LexLt y z) : LexLt x z := by
  obtain ⟨a1, b1, c1⟩ := x; obtain ⟨a2, b2, c2⟩ := y; obtain ⟨a3, b3, c3⟩ := z
  simp only [LexLt] at *; omega

theorem lexLe_trans {x y z : Nat × Nat × Nat} (h1 : LexLe x y) (h2 : LexLe y z) : LexLe x z := by
  rcases h1 with h1 | rfl
  · rcases h2 with h2 | rfl
    · exact Or.inl (lexLt_trans h1 h2)
    · exact Or.inl h1
  · exact h2

theorem lexLt_of_lt_le {x y z : Nat × Nat × Nat} (h1 : LexLt x y) (h2 : LexLe y z) : LexLt x z := by
  rcases h2 with h2 | rfl
  · exact lexLt_trans h1 h2
  · exact h1

theorem lexLt_of_le_lt {x y z : Nat × Nat × Nat} (h1 : LexLe x y) (h2 : LexLt y z) : LexLt x z := by
  rcases h1 with h1 | rfl
  · exact lexLt_trans h1 h2
  · exact h2

/-- **Induction along the lexicographic order.** -/
theorem lex_induction (P : Nat × Nat × Nat → Prop) (h : ∀ x, (∀ y, LexLt y x → P y) → P x) : ∀ x, P x := by
  intro ⟨a, b, c⟩
  induction a using Nat.strongRecOn generalizing b c with
  | _ a iha =>
    induction b using Nat.strongRecOn generalizing c with
    | _ b ihb =>
      induction c using Nat.strongRecOn with
      | _ c ihc =>
        apply h
        intro ⟨a', b', c'⟩ hlt
        simp only [LexLt] at hlt
        rcases hlt with h1 | ⟨rfl, h2 | ⟨rfl, h3⟩⟩
        · exact iha a' h1 b' c'
        · exact ihb b' h2 c'
        · exact ihc c' h3

/-! ## Sums over a list -/

def sumL (L : List Nat) (f : Nat → Nat) : Nat := (L.map f).sum

theorem sumL_le {f g : Nat → Nat} : ∀ {L : List Nat}, (∀ o ∈ L, f o ≤ g o) → sumL L f ≤ sumL L g
  | [], _ => Nat.le_refl _
  | o :: L, h => by
    simp only [sumL, List.map_cons, List.sum_cons] at *
    have := h o (by simp); have := sumL_le (L := L) (fun x hx => h x (by simp [hx]))
    simp only [sumL] at this; omega

theorem sumL_lt {f g : Nat → Nat} : ∀ {L : List Nat}, (∀ o ∈ L, f o ≤ g o) → ∀ x ∈ L, f x < g x →
    sumL L f < sumL L g
  | [], _, x, hx, _ => absurd hx List.not_mem_nil
  | o :: L, h, x, hx, hlt => by
    simp only [sumL, List.map_cons, List.sum_cons] at *
    have h1 := h o (by simp)
    have h2 := sumL_le (L := L) (fun y hy => h y (by simp [hy]))
    simp only [sumL] at h2
    rcases List.mem_cons.1 hx with rfl | hx
    · omega
    · have := sumL_lt (L := L) (fun y hy => h y (by simp [hy])) x hx hlt
      simp only [sumL] at this; omega

theorem sumL_congr {f g : Nat → Nat} : ∀ {L : List Nat}, (∀ o ∈ L, f o = g o) → sumL L f = sumL L g
  | [], _ => rfl
  | o :: L, h => by
    simp only [sumL, List.map_cons, List.sum_cons] at *
    have := sumL_congr (L := L) (fun x hx => h x (by simp [hx]))
    simp only [sumL] at this; rw [h o (by simp), this]

section
variable {Map : Type → Type} [HoonMap Map]

/-! ## The invariant -/

/-- The rank `ρ` falls along every jump. -/
def RkDown (ρ : Nat → Nat) (bl : Map Blob) : Prop :=
  ∀ o b j, HoonMap.get bl o = some b → j ∈ Opt.getJmps b.fin → ρ j.there < ρ o

/-- The two-way ends. -/
def twoWay : Termin → Bool
  | Termin.clq .. => true
  | Termin.eqq .. => true
  | Termin.brn .. => true
  | Termin.brz .. => true
  | _ => false

/-- The two-way ends pass no arguments. -/
def TwoNA (bl : Map Blob) : Prop :=
  ∀ o b j, HoonMap.get bl o = some b → twoWay b.fin = true → j ∈ Opt.getJmps b.fin → j.args = []

/-- **The invariant of the structural loop.** -/
structure StInv (ρ : Nat → Nat) (L : List Nat) (bl : Map Blob) : Prop where
  rank : RkDown ρ bl
  closed : Closed bl
  arity : ArityOK bl
  zero : (HoonMap.get bl 0).isSome
  two : TwoNA bl
  keys : ∀ o, (HoonMap.get bl o).isSome → o ∈ L

theorem StInv.acyclic {ρ : Nat → Nat} {L : List Nat} {bl : Map Blob} (h : StInv ρ L bl) : Opt.Acyclic bl :=
  ⟨ρ, h.rank⟩

theorem rank_sub {ρ : Nat → Nat} {bl bl' : Map Blob} (hr : RkDown ρ bl) (hs : Opt.TargetsSub bl bl') :
    RkDown ρ bl' := by
  intro o b' j' hb' hj'
  obtain ⟨b, hb, hj⟩ := hs o b' hb'
  obtain ⟨j, hj, e⟩ := hj j' hj'
  rw [← e]; exact hr o b j hb hj

/-! ## The measure -/

def presN : Option Blob → Nat
  | some _ => 1
  | none => 0

/-- The weight of an end: `2` for a `%brn`, `1` for the other two-way ends. -/
def twoW : Termin → Nat
  | Termin.brn .. => 2
  | Termin.clq .. => 1
  | Termin.eqq .. => 1
  | Termin.brz .. => 1
  | _ => 0

def twoCnt : Option Blob → Nat
  | some b => twoW b.fin
  | none => 0

/-- The sum over the jumps of an end of the rank of the target. -/
def finRk (ρ : Nat → Nat) (f : Termin) : Nat := ((Opt.getJmps f).map fun j => ρ j.there).sum

def rkN (ρ : Nat → Nat) : Option Blob → Nat
  | some b => finRk ρ b.fin
  | none => 0

/-- **The measure of the structural loop.** -/
def mu (ρ : Nat → Nat) (L : List Nat) (bl : Map Blob) : Nat × Nat × Nat :=
  (sumL L fun o => presN (HoonMap.get bl o), sumL L fun o => twoCnt (HoonMap.get bl o),
    sumL L fun o => rkN ρ (HoonMap.get bl o))

theorem mu_eq {ρ : Nat → Nat} {L : List Nat} {bl bl' : Map Blob}
    (h : ∀ o ∈ L, presN (HoonMap.get bl' o) = presN (HoonMap.get bl o) ∧
      twoCnt (HoonMap.get bl' o) = twoCnt (HoonMap.get bl o) ∧ rkN ρ (HoonMap.get bl' o) = rkN ρ (HoonMap.get bl o)) :
    mu ρ L bl' = mu ρ L bl := by
  simp only [mu, sumL_congr (fun o ho => (h o ho).1), sumL_congr (fun o ho => (h o ho).2.1),
    sumL_congr (fun o ho => (h o ho).2.2)]

theorem mu_lt1 {ρ : Nat → Nat} {L : List Nat} {bl bl' : Map Blob}
    (h : ∀ o ∈ L, presN (HoonMap.get bl' o) ≤ presN (HoonMap.get bl o)) {x : Nat} (hx : x ∈ L)
    (hlt : presN (HoonMap.get bl' x) < presN (HoonMap.get bl x)) : LexLt (mu ρ L bl') (mu ρ L bl) :=
  Or.inl (sumL_lt h x hx hlt)

theorem mu_lt2 {ρ : Nat → Nat} {L : List Nat} {bl bl' : Map Blob}
    (h1 : ∀ o ∈ L, presN (HoonMap.get bl' o) = presN (HoonMap.get bl o))
    (h : ∀ o ∈ L, twoCnt (HoonMap.get bl' o) ≤ twoCnt (HoonMap.get bl o)) {x : Nat} (hx : x ∈ L)
    (hlt : twoCnt (HoonMap.get bl' x) < twoCnt (HoonMap.get bl x)) : LexLt (mu ρ L bl') (mu ρ L bl) :=
  Or.inr ⟨sumL_congr h1, Or.inl (sumL_lt h x hx hlt)⟩

theorem mu_le3 {ρ : Nat → Nat} {L : List Nat} {bl bl' : Map Blob}
    (h1 : ∀ o ∈ L, presN (HoonMap.get bl' o) = presN (HoonMap.get bl o))
    (h2 : ∀ o ∈ L, twoCnt (HoonMap.get bl' o) = twoCnt (HoonMap.get bl o))
    (h : ∀ o ∈ L, rkN ρ (HoonMap.get bl' o) ≤ rkN ρ (HoonMap.get bl o)) :
    LexLe (mu ρ L bl') (mu ρ L bl) := by
  rcases Nat.lt_or_eq_of_le (sumL_le h) with hlt | heq
  · exact Or.inl (Or.inr ⟨sumL_congr h1, Or.inr ⟨sumL_congr h2, hlt⟩⟩)
  · exact Or.inr (by simp only [mu, sumL_congr h1, sumL_congr h2, heq])

theorem mu_lt3 {ρ : Nat → Nat} {L : List Nat} {bl bl' : Map Blob}
    (h1 : ∀ o ∈ L, presN (HoonMap.get bl' o) = presN (HoonMap.get bl o))
    (h2 : ∀ o ∈ L, twoCnt (HoonMap.get bl' o) = twoCnt (HoonMap.get bl o))
    (h : ∀ o ∈ L, rkN ρ (HoonMap.get bl' o) ≤ rkN ρ (HoonMap.get bl o)) {x : Nat} (hx : x ∈ L)
    (hlt : rkN ρ (HoonMap.get bl' x) < rkN ρ (HoonMap.get bl x)) : LexLt (mu ρ L bl') (mu ρ L bl) :=
  Or.inr ⟨sumL_congr h1, Or.inr ⟨sumL_congr h2, sumL_lt h x hx hlt⟩⟩

/-! ## `+remove-useless-branching` -/

theorem rubFin_isSome {bl : Map Blob} {f : Termin} (hc : ∀ j ∈ Opt.getJmps f, (HoonMap.get bl j.there).isSome)
    (h2 : twoWay f = true → ∀ j ∈ Opt.getJmps f, j.args = []) : (Opt.rubFin bl f).isSome := by
  cases f with
  | clq s z o | eqq _ s z o | brn s z o | brz s z o =>
    obtain ⟨nz, hz⟩ := Option.isSome_iff_exists.1 (hc z (by simp [Opt.getJmps]))
    obtain ⟨no, ho⟩ := Option.isSome_iff_exists.1 (hc o (by simp [Opt.getJmps]))
    have hza := h2 rfl z (by simp [Opt.getJmps])
    have hoa := h2 rfl o (by simp [Opt.getJmps])
    simp [Opt.rubFin, Opt.rubTwo, hza, hoa, hz, ho]
  | _ => simp [Opt.rubFin]

variable [Opt.MapKeys Map]

/-- **`+remove-useless-branching` returns** on `Closed` blocks whose two-way
ends pass no arguments. -/
theorem rub_isSome {bl : Map Blob} (hc : Closed bl) (h2 : TwoNA bl) : (Opt.removeUselessBranching bl).isSome := by
  have := foldl_bind_isSome (fun (r : Bool × Map Blob) o => Opt.rubStep bl (some r) o) (Opt.MapKeys.keys bl)
    (false, HoonMap.empty) (fun o ho r => by
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 ((Opt.MapKeys.mem_keys bl o).1 ho)
      obtain ⟨e, he⟩ := Option.isSome_iff_exists.1
        (rubFin_isSome (bl := bl) (f := b.fin) (fun j hj => hc o b j hb hj) (fun ht j hj => h2 o b j hb ht hj))
      simp [Opt.rubStep, hb, he])
  exact this

theorem rubFold_grows (bl : Map Blob) : ∀ (ks : List Nat) (c : Bool) (m : Map Blob) (r : Bool × Map Blob),
    ks.foldl (Opt.rubStep bl) (some (c, m)) = some r → c = true → r.1 = true
  | [], c, m, r, h, hc => by simp only [List.foldl_nil, Option.some.injEq] at h; subst h; exact hc
  | k :: ks, c, m, r, h, hc => by
    simp only [List.foldl_cons] at h
    cases hb : HoonMap.get bl k with
    | none => simp [Opt.rubStep, hb, Opt.rubFold_none] at h
    | some b =>
      cases he : Opt.rubFin bl b.fin with
      | none => simp [Opt.rubStep, hb, he, Opt.rubFold_none] at h
      | some e =>
        simp only [Opt.rubStep, hb, he, Option.bind_some, Option.map_some] at h
        exact rubFold_grows bl ks _ _ r h (by simp [hc])

theorem rubFold_flag (bl : Map Blob) : ∀ (ks : List Nat) (c0 : Bool) (m0 : Map Blob) (r : Bool × Map Blob),
    ks.foldl (Opt.rubStep bl) (some (c0, m0)) = some r →
    (r.1 = true → c0 = true ∨ ∃ k ∈ ks, ∃ b e, HoonMap.get bl k = some b ∧ Opt.rubFin bl b.fin = some e ∧
      e.2 ≠ b.fin) ∧
    (r.1 = false → ∀ k ∈ ks, ∀ b e, HoonMap.get bl k = some b → Opt.rubFin bl b.fin = some e → e.2 = b.fin)
  | [], c0, m0, r, h => by
    simp only [List.foldl_nil, Option.some.injEq] at h
    subst h
    exact ⟨fun h => Or.inl h, fun _ _ h => absurd h List.not_mem_nil⟩
  | k :: ks, c0, m0, r, h => by
    simp only [List.foldl_cons] at h
    cases hb : HoonMap.get bl k with
    | none => simp [Opt.rubStep, hb, Opt.rubFold_none] at h
    | some b =>
      cases he : Opt.rubFin bl b.fin with
      | none => simp [Opt.rubStep, hb, he, Opt.rubFold_none] at h
      | some e =>
        simp only [Opt.rubStep, hb, he, Option.bind_some, Option.map_some] at h
        obtain ⟨i1, i2⟩ := rubFold_flag bl ks _ _ r h
        refine ⟨fun hr => ?_, fun hr k' hk' b' e' hb' he' => ?_⟩
        · rcases i1 hr with h1 | ⟨k', hk', b', e', hb', he', hne⟩
          · simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
            rcases h1 with h1 | h1
            · exact Or.inl h1
            · exact Or.inr ⟨k, by simp, b, e, hb, he, h1⟩
          · exact Or.inr ⟨k', by simp [hk'], b', e', hb', he', hne⟩
        · rcases List.mem_cons.1 hk' with rfl | hk'
          · rw [hb] at hb'; cases hb'; rw [he] at he'; cases he'
            refine Classical.byContradiction fun hne => ?_
            have := rubFold_grows bl ks _ _ r h (by simp [hne])
            rw [hr] at this; cases this
          · exact i2 hr k' hk' b' e' hb' he'

theorem rub_flag {bl bl' : Map Blob} {ch : Bool} (h : Opt.removeUselessBranching bl = some (ch, bl')) :
    (ch = true → ∃ k b e, HoonMap.get bl k = some b ∧ Opt.rubFin bl b.fin = some e ∧ e.2 ≠ b.fin) ∧
    (ch = false → ∀ k b e, HoonMap.get bl k = some b → Opt.rubFin bl b.fin = some e → e.2 = b.fin) := by
  obtain ⟨i1, i2⟩ := rubFold_flag bl _ false HoonMap.empty _ h
  refine ⟨fun hc => ?_, fun hc k b e hb he => i2 hc k ((Opt.MapKeys.mem_keys bl k).2 (by simp [hb])) b e hb he⟩
  rcases i1 hc with h1 | ⟨k, -, b, e, hb, he, hne⟩
  · cases h1
  · exact ⟨k, b, e, hb, he, hne⟩

theorem presN_iff {x y : Option Blob} (h : x.isSome = y.isSome) : presN x = presN y := by
  cases x <;> cases y <;> simp_all [presN]

/-- **`+remove-useless-branching` keeps `StInv` and lowers the measure when it
reports a change.** -/
theorem rub_inv_step {ρ : Nat → Nat} {L : List Nat} {bl bl' : Map Blob} {ch : Bool} (hI : StInv ρ L bl)
    (h : Opt.removeUselessBranching bl = some (ch, bl')) :
    StInv ρ L bl' ∧ LexLe (mu ρ L bl') (mu ρ L bl) ∧ (ch = true → LexLt (mu ρ L bl') (mu ρ L bl)) := by
  have hb := Opt.rub_blocks h
  have hsome : ∀ k, (HoonMap.get bl' k).isSome = (HoonMap.get bl k).isSome := by
    intro k
    cases e : HoonMap.get bl k with
    | none => rw [(hb k).1 e]
    | some b => obtain ⟨_, _, e'⟩ := (hb k).2 b e; rw [e']; rfl
  -- what a block becomes
  have hcase : ∀ k b' , HoonMap.get bl' k = some b' → ∃ b e, HoonMap.get bl k = some b ∧
      Opt.rubFin bl b.fin = some e ∧ b' = Opt.rubBlob b e ∧ (e = ([], b.fin) ∨ ∃ (z o : Jmp) (nz : Blob), z.args = [] ∧ o.args = [] ∧
      HoonMap.get bl z.there = some nz ∧ e.2 = Termin.hop ⟨[], z.there⟩ ∧ z ∈ Opt.getJmps b.fin ∧
      twoWay b.fin = true) := by
    intro k b' hb'
    obtain ⟨b, e, hbk, he, rfl⟩ := hb.back hb'
    refine ⟨b, e, hbk, he, rfl, ?_⟩
    rcases Opt.rubFin_cases he with h1 | ⟨z, o, nz, hz, ho, hnz, -, h2, hf⟩
    · exact Or.inl h1
    · refine Or.inr ⟨z, o, nz, hz, ho, hnz, h2, ?_, ?_⟩ <;>
        rcases hf with ⟨s, hf, -⟩ | ⟨s, hf, -⟩ | ⟨l, r, hf, -⟩ | ⟨s, hf, -⟩ <;> simp [hf, Opt.getJmps, twoWay]
  have hpar : ∀ k b' b, HoonMap.get bl' k = some b' → HoonMap.get bl k = some b → b'.par = b.par := by
    intro k b' b hb' hbk
    obtain ⟨b0, e, hb0, -, rfl, -⟩ := hcase k b' hb'
    rw [hbk] at hb0; cases hb0; rfl
  refine ⟨⟨rank_sub hI.rank (Opt.rub_sub h), fun o b' j' hb' hj' => ?_, fun o b' j' b2' hb' hj' hb2' => ?_,
    by rw [hsome]; exact hI.zero, fun o b' j' hb' ht hj' => ?_, fun o ho => hI.keys o (by rw [← hsome]; exact ho)⟩,
    ?_, fun hc => ?_⟩
  · obtain ⟨b, hbk, hj⟩ := Opt.rub_sub h o b' hb'
    obtain ⟨j, hj, e⟩ := hj j' hj'
    rw [hsome, ← e]; exact hI.closed o b j hbk hj
  · obtain ⟨b, e, hbk, he, rfl, hc⟩ := hcase o b' hb'
    obtain ⟨b2, hb2⟩ := Option.isSome_iff_exists.1 (by rw [← hsome, hb2']; rfl : (HoonMap.get bl j'.there).isSome)
    rw [hpar _ _ _ hb2' hb2]
    rcases hc with rfl | ⟨z, o', nz, hz, ho', hnz, h2, hzj, -⟩
    · exact hI.arity o b j' b2 hbk hj' hb2
    · simp only [Opt.rubBlob, h2, Opt.getJmps, List.mem_singleton] at hj'
      subst hj'
      have e2 : b2 = nz := Option.some.inj (hb2.symm.trans hnz)
      have := hI.arity o b z nz hbk hzj hnz
      rw [hz] at this; rw [e2]; simpa using this
  · obtain ⟨b, e, hbk, he, rfl, hc⟩ := hcase o b' hb'
    rcases hc with rfl | ⟨z, o', nz, hz, ho', hnz, h2, hzj, -⟩
    · exact hI.two o b j' hbk ht hj'
    · simp [Opt.rubBlob, h2, twoWay] at ht
  · -- the measure does not rise
    cases ch with
    | false =>
      refine Or.inr (mu_eq fun o _ => ?_)
      cases e1 : HoonMap.get bl o with
      | none => rw [(hb o).1 e1]; exact ⟨rfl, rfl, rfl⟩
      | some b =>
        obtain ⟨e, he, e2⟩ := (hb o).2 b e1
        have hfin := (rub_flag h).2 rfl o b e e1 he
        rw [e2]
        simp [presN, twoCnt, rkN, Opt.rubBlob, hfin]
    | true => exact Or.inl (by
        obtain ⟨k, b, e, hbk, he, hne⟩ := (rub_flag h).1 rfl
        refine mu_lt2 (fun o _ => presN_iff (hsome o)) (fun o _ => ?_) (hI.keys k (by simp [hbk])) ?_
        · cases e1 : HoonMap.get bl' o with
          | none => simp [twoCnt]
          | some b' =>
            obtain ⟨b0, e0, hb0, -, rfl, hc⟩ := hcase o b' e1
            rw [hb0]
            rcases hc with rfl | ⟨z, o', nz, -, -, -, h2, -, -⟩
            · exact Nat.le_refl _
            · simp [twoCnt, Opt.rubBlob, h2, twoWay, twoW]
        · obtain ⟨e', he', e2⟩ := (hb k).2 b hbk
          rw [he] at he'; cases he'
          rw [e2, hbk]
          rcases Opt.rubFin_cases he with h1 | ⟨z, o', nz, -, -, -, -, h2, hf⟩
          · rw [h1] at hne; exact absurd rfl hne
          · rcases hf with ⟨s, hf, -⟩ | ⟨s, hf, -⟩ | ⟨l, r, hf, -⟩ | ⟨s, hf, -⟩ <;>
              simp [twoCnt, Opt.rubBlob, h2, hf, twoWay, twoW])
  · obtain ⟨k, b, e, hbk, he, hne⟩ := (rub_flag h).1 hc
    -- as in the case above
    refine mu_lt2 (fun o _ => presN_iff (hsome o)) (fun o _ => ?_) (hI.keys k (by simp [hbk])) ?_
    · cases e1 : HoonMap.get bl' o with
      | none => simp [twoCnt]
      | some b' =>
        obtain ⟨b0, e0, hb0, -, rfl, hc⟩ := hcase o b' e1
        rw [hb0]
        rcases hc with rfl | ⟨z, o', nz, -, -, -, h2, -, -⟩
        · exact Nat.le_refl _
        · simp [twoCnt, Opt.rubBlob, h2, twoWay, twoW]
    · obtain ⟨e', he', e2⟩ := (hb k).2 b hbk
      rw [he] at he'; cases he'
      rw [e2, hbk]
      rcases Opt.rubFin_cases he with h1 | ⟨z, o', nz, -, -, -, -, h2, hf⟩
      · rw [h1] at hne; exact absurd rfl hne
      · rcases hf with ⟨s, hf, -⟩ | ⟨s, hf, -⟩ | ⟨l, r, hf, -⟩ | ⟨s, hf, -⟩ <;>
          simp [twoCnt, Opt.rubBlob, h2, hf, twoWay, twoW]

end

/-! ## `+remove-empty-middle` -/

section
variable {Map : Type → Type} [HoonMap Map]

theorem rj_cases {bl : Map Blob} {n : Nat} {j j' : Jmp} (h : Opt.rewriteJump bl (n + 1) j = some j') :
    j' = j ∨ ∃ nex t, j.args = [] ∧ HoonMap.get bl j.there = some nex ∧ nex.par = [] ∧
      nex.fin = Termin.hop t ∧ t.args = [] ∧ Opt.rewriteJump bl n t = some j' := by
  simp only [Opt.rewriteJump] at h
  by_cases ha : j.args = []
  · simp only [ha, ne_eq, not_true_eq_false, if_false] at h
    obtain ⟨nex, hnex, h⟩ := Option.bind_eq_some_iff.1 h
    by_cases hp : nex.par = []
    · by_cases hb : nex.body = []
      · simp only [hp, hb, ne_eq, not_true_eq_false, if_false] at h
        cases e : nex.fin with
        | hop t =>
          simp only [e] at h
          by_cases hta : t.args = []
          · simp only [hta, ne_eq, not_true_eq_false, if_false] at h
            exact Or.inr ⟨nex, t, ha, hnex, hp, e, hta, h⟩
          · simp only [hta, ne_eq, not_false_eq_true, if_true, Option.some.injEq] at h
            exact Or.inl h.symm
        | _ => simp only [e, Option.some.injEq] at h; exact Or.inl h.symm
      · simp only [hp, hb, ne_eq, not_true_eq_false, not_false_eq_true, if_false, if_true,
          Option.some.injEq] at h
        exact Or.inl h.symm
    · simp [hp] at h
  · simp only [ha, ne_eq, not_false_eq_true, if_true, Option.some.injEq] at h
    exact Or.inl h.symm

theorem rh_cases {bl : Map Blob} {rd : Nat → List Nat} {n : Nat} {j j' : Jmp}
    (h : Opt.rewriteHop bl rd (n + 1) j = some j') :
    j' = j ∨ ∃ nex t s, HoonMap.get bl j.there = some nex ∧ nex.fin = Termin.hop t ∧
      Opt.mkSub nex.par j.args (fun _ => none) = some s ∧
      Opt.rewriteHop bl rd n ⟨t.args.map (Opt.passArg s), t.there⟩ = some j' := by
  simp only [Opt.rewriteHop] at h
  obtain ⟨nex, hnex, h⟩ := Option.bind_eq_some_iff.1 h
  by_cases hb : nex.body = []
  · simp only [hb, ne_eq, not_true_eq_false, if_false] at h
    cases e : nex.fin with
    | hop t =>
      simp only [e] at h
      by_cases hp : (nex.par.all fun p => (rd p).all (· = j.there)) = true
      · simp only [hp, Bool.not_true, Bool.false_eq_true, if_false] at h
        obtain ⟨s, hs, h⟩ := Option.bind_eq_some_iff.1 h
        exact Or.inr ⟨nex, t, s, hnex, e, hs, h⟩
      · simp only [Bool.not_eq_true] at hp
        simp only [hp, Bool.not_false, if_true, Option.some.injEq] at h
        exact Or.inl h.symm
    | _ => simp only [e, Option.some.injEq] at h; exact Or.inl h.symm
  · simp only [hb, ne_eq, not_false_eq_true, if_true, Option.some.injEq] at h
    exact Or.inl h.symm

/-- A jump to a block with its arity. -/
def JOK (bl : Map Blob) (j : Jmp) : Prop := ∃ b2, HoonMap.get bl j.there = some b2 ∧ j.args.length = b2.par.length

theorem rj_ok {bl : Map Blob} (hc : Closed bl) (har : ArityOK bl) : ∀ (n : Nat) (j j' : Jmp), JOK bl j →
    Opt.rewriteJump bl n j = some j' → JOK bl j'
  | 0, _, _, _, h => by simp [Opt.rewriteJump] at h
  | n + 1, j, j', hj, h => by
    rcases rj_cases h with rfl | ⟨nex, t, -, hnex, -, ht, -, h⟩
    · exact hj
    · have htj : t ∈ Opt.getJmps nex.fin := by rw [ht]; simp [Opt.getJmps]
      obtain ⟨b3, hb3⟩ := Option.isSome_iff_exists.1 (hc _ nex t hnex htj)
      exact rj_ok hc har n t j' ⟨b3, hb3, har _ nex t b3 hnex htj hb3⟩ h

theorem rj_noargs {bl : Map Blob} : ∀ (n : Nat) (j j' : Jmp), j.args = [] →
    Opt.rewriteJump bl n j = some j' → j'.args = []
  | 0, _, _, _, h => by simp [Opt.rewriteJump] at h
  | n + 1, j, j', hj, h => by
    rcases rj_cases h with rfl | ⟨nex, t, -, -, -, -, hta, h⟩
    · exact hj
    · exact rj_noargs n t j' hta h

theorem rj_strict {bl : Map Blob} {ρ : Nat → Nat} (hr : RkDown ρ bl) : ∀ (n : Nat) (j j' : Jmp),
    Opt.rewriteJump bl n j = some j' → j' ≠ j → ρ j'.there < ρ j.there
  | 0, _, _, h, _ => by simp [Opt.rewriteJump] at h
  | n + 1, j, j', h, hne => by
    rcases rj_cases h with rfl | ⟨nex, t, -, hnex, -, ht, -, h⟩
    · exact absurd rfl hne
    · have h1 := Opt.rewriteJump_rank hr n t j' h
      have h2 := hr j.there nex t hnex (by rw [ht]; simp [Opt.getJmps])
      omega

theorem rh_ok {bl : Map Blob} {rd : Nat → List Nat} (hc : Closed bl) (har : ArityOK bl) :
    ∀ (n : Nat) (j j' : Jmp), JOK bl j → Opt.rewriteHop bl rd n j = some j' → JOK bl j'
  | 0, _, _, _, h => by simp [Opt.rewriteHop] at h
  | n + 1, j, j', hj, h => by
    rcases rh_cases h with rfl | ⟨nex, t, s, hnex, ht, -, h⟩
    · exact hj
    · have htj : t ∈ Opt.getJmps nex.fin := by rw [ht]; simp [Opt.getJmps]
      obtain ⟨b3, hb3⟩ := Option.isSome_iff_exists.1 (hc _ nex t hnex htj)
      exact rh_ok hc har n (⟨t.args.map (Opt.passArg s), t.there⟩ : Jmp) j'
        ⟨b3, hb3, by simpa using har _ nex t b3 hnex htj hb3⟩ h

theorem rh_strict {bl : Map Blob} {rd : Nat → List Nat} {ρ : Nat → Nat} (hr : RkDown ρ bl) :
    ∀ (n : Nat) (j j' : Jmp), Opt.rewriteHop bl rd n j = some j' → j' ≠ j → ρ j'.there < ρ j.there
  | 0, _, _, h, _ => by simp [Opt.rewriteHop] at h
  | n + 1, j, j', h, hne => by
    rcases rh_cases h with rfl | ⟨nex, t, s, hnex, ht, -, h⟩
    · exact absurd rfl hne
    · have h1 := Opt.rewriteHop_rank hr n _ j' h
      have h2 := hr j.there nex t hnex (by rw [ht]; simp [Opt.getJmps])
      simp only at h1; omega

/-- What `middleFin` keeps: the kind of the end (and so its weight), the targets with their
arity, the two-way ends without arguments, and the rank sum, which falls when
the end changes. -/
theorem mf_facts {bl : Map Blob} {rd : Nat → List Nat} {fuel : Nat} {ρ : Nat → Nat} (hr : RkDown ρ bl)
    (hc : Closed bl) (har : ArityOK bl) {f f' : Termin} (hj : ∀ j ∈ Opt.getJmps f, JOK bl j)
    (h2 : twoWay f = true → ∀ j ∈ Opt.getJmps f, j.args = []) (h : Opt.middleFin bl rd fuel f = some f') :
    (twoWay f' = twoWay f ∧ twoW f' = twoW f) ∧ (∀ j ∈ Opt.getJmps f', JOK bl j) ∧
      (twoWay f' = true → ∀ j ∈ Opt.getJmps f', j.args = []) ∧
      finRk ρ f' ≤ finRk ρ f ∧ (f' ≠ f → finRk ρ f' < finRk ρ f) := by
  cases f with
  | clq s z o | eqq _ s z o | brn s z o | brz s z o =>
    simp only [Opt.middleFin, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨z', hz, o', ho, rfl⟩ := h
    have jz := rj_ok hc har _ z z' (hj z (by simp [Opt.getJmps])) hz
    have jo := rj_ok hc har _ o o' (hj o (by simp [Opt.getJmps])) ho
    have az := rj_noargs _ z z' (h2 rfl z (by simp [Opt.getJmps])) hz
    have ao := rj_noargs _ o o' (h2 rfl o (by simp [Opt.getJmps])) ho
    have rz := Opt.rewriteJump_rank hr _ _ _ hz
    have ro := Opt.rewriteJump_rank hr _ _ _ ho
    refine ⟨⟨rfl, rfl⟩, ?_, ?_, ?_, fun hne => ?_⟩
    · simp only [Opt.getJmps, List.mem_cons, List.not_mem_nil, or_false]
      rintro j (rfl | rfl) <;> assumption
    · simp only [Opt.getJmps, List.mem_cons, List.not_mem_nil, or_false]
      rintro - j (rfl | rfl) <;> assumption
    · simp only [finRk, Opt.getJmps, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · simp only [finRk, Opt.getJmps, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      by_cases ez : z' = z
      · have eo : o' ≠ o := fun eo => hne (by rw [ez, eo])
        have := rj_strict hr _ o o' ho eo; omega
      · have := rj_strict hr _ z z' hz ez; omega
  | hop t =>
    simp only [Opt.middleFin, Option.map_eq_some_iff] at h
    obtain ⟨t', ht, rfl⟩ := h
    have jt := rh_ok hc har _ t t' (hj t (by simp [Opt.getJmps])) ht
    have rt := Opt.rewriteHop_rank hr _ _ _ ht
    refine ⟨⟨rfl, rfl⟩, ?_, fun h => by simp [twoWay] at h, ?_, fun hne => ?_⟩
    · simp only [Opt.getJmps, List.mem_singleton]; rintro j rfl; exact jt
    · simp only [finRk, Opt.getJmps, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · have := rh_strict hr _ t t' ht (fun e => hne (by rw [e]))
      simp only [finRk, Opt.getJmps, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
  | _ =>
    simp only [Opt.middleFin, Option.some.injEq] at h
    subst h
    exact ⟨⟨rfl, rfl⟩, hj, h2, Nat.le_refl _, fun h => absurd rfl h⟩

variable [Opt.MapKeys Map]

theorem midFold_true (fuel : Nat) (bl : Map Blob) : ∀ (ks : List Nat) (c0 : Bool) (m0 : Map Blob)
    (r : Bool × Map Blob), ks.foldl (Opt.midStep fuel bl) (some (c0, m0)) = some r → r.1 = true →
    c0 = true ∨ ∃ k ∈ ks, ∃ b f', HoonMap.get bl k = some b ∧
      Opt.middleFin bl (Opt.readersOf bl) fuel b.fin = some f' ∧ f' ≠ b.fin
  | [], c0, m0, r, h, hr => by
    simp only [List.foldl_nil, Option.some.injEq] at h
    subst h; exact Or.inl hr
  | k :: ks, c0, m0, r, h, hr => by
    simp only [List.foldl_cons] at h
    cases hb : HoonMap.get bl k with
    | none => simp [Opt.midStep, hb, Opt.midFold_none] at h
    | some b =>
      cases he : Opt.middleFin bl (Opt.readersOf bl) fuel b.fin with
      | none => simp [Opt.midStep, hb, he, Opt.midFold_none] at h
      | some f' =>
        simp only [Opt.midStep, hb, he, Option.bind_some, Option.map_some] at h
        rcases midFold_true fuel bl ks _ _ r h hr with h1 | ⟨k', hk', b', f2, hb', he', hne⟩
        · simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
          rcases h1 with h1 | h1
          · exact Or.inl h1
          · exact Or.inr ⟨k, by simp, b, f', hb, he, h1⟩
        · exact Or.inr ⟨k', by simp [hk'], b', f2, hb', he', hne⟩

/-- **`+remove-empty-middle` keeps `StInv` and lowers the measure when it
reports a change.** -/
theorem mid_inv_step {ρ : Nat → Nat} {L : List Nat} {fuel : Nat} {bl bl' : Map Blob} {ch : Bool} (hI : StInv ρ L bl)
    (h : Opt.removeEmptyMiddle fuel bl = some (ch, bl')) :
    StInv ρ L bl' ∧ LexLe (mu ρ L bl') (mu ρ L bl) ∧ (ch = true → LexLt (mu ρ L bl') (mu ρ L bl)) := by
  have hb := Opt.mid_blocks h
  have hsome : ∀ k, (HoonMap.get bl' k).isSome = (HoonMap.get bl k).isSome := by
    intro k
    cases e : HoonMap.get bl k with
    | none => rw [(hb k).1 e]
    | some b => obtain ⟨_, _, e'⟩ := (hb k).2 b e; rw [e']; rfl
  have hjok : ∀ o b j, HoonMap.get bl o = some b → j ∈ Opt.getJmps b.fin → JOK bl j := by
    intro o b j hbo hj
    obtain ⟨b2, hb2⟩ := Option.isSome_iff_exists.1 (hI.closed o b j hbo hj)
    exact ⟨b2, hb2, hI.arity o b j b2 hbo hj hb2⟩
  have hF : ∀ k b, HoonMap.get bl k = some b → ∃ f', Opt.middleFin bl (Opt.readersOf bl) fuel b.fin = some f' ∧
      HoonMap.get bl' k = some { b with fin := f' } ∧
      ((twoWay f' = twoWay b.fin ∧ twoW f' = twoW b.fin) ∧ (∀ j ∈ Opt.getJmps f', JOK bl j) ∧
        (twoWay f' = true → ∀ j ∈ Opt.getJmps f', j.args = []) ∧
        finRk ρ f' ≤ finRk ρ b.fin ∧ (f' ≠ b.fin → finRk ρ f' < finRk ρ b.fin)) := by
    intro k b hbk
    obtain ⟨f', hf', e'⟩ := (hb k).2 b hbk
    exact ⟨f', hf', e', mf_facts hI.rank hI.closed hI.arity (fun j hj => hjok k b j hbk hj)
      (fun ht j hj => hI.two k b j hbk ht hj) hf'⟩
  have hback : ∀ k b', HoonMap.get bl' k = some b' → ∃ b f', HoonMap.get bl k = some b ∧
      Opt.middleFin bl (Opt.readersOf bl) fuel b.fin = some f' ∧ b' = { b with fin := f' } := by
    intro k b' hb'
    cases e : HoonMap.get bl k with
    | none => rw [(hb k).1 e] at hb'; cases hb'
    | some b =>
      obtain ⟨f', hf', e'⟩ := (hb k).2 b e
      rw [e'] at hb'; cases hb'
      exact ⟨b, f', rfl, hf', rfl⟩
  have hjok' : ∀ j, JOK bl j → JOK bl' j := by
    rintro j ⟨b2, hb2, hl⟩
    obtain ⟨f', -, e', -⟩ := hF _ b2 hb2
    exact ⟨_, e', hl⟩
  have hpw : ∀ o, presN (HoonMap.get bl' o) = presN (HoonMap.get bl o) ∧
      twoCnt (HoonMap.get bl' o) = twoCnt (HoonMap.get bl o) ∧ rkN ρ (HoonMap.get bl' o) ≤ rkN ρ (HoonMap.get bl o) := by
    intro o
    cases e1 : HoonMap.get bl o with
    | none => rw [(hb o).1 e1]; exact ⟨rfl, rfl, Nat.le_refl _⟩
    | some b =>
      obtain ⟨f', -, e', k1, -, -, k4, -⟩ := hF o b e1
      rw [e']
      exact ⟨by simp [presN], by simp [twoCnt, k1.2], by simpa [rkN] using k4⟩
  refine ⟨⟨fun o b' j' hb' hj' => ?_, fun o b' j' hb' hj' => ?_, fun o b' j' b2' hb' hj' hb2' => ?_,
    by rw [hsome]; exact hI.zero, fun o b' j' hb' ht hj' => ?_, fun o ho => hI.keys o (by rw [← hsome]; exact ho)⟩,
    ?_, fun hc => ?_⟩
  · obtain ⟨b, f', hbk, hf', rfl⟩ := hback o b' hb'
    obtain ⟨j, hj, hle⟩ := Opt.middleFin_rank hI.rank hf' j' hj'
    have := hI.rank o b j hbk hj
    omega
  · obtain ⟨b, f', hbk, hf', rfl⟩ := hback o b' hb'
    obtain ⟨f2, hf2, -, -, k2, -⟩ := hF o b hbk
    rw [hf'] at hf2; cases hf2
    obtain ⟨b2, hb2, -⟩ := hjok' j' (k2 j' hj')
    rw [hb2]; rfl
  · obtain ⟨b, f', hbk, hf', rfl⟩ := hback o b' hb'
    obtain ⟨f2, hf2, -, -, k2, -⟩ := hF o b hbk
    rw [hf'] at hf2; cases hf2
    obtain ⟨b2, hb2, hl⟩ := hjok' j' (k2 j' hj')
    rw [hb2] at hb2'; cases hb2'; exact hl
  · obtain ⟨b, f', hbk, hf', rfl⟩ := hback o b' hb'
    obtain ⟨f2, hf2, -, -, -, k3, -⟩ := hF o b hbk
    rw [hf'] at hf2; cases hf2
    exact k3 ht j' hj'
  · cases ch with
    | false =>
      refine Or.inr (mu_eq fun o _ => ?_)
      have := Opt.mid_same h o
      refine ⟨?_, ?_, ?_⟩ <;> rw [this]
    | true =>
      refine Or.inl ?_
      rcases midFold_true fuel bl _ false HoonMap.empty _ (by rw [← Opt.removeEmptyMiddle_eq]; exact h) rfl with
        h1 | ⟨k, -, b, f', hbk, hf', hne⟩
      · cases h1
      · obtain ⟨f2, hf2, e', -, -, -, -, k5⟩ := hF k b hbk
        rw [hf'] at hf2; cases hf2
        exact mu_lt3 (fun o _ => (hpw o).1) (fun o _ => (hpw o).2.1) (fun o _ => (hpw o).2.2)
          (hI.keys k (by simp [hbk])) (by rw [e', hbk]; exact k5 hne)
  · rcases midFold_true fuel bl _ false HoonMap.empty _ (by rw [← Opt.removeEmptyMiddle_eq]; exact h) hc with
      h1 | ⟨k, -, b, f', hbk, hf', hne⟩
    · cases h1
    · obtain ⟨f2, hf2, e', -, -, -, -, k5⟩ := hF k b hbk
      rw [hf'] at hf2; cases hf2
      exact mu_lt3 (fun o _ => (hpw o).1) (fun o _ => (hpw o).2.1) (fun o _ => (hpw o).2.2)
        (hI.keys k (by simp [hbk])) (by rw [e', hbk]; exact k5 hne)

end

end Compiler
end Formalization
