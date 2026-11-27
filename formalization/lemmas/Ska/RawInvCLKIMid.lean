import lemmas.Ska.RawInvCLSABase

/-!
# Distinct sure needs through `+split` and `+into` (for track G's `KIMid`)

README Gaps 14 (b), track D.  Track G's guard with calls asks (`KIMid`,
`Glue/GuardCallsB.lean`) that `+split` and `+into` keep `LzS (DN re)`: every
sure need of the lazy (the root, every fork, every bond) has distinct
registers, all below `re`.  `kimLz` has the constructor of G's `LzS` and
`kimDN` is G's `DN`, so G's bridge is an induction on either.

* `kim_splitSure`, `kim_intoSure`: one entry (`splitNeed_spec`,
  `keeps_splitNeed`; `intoNeed_rec` with `IntoOK`), with no hypothesis on
  the state.
* `kim_prune`: `+lazy-prune` only drops entries.
* `kim_splitLoop` (mutual with `kim_splitForks`, `kim_splitBonds`) and
  `kim_intoLoopL` (mutual with `kim_intoForks`, `kim_intoBonds`).
* **`kim_split`**, **`kim_into`**: the clauses `split` and `into` of
  `KIMid`, with no other hypothesis.
* `kim_ofE` (mutual with `kim_ofF`, `kim_ofB`: `kimLz` from the root's and
  the entries' sure needs), `kim_of_goalL` (the goal part of `IL` gives it).
* **`kim_run_plainIL`**, `kim_runM_plainIL`: the clause `run` on `PlainN`
  under the precondition of the liveness induction (`IL ∧ LG` of the goal,
  in place of `KIMid.run`'s `GD`), from `liveRun_plain`.  The clause with
  `GD` alone is checked, not proved: on the 2,856 `PlainN` nomms of `enumCX`
  under `%done`, `goalY`, `goalP`, `goalB` and three goals that meet `GD`
  but not `IL` (`goalDup`; a register at the root and at a bond; the root's
  registers swapped at a bond), every result meets `kimLz (kimDN re)`
  (0 failures); the checker bites (distinct registers ACROSS entries fails
  8, 24, 32 runs under the three, the bound at the old `re` 2,848).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The predicate -/

/-- **Every sure need of a lazy meets `Q`** (the constructor of track G's
`LzS`). -/
inductive kimLz (Q : Sure S → Prop) : Lazy S → Prop
  | mk {s : Sure S} {fork : List ((Nat × Lazy S) × (Nat × Lazy S))} {bond : List (Nat × Lazy S)} :
      Q s → (∀ e ∈ fork, kimLz Q e.1.2) → (∀ e ∈ fork, kimLz Q e.2.2) → (∀ e ∈ bond, kimLz Q e.2) →
      kimLz Q (Lazy.mk s fork bond)

/-- **Distinct registers, all below `r`** (track G's `DN`). -/
def kimDN (r : Nat) (s : Sure S) : Prop := Distinct s.ned ∧ NB r s.ned

theorem kimDN.up {r r' : Nat} {s : Sure S} (h : kimDN r s) (hr : r ≤ r') : kimDN r' s :=
  ⟨h.1, fun x hx => Nat.lt_of_lt_of_le (h.2 x hx) hr⟩

theorem kimLz.imp {P Q : Sure S → Prop} (hpq : ∀ s, P s → Q s) {l : Lazy S} (h : kimLz P l) : kimLz Q l := by
  induction h with
  | mk h1 _ _ _ i2 i3 i4 => exact kimLz.mk (hpq _ h1) i2 i3 i4

theorem kimLz.up {r r' : Nat} {l : Lazy S} (h : kimLz (kimDN r) l) (hr : r ≤ r') : kimLz (kimDN r') l :=
  h.imp fun _ hs => hs.up hr

theorem kimLz.root {Q : Sure S → Prop} {l : Lazy S} (h : kimLz Q l) : Q l.sure := by
  cases h with
  | mk h1 _ _ _ => exact h1

theorem kim_ofSure {Q : Sure S → Prop} {s : Sure S} (h : Q s) : kimLz Q (ofSure s) :=
  kimLz.mk h (fun _ he => absurd he List.not_mem_nil) (fun _ he => absurd he List.not_mem_nil)
    (fun _ he => absurd he List.not_mem_nil)

/-- `+lazy-prune` only drops entries. -/
theorem kim_prune {Q : Sure S → Prop} {s : Sure S} {f : List (ForkE S)} {b : List (Nat × Lazy S)}
    (hs : Q s) (hf : ∀ e ∈ f, kimLz Q e.1.2 ∧ kimLz Q e.2.2) (hb : ∀ e ∈ b, kimLz Q e.2) :
    kimLz Q (lazyPrune (mk s f b)) := by
  unfold lazyPrune
  exact kimLz.mk hs (fun e he => (hf e (List.mem_filter.mp he).1).1)
    (fun e he => (hf e (List.mem_filter.mp he).1).2) (fun e he => hb e (List.mem_filter.mp he).1)

/-! ## One entry -/

theorem kim_splitSure {s : Sure S} {o : Nat} {g g' : Comp.Gen Map} {sh st : Sure S}
    (hs : kimDN g.re s) (h : splitSure s o g = some ((sh, st), g')) :
    g.re ≤ g'.re ∧ kimDN g'.re sh ∧ kimDN g'.re st := by
  unfold splitSure at h
  obtain ⟨⟨lh, lt⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨⟨nh, nt⟩, g2⟩, h2, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
  obtain ⟨-, -, le, -, -, -, sem, -⟩ := splitNeed_spec h2
  obtain ⟨-, nb1, nb2⟩ := keeps_splitNeed hs.2 h2
  obtain ⟨d1, d2, -, -⟩ := sem hs.1 hs.2
  exact ⟨le, ⟨d1, nb1⟩, ⟨d2, nb2⟩⟩

theorem kim_intoSure {axe : Nat} {s : Sure S} {o : Nat} {g g' : Comp.Gen Map} {sd sr : Sure S}
    (hs : kimDN g.re s) (h : intoSure axe s o g = some ((sd, sr), g')) :
    g.re ≤ g'.re ∧ kimDN g'.re sd ∧ kimDN g'.re sr := by
  unfold intoSure at h
  obtain ⟨⟨ld, lr⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨⟨nd, nr⟩, g2⟩, h2, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
  obtain ⟨-, ops, g1, I, e1, -, -, -, -⟩ := intoNeed_rec h2
  obtain ⟨dd, dr, -⟩ := I.sem hs.1 hs.2
  have le : g.re ≤ g2.re := by rw [e1]; exact I.le
  refine ⟨le, ⟨dd, fun y hy => ?_⟩, ⟨dr, fun y hy => ?_⟩⟩
  · rcases I.md y hy with h | h
    · exact Nat.lt_of_lt_of_le (hs.2 y h) le
    · rw [e1]; exact h.2
  · rcases I.mr y hy with h | h
    · exact Nat.lt_of_lt_of_le (hs.2 y h) le
    · rw [e1]; exact h.2

/-! ## The walks -/

mutual
theorem kim_splitLoop : ∀ (l : Lazy S) (o : Nat) (g g' : Comp.Gen Map) (x : Lazy S × Lazy S),
    kimLz (kimDN g.re) l → splitLoop l o g = some (x, g') →
    g.re ≤ g'.re ∧ kimLz (kimDN g'.re) x.1 ∧ kimLz (kimDN g'.re) x.2
  | mk s f b, o, g, g', x, hl, h => by
    cases hl with
    | mk hs hfy hfn hb =>
    rw [splitLoop] at h
    obtain ⟨⟨sh, st⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨le1, dh, dt⟩ := kim_splitSure hs h1
    by_cases hfb : (f.isEmpty && b.isEmpty) = true
    · simp only [hfb, if_true, pure_apply, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨le1, kim_ofSure dh, kim_ofSure dt⟩
    · simp only [hfb, Bool.false_eq_true, if_false] at h
      obtain ⟨⟨fh, ft⟩, g2, h2, h⟩ := bind_some h
      obtain ⟨le2, fH, fT⟩ := kim_splitForks f g1 g2 _
        (fun e he => ⟨(hfy e he).up le1, (hfn e he).up le1⟩) h2
      obtain ⟨⟨bh, bt⟩, g3, h3, h⟩ := bind_some h
      obtain ⟨le3, bH, bT⟩ := kim_splitBonds b g2 g3 _ (fun e he => (hb e he).up (Nat.le_trans le1 le2)) h3
      simp only [pure_apply, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      refine ⟨Nat.le_trans le1 (Nat.le_trans le2 le3), ?_, ?_⟩
      · exact kim_prune (dh.up (Nat.le_trans le2 le3))
          (fun e he => ⟨(fH e he).1.up le3, (fH e he).2.up le3⟩) bH
      · exact kim_prune (dt.up (Nat.le_trans le2 le3))
          (fun e he => ⟨(fT e he).1.up le3, (fT e he).2.up le3⟩) bT

theorem kim_splitForks : ∀ (f : List (ForkE S)) (g g' : Comp.Gen Map) (x : List (ForkE S) × List (ForkE S)),
    (∀ e ∈ f, kimLz (kimDN g.re) e.1.2 ∧ kimLz (kimDN g.re) e.2.2) → splitForks f g = some (x, g') →
    g.re ≤ g'.re ∧ (∀ e ∈ x.1, kimLz (kimDN g'.re) e.1.2 ∧ kimLz (kimDN g'.re) e.2.2) ∧
      (∀ e ∈ x.2, kimLz (kimDN g'.re) e.1.2 ∧ kimLz (kimDN g'.re) e.2.2)
  | [], g, g', x, _, h => by
    rw [splitForks] at h
    simp only [pure_apply, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨Nat.le_refl _, fun e he => absurd he List.not_mem_nil, fun e he => absurd he List.not_mem_nil⟩
  | ((oy, y), (on, n)) :: rest, g, g', x, hf, h => by
    rw [splitForks] at h
    have h0 := hf _ List.mem_cons_self
    obtain ⟨⟨yh, yt⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨le1, yH, yT⟩ := kim_splitLoop y oy g g1 _ h0.1 h1
    obtain ⟨⟨nh, nt⟩, g2, h2, h⟩ := bind_some h
    obtain ⟨le2, nH, nT⟩ := kim_splitLoop n on g1 g2 _ (h0.2.up le1) h2
    obtain ⟨⟨rh, rt⟩, g3, h3, h⟩ := bind_some h
    obtain ⟨le3, rH, rT⟩ := kim_splitForks rest g2 g3 _
      (fun e he => ⟨(hf e (List.mem_cons_of_mem _ he)).1.up (Nat.le_trans le1 le2),
        (hf e (List.mem_cons_of_mem _ he)).2.up (Nat.le_trans le1 le2)⟩) h3
    simp only [pure_apply, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    refine ⟨Nat.le_trans le1 (Nat.le_trans le2 le3), fun e he => ?_, fun e he => ?_⟩
    · rcases List.mem_cons.mp he with rfl | he
      · exact ⟨yH.up (Nat.le_trans le2 le3), nH.up le3⟩
      · exact rH e he
    · rcases List.mem_cons.mp he with rfl | he
      · exact ⟨yT.up (Nat.le_trans le2 le3), nT.up le3⟩
      · exact rT e he

theorem kim_splitBonds : ∀ (b : List (Nat × Lazy S)) (g g' : Comp.Gen Map)
    (x : List (Nat × Lazy S) × List (Nat × Lazy S)),
    (∀ e ∈ b, kimLz (kimDN g.re) e.2) → splitBonds b g = some (x, g') →
    g.re ≤ g'.re ∧ (∀ e ∈ x.1, kimLz (kimDN g'.re) e.2) ∧ (∀ e ∈ x.2, kimLz (kimDN g'.re) e.2)
  | [], g, g', x, _, h => by
    rw [splitBonds] at h
    simp only [pure_apply, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨Nat.le_refl _, fun e he => absurd he List.not_mem_nil, fun e he => absurd he List.not_mem_nil⟩
  | (o, l) :: rest, g, g', x, hb, h => by
    rw [splitBonds] at h
    obtain ⟨⟨lh, lt⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨le1, lH, lT⟩ := kim_splitLoop l o g g1 _ (hb _ List.mem_cons_self) h1
    obtain ⟨⟨rh, rt⟩, g2, h2, h⟩ := bind_some h
    obtain ⟨le2, rH, rT⟩ := kim_splitBonds rest g1 g2 _
      (fun e he => (hb e (List.mem_cons_of_mem _ he)).up le1) h2
    simp only [pure_apply, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    refine ⟨Nat.le_trans le1 le2, fun e he => ?_, fun e he => ?_⟩
    · rcases List.mem_cons.mp he with rfl | he
      · exact lH.up le2
      · exact rH e he
    · rcases List.mem_cons.mp he with rfl | he
      · exact lT.up le2
      · exact rT e he
end

mutual
theorem kim_intoLoopL (axe : Nat) : ∀ (l : Lazy S) (o : Nat) (g g' : Comp.Gen Map) (x : Lazy S × Lazy S),
    kimLz (kimDN g.re) l → intoLoopL axe l o g = some (x, g') →
    g.re ≤ g'.re ∧ kimLz (kimDN g'.re) x.1 ∧ kimLz (kimDN g'.re) x.2
  | mk s f b, o, g, g', x, hl, h => by
    cases hl with
    | mk hs hfy hfn hb =>
    rw [intoLoopL] at h
    obtain ⟨⟨sh, st⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨le1, dh, dt⟩ := kim_intoSure hs h1
    by_cases hfb : (f.isEmpty && b.isEmpty) = true
    · simp only [hfb, if_true, pure_apply, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨le1, kim_ofSure dh, kim_ofSure dt⟩
    · simp only [hfb, Bool.false_eq_true, if_false] at h
      obtain ⟨⟨fh, ft⟩, g2, h2, h⟩ := bind_some h
      obtain ⟨le2, fH, fT⟩ := kim_intoForks axe f g1 g2 _
        (fun e he => ⟨(hfy e he).up le1, (hfn e he).up le1⟩) h2
      obtain ⟨⟨bh, bt⟩, g3, h3, h⟩ := bind_some h
      obtain ⟨le3, bH, bT⟩ := kim_intoBonds axe b g2 g3 _ (fun e he => (hb e he).up (Nat.le_trans le1 le2)) h3
      simp only [pure_apply, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      refine ⟨Nat.le_trans le1 (Nat.le_trans le2 le3), ?_, ?_⟩
      · exact kim_prune (dh.up (Nat.le_trans le2 le3))
          (fun e he => ⟨(fH e he).1.up le3, (fH e he).2.up le3⟩) bH
      · exact kim_prune (dt.up (Nat.le_trans le2 le3))
          (fun e he => ⟨(fT e he).1.up le3, (fT e he).2.up le3⟩) bT

theorem kim_intoForks (axe : Nat) : ∀ (f : List (ForkE S)) (g g' : Comp.Gen Map)
    (x : List (ForkE S) × List (ForkE S)),
    (∀ e ∈ f, kimLz (kimDN g.re) e.1.2 ∧ kimLz (kimDN g.re) e.2.2) → intoForks axe f g = some (x, g') →
    g.re ≤ g'.re ∧ (∀ e ∈ x.1, kimLz (kimDN g'.re) e.1.2 ∧ kimLz (kimDN g'.re) e.2.2) ∧
      (∀ e ∈ x.2, kimLz (kimDN g'.re) e.1.2 ∧ kimLz (kimDN g'.re) e.2.2)
  | [], g, g', x, _, h => by
    rw [intoForks] at h
    simp only [pure_apply, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨Nat.le_refl _, fun e he => absurd he List.not_mem_nil, fun e he => absurd he List.not_mem_nil⟩
  | ((oy, y), (on, n)) :: rest, g, g', x, hf, h => by
    rw [intoForks] at h
    have h0 := hf _ List.mem_cons_self
    obtain ⟨⟨yh, yt⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨le1, yH, yT⟩ := kim_intoLoopL axe y oy g g1 _ h0.1 h1
    obtain ⟨⟨nh, nt⟩, g2, h2, h⟩ := bind_some h
    obtain ⟨le2, nH, nT⟩ := kim_intoLoopL axe n on g1 g2 _ (h0.2.up le1) h2
    obtain ⟨⟨rh, rt⟩, g3, h3, h⟩ := bind_some h
    obtain ⟨le3, rH, rT⟩ := kim_intoForks axe rest g2 g3 _
      (fun e he => ⟨(hf e (List.mem_cons_of_mem _ he)).1.up (Nat.le_trans le1 le2),
        (hf e (List.mem_cons_of_mem _ he)).2.up (Nat.le_trans le1 le2)⟩) h3
    simp only [pure_apply, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    refine ⟨Nat.le_trans le1 (Nat.le_trans le2 le3), fun e he => ?_, fun e he => ?_⟩
    · rcases List.mem_cons.mp he with rfl | he
      · exact ⟨yH.up (Nat.le_trans le2 le3), nH.up le3⟩
      · exact rH e he
    · rcases List.mem_cons.mp he with rfl | he
      · exact ⟨yT.up (Nat.le_trans le2 le3), nT.up le3⟩
      · exact rT e he

theorem kim_intoBonds (axe : Nat) : ∀ (b : List (Nat × Lazy S)) (g g' : Comp.Gen Map)
    (x : List (Nat × Lazy S) × List (Nat × Lazy S)),
    (∀ e ∈ b, kimLz (kimDN g.re) e.2) → intoBonds axe b g = some (x, g') →
    g.re ≤ g'.re ∧ (∀ e ∈ x.1, kimLz (kimDN g'.re) e.2) ∧ (∀ e ∈ x.2, kimLz (kimDN g'.re) e.2)
  | [], g, g', x, _, h => by
    rw [intoBonds] at h
    simp only [pure_apply, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨Nat.le_refl _, fun e he => absurd he List.not_mem_nil, fun e he => absurd he List.not_mem_nil⟩
  | (o, l) :: rest, g, g', x, hb, h => by
    rw [intoBonds] at h
    obtain ⟨⟨lh, lt⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨le1, lH, lT⟩ := kim_intoLoopL axe l o g g1 _ (hb _ List.mem_cons_self) h1
    obtain ⟨⟨rh, rt⟩, g2, h2, h⟩ := bind_some h
    obtain ⟨le2, rH, rT⟩ := kim_intoBonds axe rest g1 g2 _
      (fun e he => (hb e (List.mem_cons_of_mem _ he)).up le1) h2
    simp only [pure_apply, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    refine ⟨Nat.le_trans le1 le2, fun e he => ?_, fun e he => ?_⟩
    · rcases List.mem_cons.mp he with rfl | he
      · exact lH.up le2
      · exact rH e he
    · rcases List.mem_cons.mp he with rfl | he
      · exact lT.up le2
      · exact rT e he
end

/-! ## The clauses of `KIMid` -/

/-- **`+split` keeps distinct sure needs below `re`** (`KIMid.split`). -/
theorem kim_split : ∀ (nex : NextL S) (g g' : Comp.Gen Map) (x : Lazy S × Lazy S × Nat),
    kimLz (kimDN g.re) nex.laz → splitL nex g = some (x, g') →
    kimLz (kimDN g'.re) x.1 ∧ kimLz (kimDN g'.re) x.2.1 := by
  intro nex g g' x hl h
  unfold splitL at h
  obtain ⟨o, ge, he, h⟩ := bind_some h
  rw [emit_apply] at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨⟨hh, tt⟩, g2, h2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  obtain ⟨-, H, T⟩ := kim_splitLoop nex.laz g.bo (g.emitted _) _ _ hl h2
  exact ⟨H, T⟩

/-- **`+into` keeps distinct sure needs below `re`** (`KIMid.into`). -/
theorem kim_into : ∀ (nex : NextL S) (axe : Nat) (g g' : Comp.Gen Map) (x : Lazy S × Lazy S × Nat),
    kimLz (kimDN g.re) nex.laz → intoL nex axe g = some (x, g') →
    kimLz (kimDN g'.re) x.1 ∧ kimLz (kimDN g'.re) x.2.1 := by
  intro nex axe g g' x hl h
  unfold intoL at h
  obtain ⟨o, ge, he, h⟩ := bind_some h
  rw [emit_apply] at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨⟨dd, rr⟩, g2, h2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  obtain ⟨-, H, T⟩ := kim_intoLoopL axe nex.laz g.bo (g.emitted _) _ _ hl h2
  exact ⟨H, T⟩


/-! ## From the entries, and the clause `run` under `IL` -/

mutual
/-- `kimLz` from the root's and the entries' sure needs. -/
theorem kim_ofE {Q : Sure S → Prop} : ∀ (l : Lazy S), Q l.sure → (∀ e ∈ entries l, Q e.2.sure) → kimLz Q l
  | mk s f b, hs, he => by
    have hF := kim_ofF f (fun e h => he e (by simp only [entries, List.mem_append]; exact Or.inr h))
    exact kimLz.mk hs hF.1 hF.2 (kim_ofB b (fun e h => he e (by simp only [entries, List.mem_append]; exact Or.inl h)))

theorem kim_ofF {Q : Sure S → Prop} : ∀ (f : List (ForkE S)), (∀ e ∈ forkEntries f, Q e.2.sure) →
    (∀ e ∈ f, kimLz Q e.1.2) ∧ (∀ e ∈ f, kimLz Q e.2.2)
  | [], _ => ⟨fun e he => absurd he List.not_mem_nil, fun e he => absurd he List.not_mem_nil⟩
  | ((oy, y), (on, n)) :: rest, h => by
    have hy := kim_ofE y (h (oy, y) (by simp [forkEntries]))
      (fun e he => h e (by simp only [forkEntries, List.mem_append, List.mem_cons]; exact Or.inl (Or.inl (Or.inr he))))
    have hn := kim_ofE n (h (on, n) (by simp [forkEntries]))
      (fun e he => h e (by simp only [forkEntries, List.mem_append, List.mem_cons]; exact Or.inl (Or.inr (Or.inr he))))
    have hr := kim_ofF rest (fun e he => h e (by simp only [forkEntries, List.mem_append]; exact Or.inr he))
    refine ⟨fun e he => ?_, fun e he => ?_⟩
    · rcases List.mem_cons.mp he with rfl | he
      · exact hy
      · exact hr.1 e he
    · rcases List.mem_cons.mp he with rfl | he
      · exact hn
      · exact hr.2 e he

theorem kim_ofB {Q : Sure S → Prop} : ∀ (b : List (Nat × Lazy S)), (∀ e ∈ bondEntries b, Q e.2.sure) →
    ∀ e ∈ b, kimLz Q e.2
  | [], _ => fun e he => absurd he List.not_mem_nil
  | (o, l) :: rest, h => by
    have hl := kim_ofE l (h (o, l) (by simp [bondEntries]))
      (fun e he => h e (by simp only [bondEntries, List.mem_append, List.mem_cons]; exact Or.inl (Or.inr he)))
    have hr := kim_ofB rest (fun e he => h e (by simp only [bondEntries, List.mem_append]; exact Or.inr he))
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hl
    · exact hr e he
end

/-- **The goal part of `IL` gives `kimLz (kimDN re)` of the goal's lazy.** -/
theorem kim_of_goalL {laz : Lazy S} {th : Jmp} {g : Comp.Gen Map} (h : GoalL g (CGoalL.next laz th)) :
    kimLz (kimDN g.re) laz := by
  obtain ⟨-, -, hent⟩ := h
  have hr := hent _ List.mem_cons_self
  exact kim_ofE laz ⟨hr.2.1, fun r hm => (hr.2.2 r hm).1⟩ (fun e he =>
    have he' := hent e (List.mem_cons_of_mem _ he)
    ⟨he'.2.1, fun r hm => (he'.2.2 r hm).1⟩)

/-- **The clause `run` on `PlainN` from the precondition of the liveness
induction** (`IL` and `LG` of the goal; at the top, `il_gen0` and `trivial`):
the result's lazy has distinct sure needs below `re`.  From `liveRun_plain`
(the `JL` half). -/
theorem kim_run_plainIL (env : CallEnv) : ∀ (nm : Nomm), PlainN nm → ∀ (sup : Option Nomm)
    (K : Nat → Nat → Prop) (goal : CGoalL S) (region : List Nat) (g g' : Comp.Gen Map) (x : NextL S),
    IL K goal g → LG goal g → runLC env sup nm goal region g = some (x, g') → kimLz (kimDN g'.re) x.laz :=
  fun nm hp sup K goal region g g' x hI hL h =>
    kim_of_goalL ((liveRun_plain env nm hp sup K goal region g g' x hI hL h).1.goal : GoalL g' x.goal)

/-- The same at `runLCM env true` (`PlainN` has no direct call). -/
theorem kim_runM_plainIL (env : CallEnv) : ∀ (nm : Nomm), PlainN nm → ∀ (sup : Option Nomm)
    (K : Nat → Nat → Prop) (goal : CGoalL S) (region : List Nat) (g g' : Comp.Gen Map) (x : NextL S),
    IL K goal g → LG goal g → runLCM env true sup nm goal region g = some (x, g') → kimLz (kimDN g'.re) x.laz :=
  fun nm hp sup K goal region g g' x hI hL h => by
    rw [runLCM_true env (plainN_noDirect nm hp) sup goal region] at h
    exact kim_run_plainIL env nm hp sup K goal region g g' x hI hL h

end Raw
end SkaModel
end Formalization
