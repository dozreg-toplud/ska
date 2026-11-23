import lemmas.Ska.CompClean

/-!
# What `+copy-need-make-ops` does

`copyNeed_spec`: the need `res` that `+copy-need-make-ops` makes of two
needs `l` and `r`, and the ops `A` it puts in front of the accumulated ops.
When the two needs are clean (no `pair none none`), have no register in
common and only registers allocated before, `res` is distinct, it asks a
noun for the cells that `l` and `r` ask together, and the ops, run from
registers that hold a noun as `res` asks, hold it as `l` and `r` ask,
changing only registers of `l` and `r` (`CopySem`).

The ops run in the order of the list, so the ops made last run first: those
of the tail before those of the head, before the move of the whole.  No op
writes a register that `res` names, so the order does not matter, but it is
followed as it is.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- What the ops `A` of a copy do. -/
def CopySem (Map : Type → Type) [HoonMap Map] (l r res : Need) (A : List Pole) : Prop :=
  ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
    (R : Map Noun) (s : Noun), HoldsN res R s → ∃ R', Runs lib O c gul st t A R R' ∧ HoldsN l R' s ∧
      HoldsN r R' s ∧ ∀ y, ¬ NMem (Need.pair l r) y → SkaModel.read y R' = SkaModel.read y R

/-- What a copy assumes of its two needs. -/
structure CopyPre (l r : Need) (lo : Nat) : Prop where
  cl : Clean l
  cr : Clean r
  d : Distinct (Need.pair l r)
  lo : ∀ y, NMem (Need.pair l r) y → y < lo

/-- What a copy gives. -/
structure CopyOK (l r : Need) (g g' : Gen Map) (res : Need) (A : List Pole) : Prop where
  gen : g' = { g with re := g'.re }
  le : g.re ≤ g'.re
  mem : ∀ y, NMem res y → NMem (Need.pair l r) y ∨ (g.re ≤ y ∧ y < g'.re)
  sem : CopyPre l r g.re → Distinct res ∧ (res = Need.none → l = Need.none ∧ r = Need.none) ∧
    (∀ s, Comp.Fits res s ↔ Comp.Fits l s ∧ Comp.Fits r s) ∧ CopySem Map l r res A

theorem copySem_swap {l r res : Need} {A : List Pole} (h : CopySem Map l r res A) : CopySem Map r l res A :=
  fun lib σ O c gul st t R s hs =>
    let ⟨R', h1, h2, h3, h4⟩ := h lib σ O c gul st t R s hs
    ⟨R', h1, h3, h2, fun y hy => h4 y (fun h => hy (Or.symm h))⟩

/-- A move of the whole from the top register of `res` into `d`, the
register of the other need. -/
theorem copySem_mov {M res : Need} {m d : Nat}
    (hres : ∀ (R : Map Noun) s, HoldsN res R s → SkaModel.read m R = some s ∧ HoldsN M R s)
    (hd : ¬ NMem M d) : CopySem Map (Need.this d) M res [Pole.mov m d] := by
  intro lib σ O c gul st t R s hs
  obtain ⟨hm, hM⟩ := hres R s hs
  refine ⟨store d s R, runs_mov hm, read_store_eq _ _ _, HoldsN.agree M (fun y hy => read_store_ne
    (fun e => by subst e; exact hd hy) _ _) hM, fun y hy => read_store_ne (fun e => hy (Or.inl e)) _ _⟩

/-- Two halves: the tail's ops, then the head's. -/
theorem copySem_halves {hl hr tl tr ra rb : Need} {Ah At : List Pole}
    (sh : CopySem Map hl hr ra Ah) (stl : CopySem Map tl tr rb At)
    (d1 : ∀ y, NMem ra y → ¬ NMem (Need.pair tl tr) y)
    (d2 : ∀ y, NMem (Need.pair tl tr) y → ¬ NMem (Need.pair hl hr) y)
    (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
    (R : Map Noun) (a b : Noun) (ha : HoldsN ra R a) (hb : HoldsN rb R b) :
    ∃ R', Runs lib O c gul st t (At ++ Ah) R R' ∧ HoldsN hl R' a ∧ HoldsN hr R' a ∧ HoldsN tl R' b ∧
      HoldsN tr R' b ∧ ∀ y, ¬ NMem (Need.pair hl hr) y → ¬ NMem (Need.pair tl tr) y →
        SkaModel.read y R' = SkaModel.read y R := by
  obtain ⟨R1, r1, ht1, ht2, u1⟩ := stl lib σ O c gul st t R b hb
  have ha1 : HoldsN ra R1 a := HoldsN.agree ra (fun y hy => u1 y (d1 y hy)) ha
  obtain ⟨R2, r2, hh1, hh2, u2⟩ := sh lib σ O c gul st t R1 a ha1
  have k : ∀ y, NMem (Need.pair tl tr) y → SkaModel.read y R2 = SkaModel.read y R1 :=
    fun y hy => u2 y (d2 y hy)
  refine ⟨R2, r1.append r2, hh1, hh2, HoldsN.agree tl (fun y hy => k y (Or.inl hy)) ht1,
    HoldsN.agree tr (fun y hy => k y (Or.inr hy)) ht2, fun y n1 n2 => ?_⟩
  rw [u2 y n1, u1 y n2]

/-- Registers in two disjoint parts or two disjoint ranges are disjoint. -/
theorem disj_join {a b L1 L2 : Need} {lo mid hi : Nat}
    (m1 : ∀ y, NMem a y → NMem L1 y ∨ (lo ≤ y ∧ y < mid))
    (m2 : ∀ y, NMem b y → NMem L2 y ∨ (mid ≤ y ∧ y < hi))
    (dL : ∀ y, NMem L1 y → ¬ NMem L2 y) (l1 : ∀ y, NMem L1 y → y < lo) (l2 : ∀ y, NMem L2 y → y < lo)
    (hm : lo ≤ mid) : ∀ y, NMem a y → ¬ NMem b y := by
  intro y ha hb
  rcases m1 y ha with h1 | ⟨h1, h1'⟩ <;> rcases m2 y hb with h2 | ⟨h2, h2'⟩
  · exact dL y h1 h2
  · have := l1 y h1; omega
  · have := l2 y h2; omega
  · omega

theorem not_mem_join {a L : Need} {lo hi x : Nat} (m : ∀ y, NMem a y → NMem L y ∨ (lo ≤ y ∧ y < hi))
    (hL : ¬ NMem L x) (hx : x < lo) : ¬ NMem a x := fun ha => by
  rcases m x ha with h | ⟨h, _⟩
  · exact hL h
  · omega

theorem gen_trans {g g1 g2 : Gen Map} (h1 : g1 = { g with re := g1.re }) (h2 : g2 = { g1 with re := g2.re }) :
    g2 = { g with re := g2.re } := by
  rw [h2]; rw [h1]

/-- A need that takes a cell apart into `a` and `b`. -/
def CellN (N a b : Need) : Prop := N = Need.pair a b ∨ ∃ x, N = Need.both x a b

theorem fits_cellN {N a b : Need} (h : CellN N a b) (s : Noun) :
    Comp.Fits N s ↔ ∃ u v, s = C u v ∧ Comp.Fits a u ∧ Comp.Fits b v := by
  rcases h with rfl | ⟨x, rfl⟩ <;> cases s <;> simp [Comp.Fits] <;>
    exact ⟨fun h => ⟨_, _, ⟨rfl, rfl⟩, h⟩, fun ⟨u, v, ⟨e1, e2⟩, h⟩ => by subst e1 e2; exact h⟩

theorem fits_rec {res l r a1 a2 hl hr tl tr : Need} (hres : CellN res a1 a2) (hl' : CellN l hl tl)
    (hr' : CellN r hr tr) (F1 : ∀ s, Comp.Fits a1 s ↔ Comp.Fits hl s ∧ Comp.Fits hr s)
    (F2 : ∀ s, Comp.Fits a2 s ↔ Comp.Fits tl s ∧ Comp.Fits tr s) :
    ∀ s, Comp.Fits res s ↔ Comp.Fits l s ∧ Comp.Fits r s := by
  intro s
  rw [fits_cellN hres, fits_cellN hl', fits_cellN hr']
  constructor
  · rintro ⟨u, v, rfl, f1, f2⟩
    exact ⟨⟨u, v, rfl, ((F1 u).1 f1).1, ((F2 v).1 f2).1⟩, ⟨u, v, rfl, ((F1 u).1 f1).2, ((F2 v).1 f2).2⟩⟩
  · rintro ⟨⟨u, v, rfl, f1, f2⟩, ⟨u', v', e, f1', f2'⟩⟩
    simp only [Noun.cell.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨u, v, rfl, (F1 u).2 ⟨f1, f1'⟩, (F2 v).2 ⟨f2, f2'⟩⟩

theorem nmem_consNeed {a b : Need} {y : Nat} (h : NMem (consNeed a b) y) : NMem a y ∨ NMem b y := by
  unfold consNeed at h
  split at h
  · exact h.elim
  · exact h

theorem copyOK_left (l : Need) (g : Gen Map) : CopyOK l Need.none g g l [] where
  gen := rfl
  le := Nat.le_refl _
  mem := fun y hy => Or.inl (Or.inl hy)
  sem := fun P => ⟨P.d.1, fun e => ⟨e, rfl⟩, fun s => by simp [Comp.Fits],
    fun lib σ O c gul st t R s hs => ⟨R, Runs.nil R, hs, trivial, fun _ _ => rfl⟩⟩

theorem copyOK_right (r : Need) (g : Gen Map) : CopyOK Need.none r g g r [] where
  gen := rfl
  le := Nat.le_refl _
  mem := fun y hy => Or.inl (Or.inr hy)
  sem := fun P => ⟨P.d.2.1, fun e => ⟨rfl, e⟩, fun s => by simp [Comp.Fits],
    fun lib σ O c gul st t R s hs => ⟨R, Runs.nil R, trivial, hs, fun _ _ => rfl⟩⟩

theorem holds_both_top {x : Nat} {a b : Need} {R : Map Noun} {s : Noun} (h : HoldsN (Need.both x a b) R s) :
    SkaModel.read x R = some s ∧ HoldsN (Need.both x a b) R s := by
  cases s with
  | atom _ => exact h.elim
  | cell u v => exact ⟨h.1, h⟩

theorem holds_both_pair {x : Nat} {a b : Need} {R : Map Noun} {s : Noun} (h : HoldsN (Need.both x a b) R s) :
    SkaModel.read x R = some s ∧ HoldsN (Need.pair a b) R s := by
  cases s with
  | atom _ => exact h.elim
  | cell u v => exact ⟨h.1, h.2⟩

theorem fits_both_pair (x : Nat) (a b : Need) (s : Noun) :
    Comp.Fits (Need.both x a b) s ↔ Comp.Fits (Need.pair a b) s := by
  cases s <;> simp [Comp.Fits]

/-- **`+copy-need-make-ops`.** -/
theorem copyNeed_spec : ∀ (l r : Need) (ops : List Pole) (g g' : Gen Map) (x : Need × List Pole),
    copyNeed l r ops g = some (x, g') → ∃ A, x.2 = A ++ ops ∧ CopyOK l r g g' x.1 A := by
  intro l
  induction l with
  | none =>
    intro r ops g g' x h
    simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, copyOK_right r g⟩
  | this rl =>
    intro r ops g g' x h
    cases r with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], rfl, copyOK_left _ g⟩
    | this rr =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      dsimp only
      refine ⟨[Pole.mov rl rr], rfl, rfl, Nat.le_refl _, fun y hy => Or.inl (Or.inl hy), fun P => ?_⟩
      refine ⟨trivial, (fun e => by simp at e), (fun s => by simp [Comp.Fits]), copySem_swap (copySem_mov
        (fun R s hs => ⟨hs, hs⟩) (fun e => P.d.2.2 rr e rfl))⟩
    | both xr hr tr =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      dsimp only
      refine ⟨[Pole.mov xr rl], rfl, rfl, Nat.le_refl _, fun y hy => Or.inl (Or.inr hy), fun P => ?_⟩
      exact ⟨P.d.2.1, (fun e => by simp at e), (fun s => by simp [Comp.Fits]),
        copySem_mov (fun R s hs => holds_both_top hs) (fun e => P.d.2.2 rl rfl e)⟩
    | pair p q =>
      simp only [copyNeed, bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      dsimp only
      refine ⟨[Pole.mov g.re rl], rfl, rfl, Nat.le_succ _, fun y hy => ?_, fun P => ?_⟩
      · rcases hy with e | hy
        · exact Or.inr ⟨by simp [e], by simp [e]⟩
        · exact Or.inl (Or.inr hy)
      · have lo : ∀ y, NMem (Need.pair p q) y → y < g.re := fun y hy => P.lo y (Or.inr hy)
        exact ⟨⟨P.d.2.1.1, P.d.2.1.2.1, P.d.2.1.2.2, fun h => Nat.lt_irrefl _ (lo _ (Or.inl h)),
          fun h => Nat.lt_irrefl _ (lo _ (Or.inr h))⟩, (fun e => by simp at e),
          (fun s => by rw [fits_both_pair]; simp [Comp.Fits]),
          copySem_mov (fun R s hs => holds_both_pair hs) (fun e => P.d.2.2 rl rfl e)⟩
  | pair pl ql ihp ihq =>
    intro r ops g g' x h
    cases r with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], rfl, copyOK_left _ g⟩
    | this rr =>
      simp only [copyNeed, bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      dsimp only
      refine ⟨[Pole.mov g.re rr], rfl, rfl, Nat.le_succ _, fun y hy => ?_, fun P => ?_⟩
      · rcases hy with e | hy
        · exact Or.inr ⟨by simp [e], by simp [e]⟩
        · exact Or.inl (Or.inl hy)
      · have lo : ∀ y, NMem (Need.pair pl ql) y → y < g.re := fun y hy => P.lo y (Or.inl hy)
        exact ⟨⟨P.d.1.1, P.d.1.2.1, P.d.1.2.2, fun h => Nat.lt_irrefl _ (lo _ (Or.inl h)),
          fun h => Nat.lt_irrefl _ (lo _ (Or.inr h))⟩, (fun e => by simp at e),
          (fun s => by rw [fits_both_pair]; simp [Comp.Fits]),
          copySem_swap (copySem_mov (fun R s hs => holds_both_pair hs) (fun e => P.d.2.2 rr e rfl))⟩
    | pair pr qr =>
      simp only [copyNeed] at h
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨Ah, eh, Oh⟩ := ihp _ _ _ _ _ h1
      obtain ⟨At, et, Ot⟩ := ihq _ _ _ _ _ h2
      simp only at eh et Oh Ot
      refine ⟨At ++ Ah, by rw [et, eh, List.append_assoc], gen_trans Oh.gen Ot.gen,
        Nat.le_trans Oh.le Ot.le, fun y hy => ?_, fun P => ?_⟩
      · rcases nmem_consNeed hy with hy | hy
        · rcases Oh.mem y hy with (h | h) | ⟨h1, h2⟩
          · exact Or.inl (Or.inl (Or.inl h))
          · exact Or.inl (Or.inr (Or.inl h))
          · exact Or.inr ⟨h1, Nat.lt_of_lt_of_le h2 Ot.le⟩
        · rcases Ot.mem y hy with (h | h) | ⟨h1, h2⟩
          · exact Or.inl (Or.inl (Or.inr h))
          · exact Or.inl (Or.inr (Or.inr h))
          · exact Or.inr ⟨Nat.le_trans Oh.le h1, h2⟩
      obtain ⟨⟨dpl, dql, dplql⟩, ⟨dpr, dqr, dprqr⟩, dlr⟩ := P.d
      have Ph : CopyPre pl pr g.re := ⟨P.cl.2.1, P.cr.2.1, ⟨dpl, dpr, fun y a b => dlr y (Or.inl a) (Or.inl b)⟩,
        fun y hy => P.lo y (hy.elim (fun h => Or.inl (Or.inl h)) (fun h => Or.inr (Or.inl h)))⟩
      have Pt : CopyPre ql qr g1.re := ⟨P.cl.2.2, P.cr.2.2, ⟨dql, dqr, fun y a b => dlr y (Or.inr a) (Or.inr b)⟩,
        fun y hy => Nat.lt_of_lt_of_le (P.lo y (hy.elim (fun h => Or.inl (Or.inr h))
          (fun h => Or.inr (Or.inr h)))) Oh.le⟩
      obtain ⟨Dh, Nh, Fh, Ch⟩ := Oh.sem Ph
      obtain ⟨Dt, Nt, Ft, Ct⟩ := Ot.sem Pt
      have dHT : ∀ y, NMem (Need.pair pl pr) y → ¬ NMem (Need.pair ql qr) y := by
        intro y h1 h2
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exact dplql y h1 h2
        · exact dlr y (Or.inl h1) (Or.inr h2)
        · exact dlr y (Or.inr h2) (Or.inl h1)
        · exact dprqr y h1 h2
      have e : consNeed a1 a2 = Need.pair a1 a2 := by
        apply consNeed_pair
        by_cases e1 : a1 = Need.none
        · by_cases e2 : a2 = Need.none
          · exact absurd ⟨(Nh e1).1, (Nt e2).1⟩ P.cl.1
          · exact Or.inr e2
        · exact Or.inl e1
      rw [e]
      have lH := Ph.lo
      have lT : ∀ y, NMem (Need.pair ql qr) y → y < g.re := fun y hy =>
        P.lo y (hy.elim (fun h => Or.inl (Or.inr h)) (fun h => Or.inr (Or.inr h)))
      refine ⟨⟨Dh, Dt, disj_join Oh.mem Ot.mem dHT lH lT Oh.le⟩, (fun e => by cases e),
        fits_rec (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) Fh Ft, ?_⟩
      intro lib σ O c gul st t R s hs
      cases s with
      | atom _ => exact hs.elim
      | cell u v =>
        obtain ⟨R2, r2, h1, h2, h3, h4, u2⟩ := copySem_halves Ch Ct
          (fun y hy hm => by
            rcases Oh.mem y hy with hh | ⟨hh, _⟩
            · exact dHT y hh hm
            · have := lT y hm; omega)
          (fun y a b => dHT y b a) lib σ O c gul st t R u v hs.1 hs.2
        refine ⟨R2, r2, ⟨h1, h3⟩, ⟨h2, h4⟩, fun y hy => u2 y ?_ ?_⟩
        · exact fun hm => hy (hm.elim (fun h => Or.inl (Or.inl h)) (fun h => Or.inr (Or.inl h)))
        · exact fun hm => hy (hm.elim (fun h => Or.inl (Or.inr h)) (fun h => Or.inr (Or.inr h)))
    | both xr hr tr =>
      simp only [copyNeed] at h
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨Ah, eh, Oh⟩ := ihp _ _ _ _ _ h1
      obtain ⟨At, et, Ot⟩ := ihq _ _ _ _ _ h2
      simp only at eh et Oh Ot
      refine ⟨At ++ Ah, by rw [et, eh, List.append_assoc], gen_trans Oh.gen Ot.gen,
        Nat.le_trans Oh.le Ot.le, fun y hy => ?_, fun P => ?_⟩
      · rcases hy with e | hy | hy
        · exact Or.inl (Or.inr (Or.inl e))
        · rcases Oh.mem y hy with (h | h) | ⟨h1, h2⟩
          · exact Or.inl (Or.inl (Or.inl h))
          · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
          · exact Or.inr ⟨h1, Nat.lt_of_lt_of_le h2 Ot.le⟩
        · rcases Ot.mem y hy with (h | h) | ⟨h1, h2⟩
          · exact Or.inl (Or.inl (Or.inr h))
          · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
          · exact Or.inr ⟨Nat.le_trans Oh.le h1, h2⟩
      obtain ⟨⟨dpl, dql, dplql⟩, ⟨dhr, dtr, dhrtr, nxh, nxt⟩, dlr⟩ := P.d
      have Ph : CopyPre pl hr g.re := ⟨P.cl.2.1, P.cr.1, ⟨dpl, dhr,
        fun y a b => dlr y (Or.inl a) (Or.inr (Or.inl b))⟩,
        fun y hy => P.lo y (hy.elim (fun h => Or.inl (Or.inl h)) (fun h => Or.inr (Or.inr (Or.inl h))))⟩
      have lT : ∀ y, NMem (Need.pair ql tr) y → y < g.re := fun y hy =>
        P.lo y (hy.elim (fun h => Or.inl (Or.inr h)) (fun h => Or.inr (Or.inr (Or.inr h))))
      have Pt : CopyPre ql tr g1.re := ⟨P.cl.2.2, P.cr.2, ⟨dql, dtr,
        fun y a b => dlr y (Or.inr a) (Or.inr (Or.inr b))⟩, fun y hy => Nat.lt_of_lt_of_le (lT y hy) Oh.le⟩
      obtain ⟨Dh, _, Fh, Ch⟩ := Oh.sem Ph
      obtain ⟨Dt, _, Ft, Ct⟩ := Ot.sem Pt
      have dHT : ∀ y, NMem (Need.pair pl hr) y → ¬ NMem (Need.pair ql tr) y := by
        intro y h1 h2
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exact dplql y h1 h2
        · exact dlr y (Or.inl h1) (Or.inr (Or.inr h2))
        · exact dlr y (Or.inr h2) (Or.inr (Or.inl h1))
        · exact dhrtr y h1 h2
      have xH : ¬ NMem (Need.pair pl hr) xr := fun hm =>
        hm.elim (fun h => dlr xr (Or.inl h) (Or.inl rfl)) (fun h => nxh h)
      have xT : ¬ NMem (Need.pair ql tr) xr := fun hm =>
        hm.elim (fun h => dlr xr (Or.inr h) (Or.inl rfl)) (fun h => nxt h)
      have xlo : xr < g.re := P.lo xr (Or.inr (Or.inl rfl))
      refine ⟨⟨Dh, Dt, disj_join Oh.mem Ot.mem dHT Ph.lo lT Oh.le, not_mem_join Oh.mem xH xlo,
        not_mem_join Ot.mem xT (Nat.lt_of_lt_of_le xlo Oh.le)⟩, (fun e => by cases e),
        fits_rec (Or.inr ⟨xr, rfl⟩) (Or.inl rfl) (Or.inr ⟨xr, rfl⟩) Fh Ft, ?_⟩
      intro lib σ O c gul st t R s hs
      cases s with
      | atom _ => exact hs.elim
      | cell u v =>
        obtain ⟨R2, r2, h1, h2, h3, h4, u2⟩ := copySem_halves Ch Ct
          (fun y hy hm => by
            rcases Oh.mem y hy with hh | ⟨hh, _⟩
            · exact dHT y hh hm
            · have := lT y hm; omega)
          (fun y a b => dHT y b a) lib σ O c gul st t R u v hs.2.1 hs.2.2
        refine ⟨R2, r2, ⟨h1, h3⟩, ⟨by rw [u2 xr xH xT]; exact hs.1, h2, h4⟩, fun y hy => u2 y ?_ ?_⟩
        · exact fun hm => hy (hm.elim (fun h => Or.inl (Or.inl h)) (fun h => Or.inr (Or.inr (Or.inl h))))
        · exact fun hm => hy (hm.elim (fun h => Or.inl (Or.inr h)) (fun h => Or.inr (Or.inr (Or.inr h))))
  | both rl hl tl ihh iht =>
    intro r ops g g' x h
    cases r with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], rfl, copyOK_left _ g⟩
    | this rr =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      dsimp only
      refine ⟨[Pole.mov rl rr], rfl, rfl, Nat.le_refl _, fun y hy => Or.inl (Or.inl hy), fun P => ?_⟩
      exact ⟨P.d.1, (fun e => by simp at e), (fun s => by simp [Comp.Fits]),
        copySem_swap (copySem_mov (fun R s hs => holds_both_top hs) (fun e => P.d.2.2 rr e rfl))⟩
    | pair pr qr =>
      simp only [copyNeed] at h
      obtain ⟨xr, g0', h0, h⟩ := bind_some h
      simp only [re_apply, Option.some.injEq, Prod.mk.injEq] at h0
      obtain ⟨rfl, rfl⟩ := h0
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨Ah, eh, Oh⟩ := ihh _ _ _ _ _ h1
      obtain ⟨At, et, Ot⟩ := iht _ _ _ _ _ h2
      simp only at eh et Oh Ot
      have le1 : g.re + 1 ≤ g1.re := Oh.le
      refine ⟨At ++ (Ah ++ [Pole.mov g.re rl]), by rw [et, eh]; simp, gen_trans (gen_trans rfl Oh.gen) Ot.gen,
        by have := Ot.le; omega, fun y hy => ?_, fun P => ?_⟩
      · rcases hy with e | hy | hy
        · exact Or.inr ⟨by omega, by have := Ot.le; omega⟩
        · rcases Oh.mem y hy with (h | h) | ⟨h1, h2⟩
          · exact Or.inl (Or.inl (Or.inr (Or.inl h)))
          · exact Or.inl (Or.inr (Or.inl h))
          · exact Or.inr ⟨by simp at h1; omega, Nat.lt_of_lt_of_le h2 Ot.le⟩
        · rcases Ot.mem y hy with (h | h) | ⟨h1, h2⟩
          · exact Or.inl (Or.inl (Or.inr (Or.inr h)))
          · exact Or.inl (Or.inr (Or.inr h))
          · exact Or.inr ⟨by omega, h2⟩
      obtain ⟨⟨dhl, dtl, dhltl, nrh, nrt⟩, ⟨dpr, dqr, dprqr⟩, dlr⟩ := P.d
      have lH : ∀ y, NMem (Need.pair hl pr) y → y < g.re := fun y hy =>
        P.lo y (hy.elim (fun h => Or.inl (Or.inr (Or.inl h))) (fun h => Or.inr (Or.inl h)))
      have lT : ∀ y, NMem (Need.pair tl qr) y → y < g.re := fun y hy =>
        P.lo y (hy.elim (fun h => Or.inl (Or.inr (Or.inr h))) (fun h => Or.inr (Or.inr h)))
      have Ph : CopyPre hl pr (g.re + 1) := ⟨P.cl.1, P.cr.2.1, ⟨dhl, dpr,
        fun y a b => dlr y (Or.inr (Or.inl a)) (Or.inl b)⟩, fun y hy => Nat.lt_succ_of_lt (lH y hy)⟩
      have Pt : CopyPre tl qr g1.re := ⟨P.cl.2, P.cr.2.2, ⟨dtl, dqr,
        fun y a b => dlr y (Or.inr (Or.inr a)) (Or.inr b)⟩, fun y hy => by have := lT y hy; omega⟩
      obtain ⟨Dh, _, Fh, Ch⟩ := Oh.sem Ph
      obtain ⟨Dt, _, Ft, Ct⟩ := Ot.sem Pt
      have dHT : ∀ y, NMem (Need.pair hl pr) y → ¬ NMem (Need.pair tl qr) y := by
        intro y h1 h2
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exact dhltl y h1 h2
        · exact dlr y (Or.inr (Or.inl h1)) (Or.inr h2)
        · exact dlr y (Or.inr (Or.inr h2)) (Or.inl h1)
        · exact dprqr y h1 h2
      have xH : ¬ NMem (Need.pair hl pr) g.re := fun hm => Nat.lt_irrefl _ (lH _ hm)
      have xT : ¬ NMem (Need.pair tl qr) g.re := fun hm => Nat.lt_irrefl _ (lT _ hm)
      have rH : ¬ NMem (Need.pair hl pr) rl := fun hm =>
        hm.elim (fun h => nrh h) (fun h => dlr rl (Or.inl rfl) (Or.inl h))
      have rT : ¬ NMem (Need.pair tl qr) rl := fun hm =>
        hm.elim (fun h => nrt h) (fun h => dlr rl (Or.inl rfl) (Or.inr h))
      have rlo : rl < g.re := P.lo rl (Or.inl (Or.inl rfl))
      refine ⟨⟨Dh, Dt, disj_join Oh.mem Ot.mem dHT (fun y hy => Nat.lt_succ_of_lt (lH y hy))
          (fun y hy => Nat.lt_succ_of_lt (lT y hy)) le1,
        not_mem_join Oh.mem xH (Nat.lt_succ_self _), not_mem_join Ot.mem xT (by omega)⟩, (fun e => by cases e),
        fits_rec (Or.inr ⟨g.re, rfl⟩) (Or.inr ⟨rl, rfl⟩) (Or.inl rfl) Fh Ft, ?_⟩
      intro lib σ O c gul st t R s hs
      cases s with
      | atom _ => exact hs.elim
      | cell u v =>
        obtain ⟨R2, r2, h1, h2, h3, h4, u2⟩ := copySem_halves Ch Ct
          (fun y hy hm => by
            rcases Oh.mem y hy with hh | ⟨hh, _⟩
            · exact dHT y hh hm
            · have := lT y hm; simp at hh; omega)
          (fun y a b => dHT y b a) lib σ O c gul st t R u v hs.2.1 hs.2.2
        have hx2 : SkaModel.read g.re R2 = some (C u v) := by rw [u2 _ xH xT]; exact hs.1
        have ne : ∀ y, y ≠ rl → SkaModel.read y (store rl (C u v) R2) = SkaModel.read y R2 :=
          fun y hy => read_store_ne hy _ _
        refine ⟨store rl (C u v) R2, by rw [← List.append_assoc]; exact r2.append (runs_mov hx2),
          ⟨read_store_eq _ _ _, HoldsN.agree hl (fun y hy => ne y (fun e => by subst e; exact rH (Or.inl hy))) h1,
            HoldsN.agree tl (fun y hy => ne y (fun e => by subst e; exact rT (Or.inl hy))) h3⟩,
          ⟨HoldsN.agree pr (fun y hy => ne y (fun e => by subst e; exact rH (Or.inr hy))) h2,
            HoldsN.agree qr (fun y hy => ne y (fun e => by subst e; exact rT (Or.inr hy))) h4⟩,
          fun y hy => ?_⟩
        rw [ne y (fun e => hy (Or.inl (Or.inl e)))]
        refine u2 y ?_ ?_
        · exact fun hm => hy (hm.elim (fun h => Or.inl (Or.inr (Or.inl h))) (fun h => Or.inr (Or.inl h)))
        · exact fun hm => hy (hm.elim (fun h => Or.inl (Or.inr (Or.inr h))) (fun h => Or.inr (Or.inr h)))
    | both xr hr tr =>
      simp only [copyNeed] at h
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨Ah, eh, Oh⟩ := ihh _ _ _ _ _ h1
      obtain ⟨At, et, Ot⟩ := iht _ _ _ _ _ h2
      simp only at eh et Oh Ot
      refine ⟨At ++ (Ah ++ [Pole.mov xr rl]), by rw [et, eh]; simp, gen_trans Oh.gen Ot.gen,
        Nat.le_trans Oh.le Ot.le, fun y hy => ?_, fun P => ?_⟩
      · rcases hy with e | hy | hy
        · exact Or.inl (Or.inr (Or.inl e))
        · rcases Oh.mem y hy with (h | h) | ⟨h1, h2⟩
          · exact Or.inl (Or.inl (Or.inr (Or.inl h)))
          · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
          · exact Or.inr ⟨h1, Nat.lt_of_lt_of_le h2 Ot.le⟩
        · rcases Ot.mem y hy with (h | h) | ⟨h1, h2⟩
          · exact Or.inl (Or.inl (Or.inr (Or.inr h)))
          · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
          · exact Or.inr ⟨Nat.le_trans Oh.le h1, h2⟩
      obtain ⟨⟨dhl, dtl, dhltl, nrh, nrt⟩, ⟨dhr, dtr, dhrtr, nxh, nxt⟩, dlr⟩ := P.d
      have lH : ∀ y, NMem (Need.pair hl hr) y → y < g.re := fun y hy =>
        P.lo y (hy.elim (fun h => Or.inl (Or.inr (Or.inl h))) (fun h => Or.inr (Or.inr (Or.inl h))))
      have lT : ∀ y, NMem (Need.pair tl tr) y → y < g.re := fun y hy =>
        P.lo y (hy.elim (fun h => Or.inl (Or.inr (Or.inr h))) (fun h => Or.inr (Or.inr (Or.inr h))))
      have Ph : CopyPre hl hr g.re := ⟨P.cl.1, P.cr.1, ⟨dhl, dhr,
        fun y a b => dlr y (Or.inr (Or.inl a)) (Or.inr (Or.inl b))⟩, lH⟩
      have Pt : CopyPre tl tr g1.re := ⟨P.cl.2, P.cr.2, ⟨dtl, dtr,
        fun y a b => dlr y (Or.inr (Or.inr a)) (Or.inr (Or.inr b))⟩,
        fun y hy => Nat.lt_of_lt_of_le (lT y hy) Oh.le⟩
      obtain ⟨Dh, _, Fh, Ch⟩ := Oh.sem Ph
      obtain ⟨Dt, _, Ft, Ct⟩ := Ot.sem Pt
      have dHT : ∀ y, NMem (Need.pair hl hr) y → ¬ NMem (Need.pair tl tr) y := by
        intro y h1 h2
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exact dhltl y h1 h2
        · exact dlr y (Or.inr (Or.inl h1)) (Or.inr (Or.inr h2))
        · exact dlr y (Or.inr (Or.inr h2)) (Or.inr (Or.inl h1))
        · exact dhrtr y h1 h2
      have xH : ¬ NMem (Need.pair hl hr) xr := fun hm =>
        hm.elim (fun h => dlr xr (Or.inr (Or.inl h)) (Or.inl rfl)) (fun h => nxh h)
      have xT : ¬ NMem (Need.pair tl tr) xr := fun hm =>
        hm.elim (fun h => dlr xr (Or.inr (Or.inr h)) (Or.inl rfl)) (fun h => nxt h)
      have rH : ¬ NMem (Need.pair hl hr) rl := fun hm =>
        hm.elim (fun h => nrh h) (fun h => dlr rl (Or.inl rfl) (Or.inr (Or.inl h)))
      have rT : ¬ NMem (Need.pair tl tr) rl := fun hm =>
        hm.elim (fun h => nrt h) (fun h => dlr rl (Or.inl rfl) (Or.inr (Or.inr h)))
      have rx : xr ≠ rl := fun e => dlr rl (Or.inl rfl) (Or.inl e.symm)
      have xlo : xr < g.re := P.lo xr (Or.inr (Or.inl rfl))
      refine ⟨⟨Dh, Dt, disj_join Oh.mem Ot.mem dHT lH lT Oh.le, not_mem_join Oh.mem xH xlo,
        not_mem_join Ot.mem xT (Nat.lt_of_lt_of_le xlo Oh.le)⟩, (fun e => by cases e),
        fits_rec (Or.inr ⟨xr, rfl⟩) (Or.inr ⟨rl, rfl⟩) (Or.inr ⟨xr, rfl⟩) Fh Ft, ?_⟩
      intro lib σ O c gul st t R s hs
      cases s with
      | atom _ => exact hs.elim
      | cell u v =>
        obtain ⟨R2, r2, h1, h2, h3, h4, u2⟩ := copySem_halves Ch Ct
          (fun y hy hm => by
            rcases Oh.mem y hy with hh | ⟨hh, _⟩
            · exact dHT y hh hm
            · have := lT y hm; omega)
          (fun y a b => dHT y b a) lib σ O c gul st t R u v hs.2.1 hs.2.2
        have hx2 : SkaModel.read xr R2 = some (C u v) := by rw [u2 _ xH xT]; exact hs.1
        have ne : ∀ y, y ≠ rl → SkaModel.read y (store rl (C u v) R2) = SkaModel.read y R2 :=
          fun y hy => read_store_ne hy _ _
        refine ⟨store rl (C u v) R2, by rw [← List.append_assoc]; exact r2.append (runs_mov hx2),
          ⟨read_store_eq _ _ _, HoldsN.agree hl (fun y hy => ne y (fun e => by subst e; exact rH (Or.inl hy))) h1,
            HoldsN.agree tl (fun y hy => ne y (fun e => by subst e; exact rT (Or.inl hy))) h3⟩,
          ⟨by rw [ne xr rx]; exact hx2,
            HoldsN.agree hr (fun y hy => ne y (fun e => by subst e; exact rH (Or.inr hy))) h2,
            HoldsN.agree tr (fun y hy => ne y (fun e => by subst e; exact rT (Or.inr hy))) h4⟩,
          fun y hy => ?_⟩
        rw [ne y (fun e => hy (Or.inl (Or.inl e)))]
        refine u2 y ?_ ?_
        · exact fun hm => hy (hm.elim (fun h => Or.inl (Or.inr (Or.inl h))) (fun h => Or.inr (Or.inr (Or.inl h))))
        · exact fun hm => hy (hm.elim (fun h => Or.inl (Or.inr (Or.inr h))) (fun h => Or.inr (Or.inr (Or.inr h))))

/-- Ops put in front of a block allocated after `g`. -/
theorem ext_addOps_after {o : Nat} {ops : List Pole} {g g1 g2 : Gen Map} {u : Unit}
    (h : addOps o ops g1 = some (u, g2)) (e : Ext g g1) (ho : g.bo ≤ o) : Ext g g2 := by
  by_cases hd : g1.drop = false
  · have F := front_addOps h hd
    exact ⟨Nat.le_trans e.1 F.le, by rw [F.bo]; exact e.2.1, F.drop.trans e.2.2.1,
      fun o' ho' => (F.other o' (by omega)).trans (e.2.2.2 o' ho')⟩
  · simp only [Bool.not_eq_false] at hd
    unfold addOps at h
    simp only [hd, if_true, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact e

theorem looks_uni (a b : S) (s : Noun) : Looks (HoonSet.uni a b) s ↔ Looks a s ∧ Looks b s := by
  constructor
  · intro h
    exact ⟨fun x hx => h x ((HoonSet.mem_uni a b x).mpr (Or.inl hx)),
      fun x hx => h x ((HoonSet.mem_uni a b x).mpr (Or.inr hx))⟩
  · intro ⟨h1, h2⟩ x hx
    rcases (HoonSet.mem_uni a b x).mp hx with hx | hx
    · exact h1 x hx
    · exact h2 x hx

/-- **`+copy`**: the block it emits fills the needs of both halves from the
need it returns, and goes on to the code of the first. -/
theorem copy_ok {first : Next S} {second : Sure S} {g g' : Gen Map} {nex : Next S}
    (h : copy first second g = some (nex, g')) :
    Ext g g' ∧ nex.th = jmp0 g.bo ∧ g'.bo = g.bo + 1 ∧
    (∀ y, NMem nex.laz.ned y → NMem first.laz.ned y ∨ NMem second.ned y ∨ (g.re ≤ y ∧ y < g'.re)) ∧
    (CopyPre first.laz.ned second.ned g.re →
      Distinct nex.laz.ned ∧ (∀ s, FitsS nex.laz s ↔ FitsS first.laz s ∧ FitsS second s) ∧
      (g.drop = false → ∀ (c : Straight Map), Agree c g g' → ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (st : σ)
        (R : Map Noun) t gul s, HoldsS nex.laz R s → ∃ R', HoldsS first.laz R' s ∧ HoldsS second R' s ∧
          (∀ y, ¬ NMem first.laz.ned y → ¬ NMem second.ned y → SkaModel.read y R' = SkaModel.read y R) ∧
          goJ lib O c gul st R t nex.th = goJ lib O c gul st R' t first.th)) := by
  simp only [copy] at h
  obtain ⟨o, g0, h0, h⟩ := bind_some h
  rw [emit_apply] at h0
  simp only [Option.some.injEq, Prod.mk.injEq] at h0
  obtain ⟨rfl, rfl⟩ := h0
  obtain ⟨laz, g1, h1', h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [copyLazy] at h1'
  obtain ⟨⟨n1, o1⟩, g2, h2, h1'⟩ := bind_some h1'
  obtain ⟨_, g3, h3, h1'⟩ := bind_some h1'
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1'
  obtain ⟨rfl, rfl⟩ := h1'
  obtain ⟨Aops, eA, O⟩ := copyNeed_spec _ _ _ _ _ _ h2
  simp only [List.append_nil] at eA
  subst eA
  simp only at O
  have E0 := ext_emit g ⟨[], [], Termin.hop first.th⟩
  have e02 : Ext (g.emitted ⟨[], [], Termin.hop first.th⟩) g2 := by
    rw [O.gen]; exact ext_reg_le O.le
  have E := ext_addOps_after h3 (E0.trans e02) (Nat.le_refl _)
  have bo3 : g3.bo = g.bo + 1 := by
    by_cases hd : g2.drop = false
    · rw [(front_addOps h3 hd).bo, O.gen]; rfl
    · simp only [Bool.not_eq_false] at hd
      unfold addOps at h3
      simp only [hd, if_true, Option.some.injEq, Prod.mk.injEq] at h3
      rw [← h3.2, O.gen]; rfl
  have re3 : g2.re ≤ g3.re := by
    by_cases hd : g2.drop = false
    · exact (front_addOps h3 hd).le
    · simp only [Bool.not_eq_false] at hd
      unfold addOps at h3
      simp only [hd, if_true, Option.some.injEq, Prod.mk.injEq] at h3
      rw [← h3.2]; exact Nat.le_refl _
  refine ⟨E, rfl, bo3, fun y hy => ?_, fun P => ?_⟩
  · rcases O.mem y hy with (h | h) | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h1, Nat.lt_of_lt_of_le h2 re3⟩)
  obtain ⟨D, _, F, C⟩ := O.sem P
  refine ⟨D, fun s => ?_, fun hd c hc lib σ O' st R t gul s hs => ?_⟩
  · simp only [FitsS, F s, looks_uni]
    exact ⟨fun ⟨⟨a, b⟩, c, d⟩ => ⟨⟨a, c⟩, b, d⟩, fun ⟨⟨a, c⟩, b, d⟩ => ⟨⟨a, b⟩, c, d⟩⟩
  have hd2 : g2.drop = false := by rw [O.gen]; exact hd
  have F3 := front_addOps h3 hd2
  have hb2 : HoonMap.get g2.blocks g.bo = some ⟨[], [], Termin.hop first.th⟩ := by
    rw [O.gen]; exact emitted_get g _ hd
  have hb : HoonMap.get c.blocks g.bo = some ⟨[], o1 ++ [], Termin.hop first.th⟩ := by
    rw [hc g.bo (Nat.le_refl _) (by rw [bo3]; omega)]; exact F3.blk _ _ hb2
  obtain ⟨R', r1, hl, hr, u⟩ := C lib σ O' c gul st t R s hs.1
  have lk := (looks_uni _ _ s).mp hs.2
  refine ⟨R', ⟨hl, lk.1⟩, ⟨hr, lk.2⟩, fun y n1 n2 => u y (fun hm => hm.elim n1 n2), ?_⟩
  rw [goJ_jmp0 _ _ _ _ hb, r1, execBlob_hop]

end Comp
end SkaModel
end Formalization
