import lemmas.Ska.CompTopOK

/-!
# What the ops of `+coerce-lazy` do

`kernLoop_spec`: the ops of `+kern-need` from a register that holds a noun
fill the registers of the target need with its parts, checking each cell
the need takes apart, or crash where the noun has not the need's shape;
they change no register below the state's register counter but those of the
target.  `sureLoop_spec`: the same for the loop `sure-loop` of
`+coerce-lazy`, from registers that hold the noun as the input need asks.
`coerceSpec`: so `CoerceSpec` holds, which removes that hypothesis of
`finish_bellContract`.

The ops of a later part are put in front of those of an earlier one, so the
tail's ops run before the head's.  What makes the order harmless is that
every op writes either a register of the target, or a register allocated
after the part that runs before it read what it needs.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

theorem app_eq_self {A acc : List Pole} : A ++ acc = acc ↔ A = [] := by
  constructor
  · intro h
    have := congrArg List.length h
    simp only [List.length_append] at this
    exact List.eq_nil_of_length_eq_zero (by omega)
  · rintro rfl; rfl

/-! ## `+kern-need` -/

/-- What the ops `A` of `+kern-need` from register `r` into `tgt` do: from
registers where `r` holds `v`, they fill `tgt` with `v` and change no
register below `lo` outside `tgt`, or crash if `v` has not the shape of
`tgt`. -/
def KernSem (Map : Type → Type) [HoonMap Map] (tgt : Need) (r lo : Nat) (A : List Pole) : Prop :=
  ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
    (R : Map Noun) (v : Noun), SkaModel.read r R = some v →
    (Comp.Fits tgt v → ∃ R', Runs lib O c gul st t A R R' ∧ HoldsN tgt R' v ∧
        ∀ x, x < lo → ¬ NMem tgt x → SkaModel.read x R' = SkaModel.read x R) ∧
    (¬ Comp.Fits tgt v → Crashes lib O c gul st t A R)

/-- What a run of the loop of `+kern-need` makes. -/
structure KernOK (tgt : Need) (r : Nat) (g g' : Gen Map) (A : List Pole) : Prop where
  gen : ∃ n, g' = { g with re := n }
  le : g.re ≤ g'.re
  nil : A = [] → tgt = Need.none
  sem : Distinct tgt → (∀ x, NMem tgt x → x < g.re) → KernSem Map tgt r g.re A

section Part
variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}

/-- One half of a `%both` of `+kern-need`: the op `sel` that reads the half
into `rr`, then the ops for the half, or nothing if there are none. -/
theorem part_spec {x : Need} {rr : Nat} {gg gg' : Gen Map} {Ax : List Pole} (K : KernOK x rr gg gg' Ax)
    (hx : Distinct x) (hlt : ∀ y, NMem x y → y < gg.re) (sel : Pole) {R : Map Noun} {w : Noun}
    (hsel : Runs lib O c gul st t [sel] R (store rr w R)) :
    (Comp.Fits x w → ∃ R', Runs lib O c gul st t (if Ax = [] then [] else sel :: Ax) R R' ∧ HoldsN x R' w ∧
        ∀ y, y < gg.re → y ≠ rr → ¬ NMem x y → SkaModel.read y R' = SkaModel.read y R) ∧
    (¬ Comp.Fits x w → Crashes lib O c gul st t (if Ax = [] then [] else sel :: Ax) R) := by
  by_cases e : Ax = []
  · have := K.nil e
    subst this
    simp only [e, if_true]
    exact ⟨fun _ => ⟨R, Runs.nil R, trivial, fun _ _ _ _ => rfl⟩, fun h => absurd trivial h⟩
  · simp only [e, if_false]
    have hS := K.sem hx hlt lib σ O c gul st t (store rr w R) w (read_store_eq _ _ _)
    rw [show sel :: Ax = [sel] ++ Ax from rfl]
    refine ⟨fun hf => ?_, fun hf => Crashes.append_right hsel (hS.2 hf)⟩
    obtain ⟨R', hr, hh, ha⟩ := hS.1 hf
    exact ⟨R', hsel.append hr, hh, fun y hy hne hn => by rw [ha y hy hn, read_store_ne hne]⟩

end Part

/-- **The case `%both` of `+kern-need`**, for the target `[%both d h t]`
given what the loop does for `h` and `t`. -/
theorem kernBoth_spec {r d : Nat} {kh kt : Nat → List Pole → CM Map (List Pole)} {h t : Need}
    (sh : ∀ r' acc (g g' : Gen Map) ops, kh r' acc g = some (ops, g') → ∃ A, ops = A ++ acc ∧ KernOK h r' g g' A)
    (st : ∀ r' acc (g g' : Gen Map) ops, kt r' acc g = some (ops, g') → ∃ A, ops = A ++ acc ∧ KernOK t r' g g' A)
    {acc : List Pole} {g g' : Gen Map} {ops : List Pole} (hk : kernBoth r d kh kt acc g = some (ops, g')) :
    ∃ A, ops = A ++ acc ∧ (∃ n, g' = { g with re := n }) ∧ g.re ≤ g'.re ∧ A ≠ [] ∧
      (Distinct h → Distinct t → (∀ x, NMem h x → ¬ NMem t x) → ¬ NMem h d → ¬ NMem t d → d < g.re →
        (∀ x, NMem h x → x < g.re) → (∀ x, NMem t x → x < g.re) →
        ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (stt : σ) (tr : Trace)
          (R : Map Noun) (v : Noun), SkaModel.read r R = some v →
          (∀ a b, v = C a b → Comp.Fits h a → Comp.Fits t b → ∃ R', Runs lib O c gul stt tr A R R' ∧
            SkaModel.read d R' = some v ∧ HoldsN h R' a ∧ HoldsN t R' b ∧
            ∀ x, x < g.re → x ≠ d → ¬ NMem h x → ¬ NMem t x → SkaModel.read x R' = SkaModel.read x R) ∧
          ((∀ a b, v = C a b → ¬ (Comp.Fits h a ∧ Comp.Fits t b)) → Crashes lib O c gul stt tr A R)) := by
  unfold kernBoth at hk
  obtain ⟨rt, g1, h1, hk⟩ := bind_some hk
  rw [re_apply] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  obtain ⟨o1, g2, h2, hk⟩ := bind_some hk
  obtain ⟨At, rfl, Kt⟩ := st _ _ _ _ _ h2
  obtain ⟨rh, g3, h3, hk⟩ := bind_some hk
  rw [re_apply] at h3
  simp only [Option.some.injEq, Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  obtain ⟨o2, g4, h4, hk⟩ := bind_some hk
  have eT : (if At ++ acc ≠ acc then Pole.tal d g.re :: (At ++ acc) else At ++ acc) =
      (if At = [] then [] else Pole.tal d g.re :: At) ++ acc := by
    by_cases e : At = [] <;> simp [e, app_eq_self]
  rw [eT] at h4 hk
  obtain ⟨Ah, rfl, Kh⟩ := sh _ _ _ _ _ h4
  have eH : (if Ah ++ ((if At = [] then [] else Pole.tal d g.re :: At) ++ acc) ≠
        (if At = [] then [] else Pole.tal d g.re :: At) ++ acc
      then Pole.hed d g2.re :: (Ah ++ ((if At = [] then [] else Pole.tal d g.re :: At) ++ acc))
      else Ah ++ ((if At = [] then [] else Pole.tal d g.re :: At) ++ acc)) =
      ((if Ah = [] then [] else Pole.hed d g2.re :: Ah) ++ (if At = [] then [] else Pole.tal d g.re :: At)) ++ acc := by
    by_cases e : Ah = [] <;> simp [e, app_eq_self]
  rw [eH] at hk
  by_cases erd : r = d
  · simp only [erd, if_true] at hk; cases hk
  simp only [erd, if_false, pure_apply, Option.some.injEq, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  obtain ⟨n2, rfl⟩ := Kt.gen
  obtain ⟨n4, rfl⟩ := Kh.gen
  have l2 : g.re + 1 ≤ n2 := Kt.le
  have l4 : n2 + 1 ≤ n4 := Kh.le
  refine ⟨Pole.mov r d :: Pole.cel d :: ((if Ah = [] then [] else Pole.hed d n2 :: Ah) ++
    (if At = [] then [] else Pole.tal d g.re :: At)), by simp, ⟨n4, rfl⟩, (show g.re ≤ n4 by omega),
    by simp, ?_⟩
  intro dh dt dht ndh ndt hd lth ltt lib σ O c gul stt tr R v hr
  have rmov := runs_mov (lib := lib) (O := O) (c := c) (gul := gul) (st := stt) (t := tr) (d := d) hr
  have eA : Pole.mov r d :: Pole.cel d :: ((if Ah = [] then [] else Pole.hed d n2 :: Ah) ++
      (if At = [] then [] else Pole.tal d g.re :: At)) =
      [Pole.mov r d] ++ ([Pole.cel d] ++ ((if Ah = [] then [] else Pole.hed d n2 :: Ah) ++
      (if At = [] then [] else Pole.tal d g.re :: At))) := rfl
  rw [eA]
  -- the noun is an atom: `%cel` crashes
  have atomCase : ∀ n, v = A n → Crashes lib O c gul stt tr ([Pole.mov r d] ++ ([Pole.cel d] ++
      ((if Ah = [] then [] else Pole.hed d n2 :: Ah) ++ (if At = [] then [] else Pole.tal d g.re :: At)))) R := by
    intro n hv
    subst hv
    exact Crashes.append_right rmov (Crashes.append_left (crashes_cel (read_store_eq _ _ _)))
  -- the noun is a cell: the two halves
  have cellCase : ∀ a b, v = C a b →
      (Comp.Fits h a → Comp.Fits t b → ∃ R', Runs lib O c gul stt tr ([Pole.mov r d] ++ ([Pole.cel d] ++
        ((if Ah = [] then [] else Pole.hed d n2 :: Ah) ++ (if At = [] then [] else Pole.tal d g.re :: At)))) R R' ∧
        SkaModel.read d R' = some v ∧ HoldsN h R' a ∧ HoldsN t R' b ∧
        ∀ x, x < g.re → x ≠ d → ¬ NMem h x → ¬ NMem t x → SkaModel.read x R' = SkaModel.read x R) ∧
      (¬ (Comp.Fits h a ∧ Comp.Fits t b) → Crashes lib O c gul stt tr ([Pole.mov r d] ++ ([Pole.cel d] ++
        ((if Ah = [] then [] else Pole.hed d n2 :: Ah) ++ (if At = [] then [] else Pole.tal d g.re :: At)))) R) := by
    intro a b hv
    subst hv
    have r1 : SkaModel.read d (store d (C a b) R) = some (C a b) := read_store_eq _ _ _
    have rcel := runs_cel (lib := lib) (O := O) (c := c) (gul := gul) (st := stt) (t := tr) r1
    have P1 := part_spec Kh dh (fun y hy => by have := lth y hy; show y < n2 + 1; omega) (Pole.hed d n2)
      (runs_hed (lib := lib) (O := O) (c := c) (gul := gul) (st := stt) (t := tr) (d := n2) r1)
    refine ⟨fun fh ft => ?_, fun hn => ?_⟩
    · obtain ⟨R2, rh2, hh2, ah2⟩ := P1.1 fh
      have r2 : SkaModel.read d R2 = some (C a b) := by
        rw [ah2 d (show d < n2 + 1 by omega) (show d ≠ n2 by omega) ndh, r1]
      have P2 := part_spec Kt dt (fun y hy => by have := ltt y hy; show y < g.re + 1; omega) (Pole.tal d g.re)
        (runs_tal (lib := lib) (O := O) (c := c) (gul := gul) (st := stt) (t := tr) (d := g.re) r2)
      obtain ⟨R3, rh3, hh3, ah3⟩ := P2.1 ft
      refine ⟨R3, rmov.append (rcel.append (rh2.append rh3)), ?_, ?_, hh3, ?_⟩
      · rw [ah3 d (show d < g.re + 1 by omega) (by omega) ndt, r2]
      · exact HoldsN.agree h (fun y hy => ah3 y (by have := lth y hy; show y < g.re + 1; omega)
          (by have := lth y hy; omega) (fun hy' => dht y hy hy')) hh2
      · intro y hy hyd hyh hyt
        rw [ah3 y (show y < g.re + 1 by omega) (by omega) hyt, ah2 y (show y < n2 + 1 by omega) (show y ≠ n2 by omega) hyh,
          read_store_ne hyd]
    · by_cases fh : Comp.Fits h a
      · have ft : ¬ Comp.Fits t b := fun ft => hn ⟨fh, ft⟩
        obtain ⟨R2, rh2, _, ah2⟩ := P1.1 fh
        have r2 : SkaModel.read d R2 = some (C a b) := by
          rw [ah2 d (show d < n2 + 1 by omega) (show d ≠ n2 by omega) ndh, r1]
        have P2 := part_spec Kt dt (fun y hy => by have := ltt y hy; show y < g.re + 1; omega) (Pole.tal d g.re)
          (runs_tal (lib := lib) (O := O) (c := c) (gul := gul) (st := stt) (t := tr) (d := g.re) r2)
        exact Crashes.append_right rmov (Crashes.append_right rcel (Crashes.append_right rh2 (P2.2 ft)))
      · exact Crashes.append_right rmov (Crashes.append_right rcel (Crashes.append_left (P1.2 fh)))
  refine ⟨fun a b hv fh ft => (cellCase a b hv).1 fh ft, fun hn => ?_⟩
  cases v with
  | atom n => exact atomCase n rfl
  | cell a b => exact (cellCase a b rfl).2 (hn a b rfl)


/-- **The loop of `+kern-need`.** -/
theorem kernLoop_spec : ∀ (tgt : Need) (r : Nat) (acc : List Pole) (g g' : Gen Map) (ops : List Pole),
    kernLoop r tgt acc g = some (ops, g') → ∃ A, ops = A ++ acc ∧ KernOK tgt r g g' A := by
  intro tgt
  induction tgt with
  | none =>
    intro r acc g g' ops h
    simp only [kernLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, ⟨⟨g.re, rfl⟩, Nat.le_refl _, fun _ => rfl, fun _ _ lib σ O c gul st t R v _ =>
      ⟨fun _ => ⟨R, Runs.nil R, trivial, fun _ _ _ => rfl⟩, fun h => absurd trivial h⟩⟩⟩
  | this d =>
    intro r acc g g' ops h
    simp only [kernLoop] at h
    by_cases e : r = d
    · rw [if_pos e] at h; cases h
    rw [if_neg e] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨[Pole.mov r d], rfl, ⟨⟨g.re, rfl⟩, Nat.le_refl _, (fun h => by cases h), fun _ _ lib σ O c gul st t R v hr =>
      ⟨fun _ => ⟨store d v R, runs_mov hr, read_store_eq _ _ _, fun x _ hx => read_store_ne hx _ _⟩,
        fun h => absurd trivial h⟩⟩⟩
  | pair p q ihp ihq =>
    intro r acc g g' ops h
    simp only [kernLoop] at h
    obtain ⟨rn, g1, h1, h⟩ := bind_some h
    rw [re_apply] at h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨A, hA, ⟨n, rfl⟩, hle, hne, hsem⟩ := kernBoth_spec (fun r' acc g g' ops h => ihp r' acc g g' ops h)
      (fun r' acc g g' ops h => ihq r' acc g g' ops h) h
    refine ⟨A, hA, ⟨⟨n, rfl⟩, Nat.le_trans (Nat.le_succ _) hle, fun e => absurd e hne, fun hd hlt => ?_⟩⟩
    obtain ⟨dp, dq, dpq⟩ := hd
    have ltp : ∀ x, NMem p x → x < g.re := fun x hx => hlt x (Or.inl hx)
    have ltq : ∀ x, NMem q x → x < g.re := fun x hx => hlt x (Or.inr hx)
    intro lib σ O c gul st t R v hr
    have H := hsem dp dq dpq (fun hx => by have := ltp _ hx; omega) (fun hx => by have := ltq _ hx; omega)
      (show g.re < g.re + 1 by omega) (fun x hx => by have := ltp x hx; show x < g.re + 1; omega)
      (fun x hx => by have := ltq x hx; show x < g.re + 1; omega) lib σ O c gul st t R v hr
    refine ⟨fun hf => ?_, fun hf => H.2 fun a b hv hab => hf (by subst hv; exact hab)⟩
    cases v with
    | atom _ => exact hf.elim
    | cell a b =>
      obtain ⟨R', hR, _, hp, hq, ha⟩ := H.1 a b rfl hf.1 hf.2
      exact ⟨R', hR, ⟨hp, hq⟩, fun x hx hn => ha x (by show x < g.re + 1; omega) (by omega)
        (fun h => hn (Or.inl h)) (fun h => hn (Or.inr h))⟩
  | both d h t ihh iht =>
    intro r acc g g' ops hk
    simp only [kernLoop] at hk
    obtain ⟨A, hA, gen, hle, hne, hsem⟩ := kernBoth_spec (fun r' acc g g' ops h => ihh r' acc g g' ops h)
      (fun r' acc g g' ops h => iht r' acc g g' ops h) hk
    refine ⟨A, hA, ⟨gen, hle, fun e => absurd e hne, fun hd hlt => ?_⟩⟩
    obtain ⟨dh, dt, dht, ndh, ndt⟩ := hd
    intro lib σ O c gul st tr R v hr
    have H := hsem dh dt dht ndh ndt (hlt d (Or.inl rfl)) (fun x hx => hlt x (Or.inr (Or.inl hx)))
      (fun x hx => hlt x (Or.inr (Or.inr hx))) lib σ O c gul st tr R v hr
    refine ⟨fun hf => ?_, fun hf => H.2 fun a b hv hab => hf (by subst hv; exact hab)⟩
    cases v with
    | atom _ => exact hf.elim
    | cell a b =>
      obtain ⟨R', hR, hd', hh, ht, ha⟩ := H.1 a b rfl hf.1 hf.2
      exact ⟨R', hR, ⟨hd', hh, ht⟩, fun x hx hn => ha x hx (fun e => hn (Or.inl e))
        (fun e => hn (Or.inr (Or.inl e))) (fun e => hn (Or.inr (Or.inr e)))⟩

/-! ## `sure-loop` -/

/-- What the ops `A` of `sure-loop` from `ned` into `tgt` do. -/
def SureSem (Map : Type → Type) [HoonMap Map] (ned tgt : Need) (lo : Nat) (A : List Pole) : Prop :=
  ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
    (R : Map Noun) (s : Noun), HoldsN ned R s →
    (Comp.Fits tgt s → ∃ R', Runs lib O c gul st t A R R' ∧ HoldsN tgt R' s ∧
        ∀ x, x < lo → ¬ NMem tgt x → SkaModel.read x R' = SkaModel.read x R) ∧
    (¬ Comp.Fits tgt s → Crashes lib O c gul st t A R)

theorem front_reg {o : Nat} (g : Gen Map) {n : Nat} (h : g.re ≤ n) : Front o g { g with re := n } [] :=
  ⟨fun B fin hb => by simpa using hb, fun _ _ => rfl, rfl, rfl, h⟩

theorem Front.refl {o : Nat} (g : Gen Map) : Front o g g [] := front_reg (o := o) g (Nat.le_refl g.re)

/-- Two halves, the tail's ops in front of the head's. -/
theorem sureSem_halves {p q tp tq : Need} {lo1 lo2 : Nat} {Ap Aq : List Pole} (hlo : lo1 ≤ lo2)
    (sp : SureSem Map p tp lo1 Ap) (sq : SureSem Map q tq lo2 Aq)
    (dtq : ∀ x, NMem tp x → ¬ NMem tq x) (ltq : ∀ x, NMem tq x → x < lo1)
    (lp : ∀ x, NMem p x → x < lo1) (np : ∀ x, NMem p x → ¬ NMem tq x)
    (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
    (R : Map Noun) (a b : Noun) (ha : HoldsN p R a) (hb : HoldsN q R b) :
    (Comp.Fits tp a → Comp.Fits tq b → ∃ R', Runs lib O c gul st t (Aq ++ Ap) R R' ∧ HoldsN tp R' a ∧
        HoldsN tq R' b ∧ ∀ x, x < lo1 → ¬ NMem tp x → ¬ NMem tq x → SkaModel.read x R' = SkaModel.read x R) ∧
    (¬ (Comp.Fits tp a ∧ Comp.Fits tq b) → Crashes lib O c gul st t (Aq ++ Ap) R) := by
  have Q := sq lib σ O c gul st t R b hb
  refine ⟨fun fa fb => ?_, fun hn => ?_⟩
  · obtain ⟨R1, r1, hq1, a1⟩ := Q.1 fb
    have ha1 : HoldsN p R1 a := HoldsN.agree p (fun x hx => a1 x (Nat.lt_of_lt_of_le (lp x hx) hlo) (np x hx)) ha
    obtain ⟨R2, r2, hp2, a2⟩ := (sp lib σ O c gul st t R1 a ha1).1 fa
    refine ⟨R2, r1.append r2, hp2, HoldsN.agree tq (fun x hx => a2 x (ltq x hx) (fun h => dtq x h hx)) hq1, ?_⟩
    intro x hx n1 n2
    rw [a2 x hx n1, a1 x (Nat.lt_of_lt_of_le hx hlo) n2]
  · by_cases fb : Comp.Fits tq b
    · have fa : ¬ Comp.Fits tp a := fun fa => hn ⟨fa, fb⟩
      obtain ⟨R1, r1, _, a1⟩ := Q.1 fb
      have ha1 : HoldsN p R1 a :=
        HoldsN.agree p (fun x hx => a1 x (Nat.lt_of_lt_of_le (lp x hx) hlo) (np x hx)) ha
      exact Crashes.append_right r1 ((sp lib σ O c gul st t R1 a ha1).2 fa)
    · exact Crashes.append_left (Q.2 fb)


theorem sureSem_none (Map : Type → Type) [HoonMap Map] (ned : Need) (lo : Nat) :
    SureSem Map ned Need.none lo [] := fun _ _ _ _ _ _ _ R _ _ =>
  ⟨fun _ => ⟨R, Runs.nil R, trivial, fun _ _ _ => rfl⟩, fun h => absurd trivial h⟩

/-- **The loop `sure-loop` of `+coerce-lazy`.** -/
theorem sureLoop_spec {o : Nat} : ∀ (ned tgt : Need) (g g' : Gen Map) (u : Unit),
    sureLoop o ned tgt g = some (u, g') → g.drop = false →
    ∃ A, Front o g g' A ∧ (Distinct tgt → (∀ x, NMem tgt x → x < g.re) → (∀ x, NMem ned x → x < g.re) →
      (∀ x, NMem ned x → ¬ NMem tgt x) → SureSem Map ned tgt g.re A) := by
  intro ned
  induction ned with
  | none =>
    intro tgt g g' u h hd
    simp only [sureLoop] at h
    by_cases e : tgt = Need.none
    · rw [if_pos e] at h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      subst e
      exact ⟨[], Front.refl g, fun _ _ _ _ => sureSem_none Map _ _⟩
    · rw [if_neg e] at h; cases h
  | this r =>
    intro tgt g g' u h hd
    simp only [sureLoop] at h
    obtain ⟨ops, g1, h1, h2⟩ := bind_some h
    obtain ⟨A, rfl, K⟩ := kernLoop_spec tgt r [] g g1 ops h1
    obtain ⟨n, rfl⟩ := K.gen
    have F := (front_reg (o := o) g K.le).trans (front_addOps h2 hd)
    simp only [List.append_nil] at F
    exact ⟨A, F, fun dt lt _ _ lib σ O c gul st tt R s hs => K.sem dt lt lib σ O c gul st tt R s hs⟩
  | pair p q ihp ihq =>
    intro tgt g g' u h hd
    cases tgt with
    | none =>
      simp only [sureLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      exact ⟨[], Front.refl g, fun _ _ _ _ => sureSem_none Map _ _⟩
    | this _ => simp only [sureLoop] at h; cases h
    | both _ _ _ => simp only [sureLoop] at h; cases h
    | pair tp tq =>
      simp only [sureLoop] at h
      obtain ⟨_, g1, h1, h2⟩ := bind_some h
      obtain ⟨Ap, Fp, sp⟩ := ihp tp g g1 _ h1 hd
      obtain ⟨Aq, Fq, sq⟩ := ihq tq g1 g' _ h2 (Fp.drop.trans hd)
      refine ⟨Aq ++ Ap, Fp.trans Fq, fun dt lt ln nd => ?_⟩
      obtain ⟨dtp, dtq, dpq⟩ := dt
      have SP := sp dtp (fun x hx => lt x (Or.inl hx)) (fun x hx => ln x (Or.inl hx))
        (fun x hx h => nd x (Or.inl hx) (Or.inl h))
      have SQ := sq dtq (fun x hx => Nat.lt_of_lt_of_le (lt x (Or.inr hx)) Fp.le)
        (fun x hx => Nat.lt_of_lt_of_le (ln x (Or.inr hx)) Fp.le) (fun x hx h => nd x (Or.inr hx) (Or.inr h))
      intro lib σ O c gul st t R s hs
      cases s with
      | atom _ => exact hs.elim
      | cell a b =>
        have H := sureSem_halves Fp.le SP SQ dpq (fun x hx => lt x (Or.inr hx)) (fun x hx => ln x (Or.inl hx))
          (fun x hx h => nd x (Or.inl hx) (Or.inr h)) lib σ O c gul st t R a b hs.1 hs.2
        refine ⟨fun hf => ?_, fun hf => H.2 hf⟩
        obtain ⟨R', hr, h1, h2, ha⟩ := H.1 hf.1 hf.2
        exact ⟨R', hr, ⟨h1, h2⟩, fun x hx hn => ha x hx (fun h => hn (Or.inl h)) (fun h => hn (Or.inr h))⟩
  | both r h t ihh iht =>
    intro tgt g g' u hk hd
    cases tgt with
    | none =>
      simp only [sureLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨_, rfl⟩ := hk
      exact ⟨[], Front.refl g, fun _ _ _ _ => sureSem_none Map _ _⟩
    | this d =>
      simp only [sureLoop] at hk
      by_cases e : r = d
      · rw [if_pos e] at hk; cases hk
      rw [if_neg e] at hk
      refine ⟨[Pole.mov r d], front_addOps hk hd, fun _ _ _ _ lib σ O c gul st tt R s hs => ?_⟩
      cases s with
      | atom _ => exact hs.elim
      | cell a b =>
        exact ⟨fun _ => ⟨store d (C a b) R, runs_mov hs.1, read_store_eq _ _ _, fun x _ hx => read_store_ne hx _ _⟩,
          fun h => absurd trivial h⟩
    | pair tp tq =>
      simp only [sureLoop] at hk
      obtain ⟨_, g1, h1, h2⟩ := bind_some hk
      obtain ⟨Ap, Fp, sp⟩ := ihh tp g g1 _ h1 hd
      obtain ⟨Aq, Fq, sq⟩ := iht tq g1 g' _ h2 (Fp.drop.trans hd)
      refine ⟨Aq ++ Ap, Fp.trans Fq, fun dt lt ln nd => ?_⟩
      obtain ⟨dtp, dtq, dpq⟩ := dt
      have SP := sp dtp (fun x hx => lt x (Or.inl hx)) (fun x hx => ln x (Or.inr (Or.inl hx)))
        (fun x hx h => nd x (Or.inr (Or.inl hx)) (Or.inl h))
      have SQ := sq dtq (fun x hx => Nat.lt_of_lt_of_le (lt x (Or.inr hx)) Fp.le)
        (fun x hx => Nat.lt_of_lt_of_le (ln x (Or.inr (Or.inr hx))) Fp.le)
        (fun x hx h => nd x (Or.inr (Or.inr hx)) (Or.inr h))
      intro lib σ O c gul st tt R s hs
      cases s with
      | atom _ => exact hs.elim
      | cell a b =>
        have H := sureSem_halves Fp.le SP SQ dpq (fun x hx => lt x (Or.inr hx))
          (fun x hx => ln x (Or.inr (Or.inl hx))) (fun x hx h => nd x (Or.inr (Or.inl hx)) (Or.inr h))
          lib σ O c gul st tt R a b hs.2.1 hs.2.2
        refine ⟨fun hf => ?_, fun hf => H.2 hf⟩
        obtain ⟨R', hr, h1, h2, ha⟩ := H.1 hf.1 hf.2
        exact ⟨R', hr, ⟨h1, h2⟩, fun x hx hn => ha x hx (fun h => hn (Or.inl h)) (fun h => hn (Or.inr h))⟩
    | both d th tt =>
      simp only [sureLoop] at hk
      by_cases e : r = d
      · rw [if_pos e] at hk; cases hk
      rw [if_neg e] at hk
      obtain ⟨_, g1, h1, hk⟩ := bind_some hk
      have F0 := front_addOps h1 hd
      obtain ⟨b0, _, rfl⟩ := addOps_spec h1 hd
      obtain ⟨_, g2, h2, h3⟩ := bind_some hk
      obtain ⟨Ah, Fh, sh⟩ := ihh th _ g2 _ h2 (F0.drop.trans hd)
      obtain ⟨At, Ft, st⟩ := iht tt g2 g' _ h3 (Fh.drop.trans (F0.drop.trans hd))
      refine ⟨At ++ (Ah ++ [Pole.mov r d]), (F0.trans Fh).trans Ft, fun dt lt ln nd => ?_⟩
      obtain ⟨dth, dtt, dhtt, ndh, ndt⟩ := dt
      have SH := sh dth (fun x hx => lt x (Or.inr (Or.inl hx))) (fun x hx => ln x (Or.inr (Or.inl hx)))
        (fun x hx h => nd x (Or.inr (Or.inl hx)) (Or.inr (Or.inl h)))
      have ST := st dtt (fun x hx => Nat.lt_of_lt_of_le (lt x (Or.inr (Or.inr hx))) Fh.le)
        (fun x hx => Nat.lt_of_lt_of_le (ln x (Or.inr (Or.inr hx))) Fh.le)
        (fun x hx h => nd x (Or.inr (Or.inr hx)) (Or.inr (Or.inr h)))
      intro lib σ O c gul stt tr R s hs
      cases s with
      | atom _ => exact hs.elim
      | cell a b =>
        have H := sureSem_halves Fh.le SH ST dhtt (fun x hx => lt x (Or.inr (Or.inr hx)))
          (fun x hx => ln x (Or.inr (Or.inl hx))) (fun x hx h => nd x (Or.inr (Or.inl hx)) (Or.inr (Or.inr h)))
          lib σ O c gul stt tr R a b hs.2.1 hs.2.2
        rw [← List.append_assoc]
        refine ⟨fun hf => ?_, fun hf => Crashes.append_left (H.2 hf)⟩
        obtain ⟨R2, hr2, hh2, ht2, ha2⟩ := H.1 hf.1 hf.2
        have nr := nd r (Or.inl rfl)
        have rr : SkaModel.read r R2 = some (C a b) := by
          rw [ha2 r (ln r (Or.inl rfl)) (fun h => nr (Or.inr (Or.inl h))) (fun h => nr (Or.inr (Or.inr h)))]
          exact hs.1
        refine ⟨store d (C a b) R2, hr2.append (runs_mov rr), ⟨read_store_eq _ _ _, ?_, ?_⟩, ?_⟩
        · exact HoldsN.agree th (fun x hx => read_store_ne (fun e => ndh (by rw [← e]; exact hx)) _ _) hh2
        · exact HoldsN.agree tt (fun x hx => read_store_ne (fun e => ndt (by rw [← e]; exact hx)) _ _) ht2
        · intro x hx hn
          rw [read_store_ne (fun e => hn (Or.inl e)), ha2 x hx (fun h => hn (Or.inr (Or.inl h)))
            (fun h => hn (Or.inr (Or.inr h)))]


/-! ## The looks of `+coerce-lazy` -/

/-- One step of the fold of `coerceLok`. -/
def coerceStep (less : Cape) (ned : Need) (acc : Option S) (axe : Nat) : Option S :=
  acc.bind fun s =>
    (axeInLessCape axe less).bind fun inLess =>
      if inLess then some s else
      if axe = 0 then Option.none else
      if axeInNeedL axe ned then some s else some (HoonSet.put s axe)

theorem coerceLok_eq (lok : S) (less : Cape) (ned : Need) :
    coerceLok lok less ned = (HoonSet.toList lok).foldl (coerceStep less ned) (some HoonSet.empty) := rfl

theorem coerceFold_none (less : Cape) (ned : Need) : ∀ (xs : List Nat),
    xs.foldl (coerceStep (S := S) less ned) Option.none = Option.none
  | [] => rfl
  | _ :: xs => by simp only [List.foldl_cons, coerceStep, Option.bind_none]; exact coerceFold_none less ned xs

theorem coerceFold_spec (less : Cape) (ned : Need) : ∀ (xs : List Nat) (s0 l : S),
    xs.foldl (coerceStep less ned) (some s0) = some l →
    (∀ y ∈ HoonSet.toList l, y ∈ HoonSet.toList s0 ∨ y ∈ xs) ∧
    (∀ y ∈ xs, y ≠ 0 ∧ (axeInCape y less = true ∨ axeInNeedL y ned = true ∨ y ∈ HoonSet.toList l)) ∧
    (∀ y ∈ HoonSet.toList s0, y ∈ HoonSet.toList l)
  | [], s0, l, h => by
    simp only [List.foldl_nil, Option.some.injEq] at h
    subst h
    exact ⟨fun y hy => Or.inl hy, (fun y hy => by cases hy), fun y hy => hy⟩
  | x :: xs, s0, l, h => by
    rw [List.foldl_cons] at h
    have hx0 : x ≠ 0 := by
      intro e; subst e
      simp [coerceStep, axeInLessCape, coerceFold_none] at h
    have step : ∃ s1, coerceStep less ned (some s0) x = some s1 ∧
        (∀ y ∈ HoonSet.toList s1, y = x ∨ y ∈ HoonSet.toList s0) ∧
        (∀ y ∈ HoonSet.toList s0, y ∈ HoonSet.toList s1) ∧
        (axeInCape x less = true ∨ axeInNeedL x ned = true ∨ x ∈ HoonSet.toList s1) := by
      simp only [coerceStep, axeInLessCape, hx0, if_false, Option.bind_some]
      by_cases hc : axeInCape x less = true
      · exact ⟨s0, by simp [hc], fun y hy => Or.inr hy, fun y hy => hy, Or.inl hc⟩
      · by_cases hn : axeInNeedL x ned = true
        · exact ⟨s0, by simp [hc, hn], fun y hy => Or.inr hy, fun y hy => hy, Or.inr (Or.inl hn)⟩
        · refine ⟨HoonSet.put s0 x, by simp [hc, hn, hx0], fun y hy => (HoonSet.mem_put s0 x y).mp hy,
            fun y hy => (HoonSet.mem_put s0 x y).mpr (Or.inr hy), Or.inr (Or.inr ((HoonSet.mem_put s0 x x).mpr
              (Or.inl rfl)))⟩
    obtain ⟨s1, e1, m1, k1, c1⟩ := step
    rw [e1] at h
    obtain ⟨I1, I2, I3⟩ := coerceFold_spec less ned xs s1 l h
    refine ⟨fun y hy => ?_, fun y hy => ?_, fun y hy => I3 y (k1 y hy)⟩
    · rcases I1 y hy with h1 | h1
      · rcases m1 y h1 with h2 | h2
        · exact Or.inr (List.mem_cons.mpr (Or.inl h2))
        · exact Or.inl h2
      · exact Or.inr (List.mem_cons_of_mem _ h1)
    · rcases List.mem_cons.mp hy with e | e
      · subst e
        exact ⟨hx0, c1.elim Or.inl (fun c => c.elim (fun c => Or.inr (Or.inl c)) (fun c => Or.inr (Or.inr (I3 _ c))))⟩
      · exact I2 y e

theorem axeInNeedL_pair {axe : Nat} (h2 : 2 ≤ axe) (p q : Need) :
    axeInNeedL axe (Need.pair p q) = if cap axe = 2 then axeInNeedL (mas axe) p else axeInNeedL (mas axe) q := by
  rw [axeInNeedL]; simp [show ¬ axe ≤ 1 by omega]

theorem axeInNeedL_both {axe : Nat} (h2 : 2 ≤ axe) (r : Nat) (p q : Need) :
    axeInNeedL axe (Need.both r p q) = if cap axe = 2 then axeInNeedL (mas axe) p else axeInNeedL (mas axe) q := by
  rw [axeInNeedL]; simp [show ¬ axe ≤ 1 by omega]

theorem axeInNeedL_none {axe : Nat} (h2 : 2 ≤ axe) : axeInNeedL axe Need.none = false := by
  rw [axeInNeedL]; simp [show ¬ axe ≤ 1 by omega]
  all_goals intros; contradiction

theorem axeInNeedL_this {axe : Nat} (h2 : 2 ≤ axe) (r : Nat) : axeInNeedL axe (Need.this r) = false := by
  rw [axeInNeedL]; simp [show ¬ axe ≤ 1 by omega]
  all_goals intros; contradiction

/-- An axis inside a need is in every noun of the need's shape. -/
theorem slot_of_axeInNeed : ∀ (axe : Nat), 1 ≤ axe → ∀ (ned : Need) (s : Noun), Comp.Fits ned s →
    axeInNeedL axe ned = true → (slot? axe s).isSome := by
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
    intro h1 ned s hf ha
    by_cases e : axe = 1
    · subst e; simp [slot?_one]
    have h2 : 2 ≤ axe := by omega
    cases ned with
    | none => rw [axeInNeedL_none h2] at ha; cases ha
    | this _ => rw [axeInNeedL_this h2] at ha; cases ha
    | pair p q =>
      rw [axeInNeedL_pair h2] at ha
      cases s with
      | atom _ => exact hf.elim
      | cell a b =>
        rw [slot?_cap h2]
        rcases cap_cases _ h2 with hc | hc
        · simp only [hc, if_true] at ha ⊢
          exact ih _ (mas_lt axe h2) (mas_pos axe h2) p a hf.1 ha
        · simp only [hc, show (3 : Nat) ≠ 2 by decide, if_false] at ha ⊢
          exact ih _ (mas_lt axe h2) (mas_pos axe h2) q b hf.2 ha
    | both _ p q =>
      rw [axeInNeedL_both h2] at ha
      cases s with
      | atom _ => exact hf.elim
      | cell a b =>
        rw [slot?_cap h2]
        rcases cap_cases _ h2 with hc | hc
        · simp only [hc, if_true] at ha ⊢
          exact ih _ (mas_lt axe h2) (mas_pos axe h2) p a hf.1 ha
        · simp only [hc, show (3 : Nat) ≠ 2 by decide, if_false] at ha ⊢
          exact ih _ (mas_lt axe h2) (mas_pos axe h2) q b hf.2 ha

/-! ## `+coerce-lazy` -/

/-- **`CoerceSpec` holds.** -/
theorem coerceSpec : CoerceSpec S Map := by
  intro ned o laz less g g' h hd dn dl ll ln nd
  simp only [coerceLazy] at h
  obtain ⟨lok, g1, h1, h⟩ := bind_some h
  obtain ⟨l, hl, e⟩ := Option.map_eq_some_iff.mp h1
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  rw [coerceLok_eq] at hl
  obtain ⟨C1, C2, _⟩ := coerceFold_spec less ned _ _ _ hl
  obtain ⟨tgt, g2, h2, h3⟩ := bind_some h
  have L := sureRequireLook_spec h2
  obtain ⟨k, rfl⟩ := L.gen
  obtain ⟨A, F, sem⟩ := sureLoop_spec ned tgt _ g' () h3 hd
  have F' := (front_reg (o := o) g L.le).trans F
  simp only [List.append_nil] at F'
  refine ⟨A, F', ?_⟩
  have dt : Distinct tgt := L.dist dl ll
  have lt : ∀ x, NMem tgt x → x < k := fun x hx =>
    (L.mem x hx).elim (fun h => Nat.lt_of_lt_of_le (ll x h) L.le) (fun h => h.2)
  have SS := sem dt lt (fun x hx => Nat.lt_of_lt_of_le (ln x hx) L.le)
    (fun x hx ht => (L.mem x ht).elim (fun h => nd x hx h) (fun h => by have := ln x hx; simp at h; omega))
  intro lib σ O c gul st t R s hs hca
  have S1 := SS lib σ O c gul st t R s hs
  have sub : ∀ y ∈ HoonSet.toList l, y ∈ HoonSet.toList laz.lok := fun y hy =>
    (C1 y hy).elim (fun h => absurd h (HoonSet.mem_empty y)) id
  refine ⟨fun hf => ?_, fun hf => S1.2 fun ft => hf ?_⟩
  · have ft : Comp.Fits tgt s := (L.fits s).mpr ⟨hf.1, fun x hx => hf.2 x (sub x hx)⟩
    obtain ⟨R', hr, hh, _⟩ := S1.1 ft
    exact ⟨R', hr, L.holds R' s hh, hf.2⟩
  · have F2 := (L.fits s).mp ft
    refine ⟨F2.1, fun y hy => ?_⟩
    obtain ⟨hy0, hy⟩ := C2 y hy
    rcases hy with hc | hn | hm
    · exact hca y (by omega) hc
    · exact slot_of_axeInNeed y (by omega) ned s (fits_of_holds ned hs) hn
    · exact F2.2 y hm

end Comp
end SkaModel
end Formalization
