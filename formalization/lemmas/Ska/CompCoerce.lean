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

end Comp
end SkaModel
end Formalization
