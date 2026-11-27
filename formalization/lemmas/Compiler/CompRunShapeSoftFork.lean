import lemmas.Compiler.CompRunShapeTwo
import lemmas.Compiler.CompRunShapeSix
import lemmas.Compiler.CompRunShapeSoftForkCut

/-!
# `+run-shape`: `+laze-soft-fork` (track A, 2026-11-28)

`+laze-soft-fork` (door arm `0x55fffe`, cut in `CompRunShapeSoftForkCut.lean`) is one of the
kerf tests of the case `%6` under `[%next laz]` (`rs6Kerf`, model `sixShape`):
`(laze-soft-fork lep q r)` on the core at axis `127` of its subject, `[comp.door [gen ctx]]`.

* `lienO`, **`lienO_loop`**, **`lienO_gate`**: `+lien` with a test that can crash (`orB`: the
  first yes wins, the rest is not run).
* `softForkSB_lienO`, `softForkSF_lienO`: the model's bond and fork loops are `lienO`.
* **`lsf_all`**: the gate is `softForkS (sofsHas st.sofs) (unsS env q r)` wherever the model
  returns, on every `laze` (forks and bonds to any depth), under `CompIn ctx`, `K` at axis `7`
  and the code table at axis `52` with `CodeNomms env.cod cod` (for `+sound`, `sf_gate`).
  No `LzNZ` is needed: the arm walks no axis.
* `lsf_arm`: the arm builds its gate; `lsf_at'` (the cut) is the arm at its core axis on any
  `[comp.door y]`, as `rs6Kerf` pulls it.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun}

/-! ## `+lien` with a test that can crash -/

/-- `+lien` with a test that can crash: the first yes wins, and the rest is not run. -/
def lienO {α : Type} (p : α → Option Bool) : List α → Option Bool
  | [] => some false
  | x :: xs => orB (p x) (lienO p xs)

/-- **The loop of `+lien`** on the nouns of a list, with a gate that gives the loobean of `p x`
wherever `p x` returns. -/
theorem lienO_loop (c bp bs bc : Noun) {α : Type} (enc : α → Noun) (p : α → Option Bool) :
    ∀ (l : List α), (∀ x ∈ l, ∀ t, p x = some t → nock (C bp (C (enc x) bc)) bp = some (loob t)) →
    ∀ t, lienO p l = some t →
    nock (C lien.loop (C lien.battery (C (C (listN (l.map enc)) (C bp (C bs bc))) c))) lien.loop
      = some (loob t)
  | [], _, t, h => by
    simp only [lienO, Option.some.injEq] at h
    subst h
    nock_open lien.loop
    simp [nock_exec, loob]
  | x :: xs, hf, t, h => by
    simp only [lienO] at h
    rcases hx : p x with _ | tx
    · rw [hx] at h; simp [orB] at h
    · have hx' := hf x (by simp) tx hx
      cases tx with
      | true =>
        rw [hx] at h
        simp only [orB, Option.some.injEq] at h
        subst h
        nock_open lien.loop
        simp [nock_exec, hx', loob]
      | false =>
        rw [hx] at h
        simp only [orB] at h
        have hxs := lienO_loop c bp bs bc enc p xs (fun y hy => hf y (by simp [hy])) t h
        nock_open lien.loop
        simp [nock_exec, hx', hxs, loob]

/-- **Slamming the `+lien` gate** with a test that can crash. -/
theorem lienO_gate (c bp bs bc : Noun) {α : Type} (enc : α → Noun) (p : α → Option Bool) (l : List α)
    (hf : ∀ x ∈ l, ∀ t, p x = some t → nock (C bp (C (enc x) bc)) bp = some (loob t))
    (t : Bool) (h : lienO p l = some t) :
    nock (C lien.battery (C (C (listN (l.map enc)) (C bp (C bs bc))) c)) lien.battery = some (loob t) := by
  nock_open lien.battery
  simp only [nock_exec, lienO_loop c bp bs bc enc p l hf t h]

/-! ## The model's loops as `lienO` -/

/-- The model's test of a bond. -/
def sfBondT (soft : Nat → Bool) (uns : NeedOrd → Option Bool) (e : Nat × Laze CSet) : Option Bool :=
  orB (if soft e.1 then uns e.2.sure.ned else some false) (softForkS soft uns e.2)

/-- The model's test of a fork. -/
def sfForkT (soft : Nat → Bool) (uns : NeedOrd → Option Bool) (e : (Nat × Laze CSet) × (Nat × Laze CSet)) :
    Option Bool :=
  orB (softForkS soft uns e.1.2) (softForkS soft uns e.2.2)

theorem softForkSB_lienO (soft : Nat → Bool) (uns : NeedOrd → Option Bool) :
    ∀ b : List (Nat × Laze CSet), softForkSB soft uns b = lienO (sfBondT soft uns) b
  | [] => rfl
  | (o, l) :: rest => by
    simp only [softForkSB, lienO, sfBondT, softForkSB_lienO soft uns rest]

theorem softForkSF_lienO (soft : Nat → Bool) (uns : NeedOrd → Option Bool) :
    ∀ f : List ((Nat × Laze CSet) × (Nat × Laze CSet)), softForkSF soft uns f = lienO (sfForkT soft uns) f
  | [] => rfl
  | ((oy, a), (on, b)) :: rest => by
    simp only [softForkSF, lienO, sfForkT, softForkSF_lienO soft uns rest]

/-! ## The gate -/

theorem lsf_arm (d : Noun) : nock d lsfArm = some (C lsfGate (C lsfBunt d)) := by
  unfold lsfArm; simp only [nock_exec]

section
variable (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
  (env : ShapeEnv) (hcn : CodeNomms env.cod cod) (q r : Nomm) (st : RSt CSet) (y : RsRest)
include hc h7 hcode hcn

/-- **The `!&((sound q ned) (sound r ned))` of a bond** (`lsfSnd`), wherever `unsS` returns. -/
theorem lsf_snd (e : Nat × Laze CSet) (LZ : Noun) (u : Bool)
    (hu : unsS env q r e.2.sure.ned = some u) :
    nock (C lsfGB (C (lzbE e) (C lsfGate (C (C LZ (C q.toNoun r.toNoun)) (rsDoor st y ctx))))) lsfSnd
      = some (loob u) := by
  obtain ⟨o, l⟩ := e
  obtain ⟨s, fk, bd⟩ := l
  have hl := lz_toNoun_mk s fk bd
  simp only [Laze.sure] at hu ⊢
  have hsq := rsd_snd h7 hcode (rsGenNoun st y) q.toNoun s.ned.toNoun
  have hsr := rsd_snd h7 hcode (rsGenNoun st y) r.toNoun s.ned.toNoun
  unfold unsS andO at hu
  rcases e1 : soundS env q s.ned with _ | bq
  · rw [e1] at hu; simp at hu
  have hq := sf_gate env.cod cod hcn 3 q s.ned bq e1
  cases bq with
  | false =>
    rw [e1] at hu
    simp only [Option.bind_some, Bool.false_eq_true, if_false, Option.map_some, Bool.not_false,
      Option.some.injEq] at hu
    subst hu
    unfold lsfSnd
    simp [nock_exec, lzbE, hl, rsDoor, rsd_snd_at', snd_arm, hsq, hq, SureO.toNoun, loob]
  | true =>
    rw [e1] at hu
    rcases e2 : soundS env r s.ned with _ | br
    · rw [e2] at hu; simp at hu
    have hr := sf_gate env.cod cod hcn 3 r s.ned br e2
    rw [e2] at hu
    simp only [Option.bind_some, if_true, Option.map_some, Option.some.injEq] at hu
    subst hu
    unfold lsfSnd
    cases br <;>
      simp [nock_exec, lzbE, hl, rsDoor, rsd_snd_at', snd_arm, hsq, hq, hsr, hr, SureO.toNoun, loob]

mutual
/-- **`+laze-soft-fork` is `softForkS`** with the blocks of `sofs` and `unsS env q r`, wherever
the model returns, on every `laze`. -/
theorem lsf_all : ∀ (laz : Laze CSet) (t : Bool), softForkS (sofsHas st.sofs) (unsS env q r) laz = some t →
    nock (C lsfGate (C (C laz.toNoun (C q.toNoun r.toNoun)) (rsDoor st y ctx))) lsfGate = some (loob t)
  | Laze.mk s fk bd, t, h => by
    simp only [softForkS] at h
    rw [softForkSB_lienO, softForkSF_lienO] at h
    have hB := fun tb => lienO_gate layer2 lsfGB (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))))
      (C lsfGate (C (C (Laze.mk s fk bd).toNoun (C q.toNoun r.toNoun)) (rsDoor st y ctx)))
      lzbE (sfBondT (sofsHas st.sofs) (unsS env q r)) bd
      (fun e he t' ht' => lsf_bonds bd e he _ t' ht') tb
    have hF := fun tf => lienO_gate layer2 lsfGF
      (C (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))))
        (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))))
      (C lsfGate (C (C (Laze.mk s fk bd).toNoun (C q.toNoun r.toNoun)) (rsDoor st y ctx)))
      lzfE (sfForkT (sofsHas st.sofs) (unsS env q r)) fk
      (fun e he t' ht' => lsf_forks fk e he _ t' ht') tf
    rw [lz_toNoun_mk] at hB hF ⊢
    simp only [rsDoor] at hB hF
    have hc' : slot? 262143 ctx = some layer2 := hc
    rcases eb : lienO (sfBondT (sofsHas st.sofs) (unsS env q r)) bd with _ | tb
    · rw [eb] at h; simp [orB] at h
    have hB' := hB tb eb
    cases tb with
    | true =>
      rw [eb] at h
      simp only [orB, Option.some.injEq] at h
      subst h
      conv => { lhs; arg 2; unfold lsfGate }
      simp [nock_exec, rsDoor, hc', lien.arm_at, lien_arm, hB', loob]
    | false =>
      rw [eb] at h
      simp only [orB] at h
      have hF' := hF t h
      conv => { lhs; arg 2; unfold lsfGate }
      cases t <;> simp [nock_exec, rsDoor, hc', lien.arm_at, lien_arm, hB', hF', loob]

/-- The gate of the `+lien` over the bonds. -/
theorem lsf_bonds : ∀ (bd : List (Nat × Laze CSet)), ∀ e ∈ bd, ∀ (LZ : Noun) (t : Bool),
    sfBondT (sofsHas st.sofs) (unsS env q r) e = some t →
    nock (C lsfGB (C (lzbE e) (C lsfGate (C (C LZ (C q.toNoun r.toNoun)) (rsDoor st y ctx))))) lsfGB
      = some (loob t)
  | [], e, he => absurd he List.not_mem_nil
  | (ob, l) :: rest, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro LZ t h
      have hs := cs_has_gate st.sofs ob
      have hc' : slot? 262143 ctx = some layer2 := hc
      unfold sfBondT at h
      simp only at h
      by_cases hso : sofsHas st.sofs ob = true
      · rw [if_pos hso] at h
        rcases eu : unsS env q r l.sure.ned with _ | u
        · rw [eu] at h; simp [orB] at h
        have hsn := lsf_snd hc h7 hcode env hcn q r st y (ob, l) LZ u eu
        cases u with
        | true =>
          rw [eu] at h
          simp only [orB, Option.some.injEq] at h
          subst h
          simp only [rsDoor, rsGenNoun, lzbE] at hsn
          conv => { lhs; arg 2; unfold lsfGB }
          simp [nock_exec, lzbE, lsfHas, hsn, hso, rsDoor, rsGenNoun, hc', in_arm, in.arm_at, in.has.arm_at,
            has_in_arm, hs, loob]
        | false =>
          rw [eu] at h
          simp only [orB] at h
          have ihl := lsf_all l t h
          simp only [rsDoor, rsGenNoun, lzbE] at ihl hsn
          conv => { lhs; arg 2; unfold lsfGB }
          cases t <;> simp [nock_exec, lzbE, lsfHas, hsn, hso, ihl, rsDoor, rsGenNoun, hc', in_arm, in.arm_at,
            in.has.arm_at, has_in_arm, hs, loob]
      · simp only [Bool.not_eq_true] at hso
        rw [hso] at h
        simp only [Bool.false_eq_true, if_false, orB] at h
        have ihl := lsf_all l t h
        simp only [rsDoor, rsGenNoun] at ihl
        conv => { lhs; arg 2; unfold lsfGB }
        cases t <;> simp [nock_exec, lzbE, hso, ihl, rsDoor, rsGenNoun, hc', in_arm, in.arm_at,
          in.has.arm_at, has_in_arm, hs, loob, lsfHas]
    · exact lsf_bonds rest e he'

/-- The gate of the `+lien` over the forks. -/
theorem lsf_forks : ∀ (fk : List ((Nat × Laze CSet) × (Nat × Laze CSet))), ∀ e ∈ fk, ∀ (LZ : Noun) (t : Bool),
    sfForkT (sofsHas st.sofs) (unsS env q r) e = some t →
    nock (C lsfGF (C (lzfE e) (C lsfGate (C (C LZ (C q.toNoun r.toNoun)) (rsDoor st y ctx))))) lsfGF
      = some (loob t)
  | [], e, he => absurd he List.not_mem_nil
  | ((oy, a), (on, b)) :: rest, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro LZ t h
      unfold sfForkT at h
      simp only at h
      rcases ea : softForkS (sofsHas st.sofs) (unsS env q r) a with _ | ta
      · rw [ea] at h; simp [orB] at h
      have iha := lsf_all a ta ea
      simp only [rsDoor] at iha
      cases ta with
      | true =>
        rw [ea] at h
        simp only [orB, Option.some.injEq] at h
        subst h
        conv => { lhs; arg 2; unfold lsfGF }
        simp [nock_exec, lzfE, rsDoor, iha, loob]
      | false =>
        rw [ea] at h
        simp only [orB] at h
        have ihb := lsf_all b t h
        simp only [rsDoor] at ihb
        conv => { lhs; arg 2; unfold lsfGF }
        cases t <;> simp [nock_exec, lzfE, rsDoor, iha, ihb, loob]
    · exact lsf_forks rest e he'
end

end

end Compiler
end Formalization
