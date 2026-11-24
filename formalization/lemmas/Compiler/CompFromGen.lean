import lemmas.Compiler.CompSplitGen
import lemmas.Compiler.CompFrom

/-!
# `+from` on every lazy need

`+from` (door arm `3582`, battery `comp.from.battery`) on `[axe laz]`:

    ?:  &(?=(~ fork.laz) ?=(~ bond.laz))  [(from-sure axe sure.laz) ~ ~]
    :+  (from-sure axe sure.laz)
      (turn fork.laz |=([y n] [y(laz from-buc(laz laz.y)) n(laz from-buc(laz laz.n))]))
    (turn bond.laz |=([o laz] [o from-buc(laz laz)]))

`from-buc` is the gate itself with `laz` replaced (`[9 2 10 [13 ..] 0 7]`).
The model `fromL` of `Ska/CompLazyArms.lean` (with `fromForks`,
`fromBonds`) takes the same branches; it has no state, and a crash anywhere
is `none` in both.  No departure.

`cfr_all`: the arm on every lazy need (forks and bonds to any depth) whose
sure needs look at no axis `0`, on every state noun `G` (it reads none).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

def frGF : Noun :=
  (C (C (A 10) (C (C (A 3) (C (A 9) (C (A 2) (C (A 10) (C (C (A 13) (C (A 0) (A 25))) (C (A 0) (A 7))))))) (C (A 0) (A 12)))) (C (A 10) (C (C (A 3) (C (A 9) (C (A 2) (C (A 10) (C (C (A 13) (C (A 0) (A 27))) (C (A 0) (A 7))))))) (C (A 0) (A 13)))))

def frGB : Noun :=
  (C (C (A 0) (A 12)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 13) (C (A 0) (A 13))) (C (A 0) (A 7)))))))

def frBatS : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 54)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 55)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (C (A 8) (C (C (A 9) (C (A 0x2bfb) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 0) (A 58)))) (C (A 0) (A 2)))))))) (C (A 1) (C (A 0) (A 0)))) (C (C (A 8) (C (C (A 9) (C (A 0x2bfb) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 0) (A 58)))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 118)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))))) (C (C (A 1) frGF) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 119)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))))) (C (C (A 1) frGB) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))))))))))

theorem fr_bat_eq : comp.from.battery = frBatS := by kernel_rfl

/-- `+turn` over the nouns `E a` of a list, with a gate that is `G a`
encoded by `F` (a crash where `G a` is `none`). -/
theorem turn_gate_mapT {α β : Type} (E : α → Noun) (F : β → Noun) (c : Noun) (hc : HomoIn c)
    (bp bs bc : Noun) (G : α → Option β) (l : List α)
    (hf : ∀ a ∈ l, nock (C bp (C (E a) bc)) bp = (G a).map F) :
    nock (C turn.battery (C (C (listN (l.map E)) (C bp (C bs bc))) c)) turn.battery
      = (l.mapM G).map fun r => listN (r.map F) := by
  rw [turn_gate_mapM c hc bp bs bc (fun x => nock (C bp (C x bc)) bp) (l.map E) (fun _ _ => rfl)]
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha := hf a (by simp)
    have iht := ih (fun b hb => hf b (by simp [hb]))
    simp only [List.map_cons, List.mapM_cons, ha]
    cases e : G a with
    | none => simp
    | some b =>
      cases e2 : List.mapM (fun x => nock (C bp (C x bc)) bp) (List.map E t) with
      | none =>
        rw [e2] at iht
        cases e3 : t.mapM G with
        | none => simp [e2]
        | some r => rw [e3] at iht; simp at iht
      | some r =>
        rw [e2] at iht
        cases e3 : t.mapM G with
        | none => rw [e3] at iht; simp at iht
        | some r' =>
          rw [e3] at iht
          simp only [Option.map_some, Option.some.injEq] at iht
          simp [e2, iht]

/-- The fork gate of the `+turn`, in the model. -/
noncomputable def fFork (axe : Nat) (e : Lazy.ForkE CSet) : Option (Lazy.ForkE CSet) :=
  (Lazy.fromL axe e.1.2).bind fun y' => (Lazy.fromL axe e.2.2).map fun n' => ((e.1.1, y'), (e.2.1, n'))

/-- The bond gate of the `+turn`, in the model. -/
noncomputable def fBond (axe : Nat) (e : Nat × Lazy CSet) : Option (Nat × Lazy CSet) :=
  (Lazy.fromL axe e.2).map fun l' => (e.1, l')

theorem fromForks_mapM (axe : Nat) : ∀ fk : List (Lazy.ForkE CSet), Lazy.fromForks axe fk = fk.mapM (fFork axe)
  | [] => rfl
  | ((oy, y), (on, n)) :: rest => by
    simp only [Lazy.fromForks, List.mapM_cons, fFork, fromForks_mapM axe rest]
    cases Lazy.fromL axe y <;> cases Lazy.fromL axe n <;> cases rest.mapM (fFork axe) <;> rfl

theorem fromBonds_mapM (axe : Nat) : ∀ bd : List (Nat × Lazy CSet), Lazy.fromBonds axe bd = bd.mapM (fBond axe)
  | [] => rfl
  | (ob, l) :: rest => by
    simp only [Lazy.fromBonds, List.mapM_cons, fBond, fromBonds_mapM axe rest]
    cases Lazy.fromL axe l <;> cases rest.mapM (fBond axe) <;> rfl

section
variable (hc : CompIn ctx) (G : Noun) (axe : Nat)
include hc

mutual
/-- **`+from` on every lazy need** (forks and bonds to any depth) whose sure
needs look at no axis `0`: `fromL axe`, on every state noun `G`. -/
theorem cfr_all : ∀ (laz : Lazy CSet) (o : Nat), WalkP lok0 o laz →
    nock (C comp.from.battery (C (C (A axe) laz.toNoun) (C comp.door (C G ctx)))) comp.from.battery
      = (Lazy.fromL axe laz).map Lazy.toNoun
  | Lazy.mk s fk bd, o, ⟨hs, hfk, hbd⟩ => by
    have hf := comp_from_sure hc G axe s hs
    rw [lazy_toNoun_mk]
    conv => { lhs; arg 2; rw [fr_bat_eq]; unfold frBatS }
    have tF := lz_test forkE fk
    have tB := lz_test bondE bd
    have hFk := turn_gate_mapT forkE forkE layer2 homoIn_layer2 frGF (C (C (A 0) lzBunt) (C (A 0) lzBunt))
      (C comp.from.battery (C (C (A axe) (C s.toNoun (C (listN (fk.map forkE)) (listN (bd.map bondE)))))
        (C comp.door (C G ctx)))) (fFork axe) fk (fun e he => cfr_forks fk hfk e he _)
    have hBd := turn_gate_mapT bondE bondE layer2 homoIn_layer2 frGB (C (A 0) lzBunt)
      (C comp.from.battery (C (C (A axe) (C s.toNoun (C (listN (fk.map forkE)) (listN (bd.map bondE)))))
        (C comp.door (C G ctx)))) (fBond axe) bd (fun e he => cfr_bonds bd hbd e he _)
    unfold lzBunt at hFk hBd
    rcases tF with ⟨t1, t2, t3⟩ | ⟨t1, t2, t3⟩ <;> rcases tB with ⟨t4, t5, t6⟩ | ⟨t4, t5, t6⟩ <;>
    · first | replace t1 := eq_false t1 | replace t1 := eq_true t1
      first | replace t4 := eq_false t4 | replace t4 := eq_true t4
      cases e1 : fromSure axe s with
      | none =>
        rw [e1] at hf
        simp [nock_exec, comp_from_sure_at, comp_from_sure_arm, hf, Lazy.fromL, e1, t1, t2, t3, t4, t5, t6, Lazy.toNoun_ofSure, lazyNoun, List.isEmpty_iff]
      | some s' =>
        rw [e1] at hf
        cases e2 : fk.mapM (fFork axe) with
        | none =>
          rw [e2] at hFk
          simp [nock_exec, comp_from_sure_at, comp_from_sure_arm, hf, Lazy.fromL, e1, t1, t2, t3, t4, t5, t6, Lazy.toNoun_ofSure, lazyNoun, List.isEmpty_iff,
            hc, turn.arm_at, turn_arm, hFk, fromForks_mapM, e2, buntGate]
        | some f' =>
          rw [e2] at hFk
          cases e3 : bd.mapM (fBond axe) with
          | none =>
            rw [e3] at hBd
            simp [nock_exec, comp_from_sure_at, comp_from_sure_arm, hf, Lazy.fromL, e1, t1, t2, t3, t4, t5, t6, Lazy.toNoun_ofSure, lazyNoun, List.isEmpty_iff,
              hc, turn.arm_at, turn_arm, hFk, hBd, fromForks_mapM, fromBonds_mapM, e2, e3, buntGate]
          | some b' =>
            rw [e3] at hBd
            simp [nock_exec, comp_from_sure_at, comp_from_sure_arm, hf, Lazy.fromL, e1, t1, t2, t3, t4, t5, t6, Lazy.toNoun_ofSure, lazyNoun, List.isEmpty_iff,
              hc, turn.arm_at, turn_arm, hFk, hBd, fromForks_mapM, fromBonds_mapM, e2, e3, buntGate,
              lazy_toNoun_mk]

theorem cfr_forks : ∀ (fk : List (Lazy.ForkE CSet)), WalkPF lok0 fk → ∀ e ∈ fk, ∀ L : Noun,
    nock (C frGF (C (forkE e) (C comp.from.battery (C (C (A axe) L) (C comp.door (C G ctx)))))) frGF
      = (fFork axe e).map forkE
  | [], _, e, he => absurd he List.not_mem_nil
  | ((oy, y), (on, n)) :: rest, ⟨hy, hn, hr⟩, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro L
      have ihy := cfr_all y oy hy
      have ihn := cfr_all n on hn
      unfold frGF
      cases e1 : Lazy.fromL axe y with
      | none => rw [e1] at ihy; simp [nock_exec, forkE, ihy, fFork, e1]
      | some y' =>
        rw [e1] at ihy
        cases e2 : Lazy.fromL axe n with
        | none => rw [e2] at ihn; simp [nock_exec, forkE, ihy, ihn, fFork, e1, e2]
        | some n' => rw [e2] at ihn; simp [nock_exec, forkE, ihy, ihn, fFork, e1, e2]
    · exact cfr_forks rest hr e he'

theorem cfr_bonds : ∀ (bd : List (Nat × Lazy CSet)), WalkPB lok0 bd → ∀ e ∈ bd, ∀ L : Noun,
    nock (C frGB (C (bondE e) (C comp.from.battery (C (C (A axe) L) (C comp.door (C G ctx)))))) frGB
      = (fBond axe e).map bondE
  | [], _, e, he => absurd he List.not_mem_nil
  | (ob, l) :: rest, ⟨hl, hr⟩, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro L
      have ihl := cfr_all l ob hl
      unfold frGB
      cases e1 : Lazy.fromL axe l with
      | none => rw [e1] at ihl; simp [nock_exec, bondE, ihl, fBond, e1]
      | some l' => rw [e1] at ihl; simp [nock_exec, bondE, ihl, fBond, e1]
    · exact cfr_bonds rest hr e he'
end

end

end Compiler
end Formalization
