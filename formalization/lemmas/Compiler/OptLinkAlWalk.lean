import lemmas.Compiler.OptLinkAlWFinAll
import lemmas.Compiler.OptLinkAlStartImms

/-!
# `+alias`: the stores and the next turn (phase 15, README Gaps 13), the walk cut

```hoon
  =.  new.gen  (~(put by new.gen) o [par-new body-new fin-new])
  =.  info.gen  (~(put by info.gen) o info-local.gen)
  =.  imms.gen  (~(put by imms.gen) o imms-local.gen)
  $(topo t.topo)
```

* `alWalkC`, `alW1` to `alW6`: the walk `alWalk` cut after the test of an
  unreachable block, at each `=^` and `=.` (`alWalk_cut`, by `rfl`).
* `store_put`: `+put:by` on a map of labels whose values are related by any
  `R` to the model's `Nat → Option α` (`InfoStoreRel`, `ImmsStoreRel`).
* **`al_tail`**: on `gen` `GenRelL g loc imml`, `alTail` stores the block
  `[par-new body-new fin-new]`, `info-local` and `imms-local` at `o` and runs
  the walk on `t.topo` with `gen` `GenRel` to `g` with the three stores of
  the model's `aliasBlock`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The walk cut -/

/-- After `=^  fin-new  gen`: `alFin`, then `alTail`. -/
def alW6 : Noun :=
  C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4))
    (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C alFin alTail)))))))

/-- After `=^  par-new  gen`: the body, then `alW6`. -/
def alW5 : Noun :=
  C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4))
    (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C alBody alW6)))))))

/-- The parameters, then `alW5`. -/
def alW4 : Noun := C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C alPars alW5)))

/-- The two `=.` (`info-local.gen`, `imms-local.gen`) and `bob`, then `alW4`. -/
def alW3 : Noun :=
  C (A 7) (C (C (A 10) (C (C (A 2014) (C (A 0) (A 6))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 4030)
    (C (A 0) (A 2))) (C (A 0) (A 1)))) (C (A 8) (C alBob alW4)))))

/-- After `=^  info  gen`: `imms`, then `alW3`. -/
def alW2 : Noun :=
  C (A 7) (C (C (A 10) (C (C (A 30) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4))
    (C (A 0) (A 3))) (C (A 8) (C alImms alW3)))))

/-- A block that is reached: `=^  info  gen`, then `alW2`. -/
def alW1 : Noun := C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C alInfo alW2)))

/-- The walk with the branch of a reached block named. -/
def alWalkC : Noun :=
  C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 247)))) (C (C (C (A 0) (A 895)) (C (A 0) (A 12)))
    (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C alPre (C (A 6) (C alUnT (C alUnB alW1)))))))))

theorem alWalk_cut : alWalk = alWalkC := rfl

/-! ## The stores -/

/-- `+put:by` on a map of labels to nouns related by `R` to the values of `m`. -/
theorem store_put {α : Type} {R : Noun → α → Prop} {N : Noun} {m : Nat → Option α}
    (h : IsMap mugF N ∧ (∀ k v, Get N k v → ∃ o x, k = A o ∧ m o = some x ∧ R v x) ∧
      ∀ o x, m o = some x → KIn N (A o))
    {v : Noun} {x : α} (hv : R v x) (k : Nat) :
    ∃ N', nock (C by.put.battery (C (C (A k) v) (C by.battery (C N layer2)))) by.put.battery = some N' ∧
      (IsMap mugF N' ∧ (∀ k' w, Get N' k' w → ∃ o y, k' = A o ∧ Opt.updA m k (some x) o = some y ∧ R w y) ∧
        ∀ o y, Opt.updA m k (some x) o = some y → KIn N' (A o)) := by
  obtain ⟨out, hp, ho, hg⟩ := putF_spec mugF N (A k) v h.1
  refine ⟨out, put_gate (mug := mugF) layer2 gorIn_morIn_layer2 _ _ _ _ hp, ho, fun kn w hw => ?_,
    fun r y hy => ?_⟩
  · rcases (hg kn w).1 hw with ⟨rfl, rfl⟩ | ⟨hne, hw'⟩
    · exact ⟨k, x, rfl, by simp [Opt.updA], hv⟩
    · obtain ⟨r, y, rfl, hy, hr⟩ := h.2.1 _ _ hw'
      have : r ≠ k := fun e => hne (by rw [e])
      exact ⟨r, y, rfl, by simp [Opt.updA, this, hy], hr⟩
  · by_cases e : r = k
    · subst e; exact ⟨v, (hg _ _).2 (Or.inl ⟨rfl, rfl⟩)⟩
    · have hy' : m r = some y := by simpa [Opt.updA, e] using hy
      obtain ⟨w, hw⟩ := h.2.2 r y hy'
      exact ⟨w, (hg _ _).2 (Or.inr ⟨fun h' => e (Noun.atom.inj h'), hw⟩)⟩

/-- The model's state after the stores of a block. -/
def alStored (g : Opt.AGen (TreapMap mugF)) (loc : Opt.AInfo) (imml : Opt.AImms) (o : Nat) (b : Blob) :
    Opt.AGen (TreapMap mugF) :=
  { new := HoonMap.put g.new o b
    old := g.old
    info := Opt.updA g.info o (some loc)
    imms := Opt.updA g.imms o (some imml)
    rev := g.rev
    folded := g.folded }

/-- **Phase 15**: the stores into `new.gen`, `info.gen`, `imms.gen` and the
walk on `t.topo`. -/
theorem al_tail {g : Opt.AGen (TreapMap mugF)} {loc : Opt.AInfo} {imml : Opt.AImms} {GEN : Noun}
    (hg : GenRelL g loc imml GEN) (b : Blob) (BOB X4 X5 X6 GEN0 NA BL REV T : Noun) (o : Nat) :
    ∃ GEN', GenRel (alStored g loc imml o b) GEN' ∧
      nock (C (C (Termin.toNoun b.fin) GEN) (alFS (listNoun Pole.toNoun b.body) (listNoun A b.par) BOB X4 X5 X6
        (alWS GEN0 NA BL REV (C (A o) T)))) alTail = nock (alWS GEN' NA BL REV T) alWalk := by
  obtain ⟨OLD, INFO, IMMS, LOC, IMML, R, rfl, hO, hI, hM, hR, hL, hIm⟩ := hg
  have hpn := putF_hoonMap Blob.toNoun g.new o b
  have hpn' := put_gate (mug := mugF) layer2 gorIn_morIn_layer2 _ _ _ _ hpn
  obtain ⟨INFO', hpi, hI'⟩ := store_put hI hL o
  obtain ⟨IMMS', hpm, hM'⟩ := store_put hM hIm o
  refine ⟨genN (HoonMap.toNoun Blob.toNoun (HoonMap.put g.new o b)) OLD INFO' IMMS' LOC IMML R (flag g.folded),
    ⟨OLD, INFO', IMMS', LOC, IMML, R, rfl, hO, hI', hM', hR⟩, ?_⟩
  obtain ⟨a1, a2, a3, a4, a5, hX⟩ : ∃ a1 a2 a3 a4 a5, alBat = C a1 (C a2 (C a3 (C a4 (C a5 alWalk)))) :=
    ⟨_, _, _, _, _, rfl⟩
  have hLy := optC_layer2
  unfold alWS alFS
  rw [hX]
  unfold genN
  simp only [Blob.toNoun] at hpn'
  generalize optC = OC at hLy
  generalize HoonMap.toNoun Blob.toNoun (HoonMap.put g.new o b) = NEW' at hpn' ⊢
  generalize HoonMap.toNoun Blob.toNoun g.new = NEW at hpn' ⊢
  simp [nock_exec, alTail, hLy, by.arm_at, by_arm, by.put.arm_at, put_arm, hpn', hpi, hpm]

end Compiler
end Formalization
