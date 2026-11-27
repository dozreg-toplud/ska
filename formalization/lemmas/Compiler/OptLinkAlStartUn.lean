import lemmas.Compiler.OptLinkAlStart
import lemmas.Compiler.OptLinkAlNounsStart
import lemmas.Compiler.OptLinkHelpers
import lemmas.Compiler.OptLinkMiddle

/-!
# `+alias`: the unreachable block (phase 8 of the plan, README Gaps 13)

```hoon
  ?:  &(=(~ pre) !=(0w0 o))
    =.  folded.gen  &
    =.  rev.gen
      %+  roll  (get-jmps fin:(~(got by blocks) o))
      |=  [j=jmp acc=_rev.gen]
      (~(del ju acc) there.j o)
    $(topo t.topo)
```

* `jug_del`, `jug_delJu`: **`+del:ju`** of a label under a label on a
  `JugRel` jug; on lists with no duplicates (`RevNodup`) it is `delJu`.
* `jmp_bunt_at`: the bunt of `jmp` (the mold, arm `20` of `compTypes`, on its
  default sample), which the gate of the `+roll` holds as its first sample.
* `al_unt`: the test `&(=(~ pre) !=(0w0 o))`.
* `al_unreach`: **the branch of an unreachable block** sets `folded`, deletes
  the edges of the block's jumps from `rev.gen` (the model's `foldl` of
  `delJu`), and runs the walk on `t.topo`: the first branch of `aliasBlock`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## `+del:ju` on jugs of labels -/

theorem getF_congr {a b k : Noun} (ha : IsMap mugF a) (hb : IsMap mugF b) (h : ∀ v, Get a k v ↔ Get b k v) :
    getF mugF k a = getF mugF k b := by
  by_cases hx : ∃ v, Get a k v
  · obtain ⟨v, hv⟩ := hx
    rw [getF_some ha hv, getF_some hb ((h v).1 hv)]
  · rw [getF_none ha (fun v hv => hx ⟨v, hv⟩), getF_none hb (fun v hv => hx ⟨v, (h v).2 hv⟩)]

/-- `+del:in` of a label on a set of atoms, as `delInF`. -/
theorem sawRel_delIn {S : Noun} {l : List Nat} (h : SawRel S l) (t : Nat) :
    ∃ S', delInF mugF (A t) S = some S' ∧ SawRel S' (l.filter fun x => x ≠ t) := by
  have hm : IsMap mugF (toMap S) := h.1
  obtain ⟨out', hd, hm', hg⟩ := delF_spec (A t) hm
  rw [delF_toMap (A t) S h.1] at hd
  cases hx : delInF mugF (A t) S with
  | none => rw [hx] at hd; cases hd
  | some out =>
    rw [hx] at hd
    simp only [Option.map_some, Option.some.injEq] at hd
    subst hd
    refine ⟨out, rfl, hm', fun k => ?_⟩
    have e := hg k (A 0)
    unfold Has
    rw [e]
    change k ≠ A t ∧ Has S k ↔ _
    rw [h.2 k]
    constructor
    · rintro ⟨hk, n, hn, rfl⟩
      exact ⟨n, List.mem_filter.2 ⟨hn, by simpa using fun e => hk (by rw [e])⟩, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      obtain ⟨hn, hne⟩ := List.mem_filter.1 hn
      exact ⟨fun e => by simp at hne; exact hne (Noun.atom.inj e), n, hn, rfl⟩

/-- **`+del:ju`** of `o` under `k`: the set at `k` filtered. -/
theorem jug_del {J : Noun} {f : Nat → List Nat} (h : JugRel J f) (k o : Nat) :
    ∃ J', nock (C ju.del.battery (C (C (A k) (A o)) (C ju.battery (C J layer2)))) ju.del.battery = some J' ∧
      JugRel J' (fun p => if p = k then (f k).filter (fun x => x ≠ o) else f p) := by
  obtain ⟨out, hg, hS⟩ := h.2 k
  obtain ⟨e, he, hSe⟩ := sawRel_delIn hS o
  by_cases e0 : e = A 0
  · subst e0
    obtain ⟨J', hd, hmJ, hgJ⟩ := delF_spec (mug := mugF) (A k) h.1
    have hj : juDelF mugF (A k) (A o) J = some J' := by simp [juDelF, juGetF, hg, he, hd]
    refine ⟨J', ju_del_gate layer2 juIn_layer2' _ _ _ _ hj, hmJ, fun p => ?_⟩
    by_cases e1 : p = k
    · subst e1
      exact ⟨A 0, getF_none hmJ (fun v hv => ((hgJ _ v).1 hv).1 rfl), by simpa [unUnit] using hSe⟩
    · have hne : A p ≠ A k := fun e => e1 (Noun.atom.inj e)
      obtain ⟨out', hg', hS'⟩ := h.2 p
      refine ⟨out', ?_, by simpa [e1] using hS'⟩
      rw [getF_congr hmJ h.1 (fun v => by rw [hgJ]; exact ⟨fun x => x.2, fun x => ⟨hne, x⟩⟩), hg']
  · obtain ⟨J', hpJ, hmJ, hgJ⟩ := putF_spec mugF J (A k) e h.1
    have hj : juDelF mugF (A k) (A o) J = some J' := by simp [juDelF, juGetF, hg, he, e0, hpJ]
    refine ⟨J', ju_del_gate layer2 juIn_layer2' _ _ _ _ hj, hmJ, fun p => ?_⟩
    have hga := getF_after_put h.1 hmJ hgJ (A p)
    by_cases e1 : p = k
    · subst e1
      exact ⟨C (A 0) e, by simp [hga], by simpa [unUnit] using hSe⟩
    · obtain ⟨out', hg', hS'⟩ := h.2 p
      have hne : A p ≠ A k := fun e => e1 (Noun.atom.inj e)
      exact ⟨out', by rw [hga, if_neg hne, hg'], by simpa [e1] using hS'⟩

theorem jugRel_congr {J : Noun} {f f' : Nat → List Nat} (h : JugRel J f) (e : ∀ p x, x ∈ f p ↔ x ∈ f' p) :
    JugRel J f' :=
  ⟨h.1, fun p => let ⟨out, hg, hs⟩ := h.2 p; ⟨out, hg, sawRel_congr hs (e p)⟩⟩

/-- **`+del:ju`** on lists with no duplicates: `delJu`. -/
theorem jug_delJu {J : Noun} {f : Nat → List Nat} (h : JugRel J f) (hn : Opt.RevNodup f) (k o : Nat) :
    ∃ J', nock (C ju.del.battery (C (C (A k) (A o)) (C ju.battery (C J layer2)))) ju.del.battery = some J' ∧
      JugRel J' (Opt.delJu f k o) := by
  obtain ⟨J', h1, h2⟩ := jug_del h k o
  refine ⟨J', h1, jugRel_congr h2 (fun p x => ?_)⟩
  by_cases e : p = k
  · subst e
    simp only [Opt.delJu, Opt.updA, if_true, List.mem_filter, (hn p).mem_erase_iff, decide_eq_true_eq]
    exact ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, b⟩ => ⟨b, a⟩⟩
  · simp [Opt.delJu, Opt.updA, e]

/-! ## The bunt of `jmp` -/

/-- The mold `jmp`, arm `20` of `compTypes`. -/
noncomputable def jmpMold : Noun := (slot? 20 compTypes).getD (A 0)
theorem jmp_mold_at : slot? 20 compTypes = some jmpMold := by kernel_rfl
/-- The gate the mold builds. -/
noncomputable def jmpGate : Noun := (evalFuel 200 compTypes jmpMold).getD (A 0)
theorem jmp_gate : nock compTypes jmpMold = some jmpGate :=
  nock_of_evalFuel (fuel := 200) (by kernel_rfl)
/-- The battery of that gate. -/
noncomputable def jmpGateBat : Noun := (slot? 2 jmpGate).getD (A 0)
theorem jmp_gate_bat : slot? 2 jmpGate = some jmpGateBat := by kernel_rfl
/-- The bunt of `jmp`. -/
noncomputable def jmpBunt : Noun := (evalFuel 2000 jmpGate jmpGateBat).getD (A 0)
theorem jmp_bunt : nock jmpGate jmpGateBat = some jmpBunt :=
  nock_of_evalFuel (fuel := 2000) (by kernel_rfl)

/-- `*jmp` from a subject with `compTypes` at axis `255`. -/
theorem jmp_bunt_at (d : Noun) (h : slot? 255 d = some compTypes) :
    nock d (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))
      = some jmpBunt := by
  have h1 := jmp_mold_at
  have h2 := jmp_gate
  generalize compTypes = CT at h h1 h2
  simp [nock_exec, h, h1, h2, jmp_gate_bat, jmp_bunt]

/-! ## The test and the branch -/

/-- **The test** `&(=(~ pre) !=(0w0 o))`. -/
theorem al_unt (GEN NA BL REV T : Noun) (pre : List Nat) (o : Nat) :
    nock (C (listNoun A pre) (alWS GEN NA BL REV (C (A o) T))) alUnT = some (flag (pre = [] ∧ o ≠ 0)) := by
  unfold alWS
  cases pre with
  | nil =>
    by_cases h : o = 0
    · subst h; simp [nock_exec, alUnT, listNoun, flag, eqCode]
    · simp [nock_exec, alUnT, listNoun, flag, h, eqCode, Ne.symm h]
  | cons x l => simp [nock_exec, alUnT, listNoun, flag, eqCode]

/-- The gate of the `+roll`: `(~(del ju acc) there.j o)`. -/
theorem al_ung (PRE GEN NA BL REV T JB : Noun) (o : Nat) (j : Jmp) (N : Noun) (f : Nat → List Nat)
    (hJ : JugRel N f) (hn : Opt.RevNodup f) :
    ∃ N', nock (C alUnG (C (C j.toNoun N) (C PRE (alWS GEN NA BL REV (C (A o) T))))) alUnG = some N' ∧
      JugRel N' (Opt.delJu f j.there o) := by
  obtain ⟨N', hd, hR⟩ := jug_delJu hJ hn j.there o
  refine ⟨N', ?_, hR⟩
  have hL := optC_layer2
  unfold alWS
  generalize optC = OC at hL
  simp [nock_exec, alUnG, Jmp.toNoun, hL, ju.arm_at, ju_arm, ju.del.arm_at, ju_del_arm, hd]

/-- The model's state after an unreachable block (the first branch of `aliasBlock`). -/
def alUnState (g : Opt.AGen (TreapMap mugF)) (o : Nat) (b : Blob) : Opt.AGen (TreapMap mugF) :=
  { g with folded := true, rev := (Opt.getJmps b.fin).foldl (fun acc j => Opt.delJu acc j.there o) g.rev }

/-- **The branch of an unreachable block**: `folded` set, the edges of the
block's jumps deleted from `rev.gen`, and the walk on `t.topo`. -/
theorem al_unreach {g : Opt.AGen (TreapMap mugF)} {GEN : Noun} (hg : GenRel g GEN) (hn : Opt.RevNodup g.rev)
    (NA REV T PRE : Noun) (bl : TreapMap mugF Blob) (hl : NoLti bl) (o : Nat) (b : Blob)
    (hb : HoonMap.get bl o = some b) :
    ∃ GEN', GenRel (alUnState g o b) GEN' ∧
      nock (C PRE (alWS GEN NA (HoonMap.toNoun Blob.toNoun bl) REV (C (A o) T))) alUnB
        = nock (alWS GEN' NA (HoonMap.toNoun Blob.toNoun bl) REV T) alWalk := by
  obtain ⟨OLD, INFO, IMMS, LOC, IMML, R, rfl, hO, hI, hM, hR⟩ := hg
  have hgot := blocks_got bl o
  rw [hb] at hgot
  have hgj := gj_gate compTypes b.fin (hl o b hb)
  obtain ⟨R', hroll, hR', -⟩ := roll_gate_rel Jmp.toNoun (fun N r => JugRel N r ∧ Opt.RevNodup r)
    (fun j r => some (Opt.delJu r j.there o)) layer2 alUnG jmpBunt
    (C PRE (alWS (genN (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMS LOC IMML R (A 0)) NA
      (HoonMap.toNoun Blob.toNoun bl) REV (C (A o) T)))
    (Opt.getJmps b.fin) g.rev R _
    (fun j _ s N s' ⟨hJ, hs⟩ e => by
      cases e
      obtain ⟨N', h1, h2⟩ := al_ung PRE _ NA _ REV T jmpBunt o j N s hJ hs
      exact ⟨N', h1, h2, Opt.revNodup_delJu hs _ _⟩)
    ⟨hR, hn⟩ (foldlM_some _ _ _)
  refine ⟨genN (HoonMap.toNoun Blob.toNoun g.new) OLD INFO IMMS LOC IMML R' (A 0),
    ⟨OLD, INFO, IMMS, LOC, IMML, R', by simp [alUnState, flag], hO, hI, hM, hR'⟩, ?_⟩
  rw [← listNoun_map_listN] at hroll
  obtain ⟨a1, a2, a3, a4, a5, hX⟩ : ∃ a1 a2 a3 a4 a5, alBat = C a1 (C a2 (C a3 (C a4 (C a5 alWalk)))) :=
    ⟨_, _, _, _, _, rfl⟩
  have hL := optC_layer2
  have hT := optC_types
  have hgja := gj_at
  unfold alWS at hroll ⊢
  rw [hX] at hroll ⊢
  unfold genN at hroll ⊢
  generalize optC = OC at hL hT hroll
  generalize HoonMap.toNoun Blob.toNoun bl = BL at hgot hroll
  simp [nock_exec, alUnB, alUnRoll_cut, alUnRollC, hL, hT, roll.arm_at, roll_arm, hgja, gj_arm, hgj, by.arm_at, by_arm,
    by.got.arm_at, got_arm, hgot, Blob.toNoun, jmp_mold_at, jmp_gate, jmp_gate_bat, jmp_bunt, hroll]

end Compiler
end Formalization
