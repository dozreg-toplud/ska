import lemmas.Compiler.CompCoerceLazy
import lemmas.Compiler.CompWalkGen

/-!
# `+coerce-lazy` on every lazy need

`+coerce-lazy` (`CompCoerceLazy.lean`, the gate body `czBody`) on `[ned o laz
less]` with forks and bonds: the root part (`czX`: the `+rep:in` over
`lok`, `+sure-require-look`, the trap `sure-loop`) on `sure.laz`, then
`czTail`: `?:  &(?=(~ fork.laz) ?=(~ bond.laz))  gen`, otherwise `+roll` of
layer 2 over the bonds with the gate `czBG` (`=.  gen  gen-acc`, then the
gate itself slammed on `[ned o laz less]` of the bond: `czOrig` with the
bond's label and need), then `+roll` over the forks with `czFG` (the yes
need, then the no need).  `czTail` with its gates named is `czTailS`
(`cz_tail_eq`).

The model is `coerceLazyL` of `Ska/CompLazyFinal.lean`: `coerceLazy` at the
root, then (unless both lists are empty) `coerceBonds`, then
`coerceForks`, each entry with the same `ned` and `less`.  The order (the
bonds before the forks, the yes need before the no need), the state
threading and the recursion with the same `ned` agree with the Hoon: no
departure.  As in `cz_gate`, the model has no test `(~(has by soft.gen) o)`
at a `%this`: every visited block is not a key of `soft` (`WalkP` of
`x.SoftOut`, which `x.NoSoft` gives).

**`cz_all`**, **`comp_coerce_lazy_all`**: the gate on every lazy need (forks
and bonds to any depth) is `coerceLazyL`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun}

/-! ## The Nock of the tail -/

/-- The gate of the `+roll` over the bonds: `=.  gen  gen-acc`, then the gate
slammed on the bond's label and need. -/
def czBG : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 13))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 0) (A 7)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (C (A 0) (A 56)) (C (C (A 0) (A 57)) (C (A 0) (A 503)))))) (C (A 0) (A 2))))))))))

/-- The gate of the `+roll` over the forks: the yes need, then the no need. -/
def czFG : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 13))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 8) (C (C (A 0) (A 7)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (C (A 0) (A 112)) (C (C (A 0) (A 113)) (C (A 0) (A 503)))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 0) (A 7)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (C (A 0) (A 114)) (C (C (A 0) (A 115)) (C (A 0) (A 503)))))) (C (A 0) (A 2))))))))))))

/-- `czTail` with its two roll gates named. -/
def czTailS : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 218)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 219)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 0) (A 30)) (C (A 7) (C (C (A 10) (C (C (A 30) (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 475)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (C (A 1) (A 0)) (C (A 7) (C (C (A 9) (C (A 191) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))) (C (A 0) (A 30))) (C (C (A 1) czBG) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 474)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (C (C (A 1) (A 0)) (C (A 7) (C (C (A 9) (C (A 191) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))) (C (C (A 1) (A 0)) (C (A 7) (C (C (A 9) (C (A 191) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))) (C (A 0) (A 30))) (C (C (A 1) czFG) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))))))))

theorem cz_tail_eq : czTail = czTailS := by kernel_rfl

/-! ## The root on any lazy need -/

/-- **The `+rep:in` over `lok`** on any lazy need (`cz_lok` reads only
`sure.laz`). -/
theorem cz_lokG (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) (D G : Noun) (o : Nat)
    (ned : Need) (s : Sure CSet) (FB : Noun) (less : Cape) :
    nock (czOrig ned.toNoun o (C s.toNoun FB) less.toNoun D G ctx) czLok
      = (coerceLok s.lok less ned).map HoonSet.toNoun := by
  rw [coerceLok_eq]
  have hrep := rep_gate_list A HoonSet.toNoun (fun axe acc => czStep less ned acc axe) in.battery layer2 czGate
    (A 0) (czOrig ned.toNoun o (C s.toNoun FB) less.toNoun D G ctx) (HoonSet.toNoun s.lok) (cs_tree _)
    (HoonSet.toList s.lok) (cs_preorder _) HoonSet.empty
    (fun p _ acc => cz_gate_step hc h7 D G (C s.toNoun FB) o ned less p acc)
  rw [HoonSet.toNoun_empty] at hrep
  unfold czLok
  simp only [czOrig, Sure.toNoun] at hrep ⊢
  generalize czBody = BD at hrep ⊢
  generalize czGate = GT at hrep ⊢
  simp [nock_exec, hc, in_arm, in.arm_at, in.rep.arm_at, rep_arm, hrep]

/-- **`+sure-require-look` of `sure.laz` with the new `lok`**, on any lazy
need. -/
theorem cz_srlG (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) (x : GenRest)
    (g : Gen (TreapMap mugF)) (o : Nat) (ned : Need) (s : Sure CSet) (FB : Noun) (less : Cape) :
    nock (czOrig ned.toNoun o (C s.toNoun FB) less.toNoun comp.door (genNoun g x) ctx) czSrl
      = (coerceLok s.lok less ned).bind fun lok =>
          (sureRequireLook ⟨s.ned, lok⟩ g).map fun p => C p.1.toNoun (genNoun p.2 x) := by
  have hl := cz_lokG hc h7 comp.door (genNoun g x) o ned s FB less
  have hD := comp_srl_at
  cases e : coerceLok s.lok less ned with
  | none =>
    rw [e] at hl
    unfold czSrl
    simp only [czOrig] at hl ⊢
    generalize czLok = LK at hl ⊢
    generalize comp.door = Dr at hD hl ⊢
    simp [nock_exec, hD, comp_srl_arm, hl]
  | some lok =>
    rw [e] at hl
    have hsrl := comp_sure_require_look (x := x) hc (comp_ctx_pill ctx h7).2.1 g ⟨s.ned, lok⟩ (coerceLok_ne0 e)
    unfold czSrl
    simp only [czOrig, compCore, Sure.toNoun, Option.map_some] at hl hsrl ⊢
    generalize czLok = LK at hl ⊢
    generalize comp.door = Dr at hD hl hsrl ⊢
    simp [nock_exec, hD, comp_srl_arm, hl, Sure.toNoun, hsrl]

/-- **The root part `czX`** on any lazy need: `coerceLazy` of its sure need,
the new state. -/
theorem cz_x (h7 : slot? 7 ctx = some compK) (x : GenRest) (o : Nat) (hs : x.SoftOut o)
    (ned : Need) (s : Sure CSet) (FB : Noun) (less : Cape) (g : Gen (TreapMap mugF)) :
    nock (czOrig ned.toNoun o (C s.toNoun FB) less.toNoun comp.door (genNoun g x) ctx) czX
      = (coerceLazy ned o s less g).map fun p => genNoun p.2 x := by
  have hc := (comp_ctx_pill ctx h7).1
  have hsrl := cz_srlG hc h7 x g o ned s FB less
  unfold coerceLazy
  simp only [bind, StateT.bind]
  cases e : coerceLok s.lok less ned with
  | none =>
    rw [e] at hsrl
    unfold czX
    simp only [czOrig] at hsrl ⊢
    generalize czSrl = SR at hsrl ⊢
    generalize czLoop = LP
    simp [nock_exec, hsrl]
  | some lok =>
    rw [e] at hsrl
    simp only [Option.bind_some] at hsrl
    simp only [Option.map_some, Option.bind_some]
    cases e2 : sureRequireLook ⟨s.ned, lok⟩ g with
    | none =>
      rw [e2] at hsrl
      unfold czX
      simp only [czOrig] at hsrl ⊢
      generalize czSrl = SR at hsrl ⊢
      generalize czLoop = LP
      simp [nock_exec, hsrl]
    | some r =>
      obtain ⟨tgt, g1⟩ := r
      rw [e2] at hsrl
      have hl := cz_loop hc x o hs (C (C s.toNoun FB) less.toNoun) ned tgt g1
      simp only [czLS, compCore] at hl
      unfold czX
      simp only [czOrig, compCore, Option.bind_some, Option.map_some] at hsrl ⊢
      generalize czSrl = SR at hsrl ⊢
      cases e3 : sureLoop o ned tgt g1 with
      | none =>
        rw [e3] at hl
        generalize czLoop = LP at hl ⊢
        simp [nock_exec, hsrl, hl]
      | some r3 =>
        obtain ⟨u3, g3⟩ := r3
        rw [e3] at hl
        simp only [Option.map_some] at hsrl hl ⊢
        generalize czLoop = LP at hl ⊢
        simp [nock_exec, hsrl, hl]

/-! ## The roll gates and one step -/

theorem listN_nil' : listN [] = A 0 := rfl

/-- The bond gate on a bond entry: the gate slammed on the bond's label and
need, with the accumulated state. -/
theorem cz_bgate (NED : Noun) (o' : Nat) (L' LESS D G' : Noun) (ob : Nat) (lb acc : Noun) :
    nock (C czBG (C (C (C (A ob) lb) acc) (czOrig NED o' L' LESS D G' ctx))) czBG
      = nock (czOrig NED ob lb LESS D acc ctx) czBody := by
  unfold czBG czOrig
  simp [nock_exec]

/-- The fork gate on a fork entry: the yes need, then the no need. -/
theorem cz_fgate (NED : Noun) (o' : Nat) (L' LESS D G' : Noun) (oy on : Nat) (ly ln acc : Noun) :
    nock (C czFG (C (C (C (C (A oy) ly) (C (A on) ln)) acc) (czOrig NED o' L' LESS D G' ctx))) czFG
      = (nock (czOrig NED oy ly LESS D acc ctx) czBody).bind fun a1 => nock (czOrig NED on ln LESS D a1 ctx) czBody := by
  unfold czFG czOrig
  cases h : nock (C czBody (C (C NED (C (A oy) (C ly LESS))) (C D (C acc ctx)))) czBody with
  | none => simp [nock_exec, h]
  | some a1 => simp [nock_exec, h]

/-- What follows the root part: the two rolls, unless both lists are empty. -/
noncomputable def czCont (ctx NED : Noun) (o : Nat) (S LESS D : Noun) (fk : List (Lazy.ForkE CSet))
    (bd : List (Nat × Lazy CSet)) (G1 : Noun) : Option Noun :=
  if fk = [] ∧ bd = [] then some G1 else
  ((bd.map bondE).foldlM (fun acc y => nock (C czBG (C (C y acc)
    (czOrig NED o (C S (C (listN (fk.map forkE)) (listN (bd.map bondE)))) LESS D G1 ctx))) czBG) G1).bind
    fun G2 => (fk.map forkE).foldlM (fun acc y => nock (C czFG (C (C y acc)
      (czOrig NED o (C S (C (listN (fk.map forkE)) (listN (bd.map bondE)))) LESS D G2 ctx))) czFG) G2

section
variable (hc : CompIn ctx) (Q a M m v : Noun) (hQ : slot? 15 ctx = some Q) (ha : slot? 191 Q = some a)
  (hM : nock Q a = some M) (hmm : slot? 2 M = some m) (hv : nock M m = some v)
  (NED : Noun) (o : Nat) (S LESS D G : Noun)
include hc hQ ha hM hmm hv

theorem cz_step_none (fk : List (Lazy.ForkE CSet)) (bd : List (Nat × Lazy CSet))
    (h1 : nock (C czBody (C (C NED (C (A o) (C (C S (C (listN (fk.map forkE)) (listN (bd.map bondE)))) LESS)))
      (C D (C G ctx)))) czX = Option.none) :
    nock (czOrig NED o (C S (C (listN (fk.map forkE)) (listN (bd.map bondE)))) LESS D G ctx) czBody = Option.none := by
  unfold czOrig
  conv => { lhs; arg 2; unfold czBody; rw [cz_tail_eq]; unfold czTailS }
  simp [nock_exec, h1]

theorem cz_step_ee (G1 : Noun)
    (h1 : nock (C czBody (C (C NED (C (A o) (C (C S (C (A 0) (A 0))) LESS))) (C D (C G ctx)))) czX = some G1) :
    nock (czOrig NED o (C S (C (A 0) (A 0))) LESS D G ctx) czBody = some G1 := by
  unfold czOrig
  conv => { lhs; arg 2; unfold czBody; rw [cz_tail_eq]; unfold czTailS }
  simp [nock_exec, h1]

theorem cz_step_eb (bd : List (Nat × Lazy CSet)) (hbd : bd ≠ []) (G1 : Noun)
    (h1 : nock (C czBody (C (C NED (C (A o) (C (C S (C (A 0) (listN (bd.map bondE)))) LESS)))
      (C D (C G ctx)))) czX = some G1) :
    nock (czOrig NED o (C S (C (A 0) (listN (bd.map bondE)))) LESS D G ctx) czBody
      = czCont ctx NED o S LESS D [] bd G1 := by
  have hb : bd.map bondE ≠ [] := by simpa using hbd
  unfold czCont czOrig
  conv => { lhs; arg 2; unfold czBody; rw [cz_tail_eq]; unfold czTailS }
  simp only [List.map_nil, listN_nil']
  simp [nock_exec, h1, hbd, wl_eq_nil _ hb, wl_zero_ne _ hb, hc, roll.arm_at, roll_arm, hQ, ha, hM, hmm, hv,
    roll_gate_N, roll_gate_nil', Option.bind_assoc]

theorem cz_step_fe (fk : List (Lazy.ForkE CSet)) (hfk : fk ≠ []) (G1 : Noun)
    (h1 : nock (C czBody (C (C NED (C (A o) (C (C S (C (listN (fk.map forkE)) (A 0))) LESS)))
      (C D (C G ctx)))) czX = some G1) :
    nock (czOrig NED o (C S (C (listN (fk.map forkE)) (A 0))) LESS D G ctx) czBody
      = czCont ctx NED o S LESS D fk [] G1 := by
  have hf : fk.map forkE ≠ [] := by simpa using hfk
  unfold czCont czOrig
  conv => { lhs; arg 2; unfold czBody; rw [cz_tail_eq]; unfold czTailS }
  simp only [List.map_nil, listN_nil']
  simp [nock_exec, h1, hfk, wl_eq_nil _ hf, wl_zero_ne _ hf, hc, roll.arm_at, roll_arm, hQ, ha, hM, hmm, hv,
    roll_gate_N, roll_gate_nil', Option.bind_assoc]

theorem cz_step_fb (fk : List (Lazy.ForkE CSet)) (bd : List (Nat × Lazy CSet)) (hfk : fk ≠ []) (hbd : bd ≠ [])
    (G1 : Noun)
    (h1 : nock (C czBody (C (C NED (C (A o) (C (C S (C (listN (fk.map forkE)) (listN (bd.map bondE)))) LESS)))
      (C D (C G ctx)))) czX = some G1) :
    nock (czOrig NED o (C S (C (listN (fk.map forkE)) (listN (bd.map bondE)))) LESS D G ctx) czBody
      = czCont ctx NED o S LESS D fk bd G1 := by
  have hf : fk.map forkE ≠ [] := by simpa using hfk
  have hb : bd.map bondE ≠ [] := by simpa using hbd
  unfold czCont czOrig
  conv => { lhs; arg 2; unfold czBody; rw [cz_tail_eq]; unfold czTailS }
  simp [nock_exec, h1, hfk, hbd, wl_eq_nil _ hf, wl_zero_ne _ hf, wl_eq_nil _ hb, wl_zero_ne _ hb, hc,
    roll.arm_at, roll_arm, hQ, ha, hM, hmm, hv, roll_gate_N, roll_gate_nil', Option.bind_assoc]

end

/-- **One step of `+coerce-lazy`**: the root part, then, unless both lists
are empty, the roll of `czBG` over the bonds and of `czFG` over the forks,
each in the gate's core with the state it has reached. -/
theorem cz_step (hc : CompIn ctx) (hm : CompMold ctx 191) (NED : Noun) (o : Nat) (S LESS D G : Noun)
    (fk : List (Lazy.ForkE CSet)) (bd : List (Nat × Lazy CSet)) :
    nock (czOrig NED o (C S (C (listN (fk.map forkE)) (listN (bd.map bondE)))) LESS D G ctx) czBody
      = (nock (czOrig NED o (C S (C (listN (fk.map forkE)) (listN (bd.map bondE)))) LESS D G ctx) czX).bind
          (czCont ctx NED o S LESS D fk bd) := by
  obtain ⟨Q, a, M, m, v, hQ, ha, hM, hmm, hv⟩ := hm
  cases h1 : nock (czOrig NED o (C S (C (listN (fk.map forkE)) (listN (bd.map bondE)))) LESS D G ctx) czX with
  | none => exact cz_step_none hc Q a M m v hQ ha hM hmm hv NED o S LESS D G fk bd h1
  | some G1 =>
    simp only [Option.bind_some]
    by_cases hfk : fk = []
    · subst hfk
      by_cases hbd : bd = []
      · subst hbd
        have e := cz_step_ee hc Q a M m v hQ ha hM hmm hv NED o S LESS D G G1 h1
        simp only [List.map_nil, listN_nil'] at e ⊢
        rw [e]; simp [czCont]
      · have e := cz_step_eb hc Q a M m v hQ ha hM hmm hv NED o S LESS D G bd hbd G1
          (by simpa only [List.map_nil, listN_nil', czOrig] using h1)
        simp only [List.map_nil, listN_nil'] at e ⊢
        exact e
    · by_cases hbd : bd = []
      · subst hbd
        have e := cz_step_fe hc Q a M m v hQ ha hM hmm hv NED o S LESS D G fk hfk G1
          (by simpa only [List.map_nil, listN_nil', czOrig] using h1)
        simp only [List.map_nil, listN_nil'] at e ⊢
        exact e
      · exact cz_step_fb hc Q a M m v hQ ha hM hmm hv NED o S LESS D G fk bd hfk hbd G1 h1

/-! ## The recursion -/

theorem cz_fold_bonds (NED LESS D L G2 : Noun) (o : Nat) (bd : List (Nat × Lazy CSet)) (a : Noun) :
    (bd.map bondE).foldlM (fun acc y => nock (C czBG (C (C y acc) (czOrig NED o L LESS D G2 ctx))) czBG) a
    = bd.foldlM (fun acc e => nock (czOrig NED e.1 e.2.toNoun LESS D acc ctx) czBody) a := by
  rw [List.foldlM_map]
  congr 1
  funext acc e
  exact cz_bgate (ctx := ctx) NED o L LESS D G2 e.1 e.2.toNoun acc

theorem cz_fold_forks (NED LESS D L G1 : Noun) (o : Nat) (fk : List (Lazy.ForkE CSet)) (a : Noun) :
    (fk.map forkE).foldlM (fun acc y => nock (C czFG (C (C y acc) (czOrig NED o L LESS D G1 ctx))) czFG) a
    = fk.foldlM (fun acc e => (nock (czOrig NED e.1.1 e.1.2.toNoun LESS D acc ctx) czBody).bind fun a1 =>
        nock (czOrig NED e.2.1 e.2.2.toNoun LESS D a1 ctx) czBody) a := by
  rw [List.foldlM_map]
  congr 1
  funext acc e
  exact cz_fgate (ctx := ctx) NED o L LESS D G1 e.1.1 e.2.1 e.1.2.toNoun e.2.2.toNoun acc

section
variable (h7 : slot? 7 ctx = some compK) (x : GenRest) (ned : Need) (less : Cape)
include h7

mutual
/-- **`+coerce-lazy` on every lazy need** (forks and bonds to any depth),
with every visited block not a key of `soft`: `coerceLazyL`. -/
theorem cz_all : ∀ (laz : Lazy CSet) (o : Nat) (g : Gen (TreapMap mugF)), WalkP (fun o _ => x.SoftOut o) o laz →
    nock (czOrig ned.toNoun o laz.toNoun less.toNoun comp.door (genNoun g x) ctx) czBody
      = (coerceLazyL ned less o laz g).map fun p => genNoun p.2 x
  | Lazy.mk s fk bd, o, g, ⟨hs, hfk, hbd⟩ => by
    obtain ⟨hc, -, hm⟩ := comp_ctx_pill ctx h7
    rw [lazy_toNoun_mk, cz_step hc hm.1, cz_x h7 x o hs ned s _ less g]
    unfold czCont
    simp only [cz_fold_forks, cz_fold_bonds]
    cases e1 : coerceLazy ned o s less g with
    | none => simp [coerceLazyL, e1, bind, StateT.bind]
    | some p =>
      obtain ⟨u, g1⟩ := p
      by_cases hfb : fk = [] ∧ bd = []
      · obtain ⟨rfl, rfl⟩ := hfb
        simp [coerceLazyL, e1, bind, StateT.bind, pure, StateT.pure]
      · simp only [Option.map_some, Option.bind_some, hfb, if_false]
        rw [cz_bonds bd g1 hbd]
        cases e2 : coerceBonds ned less bd g1 with
        | none => simp [coerceLazyL, e1, e2, bind, StateT.bind, hfb]
        | some q =>
          obtain ⟨u2, g2⟩ := q
          simp only [Option.map_some, Option.bind_some]
          rw [cz_forks fk g2 hfk]
          simp [coerceLazyL, e1, e2, bind, StateT.bind, hfb]

theorem cz_bonds : ∀ (bd : List (Nat × Lazy CSet)) (g : Gen (TreapMap mugF)), WalkPB (fun o _ => x.SoftOut o) bd →
    bd.foldlM (fun acc e => nock (czOrig ned.toNoun e.1 e.2.toNoun less.toNoun comp.door acc ctx) czBody) (genNoun g x)
      = (coerceBonds ned less bd g).map fun p => genNoun p.2 x
  | [], g, _ => by simp [coerceBonds, pure, StateT.pure]
  | (ob, l) :: rest, g, ⟨hl, hr⟩ => by
    simp only [List.foldlM_cons]
    rw [cz_all l ob g hl]
    cases e1 : coerceLazyL ned less ob l g with
    | none => simp [coerceBonds, e1, bind, StateT.bind]
    | some p =>
      obtain ⟨u, g1⟩ := p
      simp only [Option.map_some, Option.bind_some, Option.bind_eq_bind]
      rw [cz_bonds rest g1 hr]
      simp [coerceBonds, e1, bind, StateT.bind]

theorem cz_forks : ∀ (fk : List (Lazy.ForkE CSet)) (g : Gen (TreapMap mugF)), WalkPF (fun o _ => x.SoftOut o) fk →
    fk.foldlM (fun acc e => (nock (czOrig ned.toNoun e.1.1 e.1.2.toNoun less.toNoun comp.door acc ctx) czBody).bind
      fun a1 => nock (czOrig ned.toNoun e.2.1 e.2.2.toNoun less.toNoun comp.door a1 ctx) czBody) (genNoun g x)
      = (coerceForks ned less fk g).map fun p => genNoun p.2 x
  | [], g, _ => by simp [coerceForks, pure, StateT.pure]
  | ((oy, y), (on, n)) :: rest, g, ⟨hy, hn, hr⟩ => by
    simp only [List.foldlM_cons]
    rw [cz_all y oy g hy]
    cases e1 : coerceLazyL ned less oy y g with
    | none => simp [coerceForks, e1, bind, StateT.bind]
    | some p =>
      obtain ⟨u, g1⟩ := p
      simp only [Option.map_some, Option.bind_some, Option.bind_eq_bind]
      rw [cz_all n on g1 hn]
      cases e2 : coerceLazyL ned less on n g1 with
      | none => simp [coerceForks, e1, e2, bind, StateT.bind]
      | some q =>
        obtain ⟨u2, g2⟩ := q
        simp only [Option.map_some, Option.bind_some, Option.bind_eq_bind]
        rw [cz_forks rest g2 hr]
        simp [coerceForks, e1, e2, bind, StateT.bind]
end

end

mutual
theorem walkP_true (P : Nat → Sure CSet → Prop) (hP : ∀ o s, P o s) : ∀ (o : Nat) (laz : Lazy CSet), WalkP P o laz
  | o, Lazy.mk s fk bd => ⟨hP o s, walkPF_true P hP fk, walkPB_true P hP bd⟩

theorem walkPF_true (P : Nat → Sure CSet → Prop) (hP : ∀ o s, P o s) : ∀ (fk : List (Lazy.ForkE CSet)), WalkPF P fk
  | [] => trivial
  | ((oy, y), (on, n)) :: rest => ⟨walkP_true P hP oy y, walkP_true P hP on n, walkPF_true P hP rest⟩

theorem walkPB_true (P : Nat → Sure CSet → Prop) (hP : ∀ o s, P o s) : ∀ (bd : List (Nat × Lazy CSet)), WalkPB P bd
  | [] => trivial
  | (ob, l) :: rest => ⟨walkP_true P hP ob l, walkPB_true P hP rest⟩
end

/-- **`+coerce-lazy` on every lazy need**, with an empty `soft`: the gate on
`[ned o laz less]` is `coerceLazyL ned less o laz`. -/
theorem comp_coerce_lazy_all (h7 : slot? 7 ctx = some compK) (x : GenRest) (hx : x.NoSoft) (ned : Need) (o : Nat)
    (laz : Lazy CSet) (less : Cape) (g : Gen (TreapMap mugF)) :
    nock (C czBody (C (C ned.toNoun (C (A o) (C laz.toNoun less.toNoun))) (compCore g x ctx))) czBody
      = (coerceLazyL ned less o laz g).map fun p => genNoun p.2 x := by
  have hw := walkP_true (fun o (_ : Sure CSet) => x.SoftOut o) (fun o _ => hx o)
  exact cz_all h7 x ned less laz o g (hw o laz)

end Compiler
end Formalization
