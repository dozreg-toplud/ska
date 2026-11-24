import lemmas.Compiler.CompSpinSplit
import lemmas.Compiler.CompSplit

/-!
# `+split` on every lazy need

The loop `split-loop` of `+split` (`comp.split.loop`, a trap on the subject

    [loop [laz [o [split-battery [nex [comp.door [gen ctx]]]]]]]

with `laz` at `6`, `o` at `14`, the door core at `63`, `gen` at `254`):

1. `=^  [sure-h sure-t]  gen  (split-sure sure.laz o)`;
2. `?:  &(?=(~ fork.laz) ?=(~ bond.laz))  [[[sure-h ~ ~] [sure-t ~ ~]] gen]`;
3. `=^  [fork-h fork-t]  gen  (spin-split fork.laz gen ..)` with the gate
   `spGF`: `=.  gen  gen-acc`, then the loop on the yes need at its block
   (`split-loop(laz laz.y, o o.y)`), then on the no need, and the two
   halves of the fork;
4. the same over the bonds with the gate `spGB`;
5. `[[(lazy-prune [sure-h fork-h bond-h]) (lazy-prune [sure-t fork-t
   bond-t])] gen]`.

The model `splitLoop` (with `splitForks`, `splitBonds`) of
`Ska/CompLazyArms.lean` does the same in the same order: the yes need
before the no need, the forks before the bonds, the state threaded through
in that order, both halves pruned.  No departure.

`csp_all`: the loop on every lazy need (forks and bonds to any depth) whose
sure needs look at no axis `0` (`WalkP lok0`); `comp_split_all`: `+split`
(the `+emit` of `[~ ~ %hop then]`, then the loop) on every `NextL`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

def spGF : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 2046) (C (A 0) (A 13))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (A 0) (A 48))) (C (A 10) (C (C (A 6) (C (A 0) (A 49))) (C (A 0) (A 15)))))))))) (C (A 7) (C (C (A 10) (C (C (A 4094) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (A 0) (A 114))) (C (A 10) (C (C (A 6) (C (A 0) (A 115))) (C (A 0) (A 31)))))))))) (C (A 7) (C (C (A 10) (C (C (A 8190) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (C (C (A 0) (A 240)) (C (A 0) (A 12))) (C (C (A 0) (A 242)) (C (A 0) (A 4)))) (C (C (C (A 0) (A 240)) (C (A 0) (A 13))) (C (C (A 0) (A 242)) (C (A 0) (A 5))))) (C (A 0) (A 8190)))))))))))))))))))))

def spGB : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 4094) (C (A 0) (A 13))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (A 0) (A 24))) (C (A 10) (C (C (A 6) (C (A 0) (A 25))) (C (A 0) (A 31)))))))))) (C (A 7) (C (C (A 10) (C (C (A 8190) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (C (A 0) (A 56)) (C (A 0) (A 4))) (C (C (A 0) (A 56)) (C (A 0) (A 5)))) (C (A 0) (A 8190)))))))))))))

def spLoopS : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x2aaf) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 0) (A 30)))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 58)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 59)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (C (C (C (A 0) (A 4)) (C (A 1) (C (A 0) (A 0)))) (C (C (A 0) (A 5)) (C (A 1) (C (A 0) (A 0))))) (C (A 0) (A 510))) (C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 372) (C (A 0) (A 2047)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 122)) (C (C (A 0) (A 1022)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (C (C (A 1) (A 0)) (C (A 7) (C (C (A 9) (C (A 191) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))) (C (C (A 1) (A 0)) (C (A 7) (C (C (A 9) (C (A 191) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))) (C (A 0) (A 510))) (C (C (A 1) spGF) (C (A 0) (A 1)))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 372) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 251)) (C (C (A 0) (A 2046)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (C (A 1) (A 0)) (C (A 7) (C (C (A 9) (C (A 191) (C (A 0) (A 8191)))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))) (C (A 0) (A 1022))) (C (C (A 1) spGB) (C (A 0) (A 1)))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 2046) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 8) (C (C (A 9) (C (A 0x15577c) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 60)) (C (C (A 0) (A 28)) (C (A 0) (A 12))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 9) (C (A 0x15577c) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 61)) (C (C (A 0) (A 29)) (C (A 0) (A 13))))) (C (A 0) (A 2))))))))) (C (A 0) (A 2046))))))))))))))))))))))))))))))))))))

theorem sp_loop_eq : comp.split.loop = spLoopS := by kernel_rfl

/-- The subject of `split-loop`. -/
def spTS (ctx : Noun) (L : Noun) (o : Nat) (B N G : Noun) : Noun :=
  C comp.split.loop (C L (C (A o) (C B (C N (C comp.door (C G ctx))))))

/-- No looked-at axis of a sure need is `0`. -/
def lok0 (_ : Nat) (s : Sure CSet) : Prop := ∀ y ∈ HoonSet.toList s.lok, y ≠ 0

/-- The noun of a result of the loop. -/
noncomputable def splitEnc (x : GenRest) (p : (Lazy CSet × Lazy CSet) × Gen (TreapMap mugF)) : Noun :=
  C (C p.1.1.toNoun p.1.2.toNoun) (genNoun p.2 x)

/-- The gate of the spin over the forks, in the model. -/
noncomputable def gForks (e : Lazy.ForkE CSet) (g : Gen (TreapMap mugF)) :
    Option (Lazy.ForkE CSet × Lazy.ForkE CSet × Gen (TreapMap mugF)) :=
  (Lazy.splitLoop e.1.2 e.1.1 g).bind fun r1 => (Lazy.splitLoop e.2.2 e.2.1 r1.2).map fun r2 =>
    (((e.1.1, r1.1.1), (e.2.1, r2.1.1)), ((e.1.1, r1.1.2), (e.2.1, r2.1.2)), r2.2)

/-- The gate of the spin over the bonds, in the model. -/
noncomputable def gBonds (e : Nat × Lazy CSet) (g : Gen (TreapMap mugF)) :
    Option ((Nat × Lazy CSet) × (Nat × Lazy CSet) × Gen (TreapMap mugF)) :=
  (Lazy.splitLoop e.2 e.1 g).map fun r => ((e.1, r.1.1), (e.1, r.1.2), r.2)

theorem splitForks_ssM : ∀ (fk : List (Lazy.ForkE CSet)) (g : Gen (TreapMap mugF)),
    Lazy.splitForks fk g = (ssM gForks fk g).map fun r => ((r.1, r.2.1), r.2.2)
  | [], g => rfl
  | ((oy, y), (on, n)) :: rest, g => by
    simp only [Lazy.splitForks, ssM, gForks]
    cases e1 : Lazy.splitLoop y oy g with
    | none => simp [e1, bind, StateT.bind]
    | some p =>
      obtain ⟨⟨yh, yt⟩, g1⟩ := p
      cases e2 : Lazy.splitLoop n on g1 with
      | none => simp [e1, e2, bind, StateT.bind]
      | some q =>
        obtain ⟨⟨nh, nt⟩, g2⟩ := q
        simp only [bind, StateT.bind, e1, e2, Option.bind_some, Option.map_some]
        rw [splitForks_ssM rest g2]
        cases ssM gForks rest g2 <;> simp [pure, StateT.pure]

theorem splitBonds_ssM : ∀ (bd : List (Nat × Lazy CSet)) (g : Gen (TreapMap mugF)),
    Lazy.splitBonds bd g = (ssM gBonds bd g).map fun r => ((r.1, r.2.1), r.2.2)
  | [], g => rfl
  | (ob, l) :: rest, g => by
    simp only [Lazy.splitBonds, ssM, gBonds]
    cases e1 : Lazy.splitLoop l ob g with
    | none => simp [e1, bind, StateT.bind]
    | some p =>
      obtain ⟨⟨lh, lt⟩, g1⟩ := p
      simp only [bind, StateT.bind, e1, Option.bind_some, Option.map_some]
      rw [splitBonds_ssM rest g1]
      cases ssM gBonds rest g1 <;> simp [pure, StateT.pure]

/-! ## The gates of the spins -/

section
variable (x : GenRest) (B N : Noun)

/-- The fork gate: `=.  gen  gen-acc`, the loop on the yes need at its
block, then on the no need, whatever loop subject it was made in. -/
theorem sp_fgate (SHT L' G' : Noun) (o' : Nat) (e : Lazy.ForkE CSet) (g : Gen (TreapMap mugF))
    (ihy : ∀ g, nock (spTS ctx e.1.2.toNoun e.1.1 B N (genNoun g x)) comp.split.loop
      = (Lazy.splitLoop e.1.2 e.1.1 g).map (splitEnc x))
    (ihn : ∀ g, nock (spTS ctx e.2.2.toNoun e.2.1 B N (genNoun g x)) comp.split.loop
      = (Lazy.splitLoop e.2.2 e.2.1 g).map (splitEnc x)) :
    nock (C spGF (C (C (forkE e) (genNoun g x)) (C SHT (spTS ctx L' o' B N G')))) spGF
      = (gForks e g).map fun r => C (C (forkE r.1) (forkE r.2.1)) (genNoun r.2.2 x) := by
  obtain ⟨⟨oy, y⟩, ⟨on, n⟩⟩ := e
  have hy := ihy g
  simp only [spTS] at hy ihn
  unfold spGF spTS
  cases e1 : Lazy.splitLoop y oy g with
  | none =>
    rw [e1] at hy
    simp [nock_exec, forkE, hy, gForks, e1]
  | some p =>
    obtain ⟨⟨yh, yt⟩, g1⟩ := p
    rw [e1] at hy
    have hn := ihn g1
    cases e2 : Lazy.splitLoop n on g1 with
    | none =>
      rw [e2] at hn
      simp [nock_exec, forkE, hy, hn, gForks, e1, e2, splitEnc]
    | some q =>
      obtain ⟨⟨nh, nt⟩, g2⟩ := q
      rw [e2] at hn
      simp [nock_exec, forkE, hy, hn, gForks, e1, e2, splitEnc]

/-- The bond gate: `=.  gen  gen-acc`, then the loop on the bond's need at
its block. -/
theorem sp_bgate (FHT SHT L' G' : Noun) (o' : Nat) (e : Nat × Lazy CSet) (g : Gen (TreapMap mugF))
    (ih : ∀ g, nock (spTS ctx e.2.toNoun e.1 B N (genNoun g x)) comp.split.loop
      = (Lazy.splitLoop e.2 e.1 g).map (splitEnc x)) :
    nock (C spGB (C (C (bondE e) (genNoun g x)) (C FHT (C SHT (spTS ctx L' o' B N G'))))) spGB
      = (gBonds e g).map fun r => C (C (bondE r.1) (bondE r.2.1)) (genNoun r.2.2 x) := by
  obtain ⟨ob, l⟩ := e
  have hl := ih g
  simp only [spTS] at hl
  unfold spGB spTS
  cases e1 : Lazy.splitLoop l ob g with
  | none =>
    rw [e1] at hl
    simp [nock_exec, bondE, hl, gBonds, e1]
  | some p =>
    obtain ⟨⟨lh, lt⟩, g1⟩ := p
    rw [e1] at hl
    simp [nock_exec, bondE, hl, gBonds, e1, splitEnc]

end

/-- `+split-sure` is door arm `6831`. -/
theorem comp_ss_at : slot? 6831 comp.door = some comp.split_sure.arm := by kernel_rfl

/-- The test `=(~ l)` of a list of entries, both forms `simp` meets. -/
theorem lz_test {α : Type} (E : α → Noun) (l : List α) :
    (l = [] ∧ eqCode (A 0) (listN (l.map E)) = A 0 ∧ (A 0 = listN (l.map E)) = True) ∨
    (l ≠ [] ∧ eqCode (A 0) (listN (l.map E)) = A 1 ∧ (A 0 = listN (l.map E)) = False) := by
  cases l with
  | nil => left; simp [listN, eqCode]
  | cons a t => right; simp [listN, eqCode]

/-- The arm `+lazy-prune` builds its gate. -/
theorem comp_lp_arm (d : Noun) : nock d lpArm = some (C lpBat (C lzBunt d)) := by
  unfold lpArm; simp only [nock_exec]

/-- `+lazy-prune` on the noun of a lazy need written out. -/
theorem lp_mk (hc : CompIn ctx) (s : Sure CSet) (fk : List (Lazy.ForkE CSet)) (bd : List (Nat × Lazy CSet))
    (G : Noun) :
    nock (C lpBat (C (C s.toNoun (C (listN (fk.map forkE)) (listN (bd.map bondE)))) (C comp.door (C G ctx))))
      lpBat = some (Lazy.lazyPrune (Lazy.mk s fk bd)).toNoun := by
  rw [← lazy_toNoun_mk]; exact comp_lazy_prune hc _ G

/-! ## The loop -/

section
variable (h7 : slot? 7 ctx = some compK) (x : GenRest) (B N : Noun)
include h7

mutual
theorem csp_all : ∀ (laz : Lazy CSet) (o : Nat) (g : Gen (TreapMap mugF)), WalkP lok0 o laz →
    nock (spTS ctx laz.toNoun o B N (genNoun g x)) comp.split.loop = (Lazy.splitLoop laz o g).map (splitEnc x)
  | Lazy.mk s fk bd, o, g, ⟨hs, hfk, hbd⟩ => by
    obtain ⟨hc, hl, hm⟩ := comp_ctx_pill ctx h7
    have hss := comp_split_sure (x := x) hc g s o hs
    obtain ⟨⟨Q, a, M, m, v, hQ, ha, hM, hmm, hv⟩, -⟩ := hm
    rw [lazy_toNoun_mk]
    unfold spTS
    conv => { lhs; arg 2; rw [sp_loop_eq]; unfold spLoopS }
    cases e1 : splitSure s o g with
    | none =>
      rw [e1] at hss
      simp [nock_exec, comp_split_sure_arm, hss, Lazy.splitLoop, e1, bind, StateT.bind]
    | some p =>
      obtain ⟨⟨sh, st⟩, g1⟩ := p
      rw [e1] at hss
      by_cases hfb : fk = [] ∧ bd = []
      · obtain ⟨rfl, rfl⟩ := hfb
        simp [nock_exec, comp_split_sure_arm, hss, Lazy.splitLoop, e1, bind, StateT.bind, listN, splitEnc,
          pure, StateT.pure, Lazy.ofSure, lazy_toNoun_mk]
      · have hlp := comp_lp_at
        have hF := spsp_gate forkE forkE (fun g => genNoun g x) spGF
          (C (C (C (A 0) v) (C (A 0) v)) (genNoun g1 x))
          (C (C sh.toNoun st.toNoun) (C comp.split.loop (C (C s.toNoun (C (listN (fk.map forkE))
            (listN (bd.map bondE)))) (C (A o) (C B (C N (C comp.door (C (genNoun g1 x) ctx))))))))
          gForks fk g1 (fun e he g' => csp_forks fk hfk e he g' _ _ _ _)
        have hfb' : ¬ (fk.isEmpty = true ∧ bd.isEmpty = true) := by simpa [List.isEmpty_iff] using hfb
        have tF := lz_test forkE fk
        have tB := lz_test bondE bd
        have tt : (fk = [] ∧ eqCode (A 0) (listN (fk.map forkE)) = A 0 ∧ (A 0 = listN (fk.map forkE)) = True ∧
            bd ≠ [] ∧ eqCode (A 0) (listN (bd.map bondE)) = A 1 ∧ (A 0 = listN (bd.map bondE)) = False) ∨
            (fk ≠ [] ∧ eqCode (A 0) (listN (fk.map forkE)) = A 1 ∧ (A 0 = listN (fk.map forkE)) = False ∧
              True ∧ True ∧ True) := by
          rcases tF with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
          · rcases tB with ⟨h4, h5, h6⟩ | ⟨h4, h5, h6⟩
            · exact absurd ⟨h1, h4⟩ hfb
            · exact Or.inl ⟨h1, h2, h3, h4, h5, h6⟩
          · exact Or.inr ⟨h1, h2, h3, trivial, trivial, trivial⟩
        obtain ⟨t1, t2, t3, t4, t5, t6⟩ | ⟨t1, t2, t3, t4, t5, t6⟩ := tt <;>
        cases eF : ssM gForks fk g1 with
        | none =>
          rw [eF] at hF
          simp [nock_exec, comp_split_sure_arm, hss, Lazy.splitLoop, e1, bind, StateT.bind, h7, compK_ss,
            ss_arm, ss_gate_eq, hQ, ha, hM, hmm, hv, hF, splitForks_ssM, eF, hfb, hfb', t2, t3, t5, t6]
        | some rF =>
          obtain ⟨fh, ft, g2⟩ := rF
          rw [eF] at hF
          have hB := spsp_gate bondE bondE (fun g => genNoun g x) spGB
            (C (C (A 0) v) (genNoun g2 x))
            (C (C (listN (fh.map forkE)) (listN (ft.map forkE))) (C (C sh.toNoun st.toNoun) (C comp.split.loop
              (C (C s.toNoun (C (listN (fk.map forkE)) (listN (bd.map bondE)))) (C (A o) (C B (C N
                (C comp.door (C (genNoun g2 x) ctx)))))))))
            gBonds bd g2 (fun e he g' => csp_bonds bd hbd e he g' _ _ _ _ _)
          cases eB : ssM gBonds bd g2 with
          | none =>
            rw [eB] at hB
            simp [nock_exec, comp_split_sure_arm, hss, Lazy.splitLoop, e1, bind, StateT.bind, h7, compK_ss,
              ss_arm, ss_gate_eq, hQ, ha, hM, hmm, hv, hF, splitForks_ssM, eF, hfb, hfb', t2, t3, t5, t6,
              hB, splitBonds_ssM, eB]
          | some rB =>
            obtain ⟨bh, bt, g3⟩ := rB
            rw [eB] at hB
            have hp1 := lp_mk hc sh fh bh (genNoun g3 x)
            have hp2 := lp_mk hc st ft bt (genNoun g3 x)
            have hssa := comp_ss_at
            simp only [compCore] at hss
            generalize comp.door = Dr at hlp hp1 hp2 hF hB hss hssa ⊢
            simp [nock_exec, comp_split_sure_arm, hss, Lazy.splitLoop, e1, bind, StateT.bind, h7, compK_ss,
              ss_arm, ss_gate_eq, hQ, ha, hM, hmm, hv, hF, splitForks_ssM, eF, hfb, hfb', t2, t3, t5, t6,
              hB, splitBonds_ssM, eB, hlp, comp_lp_arm, hp1, hp2, splitEnc, pure, StateT.pure, hssa]

theorem csp_forks : ∀ (fk : List (Lazy.ForkE CSet)), WalkPF lok0 fk → ∀ e ∈ fk,
    ∀ (g : Gen (TreapMap mugF)) (SHT L' G' : Noun) (o' : Nat),
    nock (C spGF (C (C (forkE e) (genNoun g x)) (C SHT (spTS ctx L' o' B N G')))) spGF
      = (gForks e g).map fun r => C (C (forkE r.1) (forkE r.2.1)) (genNoun r.2.2 x)
  | [], _, e, he => absurd he List.not_mem_nil
  | ((oy, y), (on, n)) :: rest, ⟨hy, hn, hr⟩, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro g SHT L' G' o'
      exact sp_fgate x B N SHT L' G' o' _ g (fun g => csp_all y oy g hy) (fun g => csp_all n on g hn)
    · exact csp_forks rest hr e he'

theorem csp_bonds : ∀ (bd : List (Nat × Lazy CSet)), WalkPB lok0 bd → ∀ e ∈ bd,
    ∀ (g : Gen (TreapMap mugF)) (FHT SHT L' G' : Noun) (o' : Nat),
    nock (C spGB (C (C (bondE e) (genNoun g x)) (C FHT (C SHT (spTS ctx L' o' B N G'))))) spGB
      = (gBonds e g).map fun r => C (C (bondE r.1) (bondE r.2.1)) (genNoun r.2.2 x)
  | [], _, e, he => absurd he List.not_mem_nil
  | (ob, l) :: rest, ⟨hl, hr⟩, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro g FHT SHT L' G' o'
      exact sp_bgate x B N FHT SHT L' G' o' _ g (fun g => csp_all l ob g hl)
    · exact csp_bonds rest hr e he'
end

end

theorem walkP_lok0 (o o' : Nat) (laz : Lazy CSet) : WalkP lok0 o laz = WalkP lok0 o' laz := by
  cases laz; rfl

/-- **`+split` on every `next`** whose lazy need (forks and bonds to any
depth) looks at no axis `0`: `+emit` of `[~ ~ %hop then.nex]`, then the
loop at the new block; it returns `[hed tel o]`.  In the pill's context
(`K` at axis `7`). -/
theorem comp_split_all (h7 : slot? 7 ctx = some compK) (x : GenRest) (g : Gen (TreapMap mugF))
    (nex : NextL CSet) (h0 : WalkP lok0 0 nex.laz) :
    nock (C comp.split.battery (C nex.goal.toNoun (compCore g x ctx))) comp.split.battery
      = (splitL nex g).map fun p => C (C p.1.1.toNoun (C p.1.2.1.toNoun (A p.1.2.2))) (genNoun p.2 x) := by
  obtain ⟨laz, th⟩ := nex
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  have he := comp_emit x hc g ⟨[], [], Termin.hop th⟩
  simp only [Blob.toNoun, listNoun, Termin.toNoun, Tag.hop] at he
  rw [cd_emit_eq] at he
  generalize hg1 : (if g.drop = true then { g with bo := g.bo + 1 }
      else { g with bo := g.bo + 1, blocks := HoonMap.put g.blocks g.bo ⟨[], [], Termin.hop th⟩ })
      = g1 at he
  have hl := csp_all h7 x comp.split.battery (C (A 0x7478656e) (C laz.toNoun th.toNoun)) laz g.bo g1
    (by rw [walkP_lok0 g.bo 0]; exact h0)
  simp only [spTS] at hl
  simp only [NextL.goal, CGoalL.toNoun]
  nock_open comp.split.battery
  cases e : Lazy.splitLoop laz g.bo g1 with
  | none =>
    rw [e] at hl
    simp [nock_exec, comp_emit_arm, he, hl, splitL, cd_emit_eq, hg1, bind, StateT.bind, e]
  | some p =>
    obtain ⟨⟨sh, st⟩, g2⟩ := p
    rw [e] at hl
    simp [nock_exec, comp_emit_arm, he, hl, splitL, cd_emit_eq, hg1, bind, StateT.bind, e, pure,
      StateT.pure, splitEnc]

end Compiler
end Formalization
