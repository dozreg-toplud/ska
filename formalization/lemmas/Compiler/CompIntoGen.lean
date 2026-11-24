import lemmas.Compiler.CompSplitGen
import lemmas.Compiler.CompInto

/-!
# `+into` on every lazy need

The loop of `+into` (`intL0` of `CompInto.lean`, a trap on the subject

    [loop [laz [o [into-battery [[nex axe] [comp.door [gen ctx]]]]]]]

with `laz` at `6`, `o` at `14`, `axe` at `125`, the door core at `63`,
`gen` at `254`) has the shape of the loop of `+split` (`CompSplitGen.lean`):
`+into-sure` of `axe` on the sure need into block `o` (the donor's half
first), the test `&(?=(~ fork.laz) ?=(~ bond.laz))`, then `+spin-split`
over the forks with the gate `itGF` (the loop on the yes need at its block,
then on the no need), over the bonds with `itGB`, and `+lazy-prune` of both
halves.  The model `intoLoopL axe` (with `intoForks`, `intoBonds`) of
`Ska/CompLazyArms.lean` does the same in the same order.  No departure.

`cit_all`: the loop on every lazy need (forks and bonds to any depth) whose
sure needs look at no axis `0`, for `axe` not `0`; `comp_into_all`: `+into`
on every `NextL`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

def itGF : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C (C (A 10) (C (C (A 2046) (C (A 0) (A 13))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (A 0) (A 48))) (C (A 10) (C (C (A 6) (C (A 0) (A 49))) (C (A 0) (A 15)))))))))) (C (A 7) (C (C (A 10) (C (C (A 4094) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (A 0) (A 114))) (C (A 10) (C (C (A 6) (C (A 0) (A 115))) (C (A 0) (A 31)))))))))) (C (A 7) (C (C (A 10) (C (C (A 8190) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (C (C (A 0) (A 240)) (C (A 0) (A 12))) (C (C (A 0) (A 242)) (C (A 0) (A 4)))) (C (C (C (A 0) (A 240)) (C (A 0) (A 13))) (C (C (A 0) (A 242)) (C (A 0) (A 5))))) (C (A 0) (A 8190)))))))))))))))))))))))

def itGB : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 4094) (C (A 0) (A 13))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (A 0) (A 24))) (C (A 10) (C (C (A 6) (C (A 0) (A 25))) (C (A 0) (A 31)))))))))) (C (A 7) (C (C (A 10) (C (C (A 8190) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (C (A 0) (A 56)) (C (A 0) (A 4))) (C (C (A 0) (A 56)) (C (A 0) (A 5)))) (C (A 0) (A 8190)))))))))))))

def itLoopS : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x2afffe) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 253)) (C (C (A 0) (A 28)) (C (A 0) (A 30))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 58)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 59)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (C (C (C (A 0) (A 4)) (C (A 1) (C (A 0) (A 0)))) (C (C (A 0) (A 5)) (C (A 1) (C (A 0) (A 0))))) (C (A 0) (A 510))) (C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 372) (C (A 0) (A 2047)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 122)) (C (C (A 0) (A 1022)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (C (C (A 1) (A 0)) (C (A 7) (C (C (A 9) (C (A 191) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))) (C (C (A 1) (A 0)) (C (A 7) (C (C (A 9) (C (A 191) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))) (C (A 0) (A 510))) (C (C (A 1) itGF) (C (A 0) (A 1)))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 372) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 251)) (C (C (A 0) (A 2046)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (C (A 1) (A 0)) (C (A 7) (C (C (A 9) (C (A 191) (C (A 0) (A 8191)))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))) (C (A 0) (A 1022))) (C (C (A 1) itGB) (C (A 0) (A 1)))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 2046) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 8) (C (C (A 9) (C (A 0x15577c) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 60)) (C (C (A 0) (A 28)) (C (A 0) (A 12))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 9) (C (A 0x15577c) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 61)) (C (C (A 0) (A 29)) (C (A 0) (A 13))))) (C (A 0) (A 2))))))))) (C (A 0) (A 2046))))))))))))))))))))))))))))))))))))

theorem it_loop_eq : intL0 = itLoopS := by kernel_rfl

/-- The subject of the loop of `+into`. -/
def itTS (ctx : Noun) (L : Noun) (o : Nat) (B N : Noun) (axe : Nat) (G : Noun) : Noun :=
  C intL0 (C L (C (A o) (C B (C (C N (A axe)) (C comp.door (C G ctx))))))

/-- The gate of the spin over the forks, in the model. -/
noncomputable def giForks (axe : Nat) (e : Lazy.ForkE CSet) (g : Gen (TreapMap mugF)) :
    Option (Lazy.ForkE CSet × Lazy.ForkE CSet × Gen (TreapMap mugF)) :=
  (Lazy.intoLoopL axe e.1.2 e.1.1 g).bind fun r1 => (Lazy.intoLoopL axe e.2.2 e.2.1 r1.2).map fun r2 =>
    (((e.1.1, r1.1.1), (e.2.1, r2.1.1)), ((e.1.1, r1.1.2), (e.2.1, r2.1.2)), r2.2)

/-- The gate of the spin over the bonds, in the model. -/
noncomputable def giBonds (axe : Nat) (e : Nat × Lazy CSet) (g : Gen (TreapMap mugF)) :
    Option ((Nat × Lazy CSet) × (Nat × Lazy CSet) × Gen (TreapMap mugF)) :=
  (Lazy.intoLoopL axe e.2 e.1 g).map fun r => ((e.1, r.1.1), (e.1, r.1.2), r.2)

theorem intoForks_ssM (axe : Nat) : ∀ (fk : List (Lazy.ForkE CSet)) (g : Gen (TreapMap mugF)),
    Lazy.intoForks axe fk g = (ssM (giForks axe) fk g).map fun r => ((r.1, r.2.1), r.2.2)
  | [], g => rfl
  | ((oy, y), (on, n)) :: rest, g => by
    simp only [Lazy.intoForks, ssM, giForks]
    cases e1 : Lazy.intoLoopL axe y oy g with
    | none => simp [e1, bind, StateT.bind]
    | some p =>
      obtain ⟨⟨yh, yt⟩, g1⟩ := p
      cases e2 : Lazy.intoLoopL axe n on g1 with
      | none => simp [e1, e2, bind, StateT.bind]
      | some q =>
        obtain ⟨⟨nh, nt⟩, g2⟩ := q
        simp only [bind, StateT.bind, e1, e2, Option.bind_some, Option.map_some]
        rw [intoForks_ssM axe rest g2]
        cases ssM (giForks axe) rest g2 <;> simp [pure, StateT.pure]

theorem intoBonds_ssM (axe : Nat) : ∀ (bd : List (Nat × Lazy CSet)) (g : Gen (TreapMap mugF)),
    Lazy.intoBonds axe bd g = (ssM (giBonds axe) bd g).map fun r => ((r.1, r.2.1), r.2.2)
  | [], g => rfl
  | (ob, l) :: rest, g => by
    simp only [Lazy.intoBonds, ssM, giBonds]
    cases e1 : Lazy.intoLoopL axe l ob g with
    | none => simp [e1, bind, StateT.bind]
    | some p =>
      obtain ⟨⟨lh, lt⟩, g1⟩ := p
      simp only [bind, StateT.bind, e1, Option.bind_some, Option.map_some]
      rw [intoBonds_ssM axe rest g1]
      cases ssM (giBonds axe) rest g1 <;> simp [pure, StateT.pure]

/-! ## The gates of the spins -/

section
variable (x : GenRest) (B N : Noun) (axe : Nat)

theorem it_fgate (SHT L' G' : Noun) (o' : Nat) (e : Lazy.ForkE CSet) (g : Gen (TreapMap mugF))
    (ihy : ∀ g, nock (itTS ctx e.1.2.toNoun e.1.1 B N axe (genNoun g x)) intL0
      = (Lazy.intoLoopL axe e.1.2 e.1.1 g).map (splitEnc x))
    (ihn : ∀ g, nock (itTS ctx e.2.2.toNoun e.2.1 B N axe (genNoun g x)) intL0
      = (Lazy.intoLoopL axe e.2.2 e.2.1 g).map (splitEnc x)) :
    nock (C itGF (C (C (forkE e) (genNoun g x)) (C SHT (itTS ctx L' o' B N axe G')))) itGF
      = (giForks axe e g).map fun r => C (C (forkE r.1) (forkE r.2.1)) (genNoun r.2.2 x) := by
  obtain ⟨⟨oy, y⟩, ⟨on, n⟩⟩ := e
  have hy := ihy g
  simp only [itTS] at hy ihn
  unfold itGF itTS
  cases e1 : Lazy.intoLoopL axe y oy g with
  | none =>
    rw [e1] at hy
    simp [nock_exec, forkE, hy, giForks, e1]
  | some p =>
    obtain ⟨⟨yh, yt⟩, g1⟩ := p
    rw [e1] at hy
    have hn := ihn g1
    cases e2 : Lazy.intoLoopL axe n on g1 with
    | none =>
      rw [e2] at hn
      simp [nock_exec, forkE, hy, hn, giForks, e1, e2, splitEnc]
    | some q =>
      obtain ⟨⟨nh, nt⟩, g2⟩ := q
      rw [e2] at hn
      simp [nock_exec, forkE, hy, hn, giForks, e1, e2, splitEnc]

theorem it_bgate (FHT SHT L' G' : Noun) (o' : Nat) (e : Nat × Lazy CSet) (g : Gen (TreapMap mugF))
    (ih : ∀ g, nock (itTS ctx e.2.toNoun e.1 B N axe (genNoun g x)) intL0
      = (Lazy.intoLoopL axe e.2 e.1 g).map (splitEnc x)) :
    nock (C itGB (C (C (bondE e) (genNoun g x)) (C FHT (C SHT (itTS ctx L' o' B N axe G'))))) itGB
      = (giBonds axe e g).map fun r => C (C (bondE r.1) (bondE r.2.1)) (genNoun r.2.2 x) := by
  obtain ⟨ob, l⟩ := e
  have hl := ih g
  simp only [itTS] at hl
  unfold itGB itTS
  cases e1 : Lazy.intoLoopL axe l ob g with
  | none =>
    rw [e1] at hl
    simp [nock_exec, bondE, hl, giBonds, e1]
  | some p =>
    obtain ⟨⟨lh, lt⟩, g1⟩ := p
    rw [e1] at hl
    simp [nock_exec, bondE, hl, giBonds, e1, splitEnc]

end

/-! ## The loop -/

section
variable (h7 : slot? 7 ctx = some compK) (x : GenRest) (B N : Noun) (axe : Nat) (ha : axe ≠ 0)
include h7 ha

mutual
theorem cit_all : ∀ (laz : Lazy CSet) (o : Nat) (g : Gen (TreapMap mugF)), WalkP lok0 o laz →
    nock (itTS ctx laz.toNoun o B N axe (genNoun g x)) intL0 = (Lazy.intoLoopL axe laz o g).map (splitEnc x)
  | Lazy.mk s fk bd, o, g, ⟨hs, hfk, hbd⟩ => by
    obtain ⟨hc, hl, hm⟩ := comp_ctx_pill ctx h7
    have hss := comp_into_sure (x := x) hc hl g axe s o ha hs
    obtain ⟨⟨Q, a, M, m, v, hQ, ha', hM, hmm, hv⟩, -⟩ := hm
    have hisa := comp_is_at
    rw [lazy_toNoun_mk]
    unfold itTS
    conv => { lhs; arg 2; rw [it_loop_eq]; unfold itLoopS }
    simp only [compCore] at hss
    cases e1 : intoSure axe s o g with
    | none =>
      rw [e1] at hss
      generalize comp.door = Dr at hss hisa ⊢
      simp [nock_exec, comp_is_arm, hss, Lazy.intoLoopL, e1, bind, StateT.bind, hisa]
    | some p =>
      obtain ⟨⟨sh, st⟩, g1⟩ := p
      rw [e1] at hss
      by_cases hfb : fk = [] ∧ bd = []
      · obtain ⟨rfl, rfl⟩ := hfb
        generalize comp.door = Dr at hss hisa ⊢
        simp [nock_exec, comp_is_arm, hss, Lazy.intoLoopL, e1, bind, StateT.bind, listN, splitEnc,
          pure, StateT.pure, Lazy.ofSure, lazy_toNoun_mk, hisa]
      · have hlp := comp_lp_at
        have hF := spsp_gate forkE forkE (fun g => genNoun g x) itGF
          (C (C (C (A 0) v) (C (A 0) v)) (genNoun g1 x))
          (C (C sh.toNoun st.toNoun) (C intL0 (C (C s.toNoun (C (listN (fk.map forkE))
            (listN (bd.map bondE)))) (C (A o) (C B (C (C N (A axe)) (C comp.door (C (genNoun g1 x) ctx))))))))
          (giForks axe) fk g1 (fun e he g' => cit_forks fk hfk e he g' _ _ _ _)
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
        cases eF : ssM (giForks axe) fk g1 with
        | none =>
          rw [eF] at hF
          generalize comp.door = Dr at hF hss hisa ⊢
          simp [nock_exec, comp_is_arm, hss, Lazy.intoLoopL, e1, bind, StateT.bind, h7, compK_ss,
            ss_arm, ss_gate_eq, hQ, ha', hM, hmm, hv, hF, intoForks_ssM, eF, hfb, hfb', t2, t3, t5, t6, hisa]
        | some rF =>
          obtain ⟨fh, ft, g2⟩ := rF
          rw [eF] at hF
          have hB := spsp_gate bondE bondE (fun g => genNoun g x) itGB
            (C (C (A 0) v) (genNoun g2 x))
            (C (C (listN (fh.map forkE)) (listN (ft.map forkE))) (C (C sh.toNoun st.toNoun) (C intL0
              (C (C s.toNoun (C (listN (fk.map forkE)) (listN (bd.map bondE)))) (C (A o) (C B (C (C N (A axe))
                (C comp.door (C (genNoun g2 x) ctx)))))))))
            (giBonds axe) bd g2 (fun e he g' => cit_bonds bd hbd e he g' _ _ _ _ _)
          cases eB : ssM (giBonds axe) bd g2 with
          | none =>
            rw [eB] at hB
            generalize comp.door = Dr at hF hB hss hisa ⊢
            simp [nock_exec, comp_is_arm, hss, Lazy.intoLoopL, e1, bind, StateT.bind, h7, compK_ss,
              ss_arm, ss_gate_eq, hQ, ha', hM, hmm, hv, hF, intoForks_ssM, eF, hfb, hfb', t2, t3, t5, t6,
              hB, intoBonds_ssM, eB, hisa]
          | some rB =>
            obtain ⟨bh, bt, g3⟩ := rB
            rw [eB] at hB
            have hp1 := lp_mk hc sh fh bh (genNoun g3 x)
            have hp2 := lp_mk hc st ft bt (genNoun g3 x)
            generalize comp.door = Dr at hlp hp1 hp2 hF hB hss hisa ⊢
            simp [nock_exec, comp_is_arm, hss, Lazy.intoLoopL, e1, bind, StateT.bind, h7, compK_ss,
              ss_arm, ss_gate_eq, hQ, ha', hM, hmm, hv, hF, intoForks_ssM, eF, hfb, hfb', t2, t3, t5, t6,
              hB, intoBonds_ssM, eB, hlp, comp_lp_arm, hp1, hp2, splitEnc, pure, StateT.pure, hisa]

theorem cit_forks : ∀ (fk : List (Lazy.ForkE CSet)), WalkPF lok0 fk → ∀ e ∈ fk,
    ∀ (g : Gen (TreapMap mugF)) (SHT L' G' : Noun) (o' : Nat),
    nock (C itGF (C (C (forkE e) (genNoun g x)) (C SHT (itTS ctx L' o' B N axe G')))) itGF
      = (giForks axe e g).map fun r => C (C (forkE r.1) (forkE r.2.1)) (genNoun r.2.2 x)
  | [], _, e, he => absurd he List.not_mem_nil
  | ((oy, y), (on, n)) :: rest, ⟨hy, hn, hr⟩, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro g SHT L' G' o'
      exact it_fgate x B N axe SHT L' G' o' _ g (fun g => cit_all y oy g hy) (fun g => cit_all n on g hn)
    · exact cit_forks rest hr e he'

theorem cit_bonds : ∀ (bd : List (Nat × Lazy CSet)), WalkPB lok0 bd → ∀ e ∈ bd,
    ∀ (g : Gen (TreapMap mugF)) (FHT SHT L' G' : Noun) (o' : Nat),
    nock (C itGB (C (C (bondE e) (genNoun g x)) (C FHT (C SHT (itTS ctx L' o' B N axe G'))))) itGB
      = (giBonds axe e g).map fun r => C (C (bondE r.1) (bondE r.2.1)) (genNoun r.2.2 x)
  | [], _, e, he => absurd he List.not_mem_nil
  | (ob, l) :: rest, ⟨hl, hr⟩, e, he => by
    rcases List.mem_cons.1 he with rfl | he'
    · intro g FHT SHT L' G' o'
      exact it_bgate x B N axe FHT SHT L' G' o' _ g (fun g => cit_all l ob g hl)
    · exact cit_bonds rest hr e he'
end

end

/-- **`+into` on every `next`** whose lazy need (forks and bonds to any
depth) looks at no axis `0`, for an axis `axe` not `0`: `+emit` of `[~ ~
%hop then.nex]`, then the loop at the new block; it returns `[don rec o]`.
In the pill's context (`K` at axis `7`). -/
theorem comp_into_all (h7 : slot? 7 ctx = some compK) (x : GenRest) (g : Gen (TreapMap mugF))
    (nex : NextL CSet) (axe : Nat) (ha : axe ≠ 0) (h0 : WalkP lok0 0 nex.laz) :
    nock (C intBat (C (C nex.goal.toNoun (A axe)) (compCore g x ctx))) intBat
      = (intoL nex axe g).map fun p => C (C p.1.1.toNoun (C p.1.2.1.toNoun (A p.1.2.2))) (genNoun p.2 x) := by
  obtain ⟨laz, th⟩ := nex
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  have he := comp_emit x hc g ⟨[], [], Termin.hop th⟩
  simp only [Blob.toNoun, listNoun, Termin.toNoun, Tag.hop] at he
  rw [cd_emit_eq] at he
  generalize hg1 : (if g.drop = true then { g with bo := g.bo + 1 }
      else { g with bo := g.bo + 1, blocks := HoonMap.put g.blocks g.bo ⟨[], [], Termin.hop th⟩ })
      = g1 at he
  have hlp := cit_all h7 x intBat (C (A 0x7478656e) (C laz.toNoun th.toNoun)) axe ha laz g.bo g1
    (by rw [walkP_lok0 g.bo 0]; exact h0)
  simp only [itTS] at hlp
  simp only [NextL.goal, CGoalL.toNoun]
  nock_open intBat
  cases e : Lazy.intoLoopL axe laz g.bo g1 with
  | none =>
    simp only [e] at hlp
    simp [nock_exec, comp_emit_arm, he, hlp, intoL, cd_emit_eq, hg1, bind, StateT.bind, e]
  | some p =>
    obtain ⟨⟨sd, sr⟩, g2⟩ := p
    simp only [e] at hlp
    simp [nock_exec, comp_emit_arm, he, hlp, intoL, cd_emit_eq, hg1, bind, StateT.bind, e, pure,
      StateT.pure, splitEnc]

end Compiler
end Formalization
