import lemmas.Compiler.CompForkGateN
import lemmas.Compiler.CompSplitGen

/-!
# The trap of `+fork` on every lazy need

The trap `fork-loop` of `+fork` (`fkLoop`, on the subject `fkTS`) is

1. `=^  [sure-0 sure-1]  gen  (fork-sure sure.laz o o-0 o-1)`;
2. `=^  [fork-0 fork-1]  gen  (spin-split fork.laz gen ..)` with the gate
   `fkGF`: `=.  gen  gen-acc`, six `+oo` (the kids `o-0-kid-y`,
   `o-1-kid-y`, `o-0-kid-n`, `o-1-kid-n`, `o-insert2-y`, `o-insert2-n`),
   `+copy-tag` of `o.y` then of `o.n` to their kids, the trap on the yes
   need (`laz.y`, at `o-insert2-y`, kids `o-0-kid-y` and `o-1-kid-y`), then
   on the no need, `+proxy` of `r-cond` in `o.y` then in `o.n`, `+emit` of
   the two `%brz` blocks, `+insert-hop` at `o.y` then at `o.n`, and the
   two halves;
3. the same over the bonds with the gate `fkGB` (three `+oo`, `+copy-tag`,
   the trap, `+proxy`, `+emit`, `+insert-hop`);
4. `[[sure-0 fork-0 bond-0] [sure-1 fork-1 bond-1]]`, with no
   `+lazy-prune`.

The model `forkLoop`, `forkForks`, `forkBonds` of `Ska/CompLazyRun.lean`
does the same in the same order (the steps `fkStepF`, `fkStepB` of
`CompForkGen.lean`).  No departure.

`fk_fgate`, `fk_bgate`: the gates against the steps, given the trap on the
inner needs; `cfk_all` (with `cfk_forks`, `cfk_bonds`): the trap on every
lazy need (forks and bonds to any depth), by a mutual induction, in the
pill's context.  `comp_fork_all`: `+fork` is `forkL` on every `next`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-- `+copy-tag` is door arm `0x1afffc` (core axis `0x2afffc`). -/
theorem comp_ct_at : slot? 0x1afffc comp.door = some comp.copy_tag.arm := by kernel_rfl

theorem comp_ct_arm (d : Noun) : nock d comp.copy_tag.arm = some (C comp.copy_tag.battery (C (C (A 0) (A 0)) d)) := by
  unfold comp.copy_tag.arm; simp only [nock_exec]

theorem comp_ih_arm (d : Noun) : nock d ihArm = some (C ihBat (C (C (A 0) (C (A 0) (A 0))) d)) := by
  unfold ihArm; simp only [nock_exec]

/-- The gate of the spin over the forks, in the model. -/
def gFkF (rc : Nat) (e : Lazy.ForkE CSet) (g : Gen (TreapMap mugF)) :
    Option (Lazy.ForkE CSet × Lazy.ForkE CSet × Gen (TreapMap mugF)) :=
  (fkStepF rc e g).map fun p => (p.1.1, p.1.2, p.2)

/-- The gate of the spin over the bonds, in the model. -/
def gFkB (rc : Nat) (e : Nat × Lazy CSet) (g : Gen (TreapMap mugF)) :
    Option ((Nat × Lazy CSet) × (Nat × Lazy CSet) × Gen (TreapMap mugF)) :=
  (fkStepB rc e g).map fun p => (p.1.1, p.1.2, p.2)

/-- The trap on a lazy need, for every block, kids and state. -/
def FkIH (x : GenRest) (N : Noun) (rc : Nat) (laz : Lazy CSet) : Prop :=
  ∀ (o o0 o1 : Nat) (g : Gen (TreapMap mugF)),
    nock (fkTS o laz.toNoun o1 o0 (C N (A rc)) (compCore g x ctx)) fkLoop
      = (forkLoop rc laz o o0 o1 g).map (splitEnc x)

/-- The simp set of the gates: the Nock, the calls, the model's steps, and
the facts `ts` of the case. -/
syntax "fk_go" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

set_option hygiene false in
macro_rules
  | `(tactic| fk_go [$ts,*]) => `(tactic| simp [nock_exec, forkE, bondE, hD, ho1, ho2, ho3, ho4, ho5, ho6,
      hDct, comp_ct_arm, hc1, hc2, ihy, ihn, hDpx, comp_px_arm, hp1, hp2, hDem, comp_emit_arm, he1, he2,
      hDih, comp_ih_arm, hi1, hi2, pure_apply, cf_emit_g, listNoun, jmp0, bind_apply, $ts,*])

/-- The same for the bond gate. -/
syntax "fkb_go" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

set_option hygiene false in
macro_rules
  | `(tactic| fkb_go [$ts,*]) => `(tactic| simp [nock_exec, forkE, bondE, hD, ho1, ho2, ho3, hDct,
      comp_ct_arm, hc1, ihy, hDpx, comp_px_arm, hp1, hDem, comp_emit_arm, he1, hDih, comp_ih_arm, hi1,
      pure_apply, cf_emit_g, listNoun, jmp0, bind_apply, $ts,*])

syntax "fkb_open" ident "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| fkb_open $p:ident [$ts,*]) => `(tactic| (conv => { lhs; arg 2; unfold $p:ident }); fkb_go [$ts,*])

/-- Open the push `p` of a gate (the rest stays a constant) and run it. -/
syntax "fk_open" ident "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| fk_open $p:ident [$ts,*]) => `(tactic| (conv => { lhs; arg 2; unfold $p:ident }); fk_go [$ts,*])

section
variable (x : GenRest) (N : Noun) (rc : Nat)

/-- The fork gate: `=.  gen  gen-acc`, six `+oo`, two `+copy-tag`, the trap
on the yes need then on the no need, two `+proxy`, two `+emit`, two
`+insert-hop`, whatever trap subject it was made in. -/
theorem fk_fgate (hc : CompIn ctx) (SHT L' G' : Noun) (o' o1' o0' : Nat) (e : Lazy.ForkE CSet)
    (g : Gen (TreapMap mugF))
    (ihy : FkIH (ctx := ctx) x N rc e.1.2) (ihn : FkIH (ctx := ctx) x N rc e.2.2) :
    nock (C fkGF (C (C (forkE e) (genNoun g x))
      (C SHT (fkTS o' L' o1' o0' (C N (A rc)) (C comp.door (C G' ctx)))))) fkGF
      = (gFkF rc e g).map fun r => C (C (forkE r.1) (forkE r.2.1)) (genNoun r.2.2 x) := by
  obtain ⟨⟨oy, y⟩, ⟨on, n⟩⟩ := e
  unfold FkIH at ihy ihn
  simp only [fkTS, compCore, splitEnc] at ihy ihn ⊢
  have hD := comp_oo_at
  have hDct := comp_ct_at
  have hDpx := comp_px_at
  have hDem := comp_emit_at
  have hDih := comp_ih_at
  have ho1 := comp_oo' (ctx := ctx) x g
  have ho2 := comp_oo' (ctx := ctx) x (ooG g)
  have ho3 := comp_oo' (ctx := ctx) x (ooG (ooG g))
  have ho4 := comp_oo' (ctx := ctx) x (ooG (ooG (ooG g)))
  have ho5 := comp_oo' (ctx := ctx) x (ooG (ooG (ooG (ooG g))))
  have ho6 := comp_oo' (ctx := ctx) x (ooG (ooG (ooG (ooG (ooG g)))))
  have hc1 := fun g' => comp_copy_tag (x := x) hc g' oy [g.bo, (ooG g).bo]
  have hc2 := fun g' => comp_copy_tag (x := x) hc g' on [(ooG (ooG g)).bo, (ooG (ooG (ooG g))).bo]
  have hp1 := fun g' => comp_proxy hc x g' rc oy
  have hp2 := fun g' => comp_proxy hc x g' rc on
  have he1 := fun g' p => cf_emit (x := x) hc g' ⟨[], [], Termin.brz p (jmp0 g.bo) (jmp0 (ooG g).bo)⟩
  have he2 := fun g' p => cf_emit (x := x) hc g'
    ⟨[], [], Termin.brz p (jmp0 (ooG (ooG g)).bo) (jmp0 (ooG (ooG (ooG g))).bo)⟩
  have hi1 := fun g' o1 => comp_insert_hop (x := x) hc g' oy o1 (ooG (ooG (ooG (ooG g)))).bo
  have hi2 := fun g' o1 => comp_insert_hop (x := x) hc g' on o1 (ooG (ooG (ooG (ooG (ooG g))))).bo
  simp only [compCore, listNoun, Blob.toNoun, Termin.toNoun, Tag.brz, Jmp.toNoun, jmp0, unitNoun]
    at hc1 hc2 hp1 hp2 he1 he2 hi1 hi2
  unfold gFkF fkStepF
  simp only [bind_apply, oo_ap, Option.bind_some]
  generalize comp.door = Dr at hD hDct hDpx hDem hDih ho1 ho2 ho3 ho4 ho5 ho6 hc1 hc2 hp1 hp2 he1 he2 hi1 hi2 ihy ihn ⊢
  cases e1 : copyTag oy [g.bo, (ooG g).bo] (ooG (ooG (ooG (ooG (ooG (ooG g)))))) with
  | none =>
    conv => { lhs; arg 2; rw [fkGF_eq] }
    fk_open fkGF0 [e1]
    fk_open fkGF1 [e1]
    fk_open fkGF2 [e1]
    fk_open fkGF3 [e1]
    fk_open fkGF4 [e1]
    fk_open fkGF5 [e1]
    fk_open fkGF6 [e1]
    fk_open fkGF7 [e1]
    fk_open fkGF8 [e1]
  | some r =>
  obtain ⟨⟨⟩, g7⟩ := r
  cases e2 : copyTag on [(ooG (ooG g)).bo, (ooG (ooG (ooG g))).bo] g7 with
  | none =>
    conv => { lhs; arg 2; rw [fkGF_eq] }
    fk_open fkGF0 [e1, e2]
    fk_open fkGF1 [e1, e2]
    fk_open fkGF2 [e1, e2]
    fk_open fkGF3 [e1, e2]
    fk_open fkGF4 [e1, e2]
    fk_open fkGF5 [e1, e2]
    fk_open fkGF6 [e1, e2]
    fk_open fkGF7 [e1, e2]
    fk_open fkGF8 [e1, e2]
    fk_open fkGF9 [e1, e2]
  | some r =>
  obtain ⟨⟨⟩, g8⟩ := r
  cases e3 : forkLoop rc y (ooG (ooG (ooG (ooG g)))).bo g.bo (ooG g).bo g8 with
  | none =>
    conv => { lhs; arg 2; rw [fkGF_eq] }
    fk_open fkGF0 [e1, e2, e3]
    fk_open fkGF1 [e1, e2, e3]
    fk_open fkGF2 [e1, e2, e3]
    fk_open fkGF3 [e1, e2, e3]
    fk_open fkGF4 [e1, e2, e3]
    fk_open fkGF5 [e1, e2, e3]
    fk_open fkGF6 [e1, e2, e3]
    fk_open fkGF7 [e1, e2, e3]
    fk_open fkGF8 [e1, e2, e3]
    fk_open fkGF9 [e1, e2, e3]
    fk_open fkGF10 [e1, e2, e3]
  | some r =>
  obtain ⟨⟨ly0, ly1⟩, g9⟩ := r
  cases e4 : forkLoop rc n (ooG (ooG (ooG (ooG (ooG g))))).bo (ooG (ooG g)).bo (ooG (ooG (ooG g))).bo g9 with
  | none =>
    conv => { lhs; arg 2; rw [fkGF_eq] }
    fk_open fkGF0 [e1, e2, e3, e4]
    fk_open fkGF1 [e1, e2, e3, e4]
    fk_open fkGF2 [e1, e2, e3, e4]
    fk_open fkGF3 [e1, e2, e3, e4]
    fk_open fkGF4 [e1, e2, e3, e4]
    fk_open fkGF5 [e1, e2, e3, e4]
    fk_open fkGF6 [e1, e2, e3, e4]
    fk_open fkGF7 [e1, e2, e3, e4]
    fk_open fkGF8 [e1, e2, e3, e4]
    fk_open fkGF9 [e1, e2, e3, e4]
    fk_open fkGF10 [e1, e2, e3, e4]
    fk_open fkGF11 [e1, e2, e3, e4]
  | some r =>
  obtain ⟨⟨ln0, ln1⟩, g10⟩ := r
  cases e5 : proxy rc oy g10 with
  | none =>
    conv => { lhs; arg 2; rw [fkGF_eq] }
    fk_open fkGF0 [e1, e2, e3, e4, e5]
    fk_open fkGF1 [e1, e2, e3, e4, e5]
    fk_open fkGF2 [e1, e2, e3, e4, e5]
    fk_open fkGF3 [e1, e2, e3, e4, e5]
    fk_open fkGF4 [e1, e2, e3, e4, e5]
    fk_open fkGF5 [e1, e2, e3, e4, e5]
    fk_open fkGF6 [e1, e2, e3, e4, e5]
    fk_open fkGF7 [e1, e2, e3, e4, e5]
    fk_open fkGF8 [e1, e2, e3, e4, e5]
    fk_open fkGF9 [e1, e2, e3, e4, e5]
    fk_open fkGF10 [e1, e2, e3, e4, e5]
    fk_open fkGF11 [e1, e2, e3, e4, e5]
    fk_open fkGF12 [e1, e2, e3, e4, e5]
  | some r =>
  obtain ⟨py, g11⟩ := r
  cases e6 : proxy rc on g11 with
  | none =>
    conv => { lhs; arg 2; rw [fkGF_eq] }
    fk_open fkGF0 [e1, e2, e3, e4, e5, e6]
    fk_open fkGF1 [e1, e2, e3, e4, e5, e6]
    fk_open fkGF2 [e1, e2, e3, e4, e5, e6]
    fk_open fkGF3 [e1, e2, e3, e4, e5, e6]
    fk_open fkGF4 [e1, e2, e3, e4, e5, e6]
    fk_open fkGF5 [e1, e2, e3, e4, e5, e6]
    fk_open fkGF6 [e1, e2, e3, e4, e5, e6]
    fk_open fkGF7 [e1, e2, e3, e4, e5, e6]
    fk_open fkGF8 [e1, e2, e3, e4, e5, e6]
    fk_open fkGF9 [e1, e2, e3, e4, e5, e6]
    fk_open fkGF10 [e1, e2, e3, e4, e5, e6]
    fk_open fkGF11 [e1, e2, e3, e4, e5, e6]
    fk_open fkGF12 [e1, e2, e3, e4, e5, e6]
    fk_open fkGF13 [e1, e2, e3, e4, e5, e6]
  | some r =>
  obtain ⟨pn, g12⟩ := r
  cases e7 : insertHop oy g12.bo (ooG (ooG (ooG (ooG g)))).bo
      (cfEmitG ⟨[], [], Termin.brz pn ⟨[], (ooG (ooG g)).bo⟩ ⟨[], (ooG (ooG (ooG g))).bo⟩⟩
        (cfEmitG ⟨[], [], Termin.brz py ⟨[], g.bo⟩ ⟨[], (ooG g).bo⟩⟩ g12)) with
  | none =>
    conv => { lhs; arg 2; rw [fkGF_eq] }
    fk_open fkGF0 [e1, e2, e3, e4, e5, e6, e7]
    fk_open fkGF1 [e1, e2, e3, e4, e5, e6, e7]
    fk_open fkGF2 [e1, e2, e3, e4, e5, e6, e7]
    fk_open fkGF3 [e1, e2, e3, e4, e5, e6, e7]
    fk_open fkGF4 [e1, e2, e3, e4, e5, e6, e7]
    fk_open fkGF5 [e1, e2, e3, e4, e5, e6, e7]
    fk_open fkGF6 [e1, e2, e3, e4, e5, e6, e7]
    fk_open fkGF7 [e1, e2, e3, e4, e5, e6, e7]
    fk_open fkGF8 [e1, e2, e3, e4, e5, e6, e7]
    fk_open fkGF9 [e1, e2, e3, e4, e5, e6, e7]
    fk_open fkGF10 [e1, e2, e3, e4, e5, e6, e7]
    fk_open fkGF11 [e1, e2, e3, e4, e5, e6, e7]
    fk_open fkGF12 [e1, e2, e3, e4, e5, e6, e7]
    fk_open fkGF13 [e1, e2, e3, e4, e5, e6, e7]
    fk_open fkGF14 [e1, e2, e3, e4, e5, e6, e7]
    fk_open fkGF15 [e1, e2, e3, e4, e5, e6, e7]
    fk_open fkGF16 [e1, e2, e3, e4, e5, e6, e7]
  | some r =>
  obtain ⟨⟨⟩, g13⟩ := r
  cases e8 : insertHop on (cfEmitG ⟨[], [], Termin.brz py ⟨[], g.bo⟩ ⟨[], (ooG g).bo⟩⟩ g12).bo
      (ooG (ooG (ooG (ooG (ooG g))))).bo g13 with
  | none =>
    conv => { lhs; arg 2; rw [fkGF_eq] }
    fk_open fkGF0 [e1, e2, e3, e4, e5, e6, e7, e8]
    fk_open fkGF1 [e1, e2, e3, e4, e5, e6, e7, e8]
    fk_open fkGF2 [e1, e2, e3, e4, e5, e6, e7, e8]
    fk_open fkGF3 [e1, e2, e3, e4, e5, e6, e7, e8]
    fk_open fkGF4 [e1, e2, e3, e4, e5, e6, e7, e8]
    fk_open fkGF5 [e1, e2, e3, e4, e5, e6, e7, e8]
    fk_open fkGF6 [e1, e2, e3, e4, e5, e6, e7, e8]
    fk_open fkGF7 [e1, e2, e3, e4, e5, e6, e7, e8]
    fk_open fkGF8 [e1, e2, e3, e4, e5, e6, e7, e8]
    fk_open fkGF9 [e1, e2, e3, e4, e5, e6, e7, e8]
    fk_open fkGF10 [e1, e2, e3, e4, e5, e6, e7, e8]
    fk_open fkGF11 [e1, e2, e3, e4, e5, e6, e7, e8]
    fk_open fkGF12 [e1, e2, e3, e4, e5, e6, e7, e8]
    fk_open fkGF13 [e1, e2, e3, e4, e5, e6, e7, e8]
    fk_open fkGF14 [e1, e2, e3, e4, e5, e6, e7, e8]
    fk_open fkGF15 [e1, e2, e3, e4, e5, e6, e7, e8]
    fk_open fkGF16 [e1, e2, e3, e4, e5, e6, e7, e8]
    fk_open fkGF17 [e1, e2, e3, e4, e5, e6, e7, e8]
  | some r =>
  obtain ⟨⟨⟩, g14⟩ := r
  conv => { lhs; arg 2; rw [fkGF_eq] }
  fk_open fkGF0 [e1, e2, e3, e4, e5, e6, e7, e8]
  fk_open fkGF1 [e1, e2, e3, e4, e5, e6, e7, e8]
  fk_open fkGF2 [e1, e2, e3, e4, e5, e6, e7, e8]
  fk_open fkGF3 [e1, e2, e3, e4, e5, e6, e7, e8]
  fk_open fkGF4 [e1, e2, e3, e4, e5, e6, e7, e8]
  fk_open fkGF5 [e1, e2, e3, e4, e5, e6, e7, e8]
  fk_open fkGF6 [e1, e2, e3, e4, e5, e6, e7, e8]
  fk_open fkGF7 [e1, e2, e3, e4, e5, e6, e7, e8]
  fk_open fkGF8 [e1, e2, e3, e4, e5, e6, e7, e8]
  fk_open fkGF9 [e1, e2, e3, e4, e5, e6, e7, e8]
  fk_open fkGF10 [e1, e2, e3, e4, e5, e6, e7, e8]
  fk_open fkGF11 [e1, e2, e3, e4, e5, e6, e7, e8]
  fk_open fkGF12 [e1, e2, e3, e4, e5, e6, e7, e8]
  fk_open fkGF13 [e1, e2, e3, e4, e5, e6, e7, e8]
  fk_open fkGF14 [e1, e2, e3, e4, e5, e6, e7, e8]
  fk_open fkGF15 [e1, e2, e3, e4, e5, e6, e7, e8]
  fk_open fkGF16 [e1, e2, e3, e4, e5, e6, e7, e8]
  fk_open fkGF17 [e1, e2, e3, e4, e5, e6, e7, e8]
  fk_open fkGF18 [e1, e2, e3, e4, e5, e6, e7, e8]


/-- The bond gate: `=.  gen  gen-acc`, three `+oo`, `+copy-tag`, the trap on
the bond's need, `+proxy`, `+emit`, `+insert-hop`, whatever trap subject it
was made in. -/
theorem fk_bgate (hc : CompIn ctx) (FHT SHT L' G' : Noun) (o' o1' o0' : Nat) (e : Nat × Lazy CSet)
    (g : Gen (TreapMap mugF)) (ihy : FkIH (ctx := ctx) x N rc e.2) :
    nock (C fkGB (C (C (bondE e) (genNoun g x))
      (C FHT (C SHT (fkTS o' L' o1' o0' (C N (A rc)) (C comp.door (C G' ctx))))))) fkGB
      = (gFkB rc e g).map fun r => C (C (bondE r.1) (bondE r.2.1)) (genNoun r.2.2 x) := by
  obtain ⟨ob, l⟩ := e
  unfold FkIH at ihy
  simp only [fkTS, compCore, splitEnc] at ihy ⊢
  have hD := comp_oo_at
  have hDct := comp_ct_at
  have hDpx := comp_px_at
  have hDem := comp_emit_at
  have hDih := comp_ih_at
  have ho1 := comp_oo' (ctx := ctx) x g
  have ho2 := comp_oo' (ctx := ctx) x (ooG g)
  have ho3 := comp_oo' (ctx := ctx) x (ooG (ooG g))
  have hc1 := fun g' => comp_copy_tag (x := x) hc g' ob [g.bo, (ooG g).bo]
  have hp1 := fun g' => comp_proxy hc x g' rc ob
  have he1 := fun g' p => cf_emit (x := x) hc g' ⟨[], [], Termin.brz p (jmp0 g.bo) (jmp0 (ooG g).bo)⟩
  have hi1 := fun g' o1 => comp_insert_hop (x := x) hc g' ob o1 (ooG (ooG g)).bo
  simp only [compCore, listNoun, Blob.toNoun, Termin.toNoun, Tag.brz, Jmp.toNoun, jmp0, unitNoun]
    at hc1 hp1 he1 hi1
  unfold gFkB fkStepB
  simp only [bind_apply, oo_ap, Option.bind_some]
  generalize comp.door = Dr at hD hDct hDpx hDem hDih ho1 ho2 ho3 hc1 hp1 he1 hi1 ihy ⊢
  cases e1 : copyTag ob [g.bo, (ooG g).bo] (ooG (ooG (ooG g))) with
  | none =>
    conv => { lhs; arg 2; rw [fkGB_eq] }
    fkb_open fkGB0 [e1]
    fkb_open fkGB1 [e1]
    fkb_open fkGB2 [e1]
    fkb_open fkGB3 [e1]
    fkb_open fkGB4 [e1]
  | some r =>
  obtain ⟨⟨⟩, g4⟩ := r
  cases e2 : forkLoop rc l (ooG (ooG g)).bo g.bo (ooG g).bo g4 with
  | none =>
    conv => { lhs; arg 2; rw [fkGB_eq] }
    fkb_open fkGB0 [e1, e2]
    fkb_open fkGB1 [e1, e2]
    fkb_open fkGB2 [e1, e2]
    fkb_open fkGB3 [e1, e2]
    fkb_open fkGB4 [e1, e2]
    fkb_open fkGB5 [e1, e2]
  | some r =>
  obtain ⟨⟨l0, l1⟩, g5⟩ := r
  cases e3 : proxy rc ob g5 with
  | none =>
    conv => { lhs; arg 2; rw [fkGB_eq] }
    fkb_open fkGB0 [e1, e2, e3]
    fkb_open fkGB1 [e1, e2, e3]
    fkb_open fkGB2 [e1, e2, e3]
    fkb_open fkGB3 [e1, e2, e3]
    fkb_open fkGB4 [e1, e2, e3]
    fkb_open fkGB5 [e1, e2, e3]
    fkb_open fkGB6 [e1, e2, e3]
  | some r =>
  obtain ⟨pb, g6⟩ := r
  cases e4 : insertHop ob g6.bo (ooG (ooG g)).bo (cfEmitG ⟨[], [], Termin.brz pb ⟨[], g.bo⟩ ⟨[], (ooG g).bo⟩⟩ g6) with
  | none =>
    conv => { lhs; arg 2; rw [fkGB_eq] }
    fkb_open fkGB0 [e1, e2, e3, e4]
    fkb_open fkGB1 [e1, e2, e3, e4]
    fkb_open fkGB2 [e1, e2, e3, e4]
    fkb_open fkGB3 [e1, e2, e3, e4]
    fkb_open fkGB4 [e1, e2, e3, e4]
    fkb_open fkGB5 [e1, e2, e3, e4]
    fkb_open fkGB6 [e1, e2, e3, e4]
    fkb_open fkGB7 [e1, e2, e3, e4]
    fkb_open fkGB8 [e1, e2, e3, e4]
  | some r =>
  obtain ⟨⟨⟩, g7⟩ := r
  conv => { lhs; arg 2; rw [fkGB_eq] }
  fkb_open fkGB0 [e1, e2, e3, e4]
  fkb_open fkGB1 [e1, e2, e3, e4]
  fkb_open fkGB2 [e1, e2, e3, e4]
  fkb_open fkGB3 [e1, e2, e3, e4]
  fkb_open fkGB4 [e1, e2, e3, e4]
  fkb_open fkGB5 [e1, e2, e3, e4]
  fkb_open fkGB6 [e1, e2, e3, e4]
  fkb_open fkGB7 [e1, e2, e3, e4]
  fkb_open fkGB8 [e1, e2, e3, e4]
  fkb_open fkGB9 [e1, e2, e3, e4]

end

end Compiler
end Formalization
