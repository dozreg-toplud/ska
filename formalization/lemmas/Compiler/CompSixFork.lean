import lemmas.Compiler.CompRunSixRes

/-!
# `+fork-need` and `+fork-sure`

The nouns are cut by hand from the output of `tools/gen/sixhelp.py forkNeed
forkSure`; `fkn_at` and `fks_at` tie them to the pill.

`+fork-need` (door arm `62`) on `[ned o o-0 o-1]` runs its loop first (the
`=;`), with `fknLoop` the trap over the need: `[%none ~]` twice, two fresh
registers for `%this`, the head then the tail for a cell, two fresh
registers then the head then the tail for `%both` (`forkNeedGo`,
`fkn_loop`); then the arguments of the two `%hop` blocks (`+turn` of `some`
over `+flatten-need` of each new need), the join block `[(flatten-need ned) ~
%hop ~ o]` by `+emit`, and the two `%hop` blocks at `o-0` and `o-1` by
`+emir` (`forkNeed`, `comp_fork_need`).  `+fork-sure` (door arm `884727`)
forks the need of a sure and keeps its looks (`forkSure`,
`comp_fork_sure`).  No departure.

`forkNeedGo_fresh`: the two new needs are made of registers taken from the
counter in order, so each has no register twice, they share none, and all
lie in `[g.re, g'.re)`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

def fknLoop : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 56)))) (C (C (C (A 1) (C (C (A 0x656e6f6e) (A 0)) (C (A 0x656e6f6e) (A 0)))) (C (A 0) (A 62))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 56)))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 15)))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 31)))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (C (A 1) (A 0x73696874)) (C (A 0) (A 6))) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 2)))) (C (A 0) (A 254))))))))))))))))))) (C (A 6) (C (C (A 3) (C (A 0) (A 56))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 28) (C (A 0) (A 56))) (C (A 0) (A 1)))))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 28) (C (A 0) (A 121))) (C (A 0) (A 3)))))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (C (A 0) (A 12)) (C (A 0) (A 4))) (C (C (A 0) (A 13)) (C (A 0) (A 5)))) (C (A 0) (A 254))))))))))))))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 56))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 15)))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 31)))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 28) (C (A 0) (A 998))) (C (A 0) (A 7)))))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 28) (C (A 0) (A 2023))) (C (A 0) (A 15)))))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (C (A 1) (A 0x68746f62)) (C (C (A 0) (A 30)) (C (C (A 0) (A 12)) (C (A 0) (A 4))))) (C (C (A 1) (A 0x68746f62)) (C (C (A 0) (A 14)) (C (C (A 0) (A 13)) (C (A 0) (A 5)))))) (C (A 0) (A 1022))))))))))))))))))))))))))))))))))))))))))))))

def fknTail : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 348) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 57))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 5982) (C (A 0) (A 0xffffff)))))))) (C (A 0) (A 2)))))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 348) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 252))) (C (A 0) (A 2)))))))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 506))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 8) (C (C (A 9) (C (A 350) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 2038)) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (C (A 0) (A 30)) (C (A 0) (A 6)))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 9) (C (A 350) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 2039)) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (C (A 0) (A 14)) (C (A 0) (A 6)))))))) (C (A 0) (A 2))))))))))))))))))))

def fknBat : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 1) fknLoop) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (C (C (A 0) (A 8)) (C (A 0) (A 9))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 348) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 24))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 5982) (C (A 0) (A 0x7fffff)))))))) (C (A 0) (A 2)))))))) fknTail)))))))

def fknBunt : Noun :=
  (C (C (A 0x656e6f6e) (A 0)) (C (A 0) (C (A 0) (A 0))))

def fknHint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x6465656e2d6b726f662d706d6f63) (C (C (A 0) (A 0x7ffff)) (A 0))))) (C (A 0) (A 1))))

def fksBat : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 94) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 56)) (C (C (A 0) (A 58)) (C (C (A 0) (A 118)) (C (A 0) (A 119)))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (C (A 0) (A 4)) (C (A 0) (A 57))) (C (C (A 0) (A 5)) (C (A 0) (A 57)))) (C (A 0) (A 62)))))))))))

def fksBunt : Noun :=
  (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (C (A 0) (A 0))))

def fksHint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x657275732d6b726f662d706d6f63) (C (C (A 0) (A 0x7ffff)) (A 0))))) (C (A 0) (A 1))))

def fknArm : Noun :=
  C (A 7) (C (C (A 8) (C (C (A 1) fknBunt) (C (C (A 1) fknBat) (C (A 0) (A 1))))) fknHint)

/-- **The cut of `+fork-need`** is the pill's (door arm `62`). -/
theorem fkn_at : slot? 62 comp.door = some fknArm := by kernel_rfl

theorem fkn_arm (d : Noun) : nock d fknArm = some (C fknBat (C fknBunt d)) := by
  unfold fknArm fknHint; simp only [nock_exec]

def fksArm : Noun :=
  C (A 7) (C (C (A 8) (C (C (A 1) fksBunt) (C (C (A 1) fksBat) (C (A 0) (A 1))))) fksHint)

/-- **`+fork-sure`** is door arm `884727`. -/
theorem fks_at : slot? 884727 comp.door = some fksArm := by kernel_rfl

theorem fks_arm (d : Noun) : nock d fksArm = some (C fksBat (C fksBunt d)) := by
  unfold fksArm fksHint; simp only [nock_exec]

section
variable (hc : CompIn ctx) (x : GenRest) (S : Noun)
include hc

/-- **The loop of `+fork-need`** is `forkNeedGo`. -/
theorem fkn_loop : ∀ (ned : Need) (g : Gen (TreapMap mugF)),
    nock (C fknLoop (C fknBat (C (C ned.toNoun S) (compCore g x ctx)))) fknLoop
      = (forkNeedGo ned g).map fun p => C (C p.1.1.toNoun p.1.2.toNoun) (genNoun p.2 x)
  | Need.none, g => by
    unfold fknLoop
    simp [nock_exec, Need.toNoun, Tag.none, forkNeedGo, pure, StateT.pure, compCore]
  | Need.this r, g => by
    have h1 := comp_re' (ctx := ctx) x g
    have h2 := comp_re' (ctx := ctx) x { g with re := g.re + 1 }
    have hD := comp_re_at
    simp only [compCore]
    generalize comp.door = Dr at h1 h2 hD ⊢
    unfold fknLoop
    simp [nock_exec, Need.toNoun, Tag.none, Tag.this, forkNeedGo, pure, StateT.pure, bind, StateT.bind, re,
      hD, h1, h2]
  | Need.pair p q, g => by
    obtain ⟨a, b, hab⟩ := cd_need_cell p
    have ih1 := fkn_loop p g
    simp only [compCore] at ih1 ⊢
    cases e1 : forkNeedGo (Map := TreapMap mugF) p g with
    | none =>
      rw [e1] at ih1
      rw [hab] at ih1
      conv => { lhs; arg 2; unfold fknLoop }
      simp [nock_exec, Need.toNoun, hab, forkNeedGo, bind, StateT.bind, e1, ih1, Tag.none, Tag.this]
    | some r1 =>
      obtain ⟨⟨h0, h1⟩, g1⟩ := r1
      rw [e1] at ih1
      have ih2 := fkn_loop q g1
      simp only [compCore] at ih2
      rw [hab] at ih1
      cases e2 : forkNeedGo (Map := TreapMap mugF) q g1 with
      | none =>
        rw [e2] at ih2
        conv => { lhs; arg 2; unfold fknLoop }
        simp [nock_exec, Need.toNoun, hab, forkNeedGo, bind, StateT.bind, e1, e2, ih1, ih2, Tag.none, Tag.this]
      | some r2 =>
        obtain ⟨⟨t0, t1⟩, g2⟩ := r2
        rw [e2] at ih2
        conv => { lhs; arg 2; unfold fknLoop }
        simp [nock_exec, Need.toNoun, hab, forkNeedGo, bind, StateT.bind, e1, e2, ih1, ih2, Tag.none, Tag.this,
          pure, StateT.pure]
  | Need.both rb p q, g => by
    have hr1 := comp_re' (ctx := ctx) x g
    have hr2 := comp_re' (ctx := ctx) x { g with re := g.re + 1 }
    have hD := comp_re_at
    have ih1 := fkn_loop p { { g with re := g.re + 1 } with re := g.re + 1 + 1 }
    simp only [compCore] at ih1 hr1 hr2 ⊢
    cases e1 : forkNeedGo (Map := TreapMap mugF) p { { g with re := g.re + 1 } with re := g.re + 1 + 1 } with
    | none =>
      rw [e1] at ih1
      generalize comp.door = Dr at hr1 hr2 hD ih1 ⊢
      conv => { lhs; arg 2; unfold fknLoop }
      simp [nock_exec, Need.toNoun, forkNeedGo, bind, StateT.bind, e1, ih1, Tag.none, Tag.this, Tag.both, re,
        hD, hr1, hr2]
    | some r1 =>
      obtain ⟨⟨h0, h1⟩, g1⟩ := r1
      rw [e1] at ih1
      have ih2 := fkn_loop q g1
      simp only [compCore] at ih2
      cases e2 : forkNeedGo (Map := TreapMap mugF) q g1 with
      | none =>
        rw [e2] at ih2
        generalize comp.door = Dr at hr1 hr2 hD ih1 ih2 ⊢
        conv => { lhs; arg 2; unfold fknLoop }
        simp [nock_exec, Need.toNoun, forkNeedGo, bind, StateT.bind, e1, e2, ih1, ih2, Tag.none, Tag.this,
          Tag.both, re, hD, hr1, hr2]
      | some r2 =>
        obtain ⟨⟨t0, t1⟩, g2⟩ := r2
        rw [e2] at ih2
        generalize comp.door = Dr at hr1 hr2 hD ih1 ih2 ⊢
        conv => { lhs; arg 2; unfold fknLoop }
        simp [nock_exec, Need.toNoun, forkNeedGo, bind, StateT.bind, e1, e2, ih1, ih2, Tag.none, Tag.this,
          Tag.both, re, hD, hr1, hr2, pure, StateT.pure]

end

end Compiler
end Formalization
