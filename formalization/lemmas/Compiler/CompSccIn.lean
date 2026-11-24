import lemmas.Compiler.CompUnaryTrap

/-!
# `+compile-scc-in` and the arms of its final pass

## The structure of `+compile-scc-in` (lines 3435 to 3709 of `nock-compilation.hoon`)

The gate (arm `2732` of `K`, `%compile-scc-in`) takes `[scc long-ska
jets-hot cache]` and returns `[(map bell straight) cache]`.

1. Line 3443: when every member of `scc` is in `nary.cache`, it returns
   their straights from the cache with `cache` unchanged.
2. Lines 3451 to 3461: `map-local` is `~`, `kids` maps each member to its
   callees inside `scc` (`calls.long-ska`), and `done` is true when `scc`
   is one bell `b` with `b` not in `kids` of itself (a function alone in its
   SCC that does not call itself).
3. Lines 3467 to 3606: the gate `member` (`%compile-scc-fn`) on `[b mode
   keep map-local top cache]`.  It builds the door `comp` on `[scc long-ska
   jets-hot map-local top b]` (line 3479), takes the nomm of `+inlined` with
   the new `cache` (line 3480), and starts `gen` as the bunt of `line-short`
   with `cache.gen` set (lines 3485, 3486).  The shape pass is the second
   expression of `!@  dedicated-shape-pass` (line 3503), since the flag is
   defined at line 2816 and `!@` (`%zppt`) takes its second expression when
   the wing exists (`?.((feel p.gen) q r)` in `+mint`).  Before the final
   pass (`mode` not `%done`) it runs `+run-shape` (line 3514) and collapses
   the shape with `+laze-collapse` (`%must`) or `+laze-may` (`%may`), then
   `+bake-need-ord`.  In the final pass (`mode` `%done`) it sets `mode.gen`
   to `%run` (line 3524), runs `(~(run comp gen) | nomm [%done ~] ~ ~)`,
   then `+collapse-shape` on the `next` and `cape.less.b` (line 3527:
   `?>  =(~ args.then.nex)`, then `+need-ord-alloc-regs` of `(shape-collapse
   laz.nex less)`, which gives `[ned-final laz.nex there.then.nex]`), then
   `bak` is `(bake-need ned-final less.b)` (line 3529) and `sur` is
   `+sure-of` of the sure part of `laz` (line 3531).  The shape `need-new`
   is `(need-to-ordered ned.bak)`.
4. Lines 3535 to 3538: `cache` becomes `cache.gen` (the `+run` above may
   have compiled callees into it), and `sure.cache` gets `sur` at `b`
   (with `keep`, the value already there wins).
5. Lines 3554 to 3576: the gate `finish` (`%compile-scc-finish`) on a
   `(unit need-ordered)`.  Unless `done`, it is `[need-new 0 ~]`.  When
   `done`: `+coerce-lazy` of `ned-final`, `o`, `laz`, `cape.less.b` (line
   3562), `+soft-done` (line 3563), `+add-ops` at `o` of the `%imm` ops of
   `imm.bak` (line 3567), then `+to-straight` of `[%next [[ned.bak ~] ~ ~]
   ~ o]` (line 3570) or, when the shape was pessimized, `+coerce-soft` of
   that `next` first (line 3572).  The changes `finish` makes to `gen` are
   thrown away with it: the cache `member` returns is the one of step 4.
6. Lines 3582 to 3604: with no straight of `b` in `map-local` yet, the
   product is `[chg (~(put by map-local) b (finish ~)) cache]`; otherwise
   `need-pessimized` is `+msg-need-ord` of the new and the old shape, and
   `finish` gets it when it differs from the new shape.
7. Lines 3612 to 3621: `final` rolls `member` with mode `%done` over `~(tap
   in scc)` and puts the straights into `nary.cache` (`+uni:by`).  When
   `done`, `+compile-scc-in` is `(final | map-local cache)`: no fixed point,
   no `%may` sweep, no `+run-shape`, one call of `member`.
8. Lines 3638 to 3709 (not `done`): the DFS postorder `order`, one `%may`
   sweep (line 3677, also in the second expression of `!@`), then the
   sweeps of `%must` over `order` until none is dirty, then `(final &
   map-local cache)`.

## Against the model `finishLF nm ord cape bake` (`Ska/CompFinishF.lean`)

* `runL nm done [] gen0` is the run of step 3 (`gen0` is the bunt with
  `mode` `%run`; the Hoon's `gen` also carries `cache`, `soft`, `sofs`).
* `if nex.th.args ≠ [] then none` is the `?>` of `+collapse-shape`.
* `needOrdAllocRegs ord g1` is `+need-ord-alloc-regs` of `+collapse-shape`,
  so `ord` must be `(shape-collapse laz.nex cape.less.b)`, a value the run
  determines: `+shape-collapse` (arm `682` of `compTypes`) has no model.
* `bake nedFinal` is `(bake-need ned-final less.b)` (line 3718).  The arm
  walks the need with the sock `k` of the part it is the need of, taken
  down with `hed:so` and `tel:so` (from line 3727); where `k` is a cell,
  `(all:ca cape.k)` holds and `+need-fits` says the data has the structure
  the need asks, it bakes that part whole (`[%none ~]`, with the `%imm`
  loads of its registers); otherwise it rebuilds cells with `+cons-need`
  and turns a `%both` whose halves were both baked into `[%this r]`.  When
  no node is baked (`NoBake` of `CompBakeNeed.lean`, the sock at every node
  `%void` or not wholly known) it is `[ned-final ~]` (`bn_gate`).
* `coerceLazyL nedFinal less nex.th.there nex.laz` is `+coerce-lazy` with
  `soft` empty (the model's `%this` case has no `(~(has by soft.gen) o)`
  test, which on a `soft` with `o` calls `+soft-ask` instead).
* Not in the model: `+soft-done` after `+coerce-lazy`, the identity when
  `soft` is `~` or `mode` is `%drop` (`sd_empty`, `sd_drop` below), and
  `+coerce-soft` when the shape was pessimized, which happens only when
  `map-local` already holds `b`, never for a bell alone in its SCC that does
  not call itself.
* `addOps nex.th.there (bak.2.map …)` is the `+add-ops` of line 3567.
* `toStraightF g4.cond g4.blocks bak.1 nex.th.there` is `+to-straight` of
  `[%next [[ned.bak ~] ~ ~] ~ o]`.
* The model returns only the straight: the cache of step 4 and the
  `nary.cache` of step 7 are not modelled.

## The arms linked here

* `sd_empty`, `sd_drop`: `+soft-done` (battery axis `54644` of the door,
  `sdArm`) is the identity on `soft` empty or `mode` `%drop`.
* `nta_gate`: the gate of `+need-to-ordered` (arm `44732` of `K`, its body
  `ntaBody`) is `needToOrd`.
* `noar_gate`: the gate of `+need-ord-alloc-regs` (battery axis `446` of the
  door, its body `noarBody`) is `needOrdAllocRegs`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The nouns -/

def noarBody : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 12)))) (C (C (C (A 1) (C (A 0x656e6f6e) (A 0))) (C (A 0) (A 30))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 12)))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 7)))))) (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 1) (A 0x73696874)) (C (A 0) (A 2))) (C (A 0) (A 62))))))))))) (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 12))) (C (A 0) (A 1)))))))) (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 3)))))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 12)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 4)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 0) (A 0)) (C (C (C (A 0) (A 6)) (C (A 0) (A 2))) (C (A 0) (A 126)))))))))))))))))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 12))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 7)))))) (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 58))) (C (A 0) (A 3)))))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 123))) (C (A 0) (A 7)))))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 12)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 4)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 0) (A 0)) (C (C (C (A 1) (A 0x68746f62)) (C (C (A 0) (A 14)) (C (C (A 0) (A 6)) (C (A 0) (A 2))))) (C (A 0) (A 254)))))))))))))))))))))))))))))))))))))))))

def noarHint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x736765722d636f6c6c612d64726f2d6465656e2d706d6f63) (C (C (A 0) (A 0x7ffff)) (A 0))))) (C (A 0) (A 1))))

def ntaBody : Noun :=
  (C (A 11) (C (C (A 0x6f6d656d) (C (A 1) (A 0))) (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 12)))) (C (C (A 1) (C (A 0x656e6f6e) (A 0))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 12)))) (C (C (A 1) (C (A 0x73696874) (A 0))) (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2))))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 12))))) (C (C (A 1) (A 0x68746f62)) (C (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 118))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 119))) (C (A 0) (A 2)))))))))))))))))))))))))

def ntaHint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x6465726564726f2d6f742d6465656e) (C (C (A 0) (A 0x7fff)) (A 0))))) (C (A 0) (A 1))))

def sdArm : Noun :=
  (C (A 6) (C (C (A 9) (C (A 1398) (C (A 0) (A 1)))) (C (C (A 0) (A 6)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 174) (C (A 10) (C (C (A 6) (C (A 0) (A 7678))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 1) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 6)))) (C (C (A 0) (A 30)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 8) (C (C (A 9) (C (A 0x555c) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2))))))))) (C (A 10) (C (C (A 6) (C (A 0) (A 13))) (C (A 0) (A 1)))))))))))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))))))

/-- `+soft-done` in the pill. -/
theorem sd_at : slot? 54644 comp.door = some sdArm := by kernel_rfl

/-- `+need-to-ordered` in `K`. -/
theorem nta_at : slot? 44732 compK = some (C (A 7) (C (C (A 8) (C (C (A 1) (C (A 0x656e6f6e) (A 0)))
    (C (C (A 1) ntaBody) (C (A 0) (A 1))))) ntaHint)) := by kernel_rfl

/-- `+need-ord-alloc-regs` in the door. -/
theorem noar_at : slot? 446 comp.door = some (C (A 7) (C (C (A 8) (C (C (A 1) (C (A 0x656e6f6e) (A 0)))
    (C (C (A 1) noarBody) (C (A 0) (A 1))))) noarHint)) := by kernel_rfl

/-! ## `+soft-done` -/

/-- **`+soft-done` on `soft` empty** is the identity: `+tap:by` of `~` is
`~`, and the loop returns `gen` on `~`. -/
theorem sd_empty (ctx : Noun) (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (x : GenRest) (hs : x.soft = A 0) :
    nock (compCore g x ctx) sdArm = some (genNoun g x) := by
  have hD := comp_drop_at
  obtain ⟨c, s, sofs⟩ := x
  simp only at hs
  subst hs
  simp only [compCore, genNoun]
  generalize comp.door = Dr at hD
  cases h : g.drop <;>
  simp [nock_exec, sdArm, h, cgModeNoun, hD, dropArm, comp_h110, eqCode_atom, hc, by_arm, by.arm_at,
    by.tap.arm_at, tap_arm, tap_loop, tapF]

/-- **`+soft-done` with `mode` `%drop`** is the identity. -/
theorem sd_drop (ctx : Noun) (g : Gen (TreapMap mugF)) (x : GenRest) (hd : g.drop = true) :
    nock (compCore g x ctx) sdArm = some (genNoun g x) := by
  have hD := comp_drop_at
  simp only [compCore, genNoun]
  generalize comp.door = Dr at hD
  simp [nock_exec, sdArm, hd, cgModeNoun, hD, dropArm, comp_h110, eqCode_atom]

/-! ## `+need-to-ordered` -/

/-- **The gate of `+need-to-ordered`** is `needToOrd`, in any context. -/
theorem nta_gate (Kc : Noun) : ∀ ned : Need,
    nock (C ntaBody (C ned.toNoun Kc)) ntaBody = some (needToOrd ned).toNoun
  | Need.none => by
    conv => { lhs; arg 2; unfold ntaBody }
    simp [nock_exec, Need.toNoun, needToOrd, NeedOrd.toNoun, eqCode, Tag.none]
  | Need.this r => by
    conv => { lhs; arg 2; unfold ntaBody }
    simp [nock_exec, Need.toNoun, needToOrd, NeedOrd.toNoun, eqCode, Tag.none, Tag.this]
  | Need.pair p q => by
    have ihp := nta_gate Kc p
    have ihq := nta_gate Kc q
    obtain ⟨a, b, hp⟩ := cd_need_cell p
    rw [hp] at ihp
    conv => { lhs; arg 2; unfold ntaBody }
    simp [nock_exec, Need.toNoun, hp, needToOrd, NeedOrd.toNoun, eqCode, ihp, ihq]
  | Need.both r h t => by
    have ihh := nta_gate Kc h
    have iht := nta_gate Kc t
    conv => { lhs; arg 2; unfold ntaBody }
    simp [nock_exec, Need.toNoun, needToOrd, NeedOrd.toNoun, eqCode, ihh, iht, Tag.none, Tag.this, Tag.both]

/-! ## `+need-ord-alloc-regs` -/

/-- The head of a need's noun is `%none` exactly for `[%none ~]`. -/
theorem noar_hd : ∀ n : Need, ∃ y z, n.toNoun = C y z ∧ (A 0x656e6f6e = y ↔ n = Need.none)
  | Need.none => ⟨_, _, rfl, by simp [Tag.none]⟩
  | Need.this r => ⟨_, _, rfl, by simp [Tag.this]⟩
  | Need.both r h t => ⟨_, _, rfl, by simp [Tag.both]⟩
  | Need.pair p q => by
    obtain ⟨a, b, hp⟩ := cd_need_cell p
    exact ⟨_, _, rfl, by simp [hp]⟩

theorem nord_cell : ∀ o : NeedOrd, ∃ a b, o.toNoun = C a b
  | NeedOrd.pair _ _ => ⟨_, _, rfl⟩
  | NeedOrd.both _ _ => ⟨_, _, rfl⟩
  | NeedOrd.this => ⟨_, _, rfl⟩
  | NeedOrd.none => ⟨_, _, rfl⟩

/-- **The gate of `+need-ord-alloc-regs`** is `needOrdAllocRegs`. -/
theorem noar_gate (ctx : Noun) (x : GenRest) : ∀ (ord : NeedOrd) (g : Gen (TreapMap mugF)),
    nock (C noarBody (C ord.toNoun (compCore g x ctx))) noarBody
      = (needOrdAllocRegs ord g).map fun p => C p.1.toNoun (genNoun p.2 x)
  | NeedOrd.none, g => by
    conv => { lhs; arg 2; unfold noarBody }
    simp [nock_exec, NeedOrd.toNoun, needOrdAllocRegs, Need.toNoun, eqCode, pure, StateT.pure, Tag.none]
  | NeedOrd.this, g => by
    have hD := comp_re_at
    have hre := comp_re' ctx x g
    simp only [genNoun] at hre
    conv => { lhs; arg 2; unfold noarBody }
    simp only [compCore]
    generalize comp.door = Dr at hD hre ⊢
    simp [nock_exec, NeedOrd.toNoun, needOrdAllocRegs, Need.toNoun, eqCode, hD, hre, genNoun, bind,
      StateT.bind, re, pure, StateT.pure, Tag.none, Tag.this]
  | NeedOrd.pair p q, g => by
    obtain ⟨a, b, hp⟩ := nord_cell p
    have ihp := noar_gate ctx x p g
    simp only [compCore] at ihp
    rw [hp] at ihp
    conv => { lhs; arg 2; unfold noarBody }
    simp only [compCore]
    cases e1 : needOrdAllocRegs p g with
    | none =>
      rw [e1] at ihp
      simp [nock_exec, NeedOrd.toNoun, hp, eqCode, ihp, needOrdAllocRegs, bind, StateT.bind, e1]
    | some r1 =>
      obtain ⟨h, g1⟩ := r1
      rw [e1] at ihp
      have ihq := noar_gate ctx x q g1
      simp only [compCore] at ihq
      cases e2 : needOrdAllocRegs q g1 with
      | none =>
        rw [e2] at ihq
        simp [nock_exec, NeedOrd.toNoun, hp, eqCode, ihp, ihq, needOrdAllocRegs, bind, StateT.bind, e1, e2]
      | some r2 =>
        obtain ⟨t, g2⟩ := r2
        rw [e2] at ihq
        obtain ⟨y1, z1, hh, eh⟩ := noar_hd h
        obtain ⟨y2, z2, ht, et⟩ := noar_hd t
        simp only [Option.map_some, hh] at ihp
        simp only [Option.map_some, ht] at ihq
        have k1 : h = Need.none → y1 = A Tag.none ∧ z1 = A 0 := by
          intro e; subst e; simp [Need.toNoun] at hh; exact ⟨hh.1.symm, hh.2.symm⟩
        have k2 : t = Need.none → y2 = A Tag.none ∧ z2 = A 0 := by
          intro e; subst e; simp [Need.toNoun] at ht; exact ⟨ht.1.symm, ht.2.symm⟩
        by_cases a1 : h = Need.none <;> by_cases a2 : t = Need.none <;>
        simp [nock_exec, NeedOrd.toNoun, hp, eqCode, ihp, ihq, needOrdAllocRegs, bind, StateT.bind, e1, e2,
          eh, et, a1, a2, crashM, pure, StateT.pure, Need.toNoun, hh, ht] <;>
        first | exact k1 a1 | exact k2 a2 | skip
  | NeedOrd.both p q, g => by
    have hD := comp_re_at
    have hre := comp_re' ctx x g
    simp only [genNoun] at hre
    have ihp := noar_gate ctx x p { g with re := g.re + 1 }
    simp only [compCore] at ihp
    conv => { lhs; arg 2; unfold noarBody }
    simp only [compCore]
    cases e1 : needOrdAllocRegs p { g with re := g.re + 1 } with
    | none =>
      rw [e1] at ihp
      simp only [Option.map_none, genNoun] at ihp
      generalize comp.door = Dr at hD hre ihp ⊢
      simp [nock_exec, NeedOrd.toNoun, eqCode, hD, hre, ihp, needOrdAllocRegs, bind, StateT.bind, re, e1,
        Tag.none, Tag.this, Tag.both, genNoun]
    | some r1 =>
      obtain ⟨h, g1⟩ := r1
      rw [e1] at ihp
      have ihq := noar_gate ctx x q g1
      simp only [compCore] at ihq
      cases e2 : needOrdAllocRegs q g1 with
      | none =>
        rw [e2] at ihq
        simp only [Option.map_none, Option.map_some, genNoun] at ihp ihq
        generalize comp.door = Dr at hD hre ihp ihq ⊢
        simp [nock_exec, NeedOrd.toNoun, eqCode, hD, hre, ihp, ihq, needOrdAllocRegs, bind, StateT.bind, re,
          e1, e2, Tag.none, Tag.this, Tag.both, genNoun]
      | some r2 =>
        obtain ⟨t, g2⟩ := r2
        rw [e2] at ihq
        obtain ⟨y1, z1, hh, eh⟩ := noar_hd h
        obtain ⟨y2, z2, ht, et⟩ := noar_hd t
        simp only [Option.map_some, hh] at ihp
        simp only [Option.map_some, ht] at ihq
        have k1 : h = Need.none → y1 = A Tag.none ∧ z1 = A 0 := by
          intro e; subst e; simp [Need.toNoun] at hh; exact ⟨hh.1.symm, hh.2.symm⟩
        have k2 : t = Need.none → y2 = A Tag.none ∧ z2 = A 0 := by
          intro e; subst e; simp [Need.toNoun] at ht; exact ⟨ht.1.symm, ht.2.symm⟩
        simp only [genNoun] at ihp ihq
        generalize comp.door = Dr at hD hre ihp ihq ⊢
        by_cases a1 : h = Need.none <;> by_cases a2 : t = Need.none <;>
        simp [nock_exec, NeedOrd.toNoun, eqCode, hD, hre, ihp, ihq, needOrdAllocRegs, bind, StateT.bind, re,
          e1, e2, eh, et, a1, a2, crashM, pure, StateT.pure, Need.toNoun, hh, ht, Tag.none, Tag.this, Tag.both,
          genNoun] <;>
        first | exact k1 a1 | exact k2 a2 | skip

/-! ## `+collapse-shape` -/

/-- The gate body of `+collapse-shape` (battery axis `1014` of the door). -/
def csBody : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 102)))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 702) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 682) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 114)) (C (A 0) (A 29)))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 0) (A 2)) (C (C (A 0) (A 114)) (C (A 0) (A 231)))) (C (A 0) (A 62))))))))))) (C (A 0) (A 0)))))

def csHint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x65706168732d657370616c6c6f632d706d6f63) (C (C (A 0) (A 0x7ffff)) (A 0))))) (C (A 0) (A 1))))

/-- `+collapse-shape` in the door. -/
theorem cs_at : slot? 1014 comp.door = some (C (A 7) (C (C (A 8) (C (C (A 1) (C (C (A 0x7478656e)
    (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))) (C (A 0) (A 0)))) (A 1)))
    (C (C (A 1) csBody) (C (A 0) (A 1))))) csHint)) := by kernel_rfl

/-- The arm `+shape-collapse` of `K` (arm `682`), no model. -/
noncomputable def scArm : Noun := (slot? 682 compK).getD (A 0)
/-- Its gate body. -/
noncomputable def scBody : Noun := (slot? 109 scArm).getD (A 0)

theorem sc_at : slot? 682 compK = some (C (A 7) (C (C (A 8) (C (C (A 1) (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0))
    (C (A 0) (A 0))) (A 1))) (C (C (A 1) scBody) (C (A 0) (A 1))))) (C (A 11) (C (C (A 0x74736166) (C (A 1)
    (C (A 0x657370616c6c6f632d6570616873) (C (C (A 0) (A 0x7fff)) (A 0))))) (C (A 0) (A 1)))))) := by
  kernel_rfl

/-- **The gate of `+collapse-shape`** on `[nex less]`: given that the gate
of `+shape-collapse` returns the shape `ord` on `[laz.nex less]`, it crashes
when `args.then.nex` is not `~`, and otherwise allocates the registers of
`ord` (`needOrdAllocRegs`) and returns `[[ned-final laz.nex there.then.nex]
gen]`. -/
theorem cs_gate (ctx : Noun) (h7 : slot? 7 ctx = some compK) (x : GenRest) (g : Gen (TreapMap mugF))
    (nex : NextL CSet) (LESS : Noun) (ord : NeedOrd)
    (hsc : nock (C scBody (C (C nex.laz.toNoun LESS) compK)) scBody = some ord.toNoun) :
    nock (C csBody (C (C nex.goal.toNoun LESS) (compCore g x ctx))) csBody
      = if nex.th.args ≠ [] then Option.none else
        (needOrdAllocRegs ord g).map fun p =>
          C (C p.1.toNoun (C nex.laz.toNoun (A nex.th.there))) (genNoun p.2 x) := by
  have hn := noar_gate ctx x ord g
  have hna := noar_at
  have hsa := sc_at
  simp only [compCore] at hn ⊢
  obtain ⟨laz, ⟨args, there⟩⟩ := nex
  conv => { lhs; arg 2; unfold csBody }
  generalize comp.door = Dr at hn hna ⊢
  generalize compK = Kc at hsa hsc h7
  cases args with
  | nil =>
    cases e : needOrdAllocRegs ord g with
    | none =>
      rw [e] at hn
      simp [nock_exec, NextL.goal, CGoalL.toNoun, Jmp.toNoun, listNoun, h7, hsa, hsc, hna, hn, noarHint]
    | some p =>
      rw [e] at hn
      simp [nock_exec, NextL.goal, CGoalL.toNoun, Jmp.toNoun, listNoun, h7, hsa, hsc, hna, hn, noarHint]
  | cons a l =>
    simp [nock_exec, NextL.goal, CGoalL.toNoun, Jmp.toNoun, listNoun]

end Compiler
end Formalization
