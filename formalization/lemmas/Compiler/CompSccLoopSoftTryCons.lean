import lemmas.Compiler.CompSccLoopSoftTryS
import lemmas.Compiler.CompFrom
import lemmas.Compiler.So
import lemmas.Compiler.CompMember

/-! # `+soft-cons` and the push `[kon rub]` of the try path (README Gaps 21.22)

`+soft-cons` (line 5674) is battery slot `12` of `comp.door` (`tc_at`), cut by
`tools/gen/softcons.py` (the definitions between the markers).  On the trap subject `tcS`
(`[tcTrap [axe [tcBat [[ned [tom k]] core]]]]`):
* `tc_get`: `(~(get by tops) axe)` on a map `AxsRel TOM tom`;
* `tc_hit`, `tc_this`, `tc_both`, `tc_none`: the cases that do not recurse;
* `tc_pH`, `tc_pT`, `tc_pR`: the cell, one `=^` at a time (the head, the tail, `re` and the
  product `:(weld oh ot [%con rh rt r]~)`);
* **`tc_loop`**: the trap is `softConsM` on every need (`TcAt`), by induction;
* **`tc_gate`**: the gate on `[ned tom k]`;
* **`tc_push`**: the push `tpY2` .. `tpY5` of the try path, on to `tpY6` with `tzS`-shaped subject.
`hed:so` / `tel:so` come from the library core at axis `255` of the door's context (`hl`; for the
context `memDCtx` of the final pass: `tc_memD_lib`). -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

-- BEGIN softcons

def tcProd : Noun :=
  (C (C (C (A 8) (C (C (A 9) (C (A 0xbef7f4) (C (A 0) (A 0x1fffffff)))) (C (A 8) (C (C (A 0) (A 2)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 0) (A 2)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 60)) (C (A 7) (C (C (A 0) (A 3)) (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x6e6f63)) (C (C (A 0) (A 29)) (C (C (A 0) (A 13)) (C (A 0) (A 2))))) (C (A 1) (A 0))))))))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2)))))))))) (C (A 0) (A 2))) (C (A 0) (A 4094)))

def tcP12 : Noun :=
  (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) tcProd))

def tcEdR : Noun :=
  (C (A 10) (C (C (A 4094) (C (A 0) (A 5))) (C (A 0) (A 1))))

def tcP11 : Noun :=
  (C (A 7) (C tcEdR tcP12))

def tcRe : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 511))))))

def tcP10 : Noun :=
  (C (A 8) (C tcRe tcP11))

def tcP9 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) tcP10))

def tcP8 : Noun :=
  (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) tcP9))

def tcEdT : Noun :=
  (C (A 10) (C (C (A 2046) (C (A 0) (A 5))) (C (A 0) (A 1))))

def tcP7 : Noun :=
  (C (A 7) (C tcEdT tcP8))

def tcRecT : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 123) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 11) (C (A 0) (A 0x1ffff)))) (C (A 9) (C (A 23) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 2043))) (C (A 0) (A 2))))))))) (C (A 10) (C (C (A 60) (C (A 0) (A 13))) (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 9) (C (A 46) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 126)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 3)))))) (C (A 0) (A 2))))))))) (C (A 0) (A 15))))))))))))

def tcP6 : Noun :=
  (C (A 8) (C tcRecT tcP7))

def tcP5 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) tcP6))

def tcP4 : Noun :=
  (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) tcP5))

def tcEdH : Noun :=
  (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1))))

def tcP3 : Noun :=
  (C (A 7) (C tcEdH tcP4))

def tcRecH : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 123) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 11) (C (A 0) (A 0xffff)))) (C (A 9) (C (A 175) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 1019))) (C (A 0) (A 2))))))))) (C (A 10) (C (C (A 60) (C (A 0) (A 4))) (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 9) (C (A 46) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 62)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 2)))))) (C (A 0) (A 2))))))))) (C (A 0) (A 7))))))))))))

def tcP2 : Noun :=
  (C (A 8) (C tcRecH tcP3))

def tcP1 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) tcP2))

def tcPair : Noun :=
  (C (A 8) (C (C (A 0) (A 124)) tcP1))

def tcNone : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 63)))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (C (C (A 1) (A 0x6d6d69)) (C (C (A 0) (A 1015)) (C (A 0) (A 2)))) (C (A 1) (A 0))) (C (A 0) (A 2))) (C (A 0) (A 510)))))))))))

def tcBoth : Noun :=
  (C (C (C (A 1) (A 0)) (C (A 0) (A 498))) (C (A 0) (A 254)))

def tcThis : Noun :=
  (C (C (C (A 1) (A 0)) (C (A 0) (A 249))) (C (A 0) (A 254)))

def tcIsNone : Noun :=
  (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 248))))

def tcIsBoth : Noun :=
  (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 248))))

def tcIsThis : Noun :=
  (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 248))))

def tcHit : Noun :=
  (C (C (C (A 1) (A 0)) (C (A 0) (A 5))) (C (A 0) (A 254)))

def tcNC : Noun :=
  (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 1) (A 1)) (C (A 1) (A 0)))))

def tcGet : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 764) (C (A 10) (C (C (A 6) (C (A 0) (A 250))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2))))))))

def tcM3 : Noun :=
  (C (A 6) (C tcIsNone (C tcNone tcPair)))

def tcM2 : Noun :=
  (C (A 6) (C tcIsBoth (C tcBoth tcM3)))

def tcMiss : Noun :=
  (C (A 6) (C tcIsThis (C tcThis tcM2)))

def tcT1 : Noun :=
  (C (A 6) (C tcNC (C tcMiss tcHit)))

def tcTrap : Noun :=
  (C (A 8) (C tcGet tcT1))

def tcBunt : Noun :=
  (C (C (A 0x656e6f6e) (A 0)) (C (A 0) (C (A 1) (A 0))))

def tcBat : Noun :=
  (C (A 8) (C (C (A 1) (A 1)) (C (A 8) (C (C (A 1) tcTrap) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))

def tcArm : Noun :=
  (C (A 8) (C (C (A 1) tcBunt) (C (C (A 1) tcBat) (C (A 0) (A 1)))))

-- END softcons

theorem tc_at : slot? 12 comp.door = some tcArm := by kernel_rfl

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {ctx : Noun} (x : GenRest)

/-- The subject of the trap of `+soft-cons`. -/
abbrev tcS (ned : Need) (axe : Nat) (TOM : Noun) (k : Sock) (g : Gen (TreapMap mugF)) (x : GenRest)
    (ctx : Noun) : Noun :=
  C tcTrap (C (A axe) (C tcBat (C (C ned.toNoun (C TOM k.toNoun)) (compCore g x ctx))))

/-- The statement of the trap at one need. -/
def TcAt (ctx : Noun) (x : GenRest) (TOM : Noun) (tom : List (Nat × Nat)) (ned : Need) : Prop :=
  ∀ (axe : Nat) (k : Sock) (g : Gen (TreapMap mugF)), 1 ≤ axe →
    nock (tcS ned axe TOM k g x ctx) tcTrap
      = (softConsM tom ned axe k g).map fun p => C (tpKR p.1.1 p.1.2) (genNoun p.2 x)

/-- The library core at axis `255` of the context of the final pass. -/
theorem tc_memD_lib (SCC LONG JH ML TOP B : Noun) : slot? 255 (memDCtx SCC LONG JH ML TOP B) = some lib := by
  have h := compK_lib
  simp only [memDCtx]
  generalize compK = K at h ⊢
  rw [← h]
  rfl

/-- **`(~(get by tops) axe)`**. -/
theorem tc_get (hc : CompIn ctx) {TOM : Noun} {tom : List (Nat × Nat)} (hT : AxsRel TOM tom) (ned : Need)
    (axe : Nat) (k : Sock) (g : Gen (TreapMap mugF)) :
    nock (tcS ned axe TOM k g x ctx) tcGet
      = some (match tom.lookup axe with | some r => C (A 0) (A r) | Option.none => A 0) := by
  have hgc : SomeIn layer2 ∧ GorIn mugF layer2 := ⟨someIn_layer2, gorIn_morIn_layer2.1⟩
  simp only [tcS, compCore]
  generalize comp.door = Dr
  generalize tcTrap = TR
  generalize tcBat = TB
  cases hl : tom.lookup axe with
  | none =>
    have hg := get_gate layer2 hgc (A axe) TOM _ (axsRel_get_none hT hl)
    simp [nock_exec, tcGet, hc, by_arm, by.arm_at, by.get.arm_at, get_arm, hg]
  | some q =>
    have hg := get_gate layer2 hgc (A axe) TOM _ (axsRel_get_some hT hl)
    simp [nock_exec, tcGet, hc, by_arm, by.arm_at, by.get.arm_at, get_arm, hg]

/-- The trap: `(~(get by tops) axe)` pushed, then the `?^`. -/
theorem tc_trap (hc : CompIn ctx) {TOM : Noun} {tom : List (Nat × Nat)} (hT : AxsRel TOM tom) (ned : Need)
    (axe : Nat) (k : Sock) (g : Gen (TreapMap mugF)) :
    nock (tcS ned axe TOM k g x ctx) tcTrap
      = nock (C (match tom.lookup axe with | some r => C (A 0) (A r) | Option.none => A 0)
          (tcS ned axe TOM k g x ctx)) tcT1 := by
  have h := tc_get x hc hT ned axe k g
  conv => { lhs; arg 2; unfold tcTrap }
  simp only [tcS, compCore] at h ⊢
  generalize comp.door = Dr at h ⊢
  simp only [nock_exec, h, Option.bind_some]

/-- **A hit in `tops`**: `[[~ u.t] gen]`. -/
theorem tc_hit (ned : Need) (axe : Nat) (TOM : Noun) (k : Sock) (g : Gen (TreapMap mugF)) (r : Nat) :
    nock (C (C (A 0) (A r)) (tcS ned axe TOM k g x ctx)) tcT1 = some (C (tpKR [] r) (genNoun g x)) := by
  simp only [tcS, compCore]
  generalize comp.door = Dr
  generalize tcTrap = TR
  generalize tcBat = TB
  simp [nock_exec, tcT1, tcNC, tcHit, listNoun]

/-- **`%this`**: `[[~ r.ned] gen]`. -/
theorem tc_this (axe : Nat) (TOM : Noun) (k : Sock) (g : Gen (TreapMap mugF)) (r : Nat) :
    nock (C (A 0) (tcS (Need.this r) axe TOM k g x ctx)) tcT1 = some (C (tpKR [] r) (genNoun g x)) := by
  simp only [tcS, compCore]
  generalize comp.door = Dr
  generalize tcTrap = TR
  generalize tcBat = TB
  simp [nock_exec, tcT1, tcNC, tcMiss, tcIsThis, tcThis, Need.toNoun, Tag.this, listNoun]

/-- **`%both`**: `[[~ r.ned] gen]`. -/
theorem tc_both (axe : Nat) (TOM : Noun) (k : Sock) (g : Gen (TreapMap mugF)) (r : Nat) (h t : Need) :
    nock (C (A 0) (tcS (Need.both r h t) axe TOM k g x ctx)) tcT1 = some (C (tpKR [] r) (genNoun g x)) := by
  simp only [tcS, compCore]
  generalize comp.door = Dr
  generalize tcTrap = TR
  generalize tcBat = TB
  simp [nock_exec, tcT1, tcNC, tcMiss, tcIsThis, tcM2, tcIsBoth, tcBoth, Need.toNoun, Tag.this, Tag.both,
    listNoun]

/-- **`%none`**: `=^  r  gen  re`, then `[[[%imm +.k r]~ r] gen]` (a crash on `%void`). -/
theorem tc_none (axe : Nat) (TOM : Noun) (k : Sock) (g : Gen (TreapMap mugF)) :
    nock (C (A 0) (tcS Need.none axe TOM k g x ctx)) tcT1
      = (match k with
          | Sock.mk _ d => some (C (tpKR [Pole.imm d g.re] g.re) (genNoun { g with re := g.re + 1 } x))
          | Sock.void => Option.none) := by
  have hD := comp_re_at
  have hre := comp_re' ctx x g
  simp only [tcS, compCore] at hre ⊢
  generalize comp.door = Dr at hD hre ⊢
  generalize tcTrap = TR
  generalize tcBat = TB
  cases k with
  | void =>
    simp [nock_exec, tcT1, tcNC, tcMiss, tcIsThis, tcM2, tcIsBoth, tcM3, tcIsNone, tcNone, Need.toNoun,
      Tag.this, Tag.both, Tag.none, hD, hre, Sock.toNoun, Tag.void]
  | mk c d =>
    simp [nock_exec, tcT1, tcNC, tcMiss, tcIsThis, tcM2, tcIsBoth, tcM3, tcIsNone, tcNone, Need.toNoun,
      Tag.this, Tag.both, Tag.none, hD, hre, Sock.toNoun, listNoun, Pole.toNoun, Tag.imm]

/-! ## The cell -/

/-- The subject after `=/  [h=need t=need]  ned`. -/
abbrev tcT2 (h t : Need) (axe : Nat) (TOM : Noun) (k : Sock) (g : Gen (TreapMap mugF)) (x : GenRest)
    (ctx : Noun) : Noun :=
  C (C h.toNoun t.toNoun) (C (A 0) (tcS (Need.pair h t) axe TOM k g x ctx))

/-- **A cell**: the tests fail, `=/  [h t]  ned`. -/
theorem tc_pdisp (h t : Need) (axe : Nat) (TOM : Noun) (k : Sock) (g : Gen (TreapMap mugF)) :
    nock (C (A 0) (tcS (Need.pair h t) axe TOM k g x ctx)) tcT1 = nock (tcT2 h t axe TOM k g x ctx) tcP1 := by
  obtain ⟨a, b, hh⟩ := need_cell h
  simp only [tcT2, tcS, compCore]
  generalize comp.door = Dr
  generalize tcTrap = TR
  generalize tcBat = TB
  simp [nock_exec, tcT1, tcNC, tcMiss, tcIsThis, tcM2, tcIsBoth, tcM3, tcIsNone, tcPair, Need.toNoun, hh, eqCode]

/-- **The `=^` of the head**: the trap on `h` at `(peg axe 2)` with `(hed:so k)`, `gen` replaced. -/
theorem tc_pH (hc : CompIn ctx) (hl : slot? 255 ctx = some lib) (h t : Need) (axe : Nat) (ha : 1 ≤ axe)
    (TOM : Noun) (k : Sock) (g : Gen (TreapMap mugF)) (o : Option ((List Pole × Nat) × Gen (TreapMap mugF)))
    (hrun : nock (tcS h (Hoon.pegF axe 2) TOM (So.hed k) g x ctx) tcTrap
      = o.map fun p => C (tpKR p.1.1 p.1.2) (genNoun p.2 x)) :
    nock (tcT2 h t axe TOM k g x ctx) tcP1
      = o.bind fun p => nock (C (tpKR p.1.1 p.1.2) (tcT2 h t axe TOM k p.2 x ctx)) tcP5 := by
  have hl1 := cf_layer1 hc
  have hp := peg_gate layer1 cf_arith axe ha 2 (by omega)
  have hhed := so_hed_gate (C so.battery lib) k
  simp only [tcT2, tcS, compCore] at hrun ⊢
  generalize comp.door = Dr at hrun ⊢
  generalize tcTrap = TR at hrun ⊢
  generalize tcBat = TB at hrun ⊢
  cases o with
  | none =>
    simp only [Option.map_none] at hrun
    simp [nock_exec, tcP1, tcP2, tcP3, tcP4, tcRecH, tcEdH, hl, hl1, peg_arm, peg.arm_at, hp, so.lib.arm_at,
      so_lib_arm, so.hed.arm_at, so_hed_arm, hhed, hrun]
  | some p =>
    simp only [Option.map_some] at hrun
    simp [nock_exec, tcP1, tcP2, tcP3, tcP4, tcRecH, tcEdH, hl, hl1, peg_arm, peg.arm_at, hp, so.lib.arm_at,
      so_lib_arm, so.hed.arm_at, so_hed_arm, hhed, hrun]

/-- **The `=^` of the tail**: the trap on `t` at `(peg axe 3)` with `(tel:so k)`, `gen` replaced. -/
theorem tc_pT (hc : CompIn ctx) (hl : slot? 255 ctx = some lib) (h t : Need) (axe : Nat) (ha : 1 ≤ axe)
    (TOM : Noun) (k : Sock) (g : Gen (TreapMap mugF)) (oh : List Pole) (rh : Nat)
    (o : Option ((List Pole × Nat) × Gen (TreapMap mugF)))
    (hrun : nock (tcS t (Hoon.pegF axe 3) TOM (So.tel k) g x ctx) tcTrap
      = o.map fun p => C (tpKR p.1.1 p.1.2) (genNoun p.2 x)) :
    nock (C (tpKR oh rh) (tcT2 h t axe TOM k g x ctx)) tcP5
      = o.bind fun p => nock (C (tpKR p.1.1 p.1.2) (C (tpKR oh rh) (tcT2 h t axe TOM k p.2 x ctx))) tcP9 := by
  have hl1 := cf_layer1 hc
  have hp := peg_gate layer1 cf_arith axe ha 3 (by omega)
  have htel := so_tel_gate (C so.battery lib) k
  simp only [tcT2, tcS, tpKR, compCore] at hrun ⊢
  generalize comp.door = Dr at hrun ⊢
  generalize tcTrap = TR at hrun ⊢
  generalize tcBat = TB at hrun ⊢
  generalize listNoun Pole.toNoun oh = OH
  cases o with
  | none =>
    simp only [Option.map_none] at hrun
    simp [nock_exec, tcP5, tcP6, tcP7, tcP8, tcRecT, tcEdT, hl, hl1, peg_arm, peg.arm_at, hp, so.lib.arm_at,
      so_lib_arm, so.tel.arm_at, so_tel_arm, htel, hrun]
  | some p =>
    simp only [Option.map_some] at hrun
    simp [nock_exec, tcP5, tcP6, tcP7, tcP8, tcRecT, tcEdT, hl, hl1, peg_arm, peg.arm_at, hp, so.lib.arm_at,
      so_lib_arm, so.tel.arm_at, so_tel_arm, htel, hrun]

/-- **`re` and the product**: `[[:(weld oh ot [%con rh rt r]~) r] gen]`. -/
theorem tc_pR (hc : CompIn ctx) (h t : Need) (axe : Nat) (TOM : Noun) (k : Sock) (g : Gen (TreapMap mugF))
    (oh ot : List Pole) (rh rt : Nat) :
    nock (C (tpKR ot rt) (C (tpKR oh rh) (tcT2 h t axe TOM k g x ctx))) tcP9
      = some (C (tpKR (oh ++ ot ++ [Pole.con rh rt g.re]) g.re) (genNoun { g with re := g.re + 1 } x)) := by
  have hD := comp_re_at
  have hre := comp_re' ctx x g
  have hw1 := weld_gate_list layer2 (ot.map Pole.toNoun) [(Pole.con rh rt g.re).toNoun]
  have hw2 := weld_gate_list layer2 (oh.map Pole.toNoun) (ot.map Pole.toNoun ++ [(Pole.con rh rt g.re).toNoun])
  simp only [tcT2, tcS, tpKR, compCore, cd_listNoun_listN] at hre ⊢
  generalize comp.door = Dr at hD hre ⊢
  generalize tcTrap = TR
  generalize tcBat = TB
  simp [listN, Pole.toNoun, Tag.con, List.map_append] at hw1 hw2
  simp [nock_exec, tcP9, tcP10, tcP11, tcP12, tcRe, tcEdR, tcProd, hD, hre, hc, weld_arm, weld.arm_at, hw1, hw2,
    listN, Pole.toNoun, Tag.con, List.map_append]

/-! ## The trap on every need, the gate -/

/-- **The trap on a cell `[h t]`**, from the trap on `h` and on `t`. -/
theorem tc_pair (hc : CompIn ctx) (hl : slot? 255 ctx = some lib) {TOM : Noun} {tom : List (Nat × Nat)}
    (hT : AxsRel TOM tom) (h t : Need) (ih_h : TcAt ctx x TOM tom h) (ih_t : TcAt ctx x TOM tom t) :
    TcAt ctx x TOM tom (Need.pair h t) := by
  intro axe k g ha
  simp only [softConsM]; rw [tc_trap x hc hT]
  cases hl' : tom.lookup axe with
  | some r =>
    simp only
    rw [tc_hit]
    simp [pure, StateT.pure]
  | none =>
    simp only
    rw [tc_pdisp]
    have h2 : 1 ≤ Hoon.pegF axe 2 := by simp [Hoon.pegF]; omega
    have h3 : 1 ≤ Hoon.pegF axe 3 := by simp [Hoon.pegF]
    rw [tc_pH x hc hl h t axe ha TOM k g _ (ih_h _ (So.hed k) g h2)]
    cases e1 : softConsM tom h (Hoon.pegF axe 2) (So.hed k) g with
    | none => simp [bind, StateT.bind, e1]
    | some p =>
      obtain ⟨⟨oh, rh⟩, g1⟩ := p
      simp only [Option.bind_some]
      rw [tc_pT x hc hl h t axe ha TOM k g1 oh rh _ (ih_t _ (So.tel k) g1 h3)]
      cases e2 : softConsM tom t (Hoon.pegF axe 3) (So.tel k) g1 with
      | none => simp [bind, StateT.bind, e1, e2]
      | some q =>
        obtain ⟨⟨ot, rt⟩, g2⟩ := q
        simp only [Option.bind_some]
        rw [tc_pR x hc]
        simp [bind, StateT.bind, e1, e2, re, pure, StateT.pure]

/-- **The trap of `+soft-cons`** is `softConsM` on every need. -/
theorem tc_loop (hc : CompIn ctx) (hl : slot? 255 ctx = some lib) {TOM : Noun} {tom : List (Nat × Nat)}
    (hT : AxsRel TOM tom) : ∀ ned : Need, TcAt ctx x TOM tom ned
  | Need.none => by
    intro axe k g ha
    simp only [softConsM]; rw [tc_trap x hc hT]
    cases hl' : tom.lookup axe with
    | some r => simp only; rw [tc_hit]; simp [pure, StateT.pure]
    | none =>
      simp only
      rw [tc_none]
      cases k <;> simp [bind, StateT.bind, re, pure, StateT.pure, crashM]
  | Need.this r => by
    intro axe k g ha
    simp only [softConsM]; rw [tc_trap x hc hT]
    cases hl' : tom.lookup axe with
    | some r' => simp only; rw [tc_hit]; simp [pure, StateT.pure]
    | none => simp only; rw [tc_this]; simp [pure, StateT.pure]
  | Need.both r h t => by
    intro axe k g ha
    simp only [softConsM]; rw [tc_trap x hc hT]
    cases hl' : tom.lookup axe with
    | some r' => simp only; rw [tc_hit]; simp [pure, StateT.pure]
    | none => simp only; rw [tc_both]; simp [pure, StateT.pure]
  | Need.pair h t => tc_pair x hc hl hT h t (tc_loop hc hl hT h) (tc_loop hc hl hT t)

/-- **The gate `+soft-cons`** on `[ned tom k]`, `tom` a map `AxsRel TOM tom`: `softConsM tom ned 1 k`. -/
theorem tc_gate (hc : CompIn ctx) (hl : slot? 255 ctx = some lib) {TOM : Noun} {tom : List (Nat × Nat)}
    (hT : AxsRel TOM tom) (ned : Need) (k : Sock) (g : Gen (TreapMap mugF)) :
    nock (C tcBat (C (C ned.toNoun (C TOM k.toNoun)) (compCore g x ctx))) tcBat
      = (softConsM tom ned 1 k g).map fun p => C (tpKR p.1.1 p.1.2) (genNoun p.2 x) := by
  have hl' := tc_loop x hc hl hT ned 1 k g (Nat.le_refl 1)
  conv => { lhs; arg 2; unfold tcBat }
  simp only [tcS] at hl'
  simp only [nock_exec]
  exact hl'

/-- The arm `+soft-cons` builds its gate. -/
theorem tc_arm (d : Noun) : nock d tcArm = some (C tcBat (C tcBunt d)) := by
  unfold tcArm; simp only [nock_exec]

/-- **The push `[kon rub]`** of the try path (`tpY2` .. `tpY5`, `=^  [kon rub]  gen  (soft-cons ned.s tom
less.b.s)`): on to `tpY6` with `[kon rub]` in front and `gen` replaced (the subject `tzS` of
`CompSccLoopSoftTryPes.lean`). -/
theorem tc_push (hc : CompIn ctx) (hl : slot? 255 ctx = some lib) {TOM : Noun} {tom : List (Nat × Nat)}
    (hT : AxsRel TOM tom) (FLAG LAT HD TR OPS CUT AXS : Noun) (o : Nat) (s : SoftCall)
    (g : Gen (TreapMap mugF)) :
    nock (C TOM (C FLAG (C LAT (tpS0 HD TR OPS CUT AXS o s g x ctx)))) tpY2
      = (softConsM tom s.ned 1 s.b.less g).bind fun p =>
          nock (C (tpKR p.1.1 p.1.2) (C TOM (C FLAG (C LAT (tpS0 HD TR OPS CUT AXS o s p.2 x ctx))))) tpY6 := by
  have hD := tc_at
  have hG := tc_gate x hc hl hT s.ned s.b.less g
  conv => { lhs; arg 2; unfold tpY2 tpY3 tpY4 tpY5 tpYH3 tpYH4 }
  simp only [tpS0, seS0, compCore, tpKR] at hG ⊢
  generalize comp.door = Dr at hD hG ⊢
  cases e : softConsM tom s.ned 1 s.b.less g with
  | none =>
    rw [e] at hG
    simp only [Option.map_none] at hG
    simp [nock_exec, hD, tc_arm, Compiler.SoftCall.toNoun, Bell.toNoun, hG]
  | some p =>
    rw [e] at hG
    simp only [Option.map_some] at hG
    simp [nock_exec, hD, tc_arm, Compiler.SoftCall.toNoun, Bell.toNoun, hG]

end Compiler
end Formalization
