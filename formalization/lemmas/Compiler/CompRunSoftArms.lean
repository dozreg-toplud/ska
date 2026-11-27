import lemmas.Compiler.CompSccLoopSoft
import lemmas.Compiler.CompMedeLink
import lemmas.Compiler.CompForlLink
import lemmas.Hoon.DelBy

/-! # `+soft-new` and `+soft-bond` in the pill (README Gaps 19 (g), track K)

The two arms of the door of `+comp` that a soft direct call of `+run` runs before its
sub-runs (lines 4005 to 4047): **`+soft-new`** (line 5196, door axis `254`, 71 cells) puts the
entry `[kin b rin ned sur o o o pro out aux ~]` at the block `o` of the call into
`soft.gen`; **`+soft-bond`** (line 5212, door axis `442`, 296 cells) emits the three hops
`h -> o -> l -> then.nex`, tags `o`, and moves the entry of `there.then.nex` to `o` with
`head` `h` and `last` `l` (`+got:by` crashes on a missing entry, the model is `none`).
Both are linked here against track I's `softNew` / `softBond` (`Ska/SccLoopSoft.lean`), at a
rest whose `soft` is `softMapNoun` of the model's map.  The arm nouns are written by
`tools/gen/softarms.py`. -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

def snBat : Noun :=
  (C (A 10) (C (C (A 1022) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7dfe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 26)) (C (C (A 0) (A 54)) (C (C (A 0) (A 110)) (C (C (A 0) (A 222)) (C (C (A 0) (A 446)) (C (C (A 0) (A 12)) (C (C (A 0) (A 12)) (C (C (A 0) (A 12)) (C (C (A 0) (A 894)) (C (C (A 0) (A 1790)) (C (C (A 0) (A 1791)) (C (A 1) (A 0))))))))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 30))))

def snArm : Noun :=
  (C (A 8) (C (C (A 1) (C (A 0) (C (A 0x6e61656d) (C (C (C (A 1) (A 0)) (C (A 0) (A 0))) (C (A 0) (C (C (A 0x656e6f6e) (A 0)) (C (C (A 0x656e6f6e) (A 0)) (C (A 0) (C (A 0) (A 0)))))))))) (C (C (A 1) snBat) (C (A 0) (A 1)))))

def sbBat : Noun :=
  (C (A 8) (C (C (A 0) (A 103)) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (A 0) (A 243)))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 6))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 6))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 8) (C (C (A 9) (C (A 0x555de) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 0) (A 509)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7fdfe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 62))) (C (A 0) (A 2)))))))) (C (A 7) (C (C (A 10) (C (C (A 0x7fdfe) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 190) (C (A 10) (C (C (A 6) (C (A 0) (A 0xffdfe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 126))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 30)) (C (A 7) (C (C (A 0) (A 3)) (C (A 10) (C (C (A 510) (C (A 0) (A 30))) (C (A 10) (C (C (A 254) (C (A 0) (A 6))) (C (A 0) (A 2)))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (C (C (A 1) (A 0x7478656e)) (C (C (C (A 1) (C (C (A 0x656e6f6e) (A 0)) (A 0))) (C (C (A 1) (A 0)) (C (C (C (A 0) (A 14)) (C (C (A 0) (A 4068)) (C (A 1) (C (A 0) (A 0))))) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 0) (A 6))))) (C (A 0) (A 1022)))))))))))))))))))))))))))))))))))

def sbArm : Noun :=
  (C (A 8) (C (C (A 1) (C (C (A 0x7478656e) (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))) (C (A 0) (A 0)))) (A 0))) (C (C (A 1) sbBat) (C (A 0) (A 1)))))


/-- `+soft-new` is at door axis `254`. -/
theorem comp_sn_at : slot? 254 comp.door = some snArm := by kernel_rfl

/-- `+soft-bond` is at door axis `442`. -/
theorem comp_sb_at : slot? 442 comp.door = some sbArm := by kernel_rfl

/-- The sample of `+soft-new`: `[o kin b rin ned sur pro out aux]`, `aux` `~`, the fields given as
nouns `E = [KIN B RIN NED SUR]` (`snEntry` puts them in the entry). -/
def snSample (o pro out : Nat) (KIN B RIN NED SUR : Noun) : Noun :=
  C (A o) (C KIN (C B (C RIN (C NED (C SUR (C (A pro) (C (A out) (A 0))))))))

/-- The entry `+soft-new` builds from its sample. -/
def snEntry (o pro out : Nat) (KIN B RIN NED SUR : Noun) : Noun :=
  C KIN (C B (C RIN (C NED (C SUR (C (A o) (C (A o) (C (A o) (C (A pro) (C (A out) (C (A 0) (A 0)))))))))))

/-- The nouns of the model's fields make the noun of the model's entry. -/
theorem snEntry_eq (o kin : Nat) (b : Bell) (rin : Option Noun) (ned : Need) (sur : NeedOrd) (pro out : Nat) :
    snEntry o pro out (A (if kin = 1 then 1818845556 else if kin = 0 then 1819042147 else 1851876717))
      b.toNoun (match rin with | none => A 0 | some r => C (A 0) r) ned.toNoun sur.toNoun
      = SoftCall.toNoun ⟨kin, b, rin, ned, sur, o, o, o, pro, out, []⟩ := rfl

variable {ctx} in
/-- **`+soft-new` is `softNew`**: on a rest whose `soft` is `softMapNoun gs.soft`, the gate of
`+soft-new` gives the noun of the model's `Gen` (unchanged) with `soft` the noun of its map. -/
theorem comp_soft_new (hc : CompIn ctx) (gs : GenSf (TreapMap mugF)) (x : GenRest)
    (hx : x.soft = softMapNoun gs.soft) (o kin : Nat) (b : Bell) (rin : Option Noun) (ned : Need)
    (sur : NeedOrd) (pro out : Nat) (KIN B RIN NED SUR : Noun)
    (hE : snEntry o pro out KIN B RIN NED SUR = SoftCall.toNoun ⟨kin, b, rin, ned, sur, o, o, o, pro, out, []⟩) :
    nock (C snBat (C (snSample o pro out KIN B RIN NED SUR) (compCore gs.g x ctx))) snBat
      = (softNew o kin b rin ned sur pro out gs).map fun p =>
          genNoun p.2.g { x with soft := softMapNoun p.2.soft } := by
  have hput := put_gate layer2 gorIn_morIn_layer2 (A o) _ _ _
    (putF_hoonMap SoftCall.toNoun gs.soft o ⟨kin, b, rin, ned, sur, o, o, o, pro, out, []⟩)
  rw [← hE] at hput
  obtain ⟨c, s, sofs⟩ := x
  simp only at hx
  subst hx
  simp only [snEntry] at hput
  nock_open snBat
  simp [nock_exec, genNoun, snSample, hc, by_arm, by.arm_at, by.put.arm_at, put_arm, hput, softNew,
    softMapNoun]

variable {ctx} in
/-- **`+soft-bond` is `softBond`**: on a rest whose `soft` is `softMapNoun gs.soft`, the gate of
`+soft-bond` gives the noun of the model's next and `Gen`, with `soft` the noun of its map: the
three hops, the tag of `o`, the entry of `there.then.nex` moved to `o` (`+got:by` crashes on a
missing entry, where the model is `none`). -/
theorem comp_soft_bond (hc : CompIn ctx) (gs : GenSf (TreapMap mugF)) (x : GenRest)
    (hx : x.soft = softMapNoun gs.soft) (nex : NextL CSet) (region : List Nat) :
    nock (C sbBat (C (C nex.goal.toNoun (listNoun A region)) (compCore gs.g x ctx))) sbBat
      = (softBond nex region gs).map fun p =>
          C p.1.goal.toNoun (genNoun p.2.g { x with soft := softMapNoun p.2.soft }) := by
  obtain ⟨g, sm⟩ := gs
  obtain ⟨⟨sr, fk, bd⟩, ⟨args, there⟩⟩ := nex
  have hgc : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
    ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
  have he1 := cf_emit (x := x) hc g ⟨[], [], Termin.hop ⟨args, there⟩⟩
  have he2 := cf_emit (x := x) hc (cfEmitG ⟨[], [], Termin.hop ⟨args, there⟩⟩ g)
    ⟨[], [], Termin.hop (jmp0 g.bo)⟩
  have he3 := cf_emit (x := x) hc (cfEmitG ⟨[], [], Termin.hop (jmp0 g.bo)⟩
    (cfEmitG ⟨[], [], Termin.hop ⟨args, there⟩⟩ g)) ⟨[], [], Termin.hop (jmp0 (g.bo + 1))⟩
  have hst := comp_set_tag x hc (cfEmitG ⟨[], [], Termin.hop (jmp0 (g.bo + 1))⟩
    (cfEmitG ⟨[], [], Termin.hop (jmp0 g.bo)⟩ (cfEmitG ⟨[], [], Termin.hop ⟨args, there⟩⟩ g))) (g.bo + 1) region
  simp only [Blob.toNoun, listNoun, Termin.toNoun, Tag.hop, Jmp.toNoun, jmp0] at he1 he2 he3
  have hD2 := comp_emit_at
  have hD3 := comp_set_tag_at
  have hget := getF_hoonMap SoftCall.toNoun sm there
  obtain ⟨c0, s0, sofs⟩ := x
  simp only at hx
  subst hx
  simp only [compCore] at hst he1 he2 he3 ⊢
  generalize comp.door = Dr at hD2 hD3 he1 he2 he3 hst ⊢
  nock_open sbBat
  cases e : HoonMap.get sm there with
  | none =>
    rw [e] at hget
    have hgot := got_gate_nil layer2 hgc (A there) _ hget
    cases hd : g.drop <;>
    simp only [genNoun, softMapNoun, cfEmitG, hd, ↓reduceIte, Bool.false_eq_true, setTag, Option.map, jmp0]
      at he1 he2 he3 hst <;>
    simp [nock_exec, NextL.goal, CGoalL.toNoun, Jmp.toNoun, listNoun, hD2, hD3, comp_emit_arm, he1, he2, he3,
      comp_set_tag_arm, hst, softBond, liftS, cf_emit_g, setTag, bind, StateT.bind, pure, StateT.pure,
      cfEmitG, hd, genNoun, softMapNoun, hc, by_arm, by.arm_at, by.got.arm_at, got_arm, hgot, e, jmp0]
  | some c =>
    rw [e] at hget
    have hgot := got_gate layer2 hgc (A there) _ _ hget
    have hdel := del_gate layer2 gorIn_morIn_layer2 (A there) _ _ (delF_hoonMap SoftCall.toNoun sm there)
    have hput := put_gate layer2 gorIn_morIn_layer2 (A (g.bo + 1)) _ _ _
      (putF_hoonMap SoftCall.toNoun (HoonMap.del sm there) (g.bo + 1) { c with head := g.bo + 1 + 1, last := g.bo })
    simp only [SoftCall.toNoun] at hput hgot
    cases hd : g.drop <;>
    simp only [genNoun, softMapNoun, cfEmitG, hd, ↓reduceIte, Bool.false_eq_true, setTag, Option.map, jmp0]
      at he1 he2 he3 hst <;>
    simp [nock_exec, NextL.goal, CGoalL.toNoun, Jmp.toNoun, listNoun, hD2, hD3, comp_emit_arm, he1, he2, he3,
      comp_set_tag_arm, hst, softBond, liftS, cf_emit_g, setTag, bind, StateT.bind, pure, StateT.pure,
      cfEmitG, hd, genNoun, softMapNoun, hc, by_arm, by.arm_at, by.got.arm_at, got_arm, hgot, e, jmp0,
      by.del.arm_at, del_arm, hdel, by.put.arm_at, put_arm, hput, Lazy.toNoun, Lazy.forksNoun,
      Lazy.bondsNoun, Sure.toNoun, Sure.bunt, Need.toNoun, Tag.none, HoonSet.toNoun_empty, Lazy.ofSure]

end Compiler
end Formalization
