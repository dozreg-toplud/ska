import lemmas.Compiler.OptLinkHelpers

/-!
# `+remove-useless-branching` linked

```hoon
++  remove-useless-branching
  ~%  %remove-useless-branching  ..ride  ~
  |=  blocks=(map @uwoo blob)
  ^-  [changed=? (map @uwoo blob)]
  %-  ~(rep by blocks)
  |=  [[o=@uwoo b=blob] changed=_| new=(map @uwoo blob)]
  =;  [epilogue=(list pole) new-fin=termin]
    :-  |(changed !=(new-fin fin.b))
    (~(put by new) o b(body (weld body.b epilogue), fin new-fin))
  ?+  -.fin.b  `fin.b
    %clq  ...  %eqq  ...  %brz  ...  %brn  ...
  ==
```

The arm is `363` of `optC` (`rub_at`, its nouns written by
`tools/gen/optlink.py rub`): the body `rubBody` pushes the door `~(rep by
blocks)` from `layer2` and slams its gate `rubGate` with the bunt `rubGBunt`,
whose accumulator `[| ~]` is the noun of `(false, ∅)`.  The gate is the
`?+` over the terminator (`rubSw`, `[epilogue new-fin]`, a crash on a failed
`?>` or a missing block) and then the new flag and the `+put:by` of the new
block (`rubRest`).

* `rub_sw`: the `?+` is `rubFin` of `Ska/OptBranch.lean`; the Hoon compares
  the two target blocks as nouns, `rubFin` as values, the same by
  `blob_toNoun_inj`.
* `rub_rest`: the flag `|(changed !=(new-fin fin.b))` (with
  `termin_toNoun_inj`) and the `+put:by` (`put_gate`, `weld_gate_list`).
* `rub_step`: the gate on a pair `(o, b)` and an accumulator `(ch, new)` is
  `rubG`, the step of the model's fold read on the pair.
* `rub_gate`: **the gate of `+remove-useless-branching` on the noun of a
  treap of blocks is `removeUselessBranching`** on the instance `TreapMap
  mugF` with the keys of `rap` (`optMapKeys`), the order of `+rep:by`,
  crashes included (`none`), for every map of blocks, `%lti` included (the
  `?+` sends it to its default, as `rubFin` does).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The nouns -/

/-- The `?+` over the terminator: `[epilogue new-fin]`. -/
def rubSw : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x716c63)) (C (A 0) (A 206)))) (C (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 1660)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 1662)))) (C (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 62))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 3709))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 126))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 7807))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 0) (A 6)) (C (A 0) (A 2)))) (C (C (C (A 1) (A 0x706f68)) (C (C (A 1) (A 0)) (C (A 0) (A 7805)))) (C (A 0) (A 487))))))))) (C (A 0) (A 0))))) (C (A 0) (A 0)))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x717165)) (C (A 0) (A 206)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 3324)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 3326)))) (C (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 62))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 7421))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 126))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 0x3cff))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 0) (A 6)) (C (A 0) (A 2)))) (C (C (C (C (C (A 1) (A 0x757165)) (C (C (A 0) (A 1950)) (C (A 0) (A 3902)))) (C (A 1) (A 0))) (C (C (A 1) (A 0x706f68)) (C (C (A 1) (A 0)) (C (A 0) (A 0x3cfd))))) (C (C (A 1) (A 0)) (C (A 0) (A 487)))))))))) (C (A 0) (A 0))))) (C (A 0) (A 0))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x7a7262)) (C (A 0) (A 206)))) (C (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 1660)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 1662)))) (C (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 62))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 3709))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 126))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 7807))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 0) (A 6)) (C (A 0) (A 2)))) (C (C (C (A 1) (A 0x706f68)) (C (C (A 1) (A 0)) (C (A 0) (A 7805)))) (C (A 0) (A 487))))))))) (C (A 0) (A 0))))) (C (A 0) (A 0)))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6e7262)) (C (A 0) (A 206)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 1660)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 1662)))) (C (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 62))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 3709))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 126))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 7807))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 0) (A 6)) (C (A 0) (A 2)))) (C (C (C (C (C (A 1) (A 0x626f6c)) (C (A 0) (A 1950))) (C (A 1) (A 0))) (C (C (A 1) (A 0x706f68)) (C (C (A 1) (A 0)) (C (A 0) (A 7805))))) (C (C (A 1) (A 0)) (C (A 0) (A 487)))))))))) (C (A 0) (A 0))))) (C (A 0) (A 0))))) (C (A 11) (C (C (A 0x73736f74) (C (A 1) (A 0))) (C (C (A 1) (A 0)) (C (A 0) (A 103)))))))))))))))))

/-- The new flag and the `+put:by` of the new block. -/
def rubRest : Noun :=
  (C (C (A 6) (C (C (A 0) (A 58)) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 5)) (C (A 0) (A 231)))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 123))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 120)) (C (A 7) (C (C (A 0) (A 3)) (C (A 10) (C (C (A 3) (C (C (A 8) (C (C (A 9) (C (A 0xbef7f4) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 486)) (C (A 0) (A 12)))) (C (A 0) (A 2)))))))) (C (A 0) (A 5)))) (C (A 0) (A 57)))))))) (C (A 0) (A 2)))))))))

/-- The gate of the `+rep:by` of `+remove-useless-branching`. -/
def rubGate : Noun :=
  (C (A 8) (C rubSw rubRest))

/-- The sample bunt of that gate, `[[0 *blob] | ~]`. -/
def rubGBunt : Noun :=
  (C (C (A 0) (C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0))))) (C (A 1) (A 0)))

/-- The gate body of `+remove-useless-branching`. -/
def rubBody : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffff)))) (C (A 9) (C (A 767) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) rubGBunt) (C (C (A 1) rubGate) (C (A 0) (A 1)))))))) (C (A 0) (A 2))))))))

/-- Its `%fast` hint. -/
def rubHint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x676e6968636e6172622d7373656c6573752d65766f6d6572) (C (C (A 0) (A 0xffff)) (A 0))))) (C (A 0) (A 1))))

/-- The arm `+remove-useless-branching`. -/
def rubArm : Noun := C (A 7) (C (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) rubBody) (C (A 0) (A 1))))) rubHint)

/-- `+remove-useless-branching` is arm `363` of `optC`. -/
theorem rub_at : slot? 363 optC = some rubArm := by kernel_rfl

@[nock_exec] theorem rub_arm (d : Noun) : nock d rubArm = some (C rubBody (C (A 0) d)) := by
  unfold rubArm rubHint; generalize rubBody = B; simp [nock_exec]

/-! ## The state of the fold -/

/-- The noun of the accumulator `[changed new]`. -/
def rubN (s : Bool × TreapMap mugF Blob) : Noun := C (flag s.1) (HoonMap.toNoun Blob.toNoun s.2)

/-- The step of the model's fold on a pair of `rap`. -/
def rubG (bl : TreapMap mugF Blob) (s : Bool × TreapMap mugF Blob) (p : Nat × Blob) :
    Option (Bool × TreapMap mugF Blob) :=
  (Opt.rubFin bl p.2.fin).map fun e => (s.1 || decide (e.2 ≠ p.2.fin), HoonMap.put s.2 p.1 (Opt.rubBlob p.2 e))

/-- The subject of the gate: `[rubGate [[[o b] acc] [rubBody [blocks optC]]]]`. -/
def rubSubj (BL : Noun) (o : Nat) (b : Blob) (ACC : Noun) : Noun :=
  C rubGate (C (C (C (A o) b.toNoun) ACC) (C rubBody (C BL optC)))

/-! ## The `?+` over the terminator -/

/-- The shared part of the four cases, on the noun: `?>` both sides pass
nothing, `got` of both targets, the test. -/
theorem rub_two (bl : TreapMap mugF Blob) (fin : Termin) (z o : Jmp) (epi : List Pole) :
    (Opt.rubTwo bl fin z o epi).map (fun e => C (listNoun Pole.toNoun e.1) e.2.toNoun)
      = if z.args = [] ∧ o.args = [] then
          ((HoonMap.get bl z.there).map Blob.toNoun).bind fun nz =>
          ((HoonMap.get bl o.there).map Blob.toNoun).map fun no =>
            if nz = no then C (listNoun Pole.toNoun epi) (Termin.hop ⟨[], z.there⟩).toNoun
            else C (listNoun Pole.toNoun []) fin.toNoun
        else none := by
  unfold Opt.rubTwo
  split
  · cases HoonMap.get bl z.there <;> cases HoonMap.get bl o.there <;> simp [blob_toNoun_inj]
    split <;> rfl
  · rfl

/-- **The `?+` over the terminator** is `rubFin`. -/
theorem rub_sw (bl : TreapMap mugF Blob) (o : Nat) (b : Blob) (ACC : Noun) :
    nock (rubSubj (HoonMap.toNoun Blob.toNoun bl) o b ACC) rubSw
      = (Opt.rubFin bl b.fin).map fun e => C (listNoun Pole.toNoun e.1) e.2.toNoun := by
  have hL := optC_layer2
  have hg := blocks_got bl
  obtain ⟨par, body, fin⟩ := b
  unfold rubSubj
  generalize optC = OC at hL
  generalize HoonMap.toNoun Blob.toNoun bl = BL at hg
  cases fin with
  | clq s z o =>
    obtain ⟨za, zt⟩ := z; obtain ⟨oa, ot⟩ := o
    dsimp only [Opt.rubFin]; rw [rub_two]
    cases za <;> cases oa <;>
      simp [nock_exec, rubSw, Blob.toNoun, Termin.toNoun, Jmp.toNoun, listNoun, Tag.clq, hL,
        by.arm_at, by_arm, by.got.arm_at, got_arm, hg]
    cases HoonMap.get bl zt <;> cases HoonMap.get bl ot <;> simp
    split <;> simp_all [nock_exec, blob_toNoun_inj, Tag.hop, Pole.toNoun, Tag.equ, Tag.lob, listNoun]
  | eqq l r z o =>
    obtain ⟨za, zt⟩ := z; obtain ⟨oa, ot⟩ := o
    dsimp only [Opt.rubFin]; rw [rub_two]
    cases za <;> cases oa <;>
      simp [nock_exec, rubSw, Blob.toNoun, Termin.toNoun, Jmp.toNoun, listNoun, Tag.clq, Tag.eqq, hL,
        by.arm_at, by_arm, by.got.arm_at, got_arm, hg]
    cases HoonMap.get bl zt <;> cases HoonMap.get bl ot <;> simp
    split <;> simp_all [nock_exec, blob_toNoun_inj, Tag.hop, Pole.toNoun, Tag.equ, Tag.lob, listNoun]
  | brz s z o =>
    obtain ⟨za, zt⟩ := z; obtain ⟨oa, ot⟩ := o
    dsimp only [Opt.rubFin]; rw [rub_two]
    cases za <;> cases oa <;>
      simp [nock_exec, rubSw, Blob.toNoun, Termin.toNoun, Jmp.toNoun, listNoun, Tag.clq, Tag.eqq, Tag.brz,
        hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg]
    cases HoonMap.get bl zt <;> cases HoonMap.get bl ot <;> simp
    split <;> simp_all [nock_exec, blob_toNoun_inj, Tag.hop, Pole.toNoun, Tag.equ, Tag.lob, listNoun]
  | brn s z o =>
    obtain ⟨za, zt⟩ := z; obtain ⟨oa, ot⟩ := o
    dsimp only [Opt.rubFin]; rw [rub_two]
    cases za <;> cases oa <;>
      simp [nock_exec, rubSw, Blob.toNoun, Termin.toNoun, Jmp.toNoun, listNoun, Tag.clq, Tag.eqq, Tag.brz,
        Tag.brn, hL, by.arm_at, by_arm, by.got.arm_at, got_arm, hg]
    cases HoonMap.get bl zt <;> cases HoonMap.get bl ot <;> simp
    split <;> simp_all [nock_exec, blob_toNoun_inj, Tag.hop, Pole.toNoun, Tag.equ, Tag.lob, listNoun]
  | _ =>
    simp [Opt.rubFin, nock_exec, rubSw, Blob.toNoun, Termin.toNoun, listNoun, Tag.clq, Tag.eqq, Tag.brz,
      Tag.brn, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti]

/-! ## The flag and the `+put:by` -/

/-- **The rest of the gate**: the flag `|(changed !=(new-fin fin.b))` and
the `+put:by` of `b(body (weld body.b epilogue), fin new-fin)`. -/
theorem rub_rest (bl : TreapMap mugF Blob) (o : Nat) (b : Blob) (ch : Bool) (new : TreapMap mugF Blob)
    (e : List Pole × Termin) :
    nock (C (C (listNoun Pole.toNoun e.1) e.2.toNoun)
        (rubSubj (HoonMap.toNoun Blob.toNoun bl) o b (rubN (ch, new)))) rubRest
      = some (rubN (ch || decide (e.2 ≠ b.fin), HoonMap.put new o (Opt.rubBlob b e))) := by
  have hL := optC_layer2
  have hp := putF_hoonMap Blob.toNoun new o (Opt.rubBlob b e)
  have hput := put_gate (mug := mugF) layer2 gorIn_morIn_layer2 (A o) _ _ _ hp
  have hw := weld_gate_list layer2 (b.body.map Pole.toNoun) (e.1.map Pole.toNoun)
  rw [← List.map_append, ← listNoun_map_listN, ← listNoun_map_listN, ← listNoun_map_listN] at hw
  obtain ⟨par, body, fin⟩ := b
  obtain ⟨epi, nf⟩ := e
  simp only [Opt.rubBlob, Blob.toNoun] at hput hw ⊢
  unfold rubSubj rubN
  generalize optC = OC at hL
  generalize HoonMap.toNoun Blob.toNoun bl = BL
  by_cases h : nf = fin
  · subst h
    cases ch <;>
      simp [nock_exec, rubRest, Blob.toNoun, hL, by.arm_at, by_arm, by.put.arm_at, put_arm, hput,
        weld.arm_at, weld_arm, hw, flag, termin_toNoun_inj]
  · cases ch <;>
      simp [nock_exec, rubRest, Blob.toNoun, hL, by.arm_at, by_arm, by.put.arm_at, put_arm, hput,
        weld.arm_at, weld_arm, hw, flag, termin_toNoun_inj, h]

/-! ## The gate of the `+rep:by` -/

/-- **The gate of the `+rep:by`** on a pair and an accumulator: `rubG`. -/
theorem rub_step (bl : TreapMap mugF Blob) (p : Nat × Blob) (s : Bool × TreapMap mugF Blob) :
    nock (C rubGate (C (C (Tr.pairNoun Blob.toNoun p) (rubN s))
        (C rubBody (C (HoonMap.toNoun Blob.toNoun bl) optC)))) rubGate
      = (rubG bl s p).map rubN := by
  obtain ⟨o, b⟩ := p
  obtain ⟨ch, new⟩ := s
  have hsw := rub_sw bl o b (rubN (ch, new))
  have hr := rub_rest bl o b ch new
  unfold rubSubj at hsw hr
  simp only [Tr.pairNoun]
  conv => lhs; arg 2; unfold rubGate
  rw [nock_op8, hsw]
  unfold rubG
  cases Opt.rubFin bl b.fin with
  | none => rfl
  | some e => simp only [Option.map_some, Option.bind_some]; exact hr e

/-! ## The gate -/

/-- The model's fold in the order of `rap`. -/
theorem rub_fold (bl : TreapMap mugF Blob) :
    Opt.removeUselessBranching bl = (TreapMap.rap bl).foldlM (fun s p => rubG bl s p) (false, HoonMap.empty) := by
  unfold Opt.removeUselessBranching
  rw [optKeys_eq]
  exact foldl_keys_rap bl (fun s k v => rubG bl s (k, v)) _ (rap_get bl) (some _)

/-- **`+remove-useless-branching`** on the noun of a treap of blocks: the
noun of `removeUselessBranching`, `[changed blocks]`, and a crash where the
model is `none`. -/
theorem rub_gate (bl : TreapMap mugF Blob) :
    nock (C rubBody (C (HoonMap.toNoun Blob.toNoun bl) optC)) rubBody
      = (Opt.removeUselessBranching bl).map rubN := by
  have hL := optC_layer2
  have ha : Tree (HoonMap.toNoun Blob.toNoun bl) := by
    rw [hoonMap_toNoun]; exact Tree.of_isMap (bl.2 Blob.toNoun)
  have hP : preorder (HoonMap.toNoun Blob.toNoun bl) = (TreapMap.rap bl).map (Tr.pairNoun Blob.toNoun) := by
    rw [hoonMap_toNoun]; exact TreapMap.preorder_toNoun Blob.toNoun bl
  have hrep := rep_gate_list (Tr.pairNoun Blob.toNoun) rubN (fun p s => rubG bl s p) by.battery layer2 rubGate
    (C (A 0) (C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0)))))
    (C rubBody (C (HoonMap.toNoun Blob.toNoun bl) optC)) _ ha _ hP (false, HoonMap.empty)
    (fun p _ s => rub_step bl p s)
  have hb : C (C (A 0) (C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0))))) (rubN (false, HoonMap.empty)) = rubGBunt := by
    simp [rubGBunt, rubN, flag, HoonMap.toNoun_empty]
  rw [hb] at hrep
  rw [rub_fold, ← hrep]
  conv => lhs; arg 2; unfold rubBody
  generalize HoonMap.toNoun Blob.toNoun bl = BL
  generalize rubGate = G
  generalize rubGBunt = GB
  generalize optC = OC at hL
  simp [nock_exec, hL, by.arm_at, by_arm, by.rep.arm_at, rep_arm]

end Compiler
end Formalization
