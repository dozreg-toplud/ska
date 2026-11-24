import lemmas.Compiler.OptLinkHelpers

/-!
# `+bb-topo` linked

```hoon
++  bb-topo
  ~%  %bb-topo  ..ride  ~
  |=  blocks=(map @uwoo blob)
  ^-  (list @uwoo)
  =|  saw=(set @uwoo)
  =|  out=(list @)
  =/  o=@uwoo  `@`0
  =<  -
  |-  ^-  [(list @uwoo) (set @uwoo)]
  =*  dfs-buc  $
  =.  saw  (~(put in saw) o)
  =<  [[o out] saw]
  ^-  [o=@uwoo out=(list @uwoo) saw=(set @uwoo)]
  :-  o
  %+  roll  (get-jmps fin:(~(got by blocks) o))
  |=  [[* o1=@uwoo] =_out =_saw]
  ?:  (~(has in saw) o1)  [out saw]
  dfs-buc(o o1, out out, saw saw)
```

The arm is `2942` of `optC` (`bb_at`, nouns by `tools/gen/optlink.py
bb`): the body pushes `saw`, `out` and `o` and runs the trap `dfs-buc`
(`bbTrap`), which puts `o` in `saw` (`bbPut`) and rolls the gate `bbRGate`
over `+get-jmps` of the terminator of the block `o` (`bbJmps`); the gate
kicks the trap again with `o`, `out` and `saw` edited.

The model `bbTopo fuel` (`Ska/OptTopo.lean`) bounds the depth of the walk by
the fuel, keeps `saw` as a list, and crashes (`none`) on a missing target.

* `saw_put`: `+put:in` of a label on `saw`.
* `bb_trap`: by induction on the fuel, wherever `dfs` returns, the trap
  returns `[out saw]` with the model's `out` and a set related to its `saw`
  (`roll_gate_rel` with the relation `BbRel` of the accumulator).
* `bb_gate`: **where `bbTopo fuel` returns `t` on a treap of blocks with no
  `%lti`, the gate of `+bb-topo` returns the noun of `t`.**  The converse
  (where the gate returns, some fuel makes the model return) is not proved:
  it needs the measure of the walk (each turn puts a new label in `saw`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The nouns -/

/-- The gate of the `+roll` over the jumps: skip a label in `saw`, else `dfs-buc`. -/
def bbRGate : Noun :=
  (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 381) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 57))) (C (A 0) (A 2)))))))) (C (C (C (A 0) (A 26)) (C (A 0) (A 27))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 27))) (C (A 10) (C (C (A 14) (C (A 0) (A 26))) (C (A 10) (C (C (A 6) (C (A 0) (A 25))) (C (A 0) (A 7)))))))))))))

/-- `(get-jmps fin:(~(got by blocks) o))`. -/
def bbJmps : Noun :=
  (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 1502) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 7) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 254))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 0) (A 7))))))) (C (A 0) (A 2))))))))))

/-- `(~(put in saw) o)`. -/
def bbPut : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 84) (C (A 10) (C (C (A 6) (C (A 0) (A 62))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2))))))))

/-- The trap `dfs-buc` of `+bb-topo`. -/
def bbTrap : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C (C (A 10) (C (C (A 30) bbPut) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 6)) (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C bbJmps (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (A 1) (C (A 0) (A 0))) (C (C (A 0) (A 14)) (C (A 0) (A 30)))) (C (C (A 1) bbRGate) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))) (C (C (C (A 0) (A 2)) (C (A 0) (A 6))) (C (A 0) (A 7)))))))))

/-- The gate body of `+bb-topo`. -/
def bbBody : Noun :=
  (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) (A 0)) (C (A 7) (C (C (A 8) (C (C (A 1) bbTrap) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (A 0) (A 2))))))))))

/-- Its sample bunt. -/
def bbBunt : Noun :=
  (A 0)

/-- Its `%fast` hint. -/
def bbHint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x6f706f742d6262) (C (C (A 0) (A 0xffff)) (A 0))))) (C (A 0) (A 1))))

/-- The arm `+bb-topo`. -/
def bbArm : Noun := C (A 7) (C (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) bbBody) (C (A 0) (A 1))))) bbHint)

/-- `+bb-topo` is arm `2942` of `optC`. -/
theorem bb_at : slot? 2942 optC = some bbArm := by kernel_rfl

@[nock_exec] theorem bb_arm (d : Noun) : nock d bbArm = some (C bbBody (C (A 0) d)) := by
  unfold bbArm bbHint; generalize bbBody = B; simp [nock_exec]

/-- `+put:in` of a label on `saw`. -/
theorem saw_put {S : Noun} {l : List Nat} (h : SawRel S l) (o : Nat) :
    ∃ S', nock (C in.put.battery (C (A o) (C in.battery (C S layer2)))) in.put.battery = some S' ∧
      SawRel S' (o :: l) := by
  obtain ⟨out, hp, hs, hh⟩ := putInF_spec mugF S (A o) h.1
  refine ⟨out, put_in_gate layer2 gorIn_morIn_layer2 (A o) S out hp, hs, fun k => ?_⟩
  rw [hh, h.2 k]
  simp

/-! ## The trap -/

/-- The subject of the trap: `[bbTrap [o [out [saw [bbBody [blocks optC]]]]]]`. -/
def bbT (o : Nat) (outN S BL : Noun) : Noun := C bbTrap (C (A o) (C outN (C S (C bbBody (C BL optC)))))

/-- The accumulator `[out saw]` of the `+roll` and the model's. -/
def BbRel (N : Noun) (s : List Nat × List Nat) : Prop := ∃ S, N = C (listNoun A s.1) S ∧ SawRel S s.2

/-- **The trap `dfs-buc`**: where `dfs` returns, the trap returns `[[o out]
saw]` with the model's `o :: out` and a set related to its `saw`. -/
theorem bb_trap (bl : TreapMap mugF Blob) (hl : NoLti bl) :
    ∀ (n o : Nat) (out saw : List Nat) (S : Noun), SawRel S saw → ∀ r, Opt.dfs bl n o (out, saw) = some r →
    ∃ S', nock (bbT o (listNoun A out) S (HoonMap.toNoun Blob.toNoun bl)) bbTrap
      = some (C (listNoun A r.1) S') ∧ SawRel S' r.2 := by
  intro n
  induction n with
  | zero => intro o out saw S hS r h; simp [Opt.dfs] at h
  | succ n ih =>
    intro o out saw S hS r h
    simp only [Opt.dfs] at h
    obtain ⟨b, hb, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r0, hr0, rfl⟩ := Option.map_eq_some_iff.mp h2
    have hfp : finPlain b.fin = true := hl o b hb
    obtain ⟨S1, hp1, hS1⟩ := saw_put hS o
    have hroll := roll_gate_rel Jmp.toNoun BbRel
      (fun j acc => if j.there ∈ acc.2 then some acc else Opt.dfs bl n j.there acc) layer2 bbRGate
      (C (A 0) (A 0)) (bbT o (listNoun A out) S1 (HoonMap.toNoun Blob.toNoun bl)) (Opt.getJmps b.fin)
      (out, o :: saw) (C (listNoun A out) S1) r0 (by
        intro j _ s N s' hR hs'
        obtain ⟨S2, rfl, hS2⟩ := hR
        have hh := saw_has hS2 j.there
        have hL := optC_layer2
        by_cases hm : j.there ∈ s.2
        · simp only [hm, if_true, Option.some.injEq] at hs'
          subst hs'
          refine ⟨C (listNoun A s.1) S2, ?_, ⟨S2, rfl, hS2⟩⟩
          unfold bbT
          generalize optC = OC at hL
          simp [nock_exec, bbRGate, Jmp.toNoun, hL, in_arm, in.arm_at, has_in_arm, in.has.arm_at, hh, hm, loob]
        · simp only [hm, if_false] at hs'
          obtain ⟨S3, hn3, hS3⟩ := ih j.there s.1 s.2 S2 hS2 s' hs'
          refine ⟨C (listNoun A s'.1) S3, ?_, ⟨S3, rfl, hS3⟩⟩
          unfold bbT at hn3 ⊢
          generalize optC = OC at hL hn3
          generalize HoonMap.toNoun Blob.toNoun bl = BL at hn3 ⊢
          simp [nock_exec, bbRGate, Jmp.toNoun, hL, in_arm, in.arm_at, has_in_arm, in.has.arm_at, hh, hm, loob,
            hn3])
      ⟨S1, rfl, hS1⟩ hr0
    obtain ⟨N', hN', S', rfl, hS'⟩ := hroll
    refine ⟨S', ?_, hS'⟩
    rw [← listNoun_map_listN] at hN'
    have hL := optC_layer2
    have hT := optC_types
    have hg := blocks_got bl o
    have hgj := gj_gate compTypes b.fin hfp
    have hgja := gj_at
    rw [hb] at hg
    unfold bbT at hN' ⊢
    conv => lhs; arg 2; unfold bbTrap
    generalize optC = OC at hL hT hN'
    generalize compTypes = CT at hT hgj hgja
    generalize HoonMap.toNoun Blob.toNoun bl = BL at hg hN' ⊢
    obtain ⟨par, body, fin⟩ := b
    simp only [Option.map_some, Blob.toNoun] at hg
    simp [nock_exec, bbPut, bbJmps, listNoun, hL, hT, in_arm, in.arm_at, put_in_arm, in.put.arm_at, hp1,
      roll.arm_at, roll_arm, hgja, gj_arm, hgj, by.arm_at, by_arm, by.got.arm_at, got_arm, hg, hN']

/-! ## The gate -/

/-- **`+bb-topo`** on the noun of a treap of blocks with no `%lti`: where
`bbTopo fuel` returns `t`, the gate returns the noun of `t`. -/
theorem bb_gate (bl : TreapMap mugF Blob) (hl : NoLti bl) (fuel : Nat) (t : List Nat)
    (h : Opt.bbTopo fuel bl = some t) :
    nock (C bbBody (C (HoonMap.toNoun Blob.toNoun bl) optC)) bbBody = some (listNoun A t) := by
  unfold Opt.bbTopo at h
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨S', hn, _⟩ := bb_trap bl hl fuel 0 [] [] (A 0) sawRel_nil r hr
  unfold bbT at hn
  conv => lhs; arg 2; unfold bbBody
  simp only [listNoun] at hn
  simp [nock_exec, hn]

end Compiler
end Formalization
