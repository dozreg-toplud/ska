import lemmas.Compiler.OptLinkHelpers
import lemmas.Hoon.ListsSort

/-!
# `+remove-hops` linked

```hoon
++  remove-hops
  ~%  %remove-hops  ..ride  ~
  |=  $:  blocks=(map @uwoo blob)
          rev=(jar @uwoo @uwoo)
          topo=(list @uwoo)
      ==
  ^-  [changed=? (map @uwoo blob)]
  =*  gen  ,[new=(map @uwoo blob) saw=(set @uwoo)]
  =;  =gen  [!=(~ saw.gen) new.gen]
  ^-  gen
  %+  roll  topo
  |=  [o=@uwoo =gen]
  ^+  gen
  ?:  (~(has in saw.gen) o)  gen
  =/  o-new=@uwoo  o
  =/  b-new=blob  (~(got by blocks) o)
  =|  segs=(list (list pole))
  |-  ^+  gen
  =*  done  ...
  ?.  ?=(%hop -.fin.b-new)  done
  =/  o1=@uwoo  there.t.fin.b-new
  =/  pre-o1=(list @uwoo)  (~(get ja rev) o1)
  ?<  =(~ pre-o1)
  ?.  =(pre-o1 ~[o])  done
  =.  saw.gen  (~(put in saw.gen) o1)
  =/  b1  (~(got by blocks) o1)
  =/  seg=(list pole)  ...
  $(o o1, segs [seg segs], fin.b-new fin.b1)
```

The arm is `4` of `optC` (`rh_at`, nouns by `tools/gen/optlink.py rh`):
the body rolls the gate `rhGate` over `topo` from `[~ ~]` and returns
`[!=(~ saw) new]`; the gate skips a label in `saw`, else takes its block
(`rhGot`) and runs the trap `rhTrap`, which follows the hops from `o-new`
while the target's predecessors in `rev` are `~[o]`, merging the targets
(`rhMerge`: `saw`, `b1`, the segment `rhSeg` with its trap `rhSegT`, the
next turn), and puts the block built at `o-new` (`rhDone`, `rhDone2`).

The model `removeHops fuel` (`Ska/OptHops.lean`) bounds the length of a
chain by the fuel and keeps `saw` as a list; `gen` is related to the model's
state by `RhRel` (the map's noun and a set of atoms, `SawRel`).

* `rh_segt`: the trap of the segment is `hopSeg`.
* `rh_done`: `done` puts `hopDone` at `o-new` (`+flop`, `+zing`, `+put:by`).
* `rh_trap`: by induction on the fuel, where `hopChain` returns, the trap
  returns `gen` with the put of the model's block and a set related to its
  `saw`.
* `rh_step`: the gate of the `+roll` against `hopsStep`.
* `rh_gate`: **where `removeHops fuel` returns `(changed, new)`, the gate of
  `+remove-hops` on the nouns of a treap of blocks, a jar `rev` and a list
  `topo` returns `[changed new]`.**
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The nouns -/

/-- The trap of the segment: the moves of the hop's arguments in front of the body. -/
def rhSegT : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 30)))) (C (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 14))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 0) (A 6)) (C (A 0) (A 0))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 14)))) (C (C (A 0) (A 0)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 61))) (C (A 10) (C (C (A 14) (C (A 0) (A 29))) (C (A 10) (C (C (A 6) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 60)))) (C (C (C (C (A 1) (A 0x6d6d69)) (C (C (A 1) (A 0)) (C (A 0) (A 28)))) (C (A 0) (A 6))) (C (C (C (A 1) (A 0x766f6d)) (C (C (A 0) (A 121)) (C (A 0) (A 28)))) (C (A 0) (A 6))))))) (C (A 0) (A 1))))))))))))))))

/-- The segment of the merged block `b1`. -/
def rhSeg : Noun :=
  (C (A 8) (C (C (A 0) (A 2030)) (C (A 8) (C (C (A 0) (A 12)) (C (A 8) (C (C (A 0) (A 58)) (C (A 8) (C (C (A 1) rhSegT) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))))))

/-- `done`: the put of the block built so far at `o-new`. -/
def rhDone : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 10) (C (C (A 2) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 1018))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 62)) (C (A 7) (C (C (A 0) (A 3)) (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 9) (C (A 0x17defa) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 58)) (C (A 8) (C (C (A 9) (C (A 0x2fbd7f) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 14)))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 253))))))

/-- `done` under the pushes of `o1` and `pre-o1`. -/
def rhDone2 : Noun :=
  (C (A 7) (C (C (A 0) (A 7)) (C (A 10) (C (C (A 2) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 1018))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 62)) (C (A 7) (C (C (A 0) (A 3)) (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 9) (C (A 0x17defa) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 58)) (C (A 8) (C (C (A 9) (C (A 0x2fbd7f) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 14)))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 253))))))

/-- The merge of `o1`: `saw`, `b1`, the segment and the next turn. -/
def rhMerge : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 2043) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 84) (C (A 10) (C (C (A 6) (C (A 0) (A 4091))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 8188))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 8) (C rhSeg (C (A 9) (C (A 2) (C (A 10) (C (C (A 252) (C (A 0) (A 30))) (C (A 10) (C (C (A 59) (C (A 0) (A 27))) (C (A 10) (C (C (A 6) (C (C (A 0) (A 2)) (C (A 0) (A 126)))) (C (A 0) (A 31))))))))))))))))

/-- `(~(get ja rev) o1)`. -/
def rhGetJa : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 761) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 10) (C (A 10) (C (C (A 6) (C (A 0) (A 8186))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2))))))))

/-- The trap of `+remove-hops` that follows the hops from `o-new`. -/
def rhTrap : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706f68)) (C (A 0) (A 118)))) (C (C (A 8) (C (C (A 0) (A 239)) (C (A 8) (C rhGetJa (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (A 0) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 0) (A 2)) (C (C (A 0) (A 1020)) (C (A 1) (A 0))))) (C rhMerge rhDone2)))))))))) rhDone)))))

/-- `(~(got by blocks) o)`. -/
def rhGot : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 252))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 60))) (C (A 0) (A 2))))))))

/-- The gate of the `+roll` over `topo`. -/
def rhGate : Noun :=
  (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 381) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) (C (C (A 0) (A 13)) (C (A 8) (C (C (A 0) (A 12)) (C (A 8) (C rhGot (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) rhTrap) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))))))))))

/-- The gate body of `+remove-hops`. -/
def rhBody : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x7ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 59)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (C (A 0) (A 0)))) (C (C (A 1) rhGate) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 5)))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (A 0) (A 4)))))))

/-- Its sample bunt. -/
def rhBunt : Noun :=
  (C (A 0) (C (A 0) (A 0)))

/-- Its `%fast` hint. -/
def rhHint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x73706f682d65766f6d6572) (C (C (A 0) (A 0xffff)) (A 0))))) (C (A 0) (A 1))))

/-- The arm `+remove-hops`. -/
def rhArm : Noun := C (A 7) (C (C (A 8) (C (C (A 1) rhBunt) (C (C (A 1) rhBody) (C (A 0) (A 1))))) rhHint)

/-- `+remove-hops` is arm `4` of `optC`. -/
theorem rh_at : slot? 4 optC = some rhArm := by kernel_rfl

@[nock_exec] theorem rh_arm (d : Noun) : nock d rhArm = some (C rhBody (C rhBunt d)) := by
  unfold rhArm rhHint; generalize rhBody = B; generalize rhBunt = U; simp [nock_exec]

/-! ## The segment -/

/-- **The trap of the segment** is `hopSeg`. -/
theorem rh_segt (REST : Noun) : ∀ (args : List (Option Nat)) (par : List Nat) (ops : List Pole),
    nock (C rhSegT (C (listNoun Pole.toNoun ops) (C (listNoun A par) (C (listNoun (unitNoun A) args) REST))))
      rhSegT = (Opt.hopSeg args par ops).map (listNoun Pole.toNoun) := by
  intro args
  induction args with
  | nil =>
    intro par ops
    cases par with
    | nil =>
      conv => lhs; arg 2; unfold rhSegT
      simp [nock_exec, listNoun, Opt.hopSeg]
    | cons p ps =>
      conv => lhs; arg 2; unfold rhSegT
      simp [nock_exec, listNoun, Opt.hopSeg]
  | cons a as ih =>
    intro par ops
    cases par with
    | nil =>
      conv => lhs; arg 2; unfold rhSegT
      simp [nock_exec, listNoun, Opt.hopSeg]
    | cons p ps =>
      have h := ih ps ((match a with | none => Pole.imm (A 0) p | some r => Pole.mov r p) :: ops)
      conv => lhs; arg 2; unfold rhSegT
      cases a with
      | none =>
        simp only [listNoun, Pole.toNoun, Tag.imm] at h
        simp [nock_exec, listNoun, Opt.hopSeg, unitNoun, h, Pole.toNoun, Tag.imm]
      | some r =>
        simp only [listNoun, Pole.toNoun, Tag.mov] at h
        simp [nock_exec, listNoun, Opt.hopSeg, unitNoun, h, Pole.toNoun, Tag.mov]

/-! ## `done` -/

theorem rh_flop (segs : List (List Pole)) :
    nock (C flop.battery (C (listNoun (listNoun Pole.toNoun) segs) layer2)) flop.battery
      = some (listNoun (listNoun Pole.toNoun) segs.reverse) := by
  rw [listNoun_map_listN, listNoun_map_listN, flop_gate layer2 homoIn_layer2, List.map_reverse]

theorem rh_zing (body : List Pole) (segs : List (List Pole)) :
    nock (C zing.battery (C (C (listNoun Pole.toNoun body) (listNoun (listNoun Pole.toNoun) segs)) layer2))
      zing.battery = some (listNoun Pole.toNoun (body ++ segs.flatten)) := by
  have h := zing_gate layer2 welp.arm_at ((body :: segs).map (List.map Pole.toNoun))
  have e1 : listN (((body :: segs).map (List.map Pole.toNoun)).map listN)
      = C (listNoun Pole.toNoun body) (listNoun (listNoun Pole.toNoun) segs) := by
    rw [listNoun_map_listN (listNoun Pole.toNoun) segs, List.map_map, List.map_cons, listN_cons]
    congr 2
    · exact (listNoun_map_listN Pole.toNoun body).symm
    · apply List.map_congr_left; intro l _; exact (listNoun_map_listN Pole.toNoun l).symm
  have e2 : listN ((body :: segs).map (List.map Pole.toNoun)).flatten = listNoun Pole.toNoun (body ++ segs.flatten) := by
    rw [listNoun_map_listN, ← List.map_flatten]; rfl
  rw [e1, e2] at h
  exact h

/-- The subject of the gate of the `+roll`: `[rhGate [[o [new saw]] [rhBody [[blocks [rev topo]] optC]]]]`. -/
def rhR (o : Nat) (newN S BL REV TOPO : Noun) : Noun :=
  C rhGate (C (C (A o) (C newN S)) (C rhBody (C (C BL (C REV TOPO)) optC)))

/-- The subject of the trap: `[rhTrap [segs [b-new [o-new R]]]]`. -/
def rhX (segs : List (List Pole)) (bnew : Blob) (onew o : Nat) (newN S BL REV TOPO : Noun) : Noun :=
  C rhTrap (C (listNoun (listNoun Pole.toNoun) segs) (C bnew.toNoun (C (A onew) (rhR o newN S BL REV TOPO))))

/-- **`done`**: `hopDone` put at `o-new`, `saw` unchanged. -/
theorem rh_done (new : TreapMap mugF Blob) (segs : List (List Pole)) (bnew : Blob) (onew o : Nat)
    (S BL REV TOPO : Noun) :
    nock (rhX segs bnew onew o (HoonMap.toNoun Blob.toNoun new) S BL REV TOPO) rhDone
      = some (C (HoonMap.toNoun Blob.toNoun (HoonMap.put new onew (Opt.hopDone bnew segs))) S) := by
  have hL := optC_layer2
  have hp := putF_hoonMap Blob.toNoun new onew (Opt.hopDone bnew segs)
  have hput := put_gate (mug := mugF) layer2 gorIn_morIn_layer2 (A onew) _ _ _ hp
  have hz := rh_zing bnew.body segs.reverse
  have hf := rh_flop segs
  have hza : ∀ c, nock c zing.arm = some (C zing.battery (C (A 0) c)) := by
    intro c; nock_open zing.arm; simp only [nock_exec]
  obtain ⟨par, body, fin⟩ := bnew
  simp only [Opt.hopDone, Blob.toNoun] at hput hz ⊢
  unfold rhX rhR
  generalize optC = OC at hL
  simp [nock_exec, rhDone, hL, by.arm_at, by_arm, by.put.arm_at, put_arm, hput, zing.arm_at, hza, hz,
    flop.arm_at, flop_arm, hf]

/-- `done` under the pushes of `o1` and `pre-o1`. -/
theorem rh_done2 (new : TreapMap mugF Blob) (segs : List (List Pole)) (bnew : Blob) (onew o : Nat)
    (S BL REV TOPO P Q : Noun) :
    nock (C P (C Q (rhX segs bnew onew o (HoonMap.toNoun Blob.toNoun new) S BL REV TOPO))) rhDone2
      = some (C (HoonMap.toNoun Blob.toNoun (HoonMap.put new onew (Opt.hopDone bnew segs))) S) := by
  have hL := optC_layer2
  have hp := putF_hoonMap Blob.toNoun new onew (Opt.hopDone bnew segs)
  have hput := put_gate (mug := mugF) layer2 gorIn_morIn_layer2 (A onew) _ _ _ hp
  have hz := rh_zing bnew.body segs.reverse
  have hf := rh_flop segs
  have hza : ∀ c, nock c zing.arm = some (C zing.battery (C (A 0) c)) := by
    intro c; nock_open zing.arm; simp only [nock_exec]
  obtain ⟨par, body, fin⟩ := bnew
  simp only [Opt.hopDone, Blob.toNoun] at hput hz ⊢
  unfold rhX rhR
  generalize optC = OC at hL
  simp [nock_exec, rhDone2, hL, by.arm_at, by_arm, by.put.arm_at, put_arm, hput, zing.arm_at, hza, hz,
    flop.arm_at, flop_arm, hf]

/-! ## The trap -/

/-- **The trap of `+remove-hops`**: where `hopChain` returns, the trap
returns `gen` with the model's block put at `o-new` and a set related to the
model's `saw`. -/
theorem rh_trap (bl : TreapMap mugF Blob) (rev : TreapMap mugF (List Nat)) (TOPO : Noun) :
    ∀ (n o : Nat) (bnew : Blob) (segs : List (List Pole)) (saw : List Nat) (S : Noun) (onew : Nat)
      (new : TreapMap mugF Blob), SawRel S saw → ∀ r, Opt.hopChain bl rev n o bnew segs saw = some r →
    ∃ S', nock (rhX segs bnew onew o (HoonMap.toNoun Blob.toNoun new) S (HoonMap.toNoun Blob.toNoun bl)
        (jarN rev) TOPO) rhTrap
      = some (C (HoonMap.toNoun Blob.toNoun (HoonMap.put new onew r.1)) S') ∧ SawRel S' r.2 := by
  intro n
  induction n with
  | zero => intro o bnew segs saw S onew new hS r h; simp [Opt.hopChain] at h
  | succ n ih =>
    intro o bnew segs saw S onew new hS r h
    have hdone := rh_done new segs bnew onew o S (HoonMap.toNoun Blob.toNoun bl) (jarN rev) TOPO
    obtain ⟨par, body, fin⟩ := bnew
    cases fin with
    | hop t =>
      obtain ⟨args, there⟩ := t
      have hg := jar_get rev there
      have hL := optC_layer2
      simp only [Opt.hopChain] at h
      cases hpre : Opt.getJa rev there with
      | nil => simp [hpre] at h
      | cons x xs =>
        rw [hpre] at hg h
        by_cases hx : x :: xs = [o]
        · simp only [List.cons_ne_nil, if_false, hx, ne_eq, not_true_eq_false] at h
          obtain ⟨b1, hb1, h2⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨seg, hseg, h3⟩ := Option.bind_eq_some_iff.mp h2
          obtain ⟨S1, hp1, hS1⟩ := saw_put hS there
          obtain ⟨S2, hn2, hS2⟩ := ih there ⟨par, body, b1.fin⟩ (seg :: segs) (there :: saw) S1 onew new hS1 r h3
          refine ⟨S2, ?_, hS2⟩
          simp only [List.cons.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          have hgb := blocks_got bl there
          rw [hb1] at hgb
          obtain ⟨bpar, bbody, bfin⟩ := b1
          have hs := rh_segt
          unfold rhX at hn2 ⊢
          unfold rhR at hn2 ⊢
          conv => lhs; arg 2; unfold rhTrap
          simp only [Blob.toNoun, Termin.toNoun, Jmp.toNoun, listNoun, Option.map_some, Tag.hop] at hgb hn2 hseg ⊢
          generalize optC = OC at hL hn2 ⊢
          generalize HoonMap.toNoun Blob.toNoun bl = BL at hgb hn2 ⊢
          simp [nock_exec, rhGetJa, rhMerge, rhSeg, hL, ja.arm_at, ja_arm, ja.get.arm_at, ju_get_arm, hg,
            in_arm, in.arm_at, put_in_arm, in.put.arm_at, hp1, by.arm_at, by_arm, by.got.arm_at, got_arm, hgb,
            hs, hseg, hn2, listNoun]
        · have h' : r = (Opt.hopDone ⟨par, body, Termin.hop ⟨args, there⟩⟩ segs, saw) := by
            simp only [List.cons_ne_nil, if_false, ne_eq, hx, not_false_eq_true, if_true, Option.some.injEq] at h
            exact h.symm
          subst h'
          refine ⟨S, ?_, hS⟩
          have hdone2 := fun P Q => rh_done2 new segs ⟨par, body, Termin.hop ⟨args, there⟩⟩ onew o S
            (HoonMap.toNoun Blob.toNoun bl) (jarN rev) TOPO P Q
          unfold rhX at hdone2 ⊢
          conv => lhs; arg 2; unfold rhTrap
          simp only [Blob.toNoun, Termin.toNoun, Jmp.toNoun, Tag.hop] at hdone2 ⊢
          unfold rhR at hdone2 ⊢
          generalize optC = OC at hL hdone2 ⊢
          cases xs with
          | nil =>
            have hxo : x ≠ o := fun e => hx (by rw [e])
            simp [nock_exec, rhGetJa, hL, ja.arm_at, ja_arm, ja.get.arm_at, ju_get_arm, hg, listNoun, hxo, hdone2]
          | cons y ys =>
            simp [nock_exec, rhGetJa, hL, ja.arm_at, ja_arm, ja.get.arm_at, ju_get_arm, hg, listNoun, hdone2]
    | _ =>
      simp only [Opt.hopChain] at h
      cases h
      refine ⟨S, ?_, hS⟩
      unfold rhX at hdone ⊢
      conv => lhs; arg 2; unfold rhTrap
      simp only [Blob.toNoun, Termin.toNoun, Tag.hop, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.jmp,
        Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti] at hdone ⊢
      simp [nock_exec, hdone]

/-! ## The gate of the `+roll` -/

/-- `gen`, `[new saw]`, and the model's state. -/
def RhRel (N : Noun) (s : TreapMap mugF Blob × List Nat) : Prop :=
  ∃ S, N = C (HoonMap.toNoun Blob.toNoun s.1) S ∧ SawRel S s.2

/-- **The gate of the `+roll` over `topo`** against `hopsStep`. -/
theorem rh_step (bl : TreapMap mugF Blob) (rev : TreapMap mugF (List Nat)) (TOPO : Noun) (fuel o : Nat) :
    ∀ s N s', RhRel N s → Opt.hopsStep fuel bl rev s o = some s' →
    ∃ N', nock (C rhGate (C (C (A o) N) (C rhBody (C (C (HoonMap.toNoun Blob.toNoun bl) (C (jarN rev) TOPO))
        optC)))) rhGate = some N' ∧ RhRel N' s' := by
  intro s N s' hR h
  obtain ⟨S, rfl, hS⟩ := hR
  have hh := saw_has hS o
  have hL := optC_layer2
  unfold Opt.hopsStep at h
  by_cases ho : o ∈ s.2
  · simp only [ho, if_true, Option.some.injEq] at h
    subst h
    refine ⟨_, ?_, S, rfl, hS⟩
    conv => lhs; arg 2; unfold rhGate
    generalize optC = OC at hL
    simp [nock_exec, hL, in_arm, in.arm_at, has_in_arm, in.has.arm_at, hh, ho, loob]
  · simp only [ho, if_false] at h
    obtain ⟨b, hb, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h2
    obtain ⟨S', hn, hS'⟩ := rh_trap bl rev TOPO fuel o b [] s.2 S o s.1 hS r hr
    refine ⟨_, ?_, S', rfl, hS'⟩
    have hgb := blocks_got bl o
    rw [hb] at hgb
    unfold rhX rhR at hn
    conv => lhs; arg 2; unfold rhGate
    simp only [listNoun, Option.map_some] at hn hgb
    generalize optC = OC at hL hn
    generalize HoonMap.toNoun Blob.toNoun bl = BL at hgb hn ⊢
    simp [nock_exec, hL, in_arm, in.arm_at, has_in_arm, in.has.arm_at, hh, ho, loob, rhGot, by.arm_at, by_arm,
      by.got.arm_at, got_arm, hgb, hn]

/-! ## The gate -/

/-- **`+remove-hops`**: where `removeHops fuel` returns `(changed, new)`, the
gate on the nouns of a treap of blocks, a jar `rev` and a list `topo` returns
`[changed new]`. -/
theorem rh_gate (bl : TreapMap mugF Blob) (rev : TreapMap mugF (List Nat)) (topo : List Nat) (fuel : Nat)
    (r : Bool × TreapMap mugF Blob) (h : Opt.removeHops fuel bl rev topo = some r) :
    nock (C rhBody (C (C (HoonMap.toNoun Blob.toNoun bl) (C (jarN rev) (listNoun A topo))) optC)) rhBody
      = some (C (flag r.1) (HoonMap.toNoun Blob.toNoun r.2)) := by
  unfold Opt.removeHops at h
  obtain ⟨r0, hr0, rfl⟩ := Option.map_eq_some_iff.mp h
  have hroll := roll_gate_rel A RhRel (fun o s => Opt.hopsStep fuel bl rev s o) layer2 rhGate (A 0)
    (C rhBody (C (C (HoonMap.toNoun Blob.toNoun bl) (C (jarN rev) (listNoun A topo))) optC)) topo
    (HoonMap.empty, []) (C (A 0) (A 0)) r0
    (fun o _ s N s' hR hs => rh_step bl rev (listNoun A topo) fuel o s N s' hR hs)
    ⟨A 0, by simp [HoonMap.toNoun_empty], sawRel_nil⟩ hr0
  obtain ⟨N', hN', S', rfl, hS'⟩ := hroll
  rw [← listNoun_map_listN] at hN'
  have hL := optC_layer2
  have he := hS'.eq_nil
  conv => lhs; arg 2; unfold rhBody
  generalize optC = OC at hL hN'
  generalize HoonMap.toNoun Blob.toNoun bl = BL at hN' ⊢
  by_cases e : r0.2 = []
  · have hS0 : S' = A 0 := he.2 e
    subst hS0
    simp [nock_exec, hL, roll.arm_at, roll_arm, hN', e, flag]
  · have hS0 : S' ≠ A 0 := fun h => e (he.1 h)
    simp [nock_exec, hL, roll.arm_at, roll_arm, hN', e, flag, Ne.symm hS0]

end Compiler
end Formalization
