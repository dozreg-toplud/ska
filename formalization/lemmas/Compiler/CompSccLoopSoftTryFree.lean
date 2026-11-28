import lemmas.Compiler.CompSccLoopSoftTryPes
import lemmas.Compiler.OptLinkHelpers
import lemmas.Compiler.OptLinkAlPrelude
import lemmas.Compiler.CompLeapPass

/-! # `def` and `+soft-free` in the try path of `+soft-emit` (README Gaps 21.22)

On the subject after `fail` (`tfS`: `fail`, `pes`, then `tzS`):
* `tf_def`: the push `tpYN8`, `=/  def  (silt (zing (turn tries |=([q r ned] (flatten-need ned)))))`
  (line 5458), a set noun of `softDefs tries` (`SawRel`);
* `+soft-free` (line 5490, battery slot `882367` of `comp.door`, `tf_at`): the arm `tfArm`, its trap
  `tfTrap` cut at its tests (`tfR1` .. `tfR5`; `tfOr` the test of `las` and `seen`, `tfGot` the
  `+got:by`, `tfLien` the `+lien` over the body with the gate `tfG1Bat`, `tfNex` the successors);
  `tf_trap`: wherever the model `softFreeF` (any fuel) gives `some b`, the trap gives `loob b`;
* `tf_test`: the `?.` of `tpYN9` goes to `tpYNY0` (`&`) or `tpYNN0` (`|`) as the model says.
The arm's names were printed from the pill by `tools/gen/nouns.py` (slot `882367` of `comp.door`). -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def tfBunt : Noun :=
  (C (A 0) (C (A 0) (A 0)))

def tfOr : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 0) (A 250)) (C (A 0) (A 12)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 381) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))))))

def tfRec1 : Noun :=
  (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 13))) (C (A 0) (A 1))))))

def tfGot : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 0x3fde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2))))))))

def tfG1Bunt : Noun :=
  (C (A 0x6d7363) (C (C (C (A 1) (A 0)) (C (A 0) (A 0))) tfBunt))

def tfG1Bat : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x2fbde) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 84) (C (A 0) (A 0x3fff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 381) (C (A 10) (C (C (A 6) (C (A 0) (A 4091))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))

def tfLien : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x2fbde) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 26)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) tfG1Bunt) (C (C (A 1) tfG1Bat) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))

def tfNex : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706f68)) (C (A 0) (A 22)))) (C (C (C (A 0) (A 47)) (C (A 1) (A 0))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x716c63)) (C (A 0) (A 22)))) (C (C (C (A 0) (A 189)) (C (C (A 0) (A 191)) (C (A 1) (A 0)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x717165)) (C (A 0) (A 22)))) (C (C (C (A 0) (A 381)) (C (C (A 0) (A 383)) (C (A 1) (A 0)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6e7262)) (C (A 0) (A 22)))) (C (C (C (A 0) (A 189)) (C (C (A 0) (A 191)) (C (A 1) (A 0)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x7a7262)) (C (A 0) (A 22)))) (C (C (C (A 0) (A 189)) (C (C (A 0) (A 191)) (C (A 1) (A 0)))) (C (A 11) (C (C (A 0x73736f74) (C (A 1) (A 0))) (C (A 1) (A 0)))))))))))))))))))

def tfRec2 : Noun :=
  (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 84) (C (A 10) (C (C (A 6) (C (A 0) (A 126))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 124))) (C (A 0) (A 2))))))))) (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 9) (C (A 0xbef7f4) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 0) (A 125)))) (C (A 0) (A 2))))))))) (C (A 0) (A 7))))))))

def tfR5 : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (A 1) (A 1)) tfRec2)))

def tfR4 : Noun :=
  (C (A 8) (C tfNex tfR5))

def tfR3 : Noun :=
  (C (A 6) (C tfLien (C (C (A 1) (A 1)) tfR4)))

def tfR2 : Noun :=
  (C (A 8) (C tfGot tfR3))

def tfR1 : Noun :=
  (C (A 6) (C tfOr (C tfRec1 tfR2)))

def tfTrap : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 6)))) (C (C (A 1) (A 0)) tfR1)))

def tfBat : Noun :=
  (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (C (A 0) (A 28)) (C (A 1) (A 0))) (C (A 8) (C (C (A 1) tfTrap) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))))

def tfArm : Noun :=
  (C (A 8) (C (C (A 1) tfBunt) (C (C (A 1) tfBat) (C (A 0) (A 1)))))


/-- `+soft-free` is at battery slot `882367` of the door (core arm `0x1576bf`). -/
theorem tf_at : slot? 882367 comp.door = some tfArm := by kernel_rfl

@[nock_exec] theorem tf_arm (d : Noun) : nock d tfArm = some (C tfBat (C tfBunt d)) := by
  unfold tfArm; generalize tfBat = B; generalize tfBunt = U; simp [nock_exec]

/-- The subject of `tpYN8`: `[fail pes [kon rub] tom flag lat tpS0]`. -/
abbrev tfS (FAIL PES : Nat) (kon : List Pole) (rub : Nat) (TOM FLAG LAT HD TR OPS CUT AXS : Noun) (o : Nat)
    (s : SoftCall) (g : Gen (TreapMap mugF)) (x : GenRest) (ctx : Noun) : Noun :=
  C (A FAIL) (C (A PES) (tzS kon rub TOM FLAG LAT HD TR OPS CUT AXS o s g x ctx))

/-- The gate of the `+turn` of `def`: `(flatten-need ned)` of an entry `[q r ned]`. -/
def tfFnGate : Noun :=
  (C (A 8) (C (C (A 9) (C (A 348) (C (A 0) (A 0xffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))

theorem tf_fn_gate {ctx : Noun} (hc : CompIn ctx) (FAIL PES : Nat) (kon : List Pole) (rub : Nat)
    (TOM FLAG LAT HD TR OPS CUT AXS : Noun) (o : Nat) (s : SoftCall) (g : Gen (TreapMap mugF)) (x : GenRest)
    (t : Nat × Nat × Need) :
    nock (C tfFnGate (C (seTopN t) (tfS FAIL PES kon rub TOM FLAG LAT HD TR OPS CUT AXS o s g x ctx))) tfFnGate
      = some (listNoun A (flattenNeed t.2.2)) := by
  have hD := comp_fn_at
  have hf := comp_flatten_need hc (genNoun g x) t.2.2
  simp only [tfS, tzS, tpS0, seS0, compCore, seTopN] at hf ⊢
  generalize comp.door = Dr at hD hf ⊢
  unfold tfFnGate
  simp [nock_exec, hD, comp_fn_arm, hf]

/-- **`def`**: `tpYN8` pushes the set of the registers that the tries define. -/
theorem tf_def {ctx : Noun} (hc : CompIn ctx) (FAIL PES : Nat) (kon : List Pole) (rub : Nat)
    (TOM FLAG LAT HD OPS CUT AXS : Noun) (o : Nat) (s : SoftCall) (g : Gen (TreapMap mugF)) (x : GenRest)
    (tries : List (Nat × Nat × Need)) :
    ∃ DEF, SawRel DEF (softDefs tries) ∧
      nock (tfS FAIL PES kon rub TOM FLAG LAT HD (listNoun seTopN tries) OPS CUT AXS o s g x ctx) tpYN8
        = nock (C DEF (tfS FAIL PES kon rub TOM FLAG LAT HD (listNoun seTopN tries) OPS CUT AXS o s g x ctx))
            tpYN9 := by
  obtain ⟨hsilt, hsaw⟩ := siltF_saw (softDefs tries)
  refine ⟨siltF (listNoun A (softDefs tries)), ⟨hsaw.1, fun k => by rw [hsaw.2]; simp [mem_dedupN]⟩, ?_⟩
  generalize siltF (listNoun A (softDefs tries)) = DEF at hsilt
  have ht := lq_turn_gate seTopN listN layer2 homoIn_layer2 tfFnGate (C (A 0) (C (A 0) (C (A 0x656e6f6e) (A 0))))
    (tfS FAIL PES kon rub TOM FLAG LAT HD (listNoun seTopN tries) OPS CUT AXS o s g x ctx)
    (fun t => (flattenNeed t.2.2).map A) tries
    (fun t _ => by rw [tf_fn_gate hc, listNoun_map_listN])
  have hz := zing_gate layer2 welp.arm_at ((tries.map fun t => (flattenNeed t.2.2).map A))
  have hflat : (tries.map fun t => (flattenNeed t.2.2).map A).flatten = (softDefs tries).map A := by
    simp [softDefs, List.map_flatten, List.map_map, Function.comp_def]
  rw [hflat] at hz
  rw [listNoun_map_listN] at hsilt
  have hc' : slot? 262143 ctx = some layer2 := hc
  have hs1 := silt_arm_at
  have hz1 := zing.arm_at
  have ht1 := turn.arm_at
  conv => { lhs; arg 2; unfold tpYN8 }
  simp only [List.map_map, Function.comp_def] at ht hz
  rw [listNoun_map_listN]
  simp only [tfS, tzS, tpKR, tpS0, seS0, compCore, tfFnGate, listNoun_map_listN] at ht ⊢
  generalize tpYN9 = Y
  generalize comp.door = Dr at ht ⊢
  generalize layer2 = L2 at hc' hs1 hz1 ht1 ht hz hsilt ⊢
  simp [tpYNH8, nock_exec, hc', hs1, silt_arm, hz1, lq_zing_arm, ht1, turn_arm, ht, hz, hsilt]

/-! ## The trap of `+soft-free` -/

/-- The subject of the trap: `[trap todo seen [battery [o las def] core]]`. -/
abbrev tfT (todo : List Nat) (SEEN : Noun) (o las : Nat) (DEF CC : Noun) : Noun :=
  C tfTrap (C (listNoun A todo) (C SEEN (C tfBat (C (C (A o) (C (A las) DEF)) CC))))

/-- The loop of `+lien` on a list of `E a`. -/
theorem tf_lien_loop {α : Type} (E : α → Noun) (c bp bs bc : Noun) (p : α → Bool) : ∀ (l : List α),
    (∀ a ∈ l, nock (C bp (C (E a) bc)) bp = some (loob (p a))) →
    nock (C lien.loop (C lien.battery (C (C (listN (l.map E)) (C bp (C bs bc))) c))) lien.loop
      = some (loob (l.any p)) := by
  intro l
  induction l with
  | nil =>
    intro _
    nock_open lien.loop
    simp [nock_exec]
  | cons x xs ih =>
    intro hf
    have hx := hf x (by simp)
    have hxs := ih (fun y hy => hf y (by simp [hy]))
    nock_open lien.loop
    cases hp : p x <;> simp [nock_exec, hx, hxs, hp]

/-- `+lien` on a list of `E a`. -/
theorem tf_lien {α : Type} (E : α → Noun) (c bp bs bc : Noun) (p : α → Bool) (l : List α)
    (hf : ∀ a ∈ l, nock (C bp (C (E a) bc)) bp = some (loob (p a))) :
    nock (C lien.battery (C (C (listN (l.map E)) (C bp (C bs bc))) c)) lien.battery
      = some (loob (l.any p)) := by
  nock_open lien.battery
  simp only [nock_exec, tf_lien_loop E c bp bs bc p l hf]

/-- The successors of a block (`?+  -.fin.blob`): `finNext`. -/
theorem tf_nex (b : Blob) (T : Noun) : nock (C b.toNoun T) tfNex = some (listNoun A (finNext b.fin)) := by
  obtain ⟨par, body, fin⟩ := b
  cases fin <;>
    simp [nock_exec, tfNex, Blob.toNoun, Termin.toNoun, Jmp.toNoun, finNext, listNoun, Tag.hop, Tag.clq,
      Tag.eqq, Tag.brn, Tag.brz, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti]

/-- The gate of the outer `+lien`: does the op read a register of `def`. -/
theorem tf_g1 {ctx : Noun} (hc : CompIn ctx) (h15 : slot? 15 ctx = some compTypes) (g : Gen (TreapMap mugF))
    (x : GenRest) (todo : List Nat) (SEEN : Noun) (o las : Nat) {DEF : Noun} {dfn : List Nat}
    (hD : SawRel DEF dfn) (B : Noun) (op : Pole) :
    nock (C tfG1Bat (C op.toNoun (C B (tfT todo SEEN o las DEF (compCore g x ctx))))) tfG1Bat
      = some (loob ((Opt.poleRegs op).any fun r => decide (r ∈ dfn))) := by
  have hg := gr_gate_pole op
  have hl := tf_lien A layer2 in.has.battery (A 0) (C in.battery (C DEF layer2)) (fun r => decide (r ∈ dfn))
    (Opt.poleRegs op) (fun r _ => saw_has hD r)
  rw [listNoun_map_listN] at hg
  have hc' : slot? 262143 ctx = some layer2 := hc
  have hgr := gr_at
  have hla := lien.arm_at
  have hia := in.arm_at
  simp only [tfT, compCore] at hl ⊢
  generalize comp.door = Dr
  generalize compTypes = CT at h15 hg hgr
  generalize layer2 = L2 at hc' hl hla hia
  simp [tfG1Bat, nock_exec, hc', h15, hgr, gr_arm, hg, hla, lien_arm, hia, in_arm, in.has.arm_at, has_in_arm, hl]

/-- **The trap of `+soft-free`** against `softFreeF`: wherever the model (with any fuel) gives
`some b`, the trap on `[todo seen]` gives `loob b`. -/
theorem tf_trap {ctx : Noun} (hc : CompIn ctx) (h15 : slot? 15 ctx = some compTypes) (g : Gen (TreapMap mugF))
    (x : GenRest) (o las : Nat) {DEF : Noun} {dfn : List Nat} (hD : SawRel DEF dfn) :
    ∀ (F : Nat) (todo seen : List Nat) (SEEN : Noun) (b : Bool), SawRel SEEN seen →
      softFreeF g.blocks las dfn F todo seen = some b →
      nock (tfT todo SEEN o las DEF (compCore g x ctx)) tfTrap = some (loob b) := by
  intro F
  induction F with
  | zero => intro todo seen SEEN b _ h; simp [softFreeF] at h
  | succ n ih =>
    intro todo seen SEEN b hS h
    have hc' : slot? 262143 ctx = some layer2 := hc
    have hia := in.arm_at
    cases todo with
    | nil =>
      simp only [softFreeF, Option.some.injEq] at h
      subst h
      conv => lhs; arg 2; unfold tfTrap
      simp [nock_exec, listNoun, loob]
    | cons i rest =>
      have hh := saw_has hS i
      by_cases hk : i = las ∨ i ∈ seen
      · have h' : softFreeF g.blocks las dfn n rest seen = some b := by
          simpa [softFreeF, hk] using h
        have hi := ih rest seen SEEN b hS h'
        conv => lhs; arg 2; unfold tfTrap
        simp only [tfT, compCore] at hi hh ⊢
        generalize comp.door = Dr at hi ⊢
        generalize tfTrap = TR at hi ⊢
        rcases hk with hl | hs
        · subst hl
          simp [nock_exec, tfR1, tfOr, tfRec1, listNoun, hi]
        · by_cases hl : i = las
          · subst hl
            simp [nock_exec, tfR1, tfOr, tfRec1, listNoun, hi]
          · have hne : (A las = A i) = False := by simp [Ne.symm hl]
            generalize layer2 = L2 at hc' hia hh
            simp [nock_exec, tfR1, tfOr, tfRec1, listNoun, hi, hc', hia, in_arm, in.has.arm_at, has_in_arm,
              hh, hs, loob, Ne.symm hl]
      · have hl : i ≠ las := fun e => hk (Or.inl e)
        have hs : i ∉ seen := fun e => hk (Or.inr e)
        cases hb : HoonMap.get g.blocks i with
        | none => simp [softFreeF, hl, hs, hb] at h
        | some blk =>
          have hget := getF_hoonMap Blob.toNoun g.blocks i
          rw [hb] at hget
          have hgc : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
            ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
          have hgot := got_gate layer2 hgc (A i) _ _ hget
          have hli := tf_lien Pole.toNoun layer2 tfG1Bat tfG1Bunt
            (C blk.toNoun (tfT (i :: rest) SEEN o las DEF (compCore g x ctx)))
            (fun op => (Opt.poleRegs op).any fun r => decide (r ∈ dfn)) blk.body
            (fun op _ => tf_g1 hc h15 g x (i :: rest) SEEN o las hD blk.toNoun op)
          have hnx := tf_nex blk (tfT (i :: rest) SEEN o las DEF (compCore g x ctx))
          have hla := lien.arm_at
          have hwa := weld.arm_at
          have hba := by.arm_at
          simp only [softFreeF, hl, hs, or_self, if_false, hb] at h
          have hne : (A las = A i) = False := by simp [Ne.symm hl]
          obtain ⟨par, body, fin⟩ := blk
          simp only [Blob.toNoun] at hli hnx hget hgot h ⊢
          rw [← listNoun_map_listN] at hli
          simp only [tfT, compCore, genNoun, listNoun] at hli hnx
          by_cases ha : body.any (fun op => (Opt.poleRegs op).any fun r => decide (r ∈ dfn)) = true
          · simp only [ha, if_true, Option.some.injEq] at h
            subst h
            conv => lhs; arg 2; unfold tfTrap
            simp only [tfT, compCore] at hli hnx hh ⊢
            generalize comp.door = Dr at hli hnx ⊢
            generalize tfTrap = TR at hli hnx ⊢
            generalize layer2 = L2 at hc' hia hh hla hli hgot hgc hba
            simp [nock_exec, tfR1, tfOr, tfRec1, tfR2, tfGot, tfR3, tfLien, listNoun, hc', hia, in_arm,
              in.has.arm_at, has_in_arm, hh, hs, loob, Ne.symm hl, genNoun, by_arm, hba, by.got.arm_at,
              got_arm, hgot, hla, lien_arm, hli, ha]
          · have ha' : body.any (fun op => (Opt.poleRegs op).any fun r => decide (r ∈ dfn)) = false := by
              simpa using ha
            simp only [ha', Bool.false_eq_true, if_false] at h
            by_cases hn : finNext fin = []
            · simp only [hn, if_true, Option.some.injEq] at h
              subst h
              rw [hn] at hnx
              conv => lhs; arg 2; unfold tfTrap
              simp only [tfT, compCore] at hh ⊢
              generalize comp.door = Dr at hli hnx ⊢
              generalize tfTrap = TR at hli hnx ⊢
              generalize layer2 = L2 at hc' hia hh hla hli hgot hgc hba
              simp [nock_exec, tfR1, tfOr, tfRec1, tfR2, tfGot, tfR3, tfLien, tfR4, tfR5, listNoun, hc', hia,
                in_arm, in.has.arm_at, has_in_arm, hh, hs, loob, Ne.symm hl, genNoun, by_arm, hba, by.got.arm_at,
                got_arm, hgot, hla, lien_arm, hli, ha', hnx]
            · simp only [hn, if_false] at h
              obtain ⟨S', hp, hS'⟩ := saw_put hS i
              have hi := ih (finNext fin ++ rest) (i :: seen) S' b hS' h
              have hw := weld_gate_list layer2 ((finNext fin).map A) (rest.map A)
              rw [← List.map_append, ← listNoun_map_listN, ← listNoun_map_listN, ← listNoun_map_listN] at hw
              have hpa := in.put.arm_at
              have hcons : ∃ u v, listNoun A (finNext fin) = C u v := by
                cases e : finNext fin with
                | nil => exact absurd e hn
                | cons y ys => exact ⟨_, _, rfl⟩
              obtain ⟨u, v, huv⟩ := hcons
              rw [huv] at hnx hw
              conv => lhs; arg 2; unfold tfTrap
              simp only [tfT, compCore] at hh ⊢
              simp only [tfT, compCore, genNoun] at hi
              generalize comp.door = Dr at hli hnx hi ⊢
              generalize tfTrap = TR at hli hnx hi ⊢
              generalize layer2 = L2 at hc' hia hh hla hli hgot hgc hba hw hwa hp
              simp [nock_exec, tfR1, tfOr, tfRec1, tfR2, tfGot, tfR3, tfLien, tfR4, tfR5, tfRec2, listNoun, hc',
                hia, in_arm, in.has.arm_at, has_in_arm, hh, hs, loob, Ne.symm hl, genNoun, by_arm, hba,
                by.got.arm_at, got_arm, hgot, hla, lien_arm, hli, ha', hnx, hwa, weld_arm, hw, hpa, put_in_arm, hp,
                hi]

/-- The gate of `+soft-free` on `[o rest]`: `seen` `~`, `todo` `~[o]`, then the trap. -/
theorem tf_bat (o : Nat) (R CC : Noun) :
    nock (C tfBat (C (C (A o) R) CC)) tfBat
      = nock (C tfTrap (C (C (A o) (A 0)) (C (A 0) (C tfBat (C (C (A o) R) CC))))) tfTrap := by
  conv => { lhs; arg 2; unfold tfBat }
  generalize tfTrap = T
  simp [nock_exec]

/-- **`?.  (soft-free o last.s def)`** (`tpYN9`): where the model `softFreeF` (any fuel) gives `b`
from `[o]`, the try path goes on to `tpYNY0` (the tries last) on `&` and to `tpYNN0` (the flag) on
`|`. -/
theorem tf_test {ctx : Noun} (hc : CompIn ctx) (h15 : slot? 15 ctx = some compTypes) (FAIL PES : Nat)
    (kon : List Pole) (rub : Nat) (TOM FLAG LAT HD TR OPS CUT AXS : Noun) (o : Nat) (s : SoftCall)
    (g : Gen (TreapMap mugF)) (x : GenRest) {DEF : Noun} {dfn : List Nat} (hD : SawRel DEF dfn) (F : Nat)
    (b : Bool) (hf : softFreeF g.blocks s.last dfn F [o] [] = some b) :
    nock (C DEF (tfS FAIL PES kon rub TOM FLAG LAT HD TR OPS CUT AXS o s g x ctx)) tpYN9
      = if b then nock (C DEF (tfS FAIL PES kon rub TOM FLAG LAT HD TR OPS CUT AXS o s g x ctx)) tpYNY0
        else nock (C DEF (tfS FAIL PES kon rub TOM FLAG LAT HD TR OPS CUT AXS o s g x ctx)) tpYNN0 := by
  have ht := tf_trap hc h15 g x o s.last hD F [o] [] (A 0) b sawRel_nil hf
  have hA := tf_at
  simp only [tfT, listNoun, compCore] at ht
  conv => { lhs; arg 2; unfold tpYN9 }
  simp only [tfS, tzS, tpKR, tpS0, seS0, compCore] at ht ⊢
  generalize comp.door = Dr at hA ht ⊢
  generalize tpYNY0 = Y at ht ⊢
  generalize tpYNN0 = N at ht ⊢
  cases b <;> simp [nock_exec, tpYNT, Compiler.SoftCall.toNoun, hA, tf_arm, tf_bat, ht, loob]

end Compiler
end Formalization
