import lemmas.Compiler.CompSccLoopSoftEmitBase

/-! # `+soft-emit`: the pushes `seOps`, `seTries`, `seHed` and the `?>` (README Gaps 21.17)

On the subject after the `=^` (`seS4`, `cut` the noun of `[ops tops]`):

* **`se_ops`**: `ops` is `(weld ops.cut (murn tops.cut ..))`, the model's `ops ++ softMoves tops`;
* **`se_tries`**: `tries` is `~` when every entry of `tops` has a need `%this`;
* **`se_hed`**: `hed` is `(~(got by blocks.gen) head.s)` (a crash on a missing block);
* **`se_bad`**: the `?>  ?=([~ ~ %hop ~ *] hed)` crashes on any other head block. -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

/-- The bunt of the gates of the two `+murn`s, `[q=@ r=@uvre ned=need]`. -/
def seMurnBunt : Noun := (C (A 0) (C (A 0) (C (A 0x656e6f6e) (A 0))))

/-- The body of the gate of the `+murn` of `ops`: `[~ %mov r d]` for a `%this`/`%both` need of
register `d` other than `r`. -/
def seOpsB : Noun :=
  (C (A 8) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 54)))) (C (C (C (A 1) (A 0)) (C (A 0) (A 55))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 54)))) (C (C (C (A 1) (A 0)) (C (A 0) (A 110))) (C (A 1) (A 0)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 0) (A 58)) (C (A 0) (A 5)))) (C (C (A 1) (A 0)) (C (C (A 1) (A 0)) (C (C (A 1) (A 0x766f6d)) (C (C (A 0) (A 58)) (C (A 0) (A 5)))))))))))))

/-- The body of the gate of the `+murn` of `tries`: `~` on `%none`/`%this`. -/
def seTriesB : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 54)))) (C (C (A 1) (A 0)) (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 54))))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 54)))) (C (C (C (A 1) (A 0)) (C (C (A 0) (A 12)) (C (C (A 0) (A 26)) (C (C (A 0) (A 222)) (C (A 0) (A 223)))))) (C (C (A 1) (A 0)) (C (C (A 0) (A 12)) (C (C (A 0) (A 26)) (C (A 0) (A 27)))))))))))

theorem seOps_eq : seOps =
    (C (A 8) (C (C (A 9) (C (A 0xbef7f4) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 12)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0x17defea) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 13)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) seMurnBunt) (C (C (A 1) seOpsB) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2)))))))) := rfl

theorem seTries_eq : seTries =
    (C (A 8) (C (C (A 9) (C (A 0x17defea) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 29)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) seMurnBunt) (C (C (A 1) seTriesB) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) := rfl

/-! ## `+murn` on typed lists -/

theorem se_murn_loop {α β : Type} (E : α → Noun) (F : β → Noun) (c bp bs bc : Noun)
    (g : α → Option β) :
    ∀ (l : List α), (∀ a ∈ l, nock (C bp (C (E a) bc)) bp = some (unitNoun F (g a))) →
    nock (C murn.loop (C murn.battery (C (C (listN (l.map E)) (C bp (C bs bc))) c))) murn.loop
      = some (listN ((l.filterMap g).map F)) := by
  intro l
  induction l with
  | nil => intro _; nock_open murn.loop; simp [nock_exec]
  | cons x xs ih =>
    intro hf
    have hx := hf x (by simp)
    have hxs := ih (fun y hy => hf y (by simp [hy]))
    nock_open murn.loop
    cases e : g x with
    | none => rw [e] at hx; simp [nock_exec, hx, hxs, unitNoun, e, List.filterMap_cons]
    | some b => rw [e] at hx; simp [nock_exec, hx, hxs, unitNoun, e, List.filterMap_cons]

theorem se_murn_gate {α β : Type} (E : α → Noun) (F : β → Noun) (c : Noun) (hc : HomoIn c)
    (bp bs bc : Noun) (g : α → Option β) (l : List α)
    (hf : ∀ a ∈ l, nock (C bp (C (E a) bc)) bp = some (unitNoun F (g a))) :
    nock (C murn.battery (C (C (listN (l.map E)) (C bp (C bs bc))) c)) murn.battery
      = some (listN ((l.filterMap g).map F)) := by
  nock_open murn.battery
  simp only [nock_exec, hc, homo_arm, se_murn_loop E F c bp bs bc g l hf]

theorem se_murn_arm (c : Noun) :
    nock c murn.arm = some (C murn.battery (C (C (A 0) buntGate) c)) := by
  nock_open murn.arm; simp only [nock_exec]; rfl

/-! ## `ops` -/

/-- The function of the `+murn` of `ops` (`softMoves`). -/
def seMoveF : Nat × Nat × Need → Option Pole
  | (_, r, Need.this d) => if r = d then none else some (Pole.mov r d)
  | (_, r, Need.both d _ _) => if r = d then none else some (Pole.mov r d)
  | _ => none

theorem softMoves_eq (tops : List (Nat × Nat × Need)) : softMoves tops = tops.filterMap seMoveF := by
  unfold softMoves
  congr 1
  funext t
  obtain ⟨q, r, ned⟩ := t
  cases ned <;> rfl

theorem se_toNoun_cell (n : Need) : ∃ a b, n.toNoun = C a b := by
  cases n <;> exact ⟨_, _, rfl⟩

theorem se_ops_body (S : Noun) (t : Nat × Nat × Need) :
    nock (C seOpsB (C (seTopN t) S)) seOpsB = some (unitNoun Pole.toNoun (seMoveF t)) := by
  obtain ⟨q, r, ned⟩ := t
  cases ned with
  | pair p p' =>
    obtain ⟨a, b, hab⟩ := se_toNoun_cell p
    simp [nock_exec, seOpsB, seTopN, Need.toNoun, hab, seMoveF, unitNoun]
  | both d h t =>
    by_cases e : r = d
    · subst e; simp [nock_exec, seOpsB, seTopN, Need.toNoun, Tag.both, seMoveF, unitNoun]
    · have e' : ¬ (A r = A d) := fun h => e (by injection h)
      simp [nock_exec, seOpsB, seTopN, Need.toNoun, Tag.both, seMoveF, unitNoun, e, e', Pole.toNoun,
        Tag.mov]
  | this d =>
    by_cases e : r = d
    · subst e; simp [nock_exec, seOpsB, seTopN, Need.toNoun, Tag.this, seMoveF, unitNoun]
    · have e' : ¬ (A r = A d) := fun h => e (by injection h)
      simp [nock_exec, seOpsB, seTopN, Need.toNoun, Tag.this, seMoveF, unitNoun, e, e', Pole.toNoun,
        Tag.mov]
  | none => simp [nock_exec, seOpsB, seTopN, Need.toNoun, Tag.none, seMoveF, unitNoun]

/-- **`ops`**: `(weld ops.cut (murn tops.cut ..))`. -/
theorem se_ops (ctx : Noun) (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (x : GenRest) (o : Nat) (s : SoftCall)
    (M : Noun) (ops : List Pole) (tops : List (Nat × Nat × Need)) :
    nock (seS4 (seCutN (ops, tops)) M g x ctx o s) seOps = some (listNoun Pole.toNoun (ops ++ softMoves tops)) := by
  have hM := se_murn_gate seTopN Pole.toNoun layer2 homoIn_layer2 seOpsB seMurnBunt
    (seS4 (seCutN (ops, tops)) M g x ctx o s) seMoveF tops (fun t _ => se_ops_body _ t)
  have hW := weld_gate_list layer2 (ops.map Pole.toNoun) ((tops.filterMap seMoveF).map Pole.toNoun)
  rw [seOps_eq, softMoves_eq, cd_listNoun_listN, List.map_append]
  simp only [seS4, seS1, seS0, seCutN, compCore, cd_listNoun_listN] at hM ⊢
  generalize comp.door = Dr at hM
  generalize genNoun g x = GN at hM
  generalize Compiler.SoftCall.toNoun s = SN at hM
  simp [nock_exec, hc, weld_arm, weld.arm_at, se_murn_arm, murn.arm_at, hM, hW]

/-! ## `tries` -/

theorem se_tries_body (S : Noun) (t : Nat × Nat × Need) (h : ∃ r, t.2.2 = Need.this r) :
    nock (C seTriesB (C (seTopN t) S)) seTriesB = some (A 0) := by
  obtain ⟨q, r, ned⟩ := t
  obtain ⟨d, hd⟩ := h
  simp only at hd
  subst hd
  simp [nock_exec, seTriesB, seTopN, Need.toNoun, Tag.this, Tag.none]

/-- **`tries`** is `~` when every entry of `tops` has a need `%this`. -/
theorem se_tries (ctx : Noun) (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (x : GenRest) (o : Nat) (s : SoftCall)
    (M OPS : Noun) (ops : List Pole) (tops : List (Nat × Nat × Need)) (htops : ∀ t ∈ tops, ∃ r, t.2.2 = Need.this r) :
    nock (C OPS (seS4 (seCutN (ops, tops)) M g x ctx o s)) seTries = some (A 0) := by
  have hM := se_murn_gate seTopN (fun n : Noun => n) layer2 homoIn_layer2 seTriesB seMurnBunt
    (C OPS (seS4 (seCutN (ops, tops)) M g x ctx o s)) (fun _ => (Option.none : Option Noun)) tops
    (fun t ht => by rw [se_tries_body _ t (htops t ht)]; rfl)
  have h0 : ∀ l : List (Nat × Nat × Need), l.filterMap (fun _ => (Option.none : Option Noun)) = [] := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => simp [List.filterMap_cons, ih]
  rw [seTries_eq]
  simp only [seS4, seS1, seS0, seCutN, compCore, cd_listNoun_listN, h0, List.map_nil, listN] at hM ⊢
  generalize comp.door = Dr at hM
  generalize genNoun g x = GN at hM
  generalize Compiler.SoftCall.toNoun s = SN at hM
  simp [nock_exec, hc, se_murn_arm, murn.arm_at, hM]

/-! ## `hed` -/

/-- **`hed`**: `(~(got by blocks.gen) head.s)`. -/
theorem se_hed (ctx : Noun) (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (x : GenRest) (o : Nat) (s : SoftCall)
    (CUT M OPS : Noun) :
    nock (C (A 0) (C OPS (seS4 CUT M g x ctx o s))) seHed = (HoonMap.get g.blocks s.head).map Blob.toNoun := by
  have hget := getF_hoonMap Blob.toNoun g.blocks s.head
  have hgc : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
    ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
  simp only [seS4, seS1, seS0, compCore]
  generalize comp.door = Dr
  cases e : HoonMap.get g.blocks s.head with
  | none =>
    rw [e] at hget
    have hgot := got_gate_nil layer2 hgc (A s.head) _ hget
    simp [seHed, nock_exec, genNoun, hc, by_arm, by.arm_at, by.got.arm_at, got_arm, hgot,
      Compiler.SoftCall.toNoun]
  | some b =>
    rw [e] at hget
    have hgot := got_gate layer2 hgc (A s.head) _ _ hget
    simp [seHed, nock_exec, genNoun, hc, by_arm, by.arm_at, by.got.arm_at, got_arm, hgot,
      Compiler.SoftCall.toNoun]

/-! ## The `?>` -/

/-- **The `?>  ?=([~ ~ %hop ~ *] hed)` crashes** on any other head block. -/
theorem se_bad (hd : Blob) (h : ¬ (hd.par = [] ∧ hd.body = [] ∧ ∃ t, hd.fin = Termin.hop t ∧ t.args = [])) (S R : Noun) :
    nock (C hd.toNoun S) (C (A 6) (C seHedT (C R (C (A 0) (A 0))))) = none := by
  obtain ⟨par, body, fin⟩ := hd
  simp only at h
  cases par with
  | cons p ps => simp [nock_exec, seHedT, Blob.toNoun, listNoun]
  | nil =>
  cases body with
  | cons b bs => simp [nock_exec, seHedT, Blob.toNoun, listNoun]
  | nil =>
  cases fin with
  | hop t =>
    obtain ⟨args, there⟩ := t
    cases args with
    | nil => simp at h
    | cons a as => simp [nock_exec, seHedT, Blob.toNoun, listNoun, Termin.toNoun, Jmp.toNoun, Tag.hop]
  | _ =>
    simp [nock_exec, seHedT, Blob.toNoun, listNoun, Termin.toNoun, Tag.hop, Tag.clq, Tag.eqq, Tag.brn,
      Tag.brz, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti]

end Compiler
end Formalization
