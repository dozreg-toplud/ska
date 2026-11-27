import lemmas.Compiler.PokeLinkRest
import lemmas.Compiler.SkaCull
import lemmas.Compiler.Mi

/-!
# `new-code` and the gate `dat` of `spRest`, linked

* `newCodeLinkAt` (**`NewCodeLinkAt`** at `codeN = codeNoun fl code`): push 7,
  `~(rep by baked)` with `~(has by code.lon)` and `~(put by acc)`, from `~`, is
  `newCode code baked`.  The fold is over the pre-order of `baked`'s treap
  (`rep_gate_on`), which is `FinMap.rap baked` (`FinMap.preorder_toNoun`), the
  order `newCode` folds in.
* `datLinkAt` (**`DatLinkAt`**, no side condition): the gate `dat` slammed on a
  bell is `unitNoun FDatum.toNoun (pokeDatF dats memo b)`: `get:by` on `dats`,
  else `get:by` of `less.b` in `(gut:mi memo.lon fol.b)` (`mi_gut_gate`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeM

/-! ## `new-code` -/

/-- The door `~(rep by baked)` of push 7. -/
def srNewDoor : Noun :=
  C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 767) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))

/-- The bunt of the sample of the gate of `new-code`. -/
def srNewBunt : Noun :=
  C (C (C (C (A 1) (A 0)) (C (A 0) (A 0))) (C (C (A 0) (A 0)) (C (A 0) (A 1)))) (A 0)

/-- The battery of the gate of `new-code`:
`?:((~(has by code.lon) b) acc (~(put by acc) b v))`. -/
def srNewGB : Noun :=
  C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 3061) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1fffd6))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 56))) (C (A 0) (A 2)))))))) (C (C (A 0) (A 13)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 56)) (C (A 0) (A 57)))) (C (A 0) (A 2))))))))))

theorem srNew_eq : srNew = C (A 8) (C srNewDoor (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3))
    (C (A 8) (C (C (A 1) srNewBunt) (C (C (A 1) srNewGB) (C (A 0) (A 1)))))))) (C (A 0) (A 2))))))) := rfl

/-- `+get:by` on the noun of `code.lon`. -/
theorem codeNoun_getF (fl : Flags) (code : FinMap Bell (VarEntry FinMap)) (k : Bell) :
    getF mugF (TKey.enc k) (codeNoun fl code)
      = some (unitNoun (fun x => x) ((code.get k).map fun e => C e.nomm.toNoun (fl code k))) := by
  unfold codeNoun
  rw [FinMap.getF_toNoun]
  rfl

/-- The step of `newCode`, on a node noun of `baked`. -/
noncomputable def ncF (code baked : FinMap Bell (VarEntry FinMap)) (x : Noun) (s : FinMap Bell (VarEntry FinMap)) :
    FinMap Bell (VarEntry FinMap) :=
  match FinMap.entry baked x with
  | some e => if Treap.has code e.1 then s else Treap.put s e.1 e.2
  | none => s

section NewCode

variable (root : Ident) (r1 r2 r3 r4 jRest callsN varsN seekN hotN : Noun)
  (gr : Callgraph FinMap × Noun)
  (r : Callgraph FinMap × FinMap Bell (FDatum FinMap) × Memo FinMap × FDatum FinMap × Noun)

set_option maxHeartbeats 1000000 in
/-- The gate of `new-code` on a node `[k v]` and an accumulator. -/
theorem nc_gate (fl : Flags) (code baked : FinMap Bell (VarEntry FinMap)) (vr : Noun) (k : Bell) (v : VarEntry FinMap)
    (s : FinMap Bell (VarEntry FinMap)) :
    nock (C srNewGB (C (C (C (TKey.enc k) (varEntryNoun v)) (s.toNoun varEntryNoun))
        (C (baked.toNoun varEntryNoun)
          (srSp root r1 r2 r3 r4 jRest (codeNoun fl code) callsN varsN seekN hotN gr r (codeNoun fl code) vr))))
      srNewGB = some ((if Treap.has code k then s else Treap.put s k v).toNoun varEntryNoun) := by
  have hhas := has_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ (TKey.enc k)
    (codeNoun fl code) _ (codeNoun_getF fl code k)
  have hput := put_gate (mug := mugF) layer2 gorIn_morIn_layer2 (TKey.enc k) (varEntryNoun v)
    (s.toNoun varEntryNoun) _ (FinMap.putF_toNoun varEntryNoun s k v)
  unfold srNewGB
  cases e : code.get k with
  | none =>
    have hh : Treap.has code k = false := by simp [Treap.has, Treap.get, e]
    simp only [e, Option.map_none, unitNoun] at hhas
    simp only [hh]
    simp [srSp, srS3x, srS0, spAfter, spT0, nock_exec, ana_l2, by.arm_at, by_arm, by.has.arm_at, has_arm,
      by.put.arm_at, put_arm, hhas, hput]
    rfl
  | some w =>
    have hh : Treap.has code k = true := by simp [Treap.has, Treap.get, e]
    simp only [e, Option.map_some, unitNoun] at hhas
    simp only [hh]
    simp [srSp, srS3x, srS0, spAfter, spT0, nock_exec, ana_l2, by.arm_at, by_arm, by.has.arm_at, has_arm, hhas]

theorem nc_foldl (code baked : FinMap Bell (VarEntry FinMap)) :
    ∀ (L : List (Bell × VarEntry FinMap)), (∀ e ∈ L, baked.1 e.1 = some e.2) → ∀ s,
    (L.map fun e => C (TKey.enc e.1) (varEntryNoun e.2)).foldl (fun s x => ncF code baked x s) s
      = L.foldl (fun acc e => if Treap.has code e.1 then acc else Treap.put acc e.1 e.2) s
  | [], _, _ => rfl
  | e :: L, h, s => by
    have he := h e List.mem_cons_self
    simp only [List.map_cons, List.foldl_cons]
    have : ncF code baked (C (TKey.enc e.1) (varEntryNoun e.2)) s
        = if Treap.has code e.1 then s else Treap.put s e.1 e.2 := by
      simp [ncF, FinMap.entry, FinMap.decode?_enc, he]
    rw [this]
    exact nc_foldl code baked L (fun e' he' => h e' (List.mem_cons_of_mem _ he')) _

set_option maxHeartbeats 1000000 in
/-- **`NewCodeLinkAt`**, at the noun of `code.lon` with any flags. -/
theorem newCodeLinkAt (fl : Flags) (code baked : FinMap Bell (VarEntry FinMap)) (vr : Noun) :
    NewCodeLinkAt root r1 r2 r3 r4 jRest (codeNoun fl code) callsN varsN seekN hotN gr r code baked vr := by
  unfold NewCodeLinkAt
  have hr := rep_gate_on (fun s : FinMap Bell (VarEntry FinMap) => s.toNoun varEntryNoun) (ncF code baked)
    by.battery layer2 srNewGB (C (C (C (A 1) (A 0)) (C (A 0) (A 0))) (C (C (A 0) (A 0)) (C (A 0) (A 1))))
    (C (baked.toNoun varEntryNoun)
      (srSp root r1 r2 r3 r4 jRest (codeNoun fl code) callsN varsN seekN hotN gr r (codeNoun fl code) vr))
    (baked.toNoun varEntryNoun) (Tree.of_isMap (FinMap.isMap_toNoun varEntryNoun baked)) Treap.empty ?hf
  · have he : FinMap.toNoun varEntryNoun (Treap.empty : FinMap Bell (VarEntry FinMap)) = A 0 :=
      FinMap.toNoun_empty _
    rw [he] at hr
    rw [FinMap.preorder_toNoun, nc_foldl code baked _ (fun e he => (FinMap.mem_rap baked e.1 e.2).1 he)] at hr
    simp only [srSp, srS3x, srS0, spAfter, spT0] at hr
    rw [srNew_eq]
    unfold srNewDoor srNewBunt
    simp [srSp, srS3x, srS0, spAfter, spT0, nock_exec, ana_l2, by.arm_at, by_arm, by.rep.arm_at, rep_arm, hr]
    rfl
  · intro x hx s
    rw [FinMap.preorder_toNoun] at hx
    obtain ⟨⟨k, v⟩, hm, rfl⟩ := List.mem_map.1 hx
    have hkv := (FinMap.mem_rap baked k v).1 hm
    have : ncF code baked (C (TKey.enc k) (varEntryNoun v)) s = if Treap.has code k then s else Treap.put s k v := by
      simp [ncF, FinMap.entry, FinMap.decode?_enc, hkv]
    rw [this]
    exact nc_gate root r1 r2 r3 r4 jRest callsN varsN seekN hotN gr r fl code baked vr k v s

end NewCode

/-! ## The gate `dat` -/

section Dat

variable (root : Ident) (r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN : Noun)
  (gr : Callgraph FinMap × Noun)
  (r : Callgraph FinMap × FinMap Bell (FDatum FinMap) × Memo FinMap × FDatum FinMap × Noun)

set_option maxHeartbeats 1000000 in
/-- **`DatLinkAt`**: the gate `dat` slammed on a bell `b` is the unit of
`pokeDatF`: `(~(get by dats) b)`, else `(~(get by (gut:mi memo.lon fol.b)) less.b)`
with its datum. -/
theorem datLinkAt : DatLinkAt root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r := by
  intro b
  have hg1 : nock (C by.get.battery (C (C b.less.toNoun b.fol) (C by.battery (C (Treap.toNoun FDatum.toNoun r.2.1)
      layer2)))) by.get.battery = some (unitNoun FDatum.toNoun (FinMap.get r.2.1 b)) :=
    get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ (TKey.enc b)
      (FinMap.toNoun FDatum.toNoun r.2.1) _ (FinMap.getF_toNoun FDatum.toNoun r.2.1 b)
  have hgut := mi_gut_pill r.2.2.1 b.fol
  have hg2 : nock (C by.get.battery (C b.less.toNoun (C by.battery (C (innerNoun (gutMi r.2.2.1 b.fol))
      layer2)))) by.get.battery = some (unitNoun entryNoun (FinMap.get (gutMi r.2.2.1 b.fol) b.less)) :=
    get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ (TKey.enc b.less)
      (innerNoun (gutMi r.2.2.1 b.fol)) _ (FinMap.getF_toNoun entryNoun (gutMi r.2.2.1 b.fol) b.less)
  unfold pokeDatF
  cases e1 : Treap.get r.2.1 b with
  | some d =>
    have e1' : FinMap.get r.2.1 b = some d := e1
    simp only [e1', unitNoun] at hg1
    unfold srDatBat
    simp [srS0, spAfter, spT0, nock_exec, ana_l2, by.arm_at, by_arm, by.get.arm_at, get_arm, hg1, unitNoun,
      Bell.toNoun]
  | none =>
    have e1' : FinMap.get r.2.1 b = none := e1
    simp only [e1', unitNoun] at hg1
    cases e2 : Treap.get (gutMi r.2.2.1 b.fol) b.less with
    | some w =>
      have e2' : FinMap.get (gutMi r.2.2.1 b.fol) b.less = some w := e2
      simp only [e2', unitNoun, entryNoun] at hg2
      unfold srDatBat
      simp [srS0, spAfter, spT0, nock_exec, ana_l2, by.arm_at, by_arm, by.get.arm_at, get_arm, hg1, hg2,
        mi.arm_at, mi_arm, mi.gut.arm_at, mi_gut_arm, hgut, unitNoun, Bell.toNoun]
    | none =>
      have e2' : FinMap.get (gutMi r.2.2.1 b.fol) b.less = none := e2
      simp only [e2', unitNoun] at hg2
      unfold srDatBat
      simp [srS0, spAfter, spT0, nock_exec, ana_l2, by.arm_at, by_arm, by.get.arm_at, get_arm, hg1, hg2,
        mi.arm_at, mi_arm, mi.gut.arm_at, mi_gut_arm, hgut, unitNoun, Bell.toNoun]

end Dat

end Compiler
end Formalization
