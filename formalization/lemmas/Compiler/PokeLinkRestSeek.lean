import lemmas.Compiler.PokeLinkRestNew

/-!
# The writes of `seek.lon` and `calls.lon` in the tail of `spRest`

Pushes 12 and 13 of `spRest` (`srSeek`, `srCalls`, 106 cells each) are
`[10 [ax F] [0 1]]`: `F` is `~(rep by new-code)` with the gate
`(~(put by acc) b seek.v)` (resp. `calls.v`) from `seek.lon` (resp.
`calls.lon`).  On a subject whose `seek` (resp. `calls`) is the noun of the
old table `code`, the write is that of `addCode code nc`
(`srSeek_run`, `srCalls_run`).  The sample's bunt `[*bell *entry]` reads
the library only (`tailBunt_run`, by the kernel).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeM

/-- The door `~(rep by new-code)` of pushes 12 and 13. -/
def srTailDoor : Noun :=
  C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 767) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2)))))))

/-- The bunt `[*bell *[nomm calls seek]]` of the gates of pushes 12 and 13. -/
def srTailBuntH : Noun :=
  C (C (A 7) (C (C (A 9) (C (A 382) (C (A 0) (A 0x1ffff)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (C (A 7) (C (C (A 9) (C (A 22) (C (A 0) (A 0x1ffff)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (C (A 7) (C (C (A 8) (C (C (A 9) (C (A 6098) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 382) (C (A 0) (A 0x1ffff))))))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (A 7) (C (C (A 9) (C (A 10) (C (A 0) (A 0x7ffff)))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))

/-- The gate battery `(~(put by acc) b x.v)` with `x.v` at axis `ax` (`231`
`seek`, `230` `calls`). -/
def srTailGB (ax : Nat) : Noun :=
  C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 56)) (C (A 0) (A ax)))) (C (A 0) (A 2)))))))

/-- The write at `wax` of the `+rep` with the gate `srTailGB gax`. -/
def srTailW (wax gax : Nat) : Noun :=
  C (A 10) (C (C (A wax) (C (A 8) (C srTailDoor (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3))
    (C (A 8) (C (C srTailBuntH (C (A 0) (A wax))) (C (C (A 1) (srTailGB gax)) (C (A 0) (A 1)))))))) (C (A 0) (A 2)))))))))
    (C (A 0) (A 1)))

theorem srSeek_eq : srSeek = srTailW 0x7fff5f 231 := rfl
theorem srCalls_eq : srCalls = srTailW 0x3fffae 230 := rfl

section Tail

variable (root : Ident) (r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN : Noun)
  (gr : Callgraph FinMap × Noun)
  (r : Callgraph FinMap × FinMap Bell (FDatum FinMap) × Memo FinMap × FDatum FinMap × Noun)

/-- The subject of pushes 12 and 13: `[new-cores [sccs [new-code [baked spine]]]]`. -/
noncomputable def srT12 (nco q ncN bkN g0 rN : Noun) : Noun :=
  C nco (C q (C ncN (C bkN (srS3x g0 (srS0 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r) rN))))

/-- `srS0` as a skeleton: what the tail reads of it is the library. -/
noncomputable def srSk (a b c d e f : Noun) : Noun := C a (C b (C c (C d (C e (C spX (C spBat (C f ana)))))))

theorem srS0_sk : srS0 root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r =
    srSk (Treap.toNoun FDatum.toNoun r.2.1) r.2.2.2.1.toNoun (Treap.toNoun FDatum.toNoun r.1)
      (C (Treap.toNoun FDatum.toNoun gr.1) gr.2) (identNoun root)
      (C (identNoun root) (C (C (C r1 (C r2 (C r3 (C r4 jRest)))) (C (memoNoun r.2.2.1) (C codeN (C callsN (C varsN seekN)))))
        hotN)) := rfl

/-- The value of the bunt, on the pill. -/
noncomputable def srTailBuntV : Noun :=
  (evalFuel 3000 (C (A 0) (C (A 0) (C (A 0) (C (A 0) (srS3x (A 0) (srSk (A 0) (A 0) (A 0) (A 0) (A 0) (A 0)) (A 0))))))
    srTailBuntH).getD (A 0)

theorem tailBunt_run (nco q ncN bkN g0 rN a b c d e f : Noun) :
    nock (C nco (C q (C ncN (C bkN (srS3x g0 (srSk a b c d e f) rN))))) srTailBuntH = some srTailBuntV :=
  nock_of_evalFuel (fuel := 3000) (by kernel_rfl)

/-- The sample of `+ska-poke` inside `srSk`, with `lon` laid out. -/
noncomputable def srSam (e0 J mN cN caN vN sN hN : Noun) : Noun := C e0 (C (C J (C mN (C cN (C caN (C vN sN))))) hN)

/-- The subject of the tail with its parts named. -/
noncomputable def srTS (nco q ncN bkN g0 rN a b c d e e0 J mN cN caN vN sN hN : Noun) : Noun :=
  C nco (C q (C ncN (C bkN (srS3x g0 (srSk a b c d e (srSam e0 J mN cN caN vN sN hN)) rN))))

/-- The step of the writes: `put` of a node of `nc`. -/
noncomputable def putF' (nc : FinMap Bell (VarEntry FinMap)) (x : Noun) (s : FinMap Bell (VarEntry FinMap)) :
    FinMap Bell (VarEntry FinMap) :=
  match FinMap.entry nc x with
  | some e => Treap.put s e.1 e.2
  | none => s

theorem putF'_foldl (nc : FinMap Bell (VarEntry FinMap)) :
    ∀ (L : List (Bell × VarEntry FinMap)), (∀ e ∈ L, nc.1 e.1 = some e.2) → ∀ s,
    (L.map fun e => C (TKey.enc e.1) (varEntryNoun e.2)).foldl (fun s x => putF' nc x s) s
      = L.foldl (fun acc e => Treap.put acc e.1 e.2) s
  | [], _, _ => rfl
  | e :: L, h, s => by
    have he := h e List.mem_cons_self
    simp only [List.map_cons, List.foldl_cons]
    have : putF' nc (C (TKey.enc e.1) (varEntryNoun e.2)) s = Treap.put s e.1 e.2 := by
      simp [putF', FinMap.entry, FinMap.decode?_enc, he]
    rw [this]
    exact putF'_foldl nc L (fun e' he' => h e' (List.mem_cons_of_mem _ he')) _

set_option maxHeartbeats 1000000 in
theorem seek_gate (nco q ncN bkN g0 rN a b c d e e0 J mN cN caN vN sN hN : Noun) (k : Bell) (v : VarEntry FinMap)
    (s : FinMap Bell (VarEntry FinMap)) :
    nock (C (srTailGB 231) (C (C (C (TKey.enc k) (varEntryNoun v)) (s.toNoun fun e => e.seek.toNoun))
        (srTS nco q ncN bkN g0 rN a b c d e e0 J mN cN caN vN sN hN))) (srTailGB 231)
      = some ((Treap.put s k v).toNoun fun e => e.seek.toNoun) := by
  have hput := put_gate (mug := mugF) layer2 gorIn_morIn_layer2 (TKey.enc k) v.seek.toNoun
    (s.toNoun fun e => e.seek.toNoun) _ (FinMap.putF_toNoun (fun e : VarEntry FinMap => e.seek.toNoun) s k v)
  unfold srTailGB
  simp [srTS, srS3x, srSk, srSam, varEntryNoun, nock_exec, ana_l2, by.arm_at, by_arm, by.put.arm_at, put_arm, hput]
  rfl

set_option maxHeartbeats 1000000 in
theorem calls_gate (nco q ncN bkN g0 rN a b c d e e0 J mN cN caN vN sN hN : Noun) (k : Bell) (v : VarEntry FinMap)
    (s : FinMap Bell (VarEntry FinMap)) :
    nock (C (srTailGB 230) (C (C (C (TKey.enc k) (varEntryNoun v)) (s.toNoun fun e => FinMap.setNoun e.calls))
        (srTS nco q ncN bkN g0 rN a b c d e e0 J mN cN caN vN sN hN))) (srTailGB 230)
      = some ((Treap.put s k v).toNoun fun e => FinMap.setNoun e.calls) := by
  have hput := put_gate (mug := mugF) layer2 gorIn_morIn_layer2 (TKey.enc k) (FinMap.setNoun v.calls)
    (s.toNoun fun e => FinMap.setNoun e.calls) _
    (FinMap.putF_toNoun (fun e : VarEntry FinMap => FinMap.setNoun e.calls) s k v)
  unfold srTailGB
  simp [srTS, srS3x, srSk, srSam, varEntryNoun, nock_exec, ana_l2, by.arm_at, by_arm, by.put.arm_at, put_arm, hput]
  rfl

theorem nock_buntH_pair (s g : Noun) :
    nock s (C srTailBuntH g) = (nock s srTailBuntH).bind fun a => (nock s g).bind fun b => some (C a b) :=
  nock_pair_of s srTailBuntH g ⟨_, _, rfl⟩

set_option maxHeartbeats 2000000 in
/-- **The write of `seek.lon`** (push 12): on a subject whose `seek` is the noun of
the old table, `~(rep by new-code)` with `put` writes that of `addCode code nc`. -/
theorem srSeek_run (nco q bkN g0 rN a b c d e e0 J mN cN caN vN sN hN : Noun) (code nc : FinMap Bell (VarEntry FinMap))
    (hs : sN = code.toNoun (fun e : VarEntry FinMap => e.seek.toNoun)) :
    nock (srTS nco q (nc.toNoun varEntryNoun) bkN g0 rN a b c d e e0 J mN cN caN vN sN hN) srSeek
      = some (srTS nco q (nc.toNoun varEntryNoun) bkN g0 rN a b c d e e0 J mN cN caN vN ((addCode code nc).toNoun fun e => e.seek.toNoun) hN) := by
  have hb := tailBunt_run nco q (nc.toNoun varEntryNoun) bkN g0 rN a b c d e (srSam e0 J mN cN caN vN sN hN)
  have hr := rep_gate_on (fun s : FinMap Bell (VarEntry FinMap) => s.toNoun (fun e : VarEntry FinMap => e.seek.toNoun)) (putF' nc)
    by.battery layer2 (srTailGB 231) srTailBuntV
    (srTS nco q (nc.toNoun varEntryNoun) bkN g0 rN a b c d e e0 J mN cN caN vN sN hN)
    (nc.toNoun varEntryNoun) (Tree.of_isMap (FinMap.isMap_toNoun varEntryNoun nc)) code ?hf
  · rw [FinMap.preorder_toNoun, putF'_foldl nc _ (fun e he => (FinMap.mem_rap nc e.1 e.2).1 he)] at hr
    rw [← hs] at hr
    subst hs
    simp only [srTS, srS3x, srSk, srSam] at hr hb
    rw [srSeek_eq]
    unfold srTailW srTailDoor
    simp [srTS, srS3x, srSk, srSam, nock_exec, ana_l2, by.arm_at, by_arm, by.rep.arm_at, rep_arm, nock_buntH_pair, hb, hr]
    rfl
  · intro x hx s
    rw [FinMap.preorder_toNoun] at hx
    obtain ⟨⟨k, v⟩, hm, rfl⟩ := List.mem_map.1 hx
    have hkv := (FinMap.mem_rap nc k v).1 hm
    have : putF' nc (C (TKey.enc k) (varEntryNoun v)) s = Treap.put s k v := by
      simp [putF', FinMap.entry, FinMap.decode?_enc, hkv]
    rw [this]
    exact seek_gate nco q _ bkN g0 rN a b c d e e0 J mN cN caN vN sN hN k v s

set_option maxHeartbeats 2000000 in
/-- **The write of `calls.lon`** (push 13): on a subject whose `calls` is the noun of
the old table, `~(rep by new-code)` with `put` writes that of `addCode code nc`. -/
theorem srCalls_run (nco q bkN g0 rN a b c d e e0 J mN cN caN vN sN hN : Noun) (code nc : FinMap Bell (VarEntry FinMap))
    (hs : caN = code.toNoun (fun e : VarEntry FinMap => FinMap.setNoun e.calls)) :
    nock (srTS nco q (nc.toNoun varEntryNoun) bkN g0 rN a b c d e e0 J mN cN caN vN sN hN) srCalls
      = some (srTS nco q (nc.toNoun varEntryNoun) bkN g0 rN a b c d e e0 J mN cN ((addCode code nc).toNoun fun e => FinMap.setNoun e.calls) vN sN hN) := by
  have hb := tailBunt_run nco q (nc.toNoun varEntryNoun) bkN g0 rN a b c d e (srSam e0 J mN cN caN vN sN hN)
  have hr := rep_gate_on (fun s : FinMap Bell (VarEntry FinMap) => s.toNoun (fun e : VarEntry FinMap => FinMap.setNoun e.calls)) (putF' nc)
    by.battery layer2 (srTailGB 230) srTailBuntV
    (srTS nco q (nc.toNoun varEntryNoun) bkN g0 rN a b c d e e0 J mN cN caN vN sN hN)
    (nc.toNoun varEntryNoun) (Tree.of_isMap (FinMap.isMap_toNoun varEntryNoun nc)) code ?hf
  · rw [FinMap.preorder_toNoun, putF'_foldl nc _ (fun e he => (FinMap.mem_rap nc e.1 e.2).1 he)] at hr
    rw [← hs] at hr
    subst hs
    simp only [srTS, srS3x, srSk, srSam] at hr hb
    rw [srCalls_eq]
    unfold srTailW srTailDoor
    simp [srTS, srS3x, srSk, srSam, nock_exec, ana_l2, by.arm_at, by_arm, by.rep.arm_at, rep_arm, nock_buntH_pair, hb, hr]
    rfl
  · intro x hx s
    rw [FinMap.preorder_toNoun] at hx
    obtain ⟨⟨k, v⟩, hm, rfl⟩ := List.mem_map.1 hx
    have hkv := (FinMap.mem_rap nc k v).1 hm
    have : putF' nc (C (TKey.enc k) (varEntryNoun v)) s = Treap.put s k v := by
      simp [putF', FinMap.entry, FinMap.decode?_enc, hkv]
    rw [this]
    exact calls_gate nco q _ bkN g0 rN a b c d e e0 J mN cN caN vN sN hN k v s

end Tail

end Compiler
end Formalization
