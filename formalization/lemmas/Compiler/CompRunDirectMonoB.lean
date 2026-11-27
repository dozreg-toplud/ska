import lemmas.Compiler.CompRunDirectMonoL
import lemmas.Compiler.CompRunDirectC

/-!
# The direct call of `%2` under `mono` `&`: the call blocks (step `7`)

README Gaps 19.  Step `7` of the call (`crDKc7`) at `mono` `A 0` (the Hoon
`&`), with any value of `sof` (pushed at step `6`, never read under `mono`
`&`), against the blocks of track J's `monoBlocks` (`Ska/CompDirectM.lean`)
before `+mono-try-call`:

* `crdBlockMM`: under `%done` `+re` (`sub-pes`), the blocks `opt` `[~ ~ %jmp b
  sub-v]` and `pes` `[~ ~ %jsp b sub-pes]` (`crD7Dm`); otherwise
  `+simple-next`, `+kerf`, `+re` twice (`merged`, `sub-pes`), the block
  `merge` `[~[merged] [%mov merged pro]~ %hop ~ out]`, `+re` twice
  (`pro-opt`, `pro-pes`), the blocks `opt` `[~ [%cal b sub-v pro-opt]~ %hop
  ~[`pro-opt] merge]` and `pes` `[~ [%csl b sub-pes pro-pes]~ %hop
  ~[`pro-pes] merge]` (`crD7Nm`); the product `[opt sub-pes pes]`.
* `crd_blkM_done`, `crd_blkM_next`: the pill's step `7` is `crdBlockMM`.
* `monoBlocks_eq`: `monoBlocks` is `crdBlockMM` then `monoTryCall`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

variable {ctx : Noun}

/-- The subject of step `7` with any `sof`. -/
abbrev crdS6m (SOF V5 SV SN V2 PV S : Noun) : Noun :=
  C SOF (C V5 (C SV (C SN (C V2 (C (A 0) (C PV S))))))

/-- **The model of step `7` under `mono` `&`**: the blocks before
`+mono-try-call`, the product `(opt, sub-pes, pes)`. -/
noncomputable def crdBlockMM (b : Bell) (subV : List Nat) : CGoalL CSet → CM (TreapMap mugF) (Nat × Nat × Nat)
  | CGoalL.done => do
      let subPes ← re
      let opt ← emit ⟨[], [], Termin.jmp b subV⟩
      let pes ← emit ⟨[], [], Termin.jsp b subPes⟩
      pure (opt, subPes, pes)
  | g => do
      let nex ← simpleNextL g
      let (out, pro) ← kerf nex
      let merged ← re
      let subPes ← re
      let merge ← emit ⟨[merged], [Pole.mov merged pro], Termin.hop (jmp0 out)⟩
      let proOpt ← re
      let proPes ← re
      let opt ← emit ⟨[], [Pole.cal b subV proOpt], Termin.hop ⟨[some proOpt], merge⟩⟩
      let pes ← emit ⟨[], [Pole.csl b subPes proPes], Termin.hop ⟨[some proPes], merge⟩⟩
      pure (opt, subPes, pes)

/-- The noun of the product of step `7` under `mono` `&`. -/
def crdBlkN (p : (Nat × Nat × Nat) × Gen (TreapMap mugF)) (x : GenRest) : Noun :=
  C (C (A p.1.1) (C (A p.1.2.1) (A p.1.2.2))) (genNoun p.2 x)

/-- **`monoBlocks`** is the blocks of step `7` then `+mono-try-call`. -/
theorem monoBlocks_eq (b : Bell) (subNed : Need) (goal : CGoalL CSet) :
    (monoBlocks b subNed goal : CM (TreapMap mugF) (Nat × Nat)) = (do
      let (opt, subPes, pes) ← crdBlockMM b (flattenNeed subNed) goal
      let o ← monoTryCall subNed opt subPes pes
      pure (subPes, o)) := by
  funext g
  cases goal with
  | done =>
    simp only [monoBlocks, crdBlockMM, bind_apply, re_apply, cf_emit_g, Option.bind_some, pure_apply]
  | next laz th =>
    simp only [monoBlocks, crdBlockMM, bind_apply]
    cases e1 : simpleNextL (S := CSet) (Map := TreapMap mugF) (CGoalL.next laz th) g with
    | none => rfl
    | some r =>
      simp only [Option.bind_some]
      cases e2 : kerf (Map := TreapMap mugF) r.1 r.2 with
      | none => rfl
      | some r2 => simp only [Option.bind_some, re_apply, cf_emit_g, pure_apply]
  | pick z o =>
    simp only [monoBlocks, crdBlockMM, bind_apply]
    cases e1 : simpleNextL (S := CSet) (Map := TreapMap mugF) (CGoalL.pick z o) g with
    | none => rfl
    | some r =>
      simp only [Option.bind_some]
      cases e2 : kerf (Map := TreapMap mugF) r.1 r.2 with
      | none => rfl
      | some r2 => simp only [Option.bind_some, re_apply, cf_emit_g, pure_apply]

/-- **Step `7` under `%done` and `mono` `&`** (`crD7Dm`): `+re`, the
`+emit` of `[~ ~ (jump-op ~)]` (`%jmp b sub-v`) and of `[~ ~ (jump-op
`sub-pes)]` (`%jsp b sub-pes`), no ring. -/
theorem crd_blkM_done (hc : CompIn ctx) (x : GenRest) (SOF V5 V2 PV : Noun) (subNed : Need) (p q : Nomm)
    (b : Bell) (region : List Nat) (sup : Noun) (g : Gen (TreapMap mugF)) :
    nock (crdS6m SOF V5 (listNoun A (flattenNeed subNed)) subNed.toNoun V2 PV
      (crSubj (A 0) (crdN p q b) (CGoalL.done : CGoalL CSet).toNoun (listNoun A region) sup (compCore g x ctx)))
      crDKc7
      = (crdBlockMM b (flattenNeed subNed) CGoalL.done g).map fun p => crdBlkN p x := by
  have hre := comp_re' ctx x g
  have he1 := cf_emit (x := x) hc (reG g) ⟨[], [], Termin.jmp b (flattenNeed subNed)⟩
  have he2 := cf_emit (x := x) hc (cfEmitG ⟨[], [], Termin.jmp b (flattenNeed subNed)⟩ (reG g))
    ⟨[], [], Termin.jsp b g.re⟩
  simp only [Blob.toNoun, listNoun, Termin.toNoun, Tag.jmp, Tag.jsp] at he1 he2
  have hD := comp_emit_at
  have hDr := comp_re_at
  simp only [crdBlockMM, bind_apply, re_apply, cf_emit_g, Option.bind_some, pure_apply, Option.map_some]
  simp only [crSubj, compCore, reG] at hre he1 he2 ⊢
  generalize comp.door = Dr at hre he1 he2 hD hDr ⊢
  unfold crDKc7 crD7 crD7Op crD7Jop crD7T crD7D crD7Dm
  simp [nock_exec, CGoalL.toNoun, hD, hDr, hre, comp_emit_arm, he1, he2, crdBlkN, cf_emitG_re]

/-! ## The cut of `crD7Nm` (`tools/gen/monoblk.py`): seven `=^` pushes -/

/-- The last part of `crD7Nm`. -/
def crNML : Noun :=
  (C (C (C (A 0) (A 6)) (C (C (A 0) (A 126)) (C (A 0) (A 2)))) (C (A 0) (A 0xfffffe)))

/-- The value of push `0` of `crD7Nm`. -/
def crNMv0 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 0x7fff))))))

/-- The value of push `1` of `crD7Nm`. -/
def crNMv1 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 0xffff))))))

/-- The value of push `2` of `crD7Nm`. -/
def crNMv2 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 0x1ffff)))) (C (A 9) (C (A 2) (C
    (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 6)) (C (A 1) (A 0))))) (C (C (A 7) (C (C
    (A 0) (A 3)) (C (C (C (A 1) (A 0x766f6d)) (C (C (A 0) (A 6)) (C (A 0) (A 29)))) (C (A 1) (A 0))))) (C (C (A
    7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A
    60))))))) (C (A 0) (A 2))))))))))

/-- The value of push `3` of `crD7Nm`. -/
def crNMv3 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 0x3ffff))))))

/-- The value of push `4` of `crD7Nm`. -/
def crNMv4 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 0x7ffff))))))

/-- The value of push `5` of `crD7Nm`. -/
def crNMv5 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C
    (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (A
    8) (C (C (A 0) (A 1022)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A
    0)))) (C (A 0) (A 14)))) (C (A 0) (A 2)))))))) (C (A 1) (A 0))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1)
    (A 0x706f68)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0)) (C (A 0) (A 6))) (C (A 1) (A 0))))) (C
    (A 0) (A 30))))))) (C (A 0) (A 2))))))))))

/-- The value of push `6` of `crD7Nm`. -/
def crNMv6 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 2) (C
    (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (A
    8) (C (C (A 0) (A 2046)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1)
    (A 0)) (C (A 0) (A 62))))) (C (A 0) (A 14)))) (C (A 0) (A 2)))))))) (C (A 1) (A 0))))) (C (C (A 7) (C (C (A
    0) (A 3)) (C (A 1) (A 0x706f68)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0)) (C (A 0) (A 6))) (C
    (A 1) (A 0))))) (C (A 0) (A 62))))))) (C (A 0) (A 2))))))))))

def crNMr6 : Noun :=
  C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C crNMv6 (C (A 7) (C (C (A 10) (C (C (A 0xfffffe) (C (A 0) (A 5))) (C (A
    0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) crNML)))))))

def crNMr5 : Noun :=
  C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C crNMv5 (C (A 7) (C (C (A 10) (C (C (A 0x7ffffe) (C (A 0) (A 5))) (C (A
    0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) crNMr6)))))))

def crNMr4 : Noun :=
  C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C crNMv4 (C (A 7) (C (C (A 10) (C (C (A 0x3ffffe) (C (A 0) (A 5))) (C (A
    0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) crNMr5)))))))

def crNMr3 : Noun :=
  C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C crNMv3 (C (A 7) (C (C (A 10) (C (C (A 0x1ffffe) (C (A 0) (A 5))) (C (A
    0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) crNMr4)))))))

def crNMr2 : Noun :=
  C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C crNMv2 (C (A 7) (C (C (A 10) (C (C (A 0xffffe) (C (A 0) (A 5))) (C (A
    0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) crNMr3)))))))

def crNMr1 : Noun :=
  C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C crNMv1 (C (A 7) (C (C (A 10) (C (C (A 0x7fffe) (C (A 0) (A 5))) (C (A
    0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) crNMr2)))))))

def crNMr0 : Noun :=
  C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C crNMv0 (C (A 7) (C (C (A 10) (C (C (A 0x3fffe) (C (A 0) (A 5))) (C (A
    0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) crNMr1)))))))

theorem crNM_eq : crD7Nm = crNMr0 := by kernel_rfl

/-- The battery of the gate `call-op`. -/
def crOpBat : Noun := (slot? 29 crD7Op).getD (A 0)

/-- The battery of the gate `jump-op`. -/
def crJopBat : Noun := (slot? 29 crD7Jop).getD (A 0)

theorem crD7Op_eq : crD7Op = C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) crOpBat) (C (A 0) (A 1)))) := by
  kernel_rfl

theorem crD7Jop_eq : crD7Jop = C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) crJopBat) (C (A 0) (A 1)))) := by
  kernel_rfl

/-- The subject of `crD7Nm` after the pushes `l` (the last first): `[out
pro]`, `nex`, the gates `jump-op` and `call-op`, the subject of step `7`. -/
noncomputable abbrev crNS (l : List Nat) (KP NEX JG OG SOF V5 SV SN V2 PV mono N GN RG sup : Noun)
    (g : Gen (TreapMap mugF)) (x : GenRest) (ctx : Noun) : Noun :=
  l.foldr (fun a s => C (A a) s)
    (C KP (C NEX (C JG (C OG (crdS6m SOF V5 SV SN V2 PV (crSubj mono N GN RG sup (compCore g x ctx)))))))

section
variable (x : GenRest) (KP NEX JG OG SOF V5 SV SN V2 PV mono N GN RG sup : Noun)

theorem crNM_0 (g : Gen (TreapMap mugF)) :
    nock (crNS [] KP NEX JG OG SOF V5 SV SN V2 PV mono N GN RG sup g x ctx) crNMr0
      = nock (crNS [g.re] KP NEX JG OG SOF V5 SV SN V2 PV mono N GN RG sup (reG g) x ctx) crNMr1 := by
  have hD := comp_re_at
  have hre := comp_re' ctx x g
  conv => { lhs; arg 2; unfold crNMr0 }
  simp only [crNS, crSubj, compCore, List.foldr, reG] at hre ⊢
  generalize comp.door = Dr at hD hre ⊢
  simp [nock_exec, crNMv0, hD, hre]

theorem crNM_1 (a1 : Nat) (g : Gen (TreapMap mugF)) :
    nock (crNS [a1] KP NEX JG OG SOF V5 SV SN V2 PV mono N GN RG sup g x ctx) crNMr1
      = nock (crNS [g.re, a1] KP NEX JG OG SOF V5 SV SN V2 PV mono N GN RG sup (reG g) x ctx) crNMr2 := by
  have hD := comp_re_at
  have hre := comp_re' ctx x g
  conv => { lhs; arg 2; unfold crNMr1 }
  simp only [crNS, crSubj, compCore, List.foldr, reG] at hre ⊢
  generalize comp.door = Dr at hD hre ⊢
  simp [nock_exec, crNMv1, hD, hre]

/-- The block `merge`. -/
def crMerge (merged pro out : Nat) : Blob := ⟨[merged], [Pole.mov merged pro], Termin.hop (jmp0 out)⟩

theorem crMerge_noun (merged pro out : Nat) : (crMerge merged pro out).toNoun
    = C (C (A merged) (A 0)) (C (C (C (A 0x766f6d) (C (A merged) (A pro))) (A 0)) (C (A 0x706f68) (C (A 0) (A out)))) := by
  simp [crMerge, Blob.toNoun, listNoun, Termin.toNoun, Pole.toNoun, Tag.hop, Tag.mov, Jmp.toNoun, jmp0]

theorem crNM_2 (hc : CompIn ctx) (out pro a2 a1 : Nat) (g : Gen (TreapMap mugF)) :
    nock (crNS [a2, a1] (C (A out) (A pro)) NEX JG OG SOF V5 SV SN V2 PV mono N GN RG sup g x ctx) crNMr2
      = nock (crNS [g.bo, a2, a1] (C (A out) (A pro)) NEX JG OG SOF V5 SV SN V2 PV mono N GN RG sup
          (cfEmitG (crMerge a1 pro out) g) x ctx) crNMr3 := by
  have hD := comp_emit_at
  have he := cf_emit (x := x) hc g (crMerge a1 pro out)
  rw [crMerge_noun] at he
  conv => { lhs; arg 2; unfold crNMr2 }
  simp only [crNS, crSubj, compCore, List.foldr] at he ⊢
  generalize comp.door = Dr at hD he ⊢
  simp [nock_exec, crNMv2, hD, comp_emit_arm, he]

theorem crNM_3 (a3 a2 a1 : Nat) (g : Gen (TreapMap mugF)) :
    nock (crNS [a3, a2, a1] KP NEX JG OG SOF V5 SV SN V2 PV mono N GN RG sup g x ctx) crNMr3
      = nock (crNS [g.re, a3, a2, a1] KP NEX JG OG SOF V5 SV SN V2 PV mono N GN RG sup (reG g) x ctx) crNMr4 := by
  have hD := comp_re_at
  have hre := comp_re' ctx x g
  conv => { lhs; arg 2; unfold crNMr3 }
  simp only [crNS, crSubj, compCore, List.foldr, reG] at hre ⊢
  generalize comp.door = Dr at hD hre ⊢
  simp [nock_exec, crNMv3, hD, hre]

theorem crNM_4 (a4 a3 a2 a1 : Nat) (g : Gen (TreapMap mugF)) :
    nock (crNS [a4, a3, a2, a1] KP NEX JG OG SOF V5 SV SN V2 PV mono N GN RG sup g x ctx) crNMr4
      = nock (crNS [g.re, a4, a3, a2, a1] KP NEX JG OG SOF V5 SV SN V2 PV mono N GN RG sup (reG g) x ctx)
          crNMr5 := by
  have hD := comp_re_at
  have hre := comp_re' ctx x g
  conv => { lhs; arg 2; unfold crNMr4 }
  simp only [crNS, crSubj, compCore, List.foldr, reG] at hre ⊢
  generalize comp.door = Dr at hD hre ⊢
  simp [nock_exec, crNMv4, hD, hre]

end

/-- The block `opt`. -/
def crOpt (b : Bell) (subV : List Nat) (proOpt merge : Nat) : Blob :=
  ⟨[], [Pole.cal b subV proOpt], Termin.hop ⟨[some proOpt], merge⟩⟩

/-- The block `pes`. -/
def crPes (b : Bell) (subPes proPes merge : Nat) : Blob :=
  ⟨[], [Pole.csl b subPes proPes], Termin.hop ⟨[some proPes], merge⟩⟩

theorem crOpt_noun (b : Bell) (subV : List Nat) (proOpt merge : Nat) : (crOpt b subV proOpt merge).toNoun
    = C (A 0) (C (C (C (A 0x6c6163) (C b.toNoun (C (listNoun A subV) (A proOpt)))) (A 0))
        (C (A 0x706f68) (C (C (C (A 0) (A proOpt)) (A 0)) (A merge)))) := by
  simp [crOpt, Blob.toNoun, listNoun, Termin.toNoun, Pole.toNoun, Tag.hop, Tag.cal, Jmp.toNoun, unitNoun]

theorem crPes_noun (b : Bell) (subPes proPes merge : Nat) : (crPes b subPes proPes merge).toNoun
    = C (A 0) (C (C (C (A 0x6c7363) (C b.toNoun (C (A subPes) (A proPes)))) (A 0))
        (C (A 0x706f68) (C (C (C (A 0) (A proPes)) (A 0)) (A merge)))) := by
  simp [crPes, Blob.toNoun, listNoun, Termin.toNoun, Pole.toNoun, Tag.hop, Tag.csl, Jmp.toNoun, unitNoun]

section
variable (x : GenRest) (KP NEX JG SOF V5 SN V2 PV mono GN RG sup : Noun) (subNed : Need) (p q : Nomm) (b : Bell)

/-- The gate `call-op` made on the subject of step `7` at the state `g0`. -/
noncomputable abbrev crOG (SOF V5 SV SN V2 PV mono N GN RG sup : Noun) (g0 : Gen (TreapMap mugF)) (x : GenRest)
    (ctx : Noun) : Noun :=
  C crOpBat (C (C (A 0) (A 0)) (crdS6m SOF V5 SV SN V2 PV (crSubj mono N GN RG sup (compCore g0 x ctx))))

theorem crNM_5 (hc : CompIn ctx) (a5 a4 a3 a2 a1 : Nat) (g0 g : Gen (TreapMap mugF)) :
    nock (crNS [a5, a4, a3, a2, a1] KP NEX JG
      (crOG SOF V5 (listNoun A (flattenNeed subNed)) SN V2 PV mono (crdN p q b) GN RG sup g0 x ctx)
      SOF V5 (listNoun A (flattenNeed subNed)) SN V2 PV mono (crdN p q b) GN RG sup g x ctx) crNMr5
      = nock (crNS [g.bo, a5, a4, a3, a2, a1] KP NEX JG
          (crOG SOF V5 (listNoun A (flattenNeed subNed)) SN V2 PV mono (crdN p q b) GN RG sup g0 x ctx)
          SOF V5 (listNoun A (flattenNeed subNed)) SN V2 PV mono (crdN p q b) GN RG sup
          (cfEmitG (crOpt b (flattenNeed subNed) a4 a3) g) x ctx) crNMr6 := by
  have hD := comp_emit_at
  have he := cf_emit (x := x) hc g (crOpt b (flattenNeed subNed) a4 a3)
  rw [crOpt_noun] at he
  conv => { lhs; arg 2; unfold crNMr5 }
  simp only [crNS, crOG, crSubj, compCore, List.foldr] at he ⊢
  generalize comp.door = Dr at hD he ⊢
  simp [nock_exec, crNMv5, crOpBat, crD7Op, crdN, hD, comp_emit_arm, he]

theorem crNM_6 (hc : CompIn ctx) (a6 a5 a4 a3 a2 a1 : Nat) (g0 g : Gen (TreapMap mugF)) :
    nock (crNS [a6, a5, a4, a3, a2, a1] KP NEX JG
      (crOG SOF V5 (listNoun A (flattenNeed subNed)) SN V2 PV mono (crdN p q b) GN RG sup g0 x ctx)
      SOF V5 (listNoun A (flattenNeed subNed)) SN V2 PV mono (crdN p q b) GN RG sup g x ctx) crNMr6
      = nock (crNS [g.bo, a6, a5, a4, a3, a2, a1] KP NEX JG
          (crOG SOF V5 (listNoun A (flattenNeed subNed)) SN V2 PV mono (crdN p q b) GN RG sup g0 x ctx)
          SOF V5 (listNoun A (flattenNeed subNed)) SN V2 PV mono (crdN p q b) GN RG sup
          (cfEmitG (crPes b a2 a5 a3) g) x ctx) crNML := by
  have hD := comp_emit_at
  have he := cf_emit (x := x) hc g (crPes b a2 a5 a3)
  rw [crPes_noun] at he
  conv => { lhs; arg 2; unfold crNMr6 }
  simp only [crNS, crOG, crSubj, compCore, List.foldr] at he ⊢
  generalize comp.door = Dr at hD he ⊢
  simp [nock_exec, crNMv6, crOpBat, crD7Op, crdN, hD, comp_emit_arm, he]

end

theorem crNM_L (x : GenRest) (KP NEX JG OG SOF V5 SV SN V2 PV mono N GN RG sup : Noun) (a7 a6 a5 a4 a3 a2 a1 : Nat)
    (g : Gen (TreapMap mugF)) :
    nock (crNS [a7, a6, a5, a4, a3, a2, a1] KP NEX JG OG SOF V5 SV SN V2 PV mono N GN RG sup g x ctx) crNML
      = some (C (C (A a6) (C (A a2) (A a7))) (genNoun g x)) := by
  unfold crNML
  simp only [crNS, crSubj, compCore, List.foldr]
  generalize comp.door = Dr
  simp [nock_exec]

end Compiler
end Formalization
