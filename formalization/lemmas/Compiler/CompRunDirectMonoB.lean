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

/-- The gate `jump-op` made on the subject of step `7` at the state `g0`. -/
noncomputable abbrev crJG (SOF V5 SV SN V2 PV mono N GN RG sup : Noun) (g0 : Gen (TreapMap mugF)) (x : GenRest)
    (ctx : Noun) : Noun :=
  C crJopBat (C (A 0) (C (crOG SOF V5 SV SN V2 PV mono N GN RG sup g0 x ctx)
    (crdS6m SOF V5 SV SN V2 PV (crSubj mono N GN RG sup (compCore g0 x ctx)))))

/-- **Step `7` on a `%next` or `%pick` goal under `mono` `&`, up to
`crD7Nm`**: the test of `%done` fails, `+simple-next`, `+kerf`, the test of
`mono`. -/
theorem crd7_nm (h7 : slot? 7 ctx = some compK) (x : GenRest) (SOF V5 SV SN V2 PV : Noun) (p q : Nomm) (b : Bell)
    (RG sup : Noun) (goal : CGoalL CSet) (k : Nat) (hk : goal.toNoun = C (A k) (crdGoalT goal))
    (hkd : k ≠ 0x656e6f64) (g g1 g2 : Gen (TreapMap mugF)) (nex0 : NextL CSet) (out pro : Nat)
    (hsn : nock (crSubj (A 0) (crdN p q b) goal.toNoun RG sup (compCore g x ctx)) crSn
      = some (C nex0.goal.toNoun (genNoun g1 x)))
    (hkf : nock (C kerfBat (C nex0.goal.toNoun (compCore g1 x ctx))) kerfBat
      = some (C (C (A out) (A pro)) (genNoun g2 x))) :
    nock (crdS6m SOF V5 SV SN V2 PV (crSubj (A 0) (crdN p q b) goal.toNoun RG sup (compCore g x ctx))) crDKc7
      = nock (crNS [] (C (A out) (A pro)) nex0.goal.toNoun (crJG SOF V5 SV SN V2 PV (A 0) (crdN p q b) goal.toNoun RG sup g x ctx)
          (crOG SOF V5 SV SN V2 PV (A 0) (crdN p q b) goal.toNoun RG sup g x ctx)
          SOF V5 SV SN V2 PV (A 0) (crdN p q b) goal.toNoun RG sup g2 x ctx) crNMr0 := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  have hkd' : (0x656e6f64 : Nat) ≠ k := fun h => hkd h.symm
  have hD1 := comp_kerf_at
  rw [← crNM_eq]
  simp only [crNS, crJG, crOG, crSubj, compCore, List.foldr] at hsn hkf ⊢
  rw [hk] at hsn ⊢
  generalize comp.door = Dr at hsn hkf hD1 ⊢
  unfold crDKc7 crD7 crD7T crD7Nr0 crD7Nc0 crD7Nr1 crD7Nc1 crD7Ne
  rw [crD7Op_eq, crD7Jop_eq]
  simp [nock_exec, crdS6m, hsn, cr_bat_sn, hkd, hkd', hD1, comp_kerf_arm, hkf]

/-- **Step `7` on a `%next` or `%pick` goal under `mono` `&`** (`crD7Nm`):
`+simple-next`, `+kerf`, `+re` twice, the `+emit` of `merge`, `+re` twice,
the `+emit` of `opt` (`call-op ~ pro-opt`: `%cal`) and of `pes` (`call-op
`sub-pes pro-pes`: `%csl`), no key, no ring. -/
theorem crd_blkM_next (h7 : slot? 7 ctx = some compK) (x : GenRest) (hx : x.NoSoft) (SOF V5 V2 PV : Noun)
    (subNed : Need) (p q : Nomm) (b : Bell) (region : List Nat) (sup : Noun) (goal : CGoalL CSet)
    (hgd : goal ≠ CGoalL.done) (g : Gen (TreapMap mugF)) (hinv : GInv g goal) :
    nock (crdS6m SOF V5 (listNoun A (flattenNeed subNed)) subNed.toNoun V2 PV
      (crSubj (A 0) (crdN p q b) goal.toNoun (listNoun A region) sup (compCore g x ctx))) crDKc7
      = (crdBlockMM b (flattenNeed subNed) goal g).map fun p => crdBlkN p x := by
  obtain ⟨hc, hl, hm⟩ := comp_ctx_pill ctx h7
  have hmod : crdBlockMM b (flattenNeed subNed) goal = (do
      let nex ← simpleNextL goal
      let (out, pro) ← kerf nex
      let merged ← re
      let subPes ← re
      let merge ← emit (crMerge merged pro out)
      let proOpt ← re
      let proPes ← re
      let opt ← emit (crOpt b (flattenNeed subNed) proOpt merge)
      let pes ← emit (crPes b subPes proPes merge)
      pure (opt, subPes, pes) : CM (TreapMap mugF) (Nat × Nat × Nat)) := by
    cases goal with
    | done => exact absurd rfl hgd
    | _ => rfl
  have htd : ∃ k, goal.toNoun = C (A k) (crdGoalT goal) ∧ k ≠ 0x656e6f64 := by
    cases goal with
    | done => exact absurd rfl hgd
    | next laz th => exact ⟨_, rfl, by decide⟩
    | pick z o => exact ⟨_, rfl, by decide⟩
  obtain ⟨k, hk, hkd⟩ := htd
  have hkd' : (0x656e6f64 : Nat) ≠ k := fun h => hkd h.symm
  have hsn := comp_simple_next hc x g goal (A 0) (crdN p q b) (listNoun A region) sup
  rw [hmod, bind_apply]
  cases e : simpleNextL (S := CSet) (Map := TreapMap mugF) goal g with
  | none =>
    rw [e] at hsn
    simp only [Option.map_none] at hsn
    simp only [crSubj, compCore] at hsn ⊢
    rw [hk] at hsn ⊢
    generalize comp.door = Dr at hsn ⊢
    unfold crDKc7 crD7 crD7Op crD7Jop crD7T crD7Nr0 crD7Nc0
    simp [nock_exec, crdS6m, hsn, cr_bat_sn, hkd, hkd']
  | some r =>
    obtain ⟨nex0, g1⟩ := r
    rw [e] at hsn
    simp only [Option.map_some] at hsn
    obtain ⟨-, -, ⟨⟨lnb, -⟩, d1, -⟩, -⟩ := simpleNextL_res hinv e
    have hkf := comp_kerf_all hc hl hm x g1 nex0 (walk_mdP hx g1.bo (lall_mono (fun _ hs => hs.1) lnb))
    have hD1 := comp_kerf_at
    rw [cr_next_nounL] at hsn
    cases ek : kerf nex0 g1 with
    | none =>
      rw [ek] at hkf
      simp only [crSubj, compCore] at hsn hkf ⊢
      rw [hk] at hsn ⊢
      generalize comp.door = Dr at hsn hkf hD1 ⊢
      unfold crDKc7 crD7 crD7Op crD7Jop crD7T crD7Nr0 crD7Nc0 crD7Nr1 crD7Nc1
      simp [nock_exec, crdS6m, hsn, cr_bat_sn, hkd, hkd', hD1, comp_kerf_arm, hkf, bind, StateT.bind, ek]
    | some r2 =>
      obtain ⟨⟨out, pro⟩, g2⟩ := r2
      rw [ek] at hkf
      simp only [Option.map_some] at hkf
      rw [← cr_next_nounL] at hsn hkf
      rw [crd7_nm h7 x SOF V5 _ _ V2 PV p q b _ sup goal k hk hkd g g1 g2 nex0 out pro hsn hkf]
      rw [crNM_0, crNM_1, crNM_2 (hc := hc), crNM_3, crNM_4, crNM_5 (hc := hc), crNM_6 (hc := hc), crNM_L]
      simp [Option.bind_some, re_apply, cf_emit_g, pure_apply, bind_apply, crdBlkN, cf_emitG_re, cf_emitG_bo, ek,
        Functor.map, StateT.map, reG]

/-! ## Steps `8` and `9` under `mono` `&` -/

/-- The gate `+mono-try-call` from the door at any state (`mtc_at`: the
gate with its bunt, under the hint `~%`). -/
theorem mtc_arm (D : Noun) : nock D (C (A 7) (C (C (A 8) (C (C (A 1) (C (C (A 0x656e6f6e) (A 0))
    (C (A 0) (C (A 0) (A 0))))) (C (C (A 1) mtcGB) (C (A 0) (A 1))))) mtcHint))
      = some (C mtcGB (C (C (C (A 0x656e6f6e) (A 0)) (C (A 0) (C (A 0) (A 0)))) D)) := by
  unfold mtcHint; simp [nock_exec]

/-- **Steps `7` to `9` under `mono` `&`**: the blocks (given, `hblk`), then
step `8` on the cell `[opt sub-pes pes]` (`+mono-try-call`, `mtc_gate`;
`sub-ned` becomes `[%this sub-pes]`), then `nex-arg` with `(~(has by
soft.gen) call-block)` `|` under `NoSoft` (step `9`); the rest from step
`10` on. -/
theorem crd_7to9M (h7 : slot? 7 ctx = some compK) (x : GenRest) (hx : x.NoSoft) (SOF V5 V2 PV : Noun)
    (subNed : Need) (p q : Nomm) (b : Bell) (RG sup : Noun) (goal : CGoalL CSet) (g : Gen (TreapMap mugF))
    (hblk : nock (crdS6m SOF V5 (listNoun A (flattenNeed subNed)) subNed.toNoun V2 PV
      (crSubj (A 0) (crdN p q b) goal.toNoun RG sup (compCore g x ctx))) crDKc7
      = (crdBlockMM b (flattenNeed subNed) goal g).map fun p => crdBlkN p x) :
    nock (crdS6m SOF V5 (listNoun A (flattenNeed subNed)) subNed.toNoun V2 PV
      (crSubj (A 0) (crdN p q b) goal.toNoun RG sup (compCore g x ctx))) crDKr7
      = (crdBlockMM b (flattenNeed subNed) goal g).bind fun r =>
          (monoTryCall subNed r.1.1 r.1.2.1 r.1.2.2 r.2).bind fun r' =>
          nock (crdS9 (crdArg (Need.this r.1.2.1) r'.1).goal.toNoun (C (Need.this r.1.2.1).toNoun (A r'.1))
            (C (A r.1.1) (C (A r.1.2.1) (A r.1.2.2))) SOF V5 (listNoun A (flattenNeed subNed)) subNed.toNoun V2
            (A 0) PV (crSubj (A 0) (crdN p q b) goal.toNoun RG sup (compCore r'.2 x ctx))) crDKr10 := by
  have h15 := cr_ctx15 h7
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  have hD := mtc_at
  simp only [crSubj, compCore, crdS6m] at hblk ⊢
  cases eb : crdBlockMM b (flattenNeed subNed) goal g with
  | none =>
    rw [eb] at hblk
    generalize comp.door = Dr at hblk hD ⊢
    unfold crDKr7
    simp [nock_exec, hblk]
  | some r =>
    obtain ⟨⟨opt, subPes, pes⟩, g1⟩ := r
    rw [eb] at hblk
    simp only [Option.map_some, crdBlkN] at hblk
    have hm := mtc_gate x hc subNed opt subPes pes g1
    simp only [compCore] at hm
    simp only [Option.bind_some]
    cases em : monoTryCall (Map := TreapMap mugF) subNed opt subPes pes g1 with
    | none =>
      rw [em] at hm
      generalize comp.door = Dr at hblk hD hm ⊢
      unfold crDKr7 crDKr8 crDKc8
      simp [nock_exec, hblk, hD, mtc_arm, hm]
    | some r' =>
      obtain ⟨o, g2⟩ := r'
      rw [em] at hm
      simp only [Option.map_some] at hm
      have hs := crn_has x o (hx o)
      simp only [Option.bind_some]
      rw [crd_arg_noun]
      generalize comp.door = Dr at hblk hD hm ⊢
      unfold crDKr7 crDKr8 crDKc8 crDKr9 crDKc9
      simp [nock_exec, hblk, hD, mtc_arm, hm, h15, hc, ct_lfn_at, ct_lfn_arm, ct_lfn_gate, by_arm, by.arm_at,
        by.has.arm_at, has_arm, hs, Need.toNoun, Tag.this]

/-! ## The tail (steps `10` to `14`) for any run model

`crd_cnf` and `crd_ctail` (`CompRunDirectC.lean`) with the runs of `p` and
`q` against any model `R` (under `mono` `&` the runs are `runLCM env
true`); the same proofs. -/

/-- One instance of the run link against the model `R`. -/
def RunAtR (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)) (ctx : Noun) (x : GenRest)
    (mono sup : Noun) (n : Nomm) (goal : CGoalL CSet) (region : List Nat) (g : Gen (TreapMap mugF)) : Prop :=
  nock (crSubj mono n.toNoun goal.toNoun (listNoun A region) sup (compCore g x ctx)) crDol
    = (R n goal region g).map fun p => C p.1.goal.toNoun (genNoun p.2 x)

/-- The first push of the run of `q` against `R`. -/
noncomputable def crdFqR (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)) (q : Nomm)
    (th : Jmp) (region : List Nat) : CM (TreapMap mugF) (NextL CSet) :=
  if safeFolFol q then pure ⟨Lazy.ofSure Sure.bunt, th⟩
  else R q (CGoalL.next (Lazy.ofSure Sure.bunt) th) region

/-- The model of the tail of the call against `R`. -/
noncomputable def crdTailMR (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)) (p q : Nomm)
    (nexA : NextL CSet) (region : List Nat) : CM (TreapMap mugF) (NextL CSet) := do
  let nexFol ← crdFqR R q nexA.th region
  let nexFol ← pastL noCode nexFol p region
  let nexSub ← R p (CGoalL.next nexA.laz nexFol.th) region
  copyL nexSub nexFol.laz

theorem crd_cnfR (h7 : slot? 7 ctx = some compK) (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)) (p q : Nomm)
    (region : List Nat) (x : GenRest) (mono I sup goalN : Noun) (nexA : NextL CSet)
    (V8 V7 V6 V5 V4 V3 V2 V1 PV : Noun) (g : Gen (TreapMap mugF))
    (hq : RunAtR R ctx x mono sup q (CGoalL.next (Lazy.ofSure Sure.bunt) nexA.th) region g) :
    nock (crdS9 nexA.goal.toNoun V8 V7 V6 V5 V4 V3 V2 V1 PV
      (crSubj mono (C (A 2) (C p.toNoun (C q.toNoun I))) goalN (listNoun A region) sup (compCore g x ctx))) crDKc10
      = (crdFqR R q nexA.th region g).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  have h63 := crd_ctx63 h7
  have hsa : slot? 767 ana = some safe_fol_fol.arm := safe_fol_fol.arm_at
  have hsf := safe_fol_fol_pill q
  have hq1 := hq
  unfold RunAtR at hq1
  rw [cgl_next_noun, cr_bunt_noun] at hq1
  rw [cr_next_nounL]
  unfold crDKc10 crdFqR
  simp only [crSubj, compCore] at hq1 ⊢
  generalize comp.door = Dr at hq1 ⊢
  cases hs : safeFolFol q with
  | true =>
    simp [nock_exec, h63, hsa, safe_fol_fol_arm, hsf, hs, loob, pure, StateT.pure, cr_next_nounL, cr_bunt_noun]
  | false =>
    simp [nock_exec, h63, hsa, safe_fol_fol_arm, hsf, hs, loob, cr_bat_dol, hq1]

/-- **The tail of the call** (steps `10` to `14`): `crd_cnf`, `+past` over
`p` (`comp_past`), the run of `p` for `[%next laz.nex-arg then.nex-fol]`,
`+copy` (`comp_copy_all`). -/
theorem crd_ctailR (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)) (p q : Nomm) (hpn : hinted noCode p ≠ Option.none)
    (region : List Nat) (x : GenRest) (mono I sup goalN : Noun) (nexA : NextL CSet)
    (V8 V7 V6 V5 V4 V3 V2 V1 PV : Noun) (g : Gen (TreapMap mugF))
    (hq : RunAtR R ctx x mono sup q (CGoalL.next (Lazy.ofSure Sure.bunt) nexA.th) region g)
    (hp : ∀ nexF g2 nexF' g3, crdFqR R q nexA.th region g = some (nexF, g2) →
      pastL noCode nexF p region g2 = some (nexF', g3) →
      RunAtR R ctx x mono sup p (CGoalL.next nexA.laz nexF'.th) region g3)
    (hcp : ∀ nexF g2 nexF' g3 nexS g4, crdFqR R q nexA.th region g = some (nexF, g2) →
      pastL noCode nexF p region g2 = some (nexF', g3) →
      R p (CGoalL.next nexA.laz nexF'.th) region g3 = some (nexS, g4) →
      CopyH g4.re nexS.laz nexF'.laz) :
    nock (crdS9 nexA.goal.toNoun V8 V7 V6 V5 V4 V3 V2 V1 PV
      (crSubj mono (C (A 2) (C p.toNoun (C q.toNoun I))) goalN (listNoun A region) sup (compCore g x ctx))) crDKr10
      = (crdTailMR R p q nexA region g).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  have hnf := crd_cnfR h7 R p q region x mono I sup goalN nexA V8 V7 V6 V5 V4 V3 V2 V1 PV g hq
  have hD1 := cr_past_at
  have hD2 := comp_cp_at
  unfold crdTailMR
  generalize hF : crdFqR R q nexA.th region = F at hnf hp hcp
  simp only [crSubj, compCore, crdS9, cr_next_nounL] at hnf ⊢
  cases eq : F g with
  | none =>
    rw [eq] at hnf
    generalize comp.door = Dr at hnf hD1 hD2 ⊢
    unfold crDKr10
    simp [nock_exec, hnf, bind, StateT.bind, eq]
  | some r =>
    obtain ⟨nexF, g2⟩ := r
    rw [eq] at hnf
    simp only [Option.map_some, cr_next_nounL] at hnf
    have hpa := comp_past h7 hcode x g2 nexF p region hpn
    simp only [cr_next_nounL, compCore] at hpa
    cases e3 : pastL (S := CSet) (Map := TreapMap mugF) noCode nexF p region g2 with
    | none =>
      rw [e3] at hpa
      generalize comp.door = Dr at hnf hD1 hD2 hpa ⊢
      unfold crDKr10 crDKr11 crDKc11
      simp [nock_exec, crSubj, Nomm.toNoun, hnf, bind, StateT.bind, h7, hcode, hD1, cr_past_arm, hpa, eq, e3]
    | some r3 =>
      obtain ⟨nexF', g3⟩ := r3
      rw [e3] at hpa
      simp only [Option.map_some, cr_next_nounL] at hpa
      have hp1 := hp nexF g2 nexF' g3 eq e3
      unfold RunAtR at hp1
      rw [cgl_next_noun] at hp1
      simp only [crSubj, compCore] at hp1
      cases eq2 : R p
          (CGoalL.next nexA.laz nexF'.th) region g3 with
      | none =>
        rw [eq2] at hp1
        generalize comp.door = Dr at hnf hD1 hD2 hpa hp1 ⊢
        unfold crDKr10 crDKr11 crDKc11 crDKr12 crDKc12
        simp [nock_exec, crSubj, Nomm.toNoun, hnf, bind, StateT.bind, h7, hcode, hD1, cr_past_arm, hpa,
          cr_bat_dol, hp1, eq, e3, eq2]
      | some r' =>
        obtain ⟨nexS, g4⟩ := r'
        rw [eq2] at hp1
        simp only [Option.map_some, cr_next_nounL] at hp1
        have hcpy := comp_copy_all h7 x g4 nexS nexF'.laz (hcp nexF g2 nexF' g3 nexS g4 eq e3 eq2)
        simp only [compCore, cr_next_nounL] at hcpy
        generalize comp.door = Dr at hnf hD1 hD2 hpa hp1 hcpy ⊢
        unfold crDKr10 crDKr11 crDKc11 crDKr12 crDKc12 crDKr13 crDKc13 crDKr14
        simp [nock_exec, crSubj, Nomm.toNoun, hnf, bind, StateT.bind, h7, hcode, hD1, cr_past_arm, hpa,
          cr_bat_dol, hp1, eq, e3, eq2, hD2, cr_cp_arm, hcpy, cr_next_nounL, Function.comp_def]


/-! ## Steps `7` to `14` under `mono` `&` -/

theorem crdArg_this (s o : Nat) : crdArg (Need.this s) o = ⟨Lazy.ofSure (lazyReg s), jmp0 o⟩ := rfl

/-- **The model of the call from step `7` on under `mono` `&`** (`callDM`
past `+need-ord-alloc-regs`): `monoBlocks`, then the tail with `nex-arg`
`[%next (lazy-from-need [%this sub-pes]) ~ call-block]`. -/
noncomputable def crdCallMM (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)) (p q : Nomm)
    (b : Bell) (subNed : Need) (goal : CGoalL CSet) (region : List Nat) : CM (TreapMap mugF) (NextL CSet) := do
  let (subPes, o) ← monoBlocks b subNed goal
  crdTailMR R p q ⟨Lazy.ofSure (lazyReg subPes), jmp0 o⟩ region

/-- **Steps `7` to `14` under `mono` `&`**: the blocks (given, `hblk`),
`+mono-try-call`, `nex-arg`, the tail against `R`, with the runs of `q`
and `p` and the `CopyH` of their results at the states the call reaches. -/
theorem crd_from7M (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)) (p q : Nomm)
    (hpn : hinted noCode p ≠ Option.none) (region : List Nat) (x : GenRest) (hx : x.NoSoft) (SOF V5 V2 PV sup : Noun)
    (subNed : Need) (b : Bell) (goal : CGoalL CSet) (g : Gen (TreapMap mugF))
    (hblk : nock (crdS6m SOF V5 (listNoun A (flattenNeed subNed)) subNed.toNoun V2 PV
      (crSubj (A 0) (crdN p q b) goal.toNoun (listNoun A region) sup (compCore g x ctx))) crDKc7
      = (crdBlockMM b (flattenNeed subNed) goal g).map fun p => crdBlkN p x)
    (hq : ∀ s o g1, monoBlocks b subNed goal g = some ((s, o), g1) →
      RunAtR R ctx x (A 0) sup q (CGoalL.next (Lazy.ofSure Sure.bunt) (jmp0 o)) region g1)
    (hp : ∀ s o g1 nexF g2 nexF' g3, monoBlocks b subNed goal g = some ((s, o), g1) →
      crdFqR R q (jmp0 o) region g1 = some (nexF, g2) → pastL noCode nexF p region g2 = some (nexF', g3) →
      RunAtR R ctx x (A 0) sup p (CGoalL.next (Lazy.ofSure (lazyReg s)) nexF'.th) region g3)
    (hcp : ∀ s o g1 nexF g2 nexF' g3 nexS g4, monoBlocks b subNed goal g = some ((s, o), g1) →
      crdFqR R q (jmp0 o) region g1 = some (nexF, g2) → pastL noCode nexF p region g2 = some (nexF', g3) →
      R p (CGoalL.next (Lazy.ofSure (lazyReg s)) nexF'.th) region g3 = some (nexS, g4) →
      CopyH g4.re nexS.laz nexF'.laz) :
    nock (crdS6m SOF V5 (listNoun A (flattenNeed subNed)) subNed.toNoun V2 PV
      (crSubj (A 0) (crdN p q b) goal.toNoun (listNoun A region) sup (compCore g x ctx))) crDKr7
      = (crdCallMM R p q b subNed goal region g).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  rw [crd_7to9M h7 x hx SOF V5 V2 PV subNed p q b (listNoun A region) sup goal g hblk]
  unfold crdCallMM
  rw [monoBlocks_eq]
  simp only [bind_apply]
  cases eb : crdBlockMM b (flattenNeed subNed) goal g with
  | none => rfl
  | some r =>
    obtain ⟨⟨opt, s, pes⟩, g1⟩ := r
    simp only [Option.bind_some]
    cases em : monoTryCall (Map := TreapMap mugF) subNed opt s pes g1 with
    | none => rfl
    | some r' =>
      obtain ⟨o, g2⟩ := r'
      have hmb : monoBlocks b subNed goal g = some ((s, o), g2) := by
        rw [monoBlocks_eq]; simp [bind_apply, eb, em, pure_apply, Functor.map, StateT.map]
      simp only [Option.bind_some, pure_apply]
      have ht := crd_ctailR h7 hcode R p q hpn region x (A 0) (C (A 0) (C b.toNoun (A 0))) sup goal.toNoun
        (crdArg (Need.this s) o) (C (Need.this s).toNoun (A o)) (C (A opt) (C (A s) (A pes))) SOF V5
        (listNoun A (flattenNeed subNed)) subNed.toNoun V2 (A 0) PV g2 (hq s o g2 hmb)
        (fun nexF g3 nexF' g4 e e3 => hp s o g2 nexF g3 nexF' g4 hmb e e3)
        (fun nexF g3 nexF' g4 nexS g5 e e3 e4 => hcp s o g2 nexF g3 nexF' g4 nexS g5 hmb e e3 e4)
      rw [crdArg_this] at ht
      exact ht

end Compiler
end Formalization
