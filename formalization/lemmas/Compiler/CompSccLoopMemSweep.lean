import lemmas.Compiler.CompSccLoopSweepBase

/-! # The gate `member` on `%must` and `%may` in the pill (README Gaps 21.18)

The copies, off `%done`, of the steps of `member` on the final pass (`CompMember.lean`,
`CompSccLoopMemDone.lean`): the push of `done` is `|` (`memS0X (A 1) MODE`), `memRes` takes the
branch `memShape` (its product the hypothesis `hbr`, `MemShapeBranch`), the `sure.cache` steps
are as on `%done`, and `finish` returns the placeholder `[np 0 ~]` (`fin_placeholder`).

* `mem_entryX`, `mem_resX`, `mem_afterX`, `fin_placeholder`;
* `mem_prod_newX` (no entry of `b`, `top` any map: `chg` is `memChgTN`), `mem_prod_oldX` (an
  entry: `need-pessimized` by `+msg-need-ord`, `chg` is `memChgO`);
* **`mem_gate_sweep_R`**: the gate on `%must` / `%may` from the branch's product. -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem modeN_cases (mode : Mode) (h : mode ≠ Mode.done) : modeN mode = mustN ∨ modeN mode = mayN := by
  cases mode <;> simp_all [modeN]

/-- **From the gate to the branch, off `%done`**: `done` is `|`, the `?>`, the door `comp`,
`+inlined` (`hinl`), the `=|` of `gen` and `=.  cache.gen  cache`. -/
theorem mem_entryX (MODE : Noun) (hmode : MODE = mustN ∨ MODE = mayN)
    (B KEEP ML TOP CACHE DN KIDS ML0 CB SCC LONG JH CACHE0 NM CA : Noun)
    (hb : ∃ c d f, B = C (C c d) f)
    (hinl : nock (C inlBody (C (C B (C LONG (C JH CACHE))) compK)) inlBody = some (C NM CA)) :
    nock (C memBody (C (memSam B MODE KEEP ML TOP CACHE) (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0)))
        memBody
      = nock (C (genNoun (genEntry : Gen (TreapMap mugF)) (cuRest CA))
          (memS3 NM (memDCtx SCC LONG JH ML TOP B)
            (memS0X (A 1) MODE B KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0)))) memR3 := by
  obtain ⟨c, d, f, rfl⟩ := hb
  have he := mem_entry_step (memS3 NM (memDCtx SCC LONG JH ML TOP (C (C c d) f))
    (memS0X (A 1) MODE (C (C c d) f) KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0))) memR3 CA
    (by simp [memS3, memS0X, memSam, nock_exec])
  rw [← he]
  have hia := inl_at
  have hca := cu_comp_at
  conv => { lhs; arg 2; unfold memBody }
  simp only [memS3, memS0X, memSam, memCtx, memDCtx]
  generalize compK = KC at hia hca hinl ⊢
  rcases hmode with rfl | rfl <;>
  simp [nock_exec, memComp, memR1, memInl, memR2, hia, hca, cu_cg_slam, hinl, inlHint, eqCode]

/-- Off `%done` (`done`, axis `30`, is `|`), `memRes` is the branch `memShape`. -/
theorem mem_resX (GN NM DCTX MODE B KEEP ML TOP CA CTX : Noun) :
    nock (C GN (memS3 NM DCTX (memS0X (A 1) MODE B KEEP ML TOP CA CTX))) memRes
      = nock (C GN (memS3 NM DCTX (memS0X (A 1) MODE B KEEP ML TOP CA CTX))) memShape := by
  conv => { lhs; arg 2; unfold memRes }
  generalize memFinal = F
  generalize memShape = SH
  simp [nock_exec, memS3, memS0X]

/-- **From the branch to the push of `finish`**, any `done` and mode: the copy of `mem_after`. -/
theorem mem_afterX (DNV MODE NN LZ NF NEDB IMM : Noun) (o : Nat) (SUR G2 GN NM DCTX CAPE DATA FOL : Noun) (keep : Bool)
    (ML TOP CA0 C1 C2 C3 C4 SURE DN KIDS ML0 CB SCC LONG JH CACHE0 WAS SURE' : Noun)
    (hG2 : slot? 510 G2 = some (cacheN C1 C2 C3 C4 SURE))
    (hwas : getF mugF (C (C CAPE DATA) FOL) SURE = some WAS) (hw : WAS = A 0 ∨ ∃ u, WAS = C (A 0) u)
    (hput : putF mugF (C (C CAPE DATA) FOL) (memSurKN keep WAS SUR) SURE = some SURE') :
    nock (C (C (C NN (C LZ (C NF (C (C NEDB IMM) (C (A o) SUR))))) G2)
        (C GN (memS3 NM DCTX (memS0X DNV MODE (C (C CAPE DATA) FOL) (loob keep) ML TOP CA0
          (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0))))) memAfter
      = nock (C (C finBody (C (A 0) (finCtx (memMovedN keep WAS SUR) (memSurKN keep WAS SUR) WAS NN LZ NF NEDB IMM
            o SUR G2 (memS3 NM DCTX (memS0X DNV MODE (C (C CAPE DATA) FOL) (loob keep) ML TOP (cacheN C1 C2 C3 C4 SURE')
              (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0))))))
          (finCtx (memMovedN keep WAS SUR) (memSurKN keep WAS SUR) WAS NN LZ NF NEDB IMM
            o SUR G2 (memS3 NM DCTX (memS0X DNV MODE (C (C CAPE DATA) FOL) (loob keep) ML TOP (cacheN C1 C2 C3 C4 SURE')
              (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0))))) memProd := by
  have hg := get_gate layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ _ _ _ hwas
  have hL := compK_layer2
  have hfa := fin_arm
  unfold memAfter memWas memSurK memPut memMoved
  unfold memS3 memS0X memSam memCtx finCtx cacheN at *
  generalize compK = KC at hL ⊢
  rcases hw with rfl | ⟨u, rfl⟩ <;> cases keep <;>
  simp only [memMovedN, memSurKN, fallNone, Bool.false_eq_true, ↓reduceIte] at hput ⊢ <;>
  have hp := put_gate layer2 gorIn_morIn_layer2 _ _ _ _ hput <;>
  (try split) <;>
  simp_all [nock_exec, by.arm_at, by_arm, by.get.arm_at, get_arm, by.put.arm_at, put_arm,
    fall.arm_at, fall_arm, fall_gate_nil, fall_gate_some, loob, nock_ite]

/-- **`finish` off `%done`** (`done`, axis `2046` of the core, is `|`): the placeholder
`[?~(pessimized need-new u.pessimized) 0 ~]`. -/
theorem fin_placeholder (c2 c6 c14 NEWN LAZ NEDF NEDB IMM : Noun) (o : Nat) (SUR G NM DCTX MODE B KEEP ML TOP CA CTX : Noun) :
    nock (C finBody (C (A 0) (finCtx c2 c6 c14 NEWN LAZ NEDF NEDB IMM o SUR G
        (memS3 NM DCTX (memS0X (A 1) MODE B KEEP ML TOP CA CTX))))) finBody = some (C NEWN (C (A 0) (A 0))) ∧
    ∀ NP, nock (C finBody (C (C (A 0) NP) (finCtx c2 c6 c14 NEWN LAZ NEDF NEDB IMM o SUR G
        (memS3 NM DCTX (memS0X (A 1) MODE B KEEP ML TOP CA CTX))))) finBody = some (C NP (C (A 0) (A 0))) := by
  constructor
  · conv => { lhs; arg 2; unfold finBody }
    simp [nock_exec, finCtx, memS3, memS0X]
  · intro NP
    conv => { lhs; arg 2; unfold finBody }
    simp [nock_exec, finCtx, memS3, memS0X]

/-- **The product off `%done` with no entry of `b`**, `top` any map whose `+gut:by` at `b` is
`fallNone TGU` (a cell): `[chg (~(put by map-local) b [need-new 0 ~]) cache]`. -/
theorem mem_prod_newX (MOVED SUR' WAS NN LZ NF NEDB IMM : Noun) (o : Nat) (SUR G2 NM DCTX CAPE DATA FOL KEEP MODE
    ML TOP CA DN KIDS ML0 CB SCC LONG JH CACHE0 TGU : Noun) (hmv : MOVED = A 0 ∨ MOVED = A 1) (hnn : ∃ p q, NN = C p q)
    (hml : IsMap mugF ML) (hnone : getF mugF (C (C CAPE DATA) FOL) ML = some (A 0))
    (htop : getF mugF (C (C CAPE DATA) FOL) TOP = some TGU) (htg : TGU = A 0 ∨ ∃ u, TGU = C (A 0) u)
    (htc : ∃ p q, fallNone TGU = C p q) :
    nock (C (C finBody (C (A 0) (finCtx MOVED SUR' WAS NN LZ NF NEDB IMM o SUR G2
          (memS3 NM DCTX (memS0X (A 1) MODE (C (C CAPE DATA) FOL) KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0))))))
        (finCtx MOVED SUR' WAS NN LZ NF NEDB IMM o SUR G2
          (memS3 NM DCTX (memS0X (A 1) MODE (C (C CAPE DATA) FOL) KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0)))))
        memProd
      = (putF mugF (C (C CAPE DATA) FOL) (C NN (C (A 0) (A 0))) ML).map fun ML' =>
            C (memChgTN MOVED NN (fallNone TGU)) (C ML' CA) := by
  have hL := compK_layer2
  have hg0 := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ (C (C CAPE DATA) FOL) ML (A 0)
    hnone
  obtain ⟨tp, tq, htc⟩ := htc
  have hgut : nock (C by.gut.battery (C (C (C (C CAPE DATA) FOL) (C (A 0x656e6f6e) (A 0))) (C by.battery (C TOP layer2))))
      by.gut.battery = some (C tp tq) := by
    rw [gut_gate (mug := mugF) layer2 ⟨fall.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ _ _ TOP TGU htop htg]
    rcases htg with rfl | ⟨u, rfl⟩ <;> simp_all [fallNone]
  have e := (fin_placeholder MOVED SUR' WAS NN LZ NF NEDB IMM o SUR G2 NM DCTX MODE (C (C CAPE DATA) FOL) KEEP ML TOP CA
    (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0)).1
  generalize hF : finCtx MOVED SUR' WAS NN LZ NF NEDB IMM o SUR G2
    (memS3 NM DCTX (memS0X (A 1) MODE (C (C CAPE DATA) FOL) KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0))) = FC at e
  have hFC := hF
  unfold finCtx memS3 memS0X memSam memCtx at hFC
  obtain ⟨np, nq, rfl⟩ := hnn
  rw [htc]
  obtain ⟨ML', hp, -, -⟩ := putF_spec mugF ML (C (C CAPE DATA) FOL) (C (C np nq) (C (A 0) (A 0))) hml
  have hpg := put_gate (mug := mugF) layer2 gorIn_morIn_layer2 (C (C CAPE DATA) FOL) _ ML ML' hp
  subst hFC
  unfold memProd memSprev memNew
  generalize compK = KC at hL e ⊢
  generalize finBody = FB at e ⊢
  rcases hmv with rfl | rfl <;>
  by_cases h1 : A 0x656e6f6e = np <;> by_cases h2 : A 0 = nq <;> (try subst h1) <;> (try subst h2) <;>
  by_cases h3 : A 0x656e6f6e = tp <;> by_cases h4 : A 0 = tq <;> (try subst h3) <;> (try subst h4) <;>
  simp [nock_exec, hL, by.arm_at, by_arm, by.get.arm_at, get_arm, hg0, by.gut.arm_at, gut_arm, hgut,
    by.put.arm_at, put_arm, hpg, hp, e, memChgTN, nock_ite, *]

/-- **The product off `%done` with an entry `[PREV REST]` of `b`**: `need-pessimized` the product
`NP` of `+msg-need-ord` (`hmsg`), `[chg (~(put by map-local) b [NP 0 ~]) cache]`, `chg` `memChgO`. -/
theorem mem_prod_oldX (MOVED SUR' WAS NN LZ NF NEDB IMM : Noun) (o : Nat) (SUR G2 NM DCTX CAPE DATA FOL KEEP MODE
    ML TOP CA DN KIDS ML0 CB SCC LONG JH CACHE0 PREV REST NP : Noun) (hmv : MOVED = A 0 ∨ MOVED = A 1)
    (hml : IsMap mugF ML) (hprev : getF mugF (C (C CAPE DATA) FOL) ML = some (C (A 0) (C PREV REST)))
    (hmsg : nock (C msgBody (C (C NN (C PREV CAPE)) compK)) msgBody = some NP) :
    nock (C (C finBody (C (A 0) (finCtx MOVED SUR' WAS NN LZ NF NEDB IMM o SUR G2
          (memS3 NM DCTX (memS0X (A 1) MODE (C (C CAPE DATA) FOL) KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0))))))
        (finCtx MOVED SUR' WAS NN LZ NF NEDB IMM o SUR G2
          (memS3 NM DCTX (memS0X (A 1) MODE (C (C CAPE DATA) FOL) KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0)))))
        memProd
      = (putF mugF (C (C CAPE DATA) FOL) (C NP (C (A 0) (A 0))) ML).map fun ML' =>
            C (memChgO MOVED NP PREV) (C ML' CA) := by
  have hL := compK_layer2
  have hma := msg_at
  have hg := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ (C (C CAPE DATA) FOL) ML _ hprev
  have hpl := fin_placeholder MOVED SUR' WAS NN LZ NF NEDB IMM o SUR G2 NM DCTX MODE (C (C CAPE DATA) FOL) KEEP ML TOP CA
    (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0)
  generalize hF : finCtx MOVED SUR' WAS NN LZ NF NEDB IMM o SUR G2
    (memS3 NM DCTX (memS0X (A 1) MODE (C (C CAPE DATA) FOL) KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0))) = FC at hpl
  have hFC := hF
  unfold finCtx memS3 memS0X memSam memCtx at hFC
  obtain ⟨ML', hp, -, -⟩ := putF_spec mugF ML (C (C CAPE DATA) FOL) (C NP (C (A 0) (A 0))) hml
  have hpg := put_gate (mug := mugF) layer2 gorIn_morIn_layer2 (C (C CAPE DATA) FOL) _ ML ML' hp
  obtain ⟨e0, e1⟩ := hpl
  have e1' := e1 NP
  subst hFC
  unfold memProd memSprev memOld
  generalize compK = KC at hL hma hmsg e0 e1' ⊢
  generalize finBody = FB at e0 e1' ⊢
  rcases hmv with rfl | rfl <;> by_cases hn : NP = NN <;> by_cases hp' : NP = PREV <;>
  (try subst hn) <;> (try subst hp') <;>
  simp [nock_exec, hL, by.arm_at, by_arm, by.get.arm_at, get_arm, hg, hma, msg_arm, hmsg, e0, e1', eqCode,
    memChgO, nock_ite, by.put.arm_at, put_arm, hpg, hp, *]

/-- **The gate `member` on `%must` / `%may`** (`top` any map, `map-local` any map), from the
branch's product `hbr` (`[[SH bunts 0 SUR] G2]`, `G2` with the cache `[C1 C2 C3 C4 SURE]`) and the
`sure.cache` steps (`hwas`, `hput`): with no entry of `b` the gate puts `[SH 0 ~]` and returns
`memChgTN` (`top`'s `+gut:by` at `b` is `fallNone TGU`); with an entry `[PREV REST]` it puts
`[NP 0 ~]`, `NP` the `+msg-need-ord` of `[SH PREV cape]`, and returns `memChgO`. -/
theorem mem_gate_sweep_R (mode : Mode) (hmode : mode ≠ Mode.done) (cape : Cape) (DATA FOL : Noun) (keep : Bool)
    (ML TOP CACHE DN KIDS ML0 CB SCC CODE LSR JH CACHE0 : Noun) (nm : Nomm) (CA1 : Noun)
    (hinl : nock (C inlBody (C (C (C (C cape.toNoun DATA) FOL) (C (C CODE LSR) (C JH CACHE))) compK)) inlBody
      = some (C nm.toNoun CA1))
    (SH SUR G2 : Noun) (hsh : ∃ p q, SH = C p q)
    (hbr : nock (memShapeSubj (modeN mode) keep nm.toNoun SCC (C CODE LSR) JH ML TOP (C (C cape.toNoun DATA) FOL) CA1
        (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0)) memShape = some (C (shapeResN SH SUR) G2))
    (C1 C2 C3 C4 SURE : Noun) (hG2 : slot? 510 G2 = some (cacheN C1 C2 C3 C4 SURE))
    (WAS SURE' : Noun) (hwas : getF mugF (C (C cape.toNoun DATA) FOL) SURE = some WAS)
    (hw : WAS = A 0 ∨ ∃ u, WAS = C (A 0) u)
    (hput : putF mugF (C (C cape.toNoun DATA) FOL) (memSurKN keep WAS SUR) SURE = some SURE')
    (hml : IsMap mugF ML) :
    (∀ TGU, getF mugF (C (C cape.toNoun DATA) FOL) TOP = some TGU → (TGU = A 0 ∨ ∃ u, TGU = C (A 0) u) →
      (∃ p q, fallNone TGU = C p q) → getF mugF (C (C cape.toNoun DATA) FOL) ML = some (A 0) →
      nock (C memBody (C (memSam (C (C cape.toNoun DATA) FOL) (modeN mode) (loob keep) ML TOP CACHE)
          (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0))) memBody
        = (putF mugF (C (C cape.toNoun DATA) FOL) (C SH (C (A 0) (A 0))) ML).map fun ML' =>
            C (memChgTN (memMovedN keep WAS SUR) SH (fallNone TGU)) (C ML' (cacheN C1 C2 C3 C4 SURE'))) ∧
    (∀ PREV REST NP, getF mugF (C (C cape.toNoun DATA) FOL) ML = some (C (A 0) (C PREV REST)) →
      nock (C msgBody (C (C SH (C PREV cape.toNoun)) compK)) msgBody = some NP →
      nock (C memBody (C (memSam (C (C cape.toNoun DATA) FOL) (modeN mode) (loob keep) ML TOP CACHE)
          (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0))) memBody
        = (putF mugF (C (C cape.toNoun DATA) FOL) (C NP (C (A 0) (A 0))) ML).map fun ML' =>
            C (memChgO (memMovedN keep WAS SUR) NP PREV) (C ML' (cacheN C1 C2 C3 C4 SURE'))) := by
  have hmv : memMovedN keep WAS SUR = A 0 ∨ memMovedN keep WAS SUR = A 1 := by
    unfold memMovedN; split <;> simp
  have hto : nock (C memBody (C (memSam (C (C cape.toNoun DATA) FOL) (modeN mode) (loob keep) ML TOP CACHE)
        (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0))) memBody
      = nock (C (C finBody (C (A 0) (finCtx (memMovedN keep WAS SUR) (memSurKN keep WAS SUR) WAS SH
            (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))) (C (A 0x656e6f6e) (A 0)) (C (A 0x656e6f6e) (A 0)) (A 0)
            0 SUR G2 (memS3 nm.toNoun (memDCtx SCC (C CODE LSR) JH ML TOP (C (C cape.toNoun DATA) FOL))
              (memS0X (A 1) (modeN mode) (C (C cape.toNoun DATA) FOL) (loob keep) ML TOP (cacheN C1 C2 C3 C4 SURE')
                (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0))))))
          (finCtx (memMovedN keep WAS SUR) (memSurKN keep WAS SUR) WAS SH
            (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))) (C (A 0x656e6f6e) (A 0)) (C (A 0x656e6f6e) (A 0)) (A 0)
            0 SUR G2 (memS3 nm.toNoun (memDCtx SCC (C CODE LSR) JH ML TOP (C (C cape.toNoun DATA) FOL))
              (memS0X (A 1) (modeN mode) (C (C cape.toNoun DATA) FOL) (loob keep) ML TOP (cacheN C1 C2 C3 C4 SURE')
                (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0))))) memProd := by
    rw [mem_entryX (modeN mode) (modeN_cases mode hmode) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨_, _, _, rfl⟩ hinl, mem_r3,
      mem_resX]
    unfold memShapeSubj at hbr
    rw [hbr, Option.bind_some]
    unfold shapeResN
    exact mem_afterX (A 1) (modeN mode) SH _ _ _ _ 0 SUR G2 _ _ _ _ _ _ keep ML TOP CA1 C1 C2 C3 C4 SURE DN KIDS ML0 CB
      SCC (C CODE LSR) JH CACHE0 WAS SURE' hG2 hwas hw hput
  refine ⟨fun TGU htop htg htc hnone => ?_, fun PREV REST NP hprev hmsg => ?_⟩
  · rw [hto]
    exact mem_prod_newX _ _ _ _ _ _ _ _ 0 _ _ _ _ _ _ _ _ _ ML TOP _ DN KIDS ML0 CB SCC _ JH CACHE0 TGU hmv hsh hml hnone
      htop htg htc
  · rw [hto]
    exact mem_prod_oldX _ _ _ _ _ _ _ _ 0 _ _ _ _ _ _ _ _ _ ML TOP _ DN KIDS ML0 CB SCC _ JH CACHE0 PREV REST NP hmv hml
      hprev hmsg

end Compiler
end Formalization
