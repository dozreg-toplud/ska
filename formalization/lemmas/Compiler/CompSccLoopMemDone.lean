import lemmas.Compiler.CompSccSixBake
import lemmas.Compiler.CompShapeColMsg
import lemmas.Compiler.CompStraightMapSix

/-! # The gate `member` on `%done` for a member of a real SCC (README Gaps 21.14)

Track A's one-bell chain (`mem_to_finish_six_B`, `mem_gate_six_B`) assumed three things that a
member of a real SCC breaks:

1. the run of `+run` is `comp_run_entry_six` on a nomm of `SixOk` (no direct call), so it
   leaves the rest of the state as it was; a real member calls the other members and callees
   outside the SCC, whose misses compile their SCCs and change `cache`.  Here the run is a
   hypothesis on the pill (`hrunN`, the instance at `mono` `|` of a threaded link
   `CompRunAtXT (runLC env ~)`) that leaves a rest `x1` whose cache is `[nary mono sccs inl
   sure]` (`hx1`) with no soft (`hs1`); `mem_to_finish_R`;
2. `map-local` and `top` are `~` (`NoSelfCall` of one bell: the member's own entry is never
   read): here `map-local` is any map (`top` is `~` on the final pass), and the product is taken
   on its two branches, no entry of `b` (`mem_prod_newM`) and an entry `prev`
   (`mem_prod_oldM`: `need-pessimized` is `msgOrd need-new prev cape` by `msg_gate_K`, and
   `finish ~` runs when it equals `need-new`, `finish `np` otherwise);
3. `finish` is always `finish ~`: on a pessimized shape the pill runs `+coerce-soft` (no
   model), whose product is left as the noun `finish` gives on `[~ np]` (`memFCR`).

**`mem_gate_done_R`**: the gate on `%done` with `map-local` a map and `top` `~`, both branches,
the straight of `finish ~` given by `finishLFC env nm ord cape (bakeNeed · [cape data])` (the
real bake, `BakeRunO`'s run condition `hrun` on the residual, track A). -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The subject of `finish` on the final pass of a member of a real SCC: `memFCB` with the
state `G2` after the run. -/
abbrev memFCR (keep : Bool) (WAS SUR NN LZ NF NEDB IMM : Noun) (o : Nat) (G2 NM DCTX B ML TOP CA CTX : Noun) :
    Noun :=
  memFCB keep WAS SUR NN LZ NF NEDB IMM o G2 NM DCTX B ML TOP CA CTX

/-- **From the gate to the push of `finish` on `%done`, the run threading the rest**: the
copy of `mem_to_finish_six_B` with the pill's run as the hypothesis `hrunN` (any rest `x1`
after it, whose cache is `cacheN C1 C2 C3 C4 SURE`), in place of `comp_run_entry_six`. -/
theorem mem_to_finish_R (cape : Cape) (DATA FOL : Noun) (keep : Bool)
    (ML TOP CACHE DN KIDS ML0 CB SCC CODE LSR JH CACHE0 : Noun)
    (nm : Nomm) (CA1 : Noun)
    (hinl : nock (C inlBody (C (C (C (C cape.toNoun DATA) FOL) (C (C CODE LSR) (C JH CACHE))) compK)) inlBody
      = some (C nm.toNoun CA1))
    (nex : NextL CSet) (g1 : Gen (TreapMap mugF)) (x1 : GenRest)
    (hrunN : nock (crSubj (A 1) nm.toNoun (C (A 0x656e6f64) (A 0)) (A 0) (A 0)
        (compCore genEntry (cuRest CA1) (memDCtx SCC (C CODE LSR) JH ML TOP (C (C cape.toNoun DATA) FOL)))) crDol
      = some (C nex.goal.toNoun (genNoun g1 x1)))
    (C1 C2 C3 C4 SURE : Noun) (hx1 : x1.cache = cacheN C1 C2 C3 C4 SURE)
    (ord : NeedOrd) (hsc : nock (C scBody (C (C nex.laz.toNoun cape.toNoun) compK)) scBody = some ord.toNoun)
    (hargs : nex.th.args = []) (nedF : Need) (g2 : Gen (TreapMap mugF))
    (hnoar : needOrdAllocRegs ord g1 = some (nedF, g2))
    (sur : NeedOrd) (hsur : sureOf (needToOrd nex.laz.sure.ned) nex.laz.sure.lok cape = some sur)
    (WAS SURE' : Noun) (hwas : getF mugF (C (C cape.toNoun DATA) FOL) SURE = some WAS)
    (hw : WAS = A 0 ∨ ∃ u, WAS = C (A 0) u)
    (hput : putF mugF (C (C cape.toNoun DATA) FOL) (memSurKN keep WAS sur.toNoun) SURE = some SURE') :
    nock (C memBody (C (memSam (C (C cape.toNoun DATA) FOL) (A 0x656e6f64) (loob keep) ML TOP CACHE)
        (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0))) memBody
      = nock (C (C finBody (C (A 0) (memFCR keep WAS sur.toNoun
            (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1).toNoun nex.laz.toNoun nedF.toNoun
            (bakeNeed nedF (Sock.mk cape DATA)).1.toNoun (immNoun (bakeNeed nedF (Sock.mk cape DATA)).2)
            nex.th.there (genNoun g2 x1) nm.toNoun
            (memDCtx SCC (C CODE LSR) JH ML TOP (C (C cape.toNoun DATA) FOL)) (C (C cape.toNoun DATA) FOL) ML TOP
            (cacheN C1 C2 C3 C4 SURE') (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0))))
          (memFCR keep WAS sur.toNoun
            (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1).toNoun nex.laz.toNoun nedF.toNoun
            (bakeNeed nedF (Sock.mk cape DATA)).1.toNoun (immNoun (bakeNeed nedF (Sock.mk cape DATA)).2)
            nex.th.there (genNoun g2 x1) nm.toNoun
            (memDCtx SCC (C CODE LSR) JH ML TOP (C (C cape.toNoun DATA) FOL)) (C (C cape.toNoun DATA) FOL) ML TOP
            (cacheN C1 C2 C3 C4 SURE') (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0))) memProd := by
  have h7 : slot? 7 (memDCtx SCC (C CODE LSR) JH ML TOP (C (C cape.toNoun DATA) FOL)) = some compK := rfl
  rw [mem_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨_, _, _, rfl⟩ hinl, mem_r3, mem_res]
  simp only [compCore] at hrunN
  -- +collapse-shape at the rest the run left
  have hcsN := cs_gate _ h7 x1 g1 nex cape.toNoun ord hsc
  simp only [hargs, ne_eq, not_true_eq_false, if_false, hnoar, Option.map_some, compCore] at hcsN
  have hlz := lazy_toNoun_eta nex.laz
  rw [hlz] at hcsN
  have hbn : nock (C bnBody (C (C nedF.toNoun (C cape.toNoun DATA)) compK)) bnBody
      = some (C (bakeNeed nedF (Sock.mk cape DATA)).1.toNoun (immNoun (bakeNeed nedF (Sock.mk cape DATA)).2)) :=
    bn_gateB nedF (Sock.mk cape DATA)
  have hn1 := nta_gate compK nex.laz.sure.ned
  have hso := so_gate (needToOrd nex.laz.sure.ned) nex.laz.sure.lok cape
  rw [hsur, Option.map_some] at hso
  have hn2 := nta_gate compK (bakeNeed nedF (Sock.mk cape DATA)).1
  rw [mem_final_B (hmode := mem_mode_noop _ _) (hrun := hrunN) (hcs := hcsN) (hbn := hbn) (hn1 := hn1) (hso := hso)
    (hn2 := hn2)]
  simp only [Option.bind_some]
  have hG2 : slot? 510 (genNoun g2 x1) = some (cacheN C1 C2 C3 C4 SURE) := by rw [cu_gen_cache, hx1]
  rw [mem_after (keep := keep) (hG2 := hG2) (hwas := hwas) (hw := hw) (hput := hput)]
  rw [hlz]
  rfl

/-- **The product of `member` when `map-local` has no entry of `b`**, with `map-local` any map
and `top` `~`: `[chg (~(put by map-local) b (finish ~)) cache]`, `chg` as with one bell. -/
theorem mem_prod_newM (MOVED SUR' WAS NN LZ NF NEDB IMM : Noun) (o : Nat) (SUR G2 NM DCTX CAPE DATA FOL KEEP
    ML CA DN KIDS ML0 CB SCC LONG JH CACHE0 : Noun) (hmv : MOVED = A 0 ∨ MOVED = A 1) (hnn : ∃ p q, NN = C p q)
    (hml : IsMap mugF ML) (hnone : getF mugF (C (C CAPE DATA) FOL) ML = some (A 0)) :
    nock (C (C finBody (C (A 0) (finCtx MOVED SUR' WAS NN LZ NF NEDB IMM o SUR G2
          (memS3 NM DCTX (memS0 (C (C CAPE DATA) FOL) KEEP ML (A 0) CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0))))))
        (finCtx MOVED SUR' WAS NN LZ NF NEDB IMM o SUR G2
          (memS3 NM DCTX (memS0 (C (C CAPE DATA) FOL) KEEP ML (A 0) CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0)))))
        memProd
      = (nock (C finBody (C (A 0) (finCtx MOVED SUR' WAS NN LZ NF NEDB IMM o SUR G2
          (memS3 NM DCTX (memS0 (C (C CAPE DATA) FOL) KEEP ML (A 0) CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0))))))
          finBody).bind fun ST => (putF mugF (C (C CAPE DATA) FOL) ST ML).map fun ML' =>
            C (memChgN MOVED NN) (C ML' CA) := by
  have hL := compK_layer2
  have hg0 := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ (C (C CAPE DATA) FOL) ML (A 0)
    hnone
  have hgut := gut_gate (mug := mugF) layer2 ⟨fall.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
    (C (C CAPE DATA) FOL) (C (A 0x656e6f6e) (A 0)) (A 0) (A 0) rfl (Or.inl rfl)
  simp only [if_true] at hgut
  generalize hF : finCtx MOVED SUR' WAS NN LZ NF NEDB IMM o SUR G2
    (memS3 NM DCTX (memS0 (C (C CAPE DATA) FOL) KEEP ML (A 0) CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0))) = FC
  have hFC := hF
  unfold finCtx memS3 memS0 memSam memCtx at hFC
  obtain ⟨np, nq, rfl⟩ := hnn
  cases e : nock (C finBody (C (A 0) FC)) finBody with
  | none =>
    subst hFC
    unfold memProd memSprev memNew
    generalize compK = KC at hL e ⊢
    generalize finBody = FB at e ⊢
    rcases hmv with rfl | rfl <;>
    by_cases h1 : A 0x656e6f6e = np <;> by_cases h2 : A 0 = nq <;> (try subst h1) <;> (try subst h2) <;>
    simp [nock_exec, hL, by.arm_at, by_arm, by.get.arm_at, get_arm, hg0, by.gut.arm_at, gut_arm, hgut,
      by.put.arm_at, put_arm, e, memChgN, nock_ite, *]
  | some ST =>
    obtain ⟨ML', hp, -, -⟩ := putF_spec mugF ML (C (C CAPE DATA) FOL) ST hml
    have hpg := put_gate (mug := mugF) layer2 gorIn_morIn_layer2 (C (C CAPE DATA) FOL) ST ML ML' hp
    subst hFC
    unfold memProd memSprev memNew
    generalize compK = KC at hL e ⊢
    generalize finBody = FB at e ⊢
    rcases hmv with rfl | rfl <;>
    by_cases h1 : A 0x656e6f6e = np <;> by_cases h2 : A 0 = nq <;> (try subst h1) <;> (try subst h2) <;>
    simp [nock_exec, hL, by.arm_at, by_arm, by.get.arm_at, get_arm, hg0, by.gut.arm_at, gut_arm, hgut,
      by.put.arm_at, put_arm, hpg, hp, e, memChgN, nock_ite, *]

/-- `chg` on an entry `prev`: `|(moved !=(need-pessimized prev))`. -/
def memChgO (MOVED NP PREV : Noun) : Noun :=
  if MOVED = A 0 then A 0 else if NP = PREV then A 1 else A 0

/-- **The product of `member` when `map-local` holds a straight `[PREV REST]` of `b`**, for any
`PREV`: `need-pessimized` is the product `NP` of `+msg-need-ord` on `[need-new PREV cape]`
(`hmsg`), `chg` is `memChgO`, and the gate puts at `b` the straight of `(finish ~)` when `NP`
is `need-new`, of `(finish `NP)` otherwise. -/
theorem mem_prod_oldM (MOVED SUR' WAS NN LZ NF NEDB IMM : Noun) (o : Nat) (SUR G2 NM DCTX CAPE DATA FOL KEEP
    ML TOP CA DN KIDS ML0 CB SCC LONG JH CACHE0 PREV REST NP : Noun) (hmv : MOVED = A 0 ∨ MOVED = A 1)
    (hml : IsMap mugF ML) (hprev : getF mugF (C (C CAPE DATA) FOL) ML = some (C (A 0) (C PREV REST)))
    (hmsg : nock (C msgBody (C (C NN (C PREV CAPE)) compK)) msgBody = some NP) :
    nock (C (C finBody (C (A 0) (finCtx MOVED SUR' WAS NN LZ NF NEDB IMM o SUR G2
          (memS3 NM DCTX (memS0 (C (C CAPE DATA) FOL) KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0))))))
        (finCtx MOVED SUR' WAS NN LZ NF NEDB IMM o SUR G2
          (memS3 NM DCTX (memS0 (C (C CAPE DATA) FOL) KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0)))))
        memProd
      = (nock (C finBody (C (if NP = NN then A 0 else C (A 0) NP) (finCtx MOVED SUR' WAS NN LZ NF NEDB IMM o SUR G2
          (memS3 NM DCTX (memS0 (C (C CAPE DATA) FOL) KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0))))))
          finBody).bind fun ST => (putF mugF (C (C CAPE DATA) FOL) ST ML).map fun ML' =>
            C (memChgO MOVED NP PREV) (C ML' CA) := by
  have hL := compK_layer2
  have hma := msg_at
  have hg := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ (C (C CAPE DATA) FOL) ML _ hprev
  generalize hF : finCtx MOVED SUR' WAS NN LZ NF NEDB IMM o SUR G2
    (memS3 NM DCTX (memS0 (C (C CAPE DATA) FOL) KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0))) = FC
  have hFC := hF
  unfold finCtx memS3 memS0 memSam memCtx at hFC
  have key : ∀ SAM, (SAM = A 0 ∧ NP = NN ∨ SAM = C (A 0) NP ∧ NP ≠ NN) →
      nock (C (C finBody (C (A 0) FC)) FC) memProd
        = (nock (C finBody (C SAM FC)) finBody).bind fun ST => (putF mugF (C (C CAPE DATA) FOL) ST ML).map
            fun ML' => C (memChgO MOVED NP PREV) (C ML' CA) := by
    intro SAM hsam
    cases e : nock (C finBody (C SAM FC)) finBody with
    | none =>
      subst hFC
      unfold memProd memSprev memOld
      generalize compK = KC at hL hma hmsg e ⊢
      generalize finBody = FB at e ⊢
      rcases hsam with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ <;> rcases hmv with rfl | rfl <;> by_cases hp' : NP = PREV <;>
      (try subst hn) <;> (try subst hp') <;>
      simp [nock_exec, hL, by.arm_at, by_arm, by.get.arm_at, get_arm, hg, hma, msg_arm, hmsg, e, eqCode,
        memChgO, nock_ite, *]
    | some ST =>
      obtain ⟨ML', hp, -, -⟩ := putF_spec mugF ML (C (C CAPE DATA) FOL) ST hml
      have hpg := put_gate (mug := mugF) layer2 gorIn_morIn_layer2 (C (C CAPE DATA) FOL) ST ML ML' hp
      subst hFC
      unfold memProd memSprev memOld
      generalize compK = KC at hL hma hmsg e ⊢
      generalize finBody = FB at e ⊢
      rcases hsam with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ <;> rcases hmv with rfl | rfl <;> by_cases hp' : NP = PREV <;>
      (try subst hn) <;> (try subst hp') <;>
      simp [nock_exec, hL, by.arm_at, by_arm, by.get.arm_at, get_arm, hg, hma, msg_arm, hmsg, e, eqCode,
        memChgO, nock_ite, by.put.arm_at, put_arm, hpg, hp, *]
  by_cases hn : NP = NN
  · rw [if_pos hn]; exact key _ (Or.inl ⟨rfl, hn⟩)
  · rw [if_neg hn]; exact key _ (Or.inr ⟨rfl, hn⟩)

end Compiler
end Formalization
