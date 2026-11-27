import lemmas.Compiler.CompSccLoopSoftEmitAll
import lemmas.Compiler.CompSccSixBake
import lemmas.Compiler.TreapList

/-! # The gate `finish` with soft calls (README Gaps 21.17)

The final pass of `+compile-scc-in` with soft calls (`finishLFCS`, `Ska/SccLoopSoftFin.lean`)
after the run and `+need-ord-alloc-regs` is `finTailS`: `+coerce-lazy` reading `soft.gen`
(`coerceLazyLS`), `+soft-done` (`softDone`), the baked immediates, `+to-straight`.

* `KCS`: a step of `CMS` keeps `cond`; `kcs_coerceLazyLS`, `kc_softEmitT`, `kc_softDone`;
* `finTailS`, `finishLFCS_tail`;
* `sd_trapP`, **`sd_treeS`**: `+soft-done` on the noun of a soft map whose calls all have
  requirements `%none` / `%this` is `softDone TreapMap.tap` (both `drop` flags), `+soft-emit`
  by `se_emit`;
* **`fin_gate_ts_BS`**: track A's `fin_gate_ts_B` with soft calls: the `+coerce-lazy` link
  with soft calls is the hypothesis `hcz` (its shape is the one of the soft
  `comp_coerce_lazy_all`), the requirements after it are `%none` / `%this` (`hreq`);
* `fin_gate_finishLFCS_B`: the same after the run of `runLCS`. -/

namespace Formalization

namespace SkaModel
namespace Comp

open Nock Lazy

set_option linter.unusedSectionVars false

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- A step of `CMS` keeps `cond`. -/
structure KCS {α : Type} (m : CMS Map α) : Prop where
  keep : ∀ s x s', m s = some (x, s') → s'.g.cond = s.g.cond

namespace KCS

theorem pure' {α : Type} (a : α) : KCS (pure a : CMS Map α) := by
  constructor; intro s x s' h; cases h; rfl

theorem bind' {α β : Type} {m : CMS Map α} {f : α → CMS Map β} (hm : KCS m) (hf : ∀ a, KCS (f a)) :
    KCS (m >>= f) := by
  constructor
  intro s x s' h
  simp only [bind, StateT.bind] at h
  obtain ⟨⟨a, s1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
  exact ((hf a).keep s1 x s' h2).trans (hm.keep s a s1 h1)

theorem liftS' {α : Type} {m : CM Map α} (hm : KC m) : KCS (liftS m) := by
  constructor
  intro s x s' h
  unfold liftS at h
  obtain ⟨⟨a, g1⟩, h1, e⟩ := Option.map_eq_some_iff.mp h
  cases e
  exact hm.keep s.g a g1 h1

theorem ite' {α : Type} (c : Prop) [Decidable c] {a b : CMS Map α} (ha : KCS a) (hb : KCS b) :
    KCS (if c then a else b) := by
  split
  · exact ha
  · exact hb

theorem withSoft' {α : Type} {k : (Nat → Bool) → CMS Map α} (hk : ∀ f, KCS (k f)) : KCS (withSoft k) := by
  constructor
  intro s x s' h
  exact (hk s.isSoft).keep s x s' h

theorem softAsk' (o src : Nat) (ned : Need) : KCS (softAsk o src ned : CMS Map Unit) := by
  constructor
  intro s x s' h
  unfold softAsk at h
  split at h
  · cases h; rfl
  · obtain ⟨c, -, e⟩ := Option.map_eq_some_iff.mp h
    cases e; rfl

end KCS

theorem kcs_sureLoopS (o : Nat) : ∀ (ned tgt : Need), KCS (sureLoopS o ned tgt : CMS Map Unit)
  | Need.none, _ => by
    unfold sureLoopS
    exact KCS.ite' _ (KCS.pure' _) (KCS.liftS' KC.crash)
  | Need.this _, _ => by
    unfold sureLoopS
    exact KCS.withSoft' fun _ => KCS.ite' _ (KCS.softAsk' _ _ _)
      (KCS.liftS' (KC.bind' (kc_kernLoop _ _ _) fun _ => KC.addOps' _ _))
  | Need.pair p q, tgt => by
    unfold sureLoopS
    cases tgt
    · exact KCS.bind' (kcs_sureLoopS o p _) fun _ => kcs_sureLoopS o q _
    · exact KCS.liftS' KC.crash
    · exact KCS.liftS' KC.crash
    · exact KCS.pure' _
  | Need.both _ h t, tgt => by
    unfold sureLoopS
    cases tgt
    · exact KCS.bind' (kcs_sureLoopS o h _) fun _ => kcs_sureLoopS o t _
    · exact KCS.ite' _ (KCS.liftS' KC.crash) (KCS.bind' (KCS.liftS' (KC.addOps' _ _)) fun _ =>
        KCS.bind' (kcs_sureLoopS o h _) fun _ => kcs_sureLoopS o t _)
    · exact KCS.ite' _ (KCS.liftS' KC.crash) (KCS.liftS' (KC.addOps' _ _))
    · exact KCS.pure' _

theorem kcs_coerceLazyS (ned : Need) (o : Nat) (laz : Sure S) (less : Cape) :
    KCS (coerceLazyS ned o laz less : CMS Map Unit) := by
  unfold coerceLazyS
  exact KCS.bind' (KCS.liftS' (KC.lift' _)) fun _ =>
    KCS.bind' (KCS.liftS' (kc_sureRequireLook _)) fun _ => kcs_sureLoopS _ _ _

mutual
theorem kcs_coerceLazyLS (ned : Need) (less : Cape) : ∀ (o : Nat) (l : Lazy S),
    KCS (coerceLazyLS ned less o l : CMS Map Unit)
  | o, mk s f b => by
    unfold coerceLazyLS
    exact KCS.bind' (kcs_coerceLazyS _ _ _ _) fun _ => KCS.ite' _ (KCS.pure' _)
      (KCS.bind' (kcs_coerceBondsS ned less b) fun _ => kcs_coerceForksS ned less f)

theorem kcs_coerceBondsS (ned : Need) (less : Cape) : ∀ (l : List (Nat × Lazy S)),
    KCS (coerceBondsS ned less l : CMS Map Unit)
  | [] => by unfold coerceBondsS; exact KCS.pure' _
  | (o, l) :: rest => by
    unfold coerceBondsS
    exact KCS.bind' (kcs_coerceLazyLS ned less o l) fun _ => kcs_coerceBondsS ned less rest

theorem kcs_coerceForksS (ned : Need) (less : Cape) : ∀ (l : List (ForkE S)),
    KCS (coerceForksS ned less l : CMS Map Unit)
  | [] => by unfold coerceForksS; exact KCS.pure' _
  | ((oy, y), (on, n)) :: rest => by
    unfold coerceForksS
    exact KCS.bind' (kcs_coerceLazyLS ned less oy y) fun _ =>
      KCS.bind' (kcs_coerceLazyLS ned less on n) fun _ => kcs_coerceForksS ned less rest
end

/-- `+soft-emit` without tries keeps `cond`. -/
theorem kc_softEmitT (s : SoftCall) : KC (softEmitT s : CM Map Unit) := by
  constructor
  intro g u g' h
  unfold softEmitT at h
  by_cases hr : s.req = []
  · simp only [hr, if_true, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; rfl
  · simp only [hr, if_false] at h
    obtain ⟨⟨oc, tc⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
    simp only at h
    by_cases ht : softTries tc ≠ []
    · rw [if_pos ht] at h; cases h
    · rw [if_neg ht] at h
      obtain ⟨hed, -, h⟩ := Option.bind_eq_some_iff.mp h
      by_cases hp : hed.par = [] ∧ hed.body = []
      · rw [if_pos hp] at h
        split at h
        · split at h
          · exact (KC.emir' _ _).keep g u g' h
          · cases h
        · cases h
      · rw [if_neg hp] at h; cases h

theorem kc_softDoneL : ∀ (l : List (Nat × SoftCall)), KC (softDoneL l : CM Map Unit)
  | [] => by unfold softDoneL; exact KC.pure' _
  | (_, s) :: rest => by
    unfold softDoneL
    exact KC.bind' (kc_softEmitT s) fun _ => kc_softDoneL rest

theorem kc_softDone (tapS : Map SoftCall → List (Nat × SoftCall)) (st : GenSf Map) (g' : Gen Map)
    (h : softDone tapS st = some g') : g'.cond = st.g.cond := by
  unfold softDone at h
  split at h
  · cases h; rfl
  · obtain ⟨⟨u, g1⟩, h1, e⟩ := Option.map_eq_some_iff.mp h
    cases e
    exact (kc_softDoneL _).keep st.g u g1 h1

end Comp
end SkaModel

namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## The model -/

/-- The part of `finishLFCS` after `+need-ord-alloc-regs`: `+coerce-lazy` with soft calls,
`+soft-done`, the baked immediates at `o`, `+to-straight`. -/
noncomputable def finTailS (tapS : TreapMap mugF SoftCall → List (Nat × SoftCall)) (nedF : Need) (less : Cape)
    (o : Nat) (laz : Lazy CSet) (bake : Need → Need × List (Nat × Noun)) (st : GenSf (TreapMap mugF)) :
    Option (Straight (TreapMap mugF)) :=
  let bak := bake nedF
  (coerceLazyLS nedF less o laz st).bind fun (_, g3) =>
    (softDone tapS g3).bind fun g3' =>
    (addOps o (bak.2.map fun (r, v) => Pole.imm v r) g3').bind fun (_, g4) =>
      toStraightF g4.cond g4.blocks bak.1 o

/-- **`finishLFCS` is the run with soft calls, the check of `args`, `+need-ord-alloc-regs`,
then `finTailS`.** -/
theorem finishLFCS_tail (env : CallEnv) (snd : Nomm → NeedOrd → Bool)
    (tapS : TreapMap mugF SoftCall → List (Nat × SoftCall)) (nm : Nomm) (ord : NeedOrd) (less : Cape)
    (bake : Need → Need × List (Nat × Noun)) :
    finishLFCS (S := CSet) (Map := TreapMap mugF) env snd tapS nm ord less bake
      = (runLCS env snd Option.none nm (CGoalL.done : CGoalL CSet) [] (GenSf.ofGen gen0)).bind fun (nex, g1) =>
          if nex.th.args ≠ [] then Option.none else
          (needOrdAllocRegs ord g1.g).bind fun (nedF, g2) =>
            finTailS tapS nedF less nex.th.there nex.laz bake ⟨g2, g1.soft⟩ := rfl

/-! ## `+soft-done` on a soft map -/

/-- The noun of an entry `[o s]` of `soft.gen`. -/
abbrev sfPairN (p : Nat × SoftCall) : Noun := C (A p.1) (Compiler.SoftCall.toNoun p.2)

/-- **The trap of `+soft-done`** over a list of entries: `softDoneL`. -/
theorem sd_trapP (x : GenRest) (ctx : Noun) (l0 : List (Nat × SoftCall))
    (hE : ∀ (g : Gen (TreapMap mugF)) p, p ∈ l0 → nock (compCore g x ctx) (seCall (sfPairN p))
      = (softEmitT p.2 g).map fun q => genNoun q.2 x) :
    ∀ (l : List (Nat × SoftCall)), (∀ p ∈ l, p ∈ l0) → ∀ (g : Gen (TreapMap mugF)),
    nock (C sdTrap (C (listN (l.map sfPairN)) (C comp.door (C (genNoun g x) ctx)))) sdTrap
      = (softDoneL l g).map fun q => genNoun q.2 x
  | [], _, g => by
    generalize comp.door = Dr
    simp [sdTrap, nock_exec, listN, softDoneL, pure, StateT.pure]
  | p :: l, hl, g => by
    have h1 := hE g p (hl p (List.mem_cons_self ..))
    have ih := fun g' => sd_trapP x ctx l0 hE l (fun e' h' => hl e' (List.mem_cons_of_mem _ h')) g'
    simp only [seCall, compCore] at h1
    generalize comp.door = Dr at h1 ih
    conv => { lhs; arg 2; unfold sdTrap }
    simp [nock_exec] at h1
    simp only [listN] at ih
    have h2 : ∀ a b : Noun, slot? 2 (Noun.cell a b) = some a := fun a b => by
      have : slot? 2 (C a b) = some a := by simp [nock_exec]
      exact this
    simp [nock_exec, listN, h1]
    obtain ⟨o, s⟩ := p
    cases hF : softEmitT s g with
    | none => simp [hF, softDoneL, bind, StateT.bind]
    | some q =>
      obtain ⟨u, g'⟩ := q
      simp [hF, softDoneL, bind, StateT.bind, h2, ih]

/-- **`+soft-done` on the noun of a soft map** whose calls all have requirements `%none` /
`%this`: `softDone` over `~(tap by soft.gen)` (`TreapMap.tap`), on both `drop` flags. -/
theorem sd_treeS (ctx : Noun) (hc : CompIn ctx) (st : GenSf (TreapMap mugF)) (x : GenRest)
    (hx : x.soft = softMapNoun st.soft) (hreq : ∀ p ∈ TreapMap.tap st.soft, ReqTN p.2.req) :
    nock (compCore st.g x ctx) sdArm = (softDone TreapMap.tap st).map (genNoun · x) := by
  cases hdr : st.g.drop
  · have hD := comp_drop_at
    have hE : ∀ (g : Gen (TreapMap mugF)) p, p ∈ TreapMap.tap st.soft → nock (compCore g x ctx) (seCall (sfPairN p))
        = (softEmitT p.2 g).map fun q => genNoun q.2 x :=
      fun g p hp => se_emit ctx hc g x p.1 p.2 (hreq p hp)
    have htr := sd_trapP x ctx (TreapMap.tap st.soft) hE (TreapMap.tap st.soft) (fun _ h => h)
    have hT : Tree x.soft := by
      rw [hx, softMapNoun, hoonMap_toNoun]; exact Tree.of_isMap (st.soft.2 Compiler.SoftCall.toNoun)
    have hL : tapList x.soft = (TreapMap.tap st.soft).map sfPairN := by
      rw [hx, softMapNoun, hoonMap_toNoun]
      exact TreapMap.tapList_toNoun Compiler.SoftCall.toNoun st.soft
    have htap := tapF_list hT []
    simp only [List.append_nil, hL] at htap
    have htap' : tapF x.soft (A 0) = some (listN ((TreapMap.tap st.soft).map sfPairN)) := htap
    unfold softDone
    rw [hdr]
    simp only [Bool.false_eq_true, if_false, Option.map_map]
    rw [sdArm_eq]
    obtain ⟨c, s, sofs⟩ := x
    simp only at hT htap htap' htr ⊢
    simp only [compCore, genNoun] at htr ⊢
    generalize comp.door = Dr at hD htr
    simp [nock_exec, hdr, cgModeNoun, hD, dropArm, comp_h110, eqCode_atom, hc, by_arm, by.arm_at,
      by.tap.arm_at, tap_arm, tap_loop]
    rw [htap']
    have := htr st.g
    simp only [Option.bind_some]
    simp only [cgModeNoun, hdr, Bool.false_eq_true, ↓reduceIte] at this
    rw [this]
    cases softDoneL (TreapMap.tap st.soft) st.g <;> rfl
  · rw [sd_drop ctx st.g x hdr]
    simp [softDone, hdr]

/-! ## The gate `finish` -/

/-- **The gate `finish` with soft calls** (`fin_gate_ts_B` with `soft.gen`): given the
`+coerce-lazy` link with soft calls (`hcz`) and requirements `%none` / `%this` in the soft map
after it (`hreq`), the gate returns `finTailS TreapMap.tap`. -/
theorem fin_gate_ts_BS (Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsOn Q) {ctx : Noun}
    (h7 : slot? 7 ctx = some compK) (c2 c6 c14 NEWN SUR REST G0 : Noun)
    (less : Cape) (hcomp : slot? 6 REST = some (C comp.door (C G0 ctx))) (hdone : slot? 14 REST = some (A 0))
    (hless : slot? 496 REST = some less.toNoun) (hl2 : slot? 0x3ffffff REST = some layer2)
    (g : Gen (TreapMap mugF)) (x : GenRest) (sf : TreapMap mugF SoftCall) (hx : x.soft = softMapNoun sf)
    (hQ : Q g.cond) (nedF : Need) (know : Sock)
    (hrun : isRun (flattenNeed (bakeNeed nedF know).1) ((flattenNeed (bakeNeed nedF know).1).headD 0) 0 = true)
    (o : Nat) (laz : Lazy CSet)
    (hcz : nock (C czBody (C (C nedF.toNoun (C (A o) (C laz.toNoun less.toNoun))) (compCore g x ctx))) czBody
      = (coerceLazyLS nedF less o laz ⟨g, sf⟩).map fun p => genNoun p.2.g { x with soft := softMapNoun p.2.soft })
    (hreq : ∀ u st, coerceLazyLS nedF less o laz ⟨g, sf⟩ = some (u, st) →
      ∀ p ∈ TreapMap.tap st.soft, ReqTN p.2.req) :
    nock (C finBody (C (A 0) (finCtx c2 c6 c14 NEWN laz.toNoun nedF.toNoun (bakeNeed nedF know).1.toNoun
        (immNoun (bakeNeed nedF know).2) o SUR (genNoun g x) REST))) finBody
      = (finTailS TreapMap.tap nedF less o laz (fun n => bakeNeed n know) ⟨g, sf⟩).map Straight.toNoun := by
  have hc := (comp_ctx_pill ctx h7).1
  have hczat := comp_cz_at
  have hsdat := sd_at
  have haoat := comp_add_ops_at
  have htsat := comp_ts_at
  unfold finTailS
  dsimp only
  generalize bakeNeed nedF know = bak at hrun ⊢
  obtain ⟨nedB, imm⟩ := bak
  simp only at hrun ⊢
  cases e1 : coerceLazyLS nedF less o laz ⟨g, sf⟩ with
  | none =>
    rw [e1] at hcz
    simp only [compCore] at hcz
    conv => { lhs; arg 2; unfold finBody }
    simp only [finCtx]
    generalize comp.door = Dr at hcz hczat hsdat haoat htsat hcomp
    simp [nock_exec, hcomp, hdone, hless, hczat, comp_cz_arm, hcz]
  | some r1 =>
    obtain ⟨u1, st3⟩ := r1
    rw [e1] at hcz
    simp only [Option.bind_some]
    have kc3 := (kcs_coerceLazyLS nedF less o laz).keep ⟨g, sf⟩ u1 st3 e1
    have hsd := sd_treeS ctx hc st3 { x with soft := softMapNoun st3.soft } rfl (hreq u1 st3 e1)
    cases e15 : softDone TreapMap.tap st3 with
    | none =>
      rw [e15] at hsd
      simp only [compCore, Option.map_some, Option.map_none] at hcz hsd
      conv => { lhs; arg 2; unfold finBody }
      simp only [finCtx, Option.bind_some, Option.bind_none]
      generalize comp.door = Dr at hcz hczat hsdat haoat htsat hcomp hsd
      generalize sdArm = SD at hsdat hsd
      simp [nock_exec, hcomp, hdone, hless, hl2, hczat, comp_cz_arm, hcz, hsdat, hsd, e15]
    | some g3 =>
      rw [e15] at hsd
      simp only [Option.bind_some]
      have kc35 := kc_softDone TreapMap.tap st3 g3 e15
      have hao := comp_add_ops { x with soft := softMapNoun st3.soft } hc g3 o (imm.map fun (r, v) => Pole.imm v r)
      cases e2 : addOps o (imm.map fun (r, v) => Pole.imm v r) g3 with
      | none =>
        rw [e2] at hao
        simp only [compCore, Option.map_some] at hcz hsd hao
        conv => { lhs; arg 2; unfold finBody }
        simp only [finCtx, Option.bind_some]
        generalize comp.door = Dr at hcz hczat hsdat haoat htsat hcomp hsd hao
        generalize sdArm = SD at hsdat hsd
        simp [nock_exec, hcomp, hdone, hless, hl2, hczat, comp_cz_arm, hcz, hsdat, hsd, haoat, comp_add_ops_arm,
          turn.arm_at, turn_arm, fin_turn_imm, hao, e2]
      | some r2 =>
        obtain ⟨u2, g4⟩ := r2
        rw [e2] at hao
        have kc4 := (KC.addOps' o (imm.map fun (r, v) => Pole.imm v r)).keep g3 u2 g4 e2
        have hts := hT ctx h7 g4 { x with soft := softMapNoun st3.soft } o nedB
          (by rw [kc4, kc35, kc3]; exact hQ) hrun
        simp only [compCore, Option.map_some, tsSampleN] at hcz hsd hao hts
        conv => { lhs; arg 2; unfold finBody }
        simp only [finCtx, Option.bind_some]
        generalize comp.door = Dr at hcz hczat hsdat haoat htsat hcomp hsd hao hts
        generalize sdArm = SD at hsdat hsd
        simp [nock_exec, hcomp, hdone, hless, hl2, hczat, comp_cz_arm, hcz, hsdat, hsd, haoat, comp_add_ops_arm,
          turn.arm_at, turn_arm, fin_turn_imm, hao, htsat, comp_ts_arm, hts, e2]
        all_goals exact hts

/-- **The gate `finish` returns the noun of `finishLFCS`** (`fin_gate_finishLF_six_B` with soft
calls): given the run with soft calls of the final pass (`runLCS` from `gen0`), the shape `ord`
that `+need-ord-alloc-regs` allocates, the `+coerce-lazy` link with soft calls (`hcz`) and
requirements `%none` / `%this` after it (`hreq`). -/
theorem fin_gate_finishLFCS_B (Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsOn Q) {ctx : Noun}
    (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (h7 : slot? 7 ctx = some compK) (c2 c6 c14 NEWN SUR REST G0 : Noun)
    (less : Cape) (hcomp : slot? 6 REST = some (C comp.door (C G0 ctx))) (hdone : slot? 14 REST = some (A 0))
    (hless : slot? 496 REST = some less.toNoun) (hl2 : slot? 0x3ffffff REST = some layer2)
    (x : GenRest) (nm : Nomm) (ord : NeedOrd) (nex : NextL CSet) (g1 : GenSf (TreapMap mugF))
    (g2 : Gen (TreapMap mugF)) (nedF : Need) (know : Sock) (hx : x.soft = softMapNoun g1.soft)
    (hrunL : runLCS env snd Option.none nm (CGoalL.done : CGoalL CSet) [] (GenSf.ofGen gen0) = some (nex, g1))
    (hargs : nex.th.args = [])
    (hQ : Q g1.g.cond)
    (hnoar : needOrdAllocRegs ord g1.g = some (nedF, g2))
    (hrun : isRun (flattenNeed (bakeNeed nedF know).1) ((flattenNeed (bakeNeed nedF know).1).headD 0) 0 = true)
    (hcz : nock (C czBody (C (C nedF.toNoun (C (A nex.th.there) (C nex.laz.toNoun less.toNoun)))
        (compCore g2 x ctx))) czBody
      = (coerceLazyLS nedF less nex.th.there nex.laz ⟨g2, g1.soft⟩).map fun p =>
          genNoun p.2.g { x with soft := softMapNoun p.2.soft })
    (hreq : ∀ u st, coerceLazyLS nedF less nex.th.there nex.laz ⟨g2, g1.soft⟩ = some (u, st) →
      ∀ p ∈ TreapMap.tap st.soft, ReqTN p.2.req) :
    nock (C finBody (C (A 0) (finCtx c2 c6 c14 NEWN nex.laz.toNoun nedF.toNoun (bakeNeed nedF know).1.toNoun
        (immNoun (bakeNeed nedF know).2) nex.th.there SUR (genNoun g2 x) REST))) finBody
      = (finishLFCS (S := CSet) (Map := TreapMap mugF) env snd TreapMap.tap nm ord less
          (fun n => bakeNeed n know)).map Straight.toNoun := by
  have kc2 := (kc_needOrdAllocRegs (Map := TreapMap mugF) ord).keep g1.g nedF g2 hnoar
  rw [finishLFCS_tail, hrunL]
  simp only [Option.bind_some, hargs, ne_eq, not_true_eq_false, if_false, hnoar]
  exact fin_gate_ts_BS Q hT h7 c2 c6 c14 NEWN SUR REST G0 less hcomp hdone hless hl2 g2 x g1.soft hx
    (by rw [kc2]; exact hQ) nedF know hrun nex.th.there nex.laz hcz hreq

end Compiler
end Formalization
