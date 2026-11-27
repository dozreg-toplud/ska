import lemmas.Compiler.CompSccLoopMemSweep
import lemmas.Compiler.CompSccLoopStrGen

/-! # `MemGate` on `%must` and `%may` for `cfgRealShape` (README Gaps 21.18)

`mem_gate_sweep_R` (`CompSccLoopMemSweep.lean`) gives the pill's gate `member` off `%done` from the
product of the branch `memShape`.  Here it is read against the model's `member (cfgRealShape r x
order kids)` at the loop's relation `LoopRS` with track K's `QK`:

* `memChgTN_loob`: `chg` with no entry is the model's;
* `TopH top TOP`: `top`'s `+gut:by` at every bell is the model's `top`; `topH_nil` (`%may`: `top`
  is `~`), `topH_of_topN` (`%must`: `top` from the `%may` sweep, `TopN`);
* **`mem_sweep_step`**: the per-call obligation of `MemGate` on `%must` / `%may`, with the branch's
  pill computation the ONE hypothesis `MemShapeBranch` (`CompSccLoopSweepBase.lean`) and what the
  branch leaves in the cache (`QK`, the members' `sure` entries, the outside callees held);
* `MemSweepCall`, **`memGate_sweep_real`**, `memGate_may_K`, `memGate_must_K` (the `%may` and
  `%must` thirds of `SccLoopAt`, in the context `csiCtx` of the loop). -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem memChgTN_loob (mv : Bool) (nn tg : NeedOrd) :
    memChgTN (loob mv) nn.toNoun tg.toNoun = loob (mv || nn != NeedOrd.none || tg != NeedOrd.none) := by
  have key : ∀ n : NeedOrd, (C (A 0x656e6f6e) (A 0) = n.toNoun) ↔ n = NeedOrd.none := fun n =>
    ⟨fun h => needOrd_toNoun_inj (by rw [← h]; simp [NeedOrd.toNoun, Tag.none]),
     fun h => by subst h; simp [NeedOrd.toNoun, Tag.none]⟩
  unfold memChgTN
  cases mv
  · simp only [loob, Bool.false_eq_true, if_false, Bool.false_or]
    by_cases e : nn = NeedOrd.none
    · rw [if_pos ((key nn).2 e)]
      by_cases e2 : tg = NeedOrd.none
      · rw [if_pos ((key tg).2 e2)]; simp [e, e2]
      · rw [if_neg (fun h => e2 ((key tg).1 h))]; simp [e, e2]
    · rw [if_neg (fun h => e ((key nn).1 h))]; simp [e]
  · simp [loob]

/-- `top` as the gate reads it: at every bell `+gut:by` gives the model's `top`. -/
def TopH (top : Noun → NeedOrd) (TOP : Noun) : Prop :=
  ∀ b, ∃ TGU, getF mugF b TOP = some TGU ∧ (TGU = A 0 ∨ ∃ u, TGU = C (A 0) u) ∧ fallNone TGU = (top b).toNoun

/-- `%may`: `top` is `~`. -/
theorem topH_nil : TopH (fun _ => NeedOrd.none) (A 0) := fun b =>
  ⟨A 0, getF_none IsMap.nil (fun v hv => absurd hv (by simp [get_nil])), Or.inl rfl, by simp [fallNone, NeedOrd.toNoun, Tag.none]⟩

/-- `%must`: `top` from the `%may` sweep. -/
theorem topH_of_topN {ml : Noun → Option NeedOrd} {TOP : Noun} (h : TopN ml TOP) :
    TopH (fun k => (ml k).getD NeedOrd.none) TOP := by
  intro b
  cases e : ml b with
  | none =>
    refine ⟨A 0, getF_none h.1 (fun v hv => ?_), Or.inl rfl, by simp [fallNone, NeedOrd.toNoun, Tag.none, e]⟩
    obtain ⟨n, hn, -⟩ := (h.2 b v).1 hv
    rw [e] at hn; cases hn
  | some n =>
    exact ⟨C (A 0) n.toNoun, getF_some h.1 ((h.2 b _).2 ⟨n, e, rfl⟩), Or.inr ⟨_, rfl⟩, by simp [fallNone, e]⟩

/-- **The per-call obligation of `MemGate` on `%must` / `%may` for `cfgRealShape`**, at a member
`b = [[cape DATA] FOL]` of the SCC `S`, with `LoopRS` for track K's invariant `QK env RR P S x`,
`top` read through `TOP` (`hTOP`).  Hypotheses besides the pill's arms: `+inlined` (`hinl`), the
branch's pill computation `MemShapeBranch` on the views of the state (`hbrn`: the model's
`lazeReal` returns `(col, sur)` and `memShape` returns its tuple and a `gen` with the cache
`[C1 C2 C3 C4 SURE]`), and what that cache keeps: `QK` (`hQ1`), the members' `sure` entries
(`hsh1`), the outside callees held (`hout1`). -/
theorem mem_sweep_step (r : RealCfg) (xs : ShapeX) (order : List Noun) (kids : Noun → List Noun)
    (outC : Noun → List Noun) (nout : Noun → NeedOrd) (envK : CallEnv) (RR : GenRest → Prop) (P : Noun → Prop)
    (S : Noun) (x : GenRest)
    (hRR : ∀ NR MO SC INL SU SU' s f : Noun, RR ⟨cacheN NR MO SC INL SU, s, f⟩ → RR ⟨cacheN NR MO SC INL SU', s, f⟩)
    (mode : Mode) (hmode : mode ≠ Mode.done) (top : Noun → NeedOrd) (TOP : Noun) (hTOP : TopH top TOP)
    (st : St Noun NeedOrd) (keep : Bool) (cape : Cape) (DATA FOL : Noun) (nm : Nomm) (fuel : Nat)
    (hinfo : r.info (C (C cape.toNoun DATA) FOL) = ⟨nm, cape, DATA, fuel⟩)
    (hbr : C (C cape.toNoun DATA) FOL ∈ r.scc) (hbS : C (C cape.toNoun DATA) FOL ∈ tapList S)
    (hxS : ∀ N u, slot? 31 x.cache = some N → getF mugF (C (C cape.toNoun DATA) FOL) N ≠ some (C (A 0) u))
    (ML CACHE DN KIDS ML0 CB SCC CODE LSR JH CACHE0 : Noun)
    (hR : LoopRS r.scc outC nout (QK envK RR P S x) st.ml st.sure ML CACHE)
    (CA1 : Noun)
    (hinl : nock (C inlBody (C (C (C (C cape.toNoun DATA) FOL) (C (C CODE LSR) (C JH CACHE))) compK)) inlBody
      = some (C nm.toNoun CA1))
    (col sur : NeedOrd) (G2 : Noun)
    (hbrn : MemShapeBranch xs mode (envView r.env r.scc (viewN top st) (viewS (cfgRealShape r xs order kids) st))
      cape DATA FOL nm fuel keep SCC (C CODE LSR) JH ML TOP CA1 (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0)
      col sur G2)
    (C1 C2 C3 C4 SURE : Noun) (hG2 : slot? 510 G2 = some (cacheN C1 C2 C3 C4 SURE))
    (hQ1 : QK envK RR P S x (cacheN C1 C2 C3 C4 SURE))
    (hsh1 : SureHolds r.scc st.sure (cacheN C1 C2 C3 C4 SURE))
    (hout1 : ∀ b', ((st.ml b').isSome ∨ b' = C (C cape.toNoun DATA) FOL) → ∀ k ∈ outC b', ∃ NR u,
      slot? 2 (cacheN C1 C2 C3 C4 SURE) = some NR ∧ getF mugF k NR = some (C (A 0) u) ∧ slot? 2 u = some (nout k).toNoun) :
    ∃ ML' CA', nock (C memBody (C (memSam (C (C cape.toNoun DATA) FOL) (modeN mode) (loob keep) ML TOP CACHE)
        (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0))) memBody
        = some (C (loob (member (cfgRealShape r xs order kids) top (C (C cape.toNoun DATA) FOL) mode keep st).1) (C ML' CA')) ∧
      LoopRS r.scc outC nout (QK envK RR P S x)
        (member (cfgRealShape r xs order kids) top (C (C cape.toNoun DATA) FOL) mode keep st).2.ml
        (member (cfgRealShape r xs order kids) top (C (C cape.toNoun DATA) FOL) mode keep st).2.sure
        ML' CA' := by
  generalize hB : C (C cape.toNoun DATA) FOL = B at *
  have hcomp : (cfgRealShape r xs order kids).comp B mode (viewN top st) (viewS (cfgRealShape r xs order kids) st)
      = ⟨bakeNeedOrd col (Sock.mk cape DATA), sur⟩ := by
    have h := compReal_sweep r xs B mode hmode (viewN top st) (viewS (cfgRealShape r xs order kids) st) col sur
      (by rw [hinfo]; exact hbrn.1)
    simp only [hinfo] at h
    exact h
  have hnone0 : (cfgRealShape r xs order kids).none = NeedOrd.none := rfl
  have hmsg' : ∀ nn prev, (cfgRealShape r xs order kids).msg B nn prev = msgOrd nn prev cape := by
    intro nn prev; simp [cfgRealShape, cfgReal, hinfo]
  have hbrn2 := hbrn.2
  generalize hNN : bakeNeedOrd col (Sock.mk cape DATA) = nn at *
  -- `sure.cache` at `b`
  have hmS : IsMap mugF SURE := qK_map hQ1
  have hwas := sureHolds_was hsh1 hbr
  obtain ⟨SURE', hput, -, -⟩ := putF_spec mugF SURE B (memSurKN keep (wasN (st.sure B)) sur.toNoun) hmS
  have hput' := hput
  rw [memSurKN_was] at hput'
  have hQ' := (csQK_put hRR hQ1 hput' hbS hxS).1
  have hSH' := csSureHolds_put hsh1 hmS hput'
  have hml := hR.1.1
  have hg := mem_gate_sweep_R mode hmode cape DATA FOL keep ML TOP CACHE DN KIDS ML0 CB SCC CODE LSR JH CACHE0 nm CA1
    (by rw [hB]; exact hinl) nn.toNoun sur.toNoun G2 (nord_cell nn) hbrn2 C1 C2 C3 C4 SURE hG2
    (wasN (st.sure B)) SURE' (by rw [hB]; exact hwas) (wasN_shape _) (by rw [hB]; exact hput) hml.1
  rw [hB] at hg
  rw [memMovedN_was] at hg
  have hout' : ∀ np : NeedOrd, OutsHeld outC nout (upd st.ml B (some np)) (cacheN C1 C2 C3 C4 SURE') := by
    intro np b' hb' k hk
    obtain ⟨NR, u, h2, h3, h4⟩ := hout1 b' (by
      by_cases e : b' = B
      · exact Or.inr e
      · left; simpa [upd, e] using hb') k hk
    rw [cacheN_slot2] at h2
    exact ⟨NR, u, by rw [cacheN_slot2]; exact h2, h3, h4⟩
  have e2 : (member (cfgRealShape r xs order kids) top B mode keep st).2.sure
      = upd st.sure B (some (if keep then (st.sure B).getD sur else sur)) := by
    simp [member, hnone0, hcomp]
  cases hm : st.ml B with
  | none =>
    have hnone : getF mugF B ML = some (A 0) :=
      getF_none hml.1 (fun v hv => by obtain ⟨n, t, hn, -⟩ := hml.2.1 B v hv; rw [hm] at hn; cases hn)
    obtain ⟨TGU, htop, htg, htc⟩ := hTOP B
    obtain ⟨ML', hp, -, -⟩ := putF_spec mugF ML B (C nn.toNoun (C (A 0) (A 0))) hml.1
    refine ⟨ML', cacheN C1 C2 C3 C4 SURE', ?_, ?_⟩
    · rw [hg.1 TGU htop htg (by rw [htc]; exact nord_cell _) hnone, hp, Option.map_some, htc, memChgTN_loob]
      simp [member, hnone0, hcomp, hm]
    · have e1 : (member (cfgRealShape r xs order kids) top B mode keep st).2.ml = upd st.ml B (some nn) := by
        simp [member, hnone0, hcomp, hm]
      rw [e1, e2]
      exact loopRS_put hR ⟨_, placeholder_straight nn⟩ hp ⟨csMlExact_put hml hp, hSH', hout' nn, hQ'⟩
  | some prev =>
    obtain ⟨t, ht⟩ := hml.2.2 B prev hm
    have hprev : getF mugF B ML = some (C (A 0) (C prev.toNoun t)) := getF_some hml.1 ht
    have hmsg := msg_gate_K nn prev cape
    unfold msgS at hmsg
    obtain ⟨ML', hp, -, -⟩ := putF_spec mugF ML B (C (msgOrd nn prev cape).toNoun (C (A 0) (A 0))) hml.1
    refine ⟨ML', cacheN C1 C2 C3 C4 SURE', ?_, ?_⟩
    · rw [hg.2 prev.toNoun t _ hprev hmsg, hp, Option.map_some, memChgO_loob]
      simp [member, hnone0, hcomp, hm, hmsg']
    · have e1 : (member (cfgRealShape r xs order kids) top B mode keep st).2.ml
          = upd st.ml B (some (msgOrd nn prev cape)) := by simp [member, hnone0, hcomp, hm, hmsg']
      rw [e1, e2]
      exact loopRS_put hR ⟨_, placeholder_straight _⟩ hp ⟨csMlExact_put hml hp, hSH', hout' _, hQ'⟩

/-- **What one `%must` / `%may` call of `member` takes** (state `st`, `keep`, `map-local` `ML`,
`cache` `CACHE`, context `memCtx DN KIDS ML0 CB SCC [CODE LSR] JH CACHE0`): the member is a bell
`[[cape DATA] FOL]` whose `r.info` is its nomm, cape, data, fuel; `+inlined` gives the nomm (`CA1`
its cache); the branch's pill computation `MemShapeBranch` on the views of `st` (track A's
hypothesis, the cache threaded by `+callee-need` track K's) leaves a `gen` whose cache
`[C1 C2 C3 C4 SURE]` keeps `QK`, the members' `sure` entries and the outside callees. -/
def MemSweepCall (r : RealCfg) (xs : ShapeX) (order : List Noun) (kids : Noun → List Noun) (outC : Noun → List Noun)
    (nout : Noun → NeedOrd) (envK : CallEnv) (RR : GenRest → Prop) (P : Noun → Prop) (S : Noun) (x : GenRest)
    (mode : Mode) (top : Noun → NeedOrd) (TOP : Noun)
    (st : St Noun NeedOrd) (keep : Bool) (DN KIDS ML0 CB SCC CODE LSR JH CACHE0 b ML CACHE : Noun) : Prop :=
  ∃ (cape : Cape) (DATA FOL : Noun) (nm : Nomm) (fuel : Nat), b = C (C cape.toNoun DATA) FOL ∧
    r.info b = ⟨nm, cape, DATA, fuel⟩ ∧ ∃ CA1,
    nock (C inlBody (C (C b (C (C CODE LSR) (C JH CACHE))) compK)) inlBody = some (C nm.toNoun CA1) ∧
    ∃ (col sur : NeedOrd) (G2 : Noun),
      MemShapeBranch xs mode (envView r.env r.scc (viewN top st) (viewS (cfgRealShape r xs order kids) st))
        cape DATA FOL nm fuel keep SCC (C CODE LSR) JH ML TOP CA1 (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0)
        col sur G2 ∧
    ∃ C1 C2 C3 C4 SURE, slot? 510 G2 = some (cacheN C1 C2 C3 C4 SURE) ∧ QK envK RR P S x (cacheN C1 C2 C3 C4 SURE) ∧
      SureHolds r.scc st.sure (cacheN C1 C2 C3 C4 SURE) ∧
      ∀ b', ((st.ml b').isSome ∨ b' = b) → ∀ k ∈ outC b', ∃ NR u,
        slot? 2 (cacheN C1 C2 C3 C4 SURE) = some NR ∧ getF mugF k NR = some (C (A 0) u) ∧ slot? 2 u = some (nout k).toNoun

/-- **`MemGate` on `%must` / `%may` for `cfgRealShape`** at `LoopRS` with `QK`: from `MemSweepCall`
at every call, `top` read through `TOP` (`hTOP`), the members in `S`, the start rest without
`sure` entries at the members, `RR` blind to `sure.cache`. -/
theorem memGate_sweep_real (r : RealCfg) (xs : ShapeX) (order : List Noun) (kids : Noun → List Noun)
    (outC : Noun → List Noun) (nout : Noun → NeedOrd) (envK : CallEnv) (RR : GenRest → Prop) (P : Noun → Prop)
    (S : Noun) (x : GenRest)
    (hRR : ∀ NR MO SC INL SU SU' s f : Noun, RR ⟨cacheN NR MO SC INL SU, s, f⟩ → RR ⟨cacheN NR MO SC INL SU', s, f⟩)
    (hS : ∀ b ∈ r.scc, b ∈ tapList S)
    (hxS : ∀ b ∈ r.scc, ∀ N u, slot? 31 x.cache = some N → getF mugF b N ≠ some (C (A 0) u))
    (mode : Mode) (hmode : mode ≠ Mode.done) (top : Noun → NeedOrd) (TOP : Noun) (hTOP : TopH top TOP)
    (DN KIDS ML0 CB SCC CODE LSR JH CACHE0 : Noun)
    (hcall : ∀ (st : St Noun NeedOrd) (keep : Bool) (b ML CACHE : Noun), b ∈ r.scc →
      LoopRS r.scc outC nout (QK envK RR P S x) st.ml st.sure ML CACHE →
      MemSweepCall r xs order kids outC nout envK RR P S x mode top TOP st keep DN KIDS ML0 CB SCC CODE LSR JH CACHE0
        b ML CACHE) :
    MemGate (cfgRealShape r xs order kids) (LoopRS (cfgRealShape r xs order kids).scc outC nout (QK envK RR P S x))
      (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0) top TOP mode (modeN mode) := by
  intro st keep b ML CA hb hR
  obtain ⟨cape, DATA, FOL, nm, fuel, rfl, hinfo, CA1, hinl, col, sur, G2, hbrn, C1, C2, C3, C4, SURE, hG2, hQ1, hsh1,
    hout1⟩ := hcall st keep _ ML CA hb hR
  exact mem_sweep_step r xs order kids outC nout envK RR P S x hRR mode hmode top TOP hTOP st keep cape DATA FOL nm fuel
    hinfo hb (hS _ hb) (hxS _ hb) ML CA DN KIDS ML0 CB SCC CODE LSR JH CACHE0 hR CA1 hinl col sur G2 hbrn C1 C2 C3 C4
    SURE hG2 hQ1 hsh1 hout1

/-- **The `%may` third of `SccLoopAt`** (`top` `~`, the loop's context `csiCtx`, `R := RK SC0 inl`). -/
theorem memGate_may_K (r : RealCfg) (xs : ShapeX) (order : List Noun) (kids : Noun → List Noun)
    (outC : Noun → List Noun) (nout : Noun → NeedOrd) (env : CallEnv) (SC0 : Noun) (inl : Noun → Option Nomm)
    (P : Noun → Prop) (S CODE JETS CALLS JH : Noun) (x : GenRest) (NR CR : Noun)
    (hS : ∀ b ∈ r.scc, b ∈ tapList S)
    (hxS : ∀ b ∈ r.scc, ∀ N u, slot? 31 x.cache = some N → getF mugF b N ≠ some (C (A 0) u))
    (hcall : ∀ (st : St Noun NeedOrd) (keep : Bool) (b ML CACHE : Noun), b ∈ r.scc →
      LoopRS r.scc outC nout (QK env (RK SC0 inl) P S x) st.ml st.sure ML CACHE →
      MemSweepCall r xs order kids outC nout env (RK SC0 inl) P S x Mode.may (fun _ => NeedOrd.none) (A 0) st keep
        (A 1) (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) (A 0) csiBody S CODE (C JETS CALLS) JH (C NR CR) b ML CACHE) :
    MemGate (cfgRealShape r xs order kids) (LoopRS (cfgRealShape r xs order kids).scc outC nout (QK env (RK SC0 inl) P S x))
      (csiCtx (A 1) (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) S (C CODE (C JETS CALLS)) JH (C NR CR))
      (fun _ => (cfgRealShape r xs order kids).none) (A 0) Mode.may (A 0x79616d) :=
  memGate_sweep_real r xs order kids outC nout env (RK SC0 inl) P S x rK_sure hS hxS Mode.may (by decide)
    (fun _ => NeedOrd.none) (A 0) topH_nil (A 1) _ (A 0) csiBody S CODE (C JETS CALLS) JH (C NR CR) hcall

/-- **The `%must` third of `SccLoopAt`**: `top` from the `%may` sweep (`TopN` of its `ml`). -/
theorem memGate_must_K (r : RealCfg) (xs : ShapeX) (order : List Noun) (kids : Noun → List Noun)
    (outC : Noun → List Noun) (nout : Noun → NeedOrd) (env : CallEnv) (SC0 : Noun) (inl : Noun → Option Nomm)
    (P : Noun → Prop) (S CODE JETS CALLS JH : Noun) (x : GenRest) (NR CR : Noun)
    (hS : ∀ b ∈ r.scc, b ∈ tapList S)
    (hxS : ∀ b ∈ r.scc, ∀ N u, slot? 31 x.cache = some N → getF mugF b N ≠ some (C (A 0) u))
    (sm : St Noun NeedOrd) (TOP : Noun) (hT : TopN sm.ml TOP)
    (hcall : ∀ (st : St Noun NeedOrd) (keep : Bool) (b ML CACHE : Noun), b ∈ r.scc →
      LoopRS r.scc outC nout (QK env (RK SC0 inl) P S x) st.ml st.sure ML CACHE →
      MemSweepCall r xs order kids outC nout env (RK SC0 inl) P S x Mode.must (topOf (cfgRealShape r xs order kids) sm)
        TOP st keep (A 1) (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) (A 0) csiBody S CODE (C JETS CALLS) JH (C NR CR)
        b ML CACHE) :
    MemGate (cfgRealShape r xs order kids) (LoopRS (cfgRealShape r xs order kids).scc outC nout (QK env (RK SC0 inl) P S x))
      (csiCtx (A 1) (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) S (C CODE (C JETS CALLS)) JH (C NR CR))
      (topOf (cfgRealShape r xs order kids) sm) TOP Mode.must (A 0x7473756d) :=
  memGate_sweep_real r xs order kids outC nout env (RK SC0 inl) P S x rK_sure hS hxS Mode.must (by decide)
    _ TOP (topH_of_topN hT) (A 1) _ (A 0) csiBody S CODE (C JETS CALLS) JH (C NR CR) hcall

end Compiler
end Formalization
