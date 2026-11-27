import lemmas.Compiler.CompSccLoopMemDone
import lemmas.Compiler.CompSccOfAny
import lemmas.Ska.SccLoopReal
import lemmas.Ska.PokeEnc

/-! # From the gate `member` on `%done` to `MemGate`'s per-call obligation (README Gaps 21.14)

`mem_gate_done_R` (`CompSccLoopMemDone.lean`) gives the product of the pill's gate `member` on
`%done` as nouns.  Here it is read against the model's `member (cfgReal r order kids)` (`Ska/
SccLoop.lean`, `Ska/SccLoopReal.lean`) and the relation of the loop `LoopR` with track K's
invariant `QK` (`CompSccOfAny.lean`):

* `wasN`, `memSurKN_was`, `memMovedN_was`, `memChgN_loob`, `memChgO_loob`: `sur`, `moved` and
  `chg` of the pill are the model's (`needOrd_toNoun_inj`);
* `csGetF_put_ne`, `csMlExact_put`, `csSureHolds_put`, `csAgreeIP_put`, `csExt_put`, `csQK_put`:
  the `+put:by` of `sure.cache` at a member `b` keeps `QK` (the write is exactly what `AgreeIP`
  at `P ∪ S` allows: the `sure` clause is not asked at the members of `S`), and the `+put:by` of
  `map-local` gives `MlExact` of the model's new `ml`;
* `memDoneM_eq`: the model's `%done` compile from the pieces of the run;
* **`mem_done_step`**: the per-call obligation of `MemGate` on `%done` for `cfgReal`, with the
  run of `+run` (at `mono` `|`) and what it leaves (`QK` at the rest, the members' `sure`
  entries, the outside callees held) as hypotheses, and the product of `+coerce-soft` (`hcs`,
  only when `need-pessimized` differs from `need-new`). -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## `sur`, `moved`, `chg` -/

/-- `was` as `+get:by` gives it. -/
def wasN : Option NeedOrd → Noun
  | some v => C (A 0) v.toNoun
  | none => A 0

theorem wasN_shape (w : Option NeedOrd) : wasN w = A 0 ∨ ∃ u, wasN w = C (A 0) u := by
  cases w <;> simp [wasN]

theorem memSurKN_was (keep : Bool) (w : Option NeedOrd) (sur : NeedOrd) :
    memSurKN keep (wasN w) sur.toNoun = (if keep then w.getD sur else sur).toNoun := by
  cases w <;> cases keep <;> simp [memSurKN, wasN]

theorem fallNone_was (w : Option NeedOrd) : fallNone (wasN w) = (w.getD NeedOrd.none).toNoun := by
  cases w <;> simp [fallNone, wasN, NeedOrd.toNoun, Tag.none]

theorem memMovedN_was (keep : Bool) (w : Option NeedOrd) (sur : NeedOrd) :
    memMovedN keep (wasN w) sur.toNoun = loob ((if keep then w.getD sur else sur) != w.getD NeedOrd.none) := by
  unfold memMovedN
  rw [memSurKN_was, fallNone_was]
  by_cases e : (if keep then w.getD sur else sur) = w.getD NeedOrd.none
  · rw [if_pos (by rw [e]), e]; simp [loob]
  · rw [if_neg (fun h => e (needOrd_toNoun_inj h))]; simp [loob, e]

theorem memChgN_loob (mv : Bool) (nn : NeedOrd) :
    memChgN (loob mv) nn.toNoun = loob (mv || nn != NeedOrd.none || NeedOrd.none != NeedOrd.none) := by
  unfold memChgN
  cases mv
  · simp only [loob, Bool.false_eq_true, if_false]
    by_cases e : nn = NeedOrd.none
    · subst e; simp [NeedOrd.toNoun, Tag.none]
    · have : C (A 0x656e6f6e) (A 0) ≠ nn.toNoun := fun h =>
        e (needOrd_toNoun_inj (by rw [← h]; simp [NeedOrd.toNoun, Tag.none]))
      simp [this, e]
  · simp [loob]

theorem memChgO_loob (mv : Bool) (np prev : NeedOrd) :
    memChgO (loob mv) np.toNoun prev.toNoun = loob (mv || np != prev) := by
  unfold memChgO
  cases mv
  · simp only [loob, Bool.false_eq_true, if_false]
    by_cases e : np = prev
    · subst e; simp
    · have : np.toNoun ≠ prev.toNoun := fun h => e (needOrd_toNoun_inj h)
      simp [this, e]
  · simp [loob]

/-! ## The `+put:by`s keep the relation -/

theorem csGetF_put_ne {M M' k v k' : Noun} (hm : IsMap mugF M) (hp : putF mugF k v M = some M')
    (hne : k' ≠ k) : getF mugF k' M' = getF mugF k' M := by
  obtain ⟨out, hput, hmo, hget⟩ := putF_spec mugF M k v hm
  rw [hp] at hput
  obtain rfl := Option.some.inj hput
  by_cases h : ∃ u, Get M k' u
  · obtain ⟨u, hu⟩ := h
    rw [getF_some hm hu, getF_some hmo ((hget k' u).2 (Or.inr ⟨hne, hu⟩))]
  · rw [getF_none hm (fun u hu => h ⟨u, hu⟩)]
    refine getF_none hmo (fun u hu => ?_)
    rcases (hget k' u).1 hu with ⟨e, -⟩ | ⟨-, hu'⟩
    · exact hne e
    · exact h ⟨u, hu'⟩

/-- **`MlExact` after the `+put:by` of `map-local`**: the straight put at `b` has the need `n`. -/
theorem csMlExact_put {ml : Noun → Option NeedOrd} {ML ML' b t : Noun} {n : NeedOrd} (h : MlExact ml ML)
    (hp : putF mugF b (C n.toNoun t) ML = some ML') : MlExact (upd ml b (some n)) ML' := by
  obtain ⟨out, hput, hmo, hget⟩ := putF_spec mugF ML b (C n.toNoun t) h.1
  rw [hp] at hput
  obtain rfl := Option.some.inj hput
  refine ⟨hmo, fun k v hv => ?_, fun k n' hk => ?_⟩
  · rcases (hget k v).1 hv with ⟨rfl, rfl⟩ | ⟨hne, hv'⟩
    · exact ⟨n, t, by simp, rfl⟩
    · obtain ⟨n', t', h1, h2⟩ := h.2.1 k v hv'
      exact ⟨n', t', by simp [upd, hne, h1], h2⟩
  · by_cases e : k = b
    · subst e
      simp only [upd_same, Option.some.injEq] at hk
      subst hk
      exact ⟨t, (hget _ _).2 (Or.inl ⟨rfl, rfl⟩)⟩
    · simp only [upd, e, if_false] at hk
      obtain ⟨t', ht⟩ := h.2.2 k n' hk
      exact ⟨t', (hget _ _).2 (Or.inr ⟨e, ht⟩)⟩

theorem cacheN_slot31 (C1 C2 C3 C4 SU : Noun) : slot? 31 (cacheN C1 C2 C3 C4 SU) = some SU := by
  simp [cacheN, nock_exec]

theorem cacheN_slot2 (C1 C2 C3 C4 SU : Noun) : slot? 2 (cacheN C1 C2 C3 C4 SU) = some C1 := by
  simp [cacheN, nock_exec]

/-- **`SureHolds` after the `+put:by` of `sure.cache`** at `b`. -/
theorem csSureHolds_put {bs : List Noun} {sure : Noun → Option NeedOrd} {C1 C2 C3 C4 SU SU' b : Noun}
    {v : NeedOrd} (h : SureHolds bs sure (cacheN C1 C2 C3 C4 SU)) (hm : IsMap mugF SU)
    (hp : putF mugF b v.toNoun SU = some SU') : SureHolds bs (upd sure b (some v)) (cacheN C1 C2 C3 C4 SU') := by
  obtain ⟨S0, hS0, hall⟩ := h
  rw [cacheN_slot31] at hS0
  obtain rfl := Option.some.inj hS0
  refine ⟨SU', cacheN_slot31 _ _ _ _ _, fun k hk => ?_⟩
  by_cases e : k = b
  · subst e; exact Or.inl ⟨v, by simp, (getF_put_self hm hp).2⟩
  · rw [show upd sure b (some v) k = sure k from by simp [upd, e], csGetF_put_ne hm hp e]
    exact hall k hk

/-- **`AgreeIP` after the `+put:by` of `sure.cache`** at a bell in progress. -/
theorem csAgreeIP_put {env : CallEnv} {P' : Noun → Prop} {NR MO SC INL SU SU' b v s f : Noun}
    (h : AgreeIP env P' ⟨cacheN NR MO SC INL SU, s, f⟩) (hp : putF mugF b v SU = some SU') (hb : P' b) :
    AgreeIP env P' ⟨cacheN NR MO SC INL SU', s, f⟩ := by
  obtain ⟨hs, NR1, MO1, SC1, INL1, SU1, hc, h1, h2, h3, h4⟩ := h
  simp only [cacheN, Noun.cell.injEq] at hc
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hc
  refine ⟨hs, NR, MO, SC, INL, SU', rfl, h1, (getF_put_self h2 hp).1, fun bb u hu => ?_, fun bb w hw hn => ?_⟩
  · obtain ⟨hn, w, hw⟩ := h3 bb u hu
    refine ⟨hn, ?_⟩
    by_cases e : bb.toNoun = b
    · exact ⟨v, by rw [e]; exact (getF_put_self h2 hp).2⟩
    · exact ⟨w, by rw [csGetF_put_ne h2 hp e]; exact hw⟩
  · rcases getF_put_cases h2 hp hw with ⟨e, -⟩ | ⟨-, hw'⟩
    · exact absurd (e ▸ hb) hn
    · exact h4 bb w hw' hn

/-- **`Ext` after the `+put:by` of `sure.cache`** at a key that the start rest `x` does not hold. -/
theorem csExt_put {x : GenRest} {NR MO SC INL SU SU' b v s f : Noun}
    (h : Ext x ⟨cacheN NR MO SC INL SU, s, f⟩) (hm : IsMap mugF SU) (hp : putF mugF b v SU = some SU')
    (hxb : ∀ N u, slot? 31 x.cache = some N → getF mugF b N ≠ some (C (A 0) u)) :
    Ext x ⟨cacheN NR MO SC INL SU', s, f⟩ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, fun N hN => ?_, fun N hN => ?_⟩
  · obtain ⟨N', hN', hsub⟩ := h3 N hN
    have e2 : slot? 2 (cacheN NR MO SC INL SU) = some N' := hN'
    rw [cacheN_slot2] at e2
    exact ⟨N', by rw [← e2]; exact cacheN_slot2 _ _ _ _ _, hsub⟩
  · obtain ⟨N', hN', hsub⟩ := h4 N hN
    have hN'' : slot? 31 (cacheN NR MO SC INL SU) = some N' := hN'
    rw [cacheN_slot31] at hN''
    obtain rfl := Option.some.inj hN''
    refine ⟨SU', cacheN_slot31 _ _ _ _ _, fun k u hk => ?_⟩
    have hne : k ≠ b := by rintro rfl; exact hxb N u hN hk
    rw [csGetF_put_ne hm hp hne]
    exact hsub k u hk

/-- **`QK` after the `+put:by` of `sure.cache` at a member `b` of `S`**: `R` does not read
`sure.cache` (`hRR`), and the start rest `x` has no entry of `b` (`hxb`). -/
theorem csQK_put {env : CallEnv} {RR : GenRest → Prop} {P : Noun → Prop} {S : Noun} {x : GenRest}
    (hRR : ∀ NR MO SC INL SU SU' s f : Noun, RR ⟨cacheN NR MO SC INL SU, s, f⟩ → RR ⟨cacheN NR MO SC INL SU', s, f⟩)
    {C1 C2 C3 C4 SU SU' b v : Noun} (h : QK env RR P S x (cacheN C1 C2 C3 C4 SU))
    (hp : putF mugF b v SU = some SU') (hbS : b ∈ tapList S)
    (hxb : ∀ N u, slot? 31 x.cache = some N → getF mugF b N ≠ some (C (A 0) u)) :
    QK env RR P S x (cacheN C1 C2 C3 C4 SU') ∧ IsMap mugF SU := by
  obtain ⟨hA, hE, hR, NR, REST, hc, hmiss⟩ := h
  have hm : IsMap mugF SU := by
    obtain ⟨-, NR1, MO1, SC1, INL1, SU1, hc1, -, h2, -⟩ := hA
    simp only [cacheN, Noun.cell.injEq] at hc1
    obtain ⟨-, -, -, -, rfl⟩ := hc1
    exact h2
  refine ⟨⟨csAgreeIP_put hA hp (Or.inr hbS), csExt_put hE hm hp hxb, hRR _ _ _ _ _ _ _ _ hR, C1,
    C C2 (C C3 (C C4 SU')), rfl, ?_⟩, hm⟩
  simp only [cacheN, Noun.cell.injEq] at hc
  obtain ⟨rfl, -⟩ := hc
  exact hmiss

/-- `RK` does not read `sure.cache`. -/
theorem rK_sure {SC0 : Noun} {inl : Noun → Option Nomm} :
    ∀ NR MO SC INL SU SU' s f : Noun, RK SC0 inl ⟨cacheN NR MO SC INL SU, s, f⟩ → RK SC0 inl ⟨cacheN NR MO SC INL SU', s, f⟩ := by
  intro NR MO SC INL SU SU' s f ⟨⟨NR1, MO1, INL1, SU1, hc, hil, hin⟩, NRc, hNRc, hcl⟩
  simp only [cacheN, Noun.cell.injEq] at hc
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hc
  exact ⟨⟨NR, MO, INL, SU', rfl, hil, hin⟩, NRc, hNRc, hcl⟩

/-! ## The model's `%done` compile -/

/-- **`memDoneM` from the pieces of the run.** -/
theorem memDoneM_eq (env : CallEnv) (nm : Nomm) (cape : Cape) (DATA : Noun) (fuel : Nat) (nex : NextL CSet)
    (g1 : Gen (TreapMap mugF))
    (hrunL : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
    (hargs : nex.th.args = []) (ord : NeedOrd) (hcol : shapeCol fuel nex.laz cape = some ord) (nedF : Need)
    (g2 : Gen (TreapMap mugF)) (hnoar : needOrdAllocRegs ord g1 = some (nedF, g2)) (sur : NeedOrd)
    (hsur : sureOf (needToOrd nex.laz.sure.ned) nex.laz.sure.lok cape = some sur) :
    memDoneM env ⟨nm, cape, DATA, fuel⟩ = some ⟨needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1, sur⟩ := by
  simp [memDoneM, hrunL, hargs, hcol, hnoar, hsur]

/-- `QK` holds `sure.cache` as a map. -/
theorem qK_map {env : CallEnv} {RR : GenRest → Prop} {P : Noun → Prop} {S : Noun} {x : GenRest}
    {C1 C2 C3 C4 SU : Noun} (h : QK env RR P S x (cacheN C1 C2 C3 C4 SU)) : IsMap mugF SU := by
  obtain ⟨⟨-, NR1, MO1, SC1, INL1, SU1, hc1, -, h2, -⟩, -⟩ := h
  simp only [cacheN, Noun.cell.injEq] at hc1
  obtain ⟨-, -, -, -, rfl⟩ := hc1
  exact h2

/-- `was`: `SureHolds` at the member gives the `+get:by` of `sure.cache`. -/
theorem sureHolds_was {bs : List Noun} {sure : Noun → Option NeedOrd} {C1 C2 C3 C4 SU b : Noun}
    (h : SureHolds bs sure (cacheN C1 C2 C3 C4 SU)) (hb : b ∈ bs) : getF mugF b SU = some (wasN (sure b)) := by
  obtain ⟨S0, hS0, hall⟩ := h
  rw [cacheN_slot31] at hS0
  obtain rfl := Option.some.inj hS0
  rcases hall b hb with ⟨v, hv, hg⟩ | ⟨hv, hg⟩ <;> rw [hv] <;> exact hg

/-! ## The step -/

/-- **The per-call obligation of `MemGate` on `%done` for `cfgReal`** (`top` `~`, `TOP` `~`), at a
member `b = [[cape DATA] FOL]` of the SCC `S` (`r.info b` its nomm, cape, data, fuel), with
`LoopR` for track K's invariant `QK env RR P S x`.  Hypotheses besides the pill's arms:
* `+inlined` (`hinl`) and the run of `+run` at `mono` `|` (`hrunN`) on the views of the state,
  against the model's run `hrunL` in the environment `envView` of those views, leaving a rest `x1`
  (no soft, cache `[C1 C2 C3 C4 SURE]`) that keeps `QK` (`hQ1`), the members' `sure` entries
  (`hsh1`) and holds the outside callees of the members with entries and of `b` (`hout1`): what
  the threaded run link gives;
* the model's `+shape-collapse` returns (`hcol`), the residual of the bake is a run (`hrun`,
  track A's `BakeRunO`), `+sure-of` (`hsur`), `finish ~` returns (`hfin`);
* `+coerce-soft` (`hcs`): on an entry `prev` with `need-pessimized` not `need-new`, `finish` on
  `[~ need-pessimized]` returns a straight with that need (never taken on the corpus:
  `Ska/SccLoopRealCheck.lean`);
* `RR` does not read `sure.cache` (`hRR`, `rK_sure`), and the start rest `x` has no `sure` entry at
  the members (`hxS`: from `AgreeIP env P x` and the members missing, as at track K's miss). -/
theorem mem_done_step (r : RealCfg) (order : List Noun) (kids : Noun → List Noun)
    (outC : Noun → List Noun) (nout : Noun → NeedOrd) (envK : CallEnv) (RR : GenRest → Prop) (P : Noun → Prop)
    (S : Noun) (x : GenRest)
    (hRR : ∀ NR MO SC INL SU SU' s f : Noun, RR ⟨cacheN NR MO SC INL SU, s, f⟩ → RR ⟨cacheN NR MO SC INL SU', s, f⟩)
    (st : St Noun NeedOrd) (keep : Bool) (cape : Cape) (DATA FOL : Noun) (nm : Nomm) (fuel : Nat)
    (hinfo : r.info (C (C cape.toNoun DATA) FOL) = ⟨nm, cape, DATA, fuel⟩)
    (hbr : C (C cape.toNoun DATA) FOL ∈ r.scc) (hbS : C (C cape.toNoun DATA) FOL ∈ tapList S)
    (hxS : ∀ N u, slot? 31 x.cache = some N → getF mugF (C (C cape.toNoun DATA) FOL) N ≠ some (C (A 0) u))
    (ML CACHE DN KIDS ML0 CB SCC CODE LSR JH CACHE0 : Noun)
    (hR : LoopR r.scc outC nout (QK envK RR P S x) st.ml st.sure ML CACHE)
    (CA1 : Noun)
    (hinl : nock (C inlBody (C (C (C (C cape.toNoun DATA) FOL) (C (C CODE LSR) (C JH CACHE))) compK)) inlBody
      = some (C nm.toNoun CA1))
    (nex : NextL CSet) (g1 : Gen (TreapMap mugF))
    (hrunL : runLC (envView r.env r.scc (viewN (fun _ => NeedOrd.none) st) (viewS (cfgReal r order kids) st))
      Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
    (x1 : GenRest)
    (hrunN : nock (crSubj (A 1) nm.toNoun (C (A 0x656e6f64) (A 0)) (A 0) (A 0)
        (compCore genEntry (cuRest CA1) (memDCtx SCC (C CODE LSR) JH ML (A 0) (C (C cape.toNoun DATA) FOL)))) crDol
      = some (C nex.goal.toNoun (genNoun g1 x1)))
    (C1 C2 C3 C4 SURE : Noun) (hx1 : x1.cache = cacheN C1 C2 C3 C4 SURE) (hs1 : x1.soft = A 0)
    (hQ1 : QK envK RR P S x (cacheN C1 C2 C3 C4 SURE))
    (hsh1 : SureHolds r.scc st.sure (cacheN C1 C2 C3 C4 SURE))
    (hout1 : ∀ b', ((st.ml b').isSome ∨ b' = C (C cape.toNoun DATA) FOL) → ∀ k ∈ outC b', ∃ NR u,
      slot? 2 (cacheN C1 C2 C3 C4 SURE) = some NR ∧ getF mugF k NR = some (C (A 0) u) ∧ slot? 2 u = some (nout k).toNoun)
    (ord : NeedOrd) (hcol : shapeCol fuel nex.laz cape = some ord)
    (hargs : nex.th.args = []) (nedF : Need) (g2 : Gen (TreapMap mugF))
    (hnoar : needOrdAllocRegs ord g1 = some (nedF, g2))
    (hrun : isRun (flattenNeed (bakeNeed nedF (Sock.mk cape DATA)).1)
      ((flattenNeed (bakeNeed nedF (Sock.mk cape DATA)).1).headD 0) 0 = true)
    (sur : NeedOrd) (hsur : sureOf (needToOrd nex.laz.sure.ned) nex.laz.sure.lok cape = some sur)
    (hfin : ∃ s, finishLFC (S := CSet) (Map := TreapMap mugF)
      (envView r.env r.scc (viewN (fun _ => NeedOrd.none) st) (viewS (cfgReal r order kids) st)) nm ord cape
        (fun n => bakeNeed n (Sock.mk cape DATA)) = some s)
    (hcs : ∀ (prev : NeedOrd) (SURE' : Noun), st.ml (C (C cape.toNoun DATA) FOL) = some prev →
      msgOrd (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1) prev cape ≠ needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1 →
      ∃ t, nock (C finBody (C (C (A 0) (msgOrd (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1) prev cape).toNoun)
            (memFCR keep (wasN (st.sure (C (C cape.toNoun DATA) FOL))) sur.toNoun
              (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1).toNoun nex.laz.toNoun nedF.toNoun
              (bakeNeed nedF (Sock.mk cape DATA)).1.toNoun (immNoun (bakeNeed nedF (Sock.mk cape DATA)).2)
              nex.th.there (genNoun g2 x1) nm.toNoun
              (memDCtx SCC (C CODE LSR) JH ML (A 0) (C (C cape.toNoun DATA) FOL)) (C (C cape.toNoun DATA) FOL) ML
              (A 0) (cacheN C1 C2 C3 C4 SURE') (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0)))) finBody
        = some (C (msgOrd (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1) prev cape).toNoun t)) :
    ∃ ML' CA', nock (C memBody (C (memSam (C (C cape.toNoun DATA) FOL) (A 0x656e6f64) (loob keep) ML (A 0) CACHE)
        (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0))) memBody
        = some (C (loob (member (cfgReal r order kids) (fun _ => (cfgReal r order kids).none)
            (C (C cape.toNoun DATA) FOL) Mode.done keep st).1) (C ML' CA')) ∧
      LoopR r.scc outC nout (QK envK RR P S x)
        (member (cfgReal r order kids) (fun _ => (cfgReal r order kids).none) (C (C cape.toNoun DATA) FOL) Mode.done keep st).2.ml
        (member (cfgReal r order kids) (fun _ => (cfgReal r order kids).none) (C (C cape.toNoun DATA) FOL) Mode.done keep st).2.sure
        ML' CA' := by
  generalize hB : C (C cape.toNoun DATA) FOL = B at *
  -- the model's compile
  have ho : compReal r B Mode.done (viewN (fun _ => NeedOrd.none) st) (viewS (cfgReal r order kids) st)
      = ⟨needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1, sur⟩ :=
    compReal_done r B _ _ _ (by rw [hinfo]; exact memDoneM_eq _ nm cape DATA fuel nex g1 hrunL hargs ord hcol nedF g2 hnoar sur hsur)
  have hnone0 : (cfgReal r order kids).none = NeedOrd.none := rfl
  have hcomp : (cfgReal r order kids).comp B Mode.done (viewN (fun _ => NeedOrd.none) st) (viewS (cfgReal r order kids) st)
      = ⟨needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1, sur⟩ := ho
  generalize hNN : needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1 = nn at *
  -- `sure.cache` at `b`
  have hmS : IsMap mugF SURE := qK_map hQ1
  have hwas := sureHolds_was hsh1 hbr
  obtain ⟨SURE', hput, -, -⟩ := putF_spec mugF SURE B (memSurKN keep (wasN (st.sure B)) sur.toNoun) hmS
  have hput' := hput
  rw [memSurKN_was] at hput'
  have hQ' := (csQK_put hRR hQ1 hput' hbS hxS).1
  have hSH' := csSureHolds_put hsh1 hmS hput'
  have hml := hR.1.1
  have hg := mem_gate_done_R cape DATA FOL keep ML CACHE DN KIDS ML0 CB SCC CODE LSR JH CACHE0 nm CA1
    (by rw [hB]; exact hinl) _ nex g1 hrunL x1 (by rw [hB]; exact hrunN) C1 C2 C3 C4 SURE hx1 hs1 ord
    (sc_gate _ _ _ _ hcol) hargs nedF g2 hnoar hrun sur hsur (wasN (st.sure B)) SURE'
    (by rw [hB]; exact hwas) (wasN_shape _) (by rw [hB]; exact hput) hml
  rw [hB, hNN] at hg
  obtain ⟨s, hs⟩ := hfin
  have hsn : s.need = nn := by
    rw [← hNN]; exact finishLFC_need _ nm ord cape _ nex g1 hrunL nedF g2 hnoar s hs
  have hout' : ∀ np : NeedOrd, OutsHeld outC nout (upd st.ml B (some np)) (cacheN C1 C2 C3 C4 SURE') := by
    intro np b' hb' k hk
    obtain ⟨NR, u, h2, h3, h4⟩ := hout1 b' (by
      by_cases e : b' = B
      · exact Or.inr e
      · left; simpa [upd, e] using hb') k hk
    rw [cacheN_slot2] at h2
    exact ⟨NR, u, by rw [cacheN_slot2]; exact h2, h3, h4⟩
  rw [memMovedN_was] at hg
  cases hm : st.ml B with
  | none =>
    have hnone : getF mugF B ML = some (A 0) :=
      getF_none hml (fun v hv => by obtain ⟨n, t, hn, -⟩ := hR.1.2.1 B v hv; rw [hm] at hn; cases hn)
    obtain ⟨ML', hp, -, -⟩ := putF_spec mugF ML B s.toNoun hml
    have hp' : putF mugF B (C nn.toNoun (C (A s.nargs) (HoonMap.toNoun Blob.toNoun s.blocks))) ML = some ML' := by
      rw [← hsn]; exact hp
    refine ⟨ML', cacheN C1 C2 C3 C4 SURE', ?_, ?_⟩
    · rw [hg.1 hnone, hs]
      simp only [Option.bind_some, hp, Option.map_some, memChgN_loob]
      simp [member, hnone0, hcomp, hm]
    · have e1 : (member (cfgReal r order kids) (fun _ => (cfgReal r order kids).none) B Mode.done keep st).2.ml
          = upd st.ml B (some nn) := by simp [member, hnone0, hcomp, hm]
      have e2 : (member (cfgReal r order kids) (fun _ => (cfgReal r order kids).none) B Mode.done keep st).2.sure
          = upd st.sure B (some (if keep then (st.sure B).getD sur else sur)) := by simp [member, hnone0, hcomp, hm]
      rw [e1, e2]
      exact ⟨csMlExact_put hR.1 hp', hSH', hout' nn, hQ'⟩
  | some prev =>
    obtain ⟨t, ht⟩ := hR.1.2.2 B prev hm
    have hprev : getF mugF B ML = some (C (A 0) (C prev.toNoun t)) := getF_some hml ht
    have hg2 := hg.2 prev t hprev
    have hmsg : (cfgReal r order kids).msg B nn prev = msgOrd nn prev cape := by simp [cfgReal, hinfo]
    by_cases hnp : msgOrd nn prev cape = nn
    · rw [if_pos (by rw [hnp]), hs] at hg2
      obtain ⟨ML', hp, -, -⟩ := putF_spec mugF ML B s.toNoun hml
      have hp' : putF mugF B (C (msgOrd nn prev cape).toNoun (C (A s.nargs) (HoonMap.toNoun Blob.toNoun s.blocks))) ML
          = some ML' := by rw [hnp, ← hsn]; exact hp
      refine ⟨ML', cacheN C1 C2 C3 C4 SURE', ?_, ?_⟩
      · rw [hg2]
        simp only [Option.map_some, Option.bind_some, hp, memChgO_loob]
        simp [member, hnone0, hcomp, hm, hmsg]
      · have e1 : (member (cfgReal r order kids) (fun _ => (cfgReal r order kids).none) B Mode.done keep st).2.ml
            = upd st.ml B (some (msgOrd nn prev cape)) := by simp [member, hnone0, hcomp, hm, hmsg]
        have e2 : (member (cfgReal r order kids) (fun _ => (cfgReal r order kids).none) B Mode.done keep st).2.sure
            = upd st.sure B (some (if keep then (st.sure B).getD sur else sur)) := by simp [member, hnone0, hcomp, hm]
        rw [e1, e2]
        exact ⟨csMlExact_put hR.1 hp', hSH', hout' _, hQ'⟩
    · have hne : (msgOrd nn prev cape).toNoun ≠ nn.toNoun := fun h => hnp (needOrd_toNoun_inj h)
      rw [if_neg hne] at hg2
      obtain ⟨t', ht'⟩ := hcs prev SURE' hm hnp
      rw [ht'] at hg2
      obtain ⟨ML', hp, -, -⟩ := putF_spec mugF ML B (C (msgOrd nn prev cape).toNoun t') hml
      refine ⟨ML', cacheN C1 C2 C3 C4 SURE', ?_, ?_⟩
      · rw [hg2]
        simp only [Option.bind_some, hp, Option.map_some, memChgO_loob]
        simp [member, hnone0, hcomp, hm, hmsg]
      · have e1 : (member (cfgReal r order kids) (fun _ => (cfgReal r order kids).none) B Mode.done keep st).2.ml
            = upd st.ml B (some (msgOrd nn prev cape)) := by simp [member, hnone0, hcomp, hm, hmsg]
        have e2 : (member (cfgReal r order kids) (fun _ => (cfgReal r order kids).none) B Mode.done keep st).2.sure
            = upd st.sure B (some (if keep then (st.sure B).getD sur else sur)) := by simp [member, hnone0, hcomp, hm]
        rw [e1, e2]
        exact ⟨csMlExact_put hR.1 hp, hSH', hout' _, hQ'⟩

end Compiler
end Formalization
