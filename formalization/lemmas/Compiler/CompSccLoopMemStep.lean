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

end Compiler
end Formalization
