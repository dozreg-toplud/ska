import lemmas.Compiler.CompSccLoopSt
import lemmas.Hoon.RunByP

/-! # The final pass and the `%may` sweep of `+compile-scc-in` on any SCC (README Gaps 21.11)

* `fin_scc_gate`: the gate `final` on `[keep map-local cache]` for any `scc` (`SccN`): the
  `+roll` of `member b %done keep m ~ c` over `~(tap in scc)` against `final c keep`, under the
  member gate hypothesis `MemGate` (mode `%done`, `top` empty), then `+uni:by` at `nary`.  It is
  `csi_final_one` (`CompSccGate.lean`) for any number of bells.
* `may_roll`: the `%may` `+roll` `csfMay` over `order` from an empty `m` against `maySweep`
  (mode `%may`, `keep` false, `top` empty).
* `fin_fold`: the induction under both, a `foldlM` of a gate that runs `member` against the
  model's `foldl` of `member`. -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {N : Type} [DecidableEq N]

/-- **The roll of `member` against the model's fold**: a gate `g` that, on `[b ML CA]`, gives
`[ray cache]` of the member gate, folded over a list of members, gives the nouns that `R`
relates to the model's fold of `member`. -/
theorem fin_fold (c : Cfg Noun N) (R : (Noun → Option N) → (Noun → Option N) → Noun → Noun → Prop)
    (ctx : Noun) (top : Noun → N) (TOP : Noun) (mode : Mode) (MODE : Noun) (keep : Bool)
    (hm : MemGate c R ctx top TOP mode MODE) (g : Noun → Noun → Option Noun)
    (hg : ∀ b ML CA, b ∈ c.scc → ∀ CHG ML' CA',
      nock (C memBody (C (memSam b MODE (loob keep) ML TOP CA) ctx)) memBody = some (C CHG (C ML' CA')) →
      g b (C ML CA) = some (C ML' CA')) :
    ∀ (l : List Noun), (∀ b ∈ l, b ∈ c.scc) → ∀ (st : St Noun N) (ML CA : Noun), R st.ml st.sure ML CA →
      ∃ ML' CA', l.foldlM (fun acc x => g x acc) (C ML CA) = some (C ML' CA') ∧
        R (l.foldl (fun st b => (member c top b mode keep st).2) st).ml
          (l.foldl (fun st b => (member c top b mode keep st).2) st).sure ML' CA' := by
  intro l
  induction l with
  | nil => intro _ st ML CA hR; exact ⟨ML, CA, rfl, hR⟩
  | cons b l ih =>
    intro hl st ML CA hR
    obtain ⟨ML1, CA1, hn, hR1⟩ := hm st keep b ML CA (hl b (by simp)) hR
    have hgb := hg b ML CA (hl b (by simp)) _ _ _ hn
    obtain ⟨ML', CA', hf, hR'⟩ := ih (fun x hx => hl x (by simp [hx])) _ ML1 CA1 hR1
    refine ⟨ML', CA', ?_, hR'⟩
    simp only [List.foldlM_cons, hgb, Option.bind_eq_bind, Option.bind_some]
    exact hf

/-! ## `final` -/

/-- The gate of the `+roll` of `final` on `[b ML CA]`: `member b %done keep ML ~ CA`, then
`[ray cache]`. -/
theorem fin_fgate (p : LoopP) (KEEP ML0 CA0 b ML CA CHG ML' CA' : Noun)
    (hm : nock (C memBody (C (memSam b (A 0x656e6f64) KEEP ML (A 0) CA) p.ctx)) memBody
      = some (C CHG (C ML' CA'))) :
    nock (C fGate (C (C b (C ML CA)) (C fBody (C (C KEEP (C ML0 CA0)) p.sm)))) fGate
      = some (C ML' CA') := by
  unfold fGate
  unfold LoopP.sm LoopP.ctx csiSM memSam at *
  generalize memBody = MB at hm ⊢
  simp [nock_exec, hm]

/-- `~(tap in scc)` of a set whose `tapList` is `c.scc`. -/
theorem fin_tap (c : Cfg Noun N) (SCC : Noun) (h : SccN c SCC) :
    tapF SCC (A 0) = some (listN c.scc) := by
  have := tapF_list h.1 []
  simp only [List.append_nil] at this
  rw [← h.2.1]; exact this

/-- **`final` on `[keep map-local cache]` for any SCC**: the `+roll` over `~(tap in scc)` of
`member b %done keep m ~ c` (`hm`) ends with nouns `R` relates to `final c keep st`, and with
`cache = [nary rest]` the gate returns `[m cache]` with `nary` united with `m` (`+uni:by`,
the product `NARYU`). -/
theorem fin_scc_gate (c : Cfg Noun N) (R : (Noun → Option N) → (Noun → Option N) → Noun → Noun → Prop)
    (p : LoopP) (hm : MemGate c R p.ctx (fun _ => c.none) (A 0) Mode.done (A 0x656e6f64))
    (hscc : SccN c p.SCC) (keep : Bool) (st : St Noun N) (ML CA : Noun)
    (hR : R st.ml st.sure ML CA) :
    ∃ ML' CA', R (final c keep st).ml (final c keep st).sure ML' CA' ∧
      ∀ NARY REST NARYU, CA' = C NARY REST →
        nock (C by.uni.battery (C ML' (C by.battery (C NARY layer2)))) by.uni.battery = some NARYU →
        nock (C fBody (C (C (loob keep) (C ML CA)) p.sm)) fBody = some (C ML' (C NARYU REST)) := by
  let FC := C fBody (C (C (loob keep) (C ML CA)) p.sm)
  let g : Noun → Noun → Option Noun := fun x acc => nock (C fGate (C (C x acc) FC)) fGate
  have hg : ∀ b ML1 CA1, b ∈ c.scc → ∀ CHG ML' CA',
      nock (C memBody (C (memSam b (A 0x656e6f64) (loob keep) ML1 (A 0) CA1) p.ctx)) memBody
        = some (C CHG (C ML' CA')) → g b (C ML1 CA1) = some (C ML' CA') := by
    intro b ML1 CA1 _ CHG ML' CA' h
    exact fin_fgate p (loob keep) ML CA b ML1 CA1 CHG ML' CA' h
  obtain ⟨ML', CA', hf, hR'⟩ := fin_fold c R p.ctx (fun _ => c.none) (A 0) Mode.done (A 0x656e6f64)
    keep hm g hg c.scc (fun _ h => h) st ML CA hR
  refine ⟨ML', CA', hR', ?_⟩
  intro NARY REST NARYU hCA huni
  subst hCA
  have hL := compK_layer2
  have hbb := bell_bunt
  have htap := fin_tap c p.SCC hscc
  have hr := roll_gate_M layer2 fGate bellBunt (C ML CA) FC g c.scc (fun _ _ _ => rfl)
  rw [hf] at hr
  show nock FC fBody = _
  conv => { lhs; arg 2; unfold fBody }
  have hFC : FC = C fBody (C (C (loob keep) (C ML CA))
      (C p.mg (C p.DN (C p.KIDS (C (A 0) (C csiBody (C (csiSam p.SCC p.LONG p.JH p.CA0) compK))))))) := rfl
  rw [hFC] at hr ⊢
  unfold LoopP.mg LoopP.ctx csiCtx memCtx csiSam at *
  generalize compK = KC at hL hbb hr ⊢
  unfold bellBuntF at hbb
  simp only [nock_exec] at hbb
  simp [nock_exec, hL, fRoll, roll.arm_at, roll_arm, fTap, in.arm_at, in_arm, in.tap.arm_at, tap_arm, tap_loop,
    htap, fRBunt, hbb, hr, fUni, by.arm_at, by_arm, by.uni.arm_at, uni_by_arm, huni]

/-! ## The `%may` sweep -/

/-- The bunt of `(map bell straight)`, as `csfMayBunt` computes it, on `compK`. -/
def mayMapBuntF : Noun :=
  C (A 7) (C
    (C (A 8) (C (C (A 9) (C (A 0x2fa6) (C (A 0) (A 65535)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6)
      (C (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 382) (C (A 0) (A 31))))))
        (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 22) (C (A 0) (A 3)))))))) (C (A 0) (A 2))))))))
    (C (A 9) (C (A 2) (C (A 0) (A 1)))))

theorem may_map_bunt : nock compK mayMapBuntF = some (A 0) :=
  nock_of_evalFuel (fuel := 4000) (by kernel_rfl)

/-- The sample bunt of the gate of the `%may` `+roll` on `[order subject]`:
`[bell-bunt ~ cache]`. -/
theorem may_bunt_eval (KC ORD FG MG DN KIDS ML CB SCC LONG JH CA : Noun)
    (hbb : nock KC bellBuntF = some bellBunt) (hmb : nock KC mayMapBuntF = some (A 0)) :
    nock (C ORD (C FG (C MG (C DN (C KIDS (C ML (C CB (C (C SCC (C LONG (C JH CA))) KC)))))))) csfMayBunt
      = some (C bellBunt (C (A 0) CA)) := by
  unfold bellBuntF at hbb
  unfold mayMapBuntF at hmb
  simp only [nock_exec] at hbb hmb
  simp only [csfMayBunt, nock_exec, hbb, hmb]

/-- The gate of the `%may` `+roll` on `[b ML CA]`: `member b %may | ML ~ CA`, then
`[ray cache]`. -/
theorem may_gate (p : LoopP) (ORD REST b ML CA CHG ML' CA' : Noun)
    (hm : nock (C memBody (C (memSam b (A 0x79616d) (A 1) ML (A 0) CA) p.ctx)) memBody
      = some (C CHG (C ML' CA'))) :
    nock (C csfMayGate (C (C b (C ML CA)) (C ORD (C p.fg (C p.mg REST))))) csfMayGate = some (C ML' CA') := by
  unfold csfMayGate
  unfold LoopP.mg memSam at *
  generalize memBody = MB at hm ⊢
  simp [nock_exec, hm]

/-- **The `%may` sweep**: the `+roll` over `order` of `member b %may | m ~ c` from an empty `m`
and the cache `CA` of the subject ends with nouns that `R` relates to `maySweep c st0`. -/
theorem may_roll (c : Cfg Noun N) (R : (Noun → Option N) → (Noun → Option N) → Noun → Noun → Prop)
    (p : LoopP) (hm : MemGate c R p.ctx (fun _ => c.none) (A 0) Mode.may (A 0x79616d))
    (hord : p.ORD = listN c.order) (hsub : ∀ b ∈ c.order, b ∈ c.scc)
    (st0 : St Noun N) (CA : Noun) (hR : R st0.ml st0.sure (A 0) CA) :
    ∃ MAY CA1, nock (C p.ORD (p.subj (A 0) CA)) csfMay = some (C MAY CA1) ∧
      R (maySweep c st0).ml (maySweep c st0).sure MAY CA1 := by
  let T := C p.ORD (p.subj (A 0) CA)
  have hT : T = C p.ORD (C p.fg (C p.mg (C p.DN (C p.KIDS (C (A 0) (C csiBody
      (C (csiSam p.SCC p.LONG p.JH CA) compK))))))) := rfl
  let g : Noun → Noun → Option Noun := fun x acc => nock (C csfMayGate (C (C x acc) T)) csfMayGate
  have hg : ∀ b ML1 CA1, b ∈ c.scc → ∀ CHG ML' CA',
      nock (C memBody (C (memSam b (A 0x79616d) (loob false) ML1 (A 0) CA1) p.ctx)) memBody
        = some (C CHG (C ML' CA')) → g b (C ML1 CA1) = some (C ML' CA') := by
    intro b ML1 CA1 _ CHG ML' CA' h
    show nock (C csfMayGate (C (C b (C ML1 CA1)) (C p.ORD (C p.fg (C p.mg _))))) csfMayGate = _
    exact may_gate p p.ORD _ b ML1 CA1 CHG ML' CA' h
  obtain ⟨MAY, CA1, hf, hR'⟩ := fin_fold c R p.ctx (fun _ => c.none) (A 0) Mode.may (A 0x79616d)
    false hm g hg c.order hsub st0 (A 0) CA hR
  refine ⟨MAY, CA1, ?_, hR'⟩
  have hL := compK_layer2
  have hbb := bell_bunt
  have hmb := may_map_bunt
  have hr := roll_gate_M layer2 csfMayGate bellBunt (C (A 0) CA) T g c.order (fun _ _ _ => rfl)
  rw [hf] at hr
  show nock T csfMay = _
  rw [csfMay_eq]
  rw [hT] at hr ⊢
  rw [hord] at hr ⊢
  unfold LoopP.fg LoopP.mg LoopP.sm LoopP.ctx csiSM csiCtx memCtx csiSam at *
  generalize compK = KC at hL hbb hmb hr ⊢
  have hB := fun ORD FG MG DN KIDS SCC LONG JH CA =>
    may_bunt_eval KC ORD FG MG DN KIDS (A 0) csiBody SCC LONG JH CA hbb hmb
  simp [nock_exec, hL, roll.arm_at, roll_arm, hB, hr]

/-! ## `top` -/

/-- `need.s` of a straight: the head of the cell. -/
def topHead : Noun → Noun
  | Noun.cell h _ => h
  | x => x

/-- **`top`**: `(~(run by may) |=(s=straight need.s))` on `[may [order subject]]`, for a map
`may` whose values are cells, is a map with the keys of `may` and the heads of its values. -/
theorem top_gate (p : LoopP) (MAY ORD ML CA : Noun) (hmap : IsMap mugF MAY)
    (hcell : ∀ k v, Get MAY k v → ∃ h t, v = C h t) :
    ∃ TOP, nock (C MAY (C ORD (p.subj ML CA))) csfTop = some TOP ∧ IsMap mugF TOP ∧
      ∀ k w, Get TOP k w ↔ ∃ v, Get MAY k v ∧ w = topHead v := by
  have hf : ∀ x, (∃ h t, x = C h t) → ∀ fc : Noun,
      nock (C (C (A 0) (A 12)) (C x fc)) (C (A 0) (A 12)) = some (topHead x) := by
    rintro x ⟨h, t, rfl⟩ fc; simp [nock_exec, topHead]
  obtain ⟨TOP, hrun, hm, hg⟩ := run_by_P layer2 (C (A 0) (A 12))
    (C (C (A 0x656e6f6e) (A 0)) csfOrdBunt) (C MAY (C ORD (p.subj ML CA)))
    (fun x => ∃ h t, x = C h t) topHead (fun x hx => hf x hx _) hmap hcell
  refine ⟨TOP, ?_, hm, hg⟩
  have hL := compK_layer2
  unfold LoopP.subj LoopP.fg LoopP.mg LoopP.sm LoopP.ctx csiSM csiCtx memCtx csiSam at *
  unfold csfTop
  generalize compK = KC at hL hrun ⊢
  simp [nock_exec, hL, by.arm_at, by_arm, by.run.arm_at, by_run_arm, csfOrdBunt]
  exact hrun

end Compiler
end Formalization
