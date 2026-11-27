import lemmas.Compiler.CompSccLoopStep
import lemmas.Compiler.CompSccLoopFin

/-! # The loop of `+compile-scc-in` in the pill: the induction on the fuel (README Gaps 21.11)

* `csf_rec`: the print and the `%=  sweep-loop` (`csfRec`) is the trap on the core with
  `counter` incremented, `st` the sweep's with `any` cleared, `map-local` and `cache` the
  sweep's (`PrintId`: the print gate gives back its sample).
* `trap_loop`: wherever the model's `loop c top n st` returns `s` (from `any` false), the trap
  of the sweeps on the nouns of `st` returns `final c true s`: `[ML' cache']` with `R` of the
  final pass, `nary` of the last member run's cache united with `ML'`.
* `csf_fix_loop`: `csiFix` (the DFS, the `%may` sweep, `top`, the trap) against `compileSccIn c
  false`, with the DFS and `top` as hypotheses on their products.
* `csi_gate_loop`: the gate `+compile-scc-in` on a cache miss with `done` false. -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {N : Type} [DecidableEq N]

/-! ## `csfRec` -/

/-- **The print and the `%=  sweep-loop`**: on `[res core]` with `res = [[ANY TK RN CG] ML' CA']`,
`csfRec` is the trap on the core with `counter` `k + 1`, `st` `[| TK RN CG]`, `map-local` `ML'`
and `cache` `CA'`. -/
theorem csf_rec (p : LoopP) (hpr : PrintId p) (k : Nat) (ST ML CA ANY TK RN CG ML' CA' : Noun) :
    nock (C (C (C ANY (C TK (C RN CG))) (C ML' CA')) (p.core (A k) ST ML CA)) csfRec
      = nock (p.core (A (k + 1)) (C (A 1) (C TK (C RN CG))) ML' CA') csfTrap := by
  obtain ⟨BAT, SAM, CTX, hp, hid⟩ := hpr k ST ML CA (C (C ANY (C TK (C RN CG))) (C ML' CA'))
  have hrec : ∀ X, nock X csfRec = nock X (C (A 8) (C csfRecPrint (C (A 9) (C (A 2) (C (A 10)
      (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) csfRecCall))) (C (A 0) (A 2)))))))) := by
    intro X; rw [csfRec_eq]
  rw [hrec]
  have hcall : nock (C (C (C ANY (C TK (C RN CG))) (C ML' CA')) (p.core (A k) ST ML CA)) csfRecCall
      = nock (p.core (A (k + 1)) (C (A 1) (C TK (C RN CG))) ML' CA') csfTrap := by
    unfold csfRecCall LoopP.core csfCore LoopP.subj csiSam
    simp [nock_exec]
  cases e : nock (p.core (A (k + 1)) (C (A 1) (C TK (C RN CG))) ML' CA') csfTrap with
  | none =>
    rw [e] at hcall
    simp [nock_exec, hp, hcall]
  | some x =>
    rw [e] at hcall
    simp [nock_exec, hp, hcall, hid]

/-- `csfFin` on `[res core]` is `final` on `[& map-local cache]` of the core. -/
theorem csf_fin (p : LoopP) (CNT ST ML CA RES : Noun) :
    nock (C RES (p.core CNT ST ML CA)) csfFin
      = nock (C fBody (C (C (A 0) (C ML CA)) p.sm)) fBody := by
  unfold csfFin LoopP.core csfCore LoopP.subj LoopP.fg
  simp [nock_exec]

/-! ## The model side -/

/-- `member` reads only `ml` and `sure` of the state for its new `ml` and `sure`. -/
theorem member_congr (c : Cfg Noun N) (top : Noun → N) (b : Noun) (m : Mode) (keep : Bool)
    (s t : St Noun N) (h1 : s.ml = t.ml) (h2 : s.sure = t.sure) :
    (member c top b m keep s).2.ml = (member c top b m keep t).2.ml ∧
      (member c top b m keep s).2.sure = (member c top b m keep t).2.sure := by
  obtain ⟨ml, sure, _, _, _, _, _, _, _⟩ := s
  obtain ⟨ml', sure', _, _, _, _, _, _, _⟩ := t
  simp only at h1 h2
  subst h1 h2
  exact ⟨rfl, rfl⟩

/-- So does the final pass. -/
theorem final_congr (c : Cfg Noun N) (keep : Bool) (s t : St Noun N) (h1 : s.ml = t.ml)
    (h2 : s.sure = t.sure) :
    (final c keep s).ml = (final c keep t).ml ∧ (final c keep s).sure = (final c keep t).sure := by
  unfold final
  generalize c.scc = l
  induction l generalizing s t with
  | nil => exact ⟨h1, h2⟩
  | cons b l ih =>
    simp only [List.foldl_cons]
    obtain ⟨e1, e2⟩ := member_congr c (fun _ => c.none) b Mode.done keep s t h1 h2
    exact ih _ _ e1 e2

/-! ## The induction -/

/-- **The trap of the sweeps against `loop`**: from a state with `any` false whose nouns are
`ST` (`StN`), `ML`, `CA` (`R`), wherever `loop c top n st` returns `s`, the trap on the core
returns `[ML' [NARYU REST]]`, where `R` relates `final c true s` to `ML'` and the cache
`[NARY REST]` of the last member run of the final pass, and `NARYU` is `(~(uni by NARY) ML')`. -/
theorem trap_loop (c : Cfg Noun N) (R : (Noun → Option N) → (Noun → Option N) → Noun → Noun → Prop)
    (p : LoopP) (top : Noun → N)
    (hmust : MemGate c R p.ctx top p.TOP Mode.must (A 0x7473756d))
    (hdone : MemGate c R p.ctx (fun _ => c.none) (A 0) Mode.done (A 0x656e6f64))
    (hkids : KidsN c p.KIDS) (hscc : SccN c p.SCC)
    (hord : p.ORD = listN c.order) (hsub : ∀ b ∈ c.order, b ∈ c.scc) (hpr : PrintId p) :
    ∀ (n : Nat) (st s : St Noun N) (k : Nat) (ST ML CA : Noun), st.any = false →
      loop c top n st = some s → StN st ST → R st.ml st.sure ML CA →
      ∃ ML' CA', R (final c true s).ml (final c true s).sure ML' CA' ∧
        ∀ NARY REST NARYU, CA' = C NARY REST →
          nock (C by.uni.battery (C ML' (C by.battery (C NARY layer2)))) by.uni.battery = some NARYU →
          nock (p.core (A k) ST ML CA) csfTrap = some (C ML' (C NARYU REST)) := by
  intro n
  induction n with
  | zero => intro st s k ST ML CA _ h; simp [loop] at h
  | succ n ih =>
    intro st s k ST ML CA h0 hl hst hR
    obtain ⟨ST1, ML1, CA1, hsw, hst1, hR1⟩ :=
      sw_roll c R p top hmust hkids hscc hord hsub (A k) st ST ML CA hst hR
    obtain ⟨RAN, CHG, rfl, hran, hchg⟩ := hst1
    simp only [loop] at hl
    cases ha : (sweep c top st).any with
    | true =>
      simp only [ha, if_true] at hl
      have htr := csf_trap_rec (A k) ST (C p.TOP (C p.MAY (C p.ORD (p.subj ML CA))))
        (A (sweep c top st).tick) RAN CHG (C ML1 CA1) (by rw [ha] at hsw; exact hsw)
      obtain ⟨ML', CA', hR', hgo⟩ := ih _ s (k + 1) (C (A 1) (C (A (sweep c top st).tick) (C RAN CHG)))
        ML1 CA1 rfl hl ⟨RAN, CHG, rfl, hran, hchg⟩ hR1
      refine ⟨ML', CA', hR', fun NARY REST NARYU hc hu => ?_⟩
      have e1 : nock (p.core (A k) ST ML CA) csfTrap
          = nock (C (C (C (A 0) (C (A (sweep c top st).tick) (C RAN CHG))) (C ML1 CA1))
              (p.core (A k) ST ML CA)) csfRec := htr
      rw [e1, csf_rec p hpr k ST ML CA (A 0) _ RAN CHG ML1 CA1]
      exact hgo NARY REST NARYU hc hu
    | false =>
      simp only [ha] at hl
      cases hl
      obtain ⟨hsame, _⟩ := foldl_noany c top c.order st h0 ha
      have hsw' : sweep c top st = st := hsame
      obtain ⟨ML', CA', hR', hfin⟩ := fin_scc_gate c R p hdone hscc true st ML CA hR
      refine ⟨ML', CA', ?_, fun NARY REST NARYU hc hu => ?_⟩
      · obtain ⟨e1, e2⟩ := final_congr c true
          { sweep c top st with any := false, sw := (sweep c top st).sw ++ [false] } st
          (show (sweep c top st).ml = st.ml from congrArg St.ml hsw')
          (show (sweep c top st).sure = st.sure from congrArg St.sure hsw')
        rw [e1, e2]; exact hR'
      · have htr := csf_trap_end (A k) ST (C p.TOP (C p.MAY (C p.ORD (p.subj ML CA))))
          (A (sweep c top st).tick) RAN CHG (C ML1 CA1) (by rw [ha] at hsw; exact hsw)
        have e3 : nock (p.core (A k) ST ML CA) csfTrap
            = nock (C (C (C (A 1) (C (A (sweep c top st).tick) (C RAN CHG))) (C ML1 CA1))
                (p.core (A k) ST ML CA)) csfFin := htr
        rw [e3, csf_fin]
        exact hfin NARY REST NARYU hc hu

end Compiler
end Formalization
