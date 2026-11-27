import lemmas.Compiler.CompSccLoopSt

/-! # One step of the sweep `+roll` of `+compile-scc-in`, and the sweep (README Gaps 21.11, item 5)

The gate of one sweep step (`csfSwGate`, on the sample `[b st m c]` and the trap core
`LoopP.core`) against `sweepStep`, part by part:

* `sw_any_body`: the test of `+any:in`, `(gte (~(gut by chg.st) k 0) u.r)`;
* `sw_dirty`: `dirty` (`+get:by` of `ran.st`, then `+any:in` over `(~(get ju kids) b)`);
* `sw_keep`: `keep`, `(gth t (mul 4 ~(wyt in scc)))`;
* `sw_mem`: the call of `member` (the hypothesis `MemGate`);
* `sw_st`: the new `st` (`+put:by` of `ran` and of `chg`);
* `csSw_gate`: the gate, against `sweepStep` under `StN` and `R`;
* `sw_roll`: the `+roll` over `order`, against `sweep`. -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {N : Type} [DecidableEq N]

/-- The body of the test of `+any:in` in `dirty`. -/
def swAnyBody : Noun :=
  (C (A 8) (C (C (A 9) (C (A 38) (C (A 0) (A 0x7ffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3ffffffff)))) (C (A 9) (C (A 1531) (C (A 10) (C (C (A 6) (C (A 0) (A 4055))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))))) (C (A 0) (A 2)))))))))) (C (A 0) (A 61)))) (C (A 0) (A 2))))))))

/-- `dirty`: `+get:by` of `ran.st`, then the `+any:in` with the gate `swAnyBody`. -/
theorem csfSwDirty_eq : csfSwDirty =
    (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffffff)))) (C (A 9) (C (A 764) (C (A 10) (C (C (A 6) (C (A 0) (A 470))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0xffffffff)))) (C (A 9) (C (A 4) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 760) (C (A 0) (A 0xffffffff)))) (C (A 9) (C (A 46) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7ffe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 60))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (A 1) (A 0)) (C (A 0) (A 0)))) (C (C (A 1) swAnyBody) (C (A 0) (A 1)))))))) (C (A 0) (A 2))))))))))))) := rfl

/-- The subject of the gate body of one sweep step: the gate, the sample `[b st m c]`, the trap
core. -/
def csSwG (p : LoopP) (CNT ST0 ML0 CA0 b ST ML CA : Noun) : Noun :=
  C csfSwGate (C (C b (C ST (C ML CA))) (p.core CNT ST0 ML0 CA0))

theorem tickOpt_cases (o : Option Nat) : tickOpt o = A 0 ∨ ∃ v, tickOpt o = C (A 0) v := by
  cases o <;> simp [tickOpt]

/-- **The test of `+any:in` in `dirty`**: `(gte (~(gut by chg.st) k 0) u.r)`. -/
theorem sw_any_body (p : LoopP) (CNT ST0 ML0 CA0 b ML CA ANY TK RAN CHG : Noun) (r : Nat)
    (f : Noun → Option Nat) (hchg : TickMap f CHG) (k : Noun) :
    nock (C swAnyBody (C k (C (C (A 0) (A r))
        (csSwG p CNT ST0 ML0 CA0 b (C ANY (C TK (C RAN CHG))) ML CA)))) swAnyBody
      = some (loob (decide (r ≤ (f k).getD 0))) := by
  have hL := compK_layer2
  have hL1 := compK_layer1
  have hgte := gte_gate layer1 arith_layer1.2.2.2.1 ((f k).getD 0) r
  have hc : FallIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
    ⟨fall.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
  have hv : nock (C by.gut.battery (C (C k (A 0)) (C by.battery (C CHG layer2)))) by.gut.battery
      = some (A ((f k).getD 0)) := by
    have hg := tickMap_get hchg k
    rcases e : f k with _ | t <;> rw [e] at hg <;> simp only [tickOpt] at hg
    · simpa using gut_gate layer2 hc k (A 0) CHG (A 0) hg (Or.inl rfl)
    · simpa using gut_gate layer2 hc k (A 0) CHG _ hg (Or.inr ⟨_, rfl⟩)
  unfold csSwG LoopP.core csfCore LoopP.subj
  generalize compK = KC at hL hL1 ⊢
  simp [nock_exec, swAnyBody, hL, hL1, gte.arm_at, gte_arm, hgte, by.arm_at, by_arm,
    by.gut.arm_at, gut_arm, hv]

theorem any_congr_mem {l l' : List Noun} (g : Noun → Bool) (h : ∀ k, k ∈ l ↔ k ∈ l') :
    l.any g = l'.any g := by
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true]
  exact ⟨fun ⟨x, hx, hg⟩ => ⟨x, (h x).1 hx, hg⟩, fun ⟨x, hx, hg⟩ => ⟨x, (h x).2 hx, hg⟩⟩

/-- **`dirty`**: `?~  r=(~(get by ran.st) b)  &`, then `+any:in` over `(~(get ju kids) b)`. -/
theorem sw_dirty (c : Cfg Noun N) (p : LoopP) (hkids : KidsN c p.KIDS)
    (CNT ST0 ML0 CA0 : Noun) (st : St Noun N) (b ST ML CA : Noun) (hb : b ∈ c.scc)
    (hst : StN st ST) :
    nock (csSwG p CNT ST0 ML0 CA0 b ST ML CA) csfSwDirty = some (loob (dirty c st b)) := by
  obtain ⟨RAN, CHG, rfl, hran, hchg⟩ := hst
  obtain ⟨out, hout, htree, hmem⟩ := hkids b hb
  have hL := compK_layer2
  have hget := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ b RAN _
    (tickMap_get hran b)
  have hju := ju_get_gate layer2 juIn_layer2 ju.battery b p.KIDS out hout
  rw [csfSwDirty_eq]
  rcases e : st.ran b with _ | r
  · rw [e] at hget
    have hd : dirty c st b = true := by simp [dirty, e]
    rw [hd]
    unfold csSwG LoopP.core csfCore LoopP.subj at *
    generalize compK = KC at hL ⊢
    simp [nock_exec, hL, by.arm_at, by_arm, by.get.arm_at, get_arm, hget, tickOpt, loob]
  · rw [e] at hget
    have hany := any_in_gate_on in.battery layer2 swAnyBody (C (C (A 1) (A 0)) (C (A 0) (A 0)))
      (C (C (A 0) (A r)) (csSwG p CNT ST0 ML0 CA0 b (C (loob st.any) (C (A st.tick) (C RAN CHG))) ML CA))
      (fun k => decide (r ≤ (st.chg k).getD 0)) (unUnit out) htree
      (fun x _ => sw_any_body p CNT ST0 ML0 CA0 b ML CA _ _ RAN CHG r st.chg hchg x)
    have hd : dirty c st b = (preorder (unUnit out)).any (fun k => decide (r ≤ (st.chg k).getD 0)) := by
      simp only [dirty, e]; exact (any_congr_mem _ hmem).symm
    rw [hd]
    unfold csSwG LoopP.core csfCore LoopP.subj at *
    generalize compK = KC at hL hany ⊢
    simp [nock_exec, hL, by.arm_at, by_arm, by.get.arm_at, get_arm, hget, tickOpt,
      in.arm_at, in_arm, in.any.arm_at, any_in_arm, ju.arm_at, ju_arm, ju.get.arm_at, ju_get_arm,
      hju, hany]

/-- **`keep`**: `(gth t (mul 4 ~(wyt in scc)))`, on the subject `[t dirty gate]`. -/
theorem sw_keep (c : Cfg Noun N) (p : LoopP) (hscc : SccN c p.SCC)
    (CNT ST0 ML0 CA0 b ST ML CA D : Noun) (t : Nat) :
    nock (C (A t) (C D (csSwG p CNT ST0 ML0 CA0 b ST ML CA))) csfSwKeep
      = some (loob (decide (4 * c.scc.length < t))) := by
  have hL := compK_layer2
  have hL1 := compK_layer1
  have hw := wyt_loop layer2 (arith_layer1.1 : Below AddIn layer2) in.battery p.SCC hscc.1
  rw [hscc.2.2] at hw
  have hmul := mul_gate layer1 arith_layer1.1 4 c.scc.length
  have hgth := gth_gate layer1 arith_layer1.2.2.2.2.1 t (4 * c.scc.length)
  unfold csSwG LoopP.core csfCore LoopP.subj
  generalize compK = KC at hL hL1 ⊢
  simp [nock_exec, csfSwKeep, hL, hL1, gth.arm_at, gth_arm, hgth, mul.arm_at, mul_arm, hmul,
    in.arm_at, in_arm, in.wyt.arm_at, wyt_arm, hw]

/-- **The call of `member`** on `[b %must keep m top c]`, with `keep` of `sw_keep`. -/
theorem sw_mem (c : Cfg Noun N) (R : (Noun → Option N) → (Noun → Option N) → Noun → Noun → Prop)
    (p : LoopP) (top : Noun → N)
    (hm : MemGate c R p.ctx top p.TOP Mode.must (A 0x7473756d)) (hscc : SccN c p.SCC)
    (CNT ST0 ML0 CA0 : Noun) (st : St Noun N) (b ST ML CA D : Noun) (t : Nat) (hb : b ∈ c.scc)
    (hR : R st.ml st.sure ML CA) :
    ∃ ML' CA', nock (C (A t) (C D (csSwG p CNT ST0 ML0 CA0 b ST ML CA))) csfSwMem
        = some (C (loob (member c top b Mode.must (decide (4 * c.scc.length < t)) st).1)
            (C ML' CA')) ∧
      R (member c top b Mode.must (decide (4 * c.scc.length < t)) st).2.ml
        (member c top b Mode.must (decide (4 * c.scc.length < t)) st).2.sure ML' CA' := by
  obtain ⟨ML', CA', hcall, hR'⟩ := hm st (decide (4 * c.scc.length < t)) b ML CA hb hR
  refine ⟨ML', CA', ?_, hR'⟩
  have hk := sw_keep c p hscc CNT ST0 ML0 CA0 b ST ML CA D t
  unfold memSam at hcall
  unfold csSwG LoopP.core csfCore LoopP.subj LoopP.mg at *
  simp [nock_exec, csfSwMem, hk, hcall]

/-- **The new `st`**: `[& t (~(put by ran.st) b t) ?:(chg.r (~(put by chg.st) b t) chg.st)]`,
on the subject `[r t dirty gate]`. -/
theorem sw_st (p : LoopP) (CNT ST0 ML0 CA0 b ML CA D ML' CA' ANY TK RAN CHG : Noun)
    (ran chg : Noun → Option Nat) (hran : TickMap ran RAN) (hchg : TickMap chg CHG) (t : Nat)
    (ch : Bool) :
    ∃ RAN' CHG', nock (C (C (loob ch) (C ML' CA')) (C (A t) (C D
        (csSwG p CNT ST0 ML0 CA0 b (C ANY (C TK (C RAN CHG))) ML CA)))) csfSwSt
        = some (C (A 0) (C (A t) (C RAN' CHG'))) ∧
      TickMap (upd ran b (some t)) RAN' ∧ TickMap (if ch then upd chg b (some t) else chg) CHG' := by
  obtain ⟨RAN', hp1, hran'⟩ := tickMap_put hran b t
  obtain ⟨CHG1, hp2, hchg1⟩ := tickMap_put hchg b t
  have hg1 := put_gate layer2 gorIn_morIn_layer2 b (A t) RAN RAN' hp1
  have hg2 := put_gate layer2 gorIn_morIn_layer2 b (A t) CHG CHG1 hp2
  have hL := compK_layer2
  unfold csSwG LoopP.core csfCore LoopP.subj
  generalize compK = KC at hL ⊢
  cases ch
  · refine ⟨RAN', CHG, ?_, hran', by simpa using hchg⟩
    simp [nock_exec, csfSwSt, hL, by.arm_at, by_arm, by.put.arm_at, put_arm, hg1, loob]
  · refine ⟨RAN', CHG1, ?_, hran', by simpa using hchg1⟩
    simp [nock_exec, csfSwSt, hL, by.arm_at, by_arm, by.put.arm_at, put_arm, hg1, hg2, loob]

theorem member_ran (c : Cfg Noun N) (top : Noun → N) (b : Noun) (m : Mode) (keep : Bool)
    (st : St Noun N) : (member c top b m keep st).2.ran = st.ran := rfl

theorem member_chg (c : Cfg Noun N) (top : Noun → N) (b : Noun) (m : Mode) (keep : Bool)
    (st : St Noun N) : (member c top b m keep st).2.chg = st.chg := rfl

/-- **One sweep step**: the gate on `[b st m c]` and the trap core returns the nouns of
`sweepStep c top st b`. -/
theorem csSw_gate (c : Cfg Noun N) (R : (Noun → Option N) → (Noun → Option N) → Noun → Noun → Prop)
    (p : LoopP) (top : Noun → N)
    (hm : MemGate c R p.ctx top p.TOP Mode.must (A 0x7473756d))
    (hkids : KidsN c p.KIDS) (hscc : SccN c p.SCC)
    (CNT ST0 ML0 CA0 : Noun) (st : St Noun N) (b ST ML CA : Noun) (hb : b ∈ c.scc)
    (hst : StN st ST) (hR : R st.ml st.sure ML CA) :
    ∃ ST' ML' CA', nock (C csfSwGate (C (C b (C ST (C ML CA))) (p.core CNT ST0 ML0 CA0))) csfSwGate
        = some (C ST' (C ML' CA')) ∧ StN (sweepStep c top st b) ST' ∧
      R (sweepStep c top st b).ml (sweepStep c top st b).sure ML' CA' := by
  have hd := sw_dirty c p hkids CNT ST0 ML0 CA0 st b ST ML CA hb hst
  unfold csSwG at hd
  have hgate : ∀ X, nock X csfSwGate =
      nock X (C (A 8) (C csfSwDirty (C (A 6) (C (C (A 0) (A 2)) (C csfSwYes csfSwNo))))) :=
    fun X => by rw [csfSwGate_eq]
  have lt : loob true = A 0 := rfl
  have lf : loob false = A 1 := rfl
  by_cases hdy : dirty c st b = true
  · rw [hdy] at hd
    obtain ⟨RAN, CHG, rfl, hran, hchg⟩ := hst
    obtain ⟨ML', CA', hmem, hR'⟩ := sw_mem c R p top hm hscc CNT ST0 ML0 CA0 st b
      (C (loob st.any) (C (A st.tick) (C RAN CHG))) ML CA (A 0) (st.tick + 1) hb hR
    obtain ⟨RAN', CHG', hst', hran', hchg'⟩ := sw_st p CNT ST0 ML0 CA0 b ML CA (A 0) ML' CA'
      (loob st.any) (A st.tick) RAN CHG st.ran st.chg hran hchg (st.tick + 1)
      (member c top b Mode.must (decide (4 * c.scc.length < st.tick + 1)) st).1
    have e1 : (sweepStep c top st b).any = true := by unfold sweepStep; rw [if_pos hdy]
    have e2 : (sweepStep c top st b).tick = st.tick + 1 := by unfold sweepStep; rw [if_pos hdy]
    have e3 : (sweepStep c top st b).ran = upd st.ran b (some (st.tick + 1)) := by
      unfold sweepStep; rw [if_pos hdy]; rfl
    have e4 : (sweepStep c top st b).chg =
        (if (member c top b Mode.must (decide (4 * c.scc.length < st.tick + 1)) st).1
          then upd st.chg b (some (st.tick + 1)) else st.chg) := by
      unfold sweepStep; rw [if_pos hdy]; rfl
    have e5 : (sweepStep c top st b).ml =
        (member c top b Mode.must (decide (4 * c.scc.length < st.tick + 1)) st).2.ml := by
      unfold sweepStep; rw [if_pos hdy]
    have e6 : (sweepStep c top st b).sure =
        (member c top b Mode.must (decide (4 * c.scc.length < st.tick + 1)) st).2.sure := by
      unfold sweepStep; rw [if_pos hdy]
    refine ⟨C (A 0) (C (A (st.tick + 1)) (C RAN' CHG')), ML', CA', ?_, ?_, ?_⟩
    · rw [hgate]
      unfold csSwG at hmem hst'
      obtain ⟨x, y, hxy⟩ : ∃ x y, csfSwSt = C x y := ⟨_, _, rfl⟩
      rw [hxy] at hst'
      simp [nock_exec, csfSwYes, csfSwOut, lt, hd, hmem, hxy, hst']
    · refine ⟨RAN', CHG', ?_, ?_, ?_⟩
      · simp [e1, e2, loob]
      · rw [e3]; exact hran'
      · rw [e4]; exact hchg'
    · rw [e5, e6]; exact hR'
  · have hdf : dirty c st b = false := by simpa using hdy
    rw [hdf] at hd
    have hs : sweepStep c top st b = st := by unfold sweepStep; rw [if_neg hdy]
    rw [hs]
    refine ⟨ST, ML, CA, ?_, hst, hR⟩
    rw [hgate]
    generalize csfSwDirty = DF at hd ⊢
    generalize csfSwYes = YF
    simp [nock_exec, csfSwNo, lf, hd]

/-- The sweep `+roll` from a state: the fold of the gate of one step over a list of members. -/
theorem sw_fold (c : Cfg Noun N) (R : (Noun → Option N) → (Noun → Option N) → Noun → Noun → Prop)
    (p : LoopP) (top : Noun → N)
    (hm : MemGate c R p.ctx top p.TOP Mode.must (A 0x7473756d))
    (hkids : KidsN c p.KIDS) (hscc : SccN c p.SCC) (CNT ST0 ML0 CA0 : Noun) :
    ∀ (l : List Noun), (∀ b ∈ l, b ∈ c.scc) → ∀ (st : St Noun N) (ST ML CA : Noun),
      StN st ST → R st.ml st.sure ML CA →
      ∃ ST' ML' CA', l.foldlM (fun acc x => nock (C csfSwGate (C (C x acc)
            (p.core CNT ST0 ML0 CA0))) csfSwGate) (C ST (C ML CA)) = some (C ST' (C ML' CA')) ∧
        StN (l.foldl (sweepStep c top) st) ST' ∧
        R (l.foldl (sweepStep c top) st).ml (l.foldl (sweepStep c top) st).sure ML' CA' := by
  intro l
  induction l with
  | nil => intro _ st ST ML CA hst hR; exact ⟨ST, ML, CA, rfl, hst, hR⟩
  | cons b l ih =>
    intro hl st ST ML CA hst hR
    obtain ⟨ST1, ML1, CA1, h1, hst1, hR1⟩ :=
      csSw_gate c R p top hm hkids hscc CNT ST0 ML0 CA0 st b ST ML CA (hl b (by simp)) hst hR
    obtain ⟨ST', ML', CA', h2, hst', hR'⟩ :=
      ih (fun x hx => hl x (by simp [hx])) _ ST1 ML1 CA1 hst1 hR1
    refine ⟨ST', ML', CA', ?_, hst', hR'⟩
    simp only [List.foldlM_cons, h1]
    exact h2

/-- **The sweep**: `csfSwRoll` on the trap core returns the nouns of `sweep c top st`. -/
theorem sw_roll (c : Cfg Noun N) (R : (Noun → Option N) → (Noun → Option N) → Noun → Noun → Prop)
    (p : LoopP) (top : Noun → N)
    (hm : MemGate c R p.ctx top p.TOP Mode.must (A 0x7473756d))
    (hkids : KidsN c p.KIDS) (hscc : SccN c p.SCC)
    (hord : p.ORD = listN c.order) (hsub : ∀ b ∈ c.order, b ∈ c.scc)
    (CNT : Noun) (st : St Noun N) (ST ML CA : Noun) (hst : StN st ST) (hR : R st.ml st.sure ML CA) :
    ∃ ST' ML' CA', nock (p.core CNT ST ML CA) csfSwRoll = some (C ST' (C ML' CA')) ∧
      StN (sweep c top st) ST' ∧ R (sweep c top st).ml (sweep c top st).sure ML' CA' := by
  obtain ⟨ST', ML', CA', hf, hst', hR'⟩ :=
    sw_fold c R p top hm hkids hscc CNT ST ML CA c.order hsub st ST ML CA hst hR
  refine ⟨ST', ML', CA', ?_, hst', hR'⟩
  have hL := compK_layer2
  have hbb := bell_bunt
  have hr := roll_gate_M layer2 csfSwGate bellBunt (C ST (C ML CA)) (p.core CNT ST ML CA)
    (fun x acc => nock (C csfSwGate (C (C x acc) (p.core CNT ST ML CA))) csfSwGate) c.order
    (fun _ _ _ => rfl)
  rw [hf] at hr
  rw [csfSwRoll_eq]
  generalize csfSwGate = GF at hr ⊢
  unfold LoopP.core csfCore LoopP.subj at *
  rw [hord] at hr ⊢
  generalize compK = KC at hL hbb hr ⊢
  unfold bellBuntF at hbb
  simp only [nock_exec] at hbb
  simp [nock_exec, hL, roll.arm_at, roll_arm, csfSwBunt, hbb, hr]

end Compiler
end Formalization
