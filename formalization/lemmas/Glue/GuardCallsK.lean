import lemmas.Glue.GuardCallsB

/-!
# `+kerf` and the calls over `KPA` with distinct needs (track G, tenth pass)

LEDGER 2.c, toward `GuardMonoC` (`Glue/GuardCallsB.lean`).

* `kpa_kernAdd`: `+kern-need` then `+add-ops` at an `FL` label keeps `InvA`
  when the source is below `re`, not in the need, and the need is distinct
  and below `re` (`kernNeed_guarded`, `kernLoop_raw`).
* `kpa_kernGate`: one gate of `+kern` (`kernGate`): `+sure-require-look`
  keeps the need distinct, its registers are the old ones (below the kern
  register `r`) or fresh; the source is `r` at the kerf block, a fresh proxy
  elsewhere.
* **`kerfG`** (`KerfG`): `+kerf` keeps `InvA` for a `nex` with `FL` labels
  and `DN` entries.
* `kpa_simpleNextLG`, `kpa_monoBlocksG`, `kpa_callTailG`, **`kpa_callDMG`**
  (the direct call with `mono` `&`), **`kpa_callLI`** (the indirect call):
  the ninth pass's proofs with `RunG` sub-runs and `GD` goals.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [Opt.MapKeys Map] [HoonMapKeys Map]

/-! ## One gate of `+kern` -/

/-- **`+kern-need` then `+add-ops` at an `FL` label.** -/
theorem kpa_kernAdd {K0 : Nat → Nat → Prop} {b0 r0 : Nat} (src : Nat) (ned : Need) (oLaz : Nat)
    (ho : FL K0 b0 oLaz) (hs : src < r0) (hn : ¬ NMem ned src) (nb : NB r0 ned) (dn : Distinct ned) :
    KPA K0 b0 r0 (fun _ _ _ _ => True) (kernNeed src ned >>= fun ops => addOps oLaz ops : CM Map Unit) := by
  constructor
  intro K g x g' hI h0 hX e
  obtain ⟨ops, g1, h1, h2⟩ := bind_some e
  have hsg : src < g.re := Nat.lt_of_lt_of_le hs hX.2.1
  have nbg : NB g.re ned := fun y hy => Nat.lt_of_lt_of_le (nb y hy) hX.2.1
  have G := kernNeed_guarded h1 hsg hn nbg dn
  obtain ⟨A, -, KR⟩ := Raw.kernLoop_raw ned src [] g g1 ops h1 hsg hn nbg dn
  have eg := KR.gen
  have hle := KR.le
  have hI1 : InvA K g1 := by rw [eg]; exact ⟨hI.ok, hI.drop, hI.below, hI.kin⟩
  have X1 : XB K g.bo g.re K g1.bo g1.re := by
    refine ⟨?_, hle, fun _ _ _ => Iff.rfl⟩
    rw [eg]; exact Nat.le_refl _
  have h01 : 0 < g1.bo := Nat.lt_of_lt_of_le h0 X1.1
  obtain ⟨K2, hI2, X2, -⟩ := (KPA.addOps' (r0 := r0) G ho).k K g1 () g' hI1 h01 (hX.trans X1) h2
  exact ⟨K2, hI2, X1.trans X2, trivial⟩

/-- `+sure-require-look` of a distinct need below `r`: distinct, its
registers the old ones (below `r`) or fresh. -/
theorem rs_srl (r r0 : Nat) (sur : Sure S) (hr : r < r0) (hd : Distinct sur.ned) (hn : NB r sur.ned) :
    RS r0 (fun r' (ned : Need) => Distinct ned ∧ ∀ y, NMem ned y → (y < r ∨ r0 ≤ y) ∧ y < r')
      (sureRequireLook sur : CM Map Need) := by
  intro g x g' hg e
  have L := sureRequireLook_spec e
  refine ⟨L.dist hd (fun y hy => by have := hn y hy; omega), fun y hy => ?_⟩
  rcases L.mem y hy with h | ⟨h1, h2⟩
  · have := hn y h; have := L.le; omega
  · exact ⟨Or.inr (by omega), h2⟩

/-- `+proxy` returns the old `re`. -/
theorem rs_proxy (r1 r o : Nat) : RS r1 (fun r' (x : Nat) => r1 ≤ x ∧ x < r') (proxy r o : CM Map Nat) := by
  intro g x g' hg e
  unfold proxy at e
  simp only at e
  split at e
  · cases e; exact ⟨hg, Nat.lt_succ_self _⟩
  · obtain ⟨tag, _, e⟩ := Option.map_eq_some_iff.mp e
    cases e; exact ⟨hg, Nat.lt_succ_self _⟩

/-- **One gate of `+kern` keeps `InvA`.** -/
theorem kpa_kernGate {K0 : Nat → Nat → Prop} {b0 r0 : Nat} (r o oLaz : Nat) (sur : Sure S) (hr : r < r0)
    (ho : FL K0 b0 oLaz) (hd : Distinct sur.ned) (hn : NB r sur.ned) :
    KPA K0 b0 r0 (fun _ _ _ _ => True) (kernGate r o oLaz sur : CM Map Unit) := by
  unfold kernGate
  refine KPA.bind' ((KPA.sureRequireLook' sur).andR (rs_srl r r0 sur hr hd hn)) fun ned K1 b1 r1 X1 hned => ?_
  obtain ⟨-, dn, hm⟩ := hned
  refine KPA.ite' _ (fun _ => KPA.pure' fun _ _ _ _ => trivial) fun _ => ?_
  refine KPA.bind' (P := fun _ _ r' src => src < r' ∧ ¬ NMem ned src) ?_ fun src K2 b2 r2 X2 hsrc => ?_
  · split
    · exact KPA.pure' fun K b r' X => ⟨by have := X1.2.1; have := X.2.1; omega, fun hk => by
        have := X1.2.1; rcases (hm r hk).1 with h | h <;> omega⟩
    · refine KPA.mono ((KPA.proxy' r oLaz).andR (rs_proxy r1 r oLaz)) fun K b r' x hx => ⟨hx.2.2, fun hk => ?_⟩
      have := (hm x hk).2; have := hx.2.1; omega
  refine KPA.ite' _ (fun _ => KPA.fail) fun _ => ?_
  exact kpa_kernAdd src ned oLaz (ho.up (X1.trans X2)) hsrc.1 hsrc.2
    (fun y hy => by have := (hm y hy).2; have := X2.2.1; omega) dn

/-! ## `+kern`, `+kerf` -/

/-- **`+kern`** of a lazy with `FL` labels and `DN` entries, at an `FL`
block: the register it returns is below `re`. -/
theorem kpa_kern {K0 : Nat → Nat → Prop} {b0 r0 : Nat} (o : Nat) (laz : Lazy S) (ho : FL K0 b0 o)
    (hl : LzL (FL K0 b0) laz) (hs : LzS (DN r0) laz) :
    KPA K0 b0 r0 (fun _ _ r x => x < r) (kern o laz : CM Map Nat) := by
  rw [kern_eq]
  refine KPA.bind' KPA.re' fun rk K1 b1 r1 X1 hrk => ?_
  refine KPA.bind' KPA.get' fun g K2 b2 r2 X2 _ => ?_
  refine KPA.ite' _ (fun _ => KPA.pure' fun K b r X => lt_up (lt_up hrk.2 X2) X) fun _ => ?_
  have X12 := X1.trans X2
  refine KPA.bind' (kpa_walkLazy (Q := fun r' s => rk < r' ∧ Distinct s.ned ∧ NB rk s.ned)
    (fun _ _ _ h q => ⟨Nat.lt_of_lt_of_le q.1 h, q.2⟩)
    (fun K0' b0' r0' o' s ho' hq => kpa_kernGate rk o o' s hq.1 ho' hq.2.1 hq.2.2) o laz (ho.up X12) (hl.up X12)
    (hs.imp fun s h => ⟨lt_up hrk.2 X2, h.1, fun y hy => Nat.lt_of_lt_of_le (h.2 y hy) hrk.1⟩))
    fun _ K3 b3 r3 X3 _ => ?_
  exact KPA.pure' fun K b r X => lt_up (lt_up (lt_up hrk.2 X2) X3) X

/-- **`+kerf` in the middle of a run** keeps `InvA`, for a `nex` with `FL`
labels and `DN` entries. -/
theorem kerfG : KerfG S Map := by
  intro K0 b0 r0 nex hth hj hl hs
  unfold kerf
  refine KPA.bind' (KPA.emit' (blockOK_nil _ _ (by simpa [getJmps] using hj)) (by simpa [getJmps] using hth))
    fun o K1 b1 r1 X1 ho => ?_
  refine KPA.bind' (kpa_kern o nex.laz ho (hl.up X1) (LzS.upD hs X1.2.1)) fun rk K2 b2 r2 X2 hrk => ?_
  exact KPA.pure' fun K b r X => ⟨(ho.up X2).up X, lt_up hrk X⟩

/-! ## The call blocks -/

/-- **`+simple-next`** under a goal with `FL` jumps and `DN` entries. -/
theorem kpa_simpleNextLG {K0 : Nat → Nat → Prop} {b0 r0 : Nat} {goal : CGoalL S} (hg : GFL K0 b0 goal)
    (hd : GD r0 goal) :
    KPA K0 b0 r0 (fun K bo r (n : NextL S) => FL K bo n.th.there ∧ JOK n.th ∧ LzL (FL K bo) n.laz ∧
      LzS (DN r) n.laz) (simpleNextL goal : CM Map (NextL S)) := by
  cases goal with
  | next laz th => exact KPA.pure' fun K b r X => ⟨hg.1.up X, hg.2.1, hg.2.2.up X, LzS.upD hd X.2.1⟩
  | done =>
    refine KPA.bind' KPA.re' fun r K1 b1 r1 X1 hr => KPA.bind' (KPA.emit' (blockOK_nil _ _ (by simp [getJmps]))
      (by simp [getJmps])) fun o K2 b2 r2 X2 ho => KPA.pure' fun K b r' X =>
        ⟨ho.up X, jok_jmp0 _, lzL_ofSure _ _, lzS_ofSure (dn_this (lt_up (lt_up hr.2 X2) X))⟩
  | pick z o =>
    refine KPA.bind' KPA.re' fun r K1 b1 r1 X1 hr => KPA.bind' (KPA.emit' (blockOK_nil _ _ ?_) ?_)
      fun o' K2 b2 r2 X2 ho => KPA.pure' fun K b r' X =>
        ⟨ho.up X, jok_jmp0 _, lzL_ofSure _ _, lzS_ofSure (dn_this (lt_up (lt_up hr.2 X2) X))⟩
    · intro j hj; simp only [getJmps, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact hg.2.1
      · exact hg.2.2.2
    · intro j hj; simp only [getJmps, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact hg.1.up X1
      · exact hg.2.2.1.up X1

/-- **The call blocks of the direct call keep `InvA`**, with `+kerf` under
`KerfG`; the register `sub-pes` is below `re`. -/
theorem kpa_monoBlocksG (hk : KerfG S Map) {K0 : Nat → Nat → Prop} {b0 r0 : Nat} (bl : Bell) (subNed : Need)
    {goal : CGoalL S} (hg : GFL K0 b0 goal) (hd : GD r0 goal) :
    KPA K0 b0 r0 (fun K bo r (x : Nat × Nat) => FL K bo x.2 ∧ x.1 < r)
      (monoBlocks bl subNed goal : CM Map (Nat × Nat)) := by
  have hdone : KPA K0 b0 r0 (fun K bo r (x : Nat × Nat) => FL K bo x.2 ∧ x.1 < r)
      (do
        let subPes ← re
        let opt ← emit ⟨[], [], Termin.jmp bl (flattenNeed subNed)⟩
        let pes ← emit ⟨[], [], Termin.jsp bl subPes⟩
        let o ← monoTryCall subNed opt subPes pes
        pure (subPes, o) : CM Map (Nat × Nat)) := by
    refine KPA.bind' KPA.re' fun sp K1 b1 r1 X1 hsp => ?_
    refine KPA.bind' (KPA.emit' (blockOK_nil _ _ (by simp [getJmps])) (by simp [getJmps])) fun opt K2 b2 r2 X2 hopt => ?_
    refine KPA.bind' (KPA.emit' (blockOK_nil _ _ (by simp [getJmps])) (by simp [getJmps])) fun pes K3 b3 r3 X3 hpes => ?_
    refine KPA.bind' (KPA.mtc (lt_up (lt_up hsp.2 X2) X3) (hopt.up X3) hpes) fun o K4 b4 r4 X4 ho => ?_
    exact KPA.pure' fun K b r X => ⟨ho.up X, lt_up (lt_up (lt_up (lt_up hsp.2 X2) X3) X4) X⟩
  have hrest : ∀ g : CGoalL S, GFL K0 b0 g → GD r0 g →
      KPA K0 b0 r0 (fun K bo r (x : Nat × Nat) => FL K bo x.2 ∧ x.1 < r) (do
        let nex ← simpleNextL g
        let (out, pro) ← kerf nex
        let merged ← re
        let subPes ← re
        let merge ← emit ⟨[merged], [Pole.mov merged pro], Termin.hop (jmp0 out)⟩
        let proOpt ← re
        let proPes ← re
        let opt ← emit ⟨[], [Pole.cal bl (flattenNeed subNed) proOpt], Termin.hop ⟨[some proOpt], merge⟩⟩
        let pes ← emit ⟨[], [Pole.csl bl subPes proPes], Termin.hop ⟨[some proPes], merge⟩⟩
        let o ← monoTryCall subNed opt subPes pes
        pure (subPes, o) : CM Map (Nat × Nat)) := by
    intro g hg hd
    refine KPA.bind' (kpa_simpleNextLG hg hd) fun nex K1 b1 r1 X1 hn => ?_
    refine KPA.bind' (hk K1 b1 r1 nex hn.1 hn.2.1 hn.2.2.1 hn.2.2.2) fun op K2 b2 r2 X2 hop => ?_
    rcases op with ⟨out, pro⟩
    refine KPA.bind' KPA.re' fun merged K3 b3 r3 X3 hm => ?_
    refine KPA.bind' KPA.re' fun sp K4 b4 r4 X4 hsp => ?_
    refine KPA.bind' (KPA.emit' (blockOK_one _ _ _ rfl (by simp [getJmps, jok_jmp0])) ?_)
      fun merge K5 b5 r5 X5 hmerge => ?_
    · intro j hj; simp only [getJmps, List.mem_singleton] at hj; subst hj; exact (hop.1.up X3).up X4
    refine KPA.bind' KPA.re' fun po K6 b6 r6 X6 _ => ?_
    refine KPA.bind' KPA.re' fun pp K7 b7 r7 X7 _ => ?_
    refine KPA.bind' (KPA.emit' (blockOK_one _ _ _ rfl (by simp [getJmps, JOK])) ?_) fun opt K8 b8 r8 X8 hopt => ?_
    · intro j hj; simp only [getJmps, List.mem_singleton] at hj; subst hj; exact (hmerge.up X6).up X7
    refine KPA.bind' (KPA.emit' (blockOK_one _ _ _ rfl (by simp [getJmps, JOK])) ?_) fun pes K9 b9 r9 X9 hpes => ?_
    · intro j hj; simp only [getJmps, List.mem_singleton] at hj; subst hj; exact ((hmerge.up X6).up X7).up X8
    have hspl : sp < r9 := lt_up (lt_up (lt_up (lt_up (lt_up hsp.2 X5) X6) X7) X8) X9
    refine KPA.bind' (KPA.mtc hspl (hopt.up X9) hpes) fun o K10 b10 r10 X10 ho => ?_
    exact KPA.pure' fun K b r X => ⟨ho.up X, lt_up (lt_up hspl X10) X⟩
  unfold monoBlocks
  cases goal with
  | done => exact hdone
  | next laz th => exact hrest _ hg hd
  | pick z o => exact hrest _ hg hd

/-! ## The direct call -/

/-- The tail of the direct call, with `RunG` parts. -/
theorem kpa_callTailG {K0 : Nat → Nat → Prop} {b0 r0 : Nat} (cod : Bell → Option Bool)
    {rp rq : CGoalL S → List Nat → CM Map (NextL S)} (hp : RunG rp) (hq : RunG rq) (p q : Nomm) (region : List Nat)
    (laz : Lazy S) (th : Jmp) (hth : FL K0 b0 th.there) (hj : JOK th) (hl : LzL (FL K0 b0) laz)
    (hd : LzS (DN r0) laz) :
    KPA K0 b0 r0 RN (do
      let nexFol ← (if safeFolFol q then pure ⟨ofSure Sure.bunt, th⟩
        else rq (CGoalL.next (ofSure Sure.bunt) th) region : CM Map (NextL S))
      let nexFol ← pastL cod nexFol p region
      let nexSub ← rp (CGoalL.next laz nexFol.th) region
      copyL nexSub nexFol.laz : CM Map (NextL S)) := by
  refine KPA.bind' (P := RN) ?_ fun n1 K1 bb1 r1 X1 h1 => ?_
  · split
    · exact KPA.pure' fun K b r X => ⟨hth.up X, hj, lzL_ofSure _ _⟩
    · exact hq _ _ _ _ _ (gfl_next hth hj (lzL_ofSure _ _)) (lzS_bunt _)
  refine KPA.bind' (kpa_pastL cod h1 p region) fun n2 K2 bb2 r2 X2 h2 => ?_
  refine KPA.bind' (hp _ _ _ _ _ (gfl_next h2.1 h2.2.1 (hl.up (X1.trans X2))) (LzS.upD hd (X1.trans X2).2.1))
    fun n3 K3 bb3 r3 X3 h3 => ?_
  exact kpa_copyL h3 (h2.2.2.up X3)

/-- **The direct call with `mono` `&` keeps `InvA`**, with `RunG` parts
and `KerfG`. -/
theorem kpa_callDMG (hk : KerfG S Map) (env : CallEnv) {rp rq : CGoalL S → List Nat → CM Map (NextL S)}
    (hp : RunG rp) (hq : RunG rq) (p q : Nomm) (bl : Bell) (key : Option Noun) {K0 : Nat → Nat → Prop} {b0 r0 : Nat}
    {goal : CGoalL S} (hg : GFL K0 b0 goal) (hd : GD r0 goal) (region : List Nat) :
    KPA K0 b0 r0 RN (callDM env rp rq p q bl key goal region : CM Map (NextL S)) := by
  have hnone : KPA K0 b0 r0 RN (match key, env.ring bl, env.need bl with
      | Option.none, Option.none, some bNed => do
        let subNed ← needOrdAllocRegs bNed
        let (subPes, callBlock) ← monoBlocks bl subNed goal
        let nexArg : NextL S := ⟨ofSure (lazyReg subPes), jmp0 callBlock⟩
        let nexFol ← (if safeFolFol q then pure ⟨ofSure Sure.bunt, nexArg.th⟩
          else rq (CGoalL.next (ofSure Sure.bunt) nexArg.th) region : CM Map (NextL S))
        let nexFol ← pastL env.cod nexFol p region
        let nexSub ← rp (CGoalL.next nexArg.laz nexFol.th) region
        copyL nexSub nexFol.laz
      | _, _, _ => fun _ => Option.none : CM Map (NextL S)) := by
    split
    · refine KPA.bind' (kpa_needOrd _) fun subNed K1 bb1 r1 X1 _ => ?_
      refine KPA.bind' (kpa_monoBlocksG hk bl subNed (hg.up X1) (hd.up X1.2.1)) fun x K2 bb2 r2 X2 hx => ?_
      rcases x with ⟨sp, cb⟩
      exact kpa_callTailG env.cod hp hq p q region _ (jmp0 cb) hx.1 (jok_jmp0 _) (lzL_ofSure _ _) (lzS_reg hx.2)
    · exact KPA.fail
  unfold callDM
  cases goal with
  | next laz th =>
    by_cases hc : (env.pure bl && noneEquivalentL laz) = true
    · simp only [hc, ↓reduceIte]
      exact kpa_callTailG env.cod hp hq p q region _ th hg.1 hg.2.1 (lzL_ofSure _ _) (lzS_bunt _)
    · simp only [hc, ↓reduceIte, Bool.false_eq_true]
      exact hnone
  | pick z o => exact hnone
  | done => exact hnone

/-! ## The indirect call -/

/-- **The indirect call keeps `InvA`**, with `RunG` parts and `KerfG`. -/
theorem kpa_callLI (hk : KerfG S Map) (env : CallEnv) {rp rq : CGoalL S → List Nat → CM Map (NextL S)}
    (hp : RunG rp) (hq : RunG rq) (p q : Nomm) (sup : Option Nomm) {K0 : Nat → Nat → Prop} {b0 r0 : Nat}
    {goal : CGoalL S} (hg : GFL K0 b0 goal) (hd : GD r0 goal) (region : List Nat) :
    KPA K0 b0 r0 RN (callL env rp rq p q Option.none sup goal region : CM Map (NextL S)) := by
  unfold callL
  refine KPA.bind' (kpa_simpleNextLG hg hd) fun nex K1 b1 r1 X1 hn => ?_
  refine KPA.bind' (hk K1 b1 r1 nex hn.1 hn.2.1 hn.2.2.1 hn.2.2.2) fun op K2 b2 r2 X2 hop => ?_
  rcases op with ⟨out, pro⟩
  refine KPA.bind' KPA.re' fun rS K3 b3 r3 X3 hS => ?_
  refine KPA.bind' KPA.re' fun rF K4 b4 r4 X4 hF => ?_
  refine KPA.bind' (KPA.emit' (blockOK_one _ _ _ rfl (by simp [getJmps, jok_jmp0])) ?_) fun o K5 b5 r5 X5 ho => ?_
  · intro j hj; simp only [getJmps, List.mem_singleton] at hj; subst hj; exact (hop.1.up X3).up X4
  refine KPA.bind' (hq _ _ _ _ _ (gfl_next ho (jok_jmp0 _) (lzL_ofSure _ _)) (lzS_reg (lt_up hF.2 X5)))
    fun n1 K6 b6 r6 X6 h1 => ?_
  refine KPA.bind' (kpa_pastL env.cod h1 p region) fun n2 K7 b7 r7 X7 h2 => ?_
  refine KPA.bind' (hp _ _ _ _ _ (gfl_next h2.1 h2.2.1 (lzL_ofSure _ _))
    (lzS_reg (lt_up (lt_up (lt_up (lt_up hS.2 X4) X5) X6) X7))) fun n3 K8 b8 r8 X8 h3 => ?_
  exact kpa_copyL h3 (h2.2.2.up X8)

end Glue
end SkaModel
end Formalization
