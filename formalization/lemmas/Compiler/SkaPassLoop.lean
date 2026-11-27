import lemmas.Compiler.SkaPass

/-!
# The pass loop of `+analyze`

The pass loop `ska_analyze.loop1` against `Ana.passStep`, one turn over an
evaluator `nockW c` with `c` equal to `nock` off `FFar`, with its calls to
itself (`hpl`), the member loop (`hml`), and the gates `+sweep` (`hsw`) and
`+cull` (`hcu`) as parameters.  The gates are parameters because `FFar`
excludes their batteries: the joint induction on the depth of calls runs
their loops at a depth it bounds, and the model gives them the fuel of the
pass.  `passStepH` is the model's turn with `+sweep` and `+cull` given, and
`passStep n` is its instance at `Ana.sweep n` and `Ana.cull n`
(`passStepH_eq`, by `rfl`).

The loop's core is `[loop1 [pass [lbc [index [hit gate]]]]]` (`passSubj`),
`gate` the gate of `+analyze` `[bat [[id st] K]]`: the turn reads `id` at
`508`, `st` at `509`, `K` at `255`, `index` at `30` and `pass` at `6`.  The
battery is split by a kernel-checked equation (`loop1_eq`) into the sweep
(`pSweep`), the count of the pass and the push of `next-before`, the member
loop (`pMem`), the test of the lowlink (`pAfter`) and the end of the pass
(`pEnd`), each with a chunk lemma over an arbitrary continuation.  The end
of the pass (Hoon of dab8478) is the test of stability (`pTest`), then, when
it holds, the `+lien` of `+dirty` over a second `+sweep` (`pLien`, the gate
`|=(m=identity (dirty m st))` built inline, `pGateBat`), and the next pass
(`pNext`) or `+cull` and `+pop` (`pPop`): no member is dropped between
passes.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon SkaModel.Ana

variable {R : Type}

set_option linter.unusedSimpArgs false

/-! ## The arms of `K` that the pass calls -/

theorem kc_sweep_at : slot? 61 ska_cg.k_bat = some ska_cg.sweep.arm := by kernel_rfl
theorem kc_cull_at : slot? 6 ska_cg.k_bat = some ska_cg.cull.arm := by kernel_rfl
theorem kc_pop_at : slot? 2 ska_cg.k_bat = some ska_cg.pop.arm := by kernel_rfl

theorem slot_K93 {K : Noun} (h : slot? 2 K = some ska_cg.k_bat) : slot? 93 K = some ska_cg.sweep.arm := by
  have e : slot? 93 K = (slot? 2 K).bind (slot? 61) := by
    cases K with
    | atom => rfl
    | cell a b => simp [nock_exec]
  rw [e, h]; exact kc_sweep_at

theorem slot_K10 {K : Noun} (h : slot? 2 K = some ska_cg.k_bat) : slot? 10 K = some ska_cg.cull.arm := by
  have e : slot? 10 K = (slot? 2 K).bind (slot? 6) := by
    cases K with
    | atom => rfl
    | cell a b => simp [nock_exec]
  rw [e, h]; exact kc_cull_at

theorem slot_K4 {K : Noun} (h : slot? 2 K = some ska_cg.k_bat) : slot? 4 K = some ska_cg.pop.arm := by
  have e : slot? 4 K = (slot? 2 K).bind (slot? 2) := by
    cases K with
    | atom => rfl
    | cell a b => simp [nock_exec]
  rw [e, h]; exact kc_pop_at

/-- The bunt of an arm `[8 [1 bunt] [[1 bat] [0 1]]]`. -/
def armBunt : Noun → Noun
  | Noun.cell _ (Noun.cell (Noun.cell _ b) _) => b
  | _ => A 0

@[nock_exec] theorem ska_sweep_arm (d : Noun) :
    nock d ska_cg.sweep.arm = some (C ska_cg.sweep.battery (C (armBunt ska_cg.sweep.arm) d)) := by
  nock_open ska_cg.sweep.arm; simp only [nock_exec]; rfl

@[nock_exec] theorem ska_cull_arm (d : Noun) :
    nock d ska_cg.cull.arm = some (C ska_cg.cull.battery (C (armBunt ska_cg.cull.arm) d)) := by
  nock_open ska_cg.cull.arm; simp only [nock_exec]; rfl

@[nock_exec] theorem ska_pop_arm (d : Noun) :
    nock d ska_cg.pop.arm = some (C ska_cg.pop.battery (C (armBunt ska_cg.pop.arm) d)) := by
  nock_open ska_cg.pop.arm; simp only [nock_exec]; rfl

/-! ## The model's turn with `+sweep` and `+cull` given -/

/-- The end of a stable pass with `+sweep` (`sw`) and `+cull` (`cu`) given:
`Ana.passEnd`. -/
noncomputable def passEndH (sw : Ident → FinMap Ident Unit → SkaState FinMap R → Option (List Ident))
    (cu : Ident → SkaState FinMap R → Option (SkaState FinMap R))
    (passLoop : PassGo FinMap R) (id : Ident) (index pass : Nat)
    (st : SkaState FinMap R) : Option (Nat × SkaState FinMap R) :=
  (Ana.above id st.stk).bind fun ab =>
  (sw id (Treap.silt ab) st).bind fun ms =>
  if ms.any (fun m => Ana.dirty m st) = true then passLoop id index (pass + 1) st else
  (cu id st).bind fun st' => (Ana.pop id st').map fun st'' => (st.next, st'')

/-- One pass with `+sweep` (`sw`) and `+cull` (`cu`) given. -/
noncomputable def passStepH (sw : Ident → FinMap Ident Unit → SkaState FinMap R → Option (List Ident))
    (cu : Ident → SkaState FinMap R → Option (SkaState FinMap R))
    (memberLoop : MemGo FinMap R) (passLoop : PassGo FinMap R) (id : Ident) (index pass : Nat)
    (st : SkaState FinMap R) : Option (Nat × SkaState FinMap R) :=
  (Ana.above id st.stk).bind fun ab =>
  (sw id (Treap.silt ab) st).bind fun members =>
  let st := { st with stats := { st.stats with passes := st.stats.passes + 1 } }
  let nextBefore := st.next
  (memberLoop index pass members st).bind fun r =>
  let st := r.2
  if r.1.1 ≠ index then some (r.1.1, st) else
  if r.1.2 = false ∧ st.next = nextBefore then passEndH sw cu passLoop id index pass st
  else passLoop id index (pass + 1) st

theorem passStepH_eq (n : Nat) (ml : MemGo FinMap R) (pl : PassGo FinMap R) (id : Ident) (index pass : Nat)
    (st : SkaState FinMap R) :
    passStepH (fun i was st => Ana.sweep n i was st) (Ana.cull n) ml pl id index pass st
      = Ana.passStep n ml pl id index pass st := rfl

/-! ## The battery, split -/

/-- The core of the pass loop. -/
noncomputable def passSubj (regsNoun : R → Noun) (K lbc hit gb : Noun) (id : Ident) (index pass : Nat)
    (st : SkaState FinMap R) : Noun :=
  C ska_analyze.loop1 (C (A pass) (C lbc (C (A index) (C hit (C gb (C (C (identNoun id) (st.toNoun regsNoun)) K))))))

theorem memSubj_pass (regsNoun : R → Noun) (K nb lbc hit gb : Noun) (id : Ident) (index pass : Nat)
    (members : List Ident) (st : SkaState FinMap R) :
    memSubj regsNoun K nb ska_analyze.loop1 lbc hit gb id index pass members st
      = C ska_analyze.loop0 (C nb (C (listNoun identNoun members) (passSubj regsNoun K lbc hit gb id index pass st))) :=
  rfl

/-- `=/  members  (sweep id (silt (above id stk.st)) st)`, the gate pushed. -/
def pSweep : Noun :=
  C (A 8) (C (C (A 9) (C (A 93) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1020)) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 767) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 22) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1020)) (C (A 0) (A 16350)))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))))) (C (A 0) (A 1021))))) (C (A 0) (A 2)))))))

/-- The member loop, its core built and kicked. -/
def pMem : Noun :=
  C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 1) ska_analyze.loop0) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))

/-- The test of stability: `&(!changed =(next.st next-before))`. -/
def pTest : Noun :=
  C (A 6) (C (C (A 6) (C (C (A 0) (A 5)) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 0x1ffbe)) (C (A 0) (A 6)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))

/-- `(sweep id (silt (above id stk.st)) st)` at the end of the pass. -/
def pSw2 : Noun :=
  C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 93) (C (A 0) (A 2047)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 8188)) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 767) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 22) (C (A 0) (A 2047)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 8188)) (C (A 0) (A 0x1ffde)))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))))) (C (A 0) (A 8189))))) (C (A 0) (A 2)))))))))

/-- The battery of the gate `|=(m=identity (dirty m st))`. -/
def pGateBat : Noun :=
  C (A 8) (C (C (A 9) (C (A 94) (C (A 0) (A 8191)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 0) (A 0x7ffd)))) (C (A 0) (A 2)))))))

/-- The gate built. -/
def pGate : Noun :=
  C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) identBunt) (C (C (A 1) pGateBat) (C (A 0) (A 1))))))

/-- `(lien (sweep ..) |=(m=identity (dirty m st)))`. -/
def pLien : Noun :=
  C (A 8) (C (C (A 9) (C (A 0x2fbde) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C pSw2 pGate)) (C (A 0) (A 2)))))))

/-- `pass-loop(pass +(pass))`. -/
def pNext : Noun :=
  C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 4) (C (A 0) (A 62)))) (C (A 0) (A 15)))))

/-- `[next.st (pop id (cull id st))]`. -/
def pPop : Noun :=
  C (C (A 0) (A 0x1ffbe)) (C (A 8) (C (C (A 9) (C (A 4) (C (A 0) (A 2047)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 8188)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 2047)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 8188)) (C (A 0) (A 8189)))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))

/-- The end of the pass. -/
def pEnd : Noun := C (A 6) (C pTest (C (C (A 6) (C pLien (C pNext pPop))) pNext))

/-- After the member loop: its state put back, the test of the lowlink. -/
def pAfter (Y : Noun) : Noun :=
  C (A 7) (C (C (A 10) (C (C (A 4093) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3)))
    (C (A 6) (C (C (A 5) (C (C (A 0) (A 4)) (C (A 0) (A 254)))) (C Y (C (C (A 0) (A 4)) (C (A 0) (A 4093)))))))))

/-- The count of the pass, the push of `next-before`, then the member loop. -/
def pCount (F : Noun) : Noun :=
  C (A 7) (C (C (A 10) (C (C (A 0x1feffe) (C (A 4) (C (A 0) (A 0x1feffe)))) (C (A 0) (A 1))))
    (C (A 8) (C (C (A 0) (A 32702)) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C pMem F)))))))

theorem loop1_eq : ska_analyze.loop1 =
    C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C pSweep (pCount (pAfter pEnd))))) := by kernel_rfl

theorem nockW_seven_one (c : Noun → Noun → Option Noun) (s X : Noun) :
    nockW c s (C (A 7) (C (C (A 0) (A 1)) X)) = nockW c s X := by
  rw [nockW_op7, nockW_op0, slot?_one]; rfl

/-- The state with the pass counted. -/
def passSt (st : SkaState FinMap R) : SkaState FinMap R :=
  { st with stats := { st.stats with passes := st.stats.passes + 1 } }

section chunks
variable (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f)
  (regsNoun : R → Noun) (K : Noun) (hK : slot? 31 K = some ana) (hKb : slot? 2 K = some ska_cg.k_bat)
  (lbc hit gb : Noun) (id : Ident) (index pass : Nat)

include hcf hK hKb in
set_option maxHeartbeats 1000000 in
/-- The sweep: `+above`, `+silt`, then the gate `+sweep` made by `c`. -/
theorem pass_sweep (sw : Ident → FinMap Ident Unit → SkaState FinMap R → Option (List Ident))
    (hsw : ∀ was st, c (sweepS0 regsNoun K id was st) ska_cg.sweep.battery = (sw id was st).map (listNoun identNoun))
    (st : SkaState FinMap R) (F : Noun) :
    nockW c (passSubj regsNoun K lbc hit gb id index pass st) (C (A 8) (C pSweep F))
      = ((Ana.above id st.stk).bind fun ab => sw id (Treap.silt ab) st).bind fun ms =>
          nockW c (C (listNoun identNoun ms) (passSubj regsNoun K lbc hit gb id index pass st)) F := by
  have hl2 := K_layer2 hK
  have h93 := slot_K93 hKb
  have h22 := slot_K22 hKb
  have habv := above_gate K id st.stk
  have hs0 := hsw
  obtain ⟨g, done, order, stk, next, moved, tick, ticks, regs, stats⟩ := st
  obtain ⟨runs, passes, lateRuns, misses, culled⟩ := stats
  simp only at habv ⊢
  cases hab : Ana.above id stk with
  | none =>
    rw [hab] at habv
    simp only [Option.map_none] at habv
    unfold passSubj pSweep
    simp (disch := ffar_disch) [nock_exec, hcf, SkaState.toNoun, Stats.toNoun, habv, h22, hl2, silt_arm_at]
  | some ab =>
    rw [hab] at habv
    simp only [Option.map_some] at habv
    have hsilt : nock (C siltBattery (C (listNoun identNoun ab) layer2)) siltBattery
        = some (Treap.setNoun (Treap.silt ab : FinMap Ident Unit)) := by
      rw [listNoun_map_listN]; exact silt_gate _ _ (silt_setNoun ab)
    have hs := hsw (Treap.silt ab) ⟨g, done, order, stk, next, moved, tick, ticks, regs,
      ⟨runs, passes, lateRuns, misses, culled⟩⟩
    unfold sweepS0 at hs
    simp only [SkaState.toNoun, Stats.toNoun] at hs
    unfold passSubj pSweep
    cases hr : sw id (Treap.silt ab) ⟨g, done, order, stk, next, moved, tick, ticks, regs,
      ⟨runs, passes, lateRuns, misses, culled⟩⟩ with
    | none =>
      rw [hr] at hs
      simp (disch := ffar_disch) [nock_exec, hcf, SkaState.toNoun, Stats.toNoun, habv, h22, h93, hl2,
        silt_arm_at, hsilt, hs, hr]
    | some ms =>
      rw [hr] at hs
      simp (disch := ffar_disch) [nock_exec, hcf, SkaState.toNoun, Stats.toNoun, habv, h22, h93, hl2,
        silt_arm_at, hsilt, hs, hr]

set_option maxHeartbeats 1000000 in
/-- The count of the pass, `next-before`, and the member loop made by `c`. -/
theorem pass_count (ml : MemGo FinMap R)
    (hml : ∀ nb ms st, c (memSubj regsNoun K (A nb) ska_analyze.loop1 lbc hit gb id index pass ms st)
      ska_analyze.loop0 = (ml index pass ms st).map (memNoun regsNoun))
    (ms : List Ident) (st : SkaState FinMap R) (F : Noun) :
    nockW c (C (listNoun identNoun ms) (passSubj regsNoun K lbc hit gb id index pass st)) (pCount F)
      = (ml index pass ms (passSt st)).bind fun r =>
          nockW c (C (memNoun regsNoun r) (C (A st.next) (C (listNoun identNoun ms)
            (passSubj regsNoun K lbc hit gb id index pass (passSt st))))) F := by
  have h := hml st.next ms (passSt st)
  rw [memSubj_pass] at h
  obtain ⟨g, done, order, stk, next, moved, tick, ticks, regs, stats⟩ := st
  obtain ⟨runs, passes, lateRuns, misses, culled⟩ := stats
  unfold passSubj at h ⊢
  simp only [passSt, SkaState.toNoun, Stats.toNoun] at h ⊢
  unfold pCount pMem
  cases hr : ml index pass ms ⟨g, done, order, stk, next, moved, tick, ticks, regs,
      ⟨runs, passes + 1, lateRuns, misses, culled⟩⟩ with
  | none =>
    rw [hr] at h
    simp (disch := ffar_disch) [nock_exec, h]
  | some r =>
    rw [hr] at h
    simp (disch := ffar_disch) [nock_exec, h]

/-- The member loop's state put back, and the test of the lowlink. -/
theorem pass_after (Y : Noun) (r : (Nat × Bool) × SkaState FinMap R) (nb : Nat) (L : Noun)
    (st : SkaState FinMap R) :
    nockW c (C (memNoun regsNoun r) (C (A nb) (C L (passSubj regsNoun K lbc hit gb id index pass st)))) (pAfter Y)
      = if r.1.1 = index then
          nockW c (C (C (A r.1.1) (flag r.1.2)) (C (A nb) (C L (passSubj regsNoun K lbc hit gb id index pass r.2)))) Y
        else some (anaNoun regsNoun (r.1.1, r.2)) := by
  obtain ⟨⟨low, ch⟩, st2⟩ := r
  unfold passSubj memNoun anaNoun pAfter
  by_cases h : low = index
  · subst h; simp [nock_exec, eqCode]
  · have h' : ¬ index = low := fun e => h e.symm
    simp [nock_exec, eqCode, h, h']

/-- The subject of the end of a pass: `[[low changed] [next-before [members
core]]]`. -/
noncomputable def endSubj (low : Nat) (ch : Bool) (nb : Nat) (L : Noun) (st : SkaState FinMap R) : Noun :=
  C (C (A low) (flag ch)) (C (A nb) (C L (passSubj regsNoun K lbc hit gb id index pass st)))

/-- The test of stability. -/
theorem pass_test (low : Nat) (ch : Bool) (nb : Nat) (L : Noun) (st : SkaState FinMap R) :
    nockW c (endSubj regsNoun K lbc hit gb id index pass low ch nb L st) pTest
      = some (loob (decide (ch = false ∧ st.next = nb))) := by
  obtain ⟨g, done, order, stk, next, moved, tick, ticks, regs, stats⟩ := st
  obtain ⟨runs, passes, lateRuns, misses, culled⟩ := stats
  unfold endSubj passSubj pTest
  by_cases hn : next = nb
  · subst hn; cases ch <;> simp [nock_exec, SkaState.toNoun, Stats.toNoun, flag, eqCode]
  · have hn' : ¬ nb = next := fun e => hn e.symm
    cases ch <;> simp [nock_exec, SkaState.toNoun, Stats.toNoun, flag, eqCode, hn, hn']

/-- The next pass, made by `c`. -/
theorem pass_next (pl : PassGo FinMap R)
    (hpl : ∀ st, c (passSubj regsNoun K lbc hit gb id index (pass + 1) st) ska_analyze.loop1
      = (pl id index (pass + 1) st).map (anaNoun regsNoun))
    (low : Nat) (ch : Bool) (nb : Nat) (L : Noun) (st : SkaState FinMap R) :
    nockW c (endSubj regsNoun K lbc hit gb id index pass low ch nb L st) pNext
      = (pl id index (pass + 1) st).map (anaNoun regsNoun) := by
  have hq := hpl st
  unfold passSubj at hq
  unfold endSubj passSubj pNext
  simp [nock_exec, hq]

include hcf hK hKb in
set_option maxHeartbeats 1000000 in
/-- `[next.st (pop id (cull id st))]`, `+cull` made by `c`. -/
theorem pass_pop (cu : Ident → SkaState FinMap R → Option (SkaState FinMap R))
    (hcu : ∀ st, c (cullS0 regsNoun K id st) ska_cg.cull.battery = (cu id st).map (SkaState.toNoun regsNoun))
    (low : Nat) (ch : Bool) (nb : Nat) (L : Noun) (st : SkaState FinMap R) :
    nockW c (endSubj regsNoun K lbc hit gb id index pass low ch nb L st) pPop
      = (cu id st).bind fun st3 => (Ana.pop id st3).map fun st' => anaNoun regsNoun (st.next, st') := by
  have h10 := slot_K10 hKb
  have h4 := slot_K4 hKb
  have hc := hcu st
  unfold cullS0 at hc
  unfold endSubj passSubj
  cases hr : cu id st with
  | none =>
    rw [hr] at hc
    obtain ⟨g, done, order, stk, next, moved, tick, ticks, regs, stats⟩ := st
    obtain ⟨runs, passes, lateRuns, misses, culled⟩ := stats
    simp only [SkaState.toNoun, Stats.toNoun] at hc ⊢
    unfold pPop
    simp (disch := ffar_disch) [nock_exec, hcf, h10, hc]
  | some st3 =>
    rw [hr] at hc
    have hp := pop_gate' regsNoun K hK id st3
    obtain ⟨g, done, order, stk, next, moved, tick, ticks, regs, stats⟩ := st
    obtain ⟨runs, passes, lateRuns, misses, culled⟩ := stats
    simp only [SkaState.toNoun, Stats.toNoun] at hc ⊢
    unfold pPop
    cases hq : Ana.pop id st3 with
    | none =>
      rw [hq] at hp
      simp (disch := ffar_disch) [nock_exec, hcf, h10, h4, hc, hp, hq]
    | some st4 =>
      rw [hq] at hp
      simp (disch := ffar_disch) [nock_exec, hcf, h10, h4, hc, hp, hq, anaNoun]

include hK hKb in
/-- The gate `|=(m=identity (dirty m st))` on `m`. -/
theorem gate_dirty (low : Nat) (ch : Bool) (nb : Nat) (L : Noun) (st : SkaState FinMap R) (m : Ident) :
    nock (C pGateBat (C (identNoun m) (endSubj regsNoun K lbc hit gb id index pass low ch nb L st))) pGateBat
      = some (loob (Ana.dirty m st)) := by
  have h94 := slot_K94 hKb
  rw [kc_dirty_at] at h94
  have hd := dirty_gate regsNoun K hK m st
  unfold endSubj passSubj pGateBat
  simp [nock_exec, h94, hd]

include hK hKb in
/-- `+lien` of that gate on a list of identities. -/
theorem lien_dirty (low : Nat) (ch : Bool) (nb : Nat) (L : Noun) (st : SkaState FinMap R) (ms : List Ident) :
    nock (C lien.battery (C (C (listNoun identNoun ms)
      (C pGateBat (C identBunt (endSubj regsNoun K lbc hit gb id index pass low ch nb L st)))) layer2))
      lien.battery = some (loob (ms.any fun m => Ana.dirty m st)) := by
  let p : Noun → Bool := fun x => decide (∃ m ∈ ms, identNoun m = x ∧ Ana.dirty m st = true)
  have hp : ∀ m ∈ ms, p (identNoun m) = Ana.dirty m st := by
    intro m hm
    by_cases hdm : Ana.dirty m st = true
    · rw [hdm]; exact decide_eq_true ⟨m, hm, rfl, hdm⟩
    · have : p (identNoun m) = false := decide_eq_false (by
        rintro ⟨m', _, e, h'⟩
        rw [(identNoun_eq_iff _ _).1 e] at h'; exact hdm h')
      rw [this]; cases h : Ana.dirty m st
      · rfl
      · exact absurd h hdm
  have hl := lien_gate layer2 pGateBat identBunt (endSubj regsNoun K lbc hit gb id index pass low ch nb L st)
    p (ms.map identNoun) (fun x hx => by
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
      rw [gate_dirty regsNoun K hK hKb lbc hit gb id index pass low ch nb L st m, hp m hm])
  rw [listNoun_map_listN, hl]
  congr 2
  rw [List.any_map]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Function.comp_apply]
  exact ⟨fun ⟨m, hm, h⟩ => ⟨m, hm, by rw [← hp m hm]; exact h⟩, fun ⟨m, hm, h⟩ => ⟨m, hm, by rw [hp m hm]; exact h⟩⟩

include hcf hK hKb in
set_option maxHeartbeats 2000000 in
/-- The `+lien` over the second `+sweep`, the gate `+sweep` made by `c`. -/
theorem pass_lien (sw : Ident → FinMap Ident Unit → SkaState FinMap R → Option (List Ident))
    (hsw : ∀ was st, c (sweepS0 regsNoun K id was st) ska_cg.sweep.battery = (sw id was st).map (listNoun identNoun))
    (low : Nat) (ch : Bool) (nb : Nat) (L : Noun) (st : SkaState FinMap R) :
    nockW c (endSubj regsNoun K lbc hit gb id index pass low ch nb L st) pLien
      = ((Ana.above id st.stk).bind fun ab => sw id (Treap.silt ab) st).map
          fun ms => loob (ms.any fun m => Ana.dirty m st) := by
  have hl2 := K_layer2 hK
  have h93 := slot_K93 hKb
  have h22 := slot_K22 hKb
  have hla : slot? 0x2fbde layer2 = some lien.arm := lien.arm_at
  have habv := above_gate K id st.stk
  have hld := lien_dirty regsNoun K hK hKb lbc hit gb id index pass low ch nb L st
  unfold endSubj at hld
  obtain ⟨g, done, order, stk, next, moved, tick, ticks, regs, stats⟩ := st
  obtain ⟨runs, passes, lateRuns, misses, culled⟩ := stats
  simp only at habv ⊢
  unfold endSubj
  cases hab : Ana.above id stk with
  | none =>
    rw [hab] at habv
    simp only [Option.map_none] at habv
    unfold passSubj pLien pSw2 pGate
    simp (disch := ffar_disch) [nock_exec, hcf, SkaState.toNoun, Stats.toNoun, habv, h22, hl2, silt_arm_at, hla]
  | some ab =>
    rw [hab] at habv
    simp only [Option.map_some] at habv
    have hsilt : nock (C siltBattery (C (listNoun identNoun ab) layer2)) siltBattery
        = some (Treap.setNoun (Treap.silt ab : FinMap Ident Unit)) := by
      rw [listNoun_map_listN]; exact silt_gate _ _ (silt_setNoun ab)
    have hs := hsw (Treap.silt ab) ⟨g, done, order, stk, next, moved, tick, ticks, regs,
      ⟨runs, passes, lateRuns, misses, culled⟩⟩
    unfold sweepS0 at hs
    simp only [SkaState.toNoun, Stats.toNoun] at hs
    cases hr : sw id (Treap.silt ab) ⟨g, done, order, stk, next, moved, tick, ticks, regs,
      ⟨runs, passes, lateRuns, misses, culled⟩⟩ with
    | none =>
      rw [hr] at hs
      unfold passSubj pLien pSw2 pGate
      simp (disch := ffar_disch) [nock_exec, hcf, SkaState.toNoun, Stats.toNoun, habv, h22, h93, hl2,
        silt_arm_at, hsilt, hs, hr, hla]
    | some ms =>
      rw [hr] at hs
      have hld' := hld ms
      unfold passSubj at hld'
      simp only [SkaState.toNoun, Stats.toNoun] at hld'
      unfold passSubj pLien pSw2 pGate
      simp (disch := ffar_disch) [nock_exec, hcf, SkaState.toNoun, Stats.toNoun, habv, h22, h93, hl2,
        silt_arm_at, hsilt, hs, hr, hla, hld']

include hcf hK hKb in
/-- The end of the pass: the test of stability, then `passEndH` (the second
`+sweep` and `+cull` made by `c`) or the next pass made by `c`. -/
theorem pass_end (sw : Ident → FinMap Ident Unit → SkaState FinMap R → Option (List Ident))
    (hsw : ∀ was st, c (sweepS0 regsNoun K id was st) ska_cg.sweep.battery = (sw id was st).map (listNoun identNoun))
    (cu : Ident → SkaState FinMap R → Option (SkaState FinMap R))
    (hcu : ∀ st, c (cullS0 regsNoun K id st) ska_cg.cull.battery = (cu id st).map (SkaState.toNoun regsNoun))
    (pl : PassGo FinMap R)
    (hpl : ∀ st, c (passSubj regsNoun K lbc hit gb id index (pass + 1) st) ska_analyze.loop1
      = (pl id index (pass + 1) st).map (anaNoun regsNoun))
    (low : Nat) (ch : Bool) (nb : Nat) (L : Noun) (st : SkaState FinMap R) :
    nockW c (C (C (A low) (flag ch)) (C (A nb) (C L (passSubj regsNoun K lbc hit gb id index pass st)))) pEnd
      = if ch = false ∧ st.next = nb then (passEndH sw cu pl id index pass st).map (anaNoun regsNoun)
        else (pl id index (pass + 1) st).map (anaNoun regsNoun) := by
  have e : C (C (A low) (flag ch)) (C (A nb) (C L (passSubj regsNoun K lbc hit gb id index pass st)))
      = endSubj regsNoun K lbc hit gb id index pass low ch nb L st := rfl
  rw [e]
  unfold pEnd
  rw [nockW_op6, pass_test]
  simp only [Option.bind_some, pick_loob]
  by_cases hcnd : ch = false ∧ st.next = nb
  · rw [decide_eq_true hcnd, if_pos rfl, if_pos hcnd, nockW_op6,
      pass_lien c hcf regsNoun K hK hKb lbc hit gb id index pass sw hsw]
    unfold passEndH
    cases Ana.above id st.stk with
    | none => rfl
    | some ab =>
      simp only [Option.bind_some]
      cases sw id (Treap.silt ab) st with
      | none => rfl
      | some ms =>
        simp only [Option.map_some, Option.bind_some, pick_loob]
        by_cases hany : (ms.any fun m => Ana.dirty m st) = true
        · rw [if_pos hany, if_pos hany, pass_next c regsNoun K lbc hit gb id index pass pl hpl]
        · rw [if_neg hany, if_neg hany, pass_pop c hcf regsNoun K hK hKb lbc hit gb id index pass cu hcu]
          cases cu id st with
          | none => rfl
          | some st3 =>
            simp only [Option.bind_some]
            cases Ana.pop id st3 <;> rfl
  · rw [decide_eq_false hcnd, if_neg Bool.false_ne_true, if_neg hcnd,
      pass_next c regsNoun K lbc hit gb id index pass pl hpl]

include hcf hK hKb in
/-- **One turn of the pass loop** over an evaluator `c` that is `nock` off
`FFar`: `passStepH` with `+sweep` (`sw`), `+cull` (`cu`), the member loop
(`ml`) and the loop's calls to itself (`pl`) made by `c`. -/
theorem pass_stepW (sw : Ident → FinMap Ident Unit → SkaState FinMap R → Option (List Ident))
    (hsw : ∀ was st, c (sweepS0 regsNoun K id was st) ska_cg.sweep.battery = (sw id was st).map (listNoun identNoun))
    (cu : Ident → SkaState FinMap R → Option (SkaState FinMap R))
    (hcu : ∀ st, c (cullS0 regsNoun K id st) ska_cg.cull.battery = (cu id st).map (SkaState.toNoun regsNoun))
    (ml : MemGo FinMap R)
    (hml : ∀ nb ms st, c (memSubj regsNoun K (A nb) ska_analyze.loop1 lbc hit gb id index pass ms st)
      ska_analyze.loop0 = (ml index pass ms st).map (memNoun regsNoun))
    (pl : PassGo FinMap R)
    (hpl : ∀ st, c (passSubj regsNoun K lbc hit gb id index (pass + 1) st) ska_analyze.loop1
      = (pl id index (pass + 1) st).map (anaNoun regsNoun))
    (st : SkaState FinMap R) :
    nockW c (passSubj regsNoun K lbc hit gb id index pass st) ska_analyze.loop1
      = (passStepH sw cu ml pl id index pass st).map (anaNoun regsNoun) := by
  conv => lhs; arg 3; rw [loop1_eq]
  rw [nockW_seven_one, pass_sweep c hcf regsNoun K hK hKb lbc hit gb id index pass sw hsw]
  simp only [pass_count c regsNoun K lbc hit gb id index pass ml hml, pass_after c regsNoun K lbc hit gb id index pass,
    pass_end c hcf regsNoun K hK hKb lbc hit gb id index pass sw hsw cu hcu pl hpl]
  unfold passStepH passSt
  cases Ana.above id st.stk with
  | none => rfl
  | some ab =>
    simp only [Option.bind_some]
    cases sw id (Treap.silt ab) st with
    | none => rfl
    | some ms =>
      simp only [Option.bind_some]
      cases ml index pass ms { st with stats := { st.stats with passes := st.stats.passes + 1 } } with
      | none => rfl
      | some r =>
        simp only [Option.bind_some]
        by_cases hl : r.1.1 = index
        · simp only [hl, if_true, ne_eq, not_true_eq_false, if_false]
          by_cases hc : r.1.2 = false ∧ r.2.next = st.next
          · rw [if_pos hc, if_pos hc]
          · rw [if_neg hc, if_neg hc]
        · simp only [hl, if_false, ne_eq, not_false_eq_true, if_true]
          rfl

end chunks

end Compiler
end Formalization
