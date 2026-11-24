import lemmas.Compiler.SkaRun

/-!
# The member loop of `+analyze`

The member loop `ska_analyze.loop0` against `Ana.memberStep`, one turn over
an evaluator `nockW c` with `c` equal to `nock` off `FFar`, with its calls to
itself (`hml`) and the calls of `+run` (`RunIsW`) as parameters.

The loop's core is `[loop0 [next-before [members [loop1 [pass [lbc [index
[hit gate]]]]]]]]` (`memSubj`), `gate` the gate of `+analyze`
`[bat [[id st] K]]`: the turn reads `members` at `14`, `pass` at `62`,
`index` at `254`, `st` at `4093` and `K` at `2047`, and kicks itself with
`members` edited.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon SkaModel.Ana

variable {R : Type}

set_option linter.unusedSimpArgs false

/-- The sample of the gate `+run` before it is slammed. -/
abbrev ska_run.bunt : Noun :=
  C (C (C (A 1) (A 0)) (C (A 0) (A 0))) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0)
    (C (A 0) (C (A 0) (C (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))) (C (A 0) (C (A 0) (C (A 0)
    (C (A 0) (A 0)))))))))))))))

@[nock_exec] theorem ska_run_arm (c : Noun) :
    nock c ska_run.arm = some (C ska_run.battery (C ska_run.bunt c)) := by
  nock_open ska_run.arm; simp only [nock_exec]

/-- The calls of the gate `+run`, made by `c`, compute `run`. -/
def RunIsW (c : Noun → Noun → Option Noun) (regsNoun : R → Noun) (K : Noun) (run : RunGo FinMap R) : Prop :=
  ∀ m o st, c (runSubj regsNoun K m o st) ska_run.battery = (run m o st).map (runNoun regsNoun)

/-- The noun of a result of the member loop: `[[low changed] st]`. -/
noncomputable def memNoun (regsNoun : R → Noun) (r : (Nat × Bool) × SkaState FinMap R) : Noun :=
  C (C (A r.1.1) (flag r.1.2)) (r.2.toNoun regsNoun)

/-- The core of the member loop. -/
noncomputable def memSubj (regsNoun : R → Noun) (K nb pl lbc hit gb : Noun) (id : Ident) (index pass : Nat)
    (members : List Ident) (st : SkaState FinMap R) : Noun :=
  C ska_analyze.loop0 (C nb (C (listNoun identNoun members) (C pl (C (A pass) (C lbc (C (A index)
    (C hit (C gb (C (C (identNoun id) (st.toNoun regsNoun)) K)))))))))

theorem slot_K95 {K : Noun} (h : slot? 2 K = some ska_cg.k_bat) : slot? 95 K = some ska_run.arm := by
  have e : slot? 95 K = (slot? 2 K).bind (slot? 63) := by
    cases K with
    | atom => rfl
    | cell a b => simp [nock_exec]
  rw [e, h]; exact kc_run_at

theorem slot_K94 {K : Noun} (h : slot? 2 K = some ska_cg.k_bat) : slot? 94 K = slot? 62 ska_cg.k_bat := by
  have e : slot? 94 K = (slot? 2 K).bind (slot? 62) := by
    cases K with
    | atom => rfl
    | cell a b => simp [nock_exec]
  rw [e, h]; rfl

theorem kc_dirty_at : slot? 62 ska_cg.k_bat = some ska_cg.dirty.arm := by kernel_rfl

abbrev ska_cg.dirty.bunt : Noun :=
  C (C (C (A 1) (A 0)) (C (A 0) (A 0))) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0)
    (C (A 0) (C (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))))))))

@[nock_exec] theorem ska_dirty_arm (c : Noun) :
    nock c ska_cg.dirty.arm = some (C ska_cg.dirty.battery (C ska_cg.dirty.bunt c)) := by
  nock_open ska_cg.dirty.arm; simp only [nock_exec]

/-- The state with a late run counted, as the member loop does when `pass`
is above `1`. -/
def lateSt (pass : Nat) (st : SkaState FinMap R) : SkaState FinMap R :=
  if pass > 1 then { st with stats := { st.stats with lateRuns := st.stats.lateRuns + 1 } } else st

set_option maxHeartbeats 2000000 in
/-- **One turn of the member loop** over an evaluator `c` that is `nock`
off `FFar`: `Ana.memberStep` with the loop's calls to itself (`ml`) and the
calls of `+run` (`run`) made by `c`. -/
theorem member_stepW (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f)
    (regsNoun : R → Noun) (K : Noun) (hK : slot? 31 K = some ana) (hKb : slot? 2 K = some ska_cg.k_bat)
    (nb pl lbc hit gb : Noun) (id : Ident) (index pass : Nat) (run : RunGo FinMap R)
    (hrun : RunIsW c regsNoun K run) (ml : MemGo FinMap R)
    (hml : ∀ ms st, c (memSubj regsNoun K nb pl lbc hit gb id index pass ms st) ska_analyze.loop0
      = (ml index pass ms st).map (memNoun regsNoun))
    (members : List Ident) (st : SkaState FinMap R) :
    nockW c (memSubj regsNoun K nb pl lbc hit gb id index pass members st) ska_analyze.loop0
      = (memberStep run ml index pass members st).map (memNoun regsNoun) := by
  have hl1 := K_layer1 hK
  have hl2 := K_layer2 hK
  have h95 := slot_K95 hKb
  have h94 := slot_K94 hKb
  rw [kc_dirty_at] at h94
  have hgth : ∀ a b : Nat, nock (C gth.battery (C (C (A a) (A b)) layer1)) gth.battery
      = some (loob (decide (b < a))) := gth_gate layer1 arith_layer1.2.2.2.2.1
  have hlth : ∀ a b : Nat, nock (C lth.battery (C (C (A a) (A b)) layer1)) lth.battery
      = some (loob (decide (a < b))) := lth_gate layer1 arith_layer1.2.2.2.1.2
  have hmin : ∀ a b : Nat, nock (C min.battery (C (C (A a) (A b)) layer1)) min.battery
      = some (A (min a b)) := min_gate layer1 arith_layer1.2.2.2.1
  have hnd : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
    ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
  cases members with
  | nil =>
    unfold memSubj
    nockW_open ska_analyze.loop0
    simp (disch := ffar_disch) [nock_exec, hcf, listNoun, memberStep, memNoun, flag]
  | cons m ms =>
    have hd := dirty_gate regsNoun K hK m st
    cases hdm : Ana.dirty m st with
    | false =>
      have h1 := hml ms st
      unfold memSubj at h1 ⊢
      nockW_open ska_analyze.loop0
      simp (disch := ffar_disch) [nock_exec, hcf, listNoun, memberStep, hdm, hd, h94, h1, loob]
    | true =>
      obtain ⟨g, done, order, stk, next, moved, tick, ticks, regs, stats⟩ := st
      obtain ⟨runs, passes, lateRuns, misses, culled⟩ := stats
      have hoi : getF mugF (identNoun m) (Treap.toNoun A order) = some (unitNoun A (Treap.get order m)) :=
        FinMap.getF_toNoun A order m
      simp only [SkaState.toNoun, Stats.toNoun] at hd
      unfold memSubj
      have key : ∀ la : Nat, (if pass > 1 then lateRuns + 1 else lateRuns) = la →
          nockW c (C ska_analyze.loop0 (C nb (C (listNoun identNoun (m :: ms)) (C pl (C (A pass) (C lbc (C (A index)
            (C hit (C gb (C (C (identNoun id) (SkaState.toNoun regsNoun ⟨g, done, order, stk, next, moved, tick,
              ticks, regs, ⟨runs, passes, lateRuns, misses, culled⟩⟩)) K)))))))))) ska_analyze.loop0
          = ((Treap.get order m).bind fun o =>
              (run m o ⟨g, done, order, stk, next, moved, tick, ticks, regs, ⟨runs, passes, la, misses, culled⟩⟩).bind
                fun r => if r.1.1 < index then some ((r.1.1, r.1.2.2), r.2) else
                  (ml index pass ms r.2).map fun t => ((min r.1.1 t.1.1, r.1.2.2 || t.1.2), t.2)).map
              (memNoun regsNoun) := by
        intro la hla
        cases eo : Treap.get order m with
        | none =>
          rw [eo, show unitNoun A (none : Option Nat) = A 0 from rfl] at hoi
          have hgot := got_gate_nil layer2 hnd (identNoun m) (Treap.toNoun A order) hoi
          nockW_open ska_analyze.loop0
          by_cases hp : pass > 1 <;>
          simp (disch := ffar_disch) [hp, hdm, nock_exec, hcf, listNoun, hd, h94, h95, hl1, hl2, hgth, hgot,
            gth.arm_at, gth_arm, by_arm, by.arm_at, by.got.arm_at, got_arm, loob, SkaState.toNoun, Stats.toNoun]
        | some o =>
          rw [eo, show unitNoun A (some o) = C (A 0) (A o) from rfl] at hoi
          have hgot := got_gate layer2 hnd (identNoun m) (Treap.toNoun A order) (A o) hoi
          have hr := hrun m o ⟨g, done, order, stk, next, moved, tick, ticks, regs, ⟨runs, passes, la, misses, culled⟩⟩
          unfold runSubj at hr
          simp only [SkaState.toNoun, Stats.toNoun] at hr
          simp only [Option.bind_some]
          have hla' : (if 1 < pass then lateRuns + 1 else lateRuns) = la := hla
          cases er : run m o ⟨g, done, order, stk, next, moved, tick, ticks, regs, ⟨runs, passes, la, misses, culled⟩⟩ with
          | none =>
            rw [er] at hr
            nockW_open ska_analyze.loop0
            by_cases hp : 1 < pass <;>
            simp (disch := ffar_disch) [hp, hdm, hla', nock_exec, hcf, listNoun, hd, h94, h95, hl1, hl2, hgth, hgot,
              hr, gth.arm_at, gth_arm, by_arm, by.arm_at, by.got.arm_at, got_arm, loob, SkaState.toNoun,
              Stats.toNoun, runSubj] <;> simp only [hp, if_true, if_false] at hla' <;> subst hla' <;>
            simp (disch := ffar_disch) [hp, hdm, nock_exec, hcf, listNoun, hd, h94, h95, hl1, hl2, hgth, hgot,
              hr, gth.arm_at, gth_arm, by_arm, by.arm_at, by.got.arm_at, got_arm, loob, SkaState.toNoun,
              Stats.toNoun, runSubj]
          | some r =>
            obtain ⟨⟨low, back, chg⟩, st2⟩ := r
            rw [er] at hr
            simp only [Option.map_some, runNoun, SkaState.toNoun, Stats.toNoun] at hr
            simp only [Option.bind_some]
            by_cases hp : 1 < pass <;> simp only [hp, if_true, if_false] at hla' <;> subst hla' <;>
            by_cases hl : low < index
            all_goals first
              | (nockW_open ska_analyze.loop0
                 simp (disch := ffar_disch) [hp, hl, hdm, nock_exec, hcf, listNoun, hd, h94, h95, hl1, hl2, hgth,
                  hgot, hlth, hr, gth.arm_at, gth_arm, lth.arm_at, lth_arm, by_arm, by.arm_at, by.got.arm_at,
                  got_arm, loob, SkaState.toNoun, Stats.toNoun, runSubj, memNoun, flag]; done)
              | (have hm2 := hml ms st2
                 unfold memSubj at hm2
                 simp only [SkaState.toNoun, Stats.toNoun] at hm2
                 cases em : ml index pass ms st2 with
                 | none =>
                   rw [em] at hm2
                   nockW_open ska_analyze.loop0
                   simp (disch := ffar_disch) [hp, hl, hdm, nock_exec, hcf, listNoun, hd, h94, h95, hl1, hl2, hgth,
                    hgot, hlth, hr, hm2, em, gth.arm_at, gth_arm, lth.arm_at, lth_arm, by_arm, by.arm_at,
                    by.got.arm_at, got_arm, loob, SkaState.toNoun, Stats.toNoun, runSubj, memNoun, flag]
                 | some t =>
                   obtain ⟨⟨lt, ct⟩, st3⟩ := t
                   rw [em] at hm2
                   simp only [Option.map_some, memNoun] at hm2
                   nockW_open ska_analyze.loop0
                   cases chg <;> cases ct <;>
                   simp (disch := ffar_disch) [hp, hl, hdm, nock_exec, hcf, listNoun, hd, h94, h95, hl1, hl2, hgth,
                    hgot, hlth, hmin, hr, hm2, em, gth.arm_at, gth_arm, lth.arm_at, lth_arm, min.arm_at, min_arm,
                    by_arm, by.arm_at, by.got.arm_at, got_arm, loob, SkaState.toNoun, Stats.toNoun, runSubj,
                    memNoun, flag])
      rw [key _ rfl]
      by_cases hp : pass > 1 <;> simp [memberStep, hdm, hp]


end Compiler
end Formalization
