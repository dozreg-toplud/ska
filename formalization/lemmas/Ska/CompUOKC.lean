import lemmas.Ska.CompConsCallWrap
import lemmas.Ska.CompFragUJ

/-!
# The joint induction for code that calls: `UOKC`

README Gaps 12.17 (twentieth session).  `UOK` collects what a parent needs
of a call-free part; `UOKC` is its counterpart for a part that may call
(`runLC` in place of `runL`), for a formula `f` on the subjects of `P`.

* `BadC`, `NecC`: the semantic `nec`.  `RunOKNC.nec` says that the pure part
  `pq` before the call crashes where the subject does not fit the run's need,
  which a pure part does not meet (`[0 1]` under a goal that asks a cell has
  a value on an atom, one that does not fit the goal).  `NecC` says it of
  `+mink` on `f`, in both directions: every result is a crash with the
  caller's trace or a value that does not fit the goal (`GNot`), and there is
  one.
* `SemGC`, `SemGCB`: `SemNC` and `SemNCB` for any goal (`%done`, `%pick`,
  `%next`); under `%next` they are `SemNC` and `SemNCB` themselves.
* `RunOKGC`: the structural fields of `RunOKNC` for any goal, `NecC`, and
  both `sem` clauses.
* `OKC`: every run of the nomm from a state with the hypotheses of `OKNV`
  meets `RunOKGC`.
* `UOKC`: the kind (call-free with `UOK` and `+mink` on `f` its pure value,
  or hinted, so that `+past` parks a need behind it), `clean` for `runLC`,
  `run` (`OKC`).
* `uokc_of_uok`: every nomm with `UOK` whose formula is its pure value meets
  `UOKC` (`goalSemC_of_goalSem`: the oracle's state stays).
* `uokc_indirect`: the indirect call with parts meeting `UOK` and a formula
  with `MinkN2` (`indirect_runN/D/P` and their `B` versions, the blocks of
  `+simple-next` by `runOKGC_of_next`).
* `UOKC.wrap`: through `WrapRel` (the memo hint, the folded `%6`).
* `finishLUC_contractG`: the whole-subject code of a nomm with `UOKC` meets
  both halves of the contract.
* `UOKC.run` is `OKCN`, the clause for every goal but `%pick`: the leaves
  meet all of `OKC`, and the first parent (the cons whose head calls,
  `CompConsGH.lean`) is proved under `%next` and `%done` only.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The relation -/

/-- A `+mink` tone that a goal sees as a failure: a crash with the trace as
it is, or a product that does not fit the goal (`GNot`). -/
def BadC (goal : CGoal S) (tm : Trace) (r : Tone) : Prop :=
  r = Tone.two tm ∨ ∃ p, r = Tone.zero p ∧ GNot goal p

/-- **The semantic `nec`**: on `s`, every result of `+mink` on `f` is a
failure for the goal, and there is one. -/
def NecC (lib : Lib) (f : Noun) (goal : CGoal S) (s : Noun) : Prop :=
  (∀ (gul : Noun) (n : Nat) (tm : Trace) (r : Tone), minkF lib gul n tm s f = some r → BadC goal tm r) ∧
  (∀ (gul : Noun) (tm : Trace), ∃ r, Mink lib gul tm s f r ∧ BadC goal tm r)

/-- **The forward `sem` of a run that calls, for any goal** (`SemNC` with
`GMem goal` in place of the `%next` goal's need). -/
def SemGC (lib : Lib) (P : Noun → Prop) (f : Noun) (goal : CGoal S) (g0 g1 : Gen Map) (nex : NextL S) :
    Prop :=
  ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) (n : Nat)
      (gul : Noun), OracleSteps Inv ν O → OracleFwd lib Inv ν O n →
    ∀ (st : σ) (t tm : Trace) (s0 s : Noun) (r : Tone), Inv st → Forall2 (FrameRel lib (ν st)) t tm → P s →
    minkF lib gul n tm s f = some r →
    (∀ st' : σ, AgreeU lib O c gul st' t cf ned g0 g1 nex.laz s0 s) → (∀ x, NMem ned x → g1.re ≤ x) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    GoalSemCM lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ GMem goal x) st regs t tm nex.th goal r

/-- **The backward `sem` of a run that calls, for any goal** (`SemNCB` with
`GMem goal`). -/
def SemGCB (lib : Lib) (P : Noun → Prop) (f : Noun) (goal : CGoal S) (g0 g1 : Gen Map) (nex : NextL S) :
    Prop :=
  ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ)
      (gul : Noun), OracleSteps Inv ν O → OracleBwd lib Inv ν O →
    ∀ (st : σ) (t tm : Trace) (s0 s : Noun), Inv st → Forall2 (FrameRel lib (ν st)) t tm → P s →
    (∀ st' : σ, AgreeU lib O c gul st' t cf ned g0 g1 nex.laz s0 s) → (∀ x, NMem ned x → g1.re ≤ x) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    ∀ res, goJ lib O c gul st regs t nex.th = some res →
    ∃ r, Mink lib gul tm s f r ∧
      GoalSemCM lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ GMem goal x) st regs t tm nex.th goal r

/-- **The run relation of code that may call, for any goal**: the
structural fields of `RunOKNC` (the entries' registers may be the goal's),
the semantic `nec`, and both `sem` clauses. -/
structure RunOKGC (lib : Lib) (P : Noun → Prop) (f : Noun) (goal : CGoal S) (g0 g1 : Gen Map) (nex : NextL S) :
    Prop where
  ext : Ext g0 g1
  grow : GrowU g0 g1
  cfr : CondFresh g0 g1
  lo : 1 ≤ nex.th.there
  hi : nex.th.there < g1.bo
  ent : Entry g1 goal nex.th
  regs : ∀ r, NMem nex.laz.sure.ned r → GMem goal r ∨ (g0.re ≤ r ∧ r < g1.re)
  dist : Distinct nex.laz.sure.ned
  eregs : ∀ e ∈ entries nex.laz, Distinct e.2.sure.ned ∧
    ∀ r, NMem e.2.sure.ned r → (GMem goal r ∨ g0.re ≤ r) ∧ r < g1.re
  labs : ∀ e ∈ entries nex.laz, g0.bo ≤ e.1 ∧ e.1 < nex.th.there ∧
    ∃ th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩
  nodup : ((entries nex.laz).map Prod.fst).Nodup
  nec : ∀ s, P s → ¬ FitsS nex.laz.sure s → NecC lib f goal s
  ncond : ∀ r, NMem nex.laz.sure.ned r → HoonMap.get g1.cond r = Option.none
  econd : ∀ e ∈ entries nex.laz, ∀ r, NMem e.2.sure.ned r → HoonMap.get g1.cond r = Option.none
  sem : SemGC lib P f goal g0 g1 nex
  semB : SemGCB lib P f goal g0 g1 nex

/-- The jumps of a goal take no arguments. -/
def GArgs : CGoal S → Prop
  | CGoal.next _ th => th.args = []
  | CGoal.pick z o => z.args = [] ∧ o.args = []
  | CGoal.done => True

/-- **What the induction proves of every run of a nomm that may call**, for
every goal with argless jumps, from a state with the hypotheses of `OKNV`. -/
abbrev OKC (lib : Lib) (env : CallEnv) (P : Noun → Prop) (f : Noun) (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {goal : CGoal S} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    GArgs goal → GJ g0.bo goal → GoalOK g0 goal → GClean goal → sixCount nm ≤ 255 → 1 ≤ g0.bo →
    g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    (∀ r, GMem goal r → HoonMap.get g0.cond r = Option.none) →
    runLC env sup nm (CGoal.toL goal) region g0 = some (nex, g1) → RunOKGC lib P f goal g0 g1 nex

/-- A goal that is not `%pick`. -/
def NoPick : CGoal S → Prop
  | CGoal.pick _ _ => False
  | _ => True

/-- **`OKC` for the goals other than `%pick`**, which is what `UOKC` asks
for now: the cons with a head that calls is proved under `%next` and
`%done` only (README Gaps 12.17). -/
abbrev OKCN (lib : Lib) (env : CallEnv) (P : Noun → Prop) (f : Noun) (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {goal : CGoal S} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    NoPick goal → GArgs goal → GJ g0.bo goal → GoalOK g0 goal → GClean goal → sixCount nm ≤ 255 → 1 ≤ g0.bo →
    g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    (∀ r, GMem goal r → HoonMap.get g0.cond r = Option.none) →
    runLC env sup nm (CGoal.toL goal) region g0 = some (nex, g1) → RunOKGC lib P f goal g0 g1 nex

theorem OKC.toN {lib : Lib} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (h : OKC (S := S) (Map := Map) lib env P f nm) : OKCN (S := S) (Map := Map) lib env P f nm :=
  fun _ ha hj hok hcl hcount b0 d0 hu hcl0 hcb hkg hr => h ha hj hok hcl hcount b0 d0 hu hcl0 hcb hkg hr

/-- `+mink` on `f` is the pure value of `nm` on the subjects of `P`. -/
def MinkEq (lib : Lib) (P : Noun → Prop) (f : Noun) (nm : Nomm) : Prop :=
  ∀ s, P s → ∀ (gul : Noun) (tm : Trace) (r : Tone), Mink lib gul tm s f r ↔ r = toneOf tm (pureEval nm s)

/-- **What the joint induction proves of a nomm that may call**, for the
formula `f` on the subjects of `P`.  `kind`: the nomm is call-free (then
its `UOK` and `+mink` on `f` being its pure value are kept, which a parent
uses for the call-free relations of the part), or it is hinted (`+past`
parks a need that asks something behind it, `pastL_hinted`).  `clean`:
`CleanA` for `runLC` but `%pick`.  `run`: `OKCN` (`OKC` but `%pick`, which only a test
of `%6` or a part under it runs for; the leaves meet the whole `OKC`,
`okc_of_uok`, `okc_indirect`).  The tag clauses of `UOK` (`TagNV`, `TagV`)
are read only by `%6` under `%next` and are not restated yet. -/
structure UOKC (lib : Lib) (env : CallEnv) (P : Noun → Prop) (f : Noun) (nm : Nomm) : Prop where
  kind : (UOK (S := S) (Map := Map) lib nm ∧ MinkEq lib P f nm) ∨ hinted env.cod nm = some true
  clean : ∀ {sup : Option Nomm} {goal : CGoal S} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    NoPick goal → GClean goal → runLC env sup nm (CGoal.toL goal) region g0 = some (nex, g1) → Clean nex.laz.sure.ned
  run : OKCN (S := S) (Map := Map) lib env P f nm

/-! ## The lift from `UOK` -/

/-- `NecC` from the pure `nec`. -/
theorem necC_of_pure {lib : Lib} {P : Noun → Prop} {f : Noun} {nm : Nomm} (M : MinkEq lib P f nm)
    {goal : CGoal S} {s : Noun} (hs : P s)
    (h : pureEval nm s = none ∨ ∃ p, pureEval nm s = some p ∧ GNot goal p) : NecC lib f goal s := by
  have B : ∀ tm, BadC goal tm (toneOf tm (pureEval nm s)) := fun tm => by
    rcases h with e | ⟨p, e, hp⟩
    · rw [e]; exact Or.inl rfl
    · rw [e]; exact Or.inr ⟨p, rfl, hp⟩
  refine ⟨fun gul n tm r hm => ?_, fun gul tm => ⟨_, (M s hs gul tm _).mpr rfl, B tm⟩⟩
  rw [(M s hs gul tm r).mp ⟨n, hm⟩]
  exact B tm

/-- **`RunOKNV` of a call-free part gives `RunOKGC`** under `%next`. -/
theorem RunOKNV.toGC {lib : Lib} {P : Noun → Prop} {f : Noun} {nm : Nomm} (M : MinkEq lib P f nm)
    {sur : Sure S} {th : Jmp} {g0 g1 : Gen Map} {nex : NextL S} (R : RunOKNV (Map := Map) lib nm sur th g0 g1 nex) :
    RunOKGC lib P f (CGoal.next sur th) g0 g1 nex := by
  refine ⟨R.ext, R.grow, R.cfr, R.lo, R.hi, R.ent, R.regs, R.dist,
    fun e he => ⟨(R.eregs e he).1, fun r hr => ⟨Or.inr ((R.eregs e he).2 r hr).1, ((R.eregs e he).2 r hr).2⟩⟩,
    R.labs, R.nodup, fun s hs hf => necC_of_pure M hs (R.nec s hf), R.ncond, R.econd, ?_, ?_⟩
  · intro cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    rw [(M s hs gul tm r).mp ⟨n, hm⟩]
    exact goalSemC_of_goalSem hI htr _ _ (R.sem cf hcf c ned σ O st t gul s0 s (ag st) hned regs hh hn)
  · intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    exact ⟨_, (M s hs gul tm _).mpr rfl,
      goalSemC_of_goalSem hI htr _ _ (R.sem cf hcf c ned σ O st t gul s0 s (ag st) hned regs hh hn)⟩

/-- **`RunOKV` of a call-free part gives `RunOKGC`** for `%done` and `%pick`. -/
theorem RunOKV.toGC {lib : Lib} {P : Noun → Prop} {f : Noun} {nm : Nomm} (M : MinkEq lib P f nm)
    {goal : CGoal S} (hg : NotNext goal) {g0 g1 : Gen Map} {nex : NextL S}
    (R : RunOKV (Map := Map) lib nm goal g0 g1 nex) : RunOKGC lib P f goal g0 g1 nex := by
  refine ⟨R.ext, R.grow, R.cfr, R.lo, R.hi, R.ent, fun r hr => Or.inr (R.regs r hr), R.dist,
    fun e he => ⟨(R.eregs e he).1, fun r hr => ⟨Or.inr ((R.eregs e he).2 r hr).1, ((R.eregs e he).2 r hr).2⟩⟩,
    R.labs, R.nodup, fun s hs hf => necC_of_pure M hs (Or.inl (R.nec s hf)), R.ncond, R.econd, ?_, ?_⟩
  · intro cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    rw [(M s hs gul tm r).mp ⟨n, hm⟩]
    exact goalSemC_of_goalSem hI htr _ _
      (GoalSem.mono (fun r h => h.1) (R.sem cf hcf c ned σ O st t gul s0 s (ag st) hned regs hh hn))
  · intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    exact ⟨_, (M s hs gul tm _).mpr rfl, goalSemC_of_goalSem hI htr _ _
      (GoalSem.mono (fun r h => h.1) (R.sem cf hcf c ned σ O st t gul s0 s (ag st) hned regs hh hn))⟩

/-- **Every nomm with `UOK` whose formula is its pure value meets `UOKC`**:
the run is `runL`'s (`runLC_eq`), and its relations lift by
`goalSemC_of_goalSem` (the oracle's state stays), backward with `+mink`'s
result the pure value. -/
theorem okc_of_uok (lib : Lib) (env : CallEnv) {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (u : UOK (S := S) (Map := Map) lib nm) (M : MinkEq lib P f nm) : OKC (S := S) (Map := Map) lib env P f nm := by
  have nc := Nomm.noCall_of_pure nm u.pure
  intro sup goal region g0 g1 nex ha hj hok hcl hcount b0 d0 hu hcl0 hcb hkg h
  rw [runLC_eq env nm nc] at h
  cases goal with
  | next sur th => exact RunOKNV.toGC M (u.next hj ha hok hcl hcount b0 d0 hu hcl0 hcb hkg h)
  | done => exact RunOKV.toGC (goal := CGoal.done) M trivial (u.done trivial hj hcount b0 d0 hu hcl0 hcb h)
  | pick z o =>
    exact RunOKV.toGC (goal := CGoal.pick z o) M trivial (u.pick z o ha.1 ha.2 trivial hj hcount b0 d0 hu hcl0 hcb h)

/-- **Every nomm with `UOK` whose formula is its pure value meets `UOKC`**
(`okc_of_uok`, the run being `runL`'s by `runLC_eq`). -/
theorem uokc_of_uok (lib : Lib) (env : CallEnv) {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (u : UOK (S := S) (Map := Map) lib nm) (M : MinkEq lib P f nm) : UOKC (S := S) (Map := Map) lib env P f nm := by
  refine ⟨Or.inl ⟨u, M⟩, fun _ hc h => ?_, OKC.toN (okc_of_uok lib env u M)⟩
  rw [runLC_eq env nm (Nomm.noCall_of_pure nm u.pure)] at h
  exact u.clean hc h

/-! ## Runs that begin with the block of `+simple-next` -/

/-- **A run for `%done` or `%pick` that begins with the block `bk` of
`+simple-next` at `bo`** (`[don re]` or `[brn re z o]`), the rest a run
under `%next (lazy-from-reg re)` into it, meets `RunOKGC` for the goal
when the block turns `GoalSemCM` of that `%next` into the goal's (`hconv`). -/
theorem runOKGC_of_next {lib : Lib} {P : Noun → Prop} {f : Noun} {goal : CGoal S} (hg : NotNext goal)
    {g0 g' : Gen Map} {nex : NextL S} {bk : Blob} (hu : UpBelow g0) (hcb : CondBelow g0)
    (hjb : JumpsBelow bk.fin g0.bo) (hpar : bk.par = [])
    (hb : HoonMap.get g'.blocks g0.bo = some bk)
    (hbc : ∀ cf : Map (Nat × List Nat), HoonMap.get cf g0.re = Option.none → unproxyBlob cf bk = bk)
    (hconv : ∀ (c : Straight Map) (σ : Type) (O : Oracle σ) (gul : Noun) (Inv : σ → Prop) (ν : σ → Needs)
      (K K' : Nat → Prop) (st : σ) (regs : Map (Option Noun)) (t tm : Trace) (je : Jmp) (r : Tone),
      (∀ x, K x → K' x) → Forall2 (FrameRel lib (ν st)) t tm → HoonMap.get c.blocks g0.bo = some bk →
      GoalSemCM lib O c gul Inv ν K' st regs t tm je (CGoal.next (lazyReg g0.re : Sure S) (jmp0 g0.bo)) r →
      GoalSemCM lib O c gul Inv ν K st regs t tm je goal r)
    (R : RunOKGC lib P f (CGoal.next (lazyReg g0.re : Sure S) (jmp0 g0.bo))
      ({ g0 with re := g0.re + 1 }.emitted bk) g' nex) :
    RunOKGC lib P f goal g0 g' nex := by
  have l1 := R.ext.1
  have l2 := R.ext.2.1
  simp only [Gen.emitted] at l1 l2
  have E0 : Ext g0 ({ g0 with re := g0.re + 1 }.emitted bk) := (ext_re _).trans (ext_emit _ _)
  have G0 : GrowU g0 ({ g0 with re := g0.re + 1 }.emitted bk) :=
    ((grow_re g0).trans (grow_emit (g := { g0 with re := g0.re + 1 }) hjb)).toU hu
  have C0 : CondFresh g0 ({ g0 with re := g0.re + 1 }.emitted bk) :=
    condFresh_of_eq (by simp [Gen.emitted]) rfl
  have gm : ∀ r, ¬ GMem goal r := notNext_gmem hg
  have gl : ∀ r, GMem (CGoal.next (lazyReg g0.re : Sure S) (jmp0 g0.bo)) r → r = g0.re := fun r h => h
  have bad : ∀ tm r, BadC (CGoal.next (lazyReg g0.re : Sure S) (jmp0 g0.bo)) tm r → BadC goal tm r :=
    fun tm r h => by
      rcases h with e | ⟨p, _, hp⟩
      · exact Or.inl e
      · exact absurd (fitsS_lazyReg g0.re p) hp
  have nlab : ∀ e ∈ entries nex.laz, g0.bo < e.1 := fun e he => by
    have := (R.labs e he).1; simp only [Gen.emitted] at this; omega
  -- the program's block at `bo` and the parts of `AgreeU`
  have blk : ∀ (cf : Map (Nat × List Nat)) (c : Straight Map) (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ)
      (t : Trace) (ned : Need) (s0 s : Noun), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g'.cond k) →
      AgreeU lib O c gul st t cf ned g0 g' nex.laz s0 s → HoonMap.get c.blocks g0.bo = some bk := by
    intro cf c σ O gul st t ned s0 s hcf ag
    have c0 : HoonMap.get cf g0.re = Option.none := by
      rw [hcf _ (by omega), R.cfr.get_lt (by simp [Gen.emitted])]
      exact condBelow_none hcb (Nat.le_refl _)
    rw [ag.1 _ (Nat.le_refl _) (by omega) (fun hm => by
      obtain ⟨e, he, e1⟩ := List.mem_map.mp hm
      have := nlab e he; omega), hb]
    simp only [Option.map_some, hbc cf c0]
  have agp : ∀ (cf : Map (Nat × List Nat)) (c : Straight Map) (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ)
      (t : Trace) (ned : Need) (s0 s : Noun), AgreeU lib O c gul st t cf ned g0 g' nex.laz s0 s →
      AgreeU lib O c gul st t cf ned ({ g0 with re := g0.re + 1 }.emitted bk) g' nex.laz s0 s :=
    fun cf c σ O gul st t ned s0 s ag =>
      AgreeU.part ag (by simp [Gen.emitted]) (Ext.refl g') (fun e he => he) (fun k _ _ hk => hk)
        (fun e he => Nat.lt_trans (R.labs e he).2.1 R.hi)
  have hK : ∀ (ned : Need), (∀ x, NMem ned x → g'.re ≤ x) → ∀ x,
      ((x < g0.re ∨ NMem ned x) ∧ ¬ GMem goal x) →
      ((x < ({ g0 with re := g0.re + 1 }.emitted bk).re ∨ NMem ned x) ∧
        ¬ GMem (CGoal.next (lazyReg g0.re : Sure S) (jmp0 g0.bo)) x) := fun ned hned x hx => by
    simp only [Gen.emitted]
    rcases hx.1 with e | e
    · exact ⟨Or.inl (by omega), fun h => by have := gl x h; omega⟩
    · exact ⟨Or.inr e, fun h => by have := gl x h; have := hned x e; omega⟩
  refine ⟨E0.trans R.ext, G0.trans R.grow, C0.trans R.cfr, R.lo, R.hi, ?_, fun r hr => ?_, R.dist,
    fun e he => ⟨(R.eregs e he).1, fun r hr => ⟨Or.inr ?_, ((R.eregs e he).2 r hr).2⟩⟩,
    fun e he => ⟨by have := nlab e he; omega, (R.labs e he).2⟩, R.nodup,
    fun s hs hf => ⟨fun gul n tm r hm => bad tm r ((R.nec s hs hf).1 gul n tm r hm), fun gul tm => by
      obtain ⟨r, hm, hb'⟩ := (R.nec s hs hf).2 gul tm
      exact ⟨r, hm, bad tm r hb'⟩⟩, R.ncond, R.econd, ?_, ?_⟩
  · rcases R.ent with fr | e
    · exact Or.inl fr
    · simp only [GoalJ] at e
      rw [e]
      exact Or.inl ⟨bk, hb, hpar, rfl⟩
  · rcases R.regs r hr with e | ⟨a, b⟩
    · have := gl r e; subst this; exact Or.inr ⟨Nat.le_refl _, by omega⟩
    · simp only [Gen.emitted] at a; exact Or.inr ⟨by omega, b⟩
  · rcases ((R.eregs e he).2 r hr).1 with a | a
    · have := gl r a; omega
    · simp only [Gen.emitted] at a; omega
  · intro cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    exact hconv c σ O gul Inv ν _ _ st regs t tm nex.th r (hK ned hned) htr (blk cf c σ O gul st t ned s0 s hcf (ag st))
      (R.sem cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm
        (fun st' => agp cf c σ O gul st' t ned s0 s (ag st')) hned regs hh hn)
  · intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨r, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs
      (fun st' => agp cf c σ O gul st' t ned s0 s (ag st')) hned regs hh hn res hres
    exact ⟨r, hm, hconv c σ O gul Inv ν _ _ st regs t tm nex.th r (hK ned hned) htr
      (blk cf c σ O gul st t ned s0 s hcf (ag st)) G⟩

/-- `GoalSemCM` under `%next (lazy-from-reg r0)` into a block `[don r0]` is
`GoalSemCM` for `%done` (`returnsC_done`). -/
theorem goalSemCM_done_of_next {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun}
    {Inv : σ → Prop} {ν : σ → Needs} {K K' : Nat → Prop} {st : σ} {regs : Map (Option Noun)} {t tm : Trace}
    {je : Jmp} {r0 b : Nat} (hb : HoonMap.get c.blocks b = some ⟨[], [], Termin.don r0⟩) {r : Tone}
    (H : GoalSemCM lib O c gul Inv ν K' st regs t tm je (CGoal.next (lazyReg r0 : Sure S) (jmp0 b)) r) :
    GoalSemCM lib O c gul Inv ν K st regs t tm je (CGoal.done : CGoal S) r :=
  returnsC_done hb H

/-- `GoalSemCM` under `%next (lazy-from-reg r0)` into a block `[brn r0 z o]`
is `GoalSemCM` for `%pick z o` (`outGoal_pick`'s steps), for a `K` inside
the `%next`'s. -/
theorem goalSemCM_pick_of_next {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun}
    {Inv : σ → Prop} {ν : σ → Needs} {K K' : Nat → Prop} (hK : ∀ x, K x → K' x) {st : σ}
    {regs : Map (Option Noun)} {t tm : Trace} (htr : Forall2 (FrameRel lib (ν st)) t tm)
    {je : Jmp} {r0 b : Nat} {z o : Jmp} (hb : HoonMap.get c.blocks b = some ⟨[], [], Termin.brn r0 z o⟩) :
    ∀ {r : Tone}, GoalSemCM lib O c gul Inv ν K' st regs t tm je (CGoal.next (lazyReg r0 : Sure S) (jmp0 b)) r →
      GoalSemCM lib O c gul Inv ν K st regs t tm je (CGoal.pick z o : CGoal S) r
  | Tone.zero p, H => by
    obtain ⟨st', regs', hI', hle, hh, hk, e⟩ := H.1 (fitsS_lazyReg r0 p)
    have hr : SkaModel.read r0 regs' = some p := hh
    have E : goJ lib O c gul st regs t je =
        if p = A 0 then goJ lib O c gul st' regs' t z
        else if p = A 1 then goJ lib O c gul st' regs' t o else some (Tone.two t, st') := by
      rw [e, goJ_jmp0 _ _ _ _ hb, execBlob_brn, hr]; rfl
    exact ⟨fun e0 => ⟨st', regs', hI', hle, trivial, fun x hx => hk x (hK x hx), by rw [E, if_pos e0]⟩,
      fun e1 => ⟨st', regs', hI', hle, trivial, fun x hx => hk x (hK x hx), by
        rw [E, if_neg (by rw [e1]; exact fun h => by cases h), if_pos e1]⟩,
      fun e0 e1 => ⟨Tone.two t, st', hI', hle, by rw [E, if_neg e0, if_neg e1],
        ToneRel.two (frames_mono hle htr)⟩⟩
  | Tone.one _, H => H
  | Tone.two _, H => H

/-! ## The indirect call -/

/-- **`RunOKNC` with `SemNCB` gives `RunOKGC` under `%next`**, when `+mink`
on `f` crashes with the trace as it is wherever the pure part `pq` has no
value (both directions). -/
theorem RunOKNC.toGC {lib : Lib} {P : Noun → Prop} {f : Noun} {pq : Nomm} {sur : Sure S} {th : Jmp}
    {g0 g1 : Gen Map} {nex : NextL S} (R : RunOKNC lib P f pq sur th g0 g1 nex) (B : SemNCB lib P f sur th g0 g1 nex)
    (Mc : ∀ s, P s → pureEval pq s = none → ∀ (gul : Noun) (tm : Trace),
      Mink lib gul tm s f (Tone.two tm) ∧ ∀ n r, minkF lib gul n tm s f = some r → r = Tone.two tm) :
    RunOKGC lib P f (CGoal.next sur th) g0 g1 nex :=
  ⟨R.ext, R.grow, R.cfr, R.lo, R.hi, R.ent, R.regs, R.dist, R.eregs, R.labs, R.nodup,
    fun s hs hf => ⟨fun gul n tm r hm => Or.inl ((Mc s hs (R.nec s hf) gul tm).2 n r hm),
      fun gul tm => ⟨_, (Mc s hs (R.nec s hf) gul tm).1, Or.inl rfl⟩⟩, R.ncond, R.econd, R.sem, B⟩

/-- `MinkN2` gives the crash of `+mink` where `[p q]` has no value. -/
theorem minkN2_crashes {lib : Lib} {P : Noun → Prop} {f : Noun} {p q : Nomm} (M : MinkN2 lib P f p q) :
    ∀ s, P s → pureEval (Nomm.cons p q) s = none → ∀ (gul : Noun) (tm : Trace),
      Mink lib gul tm s f (Tone.two tm) ∧ ∀ n r, minkF lib gul n tm s f = some r → r = Tone.two tm := by
  intro s hs e gul tm
  rw [pureEval_cons] at e
  refine ⟨M.crash hs e, fun n r hm => ?_⟩
  rcases M.fwd hs hm with ⟨n', x, y, _, ex, ey, _⟩ | ⟨_, er⟩
  · rw [ex, ey] at e; simp at e
  · exact er

/-- **The indirect call `[2 p q]` with `p`, `q` meeting `UOK` meets `OKC`**
for every formula with `MinkN2` (any `Annot` of `[2 p q]` but the bare
ones): under `%next` `indirect_runN` and `indirect_runNB`, under `%done` and
`%pick` `indirect_runD`, `indirect_runP` and their backward versions after
the block of `+simple-next` (`runOKGC_of_next`). -/
theorem okc_indirect (lib : Lib) (env : CallEnv) {p q : Nomm} (up : UOK (S := S) (Map := Map) lib p)
    (uq : UOK (S := S) (Map := Map) lib q) {P : Noun → Prop} {f : Noun} (M : MinkN2 lib P f p q) :
    OKC (S := S) (Map := Map) lib env P f (Nomm.n2 p q Option.none) := by
  intro sup goal region g0 g1 nex ha hj hok hcl hcount b0 d0 hu hcl0 hcb hkg h
  have hc : sixCount p + sixCount q ≤ 255 := hcount
  cases goal with
  | next sur th =>
    exact RunOKNC.toGC (indirect_runN lib up uq M hc hj ha hok b0 d0 hu hcl0 hcb hkg h)
      (indirect_runNB lib up uq M hc hj ha hok b0 d0 hu hcl0 hcb hkg h) (minkN2_crashes M)
  | done =>
    obtain ⟨hb, R⟩ := indirect_runD lib up uq M hc b0 d0 hu hcl0 hcb h
    have B := indirect_runDB lib up uq M hc b0 d0 hu hcl0 hcb h
    exact runOKGC_of_next (goal := CGoal.done) trivial hu hcb (fun j hj => by simp [finJumps] at hj) rfl hb
      (fun cf c0 => by simp only [unproxyBlob, renBlob, List.map_nil, renFin, unproxy_none c0])
      (fun c σ O gul Inv ν K K' st regs t tm je r _ _ hbc H => goalSemCM_done_of_next hbc H)
      (RunOKNC.toGC R B (minkN2_crashes M))
  | pick z o =>
    obtain ⟨hb, R⟩ := indirect_runP lib up uq M hc b0 d0 hu hcl0 hcb hj h
    have B := indirect_runPB lib up uq M hc b0 d0 hu hcl0 hcb hj h
    exact runOKGC_of_next (goal := CGoal.pick z o) trivial hu hcb
      (fun j hj' => by
        simp only [finJumps, List.mem_cons, List.mem_nil_iff, or_false] at hj'
        rcases hj' with rfl | rfl
        · exact hj.1
        · exact hj.2) rfl hb
      (fun cf c0 => by
        simp only [unproxyBlob, renBlob, List.map_nil, renFin, unproxy_none c0, renJmp_nil _ ha.1,
          renJmp_nil _ ha.2])
      (fun c σ O gul Inv ν K K' st regs t tm je r hK htr hbc H => goalSemCM_pick_of_next hK htr hbc H)
      (RunOKNC.toGC R B (minkN2_crashes M))

/-- **The indirect call `[2 p q]` with `p`, `q` meeting `UOK` meets `UOKC`**
(`okc_indirect`, `indirect_clean`). -/
theorem uokc_indirect (lib : Lib) (env : CallEnv) {p q : Nomm} (up : UOK (S := S) (Map := Map) lib p)
    (uq : UOK (S := S) (Map := Map) lib q) {P : Noun → Prop} {f : Noun} (M : MinkN2 lib P f p q) :
    UOKC (S := S) (Map := Map) lib env P f (Nomm.n2 p q Option.none) :=
  ⟨Or.inr rfl, fun _ _ h => indirect_clean up uq h, OKC.toN (okc_indirect lib env up uq M)⟩

/-! ## The wrappers and the top -/

/-- **`RunOKGC` goes through a wrapper** (`WrapRel`: `+mink` on `f'` runs
`f` with no more fuel and returns what it returns). -/
theorem RunOKGC.wrap {lib : Lib} {P : Noun → Prop} {f f' : Noun} (W : WrapRel lib P f f') {goal : CGoal S}
    {g0 g1 : Gen Map} {nex : NextL S} (R : RunOKGC lib P f goal g0 g1 nex) : RunOKGC lib P f' goal g0 g1 nex := by
  refine ⟨R.ext, R.grow, R.cfr, R.lo, R.hi, R.ent, R.regs, R.dist, R.eregs, R.labs, R.nodup,
    fun s hs hf => ⟨fun gul n tm r hm => ?_, fun gul tm => ?_⟩, R.ncond, R.econd, ?_, ?_⟩
  · obtain ⟨n', _, hm'⟩ := W.fwd hs hm
    exact (R.nec s hs hf).1 gul n' tm r hm'
  · obtain ⟨r, hm, hb⟩ := (R.nec s hs hf).2 gul tm
    exact ⟨r, W.bwd hs hm, hb⟩
  · intro cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    obtain ⟨n', hle, hm'⟩ := W.fwd hs hm
    exact R.sem cf hcf c ned σ Inv ν O n' gul hS (oracleFwd_le hF hle) st t tm s0 s r hI htr hs hm' ag hned
      regs hh hn
  · intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨r, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    exact ⟨r, W.bwd hs hm, G⟩

/-- **`UOKC` goes through a wrapper**: the memo hint and the folded `%6`
(`wrapRel_memo`, `wrapRel_six`), which `Annot.memo`, `Annot.six0`,
`Annot.six1` put around any nomm. -/
theorem UOKC.wrap {lib : Lib} {env : CallEnv} {P : Noun → Prop} {f f' : Noun} {nm : Nomm} (W : WrapRel lib P f f')
    (U : UOKC (S := S) (Map := Map) lib env P f nm) : UOKC (S := S) (Map := Map) lib env P f' nm := by
  refine ⟨?_, U.clean, fun hnp ha hj hok hcl hcount b0 d0 hu hcl0 hcb hkg h =>
    (U.run hnp ha hj hok hcl hcount b0 d0 hu hcl0 hcb hkg h).wrap W⟩
  rcases U.kind with ⟨u, M⟩ | k
  · refine Or.inl ⟨u, fun s hs gul tm r => ⟨fun ⟨n, hm⟩ => ?_, fun e => W.bwd hs ((M s hs gul tm r).mpr e)⟩⟩
    obtain ⟨n', _, hm'⟩ := W.fwd hs hm
    exact (M s hs gul tm r).mp ⟨n', hm'⟩
  · exact Or.inr k

/-- **The whole-subject code of a nomm with `UOKC` meets both halves of the
contract**: its run for `%done` from `gen0` meets `RunOKGC` (`U.run`), whose
structural fields give `TopS`, and `finishTop_genA` with `fwdPhi` and
`bwdPhi` turns the `sem` clauses (`ReturnsC` for `%done`) and `NecC` (a
crash with the caller's trace) into `ContractFwd` and `ContractBwd`. -/
theorem finishLUC_contractG (lib : Lib) {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (U : UOKC (S := S) (Map := Map) lib env P f nm) (hcount : sixCount nm ≤ 255)
    {c : Straight Map} (h : finishLUC (S := S) env nm = some c) (N : Needs) :
    c.need = NeedOrd.this ∧ ∀ s, P s → ContractFwd lib N s f [s] c ∧ ContractBwd lib N s f [s] c := by
  unfold finishLUC at h
  obtain ⟨⟨nex, gE⟩, hr, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨⟨o', sub⟩, g8⟩, hk, hts⟩ := Option.bind_eq_some_iff.mp h
  simp only at hts
  have R : RunOKGC lib P f (CGoal.done : CGoal S) gen0 gE nex :=
    U.run (sup := Option.none) (goal := CGoal.done) (region := []) trivial trivial trivial trivial trivial hcount
      (by simp [gen0]) rfl upBelow_gen0 clear_gen0 condBelow_gen0 (fun r hr => hr.elim) hr
  have T : TopS gE nex :=
    { ext := R.ext
      grow := R.grow
      cfr := R.cfr
      lo := R.lo
      hi := R.hi
      args := by
        rcases R.ent with ⟨b, _, _, ha⟩ | e
        · exact ha
        · exact e.elim
      regs := fun r hr => by
        rcases R.regs r hr with e | e
        · exact e.elim
        · exact e
      dist := R.dist
      eregs := fun e he => ⟨(R.eregs e he).1, fun r hr => ⟨by
        rcases ((R.eregs e he).2 r hr).1 with a | a
        · exact a.elim
        · exact a, ((R.eregs e he).2 r hr).2⟩⟩
      labs := R.labs
      nodup := R.nodup
      ncond := R.ncond
      econd := R.econd }
  have bad : ∀ {tm : Trace} {r : Tone}, BadC (CGoal.done : CGoal S) tm r → r = Tone.two tm := fun hb => by
    rcases hb with e | ⟨_, _, hp⟩
    · exact e
    · exact hp.elim
  have F := finishTop_genA lib T (fwdPhi lib N P f)
    (fun cf hcf c ned σ O st t gul s ag hned regs hh hn Inv ν n tm r hs _ hS hF hm hI htr => by
      obtain ⟨ton, st', -, -, he, hrel⟩ :=
        R.sem cf hcf c ned σ Inv ν O n gul hS hF st t tm s s r hI htr hs hm ag hned regs hh hn
      exact ⟨ton, st', he, hrel⟩)
    (fun σ O st t gul s hfs Inv ν n tm r hs _ _ _ hm _ htr =>
      ⟨Tone.two t, st, rfl, by rw [bad ((R.nec s hs hfs).1 gul n tm r hm)]; exact ToneRel.two htr⟩) hk hts
  have B := finishTop_genA lib T (bwdPhi lib N P f)
    (fun cf hcf c ned σ O st t gul s ag hned regs hh hn Inv ν tm hs _ hS hB hI htr ton st'' hx => by
      obtain ⟨r, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hS hB st t tm s s hI htr hs ag hned regs hh hn _ hx
      obtain ⟨ton', st', -, -, he, hrel⟩ := G
      rw [he] at hx
      cases hx
      exact ⟨r, hm, hrel⟩)
    (fun σ O st t gul s hfs Inv ν tm hs _ _ _ _ htr ton st' hx => by
      cases hx
      obtain ⟨r, hm, hb⟩ := (R.nec s hs hfs).2 gul tm
      rw [bad hb] at hm
      exact ⟨_, hm, ToneRel.two htr⟩) hk hts
  refine ⟨F.1, fun s hs => ⟨fun σ Inv ν O n gul ti tm r hN hS hF hm st hI htr => ?_,
    fun σ Inv ν O gul ti tm hN hS hB st ton st' hI htr hx => ?_⟩⟩
  · exact F.2 σ O st s ti gul Inv ν n tm r hs hN hS hF hm hI htr
  · exact B.2 σ O st s ti gul Inv ν tm hs hN hS hB hI htr ton st' hx

end Comp
end SkaModel
end Formalization
