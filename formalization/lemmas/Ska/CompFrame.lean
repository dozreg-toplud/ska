import lemmas.Ska.ExecPath
import lemmas.Ska.CompFootRun

/-!
# The semantic frame lemma on paths

An execution keeps every register that no block on its path writes.  The
write footprint of `CompFootRun.lean` (`poleWr`, `BlobWr`) is about the
blocks; this file says what it means for the paths of `ExecPath.lean`.

* `stepWr x`: the registers the next step of `x` writes.  A step that passes
  arguments writes the parameters of the block (`+eval-pass` moves a register
  or poison into each), a step that runs an op writes its destination
  (`poleWr`), and a jump writes nothing (its arguments are passed by the next
  step, at the block it enters).
* `step_frame`: a step changes only registers of `stepWr x` (`HoonMap.get`
  is unchanged elsewhere, so a value stays that value and poison stays
  poison), from `evalPass_frame` and `execPole_frame`.
* `TakenIn L f`: every jump the terminator `f` can take goes to a label of
  `L`.  `steps_frame`: if every block of the program at a label of `L` writes
  only registers of `Q` and takes only jumps into `L`, and so does what is left
  of the block of `x`, then along every path from `x` the registers outside
  `Q` keep their values, and every label the path enters is in `L`.
* `run_frame`, `execEntry_frame`: the same for the path that `run_iff_path`
  and `execEntry_iff_path` give for a run that returns; `steps_reads_frame`:
  a real read of a register outside `Q` on a path of a run that returns reads
  the value the register had at the start, so a register outside `Q` that is
  poisoned at the start is never read for real.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Path

section Frame
variable {Map : Type → Type} [HoonMap Map] {σ : Type}

/-! ## The registers one step writes -/

/-- **The registers the next step of `x` writes**: the parameters of the
block when it passes arguments, the destination of the op it runs, and nothing
for a jump. -/
def stepWr (x : Cfg σ Map) : List Nat :=
  if x.params ≠ [] ∨ x.b.par ≠ [] then x.b.par else
  match x.b.body with
  | p :: _ => poleWr p
  | [] => []

theorem get_store_other {r d : Nat} {v : Noun} {regs : Map (Option Noun)} (h : r ≠ d) :
    HoonMap.get (store d v regs) r = HoonMap.get regs r := by
  simp [store, HoonMap.get_put, h]

theorem get_poison_other {r d : Nat} {regs : Map (Option Noun)} (h : r ≠ d) :
    HoonMap.get (poison d regs) r = HoonMap.get regs r := by
  simp [poison, HoonMap.get_put, h]

theorem get_move_other {s d r : Nat} {regs R : Map (Option Noun)} (hm : move s d regs = some R) (h : r ≠ d) :
    HoonMap.get R r = HoonMap.get regs r := by
  unfold move at hm
  obtain ⟨u, _, rfl⟩ := Option.map_eq_some_iff.mp hm
  simp [HoonMap.get_put, h]

/-- **The loop of `+eval-pass` changes only the parameters.** -/
theorem evalPassLoop_frame : ∀ (args : List (Option Nat)) (par : List Nat) (regs R : Map (Option Noun)),
    evalPassLoop args par regs = some R → ∀ r, r ∉ par → HoonMap.get R r = HoonMap.get regs r
  | [], par, regs, R, h, r, _ => by
    simp only [evalPassLoop] at h
    by_cases hp : par = []
    · rw [if_pos hp, Option.some.injEq] at h; rw [h]
    · rw [if_neg hp] at h; cases h
  | _ :: _, [], _, _, h, _, _ => by simp [evalPassLoop] at h
  | a :: args, p :: par, regs, R, h, r, hr => by
    simp only [evalPassLoop] at h
    obtain ⟨R1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    have hrp : r ≠ p := fun e => hr (by simp [e])
    have hrq : r ∉ par := fun e => hr (by simp [e])
    rw [evalPassLoop_frame args par R1 R h2 r hrq]
    cases a with
    | none =>
      simp only [Option.some.injEq] at h1
      rw [← h1]; exact get_poison_other hrp
    | some s => exact get_move_other h1 hrp

/-- **`+eval-pass` changes only the parameters.** -/
theorem evalPass_frame {args : List (Option Nat)} {par : List Nat} {regs R : Map (Option Noun)}
    (h : evalPass args par regs = some R) : ∀ r, r ∉ par → HoonMap.get R r = HoonMap.get regs r := by
  unfold evalPass at h
  split at h
  · exact evalPassLoop_frame args par regs R h
  · cases h

theorem afterCall_frame {st st' : σ} {regs R : Map (Option Noun)} {t t' : Trace} {d : Nat} {ton ton' : Tone}
    (h : afterCall st regs t d ton = some (ton', R, t', st')) : ∀ r, r ≠ d → HoonMap.get R r = HoonMap.get regs r := by
  intro r hr
  cases ton with
  | zero p =>
    simp only [afterCall, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2.1]; exact get_store_other hr
  | one b =>
    simp only [afterCall, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2.1]
  | two tr =>
    simp only [afterCall, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2.1]

theorem call_frame {st' : σ} {regs R : Map (Option Noun)} {t t' : Trace} {d : Nat} {ton : Tone}
    {x : Option (Tone × σ)}
    (h : x.bind (fun (p : Tone × σ) => afterCall p.2 regs t d p.1) = some (ton, R, t', st')) :
    ∀ r, r ≠ d → HoonMap.get R r = HoonMap.get regs r := by
  obtain ⟨⟨ton0, st0⟩, _, h2⟩ := Option.bind_eq_some_iff.mp h
  exact afterCall_frame h2

/-- **A local op changes only its destination.** -/
theorem localPole_frame (lib : Lib) (gul : Noun) {p : Pole} {regs R : Map (Option Noun)} {t t' : Trace}
    {ton : Tone} (h : localPole lib gul p regs t = some (ton, R, t')) :
    ∀ r, r ∉ poleWr p → HoonMap.get R r = HoonMap.get regs r := by
  intro r hr
  have one : ∀ {d : Nat}, poleWr p = [d] → r ≠ d := fun e h' => hr (by rw [e, h']; simp)
  cases p with
  | imm n d =>
    simp only [localPole, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2.1]; exact get_store_other (one rfl)
  | mov s d =>
    simp only [localPole, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨R0, h0, _, rfl, _⟩ := h
    exact get_move_other h0 (one rfl)
  | inc s d =>
    simp only [localPole, Option.bind_eq_some_iff] at h
    obtain ⟨v, _, h⟩ := h
    cases v with
    | cell _ _ => simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2.1]
    | atom a => simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2.1]; exact get_store_other (one rfl)
  | con a b d =>
    simp only [localPole, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, _, _, _, rfl, _⟩ := h
    exact get_store_other (one rfl)
  | hed s d =>
    simp only [localPole, Option.bind_eq_some_iff] at h
    obtain ⟨v, _, h⟩ := h
    cases v with
    | cell _ _ => simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2.1]; exact get_store_other (one rfl)
    | atom a => cases h
  | tal s d =>
    simp only [localPole, Option.bind_eq_some_iff] at h
    obtain ⟨v, _, h⟩ := h
    cases v with
    | cell _ _ => simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2.1]; exact get_store_other (one rfl)
    | atom a => cases h
  | cel q =>
    simp only [localPole, Option.bind_eq_some_iff] at h
    obtain ⟨v, _, h⟩ := h
    cases v <;> (simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2.1])
  | lob q =>
    simp only [localPole, Option.bind_eq_some_iff] at h
    obtain ⟨v, _, h⟩ := h
    split at h <;> (simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2.1])
  | equ a b =>
    simp only [localPole, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, _, _, _, rfl, _⟩ := h; rfl
  | hsp => simp only [localPole, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2.1]
  | hse => simp only [localPole, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2.1]
  | hdp n q f =>
    simp only [localPole] at h
    split at h
    · obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2.1]
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2.1]
  | hde n q f =>
    simp only [localPole] at h
    split at h
    · obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2.1]
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2.1]
  | hmp a v f =>
    simp only [localPole] at h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2.1]
  | hme a v f =>
    simp only [localPole] at h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2.1]
  | hcp => simp only [localPole, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2.1]
  | hce =>
    simp only [localPole] at h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2.1]
  | spy e q d =>
    simp only [localPole] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2.1]
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨_, _, _, _, _, _, dr, _, h⟩ := h
      cases dr with
      | block => simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2.1]
      | hunk => simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2.1]
      | val v => simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2.1]; exact get_store_other (one rfl)
  | _ => simp [localPole] at h

/-- **An op changes only its destination.** -/
theorem execPole_frame (lib : Lib) (O : Oracle σ) (gul : Noun) {st st' : σ} {p : Pole}
    {regs R : Map (Option Noun)} {t t' : Trace} {ton : Tone}
    (h : execPole lib O gul st p regs t = some (ton, R, t', st')) :
    ∀ r, r ∉ poleWr p → HoonMap.get R r = HoonMap.get regs r := by
  intro r hr
  have one : ∀ {d : Nat}, poleWr p = [d] → r ≠ d := fun e h' => hr (by rw [e, h']; simp)
  cases p with
  | nok u f d =>
    have hd := one rfl
    simp only [execPole, Option.bind_eq_some_iff] at h
    obtain ⟨vu, _, vf, _, ⟨ton0, st0⟩, _, h⟩ := h
    cases ton0 with
    | zero q => simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2.1]; exact get_store_other hd
    | one q => simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2.1]
    | two q => simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2.1]
  | cal a v d =>
    simp only [execPole, Option.bind_eq_some_iff] at h
    obtain ⟨vs, _, ⟨ton0, st0⟩, _, h⟩ := h
    exact afterCall_frame h r (one rfl)
  | caf a v d n =>
    simp only [execPole, Option.bind_eq_some_iff] at h
    obtain ⟨vs, _, ⟨ton0, st0⟩, _, h⟩ := h
    exact afterCall_frame h r (one rfl)
  | cam a v d k =>
    simp only [execPole, Option.bind_eq_some_iff] at h
    obtain ⟨vs, _, ⟨ton0, st0⟩, _, h⟩ := h
    exact afterCall_frame h r (one rfl)
  | csl a s d =>
    simp only [execPole, Option.bind_eq_some_iff] at h
    obtain ⟨vs, _, ⟨ton0, st0⟩, _, h⟩ := h
    exact afterCall_frame h r (one rfl)
  | csf a s d n =>
    simp only [execPole, Option.bind_eq_some_iff] at h
    obtain ⟨vs, _, ⟨ton0, st0⟩, _, h⟩ := h
    exact afterCall_frame h r (one rfl)
  | csm a s d k =>
    simp only [execPole, Option.bind_eq_some_iff] at h
    obtain ⟨vs, _, ⟨ton0, st0⟩, _, h⟩ := h
    exact afterCall_frame h r (one rfl)
  | _ =>
    simp only [execPole, Option.map_eq_some_iff] at h
    obtain ⟨⟨ton0, R0, t0⟩, hl, he⟩ := h
    simp only [Prod.mk.injEq] at he
    rw [← he.2.1]
    exact localPole_frame lib gul hl r hr

/-! ## Steps and paths -/

variable {lib : Lib} {O : Oracle σ} {c : Straight Map} {gul : Noun}

/-- **A step changes only the registers it writes.** -/
theorem step_frame {x y : Cfg σ Map} {e : List (Nat × Nat)} (h : Step lib O c gul x e y) :
    ∀ r, r ∉ stepWr x → HoonMap.get y.regs r = HoonMap.get x.regs r := by
  intro r hr
  cases h with
  | pass hne hR =>
    simp only [stepWr, if_pos hne] at hr
    exact evalPass_frame hR r hr
  | op hp hq hb hpole =>
    have hne : ¬ (x.params ≠ [] ∨ x.b.par ≠ []) := by simp [hp, hq]
    simp only [stepWr, if_neg hne, hb] at hr
    exact execPole_frame lib O gul hpole r hr
  | jump => rfl

/-- What the step writes, a block that writes only `Q` writes. -/
theorem stepWr_sub {Q : Nat → Prop} {x : Cfg σ Map} (hx : BlobWr Q x.b) : ∀ r ∈ stepWr x, Q r := by
  intro r hr
  unfold stepWr at hr
  split at hr
  · exact hx.1 r hr
  · split at hr
    · rename_i p rest hb
      exact hx.2 p (by rw [hb]; exact List.mem_cons_self) r hr
    · exact absurd hr List.not_mem_nil

/-- Every jump the terminator can take goes to a label of `L`. -/
def TakenIn (L : Nat → Prop) (f : Termin) : Prop :=
  ∀ (regs : Map (Option Noun)) (j : Jmp), taken regs f = some j → L j.there

/-- What a path keeps of a configuration: what is left of its block writes
only `Q` and jumps only into `L`. -/
def CfgIn (Q L : Nat → Prop) (x : Cfg σ Map) : Prop := BlobWr Q x.b ∧ TakenIn (Map := Map) L x.b.fin

/-- Every block of the program at a label of `L` writes only `Q` and jumps
only into `L`. -/
def ProgIn (Q L : Nat → Prop) (c : Straight Map) : Prop :=
  ∀ o b, L o → HoonMap.get c.blocks o = some b → BlobWr Q b ∧ TakenIn (Map := Map) L b.fin

theorem step_cfgIn {Q L : Nat → Prop} (hc : ProgIn Q L c) {x y : Cfg σ Map} {e : List (Nat × Nat)}
    (h : Step lib O c gul x e y) (hx : CfgIn Q L x) : CfgIn Q L y ∧ ∀ a ∈ e, L a.2 := by
  cases h with
  | pass =>
    exact ⟨⟨⟨fun _ hr => absurd hr List.not_mem_nil, hx.1.2⟩, hx.2⟩, fun a ha => absurd ha List.not_mem_nil⟩
  | op hp hq hb =>
    refine ⟨⟨⟨fun r hr => hx.1.1 r hr, fun p hp' => hx.1.2 p (by rw [hb]; exact List.mem_cons_of_mem _ hp')⟩, hx.2⟩,
      fun a ha => absurd ha List.not_mem_nil⟩
  | @jump j b' hp hq hb ht hb' =>
    have hl : L j.there := hx.2 _ _ ht
    refine ⟨hc _ _ hl hb', fun a ha => ?_⟩
    simp only [List.mem_singleton] at ha
    rw [ha]; exact hl

/-- **The frame lemma on paths**: if every block at a label of `L` writes only
registers of `Q` and jumps only into `L`, and so does what is left of the block
of `x`, then along every path from `x` the registers outside `Q` keep their
values (a value stays that value, poison stays poison), every label the path
enters is in `L`, and the end still writes only `Q` and jumps into `L`. -/
theorem steps_frame {Q L : Nat → Prop} (hc : ProgIn Q L c) {x y : Cfg σ Map} {es : List (Nat × Nat)}
    (h : Steps lib O c gul x es y) (hx : CfgIn Q L x) :
    (∀ r, ¬ Q r → HoonMap.get y.regs r = HoonMap.get x.regs r) ∧ CfgIn Q L y ∧ ∀ a ∈ es, L a.2 := by
  induction h with
  | refl => exact ⟨fun _ _ => rfl, hx, fun a ha => absurd ha List.not_mem_nil⟩
  | @step x z y e es s _ ih =>
    obtain ⟨hz, ez⟩ := step_cfgIn hc s hx
    obtain ⟨fy, hy, ey⟩ := ih hz
    refine ⟨fun r hr => (fy r hr).trans (step_frame s r fun hw => hr (stepWr_sub hx.1 r hw)), hy, fun a ha => ?_⟩
    rcases List.mem_append.mp ha with ha | ha
    · exact ez a ha
    · exact ey a ha

/-- The frame lemma with `read`. -/
theorem steps_frame_read {Q L : Nat → Prop} (hc : ProgIn Q L c) {x y : Cfg σ Map} {es : List (Nat × Nat)}
    (h : Steps lib O c gul x es y) (hx : CfgIn Q L x) :
    ∀ r, ¬ Q r → SkaModel.read r y.regs = SkaModel.read r x.regs := by
  intro r hr
  simp only [SkaModel.read, (steps_frame hc h hx).1 r hr]

/-- **The whole program**: if every block writes only `Q`, every path keeps
the registers outside `Q`. -/
theorem steps_frame_all {Q : Nat → Prop} (hc : ∀ o b, HoonMap.get c.blocks o = some b → BlobWr Q b)
    {x y : Cfg σ Map} {es : List (Nat × Nat)} (h : Steps lib O c gul x es y) (hx : BlobWr Q x.b) :
    ∀ r, ¬ Q r → HoonMap.get y.regs r = HoonMap.get x.regs r :=
  (steps_frame (L := fun _ => True) (fun o b _ hb => ⟨hc o b hb, fun _ _ _ => trivial⟩) h
    ⟨hx, fun _ _ _ => trivial⟩).1

/-! ## Runs -/

/-- **A run that returns follows a path that keeps the registers outside
`Q`**, through `run_iff_path`. -/
theorem run_frame {Q L : Nat → Prop} (hc : ProgIn Q L c) {x : Cfg σ Map} (hx : CfgIn Q L x) {r : Tone × σ}
    (h : Path.run lib O c gul x = some r) :
    ∃ es y, Steps lib O c gul x es y ∧ endOf lib O gul y = some r ∧
      (∀ k, ¬ Q k → HoonMap.get y.regs k = HoonMap.get x.regs k) ∧ (∀ a ∈ es, L a.2) := by
  obtain ⟨es, y, hs, he⟩ := (run_iff_path x r).mp h
  obtain ⟨f, _, l⟩ := steps_frame hc hs hx
  exact ⟨es, y, hs, he, f, l⟩

/-- **The same from the entry**, through `execEntry_iff_path`: the block `0`
must write only `Q` and jump into `L`. -/
theorem execEntry_frame {Q L : Nat → Prop} (hc : ProgIn Q L c) (h0 : L 0) {st : σ} {vals : List Noun} {t : Trace}
    {r : Tone × σ} (h : execEntry lib O st c vals t gul = some r) :
    ∃ es y, FromEntry (lib := lib) (O := O) (c := c) (gul := gul) st vals t es y ∧ endOf lib O gul y = some r ∧
      (∀ k, ¬ Q k → HoonMap.get y.regs k = HoonMap.get (regsOf vals : Map (Option Noun)) k) ∧ (∀ a ∈ es, L a.2) := by
  obtain ⟨es, y, ⟨b0, hb0, hs⟩, he⟩ := (execEntry_iff_path st vals t r).mp h
  obtain ⟨f, _, l⟩ := steps_frame hc hs (hc 0 b0 h0 hb0)
  exact ⟨es, y, ⟨b0, hb0, hs⟩, he, f, l⟩

/-- **A real read outside `Q` reads the start's value**: on a path of a run
that returns, a register outside `Q` that the path reads for real held a value
at the start, the value read.  So a register outside `Q` poisoned at the start
is never read for real. -/
theorem steps_reads_frame {Q L : Nat → Prop} (hc : ProgIn Q L c) {x z : Cfg σ Map} {es : List (Nat × Nat)}
    {r : Tone × σ} (hs : Steps lib O c gul x es z) (hx : CfgIn Q L x) (hr : Path.run lib O c gul x = some r)
    {k : Nat} (hq : ¬ Q k) (hk : ReadsAt gul z k) :
    ∃ v, SkaModel.read k x.regs = some v ∧ SkaModel.read k z.regs = some v := by
  obtain ⟨v, hv⟩ := steps_reads hs hr hk
  exact ⟨v, by rw [← steps_frame_read hc hs hx k hq]; exact hv, hv⟩

end Frame

end Comp
end SkaModel
end Formalization
