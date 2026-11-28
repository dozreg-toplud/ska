import lemmas.Ska.CompCallSem
import lemmas.Ska.CompDirectMMerge
import lemmas.Ska.CompRingCall

/-!
# What a call through a ring does: as the plain call (track K, README Gaps 19 (h))

**"No hot driver" in the interpreter model.**  The interpreter model (`Interp.lean`), like the
Hoon's `+eval-blob` / `+eval-pole` (lines 9809 to 9818, 9966 to 9991: `%jmf` is `$(fin.b [%jmp
a v]:fin.b)`, `%jsf` is `%jsp`, `%caf` is `%cal`, `%csf` is `%csl`), never runs a driver: the
four ring ops are the plain calls, with NO hypothesis.  A driver enters only on the compiler's
side, through `(biff rin ~(get by jets-hot))` in `+callee-need`, `b-sur` (lines 3971, 4466,
4609), `+inlined`'s `hot` (line 3323) and the entry case of `%full` (line 9693); with
`jets-hot` empty (an invariant at reached states: the only write is `%jets`'s `(malt p.ovo)`,
and `Reach` admits no `%jets` whose list is a cell; owner P) these read as with no ring.

* `eraseP`, `eraseT`, `eraseB`: a block with its ring ops replaced by the plain ones.
* `execPole_eraseP`, **`execBlob_eraseB`**: in one straight, a block runs as its erasure.
* **`execBlob_ringSim`**, **`execBlob_ringEq`**, **`execEntry_ringEq`**: two straights whose
  blocks have the same erasures run the same, from blocks with the same erasures (fixpoint
  induction on `execBlob`, both directions).  So every contract theorem of a straight `c0` holds
  of a straight `c` with `eraseB` of each block of `c` that of `c0`: the contract of the code
  the compiler emits through rings is that of the code it would emit without them, once the
  compiles are related (`RingEraseCompile`, stated in `CompRingContract.lean`).
* `goJ_caf_j`, `goJ_csf_j`, `goJ_jmf`, `goJ_jsf`: the call-block steps of track C / J
  (`goJ_cal_j`, `goJ_csl_j`, `goJ_jmp`, `goJ_jsp`) for the ring ops, from the same lemmas.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy Lean.Order

/-! ## Erasing the rings -/

/-- An op with its ring dropped: `%caf` is `%cal`, `%csf` is `%csl`. -/
def eraseP : Pole → Pole
  | Pole.caf a v d _ => Pole.cal a v d
  | Pole.csf a s d _ => Pole.csl a s d
  | p => p

/-- An end with its ring dropped: `%jmf` is `%jmp`, `%jsf` is `%jsp`. -/
def eraseT : Termin → Termin
  | Termin.jmf a v _ => Termin.jmp a v
  | Termin.jsf a s _ => Termin.jsp a s
  | t => t

/-- A block with its rings dropped. -/
def eraseB (b : Blob) : Blob := ⟨b.par, b.body.map eraseP, eraseT b.fin⟩

theorem eraseP_idem (p : Pole) : eraseP (eraseP p) = eraseP p := by cases p <;> rfl

theorem eraseT_idem (t : Termin) : eraseT (eraseT t) = eraseT t := by cases t <;> rfl

theorem eraseB_idem (b : Blob) : eraseB (eraseB b) = eraseB b := by
  have e : eraseP ∘ eraseP = eraseP := funext eraseP_idem
  simp only [eraseB, List.map_map, eraseT_idem, e]

/-- The ring ops of `callOpR` / `jumpOpR` erase to the plain ones. -/
theorem eraseP_callOpR (b : Bell) (rin : Option Noun) (pes : Option Nat) (subV : List Nat) (pro : Nat) :
    eraseP (callOpR b rin pes subV pro) = callOpR b Option.none pes subV pro := by
  rcases rin with _ | u <;> rcases pes with _ | s <;> rfl

theorem eraseT_jumpOpR (b : Bell) (rin : Option Noun) (pes : Option Nat) (subV : List Nat) :
    eraseT (jumpOpR b rin pes subV) = jumpOpR b Option.none pes subV := by
  rcases rin with _ | u <;> rcases pes with _ | s <;> rfl

/-- **The environment with no ring**: what the compile would read if `call.cole` were empty. -/
def CallEnv.noRing (env : CallEnv) : CallEnv := { env with ring := fun _ => Option.none }

variable {Map : Type → Type} [HoonMap Map]

section Exec
variable {lib : Lib} {σ : Type} {O : Oracle σ} {gul : Noun}

/-- **An op runs as its erasure.** -/
theorem execPole_eraseP (st : σ) (p : Pole) (regs : Map (Option Noun)) (t : Trace) :
    execPole lib O gul st (eraseP p) regs t = execPole lib O gul st p regs t := by
  cases p <;> rfl

/-- In one straight, a block with no parameters runs as its erasure. -/
theorem execBlob_eraseB0 (s : Straight Map) : ∀ (body : List Pole) (fin : Termin) (st : σ) (regs : Map (Option Noun))
    (t : Trace), execBlob lib O s gul st regs t ⟨[], body.map eraseP, eraseT fin⟩ [] =
      execBlob lib O s gul st regs t ⟨[], body, fin⟩ []
  | [], fin, st, regs, t => by
    rw [execBlob, execBlob]
    simp only [ne_eq, not_true_eq_false, or_self, if_false, List.map_nil]
    cases fin <;> rfl
  | p :: rest, fin, st, regs, t => by
    rw [List.map_cons, execBlob_cons, execBlob_cons, execPole_eraseP]
    cases execPole lib O gul st p regs t with
    | none => rfl
    | some x =>
      obtain ⟨ton, regs', t', st'⟩ := x
      cases ton with
      | zero _ => exact execBlob_eraseB0 s rest fin st' regs' t'
      | one _ => rfl
      | two _ => rfl

/-- **In one straight, a block runs as its erasure.** -/
theorem execBlob_eraseB (s : Straight Map) (st : σ) (regs : Map (Option Noun)) (t : Trace) (b : Blob)
    (params : List (Option Nat)) :
    execBlob lib O s gul st regs t (eraseB b) params = execBlob lib O s gul st regs t b params := by
  obtain ⟨par, body, fin⟩ := b
  by_cases hp : params ≠ [] ∨ par ≠ []
  · rw [execBlob, execBlob]
    simp only [eraseB, hp, if_true]
    cases evalPass params par regs with
    | none => rfl
    | some regs' => exact execBlob_eraseB0 s body fin st regs' t
  · simp only [not_or, ne_eq, Decidable.not_not] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact execBlob_eraseB0 s body fin st regs t

/-- Two straights whose blocks have the same erasures. -/
def RingSame (s1 s2 : Straight Map) : Prop :=
  ∀ k, (HoonMap.get s1.blocks k).map eraseB = (HoonMap.get s2.blocks k).map eraseB

theorem ringSame_symm {s1 s2 : Straight Map} (h : RingSame s1 s2) : RingSame s2 s1 := fun k => (h k).symm

/-- A hop: what `s1` finds at `k` and runs, `s2` runs from the block it finds at `k`. -/
private theorem hop_sim {s1 s2 : Straight Map} (hs : RingSame s1 s2)
    (f : σ → Map (Option Noun) → Trace → Blob → List (Option Nat) → Option (Tone × σ))
    (hf : ∀ st regs t b params r, f st regs t b params = some r →
      execBlob lib O s2 gul st regs t (eraseB b) params = some r)
    (st : σ) (regs : Map (Option Noun)) (t : Trace) (j : Jmp) (r : Tone × σ)
    (h : (HoonMap.get s1.blocks j.there >>= fun b' => f st regs t b' j.args) = some r) :
    (HoonMap.get s2.blocks j.there >>= fun b' => execBlob lib O s2 gul st regs t b' j.args) = some r := by
  have e := hs j.there
  cases h1 : HoonMap.get s1.blocks j.there with
  | none => rw [h1] at h; cases h
  | some b1 =>
    rw [h1] at h e
    cases h2 : HoonMap.get s2.blocks j.there with
    | none => rw [h2] at e; cases e
    | some b2 =>
      rw [h2] at e
      simp only [Option.map_some, Option.some.injEq] at e
      have := hf st regs t b1 j.args r h
      rw [e, execBlob_eraseB] at this
      exact this

/-- **The simulation**: what `s1` returns from `b`, `s2` returns from `eraseB b`, when the
blocks of the two have the same erasures. -/
theorem execBlob_ringSim {s1 s2 : Straight Map} (hs : RingSame s1 s2) :
    ∀ (st : σ) (regs : Map (Option Noun)) (t : Trace) (b : Blob) (params : List (Option Nat)) (r : Tone × σ),
      execBlob lib O s1 gul st regs t b params = some r → execBlob lib O s2 gul st regs t (eraseB b) params = some r := by
  refine execBlob.fixpoint_induct lib O s1 gul
    (fun f => ∀ st regs t b params r, f st regs t b params = some r →
      execBlob lib O s2 gul st regs t (eraseB b) params = some r) ?_ ?_
  · exact admissible_pi_apply _ fun st => admissible_pi_apply _ fun regs => admissible_pi_apply _ fun t =>
      admissible_pi_apply _ fun b => admissible_pi_apply _ fun params => admissible_pi _ fun r =>
        Option.admissible_eq_some _ r
  · intro f hf st regs t b params r h
    obtain ⟨par, body, fin⟩ := b
    rw [execBlob]
    by_cases hp : params ≠ [] ∨ par ≠ []
    · simp only [eraseB, hp, if_true] at h ⊢
      cases e : evalPass params par regs with
      | none => rw [e] at h; cases h
      | some regs' =>
        rw [e] at h
        exact hf st regs' t _ [] r h
    · simp only [eraseB, hp, if_false] at h ⊢
      cases body with
      | cons p rest =>
        simp only [List.map_cons] at h ⊢
        rw [execPole_eraseP]
        cases e : execPole lib O gul st p regs t with
        | none => rw [e] at h; cases h
        | some x =>
          rw [e] at h
          obtain ⟨ton, regs', t', st'⟩ := x
          cases ton with
          | zero _ => exact hf st' regs' t' ⟨par, rest, fin⟩ [] r h
          | one _ => exact h
          | two _ => exact h
      | nil =>
        simp only [List.map_nil] at h ⊢
        cases fin with
        | lti n x z o =>
          simp only [eraseT] at h ⊢
          cases e : SkaModel.read x regs with
          | none => rw [e] at h; cases h
          | some v => rw [e] at h; exact hop_sim hs f hf st regs t _ r h
        | clq x z o =>
          simp only [eraseT] at h ⊢
          cases e : SkaModel.read x regs with
          | none => rw [e] at h; cases h
          | some v => rw [e] at h; exact hop_sim hs f hf st regs t _ r h
        | eqq l x z o =>
          simp only [eraseT] at h ⊢
          cases e : SkaModel.read l regs with
          | none => rw [e] at h; cases h
          | some v =>
            rw [e] at h
            cases e' : SkaModel.read x regs with
            | none => rw [e'] at h; cases h
            | some w => rw [e'] at h; exact hop_sim hs f hf st regs t _ r h
        | brn x z o =>
          simp only [eraseT] at h ⊢
          cases e : SkaModel.read x regs with
          | none => rw [e] at h; cases h
          | some v =>
            rw [e] at h
            dsimp only [bind, Option.bind] at h ⊢
            split at h
            · rw [if_pos (by assumption)]; exact hop_sim hs f hf st regs t z r h
            · rw [if_neg (by assumption)]
              split at h
              · rw [if_pos (by assumption)]; exact hop_sim hs f hf st regs t o r h
              · rw [if_neg (by assumption)]; exact h
        | brz x z o =>
          simp only [eraseT] at h ⊢
          cases e : SkaModel.read x regs with
          | none => rw [e] at h; cases h
          | some v => rw [e] at h; exact hop_sim hs f hf st regs t _ r h
        | hop j => exact hop_sim hs f hf st regs t j r h
        | jmp a v => exact h
        | jmf a v n => exact h
        | jsp a x => exact h
        | jsf a x n => exact h
        | don x => exact h
        | bom o => exact h

/-- **Two straights whose blocks have the same erasures run the same**, from blocks with the
same erasures. -/
theorem execBlob_ringEq {s1 s2 : Straight Map} (hs : RingSame s1 s2) (st : σ) (regs : Map (Option Noun))
    (t : Trace) {b1 b2 : Blob} (hb : eraseB b1 = eraseB b2) (params : List (Option Nat)) :
    execBlob lib O s1 gul st regs t b1 params = execBlob lib O s2 gul st regs t b2 params := by
  have d1 : ∀ r, execBlob lib O s1 gul st regs t b1 params = some r → execBlob lib O s2 gul st regs t b2 params = some r :=
    fun r h => by
      have := execBlob_ringSim hs st regs t b1 params r h
      rwa [hb, execBlob_eraseB] at this
  have d2 : ∀ r, execBlob lib O s2 gul st regs t b2 params = some r → execBlob lib O s1 gul st regs t b1 params = some r :=
    fun r h => by
      have := execBlob_ringSim (ringSame_symm hs) st regs t b2 params r h
      rwa [← hb, execBlob_eraseB] at this
  cases e1 : execBlob lib O s1 gul st regs t b1 params with
  | some r => exact (d1 r e1).symm
  | none =>
    cases e2 : execBlob lib O s2 gul st regs t b2 params with
    | none => rfl
    | some r => rw [d2 r e2] at e1; cases e1

/-- **Entering two straights whose blocks have the same erasures gives the same result.** -/
theorem execEntry_ringEq {s1 s2 : Straight Map} (hs : RingSame s1 s2) (st : σ) (vals : List Noun) (t : Trace) :
    execEntry lib O st s1 vals t gul = execEntry lib O st s2 vals t gul := by
  unfold execEntry
  have e := hs 0
  cases h1 : HoonMap.get s1.blocks 0 with
  | none =>
    rw [h1] at e
    cases h2 : HoonMap.get s2.blocks 0 with
    | none => rfl
    | some _ => rw [h2] at e; cases e
  | some b1 =>
    rw [h1] at e
    cases h2 : HoonMap.get s2.blocks 0 with
    | none => rw [h2] at e; cases e
    | some b2 =>
      rw [h2] at e
      simp only [Option.map_some, Option.some.injEq] at e
      exact execBlob_ringEq hs st _ t e []

/-! ## The call blocks of a ring call -/

variable {c : Straight Map}

/-- **A `%caf` block hopping to any jump**: as `%cal` (`goJ_cal_j`). -/
theorem goJ_caf_j {o pro : Nat} {b : Bell} {subV : List Nat} {j : Jmp} {n : Ring}
    (hb : HoonMap.get c.blocks o = some ⟨[], [Pole.caf b subV pro n], Termin.hop j⟩)
    (st : σ) (regs : Map (Option Noun)) (t : Trace) {vs : List Noun}
    (hvs : subV.mapM (fun r => SkaModel.read r regs) = some vs) :
    goJ lib O c gul st regs t (jmp0 o) = (O.call st b false vs t gul).bind fun (ton, st') =>
      match ton with
      | Tone.zero p => goJ lib O c gul st' (store pro p regs) t j
      | ton => some (ton, st') := by
  rw [goJ_jmp0 _ _ _ _ hb, execBlob_cons]
  simp only [execPole]
  rw [show (subV.mapM (SkaModel.read · regs)) = some vs from hvs, Option.bind_some]
  cases O.call st b false vs t gul with
  | none => rfl
  | some x =>
    obtain ⟨ton, st'⟩ := x
    cases ton <;> simp [afterCall, execBlob_hop]

/-- **A `%csf` block hopping to any jump**: as `%csl` (`goJ_csl_j`). -/
theorem goJ_csf_j {o r pro : Nat} {b : Bell} {j : Jmp} {n : Ring}
    (hb : HoonMap.get c.blocks o = some ⟨[], [Pole.csf b r pro n], Termin.hop j⟩)
    (st : σ) (regs : Map (Option Noun)) (t : Trace) {v : Noun} (hv : SkaModel.read r regs = some v) :
    goJ lib O c gul st regs t (jmp0 o) = (O.call st b true [v] t gul).bind fun (ton, st') =>
      match ton with
      | Tone.zero p => goJ lib O c gul st' (store pro p regs) t j
      | ton => some (ton, st') := by
  rw [goJ_jmp0 _ _ _ _ hb, execBlob_cons]
  simp only [execPole]
  rw [show SkaModel.read r regs = some v from hv, Option.bind_some]
  cases O.call st b true [v] t gul with
  | none => rfl
  | some x =>
    obtain ⟨ton, st'⟩ := x
    cases ton <;> simp [afterCall, execBlob_hop]

/-- **The tail call through a ring** (`%jmf`): as `%jmp` (`goJ_jmp`). -/
theorem goJ_jmf {o : Nat} {b : Bell} {subV : List Nat} {n : Ring}
    (hb : HoonMap.get c.blocks o = some ⟨[], [], Termin.jmf b subV n⟩)
    (st : σ) (regs : Map (Option Noun)) (t : Trace) {vs : List Noun}
    (hvs : subV.mapM (fun r => SkaModel.read r regs) = some vs) :
    goJ lib O c gul st regs t (jmp0 o) = O.call st b false vs t gul := by
  rw [goJ_jmp0 _ _ _ _ hb, execBlob]
  simp only [ne_eq, not_true_eq_false, or_self, if_false]
  rw [show (subV.mapM (SkaModel.read · regs)) = some vs from hvs]
  rfl

/-- **The tail call by subject through a ring** (`%jsf`): as `%jsp`. -/
theorem goJ_jsf {o r : Nat} {b : Bell} {n : Ring}
    (hb : HoonMap.get c.blocks o = some ⟨[], [], Termin.jsf b r n⟩)
    (st : σ) (regs : Map (Option Noun)) (t : Trace) {v : Noun} (hv : SkaModel.read r regs = some v) :
    goJ lib O c gul st regs t (jmp0 o) = O.call st b true [v] t gul := by
  rw [goJ_jmp0 _ _ _ _ hb, execBlob]
  simp only [ne_eq, not_true_eq_false, or_self, if_false]
  rw [show SkaModel.read r regs = some v from hv]
  rfl

end Exec

end Comp
end SkaModel
end Formalization
