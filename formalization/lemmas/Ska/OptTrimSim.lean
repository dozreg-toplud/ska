import lemmas.Ska.OptTrimWalk
import lemmas.Ska.ExecPath

/-!
# `+trim-trace-hints` keeps the code, under `TrimBr`

The dropped keys `TDrop uns opened`: not unsafe and opened.  The code after
runs every block with the hint ops of dropped keys taken out of its body.

**The relation on traces** (`TrR D g t t'`, for the bracketed stack `g` of
the frames this function pushed, top first): `t` is `t'` with the frames of
dropped keys inserted.  Read from the top of `g`, a frame of a key that is
not dropped, or a frame without key (`none`, a `%hunk`, `%hand`, `%lose`
hint), is on top of both traces; a frame of a dropped key is on top of `t`
alone; below `g` both traces are the same (the caller's trace).  When no key
of `g` is dropped, `t = t'` (`TrR.eq`).

**What reads the trace.**  An op that may crash (`notCrashing` false and no
key: `%inc`, `%cel`, `%lob`, `%spy`, `%nok`, the calls) puts the trace in a
`%2` or hands it to a callee; at such an op every key with a frame on the
stack is unsafe (`SafeAt`, from the walk), so no frame of a dropped key is
there and the traces are equal.  The same holds at an end that is not
`%clq`, `%eqq`, `%brz`, `%hop` (a `%bom`, a `%brn` on a non-loobean, a tail
call; `%don` is checked too though it does not read the trace).  A kept
hint op pushes the same frame on both traces (the registers are equal) or
pops the frame on top of both (`TrR.inv_keep`: the bracketing puts the
key's own frame on top of the stack).  The other ops (`%imm`, `%mov`,
`%con`, `%hed`, `%tal`, `%hsp`, `%hse`, `%equ`, a `%hdp` of a tag that
`stopTag` drops) pass the trace through.  So the tone, the registers and the
state are equal at every op (`kept_pole`).

**The dropped ops** (`drop_pole`): a push of a dropped key reads registers
that `ReadsOK` says hold values and puts a frame on the trace before alone;
a pop of a dropped key takes the frame on top of the trace before, which is
that key's (`TrR.inv_drop`).  Neither crashes.

**The simulation** (`TrimI`): the same label, parameters, registers and
state, the body after the body before filtered, the body before a suffix of
the block's body whose prefix has the bracketed stack `gm`, and `TrR` of
`gm` between the traces.  A step before is a step after or, for a dropped op,
none; backward, the code before first runs the dropped ops at its head
(`trim_norm`), as in `dead_keeps`.

**`trim_keeps`**: `+trim-trace-hints` keeps the code (`Keeps`), on a `topo`
with `TopoOK`, a `rev` that lists every member of `topo` jumping to a block
(`TopoInv`, so `rev = revCfg` in particular), and `TrimBr`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock Path

variable {Map : Type → Type} [HoonMap Map]

/-! ## Traces -/

/-- **The relation on traces**: `t` is `t'` with the frames of dropped keys
of `g` inserted. -/
inductive TrR (D : TKey → Prop) : List (Option TKey) → Trace → Trace → Prop
  | nil (t : Trace) : TrR D [] t t
  | keep {e : Option TKey} {g : List (Option TKey)} {t t' : Trace} (f : Frame) :
      (∀ k, e = some k → ¬ D k) → TrR D g t t' → TrR D (e :: g) (f :: t) (f :: t')
  | drop {k : TKey} {g : List (Option TKey)} {t t' : Trace} (f : Frame) :
      D k → TrR D g t t' → TrR D (some k :: g) (f :: t) t'

theorem TrR.eq {D : TKey → Prop} : ∀ {g : List (Option TKey)} {t t' : Trace}, TrR D g t t' →
    (∀ k, some k ∈ g → ¬ D k) → t = t'
  | _, _, _, TrR.nil _, _ => rfl
  | _, _, _, TrR.keep f _ h, hg => by
    rw [h.eq fun k hk => hg k (List.mem_cons_of_mem _ hk)]
  | _, _, _, TrR.drop (k := k) _ hd _, hg => absurd hd (hg k List.mem_cons_self)

theorem TrR.inv_keep {D : TKey → Prop} {e : Option TKey} {g : List (Option TKey)} {t t' : Trace}
    (h : TrR D (e :: g) t t') (he : ∀ k, e = some k → ¬ D k) :
    ∃ f t1 t1', t = f :: t1 ∧ t' = f :: t1' ∧ TrR D g t1 t1' := by
  cases h with
  | keep f _ h => exact ⟨f, _, _, rfl, rfl, h⟩
  | drop f hd _ => exact absurd hd (he _ rfl)

theorem TrR.inv_drop {D : TKey → Prop} {k : TKey} {g : List (Option TKey)} {t t' : Trace}
    (h : TrR D (some k :: g) t t') (hd : D k) : ∃ f t1, t = f :: t1 ∧ TrR D g t1 t' := by
  cases h with
  | keep f he _ => exact absurd hd (he k rfl)
  | drop f _ h => exact ⟨f, _, rfl, h⟩

/-! ## One op -/

section
variable {σ : Type}

/-- The results of an op on the two traces: both crash, or the same tone,
registers and state, with `TrR` of `g` between the traces after a `%0`. -/
def TAg (D : TKey → Prop) (g : List (Option TKey)) :
    Option (Tone × Map (Option Noun) × Trace × σ) → Option (Tone × Map (Option Noun) × Trace × σ) → Prop
  | none, none => True
  | some (ton, R, t, s), some (ton', R', t', s') => ton = ton' ∧ R = R' ∧ s = s' ∧ (∀ n, ton = Tone.zero n → TrR D g t t')
  | _, _ => False

theorem TAg.fwd {D : TKey → Prop} {g : List (Option TKey)} {r r' : Option (Tone × Map (Option Noun) × Trace × σ)}
    (h : TAg D g r r') {ton : Tone} {R : Map (Option Noun)} {t : Trace} {s : σ} (hr : r = some (ton, R, t, s)) :
    ∃ t', r' = some (ton, R, t', s) ∧ (∀ n, ton = Tone.zero n → TrR D g t t') := by
  subst hr
  match r', h with
  | some (ton', R', t', s'), h =>
    obtain ⟨rfl, rfl, rfl, h⟩ := h
    exact ⟨t', rfl, h⟩

theorem TAg.bwd {D : TKey → Prop} {g : List (Option TKey)} {r r' : Option (Tone × Map (Option Noun) × Trace × σ)}
    (h : TAg D g r r') {ton : Tone} {R : Map (Option Noun)} {t' : Trace} {s : σ} (hr : r' = some (ton, R, t', s)) :
    ∃ t, r = some (ton, R, t, s) ∧ (∀ n, ton = Tone.zero n → TrR D g t t') := by
  subst hr
  rcases r with _ | ⟨ton', R', t, s'⟩
  · exact h.elim
  · obtain ⟨rfl, rfl, rfl, h⟩ := h
    exact ⟨t, rfl, h⟩

theorem TAg.isSome {D : TKey → Prop} {g : List (Option TKey)} {r r' : Option (Tone × Map (Option Noun) × Trace × σ)}
    (h : TAg D g r r') : r'.isSome = r.isSome := by
  match r, r', h with
  | none, none, _ => rfl
  | some _, some _, _ => rfl

/-- A `%0` of an op without a frame leaves the trace as it was. -/
theorem zero_trace {lib : Lib} {O : Oracle σ} {gul : Noun} {st : σ} {op : Pole} {R R2 : Map (Option Noun)}
    {t t2 : Trace} {st2 : σ} {n : Noun} {g : List (Option TKey)} (he : traceKey op = none) (hb : brOp g op = some g)
    (h : execPole lib O gul st op R t = some (Tone.zero n, R2, t2, st2)) : t2 = t := by
  cases op with
  | nok u f d =>
    simp only [execPole, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, _, _, ⟨ton, s⟩, _, h⟩ := h
    cases ton <;> simp at h
    first | exact h.2.2.1.symm | exact h.2.1.symm | exact h.2.2.1 | exact h.2.1
  | cal a v d =>
    simp only [execPole, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, ⟨ton, s⟩, _, h⟩ := h
    cases ton <;> simp [afterCall] at h
    first | exact h.2.2.1.symm | exact h.2.1.symm | exact h.2.2.1 | exact h.2.1
  | caf a v d _ =>
    simp only [execPole, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, ⟨ton, s⟩, _, h⟩ := h
    cases ton <;> simp [afterCall] at h
    first | exact h.2.2.1.symm | exact h.2.1.symm | exact h.2.2.1 | exact h.2.1
  | cam a v d _ =>
    simp only [execPole, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, ⟨ton, s⟩, _, h⟩ := h
    cases ton <;> simp [afterCall] at h
    first | exact h.2.2.1.symm | exact h.2.1.symm | exact h.2.2.1 | exact h.2.1
  | csl a v d =>
    simp only [execPole, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, ⟨ton, s⟩, _, h⟩ := h
    cases ton <;> simp [afterCall] at h
    first | exact h.2.2.1.symm | exact h.2.1.symm | exact h.2.2.1 | exact h.2.1
  | csf a v d _ =>
    simp only [execPole, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, ⟨ton, s⟩, _, h⟩ := h
    cases ton <;> simp [afterCall] at h
    first | exact h.2.2.1.symm | exact h.2.1.symm | exact h.2.2.1 | exact h.2.1
  | csm a v d _ =>
    simp only [execPole, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, ⟨ton, s⟩, _, h⟩ := h
    cases ton <;> simp [afterCall] at h
    first | exact h.2.2.1.symm | exact h.2.1.symm | exact h.2.2.1 | exact h.2.1
  | hdp n p f =>
    simp only [traceKey] at he
    split at he
    · cases he
    · simp only [brOp, traceKey] at hb
      rw [if_neg (by assumption)] at hb
      simp only at hb
      split at hb
      · simp at hb
      · rename_i hs
        simp [execPole, localPole, hs] at h
        first | exact h.2.2.1.symm | exact h.2.1.symm | exact h.2.2.1 | exact h.2.1
  | hde n p f =>
    simp only [traceKey] at he
    split at he
    · cases he
    · simp only [brOp, traceKey] at hb
      rw [if_neg (by assumption)] at hb
      simp only at hb
      split at hb
      · split at hb <;> simp_all
      · rename_i hs
        simp [execPole, localPole, hs] at h
        first | exact h.2.2.1.symm | exact h.2.1.symm | exact h.2.2.1 | exact h.2.1
  | hmp => simp [traceKey] at he
  | hme => simp [traceKey] at he
  | hcp => simp [traceKey] at he
  | hce => simp [traceKey] at he
  | spy e p d =>
    simp only [execPole, localPole, Option.map_eq_some_iff] at h
    obtain ⟨⟨ton, R', t'⟩, h, h'⟩ := h
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h'
    split at h
    · simp at h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨_, _, _, _, _, _, dr, _, h⟩ := h
      cases dr <;> simp at h
      exact h.2.2.symm
  | _ =>
    simp only [execPole, localPole, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ton, R', t'⟩, h, h'⟩ := h
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h'
    first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.2.symm)
    | (obtain ⟨_, _, h⟩ := h; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.2.symm)
    | (obtain ⟨v, _, h⟩ := h; cases v <;> simp at h <;> exact h.2.2.symm)
    | (obtain ⟨v, _, h⟩ := h; split at h <;> simp at h; exact h.2.2.symm)
    | (obtain ⟨_, _, _, _, h⟩ := h; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.2.symm)

theorem tag_refl {D : TKey → Prop} {g : List (Option TKey)} {t : Trace} {r : Option (Tone × Map (Option Noun) × Trace × σ)}
    (hr : TrR D g t t) (h : ∀ ton R2 t2 s2 n, r = some (ton, R2, t2, s2) → ton = Tone.zero n → t2 = t) : TAg D g r r := by
  rcases r with _ | ⟨ton, R2, t2, s2⟩
  · trivial
  · exact ⟨rfl, rfl, rfl, fun n hn => by rw [h ton R2 t2 s2 n rfl hn]; exact hr⟩

theorem brOp_push {op : Pole} {k : TKey} {g g1 : List (Option TKey)} (he : traceKey op = some (true, k))
    (hb : brOp g op = some g1) : g1 = some k :: g := by
  unfold brOp at hb; rw [he] at hb; simp only [Option.some.injEq] at hb; exact hb.symm

theorem brOp_pop {op : Pole} {k : TKey} {g g1 : List (Option TKey)} (he : traceKey op = some (false, k))
    (hb : brOp g op = some g1) : g = some k :: g1 := by
  unfold brOp at hb; rw [he] at hb; simp only at hb
  rcases g with _ | ⟨_ | k', g0⟩
  · cases hb
  · cases hb
  · simp only at hb
    split at hb
    · cases hb; subst_vars; rfl
    · cases hb

theorem stopTag_of {n : Nat} (hn : n = Tag.spot ∨ n = Tag.mean) : stopTag n = true := by
  rcases hn with h | h <;> (rw [h]; decide)

/-- A push of a key puts one frame on the trace and changes nothing else. -/
theorem push_exec {lib : Lib} {O : Oracle σ} {gul : Noun} {st : σ} {op : Pole} {R R2 : Map (Option Noun)}
    {t t2 : Trace} {st2 : σ} {ton : Tone} {k : TKey} (he : traceKey op = some (true, k))
    (h : execPole lib O gul st op R t = some (ton, R2, t2, st2)) :
    ton = Tone.zero (A 0) ∧ R2 = R ∧ st2 = st ∧ ∃ f, t2 = f :: t := by
  cases op with
  | hdp n p f =>
    simp only [traceKey] at he
    split at he
    · rename_i hn
      simp only [execPole, localPole, stopTag_of hn, if_true, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
      obtain ⟨_, ⟨v, _, h⟩, h'⟩ := h
      simp only [Option.some.injEq] at h; subst h
      simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h'
      exact ⟨rfl, rfl, rfl, _, rfl⟩
    · cases he
  | hmp a v f =>
    simp only [execPole, localPole, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
    obtain ⟨_, ⟨vs, _, h⟩, h'⟩ := h
    simp only [Option.some.injEq] at h; subst h
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h'
    exact ⟨rfl, rfl, rfl, _, rfl⟩
  | hcp n f =>
    simp only [execPole, localPole, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, _, rfl⟩
  | hde n p f => simp only [traceKey] at he; split at he <;> simp at he
  | hme => simp [traceKey] at he
  | hce => simp [traceKey] at he
  | _ => simp [traceKey] at he

/-- A pop of a key pops the trace and changes nothing else. -/
theorem pop_exec {lib : Lib} {O : Oracle σ} {gul : Noun} {st : σ} {op : Pole} {R R2 : Map (Option Noun)}
    {t t2 : Trace} {st2 : σ} {ton : Tone} {k : TKey} (he : traceKey op = some (false, k))
    (h : execPole lib O gul st op R t = some (ton, R2, t2, st2)) :
    ton = Tone.zero (A 0) ∧ R2 = R ∧ st2 = st ∧ popTrace t = some t2 := by
  have pop : ∀ {x : Option Trace}, (x.bind fun t => some (Tone.zero (A 0), R, t)).map
      (fun x => (x.1, x.2.1, x.2.2, st)) = some (ton, R2, t2, st2) →
      ton = Tone.zero (A 0) ∧ R2 = R ∧ st2 = st ∧ x = some t2 := by
    intro x h
    rcases x with _ | t1
    · cases h
    · simp only [Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨rfl, rfl, rfl, rfl⟩
  cases op with
  | hde n p f =>
    simp only [traceKey] at he
    split at he
    · rename_i hn
      simp only [execPole, localPole, stopTag_of hn, if_true] at h
      exact pop h
    · cases he
  | hme a v f => simp only [execPole, localPole] at h; exact pop h
  | hce n f => simp only [execPole, localPole] at h; exact pop h
  | hdp n p f => simp only [traceKey] at he; split at he <;> simp at he
  | hmp => simp [traceKey] at he
  | hcp => simp [traceKey] at he
  | _ => simp [traceKey] at he

/-- **A dropped op** steps the code before alone, with `TrR` kept. -/
theorem drop_pole {lib : Lib} {O : Oracle σ} {gul : Noun} {st : σ} {op : Pole} {R R2 : Map (Option Noun)}
    {D : TKey → Prop} {gm g1 : List (Option TKey)} {t t' t2 : Trace} {st2 : σ} {ton : Tone} {b : Bool} {k : TKey}
    (hr : TrR D gm t t') (hb : brOp gm op = some g1) (he : traceKey op = some (b, k)) (hd : D k)
    (h : execPole lib O gul st op R t = some (ton, R2, t2, st2)) :
    ton = Tone.zero (A 0) ∧ R2 = R ∧ st2 = st ∧ TrR D g1 t2 t' := by
  cases b with
  | true =>
    obtain ⟨h1, h2, h3, f, rfl⟩ := push_exec he h
    rw [brOp_push he hb]
    exact ⟨h1, h2, h3, TrR.drop f hd hr⟩
  | false =>
    obtain ⟨h1, h2, h3, hp⟩ := pop_exec he h
    rw [brOp_pop he hb] at hr
    obtain ⟨f, t1, rfl, h4⟩ := hr.inv_drop hd
    simp only [popTrace, Option.some.injEq] at hp
    subst hp
    exact ⟨h1, h2, h3, h4⟩

/-- **A dropped op does not crash**: its reads hold values and a pop finds a
frame. -/
theorem drop_isSome {lib : Lib} {O : Oracle σ} {gul : Noun} {st : σ} {op : Pole} {R : Map (Option Noun)}
    {D : TKey → Prop} {gm g1 : List (Option TKey)} {t t' : Trace} {b : Bool} {k : TKey}
    (hr : TrR D gm t t') (hb : brOp gm op = some g1) (he : traceKey op = some (b, k)) (hd : D k)
    (hrd : ∀ r ∈ poleReads gul op, ∃ v, read r R = some v) : (execPole lib O gul st op R t).isSome := by
  have hne : b = false → ∃ f t1, t = f :: t1 := by
    intro hb0; subst hb0
    rw [brOp_pop he hb] at hr
    obtain ⟨f, t1, rfl, -⟩ := hr.inv_drop hd
    exact ⟨f, t1, rfl⟩
  cases op with
  | hdp n p f =>
    simp only [traceKey] at he
    split at he
    · rename_i hn
      obtain ⟨v, hv⟩ := hrd p (by simp [poleReads, stopTag_of hn])
      simp [execPole, localPole, stopTag_of hn, hv]
    · cases he
  | hde n p f =>
    simp only [traceKey] at he
    split at he
    · rename_i hn
      simp only [Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨f', t1, rfl⟩ := hne he.1.symm
      simp [execPole, localPole, stopTag_of hn, popTrace]
    · cases he
  | hmp a v f =>
    have : ∃ vs, v.mapM (read · R) = some vs := by
      have key : ∀ l : List Nat, (∀ r ∈ l, ∃ v, read r R = some v) → ∃ vs, l.mapM (read · R) = some vs := by
        intro l; induction l with
        | nil => intro _; exact ⟨[], rfl⟩
        | cons a l ih =>
          intro hl
          obtain ⟨va, hva⟩ := hl a List.mem_cons_self
          obtain ⟨vs, hvs⟩ := ih fun r hr => hl r (List.mem_cons_of_mem _ hr)
          exact ⟨va :: vs, by simp [List.mapM_cons, hva, hvs]⟩
      exact key v (fun r hr => hrd r (by simpa [poleReads] using hr))
    obtain ⟨vs, hvs⟩ := this
    simp [execPole, localPole, hvs]
  | hme a v f =>
    simp only [traceKey, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨f', t1, rfl⟩ := hne he.1.symm
    simp [execPole, localPole, popTrace]
  | hcp n f => simp [execPole, localPole]
  | hce n f =>
    simp only [traceKey, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨f', t1, rfl⟩ := hne he.1.symm
    simp [execPole, localPole, popTrace]
  | _ => simp [traceKey] at he

/-- **A kept op** gives the same tone, registers and state on the two
traces, with `TrR` kept: a hint op of a kept key pushes the same frame on
both or pops the top of both, an op that may crash sees equal traces (`hc`),
the others pass the trace through. -/
theorem kept_pole {lib : Lib} {O : Oracle σ} {gul : Noun} {st : σ} {op : Pole} {R : Map (Option Noun)}
    {D : TKey → Prop} {gm g1 : List (Option TKey)} {t t' : Trace} (hr : TrR D gm t t') (hb : brOp gm op = some g1)
    (hk : ∀ b k, traceKey op = some (b, k) → ¬ D k) (hc : traceKey op = none → notCrashing op = false → t = t') :
    TAg D g1 (execPole lib O gul st op R t) (execPole lib O gul st op R t') := by
  have crash : traceKey op = none → notCrashing op = false → brOp gm op = some gm →
      TAg D g1 (execPole lib O gul st op R t) (execPole lib O gul st op R t') := by
    intro he hn hg
    have htt := hc he hn
    subst htt
    rw [hb, Option.some.injEq] at hg
    subst hg
    exact tag_refl hr fun ton R2 t2 s2 n h hz => by subst hz; exact zero_trace he hb h
  have push : ∀ k (f : Frame), traceKey op = some (true, k) →
      execPole lib O gul st op R t = (execPole lib O gul st op R []).map (fun x => (x.1, x.2.1, f :: t, x.2.2.2)) →
      execPole lib O gul st op R t' = (execPole lib O gul st op R []).map (fun x => (x.1, x.2.1, f :: t', x.2.2.2)) →
      TAg D g1 (execPole lib O gul st op R t) (execPole lib O gul st op R t') := by
    intro k f he h1 h2
    rw [h1, h2, brOp_push he hb] at *
    rcases execPole lib O gul st op R [] with _ | ⟨a, b, c, d⟩
    · trivial
    · exact ⟨rfl, rfl, rfl, fun _ _ => TrR.keep f (fun k' e => by cases e; exact hk true k he) hr⟩
  have pop : ∀ k, traceKey op = some (false, k) →
      (∀ u : Trace, execPole lib O gul st op R u = (popTrace u).map (fun u1 => (Tone.zero (A 0), R, u1, st))) →
      TAg D g1 (execPole lib O gul st op R t) (execPole lib O gul st op R t') := by
    intro k he h
    rw [brOp_pop he hb] at hr
    obtain ⟨f, t1, t1', rfl, rfl, h1⟩ := hr.inv_keep (fun k' e => by cases e; exact hk false k he)
    rw [h, h]
    exact ⟨rfl, rfl, rfl, fun _ _ => h1⟩
  cases op with
  | imm n d =>
    simp only [brOp, traceKey, Option.some.injEq] at hb; subst hb
    exact ⟨rfl, rfl, rfl, fun _ _ => hr⟩
  | mov a d =>
    simp only [brOp, traceKey, Option.some.injEq] at hb; subst hb
    simp only [execPole, localPole]
    cases move a d R <;> simp [TAg, hr]
  | con a b d =>
    simp only [brOp, traceKey, Option.some.injEq] at hb; subst hb
    simp only [execPole, localPole]
    cases read a R <;> cases read b R <;> simp [TAg, hr]
  | hed a d =>
    simp only [brOp, traceKey, Option.some.injEq] at hb; subst hb
    simp only [execPole, localPole]
    cases ea : read a R with
    | none => simp [TAg]
    | some v => cases v <;> simp [TAg, hr]
  | tal a d =>
    simp only [brOp, traceKey, Option.some.injEq] at hb; subst hb
    simp only [execPole, localPole]
    cases ea : read a R with
    | none => simp [TAg]
    | some v => cases v <;> simp [TAg, hr]
  | equ a b =>
    simp only [brOp, traceKey, Option.some.injEq] at hb; subst hb
    simp only [execPole, localPole]
    cases read a R <;> cases read b R <;> simp [TAg, hr]
  | hsp a b =>
    simp only [brOp, traceKey, Option.some.injEq] at hb; subst hb
    exact ⟨rfl, rfl, rfl, fun _ _ => hr⟩
  | hse a b =>
    simp only [brOp, traceKey, Option.some.injEq] at hb; subst hb
    exact ⟨rfl, rfl, rfl, fun _ _ => hr⟩
  | hdp n p f =>
    by_cases hn : n = Tag.spot ∨ n = Tag.mean
    · have he : traceKey (Pole.hdp n p f) = some (true, TKey.clue n p) := by simp [traceKey, hn]
      cases ea : read p R with
      | none => simp [execPole, localPole, stopTag_of hn, ea, TAg]
      | some v =>
        exact push _ (n, v) he (by simp [execPole, localPole, stopTag_of hn, ea])
          (by simp [execPole, localPole, stopTag_of hn, ea])
    · simp only [brOp, traceKey, if_neg hn] at hb
      by_cases hs : stopTag n = true
      · simp only [hs, if_true, Option.some.injEq] at hb; subst hb
        cases ea : read p R with
        | none => simp [execPole, localPole, hs, ea, TAg]
        | some v =>
          simp only [execPole, localPole, hs, if_true, ea, Option.bind_some, Option.map_some]
          exact ⟨rfl, rfl, rfl, fun _ _ => TrR.keep _ (fun k e => by cases e) hr⟩
      · simp only [hs, Bool.false_eq_true, if_false, Option.some.injEq] at hb; subst hb
        simp [execPole, localPole, hs, TAg, hr]
  | hde n p f =>
    by_cases hn : n = Tag.spot ∨ n = Tag.mean
    · have he : traceKey (Pole.hde n p f) = some (false, TKey.clue n p) := by simp [traceKey, hn]
      refine pop _ he fun u => ?_
      cases u <;> simp [execPole, localPole, stopTag_of hn, popTrace]
    · simp only [brOp, traceKey, if_neg hn] at hb
      by_cases hs : stopTag n = true
      · simp only [hs, if_true] at hb
        have hg : gm = none :: g1 := by
          rcases gm with _ | ⟨_ | k', g0⟩
          · cases hb
          · simp only [Option.some.injEq] at hb; rw [hb]
          · cases hb
        subst hg
        obtain ⟨f, t1, t1', rfl, rfl, h1⟩ := hr.inv_keep (fun k e => by cases e)
        simp only [execPole, localPole, hs, if_true, popTrace, Option.bind_some, Option.map_some]
        exact ⟨rfl, rfl, rfl, fun _ _ => h1⟩
      · simp only [hs, Bool.false_eq_true, if_false, Option.some.injEq] at hb; subst hb
        simp [execPole, localPole, hs, TAg, hr]
  | hmp a v f =>
    cases ea : v.mapM (read · R) with
    | none => simp [execPole, localPole, ea, TAg]
    | some vs =>
      exact push _ (Tag.meaf, C a.toNoun (listNoun id vs)) rfl (by simp [execPole, localPole, ea])
        (by simp [execPole, localPole, ea])
  | hme a v f =>
    refine pop _ rfl fun u => ?_
    cases u <;> simp [execPole, localPole, popTrace]
  | hcp n f => exact push _ (Tag.meac, n) rfl (by simp [execPole, localPole]) (by simp [execPole, localPole])
  | hce n f =>
    refine pop _ rfl fun u => ?_
    cases u <;> simp [execPole, localPole, popTrace]
  | inc => exact crash rfl rfl (by simp [brOp, traceKey])
  | cel => exact crash rfl rfl (by simp [brOp, traceKey])
  | lob => exact crash rfl rfl (by simp [brOp, traceKey])
  | spy => exact crash rfl rfl (by simp [brOp, traceKey])
  | nok => exact crash rfl rfl (by simp [brOp, traceKey])
  | cal => exact crash rfl rfl (by simp [brOp, traceKey])
  | caf => exact crash rfl rfl (by simp [brOp, traceKey])
  | cam => exact crash rfl rfl (by simp [brOp, traceKey])
  | csl => exact crash rfl rfl (by simp [brOp, traceKey])
  | csf => exact crash rfl rfl (by simp [brOp, traceKey])
  | csm => exact crash rfl rfl (by simp [brOp, traceKey])

end

end Opt
end SkaModel
end Formalization
