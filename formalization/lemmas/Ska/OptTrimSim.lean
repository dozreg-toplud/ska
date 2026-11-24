import lemmas.Ska.OptTrimWalk
import lemmas.Ska.ExecPath
import lemmas.Ska.OptRegLe
import lemmas.Ska.OptHopsBlocks

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

/-! ## The simulation -/

/-- The dropped keys: not unsafe, and opened. -/
def TDrop (uns : Uns) (opened : List TKey) (k : TKey) : Prop := uns k = false ∧ k ∈ opened

/-- The test of the `+skip`, negated: the ops the code after keeps. -/
def tkeep (uns : Uns) (opened : List TKey) (op : Pole) : Bool := !trimDrop uns opened op

theorem trimDrop_true {uns : Uns} {opened : List TKey} {op : Pole} (h : trimDrop uns opened op = true) :
    ∃ b k, traceKey op = some (b, k) ∧ TDrop uns opened k := by
  unfold trimDrop at h
  split at h
  · rename_i b k he
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
    exact ⟨b, k, he, h⟩
  · cases h

theorem trimDrop_false {uns : Uns} {opened : List TKey} {op : Pole} (h : trimDrop uns opened op = false) :
    ∀ b k, traceKey op = some (b, k) → ¬ TDrop uns opened k := by
  intro b k he hd
  simp only [trimDrop, he, hd.1, hd.2, Bool.not_false, decide_true, Bool.and_self, Bool.true_eq_false] at h

theorem brBody_append : ∀ (g : List (Option TKey)) (l1 l2 : List Pole),
    brBody g (l1 ++ l2) = (brBody g l1).bind fun g' => brBody g' l2
  | g, [], l2 => by simp [brBody]
  | g, op :: l1, l2 => by
    simp only [List.cons_append, brBody]
    cases brOp g op with
    | none => rfl
    | some g' => exact brBody_append g' l1 l2

/-- The stack after the next op of a bracketed body. -/
theorem br_next {g gm gend : List (Option TKey)} {pre rest : List Pole} {p : Pole}
    (h : brBody g (pre ++ p :: rest) = some gend) (hm : brBody g pre = some gm) :
    ∃ g1, brOp gm p = some g1 ∧ brBody g (pre ++ [p]) = some g1 := by
  rw [brBody_append, hm, Option.bind_some] at h
  simp only [brBody, Option.bind_eq_some_iff] at h
  obtain ⟨g1, h1, -⟩ := h
  refine ⟨g1, h1, ?_⟩
  rw [brBody_append, hm, Option.bind_some]
  simp [brBody, h1]

section Sim
variable {σ : Type} {lib : Lib} {O : Oracle σ} {gul : Noun} {c c' : Straight Map}
  {K : Nat → List (Option TKey)} {uns : Uns} {opened : List TKey}

/-- **The relation**: the same label, parameters, registers and state; the
body after is the body before filtered; the body before is a suffix of its
block's body whose prefix has the bracketed stack `gm`, and the traces are in
`TrR` of `gm`. -/
def TrimI (bl : Map Blob) (K : Nat → List (Option TKey)) (uns : Uns) (opened : List TKey) (x x' : Cfg σ Map) : Prop :=
  x'.lab = x.lab ∧ x'.params = x.params ∧ x'.regs = x.regs ∧ x'.st = x.st ∧ Reach bl x.lab ∧
  x'.b = { x.b with body := x.b.body.filter (tkeep uns opened) } ∧
  ∃ b0 pre gm, HoonMap.get bl x.lab = some b0 ∧ x.b.fin = b0.fin ∧ b0.body = pre ++ x.b.body ∧
    brBody (K x.lab) pre = some gm ∧ TrR (TDrop uns opened) gm x.t x'.t

/-- The head of the body before is a dropped op. -/
def TDropped (uns : Uns) (opened : List TKey) (x : Cfg σ Map) : Prop :=
  x.params = [] ∧ x.b.par = [] ∧ ∃ p rest, x.b.body = p :: rest ∧ trimDrop uns opened p = true

/-- At a dropped op the code before steps or crashes: no end. -/
theorem tdropped_endOf {x : Cfg σ Map} (hd : TDropped uns opened x) : endOf lib O gul x = none := by
  obtain ⟨hp, hq, p, rest, hbd, hdr⟩ := hd
  obtain ⟨b, k, he, -⟩ := trimDrop_true hdr
  unfold endOf
  split
  · rfl
  rw [hbd]
  simp only
  cases e : execPole lib O gul x.st p x.regs x.t with
  | none => rfl
  | some r =>
    obtain ⟨ton, R2, t2, st2⟩ := r
    cases b with
    | true => obtain ⟨rfl, -⟩ := push_exec he e; rfl
    | false => obtain ⟨rfl, -⟩ := pop_exec he e; rfl

variable (TB : TrimBr c.blocks K) (TS : TrimSafe c.blocks K uns)
  (hc' : ∀ o, HoonMap.get c'.blocks o = (HoonMap.get c.blocks o).map fun b =>
    { b with body := b.body.filter (tkeep uns opened) })
include TB TS

/-- The facts at the next op of the body before. -/
theorem trimI_op {x x' : Cfg σ Map} {p : Pole} {rest : List Pole} (hr : TrimI c.blocks K uns opened x x')
    (hbd : x.b.body = p :: rest) :
    ∃ b0 pre gm g1, HoonMap.get c.blocks x.lab = some b0 ∧ x.b.fin = b0.fin ∧ b0.body = pre ++ p :: rest ∧
      brBody (K x.lab) pre = some gm ∧ TrR (TDrop uns opened) gm x.t x'.t ∧ brOp gm p = some g1 ∧
      brBody (K x.lab) (pre ++ [p]) = some g1 ∧
      (traceKey p = none → notCrashing p = false → x.t = x'.t) := by
  obtain ⟨-, -, -, -, hreach, -, b0, pre, gm, hb0, hfin, hpre, hgm, htr⟩ := hr
  rw [hbd] at hpre
  obtain ⟨gend, hgend, -⟩ := TB.2 x.lab b0 hreach hb0
  rw [hpre] at hgend
  obtain ⟨g1, h1, h2⟩ := br_next hgend hgm
  refine ⟨b0, pre, gm, g1, hb0, hfin, hpre, hgm, htr, h1, h2, fun he hn => htr.eq fun k hk hd => ?_⟩
  have := (TS x.lab b0 hreach hb0).1 pre p rest gm hpre hgm he hn k hk
  rw [hd.1] at this; cases this

/-- At the end of the body before, the stack is the one every jump target
starts with, and a loud end sees equal traces. -/
theorem trimI_fin {x x' : Cfg σ Map} (hr : TrimI c.blocks K uns opened x x') (hbd : x.b.body = []) :
    ∃ b0, HoonMap.get c.blocks x.lab = some b0 ∧ x.b.fin = b0.fin ∧
      (∀ j ∈ getJmps b0.fin, TrR (TDrop uns opened) (K j.there) x.t x'.t) ∧
      (finQuiet x.b.fin = false → x.t = x'.t) := by
  obtain ⟨-, -, -, -, hreach, -, b0, pre, gm, hb0, hfin, hpre, hgm, htr⟩ := hr
  rw [hbd, List.append_nil] at hpre
  obtain ⟨gend, hgend, hK⟩ := TB.2 x.lab b0 hreach hb0
  rw [hpre, hgm] at hgend
  cases hgend
  refine ⟨b0, hb0, hfin, fun j hj => by rw [hK j hj]; exact htr, fun hq => htr.eq fun k hk hd => ?_⟩
  rw [hfin] at hq
  have := (TS x.lab b0 hreach hb0).2 hq gm (by rw [hpre]; exact hgm) k hk
  rw [hd.1] at this; cases this

include hc'

/-- The jump after from the jump before. -/
theorem trim_jump {x x' : Cfg σ Map} {j : Jmp} {b2 : Blob} (hr : TrimI c.blocks K uns opened x x')
    (hbd : x.b.body = []) (htk : taken x.regs x.b.fin = some j) (hb2 : HoonMap.get c.blocks j.there = some b2) :
    HoonMap.get c'.blocks j.there = some { b2 with body := b2.body.filter (tkeep uns opened) } ∧
    TrimI c.blocks K uns opened (⟨j.there, b2, j.args, x.regs, x.t, x.st⟩ : Cfg σ Map)
      ⟨j.there, { b2 with body := b2.body.filter (tkeep uns opened) }, j.args, x'.regs, x'.t, x'.st⟩ := by
  obtain ⟨b0, hb0, hfin, hK, -⟩ := trimI_fin TB TS hr hbd
  have hreach := hr.2.2.2.2.1
  rw [hfin] at htk
  refine ⟨by rw [hc', hb2]; rfl, rfl, rfl, hr.2.2.1, hr.2.2.2.1, Reach.jump hreach hb0 (taken_mem htk), rfl,
    b2, [], K j.there, hb2, rfl, rfl, rfl, hK j (taken_mem htk)⟩

/-- **Forward**: a step of the code before is a step after or none. -/
theorem trim_fwd_step {x y x' : Cfg σ Map} {es : List (Nat × Nat)} (hs : Step lib O c gul x es y)
    (hr : TrimI c.blocks K uns opened x x') :
    ∃ es' y', Steps lib O c' gul x' es' y' ∧ TrimI c.blocks K uns opened y y' := by
  obtain ⟨lab, b, params, regs, t, st⟩ := x
  obtain ⟨lab', b', params', regs', t', st'⟩ := x'
  have hr0 := hr
  obtain ⟨hl, hpe, hrg, hst, hreach, hb', hrest⟩ := hr
  simp only at hl hpe hrg hst hreach hb' hrest
  subst lab' params' regs' st' b'
  cases hs with
  | pass hne hR =>
    refine ⟨_, _, Steps.step (Step.pass (x := ⟨lab, { b with body := b.body.filter (tkeep uns opened) }, params, regs, t', st⟩)
      hne hR) (Steps.refl _), rfl, rfl, rfl, rfl, hreach, rfl, ?_⟩
    obtain ⟨b0, pre, gm, h1, h2, h3, h4, h5⟩ := hrest
    exact ⟨b0, pre, gm, h1, h2, h3, h4, h5⟩
  | @op p rest n R2 t2 st2 hp hq hbd hpole =>
    simp only at hp hq hbd hpole
    subst hp
    obtain ⟨b0, pre, gm, g1, hb0, hfin, hpre, hgm, htr, hg1, hpre1, hcr⟩ := trimI_op TB TS hr0 hbd
    simp only at hb0 hfin hgm htr hpre1 hcr
    cases hk : trimDrop uns opened p with
    | true =>
      obtain ⟨bk, k, he, hd⟩ := trimDrop_true hk
      obtain ⟨-, rfl, rfl, htr2⟩ := drop_pole htr hg1 he hd hpole
      refine ⟨[], _, Steps.refl _, rfl, rfl, rfl, rfl, hreach, ?_, b0, pre ++ [p], g1, hb0, hfin,
        by rw [hpre]; simp, hpre1, htr2⟩
      simp only [hbd, List.filter_cons, tkeep, hk, Bool.not_true, Bool.false_eq_true, if_false]
    | false =>
      have hkp := kept_pole (lib := lib) (O := O) (gul := gul) (st := st) (R := regs) htr hg1
        (trimDrop_false hk) hcr
      obtain ⟨t2', h2', htr2⟩ := hkp.fwd hpole
      refine ⟨_, _, Steps.step (Step.op (x := ⟨lab, { b with body := b.body.filter (tkeep uns opened) }, [], regs, t', st⟩)
        (rest := rest.filter (tkeep uns opened)) rfl hq
        (by simp only [hbd, List.filter_cons, tkeep, hk, Bool.not_false, if_true]) h2') (Steps.refl _),
        rfl, rfl, rfl, rfl, hreach, rfl, b0, pre ++ [p], g1, hb0, hfin, by rw [hpre]; simp, hpre1, htr2 n rfl⟩
  | @jump j b2 hp hq hbd htk hb2 =>
    simp only at hp hq hbd htk hb2
    subst hp
    obtain ⟨hb2', hr2⟩ := trim_jump TB TS hc' hr0 hbd htk hb2
    refine ⟨_, _, Steps.step (Step.jump (x := ⟨lab, { b with body := b.body.filter (tkeep uns opened) }, [], regs, t', st⟩)
      rfl hq (by simp [hbd]) htk hb2') (Steps.refl _), hr2⟩

/-- **Backward**: out of the normal form, a step after is matched by one step
before. -/
theorem trim_bwd_step {x x' y' : Cfg σ Map} {es' : List (Nat × Nat)} (hs : Step lib O c' gul x' es' y')
    (hr : TrimI c.blocks K uns opened x x') (hnd : ¬ TDropped uns opened x) :
    ∃ es y, Steps lib O c gul x es y ∧ TrimI c.blocks K uns opened y y' := by
  obtain ⟨lab, b, params, regs, t, st⟩ := x
  obtain ⟨lab', b', params', regs', t', st'⟩ := x'
  have hr0 := hr
  obtain ⟨hl, hpe, hrg, hst, hreach, hb', hrest⟩ := hr
  simp only at hl hpe hrg hst hreach hb' hrest
  subst lab' params' regs' st' b'
  cases hs with
  | @pass R1 hne hR =>
    simp only at hne hR
    refine ⟨_, _, Steps.step (Step.pass (x := ⟨lab, b, params, regs, t, st⟩) hne hR) (Steps.refl _),
      rfl, rfl, rfl, rfl, hreach, rfl, ?_⟩
    obtain ⟨b0, pre, gm, h1, h2, h3, h4, h5⟩ := hrest
    exact ⟨b0, pre, gm, h1, h2, h3, h4, h5⟩
  | @op p rest' n R2 t2' st2 hp hq hbd hpole =>
    simp only at hp hq hbd hpole
    subst hp
    cases hb : b.body with
    | nil => rw [hb] at hbd; simp at hbd
    | cons q rest =>
      rw [hb] at hbd
      cases hk : trimDrop uns opened q with
      | true => exact (hnd ⟨rfl, hq, q, rest, hb, hk⟩).elim
      | false =>
        simp only [List.filter_cons, tkeep, hk, Bool.not_false, if_true, List.cons.injEq] at hbd
        obtain ⟨rfl, rfl⟩ := hbd
        obtain ⟨b0, pre, gm, g1, hb0, hfin, hpre, hgm, htr, hg1, hpre1, hcr⟩ := trimI_op TB TS hr0 hb
        simp only at hb0 hfin hgm htr hpre1 hcr
        have hkp := kept_pole (lib := lib) (O := O) (gul := gul) (st := st) (R := regs) htr hg1
          (trimDrop_false hk) hcr
        obtain ⟨t2, h2, htr2⟩ := hkp.bwd hpole
        exact ⟨_, _, Steps.step (Step.op (x := ⟨lab, b, [], regs, t, st⟩) (rest := rest) rfl hq hb h2) (Steps.refl _),
          rfl, rfl, rfl, rfl, hreach, rfl, b0, pre ++ [q], g1, hb0, hfin, by rw [hpre]; simp, hpre1, htr2 n rfl⟩
  | @jump j b2' hp hq hbd htk' hb2' =>
    simp only at hp hq hbd htk' hb2'
    subst hp
    have hb : b.body = [] := by
      cases hb : b.body with
      | nil => rfl
      | cons q rest =>
        rw [hb] at hbd
        cases hk : trimDrop uns opened q with
        | true => exact (hnd ⟨rfl, hq, q, rest, hb, hk⟩).elim
        | false => simp [List.filter_cons, tkeep, hk] at hbd
    rw [hc'] at hb2'
    obtain ⟨b2, hb2, rfl⟩ := Option.map_eq_some_iff.mp hb2'
    obtain ⟨-, hr2⟩ := trim_jump TB TS hc' hr0 hb htk' hb2
    exact ⟨_, _, Steps.step (Step.jump (x := ⟨lab, b, [], regs, t, st⟩) rfl hq hb htk' hb2) (Steps.refl _), hr2⟩

omit hc' in
/-- **The normal form**: the code before runs the dropped ops at its head,
which do not crash (their reads hold values by `ReadsOK`, a pop finds the
frame of its key). -/
theorem trim_norm (l : List Pole) : ∀ {x x' : Cfg σ Map}, x.b.body = l → TrimI c.blocks K uns opened x x' →
    (∀ es z k, Steps lib O c gul x es z → ReadsAt gul z k → ∃ v, read k z.regs = some v) →
    ∃ es z, Steps lib O c gul x es z ∧ TrimI c.blocks K uns opened z x' ∧ ¬ TDropped uns opened z := by
  induction l with
  | nil =>
    intro x x' hl0 hr _
    refine ⟨[], x, Steps.refl _, hr, ?_⟩
    rintro ⟨-, -, p, rest, hbd, -⟩
    rw [hl0] at hbd; cases hbd
  | cons q l ih =>
    intro x x' hl0 hr hl
    by_cases hd : TDropped uns opened x
    · obtain ⟨hp, hq, p, rest, hbd, hdr⟩ := hd
      have hbd' := hbd
      rw [hl0] at hbd
      simp only [List.cons.injEq] at hbd
      obtain ⟨rfl, rfl⟩ := hbd
      obtain ⟨bk, k, he, hdk⟩ := trimDrop_true hdr
      obtain ⟨b0, pre, gm, g1, hb0, hfin, hpre, hgm, htr, hg1, hpre1, -⟩ := trimI_op TB TS hr hbd'
      have hsome := drop_isSome (lib := lib) (O := O) (gul := gul) (st := x.st) (R := x.regs) htr hg1 he hdk
        (fun r hr' => hl [] x r (Steps.refl _) ⟨hp, hq, Or.inl ⟨q, l, hbd', hr'⟩⟩)
      obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp hsome
      obtain ⟨ton, R2, t2, st2⟩ := res
      obtain ⟨rfl, rfl, rfl, htr2⟩ := drop_pole htr hg1 he hdk hres
      have hs : Step lib O c gul x [] ⟨x.lab, { x.b with body := l }, x.params, x.regs, t2, x.st⟩ :=
        Step.op hp hq hbd' hres
      obtain ⟨hl', hpe, hrg, hst, hreach, hb', -⟩ := hr
      have hr2 : TrimI c.blocks K uns opened ⟨x.lab, { x.b with body := l }, x.params, x.regs, t2, x.st⟩ x' := by
        refine ⟨hl', hpe, hrg, hst, hreach, ?_, b0, pre ++ [q], g1, hb0, hfin, by rw [hpre]; simp, hpre1, htr2⟩
        rw [hb', hbd']
        simp [List.filter_cons, tkeep, hdr]
      obtain ⟨es, z, hz, hrz, hnd⟩ := ih rfl hr2 (fun es z k hs' => hl _ z k (Steps.step hs hs'))
      exact ⟨[] ++ es, z, Steps.step hs hz, hrz, hnd⟩
    · exact ⟨[], x, Steps.refl _, hr, hd⟩

omit hc' in
/-- **An end out of the normal form is the same end.** -/
theorem trim_endOf {x x' : Cfg σ Map} (hr : TrimI c.blocks K uns opened x x') (hnd : ¬ TDropped uns opened x) :
    endOf lib O gul x' = endOf lib O gul x := by
  have hr0 := hr
  obtain ⟨hl, hpe, hrg, hst, hreach, hb', -⟩ := hr
  by_cases hne : x.params ≠ [] ∨ x.b.par ≠ []
  · have hne' : x'.params ≠ [] ∨ x'.b.par ≠ [] := by rw [hpe, hb']; exact hne
    unfold endOf; rw [if_pos hne, if_pos hne']
  · have hne' : ¬ (x'.params ≠ [] ∨ x'.b.par ≠ []) := by rw [hpe, hb']; exact hne
    simp only [not_or, ne_eq, Decidable.not_not] at hne
    obtain ⟨hp, hq⟩ := hne
    cases hbd : x.b.body with
    | nil =>
      obtain ⟨b0, hb0, hfin, -, hloud⟩ := trimI_fin TB TS hr0 hbd
      cases hq' : finQuiet x.b.fin with
      | false =>
        have ht := hloud hq'
        have hx : x' = x := by
          obtain ⟨lab, ⟨par, body, fin⟩, params, regs, t, st⟩ := x
          obtain ⟨lab', b', params', regs', t', st'⟩ := x'
          simp only at hl hpe hrg hst hb' ht hbd ⊢
          subst hbd
          subst hl hpe hrg hst hb' ht
          rfl
        rw [hx]
      | true =>
        have hb'' : x'.b.body = [] := by rw [hb']; simp [hbd]
        have hf : x'.b.fin = x.b.fin := by rw [hb']
        unfold endOf
        rw [if_neg hne', if_neg (by simp [hp, hq]), hb'', hbd, hf]
        cases e : x.b.fin <;> simp [finQuiet, e] at hq' ⊢
    | cons p rest =>
      cases hk : trimDrop uns opened p with
      | true => exact (hnd ⟨hp, hq, p, rest, hbd, hk⟩).elim
      | false =>
        obtain ⟨b0, pre, gm, g1, -, -, -, -, htr, hg1, -, hcr⟩ := trimI_op TB TS hr0 hbd
        have hkp := kept_pole (lib := lib) (O := O) (gul := gul) (st := x.st) (R := x.regs) htr hg1
          (trimDrop_false hk) hcr
        have hb'' : x'.b.body = p :: rest.filter (tkeep uns opened) := by
          rw [hb']; simp [hbd, List.filter_cons, tkeep, hk]
        unfold endOf
        rw [if_neg hne', if_neg (by simp [hp, hq]), hb'', hbd]
        simp only
        rw [hst, hrg]
        revert hkp
        generalize execPole lib O gul x.st p x.regs x.t = r
        generalize execPole lib O gul x.st p x.regs x'.t = r'
        intro hkp
        rcases r with _ | ⟨ton, R, t, s⟩ <;> rcases r' with _ | ⟨ton', R', t', s'⟩
        · rfl
        · exact hkp.elim
        · exact hkp.elim
        · obtain ⟨rfl, rfl, rfl, -⟩ := hkp; cases ton <;> rfl

omit TB TS hc' in
/-- A real read after, out of the normal form, is a real read before, of the
same register file. -/
theorem trim_reads {x x' : Cfg σ Map} {k : Nat} (hr : TrimI c.blocks K uns opened x x')
    (hnd : ¬ TDropped uns opened x) (hk : ReadsAt gul x' k) : ReadsAt gul x k ∧ x'.regs = x.regs := by
  obtain ⟨hl, hpe, hrg, hst, hreach, hb', -⟩ := hr
  refine ⟨?_, hrg⟩
  obtain ⟨hp, hq, hk⟩ := hk
  have hp0 : x.params = [] := by rw [← hpe]; exact hp
  have hq0 : x.b.par = [] := by rw [hb'] at hq; exact hq
  refine ⟨hp0, hq0, ?_⟩
  rw [hb'] at hk
  simp only at hk
  cases hbd : x.b.body with
  | nil =>
    rw [hbd] at hk
    rcases hk with ⟨p, rest, h, -⟩ | ⟨-, hk⟩
    · simp at h
    · exact Or.inr ⟨rfl, hk⟩
  | cons p rest =>
    cases hkd : trimDrop uns opened p with
    | true => exact (hnd ⟨hp0, hq0, p, rest, hbd, hkd⟩).elim
    | false =>
      rw [hbd] at hk
      simp only [List.filter_cons, tkeep, hkd, Bool.not_false, if_true] at hk
      rcases hk with ⟨p', rest', h, hk⟩ | ⟨h, -⟩
      · simp only [List.cons.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact Or.inl ⟨_, rest, rfl, hk⟩
      · cases h

/-- **Forward, on paths.** -/
theorem trim_fwd {x z : Cfg σ Map} {es : List (Nat × Nat)} (hs : Steps lib O c gul x es z) {r : Tone × σ}
    (he : endOf lib O gul z = some r) : ∀ {x' : Cfg σ Map}, TrimI c.blocks K uns opened x x' →
      ∃ es' z', Steps lib O c' gul x' es' z' ∧ endOf lib O gul z' = some r := by
  induction hs with
  | refl y =>
    intro x' hr
    refine ⟨[], x', Steps.refl _, ?_⟩
    by_cases hd : TDropped uns opened y
    · rw [tdropped_endOf hd] at he; cases he
    · rw [trim_endOf TB TS hr hd]; exact he
  | step s _ ih =>
    intro x' hr
    obtain ⟨es1, y', hs1, hr1⟩ := trim_fwd_step TB TS hc' s hr
    obtain ⟨es2, z', hs2, he'⟩ := ih he hr1
    exact ⟨_, z', steps_trans hs1 hs2, he'⟩

/-- **Backward, on paths**, to the normal form. -/
theorem trim_bwd {x' z' : Cfg σ Map} {es' : List (Nat × Nat)} (hs : Steps lib O c' gul x' es' z') :
    ∀ {x : Cfg σ Map}, (∀ es z k, Steps lib O c gul x es z → ReadsAt gul z k → ∃ v, read k z.regs = some v) →
    TrimI c.blocks K uns opened x x' →
    ∃ es z, Steps lib O c gul x es z ∧ TrimI c.blocks K uns opened z z' ∧ ¬ TDropped uns opened z := by
  induction hs with
  | refl => intro x hl hr; exact trim_norm TB TS _ rfl hr hl
  | step s _ ih =>
    intro x hl hr
    obtain ⟨es1, x1, hs1, hr1, hnd1⟩ := trim_norm TB TS _ rfl hr hl
    obtain ⟨es2, y, hs2, hr2⟩ := trim_bwd_step TB TS hc' s hr1 hnd1
    obtain ⟨es3, z, hs3, hr3, hnd3⟩ :=
      ih (fun es z k hz => hl _ z k (steps_trans (steps_trans hs1 hs2) hz)) hr2
    exact ⟨_, z, steps_trans (steps_trans hs1 hs2) hs3, hr3, hnd3⟩

end Sim

/-- **The code after keeps the code before**, for any blocks after that are
the blocks before with the hint ops of dropped keys taken out, given
`TrimBr` and `TrimSafe` of the unsafe keys. -/
theorem trim_keeps_of (c : Straight Map) {K : Nat → List (Option TKey)} {uns : Uns} {opened : List TKey}
    {bl' : Map Blob} (TB : TrimBr c.blocks K) (TS : TrimSafe c.blocks K uns) (h0 : (HoonMap.get c.blocks 0).isSome)
    (hbl : ∀ o, HoonMap.get bl' o = (HoonMap.get c.blocks o).map fun b =>
      { b with body := b.body.filter (tkeep uns opened) }) : Keeps c (withBlocks c bl') := by
  obtain ⟨b0, hb0⟩ := Option.isSome_iff_exists.mp h0
  have hc' : ∀ o, HoonMap.get (withBlocks c bl').blocks o = (HoonMap.get c.blocks o).map fun b =>
      { b with body := b.body.filter (tkeep uns opened) } := hbl
  have hb0' : HoonMap.get (withBlocks c bl').blocks 0 = some { b0 with body := b0.body.filter (tkeep uns opened) } := by
    rw [hc', hb0]; rfl
  refine ⟨rfl, rfl, ?_, fun lib σ O gul st vals t ⟨hok, hargs, hloc⟩ => ?_⟩
  · show (HoonMap.get bl' 0).map Blob.par = (HoonMap.get c.blocks 0).map Blob.par
    rw [hbl, hb0]; rfl
  let x0 : Path.Cfg σ Map := ⟨0, b0, [], regsOf vals, t, st⟩
  let x0' : Path.Cfg σ Map := ⟨0, { b0 with body := b0.body.filter (tkeep uns opened) }, [], regsOf vals, t, st⟩
  have hr0 : TrimI c.blocks K uns opened x0 x0' :=
    ⟨rfl, rfl, rfl, rfl, Reach.zero, rfl, b0, [], K 0, hb0, rfl, rfl, rfl, by
      show TrR _ (K 0) t t
      rw [TB.1]; exact TrR.nil t⟩
  have hl0 : ∀ es z k, Steps lib O c gul x0 es z → ReadsAt gul z k → ∃ v, read k z.regs = some v :=
    fun es z k hz hk => hok es z k ⟨b0, hb0, hz⟩ hk
  have back : ∀ es' y', Path.FromEntry (lib := lib) (O := O) (c := withBlocks c bl') (gul := gul) st vals t es' y' →
      ∃ es y, Path.Steps lib O c gul x0 es y ∧ TrimI c.blocks K uns opened y y' ∧ ¬ TDropped uns opened y := by
    rintro es' y' ⟨b0'', hb0'', hs'⟩
    rw [hb0'] at hb0''; cases hb0''
    exact trim_bwd TB TS hc' hs' hl0 hr0
  refine ⟨Option.ext fun r => ⟨fun h' => ?_, fun h' => ?_⟩, fun es' y' k hy' hk => ?_,
    fun es' y' k hy' hk => ?_, fun es' y' p rest hy' hp hq hb hsa => ?_⟩
  · obtain ⟨es', y', hy', he'⟩ := (Path.execEntry_iff_path (c := withBlocks c bl') st vals t r).mp h'
    obtain ⟨es, y, hs, hn, hnd⟩ := back es' y' hy'
    exact (Path.execEntry_iff_path (c := c) st vals t r).mpr
      ⟨es, y, ⟨b0, hb0, hs⟩, by rw [← trim_endOf TB TS hn hnd]; exact he'⟩
  · obtain ⟨es, y, ⟨b0'', hb0'', hs⟩, he⟩ := (Path.execEntry_iff_path (c := c) st vals t r).mp h'
    rw [hb0] at hb0''; cases hb0''
    obtain ⟨es', z', hs', he'⟩ := trim_fwd TB TS hc' hs he hr0
    exact (Path.execEntry_iff_path (c := withBlocks c bl') st vals t r).mpr ⟨es', z', ⟨_, hb0', hs'⟩, he'⟩
  · obtain ⟨es, y, hs, hn, hnd⟩ := back es' y' hy'
    obtain ⟨hk', hrg⟩ := trim_reads hn hnd hk
    obtain ⟨v, hv⟩ := hok es y k ⟨b0, hb0, hs⟩ hk'
    exact ⟨v, by rw [hrg, hv]⟩
  · obtain ⟨es, y, hs, hn, -⟩ := back es' y' hy'
    obtain ⟨-, hpe, hrg, -⟩ := hn
    have hk0 : some k ∈ y.params := by rw [← hpe]; exact hk
    rw [hrg]
    exact hargs es y k ⟨b0, hb0, hs⟩ hk0
  · obtain ⟨es, y, hs, hn, hnd⟩ := back es' y' hy'
    have hn0 := hn
    obtain ⟨-, hpe, hrg, hst, -, hb', -⟩ := hn
    have hp0 : y.params = [] := by rw [← hpe]; exact hp
    have hq0 : y.b.par = [] := by rw [hb'] at hq; exact hq
    rw [hb'] at hb
    simp only at hb
    cases hbd : y.b.body with
    | nil => rw [hbd] at hb; simp at hb
    | cons q rest0 =>
      cases hk : trimDrop uns opened q with
      | true => exact (hnd ⟨hp0, hq0, q, rest0, hbd, hk⟩).elim
      | false =>
        rw [hbd] at hb
        simp only [List.filter_cons, tkeep, hk, Bool.not_false, if_true, List.cons.injEq] at hb
        obtain ⟨rfl, -⟩ := hb
        obtain ⟨b1, pre, gm, g1, -, -, -, -, htr, hg1, -, hcr⟩ := trimI_op TB TS hn0 hbd
        have hkp := kept_pole (lib := lib) (O := O) (gul := gul) (st := y.st) (R := y.regs) htr hg1
          (trimDrop_false hk) hcr
        rw [hst, hrg, hkp.isSome]
        exact hloc es y q rest0 ⟨b0, hb0, hs⟩ hp0 hq0 hbd hsa

section
variable [MapKeys Map]

theorem trimRun_fold (bl : Map Blob) (f : Blob → Blob) : ∀ (ks : List Nat) (acc : Map Blob),
    (∀ o, o ∉ ks → HoonMap.get acc o = (HoonMap.get bl o).map f) →
    (∀ o, HoonMap.get acc o = HoonMap.get bl o ∨ HoonMap.get acc o = (HoonMap.get bl o).map f) →
    ∀ o, HoonMap.get (ks.foldl (fun acc o =>
      match HoonMap.get bl o with
      | some b => HoonMap.put acc o (f b)
      | none => acc) acc) o = (HoonMap.get bl o).map f
  | [], acc, h1, _, o => h1 o List.not_mem_nil
  | k :: ks, acc, h1, h2, o => by
    simp only [List.foldl_cons]
    refine trimRun_fold bl f ks _ (fun o' ho' => ?_) (fun o' => ?_) o
    · by_cases e : o' = k
      · subst e
        cases hb : HoonMap.get bl o' with
        | some b => simp [HoonMap.get_put]
        | none =>
          simp only
          rcases h2 o' with h | h <;> rw [h, hb] <;> rfl
      · have : HoonMap.get (match HoonMap.get bl k with
            | some b => HoonMap.put acc k (f b)
            | none => acc) o' = HoonMap.get acc o' := by
          cases HoonMap.get bl k <;> simp [HoonMap.get_put, e]
        rw [this]
        exact h1 o' (fun h => by rcases List.mem_cons.mp h with h | h; exact e h; exact ho' h)
    · by_cases e : o' = k
      · subst e
        cases hb : HoonMap.get bl o' with
        | some b => right; simp [HoonMap.get_put, hb]
        | none => simp only; rw [← hb]; exact h2 o'
      · have : HoonMap.get (match HoonMap.get bl k with
            | some b => HoonMap.put acc k (f b)
            | none => acc) o' = HoonMap.get acc o' := by
          cases HoonMap.get bl k <;> simp [HoonMap.get_put, e]
        rw [this]
        exact h2 o'

/-- **The blocks after `+trim-trace-hints`**: each block with the hint ops of
dropped keys taken out. -/
theorem trimRun_get (bl : Map Blob) (uns : Uns) (opened : List TKey) (o : Nat) :
    HoonMap.get (trimRun bl uns opened) o = (HoonMap.get bl o).map fun b =>
      { b with body := b.body.filter (tkeep uns opened) } := by
  unfold trimRun
  refine trimRun_fold bl _ _ bl (fun o' ho' => ?_) (fun _ => Or.inl rfl) o
  have : HoonMap.get bl o' = none := by
    cases e : HoonMap.get bl o' with
    | none => rfl
    | some b => exact absurd ((MapKeys.mem_keys bl o').mpr (by simp [e])) ho'
  rw [this]; rfl

/-- **`+trim-trace-hints` keeps the code**, on a `topo` with `TopoOK`, a
`rev` that lists every member of `topo` jumping to a block, and bracketed
hints. -/
theorem trim_keeps (c : Straight Map) {topo : List Nat} {rev : Map (List Nat)} {bl' : Map Blob}
    {K : Nat → List (Option TKey)} (ht : TopoOK c.blocks topo)
    (hrev : ∀ o b j, o ∈ topo → HoonMap.get c.blocks o = some b → j ∈ getJmps b.fin → o ∈ getJa rev j.there)
    (TB : TrimBr c.blocks K) (h : trimTraceHints c.blocks topo rev = some bl') : Keeps c (withBlocks c bl') := by
  unfold trimTraceHints at h
  obtain ⟨uns, hu, rfl⟩ := Option.map_eq_some_iff.mp h
  have h0 : (HoonMap.get c.blocks 0).isSome := ht.2.2.1 0 (List.mem_of_mem_head? ht.2.1)
  exact trim_keeps_of c TB (trimWalk_safe TB ht hrev hu) h0 (trimRun_get c.blocks uns (trimOpened c.blocks))

/-- **The preservation statement of `+trim-trace-hints` under `TrimBr`
holds.** -/
theorem trimKeepsBr : TrimKeepsBr (Map := Map) :=
  fun c _ _ _ ht TB h => trim_keeps c ht (fun _ _ _ ho hb hj => revCfg_mem ho hb hj) TB h

end

end Opt
end SkaModel
end Formalization
