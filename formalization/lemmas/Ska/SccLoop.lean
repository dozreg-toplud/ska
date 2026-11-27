import lemmas.Ska.Types

/-! # `+compile-scc-in` as a loop (README Gaps 21)

The sweep loop of `+compile-scc-in` (`desk/lib/nock-compilation.hoon`, lines 3441 to 3717),
executable, with the compile of one member as a parameter (`Cfg.comp`: the `+run-shape` or
`+run` of the member and what follows it, up to `need-new` and the raw `sur`; tracks K, C and J
own that part) and `+msg-need-ord` as a parameter (`Cfg.msg`, `msgOrd` of `Ska/ShapeCol.lean`
with the member's cape in `SccLoopCheck.lean`).

* `member` is the gate `member` after its compile: `keep`, `was`, `moved`, the two branches on
  `map-local`, `need-pessimized`, `chg`.  The entry's need is `need-pessimized` (which is
  `need-new` when they are equal); off `%done` that is the placeholder `[need 0 ~]`, on `%done`
  it is the need of the straight of `finish`, which `SccLoopCheck.lean` checks on the dumps.
* `sweep` is the `+roll` of the loop over `order` with the test `dirty`, `loop` the `|-` with
  fuel, `maySweep` the `%may` sweep, `final` the final pass, `compileSccIn` the whole.
* The views of a callee in the SCC are those of `+callee-need` (`viewN`: the entry of
  `map-local`, else `top`, else `none`) and of `+callee-sure` (`viewS`).
* Ghost state: `rd` (the views and the output of each member's last compile), `tr` (one event
  per compile), `sw` (the `any` of each sweep).  The Hoon has none of them.

Proved: `loop_end` (property (a): the loop ends with a sweep that compiles nothing, so every
member ran after the last change of each of its kids), `loop_reads` (each member's last compile
read the views its kids have at the end), `final_keeps` (properties (b) and (c): the final pass
compiles each member on those same views, so `need-new` is its last sweep's, `need-pessimized`
is the entry it finds, and it leaves every entry as it found it). -/

namespace Formalization.SkaModel.SccLoop

/-- A function updated at one point. -/
def upd {B V : Type} [DecidableEq B] (f : B → V) (b : B) (v : V) : B → V :=
  fun x => if x = b then v else f x

@[simp] theorem upd_same {B V : Type} [DecidableEq B] (f : B → V) (b : B) (v : V) :
    upd f b v b = v := by simp [upd]

@[simp] theorem upd_ne {B V : Type} [DecidableEq B] (f : B → V) {b x : B} (v : V)
    (h : x ≠ b) : upd f b v x = f x := by simp [upd, h]

inductive Mode where
  | may | must | done
  deriving DecidableEq, Repr

/-- What the compile of a member gives: `need-new` and the raw `sur` (`+sure-of`). -/
structure Out (N : Type) where
  nn : N
  sur : N
  deriving DecidableEq, Repr

structure Cfg (B N : Type) where
  /-- `~(tap in scc)`, the order of the final pass. -/
  scc : List B
  /-- The DFS postorder of the members over `kids`. -/
  order : List B
  kids : B → List B
  /-- `[%none ~]`. -/
  none : N
  /-- `+msg-need-ord` with the cape of the member. -/
  msg : B → N → N → N
  /-- The compile of a member, given the views of the needs and of `sure.cache`. -/
  comp : B → Mode → (B → N) → (B → N) → Out N

/-- One compile of a member, for the checks. -/
structure Ev (B N : Type) where
  b : B
  mode : Mode
  keep : Bool
  nn : N
  sur : N
  prev : Option N
  np : N
  ch : Bool
  deriving DecidableEq, Repr

structure St (B N : Type) where
  /-- The needs of the entries of `map-local`. -/
  ml : B → Option N
  /-- `sure.cache` at the members. -/
  sure : B → Option N
  tick : Nat
  ran : B → Option Nat
  chg : B → Option Nat
  any : Bool
  /-- Ghost: the views and the output of each member's last compile. -/
  rd : B → Option ((B → N) × (B → N) × Out N)
  /-- Ghost: the compiles. -/
  tr : List (Ev B N)
  /-- Ghost: the `any` of each sweep of the loop. -/
  sw : List Bool

variable {B N : Type} [DecidableEq B] [DecidableEq N]

/-- `+callee-need` on a member: its entry, else `top`, else `none`. -/
def viewN (top : B → N) (st : St B N) (k : B) : N := (st.ml k).getD (top k)

/-- `+callee-sure`. -/
def viewS (c : Cfg B N) (st : St B N) (k : B) : N := (st.sure k).getD c.none

/-- The gate `member` from its compile on (lines 3541 to 3609). -/
def member (c : Cfg B N) (top : B → N) (b : B) (mode : Mode) (keep : Bool) (st : St B N) :
    Bool × St B N :=
  let vn := viewN top st
  let vs := viewS c st
  let o := c.comp b mode vn vs
  let was := st.sure b
  let sur := if keep then was.getD o.sur else o.sur
  let moved := sur != was.getD c.none
  let r : Bool × N := match st.ml b with
    | none => (moved || o.nn != c.none || top b != c.none, o.nn)
    | some prev => (moved || c.msg b o.nn prev != prev, c.msg b o.nn prev)
  (r.1, { st with ml := upd st.ml b (some r.2), sure := upd st.sure b (some sur),
                  rd := upd st.rd b (some (vn, vs, o)),
                  tr := st.tr ++ [⟨b, mode, keep, o.nn, sur, st.ml b, r.2, r.1⟩] })

/-- The test `dirty` of the loop: never ran, or a kid changed at or after the last run. -/
def dirty (c : Cfg B N) (st : St B N) (b : B) : Bool :=
  match st.ran b with
  | none => true
  | some r => (c.kids b).any (fun k => decide (r ≤ (st.chg k).getD 0))

/-- One member in a sweep (lines 3696 to 3708). -/
def sweepStep (c : Cfg B N) (top : B → N) (st : St B N) (b : B) : St B N :=
  if dirty c st b then
    let t := st.tick + 1
    let r := member c top b Mode.must (decide (4 * c.scc.length < t)) st
    { r.2 with any := true, tick := t, ran := upd r.2.ran b (some t),
               chg := if r.1 then upd r.2.chg b (some t) else r.2.chg }
  else st

def sweep (c : Cfg B N) (top : B → N) (st : St B N) : St B N :=
  c.order.foldl (sweepStep c top) st

/-- The sweep loop, with fuel (lines 3692 to 3717): `none` when the fuel runs out. -/
def loop (c : Cfg B N) (top : B → N) : Nat → St B N → Option (St B N)
  | 0, _ => none
  | n + 1, st =>
    let s := sweep c top st
    let s := { s with sw := s.sw ++ [s.any] }
    if s.any then loop c top n { s with any := false } else some s

/-- The `%may` sweep (lines 3683 to 3687). -/
def maySweep (c : Cfg B N) (st : St B N) : St B N :=
  c.order.foldl (fun st b => (member c (fun _ => c.none) b Mode.may false st).2) st

/-- The final pass (lines 3618 to 3626), `top` empty. -/
def final (c : Cfg B N) (keep : Bool) (st : St B N) : St B N :=
  c.scc.foldl (fun st b => (member c (fun _ => c.none) b Mode.done keep st).2) st

/-- The empty state. -/
def St.empty : St B N := ⟨fun _ => none, fun _ => none, 0, fun _ => none, fun _ => none,
  false, fun _ => none, [], []⟩

/-- `top`: the needs of the `%may` sweep. -/
def topOf (c : Cfg B N) (sm : St B N) (k : B) : N := (sm.ml k).getD c.none

/-- `+compile-scc-in` after the cache test, from `sure.cache` at the members: the final state,
whose `ml` are the needs of the entries.  `done`: one bell that does not call itself. -/
def compileSccIn (c : Cfg B N) (done : Bool) (fuel : Nat) (st0 : St B N) : Option (St B N) :=
  if done then some (final c false st0) else
  let sm := maySweep c st0
  let st1 : St B N := { sm with ml := fun _ => none, tick := 0, ran := fun _ => none,
                                chg := fun _ => none, any := false, rd := fun _ => none }
  (loop c (topOf c sm) fuel st1).map (final c true)

/-! ## The views -/

theorem member_view_ne (c : Cfg B N) (top : B → N) (b : B) (m : Mode) (keep : Bool)
    (st : St B N) {k : B} (hk : k ≠ b) :
    viewN top (member c top b m keep st).2 k = viewN top st k ∧
    viewS c (member c top b m keep st).2 k = viewS c st k := by
  simp only [member, viewN, viewS]
  split <;> simp [upd_ne _ _ hk]

theorem member_view_same (c : Cfg B N) (top : B → N) (b : B) (m : Mode) (keep : Bool)
    (st : St B N) (h : (member c top b m keep st).1 = false) :
    viewN top (member c top b m keep st).2 b = viewN top st b ∧
    viewS c (member c top b m keep st).2 b = viewS c st b := by
  revert h
  simp only [member, viewN, viewS]
  split
  · next hml =>
    intro h
    simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    simp [hml, h1, h2, h3]
  · next prev hml =>
    intro h
    simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at h
    obtain ⟨h1, h2⟩ := h
    simp [hml, h1, h2]

theorem member_view (c : Cfg B N) (top : B → N) (b : B) (m : Mode) (keep : Bool)
    (st : St B N) (k : B) (h : k ≠ b ∨ (member c top b m keep st).1 = false) :
    viewN top (member c top b m keep st).2 k = viewN top st k ∧
    viewS c (member c top b m keep st).2 k = viewS c st k := by
  by_cases hk : k = b
  · subst hk
    exact member_view_same c top k m keep st (h.resolve_left (fun x => x rfl))
  · exact member_view_ne c top b m keep st hk

@[simp] theorem member_ran (c : Cfg B N) (top : B → N) (b : B) (m : Mode) (keep : Bool)
    (st : St B N) : (member c top b m keep st).2.ran = st.ran := by
  simp only [member]

@[simp] theorem member_chg (c : Cfg B N) (top : B → N) (b : B) (m : Mode) (keep : Bool)
    (st : St B N) : (member c top b m keep st).2.chg = st.chg := by
  simp only [member]

@[simp] theorem member_tick (c : Cfg B N) (top : B → N) (b : B) (m : Mode) (keep : Bool)
    (st : St B N) : (member c top b m keep st).2.tick = st.tick := by
  simp only [member]

@[simp] theorem member_any (c : Cfg B N) (top : B → N) (b : B) (m : Mode) (keep : Bool)
    (st : St B N) : (member c top b m keep st).2.any = st.any := by
  simp only [member]

theorem member_rd (c : Cfg B N) (top : B → N) (b : B) (m : Mode) (keep : Bool)
    (st : St B N) : (member c top b m keep st).2.rd =
      upd st.rd b (some (viewN top st, viewS c st, c.comp b m (viewN top st) (viewS c st))) := by
  simp only [member]

theorem member_ml_some (c : Cfg B N) (top : B → N) (b : B) (m : Mode) (keep : Bool)
    (st : St B N) : ((member c top b m keep st).2.ml b).isSome ∧
      ((member c top b m keep st).2.sure b).isSome := by
  simp only [member]; split <;> simp

theorem member_ml_ne (c : Cfg B N) (top : B → N) (b : B) (m : Mode) (keep : Bool)
    (st : St B N) {k : B} (hk : k ≠ b) : (member c top b m keep st).2.ml k = st.ml k ∧
      (member c top b m keep st).2.sure k = st.sure k ∧
      (member c top b m keep st).2.rd k = st.rd k := by
  simp only [member]; split <;> simp [upd_ne _ _ hk]

/-! ## Property (a): how the loop ends -/

/-- The invariant of the loop: a member that ran read, at its last compile, the views that
each kid still has, unless that kid changed at or after that compile; the members that ran
have an entry and an entry of `sure.cache`; the ticks are at most `tick`. -/
def Inv (c : Cfg B N) (top : B → N) (st : St B N) : Prop :=
  ∀ b r, st.ran b = some r → r ≤ st.tick ∧ (st.ml b).isSome ∧ (st.sure b).isSome ∧
    ∃ vn vs o, st.rd b = some (vn, vs, o) ∧ o = c.comp b Mode.must vn vs ∧
      ∀ k ∈ c.kids b, (st.chg k).getD 0 < r → vn k = viewN top st k ∧ vs k = viewS c st k

theorem sweepStep_inv (c : Cfg B N) (top : B → N) (st : St B N) (b : B)
    (h : Inv c top st) : Inv c top (sweepStep c top st b) := by
  unfold sweepStep
  split
  · next hd =>
    intro x r hx
    simp only at hx ⊢
    obtain ⟨ch, st', hm⟩ : ∃ ch st', member c top b Mode.must (decide (4 * c.scc.length < st.tick + 1)) st = (ch, st') := ⟨_, _, rfl⟩
    have hm1 := member_ml_some c top b Mode.must (decide (4 * c.scc.length < st.tick + 1)) st
    have hrd1 := member_rd c top b Mode.must (decide (4 * c.scc.length < st.tick + 1)) st
    have hran := member_ran c top b Mode.must (decide (4 * c.scc.length < st.tick + 1)) st
    have hchg := member_chg c top b Mode.must (decide (4 * c.scc.length < st.tick + 1)) st
    have hv' := member_view c top b Mode.must (decide (4 * c.scc.length < st.tick + 1)) st
    have hmn : ∀ y, y ≠ b → st'.ml y = st.ml y ∧ st'.sure y = st.sure y ∧ st'.rd y = st.rd y := by
      intro y hy
      have := member_ml_ne c top b Mode.must (decide (4 * c.scc.length < st.tick + 1)) st hy
      rw [hm] at this; exact this
    rw [hm] at hm1 hrd1 hran hchg hv' hx ⊢
    simp only at hm1 hrd1 hran hchg hv' hx ⊢
    by_cases hxb : x = b
    · subst hxb
      simp only [upd_same, Option.some.injEq] at hx
      subst hx
      refine ⟨Nat.le_refl _, hm1.1, hm1.2, ?_⟩
      refine ⟨viewN top st, viewS c st, _, by rw [hrd1]; simp, rfl, ?_⟩
      intro k hk hlt
      by_cases hkx : k = x
      · subst hkx
        cases ch with
        | true => simp at hlt
        | false => exact ⟨(hv' k (Or.inr rfl)).1.symm, (hv' k (Or.inr rfl)).2.symm⟩
      · exact ⟨(hv' k (Or.inl hkx)).1.symm, (hv' k (Or.inl hkx)).2.symm⟩
    · rw [upd_ne _ _ hxb, hran] at hx
      have hm := hmn x hxb
      obtain ⟨hle, hml, hsu, vn, vs, o, hrd, ho, hv⟩ := h x r hx
      refine ⟨Nat.le_succ_of_le hle, ?_, ?_, vn, vs, o, ?_, ho, ?_⟩
      · rw [hm.1]; exact hml
      · rw [hm.2.1]; exact hsu
      · rw [hm.2.2]; exact hrd
      intro k hk hlt
      by_cases hkb : k = b
      · subst hkb
        cases ch with
        | true =>
          simp only [ite_true, upd_same, Option.getD_some] at hlt
          omega
        | false =>
          simp only [Bool.false_eq_true, ite_false] at hlt
          rw [hchg] at hlt
          show vn k = viewN top st' k ∧ vs k = viewS c st' k
          rw [(hv' k (Or.inr rfl)).1, (hv' k (Or.inr rfl)).2]; exact hv k hk hlt
      · have hlt' : (st.chg k).getD 0 < r := by
          cases ch <;> simp_all [upd_ne _ _ hkb]
        show vn k = viewN top st' k ∧ vs k = viewS c st' k
        rw [(hv' k (Or.inl hkb)).1, (hv' k (Or.inl hkb)).2]; exact hv k hk hlt'
  · exact h

theorem sweep_inv_foldl (c : Cfg B N) (top : B → N) (l : List B) (st : St B N)
    (h : Inv c top st) : Inv c top (l.foldl (sweepStep c top) st) := by
  induction l generalizing st with
  | nil => exact h
  | cons b l ih => exact ih _ (sweepStep_inv c top st b h)

/-- A sweep step keeps `any` once set. -/
theorem sweepStep_any (c : Cfg B N) (top : B → N) (st : St B N) (b : B) (h : st.any = true) :
    (sweepStep c top st b).any = true := by
  unfold sweepStep; split <;> simp [h]

theorem foldl_any (c : Cfg B N) (top : B → N) (l : List B) (st : St B N) (h : st.any = true) :
    (l.foldl (sweepStep c top) st).any = true := by
  induction l generalizing st with
  | nil => exact h
  | cons b l ih => exact ih _ (sweepStep_any c top st b h)

/-- A sweep that sets no `any` compiles nothing: no member was dirty, and the state is as it
was. -/
theorem foldl_noany (c : Cfg B N) (top : B → N) (l : List B) (st : St B N)
    (h0 : st.any = false) (h : (l.foldl (sweepStep c top) st).any = false) :
    l.foldl (sweepStep c top) st = st ∧ ∀ b ∈ l, dirty c st b = false := by
  induction l generalizing st with
  | nil => exact ⟨rfl, by simp⟩
  | cons b l ih =>
    simp only [List.foldl_cons] at h ⊢
    by_cases hd : dirty c st b = true
    · have : (sweepStep c top st b).any = true := by unfold sweepStep; simp [hd]
      rw [foldl_any c top l _ this] at h; exact absurd h (by simp)
    · have hs : sweepStep c top st b = st := by unfold sweepStep; simp [hd]
      rw [hs] at h ⊢
      obtain ⟨h1, h2⟩ := ih st h0 h
      refine ⟨h1, ?_⟩
      intro x hx
      cases hx with
      | head => simpa using hd
      | tail _ hx => exact h2 x hx

theorem dirty_false (c : Cfg B N) (st : St B N) (b : B) (h : dirty c st b = false) :
    ∃ r, st.ran b = some r ∧ ∀ k ∈ c.kids b, (st.chg k).getD 0 < r := by
  unfold dirty at h
  split at h
  · simp at h
  · next r hr =>
    refine ⟨r, hr, fun k hk => ?_⟩
    have := List.any_eq_false.mp h k hk
    simp at this; omega

/-- **Property (a).**  The loop ends (on fuel enough) with a sweep that compiles nothing:
`any` is false, and every member ran after the last change of each of its kids (a self call
included: `chg b < ran b`, so its last compile did not change it). -/
theorem loop_end (c : Cfg B N) (top : B → N) (n : Nat) (st s : St B N) (h0 : st.any = false)
    (h : loop c top n st = some s) :
    s.any = false ∧ ∀ b ∈ c.order, ∃ r, s.ran b = some r ∧ ∀ k ∈ c.kids b, (s.chg k).getD 0 < r := by
  induction n generalizing st with
  | zero => simp [loop] at h
  | succ n ih =>
    simp only [loop] at h
    split at h
    · exact ih _ rfl h
    · next hany =>
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.not_eq_true] at hany
      obtain ⟨heq, hd⟩ := foldl_noany c top c.order st h0 hany
      refine ⟨hany, fun b hb => ?_⟩
      have := dirty_false c st b (hd b hb)
      simp only [sweep, heq]; exact this

theorem loop_inv (c : Cfg B N) (top : B → N) (n : Nat) (st s : St B N) (hi : Inv c top st)
    (h : loop c top n st = some s) : Inv c top s := by
  induction n generalizing st with
  | zero => simp [loop] at h
  | succ n ih =>
    simp only [loop] at h
    have hs := sweep_inv_foldl c top c.order st hi
    split at h
    · refine ih _ ?_ h; exact hs
    · simp only [Option.some.injEq] at h; subst h; exact hs

/-- **Property (a), what the callers read.**  At the end of the loop, the last compile of every
member read exactly the views that its kids have at the end, and its output is the compile on
those views.  So no member's need or `sur` changed after a caller read it. -/
theorem loop_reads (c : Cfg B N) (top : B → N) (n : Nat) (st s : St B N) (h0 : st.any = false)
    (hi : Inv c top st) (h : loop c top n st = some s) :
    ∀ b ∈ c.order, (s.ml b).isSome ∧ (s.sure b).isSome ∧ ∃ vn vs, s.rd b = some (vn, vs,
      c.comp b Mode.must vn vs) ∧ ∀ k ∈ c.kids b, vn k = viewN top s k ∧ vs k = viewS c s k := by
  intro b hb
  obtain ⟨-, hend⟩ := loop_end c top n st s h0 h
  obtain ⟨r, hr, hk⟩ := hend b hb
  obtain ⟨-, hml, hsu, vn, vs, o, hrd, ho, hv⟩ := loop_inv c top n st s hi h b r hr
  subst ho
  exact ⟨hml, hsu, vn, vs, hrd, fun k hkk => hv k hkk (hk k hkk)⟩

theorem inv_empty (c : Cfg B N) (top : B → N) (st : St B N) (h : ∀ b, st.ran b = none) :
    Inv c top st := by
  intro b r hr; rw [h b] at hr; cases hr

/-! ## Properties (b) and (c): the final pass -/

/-- The hypotheses on the member compile and on `+msg-need-ord` that (b) needs.
* `kidsOnly`: the compile of `b` reads the views of its kids only (determinism: it is a
  function of the needs table restricted to the kids and of its own inputs).
* `shape`: the final compile (`%done`: `+run`, `+collapse-shape`, `+bake-need`) finds the
  `need-new` of the sweeps' compile (`%must`: `+run-shape`, `+laze-collapse`,
  `+bake-need-ord`) on the same views; this is the debug assert `shape-check` of line 3549.
* `msgSelf`: line 3358, `?:  =(a b)  a`.
* `msgAbs`: `+msg-need-ord` absorbs: `(msg n (msg n p)) = (msg n p)`. -/
structure Hyp (c : Cfg B N) : Prop where
  kidsOnly : ∀ b m vn vs vn' vs', (∀ k ∈ c.kids b, vn k = vn' k ∧ vs k = vs' k) →
    c.comp b m vn vs = c.comp b m vn' vs'
  shape : ∀ b vn vs, (c.comp b Mode.done vn vs).nn = (c.comp b Mode.must vn vs).nn
  msgSelf : ∀ b n, c.msg b n n = n
  msgAbs : ∀ b n p, c.msg b n (c.msg b n p) = c.msg b n p

/-- What the last compile of a member left: the entry is `need-new` or its `+msg-need-ord` with
an older need. -/
def Left (c : Cfg B N) (s : St B N) (b : B) : Prop :=
  ∃ vn vs, s.rd b = some (vn, vs, c.comp b Mode.must vn vs) ∧
    (s.ml b = some (c.comp b Mode.must vn vs).nn ∨
      ∃ p, s.ml b = some (c.msg b (c.comp b Mode.must vn vs).nn p))

theorem member_left (c : Cfg B N) (top : B → N) (b : B) (keep : Bool) (st : St B N) :
    Left c (member c top b Mode.must keep st).2 b := by
  refine ⟨viewN top st, viewS c st, by rw [member_rd]; simp, ?_⟩
  simp only [member]
  split
  · left; simp
  · next p _ => right; exact ⟨p, by simp⟩

theorem sweepStep_left (c : Cfg B N) (top : B → N) (st : St B N) (b x : B)
    (h : (st.ran x).isSome → Left c st x) :
    ((sweepStep c top st b).ran x).isSome → Left c (sweepStep c top st b) x := by
  unfold sweepStep
  split
  · intro hx
    by_cases hxb : x = b
    · subst hxb
      obtain ⟨vn, vs, h1, h2⟩ := member_left c top x (decide (4 * c.scc.length < st.tick + 1)) st
      exact ⟨vn, vs, h1, h2⟩
    · simp only [upd_ne _ _ hxb, member_ran] at hx
      obtain ⟨vn, vs, h1, h2⟩ := h hx
      have hm := member_ml_ne c top b Mode.must (decide (4 * c.scc.length < st.tick + 1)) st hxb
      refine ⟨vn, vs, ?_, ?_⟩
      · simp only; rw [hm.2.2]; exact h1
      · simp only; rw [hm.1]; exact h2
  · exact h

theorem loop_left (c : Cfg B N) (top : B → N) (n : Nat) (st s : St B N) (x : B)
    (hi : (st.ran x).isSome → Left c st x) (h : loop c top n st = some s) :
    (s.ran x).isSome → Left c s x := by
  have hf : ∀ (l : List B) (st : St B N), ((st.ran x).isSome → Left c st x) →
      ((l.foldl (sweepStep c top) st).ran x).isSome → Left c (l.foldl (sweepStep c top) st) x := by
    intro l
    induction l with
    | nil => intro st h; exact h
    | cons b l ih => intro st h; exact ih _ (sweepStep_left c top st b x h)
  induction n generalizing st with
  | zero => simp [loop] at h
  | succ n ih =>
    simp only [loop] at h
    have hs := hf c.order st hi
    split at h
    · refine ih _ ?_ h; exact hs
    · simp only [Option.some.injEq] at h; subst h; exact hs

/-- The final pass on a state `s` the loop left: a member `b` compiled on a state `st` with the
entries and `sure.cache` of `s` changes nothing (`chg` false), finds `need-new` of its last
sweep (`nn`) and `need-pessimized = prev` (the entry it finds), and leaves the entries and
`sure.cache` as they were. -/
theorem final_member (c : Cfg B N) (hy : Hyp c) (top : B → N) (s st : St B N) (b : B)
    (hml : ∀ k, st.ml k = s.ml k) (hsu : ∀ k, st.sure k = s.sure k)
    (hkid : ∀ k ∈ c.kids b, (s.ml k).isSome)
    (hb : (s.sure b).isSome)
    (hL : Left c s b) (hreads : ∀ vn vs o, s.rd b = some (vn, vs, o) →
      ∀ k ∈ c.kids b, vn k = viewN top s k ∧ vs k = viewS c s k) :
    let r := member c (fun _ => c.none) b Mode.done true st
    r.1 = false ∧ (∀ k, r.2.ml k = s.ml k) ∧ (∀ k, r.2.sure k = s.sure k) ∧
      ∃ vn vs, s.rd b = some (vn, vs, c.comp b Mode.must vn vs) ∧
        (c.comp b Mode.done (viewN (fun _ => c.none) st) (viewS c st)).nn =
          (c.comp b Mode.must vn vs).nn ∧
        st.ml b = some (c.msg b (c.comp b Mode.must vn vs).nn ((st.ml b).getD c.none)) := by
  obtain ⟨vn, vs, hrd, hent⟩ := hL
  have hv := hreads vn vs _ hrd
  -- the views of the kids in the final pass are those of the last compile
  have hsame : ∀ k ∈ c.kids b, viewN (fun _ => c.none) st k = vn k ∧ viewS c st k = vs k := by
    intro k hk
    obtain ⟨h1, h2⟩ := hv k hk
    obtain ⟨y, hy'⟩ := Option.isSome_iff_exists.mp (hkid k hk)
    refine ⟨?_, ?_⟩
    · rw [h1]; simp [viewN, hml k, hy']
    · rw [h2]; simp [viewS, hsu k]
  have hcomp : c.comp b Mode.done (viewN (fun _ => c.none) st) (viewS c st) =
      c.comp b Mode.done vn vs := hy.kidsOnly b Mode.done _ _ _ _ hsame
  have hnn : (c.comp b Mode.done (viewN (fun _ => c.none) st) (viewS c st)).nn =
      (c.comp b Mode.must vn vs).nn := by rw [hcomp, hy.shape]
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hb
  -- the entry is a fixed point of `msg` with `need-new`
  have hfix : ∃ e, s.ml b = some e ∧ c.msg b (c.comp b Mode.must vn vs).nn e = e := by
    rcases hent with h | ⟨p, h⟩
    · exact ⟨_, h, hy.msgSelf _ _⟩
    · exact ⟨_, h, hy.msgAbs _ _ _⟩
  obtain ⟨e, he, hmsg⟩ := hfix
  have hstml : st.ml b = some e := by rw [hml b, he]
  refine ⟨?_, ?_, ?_, vn, vs, hrd, hnn, ?_⟩
  · simp only [member, hstml, hnn, hmsg, hsu b, hw]; simp
  · intro k
    by_cases hk : k = b
    · subst hk; simp only [member, hstml, hnn, hmsg]; simp [he]
    · rw [(member_ml_ne c _ b _ _ st hk).1, hml k]
  · intro k
    by_cases hk : k = b
    · subst hk; simp only [member, hsu k, hw]; simp
    · rw [(member_ml_ne c _ b _ _ st hk).2.1, hsu k]
  · simp [hstml, hmsg]

/-- **Properties (b) and (c).**  After the loop, the final pass (`final &`) leaves every entry
and every entry of `sure.cache` as the loop left them, whatever the order of its `+roll`, and
every compile in it changes nothing.  So the need of the entry the final pass puts for a member
is the need its callers read in the final pass and in the last sweep.  On each member,
`final_member` gives `need-new` of the last sweep and `need-pessimized = prev`. -/
theorem final_keeps (c : Cfg B N) (hy : Hyp c) (top : B → N) (n : Nat) (st s : St B N)
    (h0 : st.any = false) (hi : Inv c top st)
    (hleft : ∀ x, (st.ran x).isSome → Left c st x)
    (hscc : ∀ b ∈ c.scc, b ∈ c.order) (hkids : ∀ b, ∀ k ∈ c.kids b, k ∈ c.order)
    (h : loop c top n st = some s) :
    (∀ k, (final c true s).ml k = s.ml k) ∧ (∀ k, (final c true s).sure k = s.sure k) := by
  have hreads := loop_reads c top n st s h0 hi h
  obtain ⟨-, hend⟩ := loop_end c top n st s h0 h
  have hL : ∀ b ∈ c.order, Left c s b := by
    intro b hb
    obtain ⟨r, hr, -⟩ := hend b hb
    exact loop_left c top n st s b (hleft b) h (by simp [hr])
  suffices H : ∀ (l : List B) (st' : St B N), (∀ b ∈ l, b ∈ c.order) →
      (∀ k, st'.ml k = s.ml k) → (∀ k, st'.sure k = s.sure k) →
      (∀ k, (l.foldl (fun st b => (member c (fun _ => c.none) b Mode.done true st).2) st').ml k
        = s.ml k) ∧
      (∀ k, (l.foldl (fun st b => (member c (fun _ => c.none) b Mode.done true st).2) st').sure k
        = s.sure k) by
    exact H c.scc s hscc (fun _ => rfl) (fun _ => rfl)
  intro l
  induction l with
  | nil => intro st' _ h1 h2; exact ⟨h1, h2⟩
  | cons b l ih =>
    intro st' hl h1 h2
    have hb := hl b (List.mem_cons_self ..)
    obtain ⟨-, hsu, vn, vs, hrd, hv⟩ := hreads b hb
    have hm := final_member c hy top s st' b h1 h2 (fun k hk => (hreads k (hkids b k hk)).1)
      hsu (hL b hb) (by
        intro vn' vs' o hrd'
        rw [hrd] at hrd'
        simp only [Option.some.injEq, Prod.mk.injEq] at hrd'
        obtain ⟨rfl, rfl, -⟩ := hrd'
        exact hv)
    exact ih _ (fun x hx => hl x (List.mem_cons_of_mem _ hx)) hm.2.1 hm.2.2.1

/-! ## The dumps of the real compiler (`tools/hoon/sccloop.py`) -/

/-- One compile as the instrumented `member` printed it. -/
structure Rec where
  b : Nat
  mode : Mode
  keep : Bool
  views : List (Nat × NeedOrd × NeedOrd)
  nn : NeedOrd
  surRaw : NeedOrd
  sur : NeedOrd
  was : Option NeedOrd
  moved : Bool
  prev : Option NeedOrd
  np : NeedOrd

/-- One SCC that went through the loop. -/
structure Dump where
  mem : List Nat
  order : List Nat
  kids : List (Nat × List Nat)
  capes : List (Nat × Cape)
  top : List (Nat × NeedOrd)
  comps : List Rec
  sweeps : List Bool
  fin : List (Nat × NeedOrd)

end Formalization.SkaModel.SccLoop
