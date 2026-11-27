import lemmas.Ska.SccLoop
import lemmas.Ska.SccLoopCycle

/-! # The loop of `+compile-scc-in` ends under `Ranked` (README Gaps 21.8.5)

`cyc_never` (`Ska/SccLoopCycle.lean`) shows that `Hyp` does not make the sweep loop end: a
member compile whose `need-new` follows `this ↦ bTT ↦ bBig ↦ this` keeps changing its entry.
`Ranked` is the hypothesis on the member compile that excludes such a fall: a rank on the
entries of each member, at most `H`, that `need-pessimized` can only raise, where the entry
`prev` it is taken with is the member's own view of itself (`+callee-need` reads the entry of
`map-local`).  Under it the loop returns on the fuel `phi st + 2`
(`loop_total`), which on the state `compileSccIn` starts the loop from is
`4 * |scc| + |order| * (H + 1) + 2` (`compileSccIn_total`).

The measure: `phi` adds the ticks left before `keep` (`4 * |scc| - tick`) and, over `order`,
`H + 1` for a member without an entry and `H - rk prev` for one with the entry `prev`.  A
compile never raises it (`sweepStep_psi`: with the number `nch` of compiles that reported a
change, `phi + nch` does not grow), a change before `keep` costs a tick, and a change after
`keep` raises the rank of the entry, since `sur` is then frozen (`moved` is false).  A sweep
without a change is followed by a sweep that compiles nothing (`quiet_clean`).

`cyc_not_ranked`: the configuration of `cyc_never` is not `Ranked`. -/

namespace Formalization.SkaModel.SccLoop
open Formalization.SkaModel Formalization.SkaModel.Comp

variable {B N : Type} [DecidableEq B] [DecidableEq N]

/-- **The hypothesis under which the loop ends.**  A rank on the entries of each member,
bounded by `H`, that a `%must` compile raises whenever its `need-pessimized` (the
`+msg-need-ord` of `need-new` with the entry `vn b`, which is the member's view of itself)
differs from the entry.  On the real compiler: README Gaps 21.8.5 (`tools/hoon/sccfall.py`, the
probe tables). -/
structure Ranked (c : Cfg B N) where
  rk : B → N → Nat
  H : Nat
  le_H : ∀ b p, rk b p ≤ H
  up : ∀ b (vn vs : B → N), c.msg b (c.comp b Mode.must vn vs).nn (vn b) ≠ vn b →
    rk b (vn b) < rk b (c.msg b (c.comp b Mode.must vn vs).nn (vn b))

/-- The part of the measure of one member. -/
def phiB {c : Cfg B N} (r : Ranked c) (st : St B N) (b : B) : Nat :=
  match st.ml b with
  | none => r.H + 1
  | some p => r.H - r.rk b p

/-- The measure of the loop. -/
def phi {c : Cfg B N} (r : Ranked c) (st : St B N) : Nat :=
  (4 * c.scc.length - st.tick) + (c.order.map (phiB r st)).sum

/-- The compiles that reported a change (ghost: from the trace). -/
def nch (st : St B N) : Nat := (st.tr.filter (fun e => e.ch)).length

/-- What the loop keeps: a member with an entry has an entry of `sure.cache`, and the ticks of
the changes are at most `tick`. -/
def Ok (st : St B N) : Prop :=
  (∀ b, (st.ml b).isSome → (st.sure b).isSome) ∧ ∀ k, (st.chg k).getD 0 ≤ st.tick

theorem sum_map_le {l : List B} {f g : B → Nat} (h : ∀ x ∈ l, g x ≤ f x) :
    (l.map g).sum ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a (by simp)
    have h2 := ih (fun x hx => h x (by simp [hx]))
    omega

theorem sum_map_lt {l : List B} {f g : B → Nat} (h : ∀ x ∈ l, g x ≤ f x) {b : B} (hb : b ∈ l)
    (hlt : g b < f b) : (l.map g).sum < (l.map f).sum := by
  induction l with
  | nil => cases hb
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a (by simp)
    have h2 := sum_map_le (l := l) (f := f) (g := g) (fun x hx => h x (by simp [hx]))
    rcases List.mem_cons.mp hb with e | hb'
    · subst e; omega
    · have := ih (fun x hx => h x (by simp [hx])) hb'; omega

/-! ## One compile -/

theorem filter_ch_snoc (l : List (Ev B N)) (e : Ev B N) :
    ((l ++ [e]).filter (fun e => e.ch)).length =
      (l.filter (fun e => e.ch)).length + (if e.ch then 1 else 0) := by
  cases h : e.ch <;> simp [List.filter_append, h]

theorem member_tr (c : Cfg B N) (top : B → N) (b : B) (m : Mode) (keep : Bool) (st : St B N) :
    nch (member c top b m keep st).2 = nch st + (if (member c top b m keep st).1 then 1 else 0) := by
  unfold nch member
  exact filter_ch_snoc _ _

theorem member_phiB_ne {c : Cfg B N} (r : Ranked c) (top : B → N) (b : B) (m : Mode)
    (keep : Bool) (st : St B N) {x : B} (hx : x ≠ b) :
    phiB r (member c top b m keep st).2 x = phiB r st x := by
  unfold phiB; rw [(member_ml_ne c top b m keep st hx).1]

/-- The compile of `b` does not raise its part of the measure, and lowers it when it reports a
change after `keep` (when an entry of `b` comes with an entry of `sure.cache`). -/
theorem member_phiB {c : Cfg B N} (r : Ranked c) (top : B → N) (b : B) (keep : Bool)
    (st : St B N) :
    phiB r (member c top b Mode.must keep st).2 b ≤ phiB r st b ∧
    (keep = true → ((st.ml b).isSome → (st.sure b).isSome) →
      (member c top b Mode.must keep st).1 = true →
      phiB r (member c top b Mode.must keep st).2 b < phiB r st b) := by
  rcases hml : st.ml b with _ | prev
  · simp only [member, phiB, hml, upd_same]
    have := r.le_H b (c.comp b Mode.must (viewN top st) (viewS c st)).nn
    constructor
    · omega
    · intros; omega
  · have hv : viewN top st b = prev := by simp [viewN, hml]
    have hup := r.up b (viewN top st) (viewS c st)
    rw [hv] at hup
    simp only [member, phiB, hml, upd_same]
    by_cases he : c.msg b (c.comp b Mode.must (viewN top st) (viewS c st)).nn prev = prev
    · rw [he]
      refine ⟨Nat.le_refl _, fun hk hs hch => ?_⟩
      subst hk
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hs (by simp))
      simp [hw] at hch
    · have h1 := hup he
      have h2 := r.le_H b (c.msg b (c.comp b Mode.must (viewN top st) (viewS c st)).nn prev)
      constructor
      · omega
      · intros; omega

/-- **One step of a sweep** keeps `Ok` and does not raise `phi + nch`. -/
theorem sweepStep_psi {c : Cfg B N} (r : Ranked c) (top : B → N) (st : St B N) (b : B)
    (hb : b ∈ c.order) (h : Ok st) :
    Ok (sweepStep c top st b) ∧
    phi r (sweepStep c top st b) + nch (sweepStep c top st b) ≤ phi r st + nch st := by
  unfold sweepStep
  split
  · next hd =>
    obtain ⟨ch, st', hm⟩ : ∃ ch st', member c top b Mode.must
        (decide (4 * c.scc.length < st.tick + 1)) st = (ch, st') := ⟨_, _, rfl⟩
    have hmp := member_phiB r top b (decide (4 * c.scc.length < st.tick + 1)) st
    have hmt := member_tr c top b Mode.must (decide (4 * c.scc.length < st.tick + 1)) st
    have hms := member_ml_some c top b Mode.must (decide (4 * c.scc.length < st.tick + 1)) st
    have hne : ∀ x, x ≠ b → phiB r st' x = phiB r st x ∧ st'.ml x = st.ml x ∧
        st'.sure x = st.sure x := by
      intro x hx
      have e1 := member_phiB_ne r top b Mode.must (decide (4 * c.scc.length < st.tick + 1)) st hx
      have e2 := member_ml_ne c top b Mode.must (decide (4 * c.scc.length < st.tick + 1)) st hx
      rw [hm] at e1 e2; exact ⟨e1, e2.1, e2.2.1⟩
    have htk := member_tick c top b Mode.must (decide (4 * c.scc.length < st.tick + 1)) st
    have hcg := member_chg c top b Mode.must (decide (4 * c.scc.length < st.tick + 1)) st
    simp only
    rw [hm] at hmp hmt hms htk hcg ⊢
    simp only at hmp hmt hms htk hcg ⊢
    have hle : ∀ x ∈ c.order, phiB r st' x ≤ phiB r st x := by
      intro x _
      by_cases hx : x = b
      · subst hx; exact hmp.1
      · exact Nat.le_of_eq (hne x hx).1
    have hsum := sum_map_le hle
    -- `phi` of the record: the ml of `st'`, the tick `t`
    have hphi : phi r
          { st' with any := true, tick := st.tick + 1,
                     ran := upd st'.ran b (some (st.tick + 1)),
                     chg := (if ch = true then upd st'.chg b (some (st.tick + 1)) else st'.chg) } =
        (4 * c.scc.length - (st.tick + 1)) + (c.order.map (phiB r st')).sum := rfl
    have hnch : nch
          { st' with any := true, tick := st.tick + 1,
                     ran := upd st'.ran b (some (st.tick + 1)),
                     chg := (if ch = true then upd st'.chg b (some (st.tick + 1)) else st'.chg) } =
        nch st' := rfl
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro x hx
      by_cases hxb : x = b
      · subst hxb; exact hms.2
      · have hx' : (st'.ml x).isSome = true := hx
        show (st'.sure x).isSome = true
        rw [(hne x hxb).2.1] at hx'; rw [(hne x hxb).2.2]; exact h.1 x hx'
    · intro k
      show ((if ch = true then upd st'.chg b (some (st.tick + 1)) else st'.chg) k).getD 0 ≤
        st.tick + 1
      have := h.2 k
      cases ch with
      | false => simp only [Bool.false_eq_true, ite_false, hcg]; omega
      | true =>
        simp only [ite_true]
        by_cases hkb : k = b
        · subst hkb; simp
        · rw [upd_ne _ _ hkb, hcg]; omega
    · rw [hphi, hnch, hmt]
      unfold phi
      by_cases hk : 4 * c.scc.length < st.tick + 1
      · cases ch with
        | false => simp only [Bool.false_eq_true, ite_false]; omega
        | true =>
          have hlt := hmp.2 (by simp [hk]) (h.1 b) rfl
          have := sum_map_lt hle hb hlt
          simp only [ite_true]; omega
      · have : st.tick < 4 * c.scc.length := by omega
        cases ch <;> simp <;> omega
  · exact ⟨h, Nat.le_refl _⟩


/-! ## A sweep -/

theorem foldl_psi {c : Cfg B N} (r : Ranked c) (top : B → N) (l : List B)
    (hl : ∀ b ∈ l, b ∈ c.order) (st : St B N) (h : Ok st) :
    Ok (l.foldl (sweepStep c top) st) ∧
    phi r (l.foldl (sweepStep c top) st) + nch (l.foldl (sweepStep c top) st) ≤
      phi r st + nch st := by
  induction l generalizing st with
  | nil => exact ⟨h, Nat.le_refl _⟩
  | cons b l ih =>
    obtain ⟨h1, h2⟩ := sweepStep_psi r top st b (hl b (by simp)) h
    obtain ⟨h3, h4⟩ := ih (fun x hx => hl x (by simp [hx])) _ h1
    simp only [List.foldl_cons]
    exact ⟨h3, by omega⟩

theorem sweepStep_nch (c : Cfg B N) (top : B → N) (st : St B N) (b : B) :
    nch st ≤ nch (sweepStep c top st b) ∧
    (nch (sweepStep c top st b) = nch st → (sweepStep c top st b).chg = st.chg) := by
  unfold sweepStep
  split
  · have hmt := member_tr c top b Mode.must (decide (4 * c.scc.length < st.tick + 1)) st
    have hcg := member_chg c top b Mode.must (decide (4 * c.scc.length < st.tick + 1)) st
    obtain ⟨ch, st', hm⟩ : ∃ ch st', member c top b Mode.must
        (decide (4 * c.scc.length < st.tick + 1)) st = (ch, st') := ⟨_, _, rfl⟩
    simp only
    rw [hm] at hmt hcg ⊢
    simp only at hmt hcg ⊢
    show nch st ≤ nch st' ∧ (nch st' = nch st →
      (if ch = true then upd st'.chg b (some (st.tick + 1)) else st'.chg) = st.chg)
    cases ch with
    | false => simp only [Bool.false_eq_true, ite_false] at hmt ⊢; exact ⟨by omega, fun _ => hcg⟩
    | true => simp only [ite_true] at hmt ⊢; exact ⟨by omega, fun e => by omega⟩
  · exact ⟨Nat.le_refl _, fun _ => rfl⟩

theorem foldl_nch (c : Cfg B N) (top : B → N) (l : List B) (st : St B N) :
    nch st ≤ nch (l.foldl (sweepStep c top) st) := by
  induction l generalizing st with
  | nil => exact Nat.le_refl _
  | cons b l ih => exact Nat.le_trans (sweepStep_nch c top st b).1 (ih _)

theorem loopDirty_congr (c : Cfg B N) {s t : St B N} (b : B) (h1 : s.ran b = t.ran b)
    (h2 : s.chg = t.chg) : dirty c s b = dirty c t b := by
  unfold dirty; rw [h1, h2]

/-- A step that reports no change leaves every clean member clean. -/
theorem sweepStep_clean (c : Cfg B N) (top : B → N) (st : St B N) (x b : B)
    (hq : nch (sweepStep c top st x) = nch st) (hb : dirty c st b = false) :
    dirty c (sweepStep c top st x) b = false := by
  have hc := (sweepStep_nch c top st x).2 hq
  by_cases hd : dirty c st x = true
  · have hxb : b ≠ x := by intro e; subst e; rw [hb] at hd; cases hd
    have hr : (sweepStep c top st x).ran b = st.ran b := by
      unfold sweepStep; rw [if_pos hd]
      simp only [upd_ne _ _ hxb, member_ran]
    rw [loopDirty_congr c b hr hc]; exact hb
  · have : sweepStep c top st x = st := by unfold sweepStep; simp [hd]
    rw [this]; exact hb

/-- A step that compiles `x` and reports no change leaves `x` clean. -/
theorem sweepStep_self_clean (c : Cfg B N) (top : B → N) (st : St B N) (x : B) (h : Ok st)
    (hq : nch (sweepStep c top st x) = nch st) : dirty c (sweepStep c top st x) x = false := by
  have hc := (sweepStep_nch c top st x).2 hq
  by_cases hd : dirty c st x = true
  · have hr : (sweepStep c top st x).ran x = some (st.tick + 1) := by
      unfold sweepStep; rw [if_pos hd]; simp
    unfold dirty; rw [hr]
    simp only [List.any_eq_false, decide_eq_true_eq]
    intro k _
    rw [hc]; have := h.2 k; omega
  · have : sweepStep c top st x = st := by unfold sweepStep; simp [hd]
    rw [this]; simpa using hd

theorem foldl_clean (c : Cfg B N) (top : B → N) (l : List B) (st : St B N) (b : B)
    (hq : nch (l.foldl (sweepStep c top) st) = nch st) (hb : dirty c st b = false) :
    dirty c (l.foldl (sweepStep c top) st) b = false := by
  induction l generalizing st with
  | nil => exact hb
  | cons x l ih =>
    simp only [List.foldl_cons] at hq ⊢
    have h1 := (sweepStep_nch c top st x).1
    have h2 := foldl_nch c top l (sweepStep c top st x)
    exact ih _ (by omega) (sweepStep_clean c top st x b (by omega) hb)

/-- **A sweep that reports no change leaves every member clean**, so the next sweep compiles
nothing. -/
theorem quiet_clean {c : Cfg B N} (r : Ranked c) (top : B → N) (l : List B)
    (hl : ∀ b ∈ l, b ∈ c.order) (st : St B N) (h : Ok st)
    (hq : nch (l.foldl (sweepStep c top) st) = nch st) :
    ∀ b ∈ l, dirty c (l.foldl (sweepStep c top) st) b = false := by
  induction l generalizing st with
  | nil => intro b hb; cases hb
  | cons x l ih =>
    simp only [List.foldl_cons] at hq ⊢
    have h1 := (sweepStep_nch c top st x).1
    have h2 := foldl_nch c top l (sweepStep c top st x)
    have hok := (sweepStep_psi r top st x (hl x (by simp)) h).1
    intro b hb
    rcases List.mem_cons.mp hb with e | hb'
    · subst e
      exact foldl_clean c top l _ b (by omega) (sweepStep_self_clean c top st b h (by omega))
    · exact ih (fun y hy => hl y (by simp [hy])) _ hok (by omega) b hb'

theorem foldl_clean_id (c : Cfg B N) (top : B → N) (l : List B) (st : St B N)
    (h : ∀ b ∈ l, dirty c st b = false) : l.foldl (sweepStep c top) st = st := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldl_cons]
    have : sweepStep c top st x = st := by unfold sweepStep; simp [h x (by simp)]
    rw [this]; exact ih (fun b hb => h b (by simp [hb]))

theorem loop_clean (c : Cfg B N) (top : B → N) (m : Nat) (s : St B N)
    (hs : sweep c top s = s) (ha : s.any = false) : (loop c top (m + 1) s).isSome := by
  simp only [loop, hs, ha]; simp

/-! ## The loop ends -/

/-- **The loop returns on the fuel `phi st + 2`**, under `Ranked`, from a state that is `Ok`. -/
theorem loop_total {c : Cfg B N} (r : Ranked c) (top : B → N) :
    ∀ n (st : St B N), Ok st → phi r st + 2 ≤ n → (loop c top n st).isSome := by
  intro n
  induction n with
  | zero => intro st _ h; omega
  | succ n ih =>
    intro st hok hn
    have hps : Ok (sweep c top st) ∧
        phi r (sweep c top st) + nch (sweep c top st) ≤ phi r st + nch st :=
      foldl_psi r top c.order (fun b hb => hb) st hok
    have hm : nch st ≤ nch (sweep c top st) := foldl_nch c top c.order st
    simp only [loop]
    split
    · by_cases hq : nch (sweep c top st) = nch st
      · have hcl : ∀ b ∈ c.order, dirty c (sweep c top st) b = false :=
          quiet_clean r top c.order (fun b hb => hb) st hok hq
        cases n with
        | zero => omega
        | succ m =>
          exact loop_clean c top m _ (foldl_clean_id c top c.order _ hcl) rfl
      · have h3 : phi r (sweep c top st) + 2 ≤ n := by omega
        exact ih _ hps.1 h3
    · simp

theorem sum_map_const (l : List B) (k : Nat) : (l.map (fun _ => k)).sum = l.length * k := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; rw [Nat.succ_mul]; omega

/-- **`+compile-scc-in` returns**, under `Ranked`, on the fuel
`4 * |scc| + |order| * (H + 1) + 2`, from any state. -/
theorem compileSccIn_total {c : Cfg B N} (r : Ranked c) (done : Bool) (st0 : St B N) (n : Nat)
    (hn : 4 * c.scc.length + c.order.length * (r.H + 1) + 2 ≤ n) :
    (compileSccIn c done n st0).isSome := by
  unfold compileSccIn
  cases done
  · simp only [Bool.false_eq_true, if_false, Option.isSome_map]
    apply loop_total r
    · exact ⟨fun b hb => by simp at hb, fun k => by simp⟩
    · have e : ∀ st : St B N, (∀ b, st.ml b = none) → st.tick = 0 →
          phi r st = 4 * c.scc.length + c.order.length * (r.H + 1) := by
        intro st h1 h2
        unfold phi
        have : c.order.map (phiB r st) = c.order.map (fun _ => r.H + 1) :=
          List.map_congr_left (fun b _ => by simp [phiB, h1 b])
        rw [this, sum_map_const, h2]; omega
      rw [e _ (fun _ => rfl) rfl]; exact hn
  · simp

/-- The configuration of `cyc_never` is not `Ranked`: its entries would need
`rk this < rk bTT < rk bBig < rk this`. -/
theorem cyc_not_ranked (r : Ranked cyc) : False := by
  have h1 : r.rk 0 NeedOrd.this < r.rk 0 bTT :=
    r.up 0 (fun _ => NeedOrd.this) (fun _ => NeedOrd.none) (by decide)
  have h2 : r.rk 0 bTT < r.rk 0 bBig :=
    r.up 0 (fun _ => bTT) (fun _ => NeedOrd.none) (by decide)
  have h3 : r.rk 0 bBig < r.rk 0 NeedOrd.this :=
    r.up 0 (fun _ => bBig) (fun _ => NeedOrd.none) (by decide)
  omega

end Formalization.SkaModel.SccLoop
