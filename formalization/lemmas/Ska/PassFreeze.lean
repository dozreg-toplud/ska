import lemmas.Ska.PassStabM
import lemmas.Ska.ConvPass

/-!
# The freezing argument for the pass loop (track F, Gaps 16)

No global measure: along an infinite chain of passes of one component (root
`id`, the stack below it `rest`), the members (`MembR`: on the stack, not in
`rest`) that stay from some pass on have an eventually constant entry
(`chain_present_const`).  If they also have an eventually constant callee set
(`EvFrozen`, the claim left open), then every member is eventually one of them:
a member at a pass start is reached from the root over callees through members
(`cull_reach`, the `+cull` at the end of the previous pass), and a callee of a
member whose callee set is frozen stays on the stack (`cull_keeps_kid`).  Then
nothing moves at all, which a pass that goes on rules out (`PassMoves`: some
member of its start falls, is culled, or changes its callee set).  So the chain
cannot be infinite (`freeze_abstract`, `freeze_no_chain`), and `FinPushes`
holds vacuously (`finPushes_of_freeze`).

What is assumed, along each chain:
* `FinIdents` ((i)): the members of the passes are among a finite list.  The
  argument for it is Kruskal over `+he-sock` (`AnaEnds.lean`, README Gaps 16);
* `PassMoves` (C): held at every one of the 18,682 recorded passes that went on
  (`tools/hoon/passmeasure-stab.py`, candidate C).  On the Hoon it holds
  because a pass that goes on changes an entry or pushes, and the function
  pushed is a callee of the start member whose run pushed it (or of one pushed
  by it), absent from that member's callee set before (it was not in the
  graph); not proved on the model (it needs the arms' invariant for callee
  sets, as `ConvArms.lean` carries ticks);
* `EvFrozen` (R, the open claim): a member that stays on the stack from some
  pass on changes its callee set finitely often.  It fails only if such a
  member, with its entry constant, reruns forever; on the Hoon a member reruns
  only when a callee changed after its last run (`+dirty` is tested at the
  member's turn, not at the pass start), so it fails only if the callees that
  keep changing are members that do not stay: pushed again and culled again
  forever.  On the traces (`tools/hoon/passmeasure-freeze.py`, test T4) no
  member was ever dirty with its entry and callee set the same as at the
  previous start and owing its dirt only to such transient callees (0 of
  12,462 such starts).

Proved here: `passOn_dirty` (a pass that goes on had a member dirty at its
start), `cull_keeps_kid`, `cull_reach`, `passOn_cull` (the state before the
`+cull` of a pass), `freeze_abstract` (the argument on any sequence of states
with the five properties), `freeze_no_chain` (on the model, from `FinIdents`,
`PassMoves`, `EvFrozen`), `finPushes_of_freeze`.
-/

namespace Formalization
namespace SkaModel
namespace Ana

open Nock

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-- A member of the component: on the stack, above the fixed bottom `rest`. -/
def MembR (rest : List Ident) (st : SkaState M R) (x : Ident) : Prop := x ∈ st.stk ∧ x ∉ rest

/-! ## 1. A pass that goes on had a dirty member -/

/-- **A member loop over clean members runs nothing.** -/
theorem memberLoop_clean (env : Env R) (memoF : Memo M) :
    ∀ n index pass (ms : List Ident) (st : SkaState M R) r st',
      (∀ m ∈ ms, dirty m st = false) → memberLoop env memoF n index pass ms st = some (r, st') →
      r = (index, false) ∧ st' = st
  | 0 => by
    intro index pass ms st r st' _ h
    rw [memberLoop_zero] at h; cases h
  | n + 1 => by
    intro index pass ms st r st' hc h
    rw [memberLoop_succ] at h
    cases ms with
    | nil =>
      simp only [memberStep, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨h.1.symm, h.2.symm⟩
    | cons m ms =>
      simp only [memberStep, hc m List.mem_cons_self, if_true] at h
      exact memberLoop_clean env memoF n index pass ms st r st' (fun x hx => hc x (List.mem_cons_of_mem _ hx)) h

/-- **A pass that goes on had a member dirty at its start**: if every member
were clean, the member loop would run nothing, report no change and push
nothing, and the pass would stop. -/
theorem passOn_dirty {env : Env R} {memoF : Memo M} {n : Nat} {id : Ident} {index pass : Nat}
    {st st' : SkaState M R} (h : PassOn env memoF n id index pass st st') :
    ∃ ab, above id st.stk = some ab ∧ ∃ m ∈ ab, dirty m st = true := by
  obtain ⟨ab, members, r, st2, h1, h2, h3, _, h5, h6⟩ := h
  refine ⟨ab, h1, Classical.byContradiction fun hn => ?_⟩
  have hc : ∀ m ∈ members,
      dirty m ({ st with stats := { st.stats with passes := st.stats.passes + 1 } } : SkaState M R) = false := by
    intro m hm
    have hab : m ∈ ab := by
      obtain ⟨ab0, rest, rfl, _, _⟩ := above_eq h1
      rcases sweep_mem h2 m hm with rfl | hm'
      · exact List.mem_append_right _ List.mem_cons_self
      · exact (Treap.has_silt _ m).mp hm'
    cases e : dirty m st with
    | false => exact e
    | true => exact absurd ⟨m, hab, e⟩ hn
  obtain ⟨rfl, rfl⟩ := memberLoop_clean env memoF n index pass members _ r st2 hc h3
  have e := cull_next h5
  exact h6 ⟨rfl, e⟩

/-! ## 2. What `+cull` keeps -/

theorem kids_of_get {st st' : SkaState M R} {m : Ident} (h : Treap.get st'.g m = Treap.get st.g m) :
    kids st' m = kids st m := by
  unfold kids gitG Treap.gut; rw [h]

/-- **A callee of a member that `+cull` keeps is kept**, if it was a member. -/
theorem cull_keeps_kid {n : Nat} {id : Ident} {st st' : SkaState M R} {ab0 rest : List Ident} (hi : SInv st)
    (hs : st.stk = ab0 ++ id :: rest) (h : cull n id st = some st') {m c : Ident}
    (hm : MembR rest st' m) (hc : c ∈ kids st' m) (hc2 : MembR rest st c) : MembR rest st' c := by
  obtain ⟨live, hlive, -, hg, -, hstk, -⟩ := cull_eff hi hs h
  have hcl := liveLoop_closed n [id] Treap.empty live hlive
    (fun x hx => by simp [Treap.has, Treap.get_empty] at hx)
  have hin : ∀ x, x ∈ st.stk → x ∉ rest → x ∈ ab0 ++ [id] := by
    intro x hx hxr
    rw [hs] at hx
    rcases List.mem_append.mp hx with h' | h'
    · exact List.mem_append_left _ h'
    · rcases List.mem_cons.mp h' with rfl | h''
      · exact List.mem_append_right _ List.mem_cons_self
      · exact absurd h'' hxr
  have hm1 : m ∈ st.stk := by
    have := hm.1; rw [hstk] at this; exact (List.mem_filter.mp this).1
  have hm2 : ¬ (m ∈ ab0 ++ [id] ∧ Treap.has live m = false) := by
    have := hm.1; rw [hstk] at this
    have := (List.mem_filter.mp this).2
    intro ⟨a, b⟩; simp [a, b] at this
  have hml : Treap.has live m = true := by
    cases e : Treap.has live m with
    | true => rfl
    | false => exact absurd ⟨hin m hm1 hm.2, e⟩ hm2
  have hk : kids st' m = kids st m := kids_of_get (by rw [hg]; exact if_neg hm2)
  have hcm : Treap.has (Treap.silt (ab0 ++ [id]) : M Ident Unit) c = true :=
    (Treap.has_silt _ c).mpr (hin c hc2.1 hc2.2)
  have hcl' := hcl m hml c (hk ▸ hc) hcm
  refine ⟨?_, hc2.2⟩
  rw [hstk]
  refine List.mem_filter.mpr ⟨hc2.1, ?_⟩
  simp [hcl']

/-- **Every member after `+cull` is reached from the root**, over callees
through members. -/
theorem cull_reach {n : Nat} {id : Ident} {st st' : SkaState M R} {ab0 rest : List Ident} (hi : SInv st)
    (hs : st.stk = ab0 ++ id :: rest) (h : cull n id st = some st') {x : Ident}
    (hx : MembR rest st' x) : Reach st' (MembR rest st') id x := by
  obtain ⟨live, hlive, -, hg, -, hstk, -⟩ := cull_eff hi hs h
  have hnd : (ab0 ++ id :: rest).Nodup := hs ▸ hi.nodup
  have hidr : id ∉ rest := ((List.nodup_append.mp hnd).2.1 |> List.nodup_cons.mp).1
  have hcl := liveLoop_closed n [id] Treap.empty live hlive
    (fun x hx => by simp [Treap.has, Treap.get_empty] at hx)
  have hso := liveLoop_sound (a := id) n [id] Treap.empty live hlive
    (fun x hx => by simp [Treap.has, Treap.get_empty] at hx) (fun x hx => by
      rw [List.mem_singleton.mp hx]; exact Or.inl Reach.refl)
  have hin : ∀ x, x ∈ st.stk → x ∉ rest → x ∈ ab0 ++ [id] := by
    intro x hx hxr
    rw [hs] at hx
    rcases List.mem_append.mp hx with h' | h'
    · exact List.mem_append_left _ h'
    · rcases List.mem_cons.mp h' with rfl | h''
      · exact List.mem_append_right _ List.mem_cons_self
      · exact absurd h'' hxr
  let W : Ident → Prop := fun y => Treap.has (Treap.silt (ab0 ++ [id]) : M Ident Unit) y = true
  have hmemW : ∀ y, W y → y ∈ ab0 ++ [id] := fun y hy => (Treap.has_silt _ y).mp hy
  -- every live identity is kept, with its callees, and is a member after
  have hkeep : ∀ y, Treap.has live y = true → MembR rest st' y ∧ kids st' y = kids st y := by
    intro y hy
    have hnd' : ¬ (y ∈ ab0 ++ [id] ∧ Treap.has live y = false) := fun ⟨_, b⟩ => by simp [hy] at b
    refine ⟨⟨?_, ?_⟩, kids_of_get (by rw [hg]; exact if_neg hnd')⟩
    · have hyW : W y := by
        refine Classical.byContradiction fun hw => ?_
        -- a live identity is a member: liveLoop only marks members
        have := hso y hy
        cases this with
        | refl => exact hw ((Treap.has_silt _ _).mpr (List.mem_append_right _ List.mem_cons_self))
        | step _ _ hc => exact hw hc
      rw [hstk]
      refine List.mem_filter.mpr ⟨?_, by simp [hy]⟩
      rw [hs]
      rcases List.mem_append.mp (hmemW y hyW) with h' | h'
      · exact List.mem_append_left _ h'
      · rw [List.mem_singleton.mp h']; exact List.mem_append_right _ List.mem_cons_self
    · intro hr
      have hyW : y ∈ ab0 ++ [id] := by
        have := hso y hy
        cases this with
        | refl => exact List.mem_append_right _ List.mem_cons_self
        | step _ _ hc => exact hmemW _ hc
      rcases List.mem_append.mp hyW with h' | h'
      · exact (List.nodup_append.mp hnd).2.2 y h' y (List.mem_cons_of_mem _ hr) rfl
      · rw [List.mem_singleton.mp h'] at hr; exact hidr hr
  -- the reach of `liveLoop_sound` goes through live identities
  have hlv : ∀ y, Reach st W id y → Treap.has live y = true := by
    intro y hy
    induction hy with
    | refl => exact liveLoop_head hlive ((Treap.has_silt _ id).mpr (List.mem_append_right _ List.mem_cons_self))
    | step _ hk hw ih => exact hcl _ ih _ hk hw
  have hxl : Treap.has live x = true := by
    have hx1 : x ∈ st.stk := by have := hx.1; rw [hstk] at this; exact (List.mem_filter.mp this).1
    have hx2 := hx.1; rw [hstk] at hx2
    have := (List.mem_filter.mp hx2).2
    cases e : Treap.has live x with
    | true => rfl
    | false => simp [hin x hx1 hx.2, e] at this
  have hr := hso x hxl
  have : ∀ y, Reach st W id y → Reach st' (MembR rest st') id y := by
    intro y hy
    induction hy with
    | refl => exact Reach.refl
    | @step b c hb hk hw ih =>
      have hbl := hlv b hb
      have hcl2 := hlv c (Reach.step hb hk hw)
      exact Reach.step ih ((hkeep b hbl).2 ▸ hk) (hkeep c hcl2).1
  exact this x hr

/-- **The state before the `+cull` of a pass** that goes on: the member loop
only pushed on the stack, and the `+cull` gives the next state. -/
theorem passOn_cull (env : Env R) (memoF : Memo M) (hmF : MemoWF memoF) {n : Nat} {id : Ident}
    {index pass : Nat} {st st' : SkaState M R} (hi : SInv st)
    (h : PassOn env memoF n id index pass st st') :
    ∃ st2, SInv st2 ∧ (∃ l, st2.stk = l ++ st.stk) ∧ cull n id st2 = some st' := by
  obtain ⟨ab, members, r, st2, _, _, h3, _, h5, _⟩ := h
  have i1 : SInv ({ st with stats := { st.stats with passes := st.stats.passes + 1 } } : SkaState M R) :=
    hi.congr rfl rfl rfl rfl
  obtain ⟨s2, _, ⟨l, el⟩, _⟩ := (allP env memoF hmF n n (Nat.le_refl n)).2.2.2.2 index pass members _ r st2
    st.stk (fun _ => False) i1 ⟨[], (List.nil_append _).symm⟩ (fun _ h => h.elim) (fun _ _ h => h) h3
  exact ⟨st2, s2, ⟨l, el⟩, h5⟩

/-! ## 3. The argument on a sequence of states -/

/-- `x` is a member from some state on. -/
def Pers (rest : List Ident) (f : Nat → SkaState M R) (x : Ident) : Prop :=
  ∃ K, ∀ k, K ≤ k → MembR rest (f k) x

/-- From `K` on, `x` is a member and its value and callee set are constant. -/
def FrozenFrom (rest : List Ident) (f : Nat → SkaState M R) (x : Ident) (K : Nat) : Prop :=
  (∀ k, K ≤ k → MembR rest (f k) x) ∧ (∀ k, K ≤ k → valE (f (k + 1)) x = valE (f k) x) ∧
    ∀ k, K ≤ k → kids (f (k + 1)) x = kids (f k) x

theorem frozenFrom_mono {rest : List Ident} {f : Nat → SkaState M R} {x : Ident} {K K' : Nat}
    (h : FrozenFrom rest f x K) (hK : K ≤ K') : FrozenFrom rest f x K' :=
  ⟨fun k hk => h.1 k (Nat.le_trans hK hk), fun k hk => h.2.1 k (Nat.le_trans hK hk),
    fun k hk => h.2.2 k (Nat.le_trans hK hk)⟩

theorem kids_const_from {rest : List Ident} {f : Nat → SkaState M R} {x : Ident} {K : Nat}
    (h : FrozenFrom rest f x K) : ∀ k, K ≤ k → kids (f k) x = kids (f K) x := by
  intro k hk
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d with
  | zero => rfl
  | succ d ih => rw [← Nat.add_assoc, h.2.2 _ (Nat.le_add_right _ _)]; exact ih (Nat.le_add_right _ _)

theorem reach_mem {st : SkaState M R} {W : Ident → Prop} {a y : Ident} (h : Reach st W a y) (ha : W a) :
    W y := by
  cases h with
  | refl => exact ha
  | step _ _ hw => exact hw

/-- **One `K` for all the members that stay**, among finitely many. -/
theorem uniform_frozen {rest : List Ident} {f : Nat → SkaState M R}
    (hval : ∀ x K, (∀ k, K ≤ k → MembR rest (f k) x) → ∃ K', ∀ k, K' ≤ k → valE (f (k + 1)) x = valE (f k) x)
    (hR : ∀ x K, (∀ k, K ≤ k → MembR rest (f k) x) → ∃ K', ∀ k, K' ≤ k → kids (f (k + 1)) x = kids (f k) x) :
    ∀ I : List Ident, ∃ K, ∀ x ∈ I, Pers rest f x → FrozenFrom rest f x K
  | [] => ⟨0, fun _ h => by cases h⟩
  | x :: I => by
    obtain ⟨K, hK⟩ := uniform_frozen hval hR I
    by_cases hp : Pers rest f x
    · obtain ⟨K1, h1⟩ := hp
      obtain ⟨K2, h2⟩ := hval x K1 h1
      obtain ⟨K3, h3⟩ := hR x K1 h1
      let Kx := max K1 (max K2 K3)
      have fx : FrozenFrom rest f x Kx :=
        ⟨fun k hk => h1 k (Nat.le_trans (Nat.le_max_left _ _) hk),
          fun k hk => h2 k (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hk),
          fun k hk => h3 k (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hk)⟩
      refine ⟨max K Kx, fun y hy hpy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact frozenFrom_mono fx (Nat.le_max_right _ _)
      · exact frozenFrom_mono (hK y hy' hpy) (Nat.le_max_left _ _)
    · refine ⟨K, fun y hy hpy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact absurd hpy hp
      · exact hK y hy' hpy

/-- **The freezing argument**, on any sequence of states: finitely many
members, the root always one, every member at a state after the first reached
from the root through members, a callee of a member kept when it was a member,
every member that stays eventually constant in value (proved on the model:
`chain_present_const`) and in callees (`hR`, the open claim), and at every step
some member falls, leaves or changes callees: impossible. -/
theorem freeze_abstract (f : Nat → SkaState M R) (rest : List Ident) (id : Ident) (I : List Ident)
    (hI : ∀ k x, MembR rest (f k) x → x ∈ I)
    (hroot : ∀ k, MembR rest (f k) id)
    (hreach : ∀ k x, MembR rest (f (k + 1)) x → Reach (f (k + 1)) (MembR rest (f (k + 1))) id x)
    (hkeep : ∀ k m c, MembR rest (f (k + 1)) m → c ∈ kids (f (k + 1)) m → MembR rest (f k) c →
      MembR rest (f (k + 1)) c)
    (hval : ∀ x K, (∀ k, K ≤ k → MembR rest (f k) x) → ∃ K', ∀ k, K' ≤ k → valE (f (k + 1)) x = valE (f k) x)
    (hR : ∀ x K, (∀ k, K ≤ k → MembR rest (f k) x) → ∃ K', ∀ k, K' ≤ k → kids (f (k + 1)) x = kids (f k) x)
    (hC : ∀ k, ∃ m, MembR rest (f k) m ∧ (¬ MembR rest (f (k + 1)) m ∨ valE (f (k + 1)) m ≠ valE (f k) m ∨
      kids (f (k + 1)) m ≠ kids (f k) m)) : False := by
  obtain ⟨K, hK⟩ := uniform_frozen hval hR I
  -- every member at `K + 1` and later stays
  have hpers : ∀ j, ∀ x, MembR rest (f (K + 1 + j)) x → Pers rest f x := by
    intro j x hx
    have hr := hreach (K + j) x (by rw [show K + j + 1 = K + 1 + j by omega]; exact hx)
    rw [show K + j + 1 = K + 1 + j by omega] at hr
    clear hx
    induction hr with
    | refl => exact ⟨0, fun k _ => hroot k⟩
    | @step b c hb hk hw ih =>
      have fb := hK b (hI _ b (reach_mem hb (hroot _))) ih
      refine ⟨K + 1 + j, fun k hk' => ?_⟩
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk'
      clear hk'
      induction d with
      | zero => exact hw
      | succ d ihd =>
        have e1 : kids (f (K + 1 + j + d + 1)) b = kids (f (K + 1 + j)) b := by
          rw [kids_const_from fb _ (by omega), kids_const_from fb (K + 1 + j) (by omega)]
        exact hkeep (K + 1 + j + d) b c (fb.1 _ (by omega)) (by rw [e1]; exact hk) ihd
  obtain ⟨m, hm, hch⟩ := hC (K + 1)
  have fm := hK m (hI _ m hm) (hpers 0 m hm)
  rcases hch with h1 | h1 | h1
  · exact h1 (fm.1 _ (by omega))
  · exact h1 (fm.2.1 _ (by omega))
  · exact h1 (fm.2.2 _ (by omega))

/-! ## 4. On the model -/

/-- (i) along a chain: its members are among a finite list. -/
def FinIdents (rest : List Ident) (f : Nat → SkaState M R) : Prop :=
  ∃ I : List Ident, ∀ k x, MembR rest (f k) x → x ∈ I

/-- C along a chain: at every pass some member of its start falls, is culled,
or changes its callee set. -/
def PassMoves (rest : List Ident) (f : Nat → SkaState M R) : Prop :=
  ∀ k, ∃ m, MembR rest (f k) m ∧ (¬ MembR rest (f (k + 1)) m ∨ valE (f (k + 1)) m ≠ valE (f k) m ∨
    kids (f (k + 1)) m ≠ kids (f k) m)

/-- R, the open claim: a member that stays from some pass on has an eventually
constant callee set. -/
def EvFrozen (rest : List Ident) (f : Nat → SkaState M R) : Prop :=
  ∀ x K, (∀ k, K ≤ k → MembR rest (f k) x) → ∃ K', ∀ k, K' ≤ k → kids (f (k + 1)) x = kids (f k) x

/-- A pass that goes on keeps the stack below the root. -/
theorem passOn_shape (env : Env R) (memoF : Memo M) (hmF : MemoWF memoF) {n : Nat} {id : Ident}
    {index pass : Nat} {st st' : SkaState M R} (hi : SInv st) (h : PassOn env memoF n id index pass st st')
    {a rest : List Ident} (ha : st.stk = a ++ id :: rest) : ∃ a', st'.stk = a' ++ id :: rest := by
  obtain ⟨st2, s2, ⟨l, el⟩, hc⟩ := passOn_cull env memoF hmF hi h
  have hs2 : st2.stk = (l ++ a) ++ id :: rest := by rw [el, ha, List.append_assoc]
  obtain ⟨_, _, ⟨⟨l', e'⟩, _, _⟩⟩ := cull_ok s2 hc hs2
  exact ⟨l', e'⟩

/-- **No infinite chain of passes**, given (i), C and R along it. -/
theorem freeze_no_chain (env : Env R) (memoF : Memo M) (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hRW : ∀ k, RunStkW (run env memoF k)) (id : Ident) (index p : Nat)
    (f : Nat → SkaState M R) (h0i : SInv (f 0)) (h0t : TInv (f 0)) (h0w : WInv (f 0))
    (hon : ∀ k, ∃ n, PassOn env memoF n id index (p + k) (f k) (f (k + 1)))
    (ab0 rest : List Ident) (hs0 : (f 0).stk = ab0 ++ id :: rest)
    (hfin : FinIdents rest f) (hC : PassMoves rest f) (hR : EvFrozen rest f) : False := by
  obtain ⟨inv, _⟩ := chain_root_mem env memoF hmF hmT hRW id index p f h0i h0t h0w hon
  -- the shape of the stack at every pass
  have shape : ∀ k, ∃ a, (f k).stk = a ++ id :: rest := by
    intro k
    induction k with
    | zero => exact ⟨ab0, hs0⟩
    | succ k ih =>
      obtain ⟨a, ha⟩ := ih
      obtain ⟨n, hk⟩ := hon k
      exact passOn_shape env memoF hmF (inv k).1 hk ha
  have hroot : ∀ k, MembR rest (f k) id := by
    intro k
    obtain ⟨a, ha⟩ := shape k
    have hnd : (a ++ id :: rest).Nodup := ha ▸ (inv k).1.nodup
    exact ⟨by rw [ha]; exact List.mem_append_right _ List.mem_cons_self,
      ((List.nodup_append.mp hnd).2.1 |> List.nodup_cons.mp).1⟩
  obtain ⟨I, hI⟩ := hfin
  refine freeze_abstract f rest id I hI hroot ?_ ?_ ?_ hR hC
  · intro k x hx
    obtain ⟨a, ha⟩ := shape k
    obtain ⟨n, hk⟩ := hon k
    obtain ⟨st2, s2, ⟨l, el⟩, hc⟩ := passOn_cull env memoF hmF (inv k).1 hk
    exact cull_reach s2 (by rw [el, ha, ← List.append_assoc]) hc hx
  · intro k m c hm hc hc2
    obtain ⟨a, ha⟩ := shape k
    obtain ⟨n, hk⟩ := hon k
    obtain ⟨st2, s2, ⟨l, el⟩, hcu⟩ := passOn_cull env memoF hmF (inv k).1 hk
    exact cull_keeps_kid s2 (by rw [el, ha, ← List.append_assoc]) hcu hm hc
      ⟨by rw [el]; exact List.mem_append_right _ hc2.1, hc2.2⟩
  · intro x K hx
    obtain ⟨K', _, h⟩ := chain_present_const env memoF hmF hmT hRW id index p f h0i h0t h0w hon x K
      (fun k hk => (hx k hk).1)
    exact ⟨K', h⟩

/-- **`FinPushes` from the freezing argument**: if along every chain of passes
from `x` the claims (i), C and R hold, there is no such chain, so `FinPushes`
holds (vacuously). -/
theorem finPushes_of_freeze (env : Env R) (memoF : Memo M) (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hmN : MemoNI memoF) (id : Ident) (index : Nat) (x : Nat × SkaState M R)
    (hi : SInv x.2) (ht : TInv x.2) (hw : WInv x.2) (ab0 rest : List Ident) (hs : x.2.stk = ab0 ++ id :: rest)
    (hclaims : ∀ f : Nat → Nat × SkaState M R, (∀ k, PassNext env memoF id index x (f (k + 1)) (f k)) →
      FinIdents rest (fun k => (f k).2) ∧ PassMoves rest (fun k => (f k).2) ∧
        EvFrozen rest (fun k => (f k).2)) :
    FinPushes env memoF id index x := by
  intro f hf
  have hRW := run_winv env memoF hmF hmT hmN
  have shape : ∀ y, PassReach env memoF id index x y → ∃ a, y.2.stk = a ++ id :: rest := by
    intro y hy
    induction hy with
    | refl => exact ⟨ab0, hs⟩
    | step hy' hp ih =>
      obtain ⟨a, ha⟩ := ih
      exact passOn_shape env memoF hmF (passReach_inv env memoF hmF hmT hmN hy' hi ht hw).1 hp ha
  have h0 := passReach_inv env memoF hmF hmT hmN (hf 0).1 hi ht hw
  obtain ⟨a0, ha0⟩ := shape _ (hf 0).1
  have hpass : ∀ k, (f k).1 = (f 0).1 + k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => obtain ⟨_, e, _⟩ := (hf k).2; rw [e, ih]; rfl
  obtain ⟨hfin, hC, hR⟩ := hclaims f hf
  exact (freeze_no_chain env memoF hmF hmT hRW id index (f 0).1 (fun k => (f k).2) h0.1 h0.2.1 h0.2.2
    (fun k => by obtain ⟨m, _, hp⟩ := (hf k).2; exact ⟨m, hpass k ▸ hp⟩) a0 rest ha0 hfin hC hR).elim
