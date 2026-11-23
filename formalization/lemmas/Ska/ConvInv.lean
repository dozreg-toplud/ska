import lemmas.Ska.BridgeD

/-!
# The convergence invariant of the state-passing analysis

With the cull before the first pass (Hoon commit `fefb95d`), the final graph
of `+ska-callgraph` is converged: every entry is a memo hit, or was written by
its last run with answers that are entries of the final graph (or the
versions of them before `+pop` turned a `%void` product into `|+~`).  This
file holds the invariant that shows it, and its parts.

* `AnsW`: `Answers` whose `%he` partner is a well-formed sock (so that the
  answers keep well-formedness); answers carry over between entries that are
  alike for a caller (`Alike`: same identity and same `TabEntry`).
* The frozen entries `F` (`FrzInv`): the finalized entries of the graph and
  the pre-pop versions of the popped ones, each justified by `F` itself
  (`FrozenOK`).
* The members (`MemInv`): each member that has run has an entry written by
  its last run, whose answers come from `F` or from callees on the stack
  below the bound `L` (where the run read them), whose entries are the ones
  it read unless their change tick is at least the member's run tick.
* `pop_frozen`: a `+pop` whose popped members are not dirty and whose callees
  on the stack are popped with them makes the popped entries frozen.
-/

namespace Formalization
namespace SkaModel

open Nock

/-! ## Answers with a well-formed partner -/

/-- `Answers` with the partner of a `%he` generalization well formed. -/
inductive AnsW (G : Entry → Prop) : Sock → Noun → TabEntry → Prop where
  | exact {e : Entry} : G e → AnsW G e.more e.fol e.d.tab
  | hit {e : Entry} {s : Sock} : G e → hitTest e s = some true → AnsW G s e.fol (patchDatum e.d s).tab
  | gen {s s' m : Sock} {f : Noun} {a : TabEntry} : WellFormed s' → msgSock s s' = some m → AnsW G m f a →
      AnsW G s f a

/-- Two entries alike for a caller: the same identity and the same
`TabEntry`. -/
def Alike (e e' : Entry) : Prop := e'.more = e.more ∧ e'.fol = e.fol ∧ e'.d.tab = e.d.tab

theorem hitTest_alike {e e' : Entry} (h : Alike e e') (s : Sock) : hitTest e' s = hitTest e s := by
  obtain ⟨h1, _, h3⟩ := h
  have hl : e'.d.less = e.d.less := congrArg TabEntry.less h3
  have hi : e'.d.indi = e.d.indi := congrArg TabEntry.indi h3
  unfold hitTest
  rw [hl, hi, h1]

theorem patchDatum_tab_alike {e e' : Entry} (h : Alike e e') (s : Sock) :
    (patchDatum e'.d s).tab = (patchDatum e.d s).tab := by
  obtain ⟨_, _, h3⟩ := h
  have hl : e'.d.less = e.d.less := congrArg TabEntry.less h3
  have hi : e'.d.indi = e.d.indi := congrArg TabEntry.indi h3
  have hs : e'.d.seek = e.d.seek := congrArg TabEntry.seek h3
  have hp : e'.d.prod = e.d.prod := congrArg TabEntry.prod h3
  have hm : e'.d.map = e.d.map := congrArg TabEntry.map h3
  simp only [patchDatum, Datum.tab, hl, hi, hs, hp, hm]

theorem AnsW.transfer {G G' : Entry → Prop} (hG : ∀ e, G e → ∃ e', G' e' ∧ Alike e e')
    {s : Sock} {f : Noun} {a : TabEntry} (h : AnsW G s f a) : AnsW G' s f a := by
  induction h with
  | exact he =>
    obtain ⟨e', he', h1, h2, h3⟩ := hG _ he
    have := AnsW.exact (G := G') he'
    rw [h1, h2, h3] at this; exact this
  | hit he ht =>
    obtain ⟨e', he', hal⟩ := hG _ he
    have := AnsW.hit (G := G') he' (by rw [hitTest_alike hal]; exact ht)
    rw [hal.2.1, patchDatum_tab_alike hal] at this; exact this
  | gen hw hm _ ih => exact AnsW.gen hw hm ih

theorem AnsW.mono {G G' : Entry → Prop} (hG : ∀ e, G e → G' e) {s : Sock} {f : Noun} {a : TabEntry}
    (h : AnsW G s f a) : AnsW G' s f a :=
  h.transfer (fun e he => ⟨e, hG e he, rfl, rfl, rfl⟩)

theorem AnsW.toAnswers {G : Entry → Prop} {s : Sock} {f : Noun} {a : TabEntry} (h : AnsW G s f a) :
    Answers G s f a := by
  induction h with
  | exact he => exact Answers.exact he
  | hit he ht => exact Answers.hit he ht
  | gen _ hm _ ih => exact Answers.gen hm ih

theorem AnsW.wf {G : Entry → Prop} (hG : ∀ e, G e → WellFormed e.more ∧ WellFormed e.d.prod)
    {s : Sock} {f : Noun} {a : TabEntry} (h : AnsW G s f a) : WellFormed s → WellFormed a.prod := by
  induction h with
  | exact he => exact fun _ => (hG _ he).2
  | hit he _ => exact fun hs => wf_patchDatum (hG _ he).2 hs
  | gen hw hm _ ih => exact fun hs => ih (wf_msgSock hs hw hm)

theorem answers_mono {G G' : Entry → Prop} (hG : ∀ e, G e → G' e) {s : Sock} {f : Noun} {a : TabEntry}
    (h : Answers G s f a) : Answers G' s f a := by
  induction h with
  | exact he => exact Answers.exact (hG _ he)
  | hit he ht => exact Answers.hit (hG _ he) ht
  | gen hm _ ih => exact Answers.gen hm ih

namespace Ana

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-! ## The parts of the state the invariant reads -/

/-- An entry of the graph as an `Entry`. -/
def entOf (i : Ident) (d : FDatum M) : Entry := ⟨i.1, i.2, d.core⟩

/-- The tick of the last run of `m` (`ran`) and of the last change of its
entry (`chg`), as `+dirty` reads them. -/
def ranOf (st : SkaState M R) (m : Ident) : Nat := (Treap.gut st.ticks m (0, 0)).1
def chgOf (st : SkaState M R) (m : Ident) : Nat := (Treap.gut st.ticks m (0, 0)).2

/-- `c` is among the callees `cs`, with some seat. -/
def InCallees (cs : M CalleeEntry Unit) (c : Ident) : Prop := ∃ seat, Treap.has cs ⟨seat, c⟩ = true

/-- The callees of `m` in the graph. -/
def calleesOf (st : SkaState M R) (m : Ident) : M CalleeEntry Unit := (gitG st.g m).callees

/-- The `+pop` of an entry: a `%void` product becomes `|+~`. -/
def postPop (d : FDatum M) : FDatum M := if d.prod = Sock.void then { d with prod := Sock.dunno } else d

/-- A memo hit of the persistent memo, as `+analyze` puts it in the graph. -/
def MemoHitE (memoF : Memo M) (e : Entry) : Prop :=
  ∃ i d, gitMi memoF e.fol e.more = some (some (i, d)) ∧ e.d = d.core

/-- **Frozen entries justify themselves**: each is a memo hit, or was written
by a run whose every answer is an answer of the frozen entries. -/
def FrozenOK (memoF : Memo M) (F : Entry → Prop) : Prop :=
  ∀ e, F e → (∃ P : Sock → Noun → TabEntry → Prop, (∀ s f a, P s f a → Answers F s f a) ∧ RunEntryR P e) ∨
    MemoHitE memoF e

theorem FrozenOK.mono {memoF : Memo M} {F F' : Entry → Prop} (h : FrozenOK memoF F) (hF : ∀ e, F e → F' e)
    {e : Entry} (he : F e) :
    (∃ P : Sock → Noun → TabEntry → Prop, (∀ s f a, P s f a → Answers F' s f a) ∧ RunEntryR P e) ∨
      MemoHitE memoF e := by
  rcases h e he with ⟨P, hP, hr⟩ | hm
  · refine Or.inl ⟨P, fun s f a hp => ?_, hr⟩
    exact answers_mono hF (hP s f a hp)
  · exact Or.inr hm

/-- **The frozen entries of a state**: `F` justifies itself, holds every
finalized entry of the graph (in the graph, not in `order`) and every entry of
`done`, and holds only entries of finalized identities, with well-formed
products. -/
structure FrzInv (memoF : Memo M) (st : SkaState M R) (F : Entry → Prop) : Prop where
  ok : FrozenOK memoF F
  cover : ∀ i d, Treap.get st.g i = some d → Treap.get st.order i = none → F (entOf i d)
  sub : ∀ e, F e → (∃ d, Treap.get st.g (e.more, e.fol) = some d) ∧ Treap.get st.order (e.more, e.fol) = none
  wf : ∀ e, F e → WellFormed e.d.prod
  done : ∀ f ms s ent, Treap.get st.done f = some ms → Treap.get ms s = some ent →
    F (entOf ent.1 ent.2) ∧ ent.1.2 = f ∧ Treap.get st.g ent.1 = some ent.2

/-- What a member may have read: a frozen entry, or a callee on the stack
below the bound `L`, whose entry is still the one read unless it changed at
or after the member's last run. -/
def MB (st : SkaState M R) (F : Entry → Prop) (m : Ident) (L : Nat) : Entry → Prop := fun e =>
  F e ∨ (InCallees (calleesOf st m) (e.more, e.fol) ∧
    (∃ o, Treap.get st.order (e.more, e.fol) = some o ∧ o < L) ∧
    (chgOf st (e.more, e.fol) < ranOf st m →
      ∃ d, Treap.get st.g (e.more, e.fol) = some d ∧ d.core.tab = e.d.tab))

/-- **A member that has run** has an entry written by its last run, with
answers from `MB` for a bound `L` at most `Lmax`. -/
def MemOK (st : SkaState M R) (F : Entry → Prop) (m : Ident) (Lmax : Nat) : Prop :=
  ∀ d, Treap.get st.g m = some d → 1 ≤ ranOf st m →
    ∃ (P : Sock → Noun → TabEntry → Prop) (L : Nat), L ≤ Lmax ∧ RunEntryR P (entOf m d) ∧
      ∀ s f a, P s f a → AnsW (MB st F m L) s f a

/-- Every member is `MemOK` with the bound `next`. -/
def MemInv (st : SkaState M R) (F : Entry → Prop) : Prop :=
  ∀ m o, Treap.get st.order m = some o → MemOK st F m st.next

/-- The ticks are at most the clock. -/
def TickInv (st : SkaState M R) : Prop := ∀ m, ranOf st m ≤ st.tick ∧ chgOf st m ≤ st.tick

/-- The DFS numbers are below `next` and decrease down the stack. -/
def OrdInv (st : SkaState M R) : Prop :=
  (∀ i o, Treap.get st.order i = some o → o < st.next) ∧
    st.stk.Pairwise (fun a b => ∀ oa ob, Treap.get st.order a = some oa → Treap.get st.order b = some ob → ob < oa)

/-- **The convergence invariant**, with the frozen entries `F`. -/
structure CInv (memoF : Memo M) (st : SkaState M R) (F : Entry → Prop) : Prop where
  s : SInv st
  tick : TickInv st
  ord : OrdInv st
  frz : FrzInv memoF st F
  mem : MemInv st F

/-! ## `+pop`, entry by entry -/

theorem putMi_get {m : Memo M} {i : Ident} {d : FDatum M} {f : Noun} {ms : M Sock (Ident × FDatum M)}
    {s : Sock} {ent : Ident × FDatum M}
    (h1 : Treap.get (putMi m i d) f = some ms) (h2 : Treap.get ms s = some ent) :
    (∃ ms', Treap.get m f = some ms' ∧ Treap.get ms' s = some ent) ∨ (ent = (i, d) ∧ f = i.2) := by
  unfold putMi at h1
  rw [Treap.get_put] at h1
  split at h1
  · rename_i hf
    cases h1
    rw [Treap.get_put] at h2
    split at h2
    · cases h2; exact Or.inr ⟨rfl, hf⟩
    · left
      subst hf
      unfold gutMi Treap.gut at h2
      cases e : Treap.get m i.2 with
      | none => rw [e] at h2; simp [Treap.get_empty] at h2
      | some ms' => rw [e] at h2; exact ⟨ms', rfl, h2⟩
  · exact Or.inl ⟨ms, h1, h2⟩

/-- **What `+pop` does**: it takes `pre ++ [id]` off the stack, deletes their
`order` and `ticks`, puts their entries back through `postPop`, and memoizes
them in `done`. -/
theorem popGo_eff {id : Ident} : ∀ (pre : List Ident) (st st' : SkaState M R) (rest : List Ident),
    st.stk = pre ++ id :: rest → (pre ++ id :: rest).Nodup →
    (∀ j ∈ pre ++ [id], ∃ d, Treap.get st.g j = some d) → popGo id st.stk st = some st' →
    st'.stk = rest ∧ st'.next = st.next ∧ st'.tick = st.tick ∧
    (∀ j, Treap.get st'.order j = if j ∈ pre ++ [id] then none else Treap.get st.order j) ∧
    (∀ j, Treap.get st'.ticks j = if j ∈ pre ++ [id] then none else Treap.get st.ticks j) ∧
    (∀ j, Treap.get st'.g j = if j ∈ pre ++ [id] then (Treap.get st.g j).map postPop else Treap.get st.g j) ∧
    (∀ f ms s ent, Treap.get st'.done f = some ms → Treap.get ms s = some ent →
      (∃ ms', Treap.get st.done f = some ms' ∧ Treap.get ms' s = some ent) ∨
      (∃ j ∈ pre ++ [id], ent = (j, postPop (gitG st.g j)) ∧ f = j.2))
  | [], st, st', rest, hs, _, _, h => by
    rw [hs] at h
    simp only [List.nil_append, popGo, if_true] at h
    cases h
    refine ⟨rfl, rfl, rfl, fun j => ?_, fun j => ?_, fun j => ?_, fun f ms s ent h1 h2 => ?_⟩
    · simp only [List.nil_append, List.mem_singleton, Treap.get_del]
    · simp only [List.nil_append, List.mem_singleton, Treap.get_del]
    · simp only [List.nil_append, List.mem_singleton, Treap.get_put]
      split
      · rename_i e; subst e
        cases e2 : Treap.get st.g j with
        | none => simp [gitG, e2] at *
        | some d => simp [gitG, Treap.gut, e2, postPop]
      · rfl
    · rcases putMi_get h1 h2 with h | ⟨rfl, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨id, by simp, by simp [postPop], rfl⟩
  | x :: pre, st, st', rest, hs, hnd, hin, h => by
    rw [hs] at h
    have hx : x ≠ id := by
      intro e; subst e; simp at hnd
    simp only [List.cons_append, popGo, if_neg hx] at h
    have hnd' : (pre ++ id :: rest).Nodup := (List.nodup_cons.mp (by simpa using hnd)).2
    have hxn : x ∉ pre ++ id :: rest := (List.nodup_cons.mp (by simpa using hnd)).1
    obtain ⟨dx, hdx⟩ := hin x (by simp)
    let st2 : SkaState M R := { st with stk := pre ++ id :: rest, order := Treap.del st.order x, ticks := Treap.del st.ticks x, g := Treap.put st.g x (postPop (gitG st.g x)), done := putMi st.done x (postPop (gitG st.g x)) }
    have hin2 : ∀ j ∈ pre ++ [id], ∃ d, Treap.get st2.g j = some d := by
      intro j hj
      have hjx : j ≠ x := by
        rintro rfl; exact hxn (by simp at hj ⊢; rcases hj with hj | hj <;> simp [hj])
      simp only [st2, Treap.get_put, if_neg hjx]
      exact hin j (by simp at hj ⊢; rcases hj with hj | hj <;> simp [hj])
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := popGo_eff pre st2 st' rest rfl hnd' hin2 (by
      simpa [st2, gitG, postPop] using h)
    have hmem : ∀ j, j ∈ x :: pre ++ [id] ↔ j = x ∨ j ∈ pre ++ [id] := by simp
    refine ⟨a1, a2, a3, fun j => ?_, fun j => ?_, fun j => ?_, fun f ms s ent h1 h2 => ?_⟩
    · rw [a4]; simp only [st2, Treap.get_del]
      by_cases e1 : j ∈ pre ++ [id] <;> by_cases e2 : j = x <;> simp_all
    · rw [a5]; simp only [st2, Treap.get_del]
      by_cases e1 : j ∈ pre ++ [id] <;> by_cases e2 : j = x <;> simp_all
    · rw [a6]; simp only [st2, Treap.get_put]
      by_cases e1 : j ∈ pre ++ [id]
      · have e2 : j ≠ x := by rintro rfl; exact hxn (by simp at e1 ⊢; rcases e1 with e1 | e1 <;> simp [e1])
        simp [e1, e2]
      · by_cases e2 : j = x
        · subst e2
          have hg : gitG st.g j = dx := by simp [gitG, Treap.gut, hdx]
          simp [e1, hdx, hg]
        · simp [e1, e2]
    · rcases a7 f ms s ent h1 h2 with ⟨ms', e1, e2⟩ | ⟨j, hj, rfl, rfl⟩
      · rcases putMi_get e1 e2 with h | ⟨rfl, rfl⟩
        · exact Or.inl h
        · exact Or.inr ⟨x, by simp, rfl, rfl⟩
      · have hjx : j ≠ x := by rintro rfl; exact hxn (by simp at hj ⊢; rcases hj with hj | hj <;> simp [hj])
        refine Or.inr ⟨j, by simp at hj ⊢; rcases hj with hj | hj <;> simp [hj], ?_, rfl⟩
        simp [st2, gitG, Treap.gut, Treap.get_put, hjx]

/-! ## The orders along the stack -/

theorem ordInv_split {st : SkaState M R} (ho : OrdInv st) {ab0 rest : List Ident} {id : Ident} {index : Nat}
    (hs : st.stk = ab0 ++ id :: rest) (hidx : Treap.get st.order id = some index) :
    (∀ x ∈ ab0 ++ [id], ∀ o, Treap.get st.order x = some o → index ≤ o) ∧
    (∀ x ∈ rest, ∀ o, Treap.get st.order x = some o → o < index) := by
  have hp := ho.2
  rw [hs, List.pairwise_append] at hp
  obtain ⟨_, hp2, hp3⟩ := hp
  rw [List.pairwise_cons] at hp2
  refine ⟨fun x hx o hxo => ?_, fun x hx o hxo => hp2.1 x hx index o hidx hxo⟩
  rcases List.mem_append.mp hx with hx | hx
  · exact Nat.le_of_lt (hp3 x hx id List.mem_cons_self o index hxo hidx)
  · rw [List.mem_singleton.mp hx] at hxo; rw [hidx] at hxo; cases hxo; exact Nat.le_refl _

theorem FDatum.postPop_core (d : FDatum M) :
    (postPop d).core = if d.core.prod = Sock.void then { d.core with prod := Sock.dunno } else d.core := by
  unfold postPop FDatum.core; split <;> rfl

/-! ## A `+pop` freezes its members -/

/-- **A `+pop` whose members are ready freezes them**: each popped member has
run, its callees on the stack did not change since its last run (it is not
dirty) and are popped with it (their DFS numbers are at least the root's);
the members below keep their answers, which come from below the root.  Then
the popped entries, before and after `+pop`, join the frozen entries. -/
theorem pop_frozen {memoF : Memo M} {id : Ident} {st st' : SkaState M R} {F : Entry → Prop}
    {ab0 rest : List Ident} {index : Nat}
    (hc : CInv memoF st F) (hs : st.stk = ab0 ++ id :: rest) (hidx : Treap.get st.order id = some index)
    (hrest : ∀ m ∈ rest, MemOK st F m index)
    (hready : ∀ x ∈ ab0 ++ [id], 1 ≤ ranOf st x ∧ ∀ c, InCallees (calleesOf st x) c → ∀ o,
      Treap.get st.order c = some o → chgOf st c < ranOf st x ∧ index ≤ o)
    (h : pop id st = some st') :
    ∃ F', (∀ e, F e → F' e) ∧ CInv memoF st' F' := by
  have hnd : (ab0 ++ id :: rest).Nodup := hs ▸ hc.s.nodup
  have hin : ∀ j ∈ ab0 ++ [id], ∃ d, Treap.get st.g j = some d := fun j hj =>
    hc.s.mem_g (by rw [hs]; simp at hj ⊢; rcases hj with hj | hj <;> simp [hj])
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := popGo_eff ab0 st st' rest hs hnd hin (by unfold pop at h; exact h)
  obtain ⟨hup, hdown⟩ := ordInv_split hc.ord hs hidx
  have hmemP : ∀ j, j ∈ ab0 ++ [id] → ∃ o, Treap.get st.order j = some o := fun j hj =>
    (hc.s.ord_stk j).mpr (by rw [hs]; simp at hj ⊢; rcases hj with hj | hj <;> simp [hj])
  -- the popped identities are exactly the members at or above the root
  have hinP : ∀ c o, Treap.get st.order c = some o → index ≤ o → c ∈ ab0 ++ [id] := by
    intro c o hco hle
    have hcs : c ∈ st.stk := (hc.s.ord_stk c).mp ⟨o, hco⟩
    rw [hs] at hcs
    simp only [List.mem_append, List.mem_cons] at hcs
    rcases hcs with hcs | rfl | hcs
    · simp [hcs]
    · simp
    · exact absurd (hdown c hcs o hco) (by omega)
  let F' : Entry → Prop := fun e => F e ∨ ∃ x ∈ ab0 ++ [id], ∃ d, Treap.get st.g x = some d ∧
    (e = entOf x d ∨ e = entOf x (postPop d))
  have hFF' : ∀ e, F e → F' e := fun e he => Or.inl he
  -- the answers of a popped member are answers of `F'`
  have hans : ∀ x ∈ ab0 ++ [id], ∀ d, Treap.get st.g x = some d →
      ∃ P : Sock → Noun → TabEntry → Prop, RunEntryR P (entOf x d) ∧ ∀ s f a, P s f a → Answers F' s f a := by
    intro x hx d hd
    obtain ⟨hr, hcal⟩ := hready x hx
    obtain ⟨o, hxo⟩ := hmemP x hx
    obtain ⟨P, L, _, hrun, hP⟩ := hc.mem x o hxo d hd hr
    refine ⟨P, hrun, fun s f a hp => (AnsW.transfer (fun e he => ?_) (hP s f a hp)).toAnswers⟩
    rcases he with he | ⟨hce, ⟨oc, hco, _⟩, htab⟩
    · exact ⟨e, Or.inl he, rfl, rfl, rfl⟩
    · obtain ⟨hlt, hle⟩ := hcal _ hce oc hco
      obtain ⟨dc, hdc, htc⟩ := htab hlt
      exact ⟨entOf (e.more, e.fol) dc, Or.inr ⟨_, hinP _ oc hco hle, dc, hdc, Or.inl rfl⟩, rfl, rfl, htc⟩
  have hok : FrozenOK memoF F' := by
    intro e he
    rcases he with he | ⟨x, hx, d, hd, rfl | rfl⟩
    · exact hc.frz.ok.mono hFF' he
    · obtain ⟨P, hrun, hP⟩ := hans x hx d hd
      exact Or.inl ⟨P, hP, hrun⟩
    · obtain ⟨P, hrun, hP⟩ := hans x hx d hd
      refine Or.inl ⟨P, hP, ?_⟩
      unfold entOf
      rw [FDatum.postPop_core]
      split
      · exact RunEntryR.pop hrun (by assumption)
      · exact hrun
  have hgP : ∀ x ∈ ab0 ++ [id], Treap.get st'.g x = (Treap.get st.g x).map postPop := fun x hx => by
    rw [a6, if_pos hx]
  have hgN : ∀ x, x ∉ ab0 ++ [id] → Treap.get st'.g x = Treap.get st.g x := fun x hx => by
    rw [a6, if_neg hx]
  have hoN : ∀ x, x ∉ ab0 ++ [id] → Treap.get st'.order x = Treap.get st.order x := fun x hx => by
    rw [a4, if_neg hx]
  have hoP : ∀ x ∈ ab0 ++ [id], Treap.get st'.order x = none := fun x hx => by rw [a4, if_pos hx]
  have htN : ∀ x, x ∉ ab0 ++ [id] → Treap.gut st'.ticks x (0, 0) = Treap.gut st.ticks x (0, 0) := fun x hx => by
    unfold Treap.gut; rw [a5, if_neg hx]
  have hpopNot : ∀ x o, Treap.get st.order x = some o → o < index → x ∉ ab0 ++ [id] := fun x o hxo hlt hx =>
    absurd (hup x hx o hxo) (by omega)
  refine ⟨F', hFF', ⟨pop_ok hc.s h hs |>.1, fun m => ?_, ⟨fun i o hio => ?_, ?_⟩, ⟨hok, ?_, ?_, ?_, ?_⟩, ?_⟩⟩
  · -- ticks
    by_cases hm : m ∈ ab0 ++ [id]
    · simp only [ranOf, chgOf, Treap.gut, a5, if_pos hm, Option.getD_none]; omega
    · simp only [ranOf, chgOf, htN m hm, a3]; exact hc.tick m
  · -- orders below next
    by_cases hi : i ∈ ab0 ++ [id]
    · rw [hoP i hi] at hio; cases hio
    · rw [hoN i hi] at hio; rw [a2]; exact hc.ord.1 i o hio
  · -- orders down the stack
    rw [a1]
    have hp := hc.ord.2
    rw [hs, List.pairwise_append, List.pairwise_cons] at hp
    refine hp.2.1.2.imp_of_mem (fun {a b} ha hb hab oa ob h1 h2 => ?_)
    have hnd2 : ((ab0 ++ [id]) ++ rest).Nodup := by simpa using hnd
    have hna : a ∉ ab0 ++ [id] := fun hx => (List.nodup_append.mp hnd2).2.2 a hx a ha rfl
    have hnb : b ∉ ab0 ++ [id] := fun hx => (List.nodup_append.mp hnd2).2.2 b hx b hb rfl
    rw [hoN a hna] at h1; rw [hoN b hnb] at h2
    exact hab oa ob h1 h2
  · -- cover
    intro i d hgd hgo
    by_cases hi : i ∈ ab0 ++ [id]
    · rw [hgP i hi] at hgd
      obtain ⟨d0, hd0, rfl⟩ := Option.map_eq_some_iff.mp hgd
      exact Or.inr ⟨i, hi, d0, hd0, Or.inr rfl⟩
    · rw [hgN i hi] at hgd; rw [hoN i hi] at hgo
      exact Or.inl (hc.frz.cover i d hgd hgo)
  · -- sub
    intro e he
    rcases he with he | ⟨x, hx, d, hd, rfl | rfl⟩
    · obtain ⟨⟨d0, hd0⟩, hno⟩ := hc.frz.sub e he
      have hn : (e.more, e.fol) ∉ ab0 ++ [id] := fun hx => by
        obtain ⟨o, ho⟩ := hmemP _ hx; rw [hno] at ho; cases ho
      exact ⟨⟨d0, by rw [hgN _ hn]; exact hd0⟩, by rw [hoN _ hn]; exact hno⟩
    · have e1 : Treap.get st'.g x = some (postPop d) := by rw [hgP x hx, hd]; rfl
      exact ⟨⟨postPop d, e1⟩, hoP x hx⟩
    · have e1 : Treap.get st'.g x = some (postPop d) := by rw [hgP x hx, hd]; rfl
      exact ⟨⟨postPop d, e1⟩, hoP x hx⟩
  · -- wf
    intro e he
    rcases he with he | ⟨x, hx, d, hd, rfl | rfl⟩
    · exact hc.frz.wf e he
    · exact (hc.s.wf_get hd).2
    · show WellFormed (postPop d).prod
      unfold postPop; split
      · exact wf_dunno
      · exact (hc.s.wf_get hd).2
  · -- done
    intro f ms s ent h1 h2
    rcases a7 f ms s ent h1 h2 with ⟨ms', e1, e2⟩ | ⟨j, hj, rfl, rfl⟩
    · obtain ⟨hF, hk, hge⟩ := hc.frz.done f ms' s ent e1 e2
      have hn : ent.1 ∉ ab0 ++ [id] := fun hx => by
        obtain ⟨o, ho⟩ := hmemP _ hx
        have := (hc.frz.sub _ hF).2
        simp only [entOf] at this
        rw [this] at ho; cases ho
      exact ⟨Or.inl hF, hk, by rw [hgN _ hn]; exact hge⟩
    · obtain ⟨dj, hdj⟩ := hin j hj
      have hg : gitG st.g j = dj := by simp [gitG, Treap.gut, hdj]
      rw [hg]
      exact ⟨Or.inr ⟨j, hj, dj, hdj, Or.inr rfl⟩, rfl, by rw [hgP j hj, hdj]; rfl⟩
  · -- members
    intro m o hmo d hd hr
    have hmN : m ∉ ab0 ++ [id] := fun hx => by rw [hoP m hx] at hmo; cases hmo
    rw [hoN m hmN] at hmo
    have hmr : m ∈ rest := by
      have hms : m ∈ st.stk := (hc.s.ord_stk m).mp ⟨o, hmo⟩
      rw [hs] at hms
      simp only [List.mem_append, List.mem_cons] at hms
      rcases hms with hms | rfl | hms
      · exact absurd (by simp [hms]) hmN
      · exact absurd (by simp) hmN
      · exact hms
    rw [hgN m hmN] at hd
    have hrn : ranOf st' m = ranOf st m := by simp only [ranOf, htN m hmN]
    rw [hrn] at hr
    obtain ⟨P, L, hL, hrun, hP⟩ := hrest m hmr d hd hr
    refine ⟨P, L, ?_, hrun, fun s f a hp => (hP s f a hp).mono (fun e he => ?_)⟩
    · rw [a2]; exact Nat.le_trans hL (Nat.le_of_lt (hc.ord.1 id index hidx))
    · rcases he with he | ⟨hce, ⟨oc, hco, hlt⟩, htab⟩
      · exact Or.inl (hFF' e he)
      · have hcN := hpopNot _ oc hco (Nat.lt_of_lt_of_le hlt hL)
        have hcal : calleesOf st' m = calleesOf st m := by
          simp only [calleesOf, gitG, Treap.gut, hgN m hmN]
        refine Or.inr ⟨by rw [hcal]; exact hce, ⟨oc, by rw [hoN _ hcN]; exact hco, hlt⟩, ?_⟩
        intro hlt'
        simp only [chgOf, ranOf, htN _ hcN, htN m hmN] at hlt'
        obtain ⟨dc, hdc, htc⟩ := htab hlt'
        exact ⟨dc, by rw [hgN _ hcN]; exact hdc, htc⟩

end Ana
end SkaModel
end Formalization
