import lemmas.Ska.PassMeasureE

/-!
# `next` and the stack (track F, Gaps 16)

Every arm of the state-passing analysis (`Analysis.lean`) leaves `next` (the
count of `+analyze`'s pushes) the same or raises it, and `resolve`, `+run`,
the member loop and `+analyze` leave the stack the same when they leave
`next` the same (`NStep`, `allN`): only a push (which raises `next`) adds to
the stack, and `+pop` and `+cull` run only inside an `+analyze` that pushed
first.  The pass loop raises `next` or keeps it (`PassN`); its `+cull` changes
the stack with `next` the same.  So a pass of the member loop that does not
raise `next` runs the same members on the same stack (`Ska/PassMeasureP.lean`).
No invariant is needed: these are facts of the control flow.
-/

namespace Formalization
namespace SkaModel
namespace Ana

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-- `next` does not fall, and the stack is the same when `next` is. -/
def NStep (st st' : SkaState M R) : Prop :=
  st.next ≤ st'.next ∧ (st'.next = st.next → st'.stk = st.stk)

theorem NStep.refl' {st st' : SkaState M R} (h1 : st'.next = st.next) (h2 : st'.stk = st.stk) :
    NStep st st' :=
  ⟨Nat.le_of_eq h1.symm, fun _ => h2⟩

theorem NStep.of_lt {st st' : SkaState M R} (h : st.next < st'.next) : NStep st st' :=
  ⟨Nat.le_of_lt h, fun e => absurd h (by rw [e]; exact Nat.lt_irrefl _)⟩

theorem NStep.trans {st st' st'' : SkaState M R} (a : NStep st st') (b : NStep st' st'') :
    NStep st st'' :=
  ⟨Nat.le_trans a.1 b.1, fun e => by
    have e1 : st'.next = st.next := Nat.le_antisymm (e ▸ b.1) a.1
    rw [b.2 (e.trans e1.symm), a.2 e1]⟩

/-- What `resolve` keeps: `NStep`, and the capes of `gen`. -/
def ResN (res : ResGo M R) : Prop :=
  ∀ idT gs r gs', res idT gs = some (r, gs') → NStep gs.st gs'.st ∧ gs'.gen = gs.gen

def AnaN (ana : AnaGo M R) : Prop := ∀ id st low st', ana id st = some (low, st') → NStep st st'

def RunN (run : RunGo M R) : Prop := ∀ id index st r st', run id index st = some (r, st') → NStep st st'

def MemN (mem : MemGo M R) : Prop :=
  ∀ index pass ms st r st', mem index pass ms st = some (r, st') → NStep st st'

/-- The pass loop: `next` does not fall. -/
def PassN (pass : PassGo M R) : Prop :=
  ∀ id index p st low st', pass id index p st = some (low, st') → st.next ≤ st'.next

/-! ## `+cull`, `+pop`, the end of `+run` keep `next` -/

theorem cullFold_next : ∀ (l : List (Ident × Unit)) (st : SkaState M R), (l.foldl cullStep st).next = st.next
  | [], _ => rfl
  | x :: l, st => by rw [List.foldl_cons, cullFold_next l]; rfl

theorem cull_next {n : Nat} {id : Ident} {st st' : SkaState M R} (h : cull n id st = some st') :
    st'.next = st.next := by
  rw [cull_eq] at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨ab, _, live, _, hst⟩ := h
  split at hst
  · subst hst; rfl
  · subst hst; rw [cullFold_next]

theorem popGo_next {id : Ident} : ∀ (l : List Ident) (st st' : SkaState M R),
    popGo id l st = some st' → st'.next = st.next
  | [], _, _, h => by simp [popGo] at h
  | top :: rest, st, st', h => by
    unfold popGo at h
    simp only at h
    split at h
    · cases h; rfl
    · have e := popGo_next rest _ st' h
      exact e

theorem pop_next {id : Ident} {st st' : SkaState M R} (h : pop id st = some st') : st'.next = st.next :=
  popGo_next st.stk st st' h

theorem runEnd_next (id : Ident) (data : FDatum M) (out : FolOut) (gs : GenS M R) :
    (runEnd id data out gs).2.next = gs.st.next := by
  unfold runEnd
  simp only
  split <;> rfl

/-! ## The arms -/

theorem resolveStep_n (env : Env R) {orig : Ident} {resolve : ResGo M R} {analyze : AnaGo M R}
    (hres : ResN resolve) (hana : AnaN analyze) : ResN (resolveStep env resolve analyze orig) := by
  intro idT gs r gs' e
  unfold resolveStep at e
  cases hg : Treap.get gs.st.g idT with
  | some d =>
    simp only [hg] at e
    cases ho : Treap.get gs.st.order idT with
    | none =>
      simp only [ho, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨NStep.refl' rfl rfl, rfl⟩
    | some o =>
      simp only [ho, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨NStep.refl' rfl rfl, rfl⟩
  | none =>
    rw [hg] at e
    simp only at e
    split at e
    · cases e
    · cases e; exact ⟨NStep.refl' rfl rfl, rfl⟩
    · split at e
      · cases e
      · exact hres _ _ _ _ e
      · simp only [Option.map_eq_some_iff] at e
        obtain ⟨o, _, e⟩ := e
        cases e
        exact ⟨NStep.refl' rfl rfl, rfl⟩
      · simp only [Option.map_eq_some_iff] at e
        obtain ⟨⟨low, st'⟩, ha, e⟩ := e
        cases e
        exact ⟨hana _ _ _ _ ha, rfl⟩

theorem runStep_n (env : Env R) (memoF : Memo M) {n : Nat}
    (hres : ∀ k, k < n → ResN (resolveR env memoF k)) : RunN (runStep (folLoop env memoF n)) := by
  intro id index st r st' e
  unfold runStep at e
  simp only [Option.map_eq_some_iff] at e
  obtain ⟨⟨out, gs⟩, hf, e⟩ := e
  cases e
  let st0 : SkaState M R := { st with stats := { st.stats with runs := st.stats.runs + 1 } }
  have hL : LocalStable (fun gs : GenS M R => NStep st0 gs.st) := by
    intro gs gs' h _ _ _ _ _ e6 e7 _ _ _
    exact ⟨by rw [e7]; exact h.1, fun e => by rw [e6]; exact h.2 (by rw [← e7]; exact e)⟩
  obtain ⟨i1, _⟩ := run_folTopRQ (P := fun _ _ _ => True) (QA := fun _ => True) (QS := fun _ => True)
    env memoF (fun _ _ => trivial) (fun _ _ _ _ _ _ _ _ _ _ _ => trivial) hL
    (fun k hk idT gs r gs' hi _ e =>
      ⟨trivial, hi.trans (hres k hk idT gs r gs' e).1, (hres k hk idT gs r gs' e).2⟩)
    (NStep.refl' (st := st0) (st' := (genInit index st0).st) rfl rfl) trivial hf
  obtain ⟨_, hs, _, _, _⟩ := runEnd_fields id (gitG st0.g id) out gs
  exact (NStep.refl' (st := st) (st' := st0) rfl rfl).trans
    (i1.trans (NStep.refl' (runEnd_next id _ out gs) hs))

theorem memberStep_n {run : RunGo M R} {mem : MemGo M R} (hrun : RunN run) (hmem : MemN mem) :
    MemN (memberStep run mem) := by
  intro index pass ms st r st' e
  cases ms with
  | nil =>
    simp only [memberStep, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨_, rfl⟩ := e
    exact NStep.refl' rfl rfl
  | cons m ms =>
    have key : ∀ st1 : SkaState M R,
        ((Treap.get st.order m).bind fun o => (run m o st1).bind fun r =>
          if r.1.1 < index then some ((r.1.1, r.1.2.2), r.2) else
          (mem index pass ms r.2).map fun t => ((min r.1.1 t.1.1, r.1.2.2 || t.1.2), t.2)) = some (r, st') →
        st1.next = st.next → st1.stk = st.stk → NStep st st' := by
      intro st1 e h1 h2
      simp only [Option.bind_eq_some_iff] at e
      obtain ⟨o, _, ⟨r1, st2⟩, hr, e⟩ := e
      have a := (NStep.refl' (st := st) (st' := st1) h1 h2).trans (hrun _ _ _ _ _ hr)
      split at e
      · simp only [Option.some.injEq, Prod.mk.injEq] at e
        obtain ⟨_, rfl⟩ := e
        exact a
      · simp only [Option.map_eq_some_iff] at e
        obtain ⟨⟨t1, st3⟩, ht, e⟩ := e
        cases e
        exact a.trans (hmem _ _ _ _ _ _ ht)
    simp only [memberStep] at e
    split at e
    · exact hmem _ _ _ _ _ _ e
    · by_cases hp : pass > 1
      · simp only [hp, if_true] at e
        exact key _ e rfl rfl
      · simp only [hp, if_false] at e
        exact key _ e rfl rfl

theorem passStep_n {n : Nat} {mem : MemGo M R} {pass : PassGo M R} (hmem : MemN mem) (hpass : PassN pass) :
    PassN (passStep n mem pass) := by
  intro id index p st low st' e
  unfold passStep at e
  simp only [Option.bind_eq_some_iff] at e
  obtain ⟨ab, _, members, _, ⟨r1, st2⟩, hm, e⟩ := e
  have a : st.next ≤ st2.next := (hmem _ _ _ _ _ _ hm).1
  simp only at e
  split at e
  · simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨_, rfl⟩ := e
    exact a
  · simp only [Option.bind_eq_some_iff] at e
    obtain ⟨st3, hc, e⟩ := e
    have b := cull_next hc
    split at e
    · simp only [Option.map_eq_some_iff] at e
      obtain ⟨st4, hp, e⟩ := e
      cases e
      rw [pop_next hp, b]; exact a
    · exact Nat.le_trans (b ▸ a) (hpass _ _ _ _ _ _ e)

theorem cullPass_n {n : Nat} {pass : PassGo M R} (hpass : PassN pass) {id : Ident} {index : Nat}
    {st st' : SkaState M R} {low : Nat} (h : cullPass n pass id index st = some (low, st')) :
    st.next ≤ st'.next := by
  unfold cullPass at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨st1, hc, h⟩ := h
  exact (cull_next hc) ▸ hpass _ _ _ _ _ _ h

theorem analyzeStep_n {n : Nat} {memoF : Memo M} {run : RunGo M R} {pass : PassGo M R}
    (hrun : RunN run) (hpass : PassN pass) : AnaN (analyzeStep n memoF run pass) := by
  intro id st low st' e
  unfold analyzeStep at e
  split at e
  · cases e
  · simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨_, rfl⟩ := e
    exact NStep.refl' rfl rfl
  · simp only [Option.bind_eq_some_iff] at e
    obtain ⟨⟨r1, st2⟩, hr, e⟩ := e
    have a : st.next + 1 ≤ st2.next := (hrun _ _ _ _ _ hr).1
    refine NStep.of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_trans a ?_))
    simp only at e
    split at e
    · simp only [Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨_, rfl⟩ := e
      exact Nat.le_refl _
    · split at e
      · exact cullPass_n hpass e
      · simp only [Option.bind_eq_some_iff] at e
        obtain ⟨ab, _, e⟩ := e
        split at e
        · exact cullPass_n hpass e
        · simp only [Option.map_eq_some_iff] at e
          obtain ⟨st3, hp, e⟩ := e
          cases e
          exact Nat.le_of_eq (pop_next hp).symm

/-- The arms at the fuel `n` keep `NStep`. -/
def AllN (env : Env R) (memoF : Memo M) (n : Nat) : Prop :=
  (∀ orig, ResN (resolve env memoF n orig)) ∧ AnaN (analyze env memoF n) ∧ RunN (run env memoF n) ∧
    PassN (passLoop env memoF n) ∧ MemN (memberLoop env memoF n)

theorem allN_zero (env : Env R) (memoF : Memo M) : AllN env memoF 0 := by
  refine ⟨fun _ _ _ _ _ h => ?_, fun _ _ _ _ h => ?_, fun _ _ _ _ _ h => ?_,
    fun _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ h => ?_⟩
  · rw [resolve_zero] at h; cases h
  · rw [analyze_zero] at h; cases h
  · rw [run_zero] at h; cases h
  · rw [passLoop_zero] at h; cases h
  · rw [memberLoop_zero] at h; cases h

/-- **Every arm keeps `NStep`** (the pass loop: `next` does not fall), at every fuel. -/
theorem allN (env : Env R) (memoF : Memo M) : ∀ n, ∀ k, k ≤ n → AllN env memoF k
  | 0 => fun k hk => by rw [Nat.le_zero.mp hk]; exact allN_zero env memoF
  | n + 1 => fun k hk => by
    rcases Nat.lt_or_ge k (n + 1) with hl | hl
    · exact allN env memoF n k (Nat.le_of_lt_succ hl)
    · have e : k = n + 1 := Nat.le_antisymm hk hl
      subst e
      obtain ⟨r, a, u, p, m⟩ := allN env memoF n n (Nat.le_refl n)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro orig; rw [resolve_succ]; exact resolveStep_n env (r orig) a
      · rw [analyze_succ]; exact analyzeStep_n u p
      · rw [run_succ]
        exact runStep_n env memoF (fun k hk => fun idT gs r' gs' e =>
          (allN env memoF n k (Nat.le_of_lt hk)).1 idT idT gs r' gs' e)
      · rw [passLoop_succ]; exact passStep_n m p
      · rw [memberLoop_succ]; exact memberStep_n u m

end Ana
end SkaModel
end Formalization
