import lemmas.Ska.PassStack
import lemmas.Ska.PassGrow

/-!
# Good stacks: the depth of `+analyze`, the members of a pass loop, and the width (track F, Gaps 16)

`noStackSeq_heSock` (`Ska/PassStack.lean`) is about a sequence of pushes;
here it is turned into a fact about the stack itself, so that no push log is
needed.  A stack is **good** (`StkGood`) when every member is absent from,
and passes the guard of `push_guard` against, the part of the stack below
it.  A push that `resolve` makes afresh keeps a stack good (`stkGood_push`),
and so does every way the model removes members (`+pop` drops a top part,
`+cull` filters): both give a sublist, and a sublist of a good stack is good
(`stkGood_sub`).

* **`noGoodChain`**: from `KruskalBT`, there is no chain of good stacks,
  each one the previous one grown on top, whose length is unbounded, when
  the members' formulas lie among `Fs` and their subjects are shaped socks
  with leaves among `Ls` (`OkId`).  The suffix of each length is the same in
  all long enough stacks of the chain, so the chain has one infinite stack,
  read bottom up; its members are the sequence of `noStackSeq_heSock`.
* **`goodUp_acc`, the depth of `+analyze`**: growing a good stack on top is
  well-founded (`Acc`), the induction principle of the nested `+analyze`
  calls (each nested push is above the stack of its caller).
* **`stack_fin`, `passChain_stack_fin`, the members of one pass loop**:
  along a chain of passes (`PassNextQ`, the stack grows on top between pass
  starts by `GG`: `passGoOn_gg`) whose stacks are good, the stacks are
  eventually constant, so their members lie in one finite list.
* **`WidthFin`**: the width, the one hypothesis left about one loop: along
  every chain of passes, the identities that entered the graph after the
  loop's entry and are not on the stack (the finished functions, popped into
  `done`) lie in one finite list.
* **`passLoop_returns_w`**: the pass loop of one component returns from
  `KruskalBT`, `RunHalts`, `WidthFin`, and good stacks with `OkId` members
  along its chains (the arm invariant and the closure invariant still to be
  proved); no push tree, no `FinBranch`.
-/

namespace Formalization
namespace SkaModel
namespace Ana

open Nock

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-! ## 1. Good stacks -/

/-- The guard of `push_guard` for `y` against the stack `T` below it: past
`th` frames of its formula, `he` of its subject over each of theirs is false. -/
def PGuard (he : Sock → Sock → Bool) (th : Nat) (y : Ident) (T : List Ident) : Prop :=
  th ≤ (T.filter (fun i => i.2 = y.2)).length → ∀ x ∈ T, x.2 = y.2 → he y.1 x.1 = false

/-- **A good stack**: every member is absent from, and guarded against, the
part of the stack below it. -/
def StkGood (he : Sock → Sock → Bool) (th : Nat) : List Ident → Prop
  | [] => True
  | y :: T => y ∉ T ∧ PGuard he th y T ∧ StkGood he th T

theorem pGuard_sub {he : Sock → Sock → Bool} {th : Nat} {y : Ident} {T T' : List Ident}
    (hs : List.Sublist T' T) (h : PGuard he th y T) : PGuard he th y T' := fun hth x hx hx2 =>
  h (Nat.le_trans hth (hs.filter _).length_le) x (hs.subset hx) hx2

/-- **A sublist of a good stack is good**: `+pop` and `+cull` keep a stack good. -/
theorem stkGood_sub {he : Sock → Sock → Bool} {th : Nat} {S S' : List Ident} (hs : List.Sublist S' S) :
    StkGood he th S → StkGood he th S' := by
  induction hs with
  | slnil => exact id
  | cons a _ ih => exact fun h => ih h.2.2
  | cons_cons a hs ih => exact fun h => ⟨fun hm => h.1 (hs.subset hm), pGuard_sub hs h.2.1, ih h.2.2⟩

theorem stkGood_append {he : Sock → Sock → Bool} {th : Nat} {A T : List Ident}
    (h : StkGood he th (A ++ T)) : StkGood he th T :=
  stkGood_sub (List.sublist_append_right A T) h

theorem stkGood_filter {he : Sock → Sock → Bool} {th : Nat} {S : List Ident} (p : Ident → Bool)
    (h : StkGood he th S) : StkGood he th (S.filter p) :=
  stkGood_sub (List.filter_sublist) h

/-- **A push that `resolve` makes afresh keeps the stack good** (the push of
`analyzeStep` onto the stack of `gen`, after `resolveStep_new`'s misses). -/
theorem stkGood_push {env : Env R} {idT : Ident} {gen : GenS M R} (hs : Sg gen.st)
    (hg : Treap.get gen.st.g idT = none)
    (hr : recursiveCall env.he env.threshold idT gen.st.stk (gCore gen.st.g) = some none)
    (h : StkGood env.he env.threshold gen.st.stk) :
    StkGood env.he env.threshold (idT :: gen.st.stk) :=
  ⟨fun hm => hs idT hm hg, fun hth => push_guard hr hth, h⟩

/-! ## 2. No unbounded chain of good stacks -/

/-- An identity whose formula is among `Fs` and whose subject is a shaped
sock with leaves among `Ls`: the two "finite list" hypotheses of
`noStackSeq_heSock`. -/
def OkId (Fs : List Noun) (Ls : List Sock) (i : Ident) : Prop :=
  i.2 ∈ Fs ∧ ∃ c d, i.1 = Sock.mk c d ∧ Shaped c d ∧ ∀ a ∈ BT.leaves (capeBT c d), a ∈ Ls

/-- The suffix of length `p`. -/
def sfx {α : Type} (l : List α) (p : Nat) : List α := l.drop (l.length - p)

theorem sfx_append {α : Type} {A T : List α} {p : Nat} (hp : p ≤ T.length) : sfx (A ++ T) p = sfx T p := by
  unfold sfx
  have e : (A ++ T).length - p = A.length + (T.length - p) := by
    simp only [List.length_append]; omega
  rw [e, List.drop_length_add_append]

theorem sfx_length {α : Type} {l : List α} {p : Nat} (hp : p ≤ l.length) : (sfx l p).length = p := by
  unfold sfx; rw [List.length_drop]; omega

theorem sfx_succ {α : Type} {l : List α} {p : Nat} (hp : p + 1 ≤ l.length) :
    ∃ x, sfx l (p + 1) = x :: sfx l p := by
  unfold sfx
  have h : l.length - (p + 1) < l.length := by omega
  refine ⟨l[l.length - (p + 1)], ?_⟩
  rw [List.drop_eq_getElem_cons h]
  have e : l.length - (p + 1) + 1 = l.length - p := by omega
  rw [e]

theorem suffix_chain {S : Nat → List Ident} (h : ∀ k, ∃ N, S (k + 1) = N ++ S k) :
    ∀ {k k' : Nat}, k ≤ k' → ∃ A, S k' = A ++ S k := by
  intro k k' hk
  induction hk with
  | refl => exact ⟨[], rfl⟩
  | step _ ih =>
    obtain ⟨A, hA⟩ := ih
    obtain ⟨N, hN⟩ := h _
    exact ⟨N ++ A, by rw [hN, hA, List.append_assoc]⟩

open Compiler in
/-- **No unbounded chain of good stacks**, from `KruskalBT`: the stacks
`S k`, each grown on top of the previous one, good, with `OkId` members,
have bounded length. -/
theorem noGoodChain (hK : KruskalBT) (th : Nat) (Fs : List Noun) (Ls : List Sock) :
    ¬ ∃ S : Nat → List Ident, (∀ k, StkGood heSock th (S k)) ∧ (∀ k, ∀ i ∈ S k, OkId Fs Ls i) ∧
      (∀ k, ∃ N, S (k + 1) = N ++ S k) ∧ (∀ m, ∃ k, m ≤ (S k).length) := by
  rintro ⟨S, hg, hok, hN, hun⟩
  have stab : ∀ k k' p, p ≤ (S k).length → p ≤ (S k').length → sfx (S k) p = sfx (S k') p := by
    intro k k' p h1 h2
    rcases Nat.le_total k k' with hk | hk
    · obtain ⟨A, hA⟩ := suffix_chain hN hk
      rw [hA, sfx_append h1]
    · obtain ⟨A, hA⟩ := suffix_chain hN hk
      rw [hA, sfx_append h2]
  obtain ⟨kp, hkp⟩ : ∃ kp : Nat → Nat, ∀ p, p ≤ (S (kp p)).length :=
    ⟨fun p => Classical.choose (hun p), fun p => Classical.choose_spec (hun p)⟩
  obtain ⟨B, hBd⟩ : ∃ B : Nat → List Ident, ∀ p, B p = sfx (S (kp p)) p := ⟨_, fun _ => rfl⟩
  have hB : ∀ k p, p ≤ (S k).length → sfx (S k) p = B p := fun k p h => by
    rw [hBd]; exact stab k (kp p) p h (hkp p)
  have hBs : ∀ p, ∃ x, B (p + 1) = x :: B p := by
    intro p
    obtain ⟨x, hx⟩ := sfx_succ (hkp (p + 1))
    refine ⟨x, ?_⟩
    rw [hBd, hx, hB _ p (by have := hkp (p + 1); omega)]
  obtain ⟨w, hw⟩ : ∃ w : Nat → Ident, ∀ p, B (p + 1) = w p :: B p :=
    ⟨fun p => Classical.choose (hBs p), fun p => Classical.choose_spec (hBs p)⟩
  have hsub : ∀ p, List.Sublist (B p) (S (kp p)) := fun p => by rw [hBd]; exact List.drop_sublist _ _
  have goodB : ∀ p, StkGood heSock th (B p) := fun p => stkGood_sub (hsub p) (hg _)
  have okB : ∀ p, ∀ i ∈ B p, OkId Fs Ls i := fun p i hi => hok _ i ((hsub p).subset hi)
  have okw : ∀ p, OkId Fs Ls (w p) := fun p => okB (p + 1) (w p) (by rw [hw p]; exact List.mem_cons.mpr (Or.inl rfl))
  have goodw : ∀ p, w p ∉ B p ∧ PGuard heSock th (w p) (B p) := fun p => by
    have := goodB (p + 1); rw [hw p] at this; exact ⟨this.1, this.2.1⟩
  have hmem : ∀ j i, i < j → w i ∈ B j := by
    intro j
    induction j with
    | zero => intro i h; omega
    | succ j ih =>
      intro i h
      rw [hw j]
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
      · exact List.mem_cons_of_mem _ (ih i h)
      · rw [h]; exact List.mem_cons.mpr (Or.inl rfl)
  exact noStackSeq_heSock hK th Fs Ls ⟨w, B, fun n => (okw n).1, fun n => (okw n).2,
    fun i j h e => (goodw j).1 (e ▸ hmem j i h), fun i j h => hmem j i h, fun j => (goodw j).2⟩

/-! ## 3. The depth of `+analyze` -/

/-- `S'` is a good stack grown on top of `S` by at least one identity, with
`OkId` members: the stack of a nested push against the stack of its caller. -/
def GoodUp (th : Nat) (Fs : List Noun) (Ls : List Sock) (S' S : List Ident) : Prop :=
  StkGood Compiler.heSock th S' ∧ (∀ i ∈ S', OkId Fs Ls i) ∧ ∃ N, N ≠ [] ∧ S' = N ++ S

/-- **The nesting of `+analyze` is well-founded**: growing a good stack on
top is a well-founded relation, from `KruskalBT`. -/
theorem goodUp_acc (hK : KruskalBT) (th : Nat) (Fs : List Noun) (Ls : List Sock) (S : List Ident) :
    Acc (GoodUp th Fs Ls) S := by
  refine acc_of_no_chain (fun f hf => ?_) S
  have hlen : ∀ k, k ≤ (f k).length := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      obtain ⟨N, hN, e⟩ := (hf k).2.2
      have : N.length ≠ 0 := fun h => hN (List.eq_nil_of_length_eq_zero h)
      rw [e, List.length_append]; omega
  refine noGoodChain hK th Fs Ls ⟨fun k => f (k + 1), fun k => (hf k).1, fun k => (hf k).2.1,
    fun k => ?_, fun m => ⟨m, ?_⟩⟩
  · obtain ⟨N, _, e⟩ := (hf (k + 1)).2.2; exact ⟨N, e⟩
  · show m ≤ (f (m + 1)).length
    have := hlen (m + 1); omega

/-! ## 4. The members of one pass loop -/

/-- **The members along a chain of good stacks lie in one finite list**:
the stacks are eventually constant. -/
theorem stack_fin (hK : KruskalBT) (th : Nat) (Fs : List Noun) (Ls : List Sock) {S : Nat → List Ident}
    (hg : ∀ k, StkGood Compiler.heSock th (S k)) (hok : ∀ k, ∀ i ∈ S k, OkId Fs Ls i)
    (hN : ∀ k, ∃ N, S (k + 1) = N ++ S k) : ∃ I : List Ident, ∀ k i, i ∈ S k → i ∈ I := by
  have hb : ∃ m, ∀ k, (S k).length < m := by
    refine Classical.byContradiction fun hn => noGoodChain hK th Fs Ls ⟨S, hg, hok, hN, fun m => ?_⟩
    refine Classical.byContradiction fun hm => hn ⟨m, fun k => ?_⟩
    exact Nat.lt_of_not_le fun h => hm ⟨k, h⟩
  obtain ⟨m, hm⟩ := hb
  have mono : ∀ {k k' : Nat}, k ≤ k' → (S k).length ≤ (S k').length := fun hk => by
    obtain ⟨A, hA⟩ := suffix_chain hN hk; rw [hA, List.length_append]; omega
  have stable : ∃ K, ∀ k, K ≤ k → (S k).length = (S K).length := by
    refine Classical.byContradiction fun hn => ?_
    have grow : ∀ j, ∃ K, j ≤ (S K).length := by
      intro j
      induction j with
      | zero => exact ⟨0, Nat.zero_le _⟩
      | succ j ih =>
        obtain ⟨K, hK'⟩ := ih
        have : ∃ k, K ≤ k ∧ (S k).length ≠ (S K).length :=
          Classical.byContradiction fun h' => hn ⟨K, fun k hk => Classical.byContradiction fun e => h' ⟨k, hk, e⟩⟩
        obtain ⟨k, hk, e⟩ := this
        exact ⟨k, by have := mono hk; omega⟩
    obtain ⟨K, hK'⟩ := grow m
    exact absurd (hm K) (by omega)
  obtain ⟨K, hKs⟩ := stable
  refine ⟨S K, fun k i hi => ?_⟩
  rcases Nat.le_total k K with h | h
  · obtain ⟨A, hA⟩ := suffix_chain hN h; rw [hA]; exact List.mem_append_right _ hi
  · obtain ⟨A, hA⟩ := suffix_chain hN h
    have hl := hKs k h
    rw [hA, List.length_append] at hl
    have hA0 : A = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hA, hA0] at hi; exact hi

/-- **`GG` over a pass that goes on**, from a state whose stack is in the graph. -/
theorem passGoOn_gg (env : Env R) (memoF : Memo M) {n : Nat} {id : Ident} {index pass : Nat}
    {st st' : SkaState M R} (hs : Sg st) (h : PassGoOn env memoF n id index pass st st') : GG st st' := by
  have key : ∀ members r, memberLoop env memoF n index pass members
      { st with stats := { st.stats with passes := st.stats.passes + 1 } } = some (r, st') → GG st st' := by
    intro members r hml
    have hs' : Sg { st with stats := { st.stats with passes := st.stats.passes + 1 } } := hs
    exact ((allG env memoF n n (Nat.le_refl n)).2.2.2.2 _ _ _ _ _ _ hs' hml).1
  rcases h with ⟨ab, members, r, _, _, h3, _⟩ | ⟨ab, members, r, _, _, h3, _⟩
  · exact key members r h3
  · exact key members r h3

/-- Good stacks with `OkId` members at every state the passes reach from `x`. -/
def ChainStk (env : Env R) (memoF : Memo M) (id : Ident) (index : Nat) (x : Nat × SkaState M R)
    (th : Nat) (Fs : List Noun) (Ls : List Sock) : Prop :=
  ∀ y, PassReachQ env memoF id index x y →
    StkGood Compiler.heSock th y.2.stk ∧ ∀ i ∈ y.2.stk, OkId Fs Ls i

/-- **The members of one pass loop are finitely many**: along every chain of
passes from a `ChainInv` state with good stacks, the stack members lie in one
finite list (with dab8478 a member stays on the stack until the stable end). -/
theorem passChain_stack_fin (hK : KruskalBT) (env : Env R) {memoF : Memo M} (hmF : MemoWF memoF)
    (hmT : MemoTP memoF) (hmN : MemoNorm memoF) (hmI : MemoNI memoF) {id : Ident} {index : Nat}
    {rest : List Ident} {x : Nat × SkaState M R} (hc : ChainInv memoF id index rest x.2)
    {th : Nat} {Fs : List Noun} {Ls : List Sock} (hstk : ChainStk env memoF id index x th Fs Ls)
    (f : Nat → Nat × SkaState M R) (hf : ∀ k, PassNextQ env memoF id index x (f (k + 1)) (f k)) :
    ∃ I : List Ident, ∀ k i, i ∈ (f k).2.stk → i ∈ I := by
  refine stack_fin hK th Fs Ls (S := fun k => (f k).2.stk) (fun k => (hstk _ (hf k).1).1)
    (fun k => (hstk _ (hf k).1).2) (fun k => ?_)
  obtain ⟨m, _, hp⟩ := (hf k).2
  have hs : Sg (f k).2 := (passReachQ_inv env hmF hmT hmN hmI (hf k).1 hc).1.sg
  obtain ⟨N, e, _⟩ := (passGoOn_gg env memoF hs hp).2.2
  exact ⟨N, e⟩

/-! ## 5. The width, and the loop of one component -/

/-- **The width of one pass loop** (the hypothesis left about one loop):
along every chain of passes from `x`, the identities that entered the graph
after `x` and are not on the stack, i.e. the functions that the runs of the
loop pushed and that finished (popped into `done`) before that pass, lie in
one finite list. -/
def WidthFin (env : Env R) (memoF : Memo M) (id : Ident) (index : Nat) (x : Nat × SkaState M R) : Prop :=
  ∀ f : Nat → Nat × SkaState M R, (∀ k, PassNextQ env memoF id index x (f (k + 1)) (f k)) →
    ∃ I : List Ident, ∀ k i, GIn (f k).2 i → ¬ GIn x.2 i → i ∉ (f k).2.stk → i ∈ I

/-- **`FinIdentsG` from the members and the width.** -/
theorem finIdentsG_of_width (hK : KruskalBT) (env : Env R) {memoF : Memo M} (hmF : MemoWF memoF)
    (hmT : MemoTP memoF) (hmN : MemoNorm memoF) (hmI : MemoNI memoF) {id : Ident} {index : Nat}
    {rest : List Ident} {x : Nat × SkaState M R} (hc : ChainInv memoF id index rest x.2)
    {th : Nat} {Fs : List Noun} {Ls : List Sock} (hstk : ChainStk env memoF id index x th Fs Ls)
    (hw : WidthFin env memoF id index x)
    (f : Nat → Nat × SkaState M R) (hf : ∀ k, PassNextQ env memoF id index x (f (k + 1)) (f k)) :
    FinIdentsG f := by
  obtain ⟨I1, h1⟩ := passChain_stack_fin hK env hmF hmT hmN hmI hc hstk f hf
  obtain ⟨I2, h2⟩ := hw f hf
  refine ⟨(Treap.tap x.2.g).map (·.1) ++ I1 ++ I2, fun k i hi => ?_⟩
  by_cases hx : GIn x.2 i
  · apply List.mem_append_left; apply List.mem_append_left
    cases e : Treap.get x.2.g i with
    | none => exact absurd e hx
    | some d => exact List.mem_map.mpr ⟨(i, d), (Treap.mem_tap _ _ _).mpr e, rfl⟩
  · by_cases hs : i ∈ (f k).2.stk
    · exact List.mem_append_left _ (List.mem_append_right _ (h1 k i hs))
    · exact List.mem_append_right _ (h2 k i hi hx hs)

/-- **The pass loop of one component returns** from `KruskalBT`, `RunHalts`,
the width `WidthFin`, and good stacks with `OkId` members along its chains:
no push tree and no `FinBranch`. -/
theorem passLoop_returns_w (hK : KruskalBT) (env : Env R) {memoF : Memo M} (hmF : MemoWF memoF)
    (hmT : MemoTP memoF) (hmN : MemoNorm memoF) (hmI : MemoNI memoF) (hrun : RunHalts env memoF)
    (id : Ident) (index : Nat) (rest : List Ident) (x : Nat × SkaState M R)
    (hc : ChainInv memoF id index rest x.2) {th : Nat} {Fs : List Noun} {Ls : List Sock}
    (hstk : ChainStk env memoF id index x th Fs Ls) (hw : WidthFin env memoF id index x) :
    ∃ n r, passLoop env memoF n id index x.1 x.2 = some r :=
  passLoop_returns_g env hmF hmT hmN hmI hrun id index rest x hc fun f hf =>
    finIdentsG_of_width hK env hmF hmT hmN hmI hc hstk hw f hf

/-! ## 6. Every arm keeps the stack good -/

/-- The stack of `st` is good for the guard of `env`. -/
def SG (env : Env R) (st : SkaState M R) : Prop := StkGood env.he env.threshold st.stk

def ResS (env : Env R) (res : ResGo M R) : Prop :=
  ∀ idT gs r gs', Sg gs.st → SG env gs.st → res idT gs = some (r, gs') → SG env gs'.st

/-- `+analyze` of `id`, not in the graph, onto a stack that stays good with `id` pushed. -/
def AnaS (env : Env R) (ana : AnaGo M R) : Prop :=
  ∀ id (st : SkaState M R) low st', Sg st → Treap.get st.g id = none →
    StkGood env.he env.threshold (id :: st.stk) → ana id st = some (low, st') → SG env st'

def RunS (env : Env R) (run : RunGo M R) : Prop :=
  ∀ id index st r st', Sg st → SG env st → run id index st = some (r, st') → SG env st'

def MemS (env : Env R) (mem : MemGo M R) : Prop :=
  ∀ index pass ms st r st', Sg st → SG env st → mem index pass ms st = some (r, st') → SG env st'

def PassS (env : Env R) (pass : PassGo M R) : Prop :=
  ∀ id index p st low st', Sg st → SG env st → pass id index p st = some (low, st') → SG env st'

theorem resolveStep_s (env : Env R) {orig : Ident} {resolve : ResGo M R} {analyze : AnaGo M R}
    (hres : ResS env resolve) (hana : AnaS env analyze) : ResS env (resolveStep env resolve analyze orig) := by
  intro idT gs r gs' hs hsg e
  unfold resolveStep at e
  cases hg : Treap.get gs.st.g idT with
  | some d =>
    simp only [hg] at e
    cases ho : Treap.get gs.st.order idT with
    | none =>
      simp only [ho, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e; exact hsg
    | some o =>
      simp only [ho, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e; exact hsg
  | none =>
    rw [hg] at e
    simp only at e
    cases hm : gitMi gs.st.done orig.2 idT.1 with
    | none => rw [hm] at e; cases e
    | some m =>
      rw [hm] at e
      cases m with
      | some m =>
        simp only [Option.some.injEq, Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e; exact hsg
      | none =>
        simp only at e
        cases hr : recursiveCall env.he env.threshold idT gs.st.stk (gCore gs.st.g) with
        | none => rw [hr] at e; cases e
        | some c =>
          rw [hr] at e
          cases c with
          | none =>
            simp only [Option.map_eq_some_iff] at e
            obtain ⟨⟨low, st'⟩, ha, e⟩ := e
            cases e
            exact hana _ _ _ _ hs hg (stkGood_push (gen := gs) hs hg hr hsg) ha
          | some p =>
            obtain ⟨b, i⟩ := p
            cases b with
            | false => exact hres _ _ _ _ hs hsg e
            | true =>
              simp only [Option.map_eq_some_iff] at e
              obtain ⟨o, _, e⟩ := e
              cases e; exact hsg

theorem runStep_s (env : Env R) (memoF : Memo M) {n : Nat}
    (hresG : ∀ k, k < n → ResG (resolveR env memoF k)) (hres : ∀ k, k < n → ResS env (resolveR env memoF k)) :
    RunS env (runStep (folLoop env memoF n)) := by
  intro id index st r st' hs hsg e
  unfold runStep at e
  simp only [Option.map_eq_some_iff] at e
  obtain ⟨⟨out, gs⟩, hf, e⟩ := e
  cases e
  let st0 : SkaState M R := { st with stats := { st.stats with runs := st.stats.runs + 1 } }
  have hL : LocalStable (fun gs : GenS M R => Sg gs.st ∧ SG env gs.st) := by
    intro gs gs' h _ _ e3 _ _ e6 _ _ _ _
    refine ⟨fun i hi => ?_, ?_⟩
    · have := h.1 i (e6 ▸ hi); unfold GIn at this ⊢; rw [e3]; exact this
    · unfold SG; rw [e6]; exact h.2
  obtain ⟨i1, _⟩ := run_folTopRQ (P := fun _ _ _ => True) (QA := fun _ => True) (QS := fun _ => True)
    env memoF (fun _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ _ _ _ => trivial) hL
    (fun k hk idT gs r gs' hi _ e =>
      ⟨trivial, ⟨(hresG k hk idT gs r gs' hi.1 e).1.1, hres k hk idT gs r gs' hi.1 hi.2 e⟩,
        (hresG k hk idT gs r gs' hi.1 e).2.2⟩)
    (Inv := fun gs : GenS M R => Sg gs.st ∧ SG env gs.st)
    (index := index) (st := st0) ⟨hs, hsg⟩ trivial hf
  obtain ⟨_, hs', _⟩ := runEnd_fields id (gitG st0.g id) out gs
  show StkGood env.he env.threshold (runEnd id (gitG st0.g id) out gs).2.stk
  rw [hs']; exact i1.2

theorem memberStep_s {env : Env R} {run : RunGo M R} {mem : MemGo M R} (hrunG : RunG run)
    (hrun : RunS env run) (hmem : MemS env mem) : MemS env (memberStep run mem) := by
  intro index pass ms st r st' hs hsg e
  cases ms with
  | nil =>
    simp only [memberStep, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨_, rfl⟩ := e
    exact hsg
  | cons m ms =>
    have key : ∀ st1 : SkaState M R,
        ((Treap.get st.order m).bind fun o => (run m o st1).bind fun r =>
          if r.1.1 < index then some ((r.1.1, r.1.2.2), r.2) else
          (mem index pass ms r.2).map fun t => ((min r.1.1 t.1.1, r.1.2.2 || t.1.2), t.2)) = some (r, st') →
        st1.stk = st.stk → st1.g = st.g → SG env st' := by
      intro st1 e h2 h3
      simp only [Option.bind_eq_some_iff] at e
      obtain ⟨o, _, ⟨r1, st2⟩, hr, e⟩ := e
      have hs1 : Sg st1 := fun i hi => by
        have := hs i (h2 ▸ hi); unfold GIn at this ⊢; rw [h3]; exact this
      have hsg1 : SG env st1 := by unfold SG; rw [h2]; exact hsg
      have hs2 : Sg st2 := (hrunG _ _ _ _ _ hs1 hr).1.1
      have hsg2 := hrun _ _ _ _ _ hs1 hsg1 hr
      split at e
      · simp only [Option.some.injEq, Prod.mk.injEq] at e
        obtain ⟨_, rfl⟩ := e
        exact hsg2
      · simp only [Option.map_eq_some_iff] at e
        obtain ⟨⟨t1, st3⟩, ht, e⟩ := e
        cases e
        exact hmem _ _ _ _ _ _ hs2 hsg2 ht
    simp only [memberStep] at e
    split at e
    · exact hmem _ _ _ _ _ _ hs hsg e
    · by_cases hp : pass > 1
      · simp only [hp, if_true] at e
        exact key _ e rfl rfl
      · simp only [hp, if_false] at e
        exact key _ e rfl rfl

/-- `+cull` keeps the stack in the graph and good. -/
theorem cull_s {env : Env R} {n : Nat} {id : Ident} {st st' : SkaState M R} (hs : Sg st) (hsg : SG env st)
    (h : cull n id st = some st') : Sg st' ∧ SG env st' := by
  obtain ⟨_, _, d, _, _, _, hg, hstk⟩ := cull_struct h
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [hstk] at hi
    obtain ⟨hi, hd⟩ := List.mem_filter.mp hi
    unfold GIn; rw [hg i]
    have : d i = false := by simpa using hd
    rw [this]; exact hs i hi
  · unfold SG; rw [hstk]; exact stkGood_filter _ hsg

/-- `+pop` leaves a sublist of the stack. -/
theorem pop_sub {id : Ident} {st st' : SkaState M R} (h : pop id st = some st') : List.Sublist st'.stk st.stk := by
  obtain ⟨pre, e, _, _⟩ := popGo_g st.stk st st' h
  rw [e]
  exact (List.sublist_cons_self _ _).trans (List.sublist_append_right _ _)

theorem pop_s {env : Env R} {id : Ident} {st st' : SkaState M R} (hsg : SG env st) (h : pop id st = some st') :
    SG env st' := stkGood_sub (pop_sub h) hsg

theorem passStep_s {env : Env R} {n : Nat} {mem : MemGo M R} {pass : PassGo M R} (hmemG : MemG mem)
    (hmem : MemS env mem) (hpass : PassS env pass) : PassS env (passStep n mem pass) := by
  intro id index p st low st' hs hsg e
  unfold passStep at e
  simp only [Option.bind_eq_some_iff] at e
  obtain ⟨ab, _, members, _, ⟨r1, st2⟩, hml, e⟩ := e
  have hs2 : Sg st2 := (hmemG _ _ _ _ _ _ (by exact hs) hml).1.1
  have hsg2 : SG env st2 := hmem _ _ _ _ _ _ (by exact hs) (by exact hsg) hml
  simp only at e
  split at e
  · simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨_, rfl⟩ := e
    exact hsg2
  · split at e
    · unfold passEnd at e
      simp only [Option.bind_eq_some_iff] at e
      obtain ⟨_, _, _, _, e⟩ := e
      split at e
      · exact hpass _ _ _ _ _ _ hs2 hsg2 e
      · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at e
        obtain ⟨st3, hc, st4, hp, e⟩ := e
        cases e
        exact pop_s (cull_s hs2 hsg2 hc).2 hp
    · exact hpass _ _ _ _ _ _ hs2 hsg2 e

theorem cullPass_s {env : Env R} {n : Nat} {pass : PassGo M R} (hpass : PassS env pass) {id : Ident}
    {index : Nat} {st st' : SkaState M R} {low : Nat} (hs : Sg st) (hsg : SG env st)
    (h : cullPass n pass id index st = some (low, st')) : SG env st' := by
  unfold cullPass at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨st1, hc, h⟩ := h
  obtain ⟨a, b⟩ := cull_s hs hsg hc
  exact hpass _ _ _ _ _ _ a b h

theorem analyzeStep_s {env : Env R} {n : Nat} {memoF : Memo M} {run : RunGo M R} {pass : PassGo M R}
    (hrunG : RunG run) (hrun : RunS env run) (hpass : PassS env pass) :
    AnaS env (analyzeStep n memoF run pass) := by
  intro id st low st' hs hg0 hsg0 e
  unfold analyzeStep at e
  split at e
  · cases e
  · simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨_, rfl⟩ := e
    exact hsg0.2.2
  · simp only [Option.bind_eq_some_iff] at e
    obtain ⟨⟨r1, st2⟩, hr, e⟩ := e
    let stp : SkaState M R := { st with next := st.next + 1, order := Treap.put st.order id st.next,
                                         stk := id :: st.stk, g := Treap.put st.g id FDatum.bunt }
    have hsp : Sg stp := fun i hi => by
      rcases List.mem_cons.mp hi with rfl | hi
      · exact get_put_self_ne_none _ _ _
      · exact get_put_ne_none (hs i hi)
    have hs2 : Sg st2 := (hrunG _ _ _ _ _ hsp hr).1.1
    have hsg2 : SG env st2 := hrun _ _ _ _ _ hsp hsg0 hr
    simp only at e
    split at e
    · simp only [Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨_, rfl⟩ := e
      exact hsg2
    · split at e
      · exact cullPass_s hpass hs2 hsg2 e
      · simp only [Option.bind_eq_some_iff] at e
        obtain ⟨ab, _, e⟩ := e
        split at e
        · exact cullPass_s hpass hs2 hsg2 e
        · simp only [Option.map_eq_some_iff] at e
          obtain ⟨st3, hp, e⟩ := e
          cases e
          exact pop_s hsg2 hp

/-- The arms at the fuel `n` keep the stack good. -/
def AllS (env : Env R) (memoF : Memo M) (n : Nat) : Prop :=
  (∀ orig, ResS env (resolve env memoF n orig)) ∧ AnaS env (analyze env memoF n) ∧ RunS env (run env memoF n) ∧
    PassS env (passLoop env memoF n) ∧ MemS env (memberLoop env memoF n)

theorem allS_zero (env : Env R) (memoF : Memo M) : AllS env memoF 0 := by
  refine ⟨fun _ _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ _ h => ?_,
    fun _ _ _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ _ _ h => ?_⟩
  · rw [resolve_zero] at h; cases h
  · rw [analyze_zero] at h; cases h
  · rw [run_zero] at h; cases h
  · rw [passLoop_zero] at h; cases h
  · rw [memberLoop_zero] at h; cases h

/-- **Every arm keeps the stack good**, at every fuel: the stacks of the
analysis are good from a good start (the push log of `noStackSeq_heSock`,
without a log: each push is guarded against the stack below it, and nothing
else is ever put under a member). -/
theorem allS (env : Env R) (memoF : Memo M) : ∀ n, ∀ k, k ≤ n → AllS env memoF k
  | 0 => fun k hk => by rw [Nat.le_zero.mp hk]; exact allS_zero env memoF
  | n + 1 => fun k hk => by
    rcases Nat.lt_or_ge k (n + 1) with hl | hl
    · exact allS env memoF n k (Nat.le_of_lt_succ hl)
    · have e : k = n + 1 := Nat.le_antisymm hk hl
      subst e
      obtain ⟨r, a, u, p, m⟩ := allS env memoF n n (Nat.le_refl n)
      obtain ⟨_, _, uG, _, mG⟩ := allG env memoF n n (Nat.le_refl n)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro orig; rw [resolve_succ]; exact resolveStep_s env (r orig) a
      · rw [analyze_succ]; exact analyzeStep_s uG u p
      · rw [run_succ]
        exact runStep_s env memoF
          (fun k hk => fun idT gs r' gs' hs e => (allG env memoF n k (Nat.le_of_lt hk)).1 idT idT gs r' gs' hs e)
          (fun k hk => fun idT gs r' gs' hs hsg e => (allS env memoF n k (Nat.le_of_lt hk)).1 idT idT gs r' gs' hs hsg e)
      · rw [passLoop_succ]; exact passStep_s mG m p
      · rw [memberLoop_succ]; exact memberStep_s uG u m

/-- A pass that goes on keeps the stack good. -/
theorem passGoOn_s (env : Env R) (memoF : Memo M) {n : Nat} {id : Ident} {index pass : Nat}
    {st st' : SkaState M R} (hs : Sg st) (hsg : SG env st) (h : PassGoOn env memoF n id index pass st st') :
    SG env st' := by
  have key : ∀ members r, memberLoop env memoF n index pass members
      { st with stats := { st.stats with passes := st.stats.passes + 1 } } = some (r, st') → SG env st' :=
    fun members r hml => (allS env memoF n n (Nat.le_refl n)).2.2.2.2 _ _ _ _ _ _ (by exact hs) (by exact hsg) hml
  rcases h with ⟨ab, members, r, _, _, h3, _⟩ | ⟨ab, members, r, _, _, h3, _⟩
  · exact key members r h3
  · exact key members r h3

/-- **`ChainStk` from a good start**: with `env.he` the `+he-sock` of the
compiler, a good stack at the loop's entry, and `OkId` members (the closure
invariant, not proved here) at every state the passes reach. -/
theorem chainStk_of (env : Env R) {memoF : Memo M} (hmF : MemoWF memoF) (hmT : MemoTP memoF)
    (hmN : MemoNorm memoF) (hmI : MemoNI memoF) {id : Ident} {index : Nat} {rest : List Ident}
    {x : Nat × SkaState M R} (hc : ChainInv memoF id index rest x.2) (hhe : env.he = Compiler.heSock)
    (hsg : SG env x.2) {Fs : List Noun} {Ls : List Sock}
    (hok : ∀ y, PassReachQ env memoF id index x y → ∀ i ∈ y.2.stk, OkId Fs Ls i) :
    ChainStk env memoF id index x env.threshold Fs Ls := by
  intro y hy
  refine ⟨?_, hok y hy⟩
  have : SG env y.2 := by
    induction hy with
    | refl => exact hsg
    | step hr hp ih => exact passGoOn_s env memoF (passReachQ_inv env hmF hmT hmN hmI hr hc).1.sg ih hp
  unfold SG at this; rw [hhe] at this; exact this

/-- **The pass loop of one component returns** from `KruskalBT`, `RunHalts`,
the width `WidthFin`, a good stack at its entry and `OkId` members along its
chains (the closure invariant). -/
theorem passLoop_returns_ws (hK : KruskalBT) (env : Env R) {memoF : Memo M} (hmF : MemoWF memoF)
    (hmT : MemoTP memoF) (hmN : MemoNorm memoF) (hmI : MemoNI memoF) (hrun : RunHalts env memoF)
    (hhe : env.he = Compiler.heSock) (id : Ident) (index : Nat) (rest : List Ident) (x : Nat × SkaState M R)
    (hc : ChainInv memoF id index rest x.2) (hsg : SG env x.2) {Fs : List Noun} {Ls : List Sock}
    (hok : ∀ y, PassReachQ env memoF id index x y → ∀ i ∈ y.2.stk, OkId Fs Ls i)
    (hw : WidthFin env memoF id index x) :
    ∃ n r, passLoop env memoF n id index x.1 x.2 = some r :=
  passLoop_returns_w hK env hmF hmT hmN hmI hrun id index rest x hc
    (chainStk_of env hmF hmT hmN hmI hc hhe hsg hok) hw

end Ana
end SkaModel
end Formalization
