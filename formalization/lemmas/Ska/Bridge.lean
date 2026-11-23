import lemmas.Ska.Analysis
import lemmas.Ska.ConvergeRel

/-!
# The state-passing `fol-loop` is in `FolR`

`bridge_step`: one level of the state-passing `fol-loop` (`Ana.folStep`),
projected to the capes of `gen`, is one level of the fixed-table model
(`folStep`) with a table and a recursion of its own: the table has the one
answer that `resolve` gave, and the recursion is the list of the calls the
level made (`goL`), told apart by the ghost.  So a run is in `FolR P`
(`folLoop_folR`) when every answer `resolve` gives is in `P`, which needs an
invariant `Inv` of the state that `resolve` keeps and that depends only on
the parts of the state a level does not change itself (`LocalStable`).
-/

namespace Formalization
namespace SkaModel
namespace Ana

open Nock

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-! ## A recursion given by a list of calls -/

/-- The arguments of the fixed model's recursion. -/
abbrev Key := Noun × Anno × Option Noun × Bool × Bool × Gen

/-- The recursion that answers the calls of a list, the first that fits. -/
def goL (calls : List (Key × (FolOut × Gen))) : FolGo := fun fol sub mk bc df gen =>
  (calls.find? (fun c => decide (c.1 = (fol, sub, mk, bc, df, gen)))).map (·.2)

theorem goL_hd {fol : Noun} {sub : Anno} {mk : Option Noun} {bc df : Bool} {gen : Gen}
    {r : FolOut × Gen} {l : List (Key × (FolOut × Gen))} :
    goL (((fol, sub, mk, bc, df, gen), r) :: l) fol sub mk bc df gen = some r := by
  simp [goL, List.find?]

theorem goL_tl {k : Key} {r : FolOut × Gen} {l : List (Key × (FolOut × Gen))} {fol : Noun}
    {sub : Anno} {mk : Option Noun} {bc df : Bool} {gen : Gen} (h : gen.ghost ≠ k.2.2.2.2.2.ghost) :
    goL ((k, r) :: l) fol sub mk bc df gen = goL l fol sub mk bc df gen := by
  have hne : (k = (fol, sub, mk, bc, df, gen)) = False := by
    apply propext; constructor
    · intro e; subst e; exact h rfl
    · intro e; exact e.elim
  simp [goL, List.find?, hne]

theorem goL_mem {calls : List (Key × (FolOut × Gen))} {fol : Noun} {sub : Anno} {mk : Option Noun}
    {bc df : Bool} {gen : Gen} {r : FolOut × Gen} (h : goL calls fol sub mk bc df gen = some r) :
    ((fol, sub, mk, bc, df, gen), r) ∈ calls := by
  unfold goL at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨c, hc, rfl⟩ := h
  have hm := List.mem_of_find?_eq_some hc
  have he := List.find?_some hc
  simp only [decide_eq_true_eq] at he
  rw [← he]
  exact hm

variable {P : Sock → Noun → TabEntry → Prop}

theorem goR_goL {n : Nat} {calls : List (Key × (FolOut × Gen))}
    (h : ∀ c ∈ calls, FolR P n c.1.1 c.1.2.1 c.1.2.2.1 c.1.2.2.2.1 c.1.2.2.2.2.1 c.1.2.2.2.2.2 c.2.1 c.2.2) :
    GoR P n (goL calls) :=
  fun _ _ _ _ _ _ _ _ hg => h _ (goL_mem hg)

theorem folR_reghost {n : Nat} {fol : Noun} {sub : Anno} {mk : Option Noun} {bc df : Bool}
    {gen g1 g2 : Gen} {out : FolOut} (h : FolR P n fol sub mk bc df gen out g1)
    (he : g2.erase = g1.erase) : FolR P n fol sub mk bc df gen out g2 := by
  cases n with
  | zero => exact h.elim
  | succ n =>
    obtain ⟨tab, go, g', ht, hgo, h, he'⟩ := h
    exact ⟨tab, go, g', ht, hgo, h, he'.trans he.symm⟩

/-- The table with no answer. -/
def tabNone : Tab := fun _ _ => none

theorem tabIn_none : TabIn P tabNone := fun _ _ _ h => by cases h

/-- The table with one answer. -/
def tabOne (s : Sock) (f : Noun) (a : TabEntry) : Tab := fun s' f' => if s' = s ∧ f' = f then some a else none

theorem tabIn_one {s : Sock} {f : Noun} {a : TabEntry} (h : P s f a) : TabIn P (tabOne s f a) := by
  intro s' f' a' h'
  unfold tabOne at h'
  split at h'
  · rename_i e; obtain ⟨rfl, rfl⟩ := e; cases h'; exact h
  · cases h'

/-! ## The invariant -/

/-- `Inv` depends only on `low`, `back` and the parts of the state other than
the registrations and the statistics. -/
def LocalStable (Inv : GenS M R → Prop) : Prop :=
  ∀ gs gs' : GenS M R, Inv gs → gs'.low = gs.low → gs'.back = gs.back → gs'.st.g = gs.st.g →
    gs'.st.done = gs.st.done → gs'.st.order = gs.st.order → gs'.st.stk = gs.st.stk →
    gs'.st.next = gs.st.next → gs'.st.moved = gs.st.moved → gs'.st.tick = gs.st.tick →
    gs'.st.ticks = gs.st.ticks → Inv gs'

theorem LocalStable.app {Inv : GenS M R → Prop} (hL : LocalStable Inv) {gs gs' : GenS M R}
    (hi : Inv gs) (h1 : gs'.low = gs.low) (h2 : gs'.back = gs.back) (h3 : gs'.st.g = gs.st.g)
    (h4 : gs'.st.done = gs.st.done) (h5 : gs'.st.order = gs.st.order) (h6 : gs'.st.stk = gs.st.stk)
    (h7 : gs'.st.next = gs.st.next) (h8 : gs'.st.moved = gs.st.moved) (h9 : gs'.st.tick = gs.st.tick)
    (h10 : gs'.st.ticks = gs.st.ticks) : Inv gs' := hL gs gs' hi h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

theorem spotHint_gen (env : Env R) (tag : Nat) (h1 h2 : Noun) (seat : Option Noun) (gen : GenS M R) :
    (spotHint env tag h1 h2 seat gen).2.gen = gen.gen := by
  unfold spotHint
  split
  · split
    · rfl
    · split <;> rfl
  · rfl

theorem spotHint_inv {Inv : GenS M R → Prop} (hL : LocalStable Inv) (env : Env R) (tag : Nat)
    (h1 h2 : Noun) (seat : Option Noun) {gen : GenS M R} (hi : Inv gen) :
    Inv (spotHint env tag h1 h2 seat gen).2 := by
  unfold spotHint
  split
  · split
    · exact hi
    · split
      · exact hL.app hi rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      · exact hi
  · exact hi

theorem fastHint_inv {Inv : GenS M R → Prop} (hL : LocalStable Inv) {env : Env R} {tag : Nat}
    {h f : FolOut} {gen gen' : GenS M R} (hi : Inv gen) (e : fastHint env tag h f gen = some gen') :
    Inv gen' ∧ gen'.gen = gen.gen := by
  unfold fastHint at e
  split at e
  · simp only [Option.map_eq_some_iff] at e
    obtain ⟨r, _, rfl⟩ := e
    split
    · exact ⟨hL.app hi rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, rfl⟩
    · exact ⟨hL.app hi rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, rfl⟩
  · cases e; exact ⟨hi, rfl⟩

/-! ## The projection -/

/-- The capes of `gen` with the ghost `γ`. -/
def GenS.at (g : GenS M R) (γ : Nat) : Gen := { want := g.want, indi := g.indi, seek := g.seek, ghost := γ }

theorem GenS.at_erase (g : GenS M R) (γ : Nat) : (g.at γ).erase = g.gen.erase := rfl

theorem GenS.at_eq {g g' : GenS M R} (h : g.gen = g'.gen) (γ : Nat) : g.at γ = g'.at γ := by
  have h1 : g.want = g'.want := congrArg Gen.want h
  have h2 : g.indi = g'.indi := congrArg Gen.indi h
  have h3 : g.seek = g'.seek := congrArg Gen.seek h
  simp only [GenS.at, h1, h2, h3]

/-! ## The `%2` case and the `%mean` arm -/

/-- What the state-passing `%2` case does, in the three ways it can go: no
call, an inlined call, or a direct call answered by `res`; and what the
fixed-table `%2` case does in each. -/
theorem callStep_cases {res : ResGo M R} {go : FolGoS M R} {seat mk : Option Noun} {bc df : Bool}
    {s f out : FolOut} {g g' : GenS M R} (h : callStep res go seat mk bc df s f g = some (out, g')) :
    (g'.low = g.low ∧ g'.back = g.back ∧ g'.st = g.st ∧ g'.callees = g.callees ∧
      ∀ (tab : Tab) (go' : FolGo) δ, SkaModel.callStep tab go' mk bc df s f (g.at δ) = some (out, g'.at δ)) ∨
    (∃ fa fb i g3, go (C fa fb) s.prod seat mk bc df
        { g with want := Ca.uni g.want (distribute Cape.yes f.prod.src) } = some (i, g3) ∧ g' = g3 ∧
      ∀ (tab : Tab) (go' : FolGo) δ δ', go' (C fa fb) s.prod mk bc df
        (GenS.at ({ g with want := Ca.uni g.want (distribute Cape.yes f.prod.src) } : GenS M R) δ) =
          some (i, g3.at δ') →
        SkaModel.callStep tab go' mk bc df s f (g.at δ) = some (out, g3.at δ')) ∨
    (∃ fa fb r g3, res (s.prod.sock, C fa fb) g = some (r, g3) ∧ s.prod.sock ≠ Sock.void ∧
      g'.low = g3.low ∧ g'.back = g3.back ∧ g'.st = g3.st ∧ g'.callees = Treap.ins g3.callees ⟨seat, r.1⟩ ∧
      (g3.gen = g.gen → ∀ (go' : FolGo) δ,
        SkaModel.callStep (tabOne s.prod.sock (C fa fb) r.2.core.tab) go' mk bc df s f (g.at δ) =
          some (out, g'.at δ))) := by
  unfold callStep at h
  by_cases hv : s.prod.sock = Sock.void ∨ f.prod.sock = Sock.void
  · rw [if_pos hv] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine Or.inl ⟨rfl, rfl, rfl, rfl, fun tab go' δ => ?_⟩
    unfold SkaModel.callStep; rw [if_pos hv]
  rw [if_neg hv] at h
  cases hf : f.prod.sock with
  | void => exact absurd (Or.inr hf) hv
  | mk c d =>
  rw [hf] at h
  cases c with
  | no => exact Or.inl (by
      refine ⟨by simp at h; rw [← h.2], by simp at h; rw [← h.2], by simp at h; rw [← h.2], by simp at h; rw [← h.2], ?_⟩
      intro tab go' δ
      unfold SkaModel.callStep; rw [if_neg hv, hf]
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩)
  | cell _ _ => exact Or.inl (by
      refine ⟨by simp at h; rw [← h.2], by simp at h; rw [← h.2], by simp at h; rw [← h.2], by simp at h; rw [← h.2], ?_⟩
      intro tab go' δ
      unfold SkaModel.callStep; rw [if_neg hv, hf]
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩)
  | yes =>
  cases d with
  | atom _ => exact Or.inl (by
      refine ⟨by simp at h; rw [← h.2], by simp at h; rw [← h.2], by simp at h; rw [← h.2], by simp at h; rw [← h.2], ?_⟩
      intro tab go' δ
      unfold SkaModel.callStep; rw [if_neg hv, hf]
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩)
  | cell fa fb =>
  cases bc with
  | true => exact Or.inl (by
      refine ⟨by simp at h; rw [← h.2], by simp at h; rw [← h.2], by simp at h; rw [← h.2], by simp at h; rw [← h.2], ?_⟩
      intro tab go' δ
      unfold SkaModel.callStep; rw [if_neg hv, hf]
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩)
  | false =>
  simp only at h
  split at h
  · rename_i hc
    simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨i, g3⟩, hi, rfl, rfl⟩ := h
    refine Or.inr (Or.inl ⟨fa, fb, i, g3, hi, rfl, fun tab go' δ δ' e => ?_⟩)
    unfold SkaModel.callStep; rw [if_neg hv, hf]
    simp only
    rw [if_pos hc]
    simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
    exact ⟨(i, g3.at δ'), e, rfl, rfl⟩
  · rename_i hc
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨⟨r, g3⟩, hr, h⟩ := h
    split at h
    · cases h
    · rename_i lc dd hl
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine Or.inr (Or.inr ⟨fa, fb, (r : Ident × FDatum M), g3, hr, fun e => hv (Or.inl e), rfl, rfl, rfl, rfl,
        fun hg go' δ => ?_⟩)
      unfold SkaModel.callStep; rw [if_neg hv, hf]
      simp only
      rw [if_neg hc]
      have ht : tabOne s.prod.sock (C fa fb) r.2.core.tab s.prod.sock (C fa fb) = some r.2.core.tab := by
        simp [tabOne]
      rw [ht]
      simp only [Option.bind_some, FDatum.core, Datum.tab]
      rw [hl]
      have hw : g3.want = g.want := congrArg Gen.want hg
      have hi : g3.indi = g.indi := congrArg Gen.indi hg
      have hs : g3.seek = g.seek := congrArg Gen.seek hg
      simp only [GenS.at, hw, hi, hs]

/-- What the state-passing `%mean` arm does: no call, or the call of the
trap's arm; and what the fixed-table arm does in each. -/
theorem meanArm_cases {go : FolGoS M R} {tag : Nat} {h : FolOut} {seat mk : Option Noun} {bc : Bool}
    {g g' : GenS M R} {arm : Option (Bell × Option Noun)}
    (e : meanArm go tag h seat mk bc g = some (arm, g')) :
    (g' = g ∧ ∀ (go' : FolGo) δ, SkaModel.meanArm go' tag h mk bc (g.at δ) = some (arm, g.at δ)) ∨
    (∃ cg, go (n3 (A 2) (slot 1) (slot 2)) h.prod seat mk bc true g = some cg ∧ g' = cg.2 ∧
      ∀ (go' : FolGo) δ δ', go' (n3 (A 2) (slot 1) (slot 2)) h.prod mk bc true (g.at δ) = some (cg.1, cg.2.at δ') →
        SkaModel.meanArm go' tag h mk bc (g.at δ) = some (arm, cg.2.at δ')) := by
  unfold meanArm at e
  split at e
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact Or.inl ⟨rfl, fun go' δ => by unfold SkaModel.meanArm; rw [if_pos hc]⟩
  · rename_i hc
    simp only [Option.bind_eq_some_iff] at e
    obtain ⟨bat, hb, e⟩ := e
    split at e
    · simp only [Option.bind_eq_some_iff] at e
      obtain ⟨cg, hcg, e⟩ := e
      refine Or.inr ⟨cg, hcg, ?_, fun go' δ δ' e' => ?_⟩
      · split at e
        · simp only [Option.some.injEq, Prod.mk.injEq] at e; exact e.2.symm
        · cases e
      · unfold SkaModel.meanArm; rw [if_neg hc]
        simp only [Option.bind_eq_some_iff]
        refine ⟨_, hb, ?_⟩
        simp only [Option.bind_eq_some_iff]
        refine ⟨_, e', ?_⟩
        split at e
        · rename_i p q b k hn
          simp only [Option.some.injEq, Prod.mk.injEq] at e
          obtain ⟨rfl, rfl⟩ := e
          simp only [hn]
          try rfl
        · cases e
    · simp only [Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      refine Or.inl ⟨rfl, fun go' δ => ?_⟩
      unfold SkaModel.meanArm; rw [if_neg hc]
      simp only [Option.bind_eq_some_iff]
      refine ⟨bat, hb, ?_⟩
      split
      · rename_i hx; exact (hx _ _ rfl).elim
      · rfl

/-! ## One level -/

theorem folR_of_calls {n : Nat} {tab : Tab} {calls : List (Key × (FolOut × Gen))} {fol : Noun}
    {sub : Anno} {mk : Option Noun} {bc df : Bool} {gen g' gen' : Gen} {out : FolOut}
    (ht : TabIn P tab)
    (hc : ∀ c ∈ calls, FolR P n c.1.1 c.1.2.1 c.1.2.2.1 c.1.2.2.2.1 c.1.2.2.2.2.1 c.1.2.2.2.2.2 c.2.1 c.2.2)
    (h : SkaModel.folStep tab (goL calls) fol sub mk bc df gen = some (out, g'))
    (he : g'.erase = gen'.erase) : FolR P (n + 1) fol sub mk bc df gen out gen' :=
  ⟨tab, goL calls, g', ht, goR_goL hc, h, he⟩

section Step

variable {Inv : GenS M R → Prop} {res : ResGo M R} {go : FolGoS M R} {n : Nat}

/-- What the bridge asks of `resolve` on a well-formed subject sock: its
answers are in `P`, it keeps `Inv`, and it leaves the capes of `gen` alone. -/
def ResOK (P : Sock → Noun → TabEntry → Prop) (Inv : GenS M R → Prop) (res : ResGo M R) : Prop :=
  ∀ idT gs r gs', Inv gs → WellFormed idT.1 → res idT gs = some (r, gs') → P idT.1 idT.2 r.2.core.tab ∧ Inv gs' ∧ gs'.gen = gs.gen

/-- What the bridge gives of a recursion on a well-formed subject sock: it
keeps `Inv`, and its results, projected, are in `FolR P n` with any ghost. -/
def GoOK (P : Sock → Noun → TabEntry → Prop) (Inv : GenS M R → Prop) (n : Nat) (go : FolGoS M R) : Prop :=
  ∀ fol sub seat mk bc df gs out gs', Inv gs → WellFormed sub.sock → go fol sub seat mk bc df gs = some (out, gs') →
    Inv gs' ∧ ∀ γ, FolR P n fol sub mk bc df (gs.at γ) out gs'.gen

theorem GoOK.ch (hgo : GoOK P Inv n go) {fol : Noun} {sub : Anno} {seat mk : Option Noun} {bc df : Bool}
    {gs gs' : GenS M R} {out : FolOut} (hi : Inv gs) (hs : WellFormed sub.sock)
    (h : go fol sub seat mk bc df gs = some (out, gs'))
    (γ γ' : Nat) : FolR P n fol sub mk bc df (gs.at γ) out (gs'.at γ') :=
  folR_reghost ((hgo _ _ _ _ _ _ _ _ _ hi hs h).2 γ) rfl

/-- **One level of the state-passing `fol-loop` is in `FolR`.** -/
theorem bridge_step (env : Env R) (hP : ∀ tab, TabIn P tab → TabWF tab) (hL : LocalStable Inv)
    (hres : ResOK P Inv res) (hgo : GoOK P Inv n go)
    {fol : Noun} {sub : Anno} {seat mk : Option Noun} {bc df : Bool} {gs gs' : GenS M R} {out : FolOut}
    (hi : Inv gs) (hsub : WellFormed sub.sock) (h : folStep env res go fol sub seat mk bc df gs = some (out, gs')) :
    Inv gs' ∧ ∀ γ, FolR P (n + 1) fol sub mk bc df (gs.at γ) out gs'.gen := by
  cases hs : shape fol with
  | cons a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨l, g1⟩, h1, ⟨r, g2⟩, h2, rfl, rfl⟩ := h
    have i1 := (hgo _ _ _ _ _ _ _ _ _ hi hsub h1).1
    refine ⟨(hgo _ _ _ _ _ _ _ _ _ i1 hsub h2).1, fun γ => ?_⟩
    refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (l, g1.at (γ + 1))),
        ((q, sub, mk, bc, df, g1.at (γ + 1)), (r, g2.at (γ + 2)))]) (g' := g2.at (γ + 2)) tabIn_none ?_ ?_ rfl
    · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hgo.ch hi hsub h1 _ _, hgo.ch i1 hsub h2 _ _⟩
    · simp only [SkaModel.folStep, hs]
      rw [goL_hd]; simp only [Option.bind_some]
      rw [goL_tl (by simp [GenS.at]), goL_hd]; rfl
  | op0 p =>
    simp only [folStep, hs, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨pr, hpr, rfl, rfl⟩ := h
    refine ⟨hi, fun γ => folR_of_calls (calls := []) (g' := gs.at γ) tabIn_none (by simp) ?_ rfl⟩
    simp only [SkaModel.folStep, hs, hpr, Option.map_some]
  | op1 p =>
    simp only [folStep, hs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hi, fun γ => folR_of_calls (calls := []) (g' := gs.at γ) tabIn_none (by simp)
      (by simp only [SkaModel.folStep, hs]) rfl⟩
  | op2 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff] at h
    obtain ⟨⟨s1, g1⟩, h1, ⟨f1, g2⟩, h2, h3⟩ := h
    dsimp only at h2 h3
    have i1 := (hgo _ _ _ _ _ _ _ _ _ hi hsub h1).1
    have ws1 : WellFormed s1.prod.sock := folR_wf hP n hsub ((hgo _ _ _ _ _ _ _ _ _ hi hsub h1).2 0)
    have i2 := (hgo _ _ _ _ _ _ _ _ _ i1 hsub h2).1
    have i2' : Inv ({ g2 with want := Ca.uni g2.want (distribute Cape.yes f1.prod.src) } : GenS M R) :=
      hL.app i2 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rcases callStep_cases h3 with ⟨el, eb, est, _, hc⟩ | ⟨fa, fb, i, g3, h4, rfl, hc⟩ | ⟨fa, fb, r, g3, h4, _, el, eb, est, _, hc⟩
    · refine ⟨hL.app i2 el eb (by rw [est]) (by rw [est]) (by rw [est]) (by rw [est]) (by rw [est])
        (by rw [est]) (by rw [est]) (by rw [est]), fun γ => ?_⟩
      refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (s1, g1.at (γ + 1))),
          ((q, sub, mk, bc, df, g1.at (γ + 1)), (f1, g2.at (γ + 2)))]) (g' := gs'.at (γ + 2)) tabIn_none ?_ ?_ rfl
      · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨hgo.ch hi hsub h1 _ _, hgo.ch i1 hsub h2 _ _⟩
      · simp only [SkaModel.folStep, hs]
        rw [goL_hd]; simp only [Option.bind_some]
        rw [goL_tl (by simp [GenS.at]), goL_hd]; simp only [Option.bind_some]
        exact hc _ _ _
    · have i3 := (hgo _ _ _ _ _ _ _ _ _ i2' ws1 h4).1
      refine ⟨i3, fun γ => ?_⟩
      refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (s1, g1.at (γ + 1))),
          ((q, sub, mk, bc, df, g1.at (γ + 1)), (f1, g2.at (γ + 2))),
          ((C fa fb, s1.prod, mk, bc, df,
            GenS.at ({ g2 with want := Ca.uni g2.want (distribute Cape.yes f1.prod.src) } : GenS M R) (γ + 2)),
            (i, gs'.at (γ + 3)))]) (g' := gs'.at (γ + 3)) tabIn_none ?_ ?_ rfl
      · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨hgo.ch hi hsub h1 _ _, hgo.ch i1 hsub h2 _ _,
          hgo.ch i2' ws1 h4 _ _⟩
      · simp only [SkaModel.folStep, hs]
        rw [goL_hd]; simp only [Option.bind_some]
        rw [goL_tl (by simp [GenS.at]), goL_hd]; simp only [Option.bind_some]
        refine hc _ _ _ _ ?_
        rw [goL_tl (by simp [GenS.at]), goL_tl (by simp [GenS.at]), goL_hd]
    · obtain ⟨hp, i3, hg3⟩ := hres _ _ _ _ i2 ws1 h4
      refine ⟨hL.app i3 el eb (by rw [est]) (by rw [est]) (by rw [est]) (by rw [est]) (by rw [est])
        (by rw [est]) (by rw [est]) (by rw [est]), fun γ => ?_⟩
      refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (s1, g1.at (γ + 1))),
          ((q, sub, mk, bc, df, g1.at (γ + 1)), (f1, g2.at (γ + 2)))]) (g' := gs'.at (γ + 2))
          (tabIn_one hp) ?_ ?_ rfl
      · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨hgo.ch hi hsub h1 _ _, hgo.ch i1 hsub h2 _ _⟩
      · simp only [SkaModel.folStep, hs]
        rw [goL_hd]; simp only [Option.bind_some]
        rw [goL_tl (by simp [GenS.at]), goL_hd]; simp only [Option.bind_some]
        exact hc hg3 _ _
  | op3 a b =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, rfl, rfl⟩ := h
    refine ⟨(hgo _ _ _ _ _ _ _ _ _ hi hsub h1).1, fun γ => ?_⟩
    refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (p1, g1.at (γ + 1)))])
      (g' := g1.at (γ + 1)) tabIn_none (by simpa using hgo.ch hi hsub h1 _ _) ?_ rfl
    simp only [SkaModel.folStep, hs]
    rw [goL_hd]; rfl
  | op4 a b =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, rfl, rfl⟩ := h
    refine ⟨(hgo _ _ _ _ _ _ _ _ _ hi hsub h1).1, fun γ => ?_⟩
    refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (p1, g1.at (γ + 1)))])
      (g' := g1.at (γ + 1)) tabIn_none (by simpa using hgo.ch hi hsub h1 _ _) ?_ rfl
    simp only [SkaModel.folStep, hs]
    rw [goL_hd]; rfl
  | op5 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, rfl, rfl⟩ := h
    have i1 := (hgo _ _ _ _ _ _ _ _ _ hi hsub h1).1
    refine ⟨(hgo _ _ _ _ _ _ _ _ _ i1 hsub h2).1, fun γ => ?_⟩
    refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (p1, g1.at (γ + 1))),
        ((q, sub, mk, bc, df, g1.at (γ + 1)), (q1, g2.at (γ + 2)))]) (g' := g2.at (γ + 2)) tabIn_none ?_ ?_ rfl
    · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hgo.ch hi hsub h1 _ _, hgo.ch i1 hsub h2 _ _⟩
    · simp only [SkaModel.folStep, hs]
      rw [goL_hd]; simp only [Option.bind_some]
      rw [goL_tl (by simp [GenS.at]), goL_hd]; rfl
  | op6 a b q r =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, ⟨r1, g3⟩, h3, rfl, rfl⟩ := h
    have i1 := (hgo _ _ _ _ _ _ _ _ _ hi hsub h1).1
    have i2 := (hgo _ _ _ _ _ _ _ _ _ i1 hsub h2).1
    refine ⟨(hgo _ _ _ _ _ _ _ _ _ i2 hsub h3).1, fun γ => ?_⟩
    refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (p1, g1.at (γ + 1))),
        ((q, sub, mk, bc, df, g1.at (γ + 1)), (q1, g2.at (γ + 2))),
        ((r, sub, mk, bc, df, g2.at (γ + 2)), (r1, g3.at (γ + 3)))]) (g' := g3.at (γ + 3)) tabIn_none ?_ ?_ rfl
    · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hgo.ch hi hsub h1 _ _, hgo.ch i1 hsub h2 _ _, hgo.ch i2 hsub h3 _ _⟩
    · simp only [SkaModel.folStep, hs]
      rw [goL_hd]; simp only [Option.bind_some]
      rw [goL_tl (by simp [GenS.at]), goL_hd]; simp only [Option.bind_some]
      rw [goL_tl (by simp [GenS.at]), goL_tl (by simp [GenS.at]), goL_hd]; rfl
  | op7 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, rfl, rfl⟩ := h
    have i1 := (hgo _ _ _ _ _ _ _ _ _ hi hsub h1).1
    have wp1 : WellFormed p1.prod.sock := folR_wf hP n hsub ((hgo _ _ _ _ _ _ _ _ _ hi hsub h1).2 0)
    refine ⟨(hgo _ _ _ _ _ _ _ _ _ i1 wp1 h2).1, fun γ => ?_⟩
    refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (p1, g1.at (γ + 1))),
        ((q, p1.prod, mk, bc, df, g1.at (γ + 1)), (q1, g2.at (γ + 2)))]) (g' := g2.at (γ + 2)) tabIn_none ?_ ?_ rfl
    · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hgo.ch hi hsub h1 _ _, hgo.ch i1 wp1 h2 _ _⟩
    · simp only [SkaModel.folStep, hs]
      rw [goL_hd]; simp only [Option.bind_some]
      rw [goL_tl (by simp [GenS.at]), goL_hd]; rfl
  | op8 a b q =>
    simp only [folStep, hs] at h
    refine ⟨(hgo _ _ _ _ _ _ _ _ _ hi hsub h).1, fun γ => ?_⟩
    refine folR_of_calls (calls := [((n3 (A 7) (C (C a b) (slot 1)) q, sub, mk, bc, df, gs.at γ),
        (out, gs'.at (γ + 1)))]) (g' := gs'.at (γ + 1)) tabIn_none (by simpa using hgo.ch hi hsub h _ _) ?_ rfl
    simp only [SkaModel.folStep, hs]
    rw [goL_hd]
  | op9 p a b =>
    simp only [folStep, hs] at h
    refine ⟨(hgo _ _ _ _ _ _ _ _ _ hi hsub h).1, fun γ => ?_⟩
    refine folR_of_calls (calls := [((n3 (A 7) (C a b) (n3 (A 2) (slot 1) (slot p)), sub, mk, bc, df, gs.at γ),
        (out, gs'.at (γ + 1)))]) (g' := gs'.at (γ + 1)) tabIn_none (by simpa using hgo.ch hi hsub h _ _) ?_ rfl
    simp only [SkaModel.folStep, hs]
    rw [goL_hd]
  | op10 ax don r1 r2 =>
    simp only [folStep, hs] at h
    split at h
    · rename_i hx
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨hi, fun γ => folR_of_calls (calls := []) (g' := gs.at γ) tabIn_none (by simp) ?_ rfl⟩
      simp only [SkaModel.folStep, hs, if_pos hx]
    · rename_i hx
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨⟨dn, g1⟩, h1, ⟨rc, g2⟩, h2, s', hd, rfl, rfl⟩ := h
      have i1 := (hgo _ _ _ _ _ _ _ _ _ hi hsub h1).1
      refine ⟨(hgo _ _ _ _ _ _ _ _ _ i1 hsub h2).1, fun γ => ?_⟩
      refine folR_of_calls (calls := [((don, sub, mk, bc, df, gs.at γ), (dn, g1.at (γ + 1))),
          ((C r1 r2, sub, mk, bc, df, g1.at (γ + 1)), (rc, g2.at (γ + 2)))]) (g' := g2.at (γ + 2))
          tabIn_none ?_ ?_ rfl
      · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨hgo.ch hi hsub h1 _ _, hgo.ch i1 hsub h2 _ _⟩
      · simp only [SkaModel.folStep, hs, if_neg hx]
        rw [goL_hd]; simp only [Option.bind_some]
        rw [goL_tl (by simp [GenS.at]), goL_hd]; simp only [Option.bind_some, hd, Option.map_some]
  | op11s p a b =>
    simp only [folStep, hs] at h
    split at h
    · rename_i hp
      refine ⟨(hgo _ _ _ _ _ _ _ _ _ hi hsub h).1, fun γ => ?_⟩
      refine folR_of_calls (calls := [((n3 (A 2) (slot 1) (quote (C (A 11) (C (A p) (C a b)))), sub, mk, true,
          df, gs.at γ), (out, gs'.at (γ + 1)))]) (g' := gs'.at (γ + 1)) tabIn_none
          (by simpa using hgo.ch hi hsub h _ _) ?_ rfl
      simp only [SkaModel.folStep, hs, if_pos hp]
      rw [goL_hd]
    · rename_i hp
      simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨q1, g1⟩, h1, rfl, rfl⟩ := h
      refine ⟨(hgo _ _ _ _ _ _ _ _ _ hi hsub h1).1, fun γ => ?_⟩
      refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (q1, g1.at (γ + 1)))])
        (g' := g1.at (γ + 1)) tabIn_none (by simpa using hgo.ch hi hsub h1 _ _) ?_ rfl
      simp only [SkaModel.folStep, hs, if_neg hp]
      rw [goL_hd]; rfl
  | op11d tag h1 h2 f =>
    simp only [folStep, hs, Option.bind_eq_some_iff] at h
    obtain ⟨⟨hh, g1⟩, e1, h⟩ := h
    have i0 := spotHint_inv hL env tag h1 h2 seat hi
    have hat0 : ∀ γ, (spotHint env tag h1 h2 seat gs).2.at γ = gs.at γ :=
      fun γ => GenS.at_eq (spotHint_gen env tag h1 h2 seat gs) γ
    have i1 := (hgo _ _ _ _ _ _ _ _ _ i0 hsub e1).1
    have whh : WellFormed hh.prod.sock := folR_wf hP n hsub ((hgo _ _ _ _ _ _ _ _ _ i0 hsub e1).2 0)
    have F1 : ∀ γ γ', FolR P n (C h1 h2) sub mk bc df (gs.at γ) hh (g1.at γ') := fun γ γ' => by
      rw [← hat0 γ]; exact hgo.ch i0 hsub e1 _ _
    split at h
    · rename_i hc
      refine ⟨(hgo _ _ _ _ _ _ _ _ _ i1 hsub h).1, fun γ => ?_⟩
      refine folR_of_calls (calls := [((C h1 h2, sub, mk, bc, df, gs.at γ), (hh, g1.at (γ + 1))),
          ((n3 (A 2) (slot 1) (quote f), sub, some hh.prod.sock.data, bc, df, g1.at (γ + 1)),
            (out, gs'.at (γ + 2)))]) (g' := gs'.at (γ + 2)) tabIn_none ?_ ?_ rfl
      · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨F1 _ _, hgo.ch i1 hsub h _ _⟩
      · simp only [SkaModel.folStep, hs]
        rw [goL_hd]; simp only [Option.bind_some]
        rw [if_pos hc, goL_tl (by simp [GenS.at]), goL_hd]
    · rename_i hc
      simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨arm, g2⟩, harm, ⟨fr, g3⟩, h3, g4, h4, rfl, rfl⟩ := h
      have iA : Inv g2 := by
        rcases meanArm_cases harm with ⟨rfl, _⟩ | ⟨cg, hcg, rfl, _⟩
        · exact i1
        · exact (hgo _ _ _ _ _ _ _ _ _ i1 whh hcg).1
      obtain ⟨i4, hg4⟩ := fastHint_inv hL ((hgo _ _ _ _ _ _ _ _ _ iA hsub h3).1) h4
      refine ⟨i4, fun γ => ?_⟩
      rcases meanArm_cases harm with ⟨rfl, hm⟩ | ⟨cg, hcg, rfl, hm⟩
      · refine folR_of_calls (calls := [((C h1 h2, sub, mk, bc, df, gs.at γ), (hh, g2.at (γ + 1))),
            ((f, sub, mk, bc, df, g2.at (γ + 1)), (fr, g3.at (γ + 2)))]) (g' := g3.at (γ + 2)) tabIn_none ?_ ?_
            (by rw [GenS.at_erase, hg4])
        · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
          exact ⟨F1 _ _, hgo.ch i1 hsub h3 _ _⟩
        · simp only [SkaModel.folStep, hs]
          rw [goL_hd]; simp only [Option.bind_some]
          rw [if_neg hc, hm]; simp only [Option.bind_some]
          rw [goL_tl (by simp [GenS.at]), goL_hd]; rfl
      · have icg := (hgo _ _ _ _ _ _ _ _ _ i1 whh hcg).1
        refine folR_of_calls (calls := [((C h1 h2, sub, mk, bc, df, gs.at γ), (hh, g1.at (γ + 1))),
            ((n3 (A 2) (slot 1) (slot 2), hh.prod, mk, bc, true, g1.at (γ + 1)), (cg.1, cg.2.at (γ + 2))),
            ((f, sub, mk, bc, df, cg.2.at (γ + 2)), (fr, g3.at (γ + 3)))]) (g' := g3.at (γ + 3)) tabIn_none ?_ ?_
            (by rw [GenS.at_erase, hg4])
        · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
          exact ⟨F1 _ _, hgo.ch i1 whh hcg _ _, hgo.ch icg hsub h3 _ _⟩
        · simp only [SkaModel.folStep, hs]
          rw [goL_hd]; simp only [Option.bind_some]
          rw [if_neg hc, hm _ _ _ (by rw [goL_tl (by simp [GenS.at]), goL_hd])]
          simp only [Option.bind_some]
          rw [goL_tl (by simp [GenS.at]), goL_tl (by simp [GenS.at]), goL_hd]; rfl
  | op12 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, rfl, rfl⟩ := h
    have i1 := (hgo _ _ _ _ _ _ _ _ _ hi hsub h1).1
    refine ⟨(hgo _ _ _ _ _ _ _ _ _ i1 hsub h2).1, fun γ => ?_⟩
    refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (p1, g1.at (γ + 1))),
        ((q, sub, mk, bc, df, g1.at (γ + 1)), (q1, g2.at (γ + 2)))]) (g' := g2.at (γ + 2)) tabIn_none ?_ ?_ rfl
    · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hgo.ch hi hsub h1 _ _, hgo.ch i1 hsub h2 _ _⟩
    · simp only [SkaModel.folStep, hs]
      rw [goL_hd]; simp only [Option.bind_some]
      rw [goL_tl (by simp [GenS.at]), goL_hd]; rfl
  | other =>
    simp only [folStep, hs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hi, fun γ => folR_of_calls (calls := []) (g' := gs.at γ) tabIn_none (by simp)
      (by simp only [SkaModel.folStep, hs]) rfl⟩

end Step

/-! ## The run -/

theorem folLoop_zero (env : Env R) (memoF : Memo M) : folLoop env memoF 0 = fun _ _ _ _ _ _ _ => none := by
  unfold folLoop; rfl

theorem folLoop_succ (env : Env R) (memoF : Memo M) (n : Nat) :
    folLoop env memoF (n + 1) = folStep env (resolve env memoF n) (folLoop env memoF n) := by
  conv => lhs; unfold folLoop

theorem resolve_succ (env : Env R) (memoF : Memo M) (n : Nat) :
    resolve env memoF (n + 1) = resolveStep env (resolve env memoF n) (analyze env memoF n) := by
  conv => lhs; unfold resolve

theorem analyze_succ (env : Env R) (memoF : Memo M) (n : Nat) :
    analyze env memoF (n + 1) = analyzeStep n memoF (run env memoF n) (passLoop env memoF n) := by
  conv => lhs; unfold analyze

theorem run_succ (env : Env R) (memoF : Memo M) (n : Nat) :
    run env memoF (n + 1) = runStep (folLoop env memoF n) := by
  conv => lhs; unfold run

theorem passLoop_succ (env : Env R) (memoF : Memo M) (n : Nat) :
    passLoop env memoF (n + 1) = passStep n (memberLoop env memoF n) (passLoop env memoF n) := by
  conv => lhs; unfold passLoop

theorem memberLoop_succ (env : Env R) (memoF : Memo M) (n : Nat) :
    memberLoop env memoF (n + 1) = memberStep (run env memoF n) (memberLoop env memoF n) := by
  conv => lhs; unfold memberLoop

/-- **The state-passing `fol-loop` is in `FolR P`**, for an invariant `Inv`
that `resolve` keeps with answers in `P` at every fuel below `n`. -/
theorem folLoop_goOK {Inv : GenS M R → Prop} (env : Env R) (memoF : Memo M)
    (hP : ∀ tab, TabIn P tab → TabWF tab) (hL : LocalStable Inv) :
    ∀ n, (∀ k, k < n → ResOK P Inv (resolve env memoF k)) → GoOK P Inv n (folLoop env memoF n)
  | 0 => fun _ _ _ _ _ _ _ _ _ _ _ _ h => by rw [folLoop_zero] at h; cases h
  | n + 1 => fun hres _ _ _ _ _ _ _ _ _ hi hs h => by
    rw [folLoop_succ] at h
    exact bridge_step env hP hL (hres n (Nat.lt_succ_self n))
      (folLoop_goOK env memoF hP hL n (fun k hk => hres k (Nat.lt_succ_of_lt hk))) hi hs h

theorem genInit_at (index : Nat) (st : SkaState M R) : (genInit index st).at 0 = Gen.init := rfl

/-- **The run of `+run` on `id` is a run with answers in `P`.** -/
theorem run_folTopR {Inv : GenS M R → Prop} (env : Env R) (memoF : Memo M)
    (hP : ∀ tab, TabIn P tab → TabWF tab) (hL : LocalStable Inv) {n index : Nat}
    (hres : ∀ k, k < n → ResOK P Inv (resolve env memoF k)) {id : Ident} {st : SkaState M R}
    {out : FolOut} {gs' : GenS M R} (hi : Inv (genInit index st)) (hw : WellFormed id.1)
    (h : folLoop env memoF n id.2 ⟨id.1, A 1⟩ none none false false (genInit index st) = some (out, gs')) :
    Inv gs' ∧ FolTopR P n id.1 id.2 out gs'.gen := by
  obtain ⟨i', F⟩ := folLoop_goOK env memoF hP hL n hres _ _ _ _ _ _ _ _ _ hi hw h
  exact ⟨i', F 0⟩

/-! ## The write of `+run` -/

theorem gCore_put (g : Callgraph M) (i : Ident) (d : FDatum M) :
    gCore (Treap.put g i d) = Graph.put (gCore g) i d.core := by
  funext j
  simp only [gCore, Graph.put, Treap.get_put]
  split <;> rfl

/-- **The write of `+run` is a `GStepR.run`**: the graph after `+run` is the
graph after its `fol-loop` with the identity set to `runDatum` of the run,
from the datum the identity had when the run began (`hold`: the identity's
entry is the same at the end of its own `fol-loop`, which the analysis keeps
and is not proved here). -/
theorem runEnd_gStepR {P : Sock → Noun → TabEntry → Prop} (hP : ∀ tab, TabIn P tab → TabWF tab)
    {n : Nat} {id : Ident} {data : FDatum M} {out : FolOut} {gs : GenS M R}
    (hF : FolTopR P n id.1 id.2 out gs.gen) (hold : gCore gs.st.g id = some data.core) :
    GStepR (gCore gs.st.g) (gCore (runEnd id data out gs).2.g) := by
  have e : gCore (runEnd id data out gs).2.g =
      Graph.put (gCore gs.st.g) id (runDatum (Treap.has gs.st.moved id) id.1 out gs.gen data.core).1 := by
    unfold runEnd
    simp only
    rw [gCore_put]
    split <;> rfl
  rw [e]
  exact GStepR.run hP hF hold

end Ana
end SkaModel
end Formalization
