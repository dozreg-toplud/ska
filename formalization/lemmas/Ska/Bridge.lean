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
    (g'.low = g.low ∧ g'.back = g.back ∧ g'.st = g.st ∧
      ∀ (tab : Tab) (go' : FolGo) δ, SkaModel.callStep tab go' mk bc df s f (g.at δ) = some (out, g'.at δ)) ∨
    (∃ fa fb i g3, go (C fa fb) s.prod seat mk bc df
        { g with want := Ca.uni g.want (distribute Cape.yes f.prod.src) } = some (i, g3) ∧ g' = g3 ∧
      ∀ (tab : Tab) (go' : FolGo) δ δ', go' (C fa fb) s.prod mk bc df
        (GenS.at ({ g with want := Ca.uni g.want (distribute Cape.yes f.prod.src) } : GenS M R) δ) =
          some (i, g3.at δ') →
        SkaModel.callStep tab go' mk bc df s f (g.at δ) = some (out, g3.at δ')) ∨
    (∃ fa fb r g3, res (s.prod.sock, C fa fb) g = some (r, g3) ∧
      g'.low = g3.low ∧ g'.back = g3.back ∧ g'.st = g3.st ∧
      (g3.gen = g.gen → ∀ (go' : FolGo) δ,
        SkaModel.callStep (tabOne s.prod.sock (C fa fb) r.2.core.tab) go' mk bc df s f (g.at δ) =
          some (out, g'.at δ))) := by
  unfold callStep at h
  by_cases hv : s.prod.sock = Sock.void ∨ f.prod.sock = Sock.void
  · rw [if_pos hv] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine Or.inl ⟨rfl, rfl, rfl, fun tab go' δ => ?_⟩
    unfold SkaModel.callStep; rw [if_pos hv]
  rw [if_neg hv] at h
  cases hf : f.prod.sock with
  | void => exact absurd (Or.inr hf) hv
  | mk c d =>
  rw [hf] at h
  cases c with
  | no => exact Or.inl (by
      refine ⟨by simp at h; rw [← h.2], by simp at h; rw [← h.2], by simp at h; rw [← h.2], ?_⟩
      intro tab go' δ
      unfold SkaModel.callStep; rw [if_neg hv, hf]
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩)
  | cell _ _ => exact Or.inl (by
      refine ⟨by simp at h; rw [← h.2], by simp at h; rw [← h.2], by simp at h; rw [← h.2], ?_⟩
      intro tab go' δ
      unfold SkaModel.callStep; rw [if_neg hv, hf]
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩)
  | yes =>
  cases d with
  | atom _ => exact Or.inl (by
      refine ⟨by simp at h; rw [← h.2], by simp at h; rw [← h.2], by simp at h; rw [← h.2], ?_⟩
      intro tab go' δ
      unfold SkaModel.callStep; rw [if_neg hv, hf]
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩)
  | cell fa fb =>
  cases bc with
  | true => exact Or.inl (by
      refine ⟨by simp at h; rw [← h.2], by simp at h; rw [← h.2], by simp at h; rw [← h.2], ?_⟩
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
      refine Or.inr (Or.inr ⟨fa, fb, (r : Ident × FDatum M), g3, hr, rfl, rfl, rfl, fun hg go' δ => ?_⟩)
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

end Ana
end SkaModel
end Formalization
