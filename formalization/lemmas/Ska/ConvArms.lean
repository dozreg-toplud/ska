import lemmas.Ska.ConvInv

/-!
# The convergence invariant, arm by arm

Each arm of `Analysis.lean` keeps `CInv` (with frozen entries that only
grow), changes nothing it must not (`Keep`, `Frame`), and returns what its
caller needs to know of the members it leaves on the stack: they have run and
read nothing below the `low` it returns (`Pushed`, `LowB`).  A run (`RunP2`)
moreover leaves its own identity `MemOK`: its answers, judged at the end of
its `fol-loop` (`BridgeD.lean`, with the family `PfR`), come from finalized
entries and from its callees on the stack as they are when the run ends.
-/

namespace Formalization
namespace SkaModel

open Nock

namespace Ana

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-! ## What a run reads -/

/-- An entry a run may have read: an entry of the graph (well formed), that
is finalized or among the callees `cs` of the run. -/
def RB (st : SkaState M R) (cs : M CalleeEntry Unit) : Entry → Prop := fun e =>
  (∃ d, Treap.get st.g (e.more, e.fol) = some d ∧ d.core.tab = e.d.tab) ∧
    WellFormed e.more ∧ WellFormed e.d.prod ∧
    (Treap.get st.order (e.more, e.fol) = none ∨ InCallees cs (e.more, e.fol))

/-- `RB` for one answer of `resolve`: finalized or the identity `c` of the
answer. -/
def RBat (st : SkaState M R) (c : Ident) : Entry → Prop := fun e =>
  (∃ d, Treap.get st.g (e.more, e.fol) = some d ∧ d.core.tab = e.d.tab) ∧
    WellFormed e.more ∧ WellFormed e.d.prod ∧
    (Treap.get st.order (e.more, e.fol) = none ∨ (e.more, e.fol) = c)

/-- The answers of a run, judged at a `gen`. -/
def PfR : PFam M R := fun gs => AnsW (RB gs.st gs.callees)

theorem pfR_wf (g : GenS M R) (tab : Tab) (h : TabIn (PfR g) tab) : TabWF tab :=
  fun s f a hs ht => AnsW.wf (fun e he => ⟨he.2.1, he.2.2.1⟩) (h s f a ht) hs

theorem pfR_stable : PStable (PfR : PFam M R) := by
  intro gs gs' hlf hc s f a h
  refine h.mono (fun e he => ?_)
  obtain ⟨⟨d, hd, ht⟩, w1, w2, ho⟩ := he
  obtain ⟨_, _, hg, _, hord, _⟩ := hlf
  refine ⟨⟨d, by rw [hg]; exact hd, ht⟩, w1, w2, ?_⟩
  rcases ho with ho | ⟨seat, hs⟩
  · exact Or.inl (by rw [hord]; exact ho)
  · exact Or.inr ⟨seat, hc _ hs⟩

/-! ## Frames -/

/-- What an arm leaves alone besides `Keep`: finalized entries, the ticks of
`bt`; and what only grows: `next`, `tick`; the members it pushes have DFS
numbers from the `next` it began with. -/
structure Frame (bt : Ident → Prop) (st st' : SkaState M R) : Prop where
  fin : ∀ i d, Treap.get st.g i = some d → Treap.get st.order i = none →
    Treap.get st'.g i = some d ∧ Treap.get st'.order i = none
  ticks : ∀ j, bt j → Treap.get st'.ticks j = Treap.get st.ticks j
  next : st.next ≤ st'.next
  tick : st.tick ≤ st'.tick
  newOrd : ∀ x o, Treap.get st'.order x = some o → x ∉ st.stk → st.next ≤ o

theorem Frame.refl' {bt : Ident → Prop} {st st' : SkaState M R} (hg : st'.g = st.g) (ho : st'.order = st.order)
    (hs : st'.stk = st.stk) (hn : st'.next = st.next) (htk : st'.tick = st.tick) (hts : st'.ticks = st.ticks)
    (hi : SInv st) : Frame bt st st' where
  fin := fun i d h1 h2 => ⟨by rw [hg]; exact h1, by rw [ho]; exact h2⟩
  ticks := fun j _ => by rw [hts]
  next := by omega
  tick := by omega
  newOrd := fun x o h hx => by
    rw [ho] at h
    exact absurd ((hi.ord_stk x).mp ⟨o, h⟩) hx

theorem Frame.trans {bt bt' : Ident → Prop} {st1 st2 st3 : SkaState M R} (h1 : Frame bt st1 st2)
    (h2 : Frame bt' st2 st3) (hb : ∀ j, bt j → bt' j)
    (hk : ∀ j ∈ st2.stk, Treap.get st3.order j = Treap.get st2.order j) (hi2 : SInv st2) : Frame bt st1 st3 where
  fin := fun i d a b => by
    obtain ⟨a', b'⟩ := h1.fin i d a b
    exact h2.fin i d a' b'
  ticks := fun j hj => (h2.ticks j (hb j hj)).trans (h1.ticks j hj)
  next := Nat.le_trans h1.next h2.next
  tick := Nat.le_trans h1.tick h2.tick
  newOrd := fun x o h hx => by
    by_cases hx2 : x ∈ st2.stk
    · rw [hk x hx2] at h; exact h1.newOrd x o h hx
    · exact Nat.le_trans h1.next (h2.newOrd x o h hx2)

/-- The members of `x`'s callees on the stack are at or above `low`. -/
def LowB (st : SkaState M R) (x : Ident) (low : Nat) : Prop :=
  ∀ c, InCallees (calleesOf st x) c → ∀ o, Treap.get st.order c = some o → low ≤ o

/-- The members not on the stack of `st0` have run and read nothing below
`low`. -/
def Pushed (st0 st : SkaState M R) (low : Nat) : Prop :=
  ∀ x o, Treap.get st.order x = some o → x ∉ st0.stk → 1 ≤ ranOf st x ∧ LowB st x low

/-! ## Congruences -/

theorem memOK_congr {st st' : SkaState M R} {F : Entry → Prop} {m : Ident} {Lmax : Nat}
    (hg : st'.g = st.g) (ho : st'.order = st.order) (hts : st'.ticks = st.ticks) (h : MemOK st F m Lmax) :
    MemOK st' F m Lmax := by
  intro d hd hr
  have hran : ranOf st' m = ranOf st m := by simp only [ranOf, hts]
  rw [hg] at hd; rw [hran] at hr
  obtain ⟨P, L, hL, hrun, hP⟩ := h d hd hr
  refine ⟨P, L, hL, hrun, fun s f a hp => (hP s f a hp).mono (fun e he => ?_)⟩
  rcases he with he | ⟨hce, ⟨o, hco, hlt⟩, htab⟩
  · exact Or.inl he
  · refine Or.inr ⟨by simpa only [calleesOf, gitG, hg] using hce, ⟨o, by rw [ho]; exact hco, hlt⟩, fun hlt' => ?_⟩
    have : chgOf st' (e.more, e.fol) = chgOf st (e.more, e.fol) := by simp only [chgOf, hts]
    rw [this, hran] at hlt'
    obtain ⟨dc, hdc, htc⟩ := htab hlt'
    exact ⟨dc, by rw [hg]; exact hdc, htc⟩

theorem CInv.congr {memoF : Memo M} {st st' : SkaState M R} {F : Entry → Prop} (h : CInv memoF st F)
    (hg : st'.g = st.g) (hd : st'.done = st.done) (ho : st'.order = st.order) (hs : st'.stk = st.stk)
    (hn : st'.next = st.next) (htk : st'.tick = st.tick) (hts : st'.ticks = st.ticks) : CInv memoF st' F := by
  obtain ⟨a, b, c, d, e⟩ := h
  refine ⟨a.congr hg hd ho hs, ?_, ?_, ?_, ?_⟩
  · intro m; simp only [ranOf, chgOf, hts, htk]; exact b m
  · simp only [OrdInv, ho, hs, hn]; exact c
  · obtain ⟨d1, d2, d3, d4, d5⟩ := d
    exact ⟨d1, by simp only [hg, ho]; exact d2, by simp only [hg, ho]; exact d3, d4, by simp only [hd]; exact d5⟩
  · intro m o hmo
    rw [hn]
    exact memOK_congr hg ho hts (e m o (by rw [← ho]; exact hmo))

theorem Pushed.congr {st0 st st' : SkaState M R} {low : Nat} (h : Pushed st0 st low) (hg : st'.g = st.g)
    (ho : st'.order = st.order) (hts : st'.ticks = st.ticks) : Pushed st0 st' low := by
  simp only [Pushed, LowB, calleesOf, ranOf, gitG, hg, ho, hts]; exact h

/-! ## Members keep their answers across an arm -/

/-- **A member on the stack at the start of an arm stays `MemOK`**, with the
same bound, when the arm keeps its entry, the entries and DFS numbers of the
stack, and the ticks of the stack, and the frozen entries only grow. -/
theorem memOK_frame {st st' : SkaState M R} {F F' : Entry → Prop} {m : Ident} {Lmax : Nat}
    (hi : SInv st) (hm : m ∈ st.stk) (hk : Keep st.stk (· ∈ st.stk) st st')
    (hts : ∀ j ∈ st.stk, Treap.get st'.ticks j = Treap.get st.ticks j)
    (hF : ∀ e, F e → F' e) (h : MemOK st F m Lmax) : MemOK st' F' m Lmax := by
  intro d hd hr
  have hgm : Treap.get st'.g m = Treap.get st.g m := hk.2.2 m hm
  have hran : ∀ j ∈ st.stk, ranOf st' j = ranOf st j := fun j hj => by
    simp only [ranOf, Treap.gut, hts j hj]
  have hchg : ∀ j ∈ st.stk, chgOf st' j = chgOf st j := fun j hj => by
    simp only [chgOf, Treap.gut, hts j hj]
  rw [hgm] at hd
  rw [hran m hm] at hr
  obtain ⟨P, L, hL, hrun, hP⟩ := h d hd hr
  refine ⟨P, L, hL, hrun, fun s f a hp => (hP s f a hp).mono (fun e he => ?_)⟩
  rcases he with he | ⟨hce, ⟨o, hco, hlt⟩, htab⟩
  · exact Or.inl (hF e he)
  · have hcs : (e.more, e.fol) ∈ st.stk := (hi.ord_stk _).mp ⟨o, hco⟩
    have hcal : calleesOf st' m = calleesOf st m := by simp only [calleesOf, gitG, Treap.gut, hgm]
    refine Or.inr ⟨by rw [hcal]; exact hce, ⟨o, by rw [hk.2.1 _ hcs]; exact hco, hlt⟩, fun hlt' => ?_⟩
    rw [hchg _ hcs, hran m hm] at hlt'
    obtain ⟨dc, hdc, htc⟩ := htab hlt'
    exact ⟨dc, by rw [hk.2.2 _ hcs]; exact hdc, htc⟩

end Ana
end SkaModel
end Formalization
