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

theorem Frame.congr2 {bt : Ident → Prop} {st st1 st2 : SkaState M R} (h : Frame bt st st1)
    (hg : st2.g = st1.g) (ho : st2.order = st1.order) (hn : st2.next = st1.next) (htk : st2.tick = st1.tick)
    (hts : st2.ticks = st1.ticks) : Frame bt st st2 where
  fin := fun i d a b => by rw [hg, ho]; exact h.fin i d a b
  ticks := fun j hj => by rw [hts]; exact h.ticks j hj
  next := by rw [hn]; exact h.next
  tick := by rw [htk]; exact h.tick
  newOrd := fun x o hx hn' => h.newOrd x o (by rw [← ho]; exact hx) hn'

theorem Keep.congr2 {bo : List Ident} {bg : Ident → Prop} {st st1 st2 : SkaState M R} (h : Keep bo bg st st1)
    (hg : st2.g = st1.g) (ho : st2.order = st1.order) (hs : st2.stk = st1.stk) : Keep bo bg st st2 := by
  obtain ⟨a, b, c⟩ := h
  exact ⟨by rw [hs]; exact a, fun j hj => by rw [ho]; exact b j hj, fun j hj => by rw [hg]; exact c j hj⟩

/-! ## What the arms keep and give -/

/-- What `resolve` keeps and gives: the invariant, the frame, the capes and
callees of `gen`; the members it leaves have run and read nothing below its
`low`; the identity of the answer is at or above `low` if it is a member,
and was not on the stack if `back` stays clear; the answer comes from
finalized entries and from the identity of the answer. -/
def ResP2 (memoF : Memo M) (res : ResGo M R) : Prop :=
  ∀ idT gs r gs' (F : Entry → Prop), CInv memoF gs.st F → WellFormed idT.1 → res idT gs = some (r, gs') →
    (∃ F', (∀ e, F e → F' e) ∧ CInv memoF gs'.st F') ∧
    GStepsR (gCore gs.st.g) (gCore gs'.st.g) ∧ Keep gs.st.stk (· ∈ gs.st.stk) gs.st gs'.st ∧
    Frame (· ∈ gs.st.stk) gs.st gs'.st ∧ gs'.gen = gs.gen ∧ gs'.callees = gs.callees ∧
    gs'.low ≤ gs.low ∧ Pushed gs.st gs'.st gs'.low ∧
    (∀ o, Treap.get gs'.st.order r.1 = some o → gs'.low ≤ o) ∧
    (gs'.back = false → gs.back = false ∧ ∀ o, Treap.get gs'.st.order r.1 = some o → r.1 ∉ gs.st.stk) ∧
    AnsW (RBat gs'.st r.1) idT.1 idT.2 r.2.core.tab

/-- What `+analyze` keeps and gives. -/
def AnaP2 (memoF : Memo M) (ana : AnaGo M R) : Prop :=
  ∀ id st low st' (F : Entry → Prop), CInv memoF st F → WellFormed id.1 → Treap.get st.g id = none →
    ana id st = some (low, st') →
    (∃ F', (∀ e, F e → F' e) ∧ CInv memoF st' F') ∧
    GStepsR (gCore st.g) (gCore st'.g) ∧ Keep st.stk (· ∈ st.stk) st st' ∧ Frame (· ∈ st.stk) st st' ∧
    low ≤ st.next ∧ Pushed st st' low ∧ (∃ d, Treap.get st'.g id = some d) ∧
    (∀ o, Treap.get st'.order id = some o → low ≤ o)

/-- What `+run` keeps and gives: the members other than `id` keep their
answers; `id` is `MemOK` (in `CInv`), its run tick is the clock, its change
tick moves to the clock exactly when the run changed its entry; `low` is at
most its DFS number, and its callees and the members the run leaves read
nothing below `low`; if `back` is clear, its callees on the stack were not
on it when the run began. -/
def RunP2 (memoF : Memo M) (run : RunGo M R) : Prop :=
  ∀ id index st r st' (F : Entry → Prop), CInv memoF st F → id ∈ st.stk → Treap.get st.order id = some index →
    run id index st = some (r, st') →
    (∃ F', (∀ e, F e → F' e) ∧ CInv memoF st' F' ∧
      ∀ m Lmax, m ∈ st.stk → m ≠ id → MemOK st F m Lmax → MemOK st' F' m Lmax) ∧
    GStepsR (gCore st.g) (gCore st'.g) ∧ Keep st.stk (fun j => j ∈ st.stk ∧ j ≠ id) st st' ∧
    Frame (fun j => j ∈ st.stk ∧ j ≠ id) st st' ∧
    ranOf st' id = st'.tick ∧ st.tick < st'.tick ∧
    (r.2.2 = false → chgOf st' id = chgOf st id ∧ (gitG st'.g id).core.tab = (gitG st.g id).core.tab) ∧
    (r.2.2 = true → chgOf st' id = st'.tick) ∧
    r.1 ≤ index ∧ LowB st' id r.1 ∧ Pushed st st' r.1 ∧
    (r.2.1 = false → ∀ c, InCallees (calleesOf st' id) c → ∀ o, Treap.get st'.order c = some o → c ∉ st.stk)

/-! ## `+run` -/

/-- The invariant of a run of `fol-loop` on the member with DFS number
`index`, begun in `st0` with the frozen entries `F0`. -/
def RunInv (memoF : Memo M) (st0 : SkaState M R) (F0 : Entry → Prop) (index : Nat) (gs : GenS M R) : Prop :=
  ∃ F, (∀ e, F0 e → F e) ∧ CInv memoF gs.st F ∧
    GStepsR (gCore st0.g) (gCore gs.st.g) ∧ Keep st0.stk (· ∈ st0.stk) st0 gs.st ∧
    Frame (· ∈ st0.stk) st0 gs.st ∧ gs.low ≤ index ∧ Pushed st0 gs.st gs.low ∧
    (∀ c, InCallees gs.callees c → ∀ o, Treap.get gs.st.order c = some o → gs.low ≤ o) ∧
    (gs.back = false → ∀ c, InCallees gs.callees c → ∀ o, Treap.get gs.st.order c = some o → c ∉ st0.stk)

theorem runInv_stable (memoF : Memo M) (st0 : SkaState M R) (F0 : Entry → Prop) (index : Nat) :
    LocalStableC (RunInv memoF st0 F0 index) := by
  intro gs gs' h hlf hc
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := hlf
  obtain ⟨F, hF, a, b, c, d, e, f, g, i⟩ := h
  refine ⟨F, hF, a.congr e3 e4 e5 e6 e7 e9 e10, by rw [e3]; exact b, c.congr2 e3 e5 e6,
    d.congr2 e3 e5 e7 e9 e10, by rw [e1]; exact e, by rw [e1]; exact f.congr e3 e5 e10,
    fun c' hc' o ho => ?_, fun hb c' hc' o ho => ?_⟩
  · rw [hc] at hc'; rw [e5] at ho; rw [e1]; exact g c' hc' o ho
  · rw [hc] at hc'; rw [e5] at ho; rw [e2] at hb; exact i hb c' hc' o ho

theorem runEnd_eff (id : Ident) (data : FDatum M) (out : FolOut) (gs : GenS M R) :
    (runEnd id data out gs).1 =
      (gs.low, gs.back, (runDatum (Treap.has gs.st.moved id) id.1 out gs.gen data.core).2.2) ∧
    (runEnd id data out gs).2.g = Treap.put gs.st.g id
      ⟨gs.callees, (runDatum (Treap.has gs.st.moved id) id.1 out gs.gen data.core).1.nomm,
        (runDatum (Treap.has gs.st.moved id) id.1 out gs.gen data.core).1.less,
        (runDatum (Treap.has gs.st.moved id) id.1 out gs.gen data.core).1.indi,
        (runDatum (Treap.has gs.st.moved id) id.1 out gs.gen data.core).1.seek,
        (runDatum (Treap.has gs.st.moved id) id.1 out gs.gen data.core).1.prod,
        (runDatum (Treap.has gs.st.moved id) id.1 out gs.gen data.core).1.map, gs.area⟩ ∧
    (runEnd id data out gs).2.order = gs.st.order ∧ (runEnd id data out gs).2.stk = gs.st.stk ∧
    (runEnd id data out gs).2.done = gs.st.done ∧ (runEnd id data out gs).2.next = gs.st.next ∧
    (runEnd id data out gs).2.tick = gs.st.tick + 1 ∧
    (runEnd id data out gs).2.ticks = Treap.put gs.st.ticks id (gs.st.tick + 1,
      if (runDatum (Treap.has gs.st.moved id) id.1 out gs.gen data.core).2.2 then gs.st.tick + 1
      else chgOf gs.st id) := by
  unfold runEnd
  dsimp only
  split <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial

theorem runDatum_unchanged {moved : Bool} {bus : Sock} {out : FolOut} {gen' : Gen} {old : Datum}
    (h : (runDatum moved bus out gen' old).2.2 = false) : (runDatum moved bus out gen' old).1.tab = old.tab := by
  have key : ∀ (d o : Datum), decide ((d.less, d.prod, d.map, d.indi, d.seek) ≠
      (o.less, o.prod, o.map, o.indi, o.seek)) = false → d.tab = o.tab := by
    intro d o h
    simp only [decide_eq_false_iff_not, ne_eq, Decidable.not_not, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    simp only [Datum.tab, h1, h2, h3, h4, h5]
  exact key (runDatum moved bus out gen' old).1 old h

theorem runDatum_runEntryR {P : Sock → Noun → TabEntry → Prop} {n : Nat} {bus : Sock} {fol : Noun}
    {out : FolOut} {gen' : Gen} (h : FolTopR P n bus fol out gen') (moved : Bool) (old : Datum) :
    RunEntryR P ⟨bus, fol, (runDatum moved bus out gen' old).1⟩ :=
  ⟨n, out, gen', moved, ⟨old.prod, old.map⟩, h, rfl, rfl, rfl⟩

end Ana
end SkaModel
end Formalization
