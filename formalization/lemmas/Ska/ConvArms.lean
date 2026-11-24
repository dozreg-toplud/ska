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

Proved here: `runStep_ok2` (from `ResP2`), `resolveStep_ok2` (from `ResP2`
and `AnaP2`).  `+cull`, `+sweep`, the member loop and the pass loop are in
`ConvPass.lean`; `+analyze`, the induction on the fuel and the final graph
in `ConvAna.lean` (`skaCallgraph_frozen`, `skaCallgraph_convergedM`).
-/

namespace Formalization
namespace SkaModel

open Nock

namespace Ana

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-! ## What a run reads -/

/-- An entry a run may have read: an entry of the graph (well formed) among
the callees `cs` of the run. -/
def RB (st : SkaState M R) (cs : M CalleeEntry Unit) : Entry → Prop := fun e =>
  (∃ d, Treap.get st.g (e.more, e.fol) = some d ∧ d.core.tab = e.d.tab) ∧
    WellFormed e.more ∧ WellFormed e.d.prod ∧ NormSock e.d.prod ∧ InCallees cs (e.more, e.fol)

/-- `RB` for one answer of `resolve`: the entry of the identity `c` of the
answer, which the call puts among the callees. -/
def RBat (st : SkaState M R) (c : Ident) : Entry → Prop := fun e =>
  (∃ d, Treap.get st.g (e.more, e.fol) = some d ∧ d.core.tab = e.d.tab) ∧
    WellFormed e.more ∧ WellFormed e.d.prod ∧ NormSock e.d.prod ∧ (e.more, e.fol) = c

/-- The answers of a run, judged at a `gen`. -/
def PfR : PFam M R := fun gs => AnsW (RB gs.st gs.callees)

theorem pfR_wf (g : GenS M R) (tab : Tab) (h : TabIn (PfR g) tab) : TabWF tab ∧ TabNorm tab :=
  ⟨fun s f a hs ht => AnsW.wf (fun e he => ⟨he.2.1, he.2.2.1⟩) (h s f a ht) hs,
   fun s f a hs ht => AnsW.norm (fun e he => he.2.2.2.1) (h s f a ht) hs⟩

theorem pfR_stable : PStable (PfR : PFam M R) := by
  intro gs gs' hlf hc s f a h
  refine h.mono (fun e he => ?_)
  obtain ⟨⟨d, hd, ht⟩, w1, w2, nn, ho⟩ := he
  obtain ⟨_, _, hg, _, _, _⟩ := hlf
  obtain ⟨seat, hs⟩ := ho
  exact ⟨⟨d, by rw [hg]; exact hd, ht⟩, w1, w2, nn, ⟨seat, hc _ hs⟩⟩

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
  newOrd : ∀ x o, Treap.get st'.order x = some o → Treap.get st.order x ≠ some o → st.next ≤ o

theorem Frame.refl' {bt : Ident → Prop} {st st' : SkaState M R} (hg : st'.g = st.g) (ho : st'.order = st.order)
    (hs : st'.stk = st.stk) (hn : st'.next = st.next) (htk : st'.tick = st.tick) (hts : st'.ticks = st.ticks)
    (hi : SInv st) : Frame bt st st' where
  fin := fun i d h1 h2 => ⟨by rw [hg]; exact h1, by rw [ho]; exact h2⟩
  ticks := fun j _ => by rw [hts]
  next := by omega
  tick := by omega
  newOrd := fun x o h hx => by
    rw [ho] at h
    exact absurd h hx

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
    by_cases h2o : Treap.get st2.order x = some o
    · exact h1.newOrd x o h2o hx
    · exact Nat.le_trans h1.next (h2.newOrd x o h h2o)

/-- **An entry stays an entry** across an arm that keeps the entries of the
stack and the finalized entries. -/
theorem inG_frame {st st' : SkaState M R} {bt : Ident → Prop} (hi : SInv st)
    (hk : Keep st.stk (· ∈ st.stk) st st') (hf : Frame bt st st') {c : Ident}
    (h : Treap.get st.g c ≠ none) : Treap.get st'.g c ≠ none := by
  cases ho : Treap.get st.order c with
  | some o =>
    have hcs : c ∈ st.stk := (hi.ord_stk c).mp ⟨o, ho⟩
    rw [hk.2.2 c hcs]; exact h
  | none =>
    obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp h
    rw [(hf.fin c d hd ho).1]; simp

/-- Every answer rests on an entry of its family. -/
theorem AnsW.exists_entry {G : Entry → Prop} {s : Sock} {f : Noun} {a : TabEntry} (h : AnsW G s f a) :
    ∃ e, G e := by
  induction h with
  | exact he => exact ⟨_, he⟩
  | hit he _ => exact ⟨_, he⟩
  | hitGen he _ _ => exact ⟨_, he⟩
  | gen _ _ _ _ ih => exact ih

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
  rcases he with ⟨he, hce⟩ | ⟨hce, ⟨o, hco, hlt⟩, htab⟩
  · exact Or.inl ⟨he, by simpa only [calleesOf, gitG, hg] using hce⟩
  · refine Or.inr ⟨by simpa only [calleesOf, gitG, hg] using hce, ⟨o, by rw [ho]; exact hco, hlt⟩, fun hlt' => ?_⟩
    have : chgOf st' (e.more, e.fol) = chgOf st (e.more, e.fol) := by simp only [chgOf, hts]
    rw [this, hran] at hlt'
    obtain ⟨dc, hdc, htc⟩ := htab hlt'
    exact ⟨dc, by rw [hg]; exact hdc, htc⟩

theorem CInv.congr {memoF : Memo M} {st st' : SkaState M R} {F : Entry → Prop} (h : CInv memoF st F)
    (hg : st'.g = st.g) (hd : st'.done = st.done) (ho : st'.order = st.order) (hs : st'.stk = st.stk)
    (hn : st'.next = st.next) (htk : st'.tick = st.tick) (hts : st'.ticks = st.ticks) : CInv memoF st' F := by
  obtain ⟨a, b, c, d, e, f, g, k, l, m⟩ := h
  refine ⟨a.congr hg hd ho hs, ?_, ?_, ?_, ?_, fun j hj => by rw [ho]; rw [hts] at hj; exact f j hj,
    fun i d hd => g i d (by rw [← hg]; exact hd), fun i d hd => k i d (by rw [← hg]; exact hd),
    fun i d hd => by rw [ho]; exact l i d (by rw [← hg]; exact hd), fun hm => ?_⟩
  · intro m; simp only [ranOf, chgOf, hts, htk]; exact b m
  · simp only [OrdInv, ho, hs, hn]; exact c
  · obtain ⟨d1, d2, d3, d4, d5⟩ := d
    exact ⟨by simp only [FrozenOK, calleesOf, gitG, hg]; exact d1, by simp only [hg, ho]; exact d2, by simp only [hg, ho]; exact d3, d4, by simp only [hd, hg]; exact d5⟩
  · intro m o hmo
    rw [hn]
    exact memOK_congr hg ho hts (e m o (by rw [← ho]; exact hmo))
  · obtain ⟨m1, m2⟩ := m hm
    exact ⟨fun i d hi c hc => by rw [hg] at hi ⊢; exact m1 i d hi c hc,
      fun i d hi hio c hc => by rw [ho]; rw [hg] at hi; rw [ho] at hio; exact m2 i d hi hio c hc⟩

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
  have hcal : calleesOf st' m = calleesOf st m := by simp only [calleesOf, gitG, Treap.gut, hgm]
  rcases he with ⟨he, hce⟩ | ⟨hce, ⟨o, hco, hlt⟩, htab⟩
  · exact Or.inl ⟨hF e he, by rw [hcal]; exact hce⟩
  · have hcs : (e.more, e.fol) ∈ st.stk := (hi.ord_stk _).mp ⟨o, hco⟩
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
  ∀ idT gs r gs' (F : Entry → Prop), CInv memoF gs.st F → WellFormed idT.1 → NormSock idT.1 → idT.1 ≠ Sock.void →
    res idT gs = some (r, gs') →
    (∃ F', (∀ e, F e → F' e) ∧ CInv memoF gs'.st F') ∧
    GStepsR (gCore gs.st.g) (gCore gs'.st.g) ∧ Keep gs.st.stk (· ∈ gs.st.stk) gs.st gs'.st ∧
    Frame (· ∈ gs.st.stk) gs.st gs'.st ∧ gs'.gen = gs.gen ∧ gs'.callees = gs.callees ∧
    gs'.low ≤ gs.low ∧ Pushed gs.st gs'.st gs'.low ∧
    (∀ o, Treap.get gs'.st.order r.1 = some o → gs'.low ≤ o) ∧
    (gs'.back = false → gs.back = false ∧ ∀ o, Treap.get gs'.st.order r.1 = some o → r.1 ∉ gs.st.stk) ∧
    AnsW (RBat gs'.st r.1) idT.1 idT.2 r.2.core.tab

/-- What the `resolve` loop begun with `orig` keeps and gives: `ResP2` for
the current identity, when it is `orig` or the memo lookup at `orig` misses
(after a `%he` step the loop asks `+git:mi` at `orig` again), and the current
subject sock comes from `orig.1` by `%he` steps (`HeChain`).  The answer is
an answer at `orig`: the `%rec` branch patches with `orig.1`, as the Hoon
does (`(patch-prod [prod map]:d sock.prod.s)`), which is an answer at
`orig.1` and not at the current sock. -/
def ResP2L (memoF : Memo M) (orig : Ident) (res : ResGo M R) : Prop :=
  ∀ idT gs r gs' (F : Entry → Prop), (idT = orig ∨ gitMi gs.st.done orig.2 orig.1 = some none) →
    HeChain orig.1 idT.1 → idT.2 = orig.2 → orig.1 ≠ Sock.void →
    CInv memoF gs.st F → WellFormed idT.1 → NormSock idT.1 → idT.1 ≠ Sock.void →
    res idT gs = some (r, gs') →
    (∃ F', (∀ e, F e → F' e) ∧ CInv memoF gs'.st F') ∧
    GStepsR (gCore gs.st.g) (gCore gs'.st.g) ∧ Keep gs.st.stk (· ∈ gs.st.stk) gs.st gs'.st ∧
    Frame (· ∈ gs.st.stk) gs.st gs'.st ∧ gs'.gen = gs.gen ∧ gs'.callees = gs.callees ∧
    gs'.low ≤ gs.low ∧ Pushed gs.st gs'.st gs'.low ∧
    (∀ o, Treap.get gs'.st.order r.1 = some o → gs'.low ≤ o) ∧
    (gs'.back = false → gs.back = false ∧ ∀ o, Treap.get gs'.st.order r.1 = some o → r.1 ∉ gs.st.stk) ∧
    AnsW (RBat gs'.st r.1) orig.1 orig.2 r.2.core.tab

theorem resP2_of_loop {memoF : Memo M} {resl : Ident → ResGo M R} (h : ∀ orig, ResP2L memoF orig (resl orig)) :
    ResP2 memoF (fun i => resl i i) :=
  fun idT gs r gs' F hc hw hn hnv e =>
    h idT idT gs r gs' F (Or.inl rfl) (HeChain.refl _) rfl hnv hc hw hn hnv e

/-- What `+analyze` keeps and gives. -/
def AnaP2 (memoF : Memo M) (ana : AnaGo M R) : Prop :=
  ∀ id st low st' (F : Entry → Prop), CInv memoF st F → WellFormed id.1 → NormSock id.1 → id.1 ≠ Sock.void →
    Treap.get st.g id = none →
    ana id st = some (low, st') →
    (∃ F', (∀ e, F e → F' e) ∧ CInv memoF st' F') ∧
    GStepsR (gCore st.g) (gCore st'.g) ∧ Keep st.stk (· ∈ st.stk) st st' ∧ Frame (· ∈ st.stk) st st' ∧
    Pushed st st' low ∧ (∃ d, Treap.get st'.g id = some d) ∧
    (∀ o, Treap.get st'.order id = some o → low ≤ o) ∧
    (∀ x o, Treap.get st'.order x = some o → x ∉ st.stk → low < st.next)

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
    (gs.back = false → ∀ c, InCallees gs.callees c → ∀ o, Treap.get gs.st.order c = some o → c ∉ st0.stk) ∧
    (∀ c, InCallees gs.callees c → Treap.get gs.st.g c ≠ none)

theorem runInv_stable (memoF : Memo M) (st0 : SkaState M R) (F0 : Entry → Prop) (index : Nat) :
    LocalStableC (RunInv memoF st0 F0 index) := by
  intro gs gs' h hlf hc
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := hlf
  obtain ⟨F, hF, a, b, c, d, e, f, g, i, j⟩ := h
  refine ⟨F, hF, a.congr e3 e4 e5 e6 e7 e9 e10, by rw [e3]; exact b, c.congr2 e3 e5 e6,
    d.congr2 e3 e5 e7 e9 e10, by rw [e1]; exact e, by rw [e1]; exact f.congr e3 e5 e10,
    fun c' hc' o ho => ?_, fun hb c' hc' o ho => ?_, fun c' hc' => ?_⟩
  · rw [hc] at hc'; rw [e5] at ho; rw [e1]; exact g c' hc' o ho
  · rw [hc] at hc'; rw [e5] at ho; rw [e2] at hb; exact i hb c' hc' o ho
  · rw [hc] at hc'; rw [e3]; exact j c' hc'

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

theorem inCallees_ins {cs : M CalleeEntry Unit} {seat : Option Noun} {i c : Ident}
    (h : InCallees (Treap.ins cs ⟨seat, i⟩) c) : c = i ∨ InCallees cs c := by
  obtain ⟨seat', hs⟩ := h
  rcases (Treap.has_ins _ _ _).mp hs with e | e
  · left; cases e; rfl
  · exact Or.inr ⟨seat', e⟩

theorem not_inCallees_empty (c : Ident) : ¬ InCallees (Treap.empty : M CalleeEntry Unit) c := by
  rintro ⟨seat, h⟩
  simp [Treap.has, Treap.get_empty] at h

/-- **`resolve` meets what the bridge asks**, at the `gen`s of a run. -/
theorem resOKD_of_resP2 {memoF : Memo M} {res : ResGo M R} (h : ResP2 memoF res) (st0 : SkaState M R)
    (F0 : Entry → Prop) (index : Nat) (hidx : index < st0.next) :
    ResOKD PfR (RunInv memoF st0 F0 index) res := by
  intro idT gs r gs' hi hw hnv e
  obtain ⟨F, hF0, hc, s1, k1, fr1, hlow, hpush, hcl, hbk, hing⟩ := hi
  obtain ⟨⟨F', hFF', hc'⟩, s2, k2, fr2, hgen, hcal, hle, hpush2, hr1, hback, hans⟩ := h idT gs r gs' F hc hw.1 hw.2 hnv e
  have hst0 : ∀ j ∈ st0.stk, j ∈ gs.st.stk := fun j hj => by
    obtain ⟨l, el⟩ := k1.1; rw [el]; exact List.mem_append_right _ hj
  have hnew : ∀ c o, Treap.get gs'.st.order c = some o → c ∉ gs.st.stk → gs'.low ≤ o := fun c o hco hcn => by
    have := fr2.newOrd c o hco (fun h => hcn ((hc.s.ord_stk c).mp ⟨o, h⟩))
    have := fr1.next
    omega
  have hold : ∀ c o, Treap.get gs'.st.order c = some o → c ∈ gs.st.stk → Treap.get gs.st.order c = some o :=
    fun c o hco hcs => by rw [← k2.2.1 c hcs]; exact hco
  refine ⟨hgen, ?_, fun gs'' seat hlf hcs => ?_⟩
  · intro s f a ha
    refine ha.mono (fun e he => ?_)
    obtain ⟨⟨d, hd, ht⟩, w1, w2, nn, ho⟩ := he
    by_cases hn : Treap.get gs.st.order (e.more, e.fol) = none
    · obtain ⟨a1, a2⟩ := fr2.fin _ d hd hn
      exact ⟨⟨d, a1, ht⟩, w1, w2, nn, by rw [hcal]; exact ho⟩
    · obtain ⟨o, hoo⟩ := Option.ne_none_iff_exists'.mp hn
      have hs : (e.more, e.fol) ∈ gs.st.stk := (hc.s.ord_stk _).mp ⟨o, hoo⟩
      exact ⟨⟨d, by rw [k2.2.2 _ hs]; exact hd, ht⟩, w1, w2, nn, by rw [hcal]; exact ho⟩
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := hlf
  refine ⟨⟨F', fun x hx => hFF' x (hF0 x hx), hc'.congr e3 e4 e5 e6 e7 e9 e10, by rw [e3]; exact gStepsR_trans s1 s2,
    (k1.trans (k2.weaken k1.1 (fun j hj => hst0 j hj))).congr2 e3 e5 e6,
    (fr1.trans fr2 hst0 k2.2.1 hc.s).congr2 e3 e5 e7 e9 e10, by rw [e1]; exact Nat.le_trans hle hlow, ?_, ?_, ?_,
    ?_⟩, ?_⟩
  · -- the members left on the stack
    refine Pushed.congr (fun x o hxo hx0 => ?_) e3 e5 e10
    rw [e1]
    by_cases hxs : x ∈ gs.st.stk
    · obtain ⟨hr, hlb⟩ := hpush x o (hold x o hxo hxs) hx0
      have hran : ranOf gs'.st x = ranOf gs.st x := by simp only [ranOf, Treap.gut, fr2.ticks x hxs]
      refine ⟨by rw [hran]; exact hr, fun c hce oc hco => ?_⟩
      have hcal' : calleesOf gs'.st x = calleesOf gs.st x := by
        simp only [calleesOf, gitG, Treap.gut, k2.2.2 x hxs]
      rw [hcal'] at hce
      by_cases hcs : c ∈ gs.st.stk
      · exact Nat.le_trans hle (hlb c hce oc (hold c oc hco hcs))
      · exact hnew c oc hco hcs
    · exact hpush2 x o hxo hxs
  · -- the callees
    intro c hc0 o ho
    rw [e5] at ho; rw [e1]
    rw [hcs] at hc0
    rcases inCallees_ins hc0 with rfl | hc0
    · exact hr1 o ho
    · rw [hcal] at hc0
      by_cases hcs' : c ∈ gs.st.stk
      · exact Nat.le_trans hle (hcl c hc0 o (hold c o ho hcs'))
      · exact hnew c o ho hcs'
  · -- `back`
    intro hb c hc0 o ho
    rw [e5] at ho; rw [e2] at hb
    obtain ⟨hb0, hbr⟩ := hback hb
    rw [hcs] at hc0
    rcases inCallees_ins hc0 with rfl | hc0
    · exact fun h0 => hbr o ho (hst0 _ h0)
    · rw [hcal] at hc0
      by_cases hcs' : c ∈ gs.st.stk
      · exact hbk hb0 c hc0 o (hold c o ho hcs')
      · exact fun h0 => hcs' (hst0 _ h0)
  · -- the callees are entries
    intro c hc0
    rw [e3]
    rw [hcs] at hc0
    rcases inCallees_ins hc0 with rfl | hc0
    · obtain ⟨e, ⟨d, hd, _⟩, _, _, _, he⟩ := AnsW.exists_entry hans
      rw [← he, hd]; simp
    · rw [hcal] at hc0
      exact inG_frame hc.s k2 fr2 (hing c hc0)
  · -- the answer
    refine hans.mono (fun e he => ?_)
    obtain ⟨⟨d, hd, ht⟩, w1, w2, nn, ho⟩ := he
    exact ⟨⟨d, by rw [e3]; exact hd, ht⟩, w1, w2, nn, ⟨seat, by rw [hcs, ho]; exact (Treap.has_ins _ _ _).mpr (Or.inl rfl)⟩⟩

/-- **The other members keep their answers across the write of `+run`**:
the entry of `id` changes only with its change tick moving to the new clock,
or keeps its `TabEntry`. -/
theorem memOK_runEnd {st st' : SkaState M R} {F : Entry → Prop} {m id : Ident} {L : Nat} {dn : FDatum M}
    {chg : Bool} (hmi : m ≠ id) (htk : TickInv st)
    (hg : ∀ j, Treap.get st'.g j = if j = id then some dn else Treap.get st.g j)
    (ho : st'.order = st.order) (hts : ∀ j, j ≠ id → Treap.get st'.ticks j = Treap.get st.ticks j)
    (hch : chg = true → st.tick < chgOf st' id)
    (hun : chg = false → chgOf st' id = chgOf st id ∧ dn.core.tab = (gitG st.g id).core.tab)
    (h : MemOK st F m L) : MemOK st' F m L := by
  intro d hd hr
  have hgm : Treap.get st'.g m = Treap.get st.g m := by rw [hg, if_neg hmi]
  have hran : ranOf st' m = ranOf st m := by simp only [ranOf, Treap.gut, hts m hmi]
  rw [hgm] at hd; rw [hran] at hr
  obtain ⟨P, L', hL, hrun, hP⟩ := h d hd hr
  refine ⟨P, L', hL, hrun, fun s f a hp => (hP s f a hp).mono (fun e he => ?_)⟩
  have hcal : calleesOf st' m = calleesOf st m := by simp only [calleesOf, gitG, Treap.gut, hgm]
  rcases he with ⟨he, hce⟩ | ⟨hce, ⟨o, hco, hlt⟩, htab⟩
  · exact Or.inl ⟨he, by rw [hcal]; exact hce⟩
  · refine Or.inr ⟨by rw [hcal]; exact hce, ⟨o, by rw [ho]; exact hco, hlt⟩, fun hlt' => ?_⟩
    rw [hran] at hlt'
    by_cases hci : (e.more, e.fol) = id
    · rw [hci] at hlt' ⊢
      cases chg with
      | true =>
        have := hch rfl
        have := (htk m).1
        omega
      | false =>
        obtain ⟨hc1, hc2⟩ := hun rfl
        rw [hc1] at hlt'
        obtain ⟨dc, hdc, htc⟩ := htab (by rw [hci]; exact hlt')
        rw [hci] at hdc
        refine ⟨dn, by rw [hg, if_pos rfl], ?_⟩
        rw [hc2, ← htc]
        simp [gitG, Treap.gut, hdc]
    · have hc1 : chgOf st' (e.more, e.fol) = chgOf st (e.more, e.fol) := by
        simp only [chgOf, Treap.gut, hts _ hci]
      rw [hc1] at hlt'
      obtain ⟨dc, hdc, htc⟩ := htab hlt'
      exact ⟨dc, by rw [hg, if_neg hci]; exact hdc, htc⟩

/-- **`+run` keeps the convergence invariant**, given that `resolve` does at
every lower fuel. -/
theorem runStep_ok2 (env : Env R) (memoF : Memo M) {n : Nat}
    (hres : ∀ k, k < n → ResP2 memoF (resolveR env memoF k)) : RunP2 memoF (runStep (folLoop env memoF n)) := by
  intro id index st r st' F hc hid hidx e
  unfold runStep at e
  simp only [Option.map_eq_some_iff] at e
  obtain ⟨⟨out, gs⟩, hf, e⟩ := e
  have e' : runEnd id (gitG st.g id) out gs = (r, st') := e
  have est : st' = (runEnd id (gitG st.g id) out gs).2 := (congrArg Prod.snd e').symm
  have er0 : r = (runEnd id (gitG st.g id) out gs).1 := (congrArg Prod.fst e').symm
  subst est er0
  generalize hdat : gitG st.g id = data
  let st0 : SkaState M R := { st with stats := { st.stats with runs := st.stats.runs + 1 } }
  have c0 : CInv memoF st0 F := hc.congr rfl rfl rfl rfl rfl rfl rfl
  have hidx0 : index < st0.next := hc.ord.1 id index hidx
  have r0 : RunInv memoF st0 F index (genInit index st0) := by
    refine ⟨F, fun _ h => h, c0, GStepsR.refl _, Keep.refl' _ rfl rfl rfl,
      Frame.refl' rfl rfl rfl rfl rfl rfl c0.s, Nat.le_refl _, ?_, ?_, ?_, ?_⟩
    · intro x o hxo hx; exact absurd ((c0.s.ord_stk x).mp ⟨o, hxo⟩) hx
    · intro c hc'; exact absurd hc' (not_inCallees_empty c)
    · intro _ c hc'; exact absurd hc' (not_inCallees_empty c)
    · intro c hc'; exact absurd hc' (not_inCallees_empty c)
  have hnid : NormSock id.1 := by
    obtain ⟨d0, hd0⟩ := hc.s.mem_g hid; exact (hc.norm id d0 hd0).1
  obtain ⟨i1, _, hF⟩ := run_folTopRD env memoF pfR_wf (runInv_stable memoF st0 F index) pfR_stable
    (fun k hk => resOKD_of_resP2 (hres k hk) st0 F index hidx0) r0 ⟨hc.s.wf_stk hid, hnid⟩ hf
  obtain ⟨F1, hF01, c1, s1, k1, fr1, hlow1, hpush1, hcl1, hbk1, hing1⟩ := i1
  obtain ⟨er, eg, eo, es, ed, en, etk, ets⟩ := runEnd_eff id data out gs
  generalize hrd : runDatum (Treap.has gs.st.moved id) id.1 out gs.gen data.core = rd at er eg ets
  generalize hdn : (⟨gs.callees, rd.1.nomm, rd.1.less, rd.1.indi, rd.1.seek, rd.1.prod, rd.1.map, gs.area⟩ :
    FDatum M) = dn at eg
  have hdc : dn.core = rd.1 := by rw [← hdn]; rfl
  obtain ⟨d0, hd0⟩ := hc.s.mem_g hid
  have hg0 : Treap.get gs.st.g id = Treap.get st.g id := k1.2.2 id hid
  have hgit : gitG gs.st.g id = data := by rw [← hdat]; unfold gitG Treap.gut; rw [hg0]
  have hold : gCore gs.st.g id = some data.core := by
    rw [← hdat]
    simp only [gCore, hg0]
    simp [hd0, gitG, Treap.gut]
  have hgid : gitG (runEnd id data out gs).2.g id = dn := by
    unfold gitG Treap.gut; rw [eg, Treap.get_put, if_pos rfl]; rfl
  have hgx : ∀ x, x ≠ id → gitG (runEnd id data out gs).2.g x = gitG gs.st.g x := fun x hx => by
    unfold gitG Treap.gut; rw [eg, Treap.get_put, if_neg hx]
  have hcalid : calleesOf (runEnd id data out gs).2 id = gs.callees := by
    unfold calleesOf; rw [hgid, ← hdn]
  have hstep := runEnd_gStepR (fun t ht => (pfR_wf gs t ht).1) hF hold
  obtain ⟨iS, kS⟩ := runEnd_ok c1.s hstep
  have hidS : id ∈ gs.st.stk := by obtain ⟨l, el⟩ := k1.1; rw [el]; exact List.mem_append_right _ hid
  have hidO : ∃ o, Treap.get gs.st.order id = some o := (c1.s.ord_stk id).mpr hidS
  have hgj : ∀ j, Treap.get (runEnd id data out gs).2.g j =
      if j = id then some dn else Treap.get gs.st.g j := fun j => by rw [eg, Treap.get_put]
  have htsj : ∀ j, j ≠ id → Treap.get (runEnd id data out gs).2.ticks j = Treap.get gs.st.ticks j :=
    fun j hj => by rw [ets, Treap.get_put, if_neg hj]
  have hchgid : chgOf (runEnd id data out gs).2 id =
      if rd.2.2 then gs.st.tick + 1 else chgOf gs.st id := by
    simp [chgOf, Treap.gut, ets, Treap.get_put]
  have hranid : ranOf (runEnd id data out gs).2 id = gs.st.tick + 1 := by
    simp [ranOf, Treap.gut, ets, Treap.get_put]
  have hunch : rd.2.2 = false → dn.core.tab = (gitG gs.st.g id).core.tab := fun h => by
    rw [hdc, hgit, ← hrd]; exact runDatum_unchanged (by rw [hrd]; exact h)
  have hmem : ∀ m L, m ≠ id → MemOK gs.st F1 m L → MemOK (runEnd id data out gs).2 F1 m L :=
    fun m L hmi h => memOK_runEnd (chg := rd.2.2) hmi c1.tick hgj eo htsj
      (fun h' => by rw [hchgid, if_pos h']; omega)
      (fun h' => ⟨by rw [hchgid, if_neg (by simp [h'])], hunch h'⟩) h
  -- the invariant after the write
  have cS : CInv memoF (runEnd id data out gs).2 F1 := by
    have hcalF : ∀ e, F1 e → calleesOf (runEnd id data out gs).2 (e.more, e.fol) = calleesOf gs.st (e.more, e.fol) :=
      fun e he => by
        have hi : (e.more, e.fol) ≠ id := by
          intro h; obtain ⟨o, ho'⟩ := hidO; rw [← h, (c1.frz.sub e he).2] at ho'; cases ho'
        unfold calleesOf; rw [hgx _ hi]
    refine ⟨iS, fun m => ?_, ?_, ⟨fun e he => c1.frz.ok.mono (fun _ h => h) hcalF he, fun i d h1 h2 => ?_,
      fun e he => ?_, c1.frz.wf, ?_⟩, ?_, ?_, ?_, ?_, ?_, fun hm => ?_⟩
    · by_cases hm : m = id
      · subst hm
        rw [hranid, hchgid, etk]
        obtain ⟨_, h2⟩ := c1.tick m
        refine ⟨Nat.le_refl _, ?_⟩
        split <;> omega
      · have e1 : ranOf (runEnd id data out gs).2 m = ranOf gs.st m := by
          simp only [ranOf, Treap.gut, htsj m hm]
        have e2 : chgOf (runEnd id data out gs).2 m = chgOf gs.st m := by
          simp only [chgOf, Treap.gut, htsj m hm]
        rw [e1, e2, etk]
        obtain ⟨h1, h2⟩ := c1.tick m
        omega
    · simp only [OrdInv, eo, es, en]; exact c1.ord
    · rw [eo] at h2
      have hi : i ≠ id := by rintro rfl; obtain ⟨o, ho⟩ := hidO; rw [h2] at ho; cases ho
      rw [hgj, if_neg hi] at h1
      exact c1.frz.cover i d h1 h2
    · obtain ⟨⟨d, hd, hl⟩, ho⟩ := c1.frz.sub e he
      have hi : (e.more, e.fol) ≠ id := by intro h; obtain ⟨o, ho'⟩ := hidO; rw [← h, ho] at ho'; cases ho'
      exact ⟨⟨d, by rw [hgj, if_neg hi]; exact hd, hl⟩, by rw [eo]; exact ho⟩
    · intro f ms s ent h1 h2
      rw [ed] at h1
      obtain ⟨hF, hk, hge⟩ := c1.frz.done f ms s ent h1 h2
      have hi : ent.1 ≠ id := by
        intro h; obtain ⟨o, ho⟩ := hidO
        have := (c1.frz.sub _ hF).2
        simp only [entOf] at this
        rw [h] at this; rw [this] at ho; cases ho
      exact ⟨hF, hk, by rw [hgj, if_neg hi]; exact hge⟩
    · intro m o hmo
      rw [eo] at hmo; rw [en]
      by_cases hm : m = id
      · subst hm
        intro d hd _
        rw [hgj, if_pos rfl] at hd
        cases hd
        refine ⟨PfR gs, gs.st.next, Nat.le_refl _, ?_, fun s f a hp => hp.transfer (fun e he => ?_)⟩
        · show RunEntryR (PfR gs) ⟨m.1, m.2, dn.core⟩
          rw [hdc, ← hrd]; exact runDatum_runEntryR hF _ _
        · obtain ⟨⟨d, hd, ht⟩, _, _, _, ho⟩ := he
          by_cases hn : Treap.get gs.st.order (e.more, e.fol) = none
          · exact ⟨entOf (e.more, e.fol) d, Or.inl ⟨c1.frz.cover _ d hd hn, by rw [hcalid]; exact ho⟩, rfl, rfl, ht⟩
          · obtain ⟨oc, hoc⟩ := Option.ne_none_iff_exists'.mp hn
            refine ⟨e, Or.inr ⟨?_, ⟨oc, by rw [eo]; exact hoc, c1.ord.1 _ oc hoc⟩, fun hlt => ?_⟩,
              rfl, rfl, rfl⟩
            · rw [hcalid]; exact ho
            · by_cases hci : (e.more, e.fol) = m
              · rw [hci] at hlt ⊢
                rw [hranid, hchgid] at hlt
                cases hch : rd.2.2 with
                | true => rw [hch] at hlt; simp at hlt
                | false =>
                  refine ⟨dn, by rw [hgj, if_pos rfl], ?_⟩
                  rw [hunch hch, ← ht]
                  rw [hci] at hd
                  simp [gitG, Treap.gut, hd]
              · exact ⟨d, by rw [hgj, if_neg hci]; exact hd, ht⟩
      · exact hmem m _ hm (c1.mem m o hmo)
    · intro j hj
      rw [eo]
      by_cases hji : j = id
      · rw [hji]; obtain ⟨o, ho⟩ := hidO; rw [ho]; simp
      · rw [htsj j hji] at hj; exact c1.tkeys j hj
    · intro i d hd
      rw [hgj] at hd
      split at hd
      · rename_i hi; rw [hi]; exact c1.nv id d0 (by rw [hg0]; exact hd0)
      · exact c1.nv i d hd
    · intro i d hd
      rw [hgj] at hd
      split at hd
      · rename_i hi
        cases hd
        rw [hi]
        have hn0 := c1.norm id d0 (by rw [hg0]; exact hd0)
        have hout : NormSock out.prod.sock := folR_norm (fun t ht => (pfR_wf gs t ht).2) n hnid hF
        have hdn0 : NormSock data.core.prod := by
          rw [← hdat]; simp only [gitG, Treap.gut, hd0, Option.getD_some]; exact (hc.norm id d0 hd0).2.2
        obtain ⟨r1, r2⟩ := runDatum_norm (moved := Treap.has gs.st.moved id) (gen' := gs.gen) hnid hout hdn0
        rw [hrd] at r1 r2
        refine ⟨hnid, ?_, ?_⟩
        · rw [← hdn]; exact r1
        · rw [← hdn]; exact r2
      · exact c1.norm i d hd
    · intro i d hd
      rw [hgj] at hd
      split at hd
      · rename_i hi
        cases hd
        rw [hi]
        refine Or.inr ⟨?_, ?_, fun ho => ?_⟩
        · rw [← hdn]
          show Bake.NoAx0 rd.1.nomm
          rw [← hrd]
          exact (folLoop_noAx0 env memoF n _ _ _ _ _ _ _ _ _ hf : Bake.NoAx0 out.nomm)
        · rw [← hdn]
          show ∃ y, Fits rd.1.less y
          rw [← hrd]
          obtain ⟨y, hy⟩ := wf_inhab (hc.s.wf_stk hid) (c1.nv id d0 (by rw [hg0]; exact hd0))
          exact ⟨y, app_fits gs.gen.want id.1 y hy⟩
        · rw [eo] at ho; obtain ⟨o, ho'⟩ := hidO; rw [ho'] at ho; cases ho
      · rw [eo]; exact c1.dat i d hd
    · obtain ⟨hcl, hfc⟩ := c1.clo hm
      refine ⟨closed_put_callees (st := gs.st) hcl eg (fun c hce => ?_), fun i d h1 h2 c hce => ?_⟩
      · rw [← hdn] at hce; exact hing1 c hce
      · rw [eo] at h2 ⊢
        have hi : i ≠ id := by rintro rfl; obtain ⟨o, ho⟩ := hidO; rw [h2] at ho; cases ho
        rw [hgj, if_neg hi] at h1
        exact hfc i d h1 h2 c hce
  refine ⟨⟨F1, hF01, cS, fun m Lmax hm hmi h => hmem m Lmax hmi
    (memOK_frame c0.s hm k1 (fun j hj => fr1.ticks j hj) hF01 (memOK_congr rfl rfl rfl h))⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gStepsR_trans s1 (gStepsR_one hstep)
  · exact (k1.mono (fun j hj => hj.1)).trans (kS.weaken k1.1 (fun j hj => hj.2))
  · refine ⟨fun i d h1 h2 => ?_, fun j hj => ?_, ?_, ?_, fun x o hxo hx => ?_⟩
    · obtain ⟨a1, a2⟩ := fr1.fin i d h1 h2
      have hi : i ≠ id := by rintro rfl; obtain ⟨o, ho⟩ := hidO; rw [a2] at ho; cases ho
      exact ⟨by rw [hgj, if_neg hi]; exact a1, by rw [eo]; exact a2⟩
    · obtain ⟨hj1, hj2⟩ := hj
      rw [htsj j hj2]; exact fr1.ticks j hj1
    · rw [en]; exact fr1.next
    · rw [etk]; have h1 : st.tick ≤ gs.st.tick := fr1.tick; omega
    · rw [eo] at hxo; exact fr1.newOrd x o hxo hx
  · rw [hranid, etk]
  · rw [etk]; have h1 : st.tick ≤ gs.st.tick := fr1.tick; omega
  · intro hch
    rw [er] at hch
    simp only at hch
    refine ⟨?_, ?_⟩
    · rw [hchgid, if_neg (by simp [hch])]
      simp only [chgOf, Treap.gut, fr1.ticks id hid]; rfl
    · rw [hgid, hunch hch, hgit]
  · intro hch
    rw [er] at hch
    simp only at hch
    rw [hchgid, if_pos hch, etk]
  · rw [er]; exact hlow1
  · intro c hce o hco
    rw [er]
    rw [hcalid] at hce; rw [eo] at hco
    exact hcl1 c hce o hco
  · intro x o hxo hx
    rw [er]
    rw [eo] at hxo
    have hxi : x ≠ id := by rintro rfl; exact hx hid
    obtain ⟨hr, hlb⟩ := hpush1 x o hxo hx
    refine ⟨by simp only [ranOf, Treap.gut, htsj x hxi] at hr ⊢; exact hr, fun c hce oc hco => ?_⟩
    have : calleesOf (runEnd id data out gs).2 x = calleesOf gs.st x := by
      unfold calleesOf; rw [hgx x hxi]
    rw [this] at hce; rw [eo] at hco
    exact hlb c hce oc hco
  · intro hb c hce o hco
    rw [er] at hb
    simp only at hb
    rw [hcalid] at hce; rw [eo] at hco
    exact hbk1 hb c hce o hco

/-! ## `resolve` -/

theorem recLoop_cases2 {he : Sock → Sock → Bool} {heOn : Bool} {g : Sock × Noun → Option Datum}
    {kid : Sock × Noun} : ∀ {stk : List (Sock × Noun)} {b : Bool} {i : Sock × Noun},
    recLoop he heOn g kid stk = some (some (b, i)) →
    (b = true ∧ i ∈ stk ∧ i.2 = kid.2 ∧ hitTest ⟨i.1, i.2, SkaModel.gitG g i⟩ kid.1 = some true) ∨
    (b = false ∧ ∃ j ∈ stk, msgSock kid.1 j.1 = some i.1 ∧ i.2 = kid.2)
  | [], _, _, h => by simp [recLoop] at h
  | j :: stk, b, i, h => by
    unfold recLoop at h
    split at h
    · rcases recLoop_cases2 h with ⟨hb, hi, hf, ht⟩ | ⟨hb, j', hj', hm, he'⟩
      · exact Or.inl ⟨hb, List.mem_cons_of_mem _ hi, hf, ht⟩
      · exact Or.inr ⟨hb, j', List.mem_cons_of_mem _ hj', hm, he'⟩
    · rename_i hf
      split at h
      · cases h
      · rename_i ht
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Or.inl ⟨rfl, List.mem_cons_self, (by simpa using hf : kid.2 = j.2).symm, ht⟩
      · split at h
        · simp only [Option.map_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨m, hm, rfl, rfl⟩ := h
          exact Or.inr ⟨rfl, j, List.mem_cons_self, hm, rfl⟩
        · rcases recLoop_cases2 h with ⟨hb, hi, hf, ht⟩ | ⟨hb, j', hj', hm, he'⟩
          · exact Or.inl ⟨hb, List.mem_cons_of_mem _ hi, hf, ht⟩
          · exact Or.inr ⟨hb, j', List.mem_cons_of_mem _ hj', hm, he'⟩

theorem gitG_gCore (g : Callgraph M) (i : Ident) : SkaModel.gitG (gCore g) i = (gitG g i).core := by
  unfold SkaModel.gitG gCore gitG Treap.gut
  cases Treap.get g i <;> simp [FDatum.bunt_core]

/-- The answer of an entry of the graph, as `AnsW` from `RBat`. -/
theorem ansW_entry {st : SkaState M R} (hi : SInv st) {i : Ident} {d : FDatum M} (hd : Treap.get st.g i = some d)
    (hn : NormSock d.prod) {c : Ident} (hc : i = c) : AnsW (RBat st c) i.1 i.2 d.core.tab :=
  AnsW.exact (e := entOf i d) ⟨⟨d, hd, rfl⟩, (hi.wf_get hd).1, (hi.wf_get hd).2, hn, hc⟩

theorem ansW_hit {st : SkaState M R} (hi : SInv st) {i : Ident} {d : FDatum M} (hd : Treap.get st.g i = some d)
    (hn : NormSock d.prod) {c : Ident} (hc : i = c) {s : Sock} (ht : hitTest (entOf i d) s = some true) :
    AnsW (RBat st c) s i.2 (patchDatum d.core s).tab :=
  AnsW.hit (e := entOf i d) ⟨⟨d, hd, rfl⟩, (hi.wf_get hd).1, (hi.wf_get hd).2, hn, hc⟩ ht

theorem ansW_hitGen {st : SkaState M R} (hi : SInv st) {i : Ident} {d : FDatum M} (hd : Treap.get st.g i = some d)
    (hn : NormSock d.prod) {c : Ident} (hc : i = c) {s s0 : Sock} (ht : hitTest (entOf i d) s = some true)
    (hg : GenLe s0 s) : AnsW (RBat st c) s0 i.2 (patchDatum d.core s0).tab :=
  AnsW.hitGen (e := entOf i d) ⟨⟨d, hd, rfl⟩, (hi.wf_get hd).1, (hi.wf_get hd).2, hn, hc⟩ ht hg

/-- **`resolve` keeps the convergence invariant**, given that `resolve` and
`+analyze` do at the fuel below. -/
theorem resolveStep_ok2 (env : Env R) (memoF : Memo M) {orig : Ident} {resolve : ResGo M R} {analyze : AnaGo M R}
    (hres : ResP2L memoF orig resolve) (hana : AnaP2 memoF analyze) :
    ResP2L memoF orig (resolveStep env resolve analyze orig) := by
  intro idT gs r gs' F horig hch hf2 hov hc hw hn hnv e
  have lift : ∀ {G : Entry → Prop} {a : TabEntry}, AnsW G idT.1 idT.2 a → AnsW G orig.1 orig.2 a :=
    fun h => by rw [← hf2]; exact hch.lift h
  have hstay : ∀ low' back', low' ≤ gs.low → (back' = false → gs.back = false) →
      let gs2 : GenS M R := { gs with low := low', back := back' }
      (∃ F', (∀ e, F e → F' e) ∧ CInv memoF gs2.st F') ∧ GStepsR (gCore gs.st.g) (gCore gs2.st.g) ∧
      Keep gs.st.stk (· ∈ gs.st.stk) gs.st gs2.st ∧ Frame (· ∈ gs.st.stk) gs.st gs2.st ∧ gs2.gen = gs.gen ∧
      gs2.callees = gs.callees ∧ gs2.low ≤ gs.low ∧ Pushed gs.st gs2.st gs2.low := fun low' back' hl _ =>
    ⟨⟨F, fun _ h => h, hc⟩, GStepsR.refl _, Keep.refl' _ rfl rfl rfl,
      Frame.refl' rfl rfl rfl rfl rfl rfl hc.s, rfl, rfl, hl,
      fun x o hxo hx => absurd ((hc.s.ord_stk x).mp ⟨o, hxo⟩) hx⟩
  unfold resolveStep at e
  cases hg : Treap.get gs.st.g idT with
  | some d =>
    simp only [hg] at e
    cases ho : Treap.get gs.st.order idT with
    | none =>
      simp only [ho, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hstay gs.low gs.back (Nat.le_refl _) id
      exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, fun o h => by simp [ho] at h,
        fun hb => ⟨hb, fun o h => by simp [ho] at h⟩, lift (ansW_entry hc.s hg (hc.norm _ _ hg).2.2 rfl)⟩
    | some o =>
      simp only [ho, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hstay (min gs.low o) true (Nat.min_le_left _ _) (by simp)
      exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, fun o' h => by rw [ho] at h; cases h; exact Nat.min_le_right _ _,
        fun hb => by simp at hb, lift (ansW_entry hc.s hg (hc.norm _ _ hg).2.2 rfl)⟩
  | none =>
    rw [hg] at e
    simp only at e
    split at e
    · cases e
    · rename_i m hm
      cases e
      -- the lookup is at `orig`; it hits only when `orig` is the identity
      obtain rfl : idT = orig := by
        rcases horig with h | hmiss
        · exact h
        · rw [hmiss] at hm; cases hm
      obtain ⟨k, d0, hk, ht, hcore, _⟩ := gitMi_hit hm
      have hget : Treap.get gs.st.done idT.2 = some (gutMi gs.st.done idT.2) := by
        unfold gutMi Treap.gut
        cases e2 : Treap.get gs.st.done idT.2 with
        | none => simp only [gutMi, Treap.gut, e2, Option.getD_none, Treap.get_empty] at hk; cases hk
        | some ms => rfl
      obtain ⟨hF, hkey, hge⟩ := hc.frz.done _ _ _ _ hget hk
      have hno : Treap.get gs.st.order r.1 = none := (hc.frz.sub _ hF).2
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hstay gs.low gs.back (Nat.le_refl _) id
      refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, fun o h => by simp [hno] at h,
        fun hb => ⟨hb, fun o h => by simp [hno] at h⟩, ?_⟩
      have := ansW_hit (c := r.1) hc.s hge (hc.norm _ _ hge).2.2 rfl (s := idT.1) ht
      simp only at hkey
      rw [hkey, ← hcore] at this
      exact this
    · rename_i hmiss
      split at e
      · cases e
      · rename_i i hrc
        rcases recLoop_cases2 hrc with ⟨hb, _⟩ | ⟨_, j, hj, hm, hf⟩
        · cases hb
        have hwj : WellFormed j.1 := hc.s.wf_stk hj
        have hwi : WellFormed i.1 := wf_msgSock hw hwj hm
        have hnj : NormSock j.1 := by
          obtain ⟨dj, hdj⟩ := hc.s.mem_g hj
          exact (hc.norm j dj hdj).1
        exact hres i gs r gs' F (Or.inr hmiss) (hch.snoc hwj hnj hm) (hf.trans hf2) hov hc hwi
          (normSock_msgSock hn hnj hm) (msgSock_nv hnv hm) e
      · rename_i i hrc
        rcases recLoop_cases2 hrc with ⟨_, hi, hf, ht⟩ | ⟨hb, _⟩
        · simp only [Option.map_eq_some_iff] at e
          obtain ⟨o, hoi, e⟩ := e
          cases e
          obtain ⟨di, hdi⟩ := hc.s.mem_g hi
          have hgi : gitG gs.st.g i = di := by simp [gitG, Treap.gut, hdi]
          obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hstay (min gs.low o) true (Nat.min_le_left _ _) (by simp)
          refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, fun o' h => by
            simp only at h; rw [hoi] at h; cases h; exact Nat.min_le_right _ _, fun hb => by simp at hb, ?_⟩
          rw [gitG_gCore, hgi] at ht
          have := ansW_hitGen hc.s hdi (hc.norm _ _ hdi).2.2 rfl ht (hch.genLe hov)
          rw [hf, hf2] at this
          simp only [hgi]
          exact this
        · cases hb
      · simp only [Option.map_eq_some_iff] at e
        obtain ⟨⟨low, st'⟩, ha, e⟩ := e
        cases e
        obtain ⟨⟨F', hFF', hc'⟩, s1, k1, fr1, hpush, ⟨d, hd⟩, hlo, _⟩ := hana idT gs.st low st' F hc hw hn hnv hg ha
        have hnot : idT ∉ gs.st.stk := hc.s.not_mem hg
        refine ⟨⟨F', hFF', hc'⟩, s1, k1, fr1, rfl, rfl, Nat.min_le_left _ _, fun x o hxo hx => ?_,
          fun o h => Nat.le_trans (Nat.min_le_right _ _) (hlo o h), fun hb => ⟨hb, fun _ _ => hnot⟩, ?_⟩
        · obtain ⟨h1, h2⟩ := hpush x o hxo hx
          exact ⟨h1, fun c hce oc hco => Nat.le_trans (Nat.min_le_right _ _) (h2 c hce oc hco)⟩
        · have hgd : gitG st'.g idT = d := by simp [gitG, Treap.gut, hd]
          simp only [hgd]
          exact lift (ansW_entry hc'.s hd (hc'.norm _ _ hd).2.2 rfl)

end Ana
end SkaModel
end Formalization
