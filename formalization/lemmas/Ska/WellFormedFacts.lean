import lemmas.Ska.ConvergeProd

/-!
# Well-formed socks: kept by every sock operation of the analysis

`WellFormed` (from `AppMask.lean`) says that no part of a sock is a cell cape
over atom data that knows something.  The proofs of `fol-loop` need it of the
subject sock of every function (`hwf` of `agree_at_convergence`).

Here: every sock operation that makes a product or a subject sock in the
analysis keeps it (`+knit:so`, `+hed:so`, `+tel:so`, `+pull:so`, `+darn:so`,
`+double-int`, `+msg-anno`, `+msg-sock`, `+patch-prod`), and it holds of a
constant `&+d` and of `|+~`.  Then, for the model of `fol-loop`
(`folLoop_wf`): given a well-formed subject sock and a table whose answers
at well-formed subject socks have well-formed products, every product is
well formed, and every subject sock at which the run reads the table is well
formed (the run is the same with a table that fails everywhere else).
-/

namespace Formalization
namespace SkaModel

open Nock

/-! ## Constants -/

theorem wf_void : WellFormed Sock.void := by
  intro ρ c1 c2 k he
  rw [sockAt_void] at he; cases he

theorem wf_dunno : WellFormed Sock.dunno := by
  intro ρ c1 c2 k he
  rw [sockAt_dunno] at he; cases he

theorem sockAt_yes : ∀ (ρ : List Bool) (d : Noun),
    (∃ d', sockAt (Sock.mk Cape.yes d) ρ = Sock.mk Cape.yes d') ∨
      sockAt (Sock.mk Cape.yes d) ρ = Sock.dunno
  | [], d => Or.inl ⟨d, rfl⟩
  | b :: ρ, d => by
    cases d with
    | atom k =>
      right
      cases b
      · show sockAt (So.hed _) ρ = _; simp only [So.hed]; exact sockAt_dunno ρ
      · show sockAt (So.tel _) ρ = _; simp only [So.tel]; exact sockAt_dunno ρ
    | cell h t =>
      cases b
      · exact sockAt_yes ρ h
      · exact sockAt_yes ρ t

/-- A constant `&+d` is well formed. -/
theorem wf_yes (d : Noun) : WellFormed (Sock.mk Cape.yes d) := by
  intro ρ c1 c2 k he
  rcases sockAt_yes ρ d with ⟨d', e⟩ | e <;> rw [e] at he <;> cases he

theorem wf_no (d : Noun) : WellFormed (Sock.mk Cape.no d) := by
  intro ρ c1 c2 k he
  obtain ⟨d', e⟩ := sockAt_no d ρ
  rw [e] at he; cases he

/-! ## Parts and knits -/

theorem wf_hed {S : Sock} (h : WellFormed S) : WellFormed (So.hed S) := h.part [false]

theorem wf_tel {S : Sock} (h : WellFormed S) : WellFormed (So.tel S) := h.part [true]

theorem wf_knit {S1 S2 : Sock} (h1 : WellFormed S1) (h2 : WellFormed S2) :
    WellFormed (So.knit S1 S2) := by
  cases S1 with
  | void => exact wf_void
  | mk l d1 =>
  cases S2 with
  | void => exact wf_void
  | mk r d2 =>
  intro ρ c1 c2 k he
  cases ρ with
  | nil =>
    simp only [sockAt, So.knit] at he
    split at he
    · simp [Sock.dunno] at he
    · cases (Sock.mk.inj he).2
  | cons b ρ =>
    rcases sockAt_knit_cons (S1 := Sock.mk l d1) (S2 := Sock.mk r d2) (by simp) (by simp) b ρ
      with e | e
    · rw [e] at he; cases he
    · rw [e] at he
      cases b
      · exact h1 ρ c1 c2 k he
      · exact h2 ρ c1 c2 k he

theorem wf_pull {S s : Sock} {a : Nat} (h : WellFormed S) (hp : So.pull S a = some s) :
    WellFormed s := by
  by_cases ha : a = 0
  · subst ha; simp [So.pull] at hp
  obtain ⟨q, hq⟩ := axisPath_pos a (by omega)
  rw [pull_eq_sockAt (by omega) hq] at hp
  cases hp
  exact h.part q

/-! ## `+darn:so` -/

theorem wf_darnUp : ∀ (acc : List (Nat × Sock)) (two : Sock), WellFormed two →
    (∀ p ∈ acc, WellFormed p.2) → WellFormed (So.darnUp two acc)
  | [], two, h, _ => h
  | (n, s) :: acc, two, h, ha => by
    have hs : WellFormed s := ha (n, s) (by simp)
    have ht : ∀ p ∈ acc, WellFormed p.2 := fun p hp => ha p (by simp [hp])
    rw [darnUp_eq]
    split
    · exact wf_darnUp _ _ (wf_knit h hs) ht
    · exact wf_darnUp _ _ (wf_knit hs h) ht

theorem wf_darnDown : ∀ (ax : Nat) (one two : Sock) (acc : List (Nat × Sock)) (s : Sock),
    WellFormed one → WellFormed two → (∀ p ∈ acc, WellFormed p.2) →
    So.darnDown one ax two acc = some s → WellFormed s := by
  intro ax
  induction ax using Nat.strongRecOn with
  | _ ax ih =>
  intro one two acc s h1 h2 ha hd
  rw [So.darnDown] at hd
  split at hd
  · cases hd; exact wf_darnUp acc two h2 ha
  · split at hd
    · cases hd
    · split at hd
      · exact ih (mas ax) (mas_lt ax (by omega)) _ _ _ _ (wf_hed h1) h2
          (fun p hp => by
            simp only [List.mem_cons] at hp
            rcases hp with rfl | hp
            · exact wf_tel h1
            · exact ha p hp) hd
      · exact ih (mas ax) (mas_lt ax (by omega)) _ _ _ _ (wf_tel h1) h2
          (fun p hp => by
            simp only [List.mem_cons] at hp
            rcases hp with rfl | hp
            · exact wf_hed h1
            · exact ha p hp) hd

theorem wf_darn {one two s : Sock} {ax : Nat} (h1 : WellFormed one) (h2 : WellFormed two)
    (hd : So.darn one ax two = some s) : WellFormed s := by
  unfold So.darn at hd
  split at hd
  · cases hd; exact h2
  · split at hd
    · cases hd; exact wf_void
    · split at hd
      · cases hd; exact wf_dunno
      · exact wf_darnDown ax one two [] s h1 h2 (by simp) hd

/-! ## The merges of products and of subjects -/

theorem wf_doubleInt' : ∀ (k : Nat) (a b : Anno), Sock.msr a.sock + Sock.msr b.sock < k →
    WellFormed a.sock → WellFormed b.sock → WellFormed (doubleInt a b).sock := by
  intro k
  induction k with
  | zero => intro _ _ h; omega
  | succ k ih =>
  intro a b hk ha hb
  by_cases hab : a = b
  · subst hab; rw [doubleInt_self]; exact ha
  obtain ⟨sa, ra⟩ := a
  obtain ⟨sb, rb⟩ := b
  cases sa with
  | void => rw [doubleInt_void_left rfl hab]; exact hb
  | mk ca da =>
  cases sb with
  | void => rw [doubleInt_void_right rfl (by simp) hab]; exact ha
  | mk cb db =>
    apply doubleInt_cases (fun r => WellFormed r.sock) hab wf_dunno
    intro hno
    simp only [not_or] at hno
    have h1 : Sock.msr (So.hed (Sock.mk ca da)) + Sock.msr (So.hed (Sock.mk cb db)) < k := by
      have := msr_hed_lt hno.1 da; have := msr_hed_lt hno.2 db; simp only at hk; omega
    have h2 : Sock.msr (So.tel (Sock.mk ca da)) + Sock.msr (So.tel (Sock.mk cb db)) < k := by
      have := msr_tel_lt hno.1 da; have := msr_tel_lt hno.2 db; simp only at hk; omega
    exact wf_knit (ih _ _ h1 (wf_hed ha) (wf_hed hb)) (ih _ _ h2 (wf_tel ha) (wf_tel hb))

/-- **`+double-int` keeps well-formedness.** -/
theorem wf_doubleInt {a b : Anno} (ha : WellFormed a.sock) (hb : WellFormed b.sock) :
    WellFormed (doubleInt a b).sock :=
  wf_doubleInt' _ a b (Nat.lt_succ_self _) ha hb

theorem wf_msgAnno' : ∀ (k : Nat) (a b : Anno), Sock.msr a.sock + Sock.msr b.sock < k →
    WellFormed a.sock → WellFormed b.sock → WellFormed (msgAnno a b).sock := by
  intro k
  induction k with
  | zero => intro _ _ h; omega
  | succ k ih =>
  intro a b hk ha hb
  obtain ⟨sa, ra⟩ := a
  obtain ⟨sb, rb⟩ := b
  unfold msgAnno
  split
  · exact ha
  · split
    · exact hb
    · exact ha
    · rename_i ah aT da ra' bh bT db rb' heq1 heq2
      simp only [Anno.mk.injEq] at heq1 heq2
      obtain ⟨rfl, rfl⟩ := heq1
      obtain ⟨rfl, rfl⟩ := heq2
      simp only at hk ha hb
      have h1 := msr_hed_lt (c := Cape.cell ah aT) (by simp) da
      have h2 := msr_hed_lt (c := Cape.cell bh bT) (by simp) db
      have h3 := msr_tel_lt (c := Cape.cell ah aT) (by simp) da
      have h4 := msr_tel_lt (c := Cape.cell bh bT) (by simp) db
      exact wf_knit (ih _ _ (by simp only; omega) (wf_hed ha) (wf_hed hb))
        (ih _ _ (by simp only; omega) (wf_tel ha) (wf_tel hb))
    · exact wf_dunno

/-- **`+msg-anno` keeps well-formedness.** -/
theorem wf_msgAnno {a b : Anno} (ha : WellFormed a.sock) (hb : WellFormed b.sock) :
    WellFormed (msgAnno a b).sock :=
  wf_msgAnno' _ a b (Nat.lt_succ_self _) ha hb

theorem wf_mergeProd (moved : Bool) {a b : Anno} (ha : WellFormed a.sock) (hb : WellFormed b.sock) :
    WellFormed (mergeProd moved a b).sock := by
  unfold mergeProd; split
  · exact wf_msgAnno ha hb
  · exact wf_doubleInt ha hb

theorem wf_msgSock' : ∀ (k : Nat) (a b m : Sock), nsize a.data < k → WellFormed a → WellFormed b →
    msgSock a b = some m → WellFormed m := by
  intro k
  induction k with
  | zero => intro _ _ _ h; omega
  | succ k ih =>
  intro a b m hk ha hb hm
  unfold msgSock at hm
  split at hm
  · cases hm; exact ha
  · split at hm
    · cases hm; exact hb
    · cases hm; exact ha
    · rename_i ah aT ad1 ad2 bh bT bd1 bd2 _
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hm
      obtain ⟨h, hh, t, ht, rfl⟩ := hm
      simp only [Sock.data, nsize] at hk
      exact wf_knit (ih (Sock.mk ah ad1) _ _ (by simp only [Sock.data]; omega) (wf_hed ha) (wf_hed hb) hh)
        (ih (Sock.mk aT ad2) _ _ (by simp only [Sock.data]; omega) (wf_tel ha) (wf_tel hb) ht)
    · cases hm
    · cases hm; exact wf_dunno

/-- **`+msg-sock` keeps well-formedness**: the subject of a `%he`
generalization is well formed if both subjects are. -/
theorem wf_msgSock {a b m : Sock} (ha : WellFormed a) (hb : WellFormed b) (hm : msgSock a b = some m) :
    WellFormed m :=
  wf_msgSock' _ a b m (Nat.lt_succ_self _) ha hb hm

/-- **`+patch-prod` keeps well-formedness** of the product and the new
subject sock. -/
theorem wf_patchProd {new : Sock} (hn : WellFormed new) :
    ∀ (σ : Noun) (S : Sock), WellFormed S → WellFormed (patchProd S σ new).sock := by
  intro σ
  induction σ with
  | atom a =>
    intro S hS
    by_cases ha : a = 0
    · subst ha; rw [patchProd_zero]; exact hS
    by_cases hv : S = Sock.void
    · subst hv; rw [patchProd]; simp only [if_neg (by simp [ha] : ¬ A a = A 0), if_true]; exact wf_void
    rw [patchProd_atom new ha hv]
    cases hp : So.pull new a with
    | none => exact wf_void
    | some s' => exact wf_pull hn hp
  | cell h t ih1 ih2 =>
    intro S hS
    by_cases hv : S = Sock.void
    · subst hv; rw [patchProd]; simp; exact wf_void
    rw [patchProd_cell new hv]
    exact wf_knit (ih1 _ (wf_hed hS)) (ih2 _ (wf_tel hS))

theorem wf_patchDatum {d : Datum} {s : Sock} (hd : WellFormed d.prod) (hs : WellFormed s) :
    WellFormed (patchDatum d s).prod :=
  wf_patchProd hs d.map d.prod hd

/-! ## `fol-loop` keeps well-formed products and reads the table only at
well-formed subject socks -/

/-- The table's answers at well-formed subject socks have well-formed
products. -/
def TabWF (tab : Tab) : Prop := ∀ s f a, WellFormed s → tab s f = some a → WellFormed a.prod

/-- The table cut down to well-formed subject socks: it fails elsewhere. -/
noncomputable def tabOnWF (tab : Tab) : Tab := fun s f =>
  @ite _ (WellFormed s) (Classical.propDecidable _) (tab s f) none

theorem tabOnWF_eq {tab : Tab} {s : Sock} (hs : WellFormed s) (f : Noun) : tabOnWF tab s f = tab s f := by
  unfold tabOnWF; rw [@if_pos _ (Classical.propDecidable _) hs]

/-- What a run of the recursion `go` gives on a well-formed subject sock: a
well-formed product, and the same result from `go'` (the recursion with the
table cut down to well-formed subject socks). -/
def GoWF (go go' : FolGo) : Prop :=
  ∀ fol sub mk bc df gen out gen', WellFormed sub.sock → go fol sub mk bc df gen = some (out, gen') →
    WellFormed out.prod.sock ∧ go' fol sub mk bc df gen = some (out, gen')

theorem callStep_wf {tab : Tab} {go go' : FolGo} (htab : TabWF tab) (IH : GoWF go go')
    {mk : Option Noun} {bc df : Bool} {s f out : FolOut} {gen gen' : Gen}
    (hs : WellFormed s.prod.sock) (h : callStep tab go mk bc df s f gen = some (out, gen')) :
    WellFormed out.prod.sock ∧ callStep (tabOnWF tab) go' mk bc df s f gen = some (out, gen') := by
  unfold callStep at h ⊢
  by_cases hv : s.prod.sock = Sock.void ∨ f.prod.sock = Sock.void
  · rw [if_pos hv] at h ⊢
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨wf_void, rfl⟩
  rw [if_neg hv] at h ⊢
  have dflt : ∀ (o : FolOut) (g : Gen), some (o, g) = some (out, gen') → o.prod = Anno.dunno →
      WellFormed out.prod.sock ∧ some (o, g) = some (out, gen') := by
    intro o g e hp
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨by rw [hp]; exact wf_dunno, rfl⟩
  cases hf : f.prod.sock with
  | void => exact absurd (Or.inr hf) hv
  | mk c d =>
  rw [hf] at h
  cases c with
  | no => exact dflt _ _ h rfl
  | cell _ _ => exact dflt _ _ h rfl
  | yes =>
  cases d with
  | atom _ => exact dflt _ _ h rfl
  | cell fa fb =>
  cases bc with
  | true => exact dflt _ _ h rfl
  | false =>
  simp only at h ⊢
  split at h
  · rename_i hc
    rw [if_pos hc]
    simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨i, hi, rfl, rfl⟩ := h
    obtain ⟨w, e⟩ := IH _ _ _ _ _ _ _ _ hs hi
    exact ⟨w, i, e, rfl, rfl⟩
  · rename_i hc
    rw [if_neg hc, tabOnWF_eq hs]
    simp only [Option.bind_eq_some_iff] at h ⊢
    obtain ⟨dd, hd, h⟩ := h
    refine ⟨?_, dd, hd, h⟩
    split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact htab _ _ _ hs hd

theorem meanArm_wf {go go' : FolGo} (IH : GoWF go go') {tag : Nat} {h : FolOut} {mk : Option Noun}
    {bc : Bool} {gen : Gen} {r : Option (Bell × Option Noun) × Gen} (hh : WellFormed h.prod.sock)
    (hm : meanArm go tag h mk bc gen = some r) : meanArm go' tag h mk bc gen = some r := by
  unfold meanArm at hm ⊢
  split at hm
  · rename_i hc; rw [if_pos hc]; exact hm
  · rename_i hc; rw [if_neg hc]
    simp only [Option.bind_eq_some_iff] at hm ⊢
    obtain ⟨bat, hb, hm⟩ := hm
    refine ⟨bat, hb, ?_⟩
    split at hm
    · simp only [Option.bind_eq_some_iff] at hm ⊢
      obtain ⟨cg, hcg, hm⟩ := hm
      exact ⟨cg, (IH _ _ _ _ _ _ _ _ hh hcg).2, hm⟩
    · exact hm

theorem consProd_wf {l r : FolOut} (hl : WellFormed l.prod.sock) (hr : WellFormed r.prod.sock) :
    WellFormed (consProd l r).1.sock := by
  unfold consProd; split
  · exact wf_yes _
  · exact wf_knit hl hr

/-- One level of `fol-loop` keeps `GoWF`. -/
theorem folStep_wf {tab : Tab} {go go' : FolGo} (htab : TabWF tab) (IH : GoWF go go')
    (IHs : ∀ fol sub mk bc df gen out gen', WellFormed sub.sock →
      go fol sub mk bc df gen = some (out, gen') → go' fol sub mk bc df gen = some (out, gen')) :
    GoWF (folStep tab go) (folStep (tabOnWF tab) go') := by
  intro fol sub mk bc df gen out gen' hsub h
  cases hs : shape fol with
  | cons a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨⟨l, g1⟩, h1, ⟨r, g2⟩, h2, rfl, rfl⟩ := h
    obtain ⟨w1, e1⟩ := IH _ _ _ _ _ _ _ _ hsub h1
    obtain ⟨w2, e2⟩ := IH _ _ _ _ _ _ _ _ hsub h2
    exact ⟨consProd_wf w1 w2, _, e1, _, e2, rfl, rfl⟩
  | op0 p =>
    simp only [folStep, hs, Option.map_eq_some_iff, Prod.mk.injEq] at h ⊢
    obtain ⟨pr, hpr, rfl, rfl⟩ := h
    refine ⟨?_, pr, hpr, rfl, rfl⟩
    split at hpr
    · cases hpr; exact wf_dunno
    · split at hpr
      · cases hpr; exact hsub
      · simp only [Option.map_eq_some_iff] at hpr
        obtain ⟨s', hs', rfl⟩ := hpr
        exact wf_pull hsub hs'
  | op1 p =>
    simp only [folStep, hs, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨wf_yes p, rfl, rfl⟩
  | op2 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨⟨s1, g1⟩, h1, ⟨f1, g2⟩, h2, h3⟩ := h
    obtain ⟨w1, e1⟩ := IH _ _ _ _ _ _ _ _ hsub h1
    obtain ⟨_, e2⟩ := IH _ _ _ _ _ _ _ _ hsub h2
    obtain ⟨w3, e3⟩ := callStep_wf htab IH w1 h3
    exact ⟨w3, _, e1, _, e2, e3⟩
  | op3 a b =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨⟨p1, g1⟩, h1, rfl, rfl⟩ := h
    exact ⟨wf_dunno, _, (IH _ _ _ _ _ _ _ _ hsub h1).2, rfl, rfl⟩
  | op4 a b =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨⟨p1, g1⟩, h1, rfl, rfl⟩ := h
    exact ⟨wf_dunno, _, (IH _ _ _ _ _ _ _ _ hsub h1).2, rfl, rfl⟩
  | op5 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, rfl, rfl⟩ := h
    exact ⟨wf_dunno, _, (IH _ _ _ _ _ _ _ _ hsub h1).2, _, (IH _ _ _ _ _ _ _ _ hsub h2).2, rfl, rfl⟩
  | op6 a b q r =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, ⟨r1, g3⟩, h3, rfl, rfl⟩ := h
    obtain ⟨_, e1⟩ := IH _ _ _ _ _ _ _ _ hsub h1
    obtain ⟨w2, e2⟩ := IH _ _ _ _ _ _ _ _ hsub h2
    obtain ⟨w3, e3⟩ := IH _ _ _ _ _ _ _ _ hsub h3
    exact ⟨wf_doubleInt w2 w3, _, e1, _, e2, _, e3, rfl, rfl⟩
  | op7 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, rfl, rfl⟩ := h
    obtain ⟨w1, e1⟩ := IH _ _ _ _ _ _ _ _ hsub h1
    obtain ⟨w2, e2⟩ := IH _ _ _ _ _ _ _ _ w1 h2
    exact ⟨w2, _, e1, _, e2, rfl, rfl⟩
  | op8 a b q =>
    simp only [folStep, hs] at h ⊢
    exact IH _ _ _ _ _ _ _ _ hsub h
  | op9 p a b =>
    simp only [folStep, hs] at h ⊢
    exact IH _ _ _ _ _ _ _ _ hsub h
  | op10 ax don r1 r2 =>
    simp only [folStep, hs] at h ⊢
    split at h
    · rename_i hx
      rw [if_pos hx]
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨wf_dunno, rfl⟩
    · rename_i hx
      rw [if_neg hx]
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h ⊢
      obtain ⟨⟨dn, g1⟩, h1, ⟨rc, g2⟩, h2, s', hd, rfl, rfl⟩ := h
      obtain ⟨w1, e1⟩ := IH _ _ _ _ _ _ _ _ hsub h1
      obtain ⟨w2, e2⟩ := IH _ _ _ _ _ _ _ _ hsub h2
      exact ⟨wf_darn w2 w1 hd, _, e1, _, e2, s', hd, rfl, rfl⟩
  | op11s p a b =>
    simp only [folStep, hs] at h ⊢
    split at h
    · rename_i hp
      rw [if_pos hp]
      exact IH _ _ _ _ _ _ _ _ hsub h
    · rename_i hp
      rw [if_neg hp]
      simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨⟨q1, g1⟩, h1, rfl, rfl⟩ := h
      obtain ⟨w1, e1⟩ := IH _ _ _ _ _ _ _ _ hsub h1
      exact ⟨w1, _, e1, rfl, rfl⟩
  | op11d tag h1 h2 f =>
    simp only [folStep, hs, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨⟨hh, g1⟩, e1, h⟩ := h
    obtain ⟨wh, e1'⟩ := IH _ _ _ _ _ _ _ _ hsub e1
    split at h
    · rename_i hc
      obtain ⟨w, e⟩ := IH _ _ _ _ _ _ _ _ hsub h
      refine ⟨w, _, e1', ?_⟩
      simp only [if_pos hc]
      exact e
    · rename_i hc
      simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨arm, harm, ⟨fr, g3⟩, h3, rfl, rfl⟩ := h
      obtain ⟨w3, e3⟩ := IH _ _ _ _ _ _ _ _ hsub h3
      refine ⟨w3, _, e1', ?_⟩
      simp only [if_neg hc, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
      exact ⟨arm, meanArm_wf IH wh harm, _, e3, rfl, rfl⟩
  | op11c x y h1 h2 f =>
    simp only [folStep, hs] at h ⊢
    exact IH _ _ _ _ _ _ _ _ hsub h
  | op12 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, rfl, rfl⟩ := h
    exact ⟨wf_dunno, _, (IH _ _ _ _ _ _ _ _ hsub h1).2, _, (IH _ _ _ _ _ _ _ _ hsub h2).2, rfl, rfl⟩
  | other =>
    simp only [folStep, hs, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨wf_dunno, rfl, rfl⟩

/-- **`fol-loop` on a well-formed subject sock**, with a table whose answers
at well-formed subject socks have well-formed products: every product is
well formed, and the run reads the table only at well-formed subject socks:
it returns the same with the table cut down to them (`tabOnWF`), which fails
at every other sock, so a read anywhere else would have failed the run. -/
theorem folLoop_wf {tab : Tab} (htab : TabWF tab) : ∀ n, GoWF (folLoopF tab n) (folLoopF (tabOnWF tab) n)
  | 0 => fun _ _ _ _ _ _ _ _ _ h => by cases h
  | n + 1 => folStep_wf htab (folLoop_wf htab n) (fun _ _ _ _ _ _ _ _ hs h => (folLoop_wf htab n _ _ _ _ _ _ _ _ hs h).2)

/-- **The run of an entry**: from a well-formed subject sock `bus`, the
product is well formed and the table is read only at well-formed subject
socks. -/
theorem folLoopTop_wf {tab : Tab} (htab : TabWF tab) {n : Nat} {bus : Sock} {fol : Noun}
    {out : FolOut} {gen' : Gen} (hb : WellFormed bus) (h : folLoopTop tab n bus fol = some (out, gen')) :
    WellFormed out.prod.sock ∧ folLoopTop (tabOnWF tab) n bus fol = some (out, gen') :=
  folLoop_wf htab n _ _ _ _ _ _ _ _ hb h

end SkaModel
end Formalization
