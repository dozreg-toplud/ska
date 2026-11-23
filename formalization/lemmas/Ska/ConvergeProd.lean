import lemmas.Ska.Converge
import lemmas.Ska.FolLoopProd

/-!
# `ProdRel` at convergence, by induction on the fuel of `+mink`

`prodRel_of_converged`: if every entry of the graph is made by the last run
of `fol-loop` on its identity with the final table, and its stored product
is the merge of that run's product with an older one (`RunEntryM`: `pm` in
`+run`, by `+msg-anno` or `+double-int`), and every answer of the table
comes from the graph (`Answers`), then the entries are right on products
relative to their code requirements (`ProdRel`), given well-formed subject
socks.

The proof breaks the circle of `prodRel_of_rtab` and `rtab_of_answers` by
induction on the fuel of `+mink`.  `ProdRelN K` is `ProdRel` for the runs
with fuel `K`.  It holds for `K = 0`, where no run returns.  From `ProdRelN K`
the table's answers are right on the runs of their callees with fuel `K`
(`rtabP_of_answers`, which is `answers_rel` with the fuel), so the last run
of each entry is right on the runs with fuel `K + 1` (`folLoop_relProdN`),
and so is the merge of the run's product with any other
(`mergeProd_rel`: both merges keep the provenance invariant and the static
condition of their first side), which is the entry's product.

`codeOK_at_convergence` and `agree_at_convergence` are then
`codeOK_of_converged` and `converged_agree` without the hypothesis `ProdRel`.
-/

namespace Formalization
namespace SkaModel

open Nock

/-! ## `+msg-anno` keeps the invariants of its first side -/

theorem provO_msgAnno_left' : ∀ (k : Nat) (a b : Anno), Sock.msr a.sock + Sock.msr b.sock < k →
    ∀ (y : Noun) (o : Option Noun), ProvO y a.sock a.src o →
      ProvO y (msgAnno a b).sock (msgAnno a b).src o := by
  intro k
  induction k with
  | zero => intro _ _ h; omega
  | succ k ih =>
  intro a b hk y o hp
  obtain ⟨sa, ra⟩ := a
  obtain ⟨sb, rb⟩ := b
  unfold msgAnno
  split
  · exact hp
  · split
    · rename_i heq
      simp only [Anno.mk.injEq] at heq
      exact absurd heq.1 hp.nonvoid
    · exact hp
    · rename_i ah aT da ra' bh bT db rb' heq1 heq2
      simp only [Anno.mk.injEq] at heq1 heq2
      obtain ⟨rfl, rfl⟩ := heq1
      obtain ⟨rfl, rfl⟩ := heq2
      simp only at hk
      have h1 := msr_hed_lt (c := Cape.cell ah aT) (by simp) da
      have h2 := msr_hed_lt (c := Cape.cell bh bT) (by simp) db
      have h3 := msr_tel_lt (c := Cape.cell ah aT) (by simp) da
      have h4 := msr_tel_lt (c := Cape.cell bh bT) (by simp) db
      exact provO_knit (ih _ _ (by simp only; omega) y _ (hp.part [false]))
        (ih _ _ (by simp only; omega) y _ (hp.part [true]))
    · exact provO_dunno y o

/-- **`+msg-anno` keeps the provenance invariant of its first side.** -/
theorem provO_msgAnno_left {y : Noun} {o : Option Noun} (a b : Anno) (h : ProvO y a.sock a.src o) :
    ProvO y (msgAnno a b).sock (msgAnno a b).src o :=
  provO_msgAnno_left' _ a b (Nat.lt_succ_self _) y o h

theorem statOK_msgAnno_left' {T : Sock} : ∀ (k : Nat) (a b : Anno),
    Sock.msr a.sock + Sock.msr b.sock < k → a.sock ≠ Sock.void → StatOK T a.sock a.src →
      StatOK T (msgAnno a b).sock (msgAnno a b).src := by
  intro k
  induction k with
  | zero => intro _ _ h; omega
  | succ k ih =>
  intro a b hk hne hp
  obtain ⟨sa, ra⟩ := a
  obtain ⟨sb, rb⟩ := b
  unfold msgAnno
  split
  · exact hp
  · split
    · rename_i heq
      simp only [Anno.mk.injEq] at heq
      exact absurd heq.1 hne
    · exact hp
    · rename_i ah aT da ra' bh bT db rb' heq1 heq2
      simp only [Anno.mk.injEq] at heq1 heq2
      obtain ⟨rfl, rfl⟩ := heq1
      obtain ⟨rfl, rfl⟩ := heq2
      simp only at hk hne
      have h1 := msr_hed_lt (c := Cape.cell ah aT) (by simp) da
      have h2 := msr_hed_lt (c := Cape.cell bh bT) (by simp) db
      have h3 := msr_tel_lt (c := Cape.cell ah aT) (by simp) da
      have h4 := msr_tel_lt (c := Cape.cell bh bT) (by simp) db
      exact statOK_knit (ih _ _ (by simp only; omega) (hed_ne_void hne) (hp.part [false]))
        (ih _ _ (by simp only; omega) (tel_ne_void hne) (hp.part [true]))
    · exact statOK_dunno _ _

/-- **`+msg-anno` keeps the static condition of a first side that is not
`%void`.** -/
theorem statOK_msgAnno_left {T : Sock} (a b : Anno) (hne : a.sock ≠ Sock.void)
    (h : StatOK T a.sock a.src) : StatOK T (msgAnno a b).sock (msgAnno a b).src :=
  statOK_msgAnno_left' _ a b (Nat.lt_succ_self _) hne h

/-- **The product an entry keeps satisfies the provenance invariant and the
static condition wherever the run's product does**, by `+msg-anno` or by
`+double-int`. -/
theorem mergeProd_rel {y p : Noun} {T : Sock} (moved : Bool) (new old : Anno)
    (h : ProvR y new.sock new.src p ∧ StatOK T new.sock new.src) :
    ProvR y (mergeProd moved new old).sock (mergeProd moved new old).src p ∧
      StatOK T (mergeProd moved new old).sock (mergeProd moved new old).src := by
  obtain ⟨hR, hS⟩ := h
  unfold mergeProd
  split
  · exact ⟨provO_iff.mp (provO_msgAnno_left new old (provO_iff.mpr hR)),
      statOK_msgAnno_left new old hR.nonvoid hS⟩
  · exact ⟨provO_iff.mp (provO_doubleInt_left new old (provO_iff.mpr hR)),
      statOK_doubleInt_left new old hR.nonvoid hS⟩

/-! ## The condition the Hoon reaches -/

/-- **An entry as `+run` leaves it**: its nomm and code requirement are those
of the last run of `fol-loop` on its identity with the final table, and its
product (`prod`, `map`) is the merge (`pm` in `+run`) of the run's product
with some earlier product `old`, by `+msg-anno` or `+double-int` as `moved`
says.  Convergence would give `old` = the entry's own product, but the
proofs need no fixed point: both merges keep the invariants of the run's
product.  This matters, because the Hoon does not always reach the fixed
point: a member of a component whose product changed in its last run is not
run again when none of its callees changed since (`+dirty`), and then its
product is `merge(out, old)` with an older `old`.  It also covers the entry
after `+pop`, which turns a `%void` product into `|+~`: a run whose product
is `%void` merges to `old` whatever `old` is.  It is weaker than
`RunEntryP`, which asks that the stored product be the run's. -/
def RunEntryM (tab : Tab) (e : Entry) : Prop :=
  ∃ n out gen' moved old, folLoopTop tab n e.more e.fol = some (out, gen') ∧
    e.d.nomm = out.nomm ∧ e.d.less = Ca.app gen'.want e.more ∧
    (⟨e.d.prod, e.d.map⟩ : Anno) = mergeProd moved out.prod old

/-- **The merges have no common fixed point**, which is why `RunEntryM` asks
for none.  With the run's product `out = [&+[1 2] [2 3]]` and the old
product `[&+[1 2] [2 0]]`, `+double-int` stores `D = [[& |]+[1 0] [2 0]]`,
a change, so the entry joins `moved`; a further run with the same callees
would store `+msg-anno` of `out` and `D`, which is `|+~`, another change.
If no callee of the entry changed since it ran, `+dirty` does not run it
again, and the graph is final with `D`, which is not `msg-anno(out, D)`. -/
theorem merge_no_fixed_point :
    doubleInt ⟨Sock.mk Cape.yes (C (A 1) (A 2)), C (A 2) (A 3)⟩
      ⟨Sock.mk Cape.yes (C (A 1) (A 2)), C (A 2) (A 0)⟩ =
      ⟨Sock.mk (Cape.cell Cape.yes Cape.no) (C (A 1) (A 0)), C (A 2) (A 0)⟩ ∧
    msgAnno ⟨Sock.mk Cape.yes (C (A 1) (A 2)), C (A 2) (A 3)⟩
      ⟨Sock.mk (Cape.cell Cape.yes Cape.no) (C (A 1) (A 0)), C (A 2) (A 0)⟩ = Anno.dunno := by
  constructor
  · rw [doubleInt_mk (by decide)]
    simp only [So.hed, So.tel, Pi.hed, Pi.tel]
    rw [doubleInt_self, doubleInt_mk (by decide)]
    decide
  · unfold msgAnno
    simp

theorem RunEntryM.run {tab : Tab} {e : Entry} (h : RunEntryM tab e) : RunEntry tab e :=
  let ⟨n, out, gen', _, _, h1, h2, h3, _⟩ := h
  ⟨n, out, gen', h1, h2, h3⟩

theorem msgAnno_self (a : Anno) : msgAnno a a = a := by
  unfold msgAnno; simp

theorem mergeProd_self (moved : Bool) (a : Anno) : mergeProd moved a a = a := by
  unfold mergeProd; split
  · exact msgAnno_self a
  · exact doubleInt_self a

/-- `RunEntryP` is the special case where the stored product is the run's. -/
theorem RunEntryP.toM {tab : Tab} {e : Entry} (h : RunEntryP tab e) : RunEntryM tab e := by
  obtain ⟨n, out, gen', h1, h2, h3, hp, hm⟩ := h
  refine ⟨n, out, gen', false, out.prod, h1, h2, h3, ?_⟩
  have : (⟨e.d.prod, e.d.map⟩ : Anno) = out.prod := by rw [hp, hm]
  rw [this, mergeProd_self]

/-! ## The fuel induction -/

/-- `ProdRel` for the runs of `+mink` with fuel `K`. -/
def ProdRelN (lib : Lib) (G : Entry → Prop) (K : Nat) : Prop :=
  ∀ e, G e → ∀ y gul p, Fits e.d.less y → minkF lib gul K [] y e.fol = some (Tone.zero p) →
    ProvR y e.d.prod e.d.map p ∧ StatOK e.more e.d.prod e.d.map

/-- The `less` half of `answers_rel`, which needs nothing about products. -/
theorem answers_lessRel {G : Entry → Prop} (hL : LessRel G) {s : Sock} {f : Noun} {a : TabEntry}
    (h : Answers G s f a) : s ≠ Sock.void →
    ∀ lc dl, a.less = Sock.mk lc dl → ∀ y, Fits (Ca.app lc s) y → Fits a.less y := by
  induction h with
  | exact he => intro _ lc dl hl y hy; exact hL _ lc dl he hl y hy
  | @hit e s he ht => intro hs lc dl hl y hy; exact huge_less hs ht hl hy
  | @gen s s' m f a hm _ ih =>
    intro hs lc dl hl y hy
    have hg := msgSock_genLe hs hm
    have hmv : m ≠ Sock.void := fun e => hs (hg.void_inv e)
    exact ih hmv lc dl hl y (hg.appFits lc (some y) hy)

/-- **The `prod` half of `answers_rel`, with the fuel**: from `ProdRelN K`,
every answer is right on the runs of its formula with fuel `K`. -/
theorem answers_relN {lib : Lib} {G : Entry → Prop} {K : Nat} (hP : ProdRelN lib G K)
    {s : Sock} {f : Noun} {a : TabEntry} (h : Answers G s f a) : s ≠ Sock.void →
    ∀ y gul p, Fits a.less y → minkF lib gul K [] y f = some (Tone.zero p) →
      ProvR y a.prod a.map p ∧ StatOK s a.prod a.map := by
  induction h with
  | exact he => intro _ y gul p hy hm; exact hP _ he y gul p hy hm
  | @hit e s he ht =>
    intro hs y gul p hy hm
    obtain ⟨hR, _⟩ := hP _ he y gul p hy hm
    exact ⟨provO_iff.mp (provO_patchProd hs _ _ _ (provO_iff.mpr hR)), statOK_patchProd _ _⟩
  | @gen s s' m f a hm _ ih =>
    intro hs y gul p hy hmk
    have hg := msgSock_genLe hs hm
    have hmv : m ≠ Sock.void := fun e => hs (hg.void_inv e)
    obtain ⟨hR, hS⟩ := ih hmv y gul p hy hmk
    exact ⟨hR, hS.base hg⟩

theorem rtabL_of_answers {tab : Tab} {G : Entry → Prop} (hL : LessRel G)
    (hans : ∀ s f a, tab s f = some a → Answers G s f a) : RTabL tab :=
  fun s f d lc dl h hs hl y hy => answers_lessRel hL (hans s f d h) hs lc dl hl y hy

theorem rtabP_of_answers {lib : Lib} {tab : Tab} {G : Entry → Prop} {K : Nat} (hP : ProdRelN lib G K)
    (hans : ∀ s f a, tab s f = some a → Answers G s f a) : RTabP lib tab K :=
  fun s f d h hs y gul p hy hm => answers_relN hP (hans s f d h) hs y gul p hy hm

/-- **`ProdRelN K` for every fuel `K`**, by induction on `K`. -/
theorem prodRelN_of_converged {lib : Lib} {tab : Tab} {G : Entry → Prop}
    (hr : ∀ e, G e → RunEntryM tab e) (hans : ∀ s f a, tab s f = some a → Answers G s f a)
    (hwf : ∀ e, G e → WellFormed e.more) : ∀ K, ProdRelN lib G K := by
  have hL : RTabL tab := rtabL_of_answers (lessRel_of_run fun e he => (hr e he).run) hans
  intro K
  induction K with
  | zero => intro e _ y gul p _ hm; simp [minkF] at hm
  | succ K ih =>
    intro e he y gul p hy hm
    obtain ⟨n, out, gen', moved, old, h, _, hl, hpm⟩ := hr e he
    rw [hl] at hy
    have R := mergeProd_rel moved out.prod old
      (folLoop_relProdN hL (rtabP_of_answers ih hans) (hwf e he) h hy hm)
    rw [← hpm] at R
    exact R

/-- **`ProdRel` at convergence.**  Every entry is made by the last run of
`fol-loop` on its identity with the final table and its product is the
merge of the run's with an older one (`hr`), every answer of the table comes from the graph (`hans`), and
every entry's subject sock is well formed (`hwf`). -/
theorem prodRel_of_converged {lib : Lib} {tab : Tab} {G : Entry → Prop}
    (hr : ∀ e, G e → RunEntryM tab e) (hans : ∀ s f a, tab s f = some a → Answers G s f a)
    (hwf : ∀ e, G e → WellFormed e.more) : ProdRel lib G := by
  intro e he y gul p hy hm
  obtain ⟨n, hm⟩ := hm
  exact prodRelN_of_converged hr hans hwf n e he y gul p hy hm

/-- **A converged call graph gives `CodeOK`**, with no assumption on
products: every entry is made by the last run of `fol-loop` on its identity
with the final table, with a product merged from the run's (`hr`, which holds
the termination of the runs), every answer of the table comes from the graph
(`hans`), the code table holds exactly the entries' nomms under their bells
(`hc`, `hhas`), and every entry's subject sock is well formed (`hwf`). -/
theorem codeOK_at_convergence {lib : Lib} {code : Bell → Option Nomm} {tab : Tab} {G : Entry → Prop}
    (hr : ∀ e, G e → RunEntryM tab e) (hans : ∀ s f a, tab s f = some a → Answers G s f a)
    (hc : CodeIs code G) (hhas : CodeHas code G) (hwf : ∀ e, G e → WellFormed e.more) :
    CodeOK lib code :=
  codeOK_of_converged (fun e he => (hr e he).run) hans hc hhas hwf (prodRel_of_converged hr hans hwf)

/-- **The analysis output of every entry of a converged graph agrees with
`+mink` on every subject of its code requirement**, under the assumptions
of `codeOK_at_convergence` only: convergence (`hr`, `hans`, `hc`, `hhas`),
with the termination of the runs inside `hr`, and well-formed subject socks
(`hwf`). -/
theorem agree_at_convergence {lib : Lib} {code : Bell → Option Nomm} {tab : Tab} {G : Entry → Prop}
    (hr : ∀ e, G e → RunEntryM tab e) (hans : ∀ s f a, tab s f = some a → Answers G s f a)
    (hc : CodeIs code G) (hhas : CodeHas code G) (hwf : ∀ e, G e → WellFormed e.more)
    {e : Entry} (he : G e) {x : Noun} (hx : Fits e.d.less x) (gul : Noun) (t : Trace) (r : Tone) :
    Mink lib gul t x e.fol r ↔ ∃ m, nommF lib gul code m t x e.d.nomm = some r :=
  converged_agree (fun e he => (hr e he).run) hans hc hhas hwf (prodRel_of_converged hr hans hwf)
    he hx gul t r

end SkaModel
end Formalization
