import lemmas.Ska.Converge
import lemmas.Ska.FolLoopProd

/-!
# `ProdRel` at convergence, by induction on the fuel of `+mink`

`prodRel_of_converged`: if every entry of the graph is made by the last run
of `fol-loop` on its identity with the final table, and its product did not
move in that run (`RunEntryP`), and every answer of the table comes from the
graph (`Answers`), then the entries are right on products relative to their
code requirements (`ProdRel`), given well-formed subject socks.

The proof breaks the circle of `prodRel_of_rtab` and `rtab_of_answers` by
induction on the fuel of `+mink`.  `ProdRelN K` is `ProdRel` for the runs
with fuel `K`.  It holds for `K = 0`, where no run returns.  From `ProdRelN K`
the table's answers are right on the runs of their callees with fuel `K`
(`rtabP_of_answers`, which is `answers_rel` with the fuel), so the last run
of each entry is right on the runs with fuel `K + 1` (`folLoop_relProdN`),
and since the product did not move, so is the entry.

`codeOK_at_convergence` and `agree_at_convergence` are then
`codeOK_of_converged` and `converged_agree` without the hypothesis `ProdRel`.
-/

namespace Formalization
namespace SkaModel

open Nock

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
    (hr : ∀ e, G e → RunEntryP tab e) (hans : ∀ s f a, tab s f = some a → Answers G s f a)
    (hwf : ∀ e, G e → WellFormed e.more) : ∀ K, ProdRelN lib G K := by
  have hL : RTabL tab := rtabL_of_answers (lessRel_of_run fun e he => (hr e he).run) hans
  intro K
  induction K with
  | zero => intro e _ y gul p _ hm; simp [minkF] at hm
  | succ K ih =>
    intro e he y gul p hy hm
    obtain ⟨n, out, gen', h, _, hl, hp, hmap⟩ := hr e he
    rw [hl] at hy
    rw [hp, hmap]
    exact folLoop_relProdN hL (rtabP_of_answers ih hans) (hwf e he) h hy hm

/-- **`ProdRel` at convergence.**  Every entry is made by the last run of
`fol-loop` on its identity with the final table and its product did not
move (`hr`), every answer of the table comes from the graph (`hans`), and
every entry's subject sock is well formed (`hwf`). -/
theorem prodRel_of_converged {lib : Lib} {tab : Tab} {G : Entry → Prop}
    (hr : ∀ e, G e → RunEntryP tab e) (hans : ∀ s f a, tab s f = some a → Answers G s f a)
    (hwf : ∀ e, G e → WellFormed e.more) : ProdRel lib G := by
  intro e he y gul p hy hm
  obtain ⟨n, hm⟩ := hm
  exact prodRelN_of_converged hr hans hwf n e he y gul p hy hm

/-- **A converged call graph gives `CodeOK`**, with no assumption on
products: every entry is made by the last run of `fol-loop` on its identity
with the final table, with a product that did not move (`hr`, which holds
the termination of the runs), every answer of the table comes from the graph
(`hans`), the code table holds exactly the entries' nomms under their bells
(`hc`, `hhas`), and every entry's subject sock is well formed (`hwf`). -/
theorem codeOK_at_convergence {lib : Lib} {code : Bell → Option Nomm} {tab : Tab} {G : Entry → Prop}
    (hr : ∀ e, G e → RunEntryP tab e) (hans : ∀ s f a, tab s f = some a → Answers G s f a)
    (hc : CodeIs code G) (hhas : CodeHas code G) (hwf : ∀ e, G e → WellFormed e.more) :
    CodeOK lib code :=
  codeOK_of_converged (fun e he => (hr e he).run) hans hc hhas hwf (prodRel_of_converged hr hans hwf)

/-- **The analysis output of every entry of a converged graph agrees with
`+mink` on every subject of its code requirement**, under the assumptions
of `codeOK_at_convergence` only: convergence (`hr`, `hans`, `hc`, `hhas`),
with the termination of the runs inside `hr`, and well-formed subject socks
(`hwf`). -/
theorem agree_at_convergence {lib : Lib} {code : Bell → Option Nomm} {tab : Tab} {G : Entry → Prop}
    (hr : ∀ e, G e → RunEntryP tab e) (hans : ∀ s f a, tab s f = some a → Answers G s f a)
    (hc : CodeIs code G) (hhas : CodeHas code G) (hwf : ∀ e, G e → WellFormed e.more)
    {e : Entry} (he : G e) {x : Noun} (hx : Fits e.d.less x) (gul : Noun) (t : Trace) (r : Tone) :
    Mink lib gul t x e.fol r ↔ ∃ m, nommF lib gul code m t x e.d.nomm = some r :=
  converged_agree (fun e he => (hr e he).run) hans hc hhas hwf (prodRel_of_converged hr hans hwf)
    he hx gul t r

end SkaModel
end Formalization
