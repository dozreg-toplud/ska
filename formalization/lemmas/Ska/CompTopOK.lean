import lemmas.Ska.CompEntry

/-!
# From `run` to the contract: the final pass of `+compile-scc-in`

`finish_compDone`: on the fragment `Frag`, what the model of the final pass
(`finish`) returns, entered as the interpreter enters a function, returns the
value of the nomm on every subject that has the axes the bell's cape says it
has, and crashes with the entry trace where the nomm crashes.
`finish_bellContract`: so it meets `BellContract` for its bell.

Two facts about the model are taken as explicit hypotheses, not yet proved:

* `RunDown nm`: the blocks that `run` makes for `%done` go down (each jumps
  only to labels below its own), and the entry block has no parameters.
* `CoerceSpec`: what `+coerce-lazy` puts in front of the entry block takes
  the input registers to the registers of the lazy need, or crashes, and it
  crashes only on a subject that has not the lazy need's shape and looks.

Nothing is baked (`bake ned = (ned, [])`): `+bake-need` is not modelled.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-! ## `+need-ord-alloc-regs` -/

theorem needOrdAllocRegs_spec : ∀ (ord : NeedOrd) (g g' : Gen Map) (ned : Need),
    needOrdAllocRegs ord g = some (ned, g') →
    (∃ k, g' = { g with re := k }) ∧ g.re ≤ g'.re ∧ Distinct ned ∧ ∀ r, NMem ned r → g.re ≤ r ∧ r < g'.re
  | NeedOrd.none, g, g', ned, h => by
    simp only [needOrdAllocRegs, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨⟨g.re, rfl⟩, Nat.le_refl _, trivial, fun r hr => hr.elim⟩
  | NeedOrd.this, g, g', ned, h => by
    simp only [needOrdAllocRegs, bind_apply, re_apply, pure_apply, Option.bind_some, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨⟨_, rfl⟩, Nat.le_succ _, trivial, fun r hr => by simp [NMem] at hr; subst hr; simp⟩
  | NeedOrd.pair p q, g, g', ned, h => by
    obtain ⟨hn, ga, h1, h⟩ := bind_some h
    obtain ⟨tn, gb, h2, h⟩ := bind_some h
    obtain ⟨⟨ka, rfl⟩, la, da, ma⟩ := needOrdAllocRegs_spec p _ _ _ h1
    obtain ⟨⟨kb, rfl⟩, lb, db, mb⟩ := needOrdAllocRegs_spec q _ _ _ h2
    split at h
    · cases h
    · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨⟨kb, rfl⟩, Nat.le_trans la lb, ⟨da, db, fun x hx hy => ?_⟩, fun r hr => ?_⟩
      · have := (ma x hx).2; have := (mb x hy).1; simp at *; omega
      · rcases hr with hr | hr
        · have := ma r hr; simp at *; omega
        · have := mb r hr; simp at *; omega
  | NeedOrd.both p q, g, g', ned, h => by
    obtain ⟨r0, g0', h0, h⟩ := bind_some h
    simp only [re_apply, Option.some.injEq, Prod.mk.injEq] at h0
    obtain ⟨rfl, rfl⟩ := h0
    obtain ⟨hn, ga, h1, h⟩ := bind_some h
    obtain ⟨tn, gb, h2, h⟩ := bind_some h
    obtain ⟨⟨ka, rfl⟩, la, da, ma⟩ := needOrdAllocRegs_spec p _ _ _ h1
    obtain ⟨⟨kb, rfl⟩, lb, db, mb⟩ := needOrdAllocRegs_spec q _ _ _ h2
    split at h
    · cases h
    · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨⟨kb, rfl⟩, by simp at la lb ⊢; omega, ⟨da, db, fun x hx hy => ?_, fun hx => ?_, fun hy => ?_⟩,
        fun r hr => ?_⟩
      · have := (ma x hx).2; have := (mb x hy).1; simp at *; omega
      · have := (ma _ hx).1; simp at *; omega
      · have := (mb _ hy).1; simp at *; omega
      · rcases hr with hr | hr | hr
        · subst hr; simp at la lb ⊢; omega
        · have := ma r hr; simp at *; omega
        · have := mb r hr; simp at *; omega

/-! ## The hypotheses -/

/-- **Assumed of `run`, not yet proved**: for `%done` from the initial
state, every block goes down and the entry block has no parameters. -/
def RunDown (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] (nm : Nomm) : Prop :=
  ∀ (nex : Next S) (g1 : Gen Map), run nm CGoal.done gen0 = some (nex, g1) →
    Down g1.blocks ∧ ∃ B fin, HoonMap.get g1.blocks nex.th.there = some ⟨[], B, fin⟩

/-- The subjects on which `+axe-in-less-cape` is right: those that have
every axis the cape says they have. -/
def CapeAxes (less : Cape) (s : Noun) : Prop :=
  ∀ axe, 1 ≤ axe → axeInCape axe less = true → (slot? axe s).isSome

/-- **Assumed of `+coerce-lazy`, not yet proved**: from registers that hold
the subject as the input need asks, the ops it puts in front of block `o`
reach registers that hold it as the lazy need asks, or crash with the trace
the block was entered with, and they crash only on a subject that has not
the lazy need's shape and looks. -/
def CoerceSpec (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] : Prop :=
  ∀ (ned : Need) (o : Nat) (laz : Sure S) (less : Cape) (g g' : Gen Map),
    coerceLazy ned o laz less g = some ((), g') → g.drop = false → Distinct ned → Distinct laz.ned →
    (∀ r, NMem laz.ned r → r < g.re) → (∀ r, NMem ned r → r < g.re) → (∀ r, NMem ned r → ¬ NMem laz.ned r) →
    ∃ A, Front o g g' A ∧ ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) gul st t (R : Map Noun) s,
      HoldsN ned R s → CapeAxes less s →
      (FitsS laz s → ∃ R', Runs lib O c gul st t A R R' ∧ HoldsS laz R' s) ∧
      (¬ FitsS laz s → Crashes lib O c gul st t A R)

/-! ## The final pass -/

/-- **What `+comp` establishes at the entry, on the subjects of `P`.** -/
def CompDoneOn (lib : Lib) (c : Straight Map) (nm : Nomm) (P : Noun → Prop) : Prop :=
  ∀ (σ : Type) (O : Oracle σ) (st : σ) (s : Noun) (args : List Noun) (t : Trace) (gul : Noun),
    P s → SkaModel.split c.need s = some args → execEntry lib O st c args t gul = some (pureTone t nm s, st)

theorem down_front {o : Nat} {g g' : Gen Map} {A B : List Pole} {fin : Termin} (hd : Down g.blocks)
    (hb : HoonMap.get g.blocks o = some ⟨[], B, fin⟩) (hf : Front o g g' A) : Down g'.blocks := by
  intro k b hk
  by_cases e : k = o
  · subst e; rw [hf.blk B fin hb] at hk; cases hk; exact hd _ ⟨[], B, fin⟩ hb
  · rw [hf.other k e] at hk; exact hd k b hk

/-- **The final pass meets the relation at the entry.** -/
theorem finish_compDone [HoonMapKeys Map] (lib : Lib) {nm : Nomm} (hf : Frag nm (CGoal.done : CGoal S))
    {ord : NeedOrd} {less : Cape} {bake : Need → Need × List (Nat × Noun)} {c' : Straight Map}
    (hbake : ∀ ned, bake ned = (ned, [])) (hdown : RunDown S Map nm) (hco : CoerceSpec S Map)
    (h : finish (S := S) nm ord less bake = some c') : CompDoneOn lib c' nm (CapeAxes less) := by
  unfold finish at h
  obtain ⟨⟨nex, g1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
  simp only at h
  split at h
  · cases h
  rename_i hargs
  simp only [ne_eq, Decidable.not_not] at hargs
  obtain ⟨⟨nedF, g2⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [hbake, List.map_nil] at h
  obtain ⟨⟨u3, g3⟩, h3, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨u4, g4⟩, h4, h5⟩ := Option.bind_eq_some_iff.mp h
  have hr := run_ok lib nm CGoal.done gen0 g1 nex hf trivial h1
  have hd1 : g1.drop = false := hr.ext.2.2.1
  obtain ⟨⟨k2, rfl⟩, l2, dist2, mem2⟩ := needOrdAllocRegs_spec ord g1 _ nedF h2
  obtain ⟨hdn, B, fin, hB⟩ := hdown nex g1 h1
  have hlaz : ∀ r, NMem nex.laz.ned r → r < g1.re := fun r hr' => by
    rcases hr.regs r hr' with hg | hg
    · exact hg.elim
    · exact hg.2
  obtain ⟨A, hfr, hsem⟩ := hco nedF nex.th.there nex.laz less _ g3 h3 hd1 dist2 hr.dist
    (fun r hr' => Nat.lt_of_lt_of_le (hlaz r hr') l2) (fun r hr' => (mem2 r hr').2)
    (fun r hr' hl => by have := (mem2 r hr').1; have := hlaz r hl; simp at *; omega)
  have hfr4 := hfr.trans (front_addOps h4 (by rw [hfr.drop]; exact hd1))
  simp only [List.nil_append] at hfr4
  have hB2 : HoonMap.get ({ g1 with re := k2 } : Gen Map).blocks nex.th.there = some ⟨[], B, fin⟩ := hB
  have hd4 := down_front (g := { g1 with re := k2 }) hdn hB2 hfr4
  have hB4 := hfr4.blk B fin hB2
  let c1 : Straight Map := ⟨NeedOrd.none, 0, HoonMap.put g4.blocks nex.th.there ⟨[], B, fin⟩⟩
  have hc1o : HoonMap.get c1.blocks nex.th.there = some ⟨[], B, fin⟩ := by simp [c1, HoonMap.get_put]
  have hag : ∀ k, k ≠ nex.th.there → HoonMap.get c1.blocks k = HoonMap.get g4.blocks k := fun k hk => by
    simp [c1, HoonMap.get_put, hk]
  have hd1' : Down c1.blocks := by
    intro k b hk
    by_cases e : k = nex.th.there
    · subst e; rw [hc1o] at hk; cases hk; exact hdn _ _ hB
    · rw [hag k e] at hk; exact hd4 k b hk
  obtain ⟨hneed, start, hst, hent⟩ := toStraight_entry h5 hd4 hd1' hag
  rw [hB4] at hst; cases hst
  intro σ O st s args t gul hP hsp
  obtain ⟨R, hR, he⟩ := hent lib O st s args t gul hsp
  rw [he]
  have hagree : Agree c1 gen0 g1 := fun k _ hk => by
    by_cases e : k = nex.th.there
    · subst e; rw [hc1o, hB]
    · rw [hag k e, hfr4.other k e]
  have hj : nex.th = jmp0 nex.th.there := by
    rcases hth : nex.th with ⟨args', there⟩; rw [hth] at hargs; simp at hargs; subst hargs; rfl
  obtain ⟨hfit, hcr⟩ := hsem lib σ O c1 gul st t R s hR hP
  by_cases hfs : FitsS nex.laz s
  · obtain ⟨R', hruns, hhold⟩ := hfit hfs
    rw [hruns]
    have := hr.sem (by rfl) c1 hagree σ O st s R' t gul hhold
    simp only [GoalSem] at this
    rw [hj, goJ_jmp0 _ _ _ _ hc1o] at this
    exact this
  · rw [show A ++ B = A ++ B from rfl, hcr hfs]
    rcases hr.nec s hfs with hn | ⟨p, _, hg⟩
    · simp [pureTone, hn, toneOf]
    · exact hg.elim

/-! ## The contract -/

/-- A cape in which no cell knows nothing (`[| |]` is normalized to `|`). -/
def CapeNorm : Cape → Prop
  | Cape.cell h t => (h.isNo && t.isNo) = false ∧ CapeNorm h ∧ CapeNorm t
  | _ => True

theorem axeInCape_cell {axe : Nat} (h2 : 2 ≤ axe) (h t : Cape) :
    axeInCape axe (Cape.cell h t) = if cap axe = 2 then axeInCape (mas axe) h else axeInCape (mas axe) t := by
  rw [axeInCape]; simp [show ¬ axe ≤ 1 by omega]

theorem axeInCape_yes {axe : Nat} (h2 : 2 ≤ axe) : axeInCape axe Cape.yes = false := by
  rw [axeInCape]; simp [show ¬ axe ≤ 1 by omega]; intro h t e; cases e

theorem axeInCape_no {axe : Nat} (h2 : 2 ≤ axe) : axeInCape axe Cape.no = false := by
  rw [axeInCape]; simp [show ¬ axe ≤ 1 by omega]; intro h t e; cases e

theorem capeAxes_of_fits : ∀ (axe : Nat), 1 ≤ axe → ∀ (c : Cape) (d s : Noun), CapeNorm c → FitsCape c d s →
    axeInCape axe c = true → (slot? axe s).isSome := by
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
    intro h1 c d s hn hf ha
    by_cases e : axe = 1
    · subst e; simp [slot?_one]
    have h2 : 2 ≤ axe := by omega
    cases c with
    | yes => rw [axeInCape_yes h2] at ha; cases ha
    | no => rw [axeInCape_no h2] at ha; cases ha
    | cell ch ct =>
      rw [axeInCape_cell h2] at ha
      rcases hf with hno | ⟨dh, dt, nh, nt, rfl, rfl, fh, ft⟩
      · rw [hn.1] at hno; cases hno
      rw [slot?_cap h2]
      rcases cap_cases _ h2 with hc | hc
      · simp only [hc, if_true] at ha ⊢
        exact ih _ (mas_lt axe h2) (mas_pos axe h2) ch dh nh hn.2.1 fh ha
      · simp only [hc, show (3 : Nat) ≠ 2 by decide, if_false] at ha ⊢
        exact ih _ (mas_lt axe h2) (mas_pos axe h2) ct dt nt hn.2.2 ft ha

theorem bellContract_of_compDoneOn {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {b : Bell} {nm : Nomm} (hp : nm.pure = true) (hA : Annot lib code (SkaModel.Fits b.less) b.fol nm)
    {c : Straight Map} (hc : CompDoneOn lib c nm (SkaModel.Fits b.less)) (N : Needs) :
    BellContract lib N b false c := by
  intro s hs args hargs
  have hargs' : SkaModel.split c.need s = some args := by simpa using hargs
  refine ⟨?_, ?_⟩
  · intro σ Inv ν O n gul ti tm r _ _ _ hm st _ htr
    have e := (mink_pure hok hp hA hs gul tm r).mp ⟨n, hm⟩
    subst e
    exact ⟨pureTone ti nm s, st, hc σ O st s args ti gul hs hargs', toneRel_pureTone htr nm s⟩
  · intro σ Inv ν O gul ti tm _ _ _ st ton st' _ htr hrun
    rw [hc σ O st s args ti gul hs hargs'] at hrun
    cases hrun
    exact ⟨pureTone tm nm s, (mink_pure hok hp hA hs gul tm _).mpr rfl, toneRel_pureTone htr nm s⟩

/-- **The final pass meets the contract** of its bell, on the fragment,
for every shape `ord` for which it does not crash, when nothing is baked,
under `RunDown` and `CoerceSpec`. -/
theorem finish_bellContract [HoonMapKeys Map] {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {b : Bell} {nm : Nomm} (hp : nm.pure = true) (hA : Annot lib code (SkaModel.Fits b.less) b.fol nm)
    (hf : Frag nm (CGoal.done : CGoal S)) {cape : Cape} {data : Noun} (hb : b.less = Sock.mk cape data)
    (hn : CapeNorm cape) {ord : NeedOrd} {bake : Need → Need × List (Nat × Noun)}
    (hbake : ∀ ned, bake ned = (ned, [])) (hdown : RunDown S Map nm) (hco : CoerceSpec S Map)
    {c' : Straight Map} (h : finish (S := S) nm ord cape bake = some c') (N : Needs) :
    BellContract lib N b false c' := by
  have hc := finish_compDone lib hf hbake hdown hco h
  refine bellContract_of_compDoneOn hok hp hA (fun σ O st s args t gul hs hsp => ?_) N
  rw [hb] at hs
  exact hc σ O st s args t gul (fun axe h1 ha => capeAxes_of_fits axe h1 cape data s hn hs ha) hsp

end Comp
end SkaModel
end Formalization
