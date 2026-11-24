import lemmas.Ska.CompKernW

/-!
# The indirect call under a goal with entries: `kerfLC`

README Gaps 12.20.  Under `%next L th` with entries (the bond goal of `+past`
behind a calling tail, the forks of a `%6`), the indirect call's `+kerf`
puts `+kern`'s ops from the call's product register `pro` in front of every
lazy block of `L` (the block `out` for `L`'s sure part, a proxy for `pro` at
each entry), and the rest of the call is the inner run into `out` with the
product in `pro`.  So the call meets `RunOKLC` with the witness `kernWit
pro`: `d = this pro` holding the product.  In `%cc2` (`CompRunOKLC.lean`)
the head call's `+kern` puts `mov v7 v2` at the bond block `3`, and `v7` is
its `pro`.

* `kop_ren`, `poleWr_ren`, `kernPW_fill`: the ops of `KernPW` unproxied fill
  the need from `pro` and write nothing outside `pro`, the need and the walk's
  range.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

theorem kop_ren (u : Nat → Nat) : ∀ {p : Pole}, KOp p → KOp (renPole u p)
  | Pole.mov _ _, _ => trivial
  | Pole.hed _ _, _ => trivial
  | Pole.tal _ _, _ => trivial
  | Pole.cel _, _ => trivial

theorem poleWr_ren (u : Nat → Nat) : ∀ {p : Pole}, KOp p → ∀ {x : Nat}, x ∈ poleWr (renPole u p) →
    ∃ y ∈ poleRegs p, x = u y
  | Pole.mov s d, _, x, hx => by
    simp only [renPole, poleWr, List.mem_singleton] at hx
    exact ⟨d, by simp [poleRegs], hx⟩
  | Pole.hed s d, _, x, hx => by
    simp only [renPole, poleWr, List.mem_singleton] at hx
    exact ⟨d, by simp [poleRegs], hx⟩
  | Pole.tal s d, _, x, hx => by
    simp only [renPole, poleWr, List.mem_singleton] at hx
    exact ⟨d, by simp [poleRegs], hx⟩
  | Pole.cel p, _, x, hx => by simp [renPole, poleWr] at hx

/-- **The ops of `KernPW` unproxied by a later `cond`**: from registers where
`r` holds `v`, they fill the need for `v` (or crash), keep every register
below the range's start outside the need, and keep every register above the
range but `r` outside the need. -/
theorem kernPW_fill {r : Nat} {cond cf : Map (Nat × List Nat)} {lo hi o : Nat} {sur : Sure S} {A : List Pole}
    (h : KernPW (Map := Map) r cond lo hi o sur A) (hrlo : r < lo) (dist : Distinct sur.ned)
    (hlt : ∀ x, NMem sur.ned x → x < r) (hr : HoonMap.get cf r = Option.none)
    (hs : ∀ x, NMem sur.ned x → HoonMap.get cf x = Option.none)
    (hagree : ∀ x, x < hi → HoonMap.get cf x = HoonMap.get cond x)
    (hrange : ∀ x, lo ≤ x → x < hi → unproxy cf x = x ∨ unproxy cf x = r)
    (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
    (R : Map (Option Noun)) (v : Noun) (hv : SkaModel.read r R = some v) :
    (FitsS sur v → ∃ R', Runs lib O c gul st t (A.map (renPole (unproxy cf))) R R' ∧ HoldsS sur R' v ∧
      ∀ x, (x < lo ∨ (hi ≤ x ∧ x ≠ r)) → ¬ NMem sur.ned x → SkaModel.read x R' = SkaModel.read x R) ∧
    (¬ FitsS sur v → Crashes lib O c gul st t (A.map (renPole (unproxy cf))) R) := by
  obtain ⟨⟨lo0, hi0, l0, h0, src, hsrc, hk, hsem⟩, kop, rin⟩ := h
  have KS := hsem (by omega) dist hlt (unproxy cf) (unproxy_none hr) (fun x hx => unproxy_none (hs x hx))
    (fun x hx => by simp only [unproxy, hagree x (by omega)])
  obtain ⟨S1, S2⟩ := KS lib σ O c gul st t R v hv
  refine ⟨fun f => ?_, S2⟩
  obtain ⟨R', hr', hh, hk'⟩ := S1 f
  refine ⟨R', hr', hh, fun x hx hn => ?_⟩
  rcases hx with hx | ⟨hx1, hx2⟩
  · exact hk' x (by omega) hn
  · refine runs_keep _ R R' (fun p hp => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact kop_ren _ (kop q hq)) hr' x (fun p hp hw => ?_)
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨y, hy, rfl⟩ := poleWr_ren _ (kop q hq) hw
    rcases rin q hq y hy with e | e | ⟨a, b⟩
    · subst e; exact hx2 (unproxy_none hr)
    · rw [unproxy_none (hs y e)] at hn hx1; exact hn e
    · rcases hrange y a b with e | e
      · rw [e] at hx1; omega
      · exact hx2 e


/-! ## The inner run of the call -/

/-- `OutGoal` of the goal `%next (lazy-from-reg pro) (jmp0 out)` itself. -/
theorem outGoal_self {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {Inv : σ → Prop}
    {ν : σ → Needs} {K : Nat → Prop} {pro out : Nat} :
    OutGoal lib O c gul Inv ν K pro out (CGoal.next (lazyReg pro : Sure S) (jmp0 out)) :=
  fun st regs ti tm p hI htr hp => ⟨fun _ => ⟨st, regs, hI, Needs.le_refl _, hp, fun _ _ => rfl, rfl⟩,
    fun nf => absurd (fitsS_lazyReg pro p) nf⟩

/-- **The call after `+kerf`**: from the state after `+kerf` (`pro`, `out`
made), the `%nok` block, the formula part (behind `+past` when the subject
part is hinted) and the subject part meet `RunOKGC` under `%next
(lazy-from-reg pro) (jmp0 out)`: `pairLC_ok` with `outGoal_self`. -/
theorem indirectC_inner (lib : Lib) {p q : Nomm} {env : CallEnv} {P : Noun → Prop} {f fb fc : Noun}
    (Up : UOKC (S := S) (Map := Map) lib env P fb p) (Uq : UOKC (S := S) (Map := Map) lib env P fc q)
    (M : MinkC2 lib P f fb fc) (hcount : sixCount p + sixCount q ≤ 255) {sup : Option Nomm}
    {region : List Nat} {g2 g' : Gen Map} {nex : NextL S} {out pro : Nat}
    (hpro : pro < g2.re) (ho1 : 1 ≤ out) (ho2 : out < g2.bo) (hpk : HoonMap.get g2.cond pro = Option.none)
    (b2 : 1 ≤ g2.bo) (d2 : g2.drop = false) (u2 : UpBelow g2) (cl2 : Clear g2) (cb2 : CondBelow g2)
    {o : Nat} {g3 g4 g5 g6 : Gen Map} {nexF nexF' nexS : NextL S}
    (h3 : emit ⟨[], [Pole.nok g2.re (g2.re + 1) pro], Termin.hop (jmp0 out)⟩
        { { g2 with re := g2.re + 1 } with re := g2.re + 1 + 1 } = some (o, g3))
    (h4 : runLC env sup q (CGoalL.next (ofSure (lazyReg (g2.re + 1))) (jmp0 o)) region g3 = some (nexF, g4))
    (h5 : pastL env.cod nexF p region g4 = some (nexF', g5))
    (h6 : runLC env sup p (CGoalL.next (ofSure (lazyReg g2.re)) nexF'.th) region g5 = some (nexS, g6))
    (h7 : copyL nexS nexF'.laz g6 = some (nex, g')) :
    RunOKGC lib P f (CGoal.next (lazyReg pro : Sure S) (jmp0 out)) g2 g' nex ∧ g2.bo ≤ nex.th.there := by
  rw [emit_apply] at h3
  simp only [Option.some.injEq, Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  have nk : ∀ x, g2.re ≤ x → HoonMap.get g2.cond x = Option.none := fun x hx => condBelow_none cb2 hx
  have eb3 : ∀ k, HoonMap.get ({ { g2 with re := g2.re + 1 } with re := g2.re + 1 + 1 }.emitted
      ⟨[], [Pole.nok g2.re (g2.re + 1) pro], Termin.hop (jmp0 out)⟩).blocks k =
      if k = g2.bo then some ⟨[], [Pole.nok g2.re (g2.re + 1) pro], Termin.hop (jmp0 out)⟩ else
        HoonMap.get g2.blocks k := fun k => by
    simp only [Gen.emitted, d2, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]
  have G0 := growU_emit (g := { { g2 with re := g2.re + 1 } with re := g2.re + 1 + 1 })
    (b := ⟨[], [Pole.nok g2.re (g2.re + 1) pro], Termin.hop (jmp0 out)⟩)
    (fun j hj => by
      simp only [finJumps, List.mem_singleton] at hj; subst hj; simp only [jmp0]; exact ⟨ho1, ho2⟩) u2
  have G3 : GrowU g2 ({ { g2 with re := g2.re + 1 } with re := g2.re + 1 + 1 }.emitted
      ⟨[], [Pole.nok g2.re (g2.re + 1) pro], Termin.hop (jmp0 out)⟩) := ⟨G0.bo, G0.drop, G0.keep, G0.new⟩
  generalize hg3 : ({ { g2 with re := g2.re + 1 } with re := g2.re + 1 + 1 }.emitted
      ⟨[], [Pole.nok g2.re (g2.re + 1) pro], Termin.hop (jmp0 out)⟩ : Gen Map) = g3 at G3 eb3 h4
  have r3 : g3.re = g2.re + 2 := by rw [← hg3]; simp [Gen.emitted]
  have b3 : g3.bo = g2.bo + 1 := by rw [← hg3]; simp [Gen.emitted]
  have d3 : g3.drop = false := by rw [← hg3]; simp [Gen.emitted, d2]
  have cn3 : g3.cond = g2.cond := by rw [← hg3]; simp [Gen.emitted]
  have k3o : HoonMap.get g3.blocks g2.bo = some ⟨[], [Pole.nok g2.re (g2.re + 1) pro], Termin.hop (jmp0 out)⟩ := by
    rw [eb3, if_pos rfl]
  have E3 : Ext g2 g3 := ⟨by omega, by omega, by rw [d3, d2], fun k hk => by rw [eb3, if_neg (by omega)]⟩
  have u3 : UpBelow g3 := G3.up u2
  have cl3 : Clear g3 := cl2.growU G3
  have cb3 : CondBelow g3 := fun k hk => by rw [cn3] at hk; have := cb2 k hk; omega
  have hc : sixCount p ≤ 255 ∧ sixCount q ≤ 255 := ⟨by omega, by omega⟩
  have Rq := Uq.run (sup := sup) (goal := CGoal.next (lazyReg (g2.re + 1)) (jmp0 g2.bo)) (region := region)
    trivial rfl ⟨by simp only [jmp0]; omega, by simp only [jmp0]; omega⟩
    ⟨trivial, fun r hr => by simp only [lazyReg, NMem] at hr; subst hr; omega⟩ trivial hc.2 (by omega) d3 u3
    cl3 cb3 (fun r hr => by simp only [lazyReg, NMem] at hr; subst hr; rw [cn3]; exact nk _ (by omega)) h4
  have cq := Uq.clean (goal := CGoal.next (lazyReg (g2.re + 1)) (jmp0 g2.bo)) trivial trivial h4
  obtain ⟨T, hhd, cq', -⟩ := tailGC_of_past Up Rq cq
    (fun r hr => by simp only [lazyReg, NMem] at hr; subst hr; omega) (Rq.ext.2.2.1.trans d3) (Rq.grow.up u3) h5
  have Rp := Up.run (sup := sup) (goal := CGoal.next (lazyReg g2.re) nexF'.th) (region := region) trivial
    (nextArgs_nil T.ent rfl) ⟨T.lo, T.hi⟩
    ⟨trivial, fun r hr => by simp only [lazyReg, NMem] at hr; subst hr; have := T.ext.1; omega⟩ trivial hc.1
    (by have := T.lo; have := T.hi; omega) (T.ext.2.2.1.trans d3) (T.grow.up u3) (cl3.growU T.grow)
    (T.cfr.below cb3)
    (fun r hr => by
      simp only [lazyReg, NMem] at hr; subst hr
      rw [T.cfr.get_lt (by omega), cn3]; exact nk _ (by omega)) h6
  have cp := Up.clean (goal := CGoal.next (lazyReg g2.re) nexF'.th) trivial trivial h6
  have hfix : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g3.re → HoonMap.get cf k = HoonMap.get g2.cond k) →
      ∀ k, g2.bo ≤ k → k < g3.bo → (HoonMap.get g3.blocks k).map (unproxyBlob cf) = HoonMap.get g3.blocks k := by
    intro cf hcf k h0 h1'
    obtain rfl : k = g2.bo := by omega
    rw [k3o]
    simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, List.map_cons, renPole, renFin,
      renJmp_nil _ (show (jmp0 out).args = [] from rfl)]
    rw [unproxy_none (by rw [hcf _ (by omega)]; exact nk _ (by omega)),
      unproxy_none (by rw [hcf _ (by omega)]; exact nk _ (by omega)),
      unproxy_none (by rw [hcf _ (by omega)]; exact hpk)]
  have hbN : ∀ (c : Straight Map), Agree c g2 g3 → HoonMap.get c.blocks g2.bo =
      some ⟨[], [Pole.nok g2.re (g2.re + 1) pro], Termin.hop (jmp0 out)⟩ := fun c agc => by
    rw [agc g2.bo (Nat.le_refl _) (by omega)]; exact k3o
  have hKp : ∀ z, Keep g2 g3 (CGoal.next (lazyReg pro : Sure S) (jmp0 out)) z → z ≠ pro := fun z hz e => by
    subst e; exact hz.2 rfl
  have nfit : ∀ (x y : Noun), ¬ (¬ FitsS (lazyReg g2.re : Sure S) x ∨ ¬ FitsS (lazyReg (g2.re + 1) : Sure S) y) :=
    fun x y h => h.elim (fun h => h (fitsS_lazyReg _ x)) (fun h => h (fitsS_lazyReg _ y))
  exact pairLC_ok (Fin := fun gul n' tm x y r => minkF lib gul n' tm x y = some r)
    (FinB := fun gul tm x y r => Mink lib gul tm x y r) (fun hs hm => M.fwd hs hm) (fun hs hb => M.bwd hs hb)
    ⟨trivial, fun r hr => by simp only [lazyReg, NMem] at hr; subst hr; exact hpro⟩ E3 G3 cn3 cb2
    (fun r hr => by simp only [lazyReg, NMem] at hr; subst hr; exact Or.inr ⟨by omega, by omega⟩)
    (fun r hr => by simp only [lazyReg, NMem] at hr; subst hr; exact Or.inr ⟨by omega, by omega⟩)
    (fun r h1' h2' => by simp only [lazyReg, NMem] at h1' h2'; omega)
    (Ext.refl g3) (GrowU.refl g3) rfl rfl
    (Or.inl ⟨rfl, rfl, Or.inl (fun x => fitsS_lazyReg _ x)⟩) hhd T (RunOKGC.toLC Rp) cq' cp h7 u2 d2 hfix
    (fun _ _ _ x y _ hn _ => absurd hn (nfit x y)) (fun _ _ x y hn => absurd hn (nfit x y))
    (fun c agc σ Inv ν O n gul hS hF st regs t tm x y n' r hn' hI htr _ _ hx hy hfin =>
      nokStep_fwd hS hF (hbN c agc) hKp outGoal_self hI htr hx hy hn' hfin)
    (fun c agc σ Inv ν O gul hS hB st regs t tm x y hI htr _ _ hx hy res hres =>
      nokStep_bwd hS hB (hbN c agc) hKp outGoal_self hI htr hx hy hres)

/-! ## `+kerf` under a goal with entries -/

/-- **The witness of a call under a goal with entries**: `+kern`'s register
holding the product. -/
def kernWit (pro : Nat) : Wit := fun _ v d w => d = Need.this pro ∧ w = v

/-- **`+kerf` under `%next L th`**: the block `out = bo` with `+kern`'s ops
for `L`'s sure part in front of `hop th`, `pro = re`, the ops of `KernPW` in
front of every entry's block, proxies for `pro` only, and the state grown. -/
theorem kerf_specL {L : Lazy S} {th : Jmp} {g0 g2 : Gen Map} {out pro : Nat}
    (hk : kerf (⟨L, th⟩ : NextL S) g0 = some ((out, pro), g2)) (d0 : g0.drop = false) (hcb : CondBelow g0)
    (hu : UpBelow g0) (h1 : 1 ≤ th.there) (h2 : th.there < g0.bo)
    (hlab : ∀ e ∈ entries L, e.1 < g0.bo ∧ ∃ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩)
    (hnd : ((entries L).map Prod.fst).Nodup) :
    out = g0.bo ∧ pro = g0.re ∧ g2.bo = g0.bo + 1 ∧ g2.drop = g0.drop ∧ g0.re + 1 ≤ g2.re ∧
    ProxyFor g0.re g0 g2 ∧ GrowU g0 g2 ∧
    (∃ A, HoonMap.get g2.blocks g0.bo = some ⟨[], A, Termin.hop th⟩ ∧
      KernPW (Map := Map) g0.re g2.cond (g0.re + 1) g2.re g0.bo L.sure A) ∧
    (∀ e ∈ entries L, ∃ A, (∀ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩ →
      HoonMap.get g2.blocks e.1 = some ⟨[], A ++ B, fin⟩) ∧
      KernPW (Map := Map) g0.re g2.cond (g0.re + 1) g2.re e.1 e.2.sure A) ∧
    (∀ k, k < g0.bo → k ∉ (entries L).map Prod.fst → HoonMap.get g2.blocks k = HoonMap.get g0.blocks k) ∧
    HoonMap.get g2.cond g0.re = Option.none ∧
    (∀ k, g0.re ≤ k → HoonMap.get g2.cond k = Option.none ∨ ∃ tag, HoonMap.get g2.cond k = some (g0.re, tag)) := by
  unfold kerf at hk
  obtain ⟨o', ge, he, hk⟩ := bind_some hk
  rw [emit_apply] at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨r, g4, h3, h4⟩ := bind_some hk
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
  have eblk : ∀ k, HoonMap.get (g0.emitted ⟨[], [], Termin.hop th⟩).blocks k =
      if k = g0.bo then some ⟨[], [], Termin.hop th⟩ else HoonMap.get g0.blocks k := fun k => by
    simp only [Gen.emitted, d0, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]
  have hn : (((g0.bo, L) :: entries L).map Prod.fst).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    exact ⟨fun hm => by obtain ⟨e, he, e1⟩ := List.mem_map.mp hm; have := (hlab e he).1; omega, hnd⟩
  have cbe : CondBelow (g0.emitted ⟨[], [], Termin.hop th⟩) := hcb
  obtain ⟨hr, W⟩ := kern_specW h3 d0 cbe hn
  simp only [Gen.emitted] at hr
  subst hr
  have wbo := W.bo
  have wdr := W.drop
  have wle := W.le
  simp only [Gen.emitted] at wbo wdr wle
  obtain ⟨A0, hA0, P0⟩ := W.at_ (g0.bo, L) List.mem_cons_self
  have hB0 : HoonMap.get g4.blocks g0.bo = some ⟨[], A0, Termin.hop th⟩ := by
    have := hA0 [] (Termin.hop th) (by simp only [eblk]; simp [Gen.emitted])
    simpa using this
  have hE : ∀ e ∈ entries L, ∃ A, (∀ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩ →
      HoonMap.get g4.blocks e.1 = some ⟨[], A ++ B, fin⟩) ∧
      KernPW (Map := Map) g0.re g4.cond (g0.re + 1) g4.re e.1 e.2.sure A := fun e he => by
    obtain ⟨A, hA, P⟩ := W.at_ e (List.mem_cons_of_mem _ he)
    refine ⟨A, fun B fin hb => hA B fin (by
      have ne : e.1 ≠ g0.bo := by have := (hlab e he).1; omega
      simp only [Gen.emitted, d0, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put, ne]; exact hb), ?_⟩
    simpa [Gen.emitted] using P
  have hO : ∀ k, k ≠ g0.bo → k ∉ (entries L).map Prod.fst → HoonMap.get g4.blocks k = HoonMap.get g0.blocks k := by
    intro k k1 k2
    rw [W.other k (by simp only [List.map_cons, List.mem_cons, not_or]; exact ⟨k1, k2⟩)]
    simp only [Gen.emitted, d0, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put, k1]
  have PF : ProxyFor g0.re g0 g4 := by
    have := W.cnd
    exact ⟨⟨by omega, fun k => by
      rcases this.1.2 k with e | e
      · exact Or.inl (by simpa [Gen.emitted] using e)
      · exact Or.inr ⟨by simp [Gen.emitted] at e; omega, e.2⟩⟩, fun k hk => this.2 k (by simpa [Gen.emitted] using hk)⟩
  have Ge := growU_emit (g := g0) (b := ⟨[], [], Termin.hop th⟩) (fun j hj => by
    simp only [finJumps, List.mem_singleton] at hj; subst hj; exact ⟨h1, h2⟩) hu
  have G4 : GrowU (g0.emitted ⟨[], [], Termin.hop th⟩) g4 := by
    refine ⟨by simp only [Gen.emitted]; omega, by simp only [Gen.emitted] at wdr ⊢; exact wdr,
      fun k b hk hb => ?_, fun k b' hb' => Or.inl ?_⟩
    · by_cases e0 : k = g0.bo
      · subst e0; rw [eblk, if_pos rfl] at hb; cases hb; exact ⟨_, hB0, rfl, rfl⟩
      · rw [eblk, if_neg e0] at hb
        by_cases e1 : k ∈ (entries L).map Prod.fst
        · obtain ⟨e, he, rfl⟩ := List.mem_map.mp e1
          obtain ⟨B, fin, hb0⟩ := (hlab e he).2
          rw [hb0] at hb; cases hb
          obtain ⟨A, hA, _⟩ := hE e he
          exact ⟨_, hA B fin hb0, rfl, rfl⟩
        · exact ⟨b, by rw [hO k e0 e1]; exact hb, rfl, rfl⟩
    · by_cases e0 : k = g0.bo
      · subst e0; rw [hB0] at hb'; cases hb'; exact ⟨⟨[], [], Termin.hop th⟩, by rw [eblk, if_pos rfl], rfl, rfl⟩
      · by_cases e1 : k ∈ (entries L).map Prod.fst
        · obtain ⟨e, he, rfl⟩ := List.mem_map.mp e1
          obtain ⟨B, fin, hb0⟩ := (hlab e he).2
          obtain ⟨A, hA, _⟩ := hE e he
          rw [hA B fin hb0] at hb'; cases hb'
          exact ⟨⟨[], B, fin⟩, by rw [eblk, if_neg e0]; exact hb0, rfl, rfl⟩
        · exact ⟨b', by rw [eblk, if_neg e0, ← hO k e0 e1]; exact hb', rfl, rfl⟩
  have c0 : HoonMap.get g4.cond g0.re = Option.none := by
    have := W.cnd.get_lt (k := g0.re) (by simp [Gen.emitted])
    rw [this]; exact condBelow_none hcb (Nat.le_refl _)
  refine ⟨rfl, rfl, by omega, by simpa [Gen.emitted] using wdr, by omega, PF, Ge.trans G4,
    ⟨A0, hB0, by simpa [Gen.emitted] using P0⟩, hE, fun k hk hn' => hO k (by omega) hn', c0, fun k hk => ?_⟩
  by_cases e : HoonMap.get g4.cond k = HoonMap.get g0.cond k
  · exact Or.inl (by rw [e]; exact condBelow_none hcb hk)
  · exact Or.inr (PF.2 k e)

/-- **The indirect call's `+kerf` under a goal with entries meets
`RunOKLC`**, with the witness `kernWit pro`, from the inner run's `RunOKGC`
under `%next (lazy-from-reg pro) (jmp0 out)`: the block `out` fills `L`'s
sure part from `pro` and keeps `pro`, and the ops in front of each entry's
block fill the entry's need from `pro` (`kernPW_fill`). -/
theorem kerfLC {lib : Lib} {P : Noun → Prop} {f : Noun} {L : Lazy S} {th : Jmp} {g0 g2 g' : Gen Map}
    {out pro : Nat} {nex : NextL S}
    (hk : kerf (⟨L, th⟩ : NextL S) g0 = some ((out, pro), g2)) (d0 : g0.drop = false) (hcb : CondBelow g0)
    (hu : UpBelow g0) (hth : th.args = []) (h1 : 1 ≤ th.there) (h2 : th.there < g0.bo)
    (hsd : Distinct L.sure.ned)
    (hsl : ∀ x, NMem L.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none)
    (hlab : ∀ e ∈ entries L, e.1 < g0.bo ∧ ∃ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩)
    (hnd : ((entries L).map Prod.fst).Nodup)
    (hed : ∀ e ∈ entries L, Distinct e.2.sure.ned ∧
      ∀ x, NMem e.2.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none)
    (R : RunOKGC lib P f (CGoal.next (lazyReg pro : Sure S) (jmp0 out)) g2 g' nex) :
    RunOKLC (Map := Map) lib P f L th (kernWit pro) g0 g' nex := by
  obtain ⟨rfl, rfl, b2, dr2, l2, PF, G2, ⟨A0, hB0, P0⟩, hE, hO, c0, crng⟩ := kerf_specL hk d0 hcb hu h1 h2 hlab hnd
  have Re := R.ext
  have rl := R.ext.1
  have bl := R.ext.2.1
  have lab' : ∀ e ∈ entries nex.laz, g2.bo ≤ e.1 := fun e he => (R.labs e he).1
  -- the later `cond`s
  have hcf2 : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g'.cond k) →
      ∀ x, x < g2.re → HoonMap.get cf x = HoonMap.get g2.cond x := fun cf hcf x hx =>
    (hcf x (by omega)).trans (R.cfr.get_lt hx)
  have hfill : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g'.cond k) →
      ∀ {sur : Sure S} {A : List Pole} {o : Nat}, KernPW (Map := Map) g0.re g2.cond (g0.re + 1) g2.re o sur A →
      Distinct sur.ned → (∀ x, NMem sur.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) →
      ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
        (R : Map (Option Noun)) (v : Noun), SkaModel.read g0.re R = some v →
      (FitsS sur v → ∃ R', Runs lib O c gul st t (A.map (renPole (unproxy cf))) R R' ∧ HoldsS sur R' v ∧
        ∀ x, (x < g0.re + 1 ∨ (g2.re ≤ x ∧ x ≠ g0.re)) → ¬ NMem sur.ned x →
          SkaModel.read x R' = SkaModel.read x R) ∧
      (¬ FitsS sur v → Crashes lib O c gul st t (A.map (renPole (unproxy cf))) R) :=
    fun cf hcf sur A o KP hd hsl' => kernPW_fill KP (by omega) hd (fun x hx => (hsl' x hx).1)
      (by rw [hcf2 cf hcf _ (by omega)]; exact c0)
      (fun x hx => by rw [hcf2 cf hcf _ (by have := (hsl' x hx).1; omega), PF.get_lt (hsl' x hx).1]; exact (hsl' x hx).2)
      (hcf2 cf hcf)
      (fun x a b => by
        rcases crng x (by omega) with e | ⟨tag, e⟩
        · exact Or.inl (unproxy_none (by rw [hcf2 cf hcf x b]; exact e))
        · exact Or.inr (by simp only [unproxy, hcf2 cf hcf x b, e]))
  -- the shared part of the two `sem` clauses: through the block `out`
  have conv : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g'.cond k) →
      ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) (gul : Noun)
        (st : σ) (t tm : Trace) (s0 s : Noun) (regs : Map (Option Noun)),
      (∀ st' : σ, AgreeL lib O c gul st' t cf ned g0 g' nex.laz s0 s) → (∀ x, NMem ned x → g'.re ≤ x) →
      Forall2 (FrameRel lib (ν st)) t tm → ∀ r,
      GoalSemCM lib O c gul Inv ν (fun x => (x < g2.re ∨ NMem ned x) ∧ ¬ GMem (CGoal.next (lazyReg g0.re : Sure S)
        (jmp0 g0.bo)) x) st regs t tm nex.th (CGoal.next (lazyReg g0.re : Sure S) (jmp0 g0.bo)) r →
      GoalSemCMD lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ NMem L.sure.ned x) st regs t tm nex.th
        L.sure th (kernWit g0.re s) r := by
    intro cf hcf c ned σ Inv ν O gul st t tm s0 s regs ag hned htr r G
    have hbo : HoonMap.get c.blocks g0.bo = some ⟨[], A0.map (renPole (unproxy cf)), Termin.hop th⟩ := by
      rw [(ag st).1 g0.bo (Nat.le_refl _) (by omega) (fun hm => by
        obtain ⟨e, he, e1⟩ := List.mem_map.mp hm; have := lab' e he; omega), Re.2.2.2 _ (by omega), hB0]
      simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, renFin, renJmp_nil _ hth]
    cases r with
    | one q => exact G
    | two t' => exact G
    | zero p =>
      obtain ⟨st1, R1, hI1, hν1, hp1, k1, e1⟩ := G.1 (fitsS_lazyReg _ p)
      obtain ⟨F1, F2⟩ := hfill cf hcf P0 hsd hsl lib σ O c gul st1 t R1 p hp1
      refine ⟨fun fp => ?_, fun nf => ?_⟩
      · obtain ⟨R2, r2, hh2, k2⟩ := F1 fp
        have e2 : goJ lib O c gul st1 R1 t (jmp0 g0.bo) = goJ lib O c gul st1 R2 t th := by
          have := r2 [] (Termin.hop th)
          simp only [List.append_nil] at this
          rw [goJ_jmp0 _ _ _ _ hbo, this, execBlob_hop]
        refine ⟨st1, R2, Need.this g0.re, p, hI1, hν1, ⟨rfl, rfl⟩, hh2.1,
          (k2 g0.re (Or.inl (by omega)) (fun hm => by have := (hsl _ hm).1; omega)).trans hp1,
          fun x ⟨x1, x2⟩ => ?_, e1.trans e2⟩
        rw [k2 x (x1.elim (fun h => Or.inl (by omega)) (fun h => Or.inr ⟨by have := hned x h; omega, by
          have := hned x h; omega⟩)) x2]
        exact k1 x ⟨x1.elim (fun h => Or.inl (by omega)) Or.inr, fun e => by
          simp only [GMem, lazyReg, NMem] at e
          rcases x1 with h | h
          · omega
          · have := hned x h; omega⟩
      · exact ⟨Tone.two t, st1, hI1, hν1, by
          rw [e1, goJ_jmp0 _ _ _ _ hbo]
          have := F2 nf [] (Termin.hop th)
          simp only [List.append_nil] at this
          exact this, ToneRel.two (frames_mono hν1 htr)⟩
  have agR : ∀ (cf : Map (Nat × List Nat)) (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (gul : Noun)
      (t : Trace) (s0 s : Noun), (∀ st' : σ, AgreeL lib O c gul st' t cf ned g0 g' nex.laz s0 s) →
      ∀ st' : σ, AgreeU lib O c gul st' t cf ned g2 g' nex.laz s0 s :=
    fun cf c ned σ O gul t s0 s ag st' =>
      ⟨fun o h0 h1' hn' => (ag st').1 o (by omega) h1' hn', fun e he => (ag st').2 e he (by have := lab' e he; omega)⟩
  refine ⟨by omega, by omega, Re.2.2.1.trans dr2, fun o ho hn' => by rw [Re.2.2.2 o (by omega), hO o ho hn'],
    G2.trans R.grow, PF.1.trans R.cfr, R.lo, R.hi, ?_, fun r hr => ?_, R.dist,
    fun e he => ⟨(R.eregs e he).1, fun r hr => Or.inr (Or.inr ⟨by
      rcases ((R.eregs e he).2 r hr).1 with h | h
      · simp only [GMem, lazyReg, NMem] at h; omega
      · omega, ((R.eregs e he).2 r hr).2⟩)⟩,
    fun e he => ⟨Or.inr ⟨by have := (R.labs e he).1; omega, (R.labs e he).2.1⟩, (R.labs e he).2.2⟩, R.nodup,
    fun s v d w r hq hr => ?_, fun s hs hf => ?_, R.ncond, R.econd, fun e he => ?_, ?_, ?_⟩
  · rcases R.ent with fr | e
    · exact Or.inl fr
    · simp only [GoalJ] at e
      rw [e]
      exact Or.inl ⟨_, by rw [Re.2.2.2 _ (by simp only [jmp0]; omega)]; exact hB0, rfl, rfl⟩
  · rcases R.regs r hr with h | h
    · simp only [GMem, lazyReg, NMem] at h; subst h; exact Or.inr ⟨Nat.le_refl _, by omega⟩
    · exact Or.inr ⟨by omega, h.2⟩
  · obtain ⟨rfl, rfl⟩ := hq
    simp only [NMem] at hr; subst hr; exact ⟨Nat.le_refl _, by omega⟩
  · obtain ⟨N1, N2⟩ := R.nec s hs hf
    have bad : ∀ {tm : Trace} {r : Tone}, BadC (CGoal.next (lazyReg g0.re : Sure S) (jmp0 g0.bo)) tm r →
        BadC (CGoal.next L.sure th) tm r := fun h => by
      rcases h with e | ⟨q, _, nq⟩
      · exact Or.inl e
      · exact absurd (fitsS_lazyReg _ q) nq
    exact ⟨fun gul n tm r hm => bad (N1 gul n tm r hm), fun gul tm => by
      obtain ⟨r, hm, hb⟩ := N2 gul tm; exact ⟨r, hm, bad hb⟩⟩
  · obtain ⟨A, hA, KP⟩ := hE e he
    refine ⟨A, fun B fin hb => by rw [Re.2.2.2 _ (by have := (hlab e he).1; omega)]; exact hA B fin hb,
      fun cf hcf => Or.inr ⟨fun hm => by
        obtain ⟨e', he', e1⟩ := List.mem_map.mp hm; have := lab' e' he'; have := (hlab e he).1; omega, ?_⟩⟩
    intro lib σ O c gul st t ned A1 s0 s v d w hned hq hf0
    obtain ⟨hd, hw⟩ := hq
    subst d; subst w
    intro R0 hR0
    obtain ⟨hn0, hv0⟩ := hR0
    obtain ⟨R1, r1, -, k1⟩ := (hf0 R0 hn0).1 (fitsS_bunt s)
    have hv1 : SkaModel.read g0.re R1 = some v :=
      (k1 g0.re (Or.inr (by omega)) (by simp [Sure.bunt, NMem])).trans hv0
    obtain ⟨F1, F2⟩ := hfill cf hcf KP (hed e he).1 (hed e he).2 lib σ O c gul st t R1 v hv1
    refine ⟨fun fv => ?_, fun nf => Crashes.append_right r1 (F2 nf)⟩
    obtain ⟨R2, r2, hh2, k2⟩ := F1 fv
    refine ⟨R2, Runs.append r1 r2, hh2, fun x hx hn' => ?_⟩
    have hnot : ¬ NMem (Sure.bunt : Sure S).ned x := by simp [Sure.bunt, NMem]
    rcases hx with (h | h) | h
    · have := hned x h
      rw [k2 x (Or.inr ⟨by omega, by omega⟩) hn', k1 x (Or.inl h) hnot]
    · simp only [NMem] at h; subst h
      rw [k2 _ (Or.inl (by omega)) hn', k1 _ (Or.inr (by omega)) hnot]
    · rw [k2 x (Or.inl (by omega)) hn', k1 x (Or.inr (by omega)) hnot]
  · intro cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    exact conv cf hcf c ned σ Inv ν O gul st t tm s0 s regs ag hned htr r
      (R.sem cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm (agR cf c ned σ O gul t s0 s ag) hned
        regs hh hn)
  · intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨r, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs (agR cf c ned σ O gul t s0 s ag)
      hned regs hh hn res hres
    exact ⟨r, hm, conv cf hcf c ned σ Inv ν O gul st t tm s0 s regs ag hned htr r G⟩

end Comp
end SkaModel
end Formalization
