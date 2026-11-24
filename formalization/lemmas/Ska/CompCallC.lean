import lemmas.Ska.CompPairLC

/-!
# The indirect call whose parts may call

README Gaps 12.20.  The indirect call `[2 p q]` with parts meeting `UOKC`
(each may itself call): the blocks of `+kerf` and the `%nok` block are the
prefix of a pair (`pairLC_ok`) whose block `o` is the `%nok` block, whose
first part is `p` (the subject, under `%next (lazy-from-reg rSub)`) and
whose second part is `q` (the formula, under `%next (lazy-from-reg rFol)`
into `o`, parked behind `p` by `+past` when `p` is hinted).  The last step
is `+mink` on the two products, which the oracle answers at the `%nok`
(`nokStep_fwd`, `nokStep_bwd`), and the block `out` of `+kerf` meets the
goal (`outGoal_kerf`, `outGoal_done`, `outGoal_pick`).

The raw blocks of `[2 [2 [0 3] [0 2]] [0 2]]` (`%isc`, `CompRunOKLC.lean`):
`6: nok v6 v7 -> v5` (the subject part's call), `5: mov v5 v3`, `4: v0 ->
cel, hed -> v4` (the `+past` of the formula part behind it), `3: nok v3 v4
-> v2`.

* `MinkC2`, `minkC2_indirect`: `+mink` on `[2 b c]` from its parts.
* `nokStep_fwd`, `nokStep_bwd`: the `%nok` block for any goal.
* `indirectC_runS`, `indirectC_runN`, `indirectC_runD`, `indirectC_runP`,
  `okc_indirectC`, `uokc_indirectC`, `entNew_indirectC`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## `+mink` on `[2 b c]` from its parts -/

/-- **`+mink` on `f` is an indirect call of the formulas `fb`, `fc`**: `fb`
runs, then `fc`, with less fuel, then `+mink` on the two products with that
fuel (`fwd`); backward, runs of the parts and of the products give one of
`f` (`bwd`). -/
structure MinkC2 (lib : Lib) (P : Noun → Prop) (f fb fc : Noun) : Prop where
  fwd : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {r : Tone}, P s → minkF lib gul n tm s f = some r →
    ∃ n', n' < n ∧ ∃ rb, minkF lib gul n' tm s fb = some rb ∧
      (((∀ q, rb ≠ Tone.zero q) ∧ r = rb) ∨ ∃ x, rb = Tone.zero x ∧ ∃ rc, minkF lib gul n' tm s fc = some rc ∧
        (((∀ q, rc ≠ Tone.zero q) ∧ r = rc) ∨ ∃ y, rc = Tone.zero y ∧ minkF lib gul n' tm x y = some r))
  bwd : ∀ {s gul : Noun} {tm : Trace} {rb : Tone}, P s → Mink lib gul tm s fb rb →
    ((∀ q, rb ≠ Tone.zero q) → Mink lib gul tm s f rb) ∧
    ∀ x rc, rb = Tone.zero x → Mink lib gul tm s fc rc →
      ((∀ q, rc ≠ Tone.zero q) → Mink lib gul tm s f rc) ∧
      ∀ y r, rc = Tone.zero y → Mink lib gul tm x y r → Mink lib gul tm s f r

/-- `[2 b c]` itself. -/
theorem minkC2_indirect (lib : Lib) (P : Noun → Prop) (b c : Noun) : MinkC2 lib P (n3 (A 2) b c) b c where
  fwd := fun {s gul n tm r} _ h => by
    cases n with
    | zero => simp [minkF] at h
    | succ n' =>
      rw [minkF_succ_eq] at h
      simp only [minkStep] at h
      refine ⟨n', Nat.lt_succ_self n', ?_⟩
      cases eb : minkF lib gul n' tm s b with
      | none => rw [eb] at h; simp [tbind] at h
      | some rb =>
        rw [eb] at h
        refine ⟨rb, rfl, ?_⟩
        cases rb with
        | one q => simp only [tbind, Option.some.injEq] at h; exact Or.inl ⟨(fun _ e => by cases e), h.symm⟩
        | two t' => simp only [tbind, Option.some.injEq] at h; exact Or.inl ⟨(fun _ e => by cases e), h.symm⟩
        | zero x =>
          refine Or.inr ⟨x, rfl, ?_⟩
          simp only [tbind_zero] at h
          cases ec : minkF lib gul n' tm s c with
          | none => rw [ec] at h; simp [tbind] at h
          | some rc =>
            rw [ec] at h
            refine ⟨rc, rfl, ?_⟩
            cases rc with
            | one q => simp only [tbind, Option.some.injEq] at h; exact Or.inl ⟨(fun _ e => by cases e), h.symm⟩
            | two t' => simp only [tbind, Option.some.injEq] at h; exact Or.inl ⟨(fun _ e => by cases e), h.symm⟩
            | zero y => exact Or.inr ⟨y, rfl, h⟩
  bwd := fun {s gul tm rb} _ hb => by
    obtain ⟨n1, e1⟩ := hb
    refine ⟨fun hn => ⟨n1 + 1, ?_⟩, fun x rc ex hc => ?_⟩
    · rw [minkF_succ_eq]; simp only [minkStep]; rw [e1]
      cases rb with
      | zero q => exact absurd rfl (hn q)
      | one _ => rfl
      | two _ => rfl
    · subst ex
      obtain ⟨n2, e2⟩ := hc
      refine ⟨fun hn => ⟨max n1 n2 + 1, ?_⟩, fun y r ey hr => ?_⟩
      · have e1' := minkF_le lib gul (Nat.le_max_left n1 n2) tm s b _ e1
        have e2' := minkF_le lib gul (Nat.le_max_right n1 n2) tm s c _ e2
        rw [minkF_succ_eq]; simp only [minkStep]; rw [e1', tbind_zero, e2']
        cases rc with
        | zero q => exact absurd rfl (hn q)
        | one _ => rfl
        | two _ => rfl
      · subst ey
        obtain ⟨n3', e3⟩ := hr
        have e1' := minkF_le lib gul (Nat.le_trans (Nat.le_max_left n1 n2) (Nat.le_max_left _ n3')) tm s b _ e1
        have e2' := minkF_le lib gul (Nat.le_trans (Nat.le_max_right n1 n2) (Nat.le_max_left _ n3')) tm s c _ e2
        have e3' := minkF_le lib gul (Nat.le_max_right (max n1 n2) n3') tm x y _ e3
        exact ⟨max (max n1 n2) n3' + 1, by rw [minkF_succ_eq]; simp only [minkStep]; rw [e1', tbind_zero, e2',
          tbind_zero, e3']⟩

/-! ## The `%nok` block -/

section
variable {lib : Lib} {σ : Type} {Inv : σ → Prop} {ν : σ → Needs} {O : Oracle σ} {c : Straight Map} {gul : Noun}

/-- **The `%nok` block, forward**: from registers holding the subject and
the formula, `+mink` on them with fuel below the oracle's bound gives the
tone at which the code from the block meets `GoalSemCM` (the block `out`
meeting `OutGoal`). -/
theorem nokStep_fwd (hS : OracleSteps Inv ν O) {n : Nat} (hF : OracleFwd lib Inv ν O n)
    {a b pro o out : Nat} (hb : HoonMap.get c.blocks o = some ⟨[], [Pole.nok a b pro], Termin.hop (jmp0 out)⟩)
    {K : Nat → Prop} (hK : ∀ x, K x → x ≠ pro) {goal : CGoal S} (Hout : OutGoal lib O c gul Inv ν K pro out goal)
    {st : σ} (hI : Inv st) {t tm : Trace} (htr : Forall2 (FrameRel lib (ν st)) t tm) {regs : Map (Option Noun)}
    {x y : Noun} (hx : SkaModel.read a regs = some x) (hy : SkaModel.read b regs = some y) {n' : Nat} {r : Tone}
    (hn : n' < n) (hm : minkF lib gul n' tm x y = some r) :
    GoalSemCM lib O c gul Inv ν K st regs t tm (jmp0 o) goal r := by
  have J := goJ_nok (lib := lib) (O := O) (gul := gul) hb st regs t hx hy
  rw [minkF_trace] at hm
  obtain ⟨r0, h0, rfl⟩ := Option.map_eq_some_iff.mp hm
  obtain ⟨ton, st', hO, hrel⟩ := hF.nok st x y gul n' r0 hI hn h0
  obtain ⟨hI', hν⟩ := hS.nok st x y gul ton st' hI hO
  rw [hO, Option.bind_some] at J
  cases hrel with
  | zero p' =>
    have J' : goJ lib O c gul st regs t (jmp0 o) = goJ lib O c gul st' (SkaModel.store pro p' regs) t (jmp0 out) := J
    exact goalSemCM_step hν (fun z hz => read_store_ne (hK z hz) p' regs) J' goal _
      (Hout st' (SkaModel.store pro p' regs) t tm p' hI' (frames_mono hν htr) (read_store_eq pro p' regs))
  | one p' =>
    exact goalSemCM_ret goal _ (fun _ h => by cases h) ⟨Tone.one p', st', hI', hν, J, ToneRel.one p'⟩
  | two hl =>
    exact goalSemCM_ret goal _ (fun _ h => by cases h)
      ⟨_, st', hI', hν, J, ToneRel.two (Forall2.append hl (frames_mono hν htr))⟩

/-- **The `%nok` block, backward**: if the code from it returns, the oracle
answered, and `+mink` on the subject and the formula returns a tone at
which the code meets `GoalSemCM`. -/
theorem nokStep_bwd (hS : OracleSteps Inv ν O) (hB : OracleBwd lib Inv ν O)
    {a b pro o out : Nat} (hb : HoonMap.get c.blocks o = some ⟨[], [Pole.nok a b pro], Termin.hop (jmp0 out)⟩)
    {K : Nat → Prop} (hK : ∀ x, K x → x ≠ pro) {goal : CGoal S} (Hout : OutGoal lib O c gul Inv ν K pro out goal)
    {st : σ} (hI : Inv st) {t tm : Trace} (htr : Forall2 (FrameRel lib (ν st)) t tm) {regs : Map (Option Noun)}
    {x y : Noun} (hx : SkaModel.read a regs = some x) (hy : SkaModel.read b regs = some y)
    {res : Tone × σ} (hres : goJ lib O c gul st regs t (jmp0 o) = some res) :
    ∃ r, Mink lib gul tm x y r ∧ GoalSemCM lib O c gul Inv ν K st regs t tm (jmp0 o) goal r := by
  have J := goJ_nok (lib := lib) (O := O) (gul := gul) hb st regs t hx hy
  have hres' := hres
  rw [J] at hres'
  obtain ⟨⟨ton, st'⟩, hO, -⟩ := Option.bind_eq_some_iff.mp hres'
  obtain ⟨r0, ⟨k, hM⟩, hrel⟩ := hB.nok st x y gul ton st' hI hO
  obtain ⟨hI', hν⟩ := hS.nok st x y gul ton st' hI hO
  have Mk : Mink lib gul tm x y (r0.app tm) := ⟨k, by rw [minkF_trace, hM]; rfl⟩
  rw [hO, Option.bind_some] at J
  refine ⟨_, Mk, ?_⟩
  cases hrel with
  | zero p' =>
    have J' : goJ lib O c gul st regs t (jmp0 o) = goJ lib O c gul st' (SkaModel.store pro p' regs) t (jmp0 out) := J
    exact goalSemCM_step hν (fun z hz => read_store_ne (hK z hz) p' regs) J' goal _
      (Hout st' (SkaModel.store pro p' regs) t tm p' hI' (frames_mono hν htr) (read_store_eq pro p' regs))
  | one p' =>
    exact goalSemCM_ret goal _ (fun _ h => by cases h) ⟨Tone.one p', st', hI', hν, J, ToneRel.one p'⟩
  | two hl =>
    exact goalSemCM_ret goal _ (fun _ h => by cases h)
      ⟨_, st', hI', hν, J, ToneRel.two (Forall2.append hl (frames_mono hν htr))⟩

end


/-! ## The run -/

/-- **The second part behind `+past`**: the run of `q` with the `+past`
behind a first part `p` with `UOKC` meets `TailGC`, and its need fits every
subject or `p` does not block. -/
theorem tailGC_of_past {lib : Lib} {p : Nomm} {env : CallEnv} {P : Noun → Prop} {fb fc : Noun}
    (Up : UOKC (S := S) (Map := Map) lib env P fb p) {sur : Sure S} {o : Nat} {region : List Nat}
    {g0 g1 g2 : Gen Map} {nex nex' : NextL S}
    (R : RunOKGC (Map := Map) lib P fc (CGoal.next sur (jmp0 o)) g0 g1 nex) (cq : Clean nex.laz.sure.ned)
    (hsur : ∀ r, NMem sur.ned r → r < g0.re) (d1 : g1.drop = false) (u1 : UpBelow g1)
    (h : pastL env.cod nex p region g1 = some (nex', g2)) :
    TailGC lib P fc sur (jmp0 o) g0 g2 nex' ∧ ((∀ s, FitsS nex'.laz.sure s) ∨ TotalC lib P fb) ∧
      Clean nex'.laz.sure.ned := by
  rcases Up.kind with ⟨up, Mp⟩ | hh
  · rw [pastL_pure _ _ up.pure, pure_apply] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨TailGC.ofRun R, Or.inr (totalC_of_minkEq Mp), cq⟩
  · rcases pastL_hinted hh h with ⟨x1, x2, en, es, _⟩ | ⟨x1, x2⟩
    · subst x1 x2
      exact ⟨TailGC.ofRun R, Or.inl (fun s => fitsS_trivial en es s), cq⟩
    · subst x1 x2
      exact ⟨tailGC_past R hsur d1 u1 region, Or.inl (fun s => fitsS_bunt s), trivial⟩

/-- **The indirect call whose parts may call, under a fork-free `%next sur
th`, from the pieces of its run** (`runLC_n2_none` with `+simple-next` the
identity): `+kerf`, the `%nok` block, then the pair of `q` (behind `+past`
when `p` is hinted) and `p` (`pairLC_ok`, the last step `nokStep_fwd`,
`nokStep_bwd` with the block of `+kerf` meeting `outGoal_kerf`). -/
theorem indirectC_runS (lib : Lib) {p q : Nomm} {env : CallEnv} {P : Noun → Prop} {f fb fc : Noun}
    (Up : UOKC (S := S) (Map := Map) lib env P fb p) (Uq : UOKC (S := S) (Map := Map) lib env P fc q)
    (M : MinkC2 lib P f fb fc) (hcount : sixCount p + sixCount q ≤ 255) {sup : Option Nomm}
    {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g' : Gen Map} {nex : NextL S}
    (hj : GJ g0.bo (CGoal.next sur th)) (hth : th.args = []) (hok : GoalOK g0 (CGoal.next sur th))
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (hkg : ∀ r, NMem sur.ned r → HoonMap.get g0.cond r = Option.none)
    {out pro o : Nat} {g2 g3 g4 g5 g6 : Gen Map} {nexF nexF' nexS : NextL S}
    (h2 : kerf (⟨ofSure sur, th⟩ : NextL S) g0 = some ((out, pro), g2))
    (h3 : emit ⟨[], [Pole.nok g2.re (g2.re + 1) pro], Termin.hop (jmp0 out)⟩
        { { g2 with re := g2.re + 1 } with re := g2.re + 1 + 1 } = some (o, g3))
    (h4 : runLC env sup q (CGoalL.next (ofSure (lazyReg (g2.re + 1))) (jmp0 o)) region g3 = some (nexF, g4))
    (h5 : pastL env.cod nexF p region g4 = some (nexF', g5))
    (h6 : runLC env sup p (CGoalL.next (ofSure (lazyReg g2.re)) nexF'.th) region g5 = some (nexS, g6))
    (h7 : copyL nexS nexF'.laz g6 = some (nex, g')) :
    RunOKGC lib P f (CGoal.next sur th) g0 g' nex ∧ g0.bo ≤ nex.th.there := by
  have h1 : simpleNextL (CGoalL.next (ofSure sur) th) g0 = some (⟨ofSure sur, th⟩, g0) := rfl
  obtain ⟨-, -, rfl, rfl, rfl, l2, r3, b3, d3, cn3, k3o, k3out, k3lo, hk2, G3, u3, cb3⟩ :=
    indirect_prefixN h1 h2 h3 d0 hu hcb b0 hj
  obtain ⟨-, -, bo2, dr2, cd2, -, -, Ak, hblk, -, RI, -⟩ := kerf_ofSure h2 d0
  have nk : ∀ x, g0.re ≤ x → HoonMap.get g0.cond x = Option.none := fun x hx => condBelow_none hcb hx
  have E3 : Ext g0 g3 := ⟨by omega, by omega, by rw [d3, d0], k3lo⟩
  have cl3 : Clear g3 := hcl.growU G3
  have hc : sixCount p ≤ 255 ∧ sixCount q ≤ 255 := ⟨by omega, by omega⟩
  -- the formula part
  have Rq := Uq.run (sup := sup) (goal := CGoal.next (lazyReg (g2.re + 1)) (jmp0 (g0.bo + 1))) (region := region)
    trivial rfl ⟨by simp only [jmp0]; omega, by simp only [jmp0]; omega⟩
    ⟨trivial, fun r hr => by simp only [lazyReg, NMem] at hr; subst hr; omega⟩ trivial hc.2 (by omega) d3 u3
    cl3 cb3 (fun r hr => by simp only [lazyReg, NMem] at hr; subst hr; rw [cn3]; exact nk _ (by omega)) h4
  have cq := Uq.clean (goal := CGoal.next (lazyReg (g2.re + 1)) (jmp0 (g0.bo + 1))) trivial trivial h4
  obtain ⟨T, hhd, cq'⟩ := tailGC_of_past Up Rq cq
    (fun r hr => by simp only [lazyReg, NMem] at hr; subst hr; omega) (Rq.ext.2.2.1.trans d3) (Rq.grow.up u3) h5
  -- the subject part
  have Rp := Up.run (sup := sup) (goal := CGoal.next (lazyReg g2.re) nexF'.th) (region := region) trivial
    (nextArgs_nil T.ent rfl) ⟨T.lo, T.hi⟩
    ⟨trivial, fun r hr => by simp only [lazyReg, NMem] at hr; subst hr; have := T.ext.1; omega⟩ trivial hc.1
    (by have := T.lo; have := T.hi; omega) (T.ext.2.2.1.trans d3) (T.grow.up u3) (cl3.growU T.grow)
    (T.cfr.below cb3)
    (fun r hr => by
      simp only [lazyReg, NMem] at hr; subst hr
      rw [T.cfr.get_lt (by omega), cn3]; exact nk _ (by omega)) h6
  have cp := Up.clean (goal := CGoal.next (lazyReg g2.re) nexF'.th) trivial trivial h6
  -- the blocks of the prefix keep their registers under every later `cond`
  have hfix : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g3.re → HoonMap.get cf k = HoonMap.get g0.cond k) →
      ∀ k, g0.bo ≤ k → k < g3.bo → (HoonMap.get g3.blocks k).map (unproxyBlob cf) = HoonMap.get g3.blocks k := by
    intro cf hcf k h0 h1'
    rcases (show k = g0.bo ∨ k = g0.bo + 1 by omega) with rfl | rfl
    · rw [k3out, hblk, if_pos rfl]
      simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, renFin, renJmp_nil _ hth,
        renOps_fix (fun x hx => unproxy_none (by
          rcases hx with e | e | ⟨a, b⟩
          · rw [hcf x (by omega)]; exact nk x (by omega)
          · rw [hcf x (by have := hok.2 x e; omega)]; exact hkg x e
          · rw [hcf x (by omega)]; exact nk x (by omega))) RI]
    · rw [k3o]
      simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, List.map_cons, renPole, renFin,
        renJmp_nil _ (show (jmp0 g0.bo).args = [] from rfl)]
      rw [unproxy_none (by rw [hcf _ (by omega)]; exact nk _ (by omega)),
        unproxy_none (by rw [hcf _ (by omega)]; exact nk _ (by omega)),
        unproxy_none (by rw [hcf _ (by omega)]; exact nk _ (Nat.le_refl _))]
  -- the block of `+kerf` in any program that agrees with the prefix
  have hid : ∀ b, unproxyBlob (HoonMap.empty : Map (Nat × List Nat)) b = b :=
    fun b => unproxyBlob_empty (fun k => HoonMap.get_empty k) b
  have Hout : ∀ (c : Straight Map), Agree c g0 g3 → ∀ (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ)
      (gul : Noun), OutGoal lib O c gul Inv ν (Keep g0 g3 (CGoal.next sur th)) g0.re g0.bo (CGoal.next sur th) :=
    fun c agc σ Inv ν O gul => outGoal_kerf (cf := HoonMap.empty) hk2 d0 hth hok.1 hok.2
      (by
        rw [agc g0.bo (Nat.le_refl _) (by omega), k3out]
        cases HoonMap.get g2.blocks g0.bo <;> simp [hid])
      (fun x _ => HoonMap.get_empty x)
      (fun x hx => ⟨hx.2, hx.1.imp id (fun h => by omega)⟩)
  have hbN : ∀ (c : Straight Map), Agree c g0 g3 → HoonMap.get c.blocks (g0.bo + 1) =
      some ⟨[], [Pole.nok g2.re (g2.re + 1) g0.re], Termin.hop (jmp0 g0.bo)⟩ := fun c agc => by
    rw [agc (g0.bo + 1) (by omega) (by omega)]; exact k3o
  have hKp : ∀ z, Keep g0 g3 (CGoal.next sur th) z → z ≠ g0.re := fun z hz e => by
    subst e; rcases hz.1 with a | a <;> omega
  have nfit : ∀ (x y : Noun), ¬ (¬ FitsS (lazyReg g2.re : Sure S) x ∨ ¬ FitsS (lazyReg (g2.re + 1) : Sure S) y) :=
    fun x y h => h.elim (fun h => h (fitsS_lazyReg _ x)) (fun h => h (fitsS_lazyReg _ y))
  exact pairLC_ok (Fin := fun gul n' tm x y r => minkF lib gul n' tm x y = some r)
    (FinB := fun gul tm x y r => Mink lib gul tm x y r) (fun hs hm => M.fwd hs hm) (fun hs hb => M.bwd hs hb)
    hok E3 G3 cn3 hcb
    (fun r hr => by simp only [lazyReg, NMem] at hr; subst hr; exact Or.inr ⟨by omega, by omega⟩)
    (fun r hr => by simp only [lazyReg, NMem] at hr; subst hr; exact Or.inr ⟨by omega, by omega⟩)
    (fun r h1' h2' => by simp only [lazyReg, NMem] at h1' h2'; omega)
    (Ext.refl g3) (GrowU.refl g3) rfl rfl
    (Or.inl ⟨rfl, rfl, Or.inl (fun x => fitsS_lazyReg _ x)⟩) hhd T (RunOKGC.toLC Rp) cq' cp h7 hu d0 hfix
    (fun _ _ _ x y _ hn _ => absurd hn (nfit x y)) (fun _ _ x y hn => absurd hn (nfit x y))
    (fun c agc σ Inv ν O n gul hS hF st regs t tm x y n' r hn' hI htr _ _ hx hy hfin =>
      nokStep_fwd hS hF (hbN c agc) hKp (Hout c agc σ Inv ν O gul) hI htr hx hy hn' hfin)
    (fun c agc σ Inv ν O gul hS hB st regs t tm x y hI htr _ _ hx hy res hres =>
      nokStep_bwd hS hB (hbN c agc) hKp (Hout c agc σ Inv ν O gul) hI htr hx hy hres)


/-- **The indirect call whose parts may call, under a fork-free `%next`**
(`indirectC_runS` after `runLC_n2_none`). -/
theorem indirectC_runN (lib : Lib) {p q : Nomm} {env : CallEnv} {P : Noun → Prop} {f fb fc : Noun}
    (Up : UOKC (S := S) (Map := Map) lib env P fb p) (Uq : UOKC (S := S) (Map := Map) lib env P fc q)
    (M : MinkC2 lib P f fb fc) (hcount : sixCount p + sixCount q ≤ 255) {sup : Option Nomm}
    {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g' : Gen Map} {nex : NextL S}
    (hj : GJ g0.bo (CGoal.next sur th)) (hth : th.args = []) (hok : GoalOK g0 (CGoal.next sur th))
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (hkg : ∀ r, NMem sur.ned r → HoonMap.get g0.cond r = Option.none)
    (h : runLC env sup (Nomm.n2 p q Option.none) (CGoalL.next (ofSure sur) th) region g0 = some (nex, g')) :
    RunOKGC lib P f (CGoal.next sur th) g0 g' nex ∧ g0.bo ≤ nex.th.there := by
  obtain ⟨nex0, g1, out, pro, g2, o, g3, nexF, g4, nexF', g5, nexS, g6, h1, h2, h3, h4, h5, h6, h7⟩ :=
    runLC_n2_none h
  simp only [simpleNextL, pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  exact indirectC_runS lib Up Uq M hcount hj hth hok b0 d0 hu hcl hcb hkg h2 h3 h4 h5 h6 h7

theorem simpleNextL_done (g0 : Gen Map) : simpleNextL (CGoalL.done : CGoalL S) g0 =
    some (⟨ofSure (lazyReg g0.re), jmp0 g0.bo⟩, { g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) := by
  simp only [simpleNextL, bind_apply, re_apply, Option.bind_some, emit_apply, pure_apply]
  rfl

theorem simpleNextL_pick (z o : Jmp) (g0 : Gen Map) : simpleNextL (CGoalL.pick z o : CGoalL S) g0 =
    some (⟨ofSure (lazyReg g0.re), jmp0 g0.bo⟩, { g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.brn g0.re z o⟩) := by
  simp only [simpleNextL, bind_apply, re_apply, Option.bind_some, emit_apply, pure_apply]
  rfl

/-- **The indirect call whose parts may call, under `%done` or `%pick`**:
`+simple-next` makes the block `bk` (`[don re]` or `[brn re z o]`) at `bo`,
kept to the end, and the rest of the run is the one under `%next
(lazy-from-reg re)` into it (`indirectC_runS`). -/
theorem indirectC_runB (lib : Lib) {p q : Nomm} {env : CallEnv} {P : Noun → Prop} {f fb fc : Noun}
    (Up : UOKC (S := S) (Map := Map) lib env P fb p) (Uq : UOKC (S := S) (Map := Map) lib env P fc q)
    (M : MinkC2 lib P f fb fc) (hcount : sixCount p + sixCount q ≤ 255) {sup : Option Nomm}
    {region : List Nat} {g0 g' : Gen Map} {nex : NextL S} {goal : CGoalL S} {bk : Blob}
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (hjb : JumpsBelow bk.fin g0.bo)
    (hsn : simpleNextL goal g0 = some (⟨ofSure (lazyReg g0.re), jmp0 g0.bo⟩, { g0 with re := g0.re + 1 }.emitted bk))
    (h : runLC env sup (Nomm.n2 p q Option.none) goal region g0 = some (nex, g')) :
    HoonMap.get g'.blocks g0.bo = some bk ∧
    RunOKGC lib P f (CGoal.next (lazyReg g0.re) (jmp0 g0.bo)) ({ g0 with re := g0.re + 1 }.emitted bk) g' nex := by
  obtain ⟨nex0, g1, out, pro, g2, o, g3, nexF, g4, nexF', g5, nexS, g6, h1, h2, h3, h4, h5, h6, h7⟩ :=
    runLC_n2_none h
  rw [hsn] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  have G1 : GrowU ({ g0 with re := g0.re + 1 } : Gen Map) ({ g0 with re := g0.re + 1 }.emitted bk) :=
    growU_emit (g := { g0 with re := g0.re + 1 }) hjb hu
  have R := (indirectC_runS (sur := lazyReg g0.re) (th := jmp0 g0.bo) lib Up Uq M hcount
    ⟨b0, by simp only [jmp0, Gen.emitted]; omega⟩ rfl
    ⟨trivial, fun x hx => by simp only [lazyReg, NMem] at hx; subst hx; simp only [Gen.emitted]; omega⟩
    (by simp only [Gen.emitted]; omega) (by simp only [Gen.emitted]; exact d0) (G1.up hu)
    (Clear.growU (g := ({ g0 with re := g0.re + 1 } : Gen Map)) hcl G1)
    (fun k hk => by have := hcb k hk; simp only [Gen.emitted] at this ⊢; omega)
    (fun x hx => by
      simp only [lazyReg, NMem] at hx; subst hx
      exact condBelow_none hcb (Nat.le_refl _)) h2 h3 h4 h5 h6 h7).1
  refine ⟨?_, R⟩
  rw [R.ext.2.2.2 _ (by simp only [Gen.emitted]; omega)]
  simp only [Gen.emitted, d0, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]

/-- **The sure need of the indirect call's run is clean** (`+copy` of the
parts', clean by `UOKC.clean`, or the bunt of `+past`). -/
theorem indirectC_clean {lib : Lib} {p q : Nomm} {env : CallEnv} {P : Noun → Prop} {fb fc : Noun}
    (Up : UOKC (S := S) (Map := Map) lib env P fb p) (Uq : UOKC (S := S) (Map := Map) lib env P fc q)
    {sup : Option Nomm} {goal : CGoalL S} {region : List Nat} {g0 g' : Gen Map} {nex : NextL S}
    (h : runLC env sup (Nomm.n2 p q Option.none) goal region g0 = some (nex, g')) : Clean nex.laz.sure.ned := by
  obtain ⟨nex0, g1, out, pro, g2, o, g3, nexF, g4, nexF', g5, nexS, g6, h1, h2, h3, h4, h5, h6, h7⟩ :=
    runLC_n2_none h
  have cq := Uq.clean (goal := CGoal.next (lazyReg (g2.re + 1)) (jmp0 o)) trivial trivial h4
  have cq' : Clean nexF'.laz.sure.ned := by
    rcases Up.kind with ⟨up, _⟩ | hh
    · rw [pastL_pure _ _ up.pure, pure_apply] at h5
      simp only [Option.some.injEq, Prod.mk.injEq] at h5
      obtain ⟨rfl, rfl⟩ := h5
      exact cq
    · rcases pastL_hinted hh h5 with ⟨x1, x2, _⟩ | ⟨x1, x2⟩
      · subst x1 x2; exact cq
      · subst x1 x2; trivial
  exact clean_copyL h7 (Up.clean (goal := CGoal.next (lazyReg g2.re) nexF'.th) trivial trivial h6) cq'

/-- **The indirect call whose parts meet `UOKC` meets `OKC`** for a formula
with `MinkC2` (`indirectC_runN`; under `%done` and `%pick` `indirectC_runB`
and `runOKGC_of_next`). -/
theorem okc_indirectC (lib : Lib) (env : CallEnv) {p q : Nomm} {P : Noun → Prop} {f fb fc : Noun}
    (Up : UOKC (S := S) (Map := Map) lib env P fb p) (Uq : UOKC (S := S) (Map := Map) lib env P fc q)
    (M : MinkC2 lib P f fb fc) : OKC (S := S) (Map := Map) lib env P f (Nomm.n2 p q Option.none) := by
  intro sup goal region g0 g1 nex ha hj hok hcl hcount b0 d0 hu hcl0 hcb hkg h
  have hc : sixCount p + sixCount q ≤ 255 := hcount
  cases goal with
  | next sur th => exact (indirectC_runN lib Up Uq M hc hj ha hok b0 d0 hu hcl0 hcb hkg h).1
  | done =>
    obtain ⟨hb, R⟩ := indirectC_runB lib Up Uq M hc b0 d0 hu hcl0 hcb (bk := ⟨[], [], Termin.don g0.re⟩)
      (fun j hj => by simp [finJumps] at hj) (simpleNextL_done g0) h
    exact runOKGC_of_next (goal := CGoal.done) trivial hu hcb (fun j hj => by simp [finJumps] at hj) rfl hb
      (fun cf c0 => by simp only [unproxyBlob, renBlob, List.map_nil, renFin, unproxy_none c0])
      (fun c σ O gul Inv ν K K' st regs t tm je r _ _ hbc H => goalSemCM_done_of_next hbc H) R
  | pick z o =>
    have hjb : JumpsBelow (Termin.brn g0.re z o) g0.bo := fun j hj' => by
      simp only [finJumps, List.mem_cons, List.mem_nil_iff, or_false] at hj'
      rcases hj' with rfl | rfl
      · exact hj.1
      · exact hj.2
    obtain ⟨hb, R⟩ := indirectC_runB lib Up Uq M hc b0 d0 hu hcl0 hcb (bk := ⟨[], [], Termin.brn g0.re z o⟩)
      hjb (simpleNextL_pick z o g0) h
    exact runOKGC_of_next (goal := CGoal.pick z o) trivial hu hcb hjb rfl hb
      (fun cf c0 => by
        simp only [unproxyBlob, renBlob, List.map_nil, renFin, unproxy_none c0, renJmp_nil _ ha.1,
          renJmp_nil _ ha.2])
      (fun c σ O gul Inv ν K K' st regs t tm je r hK htr hbc H => goalSemCM_pick_of_next hK htr hbc H) R

/-- **The indirect call whose parts meet `UOKC` meets `UOKC`**. -/
theorem uokc_indirectC (lib : Lib) (env : CallEnv) {p q : Nomm} {P : Noun → Prop} {f fb fc : Noun}
    (Up : UOKC (S := S) (Map := Map) lib env P fb p) (Uq : UOKC (S := S) (Map := Map) lib env P fc q)
    (M : MinkC2 lib P f fb fc) : UOKC (S := S) (Map := Map) lib env P f (Nomm.n2 p q Option.none) :=
  ⟨Or.inr rfl, fun _ _ h => indirectC_clean Up Uq h, OKC.toN (okc_indirectC lib env Up Uq M)⟩

/-- **The indirect call whose parts meet `UOKC` meets `EntNew`** (the block
of `+copy`, `indirectC_runN`). -/
theorem entNew_indirectC (lib : Lib) (env : CallEnv) {p q : Nomm} {P : Noun → Prop} {f fb fc : Noun}
    (Up : UOKC (S := S) (Map := Map) lib env P fb p) (Uq : UOKC (S := S) (Map := Map) lib env P fc q)
    (M : MinkC2 lib P f fb fc) : EntNew (S := S) (Map := Map) env (Nomm.n2 p q Option.none) := by
  intro sup sur th region g0 g1 nex hj hth hok hcl hcount b0 d0 hu hcl0 hcb hkg h
  exact (indirectC_runN lib Up Uq M hcount hj hth hok b0 d0 hu hcl0 hcb hkg h).2

end Comp
end SkaModel
end Formalization
