import lemmas.Ska.CompHintClsAux
import lemmas.Ska.CompHintSixRegS2

/-!
# A `%mean` with a constant (README Gaps 24): `%hcp` / `%hce`

With a constant (`+mean-konst` `some n`, the trap's arm pure) `+run` of
`[11 [%mean p] q]` under `%next (ofSure sur) th` is: `+need-ord-alloc-regs`
of `%none` (no state change), `+simple-next`, `+past-if` (nothing when
`+sound` of `q` holds at `sur`), the epilogue `[hce n body]` hopping to `th`,
`q` into it, `+lazy-bound`, the prologue `[hcp n body]`, the test `+sound`
of `p` at `%none`, the trap `p` run LAST under `%next bunt` (its product not
needed: only its crash is), and `+copy`.  The prologue pushes `(%meac, n)`
whatever the trap is, so the frame stands for `+mink`'s `(%mean, trap)` only
through `FrameRel.meac`: `+mack` of every trap gives `n` (the hypothesis
`hK`, the `konst` field of `MeanOK`).

* `doneNext_meanK`: the run under `%done` is the block `[don re]` and the
  run under `%next (lazy-from-reg re)` into it.
* `runLCH_meanK_sur`: the run step by step.
* `goJ_pushMeanK`, `goJ_popMeanK`, `FrameOKMeanK`, `frameOKMeanK_goesR`:
  the frame.
* **`surGBT_meanK`**: in `SurGBT` (`Ap` with `SoundK` and `FitP` of `q`),
  the text of `surGBT_n11dKept` with the trap in place of the clue.
* **`regGBT_meanK`**: in `RegGBT` (`RegGBT.ofSur` of `surGBT_meanK`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

section
variable {snd : Nomm → NeedOrd → Bool}

/-- **A constant `%mean` under `%done`** begins with `+simple-next`. -/
theorem doneNext_meanK {env : CallEnv} {p : Nomm} {b : Bell} {q : Nomm} {body : Noun} {k : Option Noun}
    {n : Noun} (hk : meanKonst env b k = some n) :
    DoneNext (S := S) (Map := Map) env snd (Nomm.mean p b q body k) := by
  intro sup region g0
  simp only [runLCH, hk, needOrdAllocRegs, bind_apply, pure_apply, Option.bind_some, simpleNextL_done]
  simp only [simpleNextL, pure_apply, Option.bind_some]

/-- The state after the epilogue of a constant `%mean` under `%next`. -/
def genMeanK (g0 : Gen Map) (n body : Noun) (th : Jmp) : Gen Map :=
  g0.emitted ⟨[], [Pole.hce n body], Termin.hop th⟩

/-- **The run of a constant `%mean` under `%next (ofSure sur) th`, step by
step**, when `+past-if` emits nothing. -/
theorem runLCH_meanK_sur {env : CallEnv} {p q : Nomm} {b : Bell} {body : Noun} {k : Option Noun} {n : Noun}
    (hk : meanKonst env b k = some n) {sur : Sure S}
    (hp : HoonSet.small sur.lok = true ∧ snd q (needToOrd sur.ned) = true) {sup : Option Nomm} {th : Jmp}
    {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (hr : runLCH env snd true sup (Nomm.mean p b q body k) (CGoalL.next (ofSure sur) th) region g0 =
      some (nex, g1)) :
    ∃ nq gc nh gh, runLCH env snd true sup q (CGoalL.next (ofSure sur) (jmp0 g0.bo)) region
        (genMeanK g0 n body th) = some (nq, gc) ∧
      nq.th.args = [] ∧
      runLCH env snd true sup p (CGoalL.next (ofSure Sure.bunt) (jmp0 (gc.bo + 1))) region
        (((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).emitted
          ⟨[], [Pole.hcp n body], Termin.hop (jmp0 gc.bo)⟩) = some (nh, gh) ∧
      copyL nh (mk Sure.bunt [] [(gc.bo, nq.laz)]) gh = some (nex, g1) := by
  simp only [runLCH, hk] at hr
  obtain ⟨n0, ga, h0, hr⟩ := bind_some hr
  simp only [needOrdAllocRegs, pure_apply, Option.some.injEq, Prod.mk.injEq] at h0
  obtain ⟨rfl, rfl⟩ := h0
  obtain ⟨n1, gb, h1, hr⟩ := bind_some hr
  simp only [simpleNextL, pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  obtain ⟨n2, gb, h2, hr⟩ := bind_some hr
  have hp' : HoonSet.small (ofSure sur : Lazy S).sure.lok = true ∧
      snd q (needToOrd (ofSure sur : Lazy S).sure.ned) = true := hp
  unfold pastIfL at h2
  rw [if_pos hp'] at h2
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  obtain ⟨ep, gb', h3, hr⟩ := bind_some hr
  rw [emit_apply] at h3
  simp only [Option.some.injEq, Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  obtain ⟨nq, gc, h4, hr⟩ := bind_some hr
  obtain ⟨nb, gd, h5, hr⟩ := bind_some hr
  have hta : nq.th.args = [] := by
    cases hne : nq.th.args with
    | nil => rfl
    | cons a l =>
      unfold lazyBound at h5
      simp [bind_apply, emit_apply, setTag_apply, hne] at h5
  rw [lazyBound_apply hta] at h5
  simp only [Option.some.injEq, Prod.mk.injEq] at h5
  obtain ⟨rfl, rfl⟩ := h5
  obtain ⟨pr, ge, h6, hr⟩ := bind_some hr
  rw [emit_apply] at h6
  simp only [Option.some.injEq, Prod.mk.injEq] at h6
  obtain ⟨rfl, rfl⟩ := h6
  split at hr
  · cases hr
  · obtain ⟨nh, gh, h7, hr⟩ := bind_some hr
    refine ⟨nq, gc, nh, gh, ?_, hta, ?_, hr⟩
    · simpa only [genMeanK, Gen.emitted] using h4
    · simpa only [Gen.emitted, tagged_bo, Sure.bunt] using h7

end

/-! ## The frame -/

section Frame
variable {σ : Type} {lib : Lib} {O : Oracle σ} {c : Straight Map} {gul : Noun} {Inv : σ → Prop} {ν : σ → Needs}

/-- `%hcp` pushes `(%meac, n)`. -/
theorem goJ_pushMeanK {o : Nat} {n body : Noun} {th : Jmp}
    (hb : HoonMap.get c.blocks o = some ⟨[], [Pole.hcp n body], Termin.hop th⟩)
    (st : σ) (regs : Map (Option Noun)) (t : Trace) :
    goJ lib O c gul st regs t (jmp0 o) = goJ lib O c gul st regs ((Tag.meac, n) :: t) th := by
  rw [goJ_jmp0 _ _ _ _ hb, execBlob_cons]
  simp [execPole, localPole, execBlob_hop]

/-- `%hce` pops. -/
theorem goJ_popMeanK {o : Nat} {n body : Noun} {th : Jmp}
    (hb : HoonMap.get c.blocks o = some ⟨[], [Pole.hce n body], Termin.hop th⟩)
    (st : σ) (regs : Map (Option Noun)) (fr : Nat × Noun) (t : Trace) :
    goJ lib O c gul st regs (fr :: t) (jmp0 o) = goJ lib O c gul st regs t th := by
  rw [goJ_jmp0 _ _ _ _ hb, execBlob_cons]
  simp [execPole, localPole, popTrace, execBlob_hop]

/-- **The frame of a constant `%mean` in the program**: the prologue `prol`
pushes `(%meac, n)` and goes to `o`, the epilogue `epil` pops and goes to `th`. -/
def FrameOKMeanK (c : Straight Map) (n body : Noun) (prol o epil : Nat) (th : Jmp) : Prop :=
  HoonMap.get c.blocks prol = some ⟨[], [Pole.hcp n body], Termin.hop (jmp0 o)⟩ ∧
  HoonMap.get c.blocks epil = some ⟨[], [Pole.hce n body], Termin.hop th⟩

/-- **The frame part** (the text of `frameOK_goesR`): the code from `o` at
`(%meac, n) :: t` against `+mink` at `fm :: tm` is the code from the
prologue at `t` against `tm`. -/
theorem frameOKMeanK_goesR {n body : Noun} {prol o epil : Nat} {th : Jmp} (F : FrameOKMeanK c n body prol o epil th)
    {sur : Sure S} {r : Tone} (hfit : ∀ p, r = Tone.zero p → FitsS sur p) {K : Nat → Prop} {st : σ}
    {regs : Map (Option Noun)} {fm : Nat × Noun} {t tm : Trace}
    (G : GoalSemCM lib O c gul Inv ν K st regs ((Tag.meac, n) :: t) (fm :: tm) (jmp0 o) (CGoal.next sur (jmp0 epil)) r) :
    GoalSemCM lib O c gul Inv ν K st regs t tm (jmp0 prol) (CGoal.next sur th) r := by
  have epush : ∀ st regs, goJ lib O c gul st regs t (jmp0 prol) = goJ lib O c gul st regs ((Tag.meac, n) :: t) (jmp0 o) :=
    fun st regs => goJ_pushMeanK F.1 st regs t
  have epop : ∀ st regs, goJ lib O c gul st regs ((Tag.meac, n) :: t) (jmp0 epil) = goJ lib O c gul st regs t th :=
    fun st regs => goJ_popMeanK F.2 st regs (Tag.meac, n) t
  cases r with
  | zero p =>
    refine ⟨fun hf => ?_, fun hf => absurd (hfit p rfl) hf⟩
    obtain ⟨st', regs', hI, hle, hh, hk, e⟩ := G.1 hf
    exact ⟨st', regs', hI, hle, hh, hk, by rw [epush st regs, e, epop]⟩
  | one b =>
    obtain ⟨ton, st', hI, hle, e, hrel⟩ := G
    exact ⟨ton, st', hI, hle, by rw [epush st regs]; exact e, hrel⟩
  | two tr =>
    obtain ⟨ton, st', hI, hle, e, hrel⟩ := G
    exact ⟨ton, st', hI, hle, by rw [epush st regs]; exact e, hrel⟩

end Frame

/-- Under `%next bunt`, a bad tone is a crash with `+mink`'s trace. -/
theorem badC_buntMeanK {th : Jmp} {tm : Trace} {x : Tone} (h : BadC (CGoal.next (Sure.bunt : Sure S) th) tm x) :
    x = Tone.two tm := by
  rcases h with e | ⟨p, _, hp⟩
  · exact e
  · exact absurd (fitsS_bunt p) hp

theorem stopTag_meanMeanK : stopTag Tag.mean = true := by decide

section Main
variable {snd : Nomm → NeedOrd → Bool}

/-- **A constant `%mean` over a member of `SurGBT Ap` is in `SurGBT`** at
the sure needs `q` is `+sound` at and whose products fit (so `+past-if`
emits nothing): the trap `p` with `LOKSFH` and `NoBondH`, and `+mack` of
every trap giving the constant (`hK`).  The text of `surGBT_n11dKept`: no
`toke`, the trap's code under `%next bunt` in place of the clue's (a crash
of the trap is the hint's, its product goes nowhere), the frame
`(%meac, n)` against `+mink`'s `(%mean, trap)` (`FrameRel.meac`). -/
theorem surGBT_meanK {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {fp fq : Noun} {p q : Nomm}
    {b : Bell} {body : Noun} {k : Option Noun} {n : Noun} (hk : meanKonst env b k = some n)
    {Ap : Sure S → Prop} (Hq : SurGBT (S := S) (Map := Map) snd lib N env P Ap fq q)
    (Hp : LOKSFH (S := S) (Map := Map) (snd := snd) lib N env P fp p) (hcp : sixCount p ≤ 255)
    (hnp : NoBondH (S := S) (Map := Map) snd env p)
    (hK : ∀ {s gul : Noun} {tm : Trace} {trap : Noun}, P s → Mink lib gul tm s fp (Tone.zero trap) →
      MackRel lib trap n) :
    SurGBT (S := S) (Map := Map) snd lib N env P (fun sur => Ap sur ∧ SoundK snd q sur ∧ FitP lib P fq sur)
      (n3 (A 11) (C (A Tag.mean) fp) fq) (Nomm.mean p b q body k) := by
  have hst : stopTag Tag.mean = true := stopTag_meanMeanK
  intro sup sur th region g0 g1 nex hA b0 d0 hu hcl hcb th1 th2 hta hsd hcs hsl hr
  obtain ⟨nq, gc, nh, gh, h3, hqa, h6, h7⟩ := runLCH_meanK_sur hk hA.2.1 hr
  have e0 : entries (ofSure (Sure.bunt : Sure S)) = [] := entries_ofSure _
  -- the state after the epilogue
  have dA : (genMeanK g0 n body th).drop = false := d0
  have reA : (genMeanK g0 n body th).re = g0.re := rfl
  have boA : (genMeanK g0 n body th).bo = g0.bo + 1 := rfl
  have bA : ∀ k, HoonMap.get (genMeanK g0 n body th).blocks k =
      if k = g0.bo then some ⟨[], [Pole.hce n body], Termin.hop th⟩ else HoonMap.get g0.blocks k := by
    intro k; simp only [genMeanK, Gen.emitted, d0, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]
  have GA : GrowU g0 (genMeanK g0 n body th) :=
    growU_emit (g := g0) (b := ⟨[], [Pole.hce n body], Termin.hop th⟩)
      (fun j hj => by simp only [finJumps, List.mem_singleton] at hj; subst hj; exact ⟨th1, th2⟩) hu
  have uA : UpBelow (genMeanK g0 n body th) := GA.up hu
  have clA : Clear (genMeanK g0 n body th) := hcl.growU GA
  have cbA : CondBelow (genMeanK g0 n body th) := fun k hk => hcb k hk
  have extA : Ext g0 (genMeanK g0 n body th) := ⟨Nat.le_refl _, by rw [boA]; omega, dA.trans d0.symm,
    fun o ho => by rw [bA, if_neg (by omega)]⟩
  -- the formula, its bond
  have RQ := Hq hA.1 (by rw [boA]; omega) dA uA clA cbA (by simp only [jmp0]; omega)
    (by simp only [jmp0]; rw [boA]; omega) rfl hsd hcs
    (fun x hx => ⟨(hsl x hx).1, (hsl x hx).2⟩) h3
  have dc : gc.drop = false := RQ.ext.2.2.1.trans dA
  have uc : UpBelow gc := RQ.grow.up uA
  have RG := RQ.bound (fun x hx => (hsl x hx).1) hqa dc uc region
  have nql : ∀ e ∈ entries nq.laz, g0.bo + 1 ≤ e.1 ∧ e.1 < gc.bo := fun e he =>
    ⟨by have := (RQ.labs e he).1; rw [boA] at this; exact this, (RQ.labs e he).2.1⟩
  have boD : ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).bo = gc.bo + 1 := by
    simp only [tagged_bo, Gen.emitted]
  have dD : ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).drop = false := by
    simp only [tagged_drop, Gen.emitted]; exact dc
  have rcA : g0.re ≤ gc.re := by have := RG.ext.1; simp only [reA, tagged_re, Gen.emitted] at this; exact this
  have bcA : g0.bo + 1 ≤ gc.bo := by have := RQ.ext.2.1; rw [boA] at this; exact this
  -- the prologue
  have GE : GrowU ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region)
      (((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).emitted
        ⟨[], [Pole.hcp n body], Termin.hop (jmp0 gc.bo)⟩) :=
    growU_emit (fun j hj => by
      simp only [finJumps, List.mem_singleton] at hj; subst hj; simp only [jmp0, boD]; omega) (RG.grow.up uA)
  have uE := GE.up (RG.grow.up uA)
  have clE := (clA.growU RG.grow).growU GE
  have cbE : CondBelow (((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).emitted
        ⟨[], [Pole.hcp n body], Termin.hop (jmp0 gc.bo)⟩) := RG.cfr.below cbA
  -- the trap, under `%next bunt`
  obtain ⟨⟨Qh, RSh⟩, -, -, hflh, -⟩ := Hp.run (sup := sup) (L := ofSure Sure.bunt) (th := jmp0 (gc.bo + 1))
    (region := region) (Or.inr e0) hcp (by simp only [Gen.emitted]; omega) (by simp only [emitted_drop]; exact dD)
    uE clE cbE (by simp only [jmp0]; omega) (by simp only [jmp0, Gen.emitted, tagged_bo]; omega) rfl
    (by rw [e0]; simp) trivial
    (fun x hx => by simp [Sure.bunt, ofSure, NMem] at hx)
    (fun e he => by rw [e0] at he; cases he) (by rw [e0]; simp) (fun e he => by rw [e0] at he; cases he)
    (flat_ofSure _) trivial (fun e he => by rw [e0] at he; cases he) h6
  have RGh := RSh.toRunOKLB.toGB (fun r hr => by simp [Sure.bunt, NMem] at hr)
  obtain ⟨hfh, hbh⟩ := hnp h6
  have dh : gh.drop = false := RSh.drop.trans (by simp only [emitted_drop]; exact dD)
  obtain ⟨rfl, r1, b1, d1, c1, k1⟩ := copyL_bond1 dh hfh hbh h7
  -- the copy block, the facts of the states
  have hb1 : ∀ k, HoonMap.get g1.blocks k =
      if k = gh.bo then some ⟨[], [], Termin.hop nh.th⟩ else HoonMap.get gh.blocks k := by
    intro k; rw [k1 k]; simp [Gen.emitted, dh, HoonMap.get_put]
  have hargs : nh.th.args = [] := nextArgs_nil RGh.ent rfl
  have boh : gc.bo + 2 ≤ gh.bo := by have := RGh.ext.2.1; simp only [Gen.emitted, tagged_bo] at this; omega
  have reh : gc.re ≤ gh.re := by have := RGh.ext.1; simp only [Gen.emitted, tagged_re] at this; omega
  have E1 : Ext gh g1 := ⟨by omega, by omega, by rw [d1, dh], fun o ho => by rw [hb1, if_neg (by omega)]⟩
  have EE1 : Ext (((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).emitted
      ⟨[], [Pole.hcp n body], Termin.hop (jmp0 gc.bo)⟩) g1 := RGh.ext.trans E1
  have ED1 : Ext ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region) g1 := (ext_emit _ _).trans EE1
  have EA1 : Ext (genMeanK g0 n body th) g1 := RG.ext.trans ED1
  have CF1 : CondFresh ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region) g1 :=
    (condFresh_of_eq (Nat.le_refl _) rfl).trans (RGh.cfr.trans (condFresh_of_eq (by omega) c1))
  have CFA1 : CondFresh (genMeanK g0 n body th) g1 := RG.cfr.trans CF1
  have GG : Grow gh g1 := Grow.congr_right (grow_emit (g := gh) (b := ⟨[], [], Termin.hop nh.th⟩) (fun j hj => by
    simp [finJumps] at hj; subst hj; exact ⟨RGh.lo, RGh.hi⟩)) b1 (by rw [d1, emitted_drop, dh]) k1
  have hent : entries (mk Sure.bunt [] [(gc.bo, nq.laz)] : Lazy S) = (gc.bo, nq.laz) :: entries nq.laz :=
    entries_bound1 _ _ _
  have hent' : entries (mk ⟨nh.laz.sure.ned, HoonSet.uni nh.laz.sure.lok HoonSet.empty⟩ [] [(gc.bo, nq.laz)] :
      Lazy S) = (gc.bo, nq.laz) :: entries nq.laz := entries_bound1 _ _ _
  have hentN : entries nh.laz = [] := by rw [entries_flat hflh, hbh]
  have hmem : ∀ e, e ∈ entries (mk ⟨nh.laz.sure.ned, HoonSet.uni nh.laz.sure.lok HoonSet.empty⟩ [] [(gc.bo, nq.laz)] :
      Lazy S) → e ∈ entries (mk Sure.bunt [] [(gc.bo, nq.laz)] : Lazy S) := fun e he => by
    rw [hent]; rw [hent'] at he; exact he
  have hnot : ∀ o, o ≠ gc.bo → (o < g0.bo + 1 ∨ gc.bo ≤ o) →
      o ∉ (entries (mk ⟨nh.laz.sure.ned, HoonSet.uni nh.laz.sure.lok HoonSet.empty⟩ []
        [(gc.bo, nq.laz)] : Lazy S)).map Prod.fst := fun o ho hlt hm => by
    rw [hent', List.map_cons, List.mem_cons] at hm
    rcases hm with hm | hm
    · exact ho hm
    · obtain ⟨e, he, ee⟩ := List.mem_map.mp hm
      have := nql e he; omega
  -- the blocks in the program
  have blocks : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      ∀ (c : Straight Map) (ned : Need) {σ : Type} (O : Oracle σ) (gul : Noun) (st : σ) (t : Trace) (s0 s : Noun),
      AgreeUB lib O c gul st t cf ned g0 g1
        (mk ⟨nh.laz.sure.ned, HoonSet.uni nh.laz.sure.lok HoonSet.empty⟩ [] [(gc.bo, nq.laz)]) s0 s →
      HoonMap.get c.blocks gh.bo = some ⟨[], [], Termin.hop nh.th⟩ ∧
      FrameOKMeanK c n body (gc.bo + 1) gc.bo g0.bo th := by
    intro cf hcf c ned σ O gul st t s0 s ag
    have bE : HoonMap.get g1.blocks (gc.bo + 1) =
        some ⟨[], [Pole.hcp n body], Termin.hop (jmp0 gc.bo)⟩ := by
      rw [EE1.2.2.2 _ (by simp only [Gen.emitted, tagged_bo]; omega), ← boD]; exact hk_emitted_self dD _
    refine ⟨?_, ?_, ?_⟩
    · rw [ag.1 gh.bo (by omega) (by omega) (hnot _ (by omega) (Or.inr (by omega))), hb1, if_pos rfl]
      simp [unproxyBlob, renBlob, renFin, renJmp_nil _ hargs]
    · rw [ag.1 _ (by omega) (by omega) (hnot _ (by omega) (Or.inr (by omega))), bE]
      simp [unproxyBlob, renBlob, renFin, renPole, renJmp, jmp0]
    · rw [ag.1 _ (Nat.le_refl _) (by omega) (hnot _ (by omega) (Or.inl (by omega))),
        EA1.2.2.2 _ (by rw [boA]; omega), bA, if_pos rfl]
      simp [unproxyBlob, renBlob, renFin, renPole, renJmp_nil _ hta]
  have agh : ∀ {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
      {cf : Map (Nat × List Nat)} {ned : Need} {s0 s : Noun},
      AgreeUB lib O c gul st t cf ned g0 g1
        (mk ⟨nh.laz.sure.ned, HoonSet.uni nh.laz.sure.lok HoonSet.empty⟩ [] [(gc.bo, nq.laz)]) s0 s →
      AgreeUB lib O c gul st t cf ned (((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).emitted
        ⟨[], [Pole.hcp n body], Termin.hop (jmp0 gc.bo)⟩) gh nh.laz s0 s := fun ag =>
    ⟨fun o h0 h1 hn => by
      simp only [Gen.emitted, tagged_bo] at h0
      rw [ag.1 o (by omega) (by omega) (hnot o (by omega) (Or.inr (by omega))), hb1, if_neg (by omega)],
     fun e he => by rw [hentN] at he; cases he⟩
  have agq : ∀ {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
      {cf : Map (Nat × List Nat)} {ned : Need} {s0 s : Noun},
      AgreeUB lib O c gul st t cf ned g0 g1
        (mk ⟨nh.laz.sure.ned, HoonSet.uni nh.laz.sure.lok HoonSet.empty⟩ [] [(gc.bo, nq.laz)]) s0 s →
      AgreeUB lib O c gul st t cf ned (genMeanK g0 n body th)
        ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region) (mk Sure.bunt [] [(gc.bo, nq.laz)]) s0 s :=
    fun ag =>
    ⟨fun o h0 h1 hn => by
      rw [ag.1 o (by rw [boA] at h0; omega) (by have := ED1.2.1; omega) (by rw [hent']; rw [hent] at hn; exact hn),
        ED1.2.2.2 o h1],
     fun e he => by
      obtain ⟨A, B, th', a1, a2, a3⟩ := ag.2 e (by rw [hent']; rw [hent] at he; exact he)
      have l2 := (RG.labs e he).2.1
      exact ⟨A, B, th', by rw [← ED1.2.2.2 e.1 l2]; exact a1, a2, a3.mono (by have := ED1.1; omega)⟩⟩
  -- the kept registers across the trap
  have hkc : ∀ (ned : Need) (regs regs1 : Map (Option Noun)), (∀ x, NMem ned x → g1.re ≤ x) →
      (∀ x, ((x < (((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).emitted
        ⟨[], [Pole.hcp n body], Termin.hop (jmp0 gc.bo)⟩).re ∨ NMem ned x) ∧
        ¬ GMem (CGoal.next (Sure.bunt : Sure S) (jmp0 (gc.bo + 1))) x) →
        SkaModel.read x regs1 = SkaModel.read x regs) →
      ∀ x, ((x < g0.re ∨ NMem ned x) ∧ ¬ GMem (CGoal.next sur th) x) →
        SkaModel.read x regs1 = SkaModel.read x regs := fun ned regs regs1 hned hk1 x ⟨a, _⟩ =>
    hk1 x ⟨a.imp (fun h => by simp only [Gen.emitted, tagged_re]; omega) id, fun hg => by
      simp [GMem, Sure.bunt, NMem] at hg⟩
  have hKm : ∀ (ned : Need) x, ((x < g0.re ∨ NMem ned x) ∧ ¬ GMem (CGoal.next sur th) x) →
      ((x < (genMeanK g0 n body th).re ∨ NMem ned x) ∧ ¬ GMem (CGoal.next sur (jmp0 g0.bo)) x) :=
    fun ned x ⟨a, b⟩ => ⟨a, fun hg => b (by simpa [GMem] using hg)⟩
  refine ⟨extA.trans EA1, GA.trans (RG.grow.trans (GE.trans (RGh.grow.trans (GG.toU (RGh.grow.up uE))))),
    (condFresh_of_eq (g0 := g0) (g1 := genMeanK g0 n body th) (Nat.le_refl _) rfl).trans CFA1,
    by simp only [jmp0]; omega, by simp only [jmp0]; omega,
    Or.inl ⟨_, by simp only [jmp0]; rw [hb1, if_pos rfl], rfl, rfl⟩,
    fun r hr => Or.inr ?_, RGh.dist, fun e he => ?_, fun e he => ?_, ?_, fun s hs hf => ?_,
    fun r hr => by rw [c1]; exact RGh.ncond r hr, fun e he r hr => ?_, ?_, ?_⟩
  · rcases RGh.regs r hr with h | h
    · simp [GMem, Sure.bunt, NMem] at h
    · simp only [Gen.emitted, tagged_re] at h; constructor <;> omega
  · have he' := hmem e he
    refine ⟨(RG.eregs e he').1, fun r hr => ?_⟩
    have := (RG.eregs e he').2 r hr
    refine ⟨this.1.imp (fun h => by simpa [GMem] using h) (fun h => h), ?_⟩
    have := this.2; simp only [tagged_re, Gen.emitted] at this; omega
  · have he' := hmem e he
    obtain ⟨l1, l2, B, th', hB⟩ := RG.labs e he'
    exact ⟨by rw [boA] at l1; omega, by have := ED1.2.1; omega, B, th', by rw [ED1.2.2.2 e.1 l2]; exact hB⟩
  · rw [hent', List.map_cons, List.nodup_cons]
    exact ⟨fun hm => by obtain ⟨e, he, ee⟩ := List.mem_map.mp hm; have := nql e he; simp at ee; omega, RQ.nodup⟩
  · have hf' : ¬ FitsS nh.laz.sure s := fun hf2 => hf ⟨hf2.1, (looks_uni _ _ _).mpr ⟨hf2.2, looks_empty _⟩⟩
    have NC := RGh.nec s hs hf'
    refine ⟨fun gul m' tm r hm => ?_, fun gul tm => ?_⟩
    · cases m' with
      | zero => rw [minkF_zero_fuel] at hm; cases hm
      | succ m =>
        rw [minkF_n11d_stop lib gul m tm s hst] at hm
        cases hmh : minkF lib gul m tm s fp with
        | none => rw [hmh] at hm; cases hm
        | some rh =>
          have := badC_buntMeanK (NC.1 gul m tm rh hmh); subst this
          rw [hmh] at hm; simp only [tbind] at hm; cases hm
          exact Or.inl rfl
    · obtain ⟨rh, hm, hb⟩ := NC.2 gul tm
      have := badC_buntMeanK hb; subst this
      exact ⟨_, mink_n11d_clue hst hm (fun q => by simp), Or.inl rfl⟩
  · have he' := hmem e he
    rw [CF1.get_lt ((RG.eregs e he').2 r hr).2]; exact RG.econd e he' r hr
  · intro cf hcf c ned σ Inv ν O m' gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    obtain ⟨hcp', F⟩ := blocks cf hcf c ned O gul st t s0 s (ag st t)
    have ecopy : ∀ st regs, goJ lib O c gul st regs t (jmp0 gh.bo) = goJ lib O c gul st regs t nh.th :=
      fun st regs => by rw [goJ_jmp0 _ _ _ _ hcp', execBlob_hop]
    cases m' with
    | zero => rw [minkF_zero_fuel] at hm; cases hm
    | succ m =>
      rw [minkF_n11d_stop lib gul m tm s hst] at hm
      cases hmh : minkF lib gul m tm s fp with
      | none => rw [hmh] at hm; cases hm
      | some rh =>
        rw [hmh] at hm
        have Gh := RGh.sem cf (fun k hk => by rw [hcf k (by omega), c1]) c ned σ Inv ν O m gul hN hS
          (oracleFwd_le hF (Nat.le_succ m)) st t tm s0 s rh
          hI htr hs hmh (fun st' => agh (ag st' t)) (fun x hx => by have := hned x hx; omega) regs
          ⟨hh.1, ((looks_uni _ _ _).mp hh.2).1⟩ hn
        cases rh with
        | zero v =>
          simp only [tbind] at hm
          obtain ⟨st1, regs1, hI1, hle1, hh1, hk1, e1⟩ := Gh.1 (fitsS_bunt v)
          have hn1 : HoldsN ned regs1 s0 := holdsN_frame ned hn (fun x hx => hk1 x ⟨Or.inr hx, fun hg => by
            simp [GMem, Sure.bunt, NMem] at hg⟩)
          have Gq := RG.sem cf (fun k hk => by rw [hcf k (by have := CF1.1; omega), CF1.get_lt hk]) c ned σ Inv ν O m gul
            hN hS (oracleFwd_le hF (Nat.le_succ m)) st1 ((Tag.meac, n) :: t) ((Tag.mean, v) :: tm) s0 s r hI1
            (Forall2.cons (FrameRel.meac (hK hs ⟨m, hmh⟩)) (frames_mono hle1 htr)) hs hm (fun st' t' => agq (ag st' t'))
            (fun x hx => by have := hned x hx; simp only [tagged_re, Gen.emitted]; omega) regs1 (holdsS_bunt _ _) hn1
          exact goalSemCM_step hle1 (hkc ned regs regs1 hned hk1) (by rw [ecopy, e1]) _ _
            (goalSemCM_monoK (hKm ned) _ _
              (frameOKMeanK_goesR F (fun p e => hA.2.2 s hs gul _ p ⟨m, by rw [← e]; exact hm⟩) Gq))
        | one b =>
          simp only [tbind] at hm; cases hm
          obtain ⟨ton, st2, hI2, hle2, e2, hrel⟩ := Gh
          exact ⟨ton, st2, hI2, hle2, by rw [ecopy]; exact e2, hrel⟩
        | two tr =>
          simp only [tbind] at hm; cases hm
          obtain ⟨ton, st2, hI2, hle2, e2, hrel⟩ := Gh
          exact ⟨ton, st2, hI2, hle2, by rw [ecopy]; exact e2, hrel⟩
  · intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨hcp', F⟩ := blocks cf hcf c ned O gul st t s0 s (ag st t)
    have ecopy : ∀ st regs, goJ lib O c gul st regs t (jmp0 gh.bo) = goJ lib O c gul st regs t nh.th :=
      fun st regs => by rw [goJ_jmp0 _ _ _ _ hcp', execBlob_hop]
    rw [ecopy] at hres
    obtain ⟨rh, hmh, Gh⟩ := RGh.semB cf (fun k hk => by rw [hcf k (by omega), c1]) c ned σ Inv ν O gul hN hS hB
      st t tm s0 s hI htr hs (fun st' => agh (ag st' t)) (fun x hx => by have := hned x hx; omega) regs
      ⟨hh.1, ((looks_uni _ _ _).mp hh.2).1⟩ hn res hres
    cases rh with
    | zero v =>
      obtain ⟨st1, regs1, hI1, hle1, hh1, hk1, e1⟩ := Gh.1 (fitsS_bunt v)
      have hn1 : HoldsN ned regs1 s0 := holdsN_frame ned hn (fun x hx => hk1 x ⟨Or.inr hx, fun hg => by
        simp [GMem, Sure.bunt, NMem] at hg⟩)
      rw [e1, goJ_pushMeanK F.1 st1 regs1 t] at hres
      obtain ⟨r, hmq, Gq⟩ := RG.semB cf (fun k hk => by rw [hcf k (by have := CF1.1; omega), CF1.get_lt hk]) c ned σ Inv ν
        O gul hN hS hB st1 ((Tag.meac, n) :: t) ((Tag.mean, v) :: tm) s0 s hI1
        (Forall2.cons (FrameRel.meac (hK hs hmh)) (frames_mono hle1 htr)) hs (fun st' t' => agq (ag st' t'))
        (fun x hx => by have := hned x hx; simp only [tagged_re, Gen.emitted]; omega) regs1 (holdsS_bunt _ _) hn1
        res hres
      exact ⟨r, mink_n11d_stop hst hmh hmq, goalSemCM_step hle1 (hkc ned regs regs1 hned hk1) (by rw [ecopy, e1]) _ _
        (goalSemCM_monoK (hKm ned) _ _
          (frameOKMeanK_goesR F (fun p e => hA.2.2 s hs gul _ p (by rw [← e]; exact hmq)) Gq))⟩
    | one b =>
      obtain ⟨ton, st2, hI2, hle2, e2, hrel⟩ := Gh
      exact ⟨_, mink_n11d_clue hst hmh (fun q => by simp), ton, st2, hI2, hle2, by rw [ecopy]; exact e2, hrel⟩
    | two tr =>
      obtain ⟨ton, st2, hI2, hle2, e2, hrel⟩ := Gh
      exact ⟨_, mink_n11d_clue hst hmh (fun q => by simp), ton, st2, hI2, hle2, by rw [ecopy]; exact e2, hrel⟩

/-- An `IsReg` need meets what `+past-if` asks (`regLike_soundFit`). -/
theorem isReg_soundFitMeanK {q : Nomm} (hs : snd q NeedOrd.this = true) (lib : Lib) (P : Noun → Prop) (fq : Noun)
    {sur : Sure S} (hR : IsReg sur) : SoundK snd q sur ∧ FitP lib P fq sur := by
  obtain ⟨r, rfl⟩ := hR
  exact regLike_soundFit hs lib P fq (regLike_lazyReg r)

/-- **A constant `%mean` over a member of `RegGBT` is in `RegGBT`**, with
`+sound` of `%this` for the formula (`surGBT_meanK` at `IsReg`, through
`RegGBT.toSur`, `regLike_soundFit`, `RegGBT.ofSur`). -/
theorem regGBT_meanK {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {fp fq : Noun} {p q : Nomm}
    {b : Bell} {body : Noun} {k : Option Noun} {n : Noun} (hk : meanKonst env b k = some n)
    (Hq : RegGBT (S := S) (Map := Map) snd lib N env P fq q) (hsnd : snd q NeedOrd.this = true)
    (Hp : LOKSFH (S := S) (Map := Map) (snd := snd) lib N env P fp p) (hcp : sixCount p ≤ 255)
    (hnp : NoBondH (S := S) (Map := Map) snd env p)
    (hK : ∀ {s gul : Noun} {tm : Trace} {trap : Noun}, P s → Mink lib gul tm s fp (Tone.zero trap) →
      MackRel lib trap n) :
    RegGBT (S := S) (Map := Map) snd lib N env P (n3 (A 11) (C (A Tag.mean) fp) fq) (Nomm.mean p b q body k) :=
  RegGBT.ofSur (SurGBT.mono (fun s hs => ⟨hs, isReg_soundFitMeanK hsnd lib P fq hs⟩)
    (surGBT_meanK hk (RegGBT.toSur Hq) Hp hcp hnp hK))

end Main

/-! ## The shape of a constant `%mean` (a `%6` branch) -/

section Shape
variable {snd : Nomm → NeedOrd → Bool}

/-- **`ShapeH` of a constant `%mean`** (the text of `shapeH_n11dKept`):
`q`'s count plus the bond of `+lazy-bound`; the trap `p`'s run under `%next
bunt` changes the tags and conditions only within the region and leaves no
entry with a tag outside it (`Tp`, what `TagCA` gives of a hint-free trap),
and has no bond (`NoBondH`). -/
theorem shapeH_meanK {env : CallEnv} {Ap : Sure S → Prop} {p q : Nomm} {b : Bell} {body : Noun}
    {k : Option Noun} {n : Noun} {kq : Nat} (hk : meanKonst env b k = some n)
    (Hq : ShapeH (S := S) (Map := Map) snd env Ap q kq)
    (hA : ∀ sur : Sure S, Ap sur → HoonSet.small sur.lok = true ∧ snd q (needToOrd sur.ned) = true)
    (hnp : NoBondH (S := S) (Map := Map) snd env p)
    (Tp : ∀ {sup : Option Nomm} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
      g0.drop = false →
      runLCH (S := S) (Map := Map) env snd true sup p (CGoalL.next (ofSure Sure.bunt) th) region g0 =
        some (nex, g1) →
      TagCS region g0 g1 ∧ ∀ e ∈ entries nex.laz, TagOK region g1 e.1) :
    ShapeH (S := S) (Map := Map) snd env Ap (Nomm.mean p b q body k) (kq + 1) := by
  intro sup sur th region g0 g1 nex hAp d0 hta hr
  obtain ⟨nq, gc, nh, gh, h3, hqa, h6, h7⟩ := runLCH_meanK_sur hk (hA sur hAp) hr
  have S0 : TagCS region g0 (genMeanK g0 n body th) := TagCS.of_eqs rfl rfl rfl
  obtain ⟨Sq, Eq, Lq⟩ := Hq hAp (show (genMeanK g0 n body th).drop = false from d0) rfl h3
  have dc : gc.drop = false := Sq.drop.trans d0
  obtain ⟨SB, TB⟩ := lazyBound_tagCS nq.th region dc
  have SP : TagCS region ((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region)
      (((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).emitted
        ⟨[], [Pole.hcp n body], Termin.hop (jmp0 gc.bo)⟩) := TagCS.of_eqs rfl rfl rfl
  have dP : (((gc.emitted ⟨[], [], Termin.hop nq.th⟩).tagged gc.bo region).emitted
      ⟨[], [Pole.hcp n body], Termin.hop (jmp0 gc.bo)⟩).drop = false := SP.drop.trans (SB.drop.trans dc)
  obtain ⟨SM, EM⟩ := Tp dP h6
  have dm : gh.drop = false := SM.drop.trans dP
  have hent : entries (mk Sure.bunt [] [(gc.bo, nq.laz)] : Lazy S) = (gc.bo, nq.laz) :: entries nq.laz :=
    entries_bound1 _ _ _
  obtain ⟨SC, EC⟩ := copyL_tagC h7 EM (fun e he => by
    rw [hent, List.mem_cons] at he
    rcases he with rfl | he
    · exact (TB.cs SP).cs SM
    · exact (((Eq e he).cs SB).cs SP).cs SM)
  obtain ⟨hf, hb⟩ := hnp h6
  obtain ⟨rfl, -⟩ := copyL_bond1 dm hf hb h7
  refine ⟨S0.trans (Sq.trans (SB.trans (SP.trans (SM.trans SC)))), EC, ?_⟩
  rw [entries_bound1, List.length_cons]
  omega

end Shape

end Comp
end SkaModel
end Formalization
