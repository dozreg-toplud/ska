import lemmas.Ska.CompGenClassL

/-!
# The `%done` top on `ConsFrag`: the unary contract with no premise

README Gaps 12.39, item 12.  Under `%done`, `[0 a]` and the cons begin with
the block `[don re]` and run under `%next (lazy-from-reg re)` into it
(`runLC_done_next`); that goal meets `PremG` (`cm2_premDon`), and a
`RunOKGen` run there with `GrowU` is `RunOKGD` under `%done`
(`runOKGD_done_of_gen`, the text of `runOKGB_of_next` with `AgreeG`).  `[1 k]`
under `%done` is the old tower's (`uokc_of_uok`, `RunOKGC.toB`,
`RunOKGB.toGD`).  `[7 p q]`: `q` under `%done` (the class itself), `p` under
`q`'s result in `NextGCS` (its `PremG` from `q`'s `RunOKGD` and the result
facts the class carries), `runOKGD_sevenG`.

* `DoneGS`: the class under `%done`: `RunOKGD` and, of the result, `LabUniq`,
  `Clean` needs, `SureApart` (what `p`'s `PremG` reads).
* `doneGS_consFrag`: every nomm of `ConsFrag` is in it at every `P`.
* `contract_consFrag`: the unary contract of every nomm of `ConsFrag`
  (`finishLUC_contractGD`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **A `RunOKGen` run under `%next (lazy-from-reg re)` into the block
`[don re]`, with `GrowU`, is `RunOKGD` under `%done`** (labels possibly
repeated; the text of `runOKGB_of_next`). -/
theorem runOKGD_done_of_gen {lib : Lib} {N : Needs} {P : Noun → Prop} {f : Noun} {Q : Wit} {x : Bool}
    {g0 g' : Gen Map} {nex : NextL S} (hu : UpBelow g0) (hcb : CondBelow g0) (d0 : g0.drop = false)
    (R : RunOKGen lib N P f (ofSure (lazyReg g0.re : Sure S)) (jmp0 g0.bo) Q x
      ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) g' nex)
    (Gu : GrowU ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) g') :
    RunOKGD lib N P f (CGoal.done : CGoal S) g0 g' nex := by
  have e0 : entries (ofSure (lazyReg g0.re : Sure S)) = [] := entries_ofSure _
  have l1 := R.re
  have l2 := R.bo
  simp only [Gen.emitted] at l1 l2
  have E0 : Ext g0 ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) :=
    (ext_re _).trans (ext_emit _ _)
  have E1 : Ext ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) g' :=
    ⟨R.re, R.bo, R.drop, fun o ho => R.keep o ho (by rw [e0]; simp)⟩
  have G0 : GrowU g0 ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) :=
    ((grow_re g0).trans (grow_emit (g := { g0 with re := g0.re + 1 }) (b := ⟨[], [], Termin.don g0.re⟩)
      (fun j hj => by simp [finJumps] at hj))).toU hu
  have C0 : CondFresh g0 ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) :=
    condFresh_of_eq (by simp [Gen.emitted]) rfl
  have hb : HoonMap.get g'.blocks g0.bo = some ⟨[], [], Termin.don g0.re⟩ := by
    rw [R.keep _ (by simp only [Gen.emitted]; omega) (by rw [e0]; simp)]
    simp only [Gen.emitted, d0, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]
  have gl : ∀ r, NMem (ofSure (lazyReg g0.re : Sure S)).sure.ned r → r = g0.re := fun r h => by
    simp only [lazyReg, ofSure, NMem] at h; exact h
  have bad : ∀ tm r, BadC (CGoal.next (lazyReg g0.re : Sure S) (jmp0 g0.bo)) tm r → BadC (CGoal.done : CGoal S) tm r :=
    fun tm r h => by
      rcases h with e | ⟨p, _, hp⟩
      · exact Or.inl e
      · exact absurd (fitsS_lazyReg g0.re p) hp
  have nlab : ∀ e ∈ entries nex.laz, g0.bo < e.1 ∧ e.1 < g'.bo := fun e he => by
    rcases (R.labs e he).1 with h | h
    · rw [e0] at h; simp at h
    · simp only [Gen.emitted] at h; omega
  have er : ∀ e ∈ entries nex.laz, ∀ r, NMem e.2.sure.ned r → g0.re ≤ r ∧ r < g'.re := fun e he r hr => by
    rcases (R.eregs e he).2 r hr with ⟨e0', he0, _⟩ | h | h
    · rw [e0] at he0; cases he0
    · have := gl r h; omega
    · simp only [Gen.emitted] at h; omega
  have blk : ∀ (cf : Map (Nat × List Nat)) (c : Straight Map) (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ)
      (t : Trace) (ned : Need) (s0 s : Noun), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g'.cond k) →
      AgreeG lib O c gul st t cf ned g0 g' nex.laz s0 s →
      HoonMap.get c.blocks g0.bo = some ⟨[], [], Termin.don g0.re⟩ := by
    intro cf c σ O gul st t ned s0 s hcf ag
    have c0 : HoonMap.get cf g0.re = Option.none := by
      rw [hcf _ (by omega), R.cfr.get_lt (by simp [Gen.emitted])]
      exact condBelow_none hcb (Nat.le_refl _)
    rw [ag.1 _ (Nat.le_refl _) (by omega) (fun hm => by
      obtain ⟨e, he, e1⟩ := List.mem_map.mp hm
      have := (nlab e he).1; omega), hb]
    simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, renFin, unproxy_none c0]
  have agp : ∀ (cf : Map (Nat × List Nat)) (c : Straight Map) (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ)
      (t : Trace) (ned : Need) (s0 s : Noun), AgreeG lib O c gul st t cf ned g0 g' nex.laz s0 s →
      AgreeG lib O c gul st t cf ned ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) g' nex.laz
        s0 s :=
    fun cf c σ O gul st t ned s0 s ag =>
      ⟨fun o h0' h1 hn => ag.1 o (by simp only [Gen.emitted] at h0'; omega) h1 hn,
       fun o ho h0' => ag.2 o ho (by simp only [Gen.emitted] at h0'; omega)⟩
  refine ⟨E0.trans E1, G0.trans Gu, C0.trans R.cfr, R.lo, R.hi, ?_, fun r hr => ?_, R.dist,
    fun e he => ⟨(R.eregs e he).1, fun r hr => ⟨Or.inr (er e he r hr).1, (er e he r hr).2⟩⟩,
    fun e he => ⟨by have := (nlab e he).1; omega, (nlab e he).2, (R.labs e he).2⟩, R.labDisj,
    fun s hs hf => ⟨fun gul n tm r hm => bad tm r ((R.nec s hs hf).1 gul n tm r hm), fun gul tm => by
      obtain ⟨r, hm, hb'⟩ := (R.nec s hs hf).2 gul tm
      exact ⟨r, hm, bad tm r hb'⟩⟩, R.ncond, R.econd, ?_, ?_⟩
  · rcases R.ent with fr | e
    · exact Or.inl fr
    · simp only [GoalJ] at e
      rw [e]
      exact Or.inl ⟨_, hb, rfl, rfl⟩
  · rcases R.regs r hr with e | ⟨a, b⟩
    · have := gl r e; subst this; exact Or.inr ⟨Nat.le_refl _, by omega⟩
    · simp only [Gen.emitted] at a; exact Or.inr ⟨by omega, b⟩
  · intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    exact goalSemCM_done_of_next (blk cf c σ O gul st t ned s0 s hcf (ag st t))
      (goalSemCMD_toCM (R.sem cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm
        (fun st' t' => agp cf c σ O gul st' t' ned s0 s (ag st' t')) hned regs hh hn))
  · intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨r, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs
      (fun st' t' => agp cf c σ O gul st' t' ned s0 s (ag st' t')) hned regs hh hn res hres
    exact ⟨r, hm, goalSemCM_done_of_next (blk cf c σ O gul st t ned s0 s hcf (ag st t)) (goalSemCMD_toCM G)⟩

/-- **The goal `%next (lazy-from-reg re)` into `[don re]` meets `PremG`**,
from a state as a compile has it. -/
theorem cm2_premDon {g0 : Gen Map} (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0)
    (hcb : CondBelow g0) :
    PremG (Map := Map) (ofSure (lazyReg g0.re : Sure S)) (jmp0 g0.bo)
      ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) := by
  have e0 : entries (ofSure (lazyReg g0.re : Sure S)) = [] := entries_ofSure _
  have G1 : GrowU ({ g0 with re := g0.re + 1 } : Gen Map)
      ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) :=
    growU_emit (g := { g0 with re := g0.re + 1 }) (b := ⟨[], [], Termin.don g0.re⟩)
      (fun j hj => by simp [finJumps] at hj) hu
  have nE : ∀ e, e ∉ entries (ofSure (lazyReg g0.re : Sure S)) := fun e he => by rw [e0] at he; cases he
  refine
    { goal := ⟨(by simp only [Gen.emitted]; omega), ⟨(by simp only [jmp0]; omega),
          (by simp only [jmp0, Gen.emitted]; omega)⟩,
        (fun e he => absurd he (nE e)), (fun e he => absurd he (nE e)),
        (by unfold LabDisj; rw [e0]; exact List.Pairwise.nil), ?_, (fun r hr => ?_)⟩
      nc := fun r hr => ?_
      ec := fun e he => absurd he (nE e)
      lu := Raw.labUniq_ofSure _
      cl := ?_
      ecl := fun e he => absurd he (nE e)
      sa := fun e he => absurd he (nE e)
      ta := rfl
      bo := by simp only [Gen.emitted]; omega
      drop := by simp only [Gen.emitted]; exact d0
      up := G1.up hu
      clr := Clear.growU (g := ({ g0 with re := g0.re + 1 } : Gen Map)) hcl G1
      cb := fun k hk => by have := hcb k hk; simp only [Gen.emitted] at this ⊢; omega }
  · first | trivial | simp [Distinct, lazyReg, ofSure]
  · simp only [lazyReg, ofSure, NMem] at hr; subst hr; simp only [Gen.emitted]; omega
  · simp only [lazyReg, ofSure, NMem] at hr; subst hr; exact condBelow_none hcb (Nat.le_refl _)
  · first | trivial | simp [Clean, lazyReg, ofSure]

section Done
variable (S Map)

/-- **The class under `%done`**: from a state as a compile has it, a run
under `%done` meets `RunOKGD`, and its result `LabUniq`, `Clean` needs and
`SureApart` (what a later part's `PremG` reads). -/
def DoneGS (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop) (f : Noun) (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {region : List Nat} {g0 g2 : Gen Map} {nex : NextL S},
    1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    runLC env sup nm (CGoalL.done : CGoalL S) region g0 = some (nex, g2) →
    RunOKGD (Map := Map) lib N P f (CGoal.done : CGoal S) g0 g2 nex ∧ Raw.LabUniq nex.laz ∧
      Clean nex.laz.sure.ned ∧ (∀ e ∈ entries nex.laz, Clean e.2.sure.ned) ∧ SureApart nex.laz

end Done

/-- **`[0 axe]` (`axe ≥ 1`) and the cons under `%done`**, from `NextGCS`
at the goal into `[don re]`. -/
theorem cm2_done_of_next {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (hs : (∃ p q, nm = Nomm.cons p q) ∨ (∃ p q, nm = Nomm.n2 p q Option.none) ∨ (∃ ax, 1 ≤ ax ∧ nm = Nomm.n0 ax))
    (H : NextGCS (S := S) (Map := Map) lib N env P f nm) : DoneGS S Map lib N env P f nm := by
  intro sup region g0 g2 nex b0 d0 hu hcl hcb hr
  rw [runLC_done_next env sup hs region g0] at hr
  obtain ⟨Q, R, gu, nr, Res, FS⟩ := H (cm2_premDon b0 d0 hu hcl hcb) hr
  exact ⟨runOKGD_done_of_gen hu hcb d0 R gu, Res.lu, Res.cl, Res.ecl, Res.sa⟩

/-- **`[1 k]` under `%done`** (the old tower's `UOKC`). -/
theorem cm2_done_n1 (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop) (k : Noun) :
    DoneGS S Map lib N env P (quote k) (Nomm.n1 k) := by
  intro sup region g0 g2 nex b0 d0 hu hcl hcb hr
  have M1 : MinkEq lib P (quote k) (Nomm.n1 k) := genFrag_minkEq (GenFrag.n1 k) lib P
  have U := uokc_of_uok (S := S) (Map := Map) lib env
    (uok_x lib (FragX.frag (S := S) (nm := Nomm.n1 k) fun _ => trivial)) M1
  have R := U.run (sup := sup) (goal := CGoal.done) (region := region) trivial trivial trivial trivial trivial
    (by simp [Comp.sixCount]) b0 d0 hu hcl hcb (fun r hr => hr.elim) hr
  have hl : nex.laz = ofSure Sure.bunt := by
    simp only [runLC, bind_apply, re_apply, emit_apply, Option.bind_some, pure_apply, Option.some.injEq,
      Prod.mk.injEq] at hr
    rw [← hr.1]
  have e0 : entries nex.laz = [] := by rw [hl]; exact entries_ofSure _
  have nE : ∀ e, e ∉ entries nex.laz := fun e he => by rw [e0] at he; cases he
  refine ⟨(R.toB (N := N)).toGD, (by rw [hl]; exact Raw.labUniq_ofSure _), ?_, (fun e he => absurd he (nE e)),
    (fun e he => absurd he (nE e))⟩
  rw [hl]
  first | trivial | simp [Clean, ofSure, Sure.bunt]

/-- **`[7 p q]` under `%done`**: `q` under `%done`, `p` in `NextGCS` at
`q`'s result. -/
theorem cm2_done_n7 (lib : Lib) (N : Needs) (env : CallEnv) {fb fc : Noun} {p q : Nomm}
    (Hp : ∀ P, NextGCS (S := S) (Map := Map) lib N env P fb p) (Hq : ∀ P, DoneGS S Map lib N env P fc q) :
    ∀ P, DoneGS S Map lib N env P (n3 (A 7) fb fc) (Nomm.n7 p q) := by
  intro P sup region g0 g2 nex b0 d0 hu hcl hcb hr
  rw [runLC_n7] at hr
  obtain ⟨nx, g1, h1, h2⟩ := bind_some hr
  obtain ⟨Rq, lu, cl, ecl, sa⟩ := Hq (Img lib P fb) b0 d0 hu hcl hcb h1
  simp only [NextL.goal] at h2
  have hta : nx.th.args = [] := by
    rcases Rq.ent with ⟨_, _, _, ha⟩ | e
    · exact ha
    · exact e.elim
  have Hp' : PremG (Map := Map) nx.laz nx.th g1 :=
    { goal := Rq.goalOut b0 (fun r hr => hr.elim), nc := Rq.ncond, ec := Rq.econd, lu := lu, cl := cl,
      ecl := ecl, sa := sa, ta := hta, bo := Nat.le_trans b0 Rq.ext.2.1, drop := Rq.ext.2.2.1.trans d0,
      up := Rq.grow.up hu, clr := hcl.growU Rq.grow, cb := Rq.cfr.below hcb }
  obtain ⟨Qp, Rp, gup, nrp, Resp, FSp⟩ := Hp P Hp' h2
  exact ⟨runOKGD_sevenG (minkC7_seven lib P fb fc) Rq Rp gup nrp (fun r hr => hr.elim), Resp.lu, Resp.cl,
    Resp.ecl, Resp.sa⟩

/-- **Every nomm of `ConsFrag` is in the class under `%done`**, at every `P`. -/
theorem doneGS_consFrag (lib : Lib) (N : Needs) (env : CallEnv) {f : Noun} {nm : Nomm} (hf : ConsFrag f nm) :
    ∀ P, DoneGS S Map lib N env P f nm := by
  induction hf with
  | n0 ha => intro P; exact cm2_done_of_next (Or.inr (Or.inr ⟨_, by omega, rfl⟩)) (closedS_n0 lib N env ha P)
  | n1 k => intro P; exact cm2_done_n1 lib N env P k
  | cons hp hq ihp ihq =>
    intro P
    exact cm2_done_of_next (Or.inl ⟨_, _, rfl⟩) (nextGCS_consFrag lib N env (ConsFrag.cons hp hq) P)
  | n7 hp hq ihp ihq => exact cm2_done_n7 lib N env (nextGCS_consFrag lib N env hp) ihq

/-- **THE UNARY CONTRACT ON `ConsFrag`, no premise**: the whole-subject code
that `+comp`'s model makes of a nomm built of `[0 a]` (`a ≥ 2`), `[1 k]`,
the cons and `[7 p q]` has the need `this` and meets both halves of the
contract for its formula, at every subject. -/
theorem contract_consFrag (lib : Lib) (env : CallEnv) (N : Needs) {f : Noun} {nm : Nomm} (hf : ConsFrag f nm)
    {c : Straight Map} (h : finishLUC (S := S) (Map := Map) env nm = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s f [s] c ∧ ContractBwd lib N s f [s] c :=
  have H := finishLUC_contractGD (P := fun _ => True) lib N
    (fun hr => (doneGS_consFrag (S := S) (Map := Map) lib N env hf (fun _ => True) (by simp [gen0]) rfl
      upBelow_gen0 clear_gen0 condBelow_gen0 hr).1) h
  ⟨H.1, fun s => H.2 s trivial⟩

end Comp
end SkaModel
end Formalization
