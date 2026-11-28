import lemmas.Ska.CompGenClassF
import lemmas.Ska.CompGenClassG

/-!
# The class `NextGCS`: the interfaces of the cons, the closures, the induction

README Gaps 12.39, item 12.  The cons in `NextGCS` from two plumbing
interfaces, each an exact `Prop`:

* `ConsSemPreOf`: `ConsSemPre` (the copy's and the split's root blocks, the
  parts' `AgreeG` from the whole's, the registers) of the cons taken apart
  (`ConsGAt`), from the parts' frames, growth, no re-pointing and `ResG`
  (proved in `CompGenClassI.lean`).
* `FrontsSGConsOf`: the cons's `FrontsSG` from the parts' (`frontSG_consG` at
  every goal label; proved in `CompGenClassJ.lean`).

`closedS_cons_of` assembles the cons from them, with the parts' `MinkEq`
(`GenFrag` gives it, `CompGenClassK.lean`).  `nextGCS_all_of`: the
induction over `GenFrag` in `NextGCS`, from the closures.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

section Ifaces
variable (S Map)

/-- **The plumbing of the cons's sure part**: `ConsSemPre` of the cons taken
apart, from the parts' class facts. -/
def ConsSemPreOf (lib : Lib) : Prop :=
  ∀ {L : Lazy S} {th : Jmp} {p q : Nomm} {env : CallEnv} {sup : Option Nomm} {region : List Nat}
    {g0 g1 : Gen Map} {nex : NextL S} {hed tel : Lazy S} {gS g2 g3 : Gen Map} {nq np : NextL S} {Qq Qp : Wit},
    ConsGAt L th p q env sup region g0 g1 nex hed tel gS g2 g3 nq np → PremG (Map := Map) L th g0 →
    FrameG (Map := Map) tel (jmp0 g0.bo) Qq gS g2 nq → GrowU gS g2 →
    (∀ a ∈ (entries tel).map Prod.fst, ¬ RepointG gS g2 a) → ResG (Map := Map) tel gS g2 nq.laz →
    FrameG (Map := Map) hed nq.th Qp g2 g3 np → GrowU g2 g3 →
    (∀ a ∈ (entries hed).map Prod.fst, ¬ RepointG g2 g3 a) → ResG (Map := Map) hed g2 g3 np.laz →
    ConsSemPre (Map := Map) lib L th hed tel g0 gS g2 g3 g1 nq np nex

/-- **The cons's state-level fronts from the parts'.** -/
def FrontsSGConsOf : Prop :=
  ∀ {L : Lazy S} {th : Jmp} {p q : Nomm} {env : CallEnv} {sup : Option Nomm} {region : List Nat}
    {g0 g1 : Gen Map} {nex : NextL S} {hed tel : Lazy S} {gS g2 g3 : Gen Map} {nq np : NextL S} {Qq Qp : Wit},
    ConsGAt L th p q env sup region g0 g1 nex hed tel gS g2 g3 nq np → PremG (Map := Map) L th g0 →
    FrameG (Map := Map) tel (jmp0 g0.bo) Qq gS g2 nq → GrowU gS g2 →
    (∀ a ∈ (entries tel).map Prod.fst, ¬ RepointG gS g2 a) → ResG (Map := Map) tel gS g2 nq.laz →
    FrontsSG (Map := Map) Qq gS g2 tel nq →
    FrameG (Map := Map) hed nq.th Qp g2 g3 np → GrowU g2 g3 →
    (∀ a ∈ (entries hed).map Prod.fst, ¬ RepointG g2 g3 a) → ResG (Map := Map) hed g2 g3 np.laz →
    FrontsSG (Map := Map) Qp g2 g3 hed np →
    FrontsSG (Map := Map) (consWit Qp Qq) g0 g1 L nex

/-! ## The closures in `NextGCS` -/

def ClosedSN3 (lib : Lib) (N : Needs) (env : CallEnv) : Prop :=
  ∀ {f : Noun} {p : Nomm}, GenFrag f p → (∀ P, NextGCS (S := S) (Map := Map) lib N env P f p) →
    ∀ P, NextGCS (S := S) (Map := Map) lib N env P (C (A 3) f) (Nomm.n3 p)

def ClosedSN4 (lib : Lib) (N : Needs) (env : CallEnv) : Prop :=
  ∀ {f : Noun} {p : Nomm}, GenFrag f p → (∀ P, NextGCS (S := S) (Map := Map) lib N env P f p) →
    ∀ P, NextGCS (S := S) (Map := Map) lib N env P (C (A 4) f) (Nomm.n4 p)

def ClosedSN5 (lib : Lib) (N : Needs) (env : CallEnv) : Prop :=
  ∀ {fp fq : Noun} {p q : Nomm}, GenFrag fp p → GenFrag fq q →
    (∀ P, NextGCS (S := S) (Map := Map) lib N env P fp p) → (∀ P, NextGCS (S := S) (Map := Map) lib N env P fq q) →
    ∀ P, NextGCS (S := S) (Map := Map) lib N env P (n3 (A 5) fp fq) (Nomm.n5 p q)

def ClosedSCons (lib : Lib) (N : Needs) (env : CallEnv) : Prop :=
  ∀ {fp fq : Noun} {p q : Nomm}, GenFrag fp p → GenFrag fq q →
    (∀ P, NextGCS (S := S) (Map := Map) lib N env P fp p) → (∀ P, NextGCS (S := S) (Map := Map) lib N env P fq q) →
    ∀ P, NextGCS (S := S) (Map := Map) lib N env P (C fp fq) (Nomm.cons p q)

end Ifaces

/-- **The one induction in `NextGCS`, from the closures** (`[0 a]`, `[1 k]`
and `[7 p q]` are proved: `closedS_n0`, `closedS_n1`, `closedS_n7`). -/
theorem nextGCS_all_of {lib : Lib} {N : Needs} {env : CallEnv}
    (h3 : ClosedSN3 S Map lib N env) (h4 : ClosedSN4 S Map lib N env) (h5 : ClosedSN5 S Map lib N env)
    (hc : ClosedSCons S Map lib N env) {f : Noun} {nm : Nomm} (hf : GenFrag f nm) :
    ∀ P, NextGCS (S := S) (Map := Map) lib N env P f nm := by
  induction hf with
  | n0 ha => exact closedS_n0 lib N env ha
  | n1 k => exact closedS_n1 lib N env k
  | n3 hp ih => exact h3 hp ih
  | n4 hp ih => exact h4 hp ih
  | n5 hp hq ihp ihq => exact h5 hp hq ihp ihq
  | cons hp hq ihp ihq => exact hc hp hq ihp ihq
  | n7 hp hq ihp ihq => exact closedS_n7 lib N env ihp ihq

/-! ## The cons, assembled -/

/-- **The cons is in `NextGCS`** when both parts are, at every `P`, given
the two plumbing interfaces and the parts' `MinkEq` (the head's formula a
cell). -/
theorem closedS_cons_of (lib : Lib) (N : Needs) (env : CallEnv) (HX : ConsSemPreOf S Map lib)
    (HF : FrontsSGConsOf S Map) {fp fq : Noun} {p q : Nomm} (hpp : p.pure = true) (hqp : q.pure = true)
    (hfh : ∃ a b, fp = C a b) (Mp : ∀ P, MinkEq lib P fp p) (Mq : ∀ P, MinkEq lib P fq q)
    (Hp : ∀ P, NextGCS (S := S) (Map := Map) lib N env P fp p)
    (Hq : ∀ P, NextGCS (S := S) (Map := Map) lib N env P fq q) :
    ∀ P, NextGCS (S := S) (Map := Map) lib N env P (C fp fq) (Nomm.cons p q) := by
  intro P sup region g0 g1 L th nex G h
  obtain ⟨hed, tel, gS, g2, g3, nq, np, CA⟩ := consGAt_of_run env sup hpp hqp G h
  have Pq := premG_tel CA G
  obtain ⟨Qq, Rq, Gq, Nq, Resq, FSq⟩ := Hq P Pq CA.rq
  have Pp := premG_hed CA G Rq.toFrameG Gq
  obtain ⟨Qp, Rp, Gp, Np, Resp, FSp⟩ := Hp P Pp CA.rp
  have d3 : g3.drop = false := Rp.drop.trans (Rq.drop.trans CA.dS)
  have CO := CA.copyOK d3 Resp.lu Resq.lu
  have HA := halvesApart_split CA G
  obtain ⟨RG, LD⟩ := resG_copy Rq.toFrameG Rp.toFrameG Pq Pp Resq Resp HA (CA.halfH G) (CA.halfT G) CA.reS d3
    CA.cp CA.hc CO
  have CP : CopyPreAt (Map := Map) (g3.emitted ⟨[], [], Termin.hop np.th⟩) ((g3.bo, np.laz) :: entries np.laz)
      ((g3.bo, nq.laz) :: entries nq.laz) :=
    cc_copyPreAt_re (emitted_re _ _).symm (copyPreG Rq.toFrameG Rp.toFrameG Pq Pp Resq Resp HA)
  obtain ⟨Fr, GU, NR⟩ := frameG_consG CA G Rq.toFrameG Gq Nq Rp.toFrameG Gp Np Resp.lu Resq.lu
    (CopyOKL.runAt CO) CP LD
  have X := HX CA G Rq.toFrameG Gq Nq Resq Rp.toFrameG Gp Np Resp
  obtain ⟨sem, semB, nec⟩ := semCoreG_consG hfh (Mp P) (Mq P) Rq Rp X
  have FS := HF CA G Rq.toFrameG Gq Nq Resq FSq Rp.toFrameG Gp Np Resp FSp
  refine ⟨consWit Qp Qq, { toFrameG := Fr, nec := nec, front := ?_, sem := sem, semB := semB }, GU, NR, RG, FS⟩
  intro a ha
  obtain ⟨F, hb, hf⟩ := FS a ha
  refine Or.inl ⟨F, hb, fun cf hcf => ?_⟩
  exact (hf cf hcf).toLG Fr.re (fun r hr => by simp [gsE, NMem] at hr) Fr.dreg

end Comp
end SkaModel
end Formalization
