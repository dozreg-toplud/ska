import lemmas.Ska.CompSixNxRel
import lemmas.Ska.CompSevenLS

/-!
# `LOKS` at one-level tree goals: the measurement (generated)

Written by `tools/gen/loks1.py`; do not edit by hand.  README Gaps 12.36:
which constructor lemmas of `LOKS` go through for a goal that is a
one-level tree (`Tree1`, the unwrapped result of a `%6`) by the same proof
text.  `LOKS1` is `LOKS` with the premise `Tree1 L` in place of `Flat L`.

* `LOKS1`, `LOKS1.toS` (a member of `LOKS1` is one of `LOKS`).
* `lokS1_seven`: the text of `lokS_seven`, with `LOKS1` for `q`: it builds
  unchanged (the goal's premises are passed to `q`, `p` runs under `q`'s
  flat result).

The copy of `lokS_n0` (`--with-n0`) fails at three places: `entries_flat`
(the entries of a forked goal include its forks'), `fromL_flat` (`+from`
over forks has no spec), and `[0 1]`, whose result is the goal itself, so a
`Flat` result is FALSE at a forked goal: the goal-side relation must
conclude `Tree1` of the result too (`LOKT` with `Tree1` goals).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **`LOKS` at one-level tree goals** (generated): `LOKB` with `RunOKLS`, flat
goals and results with clean entries, and the run's jump the goal's or a
block it made. -/
structure LOKS1 (x : Bool) (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop) (f : Noun) (nm : Nomm) : Prop where
  clean : ∀ {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    Clean L.sure.ned → runLC env sup nm (CGoalL.next L th) region g0 = some (nex, g1) → Clean nex.laz.sure.ned
  run : ∀ {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    1 ≤ th.there → th.there < g0.bo → th.args = [] → th.there ∉ (entries L).map Prod.fst → Distinct L.sure.ned →
    (∀ x, NMem L.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) →
    (∀ e ∈ entries L, e.1 < g0.bo ∧ ∃ B th', HoonMap.get g0.blocks e.1 = some ⟨[], B, Termin.hop th'⟩) →
    ((entries L).map Prod.fst).Nodup →
    (∀ e ∈ entries L, Distinct e.2.sure.ned ∧
      ∀ x, NMem e.2.sure.ned x → x < g0.re ∧ HoonMap.get g0.cond x = Option.none) →
    Tree1 L → Clean L.sure.ned → (∀ e ∈ entries L, Clean e.2.sure.ned) →
    runLC env sup nm (CGoalL.next L th) region g0 = some (nex, g1) →
    (∃ Q, RunOKLS (Map := Map) lib N P f L th Q x g0 g1 nex) ∧ nex.th.there ∉ (entries nex.laz).map Prod.fst ∧
      (nex.th = th ∨ g0.bo ≤ nex.th.there) ∧ Flat nex.laz ∧ (∀ e ∈ entries nex.laz, Clean e.2.sure.ned)

/-- **A member of `LOKS1` is one of `LOKS`** (a flat goal is a one-level tree). -/
theorem LOKS1.toS {x : Bool} {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (H : LOKS1 (S := S) (Map := Map) x lib N env P f nm) : LOKS (S := S) (Map := Map) x lib N env P f nm :=
  ⟨H.clean, fun c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 hr =>
    H.run c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 (flat_tree1 c16) c17 c18 hr⟩

theorem lokS1_seven {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {fb fc : Noun} {p q : Nomm}
    (Lq : LOKS1 (S := S) (Map := Map) false lib N env (Img lib P fb) fc q)
    (Lp : LOKS (S := S) (Map := Map) false lib N env P fb p) :
    LOKS1 (S := S) (Map := Map) false lib N env P (n3 (A 7) fb fc) (Nomm.n7 p q) := by
  refine ⟨fun {sup L th region g0 g1 nex} hc hr => ?_, fun {sup L th region g0 g2 nex} hcount b0 d0 hu hcl hcb
    h1 h2 hta ht hsd hsl hlab hnd hed hfl hcl' hce hr => ?_⟩
  · rw [runLC_n7] at hr
    obtain ⟨nx, ga, e1, e2⟩ := bind_some hr
    exact Lp.clean (Lq.clean hc e1) e2
  · rw [runLC_n7] at hr
    obtain ⟨nx, g1, hq, hp⟩ := bind_some hr
    have cq : sixCount q ≤ 255 := by simp only [sixCount] at hcount; omega
    have cp : sixCount p ≤ 255 := by simp only [sixCount] at hcount; omega
    obtain ⟨⟨Qq, Rq⟩, qne, qj, qfl, qec⟩ :=
      Lq.run cq b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcl' hce hq
    have qc := Lq.clean hcl' hq
    have hargs : nx.th.args = [] := by
      rcases Rq.ent with ⟨_, _, _, ha⟩ | e
      · exact ha
      · simp only [GoalJ] at e; rw [e]; exact hta
    have q1 := Rq.re
    have q2 := Rq.bo
    obtain ⟨⟨Qp, Rp⟩, pne, pj, pfl, pec⟩ := Lp.run (sup := sup) (L := nx.laz) (th := nx.th) (region := region) cp
      (by omega) (Rq.drop.trans d0) (Rq.grow.up hu) (Clear.growU hcl Rq.grow) (Rq.cfr.below hcb)
      Rq.lo Rq.hi hargs qne Rq.dist
      (fun x hx => ⟨by
        rcases Rq.regs x hx with h | h
        · have := (hsl x h).1; omega
        · exact h.2, Rq.ncond x hx⟩)
      (fun e he => ⟨by
        rcases (Rq.labs e he).1 with h | h
        · obtain ⟨e0, he0, e1⟩ := List.mem_map.mp h
          have := (hlab e0 he0).1; rw [e1] at this; omega
        · exact h.2, (Rq.labs e he).2⟩) Rq.nodup
      (fun e he => ⟨(Rq.eregs e he).1, fun x hx => ⟨by
        rcases (Rq.eregs e he).2 x hx with ⟨e0, he0, h⟩ | h | h
        · have := ((hed e0 he0).2 x h).1; omega
        · have := (hsl x h).1; omega
        · exact h.2, Rq.econd e he x hx⟩⟩) qfl qc qec hp
    refine ⟨⟨_, runOKLS_seven Rq Rp (fun r hr => (hsl r hr).1) (fun e he => (hlab e he).1)
      (fun e he r hr => hr.elim)⟩, pne, ?_, pfl, pec⟩
    rcases pj with e | e
    · rw [e]; exact qj
    · exact Or.inr (by have := Rp.bo; omega)

end Comp
end SkaModel
end Formalization
