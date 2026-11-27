import lemmas.Ska.CompCallTreeTop

/-!
# `[7 p q]` under a flat lazy goal: `LOKS` of the composition

README Gaps 12.27.  `runOKLB_seven` (`CompLBSeven.lean`) composes `q` under
`%next L th` with `p` under `q`'s result; here the fronts at the state
level compose too (`frontS_seven`: `p`'s ops in front of `q`'s at an entry
both see, `frontS_seven_bunt`: `q`'s alone at an entry `q`'s result does
not have, which `p` keeps), so `RunOKLS` composes (`runOKLS_seven`), and
`LOKS` of `[7 p q]` follows from `LOKS` of the parts (`lokS_seven`): `q`'s
result is flat with clean entries and its jump at no entry, which are the
premises of `LOKS.run` for `p`.

* `frontS_seven`, `frontS_seven_bunt`, `frontsS_seven`, `runOKLS_seven`.
* `lokS_seven`: `LOKS x` of `q` (on the products of `p`) and `LOKS false`
  of `p` give `LOKS x` of `[7 p q]`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The fronts -/

/-- **The state-level fronts compose** (`frontLB_seven` for `FrontS`):
`p`'s ops `Fp` (reading no goal register) in front of `q`'s `Fq`. -/
theorem frontS_seven {Qp Qq : Wit} {E : Need} {lo0 lo1 lo2 : Nat} {Lp Lq M : Sure S} {Fp Fq : List Pole}
    (hdp : ∀ s v d w r, Qp s v d w → NMem d r → lo1 ≤ r ∧ r < lo2)
    (hdq : ∀ s v d w r, Qq s v d w → NMem d r → lo0 ≤ r ∧ r < lo1) (h01 : lo0 ≤ lo1) (h12 : lo1 ≤ lo2)
    (hE : ∀ r, NMem E r → r < lo1 ∧ ¬ NMem Lq.ned r)
    (FP : FrontS (Map := Map) Qp Need.none lo1 lo2 Lp Fp Lq) (FQ : FrontS (Map := Map) Qq E lo0 lo1 Lq Fq M) :
    FrontS (Map := Map) (sevenWit Qp Qq) E lo0 lo2 Lp (Fp ++ Fq) M where
  loc := fun r hr => by
    obtain ⟨a, b⟩ := FP.loc r hr
    exact ⟨a, fun h => (FQ.loc r (b (by omega))).2 h⟩
  dis := fun s v d w hq r hr => by
    obtain ⟨u, dp, wp, dq, wq, hp, hqq, rfl, rfl⟩ := hq
    rcases hr with hr | hr
    · exact FP.dis s u dp wp hp r hr
    · intro hm
      have := hdq u v dq wq r hqq hr
      exact FQ.dis u v dq wq hqq r hr ((FP.loc r hm).2 (by omega))
  fit := fun s v d w hq hf => by
    obtain ⟨u, dp, wp, dq, wq, hp, hqq, rfl, rfl⟩ := hq
    exact FP.fit s u dp wp hp (FQ.fit u v dq wq hqq hf)
  run := fun lib σ O c gul st t R s v d w hq hs hd hE' => by
    obtain ⟨u, dp, wp, dq, wq, hp, hqq, rfl, rfl⟩ := hq
    obtain ⟨hdp', hdq'⟩ := hd
    have P1 := FP.run lib σ O c gul st t R s u dp wp hp hs hdp' trivial
    refine ⟨fun fv => ?_, fun nf => ?_⟩
    · have fu := FQ.fit u v dq wq hqq fv
      obtain ⟨R1, r1, h1, k1⟩ := P1.1 fu
      have dq1 : HoldsN dq R1 wq := HoldsN.agree dq (fun x hx => by
        have := hdq u v dq wq x hqq hx
        exact k1 x (Or.inl (by omega)) (FQ.dis u v dq wq hqq x hx)) hdq'
      have E1 : HoldsN E R1 v := HoldsN.agree E (fun x hx => k1 x (Or.inl (hE x hx).1) (hE x hx).2) hE'
      obtain ⟨R2, r2, h2, k2⟩ := (FQ.run lib σ O c gul st t R1 u v dq wq hqq h1 dq1 E1).1 fv
      refine ⟨R2, r1.append r2, h2, fun x hx hn => ?_⟩
      have hnq : ¬ NMem Lq.ned x := fun hm => by
        have lq := FQ.loc x hm
        rcases hx with hx | hx | hx | hx
        · exact hn (lq.2 hx)
        · have := lq.1; omega
        · have := hdp s u dp wp x hp hx; omega
        · exact FQ.dis u v dq wq hqq x hx hm
      have a1 : x < lo1 ∨ lo2 ≤ x ∨ NMem dp x := by
        rcases hx with hx | hx | hx | hx
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl hx)
        · exact Or.inr (Or.inr hx)
        · exact Or.inl (hdq u v dq wq x hqq hx).2
      have a2 : x < lo0 ∨ lo1 ≤ x ∨ NMem dq x := by
        rcases hx with hx | hx | hx | hx
        · exact Or.inl hx
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inl (hdp s u dp wp x hp hx).1)
        · exact Or.inr (Or.inr hx)
      rw [k2 x a2 hn, k1 x a1 hnq]
    · by_cases fu : FitsS Lq u
      · obtain ⟨R1, r1, h1, k1⟩ := P1.1 fu
        have dq1 : HoldsN dq R1 wq := HoldsN.agree dq (fun x hx => by
          have := hdq u v dq wq x hqq hx
          exact k1 x (Or.inl (by omega)) (FQ.dis u v dq wq hqq x hx)) hdq'
        have E1 : HoldsN E R1 v := HoldsN.agree E (fun x hx => k1 x (Or.inl (hE x hx).1) (hE x hx).2) hE'
        exact Crashes.append_right r1 ((FQ.run lib σ O c gul st t R1 u v dq wq hqq h1 dq1 E1).2 nf)
      · exact Crashes.append_left (P1.2 fu)

/-- **A front of `q` at an entry that `q`'s result does not have**: `p`
keeps the block, the front is `q`'s alone. -/
theorem frontS_seven_bunt {Qp Qq : Wit} {E : Need} {lo0 lo1 lo2 : Nat} {M : Sure S} {Fq : List Pole}
    (hdp : ∀ s v d w r, Qp s v d w → NMem d r → lo1 ≤ r ∧ r < lo2) (h12 : lo1 ≤ lo2)
    (FQ : FrontS (Map := Map) Qq E lo0 lo1 Sure.bunt Fq M) :
    FrontS (Map := Map) (sevenWit Qp Qq) E lo0 lo2 Sure.bunt Fq M where
  loc := fun r hr => hr.elim
  dis := fun s v d w hq r hr hm => hm.elim
  fit := fun s v d w hq hf => fitsS_bunt s
  run := fun lib σ O c gul st t R s v d w hq hs hd hE' => by
    obtain ⟨u, dp, wp, dq, wq, hp, hqq, rfl, rfl⟩ := hq
    obtain ⟨hdp', hdq'⟩ := hd
    have K := FQ.run lib σ O c gul st t R u v dq wq hqq (holdsS_bunt R u) hdq' hE'
    refine ⟨fun fv => ?_, K.2⟩
    obtain ⟨R2, r2, h2, k2⟩ := K.1 fv
    refine ⟨R2, r2, h2, fun x hx hn => k2 x ?_ hn⟩
    rcases hx with hx | hx | hx | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inl (hdp s u dp wp x hp hx).1)
    · exact Or.inr (Or.inr hx)

/-- **`FrontsS` of `[7 p q]`**: at a goal entry that `q`'s result has, `p`'s
front in front of `q`'s (`frontS_seven`); at one it has not, `q`'s alone
(`frontS_seven_bunt`), the block kept by `p`. -/
theorem frontsS_seven {Qp Qq : Wit} {x : Bool} {L : Lazy S} {g0 g1 g2 : Gen Map} {nx nex : NextL S}
    (Fq : FrontsS (Map := Map) Qq x g0 g1 L nx) (Fp : FrontsS (Map := Map) Qp false g1 g2 nx.laz nex)
    (hdp : ∀ s v d w r, Qp s v d w → NMem d r → g1.re ≤ r ∧ r < g2.re)
    (hdq : ∀ s v d w r, Qq s v d w → NMem d r → g0.re ≤ r ∧ r < g1.re)
    (h01 : g0.re ≤ g1.re) (h12 : g1.re ≤ g2.re)
    (hcf : ∀ k, k < g1.re → HoonMap.get g2.cond k = HoonMap.get g1.cond k)
    (hE : ∀ e ∈ entries nx.laz, ∀ r, NMem (gsE x L) r → r < g1.re ∧ ¬ NMem e.2.sure.ned r)
    (hnd : ((entries nx.laz).map Prod.fst).Nodup)
    (hlab : ∀ e ∈ entries L, e.1 < g1.bo)
    (keep : ∀ o, o < g1.bo → o ∉ (entries nx.laz).map Prod.fst → HoonMap.get g2.blocks o = HoonMap.get g1.blocks o)
    (plab : ∀ o, o ∈ (entries nex.laz).map Prod.fst → o ∈ (entries nx.laz).map Prod.fst ∨ g1.bo ≤ o) :
    FrontsS (Map := Map) (sevenWit Qp Qq) x g0 g2 L nex := by
  intro e he
  obtain ⟨Fq', hbq, Sq⟩ := Fq e he
  have cf1 : ∀ cf : Map (Nat × List Nat), (∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g2.cond k) →
      ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun cf h k hk => by
    rw [h k (by omega), hcf k hk]
  by_cases hm : e.1 ∈ (entries nx.laz).map Prod.fst
  · obtain ⟨⟨l1, Lq⟩, hLq0, e1⟩ := List.mem_map.mp hm
    have hLq : (e.1, Lq) ∈ entries nx.laz := by simp only at e1; rw [← e1]; exact hLq0
    obtain ⟨Fp', hbp, Sp⟩ := Fp (e.1, Lq) hLq
    refine ⟨Fp' ++ Fq', fun B fin hb => ?_, fun cf hcf2 => ?_⟩
    · have := hbp (Fq' ++ B) fin (hbq B fin hb)
      simpa only [List.append_assoc] using this
    · have FQ : FrontS (Map := Map) Qq (gsE x L) g0.re g1.re Lq.sure (Fq'.map (renPole (unproxy cf))) e.2.sure := by
        rcases Sq cf (cf1 cf hcf2) with ⟨L', hL', F⟩ | ⟨hn, F⟩
        · have := eq_of_label hnd hL' hLq rfl
          simp only [Prod.mk.injEq, true_and] at this
          rw [this] at F
          exact F
        · exact absurd hm hn
      rw [List.map_append]
      rcases Sp cf hcf2 with ⟨L', hL', F⟩ | ⟨hn, F⟩
      · exact Or.inl ⟨L', hL', frontS_seven hdp hdq h01 h12 (hE _ hLq) F FQ⟩
      · exact Or.inr ⟨hn, frontS_seven hdp hdq h01 h12 (hE _ hLq) F FQ⟩
  · refine ⟨Fq', fun B fin hb => ?_, fun cf hcf2 => ?_⟩
    · rw [keep e.1 (hlab e he) hm]; exact hbq B fin hb
    · rcases Sq cf (cf1 cf hcf2) with ⟨L', hL', F⟩ | ⟨hn, F⟩
      · exact absurd (List.mem_map.mpr ⟨_, hL', rfl⟩) hm
      · refine Or.inr ⟨fun h => ?_, frontS_seven_bunt hdp h12 F⟩
        rcases plab e.1 h with h | h
        · exact hm h
        · have := hlab e he; omega

/-- **`RunOKLS` of `[7 p q]`** (`runOKLB_seven` with `frontsS_seven`). -/
theorem runOKLS_seven {lib : Lib} {N : Needs} {P : Noun → Prop} {fb fc : Noun} {L : Lazy S} {th : Jmp} {Qp Qq : Wit}
    {x : Bool} {g0 g1 g2 : Gen Map} {nx nex : NextL S}
    (Rq : RunOKLS (Map := Map) lib N (Img lib P fb) fc L th Qq x g0 g1 nx)
    (Rp : RunOKLS (Map := Map) lib N P fb nx.laz nx.th Qp false g1 g2 nex)
    (hL : ∀ r, NMem L.sure.ned r → r < g0.re)
    (hlab : ∀ e ∈ entries L, e.1 < g0.bo)
    (hE : ∀ e ∈ entries nx.laz, ∀ r, NMem (gsE x L) r → r < g1.re ∧ ¬ NMem e.2.sure.ned r) :
    RunOKLS lib N P (n3 (A 7) fb fc) L th (sevenWit Qp Qq) x g0 g2 nex :=
  { toRunOKLB := runOKLB_seven Rq.toRunOKLB Rp.toRunOKLB hL hlab
    fs := frontsS_seven Rq.fs Rp.fs Rp.dreg Rq.dreg Rq.re Rp.re (fun k hk => Rp.cfr.get_lt hk) hE Rq.nodup
      (fun e he => by have := hlab e he; have := Rq.bo; omega) Rp.keep
      (fun o ho => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
        rcases (Rp.labs e he).1 with h | h
        · exact Or.inl h
        · exact Or.inr h.1) }

/-! ## `LOKS` of `[7 p q]` -/

/-- **`[7 p q]` under a flat lazy goal**: `LOKS false` of `q` on the
products of `p` and of `p` give `LOKS false` of `[7 p q]`.  `q`'s result
is flat with clean entries and its jump at no entry (`LOKS` of `q`), so it
meets the premises of `LOKS.run` for `p`; the jump of the whole is `p`'s,
the goal's or new. -/
theorem lokS_seven {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {fb fc : Noun} {p q : Nomm}
    (Lq : LOKS (S := S) (Map := Map) false lib N env (Img lib P fb) fc q)
    (Lp : LOKS (S := S) (Map := Map) false lib N env P fb p) :
    LOKS (S := S) (Map := Map) false lib N env P (n3 (A 7) fb fc) (Nomm.n7 p q) := by
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

/-- **The jump of a hinted `[7 p q]` is a block it made**: `p`'s jump is
new, or it is `q`'s, new when `q` is hinted; when `q` is not, `p` is. -/
theorem jNewLS_seven {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {fb fc : Noun} {p q : Nomm}
    (Lq : LOKS (S := S) (Map := Map) false lib N env (Img lib P fb) fc q)
    (Lp : LOKS (S := S) (Map := Map) false lib N env P fb p)
    (Jq : hinted env.cod q = some true → JNewLS (S := S) (Map := Map) env q)
    (Jp : hinted env.cod p = some true → JNewLS (S := S) (Map := Map) env p)
    (hh : hinted env.cod (Nomm.n7 p q) = some true) : JNewLS (S := S) (Map := Map) env (Nomm.n7 p q) := by
  intro sup L th region g0 g2 nex hcount b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcl' hce hr
  rw [runLC_n7] at hr
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
  have A1 : ∀ x, NMem nx.laz.sure.ned x → x < g1.re ∧ HoonMap.get g1.cond x = Option.none := fun x hx => ⟨by
      rcases Rq.regs x hx with h | h
      · have := (hsl x h).1; omega
      · exact h.2, Rq.ncond x hx⟩
  have A2 : ∀ e ∈ entries nx.laz, e.1 < g1.bo ∧ ∃ B th', HoonMap.get g1.blocks e.1 = some ⟨[], B, Termin.hop th'⟩ :=
    fun e he => ⟨by
      rcases (Rq.labs e he).1 with h | h
      · obtain ⟨e0, he0, e1⟩ := List.mem_map.mp h
        have := (hlab e0 he0).1; rw [e1] at this; omega
      · exact h.2, (Rq.labs e he).2⟩
  have A3 : ∀ e ∈ entries nx.laz, Distinct e.2.sure.ned ∧
      ∀ x, NMem e.2.sure.ned x → x < g1.re ∧ HoonMap.get g1.cond x = Option.none := fun e he =>
    ⟨(Rq.eregs e he).1, fun x hx => ⟨by
      rcases (Rq.eregs e he).2 x hx with ⟨e0, he0, h⟩ | h | h
      · have := ((hed e0 he0).2 x h).1; omega
      · have := (hsl x h).1; omega
      · exact h.2, Rq.econd e he x hx⟩⟩
  have pj := (Lp.run (sup := sup) (L := nx.laz) (th := nx.th) (region := region) cp
    (by omega) (Rq.drop.trans d0) (Rq.grow.up hu) (Clear.growU hcl Rq.grow) (Rq.cfr.below hcb)
    Rq.lo Rq.hi hargs qne Rq.dist A1 A2 Rq.nodup A3 qfl qc qec hp).2.2.1
  by_cases hq' : hinted env.cod q = some true
  · have jq := Jq hq' cq b0 d0 hu hcl hcb h1 h2 hta ht hsd hsl hlab hnd hed hfl hcl' hce hq
    rcases pj with e | e
    · rw [e]; exact jq
    · omega
  · have hp' : hinted env.cod p = some true := by
      simp only [hinted] at hh
      cases e : hinted env.cod p with
      | none => rw [e] at hh; cases hh
      | some b => cases b with
        | true => rfl
        | false => rw [e] at hh; exact absurd hh hq'
    have jp := Jp hp' (sup := sup) (L := nx.laz) (th := nx.th) (region := region) cp
      (by omega) (Rq.drop.trans d0) (Rq.grow.up hu) (Clear.growU hcl Rq.grow) (Rq.cfr.below hcb)
      Rq.lo Rq.hi hargs qne Rq.dist A1 A2 Rq.nodup A3 qfl qc qec hp
    omega

/-! ## The class closed under `%7` -/

/-- **`CallTree` closed under `[7 p q]`**: `[0 axe]`, the cons `[[a1 a2]
b]`, the indirect call and `[7 p q]`, with the formulas of `Annot`. -/
inductive CallTree7 : Noun → Nomm → Prop
  | n0 (axe : Nat) : CallTree7 (slot axe) (Nomm.n0 axe)
  | cons {a1 a2 b : Noun} {p q : Nomm} : CallTree7 (C a1 a2) p → CallTree7 b q →
      CallTree7 (C (C a1 a2) b) (Nomm.cons p q)
  | ind {b c : Noun} {p q : Nomm} : CallTree7 b p → CallTree7 c q → CallTree7 (n3 (A 2) b c) (Nomm.n2 p q Option.none)
  | seven {b c : Noun} {p q : Nomm} : CallTree7 b p → CallTree7 c q → CallTree7 (n3 (A 7) b c) (Nomm.n7 p q)

theorem CallTree7.annot {lib : Lib} {code : Bell → Option Nomm} {f : Noun} {nm : Nomm}
    (h : CallTree7 f nm) : ∀ P, Annot lib code P f nm := by
  induction h with
  | n0 axe => exact fun _ => Annot.n0
  | cons _ _ ihp ihq => exact fun P => Annot.cons (ihp P) (ihq P)
  | ind _ _ ihp ihq => exact fun P => Annot.indirect (ihp P) (ihq P)
  | @seven b c p q _ _ ihp ihq => exact fun P => Annot.n7 (ihp P) (ihq (Img lib P b))

theorem CallTree7.cell {f : Noun} {nm : Nomm} (h : CallTree7 f nm) : ∃ a b, f = C a b := by
  cases h with
  | n0 axe => exact ⟨_, _, rfl⟩
  | cons _ _ => exact ⟨_, _, rfl⟩
  | ind _ _ => exact ⟨_, _, rfl⟩
  | seven _ _ => exact ⟨_, _, rfl⟩

theorem CallTree7.sixCount {f : Noun} {nm : Nomm} (h : CallTree7 f nm) : sixCount nm = 0 := by
  induction h with
  | n0 axe => rfl
  | cons _ _ ihp ihq => simp only [Comp.sixCount, ihp, ihq]
  | ind _ _ ihp ihq => simp only [Comp.sixCount, ihp, ihq]
  | seven _ _ ihp ihq => simp only [Comp.sixCount, ihp, ihq]

theorem CallTree7.hinted_of {f : Noun} {nm : Nomm} (h : CallTree7 f nm) (cod : Bell → Option Bool) :
    nm.pure = false → hinted cod nm = some true := by
  induction h with
  | n0 axe => intro e; cases e
  | @cons a1 a2 b p q _ _ ihp ihq =>
    intro e
    simp only [hinted]
    cases ep : p.pure
    · rw [ihp ep]; rfl
    · rw [hinted_pure cod p ep]
      exact ihq (by simpa only [Nomm.pure, ep, Bool.true_and] using e)
  | ind _ _ => intro _; rfl
  | @seven b c p q _ _ ihp ihq =>
    intro e
    simp only [hinted]
    cases ep : p.pure
    · rw [ihp ep]; rfl
    · rw [hinted_pure cod p ep]
      exact ihq (by simpa only [Nomm.pure, ep, Bool.true_and] using e)

/-- **Each nomm of the class is call-free with `MinkEq`, or hinted.** -/
theorem CallTree7.kind (lib : Lib) (cod : Bell → Option Bool) (P : Noun → Prop) {f : Noun} {nm : Nomm}
    (h : CallTree7 f nm) : (nm.pure = true ∧ MinkEq lib P f nm) ∨ hinted cod nm = some true := by
  have hok : CodeOK lib (fun _ => Option.none) := fun _ _ h => by cases h
  cases hp : nm.pure
  · exact Or.inr (h.hinted_of cod hp)
  · exact Or.inl ⟨rfl, fun s hs gul tm r => mink_pure hok hp (h.annot P) hs gul tm r⟩

/-- **Every nomm of `CallTree7` meets `LOKS false`** on any subjects, and a
hinted one `JNewLS`, with only the premises of `LOKS.run` on the starting
goal and state. -/
theorem lokS_callTree7 (lib : Lib) {N : Needs} (env : CallEnv) {f : Noun} {nm : Nomm} (h : CallTree7 f nm) :
    ∀ P, LOKS (S := S) (Map := Map) false lib N env P f nm ∧
      (hinted env.cod nm = some true → JNewLS (S := S) (Map := Map) env nm) := by
  induction h with
  | n0 axe =>
    intro P
    have M := ((CallTree7.n0 axe).kind lib env.cod P).elim (fun h => h.2) (fun h => by cases h)
    refine ⟨?_, fun h => by cases h⟩
    rcases Nat.eq_zero_or_pos axe with rfl | ha
    · exact lokS_n00 lib env M
    · exact lokS_n0 lib env ha M
  | @cons a1 a2 b p q hp hq ihp ihq =>
    intro P
    have Kp := hp.kind lib env.cod P
    have Kq := hq.kind lib env.cod P
    exact ⟨lokS_consS lib env ⟨_, _, rfl⟩ Kp Kq (ihq P).2 (ihp P).1 (ihq P).1,
      fun _ => jNewLS_cons lib env ⟨_, _, rfl⟩ Kp Kq (ihq P).2 (ihp P).1 (ihq P).1⟩
  | @ind b c p q hp hq ihp ihq =>
    intro P
    have Kp := hp.kind lib env.cod P
    exact ⟨lokS_indirect lib env (minkC2_indirect lib P b c) hp.cell Kp (ihp P).1 (ihq P).1,
      fun _ => jNewLS_indirect lib env (minkC2_indirect lib P b c) hp.cell Kp (ihp P).1 (ihq P).1⟩
  | @seven b c p q hp hq ihp ihq =>
    intro P
    exact ⟨lokS_seven (ihq (Img lib P b)).1 (ihp P).1,
      jNewLS_seven (ihq (Img lib P b)).1 (ihp P).1 (ihq (Img lib P b)).2 (ihp P).2⟩

/-! ## The class at the top -/

/-- **A nomm with `LOKS` that begins under `%done` with the block `[don
re]`** meets `DoneOK` (`runLC_done_next`, `lokS_done`). -/
theorem done_of_lokS {x : Bool} {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (H : LOKS (S := S) (Map := Map) x lib N env P f nm) (hcount : sixCount nm ≤ 255)
    (hs : (∃ p q, nm = Nomm.cons p q) ∨ (∃ p q, nm = Nomm.n2 p q Option.none) ∨ (∃ ax, 1 ≤ ax ∧ nm = Nomm.n0 ax))
    {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (hr : runLC env sup nm CGoalL.done region g0 = some (nex, g1)) : DoneOK lib N P f g0 g1 nex := by
  rw [runLC_done_next env sup hs region g0] at hr
  exact lokS_done H hcount b0 d0 hu hcl hcb hr

/-- **Every nomm of `CallTree7` under `%done` meets `DoneOK`**: `[0 axe]`
by `callTree_done`, the cons and the indirect call by `done_of_lokS`,
`[7 p q]` with `q`'s `DoneOK` and `p`'s `LOKS` at `q`'s result through
`runOKGB_sevenL` (`topTree_done`'s step). -/
theorem callTree7_done (lib : Lib) {N : Needs} (env : CallEnv) {f : Noun} {nm : Nomm} (h : CallTree7 f nm) :
    ∀ (P : Noun → Prop) {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    runLC env sup nm CGoalL.done region g0 = some (nex, g1) → DoneOK (S := S) (Map := Map) lib N P f g0 g1 nex := by
  induction h with
  | n0 axe =>
    intro P sup region g0 g1 nex b0 d0 hu hcl hcb hr
    exact callTree_done lib env P (CallTree.n0 axe) b0 d0 hu hcl hcb hr
  | @cons a1 a2 b p q hp hq _ _ =>
    intro P sup region g0 g1 nex b0 d0 hu hcl hcb hr
    have hc := CallTree7.cons hp hq
    exact done_of_lokS (lokS_callTree7 lib env hc P).1 (by rw [hc.sixCount]; omega) (Or.inl ⟨_, _, rfl⟩)
      b0 d0 hu hcl hcb hr
  | @ind b c p q hp hq _ _ =>
    intro P sup region g0 g1 nex b0 d0 hu hcl hcb hr
    have hc := CallTree7.ind hp hq
    exact done_of_lokS (lokS_callTree7 lib env hc P).1 (by rw [hc.sixCount]; omega) (Or.inr (Or.inl ⟨_, _, rfl⟩))
      b0 d0 hu hcl hcb hr
  | @seven b c p q hp hq _ ihq =>
    intro P sup region g0 g1 nex b0 d0 hu hcl hcb hr
    rw [runLC_n7] at hr
    obtain ⟨nx, ga, h1, h2⟩ := bind_some hr
    have D := ihq (Img lib P b) b0 d0 hu hcl hcb h1
    have Rq := D.run
    have Lp := (lokS_callTree7 (S := S) (Map := Map) lib (N := N) env hp P).1
    have hj : nx.th.args = [] := by
      rcases Rq.ent with ⟨_, _, _, ha⟩ | e
      · exact ha
      · exact e.elim
    obtain ⟨⟨Q, RS⟩, hne, -, hfl, hec⟩ := Lp.run (sup := sup) (L := nx.laz) (th := nx.th) (region := region)
      (by rw [hp.sixCount]; omega) (by have := Rq.ext.2.1; omega) (Rq.ext.2.2.1.trans d0) (Rq.grow.up hu)
      (Clear.growU hcl Rq.grow) (Rq.cfr.below hcb) Rq.lo Rq.hi hj D.nent Rq.dist
      (fun x hx => ⟨by
        rcases Rq.regs x hx with e | e
        · exact e.elim
        · exact e.2, Rq.ncond x hx⟩)
      (fun e he => ⟨(Rq.labs e he).2.1, (Rq.labs e he).2.2⟩) Rq.nodup
      (fun e he => ⟨(Rq.eregs e he).1, fun x hx => ⟨((Rq.eregs e he).2 x hx).2, Rq.econd e he x hx⟩⟩)
      D.flat D.clean D.eclean h2
    exact ⟨runOKGB_sevenL (minkC7_seven lib P b c) Rq RS.toRunOKLB (fun r hr => hr.elim), hne, hfl,
      Lp.clean (L := nx.laz) D.clean h2, hec⟩

/-- **The contract of `CallTree7` at the top**: the whole-subject code of
every nomm of the class meets both halves of the contract for its formula,
on every subject, with no hypothesis about the run. -/
theorem finishLUC_contractCallTree7 (lib : Lib) (env : CallEnv) (P : Noun → Prop) {f : Noun} {nm : Nomm}
    (h : CallTree7 f nm) {c : Straight Map} (hc : finishLUC (S := S) env nm = some c) (N : Needs) :
    c.need = NeedOrd.this ∧ ∀ s, P s → ContractFwd lib N s f [s] c ∧ ContractBwd lib N s f [s] c :=
  finishLUC_contractGB lib N (fun hr => (callTree7_done (S := S) (Map := Map) lib env h P (by simp [gen0]) rfl
    upBelow_gen0 clear_gen0 condBelow_gen0 hr).run) hc

/-- **The bell contract of `CallTree7`** (`finishLUC_contractNC`'s form). -/
theorem finishLUC_bellContractCallTree7 {lib : Lib} {bl : Bell} {nm : Nomm} (h : CallTree7 bl.fol nm)
    {env : CallEnv} {cd : Straight Map} (hc : finishLUC (S := S) env nm = some cd) (N : Needs) :
    cd.need = NeedOrd.this ∧ BellContract lib N bl true cd := by
  have H := finishLUC_contractCallTree7 (S := S) lib env (SkaModel.Fits bl.less) h hc N
  refine ⟨H.1, fun s hs args hargs => ?_⟩
  simp only [if_true, Option.some.injEq] at hargs
  subst hargs
  exact H.2 s hs

/-- `TopTree` is inside `CallTree7`. -/
theorem CallTree.to7 {f : Noun} {nm : Nomm} (h : CallTree f nm) : CallTree7 f nm := by
  induction h with
  | n0 axe => exact CallTree7.n0 axe
  | cons _ _ ihp ihq => exact CallTree7.cons ihp ihq
  | ind _ _ ihp ihq => exact CallTree7.ind ihp ihq

theorem TopTree.to7 {f : Noun} {nm : Nomm} (h : TopTree f nm) : CallTree7 f nm := by
  induction h with
  | tree hc => exact hc.to7
  | seven hp _ ihq => exact CallTree7.seven hp.to7 ihq

/-! ## Examples -/

/-- `%7` inside a cons and inside an indirect call:
`[[7 [[0 3] [0 2]] [2 [0 2] [0 3]]] [2 [7 [0 3] [0 1]] [0 2]]]`. -/
theorem sevenIn_contract (lib : Lib) (env : CallEnv) {c : Straight Map}
    (hc : finishLUC (S := S) (Map := Map) env
      (Nomm.cons
        (Nomm.n7 (Nomm.cons (Nomm.n0 3) (Nomm.n0 2)) (Nomm.n2 (Nomm.n0 2) (Nomm.n0 3) Option.none))
        (Nomm.n2 (Nomm.n7 (Nomm.n0 3) (Nomm.n0 1)) (Nomm.n0 2) Option.none)) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (C (n3 (A 7) (C (slot 3) (slot 2)) (n3 (A 2) (slot 2) (slot 3)))
        (n3 (A 2) (n3 (A 7) (slot 3) (slot 1)) (slot 2))) [s] c ∧
      ContractBwd lib N s (C (n3 (A 7) (C (slot 3) (slot 2)) (n3 (A 2) (slot 2) (slot 3)))
        (n3 (A 2) (n3 (A 7) (slot 3) (slot 1)) (slot 2))) [s] c :=
  have H := finishLUC_contractCallTree7 lib env (fun _ => True)
    (CallTree7.cons
      (CallTree7.seven (CallTree7.cons (CallTree7.n0 3) (CallTree7.n0 2)) (CallTree7.ind (CallTree7.n0 2) (CallTree7.n0 3)))
      (CallTree7.ind (CallTree7.seven (CallTree7.n0 3) (CallTree7.n0 1)) (CallTree7.n0 2))) hc N
  ⟨H.1, fun s => H.2 s trivial⟩

end Comp
end SkaModel
end Formalization
