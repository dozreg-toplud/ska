import lemmas.Ska.CompGen
import lemmas.Ska.CompLBSeven

/-!
# `[7 p q]` in `RunOKGen`: the pieces that phase F needs

README Gaps 12.39, item 8.  `q` runs under `%next L th` (from `g0` to
`g1`), `p` under `q`'s result (from `g1` to `g2`).  When `p` is a `%6` in
phase F it re-points a goal entry `a` of `L` that `q` fronted with `Fq`: the
old body of `a` in `g1` is `Fq ++ B`.  Then the whole re-points `a`, and its
semantic front is `p`'s entry semantics (`FrontRG`) followed by `q`'s front
(`FrontLG`), composed by `EntA.front`: no lemma on register maps is needed,
because `EntA` states the jump as SOME ops in front of the body.

* `FillSemL.conv`: a fill from one input need is a fill from another.
* `EntA.conv`, `fillSemL_nil_nil`, `AgreeGA.restrict`: helpers.
* `agreeGA_seven`: the agreement of the whole and `p`'s fronts (re-pointed
  ones included) give `q`'s agreement, in the entry-semantics form.
* `frontRG_seven`: the front of a re-pointed entry composes.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **A fill of a conjunction moves to another input need** that holds
whenever the first does, whose registers are the first's or below `lo`. -/
theorem FillSemL.conv {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
    {N1 N2 : Need} {lo : Nat} {Ls : List (Sure S)} {A : List Pole} {x1 x2 s : Noun}
    (h : FillSemL (Map := Map) lib O c gul st t N2 lo Ls A x2 s)
    (hh : ∀ R : Map (Option Noun), HoldsN N1 R x1 → HoldsN N2 R x2)
    (hm : ∀ z, NMem N1 z → NMem N2 z ∨ z < lo) : FillSemL lib O c gul st t N1 lo Ls A x1 s := by
  intro R hR
  obtain ⟨F1, F2⟩ := h R (hh R hR)
  refine ⟨fun f => ?_, F2⟩
  obtain ⟨R', r, hs, k⟩ := F1 f
  exact ⟨R', r, hs, fun z hz hn => k z (hz.elim (hm z) Or.inr) hn⟩

/-- **The entry semantics moves to another input need.** -/
theorem EntA.conv {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
    {N1 N2 : Need} {lo : Nat} {Ls : List (Sure S)} {a : Nat} {B : List Pole} {fin : Termin} {x1 x2 s : Noun}
    (h : EntA (Map := Map) lib O c gul st t N2 lo Ls a B fin x2 s)
    (hh : ∀ R : Map (Option Noun), HoldsN N1 R x1 → HoldsN N2 R x2)
    (hm : ∀ z, NMem N1 z → NMem N2 z ∨ z < lo) : EntA lib O c gul st t N1 lo Ls a B fin x1 s :=
  let ⟨A, hf, hj⟩ := h
  ⟨A, hf.conv hh hm, fun R hR => hj R (hh R hR)⟩

/-- The empty fill of the empty conjunction. -/
theorem fillSemL_nil_nil {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
    {N : Need} {lo : Nat} {x s : Noun} : FillSemL (S := S) (Map := Map) lib O c gul st t N lo [] [] x s :=
  fun R _ => ⟨fun _ => ⟨R, Runs.nil R, fun _ h => by simp at h, fun _ _ _ => rfl⟩, fun ⟨_, h, _⟩ => by simp at h⟩

/-- **The agreement from `g0` is the agreement from a later `g1`.** -/
theorem AgreeGA.restrict {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
    {cond : Map (Nat × List Nat)} {ned : Need} {g0 g1 g2 : Gen Map} {laz : Lazy S} {s0 s : Noun}
    (h : AgreeGA lib O c gul st t cond ned g0 g2 laz s0 s) (hbo : g0.bo ≤ g1.bo) :
    AgreeGA lib O c gul st t cond ned g1 g2 laz s0 s :=
  ⟨fun o l u hn => h.1 o (Nat.le_trans hbo l) u hn, fun o ho l => h.2 o ho (Nat.le_trans hbo l)⟩

/-- **The front of an entry that `p` re-pointed after `q` fronted it**:
`p`'s entry semantics and `q`'s front give the whole's entry semantics, with
the witness `sevenWit`. -/
theorem frontRG_seven {Qp Qq : Wit} {E : Need} {g0 g1 g2 : Gen Map} {nex : NextL S} {a : Nat} {Fq B : List Pole}
    {fin : Termin} {Lp Lq : List (Sure S)}
    (hbo : g0.bo ≤ g1.bo) (cfr : CondFresh g1 g2)
    (hdp : ∀ s v d w r, Qp s v d w → NMem d r → g1.re ≤ r)
    (hb0 : HoonMap.get g0.blocks a = some ⟨[], B, fin⟩) (hFq : FrontBlk g0 g1 a Fq)
    (FQ : ∀ cf : Map (Nat × List Nat), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      FrontLG (Map := Map) Qq E g0.re g1.re Lp (Fq.map (renPole (unproxy cf))) Lq)
    (FP : FrontRG (Map := Map) Qp Need.none g1 g2 nex a Lp) :
    FrontRG (Map := Map) (sevenWit Qp Qq) E g0 g2 nex a Lq := by
  obtain ⟨Bp, finp, hb1, FP⟩ := FP
  have hb1' := hFq B fin hb0
  rw [hb1] at hb1'
  simp only [Option.some.injEq, Blob.mk.injEq, true_and] at hb1'
  obtain ⟨rfl, rfl⟩ := hb1'
  refine ⟨B, _, hb0, fun cf hcf lib σ O c gul ned s0 s v d w hned hq ag hc st t => ?_⟩
  obtain ⟨u, dp, wp, dq, wq, hp, hqq, rfl, rfl⟩ := hq
  have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk =>
    (hcf k (Nat.lt_of_lt_of_le hk cfr.1)).trans (cfr.get_lt hk)
  have E1 := FP cf hcf lib σ O c gul ned s0 s u dp wp hned hp (fun st' t' => (ag st' t').restrict hbo) hc st t
  simp only [unproxyBlob, renBlob, List.map_append] at E1 ⊢
  refine E1.front (fun A hA => ?_)
    (fun R (hR : HoldsN (Need.pair (Need.pair ned (Need.pair dp dq)) E) R (C (C s0 (C wp wq)) v)) =>
      ⟨⟨hR.1.1, hR.1.2.1⟩, trivial⟩)
  have h1 := FQ cf hcf1 lib σ O c gul st t (Need.pair (Need.pair ned dp) Need.none) A (C (C s0 wp) u) u v dq wq
    (fun r hr => by
      rcases hr with (hr | hr) | hr
      · exact Nat.le_trans cfr.1 (hned r hr)
      · exact hdp s u dp wp r hp hr
      · exact hr.elim) hqq hA
  refine h1.conv
    (fun R (hR : HoldsN (Need.pair (Need.pair ned (Need.pair dp dq)) E) R (C (C s0 (C wp wq)) v)) =>
      ⟨⟨⟨⟨hR.1.1, hR.1.2.1⟩, trivial⟩, hR.1.2.2⟩, hR.2⟩) (fun z hz => ?_)
  rcases hz with (hz | hz | hz) | hz
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hz))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hz))))
  · exact Or.inl (Or.inl (Or.inr hz))
  · exact Or.inl (Or.inr hz)

/-- **`q`'s agreement from the whole's and `p`'s fronts** (`[7 p q]`, `p`
with `x = false`): at a fresh lazy block `o` of `q`, `p` either put ops in
front (the whole's entry semantics at `o`, or `o`'s block when `p`'s result
has no entry there, then `p`'s front) or re-pointed it (`p`'s `FrontRG`),
and either way a jump into `o` runs as a fill of `q`'s needs at `o` from
`ned` and `p`'s witness `dp`, then `q`'s body.  This is the step of
`runOKLB_seven`'s `core` that phase F needs, in the entry-semantics form. -/
theorem agreeGA_seven {Qp : Wit} {g0 g1 g2 : Gen Map} {nx nex : NextL S}
    (Fp : FrameG (Map := Map) nx.laz nx.th Qp g1 g2 nex) (Sp : FrontsG (Map := Map) Qp false g1 g2 nx.laz nex)
    (hbo : g0.bo ≤ g1.bo)
    (qlab : ∀ o ∈ (entries nx.laz).map Prod.fst, g0.bo ≤ o →
      o < g1.bo ∧ ∃ B th, HoonMap.get g1.blocks o = some ⟨[], B, Termin.hop th⟩)
    {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {cf : Map (Nat × List Nat)} {ned : Need}
    {s0 s u : Noun} {dp : Need} {wp : Noun}
    (hcf : ∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g2.cond k) (hned : ∀ r, NMem ned r → g2.re ≤ r)
    (hp : Qp s u dp wp) (ag : ∀ (st : σ) (t : Trace), AgreeGA lib O c gul st t cf ned g0 g2 nex.laz s0 s) :
    ∀ (st : σ) (t : Trace), AgreeGA lib O c gul st t cf (Need.pair ned dp) g0 g1 nx.laz (C s0 wp) u := by
  intro st t
  have p2 := Fp.bo
  have plab : ∀ o, o ∈ (entries nex.laz).map Prod.fst → o ∈ (entries nx.laz).map Prod.fst ∨ g1.bo ≤ o :=
    fun o ho => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
      rcases (Fp.labs e he).1 with h | h
      · exact Or.inl h
      · exact Or.inr h.1
  have hE : ∀ R : Map (Option Noun), HoldsN (Need.pair ned dp) R (C s0 wp) →
      HoldsN (Need.pair (Need.pair ned dp) (gsE false nx.laz)) R (C (C s0 wp) u) :=
    fun R hR => ⟨hR, by simp [gsE, HoldsN]⟩
  have hm : ∀ z, NMem (Need.pair ned dp) z → NMem (Need.pair (Need.pair ned dp) (gsE false nx.laz)) z ∨ z < g1.re :=
    fun z hz => Or.inl (Or.inl hz)
  refine ⟨fun o l u' hn => ?_, fun o ho l => ?_⟩
  · have hn2 : o ∉ (entries nex.laz).map Prod.fst := fun hm => (plab o hm).elim hn (fun h => by omega)
    rw [(ag st t).1 o l (by omega) hn2, Fp.keep o u' hn]
  · obtain ⟨lt, Bq, th, hb1⟩ := qlab o ho l
    refine ⟨Bq, th, hb1, ?_⟩
    rcases Sp o ho with ⟨F, hF, FP⟩ | ⟨_, FR⟩
    · have hb2 := hF Bq (Termin.hop th) hb1
      have base : EntA lib O c gul st t ned g2.re (suresAt nex.laz o) o
          ((F ++ Bq).map (renPole (unproxy cf))) (Termin.hop (renJmp (unproxy cf) th)) s0 s := by
        by_cases hk : o ∈ (entries nex.laz).map Prod.fst
        · obtain ⟨B2, th2, hb3, E⟩ := (ag st t).2 o hk (by omega)
          rw [hb2] at hb3
          simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at hb3
          obtain ⟨rfl, rfl⟩ := hb3
          exact E
        · rw [suresAt_nil hk]
          refine EntA.ofBlock (A := []) ?_ fillSemL_nil_nil
          rw [(ag st t).1 o (by omega) (by omega) hk, hb2]
          simp [unproxyBlob, renBlob, renFin]
      rw [List.map_append] at base
      refine base.front (fun A hA => ?_) (fun R hR => hR.1)
      exact (FP cf hcf lib σ O c gul st t ned A s0 s u dp wp hned hp hA).conv hE hm
    · obtain ⟨B0, fin0, hb0, FR⟩ := FR
      rw [hb1] at hb0
      simp only [Option.some.injEq, Blob.mk.injEq, true_and] at hb0
      obtain ⟨rfl, rfl⟩ := hb0
      have hent : ∀ (st' : σ) (t' : Trace), ∃ b, HoonMap.get g2.blocks o = some b ∧
          EntA lib O c gul st' t' ned g2.re (suresAt nex.laz o) o (unproxyBlob cf b).body (unproxyBlob cf b).fin s0 s :=
        fun st' t' => by
          by_cases hk : o ∈ (entries nex.laz).map Prod.fst
          · obtain ⟨B2, th2, hb3, E⟩ := (ag st' t').2 o hk (by omega)
            exact ⟨_, hb3, by simpa [unproxyBlob, renBlob, renFin] using E⟩
          · have hc := (ag st' t').1 o (by omega) (by omega) hk
            obtain ⟨b, hb, hpar, _⟩ := Fp.grow.keep o _ lt hb1
            rw [hb] at hc
            refine ⟨b, hb, ?_⟩
            rw [suresAt_nil hk]
            refine EntA.ofBlock (A := []) ?_ fillSemL_nil_nil
            rw [hc]
            obtain ⟨par, body, fin⟩ := b
            simp only at hpar
            subst hpar
            simp [unproxyBlob, renBlob]
      have E := FR cf hcf lib σ O c gul ned s0 s u dp wp hned hp (fun st' t' => (ag st' t').restrict hbo) hent st t
      simp only [unproxyBlob, renBlob, renFin] at E
      exact E.conv hE hm

end Comp
end SkaModel
end Formalization
