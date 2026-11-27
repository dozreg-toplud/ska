import lemmas.Ska.CompFrontS

/-!
# The fronts of a pair whose parts read their goals' registers: `frontS_pairX`

README Gaps 12.32.  `frontS_pair` (`CompFrontS.lean`) composes the parts'
state-level fronts at one goal label when neither reads its goal's sure
registers (`E = Need.none`).  `frontS_pairX` takes parts of any flag: the
head's goal registers `Ep` and the tail's `Eq` are either the parent's own
(`+split` of `pair a b` or `both r a b`: `Ep = a`, `Eq = b`, held because `E`
holds the product) or the fresh halves `h`, `t` of `+split` of `this r`,
which the parent's witness holds (`pairWitX`, `H = pair (this h) (this t)`).

Tested before the proof (scratch `DisTest.lean` on the executable model of
`CompCall.lean`: 75 nomms built from `[0 1]`, `[0 2]`, `[0 3]`, `[4 [0 2]]`,
`[3 [0 3]]`, `[4 [0 1]]`, `[1 5]`, `[2 [0 3] [0 2]]` and cons, under 30 flat
lazy goals of 6 sure needs and 5 bond lists, 2 jumps, 2 states; 4,136 runs).
At every GOAL label a run's result entry is apart from its goal's sure
registers when the goal's entries are (no failure: the source of `hEp` and
`hEq`), and every result's entries are apart from its own sure registers
(no failure: the goal's property is kept).  At NEW labels the first fails
108 times, every one a cons with a hinted tail: the park entry
`(g''.bo, ofSure hed.sure)` holds the goal's own registers
(`[[0 1] [2 [0 3] [0 2]]]` under the sure need `[this 0 this 1]` has the
result entry `(5, this 0)`), so it is a fact about goal labels only.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The witness relation of a pair with halves `H`**: `pairWit` with the
registers `H` of the halves that `+split` allocated (`this r` split into
fresh `h`, `t`: `H = pair (this h) (this t)`), or `Need.none` when the
halves are the goal's own registers, holding the parts' products. -/
def pairWitX (comb : Noun → Noun → Noun) (H : Need) (Qp Qq : Wit) : Wit :=
  fun s v d w => ∃ vp vq dp dq wp wq, v = comb vp vq ∧ d = Need.pair H (Need.pair dp dq) ∧
    w = C (C vp vq) (C wp wq) ∧ Qp s vp dp wp ∧ Qq s vq dq wq

/-- **`frontS_pair` for parts of any flag** (README Gaps 12.32).  The head's
and the tail's fronts may read their goals' sure registers `Ep`, `Eq`; they
are held where the parent's goal registers `E` hold the product and the
halves `H` in the witness hold the parts' products (`hEH`), and the copy's
moves (and, for `Eq`, the head's ops) leave them alone (`hEp`, `hEq`).  The
halves lie in the parent's range below the tail's start, apart from the
parts' entries at the label and from the halves of the goal entry (`hH`). -/
theorem frontS_pairX {comb : Noun → Noun → Noun} {Qp Qq : Wit} {lo0 lo0q loq lo0p lop lo : Nat}
    {Lp Lq M Lh Lt Lb : Sure S} {Ac Fp Fq Fs : List Pole} {E Ep Eq H : Need}
    (FP : FrontS (Map := Map) Qp Ep lo0p lop Lp Fp Lh)
    (FQ : FrontS (Map := Map) Qq Eq lo0q loq Lq Fq Lt)
    (o1 : lo0 ≤ lo0q) (o2 : lo0q ≤ loq) (o3 : loq ≤ lo0p) (o4 : lo0p ≤ lop) (o5 : lop ≤ lo)
    (hdp : ∀ s v d w r, Qp s v d w → NMem d r → lo0p ≤ r ∧ r < lop)
    (hdq : ∀ s v d w r, Qq s v d w → NMem d r → lo0q ≤ r ∧ r < loq)
    (hLh : ∀ r, NMem Lh.ned r → r < lo0q ∧ (r < lo0 → NMem Lb.ned r))
    (hLt : ∀ r, NMem Lt.ned r → r < lo0q ∧ (r < lo0 → NMem Lb.ned r))
    (hht : ∀ r, NMem Lh.ned r → ¬ NMem Lt.ned r)
    (hM : ∀ r, NMem M.ned r → NMem Lp.ned r ∨ NMem Lq.ned r ∨ (lop ≤ r ∧ r < lo))
    (hMf : ∀ s, FitsS M s ↔ FitsS Lp s ∧ FitsS Lq s)
    (hMl : ∀ s, Looks M.lok s → Looks Lp.lok s ∧ Looks Lq.lok s)
    (hAc : CopySem Map Lp.ned Lq.ned M.ned Ac)
    (hFf : ∀ a b, FitsS Lb (comb a b) ↔ FitsS Lh a ∧ FitsS Lt b)
    (hFs : ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
      (R : Map (Option Noun)) (a b : Noun), HoldsN Lh.ned R a → HoldsN Lt.ned R b →
      ∃ R', Runs lib O c gul st t Fs R R' ∧ HoldsN Lb.ned R' (comb a b) ∧
        ∀ y, ¬ NMem Lb.ned y → SkaModel.read y R' = SkaModel.read y R)
    (hH : ∀ r, NMem H r → lo0 ≤ r ∧ r < lo0q ∧ ¬ NMem Lp.ned r ∧ ¬ NMem Lq.ned r ∧ ¬ NMem Lh.ned r ∧
      ¬ NMem Lt.ned r)
    (hEp : ∀ r, NMem Ep r → ¬ NMem Lp.ned r ∧ ¬ NMem Lq.ned r)
    (hEq : ∀ r, NMem Eq r → r < lo0q ∧ ¬ NMem Lp.ned r ∧ ¬ NMem Lq.ned r ∧ ¬ NMem Lh.ned r)
    (hEH : ∀ (R : Map (Option Noun)) (a b : Noun), HoldsN E R (comb a b) → HoldsN H R (C a b) →
      HoldsN Ep R a ∧ HoldsN Eq R b) :
    FrontS (Map := Map) (pairWitX comb H Qp Qq) E lo0 lo M (Ac ++ Fp ++ Fq ++ Fs) Lb := by
  -- registers of the parts' entries
  have lpL : ∀ r, NMem Lp.ned r → r < lop ∧ (r < lo0p → r < lo0q ∧ (r < lo0 → NMem Lb.ned r) ∧ ¬ NMem Lt.ned r) :=
    fun r hr => ⟨(FP.loc r hr).1, fun h => ⟨(hLh r ((FP.loc r hr).2 h)).1, (hLh r ((FP.loc r hr).2 h)).2,
      hht r ((FP.loc r hr).2 h)⟩⟩
  have lqL : ∀ r, NMem Lq.ned r → r < loq ∧ (r < lo0q → (r < lo0 → NMem Lb.ned r) ∧ ¬ NMem Lh.ned r) :=
    fun r hr => ⟨(FQ.loc r hr).1, fun h => ⟨(hLt r ((FQ.loc r hr).2 h)).2,
      fun hm => hht r hm ((FQ.loc r hr).2 h)⟩⟩
  refine ⟨fun r hr => ?_, fun s v d w hq r hd hm => ?_, fun s v d w hq fit => ?_, ?_⟩
  · -- loc
    rcases hM r hr with a | a | ⟨a, b⟩
    · obtain ⟨l1, l2⟩ := lpL r a
      exact ⟨by omega, fun h => (l2 (by omega)).2.1 h⟩
    · obtain ⟨l1, l2⟩ := lqL r a
      refine ⟨by omega, fun h => ?_⟩
      by_cases h' : r < lo0q
      · exact (l2 h').1 h
      · omega
    · exact ⟨b, fun h => by omega⟩
  · -- dis
    obtain ⟨vp, vq, dp, dq, wp, wq, rfl, rfl, rfl, qp, qq⟩ := hq
    rcases hd with hd | hd | hd
    · obtain ⟨a1, a2, a3, a4, _⟩ := hH r hd
      rcases hM r hm with a | a | ⟨a, _⟩
      · exact a3 a
      · exact a4 a
      · omega
    · have := hdp s vp dp wp r qp hd
      rcases hM r hm with a | a | ⟨a, _⟩
      · exact FP.dis s vp dp wp qp r hd a
      · have := (lqL r a).1; omega
      · omega
    · have := hdq s vq dq wq r qq hd
      rcases hM r hm with a | a | ⟨a, _⟩
      · obtain ⟨l1, l2⟩ := lpL r a
        have := (l2 (by omega)).1; omega
      · exact FQ.dis s vq dq wq qq r hd a
      · omega
  · -- fit
    obtain ⟨vp, vq, dp, dq, wp, wq, rfl, rfl, rfl, qp, qq⟩ := hq
    obtain ⟨fh, ft⟩ := (hFf vp vq).mp fit
    exact (hMf s).mpr ⟨FP.fit s vp dp wp qp fh, FQ.fit s vq dq wq qq ft⟩
  · -- run
    intro lib σ O c gul st t R s v d w hq hM' hd hE
    obtain ⟨vp, vq, dp, dq, wp, wq, rfl, rfl, rfl, qp, qq⟩ := hq
    have hdp' : HoldsN dp R wp := hd.2.1
    have hdq' : HoldsN dq R wq := hd.2.2
    obtain ⟨ep0, eq0⟩ := hEH R vp vq hE hd.1
    obtain ⟨lkp, lkq⟩ := hMl s hM'.2
    -- the moves of the copy
    obtain ⟨R1, r1, hp1, hq1, k1⟩ := hAc lib σ O c gul st t R s hM'.1
    have nLp_dp : ∀ x, NMem dp x → ¬ NMem (Need.pair Lp.ned Lq.ned) x := fun x hx hm => by
      have := hdp s vp dp wp x qp hx
      rcases hm with hm | hm
      · exact FP.dis s vp dp wp qp x hx hm
      · have := (lqL x hm).1; omega
    have nLp_dq : ∀ x, NMem dq x → ¬ NMem (Need.pair Lp.ned Lq.ned) x := fun x hx hm => by
      have := hdq s vq dq wq x qq hx
      rcases hm with hm | hm
      · obtain ⟨l1, l2⟩ := lpL x hm
        have := (l2 (by omega)).1; omega
      · exact FQ.dis s vq dq wq qq x hx hm
    have dp1 : HoldsN dp R1 wp := HoldsN.agree dp (fun x hx => k1 x (nLp_dp x hx)) hdp'
    have dq1 : HoldsN dq R1 wq := HoldsN.agree dq (fun x hx => k1 x (nLp_dq x hx)) hdq'
    -- the head's ops
    have nLp_E : ∀ x, NMem Ep x → ¬ NMem (Need.pair Lp.ned Lq.ned) x := fun x hx hm => by
      rcases hm with hm | hm
      · exact (hEp x hx).1 hm
      · exact (hEp x hx).2 hm
    have nLq_E : ∀ x, NMem Eq x → ¬ NMem (Need.pair Lp.ned Lq.ned) x := fun x hx hm => by
      rcases hm with hm | hm
      · exact (hEq x hx).2.1 hm
      · exact (hEq x hx).2.2.1 hm
    have ep1 : HoldsN Ep R1 vp := HoldsN.agree Ep (fun x hx => k1 x (nLp_E x hx)) ep0
    have eq1 : HoldsN Eq R1 vq := HoldsN.agree Eq (fun x hx => k1 x (nLq_E x hx)) eq0
    have Hp := FP.run lib σ O c gul st t R1 s vp dp wp qp ⟨hp1, lkp⟩ dp1 ep1
    -- keeps through the copy, for the whole
    have keepC : ∀ x, (x < lo0 ∨ lo ≤ x ∨ NMem (Need.pair H (Need.pair dp dq)) x) → ¬ NMem Lb.ned x →
        SkaModel.read x R1 = SkaModel.read x R := fun x hx hnx => by
      refine k1 x fun hm => ?_
      rcases hx with hx | hx | hx | hx | hx
      · rcases hm with hm | hm
        · exact hnx (((lpL x hm).2 (by omega)).2.1 hx)
        · exact hnx (((lqL x hm).2 (by omega)).1 hx)
      · rcases hm with hm | hm
        · have := (lpL x hm).1; omega
        · have := (lqL x hm).1; omega
      · rcases hm with hm | hm
        · exact (hH x hx).2.2.1 hm
        · exact (hH x hx).2.2.2.1 hm
      · exact nLp_dp x hx hm
      · exact nLp_dq x hx hm
    refine ⟨fun fit => ?_, fun nf => ?_⟩
    · obtain ⟨fh, ft⟩ := (hFf vp vq).mp fit
      obtain ⟨R2, r2, hh2, k2⟩ := Hp.1 fh
      have q2 : HoldsS Lq R2 s := ⟨HoldsN.agree _ (fun x hx => by
          have := (lqL x hx).1
          refine k2 x (Or.inl (by omega)) fun hm => ?_
          have := (hLh x hm).1
          by_cases h' : x < lo0q
          · exact ((lqL x hx).2 h').2 hm
          · omega) hq1, lkq⟩
      have dq2 : HoldsN dq R2 wq := HoldsN.agree dq (fun x hx => by
        have := hdq s vq dq wq x qq hx
        exact k2 x (Or.inl (by omega)) fun hm => by have := (hLh x hm).1; omega) dq1
      have eq2 : HoldsN Eq R2 vq := HoldsN.agree Eq (fun x hx => by
        have := (hEq x hx).1
        exact k2 x (Or.inl (by omega)) (hEq x hx).2.2.2) eq1
      obtain ⟨R3, r3, ht3, k3⟩ := (FQ.run lib σ O c gul st t R2 s vq dq wq qq q2 dq2 eq2).1 ft
      have hh3 : HoldsN Lh.ned R3 vp := HoldsN.agree _ (fun x hx => k3 x (Or.inl (hLh x hx).1) (hht x hx)) hh2.1
      obtain ⟨R4, r4, hb4, k4⟩ := hFs lib σ O c gul st t R3 vp vq hh3 ht3.1
      refine ⟨R4, ((r1.append r2).append r3).append r4, ⟨hb4, fit.2⟩, fun x hx hnx => ?_⟩
      rw [k4 x hnx, ← keepC x hx hnx]
      have nt : ¬ NMem Lt.ned x := fun hm => by
        rcases hx with hx | hx | hx | hx | hx
        · exact hnx ((hLt x hm).2 hx)
        · have := (hLt x hm).1; omega
        · exact (hH x hx).2.2.2.2.2 hm
        · have := (hLt x hm).1; have := hdp s vp dp wp x qp hx; omega
        · have := (hLt x hm).1; have := hdq s vq dq wq x qq hx; omega
      have nh : ¬ NMem Lh.ned x := fun hm => by
        rcases hx with hx | hx | hx | hx | hx
        · exact hnx ((hLh x hm).2 hx)
        · have := (hLh x hm).1; omega
        · exact (hH x hx).2.2.2.2.1 hm
        · have := (hLh x hm).1; have := hdp s vp dp wp x qp hx; omega
        · have := (hLh x hm).1; have := hdq s vq dq wq x qq hx; omega
      rw [k3 x ?_ nt, k2 x ?_ nh]
      · rcases hx with hx | hx | hx | hx | hx
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl (by omega))
        · have := (hH x hx).2.1; exact Or.inl (by omega)
        · exact Or.inr (Or.inr hx)
        · have := hdq s vq dq wq x qq hx; exact Or.inl (by omega)
      · rcases hx with hx | hx | hx | hx | hx
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl (by omega))
        · have := (hH x hx).2.1; exact Or.inl (by omega)
        · have := hdp s vp dp wp x qp hx; exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr hx)
    · have hnf : ¬ FitsS Lh vp ∨ (FitsS Lh vp ∧ ¬ FitsS Lt vq) := by
        by_cases fh : FitsS Lh vp
        · exact Or.inr ⟨fh, fun ft => nf ((hFf vp vq).mpr ⟨fh, ft⟩)⟩
        · exact Or.inl fh
      rcases hnf with fh | ⟨fh, ft⟩
      · have := Crashes.append_left (B := Fq ++ Fs) (Crashes.append_right r1 (Hp.2 fh))
        simpa only [List.append_assoc] using this
      · obtain ⟨R2, r2, hh2, k2⟩ := Hp.1 fh
        have q2 : HoldsS Lq R2 s := ⟨HoldsN.agree _ (fun x hx => by
            have := (lqL x hx).1
            refine k2 x (Or.inl (by omega)) fun hm => ?_
            have := (hLh x hm).1
            by_cases h' : x < lo0q
            · exact ((lqL x hx).2 h').2 hm
            · omega) hq1, lkq⟩
        have dq2 : HoldsN dq R2 wq := HoldsN.agree dq (fun x hx => by
          have := hdq s vq dq wq x qq hx
          exact k2 x (Or.inl (by omega)) fun hm => by have := (hLh x hm).1; omega) dq1
        have eq2 : HoldsN Eq R2 vq := HoldsN.agree Eq (fun x hx => by
          have := (hEq x hx).1
          exact k2 x (Or.inl (by omega)) (hEq x hx).2.2.2) eq1
        have := Crashes.append_left (B := Fs)
          (Crashes.append_right (r1.append r2) ((FQ.run lib σ O c gul st t R2 s vq dq wq qq q2 dq2 eq2).2 ft))
        simpa only [List.append_assoc] using this

/-- **`FrontsS.toFront` with the disjointness at the goal's labels only**
(README Gaps 12.32): the result entries at new labels may hold the goal's
own registers (the park entry of a cons with a hinted tail), and the field
`front` reads only the result entries at the goal's labels. -/
theorem FrontsS.toFrontG {Q : Wit} {x : Bool} {g0 g1 : Gen Map} {L : Lazy S} {nex : NextL S}
    (h : FrontsS (Map := Map) Q x g0 g1 L nex) (hl : g0.re ≤ g1.re)
    (hL : ∀ r, NMem L.sure.ned r → r < g0.re)
    (hLE : ∀ e ∈ entries nex.laz, e.1 ∈ (entries L).map Prod.fst → ∀ r, NMem (gsE x L) r → ¬ NMem e.2.sure.ned r)
    (hd : ∀ s v d w r, Q s v d w → NMem d r → g0.re ≤ r ∧ r < g1.re) :
    ∀ e ∈ entries L, ∃ F : List Pole,
      (∀ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩ → HoonMap.get g1.blocks e.1 = some ⟨[], F ++ B, fin⟩) ∧
      ∀ cf : Map (Nat × List Nat), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      ((∃ L', (e.1, L') ∈ entries nex.laz ∧
          FrontLB (Map := Map) Q (gsE x L) g0.re g1.re L'.sure (F.map (renPole (unproxy cf))) e.2.sure) ∨
       (e.1 ∉ (entries nex.laz).map Prod.fst ∧
          FrontLB (Map := Map) Q (gsE x L) g0.re g1.re Sure.bunt (F.map (renPole (unproxy cf))) e.2.sure)) := by
  intro e he
  have hel : e.1 ∈ (entries L).map Prod.fst := List.mem_map.mpr ⟨e, he, rfl⟩
  obtain ⟨F, hb, hf⟩ := h e he
  have hE := gsE_lt (x := x) hL
  refine ⟨F, hb, fun cf hcf => (hf cf hcf).imp (fun ⟨L', hm, fs⟩ => ⟨L', hm, fs.toLB hl
    (fun r hr => ⟨hE r hr, hLE _ hm hel r hr⟩) hd⟩) (fun ⟨hn, fs⟩ => ⟨hn, fs.toLB hl
    (fun r hr => ⟨hE r hr, fun hm => by simp [Sure.bunt, NMem] at hm⟩) hd⟩)⟩

end Comp
end SkaModel
end Formalization
