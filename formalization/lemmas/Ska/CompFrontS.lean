import lemmas.Ska.CompLBFour

/-!
# Fronts at the state level: `FrontS`, `FrontsS`, `RunOKLS`

README Gaps 12.24.  `RunOKLB.front` (`CompRunOKLB.lean`) says what the ops
`F` a run put in front of a goal entry's block do through `FrontLB`: for
EVERY ops `A` that fill the run's result entry `L'` and keep every register
below the run's end but those of `L'`, `A ++ F` fill the goal entry.  That
form does not compose where `+copy` merges two parts' entries at one label
(`%bc2`: `5: mov v0 v4, mov v4 v5, hop 3`; `%bc1`: the inner cons's halves
`[v6 ~]`, `[~ v7]` merged into `[v6 v7]`): before the head's ops run, the
fill of the merged need and the copy's moves have written the TAIL's
registers, which lie below the head's end, so no `A` of the head's
`FrontLB` describes the state the head's ops start from.

`FrontS` says the same at the level of the state just before `F`: from any
registers where `L'` holds the subject, the witness `d` holds `w` and the
goal's registers `E` hold the product, `F` fills the goal entry and keeps
every register outside the run's range and the entry, or crashes where the
product does not fit the entry; with the facts that make it imply
`FrontLB` (`FrontS.toLB`): the result entry's registers below the run's
start are the goal entry's (`loc`, label-locality), the witness is apart
from it (`dis`), and a product that fits the entry comes from a subject
that fits `L'` (`fit`).

* `FrontS`, `FrontS.toLB`, `frontS_bunt` (the result has no entry at the
  label and the product never fits a witness), `frontS_empty` (an empty
  half pruned by `+lazy-prune`: no op, nothing asked).
* `pairWit`, `frontS_pair`: the fronts of the two parts of a pair at one
  goal label compose with the moves of `+copy` in front and the ops of
  `+split` (or `+into`) behind, the parts' entries merged or not.
* `FrontsS` (every goal entry's front of a run as `FrontS`), `RunOKLS`
  (`RunOKLB` with `FrontsS`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The state-level front -/

/-- **What the ops `F` a run put in front of a goal entry's block do, from
the state just before them.**  `L'` is the run's result entry at that label
(`bunt` when it has none), `L` the goal entry, `E` the goal's registers the
ops may read (`gsE x`), `lo0`, `lo` the run's range of registers. -/
structure FrontS (Q : Wit) (E : Need) (lo0 lo : Nat) (L' : Sure S) (F : List Pole) (L : Sure S) : Prop where
  loc : ∀ r, NMem L'.ned r → r < lo ∧ (r < lo0 → NMem L.ned r)
  dis : ∀ s v d w, Q s v d w → ∀ r, NMem d r → ¬ NMem L'.ned r
  fit : ∀ s v d w, Q s v d w → FitsS L v → FitsS L' s
  run : ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
    (R : Map (Option Noun)) (s v : Noun) (d : Need) (w : Noun), Q s v d w →
    HoldsS L' R s → HoldsN d R w → HoldsN E R v →
    (FitsS L v → ∃ R', Runs lib O c gul st t F R R' ∧ HoldsS L R' v ∧
      ∀ x, (x < lo0 ∨ lo ≤ x ∨ NMem d x) → ¬ NMem L.ned x → SkaModel.read x R' = SkaModel.read x R) ∧
    (¬ FitsS L v → Crashes lib O c gul st t F R)

/-- **`FrontS` gives `FrontLB`**, when the goal's registers `E` lie below
the run's start and apart from `L'`, and the witness in the run's range. -/
theorem FrontS.toLB {Q : Wit} {E : Need} {lo0 lo : Nat} {L' : Sure S} {F : List Pole} {L : Sure S}
    (h : FrontS (Map := Map) Q E lo0 lo L' F L) (hl : lo0 ≤ lo)
    (hE : ∀ r, NMem E r → r < lo0 ∧ ¬ NMem L'.ned r)
    (hd : ∀ s v d w r, Q s v d w → NMem d r → lo0 ≤ r ∧ r < lo) :
    FrontLB (Map := Map) Q E lo0 lo L' F L := by
  intro lib σ O c gul st t ned A s0 s v d w hn hq hf R hR
  have hR0 : HoldsN ned R s0 := hR.1.1
  have hRd : HoldsN d R w := hR.1.2
  have hRE : HoldsN E R v := hR.2
  -- the state after `A`, where `L'` holds the subject
  have after : FitsS L' s → ∃ R1, Runs lib O c gul st t A R R1 ∧ HoldsS L' R1 s ∧
      (∀ x, (NMem ned x ∨ x < lo) → ¬ NMem L'.ned x → SkaModel.read x R1 = SkaModel.read x R) ∧
      HoldsN d R1 w ∧ HoldsN E R1 v := fun fs => by
    obtain ⟨R1, r1, h1, k1⟩ := (hf R hR0).1 fs
    refine ⟨R1, r1, h1, k1, HoldsN.agree d (fun x hx => k1 x (Or.inr (hd s v d w x hq hx).2)
      (h.dis s v d w hq x hx)) hRd, HoldsN.agree E (fun x hx => k1 x (Or.inr (by have := (hE x hx).1; omega))
      (hE x hx).2) hRE⟩
  refine ⟨fun fit => ?_, fun nf => ?_⟩
  · obtain ⟨R1, r1, h1, k1, d1, e1⟩ := after (h.fit s v d w hq fit)
    obtain ⟨R2, r2, h2, k2⟩ := (h.run lib σ O c gul st t R1 s v d w hq h1 d1 e1).1 fit
    refine ⟨R2, r1.append r2, h2, fun x hx hnx => ?_⟩
    have hx' : (NMem ned x ∨ NMem d x ∨ NMem E x) ∨ x < lo0 := by
      rcases hx with hx | hx
      · rcases hx with (hx | hx) | hx
        · exact Or.inl (Or.inl hx)
        · exact Or.inl (Or.inr (Or.inl hx))
        · exact Or.inl (Or.inr (Or.inr hx))
      · exact Or.inr hx
    rw [k2 x ?_ hnx]
    · refine k1 x ?_ ?_
      · rcases hx' with hx' | hx'
        · rcases hx' with hx' | hx' | hx'
          · exact Or.inl hx'
          · exact Or.inr (hd s v d w x hq hx').2
          · exact Or.inr (by have := (hE x hx').1; omega)
        · exact Or.inr (by omega)
      · intro hm
        rcases hx' with hx' | hx'
        · rcases hx' with hx' | hx' | hx'
          · have := (h.loc x hm).1; have := hn x hx'; omega
          · exact h.dis s v d w hq x hx' hm
          · exact (hE x hx').2 hm
        · exact hnx ((h.loc x hm).2 hx')
    · rcases hx' with hx' | hx'
      · rcases hx' with hx' | hx' | hx'
        · exact Or.inr (Or.inl (hn x hx'))
        · exact Or.inr (Or.inr hx')
        · exact Or.inl (hE x hx').1
      · exact Or.inl hx'
  · by_cases fs : FitsS L' s
    · obtain ⟨R1, r1, h1, k1, d1, e1⟩ := after fs
      exact Crashes.append_right r1 ((h.run lib σ O c gul st t R1 s v d w hq h1 d1 e1).2 nf)
    · exact Crashes.append_left ((hf R hR0).2 fs)

/-- **No result entry and a witness relation that never holds**: any ops. -/
theorem frontS_false {Q : Wit} {E : Need} {lo0 lo : Nat} {F : List Pole} {L : Sure S}
    (hQ : ∀ s v d w, ¬ Q s v d w) : FrontS (Map := Map) Q E lo0 lo Sure.bunt F L :=
  ⟨fun r hr => by simp [Sure.bunt, NMem] at hr, fun s v d w hq => absurd hq (hQ s v d w),
    fun s v d w hq => absurd hq (hQ s v d w),
    fun lib σ O c gul st t R s v d w hq => absurd hq (hQ s v d w)⟩

/-- **An empty half pruned by `+lazy-prune`**: no op, the entry asks
nothing. -/
theorem frontS_empty {Q : Wit} {E : Need} {lo0 lo : Nat} {L : Sure S} (hn : L.ned = Need.none)
    (hs : HoonSet.small L.lok = true) :
    FrontS (Map := Map) Q E lo0 lo Sure.bunt [] L := by
  refine ⟨fun r hr => by simp [Sure.bunt, NMem] at hr, fun s v d w _ r _ hr => by simp [Sure.bunt, NMem] at hr,
    fun s v d w _ _ => fitsS_bunt s, fun lib σ O c gul st t R s v d w _ _ _ _ => ⟨fun _ => ?_, fun nf => ?_⟩⟩
  · exact ⟨R, Runs.nil R, ⟨by rw [hn]; trivial, looks_small hs v⟩, fun _ _ _ => rfl⟩
  · exact absurd (fitsS_trivial hn hs v) nf

/-! ## The two parts of a pair at one goal label -/

/-- **The witness relation of a pair** whose two parts run on the same
subject and whose product is `comb` of theirs: the witnesses side by side. -/
def pairWit (comb : Noun → Noun → Noun) (Qp Qq : Wit) : Wit :=
  fun s v d w => ∃ vp vq dp dq wp wq, v = comb vp vq ∧ d = Need.pair dp dq ∧ w = C wp wq ∧
    Qp s vp dp wp ∧ Qq s vq dq wq

/-- **The fronts of the two parts of a pair at one goal label compose.**
At run time the block holds, in front of its old body, the moves `Ac` of
`+copy` (which fill the parts' result entries `Lp`, `Lq` from the merged
`M`; `Ac = []`, `M` the one entry, when at most one part kept one), the
head's ops `Fp`, the tail's ops `Fq`, and the ops `Fs` that `+split` (or
`+into`) put there to build the goal entry `Lb` from its halves `Lh`, `Lt`.
The registers lie in the order of compilation: the halves from the parent's
start `lo0` to the tail's start `lo0q`, the tail's run to `loq`, the head's
from `lo0p` to `lop`, the copy's to the parent's end `lo`. -/
theorem frontS_pair {comb : Noun → Noun → Noun} {Qp Qq : Wit} {lo0 lo0q loq lo0p lop lo : Nat}
    {Lp Lq M Lh Lt Lb : Sure S} {Ac Fp Fq Fs : List Pole}
    (FP : FrontS (Map := Map) Qp Need.none lo0p lop Lp Fp Lh)
    (FQ : FrontS (Map := Map) Qq Need.none lo0q loq Lq Fq Lt)
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
        ∀ y, ¬ NMem Lb.ned y → SkaModel.read y R' = SkaModel.read y R) :
    FrontS (Map := Map) (pairWit comb Qp Qq) Need.none lo0 lo M (Ac ++ Fp ++ Fq ++ Fs) Lb := by
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
    rcases hd with hd | hd
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
    have hdp' : HoldsN dp R wp := hd.1
    have hdq' : HoldsN dq R wq := hd.2
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
    have Hp := FP.run lib σ O c gul st t R1 s vp dp wp qp ⟨hp1, lkp⟩ dp1 trivial
    -- keeps through the copy, for the whole
    have keepC : ∀ x, (x < lo0 ∨ lo ≤ x ∨ NMem (Need.pair dp dq) x) → ¬ NMem Lb.ned x →
        SkaModel.read x R1 = SkaModel.read x R := fun x hx hnx => by
      refine k1 x fun hm => ?_
      rcases hx with hx | hx | hx | hx
      · rcases hm with hm | hm
        · exact hnx (((lpL x hm).2 (by omega)).2.1 hx)
        · exact hnx (((lqL x hm).2 (by omega)).1 hx)
      · rcases hm with hm | hm
        · have := (lpL x hm).1; omega
        · have := (lqL x hm).1; omega
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
      obtain ⟨R3, r3, ht3, k3⟩ := (FQ.run lib σ O c gul st t R2 s vq dq wq qq q2 dq2 trivial).1 ft
      have hh3 : HoldsN Lh.ned R3 vp := HoldsN.agree _ (fun x hx => k3 x (Or.inl (hLh x hx).1) (hht x hx)) hh2.1
      obtain ⟨R4, r4, hb4, k4⟩ := hFs lib σ O c gul st t R3 vp vq hh3 ht3.1
      refine ⟨R4, ((r1.append r2).append r3).append r4, ⟨hb4, fit.2⟩, fun x hx hnx => ?_⟩
      rw [k4 x hnx, ← keepC x hx hnx]
      have nt : ¬ NMem Lt.ned x := fun hm => by
        rcases hx with hx | hx | hx | hx
        · exact hnx ((hLt x hm).2 hx)
        · have := (hLt x hm).1; omega
        · have := (hLt x hm).1; have := hdp s vp dp wp x qp hx; omega
        · have := (hLt x hm).1; have := hdq s vq dq wq x qq hx; omega
      have nh : ¬ NMem Lh.ned x := fun hm => by
        rcases hx with hx | hx | hx | hx
        · exact hnx ((hLh x hm).2 hx)
        · have := (hLh x hm).1; omega
        · have := (hLh x hm).1; have := hdp s vp dp wp x qp hx; omega
        · have := (hLh x hm).1; have := hdq s vq dq wq x qq hx; omega
      rw [k3 x ?_ nt, k2 x ?_ nh]
      · rcases hx with hx | hx | hx | hx
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr hx)
        · have := hdq s vq dq wq x qq hx; exact Or.inl (by omega)
      · rcases hx with hx | hx | hx | hx
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl (by omega))
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
        have := Crashes.append_left (B := Fs)
          (Crashes.append_right (r1.append r2) ((FQ.run lib σ O c gul st t R2 s vq dq wq qq q2 dq2 trivial).2 ft))
        simpa only [List.append_assoc] using this

/-! ## The fronts of a run and the relation -/

/-- **Every goal entry's front of a run as `FrontS`**: the ops `F` the run
put in front of the entry's block, unproxied, fill the entry from the
run's result entry at that label (or from nothing). -/
def FrontsS (Q : Wit) (x : Bool) (g0 g1 : Gen Map) (L : Lazy S) (nex : NextL S) : Prop :=
  ∀ e ∈ entries L, ∃ F : List Pole,
    (∀ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩ → HoonMap.get g1.blocks e.1 = some ⟨[], F ++ B, fin⟩) ∧
    ∀ cf : Map (Nat × List Nat), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ((∃ L', (e.1, L') ∈ entries nex.laz ∧
        FrontS (Map := Map) Q (gsE x L) g0.re g1.re L'.sure (F.map (renPole (unproxy cf))) e.2.sure) ∨
     (e.1 ∉ (entries nex.laz).map Prod.fst ∧
        FrontS (Map := Map) Q (gsE x L) g0.re g1.re Sure.bunt (F.map (renPole (unproxy cf))) e.2.sure))

/-- **`RunOKLB` with every front at the state level.** -/
structure RunOKLS (lib : Lib) (P : Noun → Prop) (f : Noun) (L : Lazy S) (th : Jmp) (Q : Wit) (x : Bool)
    (g0 g1 : Gen Map) (nex : NextL S) : Prop extends RunOKLB (Map := Map) lib P f L th Q x g0 g1 nex where
  fs : FrontsS (Map := Map) Q x g0 g1 L nex

/-- **The fronts of `FrontsS` give the field `front` of `RunOKLB`.** -/
theorem FrontsS.toFront {Q : Wit} {x : Bool} {g0 g1 : Gen Map} {L : Lazy S} {nex : NextL S}
    (h : FrontsS (Map := Map) Q x g0 g1 L nex) (hl : g0.re ≤ g1.re)
    (hL : ∀ r, NMem L.sure.ned r → r < g0.re)
    (hLE : ∀ e ∈ entries nex.laz, ∀ r, NMem (gsE x L) r → ¬ NMem e.2.sure.ned r)
    (hd : ∀ s v d w r, Q s v d w → NMem d r → g0.re ≤ r ∧ r < g1.re) :
    ∀ e ∈ entries L, ∃ F : List Pole,
      (∀ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩ → HoonMap.get g1.blocks e.1 = some ⟨[], F ++ B, fin⟩) ∧
      ∀ cf : Map (Nat × List Nat), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      ((∃ L', (e.1, L') ∈ entries nex.laz ∧
          FrontLB (Map := Map) Q (gsE x L) g0.re g1.re L'.sure (F.map (renPole (unproxy cf))) e.2.sure) ∨
       (e.1 ∉ (entries nex.laz).map Prod.fst ∧
          FrontLB (Map := Map) Q (gsE x L) g0.re g1.re Sure.bunt (F.map (renPole (unproxy cf))) e.2.sure)) := by
  intro e he
  obtain ⟨F, hb, hf⟩ := h e he
  have hE := gsE_lt (x := x) hL
  refine ⟨F, hb, fun cf hcf => (hf cf hcf).imp (fun ⟨L', hm, fs⟩ => ⟨L', hm, fs.toLB hl
    (fun r hr => ⟨hE r hr, hLE _ hm r hr⟩) hd⟩) (fun ⟨hn, fs⟩ => ⟨hn, fs.toLB hl
    (fun r hr => ⟨hE r hr, fun hm => by simp [Sure.bunt, NMem] at hm⟩) hd⟩)⟩

end Comp
end SkaModel
end Formalization
