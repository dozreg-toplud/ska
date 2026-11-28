import lemmas.Ska.CompGenClassB

/-!
# The fronts of the general cons at one label

README Gaps 12.39, item 12.  The finding first.  `FrontLG` (the form of
`FrontsG` in `RunOKGen`) describes a part's front `F` through every fill `A`
of the part's result needs that keeps every register below the part's end
(relative to the registers before `A`).  At a goal label of the cons the
block holds the copy's ops `Pc`, then `p`'s front `Fp`, then `q`'s `Fq`, then
the split's `Ps`.  `Pc` fills `q`'s result needs there, whose registers lie
below `q`'s end `g2.re` and so below `p`'s end: `A ++ Pc` is no fill of
`p`'s result needs in the sense of `p`'s `FrontLG` (it changes registers
below `g3.re` outside them), and likewise `A ++ Pc ++ Fp` is none of `q`'s
(`Fp` writes `hed`'s registers, below `g2.re`).  So the parts' `FrontLG` do
not give the whole's: the finding of Gaps 12.24 (`FrontLB`) again, at
conjunctions.  As there, the cure is the front at the level of the state
just before `F`: `FrontSG` (`FrontS` of `CompFrontS.lean` for the
conjunctions at one label), which gives `FrontLG` (`FrontSG.toLG`) and
composes for the cons (`frontSG_consG`, the conjunction form of
`frontS_pair`).  The class then has to carry `FrontSG` of every non
re-pointed goal label beside `FrontsG`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The front at one label, from the state just before it, in
conjunctions**: `Ls'` the result's needs at the label, `Ls` the goal's,
`E` the goal's registers the ops may read, `lo0`, `lo` the run's range.
From any registers where every need of `Ls'` holds the subject, `d` the
witness and `E` the product, `F` fills every need of `Ls` with the product,
keeping every register outside the run's range (and `d`'s) outside `Ls`, or
crashes where the product does not fit one of them.  `loc`: a result
register below the run's start is a goal register at the label; `dis`: the
witness is apart from the result's needs; `fit`: a product that fits the
goal's needs comes from a subject that fits the result's. -/
structure FrontSG (Q : Wit) (E : Need) (lo0 lo : Nat) (Ls' : List (Sure S)) (F : List Pole) (Ls : List (Sure S)) :
    Prop where
  loc : ∀ L' ∈ Ls', ∀ r, NMem L'.ned r → r < lo ∧ (r < lo0 → ∃ L ∈ Ls, NMem L.ned r)
  dis : ∀ s v d w, Q s v d w → ∀ r, NMem d r → ∀ L' ∈ Ls', ¬ NMem L'.ned r
  fit : ∀ s v d w, Q s v d w → (∀ L ∈ Ls, FitsS L v) → ∀ L' ∈ Ls', FitsS L' s
  run : ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
    (R : Map (Option Noun)) (s v : Noun) (d : Need) (w : Noun), Q s v d w →
    (∀ L' ∈ Ls', HoldsS L' R s) → HoldsN d R w → HoldsN E R v →
    ((∀ L ∈ Ls, FitsS L v) → ∃ R', Runs lib O c gul st t F R R' ∧ (∀ L ∈ Ls, HoldsS L R' v) ∧
      ∀ x, (x < lo0 ∨ lo ≤ x ∨ NMem d x) → (∀ L ∈ Ls, ¬ NMem L.ned x) →
        SkaModel.read x R' = SkaModel.read x R) ∧
    ((∃ L ∈ Ls, ¬ FitsS L v) → Crashes lib O c gul st t F R)

theorem ce_holdsS_fits {L : Sure S} {R : Map (Option Noun)} {s : Noun} (h : HoldsS L R s) : FitsS L s :=
  ⟨fits_of_holds _ h.1, h.2⟩

/-- **`FrontSG` gives `FrontLG`**, when the goal's registers `E` lie below
the run's start and apart from the result's needs, and the witness in the
run's range (`FrontS.toLB` for conjunctions). -/
theorem FrontSG.toLG {Q : Wit} {E : Need} {lo0 lo : Nat} {Ls' : List (Sure S)} {F : List Pole}
    {Ls : List (Sure S)} (h : FrontSG (Map := Map) Q E lo0 lo Ls' F Ls) (hl : lo0 ≤ lo)
    (hE : ∀ r, NMem E r → r < lo0 ∧ ∀ L' ∈ Ls', ¬ NMem L'.ned r)
    (hd : ∀ s v d w r, Q s v d w → NMem d r → lo0 ≤ r ∧ r < lo) :
    FrontLG (Map := Map) Q E lo0 lo Ls' F Ls := by
  intro lib σ O c gul st t ned A s0 s v d w hn hq hf R hR
  have hR0 : HoldsN ned R s0 := hR.1.1
  have hRd : HoldsN d R w := hR.1.2
  have hRE : HoldsN E R v := hR.2
  have after : (∀ L' ∈ Ls', FitsS L' s) → ∃ R1, Runs lib O c gul st t A R R1 ∧ (∀ L' ∈ Ls', HoldsS L' R1 s) ∧
      (∀ x, (NMem ned x ∨ x < lo) → (∀ L' ∈ Ls', ¬ NMem L'.ned x) → SkaModel.read x R1 = SkaModel.read x R) ∧
      HoldsN d R1 w ∧ HoldsN E R1 v := fun fs => by
    obtain ⟨R1, r1, h1, k1⟩ := (hf R hR0).1 fs
    refine ⟨R1, r1, h1, k1, HoldsN.agree d (fun x hx => k1 x (Or.inr (hd s v d w x hq hx).2)
      (fun L' hL' => h.dis s v d w hq x hx L' hL')) hRd, HoldsN.agree E (fun x hx => k1 x
        (Or.inr (by have := (hE x hx).1; omega)) (hE x hx).2) hRE⟩
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
      · intro L' hL' hm
        rcases hx' with hx' | hx'
        · rcases hx' with hx' | hx' | hx'
          · have := (h.loc L' hL' x hm).1; have := hn x hx'; omega
          · exact h.dis s v d w hq x hx' L' hL' hm
          · exact (hE x hx').2 L' hL' hm
        · obtain ⟨L, hL, hm'⟩ := (h.loc L' hL' x hm).2 hx'
          exact hnx L hL hm'
    · rcases hx' with hx' | hx'
      · rcases hx' with hx' | hx' | hx'
        · exact Or.inr (Or.inl (hn x hx'))
        · exact Or.inr (Or.inr hx')
        · exact Or.inl (hE x hx').1
      · exact Or.inl hx'
  · by_cases fs : ∀ L' ∈ Ls', FitsS L' s
    · obtain ⟨R1, r1, h1, k1, d1, e1⟩ := after fs
      exact Crashes.append_right r1 ((h.run lib σ O c gul st t R1 s v d w hq h1 d1 e1).2 nf)
    · have : ∃ L' ∈ Ls', ¬ FitsS L' s :=
        Classical.byContradiction fun ne => fs fun L' hL' => Classical.byContradiction fun nf' => ne ⟨L', hL', nf'⟩
      exact Crashes.append_left ((hf R hR0).2 this)

/-- **The fronts of the two parts of the cons at one goal label compose**
(`frontS_pair` in conjunctions).  At run time the block holds the copy's ops
`Pc` (filling `p`'s result needs `Lp` and `q`'s `Lq` at the label from the
merged needs `Ms`), `p`'s front `Fp`, `q`'s front `Fq`, and the split's ops
`Ps` (building the goal's needs `Ls` from the halves `Lh`, `Lt`).  The
registers in the order of compilation: the halves from the parent's start
`lo0` to `q`'s start `lo1`, `q`'s run to `lo2`, `p`'s to `lo3`, the copy's to
the parent's end `lo4`. -/
theorem frontSG_consG {Qp Qq : Wit} {lo0 lo1 lo2 lo3 lo4 : Nat} {Ms Lp Lq Lh Lt Ls : List (Sure S)}
    {Pc Fp Fq Ps : List Pole}
    (FP : FrontSG (Map := Map) Qp Need.none lo2 lo3 Lp Fp Lh)
    (FQ : FrontSG (Map := Map) Qq Need.none lo1 lo2 Lq Fq Lt)
    (o1 : lo0 ≤ lo1) (o2 : lo1 ≤ lo2) (o3 : lo2 ≤ lo3) (o4 : lo3 ≤ lo4)
    (hdp : ∀ s v d w r, Qp s v d w → NMem d r → lo2 ≤ r ∧ r < lo3)
    (hdq : ∀ s v d w r, Qq s v d w → NMem d r → lo1 ≤ r ∧ r < lo2)
    (hLh : ∀ H ∈ Lh, ∀ r, NMem H.ned r → r < lo1 ∧ (r < lo0 → ∃ L ∈ Ls, NMem L.ned r))
    (hLt : ∀ T ∈ Lt, ∀ r, NMem T.ned r → r < lo1 ∧ (r < lo0 → ∃ L ∈ Ls, NMem L.ned r))
    (hht : ∀ H ∈ Lh, ∀ T ∈ Lt, ∀ r, NMem H.ned r → ¬ NMem T.ned r)
    (hM : ∀ M ∈ Ms, ∀ r, NMem M.ned r → (∃ F ∈ Lp ++ Lq, NMem F.ned r) ∨ (lo3 ≤ r ∧ r < lo4))
    (Cfit : ∀ z, (∀ M ∈ Ms, FitsS M z) ↔ (∀ F ∈ Lp, FitsS F z) ∧ (∀ T ∈ Lq, FitsS T z))
    (Crun : ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st' : σ) (t : Trace)
      (R : Map (Option Noun)) (z : Noun), (∀ M ∈ Ms, HoldsN M.ned R z) →
      ∃ R', Runs lib O c gul st' t Pc R R' ∧ (∀ F ∈ Lp ++ Lq, HoldsN F.ned R' z) ∧
        ∀ y, (∀ F ∈ Lp ++ Lq, ¬ NMem F.ned y) → SkaModel.read y R' = SkaModel.read y R)
    (Sfit : ∀ x y, (∀ L ∈ Ls, FitsS L (C x y)) ↔ (∀ H ∈ Lh, FitsS H x) ∧ (∀ T ∈ Lt, FitsS T y))
    (Srun : ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st' : σ) (t : Trace)
      (R : Map (Option Noun)) (x y : Noun), (∀ H ∈ Lh, HoldsN H.ned R x) → (∀ T ∈ Lt, HoldsN T.ned R y) →
      ∃ R', Runs lib O c gul st' t Ps R R' ∧ (∀ L ∈ Ls, HoldsN L.ned R' (C x y)) ∧
        ∀ y, (∀ L ∈ Ls, ¬ NMem L.ned y) → SkaModel.read y R' = SkaModel.read y R) :
    FrontSG (Map := Map) (consWit Qp Qq) Need.none lo0 lo4 Ms (Pc ++ Fp ++ Fq ++ Ps) Ls := by
  -- the witnesses are apart from both parts' result needs
  have dpA : ∀ s vp dp wp, Qp s vp dp wp → ∀ r, NMem dp r → ∀ F ∈ Lp ++ Lq, ¬ NMem F.ned r := by
    intro s vp dp wp qp r hr F hF hm
    rcases List.mem_append.mp hF with hF | hF
    · exact FP.dis s vp dp wp qp r hr F hF hm
    · have := (FQ.loc F hF r hm).1; have := (hdp s vp dp wp r qp hr).1; omega
  have dqA : ∀ s vq dq wq, Qq s vq dq wq → ∀ r, NMem dq r → ∀ F ∈ Lp ++ Lq, ¬ NMem F.ned r := by
    intro s vq dq wq qq r hr F hF hm
    have b := hdq s vq dq wq r qq hr
    rcases List.mem_append.mp hF with hF | hF
    · obtain ⟨H, hH, hmH⟩ := (FP.loc F hF r hm).2 (by omega)
      have := (hLh H hH r hmH).1; omega
    · exact FQ.dis s vq dq wq qq r hr F hF hm
  refine ⟨fun M hMm r hr => ?_, fun s v d w hq r hd M hMm hm => ?_, fun s v d w hq fit M hMm => ?_, ?_⟩
  · -- loc
    rcases hM M hMm r hr with ⟨F, hF, hmF⟩ | ⟨a, b⟩
    · rcases List.mem_append.mp hF with hF | hF
      · obtain ⟨l1, l2⟩ := FP.loc F hF r hmF
        refine ⟨by omega, fun h => ?_⟩
        obtain ⟨H, hH, hmH⟩ := l2 (by omega)
        exact (hLh H hH r hmH).2 h
      · obtain ⟨l1, l2⟩ := FQ.loc F hF r hmF
        refine ⟨by omega, fun h => ?_⟩
        obtain ⟨T, hT, hmT⟩ := l2 (by omega)
        exact (hLt T hT r hmT).2 h
    · exact ⟨b, fun h => by omega⟩
  · -- dis
    obtain ⟨vp, vq, dp, wp, dq, wq, qp, qq, rfl, rfl, rfl⟩ := hq
    rcases hM M hMm r hm with ⟨F, hF, hmF⟩ | ⟨a, b⟩
    · rcases hd with hd | hd
      · exact dpA s vp dp wp qp r hd F hF hmF
      · exact dqA s vq dq wq qq r hd F hF hmF
    · rcases hd with hd | hd
      · have := (hdp s vp dp wp r qp hd).2; omega
      · have := (hdq s vq dq wq r qq hd).2; omega
  · -- fit
    obtain ⟨vp, vq, dp, wp, dq, wq, qp, qq, rfl, rfl, rfl⟩ := hq
    obtain ⟨fh, ft⟩ := (Sfit vp vq).mp fit
    exact (Cfit s).mpr ⟨FP.fit s vp dp wp qp fh, FQ.fit s vq dq wq qq ft⟩ M hMm
  · -- run
    intro lib σ O c gul st t R s v d w hq hMs hd hE
    obtain ⟨vp, vq, dp, wp, dq, wq, qp, qq, rfl, rfl, rfl⟩ := hq
    have hd0p : HoldsN dp R wp := hd.1
    have hd0q : HoldsN dq R wq := hd.2
    have fM : ∀ M ∈ Ms, FitsS M s := fun M hM => ce_holdsS_fits (hMs M hM)
    obtain ⟨fLp, fLq⟩ := (Cfit s).mp fM
    obtain ⟨R1, r1, h1, k1⟩ := Crun lib σ O c gul st t R s (fun M hM => (hMs M hM).1)
    have hLp1 : ∀ F ∈ Lp, HoldsS F R1 s := fun F hF => ⟨h1 F (List.mem_append_left _ hF), (fLp F hF).2⟩
    have hLq1 : ∀ F ∈ Lq, HoldsS F R1 s := fun F hF => ⟨h1 F (List.mem_append_right _ hF), (fLq F hF).2⟩
    have d1p : HoldsN dp R1 wp := HoldsN.agree dp (fun x hx => k1 x (dpA s vp dp wp qp x hx)) hd0p
    have d1q : HoldsN dq R1 wq := HoldsN.agree dq (fun x hx => k1 x (dqA s vq dq wq qq x hx)) hd0q
    -- after `Fp`: `q`'s result needs and witness kept
    have afterP : (∀ H ∈ Lh, FitsS H vp) → ∃ R2, Runs lib O c gul st t Fp R1 R2 ∧ (∀ H ∈ Lh, HoldsS H R2 vp) ∧
        (∀ x, (x < lo2 ∨ lo3 ≤ x ∨ NMem dp x) → (∀ H ∈ Lh, ¬ NMem H.ned x) →
          SkaModel.read x R2 = SkaModel.read x R1) ∧ (∀ F ∈ Lq, HoldsS F R2 s) ∧ HoldsN dq R2 wq := fun fh => by
      obtain ⟨R2, r2, h2, k2⟩ := (FP.run lib σ O c gul st t R1 s vp dp wp qp hLp1 d1p trivial).1 fh
      refine ⟨R2, r2, h2, k2, fun F hF => ⟨HoldsN.agree F.ned (fun x hx => k2 x (Or.inl (FQ.loc F hF x hx).1)
        (fun H hH hmH => ?_)) (hLq1 F hF).1, (hLq1 F hF).2⟩, HoldsN.agree dq (fun x hx => k2 x
          (Or.inl (hdq s vq dq wq x qq hx).2) (fun H hH hmH => ?_)) d1q⟩
      · obtain ⟨T, hT, hmT⟩ := (FQ.loc F hF x hx).2 (hLh H hH x hmH).1
        exact hht H hH T hT x hmH hmT
      · have := (hLh H hH x hmH).1; have := (hdq s vq dq wq x qq hx).1; omega
    refine ⟨fun fit => ?_, fun ⟨L, hL, nf⟩ => ?_⟩
    · obtain ⟨fh, ft⟩ := (Sfit vp vq).mp fit
      obtain ⟨R2, r2, h2, k2, hLq2, d2q⟩ := afterP fh
      obtain ⟨R3, r3, h3, k3⟩ := (FQ.run lib σ O c gul st t R2 s vq dq wq qq hLq2 d2q trivial).1 ft
      have hLh3 : ∀ H ∈ Lh, HoldsN H.ned R3 vp := fun H hH => HoldsN.agree H.ned
        (fun x hx => k3 x (Or.inl (hLh H hH x hx).1) (fun T hT hmT => hht H hH T hT x hx hmT)) (h2 H hH).1
      obtain ⟨R4, r4, h4, k4⟩ := Srun lib σ O c gul st t R3 vp vq hLh3 (fun T hT => (h3 T hT).1)
      refine ⟨R4, ((r1.append r2).append r3).append r4, fun L hL => ⟨h4 L hL, (fit L hL).2⟩,
        fun x hx hnx => ?_⟩
      -- `x` below the start, from the end, or the witness's
      have nLt : ∀ T ∈ Lt, ¬ NMem T.ned x := fun T hT hmT => by
        obtain ⟨b1, b2⟩ := hLt T hT x hmT
        rcases hx with hx | hx | hx | hx
        · obtain ⟨L, hL, hmL⟩ := b2 hx; exact hnx L hL hmL
        · omega
        · have := (hdp s vp dp wp x qp hx).1; omega
        · have := (hdq s vq dq wq x qq hx).1; omega
      have nLh : ∀ H ∈ Lh, ¬ NMem H.ned x := fun H hH hmH => by
        obtain ⟨b1, b2⟩ := hLh H hH x hmH
        rcases hx with hx | hx | hx | hx
        · obtain ⟨L, hL, hmL⟩ := b2 hx; exact hnx L hL hmL
        · omega
        · have := (hdp s vp dp wp x qp hx).1; omega
        · have := (hdq s vq dq wq x qq hx).1; omega
      have nF : ∀ F ∈ Lp ++ Lq, ¬ NMem F.ned x := fun F hF hmF => by
        rcases hx with hx | hx | hx | hx
        · rcases List.mem_append.mp hF with hF' | hF'
          · obtain ⟨H, hH, hmH⟩ := (FP.loc F hF' x hmF).2 (by omega)
            exact nLh H hH hmH
          · obtain ⟨T, hT, hmT⟩ := (FQ.loc F hF' x hmF).2 (by omega)
            exact nLt T hT hmT
        · rcases List.mem_append.mp hF with hF' | hF'
          · have := (FP.loc F hF' x hmF).1; omega
          · have := (FQ.loc F hF' x hmF).1; omega
        · exact dpA s vp dp wp qp x hx F hF hmF
        · exact dqA s vq dq wq qq x hx F hF hmF
      have c3 : x < lo1 ∨ lo2 ≤ x ∨ NMem dq x := by
        rcases hx with hx | hx | hx | hx
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inl (hdp s vp dp wp x qp hx).1)
        · exact Or.inr (Or.inr hx)
      have c2 : x < lo2 ∨ lo3 ≤ x ∨ NMem dp x := by
        rcases hx with hx | hx | hx | hx
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr hx)
        · exact Or.inl (hdq s vq dq wq x qq hx).2
      rw [k4 x hnx, k3 x c3 nLt, k2 x c2 nLh, k1 x nF]
    · have nfit : ¬ ((∀ H ∈ Lh, FitsS H vp) ∧ (∀ T ∈ Lt, FitsS T vq)) := fun h => nf ((Sfit vp vq).mpr h L hL)
      by_cases ex : ∃ H ∈ Lh, ¬ FitsS H vp
      · exact Crashes.append_left (Crashes.append_left (Crashes.append_right r1
          ((FP.run lib σ O c gul st t R1 s vp dp wp qp hLp1 d1p trivial).2 ex)))
      · have fh : ∀ H ∈ Lh, FitsS H vp := fun H hH => Classical.byContradiction fun n => ex ⟨H, hH, n⟩
        have et : ∃ T ∈ Lt, ¬ FitsS T vq := Classical.byContradiction fun ne => nfit ⟨fh, fun T hT =>
          Classical.byContradiction fun n => ne ⟨T, hT, n⟩⟩
        obtain ⟨R2, r2, h2, k2, hLq2, d2q⟩ := afterP fh
        exact Crashes.append_left (Crashes.append_right (r1.append r2)
          ((FQ.run lib σ O c gul st t R2 s vq dq wq qq hLq2 d2q trivial).2 et))

end Comp
end SkaModel
end Formalization
