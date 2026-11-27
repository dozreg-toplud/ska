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
