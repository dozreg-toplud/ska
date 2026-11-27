import lemmas.Ska.CompGenConsF

/-!
# The cons of two leaves: the fill chain at one label, the root, the fronts

README Gaps 12.39, item 11.  At one label the ops of `[[0 a] [0 b]]` are the
copy's `Pc` (the merged needs `Ms` held by the subject to the firsts `Fs` and
the seconds `Ts`), in front of the split's `Ps` (the goal's needs `Es` for
`[x y]` from the head halves `Hs` at `x` and the tail halves `Ts'` at `y`);
`Fs` are `+from` of `Hs` at `a`, `Ts` of `Ts'` at `b`.

* `frontLG_cons00`: the chain as a front (`FrontLG` with `pureWit`).
* `goalSemD_cons00`: the chain at the root, through the two blocks.
* `frontsG_cons00`: `FrontsG` of the cons of two leaves.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **Needs moved by `+from` at one axis**: fits, holds and registers. -/
theorem ch_from_at {ax : Nat} {ps : List (Sure S × Sure S)} (hp : ∀ p ∈ ps, fromSure ax p.1 = some p.2)
    {s x : Noun} (hs : slot? ax s = some x) :
    ((∀ F ∈ ps.map Prod.snd, FitsS F s) ↔ (∀ H ∈ ps.map Prod.fst, FitsS H x)) ∧
    (∀ R : Map (Option Noun), (∀ F ∈ ps.map Prod.snd, HoldsS F R s) → ∀ H ∈ ps.map Prod.fst, HoldsS H R x) ∧
    (∀ y, (∃ F ∈ ps.map Prod.snd, NMem F.ned y) → ∃ H ∈ ps.map Prod.fst, NMem H.ned y) := by
  refine ⟨⟨fun h H hH => ?_, fun h F hF => ?_⟩, fun R h H hH => ?_, fun y ⟨F, hF, hm⟩ => ?_⟩
  · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hH
    obtain ⟨q, hq, fq⟩ := fromSure_fits (hp p hp') s (h p.2 (List.mem_map_of_mem hp'))
    rw [hs] at hq; cases hq; exact fq
  · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hF
    exact (fromSure_spec (Map := Map) (hp p hp')).2.2.1 s x hs (h p.1 (List.mem_map_of_mem hp'))
  · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hH
    obtain ⟨q, hq, hq'⟩ := (fromSure_spec (Map := Map) (hp p hp')).2.1 R s (h p.2 (List.mem_map_of_mem hp'))
    rw [hs] at hq; cases hq; exact hq'
  · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hF
    exact ⟨p.1, List.mem_map_of_mem hp', (fromSure_spec (Map := Map) (hp p hp')).2.2.2 y hm⟩

theorem ch_exists_not {Ls : List (Sure S)} {s : Noun} (h : ¬ ∀ M ∈ Ls, FitsS M s) : ∃ M ∈ Ls, ¬ FitsS M s :=
  Classical.byContradiction fun hc => h fun M hM => Classical.byContradiction fun nM => hc ⟨M, hM, nM⟩

theorem ch_pure_cons {a b : Nat} {s v : Noun} (h : pureEval (Nomm.cons (Nomm.n0 a) (Nomm.n0 b)) s = some v) :
    ∃ x y, slot? a s = some x ∧ slot? b s = some y ∧ v = C x y := by
  simp only [pureEval] at h
  cases hx : slot? a s with
  | none => rw [hx] at h; simp at h
  | some x =>
    cases hy : slot? b s with
    | none => rw [hx, hy] at h; simp at h
    | some y =>
      rw [hx, hy] at h
      simp only [Option.bind_some, Option.some.injEq] at h
      exact ⟨x, y, rfl, rfl, h.symm⟩

/-- **The fill chain of the cons at one label, as a front.** -/
theorem frontLG_cons00 {a b : Nat} {W : Noun → Noun} {lo0 hi1 : Nat} {Ms Fs Ts Hs Ts' Es : List (Sure S)}
    {Pc Ps : List Pole} {phs pts : List (Sure S × Sure S)}
    (eh1 : phs.map Prod.fst = Hs) (eh2 : phs.map Prod.snd = Fs) (ehf : ∀ p ∈ phs, fromSure a p.1 = some p.2)
    (et1 : pts.map Prod.fst = Ts') (et2 : pts.map Prod.snd = Ts) (etf : ∀ p ∈ pts, fromSure b p.1 = some p.2)
    (Cfit : ∀ z, (∀ M ∈ Ms, FitsS M z) ↔ (∀ F ∈ Fs, FitsS F z) ∧ (∀ T ∈ Ts, FitsS T z))
    (Crun : ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st' : σ) (t : Trace)
      (R : Map (Option Noun)) (z : Noun), (∀ M ∈ Ms, HoldsN M.ned R z) →
      ∃ R', Runs lib O c gul st' t Pc R R' ∧ (∀ F ∈ Fs ++ Ts, HoldsN F.ned R' z) ∧
        ∀ y, (∀ F ∈ Fs ++ Ts, ¬ NMem F.ned y) → SkaModel.read y R' = SkaModel.read y R)
    (Sfit : ∀ x y, (∀ L ∈ Es, FitsS L (C x y)) ↔ (∀ H ∈ Hs, FitsS H x) ∧ (∀ T ∈ Ts', FitsS T y))
    (Srun : ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st' : σ) (t : Trace)
      (R : Map (Option Noun)) (x y : Noun), (∀ H ∈ Hs, HoldsN H.ned R x) → (∀ T ∈ Ts', HoldsN T.ned R y) →
      ∃ R', Runs lib O c gul st' t Ps R R' ∧ (∀ L ∈ Es, HoldsN L.ned R' (C x y)) ∧
        ∀ y, (∀ L ∈ Es, ¬ NMem L.ned y) → SkaModel.read y R' = SkaModel.read y R)
    (hreg : ∀ y, (∃ M ∈ Ms ++ Hs ++ Ts', NMem M.ned y) → (∃ L ∈ Es, NMem L.ned y) ∨ (lo0 ≤ y ∧ y < hi1))
    (hlo : lo0 ≤ hi1) :
    FrontLG (Map := Map) (pureWit (Nomm.cons (Nomm.n0 a) (Nomm.n0 b)) (fun _ => Need.none) W) Need.none lo0 hi1
      Ms (Pc ++ Ps) Es := by
  intro lib σ O c gul st t ned A s0 s v d w hn hq hA
  obtain ⟨hv, rfl, rfl⟩ := hq
  obtain ⟨x, y, hx, hy, rfl⟩ := ch_pure_cons hv
  obtain ⟨FH, HH, MH⟩ := ch_from_at (Map := Map) ehf hx
  obtain ⟨FT, HT, MT⟩ := ch_from_at (Map := Map) etf hy
  rw [eh1, eh2] at FH HH MH
  rw [et1, et2] at FT HT MT
  have fitE : (∀ L ∈ Es, FitsS L (C x y)) ↔ ∀ M ∈ Ms, FitsS M s := by
    rw [Sfit, Cfit, FH, FT]
  refine FillSemL.conv (N2 := ned) (x2 := s0) ?_ (fun R hR => hR.1.1) (fun z hz => ?_)
  · intro R hR
    refine ⟨fun f => ?_, fun ⟨L, hL, nf⟩ => ?_⟩
    · have fM := fitE.mp f
      obtain ⟨R1, r1, h1, k1⟩ := (hA R hR).1 fM
      obtain ⟨R2, r2, h2, k2⟩ := Crun lib σ O c gul st t R1 s (fun M hM => (h1 M hM).1)
      have fFT := (Cfit s).mp fM
      have hH : ∀ H ∈ Hs, HoldsN H.ned R2 x := fun H hH =>
        (HH R2 (fun F hF => ⟨h2 F (List.mem_append_left _ hF), (fFT.1 F hF).2⟩) H hH).1
      have hT : ∀ T ∈ Ts', HoldsN T.ned R2 y := fun T hT =>
        (HT R2 (fun F hF => ⟨h2 F (List.mem_append_right _ hF), (fFT.2 F hF).2⟩) T hT).1
      obtain ⟨R3, r3, h3, k3⟩ := Srun lib σ O c gul st t R2 x y hH hT
      refine ⟨R3, r1.append (r2.append r3), fun L hL => ⟨h3 L hL, (f L hL).2⟩, fun z hz hnE => ?_⟩
      have out : ∀ M ∈ Ms ++ Hs ++ Ts', ¬ NMem M.ned z := fun M hM hm => by
        rcases hreg z ⟨M, hM, hm⟩ with ⟨L, hL, hl⟩ | ⟨h1', h2'⟩
        · exact hnE L hL hl
        · rcases hz with hz | hz
          · have := hn z hz; omega
          · omega
      have outF : ∀ F ∈ Fs ++ Ts, ¬ NMem F.ned z := fun F hF hm => by
        rcases List.mem_append.mp hF with hF | hF
        · obtain ⟨H, hH', hm'⟩ := MH z ⟨F, hF, hm⟩
          exact out H (by simp [hH']) hm'
        · obtain ⟨T, hT', hm'⟩ := MT z ⟨F, hF, hm⟩
          exact out T (by simp [hT']) hm'
      rw [k3 z hnE, k2 z outF, k1 z (hz.imp_right (fun h => by omega)) (fun M hM => out M (by simp [hM]))]
    · obtain ⟨M, hM, nM⟩ := ch_exists_not (fun h => nf (fitE.mpr h L hL))
      exact Crashes.append_left ((hA R hR).2 ⟨M, hM, nM⟩)
  · rcases hz with (hz | hz) | hz
    · exact Or.inl hz
    · exact hz.elim
    · exact hz.elim

/-- **The chain at the root**: a jump into the copy's block runs the copy,
hops to the split's block, runs the split and goes on to `th`. -/
theorem goalSemD_cons00 {a b : Nat} (lib : Lib) {σ : Type} (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ)
    {K : Nat → Prop} {regs : Map (Option Noun)} {t : Trace} {oc os : Nat} {th : Jmp} {w : Noun}
    {Msure Fsure Tsure Hsure Tsure' Lsure : Sure S} {Pc Ps : List Pole}
    (hbc : HoonMap.get c.blocks oc = some ⟨[], Pc, Termin.hop (jmp0 os)⟩)
    (hbs : HoonMap.get c.blocks os = some ⟨[], Ps, Termin.hop th⟩)
    (hf : fromSure a Hsure = some Fsure) (hg : fromSure b Tsure' = some Tsure)
    (Cfit : ∀ z, (∀ M ∈ [Msure], FitsS M z) ↔ (∀ F ∈ [Fsure], FitsS F z) ∧ (∀ T ∈ [Tsure], FitsS T z))
    (Crun : ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st' : σ) (t : Trace)
      (R : Map (Option Noun)) (z : Noun), (∀ M ∈ [Msure], HoldsN M.ned R z) →
      ∃ R', Runs lib O c gul st' t Pc R R' ∧ (∀ F ∈ [Fsure] ++ [Tsure], HoldsN F.ned R' z) ∧
        ∀ y, (∀ F ∈ [Fsure] ++ [Tsure], ¬ NMem F.ned y) → SkaModel.read y R' = SkaModel.read y R)
    (Sfit : ∀ x y, (∀ L ∈ [Lsure], FitsS L (C x y)) ↔ (∀ H ∈ [Hsure], FitsS H x) ∧ (∀ T ∈ [Tsure'], FitsS T y))
    (Srun : ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st' : σ) (t : Trace)
      (R : Map (Option Noun)) (x y : Noun), (∀ H ∈ [Hsure], HoldsN H.ned R x) → (∀ T ∈ [Tsure'], HoldsN T.ned R y) →
      ∃ R', Runs lib O c gul st' t Ps R R' ∧ (∀ L ∈ [Lsure], HoldsN L.ned R' (C x y)) ∧
        ∀ y, (∀ L ∈ [Lsure], ¬ NMem L.ned y) → SkaModel.read y R' = SkaModel.read y R)
    (hK : ∀ y, K y → ¬ NMem Lsure.ned y ∧ ¬ NMem Fsure.ned y ∧ ¬ NMem Tsure.ned y) {s : Noun}
    (hh : HoldsS Msure regs s) :
    GoalSemD lib O c gul st K regs t (jmp0 oc) Lsure th Need.none w
      (pureEval (Nomm.cons (Nomm.n0 a) (Nomm.n0 b)) s) := by
  have fM : FitsS Msure s := fitsS_of_holdsS hh
  obtain ⟨fF, fT⟩ := (Cfit s).mp (fun M hM => by rw [List.mem_singleton.mp hM]; exact fM)
  have fF' := fF Fsure (List.mem_singleton_self _)
  have fT' := fT Tsure (List.mem_singleton_self _)
  obtain ⟨x, hx, fx⟩ := fromSure_fits hf s fF'
  obtain ⟨y, hy, fy⟩ := fromSure_fits hg s fT'
  have ev : pureEval (Nomm.cons (Nomm.n0 a) (Nomm.n0 b)) s = some (C x y) := by
    simp only [pureEval, hx, hy, Option.bind_some]
  have fL : FitsS Lsure (C x y) := (Sfit x y).mpr ⟨fun H hH => by rw [List.mem_singleton.mp hH]; exact fx,
    fun T hT => by rw [List.mem_singleton.mp hT]; exact fy⟩ Lsure (List.mem_singleton_self _)
  rw [ev]
  refine ⟨fun _ => ?_, fun nf => absurd fL nf⟩
  obtain ⟨R2, r2, h2, k2⟩ := Crun lib σ O c gul st t regs s (fun M hM => by rw [List.mem_singleton.mp hM]; exact hh.1)
  have hF2 : HoldsS Fsure R2 s := ⟨h2 Fsure (by simp), fF'.2⟩
  have hT2 : HoldsS Tsure R2 s := ⟨h2 Tsure (by simp), fT'.2⟩
  obtain ⟨x', hx', hH⟩ := (fromSure_spec (Map := Map) hf).2.1 R2 s hF2
  obtain ⟨y', hy', hT⟩ := (fromSure_spec (Map := Map) hg).2.1 R2 s hT2
  rw [hx] at hx'; cases hx'
  rw [hy] at hy'; cases hy'
  obtain ⟨R3, r3, h3, k3⟩ := Srun lib σ O c gul st t R2 x y
    (fun H hH' => by rw [List.mem_singleton.mp hH']; exact hH.1) (fun T hT' => by rw [List.mem_singleton.mp hT']; exact hT.1)
  refine ⟨R3, h3 Lsure (List.mem_singleton_self _), trivial, fun r hr => ?_, ?_⟩
  · obtain ⟨n1, n2, n3⟩ := hK r hr
    rw [k3 r (fun L hL => by rw [List.mem_singleton.mp hL]; exact n1),
      k2 r (fun F hF => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hF
        rcases hF with rfl | rfl
        · exact n2
        · exact n3)]
  · have e1 := r2 [] (Termin.hop (jmp0 os))
    have e2 := r3 [] (Termin.hop th)
    simp only [List.append_nil] at e1 e2
    rw [goJ_jmp0 regs t oc _ hbc, e1, execBlob_hop, goJ_jmp0 R2 t os _ hbs, e2, execBlob_hop]

/-! ## The fronts of the cons of two leaves -/

theorem ch_emitted_ne (g : Gen Map) (b : Blob) {k : Nat} (hk : k ≠ g.bo) :
    HoonMap.get (g.emitted b).blocks k = HoonMap.get g.blocks k := by
  unfold Gen.emitted
  cases g.drop <;> simp [HoonMap.get_put, hk]

theorem ch_pref_uniq {g g' : Gen Map} {P P' : Nat → List Pole} (h : Pref g g' P) (h' : Pref g g' P') {k : Nat}
    {b : Blob} (hb : HoonMap.get g.blocks k = some b) : P k = P' k := by
  have e := (h.get k).symm.trans (h'.get k)
  rw [hb] at e
  simp only [Option.map_some, Option.some.injEq, preBody] at e
  have := congrArg Blob.body e
  simpa using this

theorem ch_regsIn_flatten {α : Type} {P : Nat → Prop} (f : α → List Pole) (ps : List α)
    (h : ∀ p ∈ ps, RegsIn P (f p)) : RegsIn P (ps.map f).flatten := by
  intro q hq x hx
  obtain ⟨l, hl, hql⟩ := List.mem_flatten.mp hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
  exact h p hp q hql x hx

/-- **`FrontsG` of the cons of two leaves**: at every goal label the ops in
front are the copy's and the split's there, and they fill the goal's needs
at that label (`frontLG_cons00`). -/
theorem frontsG_cons00 {L : Lazy S} {th : Jmp} {a b : Nat} {g0 g1 : Gen Map} {nex : NextL S}
    {hed tel hed' tel' : Lazy S} {gS : Gen Map}
    (CA : ConsAt L th a b g0 g1 nex hed tel hed' tel' gS) (G : GoalG (Map := Map) L th g0)
    (hec : ∀ e ∈ entries L, ∀ r, NMem e.2.sure.ned r → HoonMap.get g0.cond r = Option.none) (hcb : CondBelow g0)
    (CR : CopyRunAt (gS.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩) g1 ((gS.bo, hed') :: entries hed')
      ((gS.bo, tel') :: entries tel') ((gS.bo, nex.laz) :: entries nex.laz))
    (CP : CopyPreAt (gS.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩) ((gS.bo, hed') :: entries hed')
      ((gS.bo, tel') :: entries tel'))
    (W : Noun → Noun) :
    FrontsG (Map := Map) (pureWit (Nomm.cons (Nomm.n0 a) (Nomm.n0 b)) (fun _ => Need.none) W) false g0 g1 L nex := by
  have reE : (g0.emitted ⟨[], [], Termin.hop th⟩).re = g0.re := rfl
  have reC : (gS.emitted ⟨[], [], Termin.hop (jmp0 g0.bo)⟩).re = gS.re := rfl
  have rS := CA.reS
  have rC := CA.reC
  have hdj : ((g0.bo, L) :: entries L).Pairwise
      fun e e' => e.1 = e'.1 → ∀ r, NMem e.2.sure.ned r → ¬ NMem e'.2.sure.ned r := by
    refine List.pairwise_cons.mpr ⟨fun e' he' heq => ?_, G.labDisj⟩
    have := (G.lab e' he').2.1
    simp only at heq; omega
  have hreg0 : ∀ e ∈ (g0.bo, L) :: entries L, Distinct e.2.sure.ned ∧
      ∀ y, NMem e.2.sure.ned y → y < (g0.emitted ⟨[], [], Termin.hop th⟩).re := by
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨G.dist, G.sregs⟩
    · exact G.eregs e he
  obtain ⟨PS, PPS, -, SA⟩ := SplitOKL.runAt CA.sp.toL hdj hreg0
  obtain ⟨P0, PP0, -, A0⟩ := CA.sp
  obtain ⟨PC, PPC, -, CA'⟩ := CR
  have fromRegs : ∀ (ax : Nat) (ps : List (Sure S × Sure S)), (∀ p ∈ ps, fromSure ax p.1 = some p.2) →
      ∀ y, (∃ F ∈ ps.map Prod.snd, NMem F.ned y) → ∃ H ∈ ps.map Prod.fst, NMem H.ned y := by
    intro ax ps hp y ⟨F, hF, hm⟩
    obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hF
    exact ⟨p.1, List.mem_map_of_mem hp', (fromSure_spec (Map := Map) (hp p hp')).2.2.2 y hm⟩
  intro k hk
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
  obtain ⟨-, hlt, B0, th0, hb0⟩ := G.lab e he
  have hk0 : ((g0.bo, L) : Nat × Lazy S).1 ≠ e.1 := by simp only; omega
  have hkS : ((gS.bo, L) : Nat × Lazy S).1 ≠ e.1 := by simp only; rw [CA.boS]; omega
  have eEs : atL ((g0.bo, L) :: entries L) e.1 = atL (entries L) e.1 := atL_cons_ne hk0
  have eHs : atL ((g0.bo, hed) :: entries hed) e.1 = atL (entries hed) e.1 := atL_cons_ne hk0
  have eTs : atL ((g0.bo, tel) :: entries tel) e.1 = atL (entries tel) e.1 := atL_cons_ne hk0
  have eFs : atL ((gS.bo, hed') :: entries hed') e.1 = atL (entries hed') e.1 := atL_cons_ne hkS
  have eGs : atL ((gS.bo, tel') :: entries tel') e.1 = atL (entries tel') e.1 := atL_cons_ne hkS
  have eMs : atL ((gS.bo, nex.laz) :: entries nex.laz) e.1 = atL (entries nex.laz) e.1 := atL_cons_ne hkS
  obtain ⟨Sfit, Sreg1, Sreg2, Srun⟩ := SA e.1
  rw [eEs, eHs, eTs] at Sfit Srun
  rw [eEs, eHs] at Sreg1
  rw [eEs, eTs] at Sreg2
  have C1 := CA' e.1 (CP e.1).1 (CP e.1).2
  rw [eFs, eGs, eMs] at C1
  obtain ⟨Cfit, Creg, -, CRg, Crun⟩ := C1
  obtain ⟨phs, ph1, ph2, ph3⟩ := FromEnt.pairsAt (fromL_ent a hed hed' CA.f2) e.1
  obtain ⟨pts, pt1, pt2, pt3⟩ := FromEnt.pairsAt (fromL_ent b tel tel' CA.f1) e.1
  -- the registers
  have good : ∀ x, ((∃ L' ∈ atL (entries L) e.1, NMem L'.ned x) ∨ (g0.re ≤ x ∧ x < g1.re)) →
      x < g1.re ∧ HoonMap.get g0.cond x = Option.none := by
    intro x hx
    rcases hx with ⟨L', hL', hm⟩ | ⟨h1, h2⟩
    · obtain ⟨e', he', -, es'⟩ := mem_atL hL'
      rw [← es'] at hm
      have := (G.eregs e' he').2 x hm
      exact ⟨by omega, hec e' he' x hm⟩
    · exact ⟨h2, condBelow_none hcb h1⟩
  have hsplitR : ∀ y, ((∃ H ∈ atL (entries hed) e.1, NMem H.ned y) ∨ (∃ T ∈ atL (entries tel) e.1, NMem T.ned y)) →
      (∃ L' ∈ atL (entries L) e.1, NMem L'.ned y) ∨ (g0.re ≤ y ∧ y < g1.re) := by
    intro y hy
    rcases hy with ⟨H, hH, hm⟩ | ⟨T, hT, hm⟩
    · rcases Sreg1 H hH y hm with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨by rw [reE] at h1; exact h1, by omega⟩
    · rcases Sreg2 T hT y hm with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨by rw [reE] at h1; exact h1, by omega⟩
  have hcopyR : ∀ y, (∃ F ∈ atL (entries hed') e.1 ++ atL (entries tel') e.1, NMem F.ned y) →
      (∃ L' ∈ atL (entries L) e.1, NMem L'.ned y) ∨ (g0.re ≤ y ∧ y < g1.re) := by
    intro y ⟨F, hF, hm⟩
    rcases List.mem_append.mp hF with hF | hF
    · obtain ⟨H, hH, hm'⟩ := fromRegs a phs ph3 y ⟨F, by rw [ph2]; exact hF, hm⟩
      exact hsplitR y (Or.inl ⟨H, by rw [← ph1]; exact hH, hm'⟩)
    · obtain ⟨T, hT, hm'⟩ := fromRegs b pts pt3 y ⟨F, by rw [pt2]; exact hF, hm⟩
      exact hsplitR y (Or.inr ⟨T, by rw [← pt1]; exact hT, hm'⟩)
  have hregC : ∀ y, (∃ M ∈ atL (entries nex.laz) e.1 ++ atL (entries hed) e.1 ++ atL (entries tel) e.1,
      NMem M.ned y) → (∃ L' ∈ atL (entries L) e.1, NMem L'.ned y) ∨ (g0.re ≤ y ∧ y < g1.re) := by
    intro y ⟨M, hM, hm⟩
    rcases List.mem_append.mp hM with hM | hM
    · rcases List.mem_append.mp hM with hM | hM
      · rcases (Creg M hM).2 y hm with h | ⟨h1, h2⟩
        · exact hcopyR y h
        · exact Or.inr ⟨by rw [reC] at h1; omega, h2⟩
      · exact hsplitR y (Or.inl ⟨M, hM, hm⟩)
    · exact hsplitR y (Or.inr ⟨M, hM, hm⟩)
  -- the split's ops at `e.1` are those of `CA.sp`
  have bE : HoonMap.get (g0.emitted ⟨[], [], Termin.hop th⟩).blocks e.1 = some ⟨[], B0, Termin.hop th0⟩ := by
    rw [ch_emitted_ne _ _ (by omega)]; exact hb0
  have eP : PS e.1 = P0 e.1 := ch_pref_uniq PPS PP0 bE
  have regsS : RegsIn (fun x => x < g1.re ∧ HoonMap.get g0.cond x = Option.none) (PS e.1) := by
    rw [eP]
    obtain ⟨ps, eps, pE, -, -, sP, -⟩ := A0 e.1
    rw [eps]
    refine ch_regsIn_flatten _ ps (fun p hp => ?_)
    have hp1 : p.1 ∈ atL (entries L) e.1 := by
      rw [← eEs]; exact pE.mem_iff.mp (List.mem_map_of_mem hp)
    obtain ⟨e', he', -, es'⟩ := mem_atL hp1
    have ra := (sP p hp).ra (fun x => HoonMap.get g0.cond x = Option.none)
      (fun r hr => by rw [← es'] at hr; exact hec e' he' r hr) (fun r hr => condBelow_none hcb hr)
    have rb := (sP p hp).rb (fun r hr => by rw [← es'] at hr; exact (G.eregs e' he').2 r hr)
    intro q hq x hx
    exact ⟨by have := rb q hq x hx; omega, ra q hq x hx⟩
  have regsC : RegsIn (fun x => x < g1.re ∧ HoonMap.get g0.cond x = Option.none) (PC e.1) := by
    refine RegsIn.mono (fun x hx => good x ?_) CRg
    rcases hx with h | ⟨h1, h2⟩
    · exact hcopyR x h
    · exact Or.inr ⟨by rw [reC] at h1; omega, h2⟩
  refine Or.inl ⟨PC e.1 ++ PS e.1, fun B fin hb => ?_, fun cf hcf => ?_⟩
  · rw [PPC.get, ch_emitted_ne _ _ (by rw [CA.boS]; omega), PPS.get, ch_emitted_ne _ _ (by omega), hb]
    simp [preBody, List.append_assoc]
  · have ren : (PC e.1 ++ PS e.1).map (renPole (unproxy cf)) = PC e.1 ++ PS e.1 :=
      renOps_fix (P := fun x => x < g1.re ∧ HoonMap.get g0.cond x = Option.none)
        (fun x hx => unproxy_none (by rw [hcf x hx.1, CA.cond]; exact hx.2)) (regsC.append regsS)
    rw [ren]
    exact frontLG_cons00 ph1 ph2 ph3 pt1 pt2 pt3 Cfit Crun Sfit Srun hregC (Nat.le_trans rS rC)

end Comp
end SkaModel
end Formalization
