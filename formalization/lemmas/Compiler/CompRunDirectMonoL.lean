import lemmas.Compiler.CompRunDirectMono

/-!
# `+mono-try-call` on a cell and on `%both`, one push at a time

README Gaps 19.  The branches `mtcPAr0` (a cell `[h t]`) and `[11 mtcBOh
mtcBOr0]` (`%both`) of the trap `mtcLoop` (`CompRunDirectMono.lean`), each a
chain of five `=^` pushes and a last `+emit`, one lemma per push: the subject
after `k` pushes is `mtcS l …` (the pushed atoms `l`, last first, on the trap
subject `mtcT`), and step `i` is `nock S_i mtcPAr<i> = nock S_(i+1)
mtcPAr<i+1>` with `comp.door` generalized and `genNoun` folded:

* pushes 0 and 1: `+re` (`comp_re'`);
* push 2: the run on the tail, at `[252 +.ned] [30 r-t]` (hypothesis on the
  run of `mtcLoop`, or its failure);
* push 3: the run on the head, at `[252 -.ned] [30 r-h] [6 o-t]`;
* push 4: the `+emit` of the split block (`%both`: after `?<  =(r r.ned)`);
* the last part: the `+emit` of `[%clq r ~^o-split ~^fail]`.

Then `mtc_pair` and `mtc_both` (the trap on a cell and on `%both`, from
`MtcAt` of the parts), `mtc_loop` (every need, by induction) and
`mtc_gate` (the gate on `[ned opt [sub pes]]` is `monoTryCall`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

variable {ctx : Noun} (x : GenRest)

/-- The subject after the pushes `l` (the last first) on the trap subject. -/
noncomputable def mtcS (l : List Nat) (ned : Need) (r o fail : Nat) (Z : Noun) (g : Gen (TreapMap mugF))
    (x : GenRest) (ctx : Noun) : Noun :=
  l.foldr (fun a s => C (A a) s) (mtcT ned r o fail Z g x ctx)

/-- The state after one `+re`. -/
abbrev mtcReG (g : Gen (TreapMap mugF)) : Gen (TreapMap mugF) := { g with re := g.re + 1 }

/-! ## The cell branch -/

theorem mtcPA_0 (ned : Need) (r o fail : Nat) (Z : Noun) (g : Gen (TreapMap mugF)) :
    nock (mtcT ned r o fail Z g x ctx) mtcPAr0 = nock (mtcS [g.re] ned r o fail Z (mtcReG g) x ctx) mtcPAr1 := by
  have hD := comp_re_at
  have hre := comp_re' ctx x g
  conv => { lhs; arg 2; unfold mtcPAr0 }
  simp only [mtcS, mtcT, compCore, List.foldr, mtcReG] at hre ⊢
  generalize comp.door = Dr at hD hre ⊢
  simp [nock_exec, mtcPAv0, hD, hre]

theorem mtcPA_1 (ned : Need) (rt r o fail : Nat) (Z : Noun) (g : Gen (TreapMap mugF)) :
    nock (mtcS [rt] ned r o fail Z g x ctx) mtcPAr1
      = nock (mtcS [g.re, rt] ned r o fail Z (mtcReG g) x ctx) mtcPAr2 := by
  have hD := comp_re_at
  have hre := comp_re' ctx x g
  conv => { lhs; arg 2; unfold mtcPAr1 }
  simp only [mtcS, mtcT, compCore, List.foldr, mtcReG] at hre ⊢
  generalize comp.door = Dr at hD hre ⊢
  simp [nock_exec, mtcPAv1, hD, hre]

theorem mtcPA_2 (h t : Need) (rh rt r o fail : Nat) (Z : Noun) (g g' : Gen (TreapMap mugF)) (ot : Nat)
    (hrun : nock (mtcT t rt o fail Z g x ctx) mtcLoop = some (C (A ot) (genNoun g' x))) :
    nock (mtcS [rh, rt] (Need.pair h t) r o fail Z g x ctx) mtcPAr2
      = nock (mtcS [ot, rh, rt] (Need.pair h t) r o fail Z g' x ctx) mtcPAr3 := by
  conv => { lhs; arg 2; unfold mtcPAr2 }
  simp only [mtcS, mtcT, compCore, List.foldr] at hrun ⊢
  generalize comp.door = Dr at hrun ⊢
  simp [nock_exec, mtcPAv2, Need.toNoun, hrun]

theorem mtcPA_2n (h t : Need) (rh rt r o fail : Nat) (Z : Noun) (g : Gen (TreapMap mugF))
    (hrun : nock (mtcT t rt o fail Z g x ctx) mtcLoop = none) :
    nock (mtcS [rh, rt] (Need.pair h t) r o fail Z g x ctx) mtcPAr2 = none := by
  conv => { lhs; arg 2; unfold mtcPAr2 }
  simp only [mtcS, mtcT, compCore, List.foldr] at hrun ⊢
  generalize comp.door = Dr at hrun ⊢
  simp [nock_exec, mtcPAv2, Need.toNoun, hrun]

theorem mtcPA_3 (h t : Need) (ot rh rt r o fail : Nat) (Z : Noun) (g g' : Gen (TreapMap mugF)) (oh : Nat)
    (hrun : nock (mtcT h rh ot fail Z g x ctx) mtcLoop = some (C (A oh) (genNoun g' x))) :
    nock (mtcS [ot, rh, rt] (Need.pair h t) r o fail Z g x ctx) mtcPAr3
      = nock (mtcS [oh, ot, rh, rt] (Need.pair h t) r o fail Z g' x ctx) mtcPAr4 := by
  conv => { lhs; arg 2; unfold mtcPAr3 }
  simp only [mtcS, mtcT, compCore, List.foldr] at hrun ⊢
  generalize comp.door = Dr at hrun ⊢
  simp [nock_exec, mtcPAv3, Need.toNoun, hrun]

theorem mtcPA_3n (h t : Need) (ot rh rt r o fail : Nat) (Z : Noun) (g : Gen (TreapMap mugF))
    (hrun : nock (mtcT h rh ot fail Z g x ctx) mtcLoop = none) :
    nock (mtcS [ot, rh, rt] (Need.pair h t) r o fail Z g x ctx) mtcPAr3 = none := by
  conv => { lhs; arg 2; unfold mtcPAr3 }
  simp only [mtcS, mtcT, compCore, List.foldr] at hrun ⊢
  generalize comp.door = Dr at hrun ⊢
  simp [nock_exec, mtcPAv3, Need.toNoun, hrun]

/-- The split block of a cell. -/
def mtcSplit (r rh rt oh : Nat) : Blob := ⟨[], [Pole.hed r rh, Pole.tal r rt], Termin.hop (jmp0 oh)⟩

/-- The test block. -/
def mtcClq (r os fail : Nat) : Blob := ⟨[], [], Termin.clq r (jmp0 os) (jmp0 fail)⟩

theorem mtcPA_4 (hc : CompIn ctx) (ned : Need) (oh ot rh rt r o fail : Nat) (Z : Noun)
    (g : Gen (TreapMap mugF)) :
    nock (mtcS [oh, ot, rh, rt] ned r o fail Z g x ctx) mtcPAr4
      = nock (mtcS [g.bo, oh, ot, rh, rt] ned r o fail Z (cfEmitG (mtcSplit r rh rt oh) g) x ctx) mtcPAL := by
  have hD := comp_emit_at
  have he := cf_emit (x := x) hc g (mtcSplit r rh rt oh)
  rw [mtcSplit, mtc_blob_split] at he
  conv => { lhs; arg 2; unfold mtcPAr4 }
  simp only [mtcS, mtcT, compCore, List.foldr, mtcSplit] at he ⊢
  generalize comp.door = Dr at hD he ⊢
  simp [nock_exec, mtcPAv4, hD, comp_emit_arm, he]

theorem mtcPA_L (hc : CompIn ctx) (ned : Need) (os oh ot rh rt r o fail : Nat) (Z : Noun)
    (g : Gen (TreapMap mugF)) :
    nock (mtcS [os, oh, ot, rh, rt] ned r o fail Z g x ctx) mtcPAL
      = some (C (A g.bo) (genNoun (cfEmitG (mtcClq r os fail) g) x)) := by
  have hD := comp_emit_at
  have he := cf_emit (x := x) hc g (mtcClq r os fail)
  rw [mtcClq, mtc_blob_clq] at he
  conv => { lhs; arg 2; unfold mtcPAL }
  simp only [mtcS, mtcT, compCore, List.foldr, mtcClq] at he ⊢
  generalize comp.door = Dr at hD he ⊢
  simp [nock_exec, hD, comp_emit_arm, he]

/-! ## The `%both` branch -/

theorem mtcBO_0 (ned : Need) (r o fail : Nat) (Z : Noun) (g : Gen (TreapMap mugF)) :
    nock (mtcT ned r o fail Z g x ctx) mtcBOr0 = nock (mtcS [g.re] ned r o fail Z (mtcReG g) x ctx) mtcBOr1 := by
  have hD := comp_re_at
  have hre := comp_re' ctx x g
  conv => { lhs; arg 2; unfold mtcBOr0 }
  simp only [mtcS, mtcT, compCore, List.foldr, mtcReG] at hre ⊢
  generalize comp.door = Dr at hD hre ⊢
  simp [nock_exec, mtcBOv0, hD, hre]

theorem mtcBO_1 (ned : Need) (rt r o fail : Nat) (Z : Noun) (g : Gen (TreapMap mugF)) :
    nock (mtcS [rt] ned r o fail Z g x ctx) mtcBOr1
      = nock (mtcS [g.re, rt] ned r o fail Z (mtcReG g) x ctx) mtcBOr2 := by
  have hD := comp_re_at
  have hre := comp_re' ctx x g
  conv => { lhs; arg 2; unfold mtcBOr1 }
  simp only [mtcS, mtcT, compCore, List.foldr, mtcReG] at hre ⊢
  generalize comp.door = Dr at hD hre ⊢
  simp [nock_exec, mtcBOv1, hD, hre]

theorem mtcBO_2 (rn : Nat) (h t : Need) (rh rt r o fail : Nat) (Z : Noun) (g g' : Gen (TreapMap mugF)) (ot : Nat)
    (hrun : nock (mtcT t rt o fail Z g x ctx) mtcLoop = some (C (A ot) (genNoun g' x))) :
    nock (mtcS [rh, rt] (Need.both rn h t) r o fail Z g x ctx) mtcBOr2
      = nock (mtcS [ot, rh, rt] (Need.both rn h t) r o fail Z g' x ctx) mtcBOr3 := by
  conv => { lhs; arg 2; unfold mtcBOr2 }
  simp only [mtcS, mtcT, compCore, List.foldr] at hrun ⊢
  generalize comp.door = Dr at hrun ⊢
  simp [nock_exec, mtcBOv2, Need.toNoun, hrun]

theorem mtcBO_2n (rn : Nat) (h t : Need) (rh rt r o fail : Nat) (Z : Noun) (g : Gen (TreapMap mugF))
    (hrun : nock (mtcT t rt o fail Z g x ctx) mtcLoop = none) :
    nock (mtcS [rh, rt] (Need.both rn h t) r o fail Z g x ctx) mtcBOr2 = none := by
  conv => { lhs; arg 2; unfold mtcBOr2 }
  simp only [mtcS, mtcT, compCore, List.foldr] at hrun ⊢
  generalize comp.door = Dr at hrun ⊢
  simp [nock_exec, mtcBOv2, Need.toNoun, hrun]

theorem mtcBO_3 (rn : Nat) (h t : Need) (ot rh rt r o fail : Nat) (Z : Noun) (g g' : Gen (TreapMap mugF))
    (oh : Nat) (hrun : nock (mtcT h rh ot fail Z g x ctx) mtcLoop = some (C (A oh) (genNoun g' x))) :
    nock (mtcS [ot, rh, rt] (Need.both rn h t) r o fail Z g x ctx) mtcBOr3
      = nock (mtcS [oh, ot, rh, rt] (Need.both rn h t) r o fail Z g' x ctx) mtcBOr4 := by
  conv => { lhs; arg 2; unfold mtcBOr3 }
  simp only [mtcS, mtcT, compCore, List.foldr] at hrun ⊢
  generalize comp.door = Dr at hrun ⊢
  simp [nock_exec, mtcBOv3, Need.toNoun, hrun]

theorem mtcBO_3n (rn : Nat) (h t : Need) (ot rh rt r o fail : Nat) (Z : Noun) (g : Gen (TreapMap mugF))
    (hrun : nock (mtcT h rh ot fail Z g x ctx) mtcLoop = none) :
    nock (mtcS [ot, rh, rt] (Need.both rn h t) r o fail Z g x ctx) mtcBOr3 = none := by
  conv => { lhs; arg 2; unfold mtcBOr3 }
  simp only [mtcS, mtcT, compCore, List.foldr] at hrun ⊢
  generalize comp.door = Dr at hrun ⊢
  simp [nock_exec, mtcBOv3, Need.toNoun, hrun]

/-- The split block of `%both`. -/
def mtcSplit3 (r rh rt rn oh : Nat) : Blob :=
  ⟨[], [Pole.hed r rh, Pole.tal r rt, Pole.mov r rn], Termin.hop (jmp0 oh)⟩

theorem mtcBO_4 (hc : CompIn ctx) (rn : Nat) (h t : Need) (oh ot rh rt r o fail : Nat) (Z : Noun)
    (g : Gen (TreapMap mugF)) :
    nock (mtcS [oh, ot, rh, rt] (Need.both rn h t) r o fail Z g x ctx) mtcBOr4
      = if r = rn then none else
        nock (mtcS [g.bo, oh, ot, rh, rt] (Need.both rn h t) r o fail Z
          (cfEmitG (mtcSplit3 r rh rt rn oh) g) x ctx) mtcBOL := by
  have hD := comp_emit_at
  have he := cf_emit (x := x) hc g (mtcSplit3 r rh rt rn oh)
  rw [mtcSplit3, mtc_blob_split3] at he
  conv => { lhs; arg 2; unfold mtcBOr4 }
  simp only [mtcS, mtcT, compCore, List.foldr, mtcSplit3] at he ⊢
  generalize comp.door = Dr at hD he ⊢
  by_cases hr : r = rn
  · subst hr
    simp [nock_exec, mtcBOv4, Need.toNoun, eqCode]
  · have hr' : rn ≠ r := Ne.symm hr
    simp [nock_exec, mtcBOv4, Need.toNoun, eqCode, hr, hr', hD, comp_emit_arm, he]

theorem mtcBO_L (hc : CompIn ctx) (ned : Need) (os oh ot rh rt r o fail : Nat) (Z : Noun)
    (g : Gen (TreapMap mugF)) :
    nock (mtcS [os, oh, ot, rh, rt] ned r o fail Z g x ctx) mtcBOL
      = some (C (A g.bo) (genNoun (cfEmitG (mtcClq r os fail) g) x)) := by
  have h : mtcBOL = mtcPAL := rfl
  rw [h]; exact mtcPA_L x hc ned os oh ot rh rt r o fail Z g

/-! ## The dispatch of the trap -/

theorem mtc_disp_pair (h t : Need) (r o fail : Nat) (Z : Noun) (g : Gen (TreapMap mugF)) :
    nock (mtcT (Need.pair h t) r o fail Z g x ctx) mtcLoop
      = nock (mtcT (Need.pair h t) r o fail Z g x ctx) mtcPAr0 := by
  obtain ⟨a, b, hh⟩ := need_cell h
  conv => { lhs; arg 2; rw [mtc_loop_eq] }
  simp only [mtcT, compCore]
  generalize comp.door = Dr
  simp [nock_exec, mtcT1, mtcT2, mtcT3, Need.toNoun, hh, eqCode]

theorem mtc_disp_both (rn : Nat) (h t : Need) (r o fail : Nat) (Z : Noun) (g : Gen (TreapMap mugF)) :
    nock (mtcT (Need.both rn h t) r o fail Z g x ctx) mtcLoop
      = nock (mtcT (Need.both rn h t) r o fail Z g x ctx) mtcBOr0 := by
  conv => { lhs; arg 2; rw [mtc_loop_eq] }
  simp only [mtcT, compCore]
  generalize comp.door = Dr
  simp [nock_exec, mtcT1, mtcT2, mtcT3, mtcBOh, Need.toNoun, eqCode, Tag.both, Tag.none, Tag.this]

/-! ## The trap on a cell and on `%both`, and on every need -/

/-- **The trap on a cell `[h t]`**, from the trap on `h` and on `t`. -/
theorem mtc_pair (hc : CompIn ctx) (fail : Nat) (Z : Noun) (h t : Need)
    (ih_h : MtcAt ctx x fail Z h) (ih_t : MtcAt ctx x fail Z t) : MtcAt ctx x fail Z (Need.pair h t) := by
  intro r o g
  rw [mtc_disp_pair, mtcPA_0, mtcPA_1]
  show _ = ((monoTryLoop fail t g.re o (mtcReG (mtcReG g))).bind fun p =>
    (monoTryLoop fail h (mtcReG g).re p.1 p.2).bind fun q =>
    (emit (mtcSplit r (mtcReG g).re g.re q.1) q.2).bind fun s => emit (mtcClq r s.1 fail) s.2).map
      (fun p => C (A p.1) (genNoun p.2 x))
  have et := ih_t g.re o (mtcReG (mtcReG g))
  cases e3 : monoTryLoop fail t g.re o (mtcReG (mtcReG g)) with
  | none =>
    rw [e3] at et
    rw [mtcPA_2n x h t _ _ r o fail Z _ et]; rfl
  | some p =>
    obtain ⟨ot, g3⟩ := p
    rw [e3] at et
    rw [mtcPA_2 x h t _ _ r o fail Z _ g3 ot et]
    simp only [Option.bind_some]
    have eh := ih_h (mtcReG g).re ot g3
    cases e4 : monoTryLoop fail h (mtcReG g).re ot g3 with
    | none => rw [e4] at eh; rw [mtcPA_3n x h t ot _ _ r o fail Z _ eh]; rfl
    | some q =>
      obtain ⟨oh, g4⟩ := q
      rw [e4] at eh
      rw [mtcPA_3 x h t ot _ _ r o fail Z _ g4 oh eh, mtcPA_4 x hc, mtcPA_L x hc]
      simp [cf_emit_g]

/-- **The trap on `%both`**, from the trap on `h` and on `t`. -/
theorem mtc_both (hc : CompIn ctx) (fail : Nat) (Z : Noun) (rn : Nat) (h t : Need)
    (ih_h : MtcAt ctx x fail Z h) (ih_t : MtcAt ctx x fail Z t) :
    MtcAt ctx x fail Z (Need.both rn h t) := by
  intro r o g
  rw [mtc_disp_both, mtcBO_0, mtcBO_1]
  show _ = ((monoTryLoop fail t g.re o (mtcReG (mtcReG g))).bind fun p =>
    (monoTryLoop fail h (mtcReG g).re p.1 p.2).bind fun q =>
    (if r = rn then (crashM : CM (TreapMap mugF) Nat) else
      (emit (mtcSplit3 r (mtcReG g).re g.re rn q.1) >>= fun os => emit (mtcClq r os fail))) q.2).map
      (fun p => C (A p.1) (genNoun p.2 x))
  have et := ih_t g.re o (mtcReG (mtcReG g))
  cases e3 : monoTryLoop fail t g.re o (mtcReG (mtcReG g)) with
  | none =>
    rw [e3] at et
    rw [mtcBO_2n x rn h t _ _ r o fail Z _ et]; rfl
  | some p =>
    obtain ⟨ot, g3⟩ := p
    rw [e3] at et
    rw [mtcBO_2 x rn h t _ _ r o fail Z _ g3 ot et]
    simp only [Option.bind_some]
    have eh := ih_h (mtcReG g).re ot g3
    cases e4 : monoTryLoop fail h (mtcReG g).re ot g3 with
    | none => rw [e4] at eh; rw [mtcBO_3n x rn h t ot _ _ r o fail Z _ eh]; rfl
    | some q =>
      obtain ⟨oh, g4⟩ := q
      rw [e4] at eh
      rw [mtcBO_3 x rn h t ot _ _ r o fail Z _ g4 oh eh, mtcBO_4 x hc]
      by_cases hr : r = rn
      · simp [hr, crashM]
      · rw [if_neg hr, mtcBO_L x hc]
        simp [hr, cf_emit_g, bind_apply]

/-- **The trap of `+mono-try-call` on every need** is `monoTryLoop`. -/
theorem mtc_loop (hc : CompIn ctx) (fail : Nat) (Z : Noun) : ∀ ned : Need, MtcAt ctx x fail Z ned
  | Need.none => mtc_none x fail Z
  | Need.this rn => mtc_this hc x fail Z rn
  | Need.pair h t => mtc_pair x hc fail Z h t (mtc_loop hc fail Z h) (mtc_loop hc fail Z t)
  | Need.both rn h t => mtc_both x hc fail Z rn h t (mtc_loop hc fail Z h) (mtc_loop hc fail Z t)

/-- **The gate `+mono-try-call`** on `[ned opt [sub pes]]` is `monoTryCall`
(the pushes at axes `54`, `119`, `122` of the gate, then the trap). -/
theorem mtc_gate (hc : CompIn ctx) (ned : Need) (opt sub pes : Nat) (g : Gen (TreapMap mugF)) :
    nock (C mtcGB (C (C ned.toNoun (C (A opt) (C (A sub) (A pes)))) (compCore g x ctx))) mtcGB
      = (monoTryCall ned opt sub pes g).map fun p => C (A p.1) (genNoun p.2 x) := by
  have hl := mtc_loop x hc pes (C (A opt) (C (A sub) (A pes))) ned sub opt g
  conv => { lhs; arg 2; rw [mtc_gb] }
  simp only [mtcT, compCore] at hl ⊢
  generalize comp.door = Dr at hl ⊢
  simp [nock_exec, hl, monoTryCall]

end Compiler
end Formalization
