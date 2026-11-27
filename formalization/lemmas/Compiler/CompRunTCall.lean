import lemmas.Compiler.CompRunTBase
import lemmas.Compiler.CompRunDirectMonoP

/-!
# The tail of a direct call, threaded (README Gaps 19 (g))

The runs of `q` and `p` inside a direct call (`crd_ctailR`, `crd_dropR`) were
linked at the one rest the call's need step left.  A miss inside them (a direct
call in the subject or the formula of another one) moves the rest again, so here
they are threaded: `RunAtRT` (some `x'` with `Y x x'`), and the run of `p` is
taken at every rest `x1` with `Y x x1` (the rest the run of `q` leaves).

* `RunAtRT`, `crd_cnfRT`, `crd_nfRT`, **`crd_ctailRT`**, **`crd_dropRT`**.
* `crd_from7MT`, **`crd_callMT`**, **`comp_run_n2_callMonoTT`** (steps `0` to
  `14` of the call, the need step from `x` to `x'`, then the tail from `x'`).
* `comp_run_n2_dropMonoT` (the dropped call), `crd_hpqMT` (the runs of `p` and
  `q` from threaded parts), **`comp_run_n2_directXTT`** (the call, dropped or
  not, with its parts threaded: `PartRT`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-- **One instance of the threaded run link against `R`**: the run at `x`
returns the model's result with some rest `x'`, `Y x x'`. -/
def RunAtRT (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)) (ctx : Noun)
    (Y : GenRest → GenRest → Prop) (x : GenRest) (mono sup : Noun) (n : Nomm) (goal : CGoalL CSet)
    (region : List Nat) (g : Gen (TreapMap mugF)) : Prop :=
  ∃ x', Y x x' ∧ nock (crSubj mono n.toNoun goal.toNoun (listNoun A region) sup (compCore g x ctx)) crDol
    = (R n goal region g).map fun p => C p.1.goal.toNoun (genNoun p.2 x')

theorem runAtRT_of {R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)}
    {Y : GenRest → GenRest → Prop} (hr : ∀ x, Y x x) {x : GenRest} {mono sup : Noun} {n : Nomm}
    {goal : CGoalL CSet} {region : List Nat} {g : Gen (TreapMap mugF)}
    (h : RunAtR R ctx x mono sup n goal region g) : RunAtRT R ctx Y x mono sup n goal region g :=
  ⟨x, hr x, h⟩

/-- The first push of the tail, threaded (`crd_cnfR`): `q` is skipped under
`+safe-fol-fol` (rest kept) or run (rest moved). -/
theorem crd_cnfRT (h7 : slot? 7 ctx = some compK) (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet))
    (p q : Nomm) (region : List Nat) (x : GenRest) (mono I sup goalN : Noun) (nexA : NextL CSet)
    (V8 V7 V6 V5 V4 V3 V2 V1 PV : Noun) (g : Gen (TreapMap mugF)) {Y : GenRest → GenRest → Prop}
    (hr : ∀ x, Y x x)
    (hq : RunAtRT R ctx Y x mono sup q (CGoalL.next (Lazy.ofSure Sure.bunt) nexA.th) region g) :
    ∃ x1, Y x x1 ∧ nock (crdS9 nexA.goal.toNoun V8 V7 V6 V5 V4 V3 V2 V1 PV
      (crSubj mono (C (A 2) (C p.toNoun (C q.toNoun I))) goalN (listNoun A region) sup (compCore g x ctx))) crDKc10
      = (crdFqR R q nexA.th region g).map fun p => C p.1.goal.toNoun (genNoun p.2 x1) := by
  have h63 := crd_ctx63 h7
  have hsa : slot? 767 ana = some safe_fol_fol.arm := safe_fol_fol.arm_at
  have hsf := safe_fol_fol_pill q
  cases hs : safeFolFol q with
  | true =>
    refine ⟨x, hr x, ?_⟩
    rw [cr_next_nounL]
    unfold crDKc10 crdFqR
    simp only [crSubj, compCore]
    generalize comp.door = Dr
    simp [nock_exec, h63, hsa, safe_fol_fol_arm, hsf, hs, loob, pure, StateT.pure, cr_next_nounL, cr_bunt_noun]
  | false =>
    obtain ⟨x1, hy, hq1⟩ := hq
    refine ⟨x1, hy, ?_⟩
    rw [cgl_next_noun, cr_bunt_noun] at hq1
    rw [cr_next_nounL]
    unfold crDKc10 crdFqR
    simp only [crSubj, compCore] at hq1 ⊢
    generalize comp.door = Dr at hq1 ⊢
    simp [nock_exec, h63, hsa, safe_fol_fol_arm, hsf, hs, loob, cr_bat_dol, hq1]

/-- The first push of the dropped call, threaded (`crd_nfR`). -/
theorem crd_nfRT (h7 : slot? 7 ctx = some compK) (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet))
    (p q : Nomm) (region : List Nat) (x : GenRest) (mono I sup : Noun) (laz : Lazy CSet) (th : Jmp)
    (g : Gen (TreapMap mugF)) {Y : GenRest → GenRest → Prop} (hr : ∀ x, Y x x)
    (hq : RunAtRT R ctx Y x mono sup q (CGoalL.next (Lazy.ofSure Sure.bunt) th) region g) :
    ∃ x1, Y x x1 ∧ nock (C (A 0) (crSubj mono (C (A 2) (C p.toNoun (C q.toNoun I))) (CGoalL.next laz th).toNoun
      (listNoun A region) sup (compCore g x ctx))) crDNf
      = (crdFqR R q th region g).map fun p => C p.1.goal.toNoun (genNoun p.2 x1) := by
  have h63 := crd_ctx63 h7
  have hsa : slot? 767 ana = some safe_fol_fol.arm := safe_fol_fol.arm_at
  have hsf := safe_fol_fol_pill q
  cases hs : safeFolFol q with
  | true =>
    refine ⟨x, hr x, ?_⟩
    rw [cgl_next_noun]
    unfold crDNf crdFqR
    simp only [crSubj, compCore]
    generalize comp.door = Dr
    simp [nock_exec, h63, hsa, safe_fol_fol_arm, hsf, hs, loob, pure, StateT.pure, cr_next_nounL, cr_bunt_noun]
  | false =>
    obtain ⟨x1, hy, hq1⟩ := hq
    refine ⟨x1, hy, ?_⟩
    rw [cgl_next_noun, cr_bunt_noun] at hq1
    rw [cgl_next_noun]
    unfold crDNf crdFqR
    simp only [crSubj, compCore] at hq1 ⊢
    generalize comp.door = Dr at hq1 ⊢
    simp [nock_exec, h63, hsa, safe_fol_fol_arm, hsf, hs, loob, cr_bat_dol, hq1]

/-- **The tail of the call, threaded** (`crd_ctailR`): `q` from `x` to `x1`,
`+past` at `x1`, `p` from `x1` (taken at every rest `Y x x1`) to `x2`, `+copy`
at `x2`. -/
theorem crd_ctailRT (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)) (cd : Bell → Option Bool) (p q : Nomm)
    (hpn : PastAt ctx cd p)
    (region : List Nat) (x : GenRest) (mono I sup goalN : Noun) (nexA : NextL CSet)
    (V8 V7 V6 V5 V4 V3 V2 V1 PV : Noun) (g : Gen (TreapMap mugF)) {Y : GenRest → GenRest → Prop}
    (hr : ∀ x, Y x x) (ht : ∀ {x y z : GenRest}, Y x y → Y y z → Y x z)
    (hq : RunAtRT R ctx Y x mono sup q (CGoalL.next (Lazy.ofSure Sure.bunt) nexA.th) region g)
    (hp : ∀ x1, Y x x1 → ∀ nexF g2 nexF' g3, crdFqR R q nexA.th region g = some (nexF, g2) →
      pastL cd nexF p region g2 = some (nexF', g3) →
      RunAtRT R ctx Y x1 mono sup p (CGoalL.next nexA.laz nexF'.th) region g3)
    (hcp : ∀ nexF g2 nexF' g3 nexS g4, crdFqR R q nexA.th region g = some (nexF, g2) →
      pastL cd nexF p region g2 = some (nexF', g3) →
      R p (CGoalL.next nexA.laz nexF'.th) region g3 = some (nexS, g4) →
      CopyH g4.re nexS.laz nexF'.laz) :
    ∃ x', Y x x' ∧ nock (crdS9 nexA.goal.toNoun V8 V7 V6 V5 V4 V3 V2 V1 PV
      (crSubj mono (C (A 2) (C p.toNoun (C q.toNoun I))) goalN (listNoun A region) sup (compCore g x ctx))) crDKr10
      = (crdTailMR R cd p q nexA region g).map fun p => C p.1.goal.toNoun (genNoun p.2 x') := by
  obtain ⟨x1, hy1, hnf⟩ := crd_cnfRT h7 R p q region x mono I sup goalN nexA V8 V7 V6 V5 V4 V3 V2 V1 PV g hr hq
  have hD1 := cr_past_at
  have hD2 := comp_cp_at
  unfold crdTailMR
  generalize hF : crdFqR R q nexA.th region = F at hnf hp hcp
  simp only [crSubj, compCore, crdS9, cr_next_nounL] at hnf ⊢
  cases eq : F g with
  | none =>
    rw [eq] at hnf
    refine ⟨x1, hy1, ?_⟩
    generalize comp.door = Dr at hnf hD1 hD2 ⊢
    unfold crDKr10
    simp [nock_exec, hnf, bind, StateT.bind, eq]
  | some r =>
    obtain ⟨nexF, g2⟩ := r
    rw [eq] at hnf
    simp only [Option.map_some, cr_next_nounL] at hnf
    have hpa := hpn x1 g2 nexF region
    simp only [cr_next_nounL, compCore] at hpa
    cases e3 : pastL (S := CSet) (Map := TreapMap mugF) cd nexF p region g2 with
    | none =>
      rw [e3] at hpa
      refine ⟨x1, hy1, ?_⟩
      generalize comp.door = Dr at hnf hD1 hD2 hpa ⊢
      unfold crDKr10 crDKr11 crDKc11
      simp [nock_exec, crSubj, Nomm.toNoun, hnf, bind, StateT.bind, h7, hcode, hD1, cr_past_arm, hpa, eq, e3]
    | some r3 =>
      obtain ⟨nexF', g3⟩ := r3
      rw [e3] at hpa
      simp only [Option.map_some, cr_next_nounL] at hpa
      obtain ⟨x2, hy2, hp1⟩ := hp x1 hy1 nexF g2 nexF' g3 eq e3
      rw [cgl_next_noun] at hp1
      simp only [crSubj, compCore] at hp1
      refine ⟨x2, ht hy1 hy2, ?_⟩
      cases eq2 : R p
          (CGoalL.next nexA.laz nexF'.th) region g3 with
      | none =>
        rw [eq2] at hp1
        generalize comp.door = Dr at hnf hD1 hD2 hpa hp1 ⊢
        unfold crDKr10 crDKr11 crDKc11 crDKr12 crDKc12
        simp [nock_exec, crSubj, Nomm.toNoun, hnf, bind, StateT.bind, h7, hcode, hD1, cr_past_arm, hpa,
          cr_bat_dol, hp1, eq, e3, eq2]
      | some r' =>
        obtain ⟨nexS, g4⟩ := r'
        rw [eq2] at hp1
        simp only [Option.map_some, cr_next_nounL] at hp1
        have hcpy := comp_copy_all h7 x2 g4 nexS nexF'.laz (hcp nexF g2 nexF' g3 nexS g4 eq e3 eq2)
        simp only [compCore, cr_next_nounL] at hcpy
        generalize comp.door = Dr at hnf hD1 hD2 hpa hp1 hcpy ⊢
        unfold crDKr10 crDKr11 crDKc11 crDKr12 crDKc12 crDKr13 crDKc13 crDKr14
        simp [nock_exec, crSubj, Nomm.toNoun, hnf, bind, StateT.bind, h7, hcode, hD1, cr_past_arm, hpa,
          cr_bat_dol, hp1, eq, e3, eq2, hD2, cr_cp_arm, hcpy, cr_next_nounL, Function.comp_def]

/-- **The dropped call after the test, threaded** (`crd_dropR`). -/
theorem crd_dropRT (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)) (cd : Bell → Option Bool) (p q : Nomm)
    (hpn : PastAt ctx cd p) (region : List Nat) (x : GenRest) (mono I sup : Noun) (laz : Lazy CSet)
    (th : Jmp) (g : Gen (TreapMap mugF)) {Y : GenRest → GenRest → Prop}
    (hr : ∀ x, Y x x) (ht : ∀ {x y z : GenRest}, Y x y → Y y z → Y x z)
    (hq : RunAtRT R ctx Y x mono sup q (CGoalL.next (Lazy.ofSure Sure.bunt) th) region g)
    (hp : ∀ x1, Y x x1 → ∀ nexF g2 nexF' g3, crdFqR R q th region g = some (nexF, g2) →
      pastL cd nexF p region g2 = some (nexF', g3) →
      RunAtRT R ctx Y x1 mono sup p (CGoalL.next (Lazy.ofSure Sure.bunt) nexF'.th) region g3)
    (hcp : ∀ nexF g2 nexF' g3 nexS g4, crdFqR R q th region g = some (nexF, g2) →
      pastL cd nexF p region g2 = some (nexF', g3) →
      R p (CGoalL.next (Lazy.ofSure Sure.bunt) nexF'.th) region g3 = some (nexS, g4) →
      CopyH g4.re nexS.laz nexF'.laz) :
    ∃ x', Y x x' ∧ nock (C (A 0) (crSubj mono (C (A 2) (C p.toNoun (C q.toNoun I))) (CGoalL.next laz th).toNoun
      (listNoun A region) sup (compCore g x ctx))) crDDrop
      = (crdTailMR R cd p q ⟨Lazy.ofSure Sure.bunt, th⟩ region g).map fun p => C p.1.goal.toNoun (genNoun p.2 x') := by
  obtain ⟨x1, hy1, hnf⟩ := crd_nfRT h7 R p q region x mono I sup laz th g hr hq
  have hD1 := cr_past_at
  have hD2 := comp_cp_at
  unfold crdTailMR
  simp only []
  generalize hF : crdFqR R q th region = F at hnf hp hcp
  simp only [crSubj, compCore] at hnf ⊢
  cases eq : F g with
  | none =>
    rw [eq] at hnf
    refine ⟨x1, hy1, ?_⟩
    generalize comp.door = Dr at hnf hD1 hD2 ⊢
    unfold crDDrop
    simp [nock_exec, hnf, bind, StateT.bind, eq]
  | some r =>
    obtain ⟨nexF, g2⟩ := r
    rw [eq] at hnf
    simp only [Option.map_some, cr_next_nounL] at hnf
    have hpa := hpn x1 g2 nexF region
    simp only [cr_next_nounL, compCore] at hpa
    cases e3 : pastL (S := CSet) (Map := TreapMap mugF) cd nexF p region g2 with
    | none =>
      rw [e3] at hpa
      refine ⟨x1, hy1, ?_⟩
      generalize comp.door = Dr at hnf hD1 hD2 hpa ⊢
      unfold crDDrop crDD1 crDD2 crDD3
      simp [nock_exec, crSubj, Nomm.toNoun, hnf, bind, StateT.bind, h7, hcode, hD1, cr_past_arm, hpa, eq, e3]
    | some r3 =>
      obtain ⟨nexF', g3⟩ := r3
      rw [e3] at hpa
      simp only [Option.map_some, cr_next_nounL] at hpa
      obtain ⟨x2, hy2, hp1⟩ := hp x1 hy1 nexF g2 nexF' g3 eq e3
      rw [cgl_next_noun, cr_bunt_noun] at hp1
      simp only [crSubj, compCore] at hp1
      refine ⟨x2, ht hy1 hy2, ?_⟩
      cases eq2 : R p (CGoalL.next (Lazy.ofSure Sure.bunt) nexF'.th) region g3 with
      | none =>
        rw [eq2] at hp1
        generalize comp.door = Dr at hnf hD1 hD2 hpa hp1 ⊢
        unfold crDDrop crDD1 crDD2 crDD3
        simp [nock_exec, crSubj, Nomm.toNoun, hnf, bind, StateT.bind, h7, hcode, hD1, cr_past_arm, hpa,
          cr_bat_dol, hp1, eq, e3, eq2]
      | some r' =>
        obtain ⟨nexS, g4⟩ := r'
        rw [eq2] at hp1
        simp only [Option.map_some, cr_next_nounL] at hp1
        have hcpy := comp_copy_all h7 x2 g4 nexS nexF'.laz (hcp nexF g2 nexF' g3 nexS g4 eq e3 eq2)
        simp only [compCore, cr_next_nounL] at hcpy
        generalize comp.door = Dr at hnf hD1 hD2 hpa hp1 hcpy ⊢
        unfold crDDrop crDD1 crDD2 crDD3
        simp [nock_exec, crSubj, Nomm.toNoun, hnf, bind, StateT.bind, h7, hcode, hD1, cr_past_arm, hpa,
          cr_bat_dol, hp1, eq, e3, eq2, hD2, cr_cp_arm, hcpy, cr_next_nounL, Function.comp_def]

/-- **Steps `7` to `14` under `mono` `&`, threaded** (`crd_from7M`). -/
theorem crd_from7MT (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)) (cd : Bell → Option Bool) (p q : Nomm)
    (hpn : PastAt ctx cd p) (region : List Nat) (x : GenRest) (hx : x.NoSoft) (SOF V5 V2 PV sup : Noun)
    (subNed : Need) (b : Bell) (goal : CGoalL CSet) (g : Gen (TreapMap mugF)) {Y : GenRest → GenRest → Prop}
    (hr : ∀ x, Y x x) (ht : ∀ {x y z : GenRest}, Y x y → Y y z → Y x z)
    (hblk : nock (crdS6m SOF V5 (listNoun A (flattenNeed subNed)) subNed.toNoun V2 PV
      (crSubj (A 0) (crdN p q b) goal.toNoun (listNoun A region) sup (compCore g x ctx))) crDKc7
      = (crdBlockMM b (flattenNeed subNed) goal g).map fun p => crdBlkN p x)
    (hq : ∀ s o g1, monoBlocks b subNed goal g = some ((s, o), g1) →
      RunAtRT R ctx Y x (A 0) sup q (CGoalL.next (Lazy.ofSure Sure.bunt) (jmp0 o)) region g1)
    (hp : ∀ x1, Y x x1 → ∀ s o g1 nexF g2 nexF' g3, monoBlocks b subNed goal g = some ((s, o), g1) →
      crdFqR R q (jmp0 o) region g1 = some (nexF, g2) → pastL cd nexF p region g2 = some (nexF', g3) →
      RunAtRT R ctx Y x1 (A 0) sup p (CGoalL.next (Lazy.ofSure (lazyReg s)) nexF'.th) region g3)
    (hcp : ∀ s o g1 nexF g2 nexF' g3 nexS g4, monoBlocks b subNed goal g = some ((s, o), g1) →
      crdFqR R q (jmp0 o) region g1 = some (nexF, g2) → pastL cd nexF p region g2 = some (nexF', g3) →
      R p (CGoalL.next (Lazy.ofSure (lazyReg s)) nexF'.th) region g3 = some (nexS, g4) →
      CopyH g4.re nexS.laz nexF'.laz) :
    ∃ x', Y x x' ∧ nock (crdS6m SOF V5 (listNoun A (flattenNeed subNed)) subNed.toNoun V2 PV
      (crSubj (A 0) (crdN p q b) goal.toNoun (listNoun A region) sup (compCore g x ctx))) crDKr7
      = (crdCallMM R cd p q b subNed goal region g).map fun p => C p.1.goal.toNoun (genNoun p.2 x') := by
  rw [crd_7to9M h7 x hx SOF V5 V2 PV subNed p q b (listNoun A region) sup goal g hblk]
  unfold crdCallMM
  rw [monoBlocks_eq]
  simp only [bind_apply]
  cases eb : crdBlockMM b (flattenNeed subNed) goal g with
  | none => exact ⟨x, hr x, rfl⟩
  | some r =>
    obtain ⟨⟨opt, s, pes⟩, g1⟩ := r
    simp only [Option.bind_some]
    cases em : monoTryCall (Map := TreapMap mugF) subNed opt s pes g1 with
    | none => exact ⟨x, hr x, rfl⟩
    | some r' =>
      obtain ⟨o, g2⟩ := r'
      have hmb : monoBlocks b subNed goal g = some ((s, o), g2) := by
        rw [monoBlocks_eq]; simp [bind_apply, eb, em, pure_apply, Functor.map, StateT.map]
      simp only [Option.bind_some, pure_apply]
      have ht' := crd_ctailRT h7 hcode R cd p q hpn region x (A 0) (C (A 0) (C b.toNoun (A 0))) sup goal.toNoun
        (crdArg (Need.this s) o) (C (Need.this s).toNoun (A o)) (C (A opt) (C (A s) (A pes))) SOF V5
        (listNoun A (flattenNeed subNed)) subNed.toNoun V2 (A 0) PV g2 hr ht (hq s o g2 hmb)
        (fun x1 hy1 nexF g3 nexF' g4 e e3 => hp x1 hy1 s o g2 nexF g3 nexF' g4 hmb e e3)
        (fun nexF g3 nexF' g4 nexS g5 e e3 e4 => hcp s o g2 nexF g3 nexF' g4 nexS g5 hmb e e3 e4)
      rw [crdArg_this] at ht'
      exact ht'

/-- **The call under `mono` `&`, threaded from the rest after the need step**
(`crd_callM` with the runs of `q` and `p` moving the rest). -/
theorem crd_callMT (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)) (cd : Bell → Option Bool)
    (msup : Option Nomm) (p q : Nomm) (hpn : PastAt ctx cd p) (b : Bell) (nb : NeedOrd) (sur SOF : Noun) (x : GenRest) (hx : x.NoSoft)
    (hn : CallNounM msup ctx p q b nb sur x (A 0) SOF) (PV : Noun) (goal : CGoalL CSet) (region : List Nat)
    (g : Gen (TreapMap mugF)) {Y : GenRest → GenRest → Prop}
    (hr : ∀ x, Y x x) (ht : ∀ {x y z : GenRest}, Y x y → Y y z → Y x z)
    (hinv : ∀ subNed g1, needOrdAllocRegs nb g = some (subNed, g1) → GInv g1 goal)
    (hq : ∀ subNed g1 s o g2, needOrdAllocRegs nb g = some (subNed, g1) →
      monoBlocks b subNed goal g1 = some ((s, o), g2) →
      RunAtRT R ctx Y x (A 0) (unitNoun Nomm.toNoun msup) q (CGoalL.next (Lazy.ofSure Sure.bunt) (jmp0 o)) region g2)
    (hp : ∀ x1, Y x x1 → ∀ subNed g1 s o g2 nexF g3 nexF' g4, needOrdAllocRegs nb g = some (subNed, g1) →
      monoBlocks b subNed goal g1 = some ((s, o), g2) →
      crdFqR R q (jmp0 o) region g2 = some (nexF, g3) → pastL cd nexF p region g3 = some (nexF', g4) →
      RunAtRT R ctx Y x1 (A 0) (unitNoun Nomm.toNoun msup) p (CGoalL.next (Lazy.ofSure (lazyReg s)) nexF'.th) region g4)
    (hcp : ∀ subNed g1 s o g2 nexF g3 nexF' g4 nexS g5, needOrdAllocRegs nb g = some (subNed, g1) →
      monoBlocks b subNed goal g1 = some ((s, o), g2) →
      crdFqR R q (jmp0 o) region g2 = some (nexF, g3) → pastL cd nexF p region g3 = some (nexF', g4) →
      R p (CGoalL.next (Lazy.ofSure (lazyReg s)) nexF'.th) region g4 = some (nexS, g5) →
      CopyH g5.re nexS.laz nexF'.laz) :
    ∃ x', Y x x' ∧ nock (C PV (crSubj (A 0) (crdN p q b) goal.toNoun (listNoun A region) (unitNoun Nomm.toNoun msup)
      (compCore g x ctx))) crDCall
      = ((needOrdAllocRegs nb >>= fun subNed => crdCallMM R cd p q b subNed goal region) g).map
          fun p => C p.1.goal.toNoun (genNoun p.2 x') := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  rw [crd_head6M h7 msup p q b nb sur x (A 0) SOF hn PV goal.toNoun region g, bind_apply]
  cases e : needOrdAllocRegs nb g with
  | none => exact ⟨x, hr x, rfl⟩
  | some r =>
    obtain ⟨subNed, g1⟩ := r
    simp only [Option.bind_some]
    have hblk : nock (crdS6m SOF sur (listNoun A (flattenNeed subNed)) subNed.toNoun nb.toNoun PV
        (crSubj (A 0) (crdN p q b) goal.toNoun (listNoun A region) (unitNoun Nomm.toNoun msup) (compCore g1 x ctx)))
        crDKc7 = (crdBlockMM b (flattenNeed subNed) goal g1).map fun p => crdBlkN p x := by
      cases goal with
      | done => exact crd_blkM_done hc x SOF sur nb.toNoun PV subNed p q b region _ g1
      | next laz th =>
        exact crd_blkM_next h7 x hx SOF sur nb.toNoun PV subNed p q b region _ _ (by simp) g1
          (hinv subNed g1 e)
      | pick z o =>
        exact crd_blkM_next h7 x hx SOF sur nb.toNoun PV subNed p q b region _ _ (by simp) g1
          (hinv subNed g1 e)
    exact crd_from7MT h7 hcode R cd p q hpn region x hx SOF sur nb.toNoun PV _ subNed b goal g1 hr ht hblk
      (fun s o g2 h => hq subNed g1 s o g2 e h)
      (fun x1 hy1 s o g2 nexF g3 nexF' g4 h h3 h4 => hp x1 hy1 subNed g1 s o g2 nexF g3 nexF' g4 e h h3 h4)
      (fun s o g2 nexF g3 nexF' g4 nexS g5 h h3 h4 h5 => hcp subNed g1 s o g2 nexF g3 nexF' g4 nexS g5 e h h3 h4 h5)

/-- **The case `%2` on a direct call under `mono` `&`, threaded through its
tail** (`comp_run_n2_callMonoT` with the runs of `q` and `p` moving the rest):
the need step takes `x` to `x'` (`Y x x'`), then the tail from `x'`. -/
theorem comp_run_n2_callMonoTT (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm)
    (hpn : PastAt ctx env.cod p) (b : Bell) (hcd : CodePure cod env b) (nb : NeedOrd) (sur SOF : Noun)
    (goal : CGoalL CSet) (region : List Nat) (g : Gen (TreapMap mugF)) (hinv : GInv g goal)
    (hdr : crdDrop (env.pure b) goal = false) (hri : env.ring b = Option.none) (hnb : env.need b = some nb)
    {Y : GenRest → GenRest → Prop} (hr : ∀ x, Y x x) (ht : ∀ {x y z : GenRest}, Y x y → Y y z → Y x z)
    (x x' : GenRest) (hy : Y x x') (hx' : x'.NoSoft) (hT : CallNounMT msup ctx p q b nb sur x x' (A 0) SOF)
    (hn : CallNounM msup ctx p q b nb sur x' (A 0) SOF)
    (hq : ∀ subNed g1 s o g2, needOrdAllocRegs nb g = some (subNed, g1) →
      monoBlocks b subNed goal g1 = some ((s, o), g2) →
      RunAtRT (runLCM env true msup) ctx Y x' (A 0) (unitNoun Nomm.toNoun msup) q
        (CGoalL.next (Lazy.ofSure Sure.bunt) (jmp0 o)) region g2)
    (hp : ∀ x1, Y x' x1 → ∀ subNed g1 s o g2 nexF g3 nexF' g4, needOrdAllocRegs nb g = some (subNed, g1) →
      monoBlocks b subNed goal g1 = some ((s, o), g2) →
      crdFqR (runLCM env true msup) q (jmp0 o) region g2 = some (nexF, g3) →
      pastL env.cod nexF p region g3 = some (nexF', g4) →
      RunAtRT (runLCM env true msup) ctx Y x1 (A 0) (unitNoun Nomm.toNoun msup) p
        (CGoalL.next (Lazy.ofSure (lazyReg s)) nexF'.th) region g4)
    (hcp : ∀ subNed g1 s o g2 nexF g3 nexF' g4 nexS g5, needOrdAllocRegs nb g = some (subNed, g1) →
      monoBlocks b subNed goal g1 = some ((s, o), g2) →
      crdFqR (runLCM env true msup) q (jmp0 o) region g2 = some (nexF, g3) →
      pastL env.cod nexF p region g3 = some (nexF', g4) →
      runLCM env true msup p (CGoalL.next (Lazy.ofSure (lazyReg s)) nexF'.th) region g4 = some (nexS, g5) →
      CopyH g5.re nexS.laz nexF'.laz) :
    ∃ x'', Y x x'' ∧ nock (crSubj (A 0) (Nomm.n2 p q (some (b, Option.none))).toNoun goal.toNoun (listNoun A region)
        (unitNoun Nomm.toNoun msup) (compCore g x ctx)) crDol
      = (runLCM env true msup (Nomm.n2 p q (some (b, Option.none))) goal region g).map
          fun r => C r.1.goal.toNoun (genNoun r.2 x'') := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  obtain ⟨V, hgot, hv⟩ := hcd
  obtain ⟨x'', hy2, hcall0⟩ := crd_callMT h7 hcode (runLCM env true msup) env.cod msup p q hpn b nb sur SOF x' hx' hn
    (loob (env.pure b)) goal region g hr ht (fun _ _ e => ginv_noar hinv e) hq hp hcp
  refine ⟨x'', ht hy hy2, ?_⟩
  rw [crd_model_n2M env msup p q b nb goal region hdr hri hnb, crd_noun, cr_disp_n2, cr2_dir, crd_eq]
  have hpure := crd_pure hc hcode p.toNoun q.toNoun b.toNoun (unitNoun id Option.none) V _ (A 0)
    goal.toNoun (listNoun A region) (unitNoun Nomm.toNoun msup) g x hgot hv
  have ht0 := crd_test_all h7 (C (A 2) (C p.toNoun (C q.toNoun (C (A 0) (C b.toNoun (unitNoun id Option.none))))))
    (A 0) (listNoun A region) (unitNoun Nomm.toNoun msup) (env.pure b) goal g x
  rw [hdr] at ht0
  have hcall := (crd_call_shift h7 msup p q b nb sur x x' (A 0) SOF hT hn (loob (env.pure b)) goal.toNoun region g).trans
    hcall0
  simp only [crdN] at hcall
  have hu : unitNoun (id : Noun → Noun) Option.none = A 0 := rfl
  rw [hu] at hpure ht0 ⊢
  have hl : loob false = A 1 := rfl
  rw [hl] at ht0
  unfold crDHead
  simp [nock_exec, hpure, ht0, hcall]

/-- **The case `%2` on a dropped call at `mono` `&`, threaded**
(`comp_run_n2_dropMono`). -/
theorem comp_run_n2_dropMonoT (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm)
    (hpn : PastAt ctx env.cod p) (b : Bell) (key : Option Noun) (hcd : CodePure cod env b)
    (laz : Lazy CSet) (th : Jmp) (region : List Nat) (g : Gen (TreapMap mugF)) (hpu : env.pure b = true)
    (hne : Lazy.noneEquivalentL laz = true) (x : GenRest) (mono sup : Noun) {Y : GenRest → GenRest → Prop}
    (hr : ∀ x, Y x x) (ht : ∀ {x y z : GenRest}, Y x y → Y y z → Y x z)
    (hq : RunAtRT (runLCM env true msup) ctx Y x mono sup q (CGoalL.next (Lazy.ofSure Sure.bunt) th) region g)
    (hp : ∀ x1, Y x x1 → ∀ nexF g2 nexF' g3, crdFqR (runLCM env true msup) q th region g = some (nexF, g2) →
      pastL env.cod nexF p region g2 = some (nexF', g3) →
      RunAtRT (runLCM env true msup) ctx Y x1 mono sup p (CGoalL.next (Lazy.ofSure Sure.bunt) nexF'.th) region g3)
    (hcp : ∀ nexF g2 nexF' g3 nexS g4, crdFqR (runLCM env true msup) q th region g = some (nexF, g2) →
      pastL env.cod nexF p region g2 = some (nexF', g3) →
      runLCM env true msup p (CGoalL.next (Lazy.ofSure Sure.bunt) nexF'.th) region g3 = some (nexS, g4) →
      CopyH g4.re nexS.laz nexF'.laz) :
    RunAtRT (runLCM env true msup) ctx Y x mono sup (Nomm.n2 p q (some (b, key))) (CGoalL.next laz th) region g := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  obtain ⟨V, hgot, hv⟩ := hcd
  obtain ⟨x', hy, hdr⟩ := crd_dropRT h7 hcode (runLCM env true msup) env.cod p q hpn region x mono
    (C (A 0) (C b.toNoun (unitNoun id key))) sup laz th g hr ht hq hp hcp
  refine ⟨x', hy, ?_⟩
  rw [crd_model_dropM env msup p q b key laz th region hpu hne, crd_noun, cr_disp_n2, cr2_dir, crd_eq]
  have hpure := crd_pure hc hcode p.toNoun q.toNoun b.toNoun (unitNoun id key) V _ mono
    (CGoalL.next laz th).toNoun (listNoun A region) sup g x hgot hv
  rw [hpu] at hpure
  have ht0 := crd_test h7 (C (A 2) (C p.toNoun (C q.toNoun (C (A 0) (C b.toNoun (unitNoun id key)))))) mono
    (listNoun A region) sup laz th g x
  rw [hne] at ht0
  unfold crDHead
  simp [nock_exec, hpure, ht0, loob, hdr]

/-- **The runs of `p` and `q` of the call from threaded parts** (`crd_hpqM`):
`q` at the rest `x` after the need step, `p` at every rest `x1` with
`Y x x1`. -/
theorem crd_hpqMT {E : GenRest → Prop} {Y : GenRest → GenRest → Prop} {msup : Option Nomm}
    (hYk : YOk (XM E msup) Y) (env : CallEnv) (p q : Nomm) {region : List Nat}
    (P : PartRT env msup ctx (XM E msup) Y p region) (Q : PartRT env msup ctx (XM E msup) Y q region) (b : Bell)
    (nb : NeedOrd) (goal : CGoalL CSet) (g : Gen (TreapMap mugF)) (hinv : GInv g goal) (x : GenRest) (hx : x.NoSoft)
    (hE : E x) :
    (∀ subNed g1 s o g2, needOrdAllocRegs nb g = some (subNed, g1) →
      monoBlocks b subNed goal g1 = some ((s, o), g2) →
      RunAtRT (runLCM env true msup) ctx Y x (A 0) (unitNoun Nomm.toNoun msup) q
        (CGoalL.next (Lazy.ofSure Sure.bunt) (jmp0 o)) region g2) ∧
    (∀ x1, Y x x1 → ∀ subNed g1 s o g2 nexF g3 nexF' g4, needOrdAllocRegs nb g = some (subNed, g1) →
      monoBlocks b subNed goal g1 = some ((s, o), g2) →
      crdFqR (runLCM env true msup) q (jmp0 o) region g2 = some (nexF, g3) →
      pastL env.cod nexF p region g3 = some (nexF', g4) →
      RunAtRT (runLCM env true msup) ctx Y x1 (A 0) (unitNoun Nomm.toNoun msup) p
        (CGoalL.next (Lazy.ofSure (lazyReg s)) nexF'.th) region g4) ∧
    (∀ subNed g1 s o g2 nexF g3 nexF' g4 nexS g5, needOrdAllocRegs nb g = some (subNed, g1) →
      monoBlocks b subNed goal g1 = some ((s, o), g2) →
      crdFqR (runLCM env true msup) q (jmp0 o) region g2 = some (nexF, g3) →
      pastL env.cod nexF p region g3 = some (nexF', g4) →
      runLCM env true msup p (CGoalL.next (Lazy.ofSure (lazyReg s)) nexF'.th) region g4 = some (nexS, g5) →
      CopyH g5.re nexS.laz nexF'.laz) := by
  have hX : XM E msup x (A 0) (unitNoun Nomm.toNoun msup) := ⟨hE, rfl, rfl⟩
  refine ⟨fun subNed g1 s o g2 e eb => Q.link _ g2 (crd_goalsM hinv e eb).1 x _ _ hx hX,
    fun x1 hy1 subNed g1 s o g2 nexF g3 nexF' g4 e eb ef e3 => ?_,
    fun subNed g1 s o g2 nexF g3 nexF' g4 nexS g5 e eb ef e3 e4 => ?_⟩
  · obtain ⟨hq2, hp2, -⟩ := crd_goalsM hinv e eb
    exact P.link _ _ (tail_pgoal hq2 hp2 (crd_fq_resR Q.res hq2.2.1 hq2.2.2 ef) e3).1 x1 _ _ (hYk.soft hx hy1)
      (hYk.pres hX hy1)
  · obtain ⟨hq2, hp2, -⟩ := crd_goalsM hinv e eb
    have R2 := crd_fq_resR Q.res hq2.2.1 hq2.2.2 ef
    have ap : (lregs (Lazy.ofSure (lazyReg s : Sure CSet)) ++ lregs (Lazy.ofSure (Sure.bunt : Sure CSet))).Nodup := by
      rw [lregs_bunt, List.append_nil]; exact hp2.2.1
    exact (tail_copyH hq2 hp2 ap R2 e3 (P.res _ _ _ _ (tail_pgoal hq2 hp2 R2 e3).1 e4)).1

/-- **The direct call under `mono` `&`, threaded through its parts**: dropped
(`comp_run_n2_dropMonoT`) or not (the need step to `x'`, then
`comp_run_n2_callMonoTT`), with `p` and `q` threaded parts (`PartRT`), so a
miss inside the subject or the formula of the call is covered. -/
theorem comp_run_n2_directXTT {E : GenRest → Prop} {Y : GenRest → GenRest → Prop} {msup : Option Nomm}
    (hYk : YOk (XM E msup) Y) (h7 : slot? 7 ctx = some compK) {cod : Noun}
    (hcode : slot? 52 ctx = some cod) (env : CallEnv) (p q : Nomm) {region : List Nat}
    (P : PartRT env msup ctx (XM E msup) Y p region) (Q : PartRT env msup ctx (XM E msup) Y q region) (b : Bell)
    (hcd : CodePure cod env b)
    (nb : NeedOrd) (hE : ∀ x, x.NoSoft → E x → ∃ x' sur SOF, Y x x' ∧
      CallNounMT msup ctx p q b nb sur x x' (A 0) SOF ∧ CallNounM msup ctx p q b nb sur x' (A 0) SOF)
    (hri : env.ring b = Option.none) (hnb : env.need b = some nb)
    (goal : CGoalL CSet) (g : Gen (TreapMap mugF)) (hinv : GInv g goal) :
    CompRunAtXT (runLCM env true msup) ctx (XM E msup) Y (Nomm.n2 p q (some (b, Option.none))) goal region g := by
  cases hdr : crdDrop (env.pure b) goal with
  | false =>
    rintro x mono sup hx ⟨hEx, rfl, rfl⟩
    obtain ⟨x', sur, SOF, hy, hT, hn⟩ := hE x hx hEx
    have hx' := hYk.soft hx hy
    have hE' : E x' := (hYk.pres (show XM E msup x (A 0) (unitNoun Nomm.toNoun msup) from ⟨hEx, rfl, rfl⟩) hy).1
    obtain ⟨hq, hp, hcp⟩ := crd_hpqMT hYk env p q P Q b nb goal g hinv x' hx' hE'
    exact comp_run_n2_callMonoTT h7 hcode env msup p q P.past b hcd nb sur SOF goal region g hinv hdr hri hnb
      hYk.refl hYk.trans x x' hy hx' hT hn hq hp hcp
  | true =>
    cases goal with
    | done => simp [crdDrop] at hdr
    | pick z o => simp [crdDrop] at hdr
    | next laz th =>
      simp only [crdDrop, Bool.and_eq_true] at hdr
      obtain ⟨hpu, hne⟩ := hdr
      have hd : g.drop = false := hinv.2.1
      have hj : JmpIn (· < g.re) th := hinv.2.2
      rintro x mono sup hx ⟨hEx, rfl, rfl⟩
      have hX : XM E msup x (A 0) (unitNoun Nomm.toNoun msup) := ⟨hEx, rfl, rfl⟩
      exact comp_run_n2_dropMonoT h7 hcode env msup p q P.past b Option.none hcd laz th region g hpu hne x _ _
        hYk.refl hYk.trans
        (Q.link _ g (ginv_bunt_j hd hj) x _ _ hx hX)
        (fun x1 hy1 nexF g2 nexF' g3 e e3 =>
          P.link _ _ (tail_pgoal (ginv_bunt_j hd hj) (linv_bunt _ _) (crd_fq_resR Q.res hd hj e) e3).1 x1 _ _
            (hYk.soft hx hy1) (hYk.pres hX hy1))
        (fun nexF g2 nexF' g3 nexS g4 e e3 e4 => by
          have R2 := crd_fq_resR Q.res hd hj e
          exact (tail_copyH (ginv_bunt_j hd hj) (linv_bunt _ _) (by simp [lregs_bunt]) R2 e3
            (P.res _ _ _ _ (tail_pgoal (ginv_bunt_j hd hj) (linv_bunt _ _) R2 e3).1 e4)).1)

end Compiler
end Formalization
