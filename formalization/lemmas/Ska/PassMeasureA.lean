import lemmas.Ska.AnaInv
import lemmas.Ska.PassMeasureT

/-!
# The writes of the state-passing analysis keep `Tidy` (track F, Gaps 16)

`Ska/PassMeasureT.lean` proves that every write of the abstract step
`GStepT` keeps `GraphTP` (every identity's subject sock, `less-code` and
product tidy, every map `PiNorm`).  Here the state-passing analysis of
`Analysis.lean` is shown to keep `GraphTP` and a tidy memo (`TInv`) in every
arm, from a tidy root and a tidy memo of earlier pokes, and every write of
`+run` is a `GStepT.run` from a graph with `GraphTP`.

## 1. A bridge over any predicate of the subject

`Bridge.lean` asks `resolve` to keep the invariant at every well-formed
subject sock.  A tidy invariant cannot be kept at an untidy subject (`resolve`
would push it), so the bridge is restated over a predicate `QA` of the
subject (here: well formed, tidy, with a normal map), kept by `FolR P`
(`QPres`), and `QS` of the sock `resolve` gets.  The proofs are those of
`Bridge.lean` with `WellFormed` replaced (`bridge_stepQ`, `folLoop_goOKQ`,
`run_folTopRQ`).

## 2. The arms

`TInv` (the graph `GraphTP`, the memo `MemoTP`) is kept by every arm
(`allPT`), given `SInv` (`AnaInv.lean`) and a tidy subject.  The answers of
`resolve` at a tidy subject are tidy: from the graph (`GraphTP`), from the memo
(`MemoTP` and `annoTP_patchDatum`), from `%rec` (`annoTP_patchProd` with the
tidy `orig`), from `%he` (`tidy_msgSock` with a tidy stack member).
-/

namespace Formalization
namespace SkaModel
namespace Ana

open Nock

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-! ## 1. The bridge over `QA` and `QS` -/

/-- `FolR P` keeps `QA` from the subject to the product. -/
def QPres (QA : Anno → Prop) (P : Sock → Noun → TabEntry → Prop) : Prop :=
  ∀ (n : Nat) {fol : Noun} {sub : Anno} {mk : Option Noun} {bc df : Bool} {gen gen' : Gen}
    {out : FolOut}, QA sub → FolR P n fol sub mk bc df gen out gen' → QA out.prod

section StepQ

variable {P : Sock → Noun → TabEntry → Prop} {QA : Anno → Prop} {QS : Sock → Prop}
variable {Inv : GenS M R → Prop} {res : ResGo M R} {go : FolGoS M R} {n : Nat}

/-- What the bridge asks of `resolve` on a subject sock in `QS`: its
answers are in `P`, it keeps `Inv`, and it leaves the capes of `gen` alone. -/
def ResOKQ (QS : Sock → Prop) (P : Sock → Noun → TabEntry → Prop) (Inv : GenS M R → Prop) (res : ResGo M R) : Prop :=
  ∀ idT gs r gs', Inv gs → QS idT.1 → res idT gs = some (r, gs') → P idT.1 idT.2 r.2.core.tab ∧ Inv gs' ∧ gs'.gen = gs.gen

/-- What the bridge gives of a recursion on a subject in `QA`: it
keeps `Inv`, and its results, projected, are in `FolR P n` with any ghost. -/
def GoOKQ (QA : Anno → Prop) (P : Sock → Noun → TabEntry → Prop) (Inv : GenS M R → Prop) (n : Nat) (go : FolGoS M R) : Prop :=
  ∀ fol sub seat mk bc df gs out gs', Inv gs → QA sub → go fol sub seat mk bc df gs = some (out, gs') →
    Inv gs' ∧ ∀ γ, FolR P n fol sub mk bc df (gs.at γ) out gs'.gen

theorem GoOKQ.ch (hgo : GoOKQ QA P Inv n go) {fol : Noun} {sub : Anno} {seat mk : Option Noun} {bc df : Bool}
    {gs gs' : GenS M R} {out : FolOut} (hi : Inv gs) (hs : QA sub)
    (h : go fol sub seat mk bc df gs = some (out, gs'))
    (γ γ' : Nat) : FolR P n fol sub mk bc df (gs.at γ) out (gs'.at γ') :=
  folR_reghost ((hgo _ _ _ _ _ _ _ _ _ hi hs h).2 γ) rfl

/-- **One level of the state-passing `fol-loop` is in `FolR`.** -/
theorem bridge_stepQ (env : Env R) (hAS : ∀ a, QA a → QS a.sock) (hQ : QPres QA P) (hL : LocalStable Inv)
    (hres : ResOKQ QS P Inv res) (hgo : GoOKQ QA P Inv n go)
    {fol : Noun} {sub : Anno} {seat mk : Option Noun} {bc df : Bool} {gs gs' : GenS M R} {out : FolOut}
    (hi : Inv gs) (hsub : QA sub) (h : folStep env res go fol sub seat mk bc df gs = some (out, gs')) :
    Inv gs' ∧ ∀ γ, FolR P (n + 1) fol sub mk bc df (gs.at γ) out gs'.gen := by
  cases hs : shape fol with
  | cons a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨l, g1⟩, h1, ⟨r, g2⟩, h2, rfl, rfl⟩ := h
    have i1 := (hgo _ _ _ _ _ _ _ _ _ hi hsub h1).1
    refine ⟨(hgo _ _ _ _ _ _ _ _ _ i1 hsub h2).1, fun γ => ?_⟩
    refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (l, g1.at (γ + 1))),
        ((q, sub, mk, bc, df, g1.at (γ + 1)), (r, g2.at (γ + 2)))]) (g' := g2.at (γ + 2)) tabIn_none ?_ ?_ rfl
    · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hgo.ch hi hsub h1 _ _, hgo.ch i1 hsub h2 _ _⟩
    · simp only [SkaModel.folStep, hs]
      rw [goL_hd]; simp only [Option.bind_some]
      rw [goL_tl (by simp [GenS.at]), goL_hd]; rfl
  | op0 p =>
    simp only [folStep, hs, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨pr, hpr, rfl, rfl⟩ := h
    refine ⟨hi, fun γ => folR_of_calls (calls := []) (g' := gs.at γ) tabIn_none (by simp) ?_ rfl⟩
    simp only [SkaModel.folStep, hs, hpr, Option.map_some]
  | op1 p =>
    simp only [folStep, hs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hi, fun γ => folR_of_calls (calls := []) (g' := gs.at γ) tabIn_none (by simp)
      (by simp only [SkaModel.folStep, hs]) rfl⟩
  | op2 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff] at h
    obtain ⟨⟨s1, g1⟩, h1, ⟨f1, g2⟩, h2, h3⟩ := h
    dsimp only at h2 h3
    have i1 := (hgo _ _ _ _ _ _ _ _ _ hi hsub h1).1
    have ws1 : QA s1.prod := hQ n hsub ((hgo _ _ _ _ _ _ _ _ _ hi hsub h1).2 0)
    have i2 := (hgo _ _ _ _ _ _ _ _ _ i1 hsub h2).1
    have i2' : Inv ({ g2 with want := Ca.uni g2.want (distribute Cape.yes f1.prod.src) } : GenS M R) :=
      hL.app i2 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rcases callStep_cases h3 with ⟨el, eb, est, _, hc⟩ | ⟨fa, fb, i, g3, h4, rfl, hc⟩ | ⟨fa, fb, r, g3, h4, _, el, eb, est, _, hc⟩
    · refine ⟨hL.app i2 el eb (by rw [est]) (by rw [est]) (by rw [est]) (by rw [est]) (by rw [est])
        (by rw [est]) (by rw [est]) (by rw [est]), fun γ => ?_⟩
      refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (s1, g1.at (γ + 1))),
          ((q, sub, mk, bc, df, g1.at (γ + 1)), (f1, g2.at (γ + 2)))]) (g' := gs'.at (γ + 2)) tabIn_none ?_ ?_ rfl
      · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨hgo.ch hi hsub h1 _ _, hgo.ch i1 hsub h2 _ _⟩
      · simp only [SkaModel.folStep, hs]
        rw [goL_hd]; simp only [Option.bind_some]
        rw [goL_tl (by simp [GenS.at]), goL_hd]; simp only [Option.bind_some]
        exact hc _ _ _
    · have i3 := (hgo _ _ _ _ _ _ _ _ _ i2' ws1 h4).1
      refine ⟨i3, fun γ => ?_⟩
      refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (s1, g1.at (γ + 1))),
          ((q, sub, mk, bc, df, g1.at (γ + 1)), (f1, g2.at (γ + 2))),
          ((C fa fb, s1.prod, mk, bc, df,
            GenS.at ({ g2 with want := Ca.uni g2.want (distribute Cape.yes f1.prod.src) } : GenS M R) (γ + 2)),
            (i, gs'.at (γ + 3)))]) (g' := gs'.at (γ + 3)) tabIn_none ?_ ?_ rfl
      · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨hgo.ch hi hsub h1 _ _, hgo.ch i1 hsub h2 _ _,
          hgo.ch i2' ws1 h4 _ _⟩
      · simp only [SkaModel.folStep, hs]
        rw [goL_hd]; simp only [Option.bind_some]
        rw [goL_tl (by simp [GenS.at]), goL_hd]; simp only [Option.bind_some]
        refine hc _ _ _ _ ?_
        rw [goL_tl (by simp [GenS.at]), goL_tl (by simp [GenS.at]), goL_hd]
    · obtain ⟨hp, i3, hg3⟩ := hres _ _ _ _ i2 (hAS _ ws1) h4
      refine ⟨hL.app i3 el eb (by rw [est]) (by rw [est]) (by rw [est]) (by rw [est]) (by rw [est])
        (by rw [est]) (by rw [est]) (by rw [est]), fun γ => ?_⟩
      refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (s1, g1.at (γ + 1))),
          ((q, sub, mk, bc, df, g1.at (γ + 1)), (f1, g2.at (γ + 2)))]) (g' := gs'.at (γ + 2))
          (tabIn_one hp) ?_ ?_ rfl
      · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨hgo.ch hi hsub h1 _ _, hgo.ch i1 hsub h2 _ _⟩
      · simp only [SkaModel.folStep, hs]
        rw [goL_hd]; simp only [Option.bind_some]
        rw [goL_tl (by simp [GenS.at]), goL_hd]; simp only [Option.bind_some]
        exact hc hg3 _ _
  | op3 a b =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, rfl, rfl⟩ := h
    refine ⟨(hgo _ _ _ _ _ _ _ _ _ hi hsub h1).1, fun γ => ?_⟩
    refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (p1, g1.at (γ + 1)))])
      (g' := g1.at (γ + 1)) tabIn_none (by simpa using hgo.ch hi hsub h1 _ _) ?_ rfl
    simp only [SkaModel.folStep, hs]
    rw [goL_hd]; rfl
  | op4 a b =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, rfl, rfl⟩ := h
    refine ⟨(hgo _ _ _ _ _ _ _ _ _ hi hsub h1).1, fun γ => ?_⟩
    refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (p1, g1.at (γ + 1)))])
      (g' := g1.at (γ + 1)) tabIn_none (by simpa using hgo.ch hi hsub h1 _ _) ?_ rfl
    simp only [SkaModel.folStep, hs]
    rw [goL_hd]; rfl
  | op5 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, rfl, rfl⟩ := h
    have i1 := (hgo _ _ _ _ _ _ _ _ _ hi hsub h1).1
    refine ⟨(hgo _ _ _ _ _ _ _ _ _ i1 hsub h2).1, fun γ => ?_⟩
    refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (p1, g1.at (γ + 1))),
        ((q, sub, mk, bc, df, g1.at (γ + 1)), (q1, g2.at (γ + 2)))]) (g' := g2.at (γ + 2)) tabIn_none ?_ ?_ rfl
    · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hgo.ch hi hsub h1 _ _, hgo.ch i1 hsub h2 _ _⟩
    · simp only [SkaModel.folStep, hs]
      rw [goL_hd]; simp only [Option.bind_some]
      rw [goL_tl (by simp [GenS.at]), goL_hd]; rfl
  | op6 a b q r =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, ⟨r1, g3⟩, h3, rfl, rfl⟩ := h
    have i1 := (hgo _ _ _ _ _ _ _ _ _ hi hsub h1).1
    have i2 := (hgo _ _ _ _ _ _ _ _ _ i1 hsub h2).1
    refine ⟨(hgo _ _ _ _ _ _ _ _ _ i2 hsub h3).1, fun γ => ?_⟩
    refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (p1, g1.at (γ + 1))),
        ((q, sub, mk, bc, df, g1.at (γ + 1)), (q1, g2.at (γ + 2))),
        ((r, sub, mk, bc, df, g2.at (γ + 2)), (r1, g3.at (γ + 3)))]) (g' := g3.at (γ + 3)) tabIn_none ?_ ?_ rfl
    · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hgo.ch hi hsub h1 _ _, hgo.ch i1 hsub h2 _ _, hgo.ch i2 hsub h3 _ _⟩
    · simp only [SkaModel.folStep, hs]
      rw [goL_hd]; simp only [Option.bind_some]
      rw [goL_tl (by simp [GenS.at]), goL_hd]; simp only [Option.bind_some]
      rw [goL_tl (by simp [GenS.at]), goL_tl (by simp [GenS.at]), goL_hd]; rfl
  | op7 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, rfl, rfl⟩ := h
    have i1 := (hgo _ _ _ _ _ _ _ _ _ hi hsub h1).1
    have wp1 : QA p1.prod := hQ n hsub ((hgo _ _ _ _ _ _ _ _ _ hi hsub h1).2 0)
    refine ⟨(hgo _ _ _ _ _ _ _ _ _ i1 wp1 h2).1, fun γ => ?_⟩
    refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (p1, g1.at (γ + 1))),
        ((q, p1.prod, mk, bc, df, g1.at (γ + 1)), (q1, g2.at (γ + 2)))]) (g' := g2.at (γ + 2)) tabIn_none ?_ ?_ rfl
    · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hgo.ch hi hsub h1 _ _, hgo.ch i1 wp1 h2 _ _⟩
    · simp only [SkaModel.folStep, hs]
      rw [goL_hd]; simp only [Option.bind_some]
      rw [goL_tl (by simp [GenS.at]), goL_hd]; rfl
  | op8 a b q =>
    simp only [folStep, hs] at h
    refine ⟨(hgo _ _ _ _ _ _ _ _ _ hi hsub h).1, fun γ => ?_⟩
    refine folR_of_calls (calls := [((n3 (A 7) (C (C a b) (slot 1)) q, sub, mk, bc, df, gs.at γ),
        (out, gs'.at (γ + 1)))]) (g' := gs'.at (γ + 1)) tabIn_none (by simpa using hgo.ch hi hsub h _ _) ?_ rfl
    simp only [SkaModel.folStep, hs]
    rw [goL_hd]
  | op9 p a b =>
    simp only [folStep, hs] at h
    refine ⟨(hgo _ _ _ _ _ _ _ _ _ hi hsub h).1, fun γ => ?_⟩
    refine folR_of_calls (calls := [((n3 (A 7) (C a b) (n3 (A 2) (slot 1) (slot p)), sub, mk, bc, df, gs.at γ),
        (out, gs'.at (γ + 1)))]) (g' := gs'.at (γ + 1)) tabIn_none (by simpa using hgo.ch hi hsub h _ _) ?_ rfl
    simp only [SkaModel.folStep, hs]
    rw [goL_hd]
  | op10 ax don r1 r2 =>
    simp only [folStep, hs] at h
    split at h
    · rename_i hx
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨hi, fun γ => folR_of_calls (calls := []) (g' := gs.at γ) tabIn_none (by simp) ?_ rfl⟩
      simp only [SkaModel.folStep, hs, if_pos hx]
    · rename_i hx
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨⟨dn, g1⟩, h1, ⟨rc, g2⟩, h2, s', hd, rfl, rfl⟩ := h
      have i1 := (hgo _ _ _ _ _ _ _ _ _ hi hsub h1).1
      refine ⟨(hgo _ _ _ _ _ _ _ _ _ i1 hsub h2).1, fun γ => ?_⟩
      refine folR_of_calls (calls := [((don, sub, mk, bc, df, gs.at γ), (dn, g1.at (γ + 1))),
          ((C r1 r2, sub, mk, bc, df, g1.at (γ + 1)), (rc, g2.at (γ + 2)))]) (g' := g2.at (γ + 2))
          tabIn_none ?_ ?_ rfl
      · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨hgo.ch hi hsub h1 _ _, hgo.ch i1 hsub h2 _ _⟩
      · simp only [SkaModel.folStep, hs, if_neg hx]
        rw [goL_hd]; simp only [Option.bind_some]
        rw [goL_tl (by simp [GenS.at]), goL_hd]; simp only [Option.bind_some, hd, Option.map_some]
  | op11s p a b =>
    simp only [folStep, hs] at h
    split at h
    · rename_i hp
      refine ⟨(hgo _ _ _ _ _ _ _ _ _ hi hsub h).1, fun γ => ?_⟩
      refine folR_of_calls (calls := [((n3 (A 2) (slot 1) (quote (C (A 11) (C (A p) (C a b)))), sub, mk, true,
          df, gs.at γ), (out, gs'.at (γ + 1)))]) (g' := gs'.at (γ + 1)) tabIn_none
          (by simpa using hgo.ch hi hsub h _ _) ?_ rfl
      simp only [SkaModel.folStep, hs, if_pos hp]
      rw [goL_hd]
    · rename_i hp
      simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨q1, g1⟩, h1, rfl, rfl⟩ := h
      refine ⟨(hgo _ _ _ _ _ _ _ _ _ hi hsub h1).1, fun γ => ?_⟩
      refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (q1, g1.at (γ + 1)))])
        (g' := g1.at (γ + 1)) tabIn_none (by simpa using hgo.ch hi hsub h1 _ _) ?_ rfl
      simp only [SkaModel.folStep, hs, if_neg hp]
      rw [goL_hd]; rfl
  | op11d tag h1 h2 f =>
    simp only [folStep, hs, Option.bind_eq_some_iff] at h
    obtain ⟨⟨hh, g1⟩, e1, h⟩ := h
    have i0 := spotHint_inv hL env tag h1 h2 seat hi
    have hat0 : ∀ γ, (spotHint env tag h1 h2 seat gs).2.at γ = gs.at γ :=
      fun γ => GenS.at_eq (spotHint_gen env tag h1 h2 seat gs) γ
    have i1 := (hgo _ _ _ _ _ _ _ _ _ i0 hsub e1).1
    have whh : QA hh.prod := hQ n hsub ((hgo _ _ _ _ _ _ _ _ _ i0 hsub e1).2 0)
    have F1 : ∀ γ γ', FolR P n (C h1 h2) sub mk bc df (gs.at γ) hh (g1.at γ') := fun γ γ' => by
      rw [← hat0 γ]; exact hgo.ch i0 hsub e1 _ _
    split at h
    · rename_i hc
      refine ⟨(hgo _ _ _ _ _ _ _ _ _ i1 hsub h).1, fun γ => ?_⟩
      refine folR_of_calls (calls := [((C h1 h2, sub, mk, bc, df, gs.at γ), (hh, g1.at (γ + 1))),
          ((n3 (A 2) (slot 1) (quote f), sub, some hh.prod.sock.data, bc, df, g1.at (γ + 1)),
            (out, gs'.at (γ + 2)))]) (g' := gs'.at (γ + 2)) tabIn_none ?_ ?_ rfl
      · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨F1 _ _, hgo.ch i1 hsub h _ _⟩
      · simp only [SkaModel.folStep, hs]
        rw [goL_hd]; simp only [Option.bind_some]
        rw [if_pos hc, goL_tl (by simp [GenS.at]), goL_hd]
    · rename_i hc
      simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨arm, g2⟩, harm, ⟨fr, g3⟩, h3, g4, h4, rfl, rfl⟩ := h
      have iA : Inv g2 := by
        rcases meanArm_cases harm with ⟨rfl, _⟩ | ⟨cg, hcg, rfl, _⟩
        · exact i1
        · exact (hgo _ _ _ _ _ _ _ _ _ i1 whh hcg).1
      obtain ⟨i4, hg4⟩ := fastHint_inv hL ((hgo _ _ _ _ _ _ _ _ _ iA hsub h3).1) h4
      refine ⟨i4, fun γ => ?_⟩
      rcases meanArm_cases harm with ⟨rfl, hm⟩ | ⟨cg, hcg, rfl, hm⟩
      · refine folR_of_calls (calls := [((C h1 h2, sub, mk, bc, df, gs.at γ), (hh, g2.at (γ + 1))),
            ((f, sub, mk, bc, df, g2.at (γ + 1)), (fr, g3.at (γ + 2)))]) (g' := g3.at (γ + 2)) tabIn_none ?_ ?_
            (by rw [GenS.at_erase, hg4])
        · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
          exact ⟨F1 _ _, hgo.ch i1 hsub h3 _ _⟩
        · simp only [SkaModel.folStep, hs]
          rw [goL_hd]; simp only [Option.bind_some]
          rw [if_neg hc, hm]; simp only [Option.bind_some]
          rw [goL_tl (by simp [GenS.at]), goL_hd]; rfl
      · have icg := (hgo _ _ _ _ _ _ _ _ _ i1 whh hcg).1
        refine folR_of_calls (calls := [((C h1 h2, sub, mk, bc, df, gs.at γ), (hh, g1.at (γ + 1))),
            ((n3 (A 2) (slot 1) (slot 2), hh.prod, mk, bc, true, g1.at (γ + 1)), (cg.1, cg.2.at (γ + 2))),
            ((f, sub, mk, bc, df, cg.2.at (γ + 2)), (fr, g3.at (γ + 3)))]) (g' := g3.at (γ + 3)) tabIn_none ?_ ?_
            (by rw [GenS.at_erase, hg4])
        · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
          exact ⟨F1 _ _, hgo.ch i1 whh hcg _ _, hgo.ch icg hsub h3 _ _⟩
        · simp only [SkaModel.folStep, hs]
          rw [goL_hd]; simp only [Option.bind_some]
          rw [if_neg hc, hm _ _ _ (by rw [goL_tl (by simp [GenS.at]), goL_hd])]
          simp only [Option.bind_some]
          rw [goL_tl (by simp [GenS.at]), goL_tl (by simp [GenS.at]), goL_hd]; rfl
  | op11c x y h1 h2 f =>
    simp only [folStep, hs] at h
    refine ⟨(hgo _ _ _ _ _ _ _ _ _ hi hsub h).1, fun γ => ?_⟩
    refine folR_of_calls (calls := [((C (A 11) (C (C (A 0) (C h1 h2)) f), sub, mk, bc, df, gs.at γ),
        (out, gs'.at (γ + 1)))]) (g' := gs'.at (γ + 1)) tabIn_none (by simpa using hgo.ch hi hsub h _ _) ?_ rfl
    simp only [SkaModel.folStep, hs]
    rw [goL_hd]
  | op12 a b q =>
    simp only [folStep, hs, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨p1, g1⟩, h1, ⟨q1, g2⟩, h2, rfl, rfl⟩ := h
    have i1 := (hgo _ _ _ _ _ _ _ _ _ hi hsub h1).1
    refine ⟨(hgo _ _ _ _ _ _ _ _ _ i1 hsub h2).1, fun γ => ?_⟩
    refine folR_of_calls (calls := [((C a b, sub, mk, bc, df, gs.at γ), (p1, g1.at (γ + 1))),
        ((q, sub, mk, bc, df, g1.at (γ + 1)), (q1, g2.at (γ + 2)))]) (g' := g2.at (γ + 2)) tabIn_none ?_ ?_ rfl
    · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hgo.ch hi hsub h1 _ _, hgo.ch i1 hsub h2 _ _⟩
    · simp only [SkaModel.folStep, hs]
      rw [goL_hd]; simp only [Option.bind_some]
      rw [goL_tl (by simp [GenS.at]), goL_hd]; rfl
  | other =>
    simp only [folStep, hs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hi, fun γ => folR_of_calls (calls := []) (g' := gs.at γ) tabIn_none (by simp)
      (by simp only [SkaModel.folStep, hs]) rfl⟩


end StepQ

section RunQ

variable {P : Sock → Noun → TabEntry → Prop} {QA : Anno → Prop} {QS : Sock → Prop}

/-- **The state-passing `fol-loop` is in `FolR P`**, for an invariant `Inv`
that `resolve` keeps with answers in `P` at every fuel below `n`. -/
theorem folLoop_goOKQ {Inv : GenS M R → Prop} (env : Env R) (memoF : Memo M)
    (hAS : ∀ a, QA a → QS a.sock) (hQ : QPres QA P) (hL : LocalStable Inv) :
    ∀ n, (∀ k, k < n → ResOKQ QS P Inv (resolveR env memoF k)) → GoOKQ QA P Inv n (folLoop env memoF n)
  | 0 => fun _ _ _ _ _ _ _ _ _ _ _ _ h => by rw [folLoop_zero] at h; cases h
  | n + 1 => fun hres _ _ _ _ _ _ _ _ _ hi hs h => by
    rw [folLoop_succ] at h
    exact bridge_stepQ env hAS hQ hL (hres n (Nat.lt_succ_self n))
      (folLoop_goOKQ env memoF hAS hQ hL n (fun k hk => hres k (Nat.lt_succ_of_lt hk))) hi hs h

/-- **The run of `+run` on `id` is a run with answers in `P`.** -/
theorem run_folTopRQ {Inv : GenS M R → Prop} (env : Env R) (memoF : Memo M)
    (hAS : ∀ a, QA a → QS a.sock) (hQ : QPres QA P) (hL : LocalStable Inv) {n index : Nat}
    (hres : ∀ k, k < n → ResOKQ QS P Inv (resolveR env memoF k)) {id : Ident} {st : SkaState M R}
    {out : FolOut} {gs' : GenS M R} (hi : Inv (genInit index st)) (hw : QA ⟨id.1, A 1⟩)
    (h : folLoop env memoF n id.2 ⟨id.1, A 1⟩ none none false false (genInit index st) = some (out, gs')) :
    Inv gs' ∧ FolTopR P n id.1 id.2 out gs'.gen := by
  obtain ⟨i', F⟩ := folLoop_goOKQ env memoF hAS hQ hL n hres _ _ _ _ _ _ _ _ _ hi hw h
  exact ⟨i', F 0⟩

end RunQ

/-! ## 2. The tidy invariant of the state -/

/-- The memo's entries have a tidy `less-code` and product and a normal map. -/
def MemoTP (m : Memo M) : Prop :=
  ∀ f ms s e, Treap.get m f = some ms → Treap.get ms s = some e →
    Tidy e.2.less ∧ Tidy e.2.prod ∧ PiNorm e.2.map

theorem MemoTP.empty : MemoTP (Treap.empty : Memo M) := by
  intro f ms s e h; rw [Treap.get_empty] at h; cases h

theorem MemoTP.putMi {m : Memo M} (hm : MemoTP m) {i : Ident} {d : FDatum M}
    (hd : Tidy d.less ∧ Tidy d.prod ∧ PiNorm d.map) : MemoTP (putMi m i d) := by
  intro f ms s e h1 h2
  unfold Ana.putMi at h1
  rw [Treap.get_put] at h1
  split at h1
  · cases h1
    rw [Treap.get_put] at h2
    split at h2
    · cases h2; exact hd
    · unfold gutMi Treap.gut at h2
      rename_i hf _
      subst hf
      cases e' : Treap.get m i.2 with
      | none => rw [e'] at h2; simp [Treap.get_empty] at h2
      | some ms' => rw [e'] at h2; exact hm _ _ _ _ e' h2
  · exact hm _ _ _ _ h1 h2

/-- **A hit of `+git:mi` on a tidy memo at a tidy subject sock is tidy**: the
product is patched for the subject (`annoTP_patchProd`). -/
theorem gitMi_tp {m : Memo M} (hm : MemoTP m) {f : Noun} {s : Sock} {hit : Ident × FDatum M}
    (hs : Tidy s) (h : gitMi m f s = some (some hit)) : Tidy hit.2.less ∧ Tidy hit.2.prod ∧ PiNorm hit.2.map := by
  obtain ⟨k, d0, hk, _, hd⟩ := gitLoop_hit (i := hit.1) (d := hit.2) h
  rw [hd]
  have hk' : Treap.get (gutMi m f) k = some (hit.1, d0) := (Treap.mem_tap _ _ _).mp hk
  have hd0 : Tidy d0.less ∧ Tidy d0.prod ∧ PiNorm d0.map := by
    have hg' : Treap.get m f = some (gutMi m f) ∨ gutMi m f = Treap.empty := by
      unfold gutMi Treap.gut
      cases e : Treap.get m f <;> simp
    rcases hg' with hg' | hg'
    · exact hm f _ k _ hg' hk'
    · rw [hg', Treap.get_empty] at hk'; cases hk'
  have hp := annoTP_patchProd hs d0.map d0.prod ⟨hd0.2.1, hd0.2.2⟩
  exact ⟨hd0.1, hp.1, hp.2⟩

/-- **The tidy invariant**: the graph is `GraphTP` and the memo of the poke `MemoTP`. -/
structure TInv (st : SkaState M R) : Prop where
  g_tp : GraphTP (gCore st.g)
  done_tp : MemoTP st.done

theorem TInv.congr {st st' : SkaState M R} (h : TInv st) (h1 : st'.g = st.g) (h2 : st'.done = st.done) :
    TInv st' := ⟨by rw [h1]; exact h.g_tp, by rw [h2]; exact h.done_tp⟩

theorem TInv.init (reg : R) : TInv (SkaState.init reg : SkaState M R) := by
  refine ⟨?_, MemoTP.empty⟩
  intro i d h
  simp [gCore, SkaState.init, Treap.get_empty] at h

theorem TInv.mem {st : SkaState M R} (h : TInv st) {i : Ident} {d : FDatum M} (hd : Treap.get st.g i = some d) :
    Tidy i.1 ∧ Tidy d.less ∧ Tidy d.prod ∧ PiNorm d.map :=
  h.g_tp i d.core (by simp [gCore, hd])

theorem TInv.stk {st : SkaState M R} (hi : SInv st) (h : TInv st) {i : Ident} (hj : i ∈ st.stk) : Tidy i.1 := by
  obtain ⟨d, hd⟩ := hi.mem_g hj
  exact (h.mem hd).1

theorem TInv.gitG {st : SkaState M R} (h : TInv st) (i : Ident) :
    Tidy (gitG st.g i).less ∧ AnnoTP ⟨(gitG st.g i).prod, (gitG st.g i).map⟩ := by
  unfold Ana.gitG Treap.gut
  cases e : Treap.get st.g i with
  | none => exact ⟨tidy_dunno, tidy_void, trivial⟩
  | some d => obtain ⟨_, a, b, c⟩ := h.mem e; exact ⟨a, b, c⟩

theorem graphTP_sub {g g' : Graph} (hg : GraphTP g) (h : ∀ k d, g' k = some d → g k = some d) :
    GraphTP g' := fun k d hk => hg k d (h k d hk)

/-! ## The writes -/

theorem hit_tp {memoF : Memo M} (hmT : MemoTP memoF) {st : SkaState M R} (ht : TInv st) {id : Ident}
    {hit : Ident × FDatum M} (htd : Tidy id.1) (h : gitMi memoF id.2 id.1 = some (some hit)) :
    TInv { st with g := Treap.put st.g id hit.2, done := putMi st.done id hit.2 } := by
  obtain ⟨hl, hp, hm⟩ := gitMi_tp hmT htd h
  exact ⟨by show GraphTP (gCore (Treap.put st.g id hit.2)); rw [gCore_put]; exact graphTP_put ht.g_tp htd hl hp hm,
    ht.done_tp.putMi ⟨hl, hp, hm⟩⟩

theorem push_tp {st : SkaState M R} (ht : TInv st) {id : Ident} (htd : Tidy id.1) (index : Nat) :
    TInv { st with next := index + 1, order := Treap.put st.order id index, stk := id :: st.stk,
                   g := Treap.put st.g id FDatum.bunt } :=
  ⟨by show GraphTP (gCore (Treap.put st.g id FDatum.bunt)); rw [gCore_put, FDatum.bunt_core]
      exact graphTP_put ht.g_tp htd tidy_dunno tidy_void trivial, ht.done_tp⟩

theorem runEnd_gStepT {P : Sock → Noun → TabEntry → Prop} (hP : ∀ tab, TabIn P tab → TabTP tab)
    {n : Nat} {id : Ident} {data : FDatum M} {out : FolOut} {gs : GenS M R}
    (hF : FolTopR P n id.1 id.2 out gs.gen) (hold : gCore gs.st.g id = some data.core) :
    GStepT (gCore gs.st.g) (gCore (runEnd id data out gs).2.g) := by
  have e : gCore (runEnd id data out gs).2.g =
      Graph.put (gCore gs.st.g) id (runDatum (Treap.has gs.st.moved id) id.1 out gs.gen data.core).1 := by
    unfold runEnd
    simp only
    rw [gCore_put]
    split <;> rfl
  rw [e]
  exact GStepT.run hP hF hold

theorem runEnd_core (id : Ident) (data : FDatum M) (out : FolOut) (gs : GenS M R) :
    gCore (runEnd id data out gs).2.g =
      Graph.put (gCore gs.st.g) id (runDatum (Treap.has gs.st.moved id) id.1 out gs.gen data.core).1 := by
  unfold runEnd
  simp only
  rw [gCore_put]
  split <;> rfl

theorem runEnd_get (id : Ident) (data : FDatum M) (out : FolOut) (gs : GenS M R) :
    gCore (runEnd id data out gs).2.g id =
      some (runDatum (Treap.has gs.st.moved id) id.1 out gs.gen data.core).1 := by
  rw [runEnd_core]; simp [Graph.put]

theorem popGo_tp {id : Ident} : ∀ (l : List Ident) (st st' : SkaState M R),
    (∀ j ∈ l, ∃ d, Treap.get st.g j = some d) → TInv st → popGo id l st = some st' → TInv st'
  | [], _, _, _, _, h => by simp [popGo] at h
  | top :: rest, st, st', hl, ht, h => by
    unfold popGo at h
    simp only at h
    obtain ⟨d0, hd0⟩ := hl top List.mem_cons_self
    have hgit : gitG st.g top = d0 := by simp [gitG, Treap.gut, hd0]
    simp only [hgit] at h
    obtain ⟨h1, h2, h3, h4⟩ := ht.mem hd0
    let d' : FDatum M := if d0.prod = Sock.void then { d0 with prod := Sock.dunno } else d0
    have hd' : Tidy d'.less ∧ Tidy d'.prod ∧ PiNorm d'.map := by
      show Tidy (if d0.prod = Sock.void then { d0 with prod := Sock.dunno } else d0).less ∧
        Tidy (if d0.prod = Sock.void then { d0 with prod := Sock.dunno } else d0).prod ∧
        PiNorm (if d0.prod = Sock.void then { d0 with prod := Sock.dunno } else d0).map
      split
      · exact ⟨h2, tidy_dunno, h4⟩
      · exact ⟨h2, h3, h4⟩
    let st2 : SkaState M R :=
      { st with stk := rest, order := Treap.del st.order top, ticks := Treap.del st.ticks top,
                g := Treap.put st.g top d', done := putMi st.done top d' }
    have t2 : TInv st2 :=
      ⟨by show GraphTP (gCore (Treap.put st.g top d')); rw [gCore_put]
          exact graphTP_put ht.g_tp h1 hd'.1 hd'.2.1 hd'.2.2, ht.done_tp.putMi hd'⟩
    have hl2 : ∀ j ∈ rest, ∃ d, Treap.get st2.g j = some d := by
      intro j hj
      show ∃ d, Treap.get (Treap.put st.g top d') j = some d
      rw [Treap.get_put]
      split
      · exact ⟨_, rfl⟩
      · exact hl j (List.mem_cons_of_mem _ hj)
    by_cases e : top = id
    · rw [if_pos e] at h
      cases h
      exact t2
    · rw [if_neg e] at h
      exact popGo_tp rest st2 st' hl2 t2 h

theorem pop_tp {id : Ident} {st st' : SkaState M R} (hi : SInv st) (ht : TInv st) (h : pop id st = some st') :
    TInv st' :=
  popGo_tp st.stk st st' (fun _ hj => hi.mem_g hj) ht h

theorem cullFold_tp (l : List (Ident × Unit)) (st : SkaState M R) (ht : TInv st) :
    TInv (l.foldl cullStep st) := by
  obtain ⟨_, a2, _, a4, _⟩ := cullFold_ok l st
  refine ⟨graphTP_sub ht.g_tp (fun k d hk => ?_), by rw [a2]; exact ht.done_tp⟩
  simp only [gCore] at hk ⊢
  rw [a4] at hk
  split at hk
  · simp at hk
  · exact hk

theorem cull_tp {n : Nat} {id : Ident} {st st' : SkaState M R} (ht : TInv st) (h : cull n id st = some st') :
    TInv st' := by
  rw [cull_eq] at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨ab, _, live, _, hst⟩ := h
  split at hst
  · subst hst; exact ht
  · subst hst; exact cullFold_tp _ _ (ht.congr rfl rfl)

/-! ## The arms, by induction on the fuel -/

/-- The answers of `resolve`: well formed at a well-formed subject sock, tidy
at a tidy one. -/
def PWT : Sock → Noun → TabEntry → Prop := fun s _ a => (WellFormed s → WellFormed a.prod) ∧ (Tidy s → Tidy a.prod)

theorem pwt_wf : ∀ tab, TabIn PWT tab → TabWF tab := fun _ ht s f a hs h => (ht s f a h).1 hs

theorem pwt_tp : ∀ tab, TabIn PWT tab → TabTP tab := fun _ ht s f a hs h => (ht s f a h).2 hs

/-- The subjects of the bridge: well formed, tidy, with a normal map. -/
def QAT : Anno → Prop := fun a => WellFormed a.sock ∧ AnnoTP a

/-- The subject socks `resolve` is asked at. -/
def QST : Sock → Prop := fun s => WellFormed s ∧ Tidy s

theorem qAS : ∀ a, QAT a → QST a.sock := fun _ h => ⟨h.1, h.2.1⟩

theorem qpres : QPres QAT PWT := fun n _ _ _ _ _ _ _ _ hs h =>
  ⟨folR_wf pwt_wf n hs.1 h, folR_tp pwt_tp n hs.2 h⟩

/-- What the `resolve` loop begun with `orig` keeps, for a tidy `orig`. -/
def ResPT (orig : Ident) (res : ResGo M R) : Prop :=
  ∀ idT gs r gs', WellFormed orig.1 → Tidy orig.1 → SInv gs.st → TInv gs.st → WellFormed idT.1 → Tidy idT.1 →
    res idT gs = some (r, gs') → TInv gs'.st ∧ Tidy r.2.prod

/-- What `resolve` keeps. -/
def ResPTop (res : ResGo M R) : Prop :=
  ∀ idT gs r gs', SInv gs.st → TInv gs.st → WellFormed idT.1 → Tidy idT.1 → res idT gs = some (r, gs') →
    TInv gs'.st ∧ Tidy r.2.prod

theorem resPTop_of_loop {resl : Ident → ResGo M R} (h : ∀ orig, ResPT orig (resl orig)) :
    ResPTop (fun i => resl i i) :=
  fun idT gs r gs' hi ht hw htd e => h idT idT gs r gs' hw htd hi ht hw htd e

/-- What `+analyze` keeps. -/
def AnaPT (ana : AnaGo M R) : Prop :=
  ∀ id st low st', SInv st → TInv st → WellFormed id.1 → Tidy id.1 → Treap.get st.g id = none →
    ana id st = some (low, st') → TInv st'

/-- What `+run` keeps. -/
def RunPT (run : RunGo M R) : Prop :=
  ∀ id index st r st', SInv st → TInv st → id ∈ st.stk → run id index st = some (r, st') → TInv st'

/-- What the member loop keeps. -/
def MemPT (mem : MemGo M R) : Prop :=
  ∀ index pass ms st r st', SInv st → TInv st → mem index pass ms st = some (r, st') → TInv st'

/-- What the pass loop keeps. -/
def PassPT (pass : PassGo M R) : Prop :=
  ∀ id index p st low st' (ab0 rest : List Ident), SInv st → TInv st → st.stk = ab0 ++ id :: rest →
    pass id index p st = some (low, st') → TInv st'

/-- The invariant of a run of `fol-loop` begun in `st0`. -/
def RInvT (st0 : SkaState M R) (gs : GenS M R) : Prop := RInv st0 gs ∧ TInv gs.st

theorem rInvT_stable (st0 : SkaState M R) : LocalStable (RInvT (M := M) st0) := by
  intro gs gs' h a b e1 e2 e3 e4 c d f g'
  exact ⟨rInv_stable st0 gs gs' h.1 a b e1 e2 e3 e4 c d f g', h.2.congr e1 e2⟩

theorem resOKQ_of {res : ResGo M R} (h : ResP res) (hT : ResPTop res) (st0 : SkaState M R) :
    ResOKQ QST PWT (RInvT st0) res := by
  intro idT gs r gs' hi hw e
  obtain ⟨⟨i1, s1, k1⟩, t1⟩ := hi
  obtain ⟨i2, s2, k2, g2, w2⟩ := h idT gs r gs' i1 hw.1 e
  obtain ⟨t2, p2⟩ := hT idT gs r gs' i1 t1 hw.1 hw.2 e
  refine ⟨⟨fun _ => w2, fun _ => p2⟩, ⟨⟨i2, gStepsR_trans s1 s2, k1.trans (k2.weaken k1.1 (fun j hj => ?_))⟩, t2⟩, g2⟩
  obtain ⟨l, el⟩ := k1.1
  rw [el]; exact List.mem_append_right _ hj

theorem resolveStep_tp (env : Env R) {orig : Ident} {resolve : ResGo M R} {analyze : AnaGo M R}
    (hres : ResPT orig resolve) (hana : AnaPT analyze) : ResPT orig (resolveStep env resolve analyze orig) := by
  intro idT gs r gs' hwo hto hi ht hw htd e
  unfold resolveStep at e
  cases hg : Treap.get gs.st.g idT with
  | some d =>
    simp only [hg] at e
    have hp := (ht.mem hg).2.2.1
    cases ho : Treap.get gs.st.order idT with
    | none =>
      simp only [ho, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨ht, hp⟩
    | some o =>
      simp only [ho, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨ht, hp⟩
  | none =>
    rw [hg] at e
    simp only at e
    split at e
    · cases e
    · rename_i m hm
      cases e
      exact ⟨ht, (gitMi_tp ht.done_tp htd hm).2.1⟩
    · split at e
      · cases e
      · rename_i i hrc
        have hwi : WellFormed i.1 := by
          rcases recursiveCall_cases hrc with ⟨hb, _⟩ | ⟨_, j, hj, hm, _⟩
          · cases hb
          · exact wf_msgSock hw (hi.wf_stk hj) hm
        have hti : Tidy i.1 := by
          rcases recursiveCall_cases hrc with ⟨hb, _⟩ | ⟨_, j, hj, hm, _⟩
          · cases hb
          · exact tidy_msgSock htd (ht.stk hi hj) hm
        exact hres i gs r gs' hwo hto hi ht hwi hti e
      · rename_i i hrc
        simp only [Option.map_eq_some_iff] at e
        obtain ⟨o, _, e⟩ := e
        cases e
        refine ⟨ht, ?_⟩
        exact (annoTP_patchProd hto _ _ (ht.gitG i).2).1
      · simp only [Option.map_eq_some_iff] at e
        obtain ⟨⟨low, st'⟩, ha, e⟩ := e
        cases e
        have t' := hana idT gs.st low st' hi ht hw htd hg ha
        exact ⟨t', (t'.gitG idT).2.1⟩

theorem runStep_tp (env : Env R) (memoF : Memo M) {n : Nat}
    (hres : ∀ k, k < n → ResP (resolveR env memoF k)) (hresT : ∀ k, k < n → ResPTop (resolveR env memoF k)) :
    RunPT (runStep (folLoop env memoF n)) := by
  intro id index st r st' hi ht hid e
  unfold runStep at e
  simp only [Option.map_eq_some_iff] at e
  obtain ⟨⟨out, gs⟩, hf, e⟩ := e
  cases e
  let st0 : SkaState M R := { st with stats := { st.stats with runs := st.stats.runs + 1 } }
  have i0 : SInv st0 := hi.congr rfl rfl rfl rfl
  have r0 : RInvT st0 (genInit index st0) := ⟨⟨i0, GStepsR.refl _, Keep.refl' _ rfl rfl rfl⟩, ht.congr rfl rfl⟩
  obtain ⟨d0, hd0⟩ := hi.mem_g hid
  have hti := (ht.mem hd0).1
  obtain ⟨⟨⟨_, _, k1⟩, t1⟩, hF⟩ := run_folTopRQ env memoF qAS qpres (rInvT_stable st0)
    (fun k hk => resOKQ_of (hres k hk) (hresT k hk) st0) r0 ⟨hi.wf_stk hid, hti, trivial⟩ hf
  have hold : gCore gs.st.g id = some (gitG st0.g id).core := by
    have e1 : Treap.get gs.st.g id = Treap.get st0.g id := k1.2.2 id hid
    simp only [gCore, e1]
    show Option.map FDatum.core (Treap.get st.g id) = some (gitG st.g id).core
    simp [hd0, gitG, Treap.gut]
  have hstep := runEnd_gStepT pwt_tp hF hold
  obtain ⟨_, _, hd, _, _⟩ := runEnd_fields id (gitG st0.g id) out gs
  have hT : TInv (runEnd id (gitG st0.g id) out gs).2 := ⟨hstep.tp t1.g_tp, by rw [hd]; exact t1.done_tp⟩
  exact hT

theorem member_tailT {run : RunGo M R} {mem : MemGo M R} (hrun : RunP run) (hrunT : RunPT run)
    (hmemT : MemPT mem) {index pass : Nat} {m : Ident} {ms : List Ident} {st st1 st' : SkaState M R}
    {r : Nat × Bool} (hi : SInv st) (ht : TInv st) (h1 : st1.g = st.g) (h2 : st1.done = st.done)
    (h3 : st1.order = st.order) (h4 : st1.stk = st.stk)
    (e : ((Treap.get st.order m).bind fun o => (run m o st1).bind fun r =>
      if r.1.1 < index then some ((r.1.1, r.1.2.2), r.2) else
      (mem index pass ms r.2).map fun t => ((min r.1.1 t.1.1, r.1.2.2 || t.1.2), t.2)) = some (r, st')) :
    TInv st' := by
  simp only [Option.bind_eq_some_iff] at e
  obtain ⟨o, ho, ⟨r1, st2⟩, hr, e⟩ := e
  have i1 : SInv st1 := hi.congr h1 h2 h3 h4
  have t1 : TInv st1 := ht.congr h1 h2
  have hm1 : m ∈ st1.stk := (i1.ord_stk m).mp ⟨o, by rw [h3]; exact ho⟩
  have t2 := hrunT m o st1 r1 st2 i1 t1 hm1 hr
  split at e
  · simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨_, rfl⟩ := e
    exact t2
  · simp only [Option.map_eq_some_iff] at e
    obtain ⟨⟨t1', st3⟩, ht', e⟩ := e
    cases e
    exact hmemT index pass ms st2 t1' st3 (hrun m o st1 r1 st2 i1 hm1 hr).1 t2 ht'

theorem memberStep_tp {run : RunGo M R} {mem : MemGo M R} (hrun : RunP run) (hrunT : RunPT run)
    (hmemT : MemPT mem) : MemPT (memberStep run mem) := by
  intro index pass ms st r st' hi ht e
  cases ms with
  | nil =>
    simp only [memberStep, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨_, rfl⟩ := e
    exact ht
  | cons m ms =>
    simp only [memberStep] at e
    split at e
    · exact hmemT index pass ms st r st' hi ht e
    · by_cases hp : pass > 1
      · simp only [hp, if_true] at e
        exact member_tailT (st1 := { st with stats := { st.stats with lateRuns := st.stats.lateRuns + 1 } })
          hrun hrunT hmemT hi ht rfl rfl rfl rfl e
      · simp only [hp, if_false] at e
        exact member_tailT (st1 := st) hrun hrunT hmemT hi ht rfl rfl rfl rfl e

theorem passStep_tp {n : Nat} {mem : MemGo M R} {pass : PassGo M R} (hmem : MemP mem) (hmemT : MemPT mem)
    (hpassT : PassPT pass) : PassPT (passStep n mem pass) := by
  intro id index p st low st' ab0 rest hi ht hs e
  unfold passStep at e
  simp only [Option.bind_eq_some_iff] at e
  obtain ⟨ab, hab, members, hsw, e⟩ := e
  obtain ⟨ab0', rest', rfl, hs', _⟩ := above_eq hab
  obtain ⟨rfl, rfl⟩ := nodup_split_unique (hs ▸ hi.nodup) (hs.symm.trans hs')
  have hnd2 : ((ab0 ++ [id]) ++ rest).Nodup := by simpa using (hs ▸ hi.nodup)
  have hms : ∀ m ∈ members, ¬ (m ∈ rest) := by
    intro m hm hr
    have hm' : m ∈ ab0 ++ [id] := by
      rcases sweep_mem hsw m hm with rfl | h
      · simp
      · exact (Treap.has_silt _ _).mp h
    exact (List.nodup_append.mp hnd2).2.2 m hm' m hr rfl
  obtain ⟨⟨r1, st2⟩, hm, e⟩ := e
  have i1 : SInv ({ st with stats := { st.stats with passes := st.stats.passes + 1 } } : SkaState M R) :=
    hi.congr rfl rfl rfl rfl
  have t1 : TInv ({ st with stats := { st.stats with passes := st.stats.passes + 1 } } : SkaState M R) :=
    ht.congr rfl rfl
  obtain ⟨i2, _, k2⟩ := hmem index p members _ r1 st2 (id :: rest) (· ∈ rest) i1 ⟨ab0, hs⟩
    (fun j hj => List.mem_cons_of_mem _ hj) hms hm
  have t2 := hmemT index p members _ r1 st2 i1 t1 hm
  have K2 : Keep (id :: rest) (· ∈ rest) st st2 := k2
  simp only at e
  split at e
  · simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨_, rfl⟩ := e
    exact t2
  · simp only [Option.bind_eq_some_iff] at e
    obtain ⟨st3, hc, e⟩ := e
    obtain ⟨l2, el2⟩ := K2.1
    obtain ⟨i3, _, k3⟩ := cull_ok i2 hc el2
    have t3 := cull_tp t2 hc
    have K3 : Keep (id :: rest) (· ∈ rest) st st3 := K2.trans (k3.mono (fun j hj => List.mem_cons_of_mem _ hj))
    obtain ⟨l3, el3⟩ := K3.1
    split at e
    · simp only [Option.map_eq_some_iff] at e
      obtain ⟨st4, hp, e⟩ := e
      cases e
      exact pop_tp i3 t3 hp
    · exact hpassT id index (p + 1) st3 low st' l3 rest i3 t3 el3 e

theorem cullPass_tp {n : Nat} {pass : PassGo M R} (hpassT : PassPT pass) {id : Ident} {index : Nat}
    {st st' : SkaState M R} {low : Nat} {ab0 rest : List Ident} (hi : SInv st) (ht : TInv st)
    (hs : st.stk = ab0 ++ id :: rest) (h : cullPass n pass id index st = some (low, st')) : TInv st' := by
  unfold cullPass at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨st1, hc, h⟩ := h
  obtain ⟨i1, _, k1⟩ := cull_ok hi hc hs
  obtain ⟨l1, el1⟩ := k1.1
  exact hpassT id index 1 st1 low st' l1 rest i1 (cull_tp ht hc) el1 h

theorem analyzeStep_tp {n : Nat} {memoF : Memo M} (hmT : MemoTP memoF) {run : RunGo M R}
    {pass : PassGo M R} (hrun : RunP run) (hrunT : RunPT run) (hpassT : PassPT pass) :
    AnaPT (analyzeStep n memoF run pass) := by
  intro id st low st' hi ht hw htd hg e
  unfold analyzeStep at e
  split at e
  · cases e
  · rename_i hit hh
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨_, rfl⟩ := e
    exact hit_tp hmT ht htd hh
  · obtain ⟨i1, _, _⟩ := push_ok hi hw hg st.next
    have t1 := push_tp ht htd st.next
    simp only [Option.bind_eq_some_iff] at e
    obtain ⟨⟨r1, st2⟩, hr, e⟩ := e
    obtain ⟨i2, _, k2⟩ := hrun id st.next _ _ st2 i1 List.mem_cons_self hr
    have t2 := hrunT id st.next _ _ st2 i1 t1 List.mem_cons_self hr
    obtain ⟨l2, el2⟩ := k2.1
    have el2' : st2.stk = l2 ++ id :: st.stk := el2
    simp only at e
    split at e
    · simp only [Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨_, rfl⟩ := e
      exact t2
    · split at e
      · exact cullPass_tp hpassT i2 t2 el2' e
      · simp only [Option.bind_eq_some_iff] at e
        obtain ⟨ab, _, e⟩ := e
        split at e
        · exact cullPass_tp hpassT i2 t2 el2' e
        · simp only [Option.map_eq_some_iff] at e
          obtain ⟨st3, hp, e⟩ := e
          cases e
          exact pop_tp i2 t2 hp

/-- The arms at the fuel `n` keep the tidy invariant. -/
def AllPT (env : Env R) (memoF : Memo M) (n : Nat) : Prop :=
  (∀ orig, ResPT orig (resolve env memoF n orig)) ∧ AnaPT (analyze env memoF n) ∧ RunPT (run env memoF n) ∧
    PassPT (passLoop env memoF n) ∧ MemPT (memberLoop env memoF n)

theorem allPT_zero (env : Env R) (memoF : Memo M) : AllPT env memoF 0 := by
  refine ⟨fun _ _ _ _ _ _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ _ _ h => ?_,
    fun _ _ _ _ _ _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ _ _ h => ?_⟩
  · rw [resolve_zero] at h; cases h
  · rw [analyze_zero] at h; cases h
  · rw [run_zero] at h; cases h
  · rw [passLoop_zero] at h; cases h
  · rw [memberLoop_zero] at h; cases h

/-- **Every arm of the analysis keeps the tidy invariant** (`TInv`), at every
fuel, for a persistent memo with well-formed and tidy entries. -/
theorem allPT (env : Env R) (memoF : Memo M) (hmF : MemoWF memoF) (hmT : MemoTP memoF) :
    ∀ n, ∀ k, k ≤ n → AllPT env memoF k
  | 0 => fun k hk => by rw [Nat.le_zero.mp hk]; exact allPT_zero env memoF
  | n + 1 => fun k hk => by
    rcases Nat.lt_or_ge k (n + 1) with hl | hl
    · exact allPT env memoF hmF hmT n k (Nat.le_of_lt_succ hl)
    · have e : k = n + 1 := Nat.le_antisymm hk hl
      subst e
      obtain ⟨r, a, u, p, m⟩ := allPT env memoF hmF hmT n n (Nat.le_refl n)
      obtain ⟨_, _, u0, _, m0⟩ := allP env memoF hmF n n (Nat.le_refl n)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro orig; rw [resolve_succ]; exact resolveStep_tp env (r orig) a
      · rw [analyze_succ]; exact analyzeStep_tp hmT u0 u p
      · rw [run_succ]
        exact runStep_tp env memoF
          (fun k hk => resP_of_loop (resl := resolve env memoF k) (allP env memoF hmF n k (Nat.le_of_lt hk)).1)
          (fun k hk => resPTop_of_loop (resl := resolve env memoF k) (allPT env memoF hmF hmT n k (Nat.le_of_lt hk)).1)
      · rw [passLoop_succ]; exact passStep_tp m0 m p
      · rw [memberLoop_succ]; exact memberStep_tp u0 u m

/-! ## 3. `+ska-callgraph` -/

/-- **The graph of `+ska-callgraph` is `GraphTP`**: from a tidy root and a
persistent memo with well-formed and tidy entries. -/
theorem skaCallgraph_tp (env : Env R) (memoF : Memo M) (hmF : MemoWF memoF) (hmT : MemoTP memoF) {n : Nat}
    {root : Ident} {reg reg' : R} {g : Callgraph M} (hw : WellFormed root.1) (htd : Tidy root.1)
    (h : skaCallgraph env n root memoF reg = some (g, reg')) : GraphTP (gCore g) := by
  unfold skaCallgraph at h
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨low, st⟩, ha, rfl, _⟩ := h
  exact ((allPT env memoF hmF hmT n n (Nat.le_refl n)).2.1 root (SkaState.init reg) low st
    (SInv.init reg) (TInv.init reg) hw htd (by simp [SkaState.init, Treap.get_empty]) ha).g_tp

/-- **A run of `+run` in the analysis**: on a state with `SInv` and `TInv`, the
entry of `id` goes from `old` to `runDatum` of `old` and the run, and the graph
it was read from is `GraphTP`. -/
theorem run_entry (env : Env R) (memoF : Memo M) (n : Nat) {id : Ident} {index : Nat}
    {st st' : SkaState M R} {r : Nat × Bool × Bool} (hi : SInv st) (hid : id ∈ st.stk)
    (h : run env memoF n id index st = some (r, st')) :
    ∃ old moved out gen', gCore st.g id = some old ∧
      gCore st'.g id = some (runDatum moved id.1 out gen' old).1 := by
  cases n with
  | zero => rw [run_zero] at h; cases h
  | succ n =>
    rw [run_succ] at h
    unfold runStep at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨out, gs⟩, _, e⟩ := h
    cases e
    obtain ⟨d0, hd0⟩ := hi.mem_g hid
    have hgit : gitG ({ st with stats := { st.stats with runs := st.stats.runs + 1 } } : SkaState M R).g id = d0 := by
      simp [gitG, Treap.gut, hd0]
    refine ⟨d0.core, Treap.has gs.st.moved id, out, gs.gen, by simp [gCore, hd0], ?_⟩
    exact (runEnd_get id _ out gs).trans
      (congrArg (fun d : FDatum M => some (runDatum (Treap.has gs.st.moved id) id.1 out gs.gen d.core).1) hgit)

end Ana
end SkaModel
end Formalization
