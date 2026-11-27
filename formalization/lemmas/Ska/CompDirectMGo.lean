import lemmas.Ska.CompDirectM
import lemmas.Ska.CompUnary
import lemmas.Ska.CompRun

/-!
# What the tree of `+mono-try-call` does

README Gaps 18 (track J, 2026-11-27).  The blocks `monoTryLoop fail ned r o`
emits, run by the interpreter model from registers where `r` holds `v`:
when `v` has the cells `ned` takes apart (`Fits ned v`), they reach the
block `o` (the optimistic call) with the registers of `ned` holding the
parts of `v` (`HoldsN ned`); otherwise they reach `fail` (the pessimistic
call).  Either way the registers below the loop's start that `ned` does not
name are as they were, the register `r` among them.

* `monoTryLoop_mono`: the loop keeps `drop`, the blocks below its start,
  and does not lower `re` or `bo`.
* `NDist`: the registers of a need are distinct.  `holdsN_frame`.
* `monoTry_go`: the run of the tree (by induction on the need).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {Map : Type → Type} [HoonMap Map]


theorem emitted_get_ne (g : Gen Map) (b : Blob) {k : Nat} (hk : k ≠ g.bo) :
    HoonMap.get (g.emitted b).blocks k = HoonMap.get g.blocks k := by
  unfold Gen.emitted
  cases g.drop <;> simp [HoonMap.get_put, hk]

theorem emitted_get_self (g : Gen Map) (b : Blob) (hd : g.drop = false) :
    HoonMap.get (g.emitted b).blocks g.bo = some b := by
  unfold Gen.emitted
  simp [hd, HoonMap.get_put]

/-- **The loop keeps `drop` and the blocks below its start.** -/
theorem monoTryLoop_mono {fail : Nat} : ∀ (ned : Need) (r o : Nat) (g g' : Gen Map) (o' : Nat),
    monoTryLoop fail ned r o g = some (o', g') →
    g'.drop = g.drop ∧ g.re ≤ g'.re ∧ g.bo ≤ g'.bo ∧
      ∀ k, k < g.bo → HoonMap.get g'.blocks k = HoonMap.get g.blocks k := by
  intro ned
  induction ned with
  | none =>
    intro r o g g' o' h
    simp only [monoTryLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl⟩
  | this rn =>
    intro r o g g' o' h
    simp only [monoTryLoop] at h
    split at h
    · exact absurd h (by simp [crashM])
    · rw [emit_apply] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, Nat.le_refl _, Nat.le_succ _, fun k hk => emitted_get_ne g _ (by omega)⟩
  | pair hn tn ihh iht =>
    intro r o g g' o' h
    simp only [monoTryLoop] at h
    obtain ⟨rt, ga, h1, h⟩ := bind_some h
    rw [re_apply] at h1; simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨rh, gb, h1, h⟩ := bind_some h
    rw [re_apply] at h1; simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨ot, g1, ht, h⟩ := bind_some h
    obtain ⟨oh, g2, hh, h⟩ := bind_some h
    obtain ⟨os, g3, he, h⟩ := bind_some h
    rw [emit_apply] at he h; simp only [Option.some.injEq, Prod.mk.injEq] at he h
    obtain ⟨rfl, rfl⟩ := he; obtain ⟨rfl, rfl⟩ := h
    obtain ⟨d1, r1, b1, k1⟩ := iht _ _ _ _ _ ht
    obtain ⟨d2, r2, b2, k2⟩ := ihh _ _ _ _ _ hh
    simp only at d1 r1 b1 k1
    refine ⟨by simp only [emitted_drop, d2, d1], by simp only [emitted_re]; omega,
      by simp only [emitted_bo]; omega, fun k hk => ?_⟩
    rw [emitted_get_ne _ _ (by simp only [emitted_bo]; omega), emitted_get_ne _ _ (by omega),
      k2 k (by omega), k1 k (by omega)]
  | both rn hn tn ihh iht =>
    intro r o g g' o' h
    simp only [monoTryLoop] at h
    obtain ⟨rt, ga, h1, h⟩ := bind_some h
    rw [re_apply] at h1; simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨rh, gb, h1, h⟩ := bind_some h
    rw [re_apply] at h1; simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨ot, g1, ht, h⟩ := bind_some h
    obtain ⟨oh, g2, hh, h⟩ := bind_some h
    split at h
    · exact absurd h (by simp [crashM])
    obtain ⟨os, g3, he, h⟩ := bind_some h
    rw [emit_apply] at he h; simp only [Option.some.injEq, Prod.mk.injEq] at he h
    obtain ⟨rfl, rfl⟩ := he; obtain ⟨rfl, rfl⟩ := h
    obtain ⟨d1, r1, b1, k1⟩ := iht _ _ _ _ _ ht
    obtain ⟨d2, r2, b2, k2⟩ := ihh _ _ _ _ _ hh
    simp only at d1 r1 b1 k1
    refine ⟨by simp only [emitted_drop, d2, d1], by simp only [emitted_re]; omega,
      by simp only [emitted_bo]; omega, fun k hk => ?_⟩
    rw [emitted_get_ne _ _ (by simp only [emitted_bo]; omega), emitted_get_ne _ _ (by omega),
      k2 k (by omega), k1 k (by omega)]

/-- The registers of a need are distinct. -/
def NDist : Need → Prop
  | Need.none => True
  | Need.this _ => True
  | Need.pair h t => NDist h ∧ NDist t ∧ ∀ x, NMem h x → ¬ NMem t x
  | Need.both rn h t => NDist h ∧ NDist t ∧ (∀ x, NMem h x → ¬ NMem t x) ∧ ¬ NMem h rn ∧ ¬ NMem t rn

/-- `HoldsN` reads only the registers of the need. -/
theorem holdsN_frame : ∀ (ned : Need) {R R' : Map (Option Noun)} {v : Noun}, HoldsN ned R v →
    (∀ x, NMem ned x → SkaModel.read x R' = SkaModel.read x R) → HoldsN ned R' v
  | Need.none, _, _, _, _, _ => trivial
  | Need.this r, _, _, _, h, hf => by
    simp only [HoldsN] at h ⊢; rw [hf r rfl]; exact h
  | Need.pair p q, _, _, Noun.cell _ _, h, hf =>
    ⟨holdsN_frame p h.1 (fun x hx => hf x (Or.inl hx)), holdsN_frame q h.2 (fun x hx => hf x (Or.inr hx))⟩
  | Need.pair _ _, _, _, Noun.atom _, h, _ => h.elim
  | Need.both r p q, _, _, Noun.cell _ _, h, hf =>
    ⟨by rw [hf r (Or.inl rfl)]; exact h.1, holdsN_frame p h.2.1 (fun x hx => hf x (Or.inr (Or.inl hx))),
      holdsN_frame q h.2.2 (fun x hx => hf x (Or.inr (Or.inr hx)))⟩
  | Need.both _ _ _, _, _, Noun.atom _, h, _ => h.elim

section Go

variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ}

theorem execBlob_hed_cons {regs : Map (Option Noun)} {t : Trace} {s d : Nat} {x y : Noun}
    (hs : SkaModel.read s regs = some (C x y)) (rest : List Pole) (fin : Termin) :
    execBlob lib O c gul st regs t ⟨[], Pole.hed s d :: rest, fin⟩ [] =
      execBlob lib O c gul st (store d x regs) t ⟨[], rest, fin⟩ [] := by
  rw [execBlob_cons]; simp [execPole, localPole, hs]

theorem execBlob_tal_cons {regs : Map (Option Noun)} {t : Trace} {s d : Nat} {x y : Noun}
    (hs : SkaModel.read s regs = some (C x y)) (rest : List Pole) (fin : Termin) :
    execBlob lib O c gul st regs t ⟨[], Pole.tal s d :: rest, fin⟩ [] =
      execBlob lib O c gul st (store d y regs) t ⟨[], rest, fin⟩ [] := by
  rw [execBlob_cons]; simp [execPole, localPole, hs]

theorem execBlob_mov_cons {regs regs' : Map (Option Noun)} {t : Trace} {s d : Nat}
    (hm : move s d regs = some regs') (rest : List Pole) (fin : Termin) :
    execBlob lib O c gul st regs t ⟨[], Pole.mov s d :: rest, fin⟩ [] =
      execBlob lib O c gul st regs' t ⟨[], rest, fin⟩ [] := by
  rw [execBlob_cons]; simp [execPole, localPole, hm]

theorem move_of_read {regs : Map (Option Noun)} {s : Nat} {v : Noun} (h : SkaModel.read s regs = some v) (d : Nat) :
    ∃ regs', move s d regs = some regs' := by
  unfold SkaModel.read at h
  unfold move
  cases e : HoonMap.get regs s with
  | none => rw [e] at h; simp at h
  | some u => exact ⟨_, rfl⟩

/-- **The run of the tree of `+mono-try-call`**: entered with `r` holding
`v`, it reaches `o` with `ned` holding `v` when `v` fits `ned`, and `fail`
otherwise, and keeps every register below the loop's start that `ned` does
not name. -/
theorem monoTry_go {fail : Nat} : ∀ (ned : Need) (r o : Nat) (g g' : Gen Map) (o' : Nat),
    monoTryLoop fail ned r o g = some (o', g') → g.drop = false →
    (∀ k, g.bo ≤ k → k < g'.bo → HoonMap.get c.blocks k = HoonMap.get g'.blocks k) →
    NDist ned → (∀ x, NMem ned x → x < g.re) → r < g.re → ¬ NMem ned r →
    ∀ (regs : Map (Option Noun)) (t : Trace) (v : Noun), SkaModel.read r regs = some v →
    ∃ regs', (∀ x, x < g.re → ¬ NMem ned x → SkaModel.read x regs' = SkaModel.read x regs) ∧
      ((Fits ned v ∧ HoldsN ned regs' v ∧
          goJ lib O c gul st regs t (jmp0 o') = goJ lib O c gul st regs' t (jmp0 o)) ∨
       (¬ Fits ned v ∧ goJ lib O c gul st regs t (jmp0 o') = goJ lib O c gul st regs' t (jmp0 fail))) := by
  intro ned
  induction ned with
  | none =>
    intro r o g g' o' h _ _ _ _ _ _ regs t v _
    simp only [monoTryLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨regs, fun _ _ _ => rfl, Or.inl ⟨trivial, trivial, rfl⟩⟩
  | this rn =>
    intro r o g g' o' h hd hc _ _ _ hr regs t v hv
    simp only [monoTryLoop] at h
    split at h
    · exact absurd h (by simp [crashM])
    rw [emit_apply] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hb : HoonMap.get c.blocks g.bo = some ⟨[], [Pole.mov r rn], Termin.hop (jmp0 o)⟩ := by
      rw [hc g.bo (Nat.le_refl _) (by simp only [emitted_bo]; omega), emitted_get_self _ _ hd]
    obtain ⟨regs', hm⟩ := move_of_read hv rn
    refine ⟨regs', fun x _ hx => ?_, Or.inl ⟨trivial, ?_, ?_⟩⟩
    · rw [read_move hm x, if_neg (show ¬ x = rn from hx)]
    · simp only [HoldsN]; rw [read_move hm rn, if_pos rfl]; exact hv
    · rw [goJ_jmp0 _ _ _ _ hb, execBlob_mov_cons hm, execBlob_hop]
  | pair hn tn ihh iht =>
    intro r o g g' o' h hd hc hdist hlt hrlt hr regs t v hv
    simp only [monoTryLoop] at h
    obtain ⟨rt, ga, h1, h⟩ := bind_some h
    rw [re_apply] at h1; simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨rh, gb, h1, h⟩ := bind_some h
    rw [re_apply] at h1; simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨ot, g1, ht, h⟩ := bind_some h
    obtain ⟨oh, g2, hh, h⟩ := bind_some h
    obtain ⟨os, g3, he, h⟩ := bind_some h
    rw [emit_apply] at he h; simp only [Option.some.injEq, Prod.mk.injEq] at he h
    obtain ⟨rfl, rfl⟩ := he; obtain ⟨rfl, rfl⟩ := h
    obtain ⟨d1, r1, b1, k1⟩ := monoTryLoop_mono _ _ _ _ _ _ ht
    obtain ⟨d2, r2, b2, k2⟩ := monoTryLoop_mono _ _ _ _ _ _ hh
    simp only at d1 r1 b1 k1
    obtain ⟨dh, dt, dht⟩ := hdist
    have hlh : ∀ x, NMem hn x → x < g.re := fun x hx => hlt x (Or.inl hx)
    have hlt' : ∀ x, NMem tn x → x < g.re := fun x hx => hlt x (Or.inr hx)
    have hd2 : g2.drop = false := by rw [d2, d1]; exact hd
    simp only [emitted_bo]
    have hcl : HoonMap.get c.blocks (g2.bo + 1) =
        some ⟨[], [], Termin.clq r (jmp0 g2.bo) (jmp0 fail)⟩ := by
      rw [hc (g2.bo + 1) (by omega) (by simp only [emitted_bo]; omega)]
      exact emitted_get_self _ _ (by simp only [emitted_drop, hd2])
    have hsp : HoonMap.get c.blocks g2.bo =
        some ⟨[], [Pole.hed r (g.re + 1), Pole.tal r g.re], Termin.hop (jmp0 oh)⟩ := by
      rw [hc g2.bo (by omega) (by simp only [emitted_bo]; omega),
        emitted_get_ne _ _ (by simp only [emitted_bo]; omega)]
      exact emitted_get_self _ _ hd2
    have hcH : ∀ k, g1.bo ≤ k → k < g2.bo → HoonMap.get c.blocks k = HoonMap.get g2.blocks k := fun k h1 h2 => by
      rw [hc k (by omega) (by simp only [emitted_bo]; omega), emitted_get_ne _ _ (by simp only [emitted_bo]; omega),
        emitted_get_ne _ _ (by omega)]
    have hcT : ∀ k, g.bo ≤ k → k < g1.bo → HoonMap.get c.blocks k = HoonMap.get g1.blocks k := fun k h1 h2 => by
      rw [hc k (by omega) (by simp only [emitted_bo]; omega), emitted_get_ne _ _ (by simp only [emitted_bo]; omega),
        emitted_get_ne _ _ (by omega), k2 k h2]
    cases v with
    | atom a =>
      refine ⟨regs, fun _ _ _ => rfl, Or.inr ⟨fun h => h.elim, ?_⟩⟩
      rw [goJ_jmp0 _ _ _ _ hcl, execBlob_clq, hv]
      rfl
    | cell vh vt =>
      have e1 : goJ lib O c gul st regs t (jmp0 (g2.bo + 1)) =
          goJ lib O c gul st (store g.re vt (store (g.re + 1) vh regs)) t (jmp0 oh) := by
        rw [goJ_jmp0 _ _ _ _ hcl, execBlob_clq, hv]
        show goJ lib O c gul st regs t (jmp0 g2.bo) = _
        rw [goJ_jmp0 _ _ _ _ hsp, execBlob_hed_cons hv,
          execBlob_tal_cons (by rw [read_store_ne (by omega)]; exact hv), execBlob_hop]
      have hrh : SkaModel.read (g.re + 1) (store g.re vt (store (g.re + 1) vh regs)) = some vh := by
        rw [read_store_ne (by omega), read_store_eq]
      obtain ⟨regs3, f3, c3⟩ := ihh (g.re + 1) ot g1 g2 oh hh (by rw [d1]; exact hd) hcH dh
        (fun x hx => by have := hlh x hx; omega) (by omega)
        (fun hx => by have := hlh _ hx; omega) _ t vh hrh
      have keep3 : ∀ x, x < g.re → ¬ NMem hn x → x ≠ g.re + 1 →
          SkaModel.read x regs3 = SkaModel.read x regs := fun x hx hn' _ => by
        rw [f3 x (by omega) hn', read_store_ne (by omega), read_store_ne (by omega)]
      rcases c3 with ⟨fh, hh3, gh⟩ | ⟨nfh, gh⟩
      · have hrt : SkaModel.read g.re regs3 = some vt := by
          rw [f3 g.re (by omega) (fun hx => by have := hlh _ hx; omega), read_store_eq]
        obtain ⟨regs4, f4, c4⟩ := iht g.re o _ g1 ot ht (by simp only; exact hd) hcT dt
          (fun x hx => by have := hlt' x hx; simp only; omega) (by simp only; omega)
          (fun hx => by have := hlt' _ hx; omega) regs3 t vt hrt
        have fr : ∀ x, x < g.re → ¬ NMem (Need.pair hn tn) x → SkaModel.read x regs4 = SkaModel.read x regs :=
          fun x hx hnm => by
            simp only [NMem, not_or] at hnm
            rw [f4 x (by simp only; omega) hnm.2, keep3 x hx hnm.1 (by omega)]
        rcases c4 with ⟨ft, ht4, gt⟩ | ⟨nft, gt⟩
        · refine ⟨regs4, fr, Or.inl ⟨⟨fh, ft⟩, ⟨holdsN_frame hn hh3 (fun x hx => f4 x (by have := hlh x hx; simp only; omega)
            (dht x hx)), ht4⟩, ?_⟩⟩
          rw [e1, gh, gt]
        · exact ⟨regs4, fr, Or.inr ⟨fun hf => nft hf.2, by rw [e1, gh, gt]⟩⟩
      · refine ⟨regs3, fun x hx hnm => ?_, Or.inr ⟨fun hf => nfh hf.1, by rw [e1, gh]⟩⟩
        simp only [NMem, not_or] at hnm
        exact keep3 x hx hnm.1 (by omega)
  | both rn hn tn ihh iht =>
    intro r o g g' o' h hd hc hdist hlt hrlt hr regs t v hv
    simp only [monoTryLoop] at h
    obtain ⟨rt, ga, h1, h⟩ := bind_some h
    rw [re_apply] at h1; simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨rh, gb, h1, h⟩ := bind_some h
    rw [re_apply] at h1; simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨ot, g1, ht, h⟩ := bind_some h
    obtain ⟨oh, g2, hh, h⟩ := bind_some h
    split at h
    · exact absurd h (by simp [crashM])
    rename_i hrn
    obtain ⟨os, g3, he, h⟩ := bind_some h
    rw [emit_apply] at he h; simp only [Option.some.injEq, Prod.mk.injEq] at he h
    obtain ⟨rfl, rfl⟩ := he; obtain ⟨rfl, rfl⟩ := h
    obtain ⟨d1, r1, b1, k1⟩ := monoTryLoop_mono _ _ _ _ _ _ ht
    obtain ⟨d2, r2, b2, k2⟩ := monoTryLoop_mono _ _ _ _ _ _ hh
    simp only at d1 r1 b1 k1
    obtain ⟨dh, dt, dht, dhr, dtr⟩ := hdist
    have hlh : ∀ x, NMem hn x → x < g.re := fun x hx => hlt x (Or.inr (Or.inl hx))
    have hlt' : ∀ x, NMem tn x → x < g.re := fun x hx => hlt x (Or.inr (Or.inr hx))
    have hrnl : rn < g.re := hlt rn (Or.inl rfl)
    have hd2 : g2.drop = false := by rw [d2, d1]; exact hd
    simp only [emitted_bo]
    have hcl : HoonMap.get c.blocks (g2.bo + 1) =
        some ⟨[], [], Termin.clq r (jmp0 g2.bo) (jmp0 fail)⟩ := by
      rw [hc (g2.bo + 1) (by omega) (by simp only [emitted_bo]; omega)]
      exact emitted_get_self _ _ (by simp only [emitted_drop, hd2])
    have hsp : HoonMap.get c.blocks g2.bo =
        some ⟨[], [Pole.hed r (g.re + 1), Pole.tal r g.re, Pole.mov r rn], Termin.hop (jmp0 oh)⟩ := by
      rw [hc g2.bo (by omega) (by simp only [emitted_bo]; omega),
        emitted_get_ne _ _ (by simp only [emitted_bo]; omega)]
      exact emitted_get_self _ _ hd2
    have hcH : ∀ k, g1.bo ≤ k → k < g2.bo → HoonMap.get c.blocks k = HoonMap.get g2.blocks k := fun k h1 h2 => by
      rw [hc k (by omega) (by simp only [emitted_bo]; omega), emitted_get_ne _ _ (by simp only [emitted_bo]; omega),
        emitted_get_ne _ _ (by omega)]
    have hcT : ∀ k, g.bo ≤ k → k < g1.bo → HoonMap.get c.blocks k = HoonMap.get g1.blocks k := fun k h1 h2 => by
      rw [hc k (by omega) (by simp only [emitted_bo]; omega), emitted_get_ne _ _ (by simp only [emitted_bo]; omega),
        emitted_get_ne _ _ (by omega), k2 k h2]
    cases v with
    | atom a =>
      refine ⟨regs, fun _ _ _ => rfl, Or.inr ⟨fun h => h.elim, ?_⟩⟩
      rw [goJ_jmp0 _ _ _ _ hcl, execBlob_clq, hv]
      rfl
    | cell vh vt =>
      have hr2 : SkaModel.read r (store g.re vt (store (g.re + 1) vh regs)) = some (C vh vt) := by
        rw [read_store_ne (by omega), read_store_ne (by omega)]; exact hv
      obtain ⟨regsM, hm⟩ := move_of_read hr2 rn
      have e1 : goJ lib O c gul st regs t (jmp0 (g2.bo + 1)) =
          goJ lib O c gul st regsM t (jmp0 oh) := by
        rw [goJ_jmp0 _ _ _ _ hcl, execBlob_clq, hv]
        show goJ lib O c gul st regs t (jmp0 g2.bo) = _
        rw [goJ_jmp0 _ _ _ _ hsp, execBlob_hed_cons hv,
          execBlob_tal_cons (by rw [read_store_ne (by omega)]; exact hv), execBlob_mov_cons hm, execBlob_hop]
      have hrh : SkaModel.read (g.re + 1) regsM = some vh := by
        rw [read_move hm, if_neg (by omega), read_store_ne (by omega), read_store_eq]
      obtain ⟨regs3, f3, c3⟩ := ihh (g.re + 1) ot g1 g2 oh hh (by rw [d1]; exact hd) hcH dh
        (fun x hx => by have := hlh x hx; omega) (by omega)
        (fun hx => by have := hlh _ hx; omega) _ t vh hrh
      have keep3 : ∀ x, x < g.re → ¬ NMem hn x → x ≠ rn →
          SkaModel.read x regs3 = SkaModel.read x regs := fun x hx hn' hxr => by
        rw [f3 x (by omega) hn', read_move hm, if_neg hxr, read_store_ne (by omega), read_store_ne (by omega)]
      rcases c3 with ⟨fh, hh3, gh⟩ | ⟨nfh, gh⟩
      · have hrt : SkaModel.read g.re regs3 = some vt := by
          rw [f3 g.re (by omega) (fun hx => by have := hlh _ hx; omega), read_move hm, if_neg (by omega), read_store_eq]
        obtain ⟨regs4, f4, c4⟩ := iht g.re o _ g1 ot ht (by simp only; exact hd) hcT dt
          (fun x hx => by have := hlt' x hx; simp only; omega) (by simp only; omega)
          (fun hx => by have := hlt' _ hx; omega) regs3 t vt hrt
        have fr : ∀ x, x < g.re → ¬ NMem (Need.both rn hn tn) x → SkaModel.read x regs4 = SkaModel.read x regs :=
          fun x hx hnm => by
            simp only [NMem, not_or] at hnm
            rw [f4 x (by simp only; omega) hnm.2.2, keep3 x hx hnm.2.1 hnm.1]
        rcases c4 with ⟨ft, ht4, gt⟩ | ⟨nft, gt⟩
        · have hrn4 : SkaModel.read rn regs4 = some (C vh vt) := by
            rw [f4 rn (by simp only; omega) dtr, f3 rn (by omega) dhr, read_move hm, if_pos rfl]; exact hr2
          refine ⟨regs4, fr, Or.inl ⟨⟨fh, ft⟩, ⟨hrn4, holdsN_frame hn hh3 (fun x hx => f4 x (by have := hlh x hx; simp only; omega)
            (dht x hx)), ht4⟩, ?_⟩⟩
          rw [e1, gh, gt]
        · exact ⟨regs4, fr, Or.inr ⟨fun hf => nft hf.2, by rw [e1, gh, gt]⟩⟩
      · refine ⟨regs3, fun x hx hnm => ?_, Or.inr ⟨fun hf => nfh hf.1, by rw [e1, gh]⟩⟩
        simp only [NMem, not_or] at hnm
        exact keep3 x hx hnm.2.1 hnm.1

end Go

end Comp
end SkaModel
end Formalization
