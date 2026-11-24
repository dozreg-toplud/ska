import lemmas.Ska.CompCallC
import lemmas.Ska.CompWholeKern

/-!
# `+kern` over a lazy tree with the registers its ops write

README Gaps 12.20.  `kern_spec` (`CompWholeKern.lean`) says what the ops of
`+kern` at each block of a lazy tree do (`KernP`: they fill the block's need
from the register `r`).  A goal with entries under a call (`+kerf` of the
indirect call) needs more: the ops keep the parent's registers, which lie
above everything the call allocated.  `KernPW` adds that the ops are ops of
`+kern-need` (`KOp`) whose registers are `r`, the need's, or the range the
walk allocated, so `runs_keep` keeps every other register.

* `KernPW`, `kernPW_mono`, `kernGate_okW` (`kernGate_ok` with the ops'
  registers, from `kernLoop_kop` and `kernLoop_lt`), `kern_specW`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **`KernP` with the registers of the ops**: ops of `+kern-need` whose
registers are `r`, the need's, or in the range `[lo, hi)`. -/
def KernPW (r : Nat) (cond : Map (Nat × List Nat)) (lo hi : Nat) (o : Nat) (sur : Sure S) (ops : List Pole) :
    Prop :=
  KernP r cond lo hi o sur ops ∧ (∀ p ∈ ops, KOp p) ∧
    RegsIn (fun x => x = r ∨ NMem sur.ned x ∨ (lo ≤ x ∧ x < hi)) ops

theorem kernPW_mono (r : Nat) : PMonoD (KernPW (S := S) (Map := Map) r) := by
  intro c c' lo hi lo' hi' o s A h hc hl hh
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨kernP_mono r c c' lo hi lo' hi' o s A h1 hc hl hh, h2, fun p hp x hx => ?_⟩
  rcases h3 p hp x hx with e | e | ⟨a, b⟩
  · exact Or.inl e
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr ⟨by omega, by omega⟩)

theorem kernGate_okW (r o : Nat) :
    GateOKDI (ProxyFor r) CondBelow (KernPW (S := S) (Map := Map) r) (kernGate (S := S) (Map := Map) r o) := by
  intro oL l g g' h hd hI
  unfold kernGate at h
  obtain ⟨ned, g1, h1, h2⟩ := bind_some h
  have L := sureRequireLook_spec h1
  obtain ⟨kk, e1⟩ := L.gen
  subst e1
  have pf1 : ProxyFor r g { g with re := kk } := ProxyFor.of_eq L.le rfl
  have nk : ∀ x, g.re ≤ x → HoonMap.get g.cond x = Option.none := fun x hx => by
    cases e : HoonMap.get g.cond x with
    | none => rfl
    | some _ => have := hI x (by simp [e]); omega
  have lk : g.re ≤ kk := L.le
  by_cases en : ned = Need.none
  · rw [if_pos en] at h2
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨-, rfl⟩ := h2
    subst en
    refine ⟨rfl, rfl, L.le, pf1, fun _ _ => rfl, fun e he => ?_⟩
    simp only [List.mem_singleton] at he
    subst he
    refine ⟨[], fun B fin hb => by simpa using hb, ⟨g.re, kk, Nat.le_refl _, Nat.le_refl _, r, Or.inl rfl,
      fun x hx _ _ => nk x hx, ?_⟩, fun p hp => absurd hp List.not_mem_nil, RegsIn.nil _⟩
    intro _ _ _ u _ _ _ lib σ O c gul st t R v _
    exact ⟨fun _ => ⟨R, Runs.nil R, holdsS_of_sure L trivial, fun _ _ _ => rfl⟩,
      fun nf => absurd ((fits_sure L v).mp trivial) nf⟩
  rw [if_neg en] at h2
  obtain ⟨src, g2, hs, h3⟩ := bind_some h2
  -- the source: `r` at the block `o`, a fresh proxy elsewhere
  have SRC : g2.blocks = g.blocks ∧ g2.drop = g.drop ∧ g2.bo = g.bo ∧ ProxyFor r { g with re := kk } g2 ∧
      kk ≤ g2.re ∧ g2.re ≤ kk + 1 ∧ (src = r ∨ (src = kk ∧ g2.re = kk + 1 ∧ unproxy g2.cond src = r)) ∧
      (∀ x, g.re ≤ x → x ≠ src → HoonMap.get g2.cond x = Option.none) := by
    obtain ⟨PF, hb2, hd2, hbo2, _, _⟩ := collSrc_spec hs hd
    by_cases e : oL = o
    · rw [if_pos e] at hs
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      exact ⟨rfl, rfl, rfl, PF, Nat.le_refl _, Nat.le_succ _, Or.inl rfl, fun x hx _ => nk x hx⟩
    · rw [if_neg e] at hs
      obtain ⟨ep, er, -, -, CF, hu⟩ := proxy_condFresh hs
      obtain ⟨tag, -, hu'⟩ := hu hd
      simp only at ep er
      refine ⟨hb2, hd2, hbo2, PF, by omega, by omega, Or.inr ⟨ep, er, hu'⟩, fun x hx hne => ?_⟩
      rcases CF.2 x with e' | ⟨a, b⟩
      · rw [e']; exact nk x hx
      · simp only at a b; exact absurd (by omega) hne
  obtain ⟨hb2, hd2, hbo2, PF, l2, u2, hsrc, kf2⟩ := SRC
  rw [show noSoft oL = false from rfl] at h3
  simp only [Bool.false_eq_true, ↓reduceIte] at h3
  obtain ⟨ops, g3, h4, h5⟩ := bind_some h3
  obtain ⟨A, hA, K⟩ := kernLoop_spec ned src [] g2 g3 ops h4
  simp only [List.append_nil] at hA
  subst hA
  obtain ⟨n, rfl⟩ := K.gen
  have l3 : g2.re ≤ n := K.le
  obtain ⟨b, hb, rfl⟩ := addOps_spec h5 (hd2.trans hd)
  refine ⟨hbo2, hd2, by simp only; omega,
    pf1.trans (PF.trans (ProxyFor.of_eq (g := g2) (by simp only; omega) rfl)), fun o' ho' => ?_, fun e he => ?_⟩
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at ho'
    simp only [HoonMap.get_put, if_neg ho']
    exact congrArg (fun m => HoonMap.get m o') hb2
  simp only [List.mem_singleton] at he
  subst he
  rw [hb2] at hb
  have kop : ∀ p ∈ ops, KOp p := kernLoop_kop ned src [] g2 _ ops h4 (fun p hp => absurd hp List.not_mem_nil)
  have rin : RegsIn (fun x => x = r ∨ NMem l.sure.ned x ∨ (g.re ≤ x ∧ x < n)) ops :=
    kernLoop_lt _ ned src [] g2 _ ops h4
      (by rcases hsrc with e | ⟨e, e', _⟩
          · exact Or.inl e
          · exact Or.inr (Or.inr ⟨by omega, by omega⟩))
      (fun x hx => by
        rcases L.mem x hx with h' | ⟨a, b⟩
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr ⟨a, by simp only at b; omega⟩))
      (fun x a b => Or.inr (Or.inr ⟨by omega, b⟩)) (RegsIn.nil _)
  refine ⟨ops, fun B fin hb' => ?_, ⟨g.re, n, Nat.le_refl _, Nat.le_refl _, src, ?_, ?_, ?_⟩, kop, rin⟩
  · rw [hb] at hb'
    cases hb'
    simp [HoonMap.get_put]
  · rcases hsrc with e | ⟨e, e', hu⟩
    · exact Or.inl e
    · exact Or.inr ⟨by omega, by omega, hu⟩
  · intro x a _ c
    exact kf2 x a c
  intro hrlo dist hlt u ur uS uc
  have kf : ∀ x, g.re ≤ x → x < n → x ≠ src → u x = x := fun x a b c => by
    rw [uc x b]; exact unproxy_none (kf2 x a c)
  have us : u src = r := by
    rcases hsrc with e | ⟨e, e', hu⟩
    · rw [e]; exact ur
    · rw [uc src (by omega)]; exact hu
  have srcl : src < g2.re := by
    rcases hsrc with e | ⟨e, e', _⟩
    · omega
    · omega
  have ut : ∀ x, NMem ned x → u x = x := fun x hx => by
    rcases L.mem x hx with h' | ⟨a, b⟩
    · exact uS x h'
    · simp only at b
      refine kf x a (by omega) fun e => ?_
      rcases hsrc with e' | ⟨e', _, _⟩
      · omega
      · omega
  have hnr : ¬ NMem ned r := fun hx => by
    rcases L.mem r hx with h' | ⟨a, _⟩
    · have := hlt r h'; omega
    · omega
  have e2 := kernLoop_ren h4 hnr (by omega) us ur ut (fun x a b => kf x (by omega) b (by omega))
  obtain ⟨A', hA', K'⟩ := kernLoop_spec ned r [] g2 _ _ e2
  simp only [List.append_nil] at hA'
  have dn : Distinct ned := L.dist dist (fun x hx => by have := hlt x hx; omega)
  have lt2 : ∀ x, NMem ned x → x < g2.re := fun x hx => by
    rcases L.mem x hx with h' | ⟨_, b⟩
    · have := hlt x h'; omega
    · simp only at b; omega
  have KS := K'.sem dn lt2
  intro lib σ O c gul st t R v hR
  obtain ⟨S1, S2⟩ := KS lib σ O c gul st t R v hR
  rw [hA']
  refine ⟨fun f => ?_, fun nf => S2 fun f => nf ((fits_sure L v).mp f)⟩
  obtain ⟨R', hr', hh, hk⟩ := S1 ((fits_sure L v).mpr f)
  exact ⟨R', hr', holdsS_of_sure L hh, fun x hx hn => hk x (by omega) fun hm => by
    rcases L.mem x hm with h' | ⟨a, _⟩
    · exact hn h'
    · omega⟩

/-- **`+kern` over the whole tree, with the ops' registers** (`kern_spec`
with `kernGate_okW`). -/
theorem kern_specW {o : Nat} {laz : Lazy S} {g g' : Gen Map} {r : Nat}
    (h : kern o laz g = some (r, g')) (hd : g.drop = false) (hI : CondBelow g)
    (hn : (((o, laz) :: entries laz).map Prod.fst).Nodup) :
    r = g.re ∧ WalkOKD (ProxyFor r) (KernPW (S := S) (Map := Map) r) { g with re := g.re + 1 } g'
      ((o, laz) :: entries laz) := by
  rw [kern_eq] at h
  obtain ⟨r', g1, h1, h⟩ := bind_some h
  rw [re_apply] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  obtain ⟨gg, g2, h2, h⟩ := bind_some h
  rw [get_apply] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  simp only at h
  rw [if_neg (show ¬ (g.drop = true) by simp [hd])] at h
  obtain ⟨u, g3, h3, h4⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨e, rfl⟩ := h4
  subst e
  have hI1 : CondBelow ({ g with re := g.re + 1 } : Gen Map) := fun k hk => by
    have := hI k hk; simp only; omega
  exact ⟨rfl, walkLazy_okDI (ProxyFor.refl g.re) (fun _ _ _ a b => ProxyFor.trans a b)
    (fun _ _ h _ hk => ProxyFor.get_lt h hk) (fun _ _ h hb => h.1.below hb) (kernPW_mono g.re)
    (kernGate_okW g.re o) o laz _ g3 h3 hd hI1 hn⟩

end Comp
end SkaModel
end Formalization
