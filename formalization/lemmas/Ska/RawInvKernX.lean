import lemmas.Ska.RawInvFinishX
import lemmas.Ska.CompWholeKern

/-!
# `+kern` over a lazy tree with forks: the raw facts of its prologues

README Gaps 14, the whole-subject pass on `FragX`.  `+kerf` emits a hop
block `o` and `+kern` walks the result's lazy tree (`+walk-lazy`: the
gate, then the forks, then the bonds), putting at each block the ops of
`+kern-need` that take the entry's sure need apart from one register
`sub` at `o`, and from a fresh proxy for `sub` at every other block.

* `wentries`: the entries in the order of `+walk-lazy` (forks before
  bonds), a permutation of `entries` (`wentries_perm`); `walkList`;
  **`walkLazy_flat`**: `+walk-lazy` is the gate at the root, then the gate
  at each entry in that order.
* `KI`: what the walk keeps (`SIP`, the keys of `cond` are proxies for
  `sub` above `sub`, no defined register is a key, `sub` is not defined,
  the entries still to do have a block and distinct sure needs below `sub`,
  apart from each other and not defined), and **`kernStep`**: one gate keeps
  `KI` and puts in front of the entry's block ops that define its sure need,
  read first only `sub` or a proxy for it, and leave the old keys alone.
* **`kernList_prep`**: the walk over a list of entries is a `Prep` that
  does this at every entry.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The order of `+walk-lazy` -/

mutual
/-- The entries of a lazy need in the order of `+walk-lazy`. -/
def wentries : Lazy S → List (Nat × Lazy S)
  | mk _ f b => wforkEntries f ++ wbondEntries b

def wbondEntries : List (Nat × Lazy S) → List (Nat × Lazy S)
  | [] => []
  | (o, l) :: rest => ((o, l) :: wentries l) ++ wbondEntries rest

def wforkEntries : List (ForkE S) → List (Nat × Lazy S)
  | [] => []
  | ((oy, y), (on, n)) :: rest => ((oy, y) :: wentries y) ++ ((on, n) :: wentries n) ++ wforkEntries rest
end

mutual
theorem wentries_perm : ∀ (l : Lazy S), (wentries l).Perm (entries l)
  | mk s f b => by
    simp only [wentries, entries]
    exact ((wforkEntries_perm f).append (wbondEntries_perm b)).trans List.perm_append_comm

theorem wbondEntries_perm : ∀ (b : List (Nat × Lazy S)), (wbondEntries b).Perm (bondEntries b)
  | [] => by simp [wbondEntries, bondEntries]
  | (o, l) :: rest => by
    simp only [wbondEntries, bondEntries]
    exact ((wentries_perm l).cons _).append (wbondEntries_perm rest)

theorem wforkEntries_perm : ∀ (f : List (ForkE S)), (wforkEntries f).Perm (forkEntries f)
  | [] => by simp [wforkEntries, forkEntries]
  | ((oy, y), (on, n)) :: rest => by
    simp only [wforkEntries, forkEntries]
    exact (((wentries_perm y).cons _).append ((wentries_perm n).cons _)).append (wforkEntries_perm rest)
end

/-- The gate at each entry, in order. -/
def walkList (f : Nat → Sure S → CM Map Unit) : List (Nat × Lazy S) → CM Map Unit
  | [] => pure ()
  | (o, l) :: rest => do
    f o l.sure
    walkList f rest

theorem walkList_append (f : Nat → Sure S → CM Map Unit) : ∀ (a b : List (Nat × Lazy S)),
    (walkList f (a ++ b) : CM Map Unit) = (do walkList f a; walkList f b)
  | [], b => by simp [walkList]
  | (o, l) :: rest, b => by
    simp only [List.cons_append, walkList, bind_assoc]
    rw [walkList_append f rest b]

mutual
/-- **`+walk-lazy` is the gate at the root, then at every entry.** -/
theorem walkLazy_flat (f : Nat → Sure S → CM Map Unit) : ∀ (o : Nat) (l : Lazy S),
    (walkLazy f o l : CM Map Unit) = (do f o l.sure; walkList f (wentries l))
  | o, mk s fk bd => by
    unfold walkLazy
    simp only [sure_mk, wentries]
    congr 1
    funext u
    split
    · rename_i hfb
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hfb
      obtain ⟨rfl, rfl⟩ := hfb
      simp [wbondEntries, wforkEntries, walkList]
    · rw [walkForks_flat f fk, walkBonds_flat f bd, walkList_append]

theorem walkBonds_flat (f : Nat → Sure S → CM Map Unit) : ∀ (b : List (Nat × Lazy S)),
    (walkBonds f b : CM Map Unit) = walkList f (wbondEntries b)
  | [] => by simp [walkBonds, wbondEntries, walkList]
  | (o, l) :: rest => by
    unfold walkBonds
    simp only [wbondEntries, List.cons_append, walkList]
    rw [walkLazy_flat f o l, walkBonds_flat f rest, walkList_append, bind_assoc]

theorem walkForks_flat (f : Nat → Sure S → CM Map Unit) : ∀ (fk : List (ForkE S)),
    (walkForks f fk : CM Map Unit) = walkList f (wforkEntries fk)
  | [] => by simp [walkForks, wforkEntries, walkList]
  | ((oy, y), (on, n)) :: rest => by
    unfold walkForks
    rw [walkLazy_flat f oy y, walkLazy_flat f on n, walkForks_flat f rest]
    simp only [wforkEntries, List.cons_append, List.append_assoc, walkList, walkList_append, bind_assoc]
end

/-! ## One gate of `+kern` -/

variable {X : Map Blob → Prop} [XOK X] {ρ : Nat → Nat} {lo : Nat}

theorem sip_of {g g' : Comp.Gen Map} (h : SIP X ρ lo g) (hb : g'.blocks = g.blocks) (hd : g'.drop = g.drop)
    (ho : g'.bo = g.bo) (hr : g.re ≤ g'.re) : SIP X ρ lo g' := by
  obtain ⟨d, b1, lab, regs, nd, cr, tr, jr, lob, rk, rlo, x⟩ := h
  refine ⟨by rw [hd]; exact d, by rw [ho]; exact b1, fun k b hk => ?_, fun k b hk => ?_, by rw [hb]; exact nd,
    by rw [hb]; exact cr, by rw [hb]; exact tr, by rw [hb]; exact jr, by rw [ho]; exact lob, rk, rlo,
    by rw [hb]; exact x⟩
  · rw [ho]; exact lab k b (by rw [← hb]; exact hk)
  · exact (regs k b (by rw [← hb]; exact hk)).mono fun x hx => Nat.lt_of_lt_of_le hx hr

/-- What the walk of `+kern` from the register `sub` keeps, with the
entries `rest` still to do. -/
def KI (X : Map Blob → Prop) (ρ : Nat → Nat) (lo : Nat) (sub : Nat) (rest : List (Nat × Lazy S))
    (g : Comp.Gen Map) : Prop :=
  SIP X ρ lo g ∧ sub < g.re ∧
    (∀ k v, HoonMap.get g.cond k = some v → sub < k ∧ k < g.re ∧ v.1 = sub) ∧
    (∀ r, Defd g.blocks r → HoonMap.get g.cond r = Option.none) ∧ ¬ Defd g.blocks sub ∧
    NeedsApart rest ∧ ∀ e ∈ rest, (∃ b, HoonMap.get g.blocks e.1 = some b) ∧ Distinct e.2.sure.ned ∧
      ∀ r, NMem e.2.sure.ned r → r < sub ∧ ¬ Defd g.blocks r

/-- What one gate does at the entry `(o, l)`. -/
def KStep (sub : Nat) (g g' : Comp.Gen Map) (o : Nat) (l : Lazy S) : Prop :=
  ∃ A, Prep (fun k => if k = o then A else []) g.blocks g'.blocks ∧ (∀ r, NMem l.sure.ned r → r ∈ defsOf A) ∧
    (∀ x, OpsRF A x → x = sub ∨ ∃ t, HoonMap.get g'.cond x = some (sub, t)) ∧
    ∀ k v, HoonMap.get g.cond k = some v → HoonMap.get g'.cond k = some v

theorem prep_same {o : Nat} {bl : Map Blob} : Prep (fun k => if k = o then [] else []) bl bl := by
  intro k
  cases HoonMap.get bl k <;> simp [pre]

/-- **One gate of `+kern` keeps `KI`.** -/
theorem kernStep {sub o oL : Nat} {l : Lazy S} {rest : List (Nat × Lazy S)} {g g' : Comp.Gen Map}
    (hI : KI X ρ lo sub ((oL, l) :: rest) g) (h : kernGate sub o oL l.sure g = some ((), g')) :
    KI X ρ lo sub rest g' ∧ KStep sub g g' oL l := by
  obtain ⟨S0, hsub, hc, hdc, hns, hap, he⟩ := hI
  obtain ⟨⟨b, hb⟩, dl, hl⟩ := he (oL, l) List.mem_cons_self
  have hap' := List.pairwise_cons.mp hap
  have dlt : ∀ r, Defd g.blocks r → r < g.re := fun r d => S0.defd_lt d
  unfold kernGate at h
  obtain ⟨ned, g1, h1, h2⟩ := bind_some h
  have L := sureRequireLook_spec h1
  obtain ⟨kk, e1⟩ := L.gen
  subst e1
  have lk : g.re ≤ kk := L.le
  have mN : ∀ y, NMem ned y → NMem l.sure.ned y ∨ (g.re ≤ y ∧ y < kk) := fun y hy => by
    rcases L.mem y hy with e | ⟨a, c⟩
    · exact Or.inl e
    · exact Or.inr ⟨a, c⟩
  have keep : ∀ y, NMem l.sure.ned y → NMem ned y := fun y hy => sureRequireLook_keeps h1 hy
  have restI : ∀ (g' : Comp.Gen Map), (∀ k, (∃ b, HoonMap.get g.blocks k = some b) → ∃ b, HoonMap.get g'.blocks k = some b) →
      (∀ r, Defd g'.blocks r → Defd g.blocks r ∨ (NMem l.sure.ned r ∨ g.re ≤ r)) →
      ∀ e ∈ rest, (∃ b, HoonMap.get g'.blocks e.1 = some b) ∧ Distinct e.2.sure.ned ∧
        ∀ r, NMem e.2.sure.ned r → r < sub ∧ ¬ Defd g'.blocks r := by
    intro g' hbk hdd e hm
    obtain ⟨hb', de, hle⟩ := he e (List.mem_cons_of_mem _ hm)
    refine ⟨hbk _ hb', de, fun r hr => ⟨(hle r hr).1, fun d => ?_⟩⟩
    rcases hdd r d with d | d | d
    · exact (hle r hr).2 d
    · exact hap'.1 e hm r d hr
    · have := (hle r hr).1; omega
  by_cases en : ned = Need.none
  · rw [if_pos en] at h2
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨-, rfl⟩ := h2
    refine ⟨⟨sip_reg S0 lk, by simp only; omega, fun k v hv => ?_, hdc, hns, hap'.2,
      restI _ (fun k h => h) (fun r d => Or.inl d)⟩, [], prep_same, fun r hr => ?_, fun x hx => hx.elim, fun k v hv => hv⟩
    · obtain ⟨a, c, d⟩ := hc k v hv; exact ⟨a, by simp only; omega, d⟩
    · have := keep r hr; rw [en] at this; exact this.elim
  rw [if_neg en] at h2
  obtain ⟨src, g2, hs, h3⟩ := bind_some h2
  -- the source: `sub` at `o`, a fresh proxy elsewhere
  have SRC : g2.blocks = g.blocks ∧ g2.drop = g.drop ∧ g2.bo = g.bo ∧
      ((src = sub ∧ g2.re = kk ∧ g2.cond = g.cond) ∨
       (src = kk ∧ g2.re = kk + 1 ∧ ∃ tag, ∀ k, HoonMap.get g2.cond k =
          if k = kk then some (sub, tag) else HoonMap.get g.cond k)) := by
    by_cases e : oL = o
    · rw [if_pos e] at hs
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      exact ⟨rfl, rfl, rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · rw [if_neg e] at hs
      unfold proxy at hs
      simp only [S0.drop, Bool.false_eq_true, if_false] at hs
      obtain ⟨tag, -, he'⟩ := Option.map_eq_some_iff.mp hs
      simp only [Prod.mk.injEq] at he'
      obtain ⟨rfl, rfl⟩ := he'
      exact ⟨rfl, S0.drop.symm, rfl, Or.inr ⟨rfl, rfl, tag, fun k => by simp [HoonMap.get_put]⟩⟩
  obtain ⟨hb2, hd2, hbo2, hsrc⟩ := SRC
  have l2 : kk ≤ g2.re := by rcases hsrc with ⟨-, e, -⟩ | ⟨-, e, -⟩ <;> omega
  -- the keys of `cond` after the source
  have c2 : ∀ k v, HoonMap.get g2.cond k = some v → HoonMap.get g.cond k = some v ∨ (k = kk ∧ src = kk ∧ v.1 = sub) := by
    intro k v hv
    rcases hsrc with ⟨-, -, ec⟩ | ⟨es, -, tag, ec⟩
    · rw [ec] at hv; exact Or.inl hv
    · rw [ec] at hv
      by_cases ek : k = kk
      · rw [if_pos ek] at hv; cases hv; exact Or.inr ⟨ek, es, rfl⟩
      · rw [if_neg ek] at hv; exact Or.inl hv
  have srcl : src < g2.re := by
    rcases hsrc with ⟨e, e', -⟩ | ⟨e, e', -⟩
    · omega
    · omega
  have nsrc : ¬ NMem ned src := fun hm => by
    rcases mN src hm with e | ⟨a, c⟩
    · have := (hl src e).1
      rcases hsrc with ⟨e', -⟩ | ⟨e', -⟩
      · omega
      · omega
    · rcases hsrc with ⟨e', -⟩ | ⟨e', -⟩
      · omega
      · omega
  rw [show noSoft oL = false from rfl] at h3
  simp only [Bool.false_eq_true, ↓reduceIte] at h3
  obtain ⟨ops, g3, h4, h5⟩ := bind_some h3
  have nb2 : NB g2.re ned := fun y hy => by
    rcases mN y hy with e | ⟨a, c⟩
    · have := (hl y e).1; omega
    · omega
  have dn : Distinct ned := L.dist dl (fun y hy => by have := (hl y hy).1; omega)
  obtain ⟨A, hA, K⟩ := kernLoop_raw ned src [] g2 g3 ops h4 srcl nsrc nb2 dn
  simp only [List.append_nil] at hA
  subst hA
  have e3 := K.gen
  have hb3 : g3.blocks = g.blocks := by rw [e3]; exact hb2
  have S3 : SIP X ρ lo g3 := sip_of S0 hb3 (by rw [e3]; exact hd2) (by rw [e3]; exact hbo2) (by have := K.le; omega)
  -- the definitions of the ops
  have dA : ∀ y ∈ defsOf ops, NMem l.sure.ned y ∨ (g.re ≤ y ∧ y < kk) ∨ (g2.re ≤ y ∧ y < g3.re) := fun y hy => by
    rcases K.defs y hy with e | e
    · rcases mN y e with e' | e'
      · exact Or.inl e'
      · exact Or.inr (Or.inl e')
    · exact Or.inr (Or.inr e)
  have P : OpsOK g3 ops := ⟨K.regs, K.nd, fun y hy d => by
      rw [hb3] at d
      have := dlt y d
      rcases dA y hy with e | e | e
      · exact (hl y e).2 d
      · omega
      · omega, K.tr⟩
  obtain ⟨S4, b4, hb4, e4, re4, bo4⟩ := sip_addOps S3 P h5
  rw [hb3, hb] at hb4
  cases hb4
  have cg : g'.cond = g2.cond := by
    obtain ⟨b5, -, e5⟩ := addOps_spec h5 S3.drop
    rw [e5]; simp only; rw [e3]
  have dd : ∀ y, Defd g'.blocks y ↔ Defd g.blocks y ∨ y ∈ defsOf ops := fun y => by
    rw [e4, hb3]; exact defd_prepend hb
  have hdd : ∀ r, Defd g'.blocks r → Defd g.blocks r ∨ (NMem l.sure.ned r ∨ g.re ≤ r) := fun r d => by
    rcases (dd r).mp d with d | d
    · exact Or.inl d
    · rcases dA r d with e | e | e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr e.1)
      · exact Or.inr (Or.inr (by omega))
  refine ⟨⟨S4, by have := K.le; omega, fun k v hv => ?_, fun r d => ?_, fun d => ?_, hap'.2,
    restI g' (fun k ⟨b', hk⟩ => ?_) hdd⟩, ops, ?_, fun r hr => K.cov r (keep r hr), fun x hx => ?_, fun k v hv => ?_⟩
  · rw [cg] at hv
    have := K.le
    rcases c2 k v hv with e | ⟨rfl, es, ev⟩
    · obtain ⟨a, c, d⟩ := hc k v e
      exact ⟨a, by omega, d⟩
    · refine ⟨by omega, ?_, ev⟩
      rcases hsrc with ⟨e1, -⟩ | ⟨-, e2, -⟩
      · omega
      · omega
  · rw [cg]
    cases ev : HoonMap.get g2.cond r with
    | none => rfl
    | some v =>
      exfalso
      rcases c2 r v ev with e | ⟨rfl, es, -⟩
      · rcases (dd r).mp d with d | d
        · rw [hdc r d] at e; cases e
        · obtain ⟨a, c, -⟩ := hc r v e
          rcases dA r d with e' | e' | e'
          · have := (hl r e').1; omega
          · omega
          · omega
      · rcases (dd r).mp d with d | d
        · have := dlt r d; omega
        · rcases dA r d with e' | e' | e'
          · have := (hl r e').1; omega
          · omega
          · rcases hsrc with ⟨e'', -⟩ | ⟨-, e'', -⟩
            · omega
            · omega
  · rcases (dd sub).mp d with d | d
    · exact hns d
    · rcases dA sub d with e | e | e
      · have := (hl sub e).1; omega
      · omega
      · omega
  · rw [e4, hb3, HoonMap.get_put]
    split
    · exact ⟨_, rfl⟩
    · exact ⟨b', hk⟩
  · rw [e4, hb3]; exact prep_put hb
  · rw [K.rf x hx, cg]
    rcases hsrc with ⟨rfl, -⟩ | ⟨rfl, -, tag, ec⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨tag, by rw [ec, if_pos rfl]⟩
  · rw [cg]
    rcases hsrc with ⟨-, -, ec⟩ | ⟨-, -, tag, ec⟩
    · rw [ec]; exact hv
    · rw [ec, if_neg]; exact hv
      intro e; subst e
      have := (hc k v hv).2.1; omega

/-! ## The walk over a list of entries -/

/-- What the walk over the entries `es` does. -/
def KMany (sub : Nat) (g g' : Comp.Gen Map) (es : List (Nat × Lazy S)) : Prop :=
  ∃ P, Prep P g.blocks g'.blocks ∧ (∀ e ∈ es, ∀ r, NMem e.2.sure.ned r → r ∈ defsOf (P e.1)) ∧
    (∀ k x, OpsRF (P k) x → x = sub ∨ ∃ t, HoonMap.get g'.cond x = some (sub, t)) ∧
    ∀ k v, HoonMap.get g.cond k = some v → HoonMap.get g'.cond k = some v

/-- **The walk of `+kern` over a list of entries.** -/
theorem kernList_prep (sub o : Nat) : ∀ (es : List (Nat × Lazy S)) (g g' : Comp.Gen Map),
    KI X ρ lo sub es g → walkList (kernGate sub o) es g = some ((), g') →
    KI (S := S) X ρ lo sub [] g' ∧ KMany sub g g' es
  | [], g, g', hI, h => by
    simp only [walkList, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact ⟨hI, fun _ => [], prep_nil _, fun e he => absurd he (List.not_mem_nil), fun _ _ h => h.elim,
      fun _ _ h => h⟩
  | (o', l) :: rest, g, g', hI, h => by
    simp only [walkList] at h
    obtain ⟨u, g1, h1, h2⟩ := bind_some h
    obtain ⟨I1, A, pA, kA, rA, cA⟩ := kernStep hI h1
    obtain ⟨I2, Q, pQ, kQ, rQ, cQ⟩ := kernList_prep sub o rest g1 g' I1 h2
    refine ⟨I2, _, prep_trans pA pQ, fun e he r hr => ?_, fun k r hr => ?_, fun k v hv => cQ k v (cA k v hv)⟩
    · rw [defsOf_append, List.mem_append]
      rcases List.mem_cons.mp he with rfl | he
      · exact Or.inr (by simp only [if_pos rfl]; exact kA r hr)
      · exact Or.inl (kQ e he r hr)
    · rcases opsRF_append.mp hr with h | ⟨-, h⟩
      · exact rQ k r h
      · by_cases e : k = o'
        · rw [if_pos e] at h
          rcases rA r h with e' | ⟨t, et⟩
          · exact Or.inl e'
          · exact Or.inr ⟨t, cQ _ _ et⟩
        · rw [if_neg e] at h; exact h.elim

end Raw
end SkaModel
end Formalization
