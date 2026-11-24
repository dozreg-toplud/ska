import lemmas.Ska.CompUnproxyRegs

/-!
# The registers the fill ops of `+coerce-lazy` mention

The second piece of the register facts that `finishLF_compDoneU` needs
(README, Gaps 12.2): the ops `+coerce-lazy` puts in front of a block mention
only the input registers, the registers of the lazy need taken there and
registers allocated in the coercion.

* `sureLoop_regs`: the ops of `sure-loop` from `ned` into `tgt` mention only
  registers of `ned`, of `tgt` and registers at or above the start's `re`.
* `Front.uniq`: the ops `Front` puts in front of a block that exists are
  unique, so the `A` of `sureLoop_regs` is the `A` of `sureLoop_spec`.
* `coerceLazy_regs`: the ops of one coercion mention only registers of the
  input need `ned`, of the lazy need `laz.ned` and fresh registers (the
  target of `+sure-require-look` is made of `laz.ned` and fresh registers,
  `SureOK.mem`).
* `coerceList_regs`, `coerceLazyL_regs`: the same at every entry of a lazy
  tree with distinct labels.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The ops of `sure-loop` from `ned` into `tgt` mention only registers of
`ned`, of `tgt` and registers allocated in the loop.** -/
theorem sureLoop_regs (P : Nat → Prop) {o : Nat} : ∀ (ned tgt : Need) (g g' : Gen Map) (u : Unit),
    sureLoop o ned tgt g = some (u, g') → g.drop = false →
    (∀ x, NMem ned x → P x) → (∀ x, NMem tgt x → P x) → (∀ x, g.re ≤ x → P x) →
    ∃ A, Front o g g' A ∧ RegsIn P A := by
  intro ned
  induction ned with
  | none =>
    intro tgt g g' u h _ _ _ _
    simp only [sureLoop] at h
    by_cases e : tgt = Need.none
    · rw [if_pos e] at h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      exact ⟨[], Front.refl g, RegsIn.nil P⟩
    · rw [if_neg e] at h; cases h
  | this r =>
    intro tgt g g' u h hd hn ht hg
    simp only [sureLoop] at h
    obtain ⟨ops, g1, h1, h2⟩ := bind_some h
    have RR := kernLoop_regs P tgt r [] g g1 ops h1 (hn r rfl) ht hg (RegsIn.nil P)
    obtain ⟨A, rfl, K⟩ := kernLoop_spec tgt r [] g g1 ops h1
    obtain ⟨n, rfl⟩ := K.gen
    have F := (front_reg (o := o) g K.le).trans (front_addOps h2 hd)
    simp only [List.append_nil] at F RR
    exact ⟨A, F, RR⟩
  | pair p q ihp ihq =>
    intro tgt g g' u h hd hn ht hg
    cases tgt with
    | none =>
      simp only [sureLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      exact ⟨[], Front.refl g, RegsIn.nil P⟩
    | this _ => simp only [sureLoop] at h; cases h
    | both _ _ _ => simp only [sureLoop] at h; cases h
    | pair tp tq =>
      simp only [sureLoop] at h
      obtain ⟨_, g1, h1, h2⟩ := bind_some h
      obtain ⟨Ap, Fp, Rp⟩ := ihp tp g g1 _ h1 hd (fun x hx => hn x (Or.inl hx)) (fun x hx => ht x (Or.inl hx)) hg
      obtain ⟨Aq, Fq, Rq⟩ := ihq tq g1 g' _ h2 (Fp.drop.trans hd) (fun x hx => hn x (Or.inr hx))
        (fun x hx => ht x (Or.inr hx)) (fun x hx => hg x (Nat.le_trans Fp.le hx))
      exact ⟨Aq ++ Ap, Fp.trans Fq, Rq.append Rp⟩
  | both r h t ihh iht =>
    intro tgt g g' u hk hd hn ht hg
    cases tgt with
    | none =>
      simp only [sureLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨_, rfl⟩ := hk
      exact ⟨[], Front.refl g, RegsIn.nil P⟩
    | this d =>
      simp only [sureLoop] at hk
      by_cases e : r = d
      · rw [if_pos e] at hk; cases hk
      rw [if_neg e] at hk
      refine ⟨[Pole.mov r d], front_addOps hk hd, RegsIn.cons (p := Pole.mov r d) (fun x hx => ?_) (RegsIn.nil P)⟩
      simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with hx | hx
      · rw [hx]; exact hn r (Or.inl rfl)
      · rw [hx]; exact ht d rfl
    | pair tp tq =>
      simp only [sureLoop] at hk
      obtain ⟨_, g1, h1, h2⟩ := bind_some hk
      obtain ⟨Ap, Fp, Rp⟩ := ihh tp g g1 _ h1 hd (fun x hx => hn x (Or.inr (Or.inl hx)))
        (fun x hx => ht x (Or.inl hx)) hg
      obtain ⟨Aq, Fq, Rq⟩ := iht tq g1 g' _ h2 (Fp.drop.trans hd) (fun x hx => hn x (Or.inr (Or.inr hx)))
        (fun x hx => ht x (Or.inr hx)) (fun x hx => hg x (Nat.le_trans Fp.le hx))
      exact ⟨Aq ++ Ap, Fp.trans Fq, Rq.append Rp⟩
    | both d th tt =>
      simp only [sureLoop] at hk
      by_cases e : r = d
      · rw [if_pos e] at hk; cases hk
      rw [if_neg e] at hk
      obtain ⟨_, g1, h1, hk⟩ := bind_some hk
      have F0 := front_addOps h1 hd
      obtain ⟨_, g2, h2, h3⟩ := bind_some hk
      obtain ⟨Ah, Fh, Rh⟩ := ihh th _ g2 _ h2 (F0.drop.trans hd) (fun x hx => hn x (Or.inr (Or.inl hx)))
        (fun x hx => ht x (Or.inr (Or.inl hx))) (fun x hx => hg x (Nat.le_trans F0.le hx))
      obtain ⟨At, Ft, Rt⟩ := iht tt g2 g' _ h3 (Fh.drop.trans (F0.drop.trans hd))
        (fun x hx => hn x (Or.inr (Or.inr hx))) (fun x hx => ht x (Or.inr (Or.inr hx)))
        (fun x hx => hg x (Nat.le_trans (Nat.le_trans F0.le Fh.le) hx))
      refine ⟨At ++ (Ah ++ [Pole.mov r d]), (F0.trans Fh).trans Ft, Rt.append (Rh.append ?_)⟩
      refine RegsIn.cons (p := Pole.mov r d) (fun x hx => ?_) (RegsIn.nil P)
      simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with hx | hx
      · rw [hx]; exact hn r (Or.inl rfl)
      · rw [hx]; exact ht d (Or.inl rfl)

/-- **The ops in front of a block that exists are unique.** -/
theorem Front.uniq {o : Nat} {g g' : Gen Map} {A A' : List Pole} (F : Front o g g' A) (F' : Front o g g' A')
    {B : List Pole} {fin : Termin} (hb : HoonMap.get g.blocks o = some ⟨[], B, fin⟩) : A = A' := by
  have h1 := F.blk B fin hb
  rw [F'.blk B fin hb] at h1
  simp only [Option.some.injEq, Blob.mk.injEq, true_and] at h1
  exact (List.append_cancel_right h1.1).symm

/-- **The ops of one coercion mention only registers of the input need, of
the lazy need and fresh registers.** -/
theorem coerceLazy_regs {ned : Need} {o : Nat} {laz : Sure S} {less : Cape} {g g' : Gen Map}
    (h : coerceLazy ned o laz less g = some ((), g')) (hd : g.drop = false) :
    ∃ A, Front o g g' A ∧ RegsIn (fun x => NMem ned x ∨ NMem laz.ned x ∨ g.re ≤ x) A := by
  simp only [coerceLazy] at h
  obtain ⟨lok, g1, h1, h⟩ := bind_some h
  obtain ⟨l, _, e⟩ := Option.map_eq_some_iff.mp h1
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨tgt, g2, h2, h3⟩ := bind_some h
  have L := sureRequireLook_spec h2
  obtain ⟨k, rfl⟩ := L.gen
  obtain ⟨A, F, R⟩ := sureLoop_regs (fun x => NMem ned x ∨ NMem laz.ned x ∨ g.re ≤ x) ned tgt _ g' () h3 hd
    (fun x hx => Or.inl hx)
    (fun x hx => (L.mem x hx).elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr (by simp at h; omega))))
    (fun x hx => Or.inr (Or.inr (by have := L.le; simp at hx this; omega)))
  have F' := (front_reg (o := o) g L.le).trans F
  simp only [List.append_nil] at F'
  exact ⟨A, F', R⟩

/-- The registers the fill ops at an entry mention. -/
def FillRegs (ned : Need) (lo : Nat) (g g' : Gen Map) (e : Nat × Lazy S) : Prop :=
  ∀ B fin, HoonMap.get g.blocks e.1 = some ⟨[], B, fin⟩ → ∃ A, HoonMap.get g'.blocks e.1 = some ⟨[], A ++ B, fin⟩ ∧
    RegsIn (fun x => NMem ned x ∨ NMem e.2.sure.ned x ∨ lo ≤ x) A

/-- **The fill ops of the coercion of a list of entries mention only the
input registers, the entry's need and fresh registers.** -/
theorem coerceList_regs (ned : Need) (less : Cape) : ∀ (es : List (Nat × Lazy S)) (g g' : Gen Map),
    coerceList ned less es g = some ((), g') → g.drop = false → (es.map Prod.fst).Nodup →
    g'.drop = g.drop ∧ g.re ≤ g'.re ∧
    (∀ o, o ∉ es.map Prod.fst → HoonMap.get g'.blocks o = HoonMap.get g.blocks o) ∧
    ∀ e ∈ es, FillRegs ned g.re g g' e
  | [], g, g', h, _, _ => by
    simp only [coerceList, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact ⟨rfl, Nat.le_refl _, fun _ _ => rfl, fun e he => absurd he (List.not_mem_nil)⟩
  | (o, l) :: rest, g, g', h, hd, hnd => by
    simp only [coerceList] at h
    obtain ⟨u, g1, h1, h2⟩ := bind_some h
    obtain ⟨A, F, RA⟩ := coerceLazy_regs h1 hd
    have hd1 : g1.drop = false := F.drop.trans hd
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨IHdr, IHle, IHo, IHf⟩ := coerceList_regs ned less rest g1 g' h2 hd1 hnd.2
    refine ⟨IHdr.trans F.drop, Nat.le_trans F.le IHle, fun o' ho' => ?_, fun e hm => ?_⟩
    · simp only [List.map_cons, List.mem_cons, not_or] at ho'
      rw [IHo o' ho'.2, F.other o' ho'.1]
    · rcases List.mem_cons.mp hm with rfl | hm
      · intro B fin hb
        refine ⟨A, ?_, RA⟩
        rw [IHo _ hnd.1]; exact F.blk B fin hb
      · intro B fin hb
        have ne : e.1 ≠ o := fun eq => hnd.1 (eq ▸ List.mem_map_of_mem hm)
        rw [← F.other _ ne] at hb
        obtain ⟨A', hb', R'⟩ := IHf e hm B fin hb
        exact ⟨A', hb', R'.mono fun x hx => hx.elim Or.inl fun hx => hx.elim (fun h => Or.inr (Or.inl h))
          fun h => Or.inr (Or.inr (Nat.le_trans F.le h))⟩

/-- **The fill ops of `+coerce-lazy` over a whole lazy tree**, at the block
of the `next` and at every entry. -/
theorem coerceLazyL_regs {ned : Need} {less : Cape} {o : Nat} {laz : Lazy S} {g g' : Gen Map}
    (h : coerceLazyL ned less o laz g = some ((), g')) (hd : g.drop = false)
    (hnd : (o :: (entries laz).map Prod.fst).Nodup) :
    FillRegs ned g.re g g' (o, laz) ∧ ∀ e ∈ entries laz, FillRegs ned g.re g g' e := by
  rw [coerceLazyL_flat] at h
  have h' : (coerceList ned less ((o, laz) :: entries laz) : CM Map Unit) g = some ((), g') := by
    simp only [coerceList]; exact h
  obtain ⟨_, _, _, b4⟩ := coerceList_regs ned less ((o, laz) :: entries laz) g g' h' hd (by simpa using hnd)
  exact ⟨b4 _ List.mem_cons_self, fun e hm => b4 e (List.mem_cons_of_mem _ hm)⟩

end Comp
end SkaModel
end Formalization
