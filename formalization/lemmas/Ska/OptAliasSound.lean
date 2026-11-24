import lemmas.Ska.OptAliasFacts
import lemmas.Ska.OptAliasField

/-!
# The transfer function of `+alias` is sound (step (b))

The state of the body walk (`ABody`: `old`, `loc`, `imml`) against the
values `R` of the code before at the same place (`R x` the value register `x`
holds, `none` for a missing or poisoned register), with `Done` the registers
whose definition has run: **`AOK st R Done`** is clauses 1 to 3 of `InfoOK`
(header of `OptAliasField.lean`): every register of `imml n` holds `n`, the
facts of `loc r` hold of the value of `r` (`InfoHolds`), and `old d` holds the
value of `d` once `d` is done.

`OpSem op R R2`: the op ran without a crash and its destination got the value
the op computes (`updA R d w`); ops without a destination keep `R`.  The
interpreter meets it: an op of `execPole` that returns `%0` gives `OpSem` on
the values `read x regs` before and after (`as_sem`, through `as_sem_local`
for the local ops and `as_after` for the calls).

**`as_op`**: one step of `aliasOp` keeps `AOK`, with the destination of the
op added to `Done`, given that the op's sources are read through `old`
correctly (`R (old x) = R x`, and `old x` is not the destination) and that the
destination is fresh (`AFresh`: no immediate, no fact names it, its own
facts are empty, it is not done, no done register is renamed to it).  The
destination becomes done when the op is dropped or keeps its own name in
`old` (a dead fill walked earlier may have renamed a register that is never
read, `OptAliasBody.lean`).  These are what single assignment gives along a path:
the destination is written once, after every fact about the registers before
it.  Every dropped op is justified by a fact: a dropped `%imm` by a register
of `imml n`, a dropped `%inc` by `decOf`, `%con` by `hedOf ∩ telOf`, `%hed`
and `%tal` by `hasHed`, `hasTel`, a dropped `%mov` by the source's own
`old`.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock

/-- `i` names the register `e`. -/
def ANames (i : InfoReg) (e : Nat) : Prop :=
  i.hasHed = some e ∨ i.hasTel = some e ∨ e ∈ i.hedOf ∨ e ∈ i.telOf ∨ i.decOf = some e

/-- **The invariant of the body walk** against the values of the code before. -/
structure AOK (st : ABody) (R : Nat → Option Noun) (Done : Nat → Prop) : Prop where
  imm : ∀ n r, r ∈ st.imml n → R r = some n
  info : ∀ r i v, st.loc r = some i → R r = some v → InfoHolds R i v
  old : ∀ d, Done d → R (st.old d) = R d

/-- The destination `e` of an op is fresh. -/
structure AFresh (st : ABody) (Done : Nat → Prop) (e : Nat) : Prop where
  imm : ∀ n, e ∉ st.imml n
  names : ∀ r i, st.loc r = some i → ¬ ANames i e
  loc : st.loc e = none ∨ st.loc e = some {}
  done : ¬ Done e
  old : ∀ d, Done d → st.old d ≠ e

/-- What an op that does not crash does to the values. -/
def OpSem : Pole → (Nat → Option Noun) → (Nat → Option Noun) → Prop
  | Pole.imm n d, R, R2 => R2 = updA R d (some n)
  | Pole.mov s d, R, R2 => R2 = updA R d (R s)
  | Pole.inc s d, R, R2 => ∃ a, R s = some (Noun.atom a) ∧ R2 = updA R d (some (Noun.atom (a + 1)))
  | Pole.con h t d, R, R2 => ∃ x y, R h = some x ∧ R t = some y ∧ R2 = updA R d (some (Noun.cell x y))
  | Pole.hed s d, R, R2 => ∃ x y, R s = some (Noun.cell x y) ∧ R2 = updA R d (some x)
  | Pole.tal s d, R, R2 => ∃ x y, R s = some (Noun.cell x y) ∧ R2 = updA R d (some y)
  | Pole.cel p, R, R2 => (∃ x y, R p = some (Noun.cell x y)) ∧ R2 = R
  | Pole.lob p, R, R2 => (R p = some (Noun.atom 0) ∨ R p = some (Noun.atom 1)) ∧ R2 = R
  | Pole.spy _ _ d, R, R2 => ∃ w, R2 = updA R d w
  | Pole.nok _ _ d, R, R2 => ∃ w, R2 = updA R d w
  | Pole.cal _ _ d, R, R2 => ∃ w, R2 = updA R d w
  | Pole.caf _ _ d _, R, R2 => ∃ w, R2 = updA R d w
  | Pole.cam _ _ d _, R, R2 => ∃ w, R2 = updA R d w
  | Pole.csl _ _ d, R, R2 => ∃ w, R2 = updA R d w
  | Pole.csf _ _ d _, R, R2 => ∃ w, R2 = updA R d w
  | Pole.csm _ _ d _, R, R2 => ∃ w, R2 = updA R d w
  | _, R, R2 => R2 = R

/-- The registers an op reads through `old` in the model. -/
def asSrc : Pole → List Nat
  | Pole.mov s _ => [s]
  | Pole.inc s _ => [s]
  | Pole.con h t _ => [h, t]
  | Pole.hed s _ => [s]
  | Pole.tal s _ => [s]
  | Pole.cel p => [p]
  | Pole.lob p => [p]
  | _ => []

section
variable {R : Nat → Option Noun} {e : Nat} {w : Option Noun}

theorem as_upd_self {α : Type} (f : Nat → α) (k : Nat) (v : α) : updA f k v k = v := by simp [updA]
theorem as_upd_other {α : Type} (f : Nat → α) {k k' : Nat} (v : α) (h : k' ≠ k) : updA f k v k' = f k' := by
  simp [updA, h]

/-- Facts that do not name `e` survive a write of `e`. -/
theorem as_frame {i : InfoReg} {v : Noun} (h : InfoHolds R i v) (hn : ¬ ANames i e) :
    InfoHolds (updA R e w) i v := by
  obtain ⟨c, l, im, hh, ht, ho, to, dc⟩ := h
  refine ⟨c, l, im, fun d hd => ?_, fun d hd => ?_, fun x hx => ?_, fun x hx => ?_, fun d hd => ?_⟩
  · have hde : d ≠ e := fun h => hn (Or.inl (h ▸ hd))
    obtain ⟨a, b, h1, h2⟩ := hh d hd
    exact ⟨a, b, h1, by rw [as_upd_other _ _ hde]; exact h2⟩
  · have hde : d ≠ e := fun h => hn (Or.inr (Or.inl (h ▸ hd)))
    obtain ⟨a, b, h1, h2⟩ := ht d hd
    exact ⟨a, b, h1, by rw [as_upd_other _ _ hde]; exact h2⟩
  · have hde : x ≠ e := fun h => hn (Or.inr (Or.inr (Or.inl (h ▸ hx))))
    obtain ⟨t, h1⟩ := ho x hx
    exact ⟨t, by rw [as_upd_other _ _ hde]; exact h1⟩
  · have hde : x ≠ e := fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl (h ▸ hx)))))
    obtain ⟨t, h1⟩ := to x hx
    exact ⟨t, by rw [as_upd_other _ _ hde]; exact h1⟩
  · have hde : d ≠ e := fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (h ▸ hd)))))
    obtain ⟨a, h1, h2⟩ := dc d hd
    exact ⟨a, h1, by rw [as_upd_other _ _ hde]; exact h2⟩

variable {st : ABody} {Done : Nat → Prop}

/-- The immediates survive a write of a fresh register. -/
theorem as_imm_keep (hok : AOK st R Done) (hf : AFresh st Done e) :
    ∀ n r, r ∈ st.imml n → updA R e w r = some n := fun n r hr => by
  have hre : r ≠ e := fun h => hf.imm n (h ▸ hr)
  rw [as_upd_other _ _ hre]; exact hok.imm n r hr

/-- The facts of the other registers survive a write of a fresh register. -/
theorem as_info_keep (hok : AOK st R Done) (hf : AFresh st Done e) {r : Nat} {i : InfoReg} {v : Noun}
    (hr : st.loc r = some i) (hv : updA R e w r = some v) : InfoHolds (updA R e w) i v := by
  by_cases hre : r = e
  · subst hre
    rcases hf.loc with h | h
    · rw [h] at hr; cases hr
    · rw [h] at hr; cases hr; exact info_empty
  · rw [as_upd_other _ _ hre] at hv
    exact as_frame (hok.info r i v hr hv) (hf.names r i hr)

/-- `old` of the done registers survives a write of a fresh register, and
the register itself is done when it keeps its own name. -/
theorem as_old_keep (hok : AOK st R Done) (hf : AFresh st Done e) :
    ∀ x, (Done x ∨ (some e = some x ∧ st.old x = x)) → updA R e w (st.old x) = updA R e w x := by
  rintro x (hx | ⟨hx, hs⟩)
  · have hxe : x ≠ e := fun h => hf.done (h ▸ hx)
    rw [as_upd_other _ _ (hf.old x hx), as_upd_other _ _ hxe]; exact hok.old x hx
  · rw [hs]

/-- `old` after a dropped write renamed to `y`, which holds the value. -/
theorem as_old_drop (hok : AOK st R Done) (hf : AFresh st Done e) {y : Nat}
    (hy : updA R e w y = w) :
    ∀ x, (Done x ∨ (some e = some x ∧ st.old x = x)) → updA R e w (updA st.old e y x) = updA R e w x := by
  rintro x (hx | ⟨hx, -⟩)
  · have hxe : x ≠ e := fun h => hf.done (h ▸ hx)
    rw [as_upd_other _ _ hxe, as_upd_other _ _ (hf.old x hx), as_upd_other _ _ hxe]; exact hok.old x hx
  · cases hx; rw [as_upd_self, hy, as_upd_self]

theorem as_jab {m m2 : AInfo} {k : Nat} {g : InfoReg → InfoReg} (h : jabA m k g = some m2) :
    ∃ i, m k = some i ∧ m2 = updA m k (some (g i)) := by
  unfold jabA at h
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨i, hi, rfl⟩


/-! ## Facts added by a kept op -/

theorem as_with_dec {i : InfoReg} {v : Noun} {d : Nat} (h : InfoHolds R i v)
    (hd : ∃ n, v = Noun.atom n ∧ R d = some (Noun.atom (n + 1))) : InfoHolds R { i with decOf := some d } v := by
  obtain ⟨c, l, im, hh, ht, ho, to, _⟩ := h
  exact ⟨c, l, im, hh, ht, ho, to, fun d' e => by simp only [Option.some.injEq] at e; subst e; exact hd⟩

theorem as_with_hed {i : InfoReg} {v : Noun} {d : Nat} (h : InfoHolds R i v)
    (hd : ∃ a b, v = Noun.cell a b ∧ R d = some a) : InfoHolds R { i with hasHed := some d } v := by
  obtain ⟨c, l, im, _, ht, ho, to, dc⟩ := h
  exact ⟨c, l, im, fun d' e => by simp only [Option.some.injEq] at e; subst e; exact hd, ht, ho, to, dc⟩

theorem as_with_tel {i : InfoReg} {v : Noun} {d : Nat} (h : InfoHolds R i v)
    (hd : ∃ a b, v = Noun.cell a b ∧ R d = some b) : InfoHolds R { i with hasTel := some d } v := by
  obtain ⟨c, l, im, hh, _, ho, to, dc⟩ := h
  exact ⟨c, l, im, hh, fun d' e => by simp only [Option.some.injEq] at e; subst e; exact hd, ho, to, dc⟩

theorem as_with_hedOf {i : InfoReg} {v : Noun} {d : Nat} (h : InfoHolds R i v)
    (hd : ∃ t, R d = some (Noun.cell v t)) : InfoHolds R { i with hedOf := insN i.hedOf d } v := by
  obtain ⟨c, l, im, hh, ht, ho, to, dc⟩ := h
  refine ⟨c, l, im, hh, ht, fun x hx => ?_, to, dc⟩
  simp only [insN] at hx; split at hx
  · exact ho x hx
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact hd
    · exact ho x hx

theorem as_with_telOf {i : InfoReg} {v : Noun} {d : Nat} (h : InfoHolds R i v)
    (hd : ∃ a, R d = some (Noun.cell a v)) : InfoHolds R { i with telOf := insN i.telOf d } v := by
  obtain ⟨c, l, im, hh, ht, ho, to, dc⟩ := h
  refine ⟨c, l, im, hh, ht, ho, fun x hx => ?_, dc⟩
  simp only [insN] at hx; split at hx
  · exact to x hx
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact hd
    · exact to x hx

theorem as_with_cell {i : InfoReg} {v : Noun} (h : InfoHolds R i v) (hd : ∃ a b, v = Noun.cell a b) :
    InfoHolds R { i with isCell := true } v := by
  obtain ⟨_, l, im, hh, ht, ho, to, dc⟩ := h
  exact ⟨fun _ => hd, l, im, hh, ht, ho, to, dc⟩

theorem as_with_loob {i : InfoReg} {v : Noun} (h : InfoHolds R i v)
    (hd : v = Noun.atom 0 ∨ v = Noun.atom 1) : InfoHolds R { i with isLoob := true } v := by
  obtain ⟨c, _, im, hh, ht, ho, to, dc⟩ := h
  exact ⟨c, fun _ => hd, im, hh, ht, ho, to, dc⟩

/-- One more layer of facts. -/
theorem as_info_upd {R2 : Nat → Option Noun} {m : AInfo} {k : Nat} {ik : InfoReg}
    (hm : ∀ r i v, m r = some i → R2 r = some v → InfoHolds R2 i v)
    (hk : ∀ v, R2 k = some v → InfoHolds R2 ik v) :
    ∀ r i v, updA m k (some ik) r = some i → R2 r = some v → InfoHolds R2 i v := by
  intro r i v hr hv
  by_cases e : r = k
  · subst e; rw [as_upd_self] at hr; cases hr; exact hk v hv
  · rw [as_upd_other _ _ e] at hr; exact hm r i v hr hv

end

/-- **`aliasOp` keeps `AOK`.** -/
theorem as_op {pick : List Nat → Nat} (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l)
    {st st2 : ABody} {op : Pole} {res : Option Pole} {R R2 : Nat → Option Noun} {Done : Nat → Prop}
    (h : aliasOp pick st op = some (res, st2)) (hok : AOK st R Done)
    (hrd : ∀ x ∈ asSrc op, R (st.old x) = R x ∧ ∀ e, aliasDst op = some e → st.old x ≠ e)
    (hfr : ∀ e, aliasDst op = some e → AFresh st Done e) (hs : OpSem op R R2) :
    AOK st2 R2 (fun x => Done x ∨ (aliasDst op = some x ∧ st.old x = x)) := by
  -- an op without destination that keeps the state
  have same : st2 = st → R2 = R → (∀ e, aliasDst op ≠ some e) →
      AOK st2 R2 (fun x => Done x ∨ (aliasDst op = some x ∧ st.old x = x)) :=
    fun e1 e2 hn => by
      subst e1 e2
      exact ⟨hok.imm, hok.info, fun d hd => hd.elim (hok.old d) (fun h => absurd h.1 (hn d))⟩
  -- an op writing `d` whose state gets the empty facts at `d`
  have blank : ∀ d, aliasDst op = some d → AFresh st Done d → (∃ w, R2 = updA R d w) →
      st2 = { st with loc := updA st.loc d (some {}) } →
      AOK st2 R2 (fun x => Done x ∨ (aliasDst op = some x ∧ st.old x = x)) :=
    fun d hd hf ⟨w, hw⟩ e => by
      subst e hw
      rw [hd]
      exact ⟨as_imm_keep (st := st) hok hf, as_info_upd (fun r i v hr hv => as_info_keep (st := st) hok hf hr hv)
        (fun _ _ => info_empty), as_old_keep (st := st) hok hf⟩
  cases op with
  | imm n d =>
    have hf := hfr d rfl
    simp only [OpSem] at hs; subst hs
    simp only [aliasOp] at h
    split at h
    · rename_i hne
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      have hp := hpick _ hne
      have hpd : pick (st.imml n) ≠ d := fun e => hf.imm n (e ▸ hp)
      exact ⟨as_imm_keep (st := st) hok hf, fun r i v hr hv => as_info_keep (st := st) hok hf hr hv,
        as_old_drop (st := st) hok hf (by rw [as_upd_other _ _ hpd, hok.imm n _ hp])⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      refine ⟨fun m r hr => ?_, as_info_upd (fun r i v hr hv => as_info_keep (st := st) hok hf hr hv) ?_, as_old_keep (st := st) hok hf⟩
      · dsimp only at hr
        split at hr
        · rename_i hm; subst hm
          unfold insN at hr; split at hr
          · exact as_imm_keep (st := st) hok hf _ _ hr
          · rcases List.mem_cons.mp hr with rfl | hr
            · rw [as_upd_self]
            · exact as_imm_keep (st := st) hok hf _ _ hr
        · exact as_imm_keep (st := st) hok hf _ _ hr
      · intro v hv
        rw [as_upd_self] at hv; cases hv
        refine ⟨fun e => by simp at e, fun e => by simp at e, fun m e => by simpa using e, fun _ e => by simp at e,
          fun _ e => by simp at e, fun _ e => by simp at e, fun _ e => by simp at e, fun _ e => by simp at e⟩
  | mov s d =>
    have hf := hfr d rfl
    obtain ⟨hs1, hs2⟩ := hrd s (by simp [asSrc])
    have hsd := hs2 d rfl
    simp only [OpSem] at hs; subst hs
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨as_imm_keep (st := st) hok hf, fun r i v hr hv => as_info_keep (st := st) hok hf hr hv,
      as_old_drop (st := st) hok hf (by rw [as_upd_other _ _ hsd, hs1])⟩
  | inc s d =>
    have hf := hfr d rfl
    obtain ⟨hs1, hs2⟩ := hrd s (by simp [asSrc])
    have hsd := hs2 d rfl
    simp only [OpSem] at hs
    obtain ⟨a, ha, rfl⟩ := hs
    simp only [aliasOp] at h
    obtain ⟨ai, hai, h⟩ := Option.bind_eq_some_iff.mp h
    have hinfo : InfoHolds R ai (Noun.atom a) := hok.info _ ai _ hai (by rw [hs1]; exact ha)
    split at h
    · rename_i x hx
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      obtain ⟨n, hn1, hn2⟩ := hinfo.2.2.2.2.2.2.2 x hx
      have hxd : x ≠ d := fun e => hf.names _ ai hai (Or.inr (Or.inr (Or.inr (Or.inr (e ▸ hx)))))
      cases hn1
      exact ⟨as_imm_keep (st := st) hok hf, fun r i v hr hv => as_info_keep (st := st) hok hf hr hv,
        as_old_drop (st := st) hok hf (by rw [as_upd_other _ _ hxd, hn2])⟩
    · obtain ⟨loc, hj, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      obtain ⟨i0, hi0, rfl⟩ := as_jab hj
      rw [as_upd_other _ _ hsd, hai] at hi0; cases hi0
      have l1 := as_info_upd (k := d) (ik := {}) (fun r i v hr hv => as_info_keep (w := some (Noun.atom (a + 1))) hok hf hr hv)
        (fun _ _ => info_empty)
      refine ⟨as_imm_keep (st := st) hok hf, as_info_upd l1 (fun v hv => ?_), as_old_keep (st := st) hok hf⟩
      rw [as_upd_other _ _ hsd, hs1, ha] at hv; cases hv
      exact as_with_dec (as_frame hinfo (hf.names _ _ hai)) ⟨a, rfl, by rw [as_upd_self]⟩
  | con h0 t0 d =>
    have hf := hfr d rfl
    obtain ⟨hh1, hh2⟩ := hrd h0 (by simp [asSrc])
    obtain ⟨ht1, ht2⟩ := hrd t0 (by simp [asSrc])
    have hhd := hh2 d rfl
    have htd := ht2 d rfl
    simp only [OpSem] at hs
    obtain ⟨x, y, hx, hy, rfl⟩ := hs
    simp only [aliasOp] at h
    obtain ⟨hi, hhi, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ti, hti, h⟩ := Option.bind_eq_some_iff.mp h
    have ihh : InfoHolds R hi x := hok.info _ hi _ hhi (by rw [hh1]; exact hx)
    have iht : InfoHolds R ti y := hok.info _ ti _ hti (by rw [ht1]; exact hy)
    split at h
    · rename_i hne
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      have hp := hpick _ hne
      obtain ⟨hp1, hp2⟩ := List.mem_filter.mp hp
      have hp2' := of_decide_eq_true hp2
      obtain ⟨t1, e1⟩ := ihh.2.2.2.2.2.1 _ hp1
      obtain ⟨h1, e2⟩ := iht.2.2.2.2.2.2.1 _ hp2'
      have hpd : pick (hi.hedOf.filter (· ∈ ti.telOf)) ≠ d :=
        fun e => hf.names _ hi hhi (Or.inr (Or.inr (Or.inl (e ▸ hp1))))
      rw [e1] at e2; cases e2
      exact ⟨as_imm_keep (st := st) hok hf, fun r i v hr hv => as_info_keep (st := st) hok hf hr hv,
        as_old_drop (st := st) hok hf (by rw [as_upd_other _ _ hpd, e1])⟩
    · obtain ⟨l1, hj1, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨l2, hj2, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      obtain ⟨i1, hi1, rfl⟩ := as_jab hj1
      obtain ⟨i2, hi2, rfl⟩ := as_jab hj2
      rw [as_upd_other _ _ hhd, hhi] at hi1; cases hi1
      have L0 := fun r i v hr hv => as_info_keep (w := some (Noun.cell x y)) hok hf (r := r) (i := i) (v := v) hr hv
      have L1 := as_info_upd (k := d)
        (ik := { hasHed := some (st.old h0), hasTel := some (st.old t0), isCell := true }) L0 (fun v hv => by
          rw [as_upd_self] at hv; cases hv
          refine ⟨fun _ => ⟨x, y, rfl⟩, fun e => by simp at e, fun _ e => by simp at e, fun d' e => ?_,
            fun d' e => ?_, fun _ e => by simp at e, fun _ e => by simp at e, fun _ e => by simp at e⟩
          · simp only [Option.some.injEq] at e; subst e
            exact ⟨x, y, rfl, by rw [as_upd_other _ _ hhd, hh1, hx]⟩
          · simp only [Option.some.injEq] at e; subst e
            exact ⟨x, y, rfl, by rw [as_upd_other _ _ htd, ht1, hy]⟩)
      have L2 := as_info_upd (k := st.old h0) (ik := { hi with hedOf := insN hi.hedOf d }) L1 (fun v hv => by
        rw [as_upd_other _ _ hhd, hh1, hx] at hv; cases hv
        exact as_with_hedOf (as_frame ihh (hf.names _ _ hhi)) ⟨y, by rw [as_upd_self]⟩)
      refine ⟨as_imm_keep (st := st) hok hf, as_info_upd L2 (fun v hv => ?_), as_old_keep (st := st) hok hf⟩
      have hi2' := L2 _ i2 v hi2 hv
      rw [as_upd_other _ _ htd, ht1, hy] at hv; cases hv
      exact as_with_telOf hi2' ⟨x, by rw [as_upd_self]⟩
  | hed s d =>
    have hf := hfr d rfl
    obtain ⟨hs1, hs2⟩ := hrd s (by simp [asSrc])
    have hsd := hs2 d rfl
    simp only [OpSem] at hs
    obtain ⟨x, y, hxy, rfl⟩ := hs
    simp only [aliasOp] at h
    obtain ⟨ai, hai, h⟩ := Option.bind_eq_some_iff.mp h
    have hinfo : InfoHolds R ai (Noun.cell x y) := hok.info _ ai _ hai (by rw [hs1]; exact hxy)
    split at h
    · rename_i z hz
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      obtain ⟨a, b, e1, e2⟩ := hinfo.2.2.2.1 z hz
      have hzd : z ≠ d := fun e => hf.names _ ai hai (Or.inl (e ▸ hz))
      cases e1
      exact ⟨as_imm_keep (st := st) hok hf, fun r i v hr hv => as_info_keep (st := st) hok hf hr hv,
        as_old_drop (st := st) hok hf (by rw [as_upd_other _ _ hzd, e2])⟩
    · obtain ⟨loc, hj, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      obtain ⟨i0, hi0, rfl⟩ := as_jab hj
      rw [as_upd_other _ _ hsd, hai] at hi0; cases hi0
      have l1 := as_info_upd (k := d) (ik := { hedOf := [st.old s] })
        (fun r i v hr hv => as_info_keep (st := st) (w := some x) hok hf hr hv) (fun v hv => by
          rw [as_upd_self] at hv; cases hv
          refine ⟨fun e => by simp at e, fun e => by simp at e, fun _ e => by simp at e, fun _ e => by simp at e,
            fun _ e => by simp at e, fun z hz => ?_, fun _ e => by simp at e, fun _ e => by simp at e⟩
          simp only [List.mem_singleton] at hz; subst hz
          exact ⟨y, by rw [as_upd_other _ _ hsd, hs1, hxy]⟩)
      refine ⟨as_imm_keep (st := st) hok hf, as_info_upd l1 (fun v hv => ?_), as_old_keep (st := st) hok hf⟩
      rw [as_upd_other _ _ hsd, hs1, hxy] at hv; cases hv
      exact as_with_hed (as_frame hinfo (hf.names _ _ hai)) ⟨x, y, rfl, by rw [as_upd_self]⟩
  | tal s d =>
    have hf := hfr d rfl
    obtain ⟨hs1, hs2⟩ := hrd s (by simp [asSrc])
    have hsd := hs2 d rfl
    simp only [OpSem] at hs
    obtain ⟨x, y, hxy, rfl⟩ := hs
    simp only [aliasOp] at h
    obtain ⟨ai, hai, h⟩ := Option.bind_eq_some_iff.mp h
    have hinfo : InfoHolds R ai (Noun.cell x y) := hok.info _ ai _ hai (by rw [hs1]; exact hxy)
    split at h
    · rename_i z hz
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      obtain ⟨a, b, e1, e2⟩ := hinfo.2.2.2.2.1 z hz
      have hzd : z ≠ d := fun e => hf.names _ ai hai (Or.inr (Or.inl (e ▸ hz)))
      cases e1
      exact ⟨as_imm_keep (st := st) hok hf, fun r i v hr hv => as_info_keep (st := st) hok hf hr hv,
        as_old_drop (st := st) hok hf (by rw [as_upd_other _ _ hzd, e2])⟩
    · obtain ⟨loc, hj, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      obtain ⟨i0, hi0, rfl⟩ := as_jab hj
      rw [as_upd_other _ _ hsd, hai] at hi0; cases hi0
      have l1 := as_info_upd (k := d) (ik := { telOf := [st.old s] })
        (fun r i v hr hv => as_info_keep (st := st) (w := some y) hok hf hr hv) (fun v hv => by
          rw [as_upd_self] at hv; cases hv
          refine ⟨fun e => by simp at e, fun e => by simp at e, fun _ e => by simp at e, fun _ e => by simp at e,
            fun _ e => by simp at e, fun _ e => by simp at e, fun z hz => ?_, fun _ e => by simp at e⟩
          simp only [List.mem_singleton] at hz; subst hz
          exact ⟨x, by rw [as_upd_other _ _ hsd, hs1, hxy]⟩)
      refine ⟨as_imm_keep (st := st) hok hf, as_info_upd l1 (fun v hv => ?_), as_old_keep (st := st) hok hf⟩
      rw [as_upd_other _ _ hsd, hs1, hxy] at hv; cases hv
      exact as_with_tel (as_frame hinfo (hf.names _ _ hai)) ⟨x, y, rfl, by rw [as_upd_self]⟩
  | cel p =>
    obtain ⟨hs1, -⟩ := hrd p (by simp [asSrc])
    simp only [OpSem] at hs
    obtain ⟨⟨x, y, hxy⟩, rfl⟩ := hs
    simp only [aliasOp] at h
    obtain ⟨ai, hai, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact same h.2.symm rfl (fun _ e => by cases e)
    · obtain ⟨loc, hj, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      obtain ⟨i0, hi0, rfl⟩ := as_jab hj
      rw [hai] at hi0; cases hi0
      refine ⟨hok.imm, as_info_upd hok.info (fun v hv => ?_), fun d hd => hd.elim (hok.old d) (fun e => by cases e.1)⟩
      rw [hs1, hxy] at hv; cases hv
      exact as_with_cell (hok.info _ _ _ hai (by rw [hs1, hxy])) ⟨x, y, rfl⟩
  | lob p =>
    obtain ⟨hs1, -⟩ := hrd p (by simp [asSrc])
    simp only [OpSem] at hs
    obtain ⟨hl, rfl⟩ := hs
    simp only [aliasOp] at h
    obtain ⟨ai, hai, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact same h.2.symm rfl (fun _ e => by cases e)
    · obtain ⟨loc, hj, h⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      obtain ⟨i0, hi0, rfl⟩ := as_jab hj
      rw [hai] at hi0; cases hi0
      refine ⟨hok.imm, as_info_upd hok.info (fun v hv => ?_), fun d hd => hd.elim (hok.old d) (fun e => by cases e.1)⟩
      rw [hs1] at hv
      exact as_with_loob (hok.info _ _ _ hai (by rw [hs1]; exact hv)) (by
        rcases hl with e | e <;> rw [e] at hv <;> cases hv
        · exact Or.inl rfl
        · exact Or.inr rfl)
  | equ l r =>
    simp only [OpSem] at hs
    simp only [aliasOp] at h
    split at h <;> (simp only [Option.some.injEq, Prod.mk.injEq] at h; exact same h.2.symm hs (fun _ e => by cases e))
  | hsp => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; exact same h.2.symm hs (fun _ e => by cases e)
  | hse => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; exact same h.2.symm hs (fun _ e => by cases e)
  | hdp => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; exact same h.2.symm hs (fun _ e => by cases e)
  | hde => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; exact same h.2.symm hs (fun _ e => by cases e)
  | hmp => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; exact same h.2.symm hs (fun _ e => by cases e)
  | hme => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; exact same h.2.symm hs (fun _ e => by cases e)
  | hcp => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; exact same h.2.symm hs (fun _ e => by cases e)
  | hce => simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h; exact same h.2.symm hs (fun _ e => by cases e)
  | spy _ _ d =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    exact blank d rfl (hfr d rfl) hs h.2.symm
  | nok _ _ d =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    exact blank d rfl (hfr d rfl) hs h.2.symm
  | cal _ _ d =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    exact blank d rfl (hfr d rfl) hs h.2.symm
  | caf _ _ d _ =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    exact blank d rfl (hfr d rfl) hs h.2.symm
  | cam _ _ d _ =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    exact blank d rfl (hfr d rfl) hs h.2.symm
  | csl _ _ d =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    exact blank d rfl (hfr d rfl) hs h.2.symm
  | csf _ _ d _ =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    exact blank d rfl (hfr d rfl) hs h.2.symm
  | csm _ _ d _ =>
    simp only [aliasOp, Option.some.injEq, Prod.mk.injEq] at h
    exact blank d rfl (hfr d rfl) hs h.2.symm

/-! ## The ops of the interpreter meet `OpSem` -/

section
variable {Map : Type → Type} [HoonMap Map] {σ : Type}

theorem as_store (d : Nat) (v : Noun) (regs : Map (Option Noun)) :
    (fun x => read x (store d v regs)) = updA (fun x => read x regs) d (some v) := by
  funext x; by_cases h : x = d
  · subst h; rw [read_store_self, as_upd_self]
  · rw [read_store_other h, as_upd_other _ _ h]

/-- **A local op that goes on (`%0`) meets `OpSem`** on the values `read`. -/
theorem as_sem_local {lib : Lib} {scry : Noun} {op : Pole} {regs regs' : Map (Option Noun)}
    {trace trace' : Trace} {p : Noun} (h : localPole lib scry op regs trace = some (Tone.zero p, regs', trace')) :
    OpSem op (fun x => read x regs) (fun x => read x regs') := by
  cases op <;> simp only [localPole, OpSem] at h ⊢
  case imm n d =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    exact as_store d n regs
  case mov s d =>
    obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    funext x
    rw [read_move hr x]
    by_cases e : x = d
    · subst e; rw [as_upd_self, if_pos rfl]
    · rw [as_upd_other _ _ e, if_neg e]
  case inc s d =>
    obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
    cases v with
    | cell => simp at h
    | atom a =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      exact ⟨a, hv, as_store _ _ _⟩
  case con h0 t0 d =>
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    exact ⟨x, y, hx, hy, as_store _ _ _⟩
  case hed s d =>
    obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
    cases v with
    | atom => simp at h
    | cell x y =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      exact ⟨x, y, hv, as_store _ _ _⟩
  case tal s d =>
    obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
    cases v with
    | atom => simp at h
    | cell x y =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      exact ⟨x, y, hv, as_store _ _ _⟩
  case cel q =>
    obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
    cases v with
    | atom => simp at h
    | cell x y =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      exact ⟨⟨x, y, hv⟩, rfl⟩
  case lob q =>
    obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      rcases hc with e | e <;> subst e
      · exact ⟨Or.inl hv, rfl⟩
      · exact ⟨Or.inr hv, rfl⟩
    · simp at h
  case equ l r =>
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h; rfl
  case hsp =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h; rfl
  case hse =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h; rfl
  case hcp =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h; rfl
  case hmp =>
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h; rfl
  case hme =>
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h; rfl
  case hce =>
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h; rfl
  case hdp =>
    split at h
    · obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h; rfl
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h; rfl
  case hde =>
    split at h
    · obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h; rfl
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h; rfl
  case spy e q d =>
    split at h
    · simp at h
    · obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨dr, _, h⟩ := Option.bind_eq_some_iff.mp h
      cases dr with
      | block => simp at h
      | hunk => simp at h
      | val v =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl, -⟩ := h
        exact ⟨some v, as_store _ _ _⟩
  all_goals simp at h


theorem as_after {st st' : σ} {regs regs' : Map (Option Noun)} {trace trace' : Trace} {d : Nat} {ton : Tone}
    {p : Noun} (h : afterCall st regs trace d ton = some (Tone.zero p, regs', trace', st')) :
    ∃ w, (fun x => read x regs') = updA (fun x => read x regs) d w := by
  cases ton with
  | zero q =>
    simp only [afterCall, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    exact ⟨some q, as_store _ _ _⟩
  | one => simp [afterCall] at h
  | two => simp [afterCall] at h

/-- **An op of `+eval-pole` that goes on (`%0`) meets `OpSem`** on the values
`read`. -/
theorem as_sem {lib : Lib} {O : Oracle σ} {scry : Noun} {st st' : σ} {op : Pole}
    {regs regs' : Map (Option Noun)} {trace trace' : Trace} {p : Noun}
    (h : execPole lib O scry st op regs trace = some (Tone.zero p, regs', trace', st')) :
    OpSem op (fun x => read x regs) (fun x => read x regs') := by
  have loc : (localPole lib scry op regs trace).map (fun (ton, regs', trace') => (ton, regs', trace', st)) =
      some (Tone.zero p, regs', trace', st') → OpSem op (fun x => read x regs) (fun x => read x regs') := by
    intro h
    obtain ⟨⟨t, r2, t2⟩, hl, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, -⟩ := he
    exact as_sem_local hl
  cases op
  case nok u f d =>
    simp only [execPole] at h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨ton, s2⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
    cases ton with
    | zero q =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      exact ⟨some q, as_store _ _ _⟩
    | one => simp at h
    | two => simp at h
  case cal a v d =>
    simp only [execPole] at h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨ton, s2⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
    exact as_after h
  case caf a v d n =>
    simp only [execPole] at h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨ton, s2⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
    exact as_after h
  case cam a v d k =>
    simp only [execPole] at h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨ton, s2⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
    exact as_after h
  case csl a s0 d =>
    simp only [execPole] at h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨ton, s2⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
    exact as_after h
  case csf a s0 d n =>
    simp only [execPole] at h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨ton, s2⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
    exact as_after h
  case csm a s0 d k =>
    simp only [execPole] at h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨ton, s2⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
    exact as_after h
  all_goals exact loc h

end

end Opt
end SkaModel
end Formalization
