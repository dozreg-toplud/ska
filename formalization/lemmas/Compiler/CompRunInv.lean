import lemmas.Compiler.CompPastLink
import lemmas.Ska.CompFootTen
import lemmas.Ska.CompAboveRun
import lemmas.Ska.CompCall

/-!
# The invariant of the goals that `+run` hands its operands

The cases of `+run` (`CompRunCases.lean`, `CompRunCons.lean`) take their
recursive calls only on goals and states that meet `CrInv`:

* `crLokOk gl`: no look at axis `0` (the side condition of `+from`);
* `g.drop = false`: the state does not drop (`%run` mode);
* `GoalIn g.re gl`: every register of the goal (its need and the arguments
  of its jump) is below the counter `re`;
* `GDist gl`: no register occurs twice in the need of a `%next` goal.

The side condition of `+copy` (`CrCopyOk`: `cnLt` of both needs at the
counter and `cnMeet`) follows from it (`cri_copy`).  What `cnMeet a b` means:
walking `a` and `b` together, wherever both have a register at the same
place (`%this` or the top of a `%both`) the two registers differ.  So it
holds as soon as no register of `a` is one of `b` (`cri_meet_apart`), and
the two needs that a `+copy` joins are apart: the second run's need is
made of the registers of its goal's need and of registers allocated during
that run, the first run's need of registers below the counter where the
second run starts, and the two goal needs are apart (`run_foot`,
`run_keeps` of the model).

The example of the README that breaks `cnMeet` is ruled out: the goal
`[%next [%both 5 [%this 5] [%this 5]] ~ 0]` has `5` twice (not `GDist`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

/-- **The invariant of the goals and states of `+run`.** -/
def CrInv (g : Gen (TreapMap mugF)) (gl : CGoal CSet) : Prop :=
  crLokOk gl ∧ g.drop = false ∧ GoalIn g.re gl ∧ GDist gl

theorem cf_emitG_drop (b : Blob) (g : Gen (TreapMap mugF)) : (cfEmitG b g).drop = g.drop := by
  unfold cfEmitG; split <;> rfl

/-- A goal `[%next (lazy-from-reg r) ~ o]` below the counter. -/
theorem cri_reg {r : Nat} (o : Nat) {g : Gen (TreapMap mugF)} (hr : r < g.re) (hd : g.drop = false) :
    CrInv g (CGoal.next (lazyReg r) (jmp0 o)) :=
  ⟨fun y hy => absurd hy (HoonSet.mem_empty y), hd, ⟨nb_this hr, jmpIn_jmp0 _ _⟩, by
    simp [GDist, lazyReg, Distinct]⟩

/-- `+collapse-lazy-atom` keeps the mode and does not lower the counter. -/
theorem cri_cla {laz : Sure CSet} {th : Jmp} {g g1 : Gen (TreapMap mugF)} {a : Option (Nat × Nat)}
    (hd : g.drop = false) (h : collapseLazyAtomL (⟨Lazy.ofSure laz, th⟩ : NextL CSet) g = some (a, g1)) :
    g.re ≤ g1.re ∧ g1.drop = false := by
  rw [collapseLazyAtomL_mk] at h
  have k := (keepsA_collapseLazyAtom (P := fun _ => True) hd (fun _ _ => trivial) (fun _ _ => trivial) h).1
  exact ⟨k.le, k.dropF hd⟩

/-- `emit` keeps the counter and the mode. -/
theorem cri_emit {b : Blob} {g g' : Gen (TreapMap mugF)} {o : Nat} (h : emit b g = some (o, g')) :
    g'.re = g.re ∧ g'.drop = g.drop := by
  rw [cf_emit_g] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact ⟨cf_emitG_re _ _, cf_emitG_drop _ _⟩

/-! ## `cnLt` and `cnMeet` from the model's bounds -/

theorem cri_lt_of_nb {k : Nat} : ∀ n : Need, NB k n → cnLt k n
  | Need.none, _ => trivial
  | Need.this r, h => h r rfl
  | Need.pair p q, h => ⟨cri_lt_of_nb p fun r e => h r (Or.inl e), cri_lt_of_nb q fun r e => h r (Or.inr e)⟩
  | Need.both r p q, h => ⟨h r (Or.inl rfl), cri_lt_of_nb p fun x e => h x (Or.inr (Or.inl e)),
      cri_lt_of_nb q fun x e => h x (Or.inr (Or.inr e))⟩

/-- **`cnMeet` holds of two needs with no register in common.** -/
theorem cri_meet_apart : ∀ a b : Need, (∀ x, NMem a x → ¬ NMem b x) → cnMeet a b
  | Need.none, _, _ => by simp [cnMeet]
  | Need.this rl, Need.none, _ => by simp [cnMeet]
  | Need.this rl, Need.this rr, h => fun e => h rl rfl (by simp [NMem, e])
  | Need.this rl, Need.both x _ _, h => fun e => h rl rfl (by simp [NMem, e])
  | Need.this _, Need.pair _ _, _ => trivial
  | Need.both x _ _, Need.none, _ => by simp [cnMeet]
  | Need.both x _ _, Need.this rr, h => fun e => h x (Or.inl rfl) (by simp [NMem, e])
  | Need.both rl hl tl, Need.both x hr tr, h =>
      ⟨fun e => h rl (Or.inl rfl) (by simp [NMem, e]),
        cri_meet_apart hl hr fun y e1 e2 => h y (Or.inr (Or.inl e1)) (Or.inr (Or.inl e2)),
        cri_meet_apart tl tr fun y e1 e2 => h y (Or.inr (Or.inr e1)) (Or.inr (Or.inr e2))⟩
  | Need.both _ hl tl, Need.pair p q, h =>
      ⟨cri_meet_apart hl p fun y e1 e2 => h y (Or.inr (Or.inl e1)) (Or.inl e2),
        cri_meet_apart tl q fun y e1 e2 => h y (Or.inr (Or.inr e1)) (Or.inr e2)⟩
  | Need.pair _ _, Need.none, _ => by simp [cnMeet]
  | Need.pair _ _, Need.this _, _ => trivial
  | Need.pair pl ql, Need.pair pr qr, h =>
      ⟨cri_meet_apart pl pr fun y e1 e2 => h y (Or.inl e1) (Or.inl e2),
        cri_meet_apart ql qr fun y e1 e2 => h y (Or.inr e1) (Or.inr e2)⟩
  | Need.pair pl ql, Need.both _ hh tt, h =>
      ⟨cri_meet_apart pl hh fun y e1 e2 => h y (Or.inl e1) (Or.inr (Or.inl e2)),
        cri_meet_apart ql tt fun y e1 e2 => h y (Or.inr e1) (Or.inr (Or.inr e2))⟩

/-! ## One run, two runs, and the copy -/

/-- **What a run returns from a goal with the invariant**: the counter grows,
the mode stays, the result is below the new counter, its need is made of
fresh registers and those of the goal's need, and has no register twice. -/
theorem cri_run {n : Nomm} {gl : CGoal CSet} {g g' : Gen (TreapMap mugF)} {nex : Next CSet}
    (hi : CrInv g gl) (h : run n gl g = some (nex, g')) :
    g.re ≤ g'.re ∧ g'.drop = false ∧ NextIn g'.re nex ∧
      (∀ x, NMem nex.laz.ned x → g.re ≤ x ∨ GMem gl x) ∧ Distinct nex.laz.ned := by
  obtain ⟨k, ni⟩ := run_keeps n gl g g' nex hi.2.1 hi.2.2.1 h
  have F := run_foot n gl g g' nex hi.2.1 hi.2.2.1 hi.2.2.2 h
  exact ⟨k.le, k.dropF hi.2.1, ni, F.sure, F.dist⟩

/-- The goal of the second run of a `+copy` (`p` for `hs` with the `then`
of the first run's result) meets the invariant. -/
theorem cri_second {q : Nomm} {hs ts : Sure CSet} {j : Jmp} {g2 g3 : Gen (TreapMap mugF)} {nex2 : Next CSet}
    (hi : CrInv g2 (CGoal.next ts j)) (nh : NB g2.re hs.ned) (dh : Distinct hs.ned)
    (lh : ∀ y ∈ HoonSet.toList hs.lok, y ≠ 0) (h3 : run q (CGoal.next ts j) g2 = some (nex2, g3)) :
    CrInv g3 (CGoal.next hs nex2.th) := by
  obtain ⟨l3, d3, n3, -, -⟩ := cri_run hi h3
  exact ⟨lh, d3, ⟨nh.mono l3, n3.2⟩, dh⟩

/-- **The side condition of `+copy` from the invariant**: `q` runs first
for `ts`, `p` second for `hs` (apart from `ts` and below the counter), and
`+copy` joins the result of `p` with the need of the result of `q`. -/
theorem cri_copy {p q : Nomm} {hs ts : Sure CSet} {j : Jmp} {g2 g3 g4 : Gen (TreapMap mugF)}
    {nex2 nex1 : Next CSet} (hi : CrInv g2 (CGoal.next ts j)) (nh : NB g2.re hs.ned) (dh : Distinct hs.ned)
    (lh : ∀ y ∈ HoonSet.toList hs.lok, y ≠ 0) (ap : ∀ x, NMem hs.ned x → ¬ NMem ts.ned x)
    (h3 : run q (CGoal.next ts j) g2 = some (nex2, g3)) (h4 : run p (CGoal.next hs nex2.th) g3 = some (nex1, g4)) :
    cnLt g4.re nex1.laz.ned ∧ cnLt g4.re nex2.laz.ned ∧ cnMeet nex1.laz.ned nex2.laz.ned := by
  obtain ⟨l3, -, n3, s3, -⟩ := cri_run hi h3
  obtain ⟨l4, -, n4, s4, -⟩ := cri_run (cri_second hi nh dh lh h3) h4
  refine ⟨cri_lt_of_nb _ n4.1, cri_lt_of_nb _ (n3.1.mono l4), cri_meet_apart _ _ fun x e1 e2 => ?_⟩
  have x3 := n3.1 x e2
  rcases s4 x e1 with e | e
  · omega
  · have x2 := nh x e
    rcases s3 x e2 with e' | e'
    · omega
    · exact ap x e e'

/-! ## `+split` and `+into` -/

/-- **`+split` of a goal with the invariant**: the tail's goal meets it, and
the head is below the counter, distinct, and apart from the tail. -/
theorem cri_split {s : Sure CSet} {th : Jmp} {g g1 : Gen (TreapMap mugF)} {hed tel : Sure CSet} {o : Nat}
    (hi : CrInv g (CGoal.next s th)) (lt : ∀ y ∈ HoonSet.toList tel.lok, y ≠ 0)
    (h : Comp.split ⟨s, th⟩ g = some ((hed, tel, o), g1)) :
    CrInv g1 (CGoal.next tel (jmp0 o)) ∧ NB g1.re hed.ned ∧ Distinct hed.ned ∧
      (∀ x, NMem hed.ned x → ¬ NMem tel.ned x) := by
  obtain ⟨k, nh, nt⟩ := keeps_split hi.2.1 hi.2.2.1.1 hi.2.2.1.2 h
  obtain ⟨-, dh, dt, ap, -, -⟩ := split_foot hi.2.1 hi.2.2.2 hi.2.2.1.1 hi.2.2.1.2 h
  exact ⟨⟨lt, k.dropF hi.2.1, ⟨nt, jmpIn_jmp0 _ _⟩, dt⟩, nh, dh, ap⟩

/-- `+simple-next` of a goal with the invariant returns a `next` below the
counter with no register twice. -/
theorem cri_simple_next {gl : CGoal CSet} {g g1 : Gen (TreapMap mugF)} {nex : Next CSet}
    (hi : CrInv g gl) (h : simpleNext gl g = some (nex, g1)) :
    g1.drop = false ∧ NextIn g1.re nex ∧ Distinct nex.laz.ned := by
  obtain ⟨k, n⟩ := keeps_simpleNext hi.2.1 hi.2.2.1 h
  refine ⟨k.dropF hi.2.1, n, ?_⟩
  cases gl with
  | next laz th =>
    simp only [simpleNext, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hi.2.2.2
  | done =>
    simp only [simpleNext] at h
    obtain ⟨r, g5, h5, h⟩ := bind_some h
    obtain ⟨o, g6, h6, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [lazyReg, Distinct]
  | pick z o =>
    simp only [simpleNext] at h
    obtain ⟨r, g5, h5, h⟩ := bind_some h
    obtain ⟨o', g6, h6, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [lazyReg, Distinct]

/-- **`+into` of a `next` below the counter with no register twice**: the
donor's goal meets the invariant, and the recipient is below the counter,
distinct, and apart from the donor. -/
theorem cri_into {nex : Next CSet} {a : Nat} {g1 g2 : Gen (TreapMap mugF)} {don rec : Sure CSet} {o : Nat}
    (hd : g1.drop = false) (hn : NextIn g1.re nex) (dn : Distinct nex.laz.ned)
    (ld : ∀ y ∈ HoonSet.toList don.lok, y ≠ 0) (h : into nex a g1 = some ((don, rec, o), g2)) :
    CrInv g2 (CGoal.next don (jmp0 o)) ∧ NB g2.re rec.ned ∧ Distinct rec.ned ∧
      (∀ x, NMem rec.ned x → ¬ NMem don.ned x) := by
  obtain ⟨k, nd, nr⟩ := keeps_into hd hn h
  obtain ⟨laz, th⟩ := nex
  obtain ⟨_, _, _, _, _, _, _, Sm⟩ := into_ok h
  obtain ⟨Dd, Dr, Ddr, _, _⟩ := Sm dn hn.1
  exact ⟨⟨ld, k.dropF hd, ⟨nd, jmpIn_jmp0 _ _⟩, Dd⟩, nr, Dr, fun x e e' => Ddr x e' e⟩

/-! ## Examples of the model

`cnMeet` as a test (`criMeetB`), on the two needs that the `+copy` of a cons
joins, for the model's run over the list sets `LS` and the function maps `FM`
of `Ska/CompCall.lean` from a state with counter `8`: false on the goal of
the README that needs `5` twice, true on goals that meet `CrInv`. -/

def criMeetB : Need → Need → Bool
  | Need.none, _ => true
  | _, Need.none => true
  | Need.this rl, Need.this rr => rl != rr
  | Need.this rl, Need.both x _ _ => rl != x
  | Need.this _, Need.pair _ _ => true
  | Need.both x _ _, Need.this rr => x != rr
  | Need.pair _ _, Need.this _ => true
  | Need.both rl hl tl, Need.both x hr tr => rl != x && criMeetB hl hr && criMeetB tl tr
  | Need.both _ hl tl, Need.pair p q => criMeetB hl p && criMeetB tl q
  | Need.pair pl ql, Need.pair pr qr => criMeetB pl pr && criMeetB ql qr
  | Need.pair pl ql, Need.both _ h t => criMeetB pl h && criMeetB ql t

/-- The test of `cnMeet` at the `+copy` of the cons `[p q]` on the goal
`[%next s ~ 0]`, from the counter `re`. -/
def criConsTest {S : Type} [HoonSet S] (p q : Nomm) (s : Need) (re : Nat) : Option Bool :=
  ((do
    let (hed, tel, o) ← Comp.split (S := S) ⟨⟨s, HoonSet.empty⟩, jmp0 0⟩
    let nex2 ← run q (CGoal.next tel (jmp0 o))
    let nex1 ← run p (CGoal.next hed nex2.th)
    pure (criMeetB nex1.laz.ned nex2.laz.ned) : CM FM Bool)
    (⟨re, 0, 0, false, HoonMap.empty, HoonMap.empty, HoonMap.empty⟩ : Gen FM)).map (·.1)

#guard criConsTest (S := LS) (Nomm.n0 1) (Nomm.n0 1) (Need.both 5 (Need.this 5) (Need.this 5)) 8 = some false
#guard criConsTest (S := LS) (Nomm.n0 1) (Nomm.n0 1) (Need.both 5 (Need.this 6) (Need.this 7)) 8 = some true
#guard criConsTest (S := LS) (Nomm.n0 2) (Nomm.n0 3) (Need.both 5 (Need.this 6) (Need.this 7)) 8 = some true
#guard criConsTest (S := LS) (Nomm.n0 1) (Nomm.n0 1)
  (Need.pair (Need.this 3) (Need.both 4 (Need.this 6) (Need.this 7))) 8 = some true
#guard criConsTest (S := LS) (Nomm.n0 3) (Nomm.n0 2)
  (Need.both 1 (Need.both 2 (Need.this 3) (Need.this 4)) (Need.this 7)) 8 = some true

end Compiler
end Formalization
