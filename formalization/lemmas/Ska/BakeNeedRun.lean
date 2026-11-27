import lemmas.Ska.BakeNeed
import lemmas.Ska.CompEntry

/-!
# The registers that `+bake-need` leaves

`+to-straight` of the residual need `ned.bak` (README Gaps 9, MAP item 6)
is linked when its registers are a run in preorder (`isRun`, the
hypothesis of `TsOn`).  The registers of `ned-final` are a run
(`isRun_needOrdAllocRegs`).  Here:

* `bakeGo_sublist`: the registers of the residual are a sublist of those of
  the need (`bakeGo` removes whole subtrees and keeps the register of every
  `%both` it does not bake whole);
* `isRun_infix`: an infix of a run is a run; so the residual is a run when
  its registers are an infix of the need's (`bake_run_of_infix`), in
  particular when the baked registers are a prefix or a suffix in preorder;
* `bakeGo_no`: nothing is baked under a sock that knows nothing;
* the two cases of a known half: **`bake_run_head`** (a cell need
  `[p q]` under a sock whose head is wholly known and fits `p`, whose tail
  knows nothing: the residual's registers are those of `q`, a suffix) and
  **`bake_run_tail`** (a cell or a `%both` whose tail is wholly known and
  fits, whose head knows nothing: the residual's registers are a prefix).
  A `%both` with a known HEAD keeps its own register before the tail's and
  is not a run unless its head has no register: that is the map path of
  `+to-straight` with `run` false, not linked.
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

theorem flatten_consNeed (a b : Need) : flattenNeed (consNeed a b) = flattenNeed a ++ flattenNeed b := by
  unfold consNeed
  split
  · next h => obtain ⟨rfl, rfl⟩ := h; rfl
  · rfl

/-- `+cons-need` is `%none` with no register, or the cell itself. -/
theorem consNeed_split (a b : Need) :
    (consNeed a b = Need.none ∧ flattenNeed a ++ flattenNeed b = []) ∨ consNeed a b = Need.pair a b := by
  unfold consNeed
  by_cases h : a = Need.none ∧ b = Need.none
  · obtain ⟨rfl, rfl⟩ := h; left; exact ⟨rfl, rfl⟩
  · right; simp only [h, if_false]

/-- **The registers of the residual are a sublist of the need's.** -/
theorem bakeGo_sublist : ∀ (n : Need) (k : Sock) (imm : List (Nat × Noun)),
    (flattenNeed (bakeGo n k imm).1).Sublist (flattenNeed n)
  | Need.none, _, _ => by simp [bakeGo, flattenNeed]
  | Need.this r, k, imm => by
    unfold bakeGo
    split <;> simp [flattenNeed]
  | Need.pair p q, k, imm => by
    unfold bakeGo
    split
    · simp [flattenNeed]
    · simp only [flatten_consNeed, flattenNeed]
      exact (bakeGo_sublist p _ imm).append (bakeGo_sublist q _ _)
  | Need.both r h t, k, imm => by
    unfold bakeGo
    split
    · simp [flattenNeed]
    · dsimp only
      have hs := (bakeGo_sublist h (So.hed k) imm).append (bakeGo_sublist t (So.tel k) (bakeGo h (So.hed k) imm).2)
      have hc := consNeed_split (bakeGo h (So.hed k) imm).1 (bakeGo t (So.tel k) (bakeGo h (So.hed k) imm).2).1
      split
      · next x y hxy =>
        rcases hc with ⟨hc, -⟩ | hc
        · rw [hc] at hxy; cases hxy
        · rw [hc] at hxy; cases hxy; simp only [flattenNeed]; exact hs.cons₂ r
      · simp only [flattenNeed]; exact (List.nil_sublist _).cons₂ r

/-- **Under a sock that knows nothing, nothing is baked.** -/
theorem bakeGo_no : ∀ (n : Need) (d : Noun) (imm : List (Nat × Noun)),
    flattenNeed (bakeGo n (Sock.mk Cape.no d) imm).1 = flattenNeed n ∧ (bakeGo n (Sock.mk Cape.no d) imm).2 = imm
  | Need.none, _, _ => by simp [bakeGo]
  | Need.this r, d, imm => by simp [bakeGo, bakeTest, Ca.all]
  | Need.pair p q, d, imm => by
    have hp := bakeGo_no p (A 0) imm
    have hq := bakeGo_no q (A 0) (bakeGo p (Sock.mk Cape.no (A 0)) imm).2
    rw [hp.2] at hq
    simp only [bakeGo, bakeTest, Ca.all, Bool.false_and, Bool.false_eq_true, if_false, So.hed, So.tel,
      Sock.dunno, flatten_consNeed, flattenNeed]
    rw [hp.2, hp.1, hq.1, hq.2]
    exact ⟨rfl, rfl⟩
  | Need.both r h t, d, imm => by
    have hh := bakeGo_no h (A 0) imm
    have ht := bakeGo_no t (A 0) (bakeGo h (Sock.mk Cape.no (A 0)) imm).2
    rw [hh.2] at ht
    simp only [bakeGo, bakeTest, Ca.all, Bool.false_and, Bool.false_eq_true, if_false, So.hed, So.tel,
      Sock.dunno]
    rw [hh.2]
    have hc := consNeed_split (bakeGo h (Sock.mk Cape.no (A 0)) imm).1 (bakeGo t (Sock.mk Cape.no (A 0)) imm).1
    split
    · next x y hxy =>
      rcases hc with ⟨hc, -⟩ | hc
      · rw [hc] at hxy; cases hxy
      · rw [hc] at hxy; cases hxy; simp only [flattenNeed]; rw [hh.1, ht.1]; exact ⟨rfl, ht.2⟩
    · next hne =>
      rcases hc with ⟨-, hc⟩ | hc
      · rw [hh.1, ht.1] at hc; simp only [flattenNeed]; rw [hc]; exact ⟨rfl, ht.2⟩
      · exact absurd hc (hne _ _)

/-- The form of `isRun` that `TsOn` wants, on a `range'`. -/
theorem isRun_range' (s m : Nat) : isRun (List.range' s m) ((List.range' s m).headD 0) 0 = true := by
  rw [isRun_iff]
  cases m with
  | zero => rfl
  | succ m => simp [List.range'_succ]

/-- **An infix of a run is a run.** -/
theorem isRun_infix {L L' : List Nat} (hL : isRun L (L.headD 0) 0 = true) (hi : L' <:+: L) :
    isRun L' (L'.headD 0) 0 = true := by
  rw [isRun_iff] at hL
  obtain ⟨a, b, hab⟩ := hi
  have hd : L' = (L.drop a.length).take L'.length := by
    rw [← hab]; simp
  have hlen : L.length - a.length ≥ L'.length := by
    have := congrArg List.length hab; simp at this; omega
  rw [hL, List.drop_range', List.take_range'_of_length_ge hlen] at hd
  rw [hd]
  exact isRun_range' _ _

/-- **The residual is a run when its registers are an infix of the need's**
(a prefix or a suffix of a run, in particular). -/
theorem bake_run_of_infix (n : Need) (k : Sock)
    (hrun : isRun (flattenNeed n) ((flattenNeed n).headD 0) 0 = true)
    (hi : flattenNeed (bakeNeed n k).1 <:+: flattenNeed n) :
    isRun (flattenNeed (bakeNeed n k).1) ((flattenNeed (bakeNeed n k).1).headD 0) 0 = true :=
  isRun_infix hrun hi

/-- **A wholly known head** that fits the head of a cell need, the tail
knowing nothing: the residual's registers are the tail's, a suffix, so the
residual is a run. -/
theorem bake_run_head (p q : Need) (dh dt : Noun) (hc : Ca.all ch = true) (hf : needFits p dh = true)
    (hrun : isRun (flattenNeed (Need.pair p q)) ((flattenNeed (Need.pair p q)).headD 0) 0 = true) :
    flattenNeed (bakeNeed (Need.pair p q) (Sock.mk (Cape.cell ch Cape.no) (C dh dt))).1 = flattenNeed q ∧
    isRun (flattenNeed (bakeNeed (Need.pair p q) (Sock.mk (Cape.cell ch Cape.no) (C dh dt))).1)
      ((flattenNeed (bakeNeed (Need.pair p q) (Sock.mk (Cape.cell ch Cape.no) (C dh dt))).1).headD 0) 0 = true := by
  have hq := bakeGo_no q dt (bakeGo p (Sock.mk ch dh) []).2
  have hp : (bakeGo p (Sock.mk ch dh) []).1 = Need.none := by
    cases p <;> simp [bakeGo, bakeTest, hc, hf]
  have he : flattenNeed (bakeNeed (Need.pair p q) (Sock.mk (Cape.cell ch Cape.no) (C dh dt))).1 = flattenNeed q := by
    cases ch <;>
    simp only [bakeNeed, bakeGo, bakeTest, Ca.all, Bool.and_false, Bool.false_and, Bool.false_eq_true, if_false,
      So.hed, So.tel, flatten_consNeed, hp, flattenNeed, List.nil_append, hq.1] at hc ⊢
  refine ⟨he, ?_⟩
  apply isRun_infix hrun
  rw [he]
  exact (List.suffix_append _ _).isInfix

/-- **A wholly known tail** that fits the tail of a cell need, the head
knowing nothing: the residual's registers are the head's, a prefix. -/
theorem bake_run_tail_pair (p q : Need) (dh dt : Noun) (hc : Ca.all ct = true) (hf : needFits q dt = true)
    (hrun : isRun (flattenNeed (Need.pair p q)) ((flattenNeed (Need.pair p q)).headD 0) 0 = true) :
    flattenNeed (bakeNeed (Need.pair p q) (Sock.mk (Cape.cell Cape.no ct) (C dh dt))).1 = flattenNeed p ∧
    isRun (flattenNeed (bakeNeed (Need.pair p q) (Sock.mk (Cape.cell Cape.no ct) (C dh dt))).1)
      ((flattenNeed (bakeNeed (Need.pair p q) (Sock.mk (Cape.cell Cape.no ct) (C dh dt))).1).headD 0) 0 = true := by
  have hp := bakeGo_no p dh []
  have hq : ∀ imm, (bakeGo q (Sock.mk ct dt) imm).1 = Need.none := by
    intro imm; cases q <;> simp [bakeGo, bakeTest, hc, hf]
  have he : flattenNeed (bakeNeed (Need.pair p q) (Sock.mk (Cape.cell Cape.no ct) (C dh dt))).1 = flattenNeed p := by
    cases ct <;>
    simp only [bakeNeed, bakeGo, bakeTest, Ca.all, Bool.and_false, Bool.false_and, Bool.false_eq_true, if_false,
      So.hed, So.tel, Sock.dunno, flatten_consNeed, hq, flattenNeed, List.append_nil, hp.1] at hc ⊢
  refine ⟨he, ?_⟩
  apply isRun_infix hrun
  rw [he]
  exact (List.prefix_append _ _).isInfix

/-- The same for a `%both`: it keeps its register in front of the head's,
still a prefix. -/
theorem bake_run_tail_both (r : Nat) (h t : Need) (dh dt : Noun) (hc : Ca.all ct = true) (hf : needFits t dt = true)
    (hrun : isRun (flattenNeed (Need.both r h t)) ((flattenNeed (Need.both r h t)).headD 0) 0 = true) :
    flattenNeed (bakeNeed (Need.both r h t) (Sock.mk (Cape.cell Cape.no ct) (C dh dt))).1 = r :: flattenNeed h ∧
    isRun (flattenNeed (bakeNeed (Need.both r h t) (Sock.mk (Cape.cell Cape.no ct) (C dh dt))).1)
      ((flattenNeed (bakeNeed (Need.both r h t) (Sock.mk (Cape.cell Cape.no ct) (C dh dt))).1).headD 0) 0 = true := by
  have hp := bakeGo_no h dh []
  have hq : ∀ imm, (bakeGo t (Sock.mk ct dt) imm).1 = Need.none := by
    intro imm; cases t <;> simp [bakeGo, bakeTest, hc, hf]
  have he : flattenNeed (bakeNeed (Need.both r h t) (Sock.mk (Cape.cell Cape.no ct) (C dh dt))).1
      = r :: flattenNeed h := by
    cases ct <;>
    simp only [bakeNeed, bakeGo, bakeTest, Ca.all, Bool.and_false, Bool.false_and, Bool.false_eq_true, if_false,
      So.hed, So.tel, Sock.dunno, hq] at hc ⊢ <;>
    (have hc' := consNeed_split (bakeGo h (Sock.mk Cape.no dh) []).1 Need.none
     split
     · next x y hxy =>
       rcases hc' with ⟨hc', -⟩ | hc'
       · rw [hc'] at hxy; cases hxy
       · rw [hc'] at hxy; cases hxy; simp only [flattenNeed, List.append_nil]; rw [hp.1]
     · next hne =>
       rcases hc' with ⟨-, hc'⟩ | hc'
       · rw [hp.1] at hc'; simp only [flattenNeed, List.append_nil] at hc' ⊢; rw [hc']
       · exact absurd hc' (hne _ _))
  refine ⟨he, ?_⟩
  apply isRun_infix hrun
  rw [he]
  exact (List.prefix_append (r :: flattenNeed h) (flattenNeed t)).isInfix

end Comp
end SkaModel
end Formalization
