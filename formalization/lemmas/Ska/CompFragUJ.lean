import lemmas.Ska.CompFragUJGen
import lemmas.Ska.CompSevenV
import lemmas.Ska.CompFiveV
import lemmas.Ska.CompFourV

/-!
# The joint induction over `FragU`

README Gaps 12.2 (tenth session).  A part of a parent may run for `%done`,
for an argless `%pick` or under a fork-free `%next`, and the parent needs
more of it than `RunOKV`: under `%next` `RunOKNV`, the tags of the keys it
adds (so that `+sect` of an enclosing `%6` under `%next` threads nothing),
and a clean sure need (for cons).  `UOK` collects every clause, and one
induction over `FragU` proves it.

* `UOK lib nm`: purity, `CleanA`, `OKV` for `%done` and for every argless
  `%pick`, `OKNV`, `TagNV` and `TagV` for every argless `%pick`.
* `uok_x`, `uok_seven4`, `uok_six`, `uok_cons`: the constructors.
* `FragU`: `x` (`FragX`), `seven4` (`[7 [4 p] q]` with `p`, `q` in `FragX`),
  `six` and `cons` with parts in `FragU`.  `runU_uok`, `runU_ok` (the old
  statement), `finishLF_bellContractFU` (the contract on `FragU`).
* `uok_four`, `uok_three` (eleventh session, `CompFourV.lean`): `[4 p]` and
  `[3 p]` with an operand in `FragU`; `finishLF_bellContract_fourProxy`.
* `finishLF_bellContract_consProxy`: the cons
  `[[7 [4 [0 3]] [6 [0 1] [0 1] [1 0]]] [0 1]]`, not covered before.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **What the joint induction proves of one nomm.** -/
structure UOK (lib : Lib) (nm : Nomm) : Prop where
  pure : nm.pure = true
  clean : CleanA S Map nm
  done : OKV (Map := Map) lib (CGoal.done : CGoal S) nm
  pick : ∀ z o : Jmp, z.args = [] → o.args = [] → OKV (Map := Map) lib (CGoal.pick z o : CGoal S) nm
  next : OKNV (S := S) (Map := Map) lib nm
  tagN : TagNV (S := S) (Map := Map) nm
  tagP : ∀ z o : Jmp, z.args = [] → o.args = [] → TagV (Map := Map) (CGoal.pick z o : CGoal S) nm

/-- **Every nomm of `FragX` meets `UOK`.** -/
theorem uok_x (lib : Lib) {nm : Nomm} (hf : FragX (S := S) nm) : UOK (S := S) (Map := Map) lib nm :=
  ⟨fragX_pure hf, runX_clean hf, (okV_fragX lib hf).1, (okV_fragX lib hf).2, okNV_fragX lib hf,
    fun {sur th} _ _ _ _ hj hth hok _ hc _ d0 _ _ _ _ h => condTag_fragX hf (goal := CGoal.next sur th) d0
      ⟨fun r hr => hok.2 r hr, jmpIn_nil hth⟩ hc h,
    fun z o hz ho => fun _ _ hc _ d0 _ _ _ h => condTag_fragX hf (goal := CGoal.pick z o) d0
      ⟨jmpIn_nil hz, jmpIn_nil ho⟩ hc h⟩

/-- **`[7 [4 p] q]` with `p`, `q` in `FragX` meets `UOK`.** -/
theorem uok_seven4 (lib : Lib) {p q : Nomm} (hp : FragX (S := S) p) (hq : FragX (S := S) q) :
    UOK (S := S) (Map := Map) lib (Nomm.n7 (Nomm.n4 p) q) :=
  ⟨by simp only [Nomm.pure, fragX_pure hp, fragX_pure hq, Bool.and_self], cleanA_seven4 q (runX_clean hp),
    fun _ _ hcount b0 d0 hu hcl hcb h => runOKV_seven4 lib (runX_ok lib hp).2.1 (runX_semR lib hp).2.1
      (runX_keeps hp) (aboveX_of_fragX hp) hq hcount b0 d0 hu hcl hcb h,
    fun _ _ hz ho => fun _ hj hcount b0 d0 hu hcl hcb h => runOKV_seven4P lib (runX_ok lib hp).2.1
      (runX_semR lib hp).2.1 (runX_keeps hp) (aboveX_of_fragX hp) hq hcount hz ho hj b0 d0 hu hcl hcb h,
    okNV_seven4 lib hp hq,
    fun {sur th} _ _ _ _ hj hth hok _ hc _ d0 _ _ _ _ h => condTag_seven4 hp hq (goal := CGoal.next sur th) d0
      ⟨fun r hr => hok.2 r hr, jmpIn_nil hth⟩ hc h,
    fun z o hz ho => fun _ _ hc _ d0 _ _ _ h => condTag_seven4 hp hq (goal := CGoal.pick z o) d0
      ⟨jmpIn_nil hz, jmpIn_nil ho⟩ hc h⟩

/-- **`%6` whose parts meet `UOK` meets `UOK`**: `sixP_okV` for `%done` and
`%pick`, `sixNext_okNV` under `%next` (with the branches' `TagNV`), and the
tag clauses `sixNext_tagNV`, `sixP_tagV` (with the test's `TagV`). -/
theorem uok_six (lib : Lib) {c a b : Nomm} (uc : UOK (S := S) (Map := Map) lib c)
    (ua : UOK (S := S) (Map := Map) lib a) (ub : UOK (S := S) (Map := Map) lib b) :
    UOK (S := S) (Map := Map) lib (Nomm.n6 c a b) :=
  ⟨by simp only [Nomm.pure, uc.pure, ua.pure, ub.pure, Bool.and_self], cleanA_six a b uc.pure uc.clean,
    sixP_okV lib uc.pure uc.pick ua.done ub.done,
    fun z o hz ho => sixP_okV lib uc.pure uc.pick (ua.pick z o hz ho) (ub.pick z o hz ho),
    fun hj hth hok hcl hcount b0 d0 hu hcl0 hcb hkg h => sixNext_okNV lib uc.pure uc.pick ua.next ub.next
      ua.tagN ub.tagN hj hth hok hcl hcount b0 d0 hu hcl0 hcb hkg h,
    sixNext_tagNV lib uc.pure uc.tagP ua.next ub.next ua.tagN ub.tagN,
    fun z o hz ho => sixP_tagV lib uc.pure uc.tagP (ua.pick z o hz ho) (ub.pick z o hz ho) (ua.tagP z o hz ho)
      (ub.tagP z o hz ho)⟩

/-- **Cons whose parts meet `UOK` meets `UOK`**: `runOKV_consD`,
`runOKV_consP`, `okNV_cons` from `OKNV` and `CleanN` of the parts, and the
tag clauses `cons_tagNV`, `cons_tagP` from their `TagNV`. -/
theorem uok_cons (lib : Lib) {p q : Nomm} (up : UOK (S := S) (Map := Map) lib p)
    (uq : UOK (S := S) (Map := Map) lib q) : UOK (S := S) (Map := Map) lib (Nomm.cons p q) :=
  ⟨by simp only [Nomm.pure, up.pure, uq.pure, Bool.and_self], cleanA_cons up.pure uq.pure up.clean uq.clean,
    runOKV_consD lib up.next uq.next (CleanA.toN up.clean) (CleanA.toN uq.clean) up.pure uq.pure,
    fun z o _ _ => runOKV_consP lib up.next uq.next (CleanA.toN up.clean) (CleanA.toN uq.clean) up.pure z o,
    okNV_cons lib up.next uq.next (CleanA.toN up.clean) (CleanA.toN uq.clean) up.pure uq.pure,
    cons_tagNV lib up.next uq.next up.tagN uq.tagN up.pure uq.pure,
    fun z o _ _ => cons_tagP lib up.next uq.next up.tagN uq.tagN up.pure z o⟩

/-- **`[7 p q]` with `p` meeting `UOK` and `q` in `Frag` meets `UOK`**:
`runOKV_n7g`, `runOKNV_n7` from `OKNV` of `p`, the tag clauses
`seven_tagV`, `seven_tagNV` from its `TagNV`, `cleanA_seven`. -/
theorem uok_seven (lib : Lib) {p q : Nomm} (up : UOK (S := S) (Map := Map) lib p)
    (hq : ∀ goal : CGoal S, Frag q goal) : UOK (S := S) (Map := Map) lib (Nomm.n7 p q) :=
  ⟨by simp only [Nomm.pure, up.pure, (frag_pure_noSix _ _ (hq CGoal.done)).1, Bool.and_self],
    cleanA_seven hq up.clean,
    fun hg hj hcount b0 d0 hu hcl hcb h => runOKV_n7g lib (goal := CGoal.done) hg (hq _) up.next
      (fun j e => by simp only [GoalJ] at e) hj (by simp only [sixCount] at hcount; omega) b0 d0 hu hcl hcb
      trivial trivial h,
    fun z o hz ho => fun hg hj hcount b0 d0 hu hcl hcb h => runOKV_n7g lib (goal := CGoal.pick z o) hg (hq _)
      up.next (fun j e => by simp only [GoalJ] at e; rcases e with rfl | rfl <;> assumption) hj
      (by simp only [sixCount] at hcount; omega) b0 d0 hu hcl hcb ⟨jmpIn_nil hz, jmpIn_nil ho⟩
      ⟨jmpIn_nil hz, jmpIn_nil ho⟩ h,
    fun hj hth hok hcl hcount b0 d0 hu hcl0 hcb hkg h => runOKNV_n7 lib (hq _) up.next hj hth hok hcl
      (by simp only [sixCount] at hcount; omega) b0 d0 hu hcl0 hcb hkg h,
    fun hj hth hok hcl hcount b0 d0 hu hcl0 hcb hkg h => seven_tagNV lib (hq _) up.tagN hj hth hok hcl
      (by simp only [sixCount] at hcount; omega) b0 d0 hu hcl0 hcb hkg h,
    fun z o hz ho => fun hg hj hcount b0 d0 hu hcl hcb h => seven_tagV lib (goal := CGoal.pick z o) hg (hq _)
      up.tagN (fun j e => by simp only [GoalJ] at e; rcases e with rfl | rfl <;> assumption) hj
      (by simp only [sixCount] at hcount; omega) b0 d0 hu hcl hcb ⟨jmpIn_nil hz, jmpIn_nil ho⟩
      ⟨jmpIn_nil hz, jmpIn_nil ho⟩ h⟩

/-- **`[5 p q]` whose parts meet `UOK` meets `UOK`**: `runOKGV_n5` for
every fork-free goal from `OKNV` and `CleanN` of the parts, `five_tagG`
from their `TagNV`, `cleanA_five`. -/
theorem uok_five (lib : Lib) {p q : Nomm} (up : UOK (S := S) (Map := Map) lib p)
    (uq : UOK (S := S) (Map := Map) lib q) : UOK (S := S) (Map := Map) lib (Nomm.n5 p q) :=
  ⟨by simp only [Nomm.pure, up.pure, uq.pure, Bool.and_self], cleanA_five up.pure up.clean uq.clean,
    fun hg hj hcount b0 d0 hu hcl hcb h => RunOKGV.toV hg (runOKGV_n5 lib up.next uq.next (CleanA.toN up.clean)
      (CleanA.toN uq.clean) up.pure (goal := CGoal.done) trivial hj hcount b0 d0 hu hcl hcb trivial trivial h),
    fun z o hz ho => fun hg hj hcount b0 d0 hu hcl hcb h => RunOKGV.toV hg (runOKGV_n5 lib up.next uq.next
      (CleanA.toN up.clean) (CleanA.toN uq.clean) up.pure (goal := CGoal.pick z o) trivial hj hcount b0 d0 hu hcl
      hcb ⟨jmpIn_nil hz, jmpIn_nil ho⟩ ⟨jmpIn_nil hz, jmpIn_nil ho⟩ h),
    fun {sur th} _ _ _ _ hj hth hok _ hcount b0 d0 hu hcl hcb hkg h => RunOKGV.toNV (runOKGV_n5 lib up.next
      uq.next (CleanA.toN up.clean) (CleanA.toN uq.clean) up.pure (goal := CGoal.next sur th) hok hj hcount b0 d0
      hu hcl hcb ⟨fun r hr => hok.2 r hr, jmpIn_nil hth⟩ ⟨hkg, jmpIn_nil hth⟩ h),
    fun {sur th} _ _ _ _ hj _ hok _ hcount b0 d0 hu hcl hcb _ h => five_tagG lib up.next uq.next up.tagN
      uq.tagN up.pure (goal := CGoal.next sur th) hok hj hcount b0 d0 hu hcl hcb h,
    fun z o _ _ => fun _ hj hcount b0 d0 hu hcl hcb h => five_tagG lib up.next uq.next up.tagN uq.tagN up.pure
      (goal := CGoal.pick z o) trivial hj hcount b0 d0 hu hcl hcb h⟩

/-- **`[4 p]` whose operand meets `UOK` meets `UOK`**: `runOKV_n4D`,
`runOKV_n4P`, `runOKNV_n4` from `OKNV` of the operand, the tag clauses
`four_tagNV`, `four_tagP` from its `TagNV`, `cleanA_four`. -/
theorem uok_four (lib : Lib) {p : Nomm} (up : UOK (S := S) (Map := Map) lib p) :
    UOK (S := S) (Map := Map) lib (Nomm.n4 p) :=
  ⟨by simpa only [Nomm.pure] using up.pure, cleanA_four up.clean, runOKV_n4D lib up.next,
    fun z o hz ho => runOKV_n4P lib up.next z o hz ho, runOKNV_n4 lib up.next, four_tagNV lib up.tagN,
    fun z o _ _ => four_tagP lib up.tagN z o⟩

/-- **`[3 p]` whose operand meets `UOK` meets `UOK`**: `runOKV_n3D`,
`runOKV_n3P`, `runOKNV_n3`, `three_tagNV`, `three_tagP`, `cleanA_three`. -/
theorem uok_three (lib : Lib) {p : Nomm} (up : UOK (S := S) (Map := Map) lib p) :
    UOK (S := S) (Map := Map) lib (Nomm.n3 p) :=
  ⟨by simpa only [Nomm.pure] using up.pure, cleanA_three up.clean, runOKV_n3D lib up.next,
    fun z o hz ho => runOKV_n3P lib up.next z o hz ho, runOKNV_n3 lib up.next, three_tagNV lib up.tagN,
    fun z o _ _ => three_tagP lib up.tagN z o⟩

/-! ## The fragment `FragU` and the top theorem -/

/-- **`FragX` with the proxy runs that compose**: `[7 [4 p] q]` with `p` and
`q` in `FragX` (a run that makes proxies when `q` has a `%6`), and `%6` and
cons whose parts are again in `FragU`.  Later parents are to be added one
constructor at a time. -/
inductive FragU : Nomm → Prop
  | x {nm : Nomm} : FragX (S := S) nm → FragU nm
  | seven4 {p q : Nomm} : FragX (S := S) p → FragX (S := S) q → FragU (Nomm.n7 (Nomm.n4 p) q)
  | six {c a b : Nomm} : FragU c → FragU a → FragU b → FragU (Nomm.n6 c a b)
  | cons {p q : Nomm} : FragU p → FragU q → FragU (Nomm.cons p q)
  | seven {p q : Nomm} : FragU p → (∀ goal : CGoal S, Frag q goal) → FragU (Nomm.n7 p q)
  | five {p q : Nomm} : FragU p → FragU q → FragU (Nomm.n5 p q)
  | four {p : Nomm} : FragU p → FragU (Nomm.n4 p)
  | three {p : Nomm} : FragU p → FragU (Nomm.n3 p)

/-- **Every nomm of `FragU` meets `UOK`** (the joint induction). -/
theorem runU_uok (lib : Lib) {nm : Nomm} (hf : FragU (S := S) nm) : UOK (S := S) (Map := Map) lib nm := by
  induction hf with
  | x h => exact uok_x lib h
  | seven4 hp hq => exact uok_seven4 lib hp hq
  | six _ _ _ ihc iha ihb => exact uok_six lib ihc iha ihb
  | cons _ _ ihp ihq => exact uok_cons lib ihp ihq
  | seven _ hq ihp => exact uok_seven lib ihp hq
  | five _ _ ihp ihq => exact uok_five lib ihp ihq
  | four _ ih => exact uok_four lib ih
  | three _ ih => exact uok_three lib ih

theorem fragU_pure {nm : Nomm} (h : FragU (S := S) nm) : nm.pure = true := by
  induction h with
  | x h => exact fragX_pure h
  | seven4 hp hq => simp only [Nomm.pure, fragX_pure hp, fragX_pure hq, Bool.and_self]
  | six _ _ _ ihc iha ihb => simp only [Nomm.pure, ihc, iha, ihb, Bool.and_self]
  | cons _ _ ihp ihq => simp only [Nomm.pure, ihp, ihq, Bool.and_self]
  | seven _ hq ih => simp only [Nomm.pure, ih, (frag_pure_noSix _ _ (hq CGoal.done)).1, Bool.and_self]
  | five _ _ ihp ihq => simp only [Nomm.pure, ihp, ihq, Bool.and_self]
  | four _ ih => simpa only [Nomm.pure] using ih
  | three _ ih => simpa only [Nomm.pure] using ih

/-- **Every run of `FragU` for `%done`, and for `%pick` with jumps without
arguments, meets `RunOKV`.** -/
theorem runU_ok (lib : Lib) {nm : Nomm} (hf : FragU (S := S) nm) :
    OKV (Map := Map) lib (CGoal.done : CGoal S) nm ∧
    ∀ z o : Jmp, z.args = [] → o.args = [] → OKV (Map := Map) lib (CGoal.pick z o : CGoal S) nm :=
  ⟨(runU_uok lib hf).done, (runU_uok lib hf).pick⟩

/-- **Every run of `FragU` under a fork-free `%next` meets `RunOKNV`.** -/
theorem runU_okNV (lib : Lib) {nm : Nomm} (hf : FragU (S := S) nm) : OKNV (S := S) (Map := Map) lib nm :=
  (runU_uok lib hf).next

/-- **The final pass meets the contract on `FragU`**, when the nomm has at
most 255 `%6`, nothing is baked and the bell's cape has no `[| |]`. -/
theorem finishLF_bellContractFU {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {bl : Bell} {nm : Nomm} (hp : nm.pure = true) (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol nm)
    (hf : FragU (S := S) nm) (hcount : sixCount nm ≤ 255) {cape : Cape} {data : Noun}
    (hbl : bl.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) nm ord cape bake = some c') (N : Needs) : BellContract lib N bl false c' :=
  finishLF_bellContractU hok hp hA (fun h1 => ((runU_ok lib hf).1 trivial trivial hcount (by simp [gen0]) rfl
    upBelow_gen0 clear_gen0 condBelow_gen0 h1).toU) hbl hn hbake h N

/-- **A proxy run inside a branch of a `%6`**:
`[6 [0 1] [7 [4 [0 3]] [6 [0 1] [0 1] [1 0]]] [1 0]]` meets the contract
with no hypothesis beyond the usual ones.  Its raw blocks (subject unknown):
the outer test `brn v7` (with `v7` the subject), the yes branch's
`[0 3]` filled at `0w9`, the increment `inc v6 v4` at `0w8`, the inner test
`brn v4` at `0w6`, and the lazy block `0w4` of the inner `[0 1]` gets
`mov v4 v3`, reading the register the increment of the same branch wrote. -/
theorem finishLF_bellContract_sixProxy {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {bl : Bell}
    (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol
      (Nomm.n6 (Nomm.n0 1) (Nomm.n7 (Nomm.n4 (Nomm.n0 3)) (Nomm.n6 (Nomm.n0 1) (Nomm.n0 1) (Nomm.n1 (A 0))))
        (Nomm.n1 (A 0))))
    {cape : Cape} {data : Noun} (hbl : bl.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) (Nomm.n6 (Nomm.n0 1) (Nomm.n7 (Nomm.n4 (Nomm.n0 3))
      (Nomm.n6 (Nomm.n0 1) (Nomm.n0 1) (Nomm.n1 (A 0)))) (Nomm.n1 (A 0))) ord cape bake = some c')
    (N : Needs) : BellContract lib N bl false c' :=
  finishLF_bellContractFU hok rfl hA
    (FragU.six (FragU.x (FragX.frag fun _ => trivial))
      (FragU.seven4 (FragX.frag fun _ => trivial)
        (FragX.six (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial)))
      (FragU.x (FragX.frag fun _ => trivial)))
    (by decide) hbl hn hbake h N

/-- **A `[7 [4 p] q]` in the test of a `%6`**, which runs for `%pick`:
`[6 [7 [4 [0 3]] [6 [0 1] [1 0] [1 1]]] [1 5] [1 6]]` is in `FragU`. -/
example : FragU (S := S) (Nomm.n6 (Nomm.n7 (Nomm.n4 (Nomm.n0 3))
    (Nomm.n6 (Nomm.n0 1) (Nomm.n1 (A 0)) (Nomm.n1 (A 1)))) (Nomm.n1 (A 5)) (Nomm.n1 (A 6))) :=
  FragU.six (FragU.seven4 (FragX.frag fun _ => trivial)
      (FragX.six (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial)))
    (FragU.x (FragX.frag fun _ => trivial)) (FragU.x (FragX.frag fun _ => trivial))

/-- **A cons whose head makes proxies**:
`[[7 [4 [0 3]] [6 [0 1] [0 1] [1 0]]] [0 1]]` meets the contract with no
hypothesis beyond the usual ones (not covered before `FragU.cons`).  Under
`%done` the cons runs for the register of its `%don` block, the tail `[0 1]`
for the tail register of `+split` and the head under `%next` of the head
register, whose increment reads the subject's tail through proxies in the
lazy blocks of the inner `%6`. -/
theorem finishLF_bellContract_consProxy {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {bl : Bell}
    (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol
      (Nomm.cons (Nomm.n7 (Nomm.n4 (Nomm.n0 3)) (Nomm.n6 (Nomm.n0 1) (Nomm.n0 1) (Nomm.n1 (A 0))))
        (Nomm.n0 1)))
    {cape : Cape} {data : Noun} (hbl : bl.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) (Nomm.cons (Nomm.n7 (Nomm.n4 (Nomm.n0 3))
      (Nomm.n6 (Nomm.n0 1) (Nomm.n0 1) (Nomm.n1 (A 0)))) (Nomm.n0 1)) ord cape bake = some c')
    (N : Needs) : BellContract lib N bl false c' :=
  finishLF_bellContractFU hok rfl hA
    (FragU.cons
      (FragU.seven4 (FragX.frag fun _ => trivial)
        (FragX.six (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial)))
      (FragU.x (FragX.frag fun _ => trivial)))
    (by decide) hbl hn hbake h N

/-- **A cons inside a cons, both heads making proxies**:
`[[7 [4 [0 3]] [6 [0 1] [0 1] [1 0]]] [7 [4 [0 2]] [6 [0 1] [0 1] [1 0]]] [0 1]]`
is in `FragU`. -/
example : FragU (S := S) (Nomm.cons (Nomm.n7 (Nomm.n4 (Nomm.n0 3)) (Nomm.n6 (Nomm.n0 1) (Nomm.n0 1) (Nomm.n1 (A 0))))
    (Nomm.cons (Nomm.n7 (Nomm.n4 (Nomm.n0 2)) (Nomm.n6 (Nomm.n0 1) (Nomm.n0 1) (Nomm.n1 (A 0)))) (Nomm.n0 1))) :=
  FragU.cons (FragU.seven4 (FragX.frag fun _ => trivial)
      (FragX.six (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial)))
    (FragU.cons (FragU.seven4 (FragX.frag fun _ => trivial)
      (FragX.six (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial)))
      (FragU.x (FragX.frag fun _ => trivial)))

/-- **A proxy run in a branch of a `%6` that runs under `%next`**:
`[7 [6 [0 2] [7 [4 [0 3]] [6 [0 1] [0 1] [1 0]]] [1 0]] [4 [0 1]]]` meets the
contract with no hypothesis beyond the usual ones (not covered before
`FragU.seven`).  The increment `[4 [0 1]]` runs first for `%done`, and the
outer `%6` under the fork-free `%next` of its operand register, so its yes
branch, `[7 [4 [0 3]] …]`, makes proxies that `+sect` must skip. -/
theorem finishLF_bellContract_sixNextProxy {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {bl : Bell}
    (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol
      (Nomm.n7 (Nomm.n6 (Nomm.n0 2) (Nomm.n7 (Nomm.n4 (Nomm.n0 3))
        (Nomm.n6 (Nomm.n0 1) (Nomm.n0 1) (Nomm.n1 (A 0)))) (Nomm.n1 (A 0))) (Nomm.n4 (Nomm.n0 1))))
    {cape : Cape} {data : Noun} (hbl : bl.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) (Nomm.n7 (Nomm.n6 (Nomm.n0 2) (Nomm.n7 (Nomm.n4 (Nomm.n0 3))
        (Nomm.n6 (Nomm.n0 1) (Nomm.n0 1) (Nomm.n1 (A 0)))) (Nomm.n1 (A 0))) (Nomm.n4 (Nomm.n0 1)))
      ord cape bake = some c')
    (N : Needs) : BellContract lib N bl false c' :=
  finishLF_bellContractFU hok rfl hA
    (FragU.seven
      (FragU.six (FragU.x (FragX.frag fun _ => trivial))
        (FragU.seven4 (FragX.frag fun _ => trivial)
          (FragX.six (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial)))
        (FragU.x (FragX.frag fun _ => trivial)))
      (fun g => by cases g <;> exact fun _ _ => trivial))
    (by decide) hbl hn hbake h N

/-- **A `%5` whose operand makes proxies**:
`[5 [7 [4 [0 3]] [6 [0 1] [0 1] [1 0]]] [1 1]]` is in `FragU`. -/
example : FragU (S := S) (Nomm.n5 (Nomm.n7 (Nomm.n4 (Nomm.n0 3)) (Nomm.n6 (Nomm.n0 1) (Nomm.n0 1) (Nomm.n1 (A 0))))
    (Nomm.n1 (A 1))) :=
  FragU.five (FragU.seven4 (FragX.frag fun _ => trivial)
      (FragX.six (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial)))
    (FragU.x (FragX.frag fun _ => trivial))

/-- **An increment of a run that makes proxies**:
`[4 [7 [4 [0 3]] [6 [0 1] [0 1] [1 0]]]]` meets the contract with no
hypothesis beyond the usual ones (not covered before `FragU.four`). -/
theorem finishLF_bellContract_fourProxy {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {bl : Bell}
    (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol
      (Nomm.n4 (Nomm.n7 (Nomm.n4 (Nomm.n0 3)) (Nomm.n6 (Nomm.n0 1) (Nomm.n0 1) (Nomm.n1 (A 0))))))
    {cape : Cape} {data : Noun} (hbl : bl.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) (Nomm.n4 (Nomm.n7 (Nomm.n4 (Nomm.n0 3))
      (Nomm.n6 (Nomm.n0 1) (Nomm.n0 1) (Nomm.n1 (A 0))))) ord cape bake = some c')
    (N : Needs) : BellContract lib N bl false c' :=
  finishLF_bellContractFU hok rfl hA
    (FragU.four (FragU.seven4 (FragX.frag fun _ => trivial)
      (FragX.six (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial))))
    (by decide) hbl hn hbake h N

/-- **A cell test of a `%5` whose operand makes proxies, in the test of a
`%6`**: `[6 [3 [5 [7 [4 [0 3]] [6 [0 1] [0 1] [1 0]]] [1 1]]] [0 2] [0 3]]` is
in `FragU`. -/
example : FragU (S := S) (Nomm.n6 (Nomm.n3 (Nomm.n5 (Nomm.n7 (Nomm.n4 (Nomm.n0 3))
    (Nomm.n6 (Nomm.n0 1) (Nomm.n0 1) (Nomm.n1 (A 0)))) (Nomm.n1 (A 1)))) (Nomm.n0 2) (Nomm.n0 3)) :=
  FragU.six (FragU.three (FragU.five (FragU.seven4 (FragX.frag fun _ => trivial)
      (FragX.six (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial)))
      (FragU.x (FragX.frag fun _ => trivial))))
    (FragU.x (FragX.frag fun _ => trivial)) (FragU.x (FragX.frag fun _ => trivial))

end Comp
end SkaModel
end Formalization
