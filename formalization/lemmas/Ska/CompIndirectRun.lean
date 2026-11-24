import lemmas.Ska.CompIndirect

/-!
# The indirect call `[2 p q]`: the runs of the subject and the formula

README Gaps 12.11 (fifteenth session).  After `+simple-next`, `+kerf` and the
`%nok` block, the case `%2` of `runLC` runs `q` for `%next (lazy-from-reg
rFol)` into the `%nok` block, `+past`, `p` for `%next (lazy-from-reg rSub)`
into the jump of `q`, and `+copy`.  This is the tail of a cons for the goal
`%next [[rSub rFol] ~]` with that block as its jump, without the block of
`+split`: so `binaryNV_ok`, the composition of the two runs that the cons
uses, gives `RunOKNV` of the cons `[p q]` for that goal from the state after
the `%nok` block (`indirect_mid`).  Its `sem` is what the call needs: entered
on the subject, the code goes on at the `%nok` block with the registers
`rSub` and `rFol` holding the products of `p` and `q` and the registers
below the state kept (in particular, the register of `p`'s product is kept
across `q`'s code), or crashes with the caller's trace when `p` or `q` has
no product.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- The goal of the two runs together: the subject in `a`, the formula in
`b`. -/
def pairSure (a b : Nat) : Sure S := ⟨Need.pair (Need.this a) (Need.this b), HoonSet.empty⟩

/-- **The runs of `p` and `q` of an indirect call, composed**: from a state
`g3` in which the registers `a` (`rSub`) and `b` (`rFol`) are allocated and
no keys of `cond`, and the `%nok` block `o` is emitted, the run of `q` for
`%next (lazy-from-reg b)` into `o`, the run of `p` for `%next
(lazy-from-reg a)` into the jump of `q`, and `+copy` meet `RunOKNV` of the
cons `[p q]` for the goal `%next [[a b] ~]` into `o`.  (`+past` between the
two runs is the identity on a pure `p`, `pastL_pure`.) -/
theorem indirect_mid (lib : Lib) {p q : Nomm} (up : UOK (S := S) (Map := Map) lib p)
    (uq : UOK (S := S) (Map := Map) lib q) {a b o : Nat} {region : List Nat} {g3 g4 g5 g6 : Gen Map}
    {nexF nexS nex : NextL S} (hab : a ≠ b) (ha : a < g3.re) (hb : b < g3.re) (ho1 : 1 ≤ o)
    (ho2 : o < g3.bo) (hcount : sixCount p + sixCount q ≤ 255) (d0 : g3.drop = false) (hu : UpBelow g3)
    (hcl : Clear g3) (hcb : CondBelow g3) (hka : HoonMap.get g3.cond a = Option.none)
    (hkb : HoonMap.get g3.cond b = Option.none)
    (hq : runL q (CGoalL.next (ofSure (lazyReg b)) (jmp0 o)) region g3 = some (nexF, g4))
    (hp : runL p (CGoalL.next (ofSure (lazyReg a)) nexF.th) region g4 = some (nexS, g5))
    (hc : copyL nexS nexF.laz g5 = some (nex, g6)) :
    RunOKNV (Map := Map) lib (Nomm.cons p q) (pairSure a b : Sure S) (jmp0 o) g3 g6 nex := by
  have b0 : 1 ≤ g3.bo := by omega
  have Rq := uq.next (sur := lazyReg b) (th := jmp0 o) ⟨ho1, ho2⟩ rfl
    ⟨trivial, fun r hr => by simp only [lazyReg, NMem] at hr; subst hr; exact hb⟩ trivial (by omega) b0 d0 hu hcl hcb
    (fun r hr => by simp only [lazyReg, NMem] at hr; subst hr; exact hkb) hq
  have d4 : g4.drop = false := Rq.ext.2.2.1.trans d0
  have u4 : UpBelow g4 := Rq.grow.up hu
  have a4 : a < g4.re := Nat.lt_of_lt_of_le ha Rq.ext.1
  have Rp := up.next (sur := lazyReg a) (th := nexF.th) ⟨Rq.lo, Rq.hi⟩ (nextArgs_nil Rq.ent rfl)
    ⟨trivial, fun r hr => by simp only [lazyReg, NMem] at hr; subst hr; exact a4⟩ trivial (by omega)
    (by have := Rq.lo; have := Rq.hi; omega) d4 u4 (hcl.growU Rq.grow) (Rq.cfr.below hcb)
    (fun r hr => by
      simp only [lazyReg, NMem] at hr; subst hr
      rw [Rq.cfr.get_lt ha]; exact hka) hp
  refine binaryNV_ok (nm := Nomm.cons p q) (pureEval_cons p q) (sur := pairSure a b) (th := jmp0 o)
    ⟨⟨trivial, trivial, fun x h1 h2 => hab (by simp only [NMem] at h1 h2; rw [← h1, ← h2])⟩,
      fun r hr => by
        simp only [pairSure, NMem] at hr
        rcases hr with e | e <;> subst e <;> assumption⟩
    (Ext.refl g3) (GrowU.refl g3) rfl hcb
    (fun r hr => Or.inl (Or.inl hr)) (fun r hr => Or.inl (Or.inr hr))
    (fun r h1 h2 => hab (by simp only [lazyReg, NMem] at h1 h2; rw [← h1, ← h2]))
    Rq Rp (CleanA.toN uq.clean (show Clean (lazyReg (S := S) b).ned from trivial) hq)
    (CleanA.toN up.clean (show Clean (lazyReg (S := S) a).ned from trivial) hp) hc hu d0
    (by simp only [sixCount]; omega)
    (fun x y hn => absurd hn (by
      intro h; rcases h with h | h
      · exact h (fitsS_lazyReg a x)
      · exact h (fitsS_lazyReg b y)))
    (fun cf _ k h0 h1 => absurd h1 (Nat.not_lt.mpr h0))
    (fun c _ σ O st regs t gul x y _ _ hx hy => ⟨fun _ => ⟨regs, ⟨hx, hy⟩, fun _ _ => rfl, rfl⟩,
      fun hn => absurd ⟨⟨trivial, trivial⟩, looks_empty _⟩ hn⟩)

end Comp
end SkaModel
end Formalization
