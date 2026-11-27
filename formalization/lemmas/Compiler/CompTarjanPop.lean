import lemmas.Compiler.CompTarjanCut
import lemmas.Ska.Tarjan
import lemmas.Hoon.SetFolds

/-!
# `+tarjan`: the pop loop against `popLoop` (track Q)

The pop loop `tjPopBat` runs on the trap core `[tjPopBat [out [lowest
[index tcore]]]]`, with `tcore = [tjConn [tjOBat [[[v kids] acc] ctx]]]` the
core of `connect` and `acc = [idx vis stk cur fin]`.  Each turn pops the
head `p` of `stk.acc` (`?~(stk.acc !! ..)`: a crash on `~`), deletes it from
`cur.acc` (`+del:in`), puts it into `out` (`+put:in`) and stops when
`=(v p)` with `[out acc]`.

* `TjSet X p`: `X` is a set noun whose members are those of `p`;
* `tjAccN`: the noun of the state `gen`;
* **`tj_pop`**: on a stack list noun, a set `cur` and a set `out`, the loop
  is `popLoop v stk out cur`: it crashes where the model is `none`, and
  otherwise returns `[out' acc']` with `out'`, `cur'` the sets of the
  model's lists and `stk'` the model's rest of the stack, every other part
  of `acc` unchanged.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel Tarjan

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- `X` is a set noun with the members `p`. -/
def TjSet (X : Noun) (p : Noun → Prop) : Prop := IsSet mugF X ∧ ∀ k, Has X k ↔ p k

/-- The noun of the state `gen` of `+tarjan`: `[idx vis stk cur fin]`. -/
def tjAccN (IDX VIS STK CUR FIN : Noun) : Noun := C IDX (C VIS (C STK (C CUR FIN)))

/-- The core of `connect` on `[[v kids] acc]` in the context `ctx`. -/
def tjConnCore (V KIDS ACC CTX : Noun) : Noun := C tjConn (C tjOBat (C (C (C V KIDS) ACC) CTX))

/-- The core of the pop loop. -/
def tjPopCore (OUT LO IX TC : Noun) : Noun := C tjPopBat (C OUT (C LO (C IX TC)))

/-- One turn's `+del:in` of the popped vertex from `cur`. -/
theorem tj_del {CUR : Noun} {cur : Noun → Bool} (h : TjSet CUR fun k => cur k = true) (p : Noun) :
    ∃ CUR', nock (C in.del.battery (C p (C in.battery (C CUR layer2)))) in.del.battery = some CUR' ∧
      TjSet CUR' fun k => (fun x => if x = p then false else cur x) k = true := by
  obtain ⟨out, he, hs, hh⟩ := del_in layer2 gorIn_morIn_layer2 CUR p h.1
  refine ⟨out, nock_of_eval he, hs, fun k => ?_⟩
  show Has out k ↔ (if k = p then false else cur k) = true
  rw [hh k, h.2 k]
  by_cases e : k = p <;> simp [e]

/-- One turn's `+put:in` of the popped vertex into `out`. -/
theorem tj_put {OUT : Noun} {out : List Noun} (h : TjSet OUT fun k => k ∈ out) (p : Noun) :
    ∃ OUT', nock (C in.put.battery (C p (C in.battery (C OUT layer2)))) in.put.battery = some OUT' ∧
      TjSet OUT' fun k => k ∈ p :: out := by
  obtain ⟨o, he, hs, hh⟩ := put_in layer2 gorIn_morIn_layer2 OUT p h.1
  refine ⟨o, nock_of_eval he, hs, fun k => ?_⟩
  show Has o k ↔ k ∈ p :: out
  rw [hh k, h.2 k, List.mem_cons]

/-- **The pop loop is `popLoop`.** -/
theorem tj_pop {CTX : Noun} (hL : slot? 32767 CTX = some layer2) (LO IX V KIDS IDX VIS FIN : Noun) :
    ∀ (stk out : List Noun) (cur : Noun → Bool) (OUT CUR : Noun),
      TjSet OUT (fun k => k ∈ out) → TjSet CUR (fun k => cur k = true) →
      match popLoop V stk out cur with
      | none => nock (tjPopCore OUT LO IX (tjConnCore V KIDS (tjAccN IDX VIS (listNoun id stk) CUR FIN) CTX))
          tjPopBat = none
      | some (out', stk', cur') => ∃ OUT' CUR', TjSet OUT' (fun k => k ∈ out') ∧
          TjSet CUR' (fun k => cur' k = true) ∧
          nock (tjPopCore OUT LO IX (tjConnCore V KIDS (tjAccN IDX VIS (listNoun id stk) CUR FIN) CTX)) tjPopBat
            = some (C OUT' (tjAccN IDX VIS (listNoun id stk') CUR' FIN))
  | [], out, cur, OUT, CUR, ho, hc => by
    simp only [popLoop]
    rw [tjPopBat_eq]
    simp [tjPopCore, tjConnCore, tjAccN, listNoun, nock_exec]
  | p :: stk, out, cur, OUT, CUR, ho, hc => by
    obtain ⟨CUR', hd, hc'⟩ := tj_del hc p
    obtain ⟨OUT', hp, ho'⟩ := tj_put ho p
    have ih := tj_pop hL LO IX V KIDS IDX VIS FIN stk (p :: out) (fun x => if x = p then false else cur x)
      OUT' CUR' ho' hc'
    simp only [popLoop]
    by_cases e : V = p
    · subst e
      simp only [if_true]
      refine ⟨OUT', CUR', ho', hc', ?_⟩
      conv => lhs; rw [tjPopBat_eq]
      simp [tjPopCore, tjConnCore, tjAccN, listNoun, nock_exec, hL, in.arm_at, in_arm, in.put.arm_at, put_in_arm,
        in.del.arm_at, del_in_arm, hd, hp]
    · simp only [e, if_false]
      revert ih
      cases popLoop V stk (p :: out) (fun x => if x = p then false else cur x) with
      | none =>
        intro ih
        conv => lhs; rw [tjPopBat_eq]
        simp [tjPopCore, tjConnCore, tjAccN, listNoun, nock_exec, hL, in.arm_at, in_arm, in.put.arm_at, put_in_arm,
          in.del.arm_at, del_in_arm, hd, hp, e]
        rw [tjPopBat_eq] at ih
        exact ih
      | some r =>
        obtain ⟨o2, s2, c2⟩ := r
        rintro ⟨OUT2, CUR2, h1, h2, h3⟩
        refine ⟨OUT2, CUR2, h1, h2, ?_⟩
        conv => lhs; rw [tjPopBat_eq]
        simp [tjPopCore, tjConnCore, tjAccN, listNoun, nock_exec, hL, in.arm_at, in_arm, in.put.arm_at, put_in_arm,
          in.del.arm_at, del_in_arm, hd, hp, e]
        rw [tjPopBat_eq] at h3
        exact h3

end Compiler
end Formalization
