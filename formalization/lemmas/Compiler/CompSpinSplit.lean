import lemmas.Compiler.CompPruneLink

/-!
# `+spin-split` of the core `K`

`+spin-split` (arm `372` of `K`, `compK_ss`; a wet gate of the library of
`nock-compilation.hoon`) is `+spin` that returns two lists:

    |*  [a=(list) b=* c=_|=(^ [*^ +<+])]
    =>  .(c `$-([_?>(?=(^ a) i.a) _b] [_-:(c) _b])`c)
    =/  acc=[p=(list _-<:(c)) q=(list _->:(c))]  [~ ~]
    |-  ^-  (pair _acc _b)
    ?~  a  [[(flop p.acc) (flop q.acc)] b]
    =^  res  b  (c i.a b)
    $(acc [[-.res p.acc] [+.res q.acc]], a t.a)

The gate `c` is slammed on each element in order with the state `b`; it
returns `[[h t] b']`; the heads go to the first list and the tails to the
second, in order (`+flop` of layer 2 at the end, `flop_gate`).  The model
is `ssM`: the fold in `Option`, stopping at the first crash of the gate.
The arm's bunt runs the mold `(list)` of the library; the kernel evaluates
the arm on `K` once (`ss_arm`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

def ssLoop : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 60)))) (C (C (C (C (A 8) (C (C (A 9) (C (A 0x2fbd7f) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 9) (C (A 0x2fbd7f) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2))))))))) (C (A 0) (A 122))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 0) (A 123)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 248)) (C (A 0) (A 250)))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 250) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 60) (C (A 0) (A 249))) (C (A 10) (C (C (A 6) (C (C (C (A 0) (A 4)) (C (A 0) (A 28))) (C (C (A 0) (A 5)) (C (A 0) (A 29))))) (C (A 0) (A 3)))))))))))))))))))

def ssBat : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 27) (C (A 0) (A 27))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (A 8) (C (C (A 1) ssLoop) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))))

def ssArm : Noun :=
  (C (A 8) (C (C (C (A 7) (C (C (A 7) (C (C (A 9) (C (A 1407) (C (A 0) (A 0x1ffff)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) (C (C (A 1) (C (A 0) (A 0))) (C (A 0) (A 13)))) (C (A 0) (A 1))))))) (C (C (A 1) ssBat) (C (A 0) (A 1)))))

theorem compK_ss : slot? 372 compK = some ssArm := by kernel_rfl

/-- The gate the arm builds on `K`, computed by the kernel. -/
noncomputable def ssGate : Noun := (evalFuel 2000 compK ssArm).getD (A 0)

theorem ss_arm : nock compK ssArm = some ssGate := nock_of_evalFuel (fuel := 2000) (by kernel_rfl)

/-- Its sample bunt. -/
noncomputable def ssBunt : Noun := (slot? 6 ssGate).getD (A 0)

theorem ss_gate_eq : ssGate = C ssBat (C ssBunt compK) := by kernel_rfl

/-- `+spin-split` in `Option`: the gate on each element in order with the
state, the heads and the tails of its products, and the last state. -/
def ssM {α σ β : Type} (G : α → σ → Option (β × β × σ)) : List α → σ → Option (List β × List β × σ)
  | [], s => some ([], [], s)
  | y :: ys, s => (G y s).bind fun r => (ssM G ys r.2.2).map fun q => (r.1 :: q.1, r.2.1 :: q.2.1, q.2.2)

theorem ss_flop (pacc : List Noun) : nock (C flop.battery (C (listN pacc) layer2)) flop.battery
    = some (listN pacc.reverse) := flop_gate layer2 homoIn_layer2 pacc

/-- The loop of `+spin-split`, from the accumulators `pacc`, `qacc` (in
reverse order), for a gate `[cb [cs cc]]` that is `G` on the state nouns. -/
theorem spsp_loop {α σ β : Type} (E : α → Noun) (Eh : β → Noun) (Sn : σ → Noun) (cb cs cc : Noun)
    (G : α → σ → Option (β × β × σ)) : ∀ (l : List α),
    (∀ y ∈ l, ∀ s, nock (C cb (C (C (E y) (Sn s)) cc)) cb = (G y s).map fun r => C (C (Eh r.1) (Eh r.2.1)) (Sn r.2.2)) →
    ∀ (pacc qacc : List Noun) (s : σ),
    nock (C ssLoop (C (C (listN pacc) (listN qacc)) (C ssBat (C (C (listN (l.map E)) (C (Sn s) (C cb (C cs cc)))) compK))))
      ssLoop
      = (ssM G l s).map fun r => C (C (listN (pacc.reverse ++ r.1.map Eh)) (listN (qacc.reverse ++ r.2.1.map Eh)))
          (Sn r.2.2) := by
  have hL := compK_layer2
  intro l
  induction l with
  | nil =>
    intro _ pacc qacc s
    nock_open ssLoop
    simp [nock_exec, ssM, hL, flop.arm_at, flop_arm, ss_flop]
  | cons y ys ih =>
    intro hf pacc qacc s
    have hy := hf y (by simp) s
    cases e : G y s with
    | none =>
      rw [e] at hy
      nock_open ssLoop
      simp [nock_exec, ssM, hy, e]
    | some r =>
      obtain ⟨h, t, s'⟩ := r
      rw [e, Option.map_some] at hy
      have ihs := ih (fun z hz => hf z (by simp [hz])) (Eh h :: pacc) (Eh t :: qacc) s'
      simp only [listN_cons] at ihs
      nock_open ssLoop
      simp [nock_exec, ssM, hy, e, ihs, Function.comp_def]

/-- **`+spin-split`** slammed on a list, a state and a gate `[cb [cs cc]]`
that is `G` on the state nouns: the heads and tails of the products, in
order, and the last state; a crash where the gate crashes. -/
theorem spsp_gate {α σ β : Type} (E : α → Noun) (Eh : β → Noun) (Sn : σ → Noun) (cb cs cc : Noun)
    (G : α → σ → Option (β × β × σ)) (l : List α) (s : σ)
    (hf : ∀ y ∈ l, ∀ s, nock (C cb (C (C (E y) (Sn s)) cc)) cb = (G y s).map fun r => C (C (Eh r.1) (Eh r.2.1)) (Sn r.2.2)) :
    nock (C ssBat (C (C (listN (l.map E)) (C (Sn s) (C cb (C cs cc)))) compK)) ssBat
      = (ssM G l s).map fun r => C (C (listN (r.1.map Eh)) (listN (r.2.1.map Eh))) (Sn r.2.2) := by
  have h := spsp_loop E Eh Sn cb cs cc G l hf [] [] s
  simp only [List.reverse_nil, List.nil_append] at h
  have h0 : listN [] = A 0 := rfl
  rw [h0] at h
  nock_open ssBat
  simp [nock_exec, h]

end Compiler
end Formalization
