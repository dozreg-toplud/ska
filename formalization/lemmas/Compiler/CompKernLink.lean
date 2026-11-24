import lemmas.Compiler.CompMedeLink
import lemmas.Compiler.CompCopyLink

/-!
# `+kern-need`, `+kern` and `+kerf` of the door of `+comp`

`+kern-need` (door arm `3497462`, found by its `%fast` cord
`%comp-kern-need`) is the gate `|=  [r=@uvre ned=need]` whose battery
pushes `ops=~` and runs the loop `knLoop` (`|-` over the need) on

    [knLoop [ops [knBat [[r ned] [comp.door [gen ctx]]]]]]

with `ops` at `6`, `r` at `60`, `ned` at `61`, `gen` at `126`.  The
loop is `kernLoop` (`kn_loop`): a pair takes a fresh register and goes on
as a `%both` on it, and the `=?` tests `!=(ops-1 ops)` compare lists of
which the first ends with the second (`kernLoop_suf`), so the noun test
is the test of the model (`kn_suf_eq`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

variable {ctx : Noun}

/-- The loop of `+kern-need`. -/
def knLoop : Noun :=
    (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 122)))) (C (C (C (A 0) (A 6)) (C (A 0) (A 126))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 122)))) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 60)) (C (A 0) (A 123)))) (C (C (A 0) (A 0)) (C (C (C (C (A 1) (A 0x766f6d)) (C (C (A 0) (A 60)) (C (A 0) (A 123)))) (C (A 0) (A 6))) (C (A 0) (A 126)))))) (C (A 6) (C (C (A 3) (C (A 0) (A 122))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 31)))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 61) (C (C (A 1) (A 0x68746f62)) (C (C (A 0) (A 2)) (C (A 0) (A 125))))) (C (A 0) (A 3)))))))))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 122))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 31)))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (C (A 0) (A 2)) (C (A 0) (A 1007)))) (C (A 0) (A 3)))))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 10) (C (C (A 2) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 2)) (C (A 0) (A 30)))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (C (C (A 1) (A 0x6c6174)) (C (C (A 0) (A 1014)) (C (A 0) (A 6)))) (C (A 0) (A 2))) (C (A 0) (A 2)))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 30) (C (A 0) (A 2))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 127)))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (C (A 0) (A 2)) (C (A 0) (A 4078)))) (C (A 0) (A 15)))))))) (C (A 7) (C (C (A 10) (C (C (A 2046) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 10) (C (C (A 2) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 2)) (C (A 0) (A 126)))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (C (C (A 1) (A 0x646568)) (C (C (A 0) (A 4086)) (C (A 0) (A 6)))) (C (A 0) (A 2))) (C (A 0) (A 2)))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 2))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (C (C (A 1) (A 0x6c6563)) (C (A 0) (A 4086))) (C (A 0) (A 126)))) (C (A 0) (A 1)))) (C (A 6) (C (C (A 5) (C (C (A 0) (A 1020)) (C (A 0) (A 4086)))) (C (C (A 0) (A 0)) (C (C (C (C (A 1) (A 0x766f6d)) (C (C (A 0) (A 1020)) (C (A 0) (A 4086)))) (C (A 0) (A 126))) (C (A 0) (A 2046)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- The battery of the gate `+kern-need`: `=|  ops`, then the loop. -/
def knBat : Noun :=
  C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) knLoop) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))

/-- The arm `+kern-need`. -/
def knArm : Noun :=
  C (A 7) (C (C (A 8) (C (C (A 1) (C (A 0) (C (A 0x656e6f6e) (A 0)))) (C (C (A 1) knBat) (C (A 0) (A 1)))))
    (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x6465656e2d6e72656b2d706d6f63)
      (C (C (A 0) (A 0x7ffff)) (A 0))))) (C (A 0) (A 1)))))

/-- **`+kern-need` is arm `3497462` of the door.** -/
theorem comp_kn_at : slot? 3497462 comp.door = some knArm := by kernel_rfl

/-! ## The accumulator only grows at the front -/

/-- The length of a noun list. -/
def nlen : Noun → Nat
  | Noun.atom _ => 0
  | Noun.cell _ t => nlen t + 1

theorem nlen_listNoun {α : Type} (f : α → Noun) : ∀ l : List α, nlen (listNoun f l) = l.length
  | [] => rfl
  | x :: l => by simp only [listNoun, nlen, nlen_listNoun f l, List.length_cons]

/-- The test `!=(ops-1 ops)` on a list that ends with `ops`. -/
theorem kn_suf_eq {α : Type} (f : α → Noun) (e ops : List α) :
    (listNoun f (e ++ ops) = listNoun f ops) ↔ (e ++ ops = ops) := by
  constructor
  · intro h
    have := congrArg nlen h
    rw [nlen_listNoun, nlen_listNoun, List.length_append] at this
    have he : e = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst he; rfl
  · intro h; rw [h]

theorem kernBoth_suf (r d : Nat) (kh kt : Nat → List Pole → CM (TreapMap mugF) (List Pole))
    (hh : ∀ x ops g p, kh x ops g = some p → ∃ e, p.1 = e ++ ops)
    (ht : ∀ x ops g p, kt x ops g = some p → ∃ e, p.1 = e ++ ops) :
    ∀ ops g p, kernBoth r d kh kt ops g = some p → ∃ e, p.1 = e ++ ops := by
  intro ops g p h
  simp only [kernBoth, bind, StateT.bind, re, crashM, pure, StateT.pure, Option.bind_some] at h
  cases e1 : kt g.re ops { g with re := g.re + 1 } with
  | none => simp [e1] at h
  | some q1 =>
    obtain ⟨o1, g1⟩ := q1
    obtain ⟨e1', he1⟩ := ht _ _ _ _ e1
    simp only at he1
    subst he1
    simp only [e1, Option.bind_some] at h
    generalize hops : (if e1' ++ ops ≠ ops then Pole.tal d g.re :: (e1' ++ ops) else e1' ++ ops) = ops2 at h
    have hs2 : ∃ e, ops2 = e ++ ops := by
      rw [← hops]; split
      · exact ⟨Pole.tal d g.re :: e1', rfl⟩
      · exact ⟨e1', rfl⟩
    obtain ⟨e2, rfl⟩ := hs2
    cases e3 : kh g1.re (e2 ++ ops) { g1 with re := g1.re + 1 } with
    | none => simp [e3] at h
    | some q3 =>
      obtain ⟨o3, g3⟩ := q3
      obtain ⟨e3', he3⟩ := hh _ _ _ _ e3
      simp only at he3
      subst he3
      simp only [e3, Option.bind_some] at h
      by_cases hrd : r = d
      · simp [hrd, crashM] at h
      · simp only [hrd, if_false, StateT.pure, pure, Option.some.injEq] at h
        subst h
        by_cases hc : e3' ++ (e2 ++ ops) ≠ e2 ++ ops
        · exact ⟨Pole.mov r d :: Pole.cel d :: Pole.hed d g1.re :: (e3' ++ e2), by simp [hc]⟩
        · exact ⟨Pole.mov r d :: Pole.cel d :: (e3' ++ e2), by simp [hc]⟩

/-- **`kernLoop` puts its ops in front of the accumulator.** -/
theorem kernLoop_suf : ∀ (ned : Need) (r : Nat) (ops : List Pole) (g : Gen (TreapMap mugF)) p,
    kernLoop r ned ops g = some p → ∃ e, p.1 = e ++ ops
  | Need.none, r, ops, g, p, h => by
    simp only [kernLoop, pure, StateT.pure, Option.some.injEq] at h
    subst h; exact ⟨[], rfl⟩
  | Need.this d, r, ops, g, p, h => by
    simp only [kernLoop] at h
    split at h
    · simp [crashM] at h
    · simp only [pure, StateT.pure, Option.some.injEq] at h
      subst h; exact ⟨[Pole.mov r d], rfl⟩
  | Need.pair a b, r, ops, g, p, h => by
    simp only [kernLoop, bind, StateT.bind, re, Option.bind_some] at h
    exact kernBoth_suf r g.re _ _ (fun x o g p h => kernLoop_suf a x o g p h)
      (fun x o g p h => kernLoop_suf b x o g p h) ops _ p h
  | Need.both d a b, r, ops, g, p, h => by
    simp only [kernLoop] at h
    exact kernBoth_suf r d _ _ (fun x o g p h => kernLoop_suf a x o g p h)
      (fun x o g p h => kernLoop_suf b x o g p h) ops g p h

/-! ## The loop of `+kern-need` -/

/-- The subject of the loop of `+kern-need`. -/
def knT (x : GenRest) (ctx : Noun) (r : Nat) (ned : Need) (ops : List Pole)
    (g : Gen (TreapMap mugF)) : Noun :=
  C knLoop (C (listNoun Pole.toNoun ops) (C knBat (C (C (A r) ned.toNoun) (compCore g x ctx))))

/-- The loop on `ned` is `kernLoop`, for every source, accumulator and state. -/
def KnAt (x : GenRest) (ctx : Noun) (ned : Need) : Prop :=
  ∀ (r : Nat) (ops : List Pole) (g : Gen (TreapMap mugF)),
    nock (knT x ctx r ned ops g) knLoop
      = (kernLoop r ned ops g).map fun p => C (listNoun Pole.toNoun p.1) (genNoun p.2 x)

end Compiler
end Formalization
