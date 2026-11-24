import lemmas.Compiler.CompRunLink

/-!
# `+hinted` and `+past` of `+comp`

`+hinted` is arm `96116` of the core `K` (battery axis `63348`, found by
its `%fast` cord `%hinted`): a gate on `[nomm cod]` (`nomm` at `12`,
`cod` at `13` of its core), whose battery `hdBat` is the `?-` over the
nomm.  The cases `%0`, `%1`, `%3`, `%4`, `%mean`, `%12` are tested
first; the rest sits behind a `%toss` hint (clue: the test of the union of
the remaining cases) and the `~+`, which is the dynamic hint
`[11 [%memo 1 0] body]`: an atom tag with the clue `[1 0]`.  The strict
executor runs the clue and then the body (`nock_op11_cell`), so the memo is
transparent.  A recursive `$(nomm ..)` is `[9 2 10 [12 ..] 0 1]`.

`hd_gate`: on every nomm on which the model `hinted noCode` returns (no
`%2` with a callee is reached, the only place where `+hinted` reads the
code table), the gate returns the model's flag, for every `cod` and every
context.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

/-! ## `+hinted` -/

def hdBat : Noun :=
    (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 1) (A 1)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 1) (A 1)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 3)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 25))) (C (A 0) (A 1)))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 4)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 25))) (C (A 0) (A 1)))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 0x6e61656d)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 12)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (A 11) (C (C (A 0x73736f74) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 11)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 10)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 6)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 3) (C (A 0) (A 24))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 2)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 7)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 5)) (C (A 0) (A 24)))) (C (A 1) (A 1)))))))))))))))))))))))) (C (A 11) (C (C (A 0x6f6d656d) (C (A 1) (A 0))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 3) (C (A 0) (A 24))) (C (A 1) (A 1))))) (C (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 24))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 25))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 5)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 50))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 51))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 6)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 50))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 102))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 103))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 7)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 50))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 51))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 10)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 101))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 51))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 2)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 103)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 7) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 926))) (C (A 0) (A 2)))))))) (C (A 0) (A 6)))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 50))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 102))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 11)) (C (A 0) (A 24)))) (C (A 1) (A 1)))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 50))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x79617278)) (C (A 0) (A 50)))) (C (C (A 1) (A 0)) (C (A 5) (C (C (A 1) (A 0x74756f62)) (C (A 0) (A 50))))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 102))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x79617278)) (C (A 0) (A 100)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6e697073)) (C (A 0) (A 100)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x74756f62)) (C (A 0) (A 100)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x786e696a)) (C (A 0) (A 100)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6576696c)) (C (A 0) (A 100)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6b6e7568)) (C (A 0) (A 100)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x646e6168)) (C (A 0) (A 100)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x676f6c73)) (C (A 0) (A 100)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6e61656d)) (C (A 0) (A 100)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x65736f6c)) (C (A 0) (A 100)))) (C (C (A 1) (A 0)) (C (A 5) (C (C (A 1) (A 0x746f7073)) (C (A 0) (A 100)))))))))))))))))))))))))))))))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 101))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 102))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- The arm `+hinted` of `K`: build the gate on the bunt `[[%0 0] ~]`. -/
def hdArm : Noun :=
  C (A 7) (C (C (A 8) (C (C (A 1) (C (C (A 0) (A 0)) (A 0))) (C (C (A 1) hdBat) (C (A 0) (A 1)))))
    (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x6465746e6968) (C (C (A 0) (A 0x7fff)) (A 0))))) (C (A 0) (A 1)))))

theorem compK_hd : slot? 96116 compK = some hdArm := by kernel_rfl

/-- The arm builds its gate. -/
theorem hd_arm (d : Noun) : nock d hdArm = some (C hdBat (C (C (C (A 0) (A 0)) (A 0)) d)) := by
  unfold hdArm; simp only [nock_exec]

/-- `|(x y)` returns: either `x` is yes, or `x` is no and `y` returns. -/
theorem orB_some' {x y : Option Bool} {b : Bool} (h : orB x y = some b) :
    (x = some true ∧ b = true) ∨ (x = some false ∧ y = some b) := by
  rcases x with _ | _ | _ <;> simp_all [orB]

/-- The static tags: `%bout`, `%xray`, or neither. -/
theorem hd_static_cases (tag : Nat) :
    (hintStatic tag = true ∧ (tag = 0x74756f62 ∨ tag = 0x79617278)) ∨
    (hintStatic tag = false ∧ ¬ (0x74756f62 = tag) ∧ ¬ (0x79617278 = tag)) := by
  by_cases h1 : tag = 0x74756f62
  · subst h1; left; simp [hintStatic, HintTag.bout]
  by_cases h2 : tag = 0x79617278
  · subst h2; left; simp [hintStatic, HintTag.bout, HintTag.xray]
  right
  exact ⟨by simp [hintStatic, HintTag.bout, HintTag.xray, h1, h2], fun e => h1 e.symm, fun e => h2 e.symm⟩

/-- The dynamic tags: one of the eleven, or none of them. -/
theorem hd_dynamic_cases (tag : Nat) :
    (hintDynamic tag = true ∧ (tag = 0x79617278 ∨ tag = 0x6e697073 ∨ tag = 0x74756f62 ∨
      tag = 0x786e696a ∨ tag = 0x6576696c ∨ tag = 0x6b6e7568 ∨ tag = 0x646e6168 ∨
      tag = 0x676f6c73 ∨ tag = 0x6e61656d ∨ tag = 0x65736f6c ∨ tag = 0x746f7073)) ∨
    (hintDynamic tag = false ∧ ¬ (0x79617278 = tag) ∧ ¬ (0x6e697073 = tag) ∧ ¬ (0x74756f62 = tag) ∧
      ¬ (0x786e696a = tag) ∧ ¬ (0x6576696c = tag) ∧ ¬ (0x6b6e7568 = tag) ∧ ¬ (0x646e6168 = tag) ∧
      ¬ (0x676f6c73 = tag) ∧ ¬ (0x6e61656d = tag) ∧ ¬ (0x65736f6c = tag) ∧ ¬ (0x746f7073 = tag)) := by
  by_cases h : hintDynamic tag = true
  · left
    refine ⟨h, ?_⟩
    simp [hintDynamic, HintTag.bout, HintTag.xray, HintTag.spin, HintTag.jinx, HintTag.live,
      HintTag.slog, Tag.hunk, Tag.hand, Tag.lose, Tag.mean, Tag.spot] at h
    simp only [decide_eq_true_eq, or_assoc] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h <;> (have h2 := of_decide_eq_true h; subst h2; simp)
  · right
    have h' : hintDynamic tag = false := by simpa using h
    refine ⟨h', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro e <;> subst e <;>
      simp [hintDynamic, HintTag.bout, HintTag.xray, HintTag.spin, HintTag.jinx, HintTag.live,
        HintTag.slog, Tag.hunk, Tag.hand, Tag.lose, Tag.mean, Tag.spot] at h'


/-- A nomm's noun is a cell, so it is no atom tag. -/
theorem hd_eq_nomm (k : Nat) (p : Nomm) : eqCode (A k) p.toNoun = A 1 := by
  cases p <;> rfl

/-- One case of `+hinted`: the tests, the hints, the recursive calls. -/
macro "hd_simp" : tactic => `(tactic|
  (simp [nock_exec, nock_ite, Nomm.toNoun, wut_nomm_toNoun, hd_eq_nomm, eqCode_atom, Tag.mean,
     loob, ite_some, unitNoun, *]))

/-- **`+hinted` is `hinted noCode`**: slamming the gate on a nomm on which the
model returns (no `%2` with a callee is reached) gives the model's flag, for
every code table `cod` and every context `K`. -/
theorem hd_gate (K cod : Noun) : ∀ (n : Nomm) (b : Bool), hinted noCode n = some b →
    nock (C hdBat (C (C n.toNoun cod) K)) hdBat = some (loob b) := by
  intro n
  induction n with
  | cons p q ihp ihq =>
    intro b h
    simp only [hinted] at h
    nock_open hdBat
    rcases orB_some' h with ⟨hp, rfl⟩ | ⟨hp, hq⟩
    · have e1 := ihp _ hp
      clear ihp ihq h
      simp only [loob] at e1
      hd_simp
    · have e1 := ihp _ hp
      have e2 := ihq _ hq
      clear ihp ihq h
      cases b <;> simp only [loob] at e1 e2 <;> hd_simp
  | n5 p q ihp ihq =>
    intro b h
    simp only [hinted] at h
    nock_open hdBat
    rcases orB_some' h with ⟨hp, rfl⟩ | ⟨hp, hq⟩
    · have e1 := ihp _ hp
      clear ihp ihq h
      simp only [loob] at e1
      hd_simp
    · have e1 := ihp _ hp
      have e2 := ihq _ hq
      clear ihp ihq h
      cases b <;> simp only [loob] at e1 e2 <;> hd_simp
  | n7 p q ihp ihq =>
    intro b h
    simp only [hinted] at h
    nock_open hdBat
    rcases orB_some' h with ⟨hp, rfl⟩ | ⟨hp, hq⟩
    · have e1 := ihp _ hp
      clear ihp ihq h
      simp only [loob] at e1
      hd_simp
    · have e1 := ihp _ hp
      have e2 := ihq _ hq
      clear ihp ihq h
      cases b <;> simp only [loob] at e1 e2 <;> hd_simp
  | n10 a v q ihp ihq =>
    intro b h
    simp only [hinted] at h
    nock_open hdBat
    rcases orB_some' h with ⟨hp, rfl⟩ | ⟨hp, hq⟩
    · have e1 := ihp _ hp
      clear ihp ihq h
      simp only [loob] at e1
      hd_simp
    · have e1 := ihp _ hp
      have e2 := ihq _ hq
      clear ihp ihq h
      cases b <;> simp only [loob] at e1 e2 <;> hd_simp
  | n6 p q r ihp ihq ihr =>
    intro b h
    simp only [hinted] at h
    nock_open hdBat
    rcases orB_some' h with ⟨hp, rfl⟩ | ⟨hp, h'⟩
    · have e1 := ihp _ hp
      clear ihp ihq ihr h
      simp only [loob] at e1
      hd_simp
    · rcases orB_some' h' with ⟨hq, rfl⟩ | ⟨hq, hr⟩
      · have e1 := ihp _ hp
        have e2 := ihq _ hq
        clear ihp ihq ihr h h'
        simp only [loob] at e1 e2
        hd_simp
      · have e1 := ihp _ hp
        have e2 := ihq _ hq
        have e3 := ihr _ hr
        clear ihp ihq ihr h h'
        cases b <;> simp only [loob] at e1 e2 e3 <;> hd_simp
  | n3 p ihp =>
    intro b h
    simp only [hinted] at h
    nock_open hdBat
    have e1 := ihp _ h
    clear ihp h
    cases b <;> simp only [loob] at e1 <;> hd_simp
  | n4 p ihp =>
    intro b h
    simp only [hinted] at h
    nock_open hdBat
    have e1 := ihp _ h
    clear ihp h
    cases b <;> simp only [loob] at e1 <;> hd_simp
  | n0 ax =>
    intro b h
    simp only [hinted, Option.some.injEq] at h
    subst h
    nock_open hdBat
    hd_simp
  | n1 k =>
    intro b h
    simp only [hinted, Option.some.injEq] at h
    subst h
    nock_open hdBat
    hd_simp
  | n12 p q ihp ihq =>
    intro b h
    simp only [hinted, Option.some.injEq] at h
    subst h
    nock_open hdBat
    clear ihp ihq
    hd_simp
  | mean p bl q body k ihp ihq =>
    intro b h
    simp only [hinted, Option.some.injEq] at h
    subst h
    nock_open hdBat
    clear ihp ihq
    hd_simp
  | n2 p q info ihp ihq =>
    intro b h
    rcases info with _ | ⟨bl, k⟩
    · simp only [hinted, Option.some.injEq] at h
      subst h
      nock_open hdBat
      clear ihp ihq
      hd_simp
    · simp [hinted, noCode, orB] at h
  | n11s tag q body ihq =>
    intro b h
    simp only [hinted] at h
    nock_open hdBat
    rcases hd_static_cases tag with ⟨hs, rfl | rfl⟩ | ⟨hs, h1, h2⟩
    · simp [hs, orB] at h; subst h; clear ihq; hd_simp
    · simp [hs, orB] at h; subst h; clear ihq; hd_simp
    · simp only [hs, orB] at h
      have e1 := ihq _ h
      clear ihq h
      cases b <;> simp only [loob] at e1 <;> hd_simp
  | n11d tag hh q body ihh ihq =>
    intro b h
    simp only [hinted] at h
    nock_open hdBat
    rcases hd_dynamic_cases tag with ⟨hs, rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl⟩ |
        ⟨hs, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    all_goals first
      | (simp [hs, orB] at h; subst h; clear ihh ihq; hd_simp; done)
      | skip
    simp only [hs, orB] at h
    rcases orB_some' h with ⟨hp, rfl⟩ | ⟨hp, hq⟩
    · have e1 := ihh _ hp
      clear ihh ihq h
      simp only [loob] at e1
      hd_simp
    · have e1 := ihh _ hp
      have e2 := ihq _ hq
      clear ihh ihq h
      cases b <;> simp only [loob] at e1 e2 <;> hd_simp

end Compiler
end Formalization
