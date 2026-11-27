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
    (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 1) (A 1)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 1) (A 1)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 3)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 25))) (C (A 0) (A 1)))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 4)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 25))) (C (A 0) (A 1)))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 0x6e61656d)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 12)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (A 11) (C (C (A 0x73736f74) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 11)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 10)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 6)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 3) (C (A 0) (A 24))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 2)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 7)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 5)) (C (A 0) (A 24)))) (C (A 1) (A 1)))))))))))))))))))))))) (C (A 11) (C (C (A 0x6f6d656d) (C (A 1) (A 0))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 3) (C (A 0) (A 24))) (C (A 1) (A 1))))) (C (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 24))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 25))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 5)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 50))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 51))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 6)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 50))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 102))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 103))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 7)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 50))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 51))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 10)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 101))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 51))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 2)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 103)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 7) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 926))) (C (A 0) (A 2)))))))) (C (A 0) (A 6)))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 50))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 102))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 11)) (C (A 0) (A 24)))) (C (A 1) (A 1)))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 50))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x79617278)) (C (A 0) (A 50)))) (C (C (A 1) (A 0)) (C (A 5) (C (C (A 1) (A 0x74756f62)) (C (A 0) (A 50))))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 102))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x79617278)) (C (A 0) (A 100)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6b6e7568)) (C (A 0) (A 100)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x646e6168)) (C (A 0) (A 100)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x676f6c73)) (C (A 0) (A 100)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6e61656d)) (C (A 0) (A 100)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x65736f6c)) (C (A 0) (A 100)))) (C (C (A 1) (A 0)) (C (A 5) (C (C (A 1) (A 0x746f7073)) (C (A 0) (A 100))))))))))))))))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6e697073)) (C (A 0) (A 100)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x74756f62)) (C (A 0) (A 100)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x786e696a)) (C (A 0) (A 100)))) (C (C (A 1) (A 0)) (C (A 5) (C (C (A 1) (A 0x6576696c)) (C (A 0) (A 100))))))))))))))))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 101))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 102))) (C (A 0) (A 1)))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))))))))))))))))))))))))))))))))))))))))))))))))))))))

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


/-! ## `+past`

`+past` is door arm `7166` (core axis `11262`, no hint; found as the callee
of the cons case of `+run` on the sample `[nex nom region]`).  Its battery
`paBat` is `[6 paTest [[0 12] 0 30] paHi]`: the inline test of the need
(`[%none ~]`, looks `~` or `[1 ~ ~]`, no fork), which returns `[nex gen]`, and
otherwise `paHi`, the slam of `+hinted` (arm `96116` of `K` at axis `127`, on
`[nom code.long-ska]`, the code at axis `52` of `ctx`), then either `[nex gen]`
or the `%hop` block, `+set-tag` and the bond. -/

def paTest : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 200))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 400)))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 401)))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 201)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 3) (C (A 0) (A 201))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 402)))) (C (C (A 6) (C (C (A 3) (C (A 0) (A 403))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 806)))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 807)))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1)))))))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 202)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1)))))

def paHi : Noun :=
  (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 0x17774) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 58)) (C (A 0) (A 2036)))) (C (A 0) (A 2)))))))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (A 0) (A 115)))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 8) (C (C (A 9) (C (A 0x555de) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 0) (A 123)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (C (C (A 1) (A 0x7478656e)) (C (C (C (A 1) (C (C (A 0x656e6f6e) (A 0)) (A 0))) (C (C (A 1) (A 0)) (C (C (C (A 0) (A 2)) (C (C (A 0) (A 228)) (C (C (A 0) (A 458)) (C (A 1) (A 0))))) (C (A 0) (A 459))))) (C (C (A 1) (A 0)) (C (A 0) (A 2))))) (C (A 0) (A 62))))))))))))) (C (C (A 0) (A 12)) (C (A 0) (A 30))))))

def paBat : Noun := C (A 6) (C paTest (C (C (C (A 0) (A 12)) (C (A 0) (A 30))) paHi))

/-- The arm `+past`: build the gate on its bunt. -/
def paArm : Noun :=
  C (A 8) (C (C (A 1) (C (C (A 0x7478656e) (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))
    (C (A 0) (A 0)))) (C (C (A 0) (A 0)) (A 0)))) (C (C (A 1) paBat) (C (A 0) (A 1))))

theorem comp_past_at : slot? 7166 comp.door = some paArm := by kernel_rfl

/-- The test of `+past`, as the model writes it. -/
noncomputable def paTestB (laz : Lazy CSet) : Bool :=
  decide (laz.sure.ned = Need.none) && HoonSet.small laz.sure.lok && laz.fork.isEmpty

/-- **The test of `+past`** on the noun of a `%next` goal at axis `12`. -/
theorem pa_test (bat rest D th : Noun) (laz : Lazy CSet) :
    nock (C bat (C (C (C (A 0x7478656e) (C laz.toNoun th)) rest) D)) paTest
      = some (loob (paTestB laz)) := by
  obtain ⟨⟨ned, lok⟩, f, b⟩ := laz
  unfold paTest
  cases ned with
  | pair p q =>
    obtain ⟨a, b', hp⟩ := cd_need_cell p
    simp [nock_exec, Lazy.toNoun, Sure.toNoun, Need.toNoun, hp, paTestB, Lazy.sure, eqCode, loob]
  | both r h t =>
    simp [nock_exec, Lazy.toNoun, Sure.toNoun, Need.toNoun, paTestB, Lazy.sure, eqCode_atom, loob,
      Tag.both, Tag.none]
  | this r =>
    simp [nock_exec, Lazy.toNoun, Sure.toNoun, Need.toNoun, paTestB, Lazy.sure, eqCode_atom, loob,
      Tag.this, Tag.none]
  | none =>
    rcases cs_small_cases lok with ⟨hsm, hl | hl⟩ | ⟨hsm, n, l, r, hl, hne⟩
    · cases f <;> simp [nock_exec, Lazy.toNoun, Lazy.forksNoun, Sure.toNoun, Need.toNoun, paTestB,
        Lazy.sure, Lazy.fork, eqCode_atom, eqCode, loob, Tag.none, hl, hsm]
    · cases f <;> simp [nock_exec, Lazy.toNoun, Lazy.forksNoun, Sure.toNoun, Need.toNoun, paTestB,
        Lazy.sure, Lazy.fork, eqCode_atom, eqCode, loob, Tag.none, hl, hsm]
    · rcases n with k | ⟨n1, n2⟩
      · by_cases hk : k = 1
        · subst hk
          rcases l with l | ⟨l1, l2⟩
          · by_cases hl0 : l = 0
            · subst hl0
              rcases r with r | ⟨r1, r2⟩
              · have hr0 : r ≠ 0 := fun e => hne ⟨rfl, rfl, by rw [e]⟩
                simp [nock_exec, Lazy.toNoun, Sure.toNoun, Need.toNoun, paTestB, Lazy.sure, eqCode_atom,
                  loob, Tag.none, hl, hsm, Ne.symm hr0]
              · simp [nock_exec, Lazy.toNoun, Sure.toNoun, Need.toNoun, paTestB, Lazy.sure, eqCode_atom,
                  eqCode, loob, Tag.none, hl, hsm]
            · simp [nock_exec, Lazy.toNoun, Sure.toNoun, Need.toNoun, paTestB, Lazy.sure, eqCode_atom,
                loob, Tag.none, hl, hsm, Ne.symm hl0]
          · simp [nock_exec, Lazy.toNoun, Sure.toNoun, Need.toNoun, paTestB, Lazy.sure, eqCode_atom,
              eqCode, loob, Tag.none, hl, hsm]
        · simp [nock_exec, Lazy.toNoun, Sure.toNoun, Need.toNoun, paTestB, Lazy.sure, eqCode_atom,
            loob, Tag.none, hl, hsm, Ne.symm hk]
      · simp [nock_exec, Lazy.toNoun, Sure.toNoun, Need.toNoun, paTestB, Lazy.sure, eqCode_atom,
          eqCode, loob, Tag.none, hl, hsm]


theorem pa_cond (laz : Lazy CSet) :
    (laz.sure.ned = Need.none ∧ HoonSet.small laz.sure.lok = true ∧ laz.fork.isEmpty = true)
      ↔ paTestB laz = true := by
  simp [paTestB, and_assoc]

variable {ctx : Noun}

/-- **`+past` is `pastL noCode`** on every `next` and every nomm on which
`hinted noCode` returns, in a context with `K` at axis `7` and a code table
at axis `52`.  It touches none of `cache`, `soft`, `sofs`. -/
theorem comp_past (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (x : GenRest) (g : Gen (TreapMap mugF)) (nex : NextL CSet) (nom : Nomm) (region : List Nat)
    (hnom : hinted noCode nom ≠ Option.none) :
    nock (C paBat (C (C nex.goal.toNoun (C nom.toNoun (listNoun A region))) (compCore g x ctx))) paBat
      = (pastL noCode nex nom region g).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  obtain ⟨laz, ⟨args, there⟩⟩ := nex
  have ht := pa_test paBat (C nom.toNoun (listNoun A region)) (compCore g x ctx)
    (Jmp.toNoun ⟨args, there⟩) laz
  simp only [NextL.goal, CGoalL.toNoun]
  nock_open paBat
  rw [nock_op6, ht]
  by_cases hb : paTestB laz = true
  · have hp : (laz.sure.ned = Need.none ∧ HoonSet.small laz.sure.lok = true ∧ laz.fork.isEmpty = true) :=
      (pa_cond laz).2 hb
    simp [hb, loob, nock_exec, pastL, hp, pure, StateT.pure, NextL.goal, CGoalL.toNoun]
  · have hp : ¬ (laz.sure.ned = Need.none ∧ HoonSet.small laz.sure.lok = true ∧ laz.fork.isEmpty = true) :=
      fun h => hb ((pa_cond laz).1 h)
    simp only [Bool.not_eq_true] at hb
    rcases e : hinted noCode nom with _ | b
    · exact absurd e hnom
    unfold pastL
    rw [if_neg hp, e]
    have hh := hd_gate compK cod nom b e
    have he := cf_emit (x := x) hc g ⟨[], [], Termin.hop ⟨args, there⟩⟩
    simp only [Blob.toNoun, listNoun, Termin.toNoun, Tag.hop, Jmp.toNoun] at he
    have hst := comp_set_tag x hc (cfEmitG ⟨[], [], Termin.hop ⟨args, there⟩⟩ g) g.bo region
    have hD2 := comp_emit_at
    have hD3 := comp_set_tag_at
    simp only [compCore] at hst ⊢
    generalize comp.door = Dr at hD2 hD3 he hst ⊢
    nock_open paHi
    obtain ⟨sr, fk, bd⟩ := laz
    cases b
    · simp [hb, loob, nock_exec, pastL, hp, e, pure, StateT.pure, NextL.goal, CGoalL.toNoun, h7, hcode,
        compK_hd, hd_arm, hh, Jmp.toNoun]
    · simp [hb, loob, nock_exec, pastL, hp, e, pure, StateT.pure, NextL.goal, CGoalL.toNoun, h7, hcode,
        compK_hd, hd_arm, hh, Jmp.toNoun, hD2, hD3, comp_emit_arm, he, comp_set_tag_arm, hst, cf_emit_g,
        setTag, bind, StateT.bind, Lazy.toNoun, Lazy.forksNoun, Lazy.bondsNoun, Sure.toNoun, Sure.bunt,
        Need.toNoun, Tag.none, HoonSet.toNoun_empty, jmp0, listNoun, Lazy.sure, Lazy.fork, Lazy.bond]

end Compiler
end Formalization
