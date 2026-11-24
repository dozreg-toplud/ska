import lemmas.Ska.Analysis

/-!
# `fol-loop` within one run: a weight, and where inlining ends

`folLoopR env res`: `fol-loop` with the direct calls answered by a fixed
`res` (as `Ana.folLoop` is with `res` the loop `resolve` at the fuel below).
`folW`: a weight on formulas that counts `%8`, `%9` and `%11` above the `%7`
and `%2` forms that `fol-loop` rewrites them into, so that every recursive
call of `folStep` that stays inside the formula analyses a formula of smaller
weight.

The one call that leaves the formula is inlining (the `%2` case of
`callStep`, on a formula known as `&` that `+inlineable` accepts).  An
inlineable formula has no `%2` and no `%9`, and its rewritten forms make
calls only with `bare-call`, `memo-key` or `defer` set, which never inline, so
an inlined formula inlines nothing (`NoInl`, `folStep_congr`).  Hence
`folLoopR_stable`: on such a formula the loop gives one result at every fuel
from `folW fol` on, whatever `res` is.

The fuel of a formula that inlines is not bounded by its weight alone: the
inlined formula is the data of a sock, which comes from the subject.  For
example `[9 2 [0 1]]` (weight `8`) against a subject `&+[g 0]` whose battery
`g` is a large inlineable formula analyses `g` inline, with the fuel `g`
needs.
-/

namespace Formalization
namespace SkaModel

open Nock

namespace Ana

variable {M : Type → Type → Type} [Treap M] {R : Type}

/-- `fol-loop` with the direct calls answered by a fixed `res`. -/
def folLoopR (env : Env R) (res : ResGo M R) : Nat → FolGoS M R
  | 0 => fun _ _ _ _ _ _ _ => none
  | n + 1 => folStep env res (folLoopR env res n)

/-- **The weight of a formula**: one per node that `fol-loop` analyses, with
`%8`, `%9` and `%11` above the forms they are rewritten into. -/
def folW : Noun → Nat
  | Noun.cell (Noun.cell a b) q => folW (Noun.cell a b) + folW q + 1
  | Noun.cell (Noun.atom 2) (Noun.cell (Noun.cell a b) q) => folW (Noun.cell a b) + folW q + 1
  | Noun.cell (Noun.atom 3) (Noun.cell a b) => folW (Noun.cell a b) + 1
  | Noun.cell (Noun.atom 4) (Noun.cell a b) => folW (Noun.cell a b) + 1
  | Noun.cell (Noun.atom 5) (Noun.cell (Noun.cell a b) q) => folW (Noun.cell a b) + folW q + 1
  | Noun.cell (Noun.atom 6) (Noun.cell (Noun.cell a b) (Noun.cell q r)) =>
      folW (Noun.cell a b) + folW q + folW r + 1
  | Noun.cell (Noun.atom 7) (Noun.cell (Noun.cell a b) q) => folW (Noun.cell a b) + folW q + 1
  | Noun.cell (Noun.atom 8) (Noun.cell (Noun.cell a b) q) => folW (Noun.cell a b) + folW q + 4
  | Noun.cell (Noun.atom 9) (Noun.cell (Noun.atom _) (Noun.cell a b)) => folW (Noun.cell a b) + 5
  | Noun.cell (Noun.atom 10) (Noun.cell (Noun.cell (Noun.atom _) don) (Noun.cell r1 r2)) =>
      folW don + folW (Noun.cell r1 r2) + 1
  | Noun.cell (Noun.atom 11) (Noun.cell (Noun.atom _) (Noun.cell a b)) => folW (Noun.cell a b) + 4
  | Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell (Noun.atom _) (Noun.cell h1 h2)) f) =>
      folW (Noun.cell h1 h2) + folW f + 4
  | Noun.cell (Noun.atom 12) (Noun.cell (Noun.cell a b) q) => folW (Noun.cell a b) + folW q + 1
  | _ => 1

theorem folW_pos (f : Noun) : 1 ≤ folW f := by
  unfold folW; split <;> omega

/-- The calls of `fol-loop` that never inline: an inlineable formula, or a
`%2` on `[0 1]` and an inlineable formula with `bare-call`, `memo-key` or
`defer` set (the forms of `%11 %bare`, `%memo` and `%mean`). -/
def NoInl (fol : Noun) (mk : Option Noun) (bc df : Bool) : Prop :=
  inlineable fol = true ∨
    ∃ x, fol = n3 (A 2) (slot 1) x ∧ inlineable x = true ∧ (bc = true ∨ mk ≠ none ∨ df = true)

/-- `callStep` takes the inline branch only with none of the three flags. -/
theorem callStep_noInl {res : ResGo M R} {go1 go2 : FolGoS M R} {seat mk : Option Noun} {bc df : Bool}
    (h : bc = true ∨ mk ≠ none ∨ df = true) (s f : FolOut) (gen : GenS M R) :
    callStep res go1 seat mk bc df s f gen = callStep res go2 seat mk bc df s f gen := by
  unfold callStep
  split
  · rfl
  · split
    · rename_i hbc
      have hb : ¬ (mk = none ∧ df = false) := by
        rintro ⟨h1, h2⟩
        rcases h with h | h | h
        · cases h
        · exact h h1
        · rw [h] at h2; cases h2
      rw [if_neg (fun e => hb ⟨e.1, e.2.1⟩), if_neg (fun e => hb ⟨e.1, e.2.1⟩)]
    · rfl

/-- What the children of an inlineable formula are: inlineable. -/
theorem inl_cons {a b q : Noun} (h : inlineable (C (C a b) q) = true) :
    inlineable (C a b) = true ∧ inlineable q = true := by
  cases q with
  | atom k => simp [inlineable] at h
  | cell c d => simpa [inlineable] using h

theorem inl_two {x : Noun} : inlineable (n3 (A 2) (slot 1) x) = false := by
  simp [inlineable]

/-- Inverting `shape`. -/
theorem shape_cons {fol a b q : Noun} (h : shape fol = Shape.cons a b q) : fol = C (C a b) q := by
  unfold shape at h; split at h <;> cases h <;> rfl
theorem shape_op2 {fol a b q : Noun} (h : shape fol = Shape.op2 a b q) : fol = C (A 2) (C (C a b) q) := by
  unfold shape at h; split at h <;> cases h <;> rfl
theorem shape_op3 {fol a b : Noun} (h : shape fol = Shape.op3 a b) : fol = C (A 3) (C a b) := by
  unfold shape at h; split at h <;> cases h <;> rfl
theorem shape_op4 {fol a b : Noun} (h : shape fol = Shape.op4 a b) : fol = C (A 4) (C a b) := by
  unfold shape at h; split at h <;> cases h <;> rfl
theorem shape_op5 {fol a b q : Noun} (h : shape fol = Shape.op5 a b q) : fol = C (A 5) (C (C a b) q) := by
  unfold shape at h; split at h <;> cases h <;> rfl
theorem shape_op6 {fol a b q r : Noun} (h : shape fol = Shape.op6 a b q r) :
    fol = C (A 6) (C (C a b) (C q r)) := by
  unfold shape at h; split at h <;> cases h <;> rfl
theorem shape_op7 {fol a b q : Noun} (h : shape fol = Shape.op7 a b q) : fol = C (A 7) (C (C a b) q) := by
  unfold shape at h; split at h <;> cases h <;> rfl
theorem shape_op8 {fol a b q : Noun} (h : shape fol = Shape.op8 a b q) : fol = C (A 8) (C (C a b) q) := by
  unfold shape at h; split at h <;> cases h <;> rfl
theorem shape_op9 {fol a b : Noun} {p : Nat} (h : shape fol = Shape.op9 p a b) :
    fol = C (A 9) (C (A p) (C a b)) := by
  unfold shape at h; split at h <;> cases h <;> rfl
theorem shape_op10 {fol don r1 r2 : Noun} {ax : Nat} (h : shape fol = Shape.op10 ax don r1 r2) :
    fol = C (A 10) (C (C (A ax) don) (C r1 r2)) := by
  unfold shape at h; split at h <;> cases h <;> rfl
theorem shape_op11s {fol a b : Noun} {p : Nat} (h : shape fol = Shape.op11s p a b) :
    fol = C (A 11) (C (A p) (C a b)) := by
  unfold shape at h; split at h <;> cases h <;> rfl
theorem shape_op11d {fol h1 h2 f : Noun} {tag : Nat} (h : shape fol = Shape.op11d tag h1 h2 f) :
    fol = C (A 11) (C (C (A tag) (C h1 h2)) f) := by
  unfold shape at h; split at h <;> cases h <;> rfl
theorem shape_op12 {fol a b q : Noun} (h : shape fol = Shape.op12 a b q) : fol = C (A 12) (C (C a b) q) := by
  unfold shape at h; split at h <;> cases h <;> rfl

omit [Treap M] in
/-- `meanArm` depends on its one call, the `%2` of `defer`. -/
theorem meanArm_congr {go1 go2 : FolGoS M R} {tag : Nat} {hd : FolOut} {seat mk : Option Noun} {bc : Bool}
    (h : ∀ sub seat mk bc gen, go1 (n3 (A 2) (slot 1) (slot 2)) sub seat mk bc true gen =
      go2 (n3 (A 2) (slot 1) (slot 2)) sub seat mk bc true gen) (gen : GenS M R) :
    meanArm go1 tag hd seat mk bc gen = meanArm go2 tag hd seat mk bc gen := by
  simp only [meanArm, h]

/-- One level of the loop depends only on its calls of smaller weight that
never inline, on a formula whose calls never inline. -/
theorem folStep_congr {env : Env R} {res : ResGo M R} {go1 go2 : FolGoS M R} {fol : Noun}
    {mk : Option Noun} {bc df : Bool} (hN : NoInl fol mk bc df)
    (h : ∀ fol' mk' bc' df', folW fol' < folW fol → NoInl fol' mk' bc' df' →
      ∀ sub seat gen, go1 fol' sub seat mk' bc' df' gen = go2 fol' sub seat mk' bc' df' gen)
    (sub : Anno) (seat : Option Noun) (gen : GenS M R) :
    folStep env res go1 fol sub seat mk bc df gen = folStep env res go2 fol sub seat mk bc df gen := by
  rcases hN with hi | ⟨x, rfl, hx, hf⟩
  · have hw : ∀ fol', folW fol' < folW fol → inlineable fol' = true →
        ∀ sub seat gen, go1 fol' sub seat mk bc df gen = go2 fol' sub seat mk bc df gen :=
      fun fol' hw hi' => h fol' mk bc df hw (Or.inl hi')
    have two : ∀ (x : Noun) (mk' : Option Noun) (bc' df' : Bool), folW (n3 (A 2) (slot 1) x) < folW fol →
        inlineable x = true → (bc' = true ∨ mk' ≠ none ∨ df' = true) →
        ∀ sub seat gen, go1 (n3 (A 2) (slot 1) x) sub seat mk' bc' df' gen =
          go2 (n3 (A 2) (slot 1) x) sub seat mk' bc' df' gen :=
      fun x mk' bc' df' hw hx hf => h _ mk' bc' df' hw (Or.inr ⟨x, rfl, hx, hf⟩)
    unfold folStep
    split
    next a b q heq =>
      cases shape_cons heq
      obtain ⟨i1, i2⟩ := inl_cons hi
      simp only [hw (C a b) (by simp only [folW, C]; omega) i1, hw q (by simp only [folW, C]; omega) i2]
    next => rfl
    next => rfl
    next a b q heq =>
      cases shape_op2 heq; simp [inlineable] at hi
    next a b heq =>
      cases shape_op3 heq
      simp only [hw (C a b) (by simp only [folW, C]; omega) (by simpa [inlineable] using hi)]
    next a b heq =>
      cases shape_op4 heq
      simp only [hw (C a b) (by simp only [folW, C]; omega) (by simpa [inlineable] using hi)]
    next a b q heq =>
      cases shape_op5 heq
      cases q with
      | atom k => simp [inlineable] at hi
      | cell c d =>
      simp only [inlineable, Bool.and_eq_true] at hi
      simp only [hw (C a b) (by simp only [folW, C]; omega) hi.1, hw (C c d) (by simp only [folW, C]; omega) hi.2]
    next a b q r heq =>
      cases shape_op6 heq
      cases q with
      | atom k => simp [inlineable] at hi
      | cell c d =>
      cases r with
      | atom k => simp [inlineable] at hi
      | cell e f =>
      simp only [inlineable, Bool.and_eq_true] at hi
      simp only [hw (C a b) (by simp only [folW, C]; omega) hi.1.1, hw (C c d) (by simp only [folW, C]; omega) hi.1.2,
        hw (C e f) (by simp only [folW, C]; omega) hi.2]
    next a b q heq =>
      cases shape_op7 heq
      cases q with
      | atom k => simp [inlineable] at hi
      | cell c d =>
      simp only [inlineable, Bool.and_eq_true] at hi
      simp only [hw (C a b) (by simp only [folW, C]; omega) hi.1, hw (C c d) (by simp only [folW, C]; omega) hi.2]
    next a b q heq =>
      cases shape_op8 heq
      cases q with
      | atom k => simp [inlineable] at hi
      | cell c d =>
      simp only [inlineable, Bool.and_eq_true] at hi
      exact hw _ (by simp only [folW, C, A, slot, n3]; omega) (by simp [inlineable, slot, n3, hi.1, hi.2]) _ _ _
    next p a b heq =>
      cases shape_op9 heq; simp [inlineable] at hi
    next ax don r1 r2 heq =>
      cases shape_op10 heq
      cases don with
      | atom k => simp [inlineable] at hi
      | cell a b =>
      simp only [inlineable, Bool.and_eq_true] at hi
      simp only [hw (C a b) (by simp only [folW, C]; omega) hi.1, hw (C r1 r2) (by simp only [folW, C]; omega) hi.2]
    next p a b heq =>
      cases shape_op11s heq
      have i1 : inlineable (C a b) = true := by simpa [inlineable] using hi
      split
      · exact two _ mk true df (by simp only [folW, C, A, slot, n3, quote]; have := folW_pos (C a b); omega)
          (by simp [inlineable, quote]) (Or.inl rfl) _ _ _
      · simp only [hw (C a b) (by simp only [folW, C]; omega) i1]
    next tag h1 h2 f heq =>
      cases shape_op11d heq
      cases f with
      | atom k => simp [inlineable] at hi
      | cell a b =>
      simp only [inlineable, Bool.and_eq_true] at hi
      have e1 := hw (C h1 h2) (by simp only [folW, C]; omega) hi.2
      have e2 := hw (C a b) (by simp only [folW, C]; omega) hi.1
      have e3 := fun mk' (hk : mk' ≠ none) => two (quote (C a b)) mk' bc df
        (by simp only [folW, C, A, slot, n3, quote]; have := folW_pos (C h1 h2); omega) (by simp [inlineable, quote])
        (Or.inr (Or.inl hk))
      have e4 : ∀ sub seat mk bc gen, go1 (n3 (A 2) (slot 1) (slot 2)) sub seat mk bc true gen =
          go2 (n3 (A 2) (slot 1) (slot 2)) sub seat mk bc true gen := fun sub seat mk' bc' gen =>
        two (slot 2) mk' bc' true (by simp only [folW, C, A, slot, n3]; have := folW_pos (C h1 h2); omega)
          (by simp [inlineable, slot]) (Or.inr (Or.inr rfl)) sub seat gen
      simp only [e1]
      congr 1; funext hh
      split
      · exact e3 _ (by simp) _ _ _
      · simp only [meanArm_congr e4, e2]
    next a b q heq =>
      cases shape_op12 heq
      cases q with
      | atom k => simp [inlineable] at hi
      | cell c d =>
      simp only [inlineable, Bool.and_eq_true] at hi
      simp only [hw (C a b) (by simp only [folW, C]; omega) hi.1, hw (C c d) (by simp only [folW, C]; omega) hi.2]
    next => rfl
  · have h1 : ∀ sub seat gen, go1 (slot 1) sub seat mk bc df gen = go2 (slot 1) sub seat mk bc df gen :=
      h _ _ _ _ (by have := folW_pos x; simp [folW]; omega) (Or.inl (by simp [inlineable]))
    have h2 : ∀ sub seat gen, go1 x sub seat mk bc df gen = go2 x sub seat mk bc df gen :=
      h _ _ _ _ (by simp [folW]; omega) (Or.inl hx)
    simp only [folStep, shape, slot, h1, h2]
    congr 1; funext s; congr 1; funext f
    exact callStep_noInl hf _ _ _

/-- **`fol-loop` within one run ends, on a formula that does not inline**:
with the direct calls fixed, its result is the same at every fuel from
`folW fol` on, crashes included.  An inlined formula is inlineable, so this
covers the analysis of every inlined formula. -/
theorem folLoopR_stable (env : Env R) (res : ResGo M R) :
    ∀ (w : Nat) (fol : Noun) (mk : Option Noun) (bc df : Bool), folW fol ≤ w → NoInl fol mk bc df →
      ∀ n m, folW fol ≤ n → folW fol ≤ m → ∀ sub seat gen,
        folLoopR env res n fol sub seat mk bc df gen = folLoopR env res m fol sub seat mk bc df gen := by
  intro w
  induction w with
  | zero => intro fol _ _ _ hw; have := folW_pos fol; omega
  | succ w ih =>
    intro fol mk bc df hw hN n m hn hm sub seat gen
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := folW_pos fol; omega⟩
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by have := folW_pos fol; omega⟩
    simp only [folLoopR]
    exact folStep_congr hN (fun fol' mk' bc' df' hlt hN' sub seat gen =>
      ih fol' mk' bc' df' (by omega) hN' n m (by omega) (by omega) sub seat gen) sub seat gen

/-- The fuel `folW fol` is enough: every larger fuel gives what it gives. -/
theorem folLoopR_at_weight (env : Env R) (res : ResGo M R) {fol : Noun} {mk : Option Noun} {bc df : Bool}
    (hN : NoInl fol mk bc df) {n : Nat} (hn : folW fol ≤ n) (sub : Anno) (seat : Option Noun) (gen : GenS M R) :
    folLoopR env res n fol sub seat mk bc df gen = folLoopR env res (folW fol) fol sub seat mk bc df gen :=
  folLoopR_stable env res _ fol mk bc df (Nat.le_refl _) hN n _ hn (Nat.le_refl _) sub seat gen

end Ana

end SkaModel
end Formalization
