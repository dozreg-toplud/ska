import lemmas.Sound

/-!
# An abstract interpreter of Nock for frames

`absNock` runs a formula on an abstract subject and returns the list of the
shapes its product can have.  A shape (`Ab`) is a tree whose leaves are an
unknown noun (`unk`), a constant (`lit`), or the noun at a path of a fixed
base subject `S` (`sub`).  Every call (Nock `2` and `9`) and every computed
atom (Nock `3`, `4`, `5`) returns `unk`; a branch on an unknown test returns
the shapes of both branches.  So nothing is run but the formula itself, and
the run always ends (it is structural on the formula, with fuel for the
kernel).

`absNock_sound`: whatever Nock computes from a subject that a shape
describes, one of the shapes `absNock` returns describes.  `slotAtPath_sub`
reads a fact off a shape: where a shape has `sub q` at a path, every noun it
describes has the noun at `q` of `S` there.  The kernel runs `absNock` on the
pill's `+poke` in `PokeFrame.lean`.
-/

namespace Formalization
namespace Frame

open Nock

/-- The shape of a noun, against a base subject. -/
inductive Ab where
  | unk : Ab
  | sub (p : List Bool) : Ab
  | lit (n : Noun) : Ab
  | cell (a b : Ab) : Ab

/-- The nouns a shape describes, against the base subject `S`. -/
def Ab.Gam (S : Noun) : Ab → Noun → Prop
  | unk, _ => True
  | sub p, n => slotAtPath S p = some n
  | lit m, n => n = m
  | cell a b, n => ∃ h t, n = C h t ∧ a.Gam S h ∧ b.Gam S t

/-- The head (`false`) or the tail (`true`) of a shape. -/
def achild : Bool → Ab → List Ab
  | _, .unk => [.unk]
  | d, .sub p => [.sub (p ++ [d])]
  | _, .lit (Noun.atom _) => []
  | false, .lit (Noun.cell h _) => [.lit h]
  | true, .lit (Noun.cell _ t) => [.lit t]
  | false, .cell a _ => [a]
  | true, .cell _ b => [b]

def aslotPath : List Bool → Ab → List Ab
  | [], a => [a]
  | d :: rest, a => (achild d a).flatMap (aslotPath rest)

def aslot (axis : Nat) (a : Ab) : List Ab :=
  match axisPath axis with
  | none => []
  | some p => aslotPath p a

/-- A shape as a cell, where it can be one. -/
def expand : Ab → List Ab
  | .unk => [.cell .unk .unk]
  | .sub p => [.cell (.sub (p ++ [false])) (.sub (p ++ [true]))]
  | .lit (Noun.atom _) => []
  | .lit (Noun.cell h t) => [.cell (.lit h) (.lit t)]
  | .cell a b => [.cell a b]

def aeditPath : List Bool → Ab → Ab → List Ab
  | [], v, _ => [v]
  | d :: rest, v, a => (expand a).flatMap fun c =>
      match c, d with
      | .cell x y, false => (aeditPath rest v x).map fun x' => .cell x' y
      | .cell x y, true => (aeditPath rest v y).map fun y' => .cell x y'
      | _, _ => []

def aedit (axis : Nat) (v a : Ab) : List Ab :=
  match axisPath axis with
  | none => []
  | some p => aeditPath p v a

/-- The shapes of the product of `f` on a subject of shape `a`. -/
def absNock (fuel : Nat) (a : Ab) (f : Noun) : List Ab :=
  match fuel with
  | 0 => [.unk]
  | k + 1 =>
    match f with
    | Noun.cell (Noun.cell b c) d =>
        (absNock k a (C b c)).flatMap fun x => (absNock k a d).map fun y => .cell x y
    | Noun.cell (Noun.atom 0) (Noun.atom axis) => aslot axis a
    | Noun.cell (Noun.atom 1) n => [.lit n]
    | Noun.cell (Noun.atom 6) (Noun.cell b (Noun.cell c d)) =>
        (absNock k a b).flatMap fun t =>
          match t with
          | .lit (Noun.atom 0) => absNock k a c
          | .lit (Noun.atom 1) => absNock k a d
          | .lit _ => []
          | .cell _ _ => []
          | _ => absNock k a c ++ absNock k a d
    | Noun.cell (Noun.atom 7) (Noun.cell b c) =>
        (absNock k a b).flatMap fun x => absNock k x c
    | Noun.cell (Noun.atom 8) (Noun.cell b c) =>
        (absNock k a b).flatMap fun x => absNock k (.cell x a) c
    | Noun.cell (Noun.atom 10) (Noun.cell (Noun.cell (Noun.atom axis) c) d) =>
        (absNock k a c).flatMap fun v => (absNock k a d).flatMap fun e => aedit axis v e
    | Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell _ _) d) => absNock k a d
    | Noun.cell (Noun.atom 11) (Noun.cell (Noun.atom _) c) => absNock k a c
    | _ => [.unk]

/-! ## Soundness -/

theorem slotAtPath_app (s : Noun) : ∀ (p q : List Bool),
    slotAtPath s (p ++ q) = (slotAtPath s p).bind fun y => slotAtPath y q := by
  intro p
  induction p generalizing s with
  | nil => intro q; simp [slotAtPath]
  | cons d rest ih =>
    intro q
    cases s with
    | atom _ => simp [slotAtPath]
    | cell h t => cases d <;> simp [slotAtPath, ih]

theorem aslotPath_unk : ∀ (p : List Bool) {q : List Bool}, aslotPath p .unk ≠ [.sub q]
  | [], _ => by simp [aslotPath]
  | d :: rest, q => by
    simp only [aslotPath, achild, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact aslotPath_unk rest

theorem aslotPath_sub_eq : ∀ (p r : List Bool), aslotPath p (.sub r) = [.sub (r ++ p)]
  | [], r => by simp [aslotPath]
  | d :: rest, r => by
    simp only [aslotPath, achild, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      aslotPath_sub_eq rest]
    simp

theorem aslotPath_lit : ∀ (p : List Bool) (m : Noun) {q : List Bool}, aslotPath p (.lit m) ≠ [.sub q]
  | [], _, _ => by simp [aslotPath]
  | d :: rest, m, q => by
    cases m with
    | atom _ => simp [aslotPath, achild]
    | cell mh mt =>
      cases d <;> simp only [aslotPath, achild, List.flatMap_cons, List.flatMap_nil,
        List.append_nil] <;> exact aslotPath_lit rest _

theorem slot3_cell (h p : Noun) : slot? 3 (C h p) = some p := by
  rw [slot?_step 3 (by decide)]
  simp [Nock.child]

section
variable {S : Noun}

theorem achild_sound {a : Ab} {h t : Noun} (hx : a.Gam S (C h t)) :
    ∀ d : Bool, ∃ b ∈ achild d a, b.Gam S (if d then t else h) := by
  intro d
  cases a with
  | unk => exact ⟨.unk, by simp [achild], trivial⟩
  | sub p =>
    refine ⟨.sub (p ++ [d]), by simp [achild], ?_⟩
    simp only [Ab.Gam] at hx ⊢
    rw [slotAtPath_app, hx]
    cases d <;> simp [slotAtPath]
  | lit m =>
    simp only [Ab.Gam] at hx
    subst hx
    cases d
    · exact ⟨.lit h, by simp [achild], rfl⟩
    · exact ⟨.lit t, by simp [achild], rfl⟩
  | cell a b =>
    obtain ⟨h', t', e, ha, hb⟩ := hx
    simp only [Noun.cell.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    cases d
    · exact ⟨a, by simp [achild], ha⟩
    · exact ⟨b, by simp [achild], hb⟩

theorem aslotPath_sound : ∀ (p : List Bool) {a : Ab} {x y : Noun}, a.Gam S x →
    slotAtPath x p = some y → ∃ b ∈ aslotPath p a, b.Gam S y
  | [], a, x, y, hx, hy => by
    simp only [slotAtPath, Option.some.injEq] at hy
    subst hy
    exact ⟨a, by simp [aslotPath], hx⟩
  | d :: rest, a, x, y, hx, hy => by
    cases x with
    | atom _ => simp [slotAtPath] at hy
    | cell h t =>
      obtain ⟨b0, hb0, hg⟩ := achild_sound hx d
      have hy' : slotAtPath (if d then t else h) rest = some y := by
        cases d <;> simpa [slotAtPath] using hy
      obtain ⟨b, hb, hgb⟩ := aslotPath_sound rest hg hy'
      exact ⟨b, by simp only [aslotPath, List.mem_flatMap]; exact ⟨b0, hb0, hb⟩, hgb⟩

theorem aslot_sound {axis : Nat} {a : Ab} {x y : Noun} (hx : a.Gam S x)
    (hy : slot? axis x = some y) : ∃ b ∈ aslot axis a, b.Gam S y := by
  unfold slot? at hy
  unfold aslot
  cases e : axisPath axis with
  | none => rw [e] at hy; cases hy
  | some p => rw [e] at hy; exact aslotPath_sound p hx hy

theorem expand_sound {a : Ab} {h t : Noun} (hx : a.Gam S (C h t)) :
    ∃ x y, Ab.cell x y ∈ expand a ∧ x.Gam S h ∧ y.Gam S t := by
  cases a with
  | unk => exact ⟨.unk, .unk, by simp [expand], trivial, trivial⟩
  | sub p =>
    refine ⟨.sub (p ++ [false]), .sub (p ++ [true]), by simp [expand], ?_, ?_⟩ <;>
      simp only [Ab.Gam] at hx ⊢ <;> rw [slotAtPath_app, hx] <;> simp [slotAtPath]
  | lit m =>
    simp only [Ab.Gam] at hx
    subst hx
    exact ⟨.lit h, .lit t, by simp [expand], rfl, rfl⟩
  | cell a b =>
    obtain ⟨h', t', e, ha, hb⟩ := hx
    simp only [Noun.cell.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨a, b, by simp [expand], ha, hb⟩

theorem aeditPath_sound : ∀ (p : List Bool) {v a : Ab} {r x out : Noun}, a.Gam S x →
    v.Gam S r → editAtPath p r x = some out → ∃ o ∈ aeditPath p v a, o.Gam S out
  | [], v, a, r, x, out, _, hv, he => by
    simp only [editAtPath, Option.some.injEq] at he
    subst he
    exact ⟨v, by simp [aeditPath], hv⟩
  | d :: rest, v, a, r, x, out, hx, hv, he => by
    cases x with
    | atom _ => simp [editAtPath] at he
    | cell h t =>
      obtain ⟨x1, y1, hm, hx1, hy1⟩ := expand_sound hx
      cases d with
      | false =>
        simp only [editAtPath] at he
        cases e : editAtPath rest r h with
        | none => rw [e] at he; cases he
        | some h' =>
          rw [e, Option.some.injEq] at he
          subst he
          obtain ⟨o, ho, hgo⟩ := aeditPath_sound rest hx1 hv e
          refine ⟨.cell o y1, ?_, h', t, rfl, hgo, hy1⟩
          simp only [aeditPath, List.mem_flatMap]
          exact ⟨_, hm, by simp only [List.mem_map]; exact ⟨o, ho, rfl⟩⟩
      | true =>
        simp only [editAtPath] at he
        cases e : editAtPath rest r t with
        | none => rw [e] at he; cases he
        | some t' =>
          rw [e, Option.some.injEq] at he
          subst he
          obtain ⟨o, ho, hgo⟩ := aeditPath_sound rest hy1 hv e
          refine ⟨.cell x1 o, ?_, h, t', rfl, hx1, hgo⟩
          simp only [aeditPath, List.mem_flatMap]
          exact ⟨_, hm, by simp only [List.mem_map]; exact ⟨o, ho, rfl⟩⟩

theorem aedit_sound {axis : Nat} {v a : Ab} {r x out : Noun} (hx : a.Gam S x) (hv : v.Gam S r)
    (he : edit? axis r x = some out) : ∃ o ∈ aedit axis v a, o.Gam S out := by
  unfold edit? at he
  unfold aedit
  cases e : axisPath axis with
  | none => rw [e] at he; cases he
  | some p => rw [e] at he; exact aeditPath_sound p hx hv he

theorem mem_unk {k : Nat} {a : Ab} {f : Noun} (h : absNock (k + 1) a f = [.unk]) :
    ∃ r ∈ absNock (k + 1) a f, r.Gam S x := ⟨.unk, by rw [h]; simp, trivial⟩

/-- **Soundness.**  What Nock computes from a subject of shape `a`, one of the
shapes of `absNock` describes. -/
theorem absNock_sound {s f x : Noun} (h : Eval s f x) :
    ∀ (fuel : Nat) (a : Ab), a.Gam S s → ∃ r ∈ absNock fuel a f, r.Gam S x := by
  induction h with
  | @cell s b c d l r _ _ ih1 ih2 =>
    intro fuel a ha
    cases fuel with
    | zero => exact ⟨.unk, by simp [absNock], trivial⟩
    | succ k =>
      obtain ⟨x1, h1, g1⟩ := ih1 k a ha
      obtain ⟨x2, h2, g2⟩ := ih2 k a ha
      refine ⟨.cell x1 x2, ?_, l, r, rfl, g1, g2⟩
      simp only [absNock, List.mem_flatMap, List.mem_map]
      exact ⟨x1, h1, x2, h2, rfl⟩
  | @op0 s axis out hs =>
    intro fuel a ha
    cases fuel with
    | zero => exact ⟨.unk, by simp [absNock], trivial⟩
    | succ k =>
      simp only [absNock]
      exact aslot_sound ha (slot?_iff.2 hs)
  | op1 =>
    intro fuel a ha
    cases fuel with
    | zero => exact ⟨.unk, by simp [absNock], trivial⟩
    | succ k => exact ⟨.lit _, by simp [absNock], rfl⟩
  | op2 => intro fuel a ha; cases fuel <;> exact ⟨.unk, by simp [absNock], trivial⟩
  | op3 => intro fuel a ha; cases fuel <;> exact ⟨.unk, by simp [absNock], trivial⟩
  | op4 => intro fuel a ha; cases fuel <;> exact ⟨.unk, by simp [absNock], trivial⟩
  | op5 => intro fuel a ha; cases fuel <;> exact ⟨.unk, by simp [absNock], trivial⟩
  | op9 => intro fuel a ha; cases fuel <;> exact ⟨.unk, by simp [absNock], trivial⟩
  | @op6_zero s b c d out _ _ ih1 ih2 =>
    intro fuel a ha
    cases fuel with
    | zero => exact ⟨.unk, by simp [absNock], trivial⟩
    | succ k =>
      obtain ⟨t, ht, gt⟩ := ih1 k a ha
      obtain ⟨r, hr, gr⟩ := ih2 k a ha
      refine ⟨r, ?_, gr⟩
      simp only [absNock, List.mem_flatMap]
      refine ⟨t, ht, ?_⟩
      cases t with
      | unk => simp [hr]
      | sub p => simp [hr]
      | lit m => simp only [Ab.Gam] at gt; subst gt; exact hr
      | cell _ _ => obtain ⟨_, _, e, _⟩ := gt; cases e
  | @op6_one s b c d out _ _ ih1 ih2 =>
    intro fuel a ha
    cases fuel with
    | zero => exact ⟨.unk, by simp [absNock], trivial⟩
    | succ k =>
      obtain ⟨t, ht, gt⟩ := ih1 k a ha
      obtain ⟨r, hr, gr⟩ := ih2 k a ha
      refine ⟨r, ?_, gr⟩
      simp only [absNock, List.mem_flatMap]
      refine ⟨t, ht, ?_⟩
      cases t with
      | unk => simp [hr]
      | sub p => simp [hr]
      | lit m => simp only [Ab.Gam] at gt; subst gt; exact hr
      | cell _ _ => obtain ⟨_, _, e, _⟩ := gt; cases e
  | @op7 s b c s' out _ _ ih1 ih2 =>
    intro fuel a ha
    cases fuel with
    | zero => exact ⟨.unk, by simp [absNock], trivial⟩
    | succ k =>
      obtain ⟨x1, h1, g1⟩ := ih1 k a ha
      obtain ⟨r, hr, gr⟩ := ih2 k x1 g1
      exact ⟨r, by simp only [absNock, List.mem_flatMap]; exact ⟨x1, h1, hr⟩, gr⟩
  | @op8 s b c p out _ _ ih1 ih2 =>
    intro fuel a ha
    cases fuel with
    | zero => exact ⟨.unk, by simp [absNock], trivial⟩
    | succ k =>
      obtain ⟨x1, h1, g1⟩ := ih1 k a ha
      obtain ⟨r, hr, gr⟩ := ih2 k (.cell x1 a) ⟨p, s, rfl, g1, ha⟩
      exact ⟨r, by simp only [absNock, List.mem_flatMap]; exact ⟨x1, h1, hr⟩, gr⟩
  | @op10 s axis c d rep base out _ _ he ih1 ih2 =>
    intro fuel a ha
    cases fuel with
    | zero => exact ⟨.unk, by simp [absNock], trivial⟩
    | succ k =>
      obtain ⟨v, hv, gv⟩ := ih1 k a ha
      obtain ⟨e, hb, gb⟩ := ih2 k a ha
      obtain ⟨o, ho, go⟩ := aedit_sound gb gv (edit?_iff.2 he)
      refine ⟨o, ?_, go⟩
      simp only [absNock, List.mem_flatMap]
      exact ⟨v, hv, e, hb, ho⟩
  | @op11_cell s b c d hint prod out _ _ h3 _ ih2 _ =>
    intro fuel a ha
    cases fuel with
    | zero => exact ⟨.unk, by simp [absNock], trivial⟩
    | succ k =>
      obtain ⟨r, hr, gr⟩ := ih2 k a ha
      have e : out = prod := by
        cases h3 with
        | op0 hs =>
          have := slot?_iff.2 hs
          rw [slot3_cell, Option.some.injEq] at this
          exact this.symm
      subst e
      exact ⟨r, by simpa [absNock] using hr, gr⟩
  | @op11_atom s tag c out _ ih =>
    intro fuel a ha
    cases fuel with
    | zero => exact ⟨.unk, by simp [absNock], trivial⟩
    | succ k =>
      obtain ⟨r, hr, gr⟩ := ih k a ha
      exact ⟨r, by simpa [absNock] using hr, gr⟩

/-- Where every shape has `sub q` at the path `p`, every noun they describe
has the noun at `q` of `S` there. -/
theorem slotAtPath_sub : ∀ (p : List Bool) {a : Ab} {x : Noun} {q : List Bool},
    a.Gam S x → aslotPath p a = [.sub q] → slotAtPath x p = slotAtPath S q
  | [], a, x, q, hx, h => by
    simp only [aslotPath, List.cons.injEq, and_true] at h
    subst h
    simp only [Ab.Gam] at hx
    simp [slotAtPath, hx]
  | d :: rest, a, x, q, hx, h => by
    cases a with
    | unk =>
      simp only [aslotPath, achild, List.flatMap_cons, List.flatMap_nil, List.append_nil] at h
      exact absurd h (aslotPath_unk rest)
    | sub p =>
      simp only [aslotPath, achild, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        aslotPath_sub_eq, List.cons.injEq, Ab.sub.injEq, and_true] at h
      subst h
      simp only [Ab.Gam] at hx
      rw [slotAtPath_app, slotAtPath_app, hx]
      cases x <;> cases d <;> simp [slotAtPath]
    | lit m =>
      cases m with
      | atom _ => simp [aslotPath, achild] at h
      | cell mh mt =>
        cases d <;> simp only [aslotPath, achild, List.flatMap_cons, List.flatMap_nil,
          List.append_nil] at h <;> exact absurd h (aslotPath_lit rest _)
    | cell a b =>
      obtain ⟨h', t', rfl, ha, hb⟩ := hx
      cases d
      · simp only [aslotPath, achild, List.flatMap_cons, List.flatMap_nil, List.append_nil] at h
        simpa [slotAtPath] using slotAtPath_sub rest ha h
      · simp only [aslotPath, achild, List.flatMap_cons, List.flatMap_nil, List.append_nil] at h
        simpa [slotAtPath] using slotAtPath_sub rest hb h

end

end Frame
end Formalization
