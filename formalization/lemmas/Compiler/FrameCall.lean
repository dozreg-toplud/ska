import lemmas.Compiler.Frame

/-!
# An abstract interpreter that follows some calls

`absNockS` is `absNock` of `Frame.lean` with two more rules for a call (Nock
`2`, and `9` through its expansion `[2 [0 1] 0 b]`).

1. A summary: a list `sm` of entries `⟨pre, fs, post⟩`.  When the core of a
   call is below `pre` and its formula below `fs` (`le`, a decidable
   sufficient test for "every noun the first shape describes, the second
   describes"), the call returns the shapes `post`.
2. A followed call: when the formula of a call is known, as a literal or as a
   path that the resolver `K` maps to a noun of the base, and `fol` accepts
   it, the interpreter runs that formula on the core's shape.

Every other call returns `unk`, as in `absNock`.  The summaries are what
make loops tractable: an entry for a loop says what every run of its battery
on a core of shape `pre` returns, and `absNockS_sound` asks only that the
interpreter itself, run on `pre` with the same summaries, return shapes
below `post` (`SummOK`).  The induction on the derivation of `Eval` meets a
call of the loop to itself at a smaller derivation, so the check is no
circular assumption.
-/

namespace Formalization
namespace FrameCall

open Nock Frame

/-- A sufficient test for inclusion of shapes. -/
def le : Ab → Ab → Bool
  | _, .unk => true
  | .sub p, .sub q => p == q
  | .lit n, .lit m => n == m
  | .cell a b, .cell c d => le a c && le b d
  | .lit (Noun.cell h t), .cell c d => le (.lit h) c && le (.lit t) d
  | _, _ => false

theorem le_sound {S : Noun} : ∀ {a b : Ab} {n : Noun}, le a b = true → a.Gam S n → b.Gam S n
  | _, .unk, _, _, _ => trivial
  | .sub p, .sub q, n, h, g => by
    simp only [le, beq_iff_eq] at h; subst h; exact g
  | .lit m, .lit m', n, h, g => by
    simp only [le, beq_iff_eq] at h; subst h; exact g
  | .cell a b, .cell c d, n, h, g => by
    simp only [le, Bool.and_eq_true] at h
    obtain ⟨x, y, rfl, ga, gb⟩ := g
    exact ⟨x, y, rfl, le_sound h.1 ga, le_sound h.2 gb⟩
  | .lit (Noun.cell x y), .cell c d, n, h, g => by
    simp only [le, Bool.and_eq_true] at h
    simp only [Ab.Gam] at g; subst g
    exact ⟨x, y, rfl, le_sound h.1 rfl, le_sound h.2 rfl⟩
  | .unk, .sub _, _, h, _ => by simp [le] at h
  | .unk, .lit _, _, h, _ => by simp [le] at h
  | .unk, .cell _ _, _, h, _ => by simp [le] at h
  | .sub _, .lit _, _, h, _ => by simp [le] at h
  | .sub _, .cell _ _, _, h, _ => by simp [le] at h
  | .lit _, .sub _, _, h, _ => by simp [le] at h
  | .lit (Noun.atom _), .cell _ _, _, h, _ => by simp [le] at h
  | .cell _ _, .sub _, _, h, _ => by simp [le] at h
  | .cell _ _, .lit _, _, h, _ => by simp [le] at h

/-- The noun a shape stands for, where it is known. -/
def formulaOf (K : List Bool → Option Noun) : Ab → Option Noun
  | .lit n => some n
  | .sub q => K q
  | _ => none

/-- `K` names nouns of the base `S`. -/
def KOK (S : Noun) (K : List Bool → Option Noun) : Prop :=
  ∀ q n, K q = some n → slotAtPath S q = some n

theorem formulaOf_sound {S : Noun} {K : List Bool → Option Noun} (hK : KOK S K) :
    ∀ {a : Ab} {g n : Noun}, formulaOf K a = some g → a.Gam S n → n = g
  | .lit _, _, _, h, gn => by simp only [formulaOf, Option.some.injEq] at h; subst h; exact gn
  | .sub q, _, _, h, gn => by
    simp only [formulaOf] at h
    simp only [Ab.Gam] at gn
    have := hK q _ h
    rw [gn] at this; exact Option.some.inj this
  | .unk, _, _, h, _ => by simp [formulaOf] at h
  | .cell _ _, _, _, h, _ => by simp [formulaOf] at h

/-- A summary entry: a call on a core below `pre` with a formula below `fs`
returns one of the shapes `post`. -/
structure Summ where
  pre : Ab
  fs : Ab
  post : List Ab

section
variable (K : List Bool → Option Noun) (fol : Noun → Bool) (sm : List Summ)

/-- The shapes of the product of `f` on a subject of shape `a`, with calls
summarized or followed. -/
def absNockS : Nat → Ab → Noun → List Ab
  | 0, _, _ => [.unk]
  | k + 1, a, f =>
    let call : Ab → Ab → List Ab := fun x g =>
      match sm.find? (fun e => le x e.pre && le g e.fs) with
      | some e => e.post
      | none =>
        match formulaOf K g with
        | some gf => if fol gf then absNockS k x gf else [.unk]
        | none => [.unk]
    match f with
    | Noun.cell (Noun.cell b c) d =>
        (absNockS k a (C b c)).flatMap fun x => (absNockS k a d).map fun y => .cell x y
    | Noun.cell (Noun.atom 0) (Noun.atom axis) => aslot axis a
    | Noun.cell (Noun.atom 1) n => [.lit n]
    | Noun.cell (Noun.atom 2) (Noun.cell b c) =>
        (absNockS k a b).flatMap fun x => (absNockS k a c).flatMap fun g => call x g
    | Noun.cell (Noun.atom 6) (Noun.cell b (Noun.cell c d)) =>
        (absNockS k a b).flatMap fun t =>
          match t with
          | .lit (Noun.atom 0) => absNockS k a c
          | .lit (Noun.atom 1) => absNockS k a d
          | .lit _ => []
          | .cell _ _ => []
          | _ => absNockS k a c ++ absNockS k a d
    | Noun.cell (Noun.atom 7) (Noun.cell b c) =>
        (absNockS k a b).flatMap fun x => absNockS k x c
    | Noun.cell (Noun.atom 8) (Noun.cell b c) =>
        (absNockS k a b).flatMap fun x => absNockS k (.cell x a) c
    | Noun.cell (Noun.atom 9) (Noun.cell (Noun.atom axis) c) =>
        (absNockS k a c).flatMap fun x => absNockS k x (invoke axis)
    | Noun.cell (Noun.atom 10) (Noun.cell (Noun.cell (Noun.atom axis) c) d) =>
        (absNockS k a c).flatMap fun v => (absNockS k a d).flatMap fun e => aedit axis v e
    | Noun.cell (Noun.atom 11) (Noun.cell (Noun.cell _ _) d) => absNockS k a d
    | Noun.cell (Noun.atom 11) (Noun.cell (Noun.atom _) c) => absNockS k a c
    | _ => [.unk]

/-- The check of one summary entry: the interpreter, run at fuel `n` on its
`pre` with the formula `fs` names, returns shapes below `post` only. -/
def summOK (n : Nat) (e : Summ) : Bool :=
  match formulaOf K e.fs with
  | some gf => (absNockS K fol sm n e.pre gf).all fun r => e.post.any fun p => le r p
  | none => false

end

section
variable {S : Noun} {K : List Bool → Option Noun} {fol : Noun → Bool} {sm : List Summ}

/-- What a derivation of `Eval s f x` gives at every fuel and shape. -/
def First (S : Noun) (K : List Bool → Option Noun) (fol : Noun → Bool) (sm : List Summ)
    (s f x : Noun) : Prop :=
  ∀ (fuel : Nat) (a : Ab), a.Gam S s → ∃ r ∈ absNockS K fol sm fuel a f, r.Gam S x

theorem second_of_first {n : Nat} (hK : KOK S K) (hchk : sm.all (summOK K fol sm n) = true)
    {s f x : Noun} (h1 : First S K fol sm s f x) {e : Summ} (he : e ∈ sm)
    (hp : e.pre.Gam S s) (hf : e.fs.Gam S f) : ∃ p ∈ e.post, p.Gam S x := by
  have hc := List.all_eq_true.1 hchk e he
  unfold summOK at hc
  cases ef : formulaOf K e.fs with
  | none => rw [ef] at hc; cases hc
  | some gf =>
    rw [ef] at hc
    have e1 := formulaOf_sound hK ef hf
    subst e1
    obtain ⟨r, hr, gr⟩ := h1 n e.pre hp
    have := List.all_eq_true.1 hc r hr
    obtain ⟨p, hp', lp⟩ := List.any_eq_true.1 this
    exact ⟨p, hp', le_sound lp gr⟩

theorem call_sound {n k : Nat} (hK : KOK S K) (hchk : sm.all (summOK K fol sm n) = true)
    {s f out : Noun} {x g : Ab} (hx : x.Gam S s) (hg : g.Gam S f)
    (h3 : First S K fol sm s f out) :
    ∃ r ∈ (match sm.find? (fun e => le x e.pre && le g e.fs) with
      | some e => e.post
      | none =>
        match formulaOf K g with
        | some gf => if fol gf then absNockS K fol sm k x gf else [.unk]
        | none => [.unk]), r.Gam S out := by
  cases ef : sm.find? (fun e => le x e.pre && le g e.fs) with
  | some e =>
    have hm := List.mem_of_find?_eq_some ef
    have ht := List.find?_some ef
    simp only [Bool.and_eq_true] at ht
    exact second_of_first hK hchk h3 hm (le_sound ht.1 hx) (le_sound ht.2 hg)
  | none =>
    simp only
    cases eg : formulaOf K g with
    | none => exact ⟨.unk, by simp, trivial⟩
    | some gf =>
      simp only
      have e1 := formulaOf_sound hK eg hg
      subst e1
      by_cases hfo : fol f = true
      · rw [if_pos hfo]; exact h3 k x hx
      · rw [if_neg hfo]; exact ⟨.unk, by simp, trivial⟩

theorem slot3_cell' (h p : Noun) : slot? 3 (C h p) = some p := by
  rw [slot?_step 3 (by decide)]
  simp [Nock.child]

/-- **Soundness**, given the checks of the summaries. -/
theorem absNockS_sound {n : Nat} (hK : KOK S K) (hchk : sm.all (summOK K fol sm n) = true)
    {s f x : Noun} (h : Eval s f x) : First S K fol sm s f x := by
  induction h with
  | @cell s b c d l r _ _ ih1 ih2 =>
    intro fuel a ha
    cases fuel with
    | zero => exact ⟨.unk, by simp [absNockS], trivial⟩
    | succ k =>
      obtain ⟨x1, h1, g1⟩ := ih1 k a ha
      obtain ⟨x2, h2, g2⟩ := ih2 k a ha
      refine ⟨.cell x1 x2, ?_, l, r, rfl, g1, g2⟩
      simp only [absNockS, List.mem_flatMap, List.mem_map]
      exact ⟨x1, h1, x2, h2, rfl⟩
  | @op0 s axis out hs =>
    intro fuel a ha
    cases fuel with
    | zero => exact ⟨.unk, by simp [absNockS], trivial⟩
    | succ k =>
      simp only [absNockS]
      exact aslot_sound ha (slot?_iff.2 hs)
  | op1 =>
    intro fuel a ha
    cases fuel with
    | zero => exact ⟨.unk, by simp [absNockS], trivial⟩
    | succ k => exact ⟨.lit _, by simp [absNockS], rfl⟩
  | @op2 s b c s' f' out _ _ _ ih1 ih2 ih3 =>
    intro fuel a ha
    cases fuel with
    | zero => exact ⟨.unk, by simp [absNockS], trivial⟩
    | succ k =>
      obtain ⟨x1, h1, g1⟩ := ih1 k a ha
      obtain ⟨x2, h2, g2⟩ := ih2 k a ha
      obtain ⟨r, hr, gr⟩ := call_sound (k := k) hK hchk g1 g2 ih3
      refine ⟨r, ?_, gr⟩
      simp only [absNockS, List.mem_flatMap]
      exact ⟨x1, h1, x2, h2, hr⟩
  | op3 => intro fuel a ha; cases fuel <;> exact ⟨.unk, by simp [absNockS], trivial⟩
  | op4 => intro fuel a ha; cases fuel <;> exact ⟨.unk, by simp [absNockS], trivial⟩
  | op5 => intro fuel a ha; cases fuel <;> exact ⟨.unk, by simp [absNockS], trivial⟩
  | @op9 s axis c core out _ _ ih1 ih2 =>
    intro fuel a ha
    cases fuel with
    | zero => exact ⟨.unk, by simp [absNockS], trivial⟩
    | succ k =>
      obtain ⟨x1, h1, g1⟩ := ih1 k a ha
      obtain ⟨r, hr, gr⟩ := ih2 k x1 g1
      refine ⟨r, ?_, gr⟩
      simp only [absNockS, List.mem_flatMap]
      exact ⟨x1, h1, hr⟩
  | @op6_zero s b c d out _ _ ih1 ih2 =>
    intro fuel a ha
    cases fuel with
    | zero => exact ⟨.unk, by simp [absNockS], trivial⟩
    | succ k =>
      obtain ⟨t, ht, gt⟩ := ih1 k a ha
      obtain ⟨r, hr, gr⟩ := ih2 k a ha
      refine ⟨r, ?_, gr⟩
      simp only [absNockS, List.mem_flatMap]
      refine ⟨t, ht, ?_⟩
      cases t with
      | unk => simp [hr]
      | sub p => simp [hr]
      | lit m => simp only [Ab.Gam] at gt; subst gt; exact hr
      | cell _ _ => obtain ⟨_, _, e, _⟩ := gt; cases e
  | @op6_one s b c d out _ _ ih1 ih2 =>
    intro fuel a ha
    cases fuel with
    | zero => exact ⟨.unk, by simp [absNockS], trivial⟩
    | succ k =>
      obtain ⟨t, ht, gt⟩ := ih1 k a ha
      obtain ⟨r, hr, gr⟩ := ih2 k a ha
      refine ⟨r, ?_, gr⟩
      simp only [absNockS, List.mem_flatMap]
      refine ⟨t, ht, ?_⟩
      cases t with
      | unk => simp [hr]
      | sub p => simp [hr]
      | lit m => simp only [Ab.Gam] at gt; subst gt; exact hr
      | cell _ _ => obtain ⟨_, _, e, _⟩ := gt; cases e
  | @op7 s b c s' out _ _ ih1 ih2 =>
    intro fuel a ha
    cases fuel with
    | zero => exact ⟨.unk, by simp [absNockS], trivial⟩
    | succ k =>
      obtain ⟨x1, h1, g1⟩ := ih1 k a ha
      obtain ⟨r, hr, gr⟩ := ih2 k x1 g1
      exact ⟨r, by simp only [absNockS, List.mem_flatMap]; exact ⟨x1, h1, hr⟩, gr⟩
  | @op8 s b c p out _ _ ih1 ih2 =>
    intro fuel a ha
    cases fuel with
    | zero => exact ⟨.unk, by simp [absNockS], trivial⟩
    | succ k =>
      obtain ⟨x1, h1, g1⟩ := ih1 k a ha
      obtain ⟨r, hr, gr⟩ := ih2 k (.cell x1 a) ⟨p, s, rfl, g1, ha⟩
      exact ⟨r, by simp only [absNockS, List.mem_flatMap]; exact ⟨x1, h1, hr⟩, gr⟩
  | @op10 s axis c d rep base out _ _ he ih1 ih2 =>
    intro fuel a ha
    cases fuel with
    | zero => exact ⟨.unk, by simp [absNockS], trivial⟩
    | succ k =>
      obtain ⟨v, hv, gv⟩ := ih1 k a ha
      obtain ⟨e, hb, gb⟩ := ih2 k a ha
      obtain ⟨o, ho, go⟩ := aedit_sound gb gv (edit?_iff.2 he)
      refine ⟨o, ?_, go⟩
      simp only [absNockS, List.mem_flatMap]
      exact ⟨v, hv, e, hb, ho⟩
  | @op11_cell s b c d hint prod out _ _ h3 _ ih2 _ =>
    intro fuel a ha
    cases fuel with
    | zero => exact ⟨.unk, by simp [absNockS], trivial⟩
    | succ k =>
      obtain ⟨r, hr, gr⟩ := ih2 k a ha
      have e : out = prod := by
        cases h3 with
        | op0 hs =>
          have := slot?_iff.2 hs
          rw [slot3_cell', Option.some.injEq] at this
          exact this.symm
      subst e
      exact ⟨r, by simpa [absNockS] using hr, gr⟩
  | @op11_atom s tag c out _ ih =>
    intro fuel a ha
    cases fuel with
    | zero => exact ⟨.unk, by simp [absNockS], trivial⟩
    | succ k =>
      obtain ⟨r, hr, gr⟩ := ih k a ha
      exact ⟨r, by simpa [absNockS] using hr, gr⟩

end

end FrameCall
end Formalization
