import lemmas.Glue.ProxPlain

/-!
# Every split register is defined earlier in its body: the frame (track G)

LEDGER 2.c, the body-local leaf `SplitDefEnd` of `Glue/ProxPlain.lean`.
`SDS g`: every body of `g` meets `SDBody` (each `%hed s` / `%tal s` comes
after an op of the same body that writes `s`).  `KS P m`: every run of `m`
from a state with `SDS` ends in one, with a result in `P` (the shape of
`KP`, `Glue/GuardStep.lean`, with `SDBody` for `GuardedBody` and no jump
clause).

* `SDx X`: `SDBody` with the splits of the registers in `X` allowed (the
  intermediate lists of `kernBoth`); `sdx_mov`: a `%mov` into `d` in front
  closes `d`; `sdBody_append` (`+add-ops` puts ops in FRONT, the old body's
  indices shift), `sdBody_of_noSplit`.
* `KS` kept by `pure`, `bind`, `if`, the steps that leave the blocks alone,
  `+add-ops` of an `SDBody` list, `+emit` of a block whose body meets
  `SDBody`; the tactic `ksb`.
* **`kernLoop_sdx`**, **`kernNeed_sd`**: the output of `+kern-need` meets
  `SDBody` (every split register is the `%mov` destination in front of its
  `%cel`), with no hypothesis on the need.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Opt Comp Raw

/-! ## Lists -/

/-- `SDBody` with the splits of the registers in `X` allowed. -/
def SDx (X : List Nat) (body : List Pole) : Prop :=
  ∀ i p s, body[i]? = some p → splitReg p = some s →
    s ∈ X ∨ ∃ j : Nat, j < i ∧ ∃ q, body[j]? = some q ∧ aliasDst q = some s

theorem sdBody_of_sdx {body : List Pole} (h : SDx [] body) : SDBody body := by
  intro i p s hp hs
  rcases h i p s hp hs with h | h
  · simp at h
  · exact h

theorem sdx_of_sdBody (X : List Nat) {body : List Pole} (h : SDBody body) : SDx X body :=
  fun i p s hp hs => Or.inr (h i p s hp hs)

theorem sdx_nil (X : List Nat) : SDx X [] := fun i p s h => by simp at h

theorem sdx_mono {X Y : List Nat} (hXY : ∀ x ∈ X, x ∈ Y) {body : List Pole} (h : SDx X body) : SDx Y body := by
  intro i p s hp hs
  rcases h i p s hp hs with h | h
  · exact Or.inl (hXY s h)
  · exact Or.inr h

/-- An op in front whose split register (if any) is allowed. -/
theorem sdx_cons {X : List Nat} {p0 : Pole} {B : List Pole} (h0 : ∀ s, splitReg p0 = some s → s ∈ X)
    (h : SDx X B) : SDx X (p0 :: B) := by
  intro i p s hp hs
  cases i with
  | zero => simp at hp; subst hp; exact Or.inl (h0 s hs)
  | succ i =>
    simp only [List.getElem?_cons_succ] at hp
    rcases h i p s hp hs with h | ⟨j, hj, q, hq, hd⟩
    · exact Or.inl h
    · exact Or.inr ⟨j + 1, by omega, q, by simpa using hq, hd⟩

theorem sdx_ite {X : List Nat} (c : Prop) [Decidable c] {p0 : Pole} {B : List Pole}
    (h0 : ∀ s, splitReg p0 = some s → s ∈ X) (h : SDx X B) : SDx X (if c then p0 :: B else B) := by
  split
  · exact sdx_cons h0 h
  · exact h

theorem sdx_cons_ns {X : List Nat} {p0 : Pole} {B : List Pole} (h0 : splitReg p0 = Option.none) (h : SDx X B) :
    SDx X (p0 :: B) :=
  sdx_cons (fun s hs => by rw [h0] at hs; cases hs) h

/-- **A write of `d` in front closes `d`.** -/
theorem sdx_mov {X : List Nat} {d : Nat} {p0 : Pole} {B : List Pole} (h0 : splitReg p0 = Option.none)
    (hd : aliasDst p0 = some d) (h : SDx (d :: X) B) : SDx X (p0 :: B) := by
  intro i p s hp hs
  cases i with
  | zero => simp at hp; subst hp; rw [h0] at hs; cases hs
  | succ i =>
    simp only [List.getElem?_cons_succ] at hp
    rcases h i p s hp hs with h | ⟨j, hj, q, hq, hd'⟩
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr ⟨0, by omega, p0, rfl, hd⟩
      · exact Or.inl h
    · exact Or.inr ⟨j + 1, by omega, q, by simpa using hq, hd'⟩

theorem sdBody_append {A B : List Pole} (hA : SDBody A) (hB : SDBody B) : SDBody (A ++ B) := by
  intro i p s hp hs
  rcases Nat.lt_or_ge i A.length with hi | hi
  · rw [List.getElem?_append_left hi] at hp
    obtain ⟨j, hj, q, hq, hd⟩ := hA i p s hp hs
    exact ⟨j, hj, q, by rw [List.getElem?_append_left (by omega)]; exact hq, hd⟩
  · rw [List.getElem?_append_right hi] at hp
    obtain ⟨j, hj, q, hq, hd⟩ := hB (i - A.length) p s hp hs
    exact ⟨j + A.length, by omega, q, by rw [List.getElem?_append_right (by omega)]; simpa using hq, hd⟩

theorem sdBody_of_noSplit {A : List Pole} (h : NoSplit A) : SDBody A := by
  intro i p s hp hs
  rw [h p (List.mem_of_getElem? hp)] at hs; cases hs

variable {Map : Type → Type} [HoonMap Map]

/-! ## The frame -/

/-- **Every body of the state meets `SDBody`.** -/
def SDS (g : Comp.Gen Map) : Prop := ∀ o b, HoonMap.get g.blocks o = some b → SDBody b.body

theorem sds_put {bl : Map Blob} {o : Nat} {b : Blob} (h : ∀ k x, HoonMap.get bl k = some x → SDBody x.body)
    (hb : SDBody b.body) : ∀ k x, HoonMap.get (HoonMap.put bl o b) k = some x → SDBody x.body := by
  intro k x hx
  rw [HoonMap.get_put] at hx
  split at hx
  · cases hx; exact hb
  · exact h k x hx

/-- **Every run of `m` keeps `SDS` and returns a result in `P`.** -/
structure KS {α : Type} (P : α → Prop) (m : CM Map α) : Prop where
  k : ∀ g x g', SDS g → m g = some (x, g') → SDS g' ∧ P x

/-- A step that keeps `SDS`, whatever it returns. -/
abbrev KSB {α : Type} (m : CM Map α) : Prop := KS (fun _ : α => True) m

namespace KS

theorem pure' {α : Type} {P : α → Prop} {a : α} (h : P a) : KS P (pure a : CM Map α) := by
  constructor; intro g x g' hb e; cases e; exact ⟨hb, h⟩

theorem bind' {α β : Type} {P : α → Prop} {Q : β → Prop} {m : CM Map α} {f : α → CM Map β}
    (hm : KS P m) (hf : ∀ a, P a → KS Q (f a)) : KS Q (m >>= f) := by
  constructor
  intro g x g' hb e
  obtain ⟨a, g1, h1, h2⟩ := bind_some e
  obtain ⟨b1, pa⟩ := hm.k g a g1 hb h1
  exact (hf a pa).k g1 x g' b1 h2

theorem mono {α : Type} {P Q : α → Prop} {m : CM Map α} (h : KS P m) (hpq : ∀ a, P a → Q a) : KS Q m := by
  constructor
  intro g x g' hb e
  obtain ⟨b1, p⟩ := h.k g x g' hb e
  exact ⟨b1, hpq x p⟩

theorem fail {α : Type} {P : α → Prop} : KS P (fun _ => Option.none : CM Map α) := by
  constructor; intro g x g' _ h; cases h

theorem crash {α : Type} {P : α → Prop} : KS P (crashM : CM Map α) := fail

theorem ite' {α : Type} {P : α → Prop} (c : Prop) [Decidable c] {a b : CM Map α} (ha : KS P a) (hb : KS P b) :
    KS P (if c then a else b) := by
  split
  · exact ha
  · exact hb

/-- A step that leaves the blocks alone. -/
theorem same {α : Type} {m : CM Map α} (h : ∀ g x g', m g = some (x, g') → g'.blocks = g.blocks) : KSB m := by
  constructor
  intro g x g' hb e
  have e1 := h g x g' e
  exact ⟨fun o b hb' => hb o b (by rw [← e1]; exact hb'), trivial⟩

theorem re' : KSB (re : CM Map Nat) := same fun g x g' h => by rw [re_apply] at h; cases h; rfl

theorem oo' : KSB (oo : CM Map Nat) := same fun g x g' h => by cases h; rfl

theorem freshId' : KSB (freshId : CM Map Nat) := same fun g x g' h => by cases h; rfl

theorem idM' : KSB (idM : CM Map Nat) := same fun g x g' h => by cases h; rfl

theorem get' : KSB (get : CM Map (Comp.Gen Map)) := same fun g x g' h => by rw [get_apply] at h; cases h; rfl

theorem getCond' : KSB (getCond : CM Map (Map (Nat × List Nat))) := same fun g x g' h => by cases h; rfl

theorem setTag' (o : Nat) (region : List Nat) : KSB (setTag o region : CM Map Unit) :=
  same fun g x g' h => by
    cases h
    split <;> rfl

theorem copyTag' (frm : Nat) (tos : List Nat) : KSB (copyTag frm tos : CM Map Unit) :=
  same fun g x g' h => by
    unfold copyTag at h
    split at h
    · cases h; rfl
    · obtain ⟨rg, _, e⟩ := Option.map_eq_some_iff.mp h
      cases e; rfl

theorem proxy' (r o : Nat) : KSB (proxy r o : CM Map Nat) :=
  same fun g x g' h => by
    unfold proxy at h
    simp only at h
    split at h
    · cases h; rfl
    · obtain ⟨tag, _, e⟩ := Option.map_eq_some_iff.mp h
      cases e; rfl

theorem liftO' {α : Type} (x : Option α) : KSB (liftO x : CM Map α) :=
  same fun g a g' h => by
    obtain ⟨b, _, e⟩ := Option.map_eq_some_iff.mp h
    cases e; rfl

theorem lift' {α : Type} (x : Option α) : KSB ((fun g => x.map fun a => (a, g)) : CM Map α) :=
  same fun g a g' h => by
    obtain ⟨b, _, e⟩ := Option.map_eq_some_iff.mp h
    cases e; rfl

/-- **`+add-ops` of an `SDBody` list.** -/
theorem addOps' (o : Nat) {ops : List Pole} (h : SDBody ops) : KSB (addOps o ops : CM Map Unit) := by
  constructor
  intro g x g' hb e
  refine ⟨?_, trivial⟩
  unfold addOps at e
  split at e
  · cases e; exact hb
  · obtain ⟨b, hb0, e⟩ := Option.map_eq_some_iff.mp e
    cases e
    exact sds_put hb (sdBody_append h (hb o b hb0))

/-- **`+add-ops` of a list with no split.** -/
theorem addOpsN (o : Nat) {ops : List Pole} (h : NoSplit ops) : KSB (addOps o ops : CM Map Unit) :=
  addOps' o (sdBody_of_noSplit h)

/-- **`+emit` of a block whose body meets `SDBody`.** -/
theorem emit' {b : Blob} (h : SDBody b.body) : KSB (emit b : CM Map Nat) := by
  constructor
  intro g x g' hb e
  rw [emit_apply] at e
  cases e
  refine ⟨?_, trivial⟩
  simp only [SDS, Gen.emitted]
  split
  · exact hb
  · exact sds_put hb h

theorem foldl' {α β : Type} (f : CM Map α → β → CM Map α) (hf : ∀ acc b, KSB acc → KSB (f acc b)) :
    ∀ (l : List β) (acc : CM Map α), KSB acc → KSB (l.foldl f acc)
  | [], _, h => h
  | b :: l, acc, h => foldl' f hf l (f acc b) (hf acc b h)

/-- `get` followed by a step chosen from the state. -/
theorem getThen {α : Type} {P : α → Prop} {f : Comp.Gen Map → CM Map α} (hf : ∀ g, KS P (f g)) :
    KS P (get >>= f) :=
  bind' get' fun g _ => hf g

end KS

/-- The side goal of an `+emit` or `+add-ops` of a literal list. -/
macro "ksblk" : tactic => `(tactic| (apply sdBody_of_noSplit; simp_all [NoSplit, splitReg]))

/-- One step of the tactic `ksb`. -/
macro "ksb_step" : tactic => `(tactic| first
  | exact KS.re' | exact KS.oo' | exact KS.freshId' | exact KS.idM' | exact KS.get'
  | exact KS.getCond' | exact KS.setTag' _ _ | exact KS.copyTag' _ _ | exact KS.proxy' _ _
  | exact KS.fail | exact KS.crash | exact KS.liftO' _ | exact KS.lift' _
  | exact KS.addOps' _ (by ksblk)
  | exact KS.emit' (by ksblk)
  | exact KS.pure' trivial
  | apply KS.bind' | apply KS.ite' | split | intro _)

/-- Prove `KS` of a computation built from the primitives. -/
macro "ksb" : tactic => `(tactic| repeat ksb_step)

/-! ## `+kern-need` -/

/-- **The case `%both` of the loop of `+kern-need`**: the head's and tail's
ops behind a `%hed d` / `%tal d`, the `%cel d`, then the `%mov` into `d`
that closes `d`. -/
theorem kernBoth_sdx {r d : Nat} {kh kt : Nat → List Pole → CM Map (List Pole)}
    (Kh : ∀ X x acc (g g' : Comp.Gen Map) ops, kh x acc g = some (ops, g') → SDx X acc → SDx X ops)
    (Kt : ∀ X x acc (g g' : Comp.Gen Map) ops, kt x acc g = some (ops, g') → SDx X acc → SDx X ops)
    {X : List Nat} {acc ops : List Pole} {g g' : Comp.Gen Map}
    (hk : kernBoth r d kh kt acc g = some (ops, g')) (ha : SDx X acc) : SDx X ops := by
  simp only [kernBoth] at hk
  obtain ⟨rt, g1, h1, hk⟩ := bind_some hk
  obtain ⟨ops1, g2, h2, hk⟩ := bind_some hk
  have s1 := Kt (d :: X) _ _ _ _ _ h2 (sdx_mono (fun x hx => List.mem_cons_of_mem d hx) ha)
  obtain ⟨rh, g3, h3, hk⟩ := bind_some hk
  obtain ⟨ops3, g4, h4, hk⟩ := bind_some hk
  have hsd : ∀ x, ∀ s, splitReg (Pole.tal d x) = some s ∨ splitReg (Pole.hed d x) = some s → s ∈ d :: X := by
    intro x s hs
    rcases hs with hs | hs <;> (simp only [splitReg, Option.some.injEq] at hs; subst hs; exact List.mem_cons_self)
  have s2 := sdx_ite (ops1 ≠ acc) (fun s hs => hsd rt s (Or.inl hs)) s1
  have s3 := Kh (d :: X) _ _ _ _ _ h4 s2
  have s4 := sdx_cons_ns (p0 := Pole.cel d) rfl
    (sdx_ite (ops3 ≠ (if ops1 ≠ acc then Pole.tal d rt :: ops1 else ops1)) (fun s hs => hsd rh s (Or.inr hs)) s3)
  by_cases hrd : r = d
  · simp [hrd] at hk; cases hk
  simp only [hrd, if_false, pure_apply, Option.some.injEq, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  exact sdx_mov rfl rfl s4

/-- **The loop of `+kern-need` keeps `SDx X`** of its accumulator. -/
theorem kernLoop_sdx : ∀ (tgt : Need) (X : List Nat) (r : Nat) (acc : List Pole) (g g' : Comp.Gen Map)
    (ops : List Pole), kernLoop r tgt acc g = some (ops, g') → SDx X acc → SDx X ops := by
  intro tgt
  induction tgt with
  | none =>
    intro X r acc g g' ops h ha
    simp only [kernLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ha
  | this d =>
    intro X r acc g g' ops h ha
    simp only [kernLoop] at h
    by_cases e : r = d
    · rw [if_pos e] at h; cases h
    rw [if_neg e] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact sdx_cons_ns rfl ha
  | pair p q ihp ihq =>
    intro X r acc g g' ops h ha
    simp only [kernLoop] at h
    obtain ⟨rn, g1, h1, h⟩ := bind_some h
    exact kernBoth_sdx (fun X x acc g g' ops hk hx => ihp X x acc g g' ops hk hx)
      (fun X x acc g g' ops hk hx => ihq X x acc g g' ops hk hx) h ha
  | both d h t ihh iht =>
    intro X r acc g g' ops hk ha
    simp only [kernLoop] at hk
    exact kernBoth_sdx (fun X x acc g g' ops hk hx => ihh X x acc g g' ops hk hx)
      (fun X x acc g g' ops hk hx => iht X x acc g g' ops hk hx) hk ha

/-- **`+kern-need`**: its output meets `SDBody`. -/
theorem kernNeed_sd {tgt : Need} {r : Nat} {g g' : Comp.Gen Map} {ops : List Pole}
    (h : kernNeed r tgt g = some (ops, g')) : SDBody ops :=
  sdBody_of_sdx (kernLoop_sdx tgt [] r [] g g' ops h (sdx_nil []))

/-- `+kern-need` as a `KS` step with its result. -/
theorem ks_kernNeed (r : Nat) (tgt : Need) : KS (fun ops => SDBody ops) (kernNeed r tgt : CM Map (List Pole)) := by
  constructor
  intro g x g' hb e
  refine ⟨?_, kernNeed_sd e⟩
  -- `kernNeed` only allocates registers
  have : ∀ (tgt : Need) (r : Nat) (acc : List Pole) (g g' : Comp.Gen Map) (ops : List Pole),
      kernLoop r tgt acc g = some (ops, g') → g'.blocks = g.blocks := by
    intro tgt
    induction tgt with
    | none =>
      intro r acc g g' ops h
      simp only [kernLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]
    | this d =>
      intro r acc g g' ops h
      simp only [kernLoop] at h
      split at h
      · cases h
      · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
    | pair p q ihp ihq =>
      intro r acc g g' ops h
      simp only [kernLoop, kernBoth] at h
      obtain ⟨rn, g1, h1, h⟩ := bind_some h
      rw [re_apply] at h1; simp only [Option.some.injEq, Prod.mk.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨rt, g2, h2, h⟩ := bind_some h
      rw [re_apply] at h2; simp only [Option.some.injEq, Prod.mk.injEq] at h2; obtain ⟨rfl, rfl⟩ := h2
      obtain ⟨o1, g3, h3, h⟩ := bind_some h
      obtain ⟨rh, g4, h4, h⟩ := bind_some h
      rw [re_apply] at h4; simp only [Option.some.injEq, Prod.mk.injEq] at h4; obtain ⟨rfl, rfl⟩ := h4
      obtain ⟨o3, g5, h5, h⟩ := bind_some h
      have e3 := ihq _ _ _ _ _ h3
      have e5 := ihp _ _ _ _ _ h5
      split at h
      · cases h
      · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2, e5]; exact e3
    | both d h t ihh iht =>
      intro r acc g g' ops hk
      simp only [kernLoop, kernBoth] at hk
      obtain ⟨rt, g2, h2, hk⟩ := bind_some hk
      rw [re_apply] at h2; simp only [Option.some.injEq, Prod.mk.injEq] at h2; obtain ⟨rfl, rfl⟩ := h2
      obtain ⟨o1, g3, h3, hk⟩ := bind_some hk
      obtain ⟨rh, g4, h4, hk⟩ := bind_some hk
      rw [re_apply] at h4; simp only [Option.some.injEq, Prod.mk.injEq] at h4; obtain ⟨rfl, rfl⟩ := h4
      obtain ⟨o3, g5, h5, hk⟩ := bind_some hk
      have e3 := iht _ _ _ _ _ h3
      have e5 := ihh _ _ _ _ _ h5
      split at hk
      · cases hk
      · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hk
        rw [← hk.2, e5]; exact e3
  have e1 := this tgt r [] g g' x e
  exact fun o b hb' => hb o b (by rw [← e1]; exact hb')

end Glue
end SkaModel
end Formalization
