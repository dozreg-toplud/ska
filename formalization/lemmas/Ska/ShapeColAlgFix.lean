import lemmas.Ska.ShapeColAlgN

/-!
# The loop of `+inter2-collapse` stops (the fuel of `fixLoop`, part 2)

The chain argument for `fixLoop` (the fixed point of `+inter2-collapse`):

* a shape the loop keeps is normal and of depth at most `D` (`OkD D`); a round
  keeps every sure of the tree `OkD D` when the parent is (`fixRound_ok`: the
  parent's shape `uniOrd parent s`, the `msgOrd` of the kids' sures and their
  `uniOrd` fold are all normal and no deeper, `Ska/ShapeColAlgN.lean`);
* a round is inflationary at every node for the order `oLe` whose join is
  `uniN` (= `uniOrd` on normal shapes): the new sure is a fold of `uniN` from
  `uniN parent s` (`fixRound_ok`, `I2.Le`), and it keeps the size;
* the weight of a tree (the sum of `ordW` over its nodes) never drops along
  `I2.Le` and rises when the tree changes (`weight_le`), and it is at most
  `size × wB D` (`weight_bound`);
* so **`fixRet_bound`**: on a tree whose sures are all normal, `fixLoop`
  returns within `fixFuel t = size × wB (depth) + 1` rounds;
* the trees of the final pass are normal when the needs of the lazy need are
  (`l2i_normal`, `sureOfS_normal` with `sureLook_normal`, `i12_normal`).
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Compiler

/-- A shape the loop keeps: normal, depth at most `D`. -/
def OkD (D : Nat) (s : NeedOrd) : Prop := ordNormal s = true ∧ ordDepth s ≤ D

theorem okD_none (D : Nat) : OkD D NeedOrd.none := ⟨rfl, Nat.zero_le _⟩

/-! ## Trees -/

mutual
/-- Every sure of a tree meets `P`. -/
def I2.All (P : NeedOrd → Prop) : I2 → Prop
  | I2.mk s f => P s ∧ I2.AllF P f
def I2.AllF (P : NeedOrd → Prop) : List (I2 × I2) → Prop
  | [] => True
  | (y, n) :: r => I2.All P y ∧ I2.All P n ∧ I2.AllF P r
end

mutual
/-- The number of nodes. -/
def I2.size : I2 → Nat
  | I2.mk _ f => 1 + I2.sizeF f
def I2.sizeF : List (I2 × I2) → Nat
  | [] => 0
  | (y, n) :: r => I2.size y + I2.size n + I2.sizeF r
end

mutual
/-- The sum of the weights of the sures. -/
def I2.weight : I2 → Nat
  | I2.mk s f => ordW s + I2.weightF f
def I2.weightF : List (I2 × I2) → Nat
  | [] => 0
  | (y, n) :: r => I2.weight y + I2.weight n + I2.weightF r
end

mutual
/-- The greatest depth of a sure. -/
def I2.depth : I2 → Nat
  | I2.mk s f => max (ordDepth s) (I2.depthF f)
def I2.depthF : List (I2 × I2) → Nat
  | [] => 0
  | (y, n) :: r => max (max (I2.depth y) (I2.depth n)) (I2.depthF r)
end

mutual
/-- `oLe` at every node, one skeleton. -/
def I2.Le : I2 → I2 → Prop
  | I2.mk s f, I2.mk s' f' => oLe s s' ∧ I2.LeF f f'
def I2.LeF : List (I2 × I2) → List (I2 × I2) → Prop
  | [], [] => True
  | (y, n) :: r, (y', n') :: r' => I2.Le y y' ∧ I2.Le n n' ∧ I2.LeF r r'
  | _, _ => False
end

theorem I2.all_sure {P : NeedOrd → Prop} : ∀ {t : I2}, I2.All P t → P t.sure
  | I2.mk _ _, h => by rw [I2.All] at h; exact h.1

mutual
theorem I2.all_okD : ∀ (t : I2) (D : Nat), I2.All (fun s => ordNormal s = true) t → I2.depth t ≤ D →
    I2.All (OkD D) t
  | I2.mk s f, D, h, hd => by
    rw [I2.All] at h ⊢; rw [I2.depth] at hd
    exact ⟨⟨h.1, by omega⟩, I2.allF_okD f D h.2 (by omega)⟩
theorem I2.allF_okD : ∀ (f : List (I2 × I2)) (D : Nat), I2.AllF (fun s => ordNormal s = true) f →
    I2.depthF f ≤ D → I2.AllF (OkD D) f
  | [], _, _, _ => by rw [I2.AllF]; trivial
  | (y, n) :: r, D, h, hd => by
    rw [I2.AllF] at h ⊢; rw [I2.depthF] at hd
    exact ⟨I2.all_okD y D h.1 (by omega), I2.all_okD n D h.2.1 (by omega), I2.allF_okD r D h.2.2 (by omega)⟩
end

/-! ## A round -/

theorem okD_uniOrd {D : Nat} {a b : NeedOrd} (ha : OkD D a) (hb : OkD D b) : OkD D (uniOrd a b) := by
  have := ordDepth_uniOrd ha.1 hb.1
  have := ha.2; have := hb.2
  exact ⟨ordNormal_uniOrd ha.1 hb.1, by omega⟩

theorem okD_msgOrd {D : Nat} {a b : NeedOrd} (c : Cape) (ha : OkD D a) (hb : OkD D b) : OkD D (msgOrd a b c) := by
  have := ordDepth_msgOrd c ha.1 hb.1
  have := ha.2; have := hb.2
  exact ⟨ordNormal_msgOrd c ha.1 hb.1, by omega⟩

/-- The `+roll` of a round keeps `OkD D` and is above its start. -/
theorem rollMsg_ok (less : Cape) (D : Nat) : ∀ (kids : List (I2 × I2)) (acc : NeedOrd), OkD D acc →
    I2.AllF (OkD D) kids → OkD D (rollMsg less kids acc) ∧ oLe acc (rollMsg less kids acc)
  | [], acc, ha, _ => ⟨ha, oLe_refl acc⟩
  | (y, n) :: r, acc, ha, hk => by
    rw [I2.AllF] at hk
    have hm := okD_msgOrd less (I2.all_sure hk.1) (I2.all_sure hk.2.1)
    have h1 := okD_uniOrd ha hm
    have ih := rollMsg_ok less D r _ h1 hk.2.2
    have hl : oLe acc (uniOrd acc (msgOrd y.sure n.sure less)) := by
      rw [uniOrd_eq_uniN ha.1 hm.1]; exact oLe_uniN_left _ _
    unfold rollMsg at ih ⊢
    rw [List.foldl_cons]
    exact ⟨ih.1, oLe_trans hl ih.2⟩

mutual
/-- **A round keeps every sure `OkD D`, is inflationary at every node, and
keeps the size.** -/
theorem fixRound_ok (less : Cape) (D : Nat) : ∀ (t : I2) (p : NeedOrd), OkD D p → I2.All (OkD D) t →
    I2.All (OkD D) (fixRound less t p) ∧ I2.Le t (fixRound less t p) ∧ I2.size (fixRound less t p) = I2.size t
  | I2.mk s fk, p, hp, ht => by
    rw [I2.All] at ht
    have hq := okD_uniOrd hp ht.1
    have hsq : oLe s (uniOrd p s) := by rw [uniOrd_eq_uniN hp.1 ht.1.1]; exact oLe_uniN_right _ _
    obtain ⟨k1, k2, k3⟩ := fixKids_ok less D fk (uniOrd p s) hq ht.2
    have hr := rollMsg_ok less D (fixKids less fk (uniOrd p s)) (uniOrd p s) hq k1
    rw [fixRound, I2.All, I2.Le, I2.size, I2.size, k3]
    exact ⟨⟨hr.1, k1⟩, ⟨oLe_trans hsq hr.2, k2⟩, rfl⟩
theorem fixKids_ok (less : Cape) (D : Nat) : ∀ (f : List (I2 × I2)) (p : NeedOrd), OkD D p → I2.AllF (OkD D) f →
    I2.AllF (OkD D) (fixKids less f p) ∧ I2.LeF f (fixKids less f p) ∧ I2.sizeF (fixKids less f p) = I2.sizeF f
  | [], _, _, _ => by rw [fixKids, I2.AllF, I2.LeF, I2.sizeF]; exact ⟨trivial, trivial, rfl⟩
  | (y, n) :: r, p, hp, hf => by
    rw [I2.AllF] at hf
    obtain ⟨a1, a2, a3⟩ := fixRound_ok less D y p hp hf.1
    obtain ⟨b1, b2, b3⟩ := fixRound_ok less D n p hp hf.2.1
    obtain ⟨c1, c2, c3⟩ := fixKids_ok less D r p hp hf.2.2
    rw [fixKids, I2.AllF, I2.LeF, I2.sizeF, I2.sizeF, a3, b3, c3]
    exact ⟨⟨a1, b1, c1⟩, ⟨a2, b2, c2⟩, rfl⟩
end

/-! ## The weight -/

mutual
/-- **The weight never drops along `I2.Le`, and stays only when the tree
does.** -/
theorem weight_le : ∀ (t t' : I2), I2.Le t t' → I2.weight t ≤ I2.weight t' ∧ (I2.weight t' ≤ I2.weight t → t = t')
  | I2.mk s f, I2.mk s' f', h => by
    rw [I2.Le] at h
    have h1 := ordW_oLe h.1
    have h2 := weightF_le f f' h.2
    rw [I2.weight, I2.weight]
    refine ⟨by omega, fun hw => ?_⟩
    have e1 : s = s' := by
      by_cases e : s = s'
      · exact e
      · have := h1.2 e; omega
    rw [e1, h2.2 (by omega)]
theorem weightF_le : ∀ (f f' : List (I2 × I2)), I2.LeF f f' →
    I2.weightF f ≤ I2.weightF f' ∧ (I2.weightF f' ≤ I2.weightF f → f = f')
  | [], [], _ => by rw [I2.weightF]; exact ⟨Nat.le_refl _, fun _ => rfl⟩
  | [], _ :: _, h => by simp [I2.LeF] at h
  | _ :: _, [], h => by simp [I2.LeF] at h
  | (y, n) :: r, (y', n') :: r', h => by
    rw [I2.LeF] at h
    have a := weight_le y y' h.1
    have b := weight_le n n' h.2.1
    have c := weightF_le r r' h.2.2
    rw [I2.weightF, I2.weightF]
    refine ⟨by omega, fun hw => ?_⟩
    rw [a.2 (by omega), b.2 (by omega), c.2 (by omega)]
end

mutual
/-- **The weight of a tree of `OkD D` sures is at most `size × wB D`.** -/
theorem weight_bound (D : Nat) : ∀ t : I2, I2.All (OkD D) t → I2.weight t ≤ I2.size t * wB D
  | I2.mk s f, h => by
    rw [I2.All] at h
    have hs : ordW s ≤ wB D := Nat.le_trans (ordW_le_wB s) (wB_mono h.1.2)
    have hf := weightF_bound D f h.2
    rw [I2.weight, I2.size, Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add hs hf
theorem weightF_bound (D : Nat) : ∀ f : List (I2 × I2), I2.AllF (OkD D) f → I2.weightF f ≤ I2.sizeF f * wB D
  | [], _ => by rw [I2.weightF, I2.sizeF]; exact Nat.zero_le _
  | (y, n) :: r, h => by
    rw [I2.AllF] at h
    rw [I2.weightF, I2.sizeF, Nat.add_mul, Nat.add_mul]
    exact Nat.add_le_add (Nat.add_le_add (weight_bound D y h.1) (weight_bound D n h.2.1)) (weightF_bound D r h.2.2)
end

/-! ## The loop -/

/-- **`fixLoop` returns** on a tree of `OkD D` sures once the fuel is past
the room left under the weight bound. -/
theorem fixLoop_some_of (less : Cape) (D : Nat) : ∀ (fuel : Nat) (t : I2), I2.All (OkD D) t →
    I2.size t * wB D < I2.weight t + fuel → (fixLoop less fuel t).isSome
  | 0, t, h, hb => by
    have := weight_bound D t h
    omega
  | k + 1, t, h, hb => by
    rw [fixLoop]
    split
    · rfl
    · rename_i hne
      obtain ⟨h1, h2, h3⟩ := fixRound_ok less D t NeedOrd.none (okD_none D) h
      have hw := weight_le _ _ h2
      have hlt : I2.weight t < I2.weight (fixRound less t NeedOrd.none) := by
        by_cases e : I2.weight (fixRound less t NeedOrd.none) ≤ I2.weight t
        · exact absurd (by rw [← hw.2 e]) hne
        · omega
      apply fixLoop_some_of less D k _ h1
      rw [h3]
      omega

/-- The fuel: the size of the tree times the most weight of a shape at its
depth, plus one. -/
def fixFuel (t : I2) : Nat := I2.size t * wB (I2.depth t) + 1

/-- **The fuel bound of `+inter2-collapse`**: on a tree whose sures are all
normal, the model's loop returns within `fixFuel t` rounds. -/
theorem fixRet_bound (less : Cape) (t : I2) (h : I2.All (fun s => ordNormal s = true) t) :
    (fixLoop less (fixFuel t) t).isSome :=
  fixLoop_some_of less (I2.depth t) (fixFuel t) t (I2.all_okD t _ h (Nat.le_refl _)) (by unfold fixFuel; omega)

/-! ## The trees of the final pass are normal when its needs are -/

theorem ordNormal_halves1 {a : NeedOrd} (h : ordNormal a = true) : ordNormal (ordHalves a).1 = true := by
  cases a with
  | pair p q => exact ((ordNormal_pair p q).1 h).2.1
  | both x y => exact ((ordNormal_both x y).1 h).1
  | _ => rfl

theorem ordNormal_halves2 {a : NeedOrd} (h : ordNormal a = true) : ordNormal (ordHalves a).2 = true := by
  cases a with
  | pair p q => exact ((ordNormal_pair p q).1 h).2.2
  | both x y => exact ((ordNormal_both x y).1 h).2
  | _ => rfl

theorem ordNormal_ordRebuild (new : NeedOrd) {x : NeedOrd} (h : ordNormal x = true) :
    ordNormal (ordRebuild new x) = true := by
  cases new with
  | none => exact h
  | pair _ _ => exact h
  | _ =>
    cases x with
    | pair a b => exact (ordNormal_both a b).2 ((ordNormal_pair a b).1 h).2
    | _ => rfl

/-- **The trap of `+inter1-to-inter2` keeps a shape normal.** -/
theorem sureLook_normal (axe : Nat) : ∀ new : NeedOrd, ordNormal new = true → ordNormal (sureLook axe new) = true := by
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
    intro new hn
    rw [sureLook]
    split
    · split
      · rfl
      · exact hn
    · rename_i h1
      have hm := ih (mas axe) (mas_lt axe (by omega))
      apply ordNormal_ordRebuild
      split
      · exact ordNormal_consOrd (hm _ (ordNormal_halves1 hn)) (ordNormal_halves2 hn)
      · exact ordNormal_consOrd (ordNormal_halves1 hn) (hm _ (ordNormal_halves2 hn))

variable {S : Type} [HoonSet S]

theorem foldlM_sure_normal (less : Cape) : ∀ (l : List Nat) (ned s : NeedOrd),
    l.foldlM (fun new axe => sureStepS less new axe) ned = some s → ordNormal ned = true → ordNormal s = true
  | [], ned, s, h, hn => by
    simp only [List.foldlM_nil, pure, Option.some.injEq] at h
    rw [← h]; exact hn
  | a :: l, ned, s, h, hn => by
    rw [List.foldlM_cons] at h
    cases e : sureStepS less ned a with
    | none => rw [e] at h; cases h
    | some m =>
      rw [e] at h
      apply foldlM_sure_normal less l m s h
      unfold sureStepS at e
      split at e
      · cases e; exact hn
      · cases e2 : axeInLessCape a less with
        | none => rw [e2] at e; cases e
        | some b =>
          rw [e2] at e
          simp only [Option.map_some, Option.some.injEq] at e
          rw [← e]
          split
          · exact hn
          · exact sureLook_normal a ned hn

/-- **`+sure-of` keeps a shape normal.** -/
theorem sureOfS_normal (ned : NeedOrd) (lok : S) (less : Cape) (s : NeedOrd) (h : sureOfS ned lok less = some s)
    (hn : ordNormal ned = true) : ordNormal s = true :=
  foldlM_sure_normal less _ ned s h hn

mutual
/-- Every sure need of a `need-inter1` is normal. -/
def I1.AllN : I1 S → Prop
  | I1.mk n _ f => ordNormal n = true ∧ I1.AllNF f
def I1.AllNF : List (I1 S × I1 S) → Prop
  | [] => True
  | (y, n) :: r => I1.AllN y ∧ I1.AllN n ∧ I1.AllNF r
end

theorem I1.allNF_append : ∀ (a b : List (I1 S × I1 S)), I1.AllNF a → I1.AllNF b → I1.AllNF (a ++ b)
  | [], _, _, hb => hb
  | (y, n) :: r, b, ha, hb => by
    rw [List.cons_append, I1.AllNF]; rw [I1.AllNF] at ha
    exact ⟨ha.1, ha.2.1, I1.allNF_append r b ha.2.2 hb⟩

mutual
/-- **`+inter1-to-inter2` of a normal `need-inter1` is normal.** -/
theorem i12_normal (less : Cape) : ∀ (t : I1 S) (t' : I2), i12 less t = some t' → I1.AllN t →
    I2.All (fun s => ordNormal s = true) t'
  | I1.mk ned lok fk, t', h, hn => by
    rw [I1.AllN] at hn
    rw [i12] at h
    cases e1 : sureOfS ned lok less with
    | none => rw [e1] at h; cases h
    | some s =>
      cases e2 : i12Forks less fk with
      | none => rw [e1, e2] at h; cases h
      | some f =>
        rw [e1, e2] at h
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
        rw [← h, I2.All]
        exact ⟨sureOfS_normal ned lok less s e1 hn.1, i12Forks_normal less fk f e2 hn.2⟩
theorem i12Forks_normal (less : Cape) : ∀ (fk : List (I1 S × I1 S)) (f : List (I2 × I2)),
    i12Forks less fk = some f → I1.AllNF fk → I2.AllF (fun s => ordNormal s = true) f
  | [], f, h, _ => by
    rw [i12Forks] at h; cases h; rw [I2.AllF]; trivial
  | (y, n) :: r, f, h, hn => by
    rw [I1.AllNF] at hn
    rw [i12Forks] at h
    cases ey : i12 less y with
    | none => rw [ey] at h; cases h
    | some y' =>
      cases en : i12 less n with
      | none => rw [ey, en] at h; cases h
      | some n' =>
        cases er : i12Forks less r with
        | none => rw [ey, en, er] at h; cases h
        | some r' =>
          rw [ey, en, er] at h
          simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
          rw [← h, I2.AllF]
          exact ⟨i12_normal less y y' ey hn.1, i12_normal less n n' en hn.2.1, i12Forks_normal less r r' er hn.2.2⟩
end

end Comp
end SkaModel
end Formalization
