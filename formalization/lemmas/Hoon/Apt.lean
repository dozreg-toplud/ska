module

public import lemmas.Hoon.PutBy
public import lemmas.Hoon.Treap
import all lemmas.Pill.Arm.By

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

/-- `?&` of two flags that the Nock computes in order: a crash or `|` of the
first ends it. -/
def andB (x k : Option Bool) : Option Bool := x.bind fun b => if b then k else some false

/-- `?~(l & &((gor p.n.a u.l) !=(p.n.a u.l)))` -/
def aptUpper (mug : Noun → Nat) : Option Noun → Noun → Option Bool
  | none, _ => some true
  | some u, Noun.cell (Noun.cell p _) _ =>
    if gorF mug p u then (if p = u then some false else some true) else some false
  | some _, _ => none

/-- `?~(r & &((gor u.r p.n.a) !=(u.r p.n.a)))` -/
def aptLower (mug : Noun → Nat) : Option Noun → Noun → Option Bool
  | none, _ => some true
  | some u, Noun.cell (Noun.cell p _) _ =>
    if gorF mug u p then (if u = p then some false else some true) else some false
  | some _, _ => none

/-- `?~(c & &((mor p.n.a p.n.c) !=(p.n.a p.n.c) rec))` for a child `c` of a
node whose head is `n`, where `rec p` checks the child with the bound `p`. -/
def aptChild (mug : Noun → Nat) (n c : Noun) (rec : Noun → Option Bool) : Option Bool :=
  match c, n with
  | Noun.atom 0, _ => some true
  | Noun.cell (Noun.cell p' _) _, Noun.cell p _ =>
    if morF mug p p' then (if p = p' then some false else rec p) else some false
  | _, _ => none

/-- `+apt:by` with the bounds `l` (upper) and `r` (lower), as the Nock
computes it: `none` where the Nock crashes. -/
def aptF (mug : Noun → Nat) (l r : Option Noun) : Noun → Option Bool
  | Noun.atom 0 => some true
  | Noun.atom (k + 1) =>
    andB (aptUpper mug l (A (k + 1))) (andB (aptLower mug r (A (k + 1))) none)
  | Noun.cell n rest =>
    andB (aptUpper mug l (C n rest)) <| andB (aptLower mug r (C n rest)) <|
      match rest with
      | Noun.atom _ => none
      | Noun.cell la ra =>
        andB (aptChild mug n la (fun p => aptF mug (some p) r la))
          (aptChild mug n ra (fun p => aptF mug l (some p) ra))

@[nock_exec] theorem pick_map_loob (x : Option Bool) (yes no : Noun) (k : Noun → Option Noun) :
    ((x.map loob).bind fun t => (pick t yes no).bind k) =
      x.bind fun b => if b then k yes else k no := by
  cases x with
  | none => rfl
  | some b => cases b <;> rfl

theorem ite_bind {α β : Type} (c : Prop) [Decidable c] (x y : Option α) (f : α → Option β) :
    (if c then x else y).bind f = if c then x.bind f else y.bind f := by
  split <;> rfl

theorem map_ite_loob (c : Prop) [Decidable c] (x y : Option Bool) :
    Option.map loob (if c then x else y) = if c then x.map loob else y.map loob := by
  split <;> rfl

theorem map_bind_loob {α : Type} (x : Option α) (g : α → Option Bool) :
    Option.map loob (x.bind g) = x.bind fun a => (g a).map loob := by
  cases x <;> rfl

theorem map_loob_eq (x : Option Bool) :
    Option.map loob x = x.bind fun b => if b = true then some (A 0) else some (A 1) := by
  cases x with
  | none => rfl
  | some b => cases b <;> rfl

theorem pick_bind_loob (x : Option Bool) (yes no : Noun) (k : Noun → Option Noun) :
    ((x.bind fun b => if b = true then some (A 0) else some (A 1)).bind fun t =>
        (pick t yes no).bind k) = x.bind fun b => if b = true then k yes else k no := by
  cases x with
  | none => rfl
  | some b => cases b <;> rfl

theorem ite_bool_some (b : Bool) : (if b = true then some true else some false) = some b := by
  cases b <;> rfl

theorem bind_some_bool (x : Option Bool) : (x.bind fun b => some b) = x := by
  cases x <;> rfl

theorem bind_bind {α β γ : Type} (x : Option α) (f : α → Option β) (g : β → Option γ) :
    (x.bind f).bind g = x.bind fun a => (f a).bind g := by
  cases x <;> rfl

theorem apt_loop {mug : Noun → Nat} (ctx B : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx) :
    ∀ (a : Noun) (l r : Option Noun),
      nock (C by.apt.battery (C (C (unitN l) (unitN r)) (C B (C a ctx)))) by.apt.battery
        = (aptF mug l r a).map loob
  | Noun.atom 0, l, r => by
    nock_open by.apt.battery
    simp [nock_exec, aptF]
  | Noun.atom (k + 1), l, r => by
    obtain ⟨⟨hg, _⟩, _⟩ := hc
    rcases l with _ | u <;> rcases r with _ | w <;>
    (nock_open by.apt.battery
     simp [nock_exec, unitN, hg, gor_arm, aptF, aptUpper, aptLower, andB])
  | Noun.cell n (Noun.atom k), l, r => by
    have hgor := gor_gate (mug := mug) ctx hc.1.2
    obtain ⟨⟨hg, _⟩, _⟩ := hc
    rcases n with x | ⟨p, q⟩ <;> rcases l with _ | u <;> rcases r with _ | w <;>
    (nock_open by.apt.battery
     simp [nock_exec, unitN, hg, gor_arm, hgor, nock_ite, ite_bind, map_ite_loob, aptF, aptUpper,
       aptLower, andB])
  | Noun.cell n (Noun.cell la ra), l, r => by
    have hl := apt_loop ctx B hc la
    have hr := apt_loop ctx B hc ra
    have hgor := gor_gate (mug := mug) ctx hc.1.2
    have hmor := mor_gate (mug := mug) ctx hc.2.2
    obtain ⟨⟨hg, _⟩, ⟨hm, _⟩⟩ := hc
    rcases n with x | ⟨p, q⟩
    · rcases l with _ | u <;> rcases r with _ | w <;>
      rcases la with ⟨_ | k⟩ | ⟨⟨x1⟩ | ⟨p1, q1⟩, y1⟩ <;>
      rcases ra with ⟨_ | k2⟩ | ⟨⟨x2⟩ | ⟨p2, q2⟩, y2⟩ <;>
      (nock_open by.apt.battery
       simp [nock_exec, unitN, hg, hm, gor_arm, mor_arm, aptF, aptUpper, aptLower, aptChild,
         andB])
    · have hl'' := hl (some p) r
      have hr'' := hr l (some p)
      rcases l with _ | u <;> rcases r with _ | w <;>
      (simp only [unitN] at hl'' hr''
       rcases la with ⟨_ | k⟩ | ⟨⟨x1⟩ | ⟨p1, q1⟩, y1⟩ <;>
       rcases ra with ⟨_ | k2⟩ | ⟨⟨x2⟩ | ⟨p2, q2⟩, y2⟩ <;>
       (nock_open by.apt.battery
        simp [nock_exec, unitN, hg, hm, gor_arm, mor_arm, hgor, hmor, nock_ite, ite_bind,
          map_loob_eq, ite_bool_some, bind_bind, hl'', hr'', aptF, aptUpper, aptLower, aptChild,
          andB]))

/-! ## What `aptF` accepts -/

/-- Every key of `a` lies below the upper bound `l` and above the lower bound
`r` in `+gor` order, and differs from them. -/
def InBounds (mug : Noun → Nat) (l r : Option Noun) (a : Noun) : Prop :=
  ∀ k v, Get a k v →
    (∀ u, l = some u → gorF mug k u = true ∧ k ≠ u) ∧ (∀ u, r = some u → gorF mug u k = true ∧ u ≠ k)

theorem andB_eq_true {x k : Option Bool} : andB x k = some true ↔ x = some true ∧ k = some true := by
  unfold andB
  cases x with
  | none => simp
  | some b => cases b <;> simp

theorem aptUpper_eq_true {mug : Noun → Nat} {l : Option Noun} {a : Noun}
    (h : aptUpper mug l a = some true) :
    l = none ∨ ∃ u p q rest, l = some u ∧ a = C (C p q) rest ∧ gorF mug p u = true ∧ p ≠ u := by
  unfold aptUpper at h
  split at h
  · exact Or.inl rfl
  · rename_i u p q rest
    refine Or.inr ⟨u, p, q, rest, rfl, rfl, ?_⟩
    by_cases g : gorF mug p u = true
    · by_cases e : p = u
      · simp [e] at h
      · exact ⟨g, e⟩
    · simp [g] at h
  · cases h

theorem aptLower_eq_true {mug : Noun → Nat} {r : Option Noun} {a : Noun}
    (h : aptLower mug r a = some true) :
    r = none ∨ ∃ u p q rest, r = some u ∧ a = C (C p q) rest ∧ gorF mug u p = true ∧ u ≠ p := by
  unfold aptLower at h
  split at h
  · exact Or.inl rfl
  · rename_i u p q rest
    refine Or.inr ⟨u, p, q, rest, rfl, rfl, ?_⟩
    by_cases g : gorF mug u p = true
    · by_cases e : u = p
      · simp [e] at h
      · exact ⟨g, e⟩
    · simp [g] at h
  · cases h

theorem aptChild_eq_true {mug : Noun → Nat} {n c : Noun} {rec : Noun → Option Bool}
    (h : aptChild mug n c rec = some true) :
    c = A 0 ∨ ∃ p q p' q' y, c = C (C p' q') y ∧ n = C p q ∧ morF mug p p' = true ∧ p ≠ p' ∧
      rec p = some true := by
  unfold aptChild at h
  split at h
  · exact Or.inl rfl
  · rename_i p' q' y p q
    refine Or.inr ⟨p, q, p', q', y, rfl, rfl, ?_⟩
    by_cases m : morF mug p p' = true
    · by_cases e : p = p'
      · simp [e] at h
      · simp only [m, e, if_true, if_false] at h
        exact ⟨m, e, h⟩
    · simp [m] at h
  · cases h

/-- On a map whose keys lie within the bounds, `aptF` says yes. -/
theorem aptF_of_isMap {mug : Noun → Nat} {a : Noun} (h : IsMap mug a) :
    ∀ l r, InBounds mug l r a → aptF mug l r a = some true := by
  induction h with
  | nil => intro l r _; rfl
  | @node p q la ra hl hr hL hR ihl ihr =>
    intro l r hb
    have hroot := hb p q Get.here
    have up : aptUpper mug l (C (C p q) (C la ra)) = some true := by
      rcases l with _ | u
      · rfl
      · obtain ⟨g, e⟩ := hroot.1 u rfl
        simp [aptUpper, g, e]
    have lo : aptLower mug r (C (C p q) (C la ra)) = some true := by
      rcases r with _ | w
      · rfl
      · obtain ⟨g, e⟩ := hroot.2 w rfl
        simp [aptLower, g, e]
    have cl : aptChild mug (C p q) la (fun x => aptF mug (some x) r la) = some true := by
      cases hl with
      | nil => rfl
      | @node p' q' dl dr _ _ _ _ =>
        have ⟨ne, _, m⟩ := hL p' q' Get.here
        have hrec : aptF mug (some p) r (C (C p' q') (C dl dr)) = some true := by
          apply ihl
          intro k v hk
          have ⟨ne, g, _⟩ := hL k v hk
          refine ⟨fun u hu => ?_, fun u hu => (hb k v (Get.left hk)).2 u hu⟩
          cases hu
          exact ⟨g, ne⟩
        simp [aptChild, m, Ne.symm ne, hrec]
    have cr : aptChild mug (C p q) ra (fun x => aptF mug l (some x) ra) = some true := by
      cases hr with
      | nil => rfl
      | @node p' q' dl dr _ _ _ _ =>
        have ⟨ne, _, m⟩ := hR p' q' Get.here
        have hrec : aptF mug l (some p) (C (C p' q') (C dl dr)) = some true := by
          apply ihr
          intro k v hk
          have ⟨ne, g, _⟩ := hR k v hk
          refine ⟨fun u hu => (hb k v (Get.right hk)).1 u hu, fun u hu => ?_⟩
          cases hu
          exact ⟨g, Ne.symm ne⟩
        simp [aptChild, m, Ne.symm ne, hrec]
    simp only [aptF, andB_eq_true]
    exact ⟨up, lo, cl, cr⟩

theorem inBounds_none (mug : Noun → Nat) (a : Noun) : InBounds mug none none a :=
  fun _ _ _ => ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩

/-- When `aptF` says yes, the noun is a map within the bounds, except for a
lone node `[x ~ ~]` whose head `x` is an atom, with no bounds. -/
theorem isMap_of_aptF {mug : Noun → Nat} : ∀ (a : Noun) (l r : Option Noun),
    aptF mug l r a = some true →
      (IsMap mug a ∧ InBounds mug l r a) ∨
      (l = none ∧ r = none ∧ ∃ x, a = C (A x) (C (A 0) (A 0)))
  | Noun.atom 0, l, r, _ => Or.inl ⟨IsMap.nil, fun _ _ hk => absurd hk Get_atom⟩
  | Noun.atom (k + 1), l, r, h => by
    simp only [aptF, andB_eq_true] at h
    exact absurd h.2.2 (by simp)
  | Noun.cell n (Noun.atom k), l, r, h => by
    simp only [aptF, andB_eq_true] at h
    exact absurd h.2.2 (by simp)
  | Noun.cell n (Noun.cell la ra), l, r, h => by
    simp only [aptF, andB_eq_true] at h
    obtain ⟨hu, hlo, hcl, hcr⟩ := h
    rcases n with x | ⟨p, q⟩
    · -- the head is an atom: no bound and no child can read it
      rcases aptChild_eq_true hcl with rfl | ⟨_, _, _, _, _, _, hn, _⟩
      · rcases aptChild_eq_true hcr with rfl | ⟨_, _, _, _, _, _, hn, _⟩
        · rcases aptUpper_eq_true hu with rfl | ⟨_, _, _, _, _, ha, _⟩
          · rcases aptLower_eq_true hlo with rfl | ⟨_, _, _, _, _, ha, _⟩
            · exact Or.inr ⟨rfl, rfl, x, rfl⟩
            · cases ha
          · cases ha
        · cases hn
      · cases hn
    · -- the left child
      have hL : IsMap mug la ∧ InBounds mug (some p) r la ∧ ∀ k v, Get la k v → morF mug p k = true := by
        rcases aptChild_eq_true hcl with rfl | ⟨p0, q0, p', q', y, rfl, hn, m, ne, hrec⟩
        · exact ⟨IsMap.nil, fun _ _ hk => absurd hk Get_atom, fun _ _ hk => absurd hk Get_atom⟩
        · cases hn
          rcases isMap_of_aptF _ _ _ hrec with ⟨hm, hb⟩ | ⟨h1, _⟩
          · refine ⟨hm, hb, ?_⟩
            cases hm with
            | node a1 a2 a3 a4 => exact morF_of_root (IsMap.node a1 a2 a3 a4) m
          · cases h1
      have hR : IsMap mug ra ∧ InBounds mug l (some p) ra ∧ ∀ k v, Get ra k v → morF mug p k = true := by
        rcases aptChild_eq_true hcr with rfl | ⟨p0, q0, p', q', y, rfl, hn, m, ne, hrec⟩
        · exact ⟨IsMap.nil, fun _ _ hk => absurd hk Get_atom, fun _ _ hk => absurd hk Get_atom⟩
        · cases hn
          rcases isMap_of_aptF _ _ _ hrec with ⟨hm, hb⟩ | ⟨_, h2, _⟩
          · refine ⟨hm, hb, ?_⟩
            cases hm with
            | node a1 a2 a3 a4 => exact morF_of_root (IsMap.node a1 a2 a3 a4) m
          · cases h2
      obtain ⟨hml, hbl, hmorl⟩ := hL
      obtain ⟨hmr, hbr, hmorr⟩ := hR
      -- the bounds of the root
      have hup : ∀ u, l = some u → gorF mug p u = true ∧ p ≠ u := by
        intro u hu'
        rcases aptUpper_eq_true hu with h0 | ⟨u', p', q', rest, h1, h2, g, e⟩
        · rw [hu'] at h0; cases h0
        · rw [hu'] at h1; cases h1
          simp only [Noun.cell.injEq] at h2
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
          exact ⟨g, e⟩
      have hlow : ∀ u, r = some u → gorF mug u p = true ∧ u ≠ p := by
        intro u hu'
        rcases aptLower_eq_true hlo with h0 | ⟨u', p', q', rest, h1, h2, g, e⟩
        · rw [hu'] at h0; cases h0
        · rw [hu'] at h1; cases h1
          simp only [Noun.cell.injEq] at h2
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
          exact ⟨g, e⟩
      refine Or.inl ⟨IsMap.node hml hmr ?_ ?_, ?_⟩
      · intro k v hk
        obtain ⟨g, ne⟩ := (hbl k v hk).1 p rfl
        exact ⟨ne, g, hmorl k v hk⟩
      · intro k v hk
        obtain ⟨g, ne⟩ := (hbr k v hk).2 p rfl
        exact ⟨Ne.symm ne, g, hmorr k v hk⟩
      · intro k v hk
        rw [Get_node] at hk
        rcases hk with ⟨rfl, rfl⟩ | hk | hk
        · exact ⟨hup, hlow⟩
        · obtain ⟨g, ne⟩ := (hbl k v hk).1 p rfl
          refine ⟨fun u hu' => ?_, (hbl k v hk).2⟩
          obtain ⟨g', ne'⟩ := hup u hu'
          refine ⟨gorF_trans mug g g', fun e => ?_⟩
          subst e
          exact ne' (gorF_antisymm mug g' g)
        · obtain ⟨g, ne⟩ := (hbr k v hk).2 p rfl
          refine ⟨(hbr k v hk).1, fun u hu' => ?_⟩
          obtain ⟨g', ne'⟩ := hlow u hu'
          refine ⟨gorF_trans mug g' g, fun e => ?_⟩
          subst e
          exact ne' (gorF_antisymm mug g' g)

/-- A lone node `[x ~ ~]` with an atom `x` passes `aptF`, though it is not a map. -/
theorem aptF_lone_atom (mug : Noun → Nat) (x : Nat) :
    aptF mug none none (C (A x) (C (A 0) (A 0))) = some true := rfl

theorem not_isMap_lone_atom (mug : Noun → Nat) (x : Nat) :
    ¬ IsMap mug (C (A x) (C (A 0) (A 0))) := by
  intro h
  cases h

/-! ## The arm -/

theorem apt_arm (d : Noun) :
    nock d by.apt.arm = nock (C by.apt.battery (C (C (A 0) (A 0)) d)) by.apt.battery := by
  nock_open by.apt.arm
  simp only [nock_exec]

/-- `~(apt by a)`, the pill's check of the invariant of a map, says yes on a
noun `a` exactly when `a` satisfies `IsMap`, or `a` is `[x ~ ~]` with an atom
`x`; on other nouns it says no or crashes. -/
theorem apt_by {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx) (a : Noun) :
    (nock (C by.battery (C a ctx)) by.apt.arm = some (loob true) ↔
      IsMap mug a ∨ ∃ x, a = C (A x) (C (A 0) (A 0))) := by
  have h := apt_loop ctx by.battery hc a none none
  simp only [unitN] at h
  rw [apt_arm, h]
  constructor
  · intro he
    have : aptF mug none none a = some true := by
      cases hx : aptF mug none none a with
      | none => rw [hx] at he; cases he
      | some b => rw [hx] at he; cases b <;> simp_all [loob]
    rcases isMap_of_aptF a none none this with ⟨hm, _⟩ | ⟨_, _, x, hx⟩
    · exact Or.inl hm
    · exact Or.inr ⟨x, hx⟩
  · rintro (hm | ⟨x, rfl⟩)
    · rw [aptF_of_isMap hm none none (inBounds_none mug a)]
      rfl
    · rw [aptF_lone_atom]
      rfl

end Hoon
end Formalization

end
