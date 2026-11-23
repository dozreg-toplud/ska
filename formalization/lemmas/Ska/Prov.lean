import lemmas.Ska.CallGraph

/-!
# Provenance: the invariant of products, and `+patch-prod`

`ProvR y S σ p` is the invariant that the product `p` of a function on the
subject `y` must satisfy for its product sock `S` and provenance `σ` (a
`+$spring`), read along paths:

* `exact`: a part whose provenance is an axis `a` is the part of `y` at `a`
  (both may be absent);
* `const`: a part without provenance fits the sock there, and where it is
  absent the sock there knows nothing;
* `nonvoid`: a product sock that is `%void` has no product.

`patchProd_sound`: under the invariant, the product fits what `+patch-prod`
makes of the product sock for any subject sock `new` that `y` fits.  So a
memo or `%rec` hit answers right on products (`hit_prod`), once the entry's
product satisfies the invariant on the subjects of the hit's subject sock.
That last part is the relative soundness of `fol-loop` (`WantSound` and its
product half), which is not proved.
-/

namespace Formalization
namespace SkaModel

open Nock

/-- The provenance of the part at a path: `+hed:pi` and `+tel:pi` along it. -/
def springAt : Noun → List Bool → Noun
  | s, [] => s
  | s, false :: π => springAt (Pi.hed s) π
  | s, true :: π => springAt (Pi.tel s) π

/-- The sock of the part at a path: `+hed:so` and `+tel:so` along it. -/
def sockAt : Sock → List Bool → Sock
  | s, [] => s
  | s, false :: π => sockAt (So.hed s) π
  | s, true :: π => sockAt (So.tel s) π

/-- A part, maybe absent, fits a sock: an absent part fits only a sock that
knows nothing. -/
def FitsOpt (s : Sock) : Option Noun → Prop
  | some q => Fits s q
  | none => s.Blank

/-- **The provenance invariant** of a product `p` of a function on the subject
`y`, for the product sock `S` and the provenance `σ`. -/
structure ProvR (y : Noun) (S : Sock) (σ p : Noun) : Prop where
  nonvoid : S ≠ Sock.void
  exact : ∀ π a, springAt σ π = A a → a ≠ 0 → slotAtPath p π = slot? a y
  const : ∀ π, springAt σ π = A 0 → FitsOpt (sockAt S π) (slotAtPath p π)

theorem hed_ne_void {s : Sock} (h : s ≠ Sock.void) : So.hed s ≠ Sock.void := by
  cases s with
  | void => exact absurd rfl h
  | mk c d => cases c <;> cases d <;> simp [So.hed, Sock.dunno]

theorem tel_ne_void {s : Sock} (h : s ≠ Sock.void) : So.tel s ≠ Sock.void := by
  cases s with
  | void => exact absurd rfl h
  | mk c d => cases c <;> cases d <;> simp [So.tel, Sock.dunno]

/-! ## Pulling at an axis that is absent -/

/-- A cape that knows nothing pulls to a sock that knows nothing. -/
theorem pullLoop_isNo_blank : ∀ (axe : Nat) (c : Cape) (d : Noun), c.isNo = true →
    (So.pullLoop c d axe).Blank := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
  intro c d hc
  rw [So.pullLoop.eq_def]
  split
  · exact ⟨c, d, rfl, hc⟩
  · rename_i hax
    have hlt := mas_lt axe (by omega)
    by_cases hcn : c = Cape.no
    · simp only [hcn, if_true]; exact dunno_blank
    · simp only [hcn, if_false]
      cases d with
      | atom _ => exact dunno_blank
      | cell dh dt =>
        cases c with
        | yes => simp [Cape.isNo] at hc
        | no => exact absurd rfl hcn
        | cell ch ct =>
          simp only [Cape.isNo, Bool.and_eq_true] at hc
          simp only
          split
          · exact ih _ hlt ch dh hc.1
          · exact ih _ hlt ct dt hc.2

/-- A sock pulled at an axis that a noun of it does not have knows nothing. -/
theorem pullLoop_blank_of_none : ∀ (axe : Nat) (c : Cape) (d y : Noun), 1 ≤ axe →
    FitsCape c d y → slot? axe y = none → (So.pullLoop c d axe).Blank := by
  intro axe
  induction axe using Nat.strongRecOn with
  | _ axe ih =>
  intro c d y h1 hf hs
  rw [So.pullLoop.eq_def]
  split
  · have : axe = 1 := by omega
    subst this
    simp at hs
  · rename_i hax
    have h2 : 2 ≤ axe := by omega
    have hlt := mas_lt axe h2
    have hpos := mas_pos axe h2
    by_cases hcn : c = Cape.no
    · simp only [hcn, if_true]; exact dunno_blank
    · simp only [hcn, if_false]
      cases d with
      | atom _ => exact dunno_blank
      | cell dh dt =>
        rw [slot?_cap h2] at hs
        cases c with
        | no => exact absurd rfl hcn
        | yes =>
          simp only [FitsCape] at hf
          subst hf
          simp only at hs ⊢
          by_cases hc : cap axe = 2
          · simp only [hc, if_true] at hs ⊢; exact ih _ hlt Cape.yes dh dh hpos rfl hs
          · simp only [hc, if_false] at hs ⊢; exact ih _ hlt Cape.yes dt dt hpos rfl hs
        | cell ch ct =>
          simp only [FitsCape] at hf
          simp only
          rcases hf with hno | ⟨dh', dt', nh, nt, hd, hn, hh, ht⟩
          · simp only [Bool.and_eq_true] at hno
            split
            · exact pullLoop_isNo_blank _ _ _ hno.1
            · exact pullLoop_isNo_blank _ _ _ hno.2
          · cases hd; subst hn
            simp only at hs
            by_cases hc : cap axe = 2
            · simp only [hc, if_true] at hs ⊢; exact ih _ hlt _ _ _ hpos hh hs
            · simp only [hc, if_false] at hs ⊢; exact ih _ hlt _ _ _ hpos ht hs

theorem pull_blank_of_none {s s' : Sock} {a : Nat} {y : Noun} (hf : Fits s y) (ha : a ≠ 0)
    (hs : slot? a y = none) (hp : So.pull s a = some s') : s'.Blank := by
  unfold So.pull at hp
  rw [if_neg ha] at hp
  cases s with
  | void => exact absurd hf id
  | mk c d =>
    simp only [Option.some.injEq] at hp
    subst hp
    exact pullLoop_blank_of_none a c d y (by omega) hf hs

/-! ## `+patch-prod` is sound -/

theorem patchProd_zero (s : Sock) (new : Sock) : patchProd s (A 0) new = ⟨s, A 0⟩ := by
  rw [patchProd]; simp

theorem patchProd_atom {s : Sock} {a : Nat} (new : Sock) (ha : a ≠ 0) (hs : s ≠ Sock.void) :
    patchProd s (A a) new = ⟨(So.pull new a).getD Sock.void, A a⟩ := by
  rw [patchProd]; simp [ha, hs]

theorem patchProd_cell {s : Sock} {h t : Noun} (new : Sock) (hs : s ≠ Sock.void) :
    patchProd s (C h t) new = knitAnno (patchProd (So.hed s) h new) (patchProd (So.tel s) t new) := by
  rw [patchProd]; simp [hs]

/-- Where the product is absent, `+patch-prod` makes a sock that knows nothing. -/
theorem patchProd_blank {new : Sock} {y : Noun} (hy : Fits new y) :
    ∀ (σ : Noun) (S : Sock), S ≠ Sock.void →
      (∀ π a, springAt σ π = A a → a ≠ 0 → slot? a y = none) →
      (∀ π, springAt σ π = A 0 → (sockAt S π).Blank) → (patchProd S σ new).sock.Blank := by
  intro σ
  induction σ with
  | atom a =>
    intro S hS hx hc
    by_cases ha : a = 0
    · subst ha; rw [patchProd_zero]; simpa [sockAt] using hc [] rfl
    · rw [patchProd_atom new ha hS]
      have hn := hx [] a rfl ha
      cases hp : So.pull new a with
      | none => unfold So.pull at hp; simp [ha] at hp; split at hp <;> cases hp
      | some s' => exact pull_blank_of_none hy ha hn hp
  | cell h t ih1 ih2 =>
    intro S hS hx hc
    rw [patchProd_cell new hS]
    exact knit_blank
      (ih1 _ (hed_ne_void hS) (fun π a e ha => hx (false :: π) a e ha) (fun π e => hc (false :: π) e))
      (ih2 _ (tel_ne_void hS) (fun π a e ha => hx (true :: π) a e ha) (fun π e => hc (true :: π) e))

/-- **`+patch-prod` is sound.**  A product that satisfies the provenance
invariant for a subject `y` fits what `+patch-prod` makes of its sock for
any subject sock `new` that `y` fits. -/
theorem patchProd_sound {new : Sock} {y : Noun} (hy : Fits new y) :
    ∀ (σ : Noun) (S : Sock) (p : Noun), ProvR y S σ p → Fits (patchProd S σ new).sock p := by
  intro σ
  induction σ with
  | atom a =>
    intro S p hR
    by_cases ha : a = 0
    · subst ha; rw [patchProd_zero]; simpa [FitsOpt, slotAtPath, sockAt] using hR.const [] rfl
    · rw [patchProd_atom new ha hR.nonvoid]
      have he := hR.exact [] a rfl ha
      simp only [slotAtPath] at he
      cases hp : So.pull new a with
      | none => unfold So.pull at hp; simp [ha] at hp; split at hp <;> cases hp
      | some s' => exact pull_fits hy he.symm hp
  | cell h t ih1 ih2 =>
    intro S p hR
    rw [patchProd_cell new hR.nonvoid]
    cases p with
    | cell p1 p2 =>
      exact knit_fits
        (ih1 _ _ ⟨hed_ne_void hR.nonvoid, fun π a e ha => hR.exact (false :: π) a e ha,
          fun π e => hR.const (false :: π) e⟩)
        (ih2 _ _ ⟨tel_ne_void hR.nonvoid, fun π a e ha => hR.exact (true :: π) a e ha,
          fun π e => hR.const (true :: π) e⟩)
    | atom k =>
      have hx : ∀ (b : Bool) π a, springAt (if b then t else h) π = A a → a ≠ 0 → slot? a y = none :=
        fun b π a e ha => by
          have := hR.exact (b :: π) a (by cases b <;> exact e) ha
          cases b <;> simpa [slotAtPath] using this.symm
      have hc : ∀ (b : Bool) π, springAt (if b then t else h) π = A 0 →
          (sockAt (if b then So.tel S else So.hed S) π).Blank :=
        fun b π e => by
          have := hR.const (b :: π) (by cases b <;> exact e)
          cases b <;> simpa [slotAtPath, FitsOpt, sockAt] using this
      exact (knit_blank
        (patchProd_blank hy h _ (hed_ne_void hR.nonvoid) (hx false) (hc false))
        (patchProd_blank hy t _ (tel_ne_void hR.nonvoid) (hx true) (hc true))).fits _

/-- **A memo or `%rec` hit is right on products**, given that the entry's
product satisfies the provenance invariant on every subject of the hit's
subject sock (`hR`, the product half of the relative soundness, not proved). -/
theorem hit_prod {lib : Lib} {e : Entry} {s : Sock}
    (hR : ∀ y gul p, Fits s y → Mink lib gul [] y e.fol (Tone.zero p) → ProvR y e.d.prod e.d.map p) :
    ∀ y gul p, Fits s y → Mink lib gul [] y e.fol (Tone.zero p) → Fits (patchDatum e.d s).tab.prod p :=
  fun y gul p hy hm => patchProd_sound hy _ _ _ (hR y gul p hy hm)

end SkaModel
end Formalization
