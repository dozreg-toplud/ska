import lemmas.Ska.ShapeCol

/-!
# A model of `+sound-far`, `+need-soft` and `+need-ord-edit` (README Gaps 19, item (f))

The two arms the push of `sof` in the direct call of `+run` slams, and the
edit `+sound-far` runs on `%10`, written from the Hoon text
(`desk/lib/nock-compilation.hoon`).  Every function returns `Option`:
`none` is the crash of the Hoon.

```hoon
++  need-ord-edit
  |=  [axe=@ ned=need-ordered]
  ^-  [don=need-ordered rec=need-ordered]
  ?:  =(1 axe)  [ned [%none ~]]
  ?:  ?=(?(%none %this) -.ned)  [[%none ~] [%none ~]]
  =/  [h=need-ordered t=need-ordered]
    ?:(?=(%both -.ned) [h.ned t.ned] [p.ned q.ned])
  ?-    (cap axe)
      %2  =/  r  $(axe (mas axe), ned h)  [don.r (cons-need rec.r t)]
      %3  =/  r  $(axe (mas axe), ned t)  [don.r (cons-need h rec.r)]
  ==
```

`needOrdEdit`: the crash is `(cap 0)`, on an axis `0` with a need that is
a cell or a `%both`.

`+sound-far` (`soundFar cod dep nom ned`) recurses on the product path:
`[^ *]` splits the need, `%6` its two branches, `%7`, `%11`, `%mean` their
`q`, `%10` both sides through `+need-ord-edit`, and a direct `%2` with
`dep > 0` the callee's nomm `nomm:(~(got by cod) b)` at `dep - 1` with the
same need.  The code table is `cod : Bell → Option Nomm` (`none`: no entry,
the crash of `+got:by`).  `sfAt cod dep rec` is one depth, with `rec` the
run at `dep - 1`; the `~+` is transparent.

`+need-soft` (`needSoft ned sur k`) recurses on the need, with `cellSure`
(`+cell-sure`, whose `-.k` crashes on the sock `%void`), `ordHed`/`ordTel`
(`+hed-need-ord`, `+tel-need-ord`, `Ska/ShapeCol.lean`) and `So.hed`,
`So.tel` (`+hed:so`, `+tel:so`).

Totality (`needOrdEdit_some`, `soundFar_some`, `needSoft_some`): the only
crashes are those named above.
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Compiler

/-- `&(x y)`: `y` only when `x` is yes. -/
def andO (x y : Option Bool) : Option Bool := x.bind fun b => if b then y else some false

/-! ## `+need-ord-edit` -/

/-- **`+need-ord-edit`**: the need of what is put at `axe` and the need of
the noun it is put into; `none` is `(cap 0)`. -/
def needOrdEdit (axe : Nat) (ned : NeedOrd) : Option (NeedOrd × NeedOrd) :=
  if axe = 1 then some (ned, NeedOrd.none) else
  match ned with
  | NeedOrd.none => some (NeedOrd.none, NeedOrd.none)
  | NeedOrd.this => some (NeedOrd.none, NeedOrd.none)
  | NeedOrd.pair h t =>
    if _h : axe < 2 then Option.none else
    if cap axe = 2 then (needOrdEdit (mas axe) h).map fun r => (r.1, consOrd r.2 t)
    else (needOrdEdit (mas axe) t).map fun r => (r.1, consOrd h r.2)
  | NeedOrd.both h t =>
    if _h : axe < 2 then Option.none else
    if cap axe = 2 then (needOrdEdit (mas axe) h).map fun r => (r.1, consOrd r.2 t)
    else (needOrdEdit (mas axe) t).map fun r => (r.1, consOrd h r.2)
termination_by axe
decreasing_by all_goals exact mas_lt axe (by omega)

/-! ## `+sound-far` -/

/-- **One depth of `+sound-far`**: `rec` is `+sound-far` at `dep - 1`. -/
def sfAt (cod : Bell → Option Nomm) (dep : Nat) (rec : Nomm → NeedOrd → Option Bool) :
    Nomm → NeedOrd → Option Bool
  | _, NeedOrd.none => some true
  | _, NeedOrd.this => some true
  | Nomm.cons p q, ned =>
      andO (sfAt cod dep rec p (ordHalves ned).1) (sfAt cod dep rec q (ordHalves ned).2)
  | Nomm.n0 a, _ => some (decide (0 = a))
  | Nomm.n6 _ q r, ned => andO (sfAt cod dep rec q ned) (sfAt cod dep rec r ned)
  | Nomm.n7 _ q, ned => sfAt cod dep rec q ned
  | Nomm.n11s _ q _, ned => sfAt cod dep rec q ned
  | Nomm.n11d _ _ q _, ned => sfAt cod dep rec q ned
  | Nomm.mean _ _ q _ _, ned => sfAt cod dep rec q ned
  | Nomm.n2 _ _ Option.none, _ => some false
  | Nomm.n2 _ _ (some (b, _)), ned => if dep = 0 then some false else (cod b).bind fun m => rec m ned
  | Nomm.n10 a v q, ned =>
      (needOrdEdit a ned).bind fun e => andO (sfAt cod dep rec v e.1) (sfAt cod dep rec q e.2)
  | _, _ => some false

/-- **`+sound-far`** at depth `dep`. -/
def soundFar (cod : Bell → Option Nomm) : Nat → Nomm → NeedOrd → Option Bool
  | 0 => sfAt cod 0 (fun _ _ => Option.none)
  | d + 1 => sfAt cod (d + 1) (soundFar cod d)

/-! ## `+need-soft` -/

/-- **`+cell-sure`**: `none` is `-.k` of the sock `%void`. -/
def cellSure (sur : NeedOrd) (k : Sock) : Option Bool :=
  match sur with
  | NeedOrd.both _ _ => some true
  | NeedOrd.pair _ _ => some true
  | _ => match k with
    | Sock.void => Option.none
    | Sock.mk (Cape.cell _ _) _ => some true
    | Sock.mk Cape.yes (Noun.cell _ _) => some true
    | Sock.mk _ _ => some false

/-- **`+need-soft`**. -/
def needSoft : NeedOrd → NeedOrd → Sock → Option Bool
  | NeedOrd.none, _, _ => some false
  | NeedOrd.this, _, _ => some false
  | NeedOrd.pair h t, sur, k => (cellSure sur k).bind fun c =>
      if c then orB (needSoft h (ordHed sur) (So.hed k)) (needSoft t (ordTel sur) (So.tel k)) else some true
  | NeedOrd.both h t, sur, k => (cellSure sur k).bind fun c =>
      if c then orB (needSoft h (ordHed sur) (So.hed k)) (needSoft t (ordTel sur) (So.tel k)) else some true

/-! ## Totality -/

theorem andO_some {x y : Option Bool} (hx : ∃ a, x = some a) (hy : ∃ b, y = some b) : ∃ c, andO x y = some c := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; cases a <;> simp [andO]

theorem orB_some {x y : Option Bool} (hx : ∃ a, x = some a) (hy : ∃ b, y = some b) : ∃ c, orB x y = some c := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; cases a <;> simp [orB]

/-- **`+need-ord-edit` returns on every axis but `0`.** -/
theorem needOrdEdit_some : ∀ (axe : Nat), 1 ≤ axe → ∀ ned, ∃ e, needOrdEdit axe ned = some e := by
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
    intro ha ned
    rw [needOrdEdit.eq_def]
    by_cases h1 : axe = 1
    · simp [h1]
    · have h2 : 2 ≤ axe := by omega
      have hm := mas_lt axe h2
      have hm1 := mas_pos axe h2
      simp only [h1, if_false]
      cases ned with
      | none => simp
      | this => simp
      | pair p q =>
        simp only [show ¬ axe < 2 by omega, dite_false]
        obtain ⟨e1, he1⟩ := ih (mas axe) hm hm1 p
        obtain ⟨e2, he2⟩ := ih (mas axe) hm hm1 q
        split <;> simp [he1, he2]
      | both p q =>
        simp only [show ¬ axe < 2 by omega, dite_false]
        obtain ⟨e1, he1⟩ := ih (mas axe) hm hm1 p
        obtain ⟨e2, he2⟩ := ih (mas axe) hm hm1 q
        split <;> simp [he1, he2]

/-- `+need-ord-edit` at axis `0` on a cell need or a `%both` crashes. -/
theorem needOrdEdit_zero {ned : NeedOrd} (h : ned ≠ NeedOrd.none ∧ ned ≠ NeedOrd.this) :
    needOrdEdit 0 ned = Option.none := by
  rw [needOrdEdit.eq_def]; cases ned <;> simp_all

/-- No `%10` with axis `0` in a nomm (the class of `+sound-far`'s totality;
`Bake.NoAx0` restricted to what `+sound-far` walks is weaker). -/
def SfNoAx0 : Nomm → Prop
  | Nomm.cons p q => SfNoAx0 p ∧ SfNoAx0 q
  | Nomm.n6 _ q r => SfNoAx0 q ∧ SfNoAx0 r
  | Nomm.n7 _ q => SfNoAx0 q
  | Nomm.n11s _ q _ => SfNoAx0 q
  | Nomm.n11d _ _ q _ => SfNoAx0 q
  | Nomm.mean _ _ q _ _ => SfNoAx0 q
  | Nomm.n10 a v q => 1 ≤ a ∧ SfNoAx0 v ∧ SfNoAx0 q
  | _ => True

/-- The callees `+sound-far` meets on the product path of a nomm (at
`dep > 0`). -/
def sfBells : Nomm → List Bell
  | Nomm.cons p q => sfBells p ++ sfBells q
  | Nomm.n6 _ q r => sfBells q ++ sfBells r
  | Nomm.n7 _ q => sfBells q
  | Nomm.n11s _ q _ => sfBells q
  | Nomm.n11d _ _ q _ => sfBells q
  | Nomm.mean _ _ q _ _ => sfBells q
  | Nomm.n10 _ v q => sfBells v ++ sfBells q
  | Nomm.n2 _ _ (some (b, _)) => [b]
  | _ => []

/-- One depth returns when the nomm has no `%10` at axis `0` on the product
path and every callee there either has a code entry on which `rec` returns,
or `dep = 0`. -/
theorem sfAt_some (cod : Bell → Option Nomm) (dep : Nat) (rec : Nomm → NeedOrd → Option Bool) :
    ∀ (nom : Nomm) (ned : NeedOrd), SfNoAx0 nom →
      (dep ≠ 0 → ∀ b ∈ sfBells nom, ∃ m, cod b = some m ∧ ∀ ned', ∃ s, rec m ned' = some s) →
      ∃ s, sfAt cod dep rec nom ned = some s := by
  intro nom
  induction nom with
  | cons p q ihp ihq =>
    intro ned hn hb
    cases ned with
    | none => simp [sfAt]
    | this => simp [sfAt]
    | pair a b =>
      simp only [sfAt]
      exact andO_some (ihp _ hn.1 fun h b m => hb h b (List.mem_append_left _ m))
        (ihq _ hn.2 fun h b m => hb h b (List.mem_append_right _ m))
    | both a b =>
      simp only [sfAt]
      exact andO_some (ihp _ hn.1 fun h b m => hb h b (List.mem_append_left _ m))
        (ihq _ hn.2 fun h b m => hb h b (List.mem_append_right _ m))
  | n6 p q r _ ihq ihr =>
    intro ned hn hb
    cases ned <;> simp only [sfAt] <;> first
      | exact ⟨_, rfl⟩
      | exact andO_some (ihq _ hn.1 fun h b m => hb h b (List.mem_append_left _ m))
          (ihr _ hn.2 fun h b m => hb h b (List.mem_append_right _ m))
  | n7 p q _ ihq =>
    intro ned hn hb
    cases ned <;> simp only [sfAt] <;> first | exact ⟨_, rfl⟩ | exact ihq _ hn hb
  | n11s t q bd ihq =>
    intro ned hn hb
    cases ned <;> simp only [sfAt] <;> first | exact ⟨_, rfl⟩ | exact ihq _ hn hb
  | n11d t h q bd _ ihq =>
    intro ned hn hb
    cases ned <;> simp only [sfAt] <;> first | exact ⟨_, rfl⟩ | exact ihq _ hn hb
  | mean p b q bd k _ ihq =>
    intro ned hn hb
    cases ned <;> simp only [sfAt] <;> first | exact ⟨_, rfl⟩ | exact ihq _ hn hb
  | n10 a v q ihv ihq =>
    intro ned hn hb
    obtain ⟨ha, hv, hq⟩ := hn
    cases ned with
    | none => simp [sfAt]
    | this => simp [sfAt]
    | pair x y =>
      simp only [sfAt]
      obtain ⟨e, he⟩ := needOrdEdit_some a ha (NeedOrd.pair x y)
      rw [he]
      exact andO_some (ihv _ hv fun h b m => hb h b (List.mem_append_left _ m))
        (ihq _ hq fun h b m => hb h b (List.mem_append_right _ m))
    | both x y =>
      simp only [sfAt]
      obtain ⟨e, he⟩ := needOrdEdit_some a ha (NeedOrd.both x y)
      rw [he]
      exact andO_some (ihv _ hv fun h b m => hb h b (List.mem_append_left _ m))
        (ihq _ hq fun h b m => hb h b (List.mem_append_right _ m))
  | n2 p q info _ _ =>
    intro ned hn hb
    rcases info with _ | ⟨b, k⟩
    · cases ned <;> simp [sfAt]
    · cases ned <;> simp only [sfAt] <;> first
        | exact ⟨_, rfl⟩
        | (by_cases hd : dep = 0
           · simp [hd]
           · obtain ⟨m, hm, hr⟩ := hb hd b (by simp [sfBells])
             simp only [hd, if_false, hm, Option.bind_some]
             exact hr _)
  | n0 _ => intro ned _ _; cases ned <;> simp [sfAt]
  | n1 _ => intro ned _ _; cases ned <;> simp [sfAt]
  | n3 _ _ => intro ned _ _; cases ned <;> simp [sfAt]
  | n4 _ _ => intro ned _ _; cases ned <;> simp [sfAt]
  | n5 _ _ _ _ => intro ned _ _; cases ned <;> simp [sfAt]
  | n12 _ _ _ _ => intro ned _ _; cases ned <;> simp [sfAt]

/-- **The code table is closed for `+sound-far` at depth `dep`**: every
nomm reached has no `%10` at axis `0` on its product path, and each callee
met there with depth left has a code entry, which is closed at the depth
below. -/
def SfClosed (cod : Bell → Option Nomm) : Nat → Nomm → Prop
  | 0, nom => SfNoAx0 nom
  | d + 1, nom => SfNoAx0 nom ∧ ∀ b ∈ sfBells nom, ∃ m, cod b = some m ∧ SfClosed cod d m

/-- **`+sound-far` returns** on every nomm closed at its depth, whatever the
need. -/
theorem soundFar_some (cod : Bell → Option Nomm) :
    ∀ (dep : Nat) (nom : Nomm), SfClosed cod dep nom → ∀ ned, ∃ s, soundFar cod dep nom ned = some s
  | 0, nom, h, ned => sfAt_some cod 0 _ nom ned h (fun h0 => absurd rfl h0)
  | d + 1, nom, h, ned => sfAt_some cod (d + 1) _ nom ned h.1 fun _ b m => by
      obtain ⟨m', hm, hc⟩ := h.2 b m
      exact ⟨m', hm, fun ned' => soundFar_some cod d m' hc ned'⟩

/-! ## Totality of `+need-soft` -/

theorem cellSure_some (sur : NeedOrd) {k : Sock} (hk : k ≠ Sock.void) : ∃ c, cellSure sur k = some c := by
  unfold cellSure
  rcases k with _ | ⟨c, d⟩
  · exact absurd rfl hk
  · cases sur <;> simp only <;> first | exact ⟨_, rfl⟩ | (rcases c with _ | _ | _ <;> rcases d with _ | _ <;> simp)

theorem so_hed_ne_void {k : Sock} (hk : k ≠ Sock.void) : So.hed k ≠ Sock.void := by
  rcases k with _ | ⟨c, d⟩
  · exact absurd rfl hk
  · rcases c with _ | _ | _ <;> rcases d with _ | _ <;> simp [So.hed, Sock.dunno]

theorem so_tel_ne_void {k : Sock} (hk : k ≠ Sock.void) : So.tel k ≠ Sock.void := by
  rcases k with _ | ⟨c, d⟩
  · exact absurd rfl hk
  · rcases c with _ | _ | _ <;> rcases d with _ | _ <;> simp [So.tel, Sock.dunno]

/-- **`+need-soft` returns on every sock but `%void`.** -/
theorem needSoft_some : ∀ (ned sur : NeedOrd) (k : Sock), k ≠ Sock.void → ∃ s, needSoft ned sur k = some s
  | NeedOrd.none, _, _, _ => ⟨_, rfl⟩
  | NeedOrd.this, _, _, _ => ⟨_, rfl⟩
  | NeedOrd.pair h t, sur, k, hk => by
    obtain ⟨c, hc⟩ := cellSure_some sur hk
    simp only [needSoft, hc, Option.bind_some]
    cases c
    · exact ⟨_, rfl⟩
    · exact orB_some (needSoft_some h _ _ (so_hed_ne_void hk)) (needSoft_some t _ _ (so_tel_ne_void hk))
  | NeedOrd.both h t, sur, k, hk => by
    obtain ⟨c, hc⟩ := cellSure_some sur hk
    simp only [needSoft, hc, Option.bind_some]
    cases c
    · exact ⟨_, rfl⟩
    · exact orB_some (needSoft_some h _ _ (so_hed_ne_void hk)) (needSoft_some t _ _ (so_tel_ne_void hk))

end Comp
end SkaModel
end Formalization
