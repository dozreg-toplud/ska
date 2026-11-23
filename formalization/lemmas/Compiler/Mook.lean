import lemmas.Compiler.Monk
import lemmas.Hoon.Lists
import lemmas.Pill.Arm.Mook
import lemmas.Pill.Arm.Mock
import lemmas.Pill.Arm.Soft
import lemmas.Pill.Arm.Tank

/-!
`+mook` and `+mock` of `hoon.hoon` against `mookF` and `Mock` of
`lemmas/Ska/Mink.lean`.

```hoon
++  mock
  ~/  %mock
  |=  [[sub=* fol=*] gul=$@(~ $-(^ (unit (unit))))]
  (mook (mink [sub fol] gul))
::
++  mook
  |=  ton=tone
  ^-  toon
  ?.  ?=([%2 *] ton)
    ton
  |^  [%2 (turn skip rend)]
  ++  skip  ...
  ++  rend  ...
  --
```

The skeleton is proved exactly: the test of the tone, `+skip` (with `+lent`,
`+gth`, `+scag`, `+slag`, `+sub` and `+weld` of the library), the `+turn` of
`rend` over the trace, and the `%mean` branch of `rend` on a cell, which slams
`+mack` (proved in `Monk.lean`) and then `(soft tank)`.  Three things stay
hypotheses, each stated on the pill's Nock and matching one field of the
model's `Lib`:

1. `SoftTankIs`: the gate `(soft tank)` of the pill computes `Lib.softTank`.
   `+soft` runs `+mole`, which runs `+mock` again, on the mold `+tank`.
2. `SkipMsgIs`: the cord `+skip` puts in place of the frames it drops is
   `Lib.skipMsg`.  It is made by `+scow` and `+crip`.
3. `RendBaseIs`: `rend` on a frame other than a `%mean` of a cell computes
   `Lib.rendBase`.  Those branches format with `+rip`, `+scow`, `+smyt` and
   `(soft path)`, `(soft spot)`.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon

/-! ## The cores of `+mook` -/

/-- The gate `+mook` on the tone `ton`, in the context `ctx`. -/
abbrev mookGate (ton ctx : Noun) : Noun := C mook.battery (C ton ctx)

/-- The `|^` core of `+mook`, `[rend skip buc]` on the gate. -/
abbrev mookCore (ton ctx : Noun) : Noun := C mook.core (mookGate ton ctx)

/-- Slamming the gate `rend` of the `|^` core on the frame `fr`. -/
abbrev rendSlam (fr ton ctx : Noun) : Option Noun :=
  nock (C mook.rend.battery (C fr (mookCore ton ctx))) mook.rend.battery

/-- The bunt of the mold `+tank`, `leaf+~`. -/
abbrev tankBunt : Noun := C (A 0x6661656c) (A 0)

/-- What `+mook` reads from its context `ctx` (layer 4): `+mack` and what it
reads, `+soft`, and in layer 2 (`l2`) the arms `+turn`, `+lent`, `+weld`,
`+scag`, `+slag` and the mold `+tank`, with `+gth` and `+sub` in layer 1, the
tail of layer 2. -/
abbrev MookIn (ctx : Noun) : Prop :=
  slot? mack.axis ctx = some mack.arm ∧ MackIn ctx ∧ slot? soft.axis ctx = some soft.arm ∧
  ∃ l2, slot? mook.layer2.axis ctx = some l2 ∧
    slot? turn.axis l2 = some turn.arm ∧ HomoIn l2 ∧ slot? lent.axis l2 = some lent.arm ∧
    slot? weld.axis l2 = some weld.arm ∧ slot? scag.axis l2 = some scag.arm ∧
    slot? slag.axis l2 = some slag.arm ∧ slot? tank.axis l2 = some tank.arm ∧
    Below (fun l1 => GthIn l1 ∧ SubIn l1) l2

/-- The gate `(soft tank)` of the pill, slammed on `n`, returns
`Lib.softTank n` as a unit.  The gate is what `+soft` of the context makes of
the mold `+tank` of layer 2 `l2`. -/
def SoftTankIs (lib : Lib) (ctx : Noun) : Prop :=
  ∀ l2, slot? mook.layer2.axis ctx = some l2 → ∀ n,
    nock (C soft.gate.battery (C n (C soft.battery (C (C tank.battery (C tankBunt l2)) ctx))))
      soft.gate.battery = some (unitN (lib.softTank n))

/-- The cord that `+skip` makes for a trace of `yel > 1024` frames is
`Lib.skipMsg (yel - 1024)`.  The formula reads `yel` and the context. -/
def SkipMsgIs (lib : Lib) (ctx : Noun) : Prop :=
  ∀ (yel : Nat) (ton : Noun), 1024 < yel →
    nock (C (A yel) (mookCore ton ctx)) mook.skip.msg = some (lib.skipMsg (yel - 1024))

/-- `rend` on a frame other than a `%mean` of a cell computes `Lib.rendBase`. -/
def RendBaseIs (lib : Lib) (ctx : Noun) : Prop :=
  ∀ (tag : Nat) (dat ton : Noun), (tag = Tag.mean → ∃ a, dat = A a) →
    rendSlam (C (A tag) dat) ton ctx = lib.rendBase tag dat

@[nock_exec] theorem mook_arm (c : Noun) :
    nock c mook.arm = some (C mook.battery (C (C (A 2) (A 0)) c)) := by
  nock_open mook.arm; simp only [nock_exec]

@[nock_exec] theorem mook_rend_arm (c : Noun) :
    nock c mook.rend.arm = some (C mook.rend.battery (C (C (A 0) (A 0)) c)) := by
  nock_open mook.rend.arm; simp only [nock_exec]

@[nock_exec] theorem soft_arm (c : Noun) :
    nock c soft.arm = some (C soft.battery (C (C (C (A 0) (A 15)) (C (A 0) (C (A 0) (A 0)))) c)) := by
  nock_open soft.arm; simp only [nock_exec]

@[nock_exec] theorem soft_battery (s c : Noun) :
    nock (C soft.battery (C s c)) soft.battery
      = some (C soft.gate.battery (C (A 0) (C soft.battery (C s c)))) := by
  nock_open soft.battery; simp only [nock_exec]

@[nock_exec] theorem tank_arm (c : Noun) :
    nock c tank.arm = some (C tank.battery (C tankBunt c)) := by
  nock_open tank.arm; simp only [nock_exec]

/-! ## Traces as lists -/

theorem trN_eq (t : Trace) : trN t = listN (t.map Frame.toNoun) := by
  induction t with
  | nil => rfl
  | cons fr t ih => simp [trN, listNoun, ih] at *

theorem listNoun_id (l : List Noun) : listNoun id l = listN l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [listNoun, ih]

/-! ## `+skip` -/

theorem slot_layer1 {ctx bat l1 : Noun} (h : slot? mook.layer2.axis ctx = some (C bat l1)) :
    slot? mink.layer1.axis ctx = some l1 := slot?_right h

/-- `+skip` keeps a trace of at most 1024 frames, and keeps the first 512
and the last 512 of a longer one, with a `%lose` frame between them. -/
theorem mook_skip (lib : Lib) (ctx : Noun) (hc : MookIn ctx) (hm : SkipMsgIs lib ctx)
    (tr : Trace) :
    nock (mookCore (twoN tr) ctx) mook.skip
      = some (listN ((skip lib (fun m => (Tag.lose, m)) tr).map Frame.toNoun)) := by
  obtain ⟨_, _, _, l2, hl2, _, _, hlent, hweld, hscag, hslag, _, hb⟩ := hc
  obtain ⟨bat, l1, rfl, hgth, hsub⟩ := hb.elim
  have hl1 := slot_layer1 hl2
  have hdec : Below DecIn (C bat l1) := hsub.2
  have hmsg := hm tr.length (twoN tr)
  nock_open mook.skip
  by_cases hlen : 1024 < tr.length
  · simp [nock_exec, trN_eq, hl2, hl1, hlent, hweld, hscag, hslag, hgth, hsub, lent_arm,
      lent_gate, gth_arm, gth_gate _ hgth.2, weld_arm, weld_gate, scag_arm, scag_gate _ hdec,
      slag_arm, slag_gate _ hdec, sub_arm, sub_gate _ hsub.2 512 tr.length (by omega), hlen,
      skip, hmsg hlen, Tag.lose]
    rw [← listN_cons, appendN_listN]; rfl
  · simp [nock_exec, trN_eq, hl2, hl1, hlent, hgth, lent_arm, lent_gate, gth_arm,
      gth_gate _ hgth.2, hlen, skip]

/-! ## `rend` on a `%mean` of a cell -/

theorem ite_unitN (o : Option Noun) (X : Noun) :
    (if A 0 = unitN o then some X else slot? 3 (unitN o)) = some (o.getD X) := by
  cases o <;> simp [unitN, nock_exec]

/-- What `rend` makes of a `%mean` frame with a cell: the unit that `+mack`
returns on the trap, `leaf+"####"` for `~`, and the product through
`(soft tank)` otherwise. -/
theorem rend_mean (lib : Lib) (ctx : Noun) (hc : MookIn ctx) (hst : SoftTankIs lib ctx)
    (ton h t : Noun) :
    rendSlam (C (A Tag.mean) (C h t)) ton ctx =
      (nock (C mack.battery (C (C (C h t) h) ctx)) mack.battery).bind fun y =>
        if A 0 = y then some leafHash else (slot? 3 y).bind fun v => some (rendProduct lib v) := by
  obtain ⟨hmack, _, hsoft, l2, hl2, _, _, _, _, _, _, htank, _⟩ := hc
  have hs := hst l2 hl2
  unfold rendSlam
  nock_open mook.rend.battery
  simp only [nock_exec, Tag.mean]
  nock_open mook.rend.mean
  simp [nock_exec, nock_ite, bind_bind_some, hmack, mack_arm, hsoft, hl2, htank, hs, ite_unitN,
    rendProduct, leafHash, leafMookMean, tape, listNoun, Tag.leaf]

/-! ## `rend` on any frame -/

/-- `rend` on a frame of a trace returns `x` exactly when the model's `rendF`
does with some fuel. -/
theorem rend_frame_iff (lib : Lib) (ctx : Noun) (hc : MookIn ctx) (hslam : SlamIsNock lib)
    (hrb : RendBaseIs lib ctx) (hst : SoftTankIs lib ctx) (ton : Noun) (fr : Frame) (x : Noun) :
    rendSlam fr.toNoun ton ctx = some x ↔ ∃ k, rendF lib k fr = some x := by
  obtain ⟨tag, dat⟩ := fr
  rcases dat with a | ⟨h, t⟩
  · rw [show Frame.toNoun (tag, A a) = C (A tag) (A a) from rfl,
      hrb tag (A a) ton (fun _ => ⟨a, rfl⟩)]
    simp [rendF]
  by_cases htag : tag = Tag.mean
  · subst htag
    rw [show Frame.toNoun (Tag.mean, C h t) = C (A Tag.mean) (C h t) from rfl,
      rend_mean lib ctx hc hst]
    have hmk := mack_gate_iff lib ctx hc.2.1 hslam (C h t) h
    cases hm : nock (C mack.battery (C (C (C h t) h) ctx)) mack.battery with
    | none =>
      simp only [Option.bind_none, reduceCtorEq, false_iff, not_exists]
      intro k hk
      simp only [rendF, if_true] at hk
      cases hr : minkF lib (A 0) k [] (C h t) h with
      | none => rw [hr] at hk; simp at hk
      | some r =>
        have := (hmk (unitN (mackUnit r))).mpr ⟨r, ⟨k, hr⟩, rfl⟩
        rw [hm] at this
        cases this
    | some y =>
      obtain ⟨r, ⟨n, hn⟩, rfl⟩ := (hmk y).mp hm
      have hpill : (if A 0 = unitN (mackUnit r) then some leafHash else
          (slot? 3 (unitN (mackUnit r))).bind fun v => some (rendProduct lib v))
          = rendF lib n (Tag.mean, C h t) := by
        simp only [rendF, if_true, hn]
        cases r <;> simp [mackUnit, unitN, nock_exec]
      simp only [Option.bind_some, hpill]
      constructor
      · intro hx; exact ⟨n, hx⟩
      · rintro ⟨k, hk⟩
        simp only [rendF, if_true] at hk
        cases hr : minkF lib (A 0) k [] (C h t) h with
        | none => rw [hr] at hk; simp at hk
        | some r' =>
          cases minkF_det lib (A 0) hn hr
          simp only [rendF, if_true, hn]
          rw [hr] at hk
          exact hk
  · rw [show Frame.toNoun (tag, C h t) = C (A tag) (C h t) from rfl,
      hrb tag (C h t) ton (fun h' => absurd h' htag)]
    simp [rendF, htag]

/-! ## The map over the trace -/

theorem mapM_map' {α β γ : Type} (f : α → β) (g : β → Option γ) :
    ∀ (l : List α), (l.map f).mapM g = l.mapM (fun a => g (f a))
  | [] => rfl
  | a :: l => by simp only [List.map_cons, List.mapM_cons, mapM_map' f g l]

/-- A map whose function returns `b` on `a` exactly when a fuelled one does
with some fuel, monotone in the fuel, returns a list exactly when the fuelled
map does with some fuel. -/
theorem mapM_fuel_iff {α β : Type} (G : α → Option β) (F : Nat → α → Option β)
    (hmono : ∀ {k k' : Nat}, k ≤ k' → ∀ a, OptLe (F k a) (F k' a))
    (hG : ∀ a b, G a = some b ↔ ∃ k, F k a = some b) :
    ∀ (l : List α) (ys : List β), l.mapM G = some ys ↔ ∃ k, l.mapM (F k) = some ys
  | [], ys => by simp
  | a :: l, ys => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq]
    constructor
    · rintro ⟨b, hb, bs, hbs, rfl⟩
      obtain ⟨k1, hk1⟩ := (hG a b).mp hb
      obtain ⟨k2, hk2⟩ := (mapM_fuel_iff G F hmono hG l bs).mp hbs
      exact ⟨max k1 k2, b, hmono (Nat.le_max_left k1 k2) a b hk1, bs,
        mapM_le (hmono (Nat.le_max_right k1 k2)) l bs hk2, rfl⟩
    · rintro ⟨k, b, hb, bs, hbs, rfl⟩
      exact ⟨b, (hG a b).mpr ⟨k, hb⟩, bs, (mapM_fuel_iff G F hmono hG l bs).mpr ⟨k, hbs⟩, rfl⟩

/-! ## The gate `+mook` -/

theorem map_bind_some {α β γ : Type} (o : Option α) (f : α → β) (g : β → γ) :
    ((o.map f).bind fun r => some (g r)) = o.map fun a => g (f a) := by
  cases o <;> rfl

/-- The arm `$` of the `|^` core: `[%2 (turn skip rend)]`. -/
theorem mook_buc (lib : Lib) (ctx : Noun) (hc : MookIn ctx) (hm : SkipMsgIs lib ctx)
    (tr : Trace) :
    nock (mookCore (twoN tr) ctx) mook.buc =
      (((skip lib (fun m => (Tag.lose, m)) tr).map Frame.toNoun).mapM
          (fun n => rendSlam n (twoN tr) ctx)).map fun ys => C (A 2) (listN ys) := by
  have hskip := mook_skip lib ctx hc hm tr
  obtain ⟨_, _, _, l2, hl2, hturn, hhomo, _⟩ := hc
  have ht := turn_gate_mapM l2 hhomo mook.rend.battery (C (A 0) (A 0)) (mookCore (twoN tr) ctx)
    (fun n => rendSlam n (twoN tr) ctx) ((skip lib (fun m => (Tag.lose, m)) tr).map Frame.toNoun)
    (fun _ _ => rfl)
  nock_open mook.buc
  simp [nock_exec, hl2, hturn, turn_arm, hskip, ht, map_bind_some]

/-- Slamming the pill's `+mook` on the encoding of a tone `ton` returns `x`
exactly when the model's `mookF` returns, with some fuel, a toon that `x`
encodes. -/
theorem mook_gate_iff (lib : Lib) (ctx : Noun) (hc : MookIn ctx) (hslam : SlamIsNock lib)
    (hrb : RendBaseIs lib ctx) (hst : SoftTankIs lib ctx) (hm : SkipMsgIs lib ctx)
    (ton : Tone) (x : Noun) :
    nock (mookGate ton.toNoun ctx) mook.battery = some x ↔
      ∃ k toon, mookF lib k ton = some toon ∧ x = toon.toNoun := by
  cases ton with
  | zero p =>
    have h0 : nock (mookGate (C (A 0) p) ctx) mook.battery = some (C (A 0) p) := by
      nock_open mook.battery; simp [nock_exec]
    simp [Tone.toNoun, h0, mookF, Toon.toNoun, eq_comm]
  | one p =>
    have h1 : nock (mookGate (C (A 1) p) ctx) mook.battery = some (C (A 1) p) := by
      nock_open mook.battery; simp [nock_exec]
    simp [Tone.toNoun, h1, mookF, Toon.toNoun, eq_comm]
  | two tr =>
    have hb := mook_buc lib ctx hc hm tr
    have hgate : nock (mookGate (Tone.two tr).toNoun ctx) mook.battery
        = nock (mookCore (twoN tr) ctx) mook.buc := by
      nock_open mook.battery
      simp [nock_exec, Tone.toNoun]
    rw [hgate, hb, mapM_map', Option.map_eq_some_iff]
    simp only [mookF, Option.map_eq_some_iff]
    have hfr := mapM_fuel_iff (fun fr => rendSlam fr.toNoun (twoN tr) ctx) (rendF lib)
      (fun hk fr => rendF_le lib hk fr) (fun fr y => rend_frame_iff lib ctx hc hslam hrb hst _ fr y)
    constructor
    · rintro ⟨ys, hys, rfl⟩
      obtain ⟨k, hk⟩ := (hfr _ ys).mp hys
      exact ⟨k, Toon.two ys, ⟨ys, hk, rfl⟩, by simp [Toon.toNoun, listNoun_id]⟩
    · rintro ⟨k, _, ⟨ys, hk, rfl⟩, rfl⟩
      exact ⟨ys, (hfr _ ys).mpr ⟨k, hk⟩, by simp [Toon.toNoun, listNoun_id]⟩

/-! ## The gate `+mock` -/

/-- What `+mock` reads from its context: `+mook` and what it reads (which
holds `+mink` through `+mack` and `+monk`). -/
abbrev MockIn (ctx : Noun) : Prop := slot? mook.axis ctx = some mook.arm ∧ MookIn ctx

/-- Slamming the pill's `+mock` on `[[s f] gul]` returns `x` exactly when the
model's `Mock` returns a toon that `x` encodes. -/
theorem mock_gate_iff (lib : Lib) (ctx : Noun) (hc : MockIn ctx) (hslam : SlamIsNock lib)
    (hrb : RendBaseIs lib ctx) (hst : SoftTankIs lib ctx) (hm : SkipMsgIs lib ctx)
    (s f gul x : Noun) :
    nock (C mock.battery (C (C (C s f) gul) ctx)) mock.battery = some x ↔
      ∃ toon, Mock lib s f gul toon ∧ x = toon.toNoun := by
  obtain ⟨hmook, hc'⟩ := hc
  have hmi : MinkIn ctx := hc'.2.1.2.2
  have hmk : slot? mink.axis ctx = some mink.arm := hc'.2.1.2.1
  have hpill : nock (C mock.battery (C (C (C s f) gul) ctx)) mock.battery
      = (nock (C mink.battery (C (C (C s f) gul) ctx)) mink.battery).bind
          fun y => nock (mookGate y ctx) mook.battery := by
    nock_open mock.battery
    simp [nock_exec, hmook, hmk, mook_arm, mink_arm, bind_bind_some]
  rw [hpill]
  cases hmn : nock (C mink.battery (C (C (C s f) gul) ctx)) mink.battery with
  | none =>
    simp only [Option.bind_none, reduceCtorEq, false_iff, not_exists, not_and]
    rintro toon ⟨k, hk⟩ _
    cases hr : minkF lib gul k [] s f with
    | none => rw [hr] at hk; simp at hk
    | some r =>
      rw [mink_gate_of_model lib ctx hmi hslam s f gul r ⟨k, hr⟩] at hmn
      cases hmn
  | some y =>
    obtain ⟨r, rfl, ⟨n, hn⟩⟩ := mink_gate_to_model lib ctx hmi hslam s f gul y hmn
    simp only [Option.bind_some]
    rw [mook_gate_iff lib ctx hc' hslam hrb hst hm]
    constructor
    · rintro ⟨k, toon, hk, rfl⟩
      refine ⟨toon, ⟨max n k, ?_⟩, rfl⟩
      rw [minkF_le lib gul (Nat.le_max_left n k) _ _ _ r hn]
      exact mookF_le lib (Nat.le_max_right n k) r toon hk
    · rintro ⟨toon, ⟨k, hk⟩, rfl⟩
      cases hr : minkF lib gul k [] s f with
      | none => rw [hr] at hk; simp at hk
      | some r' =>
        rw [hr] at hk
        cases minkF_det lib gul hn hr
        exact ⟨k, toon, hk, rfl⟩

end Compiler
end Formalization
