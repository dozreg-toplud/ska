import lemmas.Ska.CompSevenMink

/-!
# `[7 p q]` with calls on every `Annot`, and the parts whose need has no entries

README Gaps 12.21.

* `uokc_sevenM`: `UOKC` and `EntNew` of `[7 p q]` from its parts, for a
  formula with `MinkC7` (`uokc_sevenC`, `entNew_sevenC`).
* `uokc_sevenA`: the same on every `Annot` of the nomm `[7 p q]` (`n7`,
  `inline`, `n8`, `n9`, `n8g`, `n8l`; the wrappers by `UOKC.wrap`).
* `NoEntF` (the call-free nomms without `%6`, the indirect call whose subject
  part is such a nomm and whose formula part is in `NoEntF`, and `[7 p q]` of
  two of them), `entries_copyL`, `noEnt_ind`, `noEnt_of_noEntF`.
* `JNewQ` (`[0 axe]`, `[1 k]`), `jNew_of_jNewQ`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## `UOKC` of `[7 p q]` on every `Annot` -/

/-- **`[7 p q]` from its parts**, for a formula with `MinkC7` whose first
formula's products are among the subjects the second part is annotated on;
`EntNew` from the facts `Xp`, `Xq` that the parts' relations carried. -/
theorem uokc_sevenM (lib : Lib) (env : CallEnv) {p q : Nomm} {P Pq : Noun → Prop} {f fb fc : Noun}
    {Xp Xq : Prop} (Up : UOKC (S := S) (Map := Map) lib env P fb p) (xp : Xp)
    (Uq : UOKC (S := S) (Map := Map) lib env Pq fc q) (xq : Xq)
    (hI : ∀ y, Img lib P fb y → Pq y) (Nq : NoEnt (S := S) (Map := Map) env q) (M : MinkC7 lib P f fb fc)
    (hh : hinted env.cod (Nomm.n7 p q) = some true) :
    UOKC (S := S) (Map := Map) lib env P f (Nomm.n7 p q) ∧
      ((Xp → Xq → (EntNew (S := S) (Map := Map) env p ∨
        (JNew (S := S) (Map := Map) env p ∧ EntNew (S := S) (Map := Map) env q))) →
        EntNew (S := S) (Map := Map) env (Nomm.n7 p q)) :=
  ⟨uokc_sevenC lib env Up (Uq.mono hI) Nq M hh, fun E => entNew_sevenC Uq Nq (E xp xq)⟩

/-- **`[7 p q]` on every `Annot`**: for each form of the nomm the formula of
the `p` part and of the `q` part (`CompSevenMink.lean`), and `uokc_sevenM`;
the wrappers by `UOKC.wrap`.  The parts' relations carry facts `Xp`, `Xq`
that do not depend on the annotation (their `EntNew`); `hpu`: a call-free `p`
meets `UOK` and `Xp` (used when `[8 b c]` has an atom `b`, where the `p` part
has no annotation of its own). -/
theorem uokc_sevenA {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) (env : CallEnv) {p q : Nomm}
    {Xp Xq : Prop}
    (ihp : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f p → UOKC (S := S) (Map := Map) lib env P f p ∧ Xp)
    (ihq : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f q → UOKC (S := S) (Map := Map) lib env P f q ∧ Xq)
    (hpu : p.pure = true → UOK (S := S) (Map := Map) lib p ∧ Xp) (Nq : NoEnt (S := S) (Map := Map) env q)
    (hh : hinted env.cod (Nomm.n7 p q) = some true)
    {P : Noun → Prop} {f : Noun} {nm : Nomm} (hA : Annot lib code P f nm) :
    nm = Nomm.n7 p q → UOKC (S := S) (Map := Map) lib env P f nm ∧
      ((Xp → Xq → (EntNew (S := S) (Map := Map) env p ∨
        (JNew (S := S) (Map := Map) env p ∧ EntNew (S := S) (Map := Map) env q))) →
        EntNew (S := S) (Map := Map) env nm) := by
  induction hA with
  | n7 hb hc _ _ =>
    intro e; cases e
    exact uokc_sevenM lib env (ihp hb).1 (ihp hb).2 (ihq hc).1 (ihq hc).2 (fun _ h => h) Nq
      (minkC7_seven lib _ _ _) hh
  | inline hb hc hg _ _ =>
    intro e; cases e
    exact uokc_sevenM lib env (ihp hb).1 (ihp hb).2 (ihq hg).1 (ihq hg).2 (fun _ h => h) Nq (minkC7_inline lib hc) hh
  | @n8 P' b c p0 q0 hb hc _ _ =>
    intro e; cases e
    cases b with
    | atom k =>
      have hpp : (Nomm.cons p0 (Nomm.n0 1)).pure = true := by
        simp only [Nomm.pure, annot_atom hb, Bool.and_self]
      exact uokc_sevenM lib env (uokc_atomPair hok env hb rfl (fun h => (hpu h).1)) (hpu hpp).2 (ihq hc).1
        (ihq hc).2 (fun _ h => (img_atom h).elim) Nq (minkC7_eightAtom lib _ k c) hh
    | cell a1 a2 =>
      have H := ihp (Annot.cons hb Annot.n0)
      exact uokc_sevenM lib env H.1 H.2 (ihq hc).1 (ihq hc).2 (fun _ h => img_eight h) Nq
        (minkC7_eight lib _ a1 a2 c) hh
  | n9 hc hr _ _ =>
    intro e; cases e
    exact uokc_sevenM lib env (ihp hc).1 (ihp hc).2 (ihq hr).1 (ihq hr).2 (fun _ h => h) Nq
      (minkC7_nine lib _ _ _) hh
  | @n8g P' b c p0 r0 q0 hb hr hc _ _ _ =>
    intro e; cases e
    cases b with
    | atom k =>
      have hpp : (Nomm.cons p0 r0).pure = true := by
        simp only [Nomm.pure, annot_atom hb, annot_slot1_pure hr, Bool.and_self]
      exact uokc_sevenM lib env (uokc_atomPair hok env hb (annot_slot1_pure hr) (fun h => (hpu h).1))
        (hpu hpp).2 (ihq hc).1 (ihq hc).2 (fun _ h => (img_atom h).elim) Nq (minkC7_eightAtom lib _ k c) hh
    | cell a1 a2 =>
      have H := ihp (Annot.cons hb hr)
      exact uokc_sevenM lib env H.1 H.2 (ihq hc).1 (ihq hc).2 (fun _ h => img_eight h) Nq
        (minkC7_eight lib _ a1 a2 c) hh
  | @n8l P' b c y d q0 hb hc _ =>
    intro e; cases e
    have H := ihp (P := P') (Annot.n1 (k := C y d))
    exact uokc_sevenM lib env H.1 H.2 (ihq hc).1 (ihq hc).2 (fun _ h => img_eightL hb h)
      Nq (minkC7_eightL lib hb) hh
  | memo hm _ ih' => intro e; exact ⟨UOKC.wrap (wrapRel_memo hm) (ih' e).1, (ih' e).2⟩
  | six0 hb' _ ih' => intro e; exact ⟨UOKC.wrap (wrapRel_six hb' (Or.inl ⟨rfl, rfl⟩)) (ih' e).1, (ih' e).2⟩
  | six1 hb' _ ih' => intro e; exact ⟨UOKC.wrap (wrapRel_six hb' (Or.inr ⟨rfl, rfl⟩)) (ih' e).1, (ih' e).2⟩
  | cons => intro e; cases e
  | n0 => intro e; cases e
  | n1 => intro e; cases e
  | indirect => intro e; cases e
  | direct => intro e; cases e
  | n3 => intro e; cases e
  | n4 => intro e; cases e
  | n5 => intro e; cases e
  | n6 => intro e; cases e
  | n10 => intro e; cases e
  | n11s => intro e; cases e
  | n11d => intro e; cases e
  | mean => intro e; cases e
  | n12 => intro e; cases e
  | bare => intro e; cases e
  | crash => intro e; cases e
  | fold => intro e; cases e
  | bareLit => intro e; cases e

/-! ## Parts whose need has no entries -/

/-- **`+copy` of two needs without entries** returns one without entries. -/
theorem entries_copyL {first : NextL S} {second : Lazy S} {g g' : Gen Map} {nex : NextL S}
    (h : copyL first second g = some (nex, g')) (h1 : entries first.laz = []) (h2 : entries second = []) :
    entries nex.laz = [] := by
  have e1 := eq_ofSure_of_entries h1
  have e2 := eq_ofSure_of_entries h2
  unfold copyL at h
  obtain ⟨o, g0, _, h⟩ := bind_some h
  obtain ⟨laz, g1, hl, h⟩ := bind_some h
  rw [e1, e2, copyLazyL_ofSure] at hl
  obtain ⟨s, g2, _, hl⟩ := bind_some hl
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hl h
  obtain ⟨rfl, rfl⟩ := hl
  obtain ⟨rfl, rfl⟩ := h
  exact entries_ofSure _

/-- **The indirect call whose subject part is call-free without `%6` and
whose formula part meets `NoEnt`** meets `NoEnt`: `+past` is the identity
behind the subject part, and `+copy` joins two needs without entries. -/
theorem noEnt_ind {env : CallEnv} {b c : Nomm} (hb : b.pure = true) (h6 : noSix b = true)
    (Nc : NoEnt (S := S) (Map := Map) env c) : NoEnt (S := S) (Map := Map) env (Nomm.n2 b c Option.none) := by
  intro sup goal region g0 g' nex _ h
  obtain ⟨nex0, g1, out, pro, g2, o, g3, nexF, g4, nexF', g5, nexS, g6, h1, h2, h3, h4, h5, h6', h7⟩ :=
    runLC_n2_none h
  rw [pastL_pure _ _ hb, pure_apply] at h5
  simp only [Option.some.injEq, Prod.mk.injEq] at h5
  obtain ⟨rfl, rfl⟩ := h5
  have eF := Nc (goal := CGoal.next (lazyReg (g2.re + 1)) (jmp0 o)) trivial h4
  have eS := noEnt_pure (S := S) (Map := Map) env hb h6 (goal := CGoal.next (lazyReg g2.re) nexF.th) trivial h6'
  exact entries_copyL h7 eS eF

/-- **The parts whose run returns a need without entries**: call-free
without `%6`, the indirect call of such a subject part and a formula part of
`NoEntF`, `[7 p q]` of two of them. -/
inductive NoEntF : Nomm → Prop
  | pure {nm : Nomm} : nm.pure = true → noSix nm = true → NoEntF nm
  | ind {b c : Nomm} : b.pure = true → noSix b = true → NoEntF c → NoEntF (Nomm.n2 b c Option.none)
  | seven {p q : Nomm} : NoEntF p → NoEntF q → NoEntF (Nomm.n7 p q)

theorem noEnt_of_noEntF (env : CallEnv) {nm : Nomm} (h : NoEntF nm) : NoEnt (S := S) (Map := Map) env nm := by
  induction h with
  | pure hp h6 => exact noEnt_pure env hp h6
  | ind hb h6 _ ih => exact noEnt_ind hb h6 ih
  | seven _ _ ihp ihq => exact noEnt_sevenC ihp ihq

/-- **The call-free parts whose jump is the goal's or new**: `[0 axe]` and
`[1 k]`. -/
inductive JNewQ : Nomm → Prop
  | n0 {axe : Nat} : JNewQ (Nomm.n0 axe)
  | n1 {k : Noun} : JNewQ (Nomm.n1 k)

theorem jNew_of_jNewQ (env : CallEnv) {nm : Nomm} (h : JNewQ nm) : JNew (S := S) (Map := Map) env nm := by
  cases h with
  | n0 => exact jNew_n0 env _
  | n1 => exact jNew_n1 env _

theorem fragU_of_jNewQ {nm : Nomm} (h : JNewQ nm) : FragU (S := S) nm := by
  cases h with
  | n0 => exact FragU.x (FragX.frag fun _ => trivial)
  | n1 => exact FragU.x (FragX.frag fun _ => trivial)

end Comp
end SkaModel
end Formalization
