import lemmas.Ska.OptAliasRel

/-!
# The simulation of `+alias`, forward

With the relation `AliasI` of `OptAliasRel.lean` between a configuration `x`
of the code before (reached from the entry `(S0, V0, T0)`) and `x'` of the
code after (blocks `g.new`):

* **`alias_fwd_step`**: a step of `x` is matched by at most one step of `x'`
  (none for a dropped op and in the dead mode), with `AliasI` after: the
  pass from the pending mode (`apend_pass`), an op of the live mode
  (`alive_op`, or the dead mode at a dead fill, `alive_dead`), the jump at
  the end of the live mode (`alive_jump`), an `%imm` op of the dead mode
  (`adead_step`).
* **`alias_fwd_end`**: an end of `x` is an end of `x'` after the `%imm` ops
  the code after has left in the dead mode (`adead_flush`): a kept op ends
  as the op before (`XRel`), a dropped op does not end (`akd_exec`), an end of
  the block returns the same (`afn_end`, `endR_congr`).
* **`alias_fwd`**: on paths.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock

set_option linter.unusedSectionVars false

variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

/-- What an op returns when it ends the function (`Path.endOf` at an op). -/
def endPole {σ : Type} : Option (Tone × Map (Option Noun) × Trace × σ) → Option (Tone × σ)
  | some (Tone.zero _, _, _, _) => none
  | some (ton, _, _, st') => some (ton, st')
  | none => none

section
variable {σ : Type} {lib : Lib} {O : Oracle σ} {c c' : Straight Map} {gul : Noun}

theorem endOf_op {x : Path.Cfg σ Map} {p : Pole} {rest : List Pole} (hp : x.params = []) (hq : x.b.par = [])
    (hb : x.b.body = p :: rest) : Path.endOf lib O gul x = endPole (execPole lib O gul x.st p x.regs x.t) := by
  unfold Path.endOf
  rw [if_neg (by simp [hp, hq]), hb]
  simp only
  cases execPole lib O gul x.st p x.regs x.t with
  | none => rfl
  | some r =>
    obtain ⟨ton, R, t, st⟩ := r
    cases ton <;> rfl

theorem endPole_xrel {r r' : Option (Tone × Map (Option Noun) × Trace × σ)} {regs regs' : Map (Option Noun)}
    {dst : Option Nat} (h : XRel r r' regs regs' dst) : endPole r' = endPole r := by
  rcases h with ⟨rfl, rfl⟩ | ⟨ton, t2, s2, W, rfl, rfl, -, -⟩
  · rfl
  · cases ton <;> rfl

theorem fe_step {S0 : σ} {V0 : List Noun} {T0 : Trace} {es : List (Nat × Nat)} {x y : Path.Cfg σ Map}
    {e : List (Nat × Nat)} (hfe : Path.FromEntry (lib := lib) (O := O) (c := c) (gul := gul) S0 V0 T0 es x)
    (hs : Path.Step lib O c gul x e y) :
    Path.FromEntry (lib := lib) (O := O) (c := c) (gul := gul) S0 V0 T0 (es ++ e) y := by
  obtain ⟨b0, hb0, h⟩ := hfe
  refine ⟨b0, hb0, ?_⟩
  have := Path.steps_trans h (Path.Steps.step hs (Path.Steps.refl y))
  simpa using this

/-- **The pass from the pending mode.** -/
theorem apend_pass {pick : List Nat → Nat} {nargs : Nat} {topo : List Nat} {rev : Map (List Nat)}
    {es : List (Nat × Nat)} {x x' : Path.Cfg σ Map} (hp : APend pick nargs c topo rev es x x')
    {Rp : Map (Option Noun)} (hR : evalPass x.params x.b.par x.regs = some Rp) :
    ∃ Rp' s, Path.Step lib O c' gul x' [] { x' with b := { x'.b with par := [] }, params := [], regs := Rp' } ∧
      ALive pick nargs c topo rev es { x with b := { x.b with par := [] }, params := [], regs := Rp }
        { x' with b := { x'.b with par := [] }, params := [], regs := Rp' } s := by
  obtain ⟨hne, hpar, -, f, hargs, -, hpass⟩ := hp
  obtain ⟨Rp', hR', s, hl⟩ := hpass Rp hR
  refine ⟨Rp', s, Path.Step.pass ?_ hR', hl⟩
  rcases hne with h | h
  · left; rw [hargs]; intro e; exact h (List.map_eq_nil_iff.mp e)
  · right; rw [hpar]; exact h

/-- **A step of the dead mode** runs an `%imm` op. -/
theorem adead_step {x x' y : Path.Cfg σ Map} {e : List (Nat × Nat)} (hd : ADead x x')
    (hs : Path.Step lib O c gul x e y) : e = [] ∧ y.lab = x.lab ∧ y.t = x.t ∧ y.st = x.st ∧ ADead y x' := by
  cases hs with
  | pass hne _ => exact absurd hne (by simp [hd.px, hd.qx])
  | @op p rest n R t' st' hp hq hb hpole =>
    obtain ⟨n0, d, rfl⟩ := hd.imm p (by rw [hb]; exact List.mem_cons_self)
    simp only [execPole, localPole, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hpole
    obtain ⟨-, -, rfl, rfl⟩ := hpole
    exact ⟨rfl, rfl, rfl, rfl, ⟨hd.px, hd.qx, hd.px', hd.qx',
      fun op hop => hd.imm op (by rw [hb]; exact List.mem_cons_of_mem _ hop), hd.imm', hd.bom, hd.bom'⟩⟩
  | @jump j b' _ _ _ ht _ =>
    obtain ⟨u, hu⟩ := hd.bom
    rw [hu] at ht; simp [Path.taken] at ht

/-- **The code after runs its `%imm` ops of the dead mode.** -/
theorem adead_flush : ∀ (l : List Pole) {x' : Path.Cfg σ Map}, x'.b.body = l → x'.params = [] → x'.b.par = [] →
    (∀ op ∈ l, ∃ n d, op = Pole.imm n d) →
    ∃ z', Path.Steps lib O c' gul x' [] z' ∧ z'.params = [] ∧ z'.b.par = [] ∧ z'.b.body = [] ∧
      z'.b.fin = x'.b.fin ∧ z'.t = x'.t ∧ z'.st = x'.st
  | [], x', hb, hp, hq, _ => ⟨x', Path.Steps.refl _, hp, hq, hb, rfl, rfl, rfl⟩
  | op :: l, x', hb, hp, hq, hl => by
    obtain ⟨n0, d, rfl⟩ := hl op List.mem_cons_self
    have hpole : execPole lib O gul x'.st (Pole.imm n0 d) x'.regs x'.t =
        some (Tone.zero (A 0), store d n0 x'.regs, x'.t, x'.st) := rfl
    have hs := Path.Step.op (c := c') hp hq hb hpole
    let y' : Path.Cfg σ Map := ⟨x'.lab, { x'.b with body := l }, x'.params, store d n0 x'.regs, x'.t, x'.st⟩
    obtain ⟨z', hz, h1, h2, h3, h4, h5, h6⟩ := adead_flush l (x' := y') rfl hp hq
      (fun o ho => hl o (List.mem_cons_of_mem _ ho))
    exact ⟨z', Path.Steps.step hs hz, h1, h2, h3, h4, h5, h6⟩

end

/-! ## Forward -/

section
variable {σ : Type} {lib : Lib} {O : Oracle σ} {c c' : Straight Map} {gul : Noun}
  {pick : List Nat → Nat} {nargs : Nat} {topo : List Nat} {rev : Map (List Nat)} {g : AGen Map}
  {S0 : σ} {V0 : List Noun} {T0 : Trace}

/-- **Forward**: a step of the code before is matched by at most one step of
the code after. -/
theorem alias_fwd_step (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (hD : DInvS c.blocks)
    (hT : TopoInvR c.blocks topo rev) (h : aliasWalk pick nargs c.blocks topo (aliasInit rev) = some g)
    (hc' : c'.blocks = g.new) (hE : EntryOK lib O c gul S0 V0 T0)
    {x y x' : Path.Cfg σ Map} {e : List (Nat × Nat)} (hs : Path.Step lib O c gul x e y)
    (hr : AliasI pick nargs lib O c gul topo rev S0 V0 T0 x x') :
    ∃ es' y', Path.Steps lib O c' gul x' es' y' ∧ AliasI pick nargs lib O c gul topo rev S0 V0 T0 y y' := by
  obtain ⟨es, hfe, hlab, ht, hst, hm⟩ := hr
  have hfe' := fe_step hfe hs
  rcases hm with hp | ⟨s, hl⟩ | hd
  · cases hs with
    | @pass Rp hne hR =>
      obtain ⟨Rp', s', hs', hl'⟩ := apend_pass (c' := c') (lib := lib) (O := O) (gul := gul) hp hR
      rw [List.append_nil] at hfe'
      exact ⟨_, _, Path.Steps.step hs' (Path.Steps.refl _), es, hfe', hlab, ht, hst, Or.inr (Or.inl ⟨s', hl'⟩)⟩
    | op hp' hq' _ _ => exact absurd hp.1 (by simp [hp', hq'])
    | jump hp' hq' _ _ _ => exact absurd hp.1 (by simp [hp', hq'])
  · have hq0 : x.b.par = [] := by rw [hl.bx]
    cases hs with
    | pass hne _ => exact absurd hne (by simp [hl.px, hq0])
    | @op p rest n R2 t2 s2 hp' hq' hbd hpole =>
      rw [List.append_nil] at hfe'
      by_cases hdf : ∃ r, DeadFill c.blocks r x.lab s.k
      · obtain ⟨r, hdf⟩ := hdf
        obtain ⟨-, -, hty, hsty, hd'⟩ := adead_step (c := c) (alive_dead hl hdf) (Path.Step.op (c := c) hp' hq' hbd hpole)
        exact ⟨[], x', Path.Steps.refl _, es, hfe', hlab, ht.trans hty.symm, hst.trans hsty.symm,
          Or.inr (Or.inr hd')⟩
      · have hnd : ∀ r, ¬ DeadFill c.blocks r x.lab s.k := fun r hr => hdf ⟨r, hr⟩
        obtain ⟨res, st2, s', -, hkept, hdrop⟩ := alive_op hpick hD hT hE hfe hl hbd hnd hpole
        cases res with
        | none =>
          obtain ⟨rfl, rfl, -, hl'⟩ := hdrop rfl
          exact ⟨[], x', Path.Steps.refl _, es, hfe', hlab, ht, hst, Or.inr (Or.inl ⟨s', hl'⟩)⟩
        | some op' =>
          obtain ⟨R2', hout, hx', hl'⟩ := hkept op' rfl
          have hs' := Path.Step.op (c := c') (x := x') (rest := s'.outb) hl.px' (by rw [hl.bx'])
            (by rw [hl.bx', hout]) (by rw [hst, ht]; exact hx')
          exact ⟨_, _, Path.Steps.step hs' (Path.Steps.refl _), es, hfe', hlab, rfl, rfl,
            Or.inr (Or.inl ⟨s', hl'⟩)⟩
    | @jump j bo hp' hq' hbd htk hbo =>
      obtain ⟨j', pbo, htk', hj'o, hgo, hq'', hb'', hmode⟩ := alive_jump hpick hD hT h hfe hl hbd htk hbo
      have hs' := Path.Step.jump (c := c') (lib := lib) (O := O) (gul := gul) hl.px' hq'' hb'' htk'
        (by rw [hc', hj'o]; exact hgo)
      rw [hj'o] at hs'
      refine ⟨_, _, Path.Steps.step hs' (Path.Steps.refl _), es ++ [(x.lab, j.there)], hfe', rfl, ht, hst, ?_⟩
      rcases hmode with hm | ⟨s', hm⟩
      · exact Or.inl hm
      · exact Or.inr (Or.inl ⟨s', hm⟩)
  · obtain ⟨rfl, hly, hty, hsty, hd'⟩ := adead_step hd hs
    exact ⟨[], x', Path.Steps.refl _, es ++ [], hfe', hlab.trans hly.symm, ht.trans hty.symm, hst.trans hsty.symm,
      Or.inr (Or.inr hd')⟩

/-- An end of the dead mode is an end of the code after. -/
theorem adead_end {x x' : Path.Cfg σ Map} (hd : ADead x x') (ht : x'.t = x.t) (hst : x'.st = x.st)
    {r : Tone × σ} (he : Path.endOf lib O gul x = some r) :
    ∃ es' z', Path.Steps lib O c' gul x' es' z' ∧ Path.endOf lib O gul z' = some r := by
  cases hbd : x.b.body with
  | cons p rest =>
    obtain ⟨n0, d, rfl⟩ := hd.imm p (by rw [hbd]; exact List.mem_cons_self)
    rw [endOf_op hd.px hd.qx hbd] at he
    cases he
  | nil =>
    obtain ⟨u, hu⟩ := hd.bom
    rw [afn_endOf hd.px hd.qx hbd, hu] at he
    simp only [endR, Option.some.injEq] at he
    subst he
    obtain ⟨z', hz, h1, h2, h3, h4, h5, h6⟩ := adead_flush (lib := lib) (O := O) (gul := gul) (c' := c') _ rfl
      hd.px' hd.qx' hd.imm'
    obtain ⟨u', hu'⟩ := hd.bom'
    refine ⟨[], z', hz, ?_⟩
    rw [afn_endOf h1 h2 h3, h4, hu', h5, h6, ht, hst]
    rfl

/-- **Forward, at an end**: an end of the code before is an end of the code
after, possibly after the `%imm` ops of the dead mode. -/
theorem alias_fwd_end (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (hD : DInvS c.blocks)
    (hT : TopoInvR c.blocks topo rev) (hE : EntryOK lib O c gul S0 V0 T0)
    {x x' : Path.Cfg σ Map} (hr : AliasI pick nargs lib O c gul topo rev S0 V0 T0 x x')
    {r : Tone × σ} (he : Path.endOf lib O gul x = some r) :
    ∃ es' z', Path.Steps lib O c' gul x' es' z' ∧ Path.endOf lib O gul z' = some r := by
  obtain ⟨es, hfe, hlab, ht, hst, hm⟩ := hr
  rcases hm with hp | ⟨s, hl⟩ | hd
  · unfold Path.endOf at he
    rw [if_pos hp.1] at he
    cases he
  · have hq0 : x.b.par = [] := by rw [hl.bx]
    have hq0' : x'.b.par = [] := by rw [hl.bx']
    cases hbd : x.b.body with
    | cons p rest =>
      by_cases hdf : ∃ r, DeadFill c.blocks r x.lab s.k
      · obtain ⟨r0, hdf⟩ := hdf
        exact adead_end (alive_dead hl hdf) ht hst he
      · obtain ⟨res, st2, outb2, h1, hout, -, hx⟩ := alive_next hpick hD hT hfe hl hbd
        rw [endOf_op hl.px hq0 hbd] at he
        cases res with
        | none =>
          obtain ⟨R2, hR2⟩ := alive_drop_exec hpick hD hT hE hfe hl hbd h1
          rw [hR2] at he
          cases he
        | some op' =>
          refine ⟨[], x', Path.Steps.refl _, ?_⟩
          have hb' : x'.b.body = op' :: outb2 := by rw [hl.bx', hout]; rfl
          rw [endOf_op hl.px' hq0' hb', hst, ht, endPole_xrel (hx op' rfl)]
          exact he
    | nil =>
      obtain ⟨-, hout, hst', hf, hfr, hrr⟩ := alive_end hpick hD hT hfe hl hbd
      have hb' : x'.b.body = [] := by rw [hl.bx', hout]
      refine ⟨[], x', Path.Steps.refl _, ?_⟩
      have hfin : x.b.fin = s.b.fin := by rw [hl.bx]
      have hfin' : x'.b.fin = s.rf.1 := by rw [hl.bx']
      rw [afn_endOf hl.px hq0 hbd, hfin] at he
      have hrf := hl.ok.fin
      rw [hst'] at hrf
      rw [afn_endOf hl.px' hq0' hb', hfin', hst, ht, endR_congr hrr,
        afn_end O gul x.st x.t hrf hf (fun y hy => (hfr y hy).1) (hD.2.2 _ s.b hl.ok.hb) (fun s0 z o' e => ?_)]
      · exact he
      · rw [e] at he
        simp only [endR] at he
        obtain ⟨v, hv, -⟩ := Option.bind_eq_some_iff.mp he
        rw [hv]; rfl
  · exact adead_end hd ht hst he

/-- **Forward, on paths.** -/
theorem alias_fwd (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (hD : DInvS c.blocks)
    (hT : TopoInvR c.blocks topo rev) (h : aliasWalk pick nargs c.blocks topo (aliasInit rev) = some g)
    (hc' : c'.blocks = g.new) (hE : EntryOK lib O c gul S0 V0 T0)
    {x z : Path.Cfg σ Map} {es : List (Nat × Nat)} (hs : Path.Steps lib O c gul x es z) {r : Tone × σ}
    (he : Path.endOf lib O gul z = some r) : ∀ {x' : Path.Cfg σ Map},
      AliasI pick nargs lib O c gul topo rev S0 V0 T0 x x' →
      ∃ es' z', Path.Steps lib O c' gul x' es' z' ∧ Path.endOf lib O gul z' = some r := by
  induction hs with
  | refl => intro x' hr; exact alias_fwd_end hpick hD hT hE hr he
  | step s _ ih =>
    intro x' hr
    obtain ⟨es1, y', hs1, hr1⟩ := alias_fwd_step hpick hD hT h hc' hE s hr
    obtain ⟨es2, z', hs2, he'⟩ := ih he hr1
    exact ⟨_, z', Path.steps_trans hs1 hs2, he'⟩

end

end Opt
end SkaModel
end Formalization
