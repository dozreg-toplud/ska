import lemmas.Ska.CompNestPick
import lemmas.Ska.CompStraightMap
import lemmas.Ska.CompStraight

/-!
# Proxies: the unproxied blocks, the growth of `cond`, `AgreeU`

`+to-straight` reads each proxy register of `cond` as its definition
(`unproxy`, `toStraightF_run`): on a run of inputs it renames by
`ren ∘ unproxy cond`.  So the program a run that makes proxies is compared
with is the Gen blocks with every register unproxied (`unproxyBlob`), and a
proxy itself is never written there.

* `renFin`, `renBlob`: a terminator and a block renamed without chasing.
  `unproxyBlob cond = renBlob (unproxy cond)`; with no proxy it is the
  identity (`unproxyBlob_empty`).
* `CondFresh g0 g1`: `cond` grew only by fresh entries `k ↦ (d, tag)` with
  `g0.re ≤ k < g1.re` that were absent before.  `+proxy` meets it
  (`proxy_condFresh`), and so does every step that keeps `cond`
  (`condFresh_of_eq`); it composes (`CondFresh.trans`).  Below `g0.re` the
  unproxying does not change (`unproxy_condFresh`).
* `AgreeU`: `AgreeP` with the blocks outside the lazy blocks compared after
  `unproxyBlob` of a given `cond` (the final one).  With an empty `cond` it is
  `AgreeP` (`agreeU_empty`), so the runs without proxies keep their relation.
* `chase_ren`: `+chase` on the unproxied blocks is `+chase` on the Gen blocks
  followed by the renaming of the arguments, so the renaming path of
  `+to-straight` by `ren ∘ unproxy` is the renaming path by `ren` of the
  unproxied blocks, label by label (`keepBlock_ren`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-! ## Renaming without chasing -/

/-- A terminator with its registers renamed and its labels kept. -/
def renFin (u : Nat → Nat) : Termin → Termin
  | Termin.clq s z o => Termin.clq (u s) (renJmp u z) (renJmp u o)
  | Termin.eqq l r z o => Termin.eqq (u l) (u r) (renJmp u z) (renJmp u o)
  | Termin.brn s z o => Termin.brn (u s) (renJmp u z) (renJmp u o)
  | Termin.brz s z o => Termin.brz (u s) (renJmp u z) (renJmp u o)
  | Termin.hop t => Termin.hop (renJmp u t)
  | Termin.jmp a v => Termin.jmp a (v.map u)
  | Termin.jmf a v n => Termin.jmf a (v.map u) n
  | Termin.jsp a s => Termin.jsp a (u s)
  | Termin.jsf a s n => Termin.jsf a (u s) n
  | Termin.don s => Termin.don (u s)
  | Termin.bom x => Termin.bom x
  | Termin.lti n s z o => Termin.lti n (u s) (renJmp u z) (renJmp u o)

/-- A block with its registers renamed and its labels kept. -/
def renBlob (u : Nat → Nat) (b : Blob) : Blob := ⟨b.par.map u, b.body.map (renPole u), renFin u b.fin⟩

theorem renPole_id (p : Pole) : renPole id p = p := by
  cases p <;> simp [renPole]

theorem renJmp_id (j : Jmp) : renJmp id j = j := by
  rcases j with ⟨args, there⟩; simp [renJmp]

theorem renFin_id (f : Termin) : renFin id f = f := by
  cases f <;> simp [renFin, renJmp_id]

theorem renBlob_id (b : Blob) : renBlob id b = b := by
  rcases b with ⟨par, body, fin⟩
  simp only [renBlob, List.map_id, renFin_id]
  congr 1
  conv => rhs; rw [← List.map_id body]
  exact List.map_congr_left fun p _ => renPole_id p

theorem renJmp_there (u : Nat → Nat) (j : Jmp) : (renJmp u j).there = j.there := rfl

theorem renJmp_args_nil (u : Nat → Nat) (j : Jmp) : (renJmp u j).args = [] ↔ j.args = [] := by
  simp [renJmp]

theorem renJmp_comp (f u : Nat → Nat) (j : Jmp) : renJmp f (renJmp u j) = renJmp (f ∘ u) j := by
  rcases j with ⟨args, there⟩
  simp only [renJmp, List.map_map, Option.map_comp_map]

theorem renPole_comp (f u : Nat → Nat) (p : Pole) : renPole f (renPole u p) = renPole (f ∘ u) p := by
  cases p <;> simp [renPole, List.map_map]

theorem bypassable_ren (u : Nat → Nat) (br : Bool) (b : Blob) : bypassable br (renBlob u b) = bypassable br b := by
  rcases b with ⟨par, body, fin⟩
  cases par <;> cases body <;> cases fin <;> simp [bypassable, renBlob, renFin, renJmp]

/-! ## Unproxying -/

/-- **A block with every proxy register read as its definition.** -/
def unproxyBlob (cond : Map (Nat × List Nat)) (b : Blob) : Blob := renBlob (unproxy cond) b

theorem unproxy_none {cond : Map (Nat × List Nat)} {r : Nat} (h : HoonMap.get cond r = Option.none) :
    unproxy cond r = r := by
  simp [unproxy, h]

theorem unproxy_empty {cond : Map (Nat × List Nat)} (h : ∀ k, HoonMap.get cond k = Option.none) :
    unproxy cond = id :=
  funext fun r => unproxy_none (h r)

/-- **With no proxy, unproxying is the identity.** -/
theorem unproxyBlob_empty {cond : Map (Nat × List Nat)} (h : ∀ k, HoonMap.get cond k = Option.none) (b : Blob) :
    unproxyBlob cond b = b := by
  rw [unproxyBlob, unproxy_empty h, renBlob_id]

/-! ## The growth of `cond` -/

/-- **`cond` grew only by fresh proxies**: an entry that changed is at a
register allocated between the two states. -/
def CondFresh (g0 g1 : Gen Map) : Prop :=
  g0.re ≤ g1.re ∧ ∀ k, HoonMap.get g1.cond k = HoonMap.get g0.cond k ∨ (g0.re ≤ k ∧ k < g1.re)

/-- The keys of `cond` are allocated registers. -/
def CondBelow (g : Gen Map) : Prop := ∀ k, (HoonMap.get g.cond k).isSome → k < g.re

theorem CondFresh.below {g0 g1 : Gen Map} (h : CondFresh g0 g1) (hb : CondBelow g0) : CondBelow g1 := by
  intro k hk
  rcases h.2 k with e | ⟨_, l⟩
  · rw [e] at hk; exact Nat.lt_of_lt_of_le (hb k hk) h.1
  · exact l

theorem condFresh_of_eq {g0 g1 : Gen Map} (hr : g0.re ≤ g1.re) (h : g1.cond = g0.cond) : CondFresh g0 g1 :=
  ⟨hr, fun k => Or.inl (by rw [h])⟩

theorem CondFresh.refl (g : Gen Map) : CondFresh g g := condFresh_of_eq (Nat.le_refl _) rfl

theorem CondFresh.trans {g0 g1 g2 : Gen Map} (a : CondFresh g0 g1) (b : CondFresh g1 g2) : CondFresh g0 g2 := by
  refine ⟨Nat.le_trans a.1 b.1, fun k => ?_⟩
  rcases b.2 k with e2 | ⟨l2, h2⟩
  · rcases a.2 k with e1 | ⟨l1, h1⟩
    · exact Or.inl (e2.trans e1)
    · exact Or.inr ⟨l1, Nat.lt_of_lt_of_le h1 b.1⟩
  · exact Or.inr ⟨Nat.le_trans a.1 l2, h2⟩

/-- Below the registers of the run the entries of `cond` did not change. -/
theorem CondFresh.get_lt {g0 g1 : Gen Map} (h : CondFresh g0 g1) {k : Nat} (hk : k < g0.re) :
    HoonMap.get g1.cond k = HoonMap.get g0.cond k := by
  rcases h.2 k with e | ⟨l, _⟩
  · exact e
  · omega

/-- **Below `g0.re`, unproxying by the grown `cond` is unproxying by the old one.** -/
theorem unproxy_condFresh {g0 g1 : Gen Map} (h : CondFresh g0 g1) {r : Nat} (hr : r < g0.re) :
    unproxy g1.cond r = unproxy g0.cond r := by
  simp only [unproxy, h.get_lt hr]

/-- **`+proxy` makes one fresh entry**: the new register `p = g.re`, read as
`r` once unproxied (when the run does not drop). -/
theorem proxy_condFresh {r o p : Nat} {g g' : Gen Map} (h : proxy r o g = some (p, g')) :
    p = g.re ∧ g'.re = g.re + 1 ∧ g'.blocks = g.blocks ∧ g'.drop = g.drop ∧ CondFresh g g' ∧
      (g.drop = false → ∃ tag, HoonMap.get g'.cond p = some (r, tag) ∧ unproxy g'.cond p = r) := by
  unfold proxy at h
  simp only at h
  by_cases hd : g.drop = true
  · rw [if_pos hd] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, rfl, condFresh_of_eq (by simp) rfl, fun h => by simp [hd] at h⟩
  · rw [if_neg hd] at h
    obtain ⟨tag, _, ht⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at ht
    obtain ⟨rfl, rfl⟩ := ht
    refine ⟨rfl, rfl, rfl, rfl, ⟨by simp, fun k => ?_⟩, fun _ => ⟨tag, by simp [HoonMap.get_put], ?_⟩⟩
    · by_cases e : k = g.re
      · subst e; exact Or.inr ⟨Nat.le_refl _, by simp⟩
      · left; simp [HoonMap.get_put, e]
    · simp [unproxy, HoonMap.get_put]

/-! ## `AgreeU`: `AgreeP` against the unproxied blocks -/

/-- **`AgreeP` with the blocks compared after unproxying by `cond`** (the
final `cond` of the compilation): outside the lazy blocks the program holds
the Gen blocks unproxied, and at each lazy block ops `A` that fill its need
in front of its hop, unproxied. -/
def AgreeU (lib : Lib) {σ : Type} (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
    (cond : Map (Nat × List Nat)) (ned : Need) (g0 g1 : Gen Map) (laz : Lazy S) (s0 s : Noun) : Prop :=
  (∀ o, g0.bo ≤ o → o < g1.bo → o ∉ (entries laz).map Prod.fst →
    HoonMap.get c.blocks o = (HoonMap.get g1.blocks o).map (unproxyBlob cond)) ∧
  ∀ e ∈ entries laz, ∃ A th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩ ∧
    HoonMap.get c.blocks e.1 = some ⟨[], A, Termin.hop (renJmp (unproxy cond) th)⟩ ∧
    FillSem lib O c gul st t ned g1.re e.2.sure A s0 s

/-- **With no proxy, `AgreeU` is `AgreeP`**, so the relations of the runs
that make no proxy are the case of an empty `cond`. -/
theorem agreeU_empty {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
    {cond : Map (Nat × List Nat)} (hc : ∀ k, HoonMap.get cond k = Option.none) {ned : Need} {g0 g1 : Gen Map}
    {laz : Lazy S} {s0 s : Noun} :
    AgreeU lib O c gul st t cond ned g0 g1 laz s0 s ↔ AgreeP lib O c gul st t ned g0 g1 laz s0 s := by
  have hu : (unproxyBlob cond) = id := funext fun b => unproxyBlob_empty hc b
  have hj : ∀ th, renJmp (unproxy cond) th = th := fun th => by rw [unproxy_empty hc, renJmp_id]
  simp only [AgreeU, AgreeP, hu, hj, Option.map_id, id_eq]

/-! ## `+chase` and the renaming path on the unproxied blocks -/

section Chase
variable {ρ : Nat → Nat} {bs bs' : Map Blob} {u : Nat → Nat}

/-- **`+chase` on the renamed blocks is `+chase` followed by the renaming.** -/
theorem chase_ren (hd : DownRk ρ bs) (hb : ∀ k, HoonMap.get bs' k = (HoonMap.get bs k).map (renBlob u)) :
    ∀ n (j : Jmp) (br : Bool), ρ j.there < n → chase bs' br (renJmp u j) = (chase bs br j).map (renJmp u)
  | 0, _, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, j, br, hn => by
    rw [chase.eq_1 bs' br, chase.eq_1 bs br, renJmp_there, hb]
    cases hbj : HoonMap.get bs j.there with
    | none => rfl
    | some b =>
      simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
      rcases b with ⟨par, body, fin⟩
      cases fin with
      | hop t =>
        have hby := bypassable_ren u br ⟨par, body, Termin.hop t⟩
        simp only [renBlob, renFin] at hby ⊢
        simp only [hby]
        by_cases hy : bypassable br ⟨par, body, Termin.hop t⟩ = true
        · simp only [hy, if_true]
          by_cases ha : j.args = []
          · have ha' := (renJmp_args_nil u j).mpr ha
            simp only [ha, ha', if_true]
            have := (hd _ _ hbj).2 t (by simp [finJumps])
            exact chase_ren hd hb n t br (by omega)
          · have ha' : ¬ (renJmp u j).args = [] := fun e => ha ((renJmp_args_nil u j).mp e)
            simp only [ha, ha', if_false]; rfl
        · simp only [hy, Bool.false_eq_true, if_false]; rfl
      | _ => rfl

theorem chaseFin_ren (hd : DownRk ρ bs) (hb : ∀ k, HoonMap.get bs' k = (HoonMap.get bs k).map (renBlob u))
    (f : Nat → Nat) (fin : Termin) : chaseFin bs' f (renFin u fin) = chaseFin bs (f ∘ u) fin := by
  have cr : ∀ (j : Jmp) br, chase bs' br (renJmp u j) = (chase bs br j).map (renJmp u) :=
    fun j br => chase_ren hd hb (ρ j.there + 1) j br (Nat.lt_succ_self _)
  cases fin with
  | clq s z o | eqq _ s z o | brn s z o | brz s z o =>
    simp only [chaseFin, renFin, cr]
    cases chase bs true z <;> cases chase bs true o <;> simp [renJmp_comp]
  | hop t =>
    simp only [chaseFin, renFin, cr]
    cases chase bs false t <;> simp [renJmp_comp]
  | bom x =>
    cases x with
    | none => rfl
    | some x =>
      have := cr ⟨[], x⟩ true
      simp only [renJmp, List.map_nil] at this
      simp only [chaseFin, renFin, this]
      cases chase bs true ⟨[], x⟩ <;> simp [renJmp]
  | lti _ _ _ _ => rfl
  | _ => simp [chaseFin, renFin, List.map_map]

/-- **One block of the renaming path by `f ∘ u` is the block of the renaming
path by `f` on the renamed blocks.** -/
theorem keepBlock_ren (hd : DownRk ρ bs) (hb : ∀ k, HoonMap.get bs' k = (HoonMap.get bs k).map (renBlob u))
    (f : Nat → Nat) (k : Nat) (b : Blob) : keepBlock bs' f k (renBlob u b) = keepBlock bs (f ∘ u) k b := by
  unfold keepBlock
  rw [bypassable_ren]
  split
  · rfl
  · rw [show (renBlob u b).fin = renFin u b.fin from rfl, chaseFin_ren hd hb]
    cases chaseFin bs (f ∘ u) b.fin with
    | none => rfl
    | some fin => simp [renBlob, List.map_map, renPole_comp, Function.comp_def]

end Chase

end Comp
end SkaModel
end Formalization
