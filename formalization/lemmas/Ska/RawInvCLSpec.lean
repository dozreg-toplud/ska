import lemmas.Ska.RawInvWholeX
import lemmas.Ska.RawInvCAT
import lemmas.Ska.CompSevenG

/-!
# The liveness spec of a run with indirect calls

README Gaps 14 (b), track D.  The statement checked in `RawInvCLCheck.lean`
(candidate 1) as a proposition, and the first parts of its run-level
induction on `runLC`.

* `unpM g`: the blocks of `g` with every register read through `unproxy
  g.cond` (a read of a proxy is a read of the register it stands for).
* `GLiveKL bl K goal r`: what a run for the lazy goal `goal` may leave live
  at its entry: for `%next laz th`, live at `th.there` with the kills `K`
  and those of the goal's own lazy tree (`lazK th.there laz`: every entry,
  the root included, first defines its sure need); for `%pick`, live at a
  target; for `%done`, nothing.
* `LiveC K goal g0 g1 nex`: every register live at the result's entry in
  `unpM g1`, with the kills `K` and those of the result's lazy tree, is
  `GLiveKL (unpM g0) K goal`.

Proved here: `LiveC` composes along a goal chain (`LiveC.trans`, the shape
of `%7`: `liveRun_seven` for any pre- and postcondition that chain), the
pure arms (`liveC_refl`, `liveC_fromL`: `%0` under `%next`; `liveC_pick_z`,
`liveC_pick_o`: `%1` under `%pick`), `+simple-next` under `%done`
(`liveC_simpleNextL_done`: the `%don` block of a fresh register that is no
proxy), the top
(`liveC_done`: nothing is live at the entry under `%done`), and the two
facts every arm that walks the goal's lazy need uses: ops put in front of
blocks (`liveK_prepK`: a register live after them is live before them with
the kills they meet, or read first by them) and that `unpM` carries such
ops (`liveK_old`: a path from the new code into the old one; `prep_mapVals`,
`unpM_prep`: through `renBlob_congr` of track C for a
`cond` that grew by fresh proxies), and the step over a fresh hop block to
the goal (`liveK_hop_root`: the root's kills move from the hop block to the
goal's continuation; `LiveK.mono_r`: kills matter only for the register
tracked), the shape of `+mede`'s hop and of `+kerf`'s.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The statement -/

/-- **The blocks with every proxy read as its definition.** -/
def unpM (g : Comp.Gen Map) : Map Blob := mapVals (renBlob (unproxy g.cond)) g.blocks

/-- **What a run for a lazy goal may leave live at its entry**, with the
kills `K`: at the continuation of `%next laz th` once every entry of the
goal's lazy tree (the root `th.there` with `laz.sure` included) first
defines its sure need; at either target of `%pick`; nothing under `%done`. -/
def GLiveKL (bl : Map Blob) (K : Nat → Nat → Prop) : CGoalL S → Nat → Prop
  | CGoalL.next laz th, r => LiveK bl (fun x y => K x y ∨ lazK th.there laz x y) th.there r
  | CGoalL.pick z o, r => LiveK bl K z.there r ∨ LiveK bl K o.there r
  | CGoalL.done, _ => False

/-- **The liveness spec of a run with indirect calls** (checked by `live1K`
of `RawInvCLCheck.lean` on `enumCX` under `%done`, `%next`, `%pick` and a
goal with a bond): a register live at the result's entry, in the blocks
after the run read modulo `unproxy`, each entry of the result's lazy tree
first defining its sure need, is one the goal may leave live, in the blocks
before the run read modulo `unproxy`. -/
def LiveC (K : Nat → Nat → Prop) (goal : CGoalL S) (g0 g1 : Comp.Gen Map) (nex : NextL S) : Prop :=
  ∀ r, LiveK (unpM g1) (fun x y => K x y ∨ lazK nex.th.there nex.laz x y) nex.th.there r →
    GLiveKL (unpM g0) K goal r

/-- **At the top nothing is live**: under `%done` the spec leaves no register
live at the entry of the unproxied blocks, the lazy entries first defining
their needs (the hypothesis `hl` of the final passes, modulo `unproxy`). -/
theorem liveC_done {K : Nat → Nat → Prop} {g0 g1 : Comp.Gen Map} {nex : NextL S}
    (h : LiveC K CGoalL.done g0 g1 nex) (r : Nat) :
    ¬ LiveK (unpM g1) (fun x y => K x y ∨ lazK nex.th.there nex.laz x y) nex.th.there r :=
  fun hl => h r hl

/-! ## Composition -/

/-- **A run for the goal of another run's result composes**: the second
run's spec ends where the first one's begins. -/
theorem LiveC.trans {K : Nat → Nat → Prop} {goal : CGoalL S} {g0 g1 g2 : Comp.Gen Map} {nex1 nex2 : NextL S}
    (h1 : LiveC K goal g0 g1 nex1) (h2 : LiveC K nex1.goal g1 g2 nex2) : LiveC K goal g0 g2 nex2 :=
  fun r h => h1 r (h2 r h)

/-- Fewer outer kills before, fewer after. -/
theorem LiveC.monoK {K K' : Nat → Nat → Prop} {goal : CGoalL S} {g0 g1 : Comp.Gen Map} {nex : NextL S}
    (h : LiveC K goal g0 g1 nex) (hK : ∀ x y, K' x y ↔ K x y) : LiveC K' goal g0 g1 nex := by
  have e : K' = K := funext fun x => funext fun y => propext (hK x y)
  subst e; exact h

/-- **The liveness half of the run-level statement for a runner `rp`**, with
the precondition `I K goal g0` on the outer kills, the goal and the state,
and the postcondition `J K nex g1`. -/
def LiveRun (I : (Nat → Nat → Prop) → CGoalL S → Comp.Gen Map → Prop)
    (J : (Nat → Nat → Prop) → NextL S → Comp.Gen Map → Prop)
    (rp : CGoalL S → List Nat → CM Map (NextL S)) : Prop :=
  ∀ (K : Nat → Nat → Prop) (goal : CGoalL S) (region : List Nat) (g0 g1 : Comp.Gen Map) (nex : NextL S),
    I K goal g0 → rp goal region g0 = some (nex, g1) → J K nex g1 ∧ LiveC K goal g0 g1 nex

/-- **The case `%7`**: `q` for the goal, then `p` for `q`'s result, for any
pre- and postcondition such that the postcondition of a run gives the
precondition of a run for its result. -/
theorem liveRun_seven (env : CallEnv) (sup : Option Nomm) {p q : Nomm}
    {I : (Nat → Nat → Prop) → CGoalL S → Comp.Gen Map → Prop}
    {J : (Nat → Nat → Prop) → NextL S → Comp.Gen Map → Prop}
    (hq : LiveRun (Map := Map) I J (runLC (S := S) env (some p) q))
    (hp : LiveRun (Map := Map) I J (runLC (S := S) env sup p))
    (hJ : ∀ K nex g, J K nex g → I K nex.goal g) :
    LiveRun (Map := Map) I J (runLC (S := S) env sup (Nomm.n7 p q)) := by
  intro K goal region g0 g1 nex hI hr
  rw [runLC_n7] at hr
  obtain ⟨nexq, gq, hrq, hrp⟩ := bind_some hr
  obtain ⟨Jq, Lq⟩ := hq K goal region g0 gq nexq hI hrq
  obtain ⟨Jp, Lp⟩ := hp K nexq.goal region gq g1 nex (hJ K nexq gq Jq) hrp
  exact ⟨Jp, Lq.trans Lp⟩

/-! ## The pure arms -/

/-- A run that hands the goal up as its result. -/
theorem liveC_refl {K : Nat → Nat → Prop} {laz : Lazy S} {th : Jmp} {g : Comp.Gen Map} :
    LiveC K (CGoalL.next laz th) g g ⟨laz, th⟩ :=
  fun _ hl => hl

/-- **`%0` under `%next`**: `+from` emits nothing and keeps the kills. -/
theorem liveC_fromL {K : Nat → Nat → Prop} {laz laz' : Lazy S} {th : Jmp} {axe : Nat} {g : Comp.Gen Map}
    (h : fromL axe laz = some laz') : LiveC K (CGoalL.next laz th) g g ⟨laz', th⟩ :=
  fun _ hl => hl.mono fun _ _ hk => hk.elim Or.inl fun h' => Or.inr (lazK_fromL h h')

/-- **`%1` under `%pick`** (and every run that hands a target of `%pick` up
with no block made): the result's kills are only more. -/
theorem liveC_pick_z {K : Nat → Nat → Prop} {z o : Jmp} {laz : Lazy S} {g : Comp.Gen Map} :
    LiveC K (CGoalL.pick z o) g g ⟨laz, z⟩ :=
  fun _ hl => Or.inl (hl.mono fun _ _ hk => Or.inl hk)

theorem liveC_pick_o {K : Nat → Nat → Prop} {z o : Jmp} {laz : Lazy S} {g : Comp.Gen Map} :
    LiveC K (CGoalL.pick z o) g g ⟨laz, o⟩ :=
  fun _ hl => Or.inr (hl.mono fun _ _ hk => Or.inl hk)

/-- **`+simple-next` under `%done`**: the `%don` block reads only the fresh
register its result's need names, when that register is no proxy. -/
theorem liveC_simpleNextL_done {K : Nat → Nat → Prop} {g0 g1 : Comp.Gen Map} {nex : NextL S}
    (hd : g0.drop = false) (hc : HoonMap.get g0.cond g0.re = Option.none)
    (h : (simpleNextL (CGoalL.done : CGoalL S) : CM Map (NextL S)) g0 = some (nex, g1)) :
    LiveC K CGoalL.done g0 g1 nex := by
  simp only [simpleNextL] at h
  obtain ⟨r, ga, ha, h⟩ := bind_some h
  rw [re_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨o, gb, hb, h⟩ := bind_some h
  rw [emit_apply] at hb
  simp only [Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  intro y hl
  have hu : unproxy g0.cond g0.re = g0.re := unproxy_none hc
  have hget : ∀ k, k = g0.bo → HoonMap.get (unpM (({ g0 with re := g0.re + 1 } : Comp.Gen Map).emitted
      ⟨[], [], Termin.don g0.re⟩)) k = some ⟨[], [], Termin.don g0.re⟩ := by
    intro k ek
    subst ek
    unfold unpM
    rw [get_mapVals]
    simp only [Gen.emitted, hd, Bool.false_eq_true, if_false]
    rw [get_put_self]
    simp [renBlob, renFin, hu]
  cases hl with
  | here hb' hr hk =>
    have hb2 := (hget _ rfl).symm.trans hb'
    cases hb2
    obtain ⟨-, hr⟩ := hr
    rcases hr with hr | ⟨-, hr⟩
    · exact absurd hr (by simp [OpsRF])
    · simp only [finRegs, List.mem_singleton] at hr
      subst hr
      exact hk (Or.inr (lazK_ofSure.mpr ⟨rfl, rfl⟩))
  | next hb' hj _ _ _ =>
    have hb2 := (hget _ rfl).symm.trans hb'
    cases hb2
    simp [getJmps] at hj

/-! ## Ops in front of blocks -/

/-- **A register live after ops are put in front of blocks is live before
them with the kills they meet, or read first by them**, when the ops at
each label define the kills `K'` there. -/
theorem liveK_prepK {P : Nat → List Pole} {bl bl' : Map Blob} (hP : Prep P bl bl') {K K' : Nat → Nat → Prop}
    (hK : ∀ k r, K' k r → r ∈ defsOf (P k)) {k r : Nat} (h : LiveK bl' K k r) :
    LiveK bl (fun x y => K x y ∨ K' x y) k r ∨ ∃ k', OpsRF (P k') r := by
  induction h with
  | here hb hr hk =>
    rw [hP] at hb
    obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp hb
    rcases blockRF_pre hr with h | ⟨hd, h⟩
    · exact Or.inr ⟨_, h⟩
    · exact Or.inl (LiveK.here h0 h fun hk' => hk'.elim hk fun h' => hd (hK _ _ h'))
  | next hb hj _ hd hk ih =>
    rw [hP] at hb
    obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp hb
    rcases ih with ih | ih
    · exact Or.inl (LiveK.next h0 hj ih (fun hm => hd (mem_blockDefs_pre.mpr (Or.inl hm)))
        fun hk' => hk'.elim hk fun h' => hd (mem_blockDefs_pre.mpr (Or.inr (hK _ _ h'))))
    · exact Or.inr ih

/-- **Renaming carries ops in front of blocks**: the renamed blocks are the
renamed old ones with the renamed ops in front. -/
theorem prep_mapVals {P : Nat → List Pole} {bl bl' : Map Blob} (hP : Prep P bl bl') (u : Nat → Nat) :
    Prep (fun k => (P k).map (renPole u)) (mapVals (renBlob u) bl) (mapVals (renBlob u) bl') := by
  intro k
  rw [get_mapVals, get_mapVals, hP k]
  cases HoonMap.get bl k <;> simp [renBlob_pre]

/-- **`unproxy` of a grown `cond` on old registers**: when `cond'` agrees with
`cond` below `R`, a block that mentions only registers below `R` reads the
same after either. -/
theorem renBlob_unproxy_grow {cond cond' : Map (Nat × List Nat)} {R : Nat}
    (hc : ∀ x, x < R → HoonMap.get cond' x = HoonMap.get cond x) {b : Blob} (hb : BlobIn (· < R) b) :
    renBlob (unproxy cond') b = renBlob (unproxy cond) b :=
  renBlob_congr (P := (· < R)) (fun x hx => by simp only [unproxy, hc x hx]) hb

/-- **The unproxied blocks after ops in front of old blocks**: if the blocks
of `g'` are those of `g` with the ops `P` in front, and `cond` only grew
above every register the blocks of `g'` mention, then the unproxied blocks
of `g'` are those of `g` with the unproxied ops in front. -/
theorem unpM_prep {P : Nat → List Pole} {g g' : Comp.Gen Map} (hP : Prep P g.blocks g'.blocks) {R : Nat}
    (hc : ∀ x, x < R → HoonMap.get g'.cond x = HoonMap.get g.cond x)
    (hR : ∀ k b, HoonMap.get g'.blocks k = some b → BlobIn (· < R) b) :
    Prep (fun k => (P k).map (renPole (unproxy g.cond))) (unpM g) (unpM g') := by
  intro k
  unfold unpM
  rw [get_mapVals, get_mapVals, hP k]
  cases hb : HoonMap.get g.blocks k with
  | none => rfl
  | some b =>
    simp only [Option.map_some]
    rw [renBlob_unproxy_grow hc (hR k _ (by rw [hP k, hb]; rfl)), renBlob_pre]

/-- **A path into the old code after a run**: when the blocks below `L` are
the old ones with the ops `P` in front (each defining the kills `K'` at its
label), and the old blocks jump down below `L`, a register live at an old
label is live there before the ops with the kills they meet, or read first
by them.  The step of every arm whose code hops into its goal's
continuation, with `unpM_prep` for the unproxied blocks. -/
theorem liveK_old {P : Nat → List Pole} {bl0 blP bl1 : Map Blob} {L : Nat} (hP : Prep P bl0 blP)
    (hd : DownBelowP bl0 L) (he : ∀ x, x < L → HoonMap.get bl1 x = HoonMap.get blP x)
    {K K' : Nat → Nat → Prop} (hK : ∀ k r, K' k r → r ∈ defsOf (P k)) {k r : Nat} (hk : k < L)
    (h : LiveK bl1 K k r) : LiveK bl0 (fun x y => K x y ∨ K' x y) k r ∨ ∃ k', OpsRF (P k') r := by
  obtain ⟨ρ, hj, h1, h2⟩ := hd
  have hdP : DownBelowP blP L := ⟨ρ, jdownR_prep hP hj, h1, h2⟩
  exact liveK_prepK hP hK ((liveK_frameP hdP he hk).mp h)

/-! ## A fresh hop to the goal -/

/-- **Kills matter only at the register tracked**: a path for `r` keeps
going when the new kills are among the old ones for `r`. -/
theorem LiveK.mono_r {bl : Map Blob} {K K' : Nat → Nat → Prop} {k r : Nat} (h : LiveK bl K k r)
    (hK : ∀ x, K' x r → K x r) : LiveK bl K' k r := by
  induction h with
  | here hb hr hk => exact LiveK.here hb hr fun h' => hk (hK _ h')
  | next hb hj _ hd hk ih => exact LiveK.next hb hj (ih hK) hd fun h' => hk (hK _ h')

/-- **The root's kills move along a fresh hop to the goal**: a register live
at a hop block `o` to `th`, with the kills of a lazy tree rooted at `o`, is
live at `th.there` with the kills of the same tree rooted there, when no
outer kill and no entry of the tree is at `o` and `th.there ≠ o`.  The
shape of `+mede`'s hop and of `+kerf`'s hop block, before their ops are put
in front (`liveK_prepK`). -/
theorem liveK_hop_root {bl : Map Blob} {K : Nat → Nat → Prop} {o : Nat} {laz : Lazy S} {th : Jmp} {r : Nat}
    (hb : HoonMap.get bl o = some ⟨[], [], Termin.hop th⟩) (hth : th.args = [])
    (hK : ∀ y, ¬ K o y) (hent : ∀ e ∈ entries laz, e.1 ≠ o) (hne : th.there ≠ o)
    (h : LiveK bl (fun x y => K x y ∨ lazK o laz x y) o r) :
    LiveK bl (fun x y => K x y ∨ lazK th.there laz x y) th.there r := by
  have hroot : ¬ NMem laz.sure.ned r := fun hm => h.nk (Or.inr ⟨(o, laz), List.mem_cons_self, rfl, hm⟩)
  cases h with
  | here hb' hr _ =>
    rw [hb] at hb'; cases hb'
    obtain ⟨-, hr⟩ := hr
    rcases hr with hr | ⟨-, hr⟩
    · exact absurd hr (by simp [OpsRF])
    · simp [finRegs, jmpRegs, hth] at hr
  | next hb' hj hl _ _ =>
    rw [hb] at hb'; cases hb'
    rw [getJmps_hop, List.mem_singleton] at hj
    subst hj
    refine hl.mono_r fun x hx => hx.elim Or.inl fun ⟨e, he, ex, hm⟩ => ?_
    rcases List.mem_cons.mp he with rfl | he'
    · exact absurd hm hroot
    · exact Or.inr ⟨e, List.mem_cons_of_mem _ he', ex, hm⟩

end Raw
end SkaModel
end Formalization
