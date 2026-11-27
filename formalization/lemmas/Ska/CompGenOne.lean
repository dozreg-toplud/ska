import lemmas.Ska.CompGenLeaf
import lemmas.Ska.CompOneLS

/-!
# `[1 k]` in `RunOKGen`, at any lazy goal

README Gaps 12.39, item 10.  `+mede` (`medeL`) emits the block `[hop th]`
and walks the goal's lazy need with `medeGate k`, which puts in front of the
block at every entry's label the ops writing `k` into that entry's need (or
crashing where `k` has not its shape).  Stated per label (`medeWalk_okL`,
the `WalkOKL` pattern of `CompGenTop.lean`): at a label the ops are one
piece per goal entry there, up to a permutation, so forks, bonds and
repeated labels need no disjointness premise; the pieces at a label fill the
conjunction `suresAt L a` by `fillSemL_list`, the needs at one label being
apart (`LabDisj` of the goal).  The result asks nothing, has no entry, and
its jump is the new block.

* `medeGate_okDI`, `medeWalk_okL`: the walk of `+mede` per label.
* `medePiece_fill`: one piece as a `FillSem` from any input need above the
  walk's registers; `FillSemL.preOne`: an earlier part's fill of `[]` in
  front.
* **`runOKGen_n1`**: `RunOKGen` of `[1 k]` at any `GoalG` goal whose
  registers are no keys of `cond` and whose jump has no arguments, with
  `GrowU` and no re-pointing.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The walk of `+mede` per label -/

/-- The gate of `+mede` in the form `walkLazy_okL` takes (`cond` kept, no
invariant, the property not reading `cond`). -/
theorem medeGate_okDI (som : Noun) :
    GateOKDI (fun g g' : Gen Map => g'.cond = g.cond) (fun _ => True)
      (fun _ lo hi o s A => MedePR (S := S) (Map := Map) som lo hi o s A) (medeGate (S := S) (Map := Map) som) := by
  intro o l g g' h hd _
  have W := medeGateR_ok som o l g g' h hd
  exact ⟨W.bo, W.drop, W.le, W.cnd, W.other, fun e he => W.at_ e he⟩

/-- **The walk of `+mede` per label**: at every label one piece per entry
there, each writing `som` into its need. -/
theorem medeWalk_okL (som : Noun) {o : Nat} {L : Lazy S} {g g' : Gen Map}
    (h : walkLazy (medeGate som) o L g = some ((), g')) (hd : g.drop = false) :
    WalkOKL (fun g g' : Gen Map => g'.cond = g.cond)
      (fun _ lo hi o s A => MedePR (S := S) (Map := Map) som lo hi o s A) g g' ((o, L) :: entries L) :=
  walkLazy_okL (C := fun g g' : Gen Map => g'.cond = g.cond) (fun g => rfl) (fun a b c h1 h2 => h2.trans h1)
    (fun a b h k _ => by rw [h])
    (I := fun _ => True) (fun _ _ _ _ => trivial)
    (fun c c' lo hi lo' hi' o s A hP _ h1 h2 => medePR_mono som lo hi lo' hi' o s A hP h1 h2)
    (medeGate_okDI som) o L g g' h hd trivial

theorem atL_cons_of_neOne {o a : Nat} {l : Lazy S} {es : List (Nat × Lazy S)} (h : o ≠ a) :
    atL ((o, l) :: es) a = atL es a := by
  simp [atL, List.filter_cons, h]

theorem atL_cons_of_eqOne (o : Nat) (l : Lazy S) (es : List (Nat × Lazy S)) :
    atL ((o, l) :: es) o = l.sure :: atL es o := by
  simp [atL, List.filter_cons]

theorem regsIn_flattenOne {P : Nat → Prop} : ∀ (As : List (Sure S × List Pole)), (∀ p ∈ As, RegsIn P p.2) →
    RegsIn P (As.map Prod.snd).flatten
  | [], _ => RegsIn.nil P
  | p :: As, h => by
    simp only [List.map_cons, List.flatten_cons]
    exact (h p List.mem_cons_self).append (regsIn_flattenOne As fun q hq => h q (List.mem_cons_of_mem _ hq))

/-! ## The fills -/

section Fill
variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}

/-- **One piece of `+mede` as a fill**: from any input need above the
walk's registers, the constant `k` into the piece's need. -/
theorem medePiece_fill {N : Need} {lo hi o : Nat} {sur : Sure S} {A : List Pole} {k x : Noun}
    (hP : MedeP (Map := Map) k lo hi o sur A) (hd : Distinct sur.ned) (hr : ∀ r, NMem sur.ned r → r < lo)
    (hN : ∀ y, NMem N y → hi ≤ y) :
    FillSem lib O c gul st t N lo sur A x k := by
  intro R _
  obtain ⟨S1, S2⟩ := hP lib σ O c gul st t R hd hr
  refine ⟨fun f => ?_, S2⟩
  obtain ⟨R', r, hh, kp⟩ := S1 f
  refine ⟨R', r, hh, fun y hy hn => kp y hn (fun ⟨a, b⟩ => ?_)⟩
  rcases hy with hy | hy
  · have := hN y hy; omega
  · omega

/-- **An earlier part's fill of nothing in front of a fill.** -/
theorem FillSemL.preOne {N ned : Need} {lo lo' : Nat} {Ls : List (Sure S)} {A F : List Pole} {x v s0 s : Noun}
    (hA : FillSemL (S := S) (Map := Map) lib O c gul st t ned lo' [] A s0 s)
    (hF : FillSemL lib O c gul st t N lo Ls F x v)
    (hN : ∀ R : Map (Option Noun), HoldsN N R x → HoldsN ned R s0)
    (hk : ∀ y, NMem N y ∨ y < lo → NMem ned y ∨ y < lo') :
    FillSemL lib O c gul st t N lo Ls (A ++ F) x v := by
  intro R hR
  obtain ⟨R1, r1, _, k1⟩ := (hA R (hN R hR)).1 (fun _ h => by simp at h)
  have hR1 : HoldsN N R1 x := HoldsN.agree N (fun y hy => k1 y (hk y (Or.inl hy)) (fun _ h => by simp at h)) hR
  refine ⟨fun f => ?_, fun nf => Crashes.append_right r1 ((hF R1 hR1).2 nf)⟩
  obtain ⟨R2, r2, hh, k2⟩ := (hF R1 hR1).1 f
  exact ⟨R2, r1.append r2, hh, fun y hy hn => (k2 y hy hn).trans (k1 y (hk y hy) (fun _ h => by simp at h))⟩

end Fill

/-! ## `[1 k]` -/

/-- The `%1` case of `run` under `%next L th` (`runLC_n1_nextT`). -/
theorem runLC_n1_nextOne (env : CallEnv) (sup : Option Nomm) (k : Noun) (L : Lazy S) (th : Jmp)
    (region : List Nat) :
    (runLC env sup (Nomm.n1 k) (CGoalL.next L th) region : CM Map (NextL S)) = (do
      let o ← medeL th k L
      pure ⟨ofSure Sure.bunt, jmp0 o⟩) := rfl

/-- **`[1 k]` in `RunOKGen`, at any lazy goal** (forks, bonds, repeated
labels, entry blocks with bodies): the block `[hop th]` with the
constant's ops in front, every goal entry's block with the ops of all the
entries at its label in front, no product register, no entry; the run adds
blocks as `GrowU` does and re-points nothing. -/
theorem runOKGen_n1 (lib : Lib) {N : Needs} {P : Noun → Prop} {f : Noun} {k : Noun} (M : MinkEq lib P f (Nomm.n1 k))
    {env : CallEnv} {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map}
    {nex : NextL S} (G : GoalG (Map := Map) L th g0)
    (hnc : ∀ r, NMem L.sure.ned r → HoonMap.get g0.cond r = Option.none)
    (hec : ∀ e ∈ entries L, ∀ r, NMem e.2.sure.ned r → HoonMap.get g0.cond r = Option.none)
    (d0 : g0.drop = false) (hu : UpBelow g0) (hcb : CondBelow g0) (hta : th.args = [])
    (h : runLC env sup (Nomm.n1 k) (CGoalL.next L th) region g0 = some (nex, g1)) (W : Noun → Noun) :
    nex = ⟨ofSure Sure.bunt, jmp0 g0.bo⟩ ∧
    RunOKGen lib N P f L th (pureWit (Nomm.n1 k) (fun _ => Need.none) W) false g0 g1 nex ∧ GrowU g0 g1 ∧
      ∀ a ∈ (entries L).map Prod.fst, ¬ RepointG g0 g1 a := by
  rw [runLC_n1_nextOne] at h
  simp only [medeL_eq, bind_apply, emit_apply, Option.bind_some, get_apply] at h
  simp only [emitted_drop, d0, Bool.false_eq_true, if_false] at h
  obtain ⟨⟨o', gW⟩, hX, hP⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u, g3, hW, h5⟩ := bind_some hX
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h5 hP
  obtain ⟨rfl, rfl⟩ := h5
  obtain ⟨rfl, rfl⟩ := hP
  obtain ⟨gE, hgE⟩ : ∃ gE : Gen Map, gE = g0.emitted ⟨[], [], Termin.hop th⟩ := ⟨_, rfl⟩
  rw [← hgE] at hW
  have dE : gE.drop = false := by simp [hgE, emitted_drop, d0]
  have bE : HoonMap.get gE.blocks g0.bo = some ⟨[], [], Termin.hop th⟩ := by
    simp [hgE, Gen.emitted, d0, HoonMap.get_put]
  have oE : ∀ o, o ≠ g0.bo → HoonMap.get gE.blocks o = HoonMap.get g0.blocks o := fun o ho => by
    simp [hgE, Gen.emitted, d0, HoonMap.get_put, ho]
  have nlab : g0.bo ∉ (entries L).map Prod.fst := fun hm => by
    obtain ⟨e, he, e1⟩ := List.mem_map.mp hm
    have := (G.lab e he).2.1; omega
  have W' := medeWalk_okL k hW dE
  have reE : gE.re = g0.re := by rw [hgE]; rfl
  have boE : gE.bo = g0.bo + 1 := by rw [hgE]; rfl
  have kE : gE.cond = g0.cond := by rw [hgE]; rfl
  have c3 : g3.cond = g0.cond := W'.cnd.trans kE
  have le3 : g0.re ≤ g3.re := reE ▸ W'.le
  have bo3' : g3.bo = g0.bo + 1 := W'.bo.trans boE
  have hj := G.jmp
  have hb0 := G.bo
  -- no register of the ops is a key of a `cond` that agrees with the final one
  have cond0 : ∀ x, g0.re ≤ x → HoonMap.get g0.cond x = Option.none := fun x hx => by
    cases e : HoonMap.get g0.cond x with
    | none => rfl
    | some _ => have := hcb x (by simp [e]); omega
  have fix : ∀ cf : Map (Nat × List Nat), (∀ kk, kk < g3.re → HoonMap.get cf kk = HoonMap.get g3.cond kk) →
      ∀ (A : List Pole), RegsIn (fun x => (x < g0.re ∧ HoonMap.get g0.cond x = Option.none) ∨
        (gE.re ≤ x ∧ x < g3.re)) A → A.map (renPole (unproxy cf)) = A :=
    fun cf hcf A hA => renOps_fix (P := fun x => (x < g0.re ∧ HoonMap.get g0.cond x = Option.none) ∨
        (gE.re ≤ x ∧ x < g3.re))
      (fun x hx => unproxy_none (by
        rcases hx with ⟨a, b⟩ | ⟨a, b⟩
        · rw [hcf x (by omega), c3]; exact b
        · rw [hcf x b, c3]; exact cond0 x (by omega))) hA
  have pieceR : ∀ (o : Nat) (p : Sure S × List Pole), (∃ e ∈ entries L, e.2.sure = p.1) ∨ p.1 = L.sure →
      MedePR (Map := Map) k gE.re g3.re o p.1 p.2 →
      RegsIn (fun x => (x < g0.re ∧ HoonMap.get g0.cond x = Option.none) ∨ (gE.re ≤ x ∧ x < g3.re)) p.2 :=
    fun o p hp hP => hP.2.mono fun x hx => by
      rcases hx with hx | hx
      · rcases hp with ⟨e, he, h2⟩ | h2
        · rw [← h2] at hx; exact Or.inl ⟨(G.eregs e he).2 x hx, hec e he x hx⟩
        · rw [h2] at hx; exact Or.inl ⟨G.sregs x hx, hnc x hx⟩
      · exact Or.inr hx
  -- the goal entries' blocks
  have ent3 : ∀ a, a ≠ g0.bo → ∃ As : List (Sure S × List Pole), FrontBlk g0 g3 a (As.map Prod.snd).flatten ∧
      (As.map Prod.fst).Perm (suresAt L a) ∧ ∀ p ∈ As, MedePR (Map := Map) k gE.re g3.re a p.1 p.2 := by
    intro a ha
    obtain ⟨As, hA, pA, qA⟩ := W'.at_ a
    refine ⟨As, fun B fin hb => hA B fin (by rw [oE a ha]; exact hb), ?_, qA⟩
    rw [atL_cons_of_neOne (fun e => ha e.symm)] at pA
    exact pA
  -- the block of `+mede`
  obtain ⟨As0, hA0, pA0, qA0⟩ := W'.at_ g0.bo
  rw [atL_cons_of_eqOne, show atL (entries L) g0.bo = [] from suresAt_nil nlab] at pA0
  have hl0 := pA0.length_eq
  simp only [List.length_map, List.length_cons, List.length_nil] at hl0
  obtain ⟨p0, rfl⟩ := List.length_eq_one_iff.mp hl0
  have hp01 : p0.1 = L.sure := by
    have := List.perm_singleton.mp pA0
    simpa using this
  have bo3 : HoonMap.get g3.blocks g0.bo = some ⟨[], p0.2 ++ [], Termin.hop th⟩ := by
    have := hA0 [] _ bE; simpa using this
  have Pp0 : MedePR (Map := Map) k gE.re g3.re g0.bo L.sure p0.2 := by
    rw [← hp01]; exact qA0 p0 List.mem_cons_self
  have other3 : ∀ o, o ≠ g0.bo → o ∉ (entries L).map Prod.fst →
      HoonMap.get g3.blocks o = HoonMap.get g0.blocks o := fun o h1' h2' =>
    (W'.other o (by simp only [List.map_cons, List.mem_cons, not_or]; exact ⟨h1', h2'⟩)).trans (oE o h1')
  have hgrow : Grow g0 g3 := by
    refine ⟨by omega, W'.drop.trans (dE.trans d0.symm), fun kk b hk hb => ?_, fun kk b' hb' => ?_⟩
    · by_cases hm : kk ∈ (entries L).map Prod.fst
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
        obtain ⟨_, hlt, B, th', hB⟩ := G.lab e he
        obtain ⟨As, hA, _⟩ := ent3 e.1 (by omega)
        rw [hB] at hb; cases hb
        exact ⟨_, hA B _ hB, rfl, rfl⟩
      · exact ⟨b, (other3 kk (by omega) hm).trans hb, rfl, rfl⟩
    · by_cases e0 : kk = g0.bo
      · subst e0; rw [bo3] at hb'; cases hb'
        refine Or.inr ⟨Nat.le_refl _, by omega, fun j hj' => ?_⟩
        simp only [finJumps, List.mem_singleton] at hj'; subst hj'; exact ⟨hj.1, hj.2⟩
      · by_cases hm : kk ∈ (entries L).map Prod.fst
        · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
          obtain ⟨_, hlt, B, th', hB⟩ := G.lab e he
          obtain ⟨As, hA, _⟩ := ent3 e.1 e0
          rw [hA B _ hB] at hb'; cases hb'
          exact Or.inl ⟨_, hB, rfl, rfl⟩
        · rw [other3 kk e0 hm] at hb'
          exact Or.inl ⟨b', hb', rfl, rfl⟩
  have GU : GrowU g0 g3 := hgrow.toU hu
  have e0 : entries (ofSure (Sure.bunt : Sure S)) = [] := entries_ofSure _
  have nb : ∀ r, ¬ NMem (Sure.bunt : Sure S).ned r := fun r hr => by simp [Sure.bunt, NMem] at hr
  have notE : ∀ a ∈ (entries L).map Prod.fst, a ≠ g0.bo := fun a ha e => nlab (e ▸ ha)
  -- the fill at a goal label
  have frontAt : ∀ a ∈ (entries L).map Prod.fst, ∀ (As : List (Sure S × List Pole)),
      (As.map Prod.fst).Perm (suresAt L a) → (∀ p ∈ As, MedePR (Map := Map) k gE.re g3.re a p.1 p.2) →
      ∀ cf : Map (Nat × List Nat), (∀ kk, kk < g3.re → HoonMap.get cf kk = HoonMap.get g3.cond kk) →
      FrontLG (Map := Map) (pureWit (Nomm.n1 k) (fun _ => Need.none) W) (gsE false L) g0.re g3.re
        (suresAt (ofSure (Sure.bunt : Sure S)) a) (((As.map Prod.snd).flatten).map (renPole (unproxy cf)))
        (suresAt L a) := by
    intro a ha As pA qA cf hcf
    have memE : ∀ p ∈ As, ∃ e ∈ entries L, e.1 = a ∧ e.2.sure = p.1 := fun p hp =>
      mem_suresAt (pA.mem_iff.mp (List.mem_map_of_mem hp))
    rw [fix cf hcf _ (regsIn_flattenOne As fun p hp => pieceR a p
      (let ⟨e, he, _, h2⟩ := memE p hp; Or.inl ⟨e, he, h2⟩) (qA p hp))]
    intro lib σ O c gul st t ned A s0 s v d w hn hq hA
    obtain ⟨hv, rfl, rfl⟩ := hq
    simp only [pureEval, Option.some.injEq] at hv
    subst hv
    have hNx : ∀ y, NMem (Need.pair (Need.pair ned Need.none) (gsE false L)) y → g3.re ≤ y := fun y hy => by
      rcases hy with (hy | hy) | hy
      · exact hn y hy
      · exact hy.elim
      · exact hy.elim
    have FL := fillSemL_list (lib := lib) (O := O) (c := c) (gul := gul) (st := st) (t := t)
      (ned := Need.pair (Need.pair ned Need.none) (gsE false L)) (lo := g0.re) (s0 := C (C s0 (W s)) k) (s := k) As
      (fun p hp => by
        obtain ⟨e, he, _, h2⟩ := memE p hp
        have d := (G.eregs e he)
        have hP : MedeP (Map := Map) k g0.re g3.re a p.1 p.2 := by
          have := (qA p hp).1; rw [reE] at this; exact this
        rw [← h2] at hP ⊢
        exact medePiece_fill hP d.1 (fun r hr => d.2 r hr) hNx)
      (fun p hp x hx => by
        obtain ⟨e, he, _, h2⟩ := memE p hp
        rw [← h2] at hx; exact (G.eregs e he).2 x hx)
      (fun y hy => by have := hNx y hy; omega)
      ((List.Perm.pairwise_iff (fun {L1 L2} hr r h1 h2 => hr r h2 h1) pA).mpr (labDisj_at G.labDisj a))
    exact FillSemL.preOne hA (FL.perm pA) (fun R hR => hR.1.1) (fun y hy => by
      rcases hy with ((hy | hy) | hy) | hy
      · exact Or.inl hy
      · exact hy.elim
      · exact hy.elim
      · exact Or.inr (by omega))
  have fr0 : ∀ e ∈ entries L, (∃ F, FrontBlk g0 g3 e.1 F) ∨ RepointG g0 g3 e.1 := fun e he => by
    obtain ⟨As, hA, _⟩ := ent3 e.1 (notE e.1 (List.mem_map_of_mem he))
    exact Or.inl ⟨_, hA⟩
  have hbo3 : g0.bo ≤ g3.bo := by omega
  have hlo3 : 1 ≤ (jmp0 g0.bo).there := by simp [jmp0]; omega
  have hhi3 : (jmp0 g0.bo).there < g3.bo := by simp [jmp0]; omega
  have hld : LabDisj (ofSure (Sure.bunt : Sure S)) := by unfold LabDisj; rw [e0]; exact List.Pairwise.nil
  have hdr : ∀ s v d w r, pureWit (Nomm.n1 k) (fun _ => Need.none) W s v d w → NMem d r →
      g0.re ≤ r ∧ r < g3.re := fun s v d w r hq hr => by obtain ⟨_, rfl, _⟩ := hq; exact hr.elim
  refine ⟨rfl, { re := le3, bo := hbo3, drop := W'.drop.trans (dE.trans d0.symm),
                 keep := fun o ho hn => other3 o (by omega) hn, grow := GU.toG, cfr := condFresh_of_eq le3 c3,
                 lo := hlo3, hi := hhi3, ent := Or.inl ⟨_, bo3, rfl, rfl⟩,
                 regs := fun r hr => absurd hr (nb r), dist := trivial,
                 eregs := fun e he => (by rw [e0] at he; cases he), labs := fun e he => (by rw [e0] at he; cases he),
                 labDisj := hld,
                 dreg := hdr,
                 ncond := fun r hr => absurd hr (nb r), econd := fun e he => (by rw [e0] at he; cases he),
                 fronts := fr0,
                 nec := fun s _ hs => absurd (fitsS_bunt s) hs, front := ?_, sem := ?_, semB := ?_ }, GU, ?_⟩
  · -- the fronts
    intro a ha
    obtain ⟨As, hA, pA, qA⟩ := ent3 a (notE a ha)
    exact Or.inl ⟨_, hA, frontAt a ha As pA qA⟩
  · -- the forward `sem`
    intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs' hm ag hned regs hh hn
    rw [(M s hs' gul tm r).mp ⟨n, hm⟩]
    refine goalSemCMD_of_goalSemD hI htr (fun p hp => ⟨hp, rfl, rfl⟩) ?_
    have hc : HoonMap.get c.blocks g0.bo = some ⟨[], p0.2 ++ [], Termin.hop th⟩ := by
      rw [(ag st t).1 g0.bo (Nat.le_refl _) (by omega) (by rw [e0]; simp), bo3]
      have := fix cf hcf p0.2 (pieceR g0.bo p0 (Or.inr hp01) (hp01 ▸ Pp0))
      simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, List.append_nil, renFin,
        renJmp_nil _ hta, this]
    show GoalSemD lib O c gul st _ regs t (jmp0 g0.bo) L.sure th Need.none (W s) (pureEval (Nomm.n1 k) s)
    simp only [pureEval, GoalSemD]
    obtain ⟨S1, S2⟩ := Pp0.1 lib σ O c gul st t regs G.dist (fun r hr => by rw [reE]; exact G.sregs r hr)
    rw [goJ_jmp0 _ _ _ _ hc]
    refine ⟨fun f => ?_, fun nf => S2 nf [] _⟩
    obtain ⟨R2, r2, hh2, k2⟩ := S1 f
    refine ⟨R2, hh2.1, trivial, fun r hr => k2 r hr.2 (fun ⟨a, b⟩ => ?_), by rw [r2 [] _, execBlob_hop]⟩
    rcases hr.1 with x | x
    · omega
    · have := hned r x; omega
  · -- the backward `sem`
    intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs' ag hned regs hh hn res hres
    refine ⟨_, (M s hs' gul tm _).mpr rfl, goalSemCMD_of_goalSemD hI htr (fun p hp => ⟨hp, rfl, rfl⟩) ?_⟩
    have hc : HoonMap.get c.blocks g0.bo = some ⟨[], p0.2 ++ [], Termin.hop th⟩ := by
      rw [(ag st t).1 g0.bo (Nat.le_refl _) (by omega) (by rw [e0]; simp), bo3]
      have := fix cf hcf p0.2 (pieceR g0.bo p0 (Or.inr hp01) (hp01 ▸ Pp0))
      simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, List.append_nil, renFin,
        renJmp_nil _ hta, this]
    show GoalSemD lib O c gul st _ regs t (jmp0 g0.bo) L.sure th Need.none (W s) (pureEval (Nomm.n1 k) s)
    simp only [pureEval, GoalSemD]
    obtain ⟨S1, S2⟩ := Pp0.1 lib σ O c gul st t regs G.dist (fun r hr => by rw [reE]; exact G.sregs r hr)
    rw [goJ_jmp0 _ _ _ _ hc]
    refine ⟨fun f => ?_, fun nf => S2 nf [] _⟩
    obtain ⟨R2, r2, hh2, k2⟩ := S1 f
    refine ⟨R2, hh2.1, trivial, fun r hr => k2 r hr.2 (fun ⟨a, b⟩ => ?_), by rw [r2 [] _, execBlob_hop]⟩
    rcases hr.1 with x | x
    · omega
    · have := hned r x; omega
  · -- no re-pointing
    intro a ha hr
    obtain ⟨B, fin, F, o1, o2, F2, hb0', hb1, l1, u1, l2, u2, hb2⟩ := hr
    obtain ⟨As, hA, _⟩ := ent3 a (notE a ha)
    rw [hA B fin hb0'] at hb1
    simp only [Option.some.injEq, Blob.mk.injEq, true_and] at hb1
    have eo2 : o2 = g0.bo := by omega
    have eo1 : o1 = g0.bo := by omega
    subst eo2
    rw [bo3] at hb2
    simp only [Option.some.injEq, Blob.mk.injEq, true_and] at hb2
    rw [← hb2.2, Termin.hop.injEq] at hb1
    have := congrArg Jmp.there hb1.2
    simp only at this
    omega

end Comp
end SkaModel
end Formalization
