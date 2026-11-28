import lemmas.Ska.CompGenClass
import lemmas.Ska.RawInvCLSACountSplit

/-!
# The general cons taken apart, and the goals of its parts

README Gaps 12.39, item 12.  The cons `[p q]` of two call-free parts under
`%next L th` at a goal of the class (`PremG`): `+split` (state `gS`), `q`
under `%next tel (jmp0 g0.bo)` (state `g2`), `p` under `%next hed nq.th`
(state `g3`), `+copy` of the two results (`ConsGAt`, `consGAt_of_run`,
`ConsGAt.copyOK`).  The fresh registers of `+split` occur at most once in
both halves over all labels (`cb_split_count`, a count without the
definitions of `SCR`), so the halves are apart across labels
(`halvesApart_split`), and each part's goal meets the class's premises
(`premG_tel`, `premG_hed`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The cons of two call-free parts under `%next`, taken apart.** -/
theorem runLC_consG_apart (env : CallEnv) (sup : Option Nomm) {p q : Nomm} (hp : p.pure = true)
    (hq : q.pure = true) {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (h : runLC env sup (Nomm.cons p q) (CGoalL.next L th) region g0 = some (nex, g1)) :
    ∃ (hed tel : Lazy S) (o : Nat) (gS g2 g3 : Gen Map) (nq np : NextL S),
      splitL ⟨L, th⟩ g0 = some ((hed, tel, o), gS) ∧
      runLC env sup q (CGoalL.next tel (jmp0 o)) region gS = some (nq, g2) ∧
      runLC env sup p (CGoalL.next hed nq.th) region g2 = some (np, g3) ∧
      copyL np nq.laz g3 = some (nex, g1) := by
  have e : (runLC env sup (Nomm.cons p q) (CGoalL.next L th) region : CM Map (NextL S)) = (do
        let (hed, tel, o) ← splitL ⟨L, th⟩
        let nexh ← pastL env.cod ⟨hed, jmp0 o⟩ q region
        let nex2 ← runLC env sup q (CGoalL.next tel nexh.th) region
        let nex2 ← pastL env.cod nex2 p region
        let nex1 ← runLC env sup p (CGoalL.next nexh.laz nex2.th) region
        copyL nex1 nex2.laz) := rfl
  rw [e] at h
  obtain ⟨⟨hed, tel, o⟩, gS, hs, h⟩ := bind_some h
  simp only at h
  obtain ⟨nexh, gb, hph, h⟩ := bind_some h
  rw [pastL_pure _ _ hq, pure_apply] at hph
  simp only [Option.some.injEq, Prod.mk.injEq] at hph
  obtain ⟨rfl, rfl⟩ := hph
  obtain ⟨nq, g2, h3, h⟩ := bind_some h
  obtain ⟨nq', g2', hp2, h⟩ := bind_some h
  rw [pastL_pure _ _ hp, pure_apply] at hp2
  simp only [Option.some.injEq, Prod.mk.injEq] at hp2
  obtain ⟨rfl, rfl⟩ := hp2
  obtain ⟨np, g3, h4, hcp⟩ := bind_some h
  exact ⟨hed, tel, o, gS, g2, g3, nq, np, hs, h3, h4, hcp⟩

/-- **The run of the general cons, every state named**: `gS` (after the
split, whose block is `g0.bo`), `g2` (after `q`), `g3` (after `p`), `g1`;
the halves `hed`, `tel`; the parts' results `nq`, `np`. -/
structure ConsGAt (L : Lazy S) (th : Jmp) (p q : Nomm) (env : CallEnv) (sup : Option Nomm) (region : List Nat)
    (g0 g1 : Gen Map) (nex : NextL S) (hed tel : Lazy S) (gS g2 g3 : Gen Map) (nq np : NextL S) : Prop where
  hs : splitL ⟨L, th⟩ g0 = some ((hed, tel, g0.bo), gS)
  eo : HoonMap.get (g0.emitted ⟨[], [], Termin.hop th⟩).blocks g0.bo = some ⟨[], [], Termin.hop th⟩
  sp : SplitOKD (g0.emitted ⟨[], [], Termin.hop th⟩) gS ((g0.bo, L) :: entries L) ((g0.bo, hed) :: entries hed)
    ((g0.bo, tel) :: entries tel)
  boS : gS.bo = g0.bo + 1
  dS : gS.drop = false
  reS : g0.re ≤ gS.re
  condS : gS.cond = g0.cond
  growS : GrowU g0 gS
  luh : Raw.LabUniq hed
  lut : Raw.LabUniq tel
  labH : ∀ e ∈ entries hed, e.1 ∈ (entries L).map Prod.fst
  labT : ∀ e ∈ entries tel, e.1 ∈ (entries L).map Prod.fst
  rq : runLC env sup q (CGoalL.next tel (jmp0 g0.bo)) region gS = some (nq, g2)
  rp : runLC env sup p (CGoalL.next hed nq.th) region g2 = some (np, g3)
  cp : copyL np nq.laz g3 = some (nex, g1)
  hc : copyLazyL g3.bo np.laz nq.laz (g3.emitted ⟨[], [], Termin.hop np.th⟩) = some (nex.laz, g1)
  eth : nex.th = jmp0 g3.bo

theorem consGAt_of_run (env : CallEnv) (sup : Option Nomm) {p q : Nomm} (hp : p.pure = true)
    (hq : q.pure = true) {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (G : PremG (Map := Map) L th g0)
    (h : runLC env sup (Nomm.cons p q) (CGoalL.next L th) region g0 = some (nex, g1)) :
    ∃ (hed tel : Lazy S) (gS g2 g3 : Gen Map) (nq np : NextL S),
      ConsGAt L th p q env sup region g0 g1 nex hed tel gS g2 g3 nq np := by
  obtain ⟨hed, tel, o, gS, g2, g3, nq, np, hs, h3, h4, hcp⟩ := runLC_consG_apart env sup hp hq h
  obtain ⟨rfl, eo, WS⟩ := splitL_okD hs G.drop (fun e he => by
    obtain ⟨_, hlt, B, th', hb'⟩ := G.goal.lab e he
    exact ⟨hlt, B, _, hb'⟩)
  obtain ⟨eth, hc⟩ := copyL_apart hcp
  obtain ⟨luh, lut, qh, qt⟩ := Raw.lab_splitL (Q := fun o => o ∈ (entries L).map Prod.fst) hs G.lu
    (fun e he => List.mem_map_of_mem he)
  have dE : (g0.emitted ⟨[], [], Termin.hop th⟩).drop = false := G.drop
  have WS0 := WS
  obtain ⟨PS, PPS, -, -⟩ := WS0
  have GE : GrowU g0 (g0.emitted ⟨[], [], Termin.hop th⟩) :=
    growU_emit (jumpsBelow_hop G.goal.jmp.1 G.goal.jmp.2) G.up
  refine ⟨hed, tel, gS, g2, g3, nq, np, hs, eo, WS, PPS.bo, PPS.drop.trans dE, ?_, ?_, GE.trans PPS.growU,
    luh, lut, qh, qt, h3, h4, hcp, hc, eth⟩
  · have := PPS.re; simp only [emitted_re] at *; omega
  · rw [PPS.cond]; rfl

/-- **The copy's per-label spec** (track D's `copyLazyL_okL`), once the
copy's start has `drop` off and both results are `LabUniq`. -/
theorem ConsGAt.copyOK {L : Lazy S} {th : Jmp} {p q : Nomm} {env : CallEnv} {sup : Option Nomm}
    {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} {hed tel : Lazy S} {gS g2 g3 : Gen Map}
    {nq np : NextL S} (C : ConsGAt L th p q env sup region g0 g1 nex hed tel gS g2 g3 nq np)
    (d3 : g3.drop = false) (lup : Raw.LabUniq np.laz) (luq : Raw.LabUniq nq.laz) :
    CopyOKL (g3.emitted ⟨[], [], Termin.hop np.th⟩) g1 ((g3.bo, np.laz) :: entries np.laz)
      ((g3.bo, nq.laz) :: entries nq.laz) ((g3.bo, nex.laz) :: entries nex.laz) :=
  copyLazyL_okL g3.bo np.laz nq.laz _ g1 nex.laz C.hc d3 lup luq

/-! ## The fresh registers of `+split`, counted -/

/-- **A count of registers without the definitions**: each register occurs
in the output at most as often as in the input, plus once when fresh. -/
def CntR {α : Type} (ri : List Nat) (m : CM Map α) (ro : α → List Nat) : Prop :=
  ∀ g x g', m g = some (x, g') → g.re ≤ g'.re ∧ ∀ y, (ro x).count y ≤ ri.count y + Raw.fr g.re g'.re y

theorem cb_bind {α β : Type} {ri : List Nat} {r1 : α → List Nat} {ro : β → List Nat} {m : CM Map α}
    {f : α → CM Map β} (hm : CntR (Map := Map) ri m r1) (hf : ∀ a, CntR (Map := Map) (r1 a) (f a) ro) :
    CntR (Map := Map) ri (m >>= f) ro := by
  intro g x g' h
  obtain ⟨a, g1, h1, h2⟩ := bind_some h
  obtain ⟨l1, c1⟩ := hm g a g1 h1
  obtain ⟨l2, c2⟩ := hf a g1 x g' h2
  refine ⟨Nat.le_trans l1 l2, fun y => ?_⟩
  have := c1 y; have := c2 y; have := Raw.fr_add l1 l2 y
  omega

theorem cb_pure {α : Type} {ri : List Nat} {ro : α → List Nat} {a : α} (h : ∀ y, (ro a).count y ≤ ri.count y) :
    CntR (Map := Map) ri (pure a : CM Map α) ro := by
  intro g x g' e
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨Nat.le_refl _, fun y => by have := h y; omega⟩

theorem cb_re (ri : List Nat) : CntR (Map := Map) ri (re : CM Map Nat) (fun r => ri ++ [r]) := by
  intro g x g' e
  rw [re_apply] at e
  simp only [Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  refine ⟨Nat.le_succ _, fun y => ?_⟩
  simp only [List.count_append, List.count_singleton, Raw.fr]
  by_cases e : g.re = y
  · subst e; simp
  · have : ¬ (g.re ≤ y ∧ y < g.re + 1) := fun h => e (by omega)
    simp [e, this]

theorem cb_ite {α : Type} {ri : List Nat} {ro : α → List Nat} (c : Prop) [Decidable c] {a b : CM Map α}
    (ha : CntR (Map := Map) ri a ro) (hb : CntR (Map := Map) ri b ro) : CntR (Map := Map) ri (if c then a else b) ro := by
  split
  · exact ha
  · exact hb

theorem cb_addOps (o : Nat) (A : List Pole) (ri : List Nat) :
    CntR (Map := Map) ri (addOps o A) (fun _ => ri) := by
  intro g x g' e
  unfold addOps at e
  split at e
  · injection e with e
    injection e with _ e
    subst e
    exact ⟨Nat.le_refl _, fun y => Nat.le_add_right _ _⟩
  · obtain ⟨b, -, e⟩ := Option.map_eq_some_iff.mp e
    injection e with _ e
    subst e
    exact ⟨Nat.le_refl _, fun y => Nat.le_add_right _ _⟩

theorem cb_emit (b : Blob) (ri : List Nat) : CntR (Map := Map) ri (emit b) (fun _ => ri) := by
  intro g x g' e
  rw [emit_apply] at e
  simp only [Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨Nat.le_refl _, fun y => Nat.le_add_right _ _⟩

/-- A count with a frame list `X` on both sides. -/
theorem cb_fr {α : Type} {ri : List Nat} {m : CM Map α} {ro : α → List Nat} (h : CntR (Map := Map) ri m ro)
    (X : List Nat) {ri' : List Nat} {ro' : α → List Nat} (hi : ∀ y, ri.count y + X.count y ≤ ri'.count y)
    (ho : ∀ x y, (ro' x).count y ≤ (ro x).count y + X.count y) : CntR (Map := Map) ri' m ro' := by
  intro g x g' e
  obtain ⟨l1, c1⟩ := h g x g' e
  exact ⟨l1, fun y => by have := c1 y; have := hi y; have := ho x y; omega⟩

theorem cb_must (ned : Need) : CntR (Map := Map) (flattenNeed ned) (must ned) (fun x => flattenNeed x.2) := by
  cases ned with
  | both r h t => exact cb_pure fun _ => Nat.le_refl _
  | this r => exact cb_pure fun _ => Nat.le_refl _
  | pair p q =>
    simp only [must]
    refine cb_bind (cb_re _) fun r => cb_pure fun y => ?_
    have e : flattenNeed (Need.both r p q) = r :: (flattenNeed (Need.pair p q)) := rfl
    rw [e]
    exact Nat.le_of_eq ((List.perm_append_singleton r _).count_eq y).symm
  | none =>
    simp only [must]
    refine cb_bind (cb_re _) fun r => cb_pure fun y => ?_
    simp [flattenNeed]

theorem cb_need (ned : Need) (o : Nat) :
    CntR (Map := Map) (flattenNeed ned) (splitNeed ned o) (fun x => flattenNeed x.1 ++ flattenNeed x.2) := by
  cases ned with
  | pair p q => exact cb_pure fun _ => Nat.le_refl _
  | none => exact cb_pure fun _ => by simp [flattenNeed]
  | this r =>
    simp only [splitNeed]
    refine cb_bind (cb_re _) fun h => cb_bind (cb_re _) fun t => ?_
    refine cb_bind (cb_addOps o _ _) fun _ => cb_pure fun y => ?_
    simp only [flattenNeed, List.singleton_append, List.cons_append, List.nil_append]
    exact (List.sublist_cons_self r [h, t]).count_le y
  | both r h t =>
    have e : flattenNeed (Need.both r h t) = [r] ++ (flattenNeed h ++ flattenNeed t) := rfl
    simp only [splitNeed]
    rw [e]
    refine cb_bind (cb_fr (cb_must h) ([r] ++ flattenNeed t)
      (ro' := fun x => [r] ++ (flattenNeed x.2 ++ flattenNeed t))
      (fun y => by simp only [List.count_append]; omega) (fun x y => by simp only [List.count_append]; omega))
      fun hed => ?_
    refine cb_bind (cb_fr (cb_must t) ([r] ++ flattenNeed hed.2)
      (ro' := fun x => [r] ++ (flattenNeed hed.2 ++ flattenNeed x.2))
      (fun y => by simp only [List.count_append]; omega) (fun x y => by simp only [List.count_append]; omega))
      fun tel => ?_
    refine cb_bind (cb_addOps o _ _) fun _ => cb_pure fun y => ?_
    simp only [List.count_append]; omega

theorem cb_sure (sur : Sure S) (o : Nat) :
    CntR (Map := Map) (flattenNeed sur.ned) (splitSure sur o) (fun x => flattenNeed x.1.ned ++ flattenNeed x.2.ned) := by
  intro g x g' e
  unfold splitSure at e
  obtain ⟨⟨lh, lt⟩, -, e⟩ := Option.bind_eq_some_iff.mp e
  obtain ⟨⟨⟨nh, nt⟩, g1⟩, e1, e2⟩ := Option.map_eq_some_iff.mp e
  simp only [Prod.mk.injEq] at e2
  obtain ⟨rfl, rfl⟩ := e2
  exact cb_need sur.ned o g _ g1 e1

mutual
/-- **The count of `split-loop`** (`Raw.scspLoop` without the definitions). -/
theorem cbLoop : ∀ (l : Lazy S) (o : Nat),
    CntR (Map := Map) (Raw.sarR l) (splitLoop l o) (fun x => Raw.sarR x.1 ++ Raw.sarR x.2)
  | mk s f b, o => by
    rw [splitLoop, Raw.scsp_sarR_mk]
    refine cb_bind (cb_fr (cb_sure s o) (Raw.regsL (bondEntries b) ++ Raw.regsL (forkEntries f))
      (ro' := fun p => flattenNeed p.1.ned ++ flattenNeed p.2.ned ++
        (Raw.regsL (bondEntries b) ++ Raw.regsL (forkEntries f)))
      (fun z => by simp only [List.count_append]; omega) (fun x z => by simp only [List.count_append]; omega))
      fun p => ?_
    obtain ⟨sh, st⟩ := p
    refine cb_ite _ (cb_pure fun z => ?_) ?_
    · simp only [Raw.sarR_ofSure, List.count_append]; omega
    · refine cb_bind (cb_fr (cbForks f) (flattenNeed sh.ned ++ flattenNeed st.ned ++ Raw.regsL (bondEntries b))
        (ro' := fun p => flattenNeed sh.ned ++ flattenNeed st.ned ++ Raw.regsL (bondEntries b) ++
          (Raw.regsL (forkEntries p.1) ++ Raw.regsL (forkEntries p.2)))
        (fun z => by simp only [List.count_append]; omega) (fun x z => by simp only [List.count_append]; omega))
        fun p => ?_
      obtain ⟨fh, ft⟩ := p
      refine cb_bind (cb_fr (cbBonds b)
        (flattenNeed sh.ned ++ flattenNeed st.ned ++ (Raw.regsL (forkEntries fh) ++ Raw.regsL (forkEntries ft)))
        (ro' := fun p => flattenNeed sh.ned ++ flattenNeed st.ned ++
          (Raw.regsL (bondEntries p.1) ++ Raw.regsL (bondEntries p.2)) ++
          (Raw.regsL (forkEntries fh) ++ Raw.regsL (forkEntries ft)))
        (fun z => by simp only [List.count_append]; omega) (fun x z => by simp only [List.count_append]; omega))
        fun p => ?_
      obtain ⟨bh, bt⟩ := p
      refine cb_pure fun z => ?_
      have h1 := Raw.scsp_prune sh fh bh z
      have h2 := Raw.scsp_prune st ft bt z
      simp only [List.count_append] at h1 h2 ⊢
      omega

theorem cbForks : ∀ (f : List (ForkE S)),
    CntR (Map := Map) (Raw.regsL (forkEntries f)) (splitForks f)
      (fun x => Raw.regsL (forkEntries x.1) ++ Raw.regsL (forkEntries x.2))
  | [] => by
    rw [splitForks]
    exact cb_pure fun z => by simp [forkEntries, Raw.regsL_nil]
  | ((oy, y), (on, n)) :: rest => by
    rw [splitForks, Raw.scsp_fe_cons]
    refine cb_bind (cb_fr (cbLoop y oy) (Raw.sarR n ++ Raw.regsL (forkEntries rest))
      (ro' := fun p => Raw.sarR p.1 ++ Raw.sarR p.2 ++ (Raw.sarR n ++ Raw.regsL (forkEntries rest)))
      (fun z => by simp only [List.count_append]; omega) (fun x z => by simp only [List.count_append]; omega))
      fun p => ?_
    obtain ⟨yh, yt⟩ := p
    refine cb_bind (cb_fr (cbLoop n on) (Raw.sarR yh ++ Raw.sarR yt ++ Raw.regsL (forkEntries rest))
      (ro' := fun p => Raw.sarR yh ++ Raw.sarR yt ++ (Raw.sarR p.1 ++ Raw.sarR p.2) ++ Raw.regsL (forkEntries rest))
      (fun z => by simp only [List.count_append]; omega) (fun x z => by simp only [List.count_append]; omega))
      fun p => ?_
    obtain ⟨nh, nt⟩ := p
    refine cb_bind (cb_fr (cbForks rest) (Raw.sarR yh ++ Raw.sarR yt ++ (Raw.sarR nh ++ Raw.sarR nt))
      (ro' := fun p => Raw.sarR yh ++ Raw.sarR yt ++ (Raw.sarR nh ++ Raw.sarR nt) ++
        (Raw.regsL (forkEntries p.1) ++ Raw.regsL (forkEntries p.2)))
      (fun z => by simp only [List.count_append]; omega) (fun x z => by simp only [List.count_append]; omega))
      fun p => ?_
    obtain ⟨rh, rt⟩ := p
    refine cb_pure fun z => ?_
    rw [Raw.scsp_fe_cons, Raw.scsp_fe_cons]
    simp only [List.count_append]
    omega

theorem cbBonds : ∀ (b : List (Nat × Lazy S)),
    CntR (Map := Map) (Raw.regsL (bondEntries b)) (splitBonds b)
      (fun x => Raw.regsL (bondEntries x.1) ++ Raw.regsL (bondEntries x.2))
  | [] => by
    rw [splitBonds]
    exact cb_pure fun z => by simp [bondEntries, Raw.regsL_nil]
  | (o, l) :: rest => by
    rw [splitBonds, Raw.scsp_be_cons]
    refine cb_bind (cb_fr (cbLoop l o) (Raw.regsL (bondEntries rest))
      (ro' := fun p => Raw.sarR p.1 ++ Raw.sarR p.2 ++ Raw.regsL (bondEntries rest))
      (fun z => by simp only [List.count_append]; omega) (fun x z => by simp only [List.count_append]; omega))
      fun p => ?_
    obtain ⟨lh, lt⟩ := p
    refine cb_bind (cb_fr (cbBonds rest) (Raw.sarR lh ++ Raw.sarR lt)
      (ro' := fun p => Raw.sarR lh ++ Raw.sarR lt ++ (Raw.regsL (bondEntries p.1) ++ Raw.regsL (bondEntries p.2)))
      (fun z => by simp only [List.count_append]; omega) (fun x z => by simp only [List.count_append]; omega))
      fun p => ?_
    obtain ⟨rh, rt⟩ := p
    refine cb_pure fun z => ?_
    rw [Raw.scsp_be_cons, Raw.scsp_be_cons]
    simp only [List.count_append]
    omega
end

/-- **The count of `+split`**: over both halves, a register occurs at most
as often as in the goal's tree, plus once when fresh. -/
theorem cb_split_count {L : Lazy S} {th : Jmp} {g g' : Gen Map} {hed tel : Lazy S} {o : Nat}
    (h : splitL ⟨L, th⟩ g = some ((hed, tel, o), g')) (y : Nat) :
    (Raw.sarR hed ++ Raw.sarR tel).count y ≤ (Raw.sarR L).count y + Raw.fr g.re g'.re y := by
  have C : CntR (Map := Map) (Raw.sarR L) (splitL ⟨L, th⟩) (fun x => Raw.sarR x.1 ++ Raw.sarR x.2.1) := by
    unfold splitL
    refine cb_bind (cb_emit _ _) fun o => cb_bind (cbLoop L o) fun p => ?_
    obtain ⟨h, t⟩ := p
    exact cb_pure fun z => Nat.le_refl _
  exact (C g _ g' h).2 y

/-! ## The halves per label -/

theorem cb_mem_atL_self (o : Nat) (l : Lazy S) (es : List (Nat × Lazy S)) : l.sure ∈ atL ((o, l) :: es) o := by
  simp [atL]

theorem cb_mem_atL_of {e : Nat × Lazy S} {es : List (Nat × Lazy S)} (he : e ∈ es) (x : Nat × Lazy S) :
    e.2.sure ∈ atL (x :: es) e.1 := by
  unfold atL
  exact List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨List.mem_cons_of_mem _ he, by simp⟩, rfl⟩

theorem cb_mem_atL_ent {e : Nat × Lazy S} {es : List (Nat × Lazy S)} (he : e ∈ es) : e.2.sure ∈ atL es e.1 := by
  unfold atL
  exact List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨he, by simp⟩, rfl⟩

theorem cb_atL_sub (x : Nat × Lazy S) (es : List (Nat × Lazy S)) (k : Nat) : (atL es k).Sublist (atL (x :: es) k) :=
  ((List.sublist_cons_self x es).filter _).map _

/-- A half's need at a label comes from one piece of the split there. -/
theorem cb_pieceH {g g' : Gen Map} {es hs ts : List (Nat × Lazy S)} (W : SplitOKD g g' es hs ts) {k : Nat}
    {H : Sure S} (hH : H ∈ atL hs k) :
    ∃ p : SplitE S, p.1 ∈ atL es k ∧ SplitP (Map := Map) g.re g'.re p ∧ (p.2.1 = H ∨ p.2.2.1 = H) := by
  obtain ⟨P, PP, O, A⟩ := W
  obtain ⟨ps, eP, pE, dH, dT, sP, aP⟩ := A k
  obtain ⟨kk, hp, -⟩ := dH
  obtain ⟨p, hp', rfl⟩ := List.mem_map.mp (hp.mem_iff.mp (List.mem_append_left _ hH))
  exact ⟨p, pE.mem_iff.mp (List.mem_map_of_mem hp'), sP p hp', Or.inl rfl⟩

theorem cb_pieceT {g g' : Gen Map} {es hs ts : List (Nat × Lazy S)} (W : SplitOKD g g' es hs ts) {k : Nat}
    {H : Sure S} (hH : H ∈ atL ts k) :
    ∃ p : SplitE S, p.1 ∈ atL es k ∧ SplitP (Map := Map) g.re g'.re p ∧ (p.2.1 = H ∨ p.2.2.1 = H) := by
  obtain ⟨P, PP, O, A⟩ := W
  obtain ⟨ps, eP, pE, dH, dT, sP, aP⟩ := A k
  obtain ⟨kk, hp, -⟩ := dT
  obtain ⟨p, hp', rfl⟩ := List.mem_map.mp (hp.mem_iff.mp (List.mem_append_left _ hH))
  exact ⟨p, pE.mem_iff.mp (List.mem_map_of_mem hp'), sP p hp', Or.inr rfl⟩

theorem cb_atL_root {o : Nat} {L : Lazy S} (hl : ∀ e ∈ entries L, e.1 < o) {F : Sure S}
    (h : F ∈ atL ((o, L) :: entries L) o) : F = L.sure := by
  obtain ⟨e, he, e1, e2⟩ := mem_atL h
  rcases List.mem_cons.mp he with rfl | he
  · exact e2.symm
  · have := hl e he; omega

theorem cb_atL_ent {o : Nat} {L : Lazy S} {k : Nat} (hk : k < o) {F : Sure S}
    (h : F ∈ atL ((o, L) :: entries L) k) : ∃ e0 ∈ entries L, e0.1 = k ∧ e0.2.sure = F := by
  obtain ⟨e, he, e1, e2⟩ := mem_atL h
  rcases List.mem_cons.mp he with rfl | he
  · simp only at e1; omega
  · exact ⟨e, he, e1, e2⟩

/-- **What a half of the split is, per label**: distinct clean needs whose
registers are the goal's at the same place, or fresh. -/
structure HalfOK (L : Lazy S) (lo hi : Nat) (h : Lazy S) : Prop where
  sd : Distinct h.sure.ned
  sr : ∀ r, NMem h.sure.ned r → NMem L.sure.ned r ∨ (lo ≤ r ∧ r < hi)
  sc : Clean h.sure.ned
  ed : ∀ e ∈ entries h, Distinct e.2.sure.ned
  er : ∀ e ∈ entries h, ∀ r, NMem e.2.sure.ned r →
    (∃ e0 ∈ entries L, e0.1 = e.1 ∧ NMem e0.2.sure.ned r) ∨ (lo ≤ r ∧ r < hi)
  ec : ∀ e ∈ entries h, Clean e.2.sure.ned

theorem cb_halfOK {L h : Lazy S} {th : Jmp} {g0 : Gen Map} {hi : Nat} (G : PremG (Map := Map) L th g0)
    (hl : ∀ e ∈ entries h, e.1 ∈ (entries L).map Prod.fst)
    (pc : ∀ k (H : Sure S), H ∈ atL ((g0.bo, h) :: entries h) k → ∃ p : SplitE S,
      p.1 ∈ atL ((g0.bo, L) :: entries L) k ∧ SplitP (Map := Map) g0.re hi p ∧ (p.2.1 = H ∨ p.2.2.1 = H)) :
    HalfOK L g0.re hi h := by
  have hlab : ∀ e ∈ entries L, e.1 < g0.bo := fun e he => (G.goal.lab e he).2.1
  have hlab' : ∀ e ∈ entries h, e.1 < g0.bo := fun e he => by
    obtain ⟨e0, he0, e1⟩ := List.mem_map.mp (hl e he)
    rw [← e1]; exact hlab e0 he0
  -- the root
  obtain ⟨p, hp1, sp, hpH⟩ := pc g0.bo h.sure (cb_mem_atL_self _ _ _)
  have ep : p.1 = L.sure := cb_atL_root hlab hp1
  have sm := sp.sem (by rw [ep]; exact G.goal.dist) (fun y hy => by rw [ep] at hy; exact G.goal.sregs y hy)
  have scl := sp.cl (by rw [ep]; exact G.cl)
  -- an entry
  have ent : ∀ e ∈ entries h, ∃ e0 ∈ entries L, e0.1 = e.1 ∧ Distinct e.2.sure.ned ∧
      (∀ r, NMem e.2.sure.ned r → NMem e0.2.sure.ned r ∨ (g0.re ≤ r ∧ r < hi)) ∧ Clean e.2.sure.ned := by
    intro e he
    obtain ⟨q, hq1, sq, hqH⟩ := pc e.1 e.2.sure (cb_mem_atL_of he _)
    obtain ⟨e0, he0, e01, e02⟩ := cb_atL_ent (hlab' e he) hq1
    have sm' := sq.sem (by rw [← e02]; exact (G.goal.eregs e0 he0).1)
      (fun y hy => by rw [← e02] at hy; exact (G.goal.eregs e0 he0).2 y hy)
    have qcl := sq.cl (by rw [← e02]; exact G.ecl e0 he0)
    refine ⟨e0, he0, e01, ?_, fun r hr => ?_, ?_⟩
    · rcases hqH with e | e <;> rw [← e]
      · exact sm'.1
      · exact sm'.2.1
    · rcases hqH with e | e <;> rw [← e] at hr
      · rcases sq.mh r hr with h | h
        · rw [← e02] at h; exact Or.inl h
        · exact Or.inr h
      · rcases sq.mt r hr with h | h
        · rw [← e02] at h; exact Or.inl h
        · exact Or.inr h
    · rcases hqH with e | e <;> rw [← e]
      · exact qcl.1
      · exact qcl.2
  refine ⟨?_, fun r hr => ?_, ?_, fun e he => (Classical.choose_spec (ent e he)).2.2.1, fun e he r hr => ?_,
    fun e he => (Classical.choose_spec (ent e he)).2.2.2.2⟩
  · rcases hpH with e | e <;> rw [← e]
    · exact sm.1
    · exact sm.2.1
  · rcases hpH with e | e <;> rw [← e] at hr
    · rcases sp.mh r hr with h | h
      · rw [ep] at h; exact Or.inl h
      · exact Or.inr h
    · rcases sp.mt r hr with h | h
      · rw [ep] at h; exact Or.inl h
      · exact Or.inr h
  · rcases hpH with e | e <;> rw [← e]
    · exact scl.1
    · exact scl.2
  · obtain ⟨e0, he0, e01, -, hr0, -⟩ := ent e he
    rcases hr0 r hr with h | h
    · exact Or.inl ⟨e0, he0, e01, h⟩
    · exact Or.inr h

section Halves
variable {L : Lazy S} {th : Jmp} {p q : Nomm} {env : CallEnv} {sup : Option Nomm} {region : List Nat}
  {g0 g1 : Gen Map} {nex : NextL S} {hed tel : Lazy S} {gS g2 g3 : Gen Map} {nq np : NextL S}

theorem ConsGAt.halfH (C : ConsGAt L th p q env sup region g0 g1 nex hed tel gS g2 g3 nq np)
    (G : PremG (Map := Map) L th g0) : HalfOK L g0.re gS.re hed :=
  cb_halfOK G C.labH fun k H hH => cb_pieceH C.sp hH

theorem ConsGAt.halfT (C : ConsGAt L th p q env sup region g0 g1 nex hed tel gS g2 g3 nq np)
    (G : PremG (Map := Map) L th g0) : HalfOK L g0.re gS.re tel :=
  cb_halfOK G C.labT fun k H hH => cb_pieceT C.sp hH

/-- The halves at one label are pairwise apart (`SplitOKD.apartAt` at the goal). -/
theorem ConsGAt.apartAt (C : ConsGAt L th p q env sup region g0 g1 nex hed tel gS g2 g3 nq np)
    (G : PremG (Map := Map) L th g0) (k : Nat) :
    (atL ((g0.bo, hed) :: entries hed) k ++ atL ((g0.bo, tel) :: entries tel) k).Pairwise
      fun L L' => ∀ r, NMem L.ned r → ¬ NMem L'.ned r := by
  have hlab : ∀ e ∈ entries L, e.1 < g0.bo := fun e he => (G.goal.lab e he).2.1
  refine C.sp.apartAt (List.pairwise_cons.mpr ⟨fun e he heq => ?_, G.goal.labDisj⟩) (fun e he => ?_) k
  · have := hlab e he; simp only at heq; omega
  · rcases List.mem_cons.mp he with rfl | he
    · exact ⟨G.goal.dist, fun y hy => G.goal.sregs y hy⟩
    · exact G.goal.eregs e he

/-- **A fresh register of the split occurs once** over both halves, every label. -/
theorem ConsGAt.fresh1 (C : ConsGAt L th p q env sup region g0 g1 nex hed tel gS g2 g3 nq np)
    (G : PremG (Map := Map) L th g0) {r : Nat} (hr : g0.re ≤ r) :
    (flattenNeed hed.sure.ned).count r + (Raw.regsL (entries hed)).count r +
      ((flattenNeed tel.sure.ned).count r + (Raw.regsL (entries tel)).count r) ≤ 1 := by
  have c := cb_split_count C.hs r
  have z : (Raw.sarR L).count r = 0 := by
    refine List.count_eq_zero.mpr fun hm => ?_
    unfold Raw.sarR at hm
    rcases List.mem_append.mp hm with hm | hm
    · have := G.goal.sregs r ((mem_flatten _ _).mp hm); omega
    · obtain ⟨e, he, hn⟩ := Raw.mem_regsL.mp hm
      have := (G.goal.eregs e he).2 r hn; omega
  have f1 := Raw.fr_le_one g0.re gS.re r
  simp only [Raw.sarR, List.count_append] at c z
  omega

theorem cb_count_pos {l : List Nat} {r : Nat} (h : r ∈ l) : 1 ≤ l.count r := List.count_pos_iff.mpr h

/-- **The split's halves are apart as the copy reads them.** -/
theorem halvesApart_split (C : ConsGAt L th p q env sup region g0 g1 nex hed tel gS g2 g3 nq np)
    (G : PremG (Map := Map) L th g0) : HalvesApart hed tel gS.re := by
  have HH := C.halfH G
  have HT := C.halfT G
  have reS := C.reS
  refine ⟨fun r h1 h2 => ?_, fun e he e' he' heq r h1 h2 => ?_, fun e he r h1 h2 => ?_, fun e he r h1 h2 => ?_,
    ⟨fun r hr => ?_, fun e he r hr => ?_⟩, ⟨fun r hr => ?_, fun e he r hr => ?_⟩⟩
  · exact (List.pairwise_append.mp (C.apartAt G g0.bo)).2.2 _ (cb_mem_atL_self _ _ _) _ (cb_mem_atL_self _ _ _)
      r h1 h2
  · refine (List.pairwise_append.mp (C.apartAt G e.1)).2.2 _ (cb_mem_atL_of he _) _ ?_ r h1 h2
    rw [heq]; exact cb_mem_atL_of he' _
  · by_cases hr : g0.re ≤ r
    · have := C.fresh1 G hr
      have a1 := cb_count_pos ((mem_flatten _ _).mpr h1)
      have a2 := cb_count_pos (Raw.mem_regsL.mpr ⟨e, he, h2⟩)
      omega
    · rcases HH.sr r h1 with h | h
      · rcases HT.er e he r h2 with ⟨e0, he0, -, h0⟩ | h'
        · exact G.sa e0 he0 r h0 h
        · omega
      · omega
  · by_cases hr : g0.re ≤ r
    · have := C.fresh1 G hr
      have a1 := cb_count_pos ((mem_flatten _ _).mpr h1)
      have a2 := cb_count_pos (Raw.mem_regsL.mpr ⟨e, he, h2⟩)
      omega
    · rcases HT.sr r h1 with h | h
      · rcases HH.er e he r h2 with ⟨e0, he0, -, h0⟩ | h'
        · exact G.sa e0 he0 r h0 h
        · omega
      · omega
  · rcases HH.sr r hr with h | h
    · have := G.goal.sregs r h; omega
    · omega
  · rcases HH.er e he r hr with ⟨e0, he0, -, h0⟩ | h
    · have := (G.goal.eregs e0 he0).2 r h0; omega
    · omega
  · rcases HT.sr r hr with h | h
    · have := G.goal.sregs r h; omega
    · omega
  · rcases HT.er e he r hr with ⟨e0, he0, -, h0⟩ | h
    · have := (G.goal.eregs e0 he0).2 r h0; omega
    · omega

end Halves

/-! ## The goals of the parts -/

/-- `LabDisj` from apartness at every label. -/
theorem cb_labDisj_of_atL {l : Lazy S}
    (h : ∀ k, (atL (entries l) k).Pairwise fun L L' => ∀ r, NMem L.ned r → ¬ NMem L'.ned r) : LabDisj l := by
  unfold LabDisj
  generalize entries l = es at h ⊢
  induction es with
  | nil => exact List.Pairwise.nil
  | cons e rest ih =>
    refine List.pairwise_cons.mpr ⟨fun e' he' heq r hr hr' => ?_, ih fun k => (h k).sublist (cb_atL_sub e rest k)⟩
    have hk := h e.1
    have e1 : atL (e :: rest) e.1 = e.2.sure :: atL rest e.1 := by simp [atL, List.filter_cons]
    rw [e1, List.pairwise_cons] at hk
    exact hk.1 e'.2.sure (by rw [heq]; exact cb_mem_atL_ent he') r hr hr'

theorem cb_lab_grow {g g' : Gen Map} (Gr : GrowU g g') {k : Nat} (hk : k < g.bo) {B : List Pole} {j : Jmp}
    (hb : HoonMap.get g.blocks k = some ⟨[], B, Termin.hop j⟩) :
    ∃ B', HoonMap.get g'.blocks k = some ⟨[], B', Termin.hop j⟩ := by
  obtain ⟨b', h1, h2, h3⟩ := Gr.keep k _ hk hb
  refine ⟨b'.body, ?_⟩
  rw [h1]
  cases b' with
  | mk par body fin => simp only at h2 h3; subst h2; subst h3; rfl

theorem cb_cond_none {L : Lazy S} {th : Jmp} {g0 : Gen Map} (G : PremG (Map := Map) L th g0) {r : Nat}
    (hr : g0.re ≤ r) : HoonMap.get g0.cond r = Option.none := by
  cases e : HoonMap.get g0.cond r with
  | none => rfl
  | some v => have := G.cb r (by rw [e]; rfl); omega

/-- **A half's goal meets the class's premises** at a later state `g`. -/
theorem cb_premHalf {L h : Lazy S} {th j : Jmp} {g0 g : Gen Map} {hi : Nat} (G : PremG (Map := Map) L th g0)
    (H : HalfOK L g0.re hi h) (hl : ∀ e ∈ entries h, e.1 ∈ (entries L).map Prod.fst) (lu : Raw.LabUniq h)
    (ld : LabDisj h) (sa : SureApart h) (Gr : GrowU g0 g) (hlo : g0.re ≤ hi) (hre : hi ≤ g.re)
    (hj : 1 ≤ j.there ∧ j.there < g.bo) (ta : j.args = [])
    (hcond : ∀ r, r < hi → HoonMap.get g.cond r = HoonMap.get g0.cond r)
    (d : g.drop = false) (cb : CondBelow g) : PremG (Map := Map) h j g := by
  have reg : ∀ r, NMem L.sure.ned r ∨ (g0.re ≤ r ∧ r < hi) → r < g.re ∧ HoonMap.get g.cond r = Option.none := by
    intro r hr
    have hb : r < hi := by
      rcases hr with h | h
      · have := G.goal.sregs r h; omega
      · exact h.2
    refine ⟨by omega, ?_⟩
    rw [hcond r hb]
    rcases hr with h | h
    · exact G.nc r h
    · exact cb_cond_none G h.1
  have ereg : ∀ e ∈ entries h, ∀ r, NMem e.2.sure.ned r → r < g.re ∧ HoonMap.get g.cond r = Option.none := by
    intro e he r hr
    rcases H.er e he r hr with ⟨e0, he0, -, h0⟩ | h
    · have hb : r < hi := by have := (G.goal.eregs e0 he0).2 r h0; omega
      refine ⟨by omega, ?_⟩
      rw [hcond r hb]
      exact G.ec e0 he0 r h0
    · exact reg r (Or.inr h)
  refine ⟨⟨by omega, hj, fun e he => ?_, fun e he => ⟨H.ed e he, fun r hr => (ereg e he r hr).1⟩, ld, H.sd,
    fun r hr => (reg r (H.sr r hr)).1⟩, fun r hr => (reg r (H.sr r hr)).2, fun e he r hr => (ereg e he r hr).2,
    lu, H.sc, H.ec, sa, ta, by omega, d, Gr.up G.up, G.clr.growU Gr, cb⟩
  obtain ⟨e0, he0, e1⟩ := List.mem_map.mp (hl e he)
  obtain ⟨h1, h2, B, th', hb⟩ := G.goal.lab e0 he0
  obtain ⟨B', hb'⟩ := cb_lab_grow Gr h2 hb
  have := Gr.bo
  rw [← e1]
  exact ⟨h1, by omega, B', th', hb'⟩

section Halves2
variable {L : Lazy S} {th : Jmp} {p q : Nomm} {env : CallEnv} {sup : Option Nomm} {region : List Nat}
  {g0 g1 : Gen Map} {nex : NextL S} {hed tel : Lazy S} {gS g2 g3 : Gen Map} {nq np : NextL S}

theorem ConsGAt.labDisjH (C : ConsGAt L th p q env sup region g0 g1 nex hed tel gS g2 g3 nq np)
    (G : PremG (Map := Map) L th g0) : LabDisj hed :=
  cb_labDisj_of_atL fun k => ((List.pairwise_append.mp (C.apartAt G k)).1).sublist (cb_atL_sub _ _ k)

theorem ConsGAt.labDisjT (C : ConsGAt L th p q env sup region g0 g1 nex hed tel gS g2 g3 nq np)
    (G : PremG (Map := Map) L th g0) : LabDisj tel :=
  cb_labDisj_of_atL fun k => ((List.pairwise_append.mp (C.apartAt G k)).2.1).sublist (cb_atL_sub _ _ k)

theorem ConsGAt.sureApartH (C : ConsGAt L th p q env sup region g0 g1 nex hed tel gS g2 g3 nq np)
    (G : PremG (Map := Map) L th g0) : SureApart hed := by
  intro e he r h2 h1
  have HH := C.halfH G
  by_cases hr : g0.re ≤ r
  · have := C.fresh1 G hr
    have a1 := cb_count_pos ((mem_flatten _ _).mpr h1)
    have a2 := cb_count_pos (Raw.mem_regsL.mpr ⟨e, he, h2⟩)
    omega
  · rcases HH.sr r h1 with h | h
    · rcases HH.er e he r h2 with ⟨e0, he0, -, h0⟩ | h'
      · exact G.sa e0 he0 r h0 h
      · omega
    · omega

theorem ConsGAt.sureApartT (C : ConsGAt L th p q env sup region g0 g1 nex hed tel gS g2 g3 nq np)
    (G : PremG (Map := Map) L th g0) : SureApart tel := by
  intro e he r h2 h1
  have HT := C.halfT G
  by_cases hr : g0.re ≤ r
  · have := C.fresh1 G hr
    have a1 := cb_count_pos ((mem_flatten _ _).mpr h1)
    have a2 := cb_count_pos (Raw.mem_regsL.mpr ⟨e, he, h2⟩)
    omega
  · rcases HT.sr r h1 with h | h
    · rcases HT.er e he r h2 with ⟨e0, he0, -, h0⟩ | h'
      · exact G.sa e0 he0 r h0 h
      · omega
    · omega

theorem ConsGAt.condBelowS (C : ConsGAt L th p q env sup region g0 g1 nex hed tel gS g2 g3 nq np)
    (G : PremG (Map := Map) L th g0) : CondBelow gS :=
  CondFresh.below ⟨C.reS, fun k => Or.inl (by rw [C.condS])⟩ G.cb

/-- **`q`'s goal meets the class's premises.** -/
theorem premG_tel (C : ConsGAt L th p q env sup region g0 g1 nex hed tel gS g2 g3 nq np)
    (G : PremG (Map := Map) L th g0) : PremG (Map := Map) tel (jmp0 g0.bo) gS :=
  cb_premHalf G (C.halfT G) C.labT C.lut (C.labDisjT G) (C.sureApartT G) C.growS C.reS (Nat.le_refl _)
    ⟨G.bo, by simp only [jmp0]; rw [C.boS]; omega⟩ rfl (fun r _ => by rw [C.condS]) C.dS (C.condBelowS G)

/-- **`p`'s goal meets the class's premises**, given `q`'s frame and growth. -/
theorem premG_hed (C : ConsGAt L th p q env sup region g0 g1 nex hed tel gS g2 g3 nq np)
    (G : PremG (Map := Map) L th g0) {Qq : Wit}
    (F : FrameG (Map := Map) tel (jmp0 g0.bo) Qq gS g2 nq) (Gq : GrowU gS g2) :
    PremG (Map := Map) hed nq.th g2 := by
  have ta : nq.th.args = [] := by
    rcases F.ent with ⟨_, _, _, a⟩ | e
    · exact a
    · simp only [GoalJ] at e; rw [e]; rfl
  have hre := F.re
  refine cb_premHalf G (C.halfH G) C.labH C.luh (C.labDisjH G) (C.sureApartH G) (C.growS.trans Gq) C.reS F.re
    ⟨F.lo, F.hi⟩ ta (fun r hr => ?_) (F.drop.trans C.dS) (F.cfr.below (C.condBelowS G))
  rcases F.cfr.2 r with e | ⟨h1, _⟩
  · rw [e, C.condS]
  · omega

end Halves2

end Comp
end SkaModel
end Formalization
