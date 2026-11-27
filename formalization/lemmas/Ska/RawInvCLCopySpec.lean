import lemmas.Ska.RawInvCLCopyMerge

/-!
# The run-level liveness with calls: the liveness half of `+copy`

README Gaps 14 (b), track D.  The `LiveC` half of `CopySpecL`
(`RawInvCLCopy.lean`) from the structure of the merge (`mr_copyLazyL`).

* `liveK_prepK_rd`: `liveK_prepK` when the ops in front read only
  registers killed at their block: no register escapes into the ops.
* **`copyL_live`**: a register live at the merged entry (the hop block `o`
  with the moves in front), the merged tree killing its needs, is live at
  `first.th.there` before the copy with the outer kills, those of
  `second`'s tree entered at `s2` and those of `first`'s tree.  It needs
  `IL` of both goals and `LabUniq second`, not `TreesApart`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **Ops in front that read only killed registers** leave a register live
after them live before them, the definitions of the ops added as kills. -/
theorem liveK_prepK_rd {P : Nat → List Pole} {bl bl' : Map Blob} (hP : Prep P bl bl') {K : Nat → Nat → Prop}
    (hR : ∀ k y, OpsRF (P k) y → K k y) {k r : Nat} (h : LiveK bl' K k r) :
    LiveK bl (fun x y => K x y ∨ y ∈ defsOf (P x)) k r := by
  induction h with
  | here hb hr hk =>
    rw [hP] at hb
    obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp hb
    rcases blockRF_pre hr with h | ⟨hd, h⟩
    · exact absurd (hR _ _ h) hk
    · exact LiveK.here h0 h fun hk' => hk'.elim hk hd
  | next hb hj _ hd hk ih =>
    rw [hP] at hb
    obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp hb
    exact LiveK.next h0 hj ih (fun hm => hd (mem_blockDefs_pre.mpr (Or.inl hm)))
      fun hk' => hk'.elim hk fun h' => hd (mem_blockDefs_pre.mpr (Or.inr h'))

theorem unproxy_none {cond : Map (Nat × List Nat)} {y : Nat} (h : HoonMap.get cond y = Option.none) :
    unproxy cond y = y := by
  unfold unproxy; rw [h]

/-- **The liveness half of `+copy`.** -/
theorem copyL_live {K : Nat → Nat → Prop} {first : NextL S} {second : Lazy S} {s2 : Nat} {g g' : Comp.Gen Map}
    {nex : NextL S} (hI : IL K first.goal g) (hII : IL K (CGoalL.next second (jmp0 s2)) g) (hU : LabUniq second)
    (h : copyL first second g = some (nex, g')) (r : Nat)
    (hl : LiveK (unpM g') (fun x y => K x y ∨ lazK nex.th.there nex.laz x y) nex.th.there r) :
    LiveK (unpM g) (fun x y => (K x y ∨ lazK s2 second x y) ∨ lazK first.th.there first.laz x y)
      first.th.there r := by
  have hd : g.drop = false := hI.ats.1
  have hG : GoalL g (CGoalL.next first.laz first.th) := hI.goal
  obtain ⟨⟨bt, hbt, -, targs⟩, -, -⟩ := hG
  unfold copyL at h
  obtain ⟨o, g1, h1, h⟩ := bind_some h
  rw [emit_apply] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  obtain ⟨laz, g2, h2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hd1 : (g.emitted ⟨[], [], Termin.hop first.th⟩).drop = false := hd
  let Src : Nat × Lazy S → Prop := fun e => e ∈ ((g.bo, first.laz) :: entries first.laz) ++
    ((g.bo, second) :: entries second)
  obtain ⟨P, M⟩ := mr_copyLazyL Src g.bo first.laz second _ g2 laz h2 hd1
    (fun e he => List.mem_append_left _ he) (fun e he => List.mem_append_right _ he) hU
  -- registers of the sources and fresh ones are no keys
  have hnk : ∀ y, ((∃ e, Src e ∧ NMem e.2.sure.ned y) ∨ g.re ≤ y) → HoonMap.get g.cond y = Option.none := by
    intro y hy
    cases e : HoonMap.get g.cond y with
    | none => rfl
    | some v =>
      exfalso
      rcases hy with ⟨e', he', hm⟩ | hy
      · rcases List.mem_append.mp he' with he' | he'
        · refine (hI.cond y v e).2.2.1 ⟨(first.th.there, first.laz), ?_, ?_⟩
          · exact List.mem_cons_self
          · rcases List.mem_cons.mp he' with rfl | he'
            · exact hm
            · exact absurd ⟨e', List.mem_cons_of_mem _ he', hm⟩ (hI.cond y v e).2.2.1
        · refine (hII.cond y v e).2.2.1 ⟨(s2, second), List.mem_cons_self, ?_⟩
          rcases List.mem_cons.mp he' with rfl | he'
          · exact hm
          · exact absurd ⟨e', List.mem_cons_of_mem _ he', hm⟩ (hII.cond y v e).2.2.1
      · have := (hI.cond y v e).1; omega
  have hcond : g2.cond = g.cond := M.cond
  let u := unproxy g.cond
  have hP' : Prep (fun k => (P k).map (renPole u)) (unpM (g.emitted ⟨[], [], Termin.hop first.th⟩)) (unpM g2) := by
    have := prep_mapVals M.prep u
    unfold unpM; rw [hcond]; exact this
  -- the ops read only registers of the merged tree, killed at their block
  have hR : ∀ k y, OpsRF ((P k).map (renPole u)) y → (fun x y => K x y ∨ lazK g.bo laz x y) k y := by
    intro k y hy
    obtain ⟨x, hx, hrf⟩ := opsRF_ren_back _ hy
    obtain ⟨op, hop, hxr⟩ := opsRF_mem hrf
    have hlk := M.rd k op hop x hxr
    obtain ⟨e, he, ek, hm⟩ := hlk
    have hfix : u x = x := by
      apply unproxy_none
      apply hnk
      rcases (M.ent e he).2 x hm with ⟨e', hs, -, hm'⟩ | hf
      · exact Or.inl ⟨e', hs, hm'⟩
      · exact Or.inr hf.1
    rw [hfix] at hx
    subst hx
    exact Or.inr ⟨e, he, ek, hm⟩
  have hl1 := liveK_prepK_rd hP' hR hl
  -- the hop block `o`
  have hself := unpM_emitted_self hd ⟨[], [], Termin.hop first.th⟩
  have hdef : ∀ k y, y ∈ defsOf (P k) → HoonMap.get g.cond y = Option.none → y ∈ defsOf ((P k).map (renPole u)) :=
    fun k y hy hc => by rw [defsOf_ren]; exact List.mem_map.mpr ⟨y, hy, unproxy_none hc⟩
  cases hl1 with
  | here hb' hr _ =>
    have e := hself.symm.trans hb'
    cases e
    obtain ⟨-, hr | ⟨-, hr⟩⟩ := hr
    · simp [renBlob, OpsRF] at hr
    · simp [renBlob, renFin, finRegs, jmpRegs, renJmp_nil _ targs, targs] at hr
  | next hb' hj hl' _ hk =>
    have e := hself.symm.trans hb'
    cases e
    simp only [renBlob, renFin, getJmps, renJmp_nil _ targs, List.mem_singleton] at hj
    subst hj
    have hl2 := (liveK_frameP hI.downU (fun x hx => unpM_emitted_lt hd _ hx) (hI.lab hbt)).mp hl'
    -- a root register is no kill at `first.th.there`: it is killed or defined at `o`
    have hroot : ∀ (l : Lazy S), (g.bo, l) ∈ ((g.bo, first.laz) :: entries first.laz) ++
        ((g.bo, second) :: entries second) → NMem l.sure.ned r → False := by
      intro l hl hm
      have hc : HoonMap.get g.cond r = Option.none := hnk r (Or.inl ⟨(g.bo, l), hl, hm⟩)
      rcases M.cov _ hl r hm with h | h
      · exact hk (Or.inr (hdef _ _ h hc))
      · exact hk (Or.inl (Or.inr h))
    refine hl2.mono_r fun x hx => ?_
    have hent : ∀ e ∈ ((g.bo, first.laz) :: entries first.laz) ++ ((g.bo, second) :: entries second),
        e.1 = x → NMem e.2.sure.ned r → (fun x y => (K x y ∨ lazK g.bo laz x y) ∨ y ∈ defsOf ((P x).map (renPole u))) x r := by
      intro e he ex hm
      have hc : HoonMap.get g.cond r = Option.none := hnk r (Or.inl ⟨e, he, hm⟩)
      rcases M.cov e he r hm with h | h
      · rw [ex] at h; exact Or.inr (hdef _ _ h hc)
      · rw [ex] at h; exact Or.inl (Or.inr h)
    rcases hx with (hx | ⟨e, he, ex, hm⟩) | ⟨e, he, ex, hm⟩
    · exact Or.inl (Or.inl hx)
    · rcases List.mem_cons.mp he with rfl | he
      · exact (hroot second (List.mem_append_right _ List.mem_cons_self) hm).elim
      · exact hent e (List.mem_append_right _ (List.mem_cons_of_mem _ he)) ex hm
    · rcases List.mem_cons.mp he with rfl | he
      · exact (hroot first.laz (List.mem_append_left _ List.mem_cons_self) hm).elim
      · exact hent e (List.mem_append_left _ (List.mem_cons_of_mem _ he)) ex hm

end Raw
end SkaModel
end Formalization
