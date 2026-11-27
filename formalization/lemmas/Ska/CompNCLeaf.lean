import lemmas.Ska.CompNCSeven

/-!
# The leaves and the indirect call at level `2` of `NC`

README Gaps 12.22, the cases `[0 0]` and `[2 p q]` at level `2` of the
table of `CompNC.lean`.

* `runL_n00_next`, `runOKL_n00`: `[0 0]` under any lazy goal `%next L th`
  (`+bomb`): a new block `bom`, the result the bunt, every goal entry
  consumed with no op (the run has no product, so `FrontL` holds of any
  ops); `lokc_n00`, `lokc_n0all` (`[0 axe]` for every `axe` on every
  `Annot`).
* `lokc_indAU`: the indirect call whose parts meet `UOKC` meets `LOKC` on
  every `Annot` (`lokc_indirectC`, the wrappers by `LOKC.wrap`, the `%bare`
  forms excluded by `bareLitQ`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## `[0 0]` -/

theorem runL_n00_next (L : Lazy S) (th : Jmp) (region : List Nat) (g : Gen Map) :
    (runL (Nomm.n0 0) (CGoalL.next L th) region g : Option (NextL S × Gen Map)) =
      some (⟨ofSure Sure.bunt, jmp0 g.bo⟩, g.emitted ⟨[], [], Termin.bom (some th.there)⟩) := by
  unfold runL
  simp only [if_true, bombL, bind_apply, emit_apply, Option.bind_some, pure_apply]

/-- **`[0 0]` under `%next L th` for any lazy need**: the block of `+bomb`
crashes, so every goal entry is consumed with no op and no product. -/
theorem runOKL_n00 (lib : Lib) {L : Lazy S} {th : Jmp} {g : Gen Map} (b0 : 1 ≤ g.bo) (d0 : g.drop = false)
    (hu : UpBelow g) (hlab : ∀ e ∈ entries L, e.1 < g.bo) (W : Noun → Noun) :
    RunOKL (Map := Map) lib (Nomm.n0 0) L th (fun _ => Need.none) W g
      (g.emitted ⟨[], [], Termin.bom (some th.there)⟩) ⟨ofSure Sure.bunt, jmp0 g.bo⟩ := by
  have e0 : entries (ofSure (Sure.bunt : Sure S)) = [] := entries_ofSure _
  have nb : ∀ r, ¬ NMem (Sure.bunt : Sure S).ned r := fun r hr => by simp [Sure.bunt, NMem] at hr
  have pe : ∀ s, pureEval (Nomm.n0 0) s = Option.none := pureEval_n00
  have hb : HoonMap.get (g.emitted ⟨[], [], Termin.bom (some th.there)⟩).blocks g.bo =
      some ⟨[], [], Termin.bom (some th.there)⟩ := by
    simp [Gen.emitted, d0, HoonMap.get_put]
  refine ⟨by simp [Gen.emitted], by simp [Gen.emitted], rfl, fun o ho _ => (ext_emit g _).2.2.2 o ho,
    (grow_emit (fun j hj => by simp [finJumps] at hj)).toU hu, condFresh_of_eq (by simp [Gen.emitted]) rfl,
    by simp [jmp0]; omega, by simp [jmp0, Gen.emitted], Or.inl ⟨_, hb, rfl, rfl⟩,
    fun r hr => absurd hr (nb r), by simp [ofSure, Sure.bunt, Distinct],
    fun e he => (by rw [e0] at he; cases he), fun e he => (by rw [e0] at he; cases he), (by rw [e0]; simp),
    (by rw [e0]; simp), fun _ r hr => hr.elim, fun s hs => absurd (fitsS_bunt s) hs,
    fun r hr => absurd hr (nb r), fun e he => (by rw [e0] at he; cases he), fun e he => ?_, ?_⟩
  · refine ⟨[], fun B fin hbl => by rw [(ext_emit g _).2.2.2 e.1 (hlab e he)]; simpa using hbl,
      fun cf _ => Or.inr ⟨by rw [e0]; simp, fun lib σ O c gul st t ned A s0 s v _ hev _ => ?_⟩⟩
    rw [pe] at hev; cases hev
  · intro cf hcf c ned σ O st t gul s0 s ag hned regs hh hn
    show GoalSemD lib O c gul st _ regs t (jmp0 g.bo) L.sure th Need.none (W s) (pureEval (Nomm.n0 0) s)
    rw [pe]
    have hc : HoonMap.get c.blocks g.bo = some ⟨[], [], Termin.bom (some th.there)⟩ := by
      rw [ag.1 g.bo (Nat.le_refl _) (by simp [Gen.emitted]) (by rw [e0]; simp), hb]
      simp [unproxyBlob, renBlob, renFin]
    simp only [GoalSemD]
    rw [goJ_jmp0 _ _ _ _ hc, execBlob_bom']

/-- **`[0 0]` meets `LOKC`** for a formula whose `+mink` is its value (a
crash). -/
theorem lokc_n00 (lib : Lib) (env : CallEnv) {P : Noun → Prop} {f : Noun}
    (M : MinkEq lib P f (Nomm.n0 0)) : LOKC (S := S) (Map := Map) lib env P f (Nomm.n0 0) := by
  refine ⟨fun {sup L th region g0 g1 nex} hc h => ?_, fun {sup L th region g0 g1 nex} _ b0 d0 hu _ _ h1 h2 _ hd hsl
    hlab hnd hed h => ?_⟩
  · rw [runLC_eq env _ rfl, runL_n00_next] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    trivial
  · rw [runLC_eq env _ rfl, runL_n00_next] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨⟨_, (runOKL_n00 (Map := Map) lib b0 d0 hu (fun e he => (hlab e he).1) (fun _ => A 0)).toLC M⟩,
      Or.inr (Nat.le_refl _)⟩

/-- **`[0 axe]` meets `LOKC` on every `Annot`, for every `axe`.** -/
theorem lokc_n0all {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) (env : CallEnv) {axe : Nat}
    {P : Noun → Prop} {f : Noun} (hA : Annot lib code P f (Nomm.n0 axe)) :
    LOKC (S := S) (Map := Map) lib env P f (Nomm.n0 axe) := by
  rcases Nat.eq_zero_or_pos axe with rfl | ha
  · exact lokc_n00 lib env (fun s hs gul tm r => mink_pure hok rfl hA hs gul tm r)
  · exact lokc_n0A hok env ha hA

/-! ## The indirect call -/

/-- **The indirect call whose parts meet `UOKC` meets `LOKC` on every
`Annot`**: `Annot.indirect` gives `lokc_indirectC` with `minkC2_indirect`,
the wrappers `LOKC.wrap`, the `%bare` forms are excluded. -/
theorem lokc_indAU {lib : Lib} {code : Bell → Option Nomm} (env : CallEnv) {p q : Nomm}
    (ihp : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f p → UOKC (S := S) (Map := Map) lib env P f p)
    (ihq : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f q → UOKC (S := S) (Map := Map) lib env P f q)
    (hbl : bareLitQ q = false) {P : Noun → Prop} {f : Noun} {nm : Nomm} (hA : Annot lib code P f nm) :
    nm = Nomm.n2 p q Option.none → LOKC (S := S) (Map := Map) lib env P f nm := by
  induction hA with
  | indirect hb hc _ _ =>
    intro e
    cases e
    exact lokc_indirectC lib env (ihp hb) (ihq hc) (minkC2_indirect lib _ _ _)
  | bare hf => intro e; cases e; simp [bareLitQ, hf] at hbl
  | bareLit hf _ => intro e; cases e; simp [bareLitQ, hf] at hbl
  | memo hm _ ih' => intro e; exact LOKC.wrap (wrapRel_memo hm) (ih' e)
  | six0 hb' _ ih' => intro e; exact LOKC.wrap (wrapRel_six hb' (Or.inl ⟨rfl, rfl⟩)) (ih' e)
  | six1 hb' _ ih' => intro e; exact LOKC.wrap (wrapRel_six hb' (Or.inr ⟨rfl, rfl⟩)) (ih' e)
  | cons => intro e; cases e
  | n0 => intro e; cases e
  | n1 => intro e; cases e
  | direct => intro e; cases e
  | inline => intro e; cases e
  | n3 => intro e; cases e
  | n4 => intro e; cases e
  | n5 => intro e; cases e
  | n6 => intro e; cases e
  | n7 => intro e; cases e
  | n8 => intro e; cases e
  | n9 => intro e; cases e
  | n10 => intro e; cases e
  | n11s => intro e; cases e
  | n11d => intro e; cases e
  | n11c => intro e; cases e
  | mean => intro e; cases e
  | n12 => intro e; cases e
  | crash => intro e; cases e
  | fold => intro e; cases e
  | n8g => intro e; cases e
  | n8l => intro e; cases e

/-! ## `[4 p]` with a call-free `p` at level `1` -/

/-- **`[4 p]` with `p` in `FragX` meets `LOKCS`**: under a goal whose sure
part asks nothing the increment writes a fresh register, which
`+collapse-lazy-atom` reads at every entry (`runOKL_n4_none`). -/
theorem lokcs_n4X (lib : Lib) (env : CallEnv) {p : Nomm} (hp : FragX (S := S) p) {P : Noun → Prop} {f : Noun}
    (M : MinkEq lib P f (Nomm.n4 p)) : LOKCS (S := S) (Map := Map) lib env P f (Nomm.n4 p) := by
  have pp : (Nomm.n4 p).pure = true := by simpa [Nomm.pure] using fragX_pure hp
  refine ⟨fun {sup L th region g0 g1 nex} hc h => ?_, fun {sup L th region g0 g1 nex} hs ht hc b0 d0 hu hcl hcb h1 h2
    ha hsd hsl hlab hnd hed h => ?_⟩
  · rw [runLC_eq env _ (Nomm.noCall_of_pure _ pp)] at h
    exact clean_n4L (runX_clean hp) h
  · rw [runLC_eq env _ (Nomm.noCall_of_pure _ pp)] at h
    obtain ⟨d, R⟩ := runOKL_n4_none lib (runX_ok lib hp).2.1 (runX_semR lib hp).2.1 (runX_keeps hp)
      (aboveX_of_fragX hp) h hc b0 d0 hu hcl h1 h2 hs hcb (List.nodup_cons.mpr ⟨ht, hnd⟩)
      (fun e he => ⟨(hlab e he).1, by obtain ⟨th', hb⟩ := (hlab e he).2; exact ⟨[], _, hb⟩⟩)
      (fun e he x hx => (hed e he).2 x hx)
    exact ⟨_, R.toLC M⟩

/-- **`[4 p]` with `p` in `FragX` meets `LOKCS` on every `Annot`.** -/
theorem lokcs_n4XA {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) (env : CallEnv) {p : Nomm}
    (hp : FragX (S := S) p) {P : Noun → Prop} {f : Noun} (hA : Annot lib code P f (Nomm.n4 p)) :
    LOKCS (S := S) (Map := Map) lib env P f (Nomm.n4 p) :=
  lokcs_n4X lib env hp (fun s hs gul tm r => mink_pure hok (by simpa [Nomm.pure] using fragX_pure hp) hA hs gul tm r)

end Comp
end SkaModel
end Formalization
