import lemmas.Ska.RawInvXup
import lemmas.Ska.RawInvCoerceP
import lemmas.Ska.RawInvTopX
import lemmas.Ska.RawInvTop

/-!
# Raw `+comp` output on `FragX`: the final pass

README Gaps 14, track D, step 3 of the class `FragX`.  The run-level
invariant (`runX_rawIHX` for `Xup`), the prologues of `+coerce-lazy` and
`optIn_toStraight_prep` put together.

* `coerceList_prepI`, `coerceLazyL_prepI`: `coerceList_prep` and
  `coerceLazyL_prep` with an invariant of the entries still to do (the step
  at one entry may use what holds of that entry and of the later ones).
* `CoI`: that invariant (`SIP`, the input need below `R` and not defined,
  the entries still to do have a block, distinct sure needs below `R`,
  apart from the input need, apart from each other and not defined), and
  **`coI_step`**: `raw_coerceP` at one entry keeps it and is a
  `CoerceStep`.
* `LazOK bl o laz`: the sure needs of the root and of the entries of a lazy
  tree are pairwise disjoint (`NeedsApart`) and the blocks `bl` define none
  of their registers.  Checked on the 4,080 nomms of `enumX` (and under
  `%next`), not yet proved of the run.
* **`optIn_finishLFX_of`**: `OptIn` of the raw blocks of `finishLF` for
  every nomm of `FragX` with at most 255 `%6`, nothing baked, given `LazOK`
  of the top run's result; **`optimize_keeps_finishLFX_of`**.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## `+coerce-lazy` with an invariant of the entries still to do -/

theorem coerceList_prepI {ned : Need} {less : Cape} (I : List (Nat × Comp.Lazy S) → Comp.Gen Map → Prop)
    (step : ∀ o (l : Comp.Lazy S) rest g g' u, I ((o, l) :: rest) g →
      Comp.coerceLazy ned o l.sure less g = some (u, g') → I rest g' ∧ CoerceStep ned g g' o l) :
    ∀ (es : List (Nat × Comp.Lazy S)) (g g' : Comp.Gen Map), I es g →
      Comp.coerceList ned less es g = some ((), g') → I [] g' ∧ CoerceMany ned g g' es
  | [], g, g', hI, h => by
    simp only [Comp.coerceList, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact ⟨hI, fun _ => [], prep_nil _, fun e he => absurd he (List.not_mem_nil), fun _ _ h => h.elim,
      fun _ _ h => absurd h (List.not_mem_nil)⟩
  | (o, l) :: rest, g, g', hI, h => by
    simp only [Comp.coerceList] at h
    obtain ⟨u, g1, h1, h2⟩ := bind_some h
    obtain ⟨I1, A, pA, kA, rA, tA⟩ := step o l rest g g1 u hI h1
    obtain ⟨I2, Q, pQ, kQ, rQ, tQ⟩ := coerceList_prepI I step rest g1 g' I1 h2
    refine ⟨I2, _, prep_trans pA pQ, fun e he r hr => ?_, fun k r hr => ?_, fun k op hop => ?_⟩
    · rw [defsOf_append, List.mem_append]
      rcases List.mem_cons.mp he with rfl | he
      · exact Or.inr (by simp only [if_pos rfl]; exact kA r hr)
      · exact Or.inl (kQ e he r hr)
    · rcases opsRF_append.mp hr with h | ⟨-, h⟩
      · exact rQ k r h
      · by_cases e : k = o
        · rw [if_pos e] at h; exact rA r h
        · rw [if_neg e] at h; exact h.elim
    · rcases List.mem_append.mp hop with h | h
      · exact tQ k op h
      · by_cases e : k = o
        · rw [if_pos e] at h; exact tA op h
        · rw [if_neg e] at h; exact absurd h (List.not_mem_nil)

theorem coerceLazyL_prepI {ned : Need} {less : Cape} (I : List (Nat × Comp.Lazy S) → Comp.Gen Map → Prop)
    (step : ∀ o (l : Comp.Lazy S) rest g g' u, I ((o, l) :: rest) g →
      Comp.coerceLazy ned o l.sure less g = some (u, g') → I rest g' ∧ CoerceStep ned g g' o l)
    {o : Nat} {laz : Comp.Lazy S} {g g' : Comp.Gen Map} (hI : I ((o, laz) :: Comp.entries laz) g)
    (h : Comp.coerceLazyL ned less o laz g = some ((), g')) :
    I [] g' ∧ CoerceMany ned g g' ((o, laz) :: Comp.entries laz) := by
  rw [Comp.coerceLazyL_flat] at h
  have h' : (Comp.coerceList ned less ((o, laz) :: Comp.entries laz) : Comp.CM Map Unit) g = some ((), g') := by
    simp only [Comp.coerceList]; exact h
  exact coerceList_prepI I step _ g g' hI h'

/-! ## The invariant of the iteration -/

/-- The sure needs of the entries `es` are pairwise disjoint. -/
def NeedsApart (es : List (Nat × Comp.Lazy S)) : Prop :=
  es.Pairwise fun e e' => ∀ r, NMem e.2.sure.ned r → ¬ NMem e'.2.sure.ned r

/-- What the iteration of `+coerce-lazy` keeps, with the entries `rest`
still to do and the input need `ned`. -/
def CoI (X : Map Blob → Prop) (ρ : Nat → Nat) (lo : Nat) (ned : Need) (R : Nat) (rest : List (Nat × Comp.Lazy S))
    (g : Comp.Gen Map) : Prop :=
  SIP X ρ lo g ∧ R ≤ g.re ∧ (∀ r, NMem ned r → r < R ∧ ¬ Defd g.blocks r) ∧ NeedsApart rest ∧
    ∀ e ∈ rest, (∃ b, HoonMap.get g.blocks e.1 = some b) ∧ Distinct e.2.sure.ned ∧
      ∀ r, NMem e.2.sure.ned r → r < R ∧ ¬ NMem ned r ∧ ¬ Defd g.blocks r

/-- **One step of `+coerce-lazy` keeps `CoI` and is a `CoerceStep`.** -/
theorem coI_step {X : Map Blob → Prop} [XOK X] {ρ : Nat → Nat} {lo : Nat} {ned : Need} {R : Nat} {less : Cape}
    {o : Nat} {l : Comp.Lazy S} {rest : List (Nat × Comp.Lazy S)} {g g' : Comp.Gen Map} {u : Unit}
    (hI : CoI X ρ lo ned R ((o, l) :: rest) g) (h : Comp.coerceLazy ned o l.sure less g = some (u, g')) :
    CoI X ρ lo ned R rest g' ∧ CoerceStep ned g g' o l := by
  obtain ⟨S0, hR, hn, hap, he⟩ := hI
  obtain ⟨⟨b, hb⟩, dl, hl⟩ := he (o, l) List.mem_cons_self
  have hap' := List.pairwise_cons.mp hap
  obtain ⟨S1, -, le1, A, get1, rf1, cv1, df1⟩ := raw_coerceP S0 hb
    (fun y hy => by have := (hn y hy).1; omega) dl (fun y hy => by have := (hl y hy).1; omega)
    (fun y hy e => (hl y e).2.1 hy) (fun y hy => (hl y hy).2.2) h
  have dd : ∀ y, Defd g'.blocks y ↔ Defd g.blocks y ∨ y ∈ defsOf A := fun y => defd_of_ifget hb get1
  have pr : Prep (fun k => if k = o then A else []) g.blocks g'.blocks := fun k => by
    rw [get1 k]
    by_cases e : k = o
    · subst e; simp [hb]
    · simp only [if_neg e]; cases HoonMap.get g.blocks k <;> simp [pre_nil]
  have newd : ∀ y, y ∈ defsOf A → NMem l.sure.ned y ∨ g.re ≤ y := fun y hy => (df1 y hy).imp id (·.1)
  refine ⟨⟨S1, by omega, fun r hr => ⟨(hn r hr).1, fun d => ?_⟩, hap'.2, fun e he' => ?_⟩, A, pr, cv1, rf1, ?_⟩
  · rcases (dd r).mp d with d | d
    · exact (hn r hr).2 d
    · rcases newd r d with e | e
      · exact (hl r e).2.1 hr
      · have := (hn r hr).1; omega
  · obtain ⟨⟨b', hb'⟩, de, hle⟩ := he e (List.mem_cons_of_mem _ he')
    refine ⟨?_, de, fun r hr => ⟨(hle r hr).1, (hle r hr).2.1, fun d => ?_⟩⟩
    · by_cases eo : e.1 = o
      · exact ⟨_, by rw [get1, if_pos eo]⟩
      · exact ⟨b', by rw [get1, if_neg eo]; exact hb'⟩
    · rcases (dd r).mp d with d | d
      · exact (hle r hr).2.2 d
      · rcases newd r d with e' | e'
        · exact hap'.1 e he' r e' hr
        · have := (hle r hr).1; omega
  · intro op hop
    exact S1.tr o _ (by rw [get1, if_pos rfl]) op (List.mem_append.mpr (Or.inl hop))

/-! ## The final pass -/

/-- **What `optIn_finishLFX_of` asks of the run**: the sure needs of the root
and of the entries of the lazy tree are pairwise disjoint, and the blocks
define none of their registers. -/
def LazOK (bl : Map Blob) (o : Nat) (laz : Comp.Lazy S) : Prop :=
  NeedsApart ((o, laz) :: Comp.entries laz) ∧
    ∀ e ∈ (o, laz) :: Comp.entries laz, ∀ r, NMem e.2.sure.ned r → ¬ Defd bl r

theorem sip_gen0X : SIP (Xup (Map := Map)) (upRk (gen0 : Comp.Gen Map).blocks) (gen0 : Comp.Gen Map).bo gen0 := by
  have e : ∀ k, HoonMap.get (gen0 : Comp.Gen Map).blocks k = Option.none := fun k => by
    simp [gen0, HoonMap.get_empty]
  have r : ∀ k, upRk (gen0 : Comp.Gen Map).blocks k = 3 * k := fun k => by unfold upRk; rw [e k]
  have b1 : (gen0 : Comp.Gen Map).bo = 1 := by simp [gen0]
  refine ⟨rfl, by omega, fun k b hb => ?_, fun k b hb => ?_, fun k b hb => ?_, fun k k' b b' r' hb => ?_,
    fun k b hb => ?_, fun k b hb => ?_, Nat.le_refl _, fun k _ => r k, fun x hx => ?_,
    ⟨fun z bz y b j r' x hz => ?_, fun k b hb => ?_, fun y b j r' hy => ?_⟩⟩
  all_goals first
    | (rw [e] at hb; cases hb)
    | (rw [e] at hz; cases hz)
    | (rw [e] at hy; cases hy)
    | skip
  rw [r]; omega

variable [MapKeys Map]

/-- **`OptIn` of the n-ary final pass on `FragX`**, given `LazOK` of the top
run's result. -/
theorem optIn_finishLFX_of {nm : Nomm} (hf : FragX (S := S) nm) (hc : sixCount nm ≤ 255)
    (hlz : ∀ nex g1, runL nm (CGoalL.done : CGoalL S) [] (gen0 : Comp.Gen Map) = some (nex, g1) →
      LazOK g1.blocks nex.th.there nex.laz)
    {ord : NeedOrd} {less : Cape} {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, []))
    {c' : Straight Map} (h : finishLF (S := S) (Map := Map) nm ord less bake = some c') : OptIn c'.blocks := by
  have O : ∀ {nex : NextL S} {g1 : Comp.Gen Map},
      runL nm (CGoalL.done : CGoalL S) [] (gen0 : Comp.Gen Map) = some (nex, g1) →
      RunOKP (Map := Map) lib0 nm (CGoal.done : CGoal S) gen0 g1 nex :=
    fun h1 => (runX_ok lib0 hf).1 trivial trivial hc (by simp [gen0]) rfl upBelow_gen0 h1
  rw [finishLF_eq hbake (fun _ _ h1 => (O h1).cnd)] at h
  unfold finishL at h
  obtain ⟨⟨nex, g1⟩, h1, hA⟩ := Option.bind_eq_some_iff.mp h
  simp only at hA
  split at hA
  · cases hA
  obtain ⟨⟨nedF, g2⟩, h2, hB⟩ := Option.bind_eq_some_iff.mp hA
  rw [hbake] at hB
  simp only [List.map_nil] at hB
  obtain ⟨⟨u3, g3⟩, h3, hC⟩ := Option.bind_eq_some_iff.mp hB
  obtain ⟨⟨u4, g4⟩, h4, hT⟩ := Option.bind_eq_some_iff.mp hC
  have R := O h1
  obtain ⟨LA, LD⟩ := hlz nex g1 h1
  -- the run
  obtain ⟨S1, -, -, -, L1⟩ := runX_rawIHX_up (S := S) (Map := Map) hf CGoal.done [] gen0 g1 nex (fun _ _ => False)
    (KVan.none _) sip_gen0X trivial trivial trivial trivial (fun _ _ e => e) hc trivial h1
  have hl : ∀ r, ¬ LiveK g1.blocks (lazK nex.th.there nex.laz) nex.th.there r := fun r hl' =>
    L1 r (hl'.mono fun x y h => h.elim False.elim id)
  have haa : ArgsAboveR (upRk g1.blocks) g1.blocks := argsAboveR_upRk_of_xup S1.x
  have hrk : DownRk (upRk g1.blocks) g1.blocks :=
    downRk_of_growU R.grow (fun k => by simp [gen0, HoonMap.get_empty]) (by simp [gen0])
  -- the input need
  obtain ⟨⟨k2, e2⟩, l2, -, mF⟩ := needOrdAllocRegs_spec ord g1 g2 nedF h2
  subst e2
  have l2' : g1.re ≤ k2 := l2
  -- `+coerce-lazy`
  have I0 : CoI (Xup (Map := Map)) (upRk g1.blocks) g1.bo nedF k2 ((nex.th.there, nex.laz) :: entries nex.laz)
      { g1 with re := k2 } := by
    refine ⟨sip_reg S1 l2, Nat.le_refl _, fun r hr => ⟨(mF r hr).2, fun d => ?_⟩, LA, fun e he => ?_⟩
    · have := S1.defd_lt d; have := (mF r hr).1; omega
    · have rg : ∀ r, NMem e.2.sure.ned r → r < g1.re := fun r hr => by
        rcases List.mem_cons.mp he with rfl | he'
        · exact (R.regs r hr).2
        · exact ((R.eregs e he').2 r hr).2
      refine ⟨?_, ?_, fun r hr => ⟨by have := rg r hr; omega, fun m => ?_, LD e he r hr⟩⟩
      · rcases List.mem_cons.mp he with rfl | he'
        · rcases R.ent with ⟨b, hb, -, -⟩ | hj
          · exact ⟨b, hb⟩
          · exact hj.elim
        · obtain ⟨-, -, th, hb⟩ := R.labs e he'
          exact ⟨_, hb⟩
      · rcases List.mem_cons.mp he with rfl | he'
        · exact R.dist
        · exact (R.eregs e he').1
      · have := rg r hr; have := (mF r m).1; omega
  obtain ⟨I3, P, pP, kP, rP, -⟩ := coerceLazyL_prepI (S := S) (Map := Map)
    (CoI (Xup (Map := Map)) (upRk g1.blocks) g1.bo nedF k2)
    (fun _ _ _ _ _ _ hI hs => coI_step hI hs) I0 h3
  -- the empty bake
  obtain ⟨S4, b4, hb4, e4, -, -⟩ := sip_addOps I3.1 (opsOK_nil g3) h4
  have get4 : ∀ k, HoonMap.get g4.blocks k = HoonMap.get g3.blocks k := fun k => by
    rw [e4]
    by_cases e : k = nex.th.there
    · subst e; rw [get_put_self, hb4, pre_nil]
    · rw [get_put_ne e]
  have pP4 : Prep P g1.blocks g4.blocks := fun k => by rw [get4 k]; exact pP k
  exact optIn_toStraight_prep (K := lazK nex.th.there nex.laz) pP4 hrk haa
    (fun k r hk => by obtain ⟨e, he, rfl, hr⟩ := hk; exact kP e he r hr) hl S4.nd S4.cr S4.tr rP
    (fun r hr d => (I3.2.2.1 r hr).2 (by
      obtain ⟨o, b, hb, m⟩ := defd_iff.mp d
      exact defd_iff.mpr ⟨o, b, by rw [← get4]; exact hb, m⟩)) hT

/-- **`+optimize` keeps the n-ary code of `FragX`**, given `LazOK` of the
top run's result. -/
theorem optimize_keeps_finishLFX_of (M : Type → Type → Type) [Ana.Treap M] {fuel sfuel : Nat}
    {nm : Nomm} (hf : FragX (S := S) nm) (hc : sixCount nm ≤ 255)
    (hlz : ∀ nex g1, runL nm (CGoalL.done : CGoalL S) [] (gen0 : Comp.Gen Map) = some (nex, g1) →
      LazOK g1.blocks nex.th.there nex.laz)
    {ord : NeedOrd} {less : Cape} {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, []))
    {c' s' : Straight Map} (h : finishLF (S := S) (Map := Map) nm ord less bake = some c')
    (ho : optimizeF fuel ⟨aliasM (Ana.pickR M), trimTraceHints, switchChains sfuel⟩ c' = some s') : Opt.Keeps c' s' :=
  optimize_keeps_optIn M (optIn_finishLFX_of hf hc hlz hbake h) ho

end Raw
end SkaModel
end Formalization
