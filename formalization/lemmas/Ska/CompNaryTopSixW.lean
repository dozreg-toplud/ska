import lemmas.Ska.CompNaryTop
import lemmas.Ska.CompSixLSWrap

/-!
# The n-ary top of a `%6`: `finishLFC_contractGBW`

README Gaps 18.16, step 2.  A `%6` under `%done` never meets `DoneOK` (its
result is never flat), and with a calling test `+past-fork` wraps each
branch's need in a bond at the fork's own label, so the labels of the
entries repeat (`CompSixLSWrap.lean`).  Track C's top reads `+kerf` of the
wrapped need as `+kerf` of the unwrapped one (`WalkEq`).  The n-ary top
walks the need with `+coerce-lazy` instead, which visits the bonds before
the forks (`walkLazy` visits the forks first), so `WalkEq` does not say
enough.  Here:

* `walkLazyB` (`+walk-lazy` in the order of `+coerce-lazy`: the sure need,
  the bonds, the forks), `coerceLazyL_walkB` (`+coerce-lazy` is that walk of
  `coerceLazy`), `WalkEqB` and its lemmas (`walkLazyB_wrap`,
  `walkEqB_six`), the text of track C's for this order.
* `coerceLazy_bunt`: `+coerce-lazy` does nothing at a `bunt` sure need when
  the final need is not one register (`Need.this r` would add `[]` to the
  block, a new map), `needOrdAllocRegs_notThis`.
* `finishLFC_contractGBW`: the n-ary contract from `RunOKGB` of an unwrapped
  result `nexU`, walked alike by `walkLazyB`, whose jump is no lazy entry
  (`DoneOK.nent`'s clause), for a need `ord ≠ this`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The walk in the order of `+coerce-lazy` -/

mutual
/-- `+walk-lazy` with the bonds before the forks (the order of
`+coerce-lazy`). -/
def walkLazyB (f : Nat → Sure S → CM Map Unit) : Nat → Lazy S → CM Map Unit
  | o, mk s fk bd => do
    f o s
    if fk.isEmpty && bd.isEmpty then pure () else do
    walkBondsB f bd
    walkForksB f fk

def walkBondsB (f : Nat → Sure S → CM Map Unit) : List (Nat × Lazy S) → CM Map Unit
  | [] => pure ()
  | (o, l) :: rest => do
    walkLazyB f o l
    walkBondsB f rest

def walkForksB (f : Nat → Sure S → CM Map Unit) : List ((Nat × Lazy S) × (Nat × Lazy S)) → CM Map Unit
  | [] => pure ()
  | ((oy, y), (on, n)) :: rest => do
    walkLazyB f oy y
    walkLazyB f on n
    walkForksB f rest
end

mutual
/-- **`+coerce-lazy` is `walkLazyB` of `coerceLazy`.** -/
theorem coerceLazyL_walkB (ned : Need) (less : Cape) : ∀ (o : Nat) (l : Lazy S),
    (coerceLazyL ned less o l : CM Map Unit) = walkLazyB (fun o s => coerceLazy ned o s less) o l
  | o, mk s f b => by
    simp only [coerceLazyL, walkLazyB, coerceBonds_walkB ned less b, coerceForks_walkB ned less f]

theorem coerceBonds_walkB (ned : Need) (less : Cape) : ∀ (b : List (Nat × Lazy S)),
    (coerceBonds ned less b : CM Map Unit) = walkBondsB (fun o s => coerceLazy ned o s less) b
  | [] => by simp only [coerceBonds, walkBondsB]
  | (o, l) :: rest => by
    simp only [coerceBonds, walkBondsB, coerceLazyL_walkB ned less o l, coerceBonds_walkB ned less rest]

theorem coerceForks_walkB (ned : Need) (less : Cape) : ∀ (f : List ((Nat × Lazy S) × (Nat × Lazy S))),
    (coerceForks ned less f : CM Map Unit) = walkForksB (fun o s => coerceLazy ned o s less) f
  | [] => by simp only [coerceForks, walkForksB]
  | ((oy, y), (on, n)) :: rest => by
    simp only [coerceForks, walkForksB, coerceLazyL_walkB ned less oy y, coerceLazyL_walkB ned less on n,
      coerceForks_walkB ned less rest]
end

/-- **Two needs that every walk in the order of `+coerce-lazy` which does
nothing at a `bunt` sure need walks alike.** -/
def WalkEqB (l l' : Lazy S) : Prop :=
  ∀ (f : Nat → Sure S → CM Map Unit), (∀ (o : Nat) (g : Gen Map), f o Sure.bunt g = some ((), g)) →
    ∀ o, walkLazyB f o l = walkLazyB f o l'

theorem walkEqB_refl (l : Lazy S) : WalkEqB (Map := Map) l l := fun _ _ _ => rfl

/-- **The wrapper of `+past-fork` is walked as the need it wraps.** -/
theorem walkLazyB_wrap {f : Nat → Sure S → CM Map Unit} (hf : ∀ (o : Nat) (g : Gen Map), f o Sure.bunt g = some ((), g))
    (y : Nat) (a : Lazy S) : walkLazyB f y (mk Sure.bunt [] [(y, a)]) = walkLazyB f y a := by
  funext g
  simp only [walkLazyB, walkForksB, walkBondsB, bind_apply, hf, Option.bind_some, List.isEmpty_nil,
    List.isEmpty_cons, Bool.true_and, Bool.false_eq_true, if_false, pure_apply]
  cases walkLazyB f y a g with
  | none => rfl
  | some p => rfl

/-- The last fork of a list, walked alike. -/
theorem walkForksB_last {f : Nat → Sure S → CM Map Unit} {y n : Nat} {a a' b b' : Lazy S}
    (ha : walkLazyB f y a = walkLazyB f y a') (hb : walkLazyB f n b = walkLazyB f n b') :
    ∀ F : List ((Nat × Lazy S) × (Nat × Lazy S)),
      walkForksB f (F ++ [((y, a), (n, b))]) = walkForksB f (F ++ [((y, a'), (n, b'))])
  | [] => by simp only [List.nil_append, walkForksB, ha, hb]
  | ((oy, u), (on, v)) :: rest => by
    simp only [List.cons_append, walkForksB, walkForksB_last ha hb rest]

/-- **The need of a `%6` with the wrapped fork and with the plain one.** -/
theorem walkEqB_six (s : Sure S) (F : List ((Nat × Lazy S) × (Nat × Lazy S))) (B : List (Nat × Lazy S))
    {y n : Nat} {a a' b b' : Lazy S}
    (ha : ∀ (f : Nat → Sure S → CM Map Unit), (∀ (o : Nat) (g : Gen Map), f o Sure.bunt g = some ((), g)) →
      walkLazyB f y a = walkLazyB f y a')
    (hb : ∀ (f : Nat → Sure S → CM Map Unit), (∀ (o : Nat) (g : Gen Map), f o Sure.bunt g = some ((), g)) →
      walkLazyB f n b = walkLazyB f n b') :
    WalkEqB (Map := Map) (mk s (F ++ [((y, a), (n, b))]) B) (mk s (F ++ [((y, a'), (n, b'))]) B) := by
  intro f hf o
  have e1 : (F ++ [((y, a), (n, b))]).isEmpty = false := by simp
  have e2 : (F ++ [((y, a'), (n, b'))]).isEmpty = false := by simp
  simp only [walkLazyB, e1, e2, Bool.false_and, Bool.false_eq_true, if_false]
  rw [walkForksB_last (ha f hf) (hb f hf) F]

/-! ## `+coerce-lazy` at a `bunt` need -/

/-- **`+coerce-lazy` does nothing at a `bunt` sure need** when the final
need is no single register. -/
theorem coerceLazy_bunt {ned : Need} (hned : ∀ r, ned ≠ Need.this r) (less : Cape) (o : Nat) (g : Gen Map) :
    (coerceLazy ned o (Sure.bunt : Sure S) less : CM Map Unit) g = some ((), g) := by
  have hl : coerceLok (HoonSet.empty : S) less ned = some HoonSet.empty := by
    simp only [coerceLok, toList_empty, List.foldl_nil]
  simp only [coerceLazy, Sure.bunt, bind_apply, hl, Option.map_some, Option.bind_some]
  rw [show (sureRequireLook (⟨Need.none, HoonSet.empty⟩ : Sure S) : CM Map Need) g = some (Need.none, g) from
    sureRequireLook_bunt g]
  simp only [Option.bind_some]
  cases ned with
  | none => simp [sureLoop, pure_apply]
  | this r => exact absurd rfl (hned r)
  | pair p q => simp [sureLoop, pure_apply]
  | both r h t => simp [sureLoop, pure_apply]

/-- **A need other than `this` gets no single register.** -/
theorem needOrdAllocRegs_notThis {ord : NeedOrd} (hord : ord ≠ NeedOrd.this) {g g' : Gen Map} {ned : Need}
    (h : needOrdAllocRegs ord g = some (ned, g')) : ∀ r, ned ≠ Need.this r := by
  intro r e
  subst e
  cases ord with
  | this => exact hord rfl
  | none => simp [needOrdAllocRegs, pure_apply] at h
  | pair p q =>
    simp only [needOrdAllocRegs, bind_apply] at h
    obtain ⟨⟨h1, g1⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨t1, g2⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · simp [crashM] at h
    · simp [pure_apply] at h
  | both p q =>
    simp only [needOrdAllocRegs, bind_apply] at h
    obtain ⟨⟨r1, g1⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨h1, g2⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨t1, g3⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · simp [crashM] at h
    · simp [pure_apply] at h

/-! ## The top -/

/-- **The n-ary contract from `RunOKGB` of an unwrapped result**
(`finishLFC_contractGB` with `+coerce-lazy` of the run's result read as
`+coerce-lazy` of `nexU`, `WalkEqB`, and `DoneOK.nent` of `nexU`): for a
need other than `this`, both halves of the contract on every subject of `P`
with the cape's axes, entered with its split. -/
theorem finishLFC_contractGBW (lib : Lib) {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm} (N : Needs)
    (hR : ∀ {nex : NextL S} {gE : Gen Map}, runLC env Option.none nm (CGoalL.done : CGoalL S) [] (gen0 : Gen Map) =
      some (nex, gE) → ∃ nexU : NextL S, nexU.th = nex.th ∧ WalkEqB (Map := Map) nex.laz nexU.laz ∧
        nexU.th.there ∉ (entries nexU.laz).map Prod.fst ∧ RunOKGB lib N P f (CGoal.done : CGoal S) gen0 gE nexU)
    {ord : NeedOrd} (hord : ord ≠ NeedOrd.this) {less : Cape} {bake : Need → Need × List (Nat × Noun)}
    (hbake : ∀ ned, bake ned = (ned, [])) {c : Straight Map} (h : finishLFC (S := S) env nm ord less bake = some c) :
    ∀ s, P s → CapeAxes less s → ∀ args, SkaModel.split c.need s = some args →
      ContractFwd lib N s f args c ∧ ContractBwd lib N s f args c := by
  unfold finishLFC at h
  obtain ⟨⟨nex0, gE⟩, hr, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨nex, hth, hW, hnent, R⟩ := hR hr
  simp only at h
  split at h
  · cases h
  obtain ⟨⟨nedF, g2⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [hbake, List.map_nil] at h
  obtain ⟨⟨u3, g3⟩, h3, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨u4, g4⟩, h4, hts⟩ := Option.bind_eq_some_iff.mp h
  rw [coerceLazyL_walkB, ← hth, hW _ (fun o g => coerceLazy_bunt (needOrdAllocRegs_notThis hord h2) less o g),
    ← coerceLazyL_walkB] at h3
  rw [← hth] at h4 hts
  have T : TopSB gE nex :=
    { ext := R.ext
      grow := R.grow
      cfr := R.cfr
      lo := R.lo
      hi := R.hi
      args := by
        rcases R.ent with ⟨b, _, _, ha⟩ | e
        · exact ha
        · exact e.elim
      regs := fun r hr => by
        rcases R.regs r hr with e | e
        · exact e.elim
        · exact e
      dist := R.dist
      eregs := fun e he => ⟨(R.eregs e he).1, fun r hr => ⟨by
        rcases ((R.eregs e he).2 r hr).1 with a | a
        · exact a.elim
        · exact a, ((R.eregs e he).2 r hr).2⟩⟩
      labs := R.labs
      nodup := R.nodup
      ncond := R.ncond
      econd := R.econd }
  have bad : ∀ {tm : Trace} {r : Tone}, BadC (CGoal.done : CGoal S) tm r → r = Tone.two tm := fun hb => by
    rcases hb with e | ⟨_, _, hp⟩
    · exact e
    · exact hp.elim
  have F := finishTopF_genB lib T R.ent hnent (fwdPhi lib N P f)
    (fun cf hcf c ned σ O st t gul s ag hned regs hh hn Inv ν n tm r hs hN hS hF hm hI htr => by
      obtain ⟨ton, st', -, -, he, hrel⟩ :=
        R.sem cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s s r hI htr hs hm ag hned regs hh hn
      exact ⟨ton, st', he, hrel⟩)
    (fun σ O st t gul s hfs Inv ν n tm r hs _ _ _ hm _ htr =>
      ⟨Tone.two t, st, rfl, by rw [bad ((R.nec s hs hfs).1 gul n tm r hm)]; exact ToneRel.two htr⟩) h2 h3 h4 hts
  have B := finishTopF_genB lib T R.ent hnent (bwdPhi lib N P f)
    (fun cf hcf c ned σ O st t gul s ag hned regs hh hn Inv ν tm hs hN hS hB hI htr ton st'' hx => by
      obtain ⟨r, hm, G⟩ := R.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s s hI htr hs ag hned regs hh hn _ hx
      obtain ⟨ton', st', -, -, he, hrel⟩ := G
      rw [he] at hx
      cases hx
      exact ⟨r, hm, hrel⟩)
    (fun σ O st t gul s hfs Inv ν tm hs _ _ _ _ htr ton st' hx => by
      cases hx
      obtain ⟨r, hm, hb⟩ := (R.nec s hs hfs).2 gul tm
      rw [bad hb] at hm
      exact ⟨_, hm, ToneRel.two htr⟩) h2 h3 h4 hts
  intro s hs hca args hsp
  refine ⟨fun σ Inv ν O n gul ti tm r hN hS hF hm st hI htr => ?_,
    fun σ Inv ν O gul ti tm hN hS hB st ton st' hI htr hx => ?_⟩
  · exact F σ O st s args ti gul hca hsp Inv ν n tm r hs hN hS hF hm hI htr
  · exact B σ O st s args ti gul hca hsp Inv ν tm hs hN hS hB hI htr ton st' hx

/-- **The n-ary contract from `DoneOK`, through the unwrapped form**: a run
that meets `DoneOK` gives `finishLFC_contractGBW`'s premise with `nexU =
nex`. -/
theorem doneOK_toWN {lib : Lib} {N : Needs} {P : Noun → Prop} {f : Noun} {g0 g1 : Gen Map} {nex : NextL S}
    (D : DoneOK lib N P f g0 g1 nex) :
    ∃ nexU : NextL S, nexU.th = nex.th ∧ WalkEqB (Map := Map) nex.laz nexU.laz ∧
      nexU.th.there ∉ (entries nexU.laz).map Prod.fst ∧ RunOKGB lib N P f (CGoal.done : CGoal S) g0 g1 nexU :=
  ⟨nex, rfl, walkEqB_refl _, D.nent, D.run⟩

end Comp
end SkaModel
end Formalization
