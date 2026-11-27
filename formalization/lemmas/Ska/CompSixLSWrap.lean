import lemmas.Ska.CompSixLSDone

/-!
# `[6 c a b]` under `%done` with a calling test: the wrapped fork

README Gaps 12.34, step 2.  With a calling test (`hinted` true) `+past-fork`
puts each branch's need into a bond at the fork's own label, `[yes [bunt ~
[yes need]~]]`, so the labels of `entries` repeat and `RunOKGB.nodup` is
false (`CompSixLSCheck.lean`, `doneTally`).  The labels of the entries that
ask something stay distinct (checked on the 147 runs with a calling test:
`relaxTally` in the scratch check of this session, 0 of 147 repeat; the 294
entries that repeat a label are the wrappers, whose sure need is `bunt`).

The repeated label costs nothing at the top: the gate of `+kern` does
nothing at a `bunt` sure need (`sureRequireLook` of `bunt` is `none`), so
`+kern` walks the wrapped need exactly as the unwrapped one (`WalkEq`,
`kern_walkEq`, `kerf_walkEq`).  So the relation of the result is stated on
the UNWRAPPED need, whose labels are distinct: `SixDW` gives a `nexU` with
the run's jump, `WalkEq` of the run's need and `nexU`'s, and `RunOKGB` of
`nexU`; the top (`finishLUC_contractGBW`) reads `+kerf` of the run's result
as `+kerf` of `nexU`.

* `WalkEq`, `walkEq_refl`, `walkLazy_wrap`, `walkForks_last`, `walkEq_six`.
* `kernGate_bunt`, `kern_walkEq`, `kerf_walkEq`.
* `SixDW`, `SixD.toW`, `finishLUC_contractGBW`, `finishLUC_contractSixDW`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Walks that do nothing at a `bunt` need -/

/-- **Two needs that every walk which does nothing at a `bunt` sure need
walks alike.** -/
def WalkEq (l l' : Lazy S) : Prop :=
  ∀ (f : Nat → Sure S → CM Map Unit), (∀ (o : Nat) (g : Gen Map), f o Sure.bunt g = some ((), g)) →
    ∀ o, walkLazy f o l = walkLazy f o l'

theorem walkEq_refl (l : Lazy S) : WalkEq (Map := Map) l l := fun _ _ _ => rfl

/-- **The wrapper of `+past-fork` is walked as the need it wraps.** -/
theorem walkLazy_wrap {f : Nat → Sure S → CM Map Unit} (hf : ∀ (o : Nat) (g : Gen Map), f o Sure.bunt g = some ((), g))
    (y : Nat) (a : Lazy S) : walkLazy f y (mk Sure.bunt [] [(y, a)]) = walkLazy f y a := by
  funext g
  simp only [walkLazy, walkForks, walkBonds, bind_apply, hf, Option.bind_some, List.isEmpty_nil,
    List.isEmpty_cons, Bool.true_and, Bool.false_eq_true, if_false, pure_apply]
  cases walkLazy f y a g with
  | none => rfl
  | some p => rfl

/-- The last fork of a list, walked alike. -/
theorem walkForks_last {f : Nat → Sure S → CM Map Unit} {y n : Nat} {a a' b b' : Lazy S}
    (ha : walkLazy f y a = walkLazy f y a') (hb : walkLazy f n b = walkLazy f n b') :
    ∀ F : List ((Nat × Lazy S) × (Nat × Lazy S)),
      walkForks f (F ++ [((y, a), (n, b))]) = walkForks f (F ++ [((y, a'), (n, b'))])
  | [] => by simp only [List.nil_append, walkForks, ha, hb]
  | ((oy, u), (on, v)) :: rest => by
    simp only [List.cons_append, walkForks, walkForks_last ha hb rest]

/-- **The need of a `%6` with the wrapped fork and with the plain one.** -/
theorem walkEq_six (s : Sure S) (F : List ((Nat × Lazy S) × (Nat × Lazy S))) (B : List (Nat × Lazy S))
    {y n : Nat} {a a' b b' : Lazy S}
    (ha : ∀ (f : Nat → Sure S → CM Map Unit), (∀ (o : Nat) (g : Gen Map), f o Sure.bunt g = some ((), g)) →
      walkLazy f y a = walkLazy f y a')
    (hb : ∀ (f : Nat → Sure S → CM Map Unit), (∀ (o : Nat) (g : Gen Map), f o Sure.bunt g = some ((), g)) →
      walkLazy f n b = walkLazy f n b') :
    WalkEq (Map := Map) (mk s (F ++ [((y, a), (n, b))]) B) (mk s (F ++ [((y, a'), (n, b'))]) B) := by
  intro f hf o
  have e1 : (F ++ [((y, a), (n, b))]).isEmpty = false := by simp
  have e2 : (F ++ [((y, a'), (n, b'))]).isEmpty = false := by simp
  simp only [walkLazy, e1, e2, Bool.false_and, Bool.false_eq_true, if_false]
  rw [walkForks_last (ha f hf) (hb f hf) F]

/-! ## `+kern` and `+kerf` -/

theorem toList_empty : HoonSet.toList (HoonSet.empty : S) = [] :=
  List.eq_nil_iff_forall_not_mem.mpr fun x => HoonSet.mem_empty x

/-- `+sure-require-look` of `bunt` is `none`. -/
theorem sureRequireLook_bunt (g : Gen Map) :
    (sureRequireLook (Sure.bunt : Sure S) : CM Map Need) g = some (Need.none, g) := by
  simp only [sureRequireLook, Sure.bunt, toList_empty, List.foldl_nil, pure_apply]

/-- **`+kern` walks the wrapped need as the plain one.** -/
theorem kern_walkEq {l l' : Lazy S} (hW : WalkEq (Map := Map) l l') (o : Nat) :
    (kern o l : CM Map Nat) = kern o l' := by
  funext g
  simp only [kern, bind_apply, re_apply, Option.bind_some, get_apply]
  split
  · rfl
  · rw [hW _ (fun o' g' => by
      simp only [bind_apply, sureRequireLook_bunt, Option.bind_some, if_true, ↓reduceIte, pure_apply]) o]

/-- **`+kerf` of two results with one jump and needs walked alike.** -/
theorem kerf_walkEq {nex nex' : NextL S} (hth : nex.th = nex'.th) (hW : WalkEq (Map := Map) nex.laz nex'.laz) :
    (kerf nex : CM Map (Nat × Nat)) = kerf nex' := by
  unfold kerf
  rw [hth]
  simp only [kern_walkEq hW]

/-! ## The relation and the top -/

/-- **`SixD` read on the unwrapped need**: every run under `%done` returns a
result `nex` (at most `k` entries) and there is a `nexU` with its jump,
walked alike, that meets `RunOKGB`. -/
abbrev SixDW (lib : Lib) (N : Needs) (env : CallEnv) (P : Noun → Prop) (f : Noun) (nm : Nomm) (k : Nat) : Prop :=
  ∀ {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    runLC env sup nm (CGoalL.done : CGoalL S) region g0 = some (nex, g1) →
    (∃ nexU : NextL S, nexU.th = nex.th ∧ WalkEq (Map := Map) nex.laz nexU.laz ∧
      RunOKGB lib N P f (CGoal.done : CGoal S) g0 g1 nexU) ∧ (entries nex.laz).length ≤ k

theorem SixD.toW {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm} {k : Nat}
    (H : SixD (S := S) (Map := Map) lib N env P f nm k) : SixDW (S := S) (Map := Map) lib N env P f nm k :=
  fun b0 d0 hu hcl hcb hr =>
    ⟨⟨_, rfl, walkEq_refl _, (H b0 d0 hu hcl hcb hr).1⟩, (H b0 d0 hu hcl hcb hr).2⟩

/-- **The contract from `RunOKGB` of an unwrapped result** (`finishLUC_contractGB`
with `+kerf` of the run's result read as `+kerf` of `nexU`). -/
theorem finishLUC_contractGBW (lib : Lib) {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm} (N : Needs)
    (hR : ∀ {nex : NextL S} {gE : Gen Map}, runLC env Option.none nm (CGoalL.done : CGoalL S) [] (gen0 : Gen Map) =
      some (nex, gE) → ∃ nexU : NextL S, nexU.th = nex.th ∧ WalkEq (Map := Map) nex.laz nexU.laz ∧
        RunOKGB lib N P f (CGoal.done : CGoal S) gen0 gE nexU)
    {c : Straight Map} (h : finishLUC (S := S) env nm = some c) :
    c.need = NeedOrd.this ∧ ∀ s, P s → ContractFwd lib N s f [s] c ∧ ContractBwd lib N s f [s] c := by
  unfold finishLUC at h
  obtain ⟨⟨nex0, gE⟩, hr, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨⟨o', sub⟩, g8⟩, hk, hts⟩ := Option.bind_eq_some_iff.mp h
  simp only at hts
  obtain ⟨nex, hth, hW, R⟩ := hR hr
  rw [kerf_walkEq hth.symm hW] at hk
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
  have F := finishTop_genB lib T (fwdPhi lib N P f)
    (fun cf hcf c ned σ O st t gul s ag hned regs hh hn Inv ν n tm r hs hN hS hF hm hI htr => by
      obtain ⟨ton, st', -, -, he, hrel⟩ :=
        R.sem cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s s r hI htr hs hm ag hned regs hh hn
      exact ⟨ton, st', he, hrel⟩)
    (fun σ O st t gul s hfs Inv ν n tm r hs _ _ _ hm _ htr =>
      ⟨Tone.two t, st, rfl, by rw [bad ((R.nec s hs hfs).1 gul n tm r hm)]; exact ToneRel.two htr⟩) hk hts
  have B := finishTop_genB lib T (bwdPhi lib N P f)
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
      exact ⟨_, hm, ToneRel.two htr⟩) hk hts
  refine ⟨F.1, fun s hs => ⟨fun σ Inv ν O n gul ti tm r hN hS hF hm st hI htr => ?_,
    fun σ Inv ν O gul ti tm hN hS hB st ton st' hI htr hx => ?_⟩⟩
  · exact F.2 σ O st s ti gul Inv ν n tm r hs hN hS hF hm hI htr
  · exact B.2 σ O st s ti gul Inv ν tm hs hN hS hB hI htr ton st' hx

/-- **The contract from `SixDW`.** -/
theorem finishLUC_contractSixDW (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {f : Noun} {nm : Nomm}
    {k : Nat} (H : SixDW (S := S) (Map := Map) lib N env P f nm k) {c : Straight Map}
    (hc : finishLUC (S := S) env nm = some c) :
    c.need = NeedOrd.this ∧ ∀ s, P s → ContractFwd lib N s f [s] c ∧ ContractBwd lib N s f [s] c :=
  finishLUC_contractGBW lib N (fun hr => (H (by simp [gen0]) rfl upBelow_gen0 clear_gen0 condBelow_gen0 hr).1) hc

end Comp
end SkaModel
end Formalization
