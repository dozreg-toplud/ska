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

/-! ## The run with any test -/

theorem entries_wrap (y : Nat) (a : Lazy S) : entries (mk (Sure.bunt : Sure S) [] [(y, a)]) = (y, a) :: entries a := by
  simp [entries, bondEntries, forkEntries]

/-- **`[6 c a b]` under `%done` taken apart, with any test**: `+past-fork`
leaves the fork (`hinted` false) or wraps each branch's need in a bond at
its label (`hinted` true). -/
theorem runLC_six_done_apartW (env : CallEnv) (sup : Option Nomm) {c a b : Nomm}
    {region : List Nat} {g0 g4 : Gen Map} {nex : NextL S}
    (h : runLC env sup (Nomm.n6 c a b) (CGoalL.done : CGoalL S) region g0 = some (nex, g4)) :
    ∃ (x1 x0 xc : NextL S) (g1 g2 g3 : Gen Map) (l0 l1 : Lazy S),
      runLC env sup b CGoalL.done region g0 = some (x1, g1) ∧ runLC env sup a CGoalL.done region g1 = some (x0, g2) ∧
      x0.th.args = [] ∧ x1.th.args = [] ∧
      runLC env sup c (CGoalL.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1))) region (sixGenL g2 x0.th x1.th region) =
        some (xc, g3) ∧
      ((l0 = x0.laz ∧ l1 = x1.laz) ∨
        (l0 = mk (Sure.bunt : Sure S) [] [(g2.bo, x0.laz)] ∧ l1 = mk (Sure.bunt : Sure S) [] [(g2.bo + 1, x1.laz)])) ∧
      (lazyBig (mk (Sure.bunt : Sure S) [((g2.bo, l0), (g2.bo + 1, l1))] []) = false →
        copyL xc (mk (Sure.bunt : Sure S) [((g2.bo, l0), (g2.bo + 1, l1))] []) g3 = some (nex, g4)) := by
  simp only [runLC] at h
  obtain ⟨x1, g1, h1, h⟩ := bind_some h
  obtain ⟨x0, g2, h2, h⟩ := bind_some h
  simp only [bind_apply, emit_apply, setTag_apply, Option.bind_some] at h
  by_cases a0' : x0.th.args ≠ []
  · simp [a0'] at h
  have a0 : x0.th.args = [] := by simpa using a0'
  by_cases a1' : x1.th.args ≠ []
  · simp [a0, a1'] at h
  have a1 : x1.th.args = [] := by simpa using a1'
  simp only [a0, a1, ne_eq, not_true_eq_false, if_false] at h
  obtain ⟨lz, gl, hl, h⟩ := bind_some h
  simp only [liftO] at hl
  obtain ⟨lz', hpf, e⟩ := Option.map_eq_some_iff.mp hl
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨xc, g3, h3, h⟩ := bind_some h
  have hlz : ∃ l0 l1, lz' = mk (Sure.bunt : Sure S) [((g2.bo, l0), (g2.bo + 1, l1))] [] ∧
      ((l0 = x0.laz ∧ l1 = x1.laz) ∨
        (l0 = mk (Sure.bunt : Sure S) [] [(g2.bo, x0.laz)] ∧ l1 = mk (Sure.bunt : Sure S) [] [(g2.bo + 1, x1.laz)])) := by
    unfold pastFork at hpf
    split at hpf
    · cases hpf
    · simp only [Option.some.injEq] at hpf
      subst hpf
      exact ⟨_, _, by simp only [emitted_bo], Or.inl ⟨rfl, rfl⟩⟩
    · simp only [Option.some.injEq] at hpf
      subst hpf
      exact ⟨_, _, by simp [fork_mk, sure_mk, bond_mk, emitted_bo], Or.inr ⟨rfl, rfl⟩⟩
  obtain ⟨l0, l1, rfl, hl01⟩ := hlz
  refine ⟨x1, x0, xc, g1, g2, g3, l0, l1, h1, h2, a0, a1, h3, hl01, fun hbig => ?_⟩
  have hcond : (!(lazyBig (softLess noSoft (mk (Sure.bunt : Sure S) [((g2.bo, l0), (g2.bo + 1, l1))] [])))) = true := by
    rw [softLess_noSoft, hbig]; rfl
  rw [if_pos hcond] at h
  exact h

/-- **`[6 c a b]` under `%done` with any test of `PickD` and branches of
`SixDW`** (`six_doneGB` on the unwrapped need): the test may call, so
`+past-fork` may wrap each branch's need in a bond at the fork's own label;
the relation is stated for `nexU`, the result with the plain fork of the
branches' unwrapped needs, which `+kern` walks as the real one
(`walkEq_six`, `walkLazy_wrap`), and the proof is the text of
`six_doneGB` on `nexU`.  Branches of `SixDW` may be `%6` again. -/
theorem six_doneGBW (lib : Lib) {N : Needs} (env : CallEnv) {P : Noun → Prop} {fc fa fb : Noun} {c a b : Nomm}
    {kc ka kb : Nat} (Hc : PickD (S := S) (Map := Map) lib N env P fc c kc)
    (Ha : SixDW (S := S) (Map := Map) lib N env P fa a ka) (Hb : SixDW (S := S) (Map := Map) lib N env P fb b kb)
    (hk : ka + kb + 5 ≤ lazyMax) :
    SixDW (S := S) (Map := Map) lib N env P (n4 (A 6) fc fa fb) (Nomm.n6 c a b) (kc + ka + kb + 4) := by
  intro sup region g0 g4 nex b0 d0 hu hcl0 hcb0 h
  obtain ⟨x1, x0, xc, g1, g2, g3, l0, l1, h1, h2, hx0a, hx1a, h3, hl01, hrest⟩ := runLC_six_done_apartW env sup h
  obtain ⟨⟨x1U, h1th, W1, Rb⟩, sb⟩ := Hb b0 d0 hu hcl0 hcb0 h1
  have u1 : UpBelow g1 := Rb.grow.up hu
  have d1 : g1.drop = false := Rb.ext.2.2.1.trans d0
  have b01 : g0.bo ≤ g1.bo := Rb.ext.2.1
  have b1 : 1 ≤ g1.bo := Nat.le_trans b0 b01
  have cl1 : Clear g1 := hcl0.growU Rb.grow
  have cb1 : CondBelow g1 := Rb.cfr.below hcb0
  obtain ⟨⟨x0U, h0th, W0, Ra⟩, sa⟩ := Ha b1 d1 u1 cl1 cb1 h2
  have hx0a' : x0U.th.args = [] := by rw [h0th]; exact hx0a
  have hx1a' : x1U.th.args = [] := by rw [h1th]; exact hx1a
  have lo0 : 1 ≤ x0.th.there := by rw [← h0th]; exact Ra.lo
  have hi0 : x0.th.there < g2.bo := by rw [← h0th]; exact Ra.hi
  have lo1 : 1 ≤ x1.th.there := by rw [← h1th]; exact Rb.lo
  have hi1 : x1.th.there < g1.bo := by rw [← h1th]; exact Rb.hi
  have cl2 : Clear g2 := cl1.growU Ra.grow
  have cb2 : CondBelow g2 := Ra.cfr.below cb1
  have u2 : UpBelow g2 := Ra.grow.up u1
  have d2 : g2.drop = false := Ra.ext.2.2.1.trans d1
  have b12 : g1.bo ≤ g2.bo := Ra.ext.2.1
  have GU : GrowU g2 (sixGenL g2 x0.th x1.th region) := (grow_sixGenL region (jumpsBelow_hop lo0 hi0)
    (jumpsBelow_hop lo1 (by omega))).toU u2
  have uG : UpBelow (sixGenL g2 x0.th x1.th region) := GU.up u2
  have hbig : lazyBig (mk (Sure.bunt : Sure S) [((g2.bo, l0), (g2.bo + 1, l1))] []) = false := by
    apply lazyBig_entries
    rw [entries_six]; simp only [List.length_append, List.length_cons]
    have e0 : (entries l0).length ≤ ka + 1 := by
      rcases hl01 with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · omega
      · rw [entries_wrap]; simp only [List.length_cons]; omega
    have e1 : (entries l1).length ≤ kb + 1 := by
      rcases hl01 with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · omega
      · rw [entries_wrap]; simp only [List.length_cons]; omega
    omega
  -- the test
  have dG : (sixGenL g2 x0.th x1.th region).drop = false := by simp [d2]
  obtain ⟨Rc, sc⟩ := Hc (jmp0 g2.bo) (jmp0 (g2.bo + 1)) rfl rfl
    ⟨⟨by simp only [jmp0]; omega, by simp only [jmp0, sixGenL_bo]; omega⟩,
      by simp only [jmp0]; omega, by simp only [jmp0, sixGenL_bo]; omega⟩
    (by simp only [sixGenL_bo]; omega) dG uG (cl2.growU GU)
    (fun k hk => by simp only [sixGenL_cond, sixGenL_re] at hk ⊢; exact cb2 k hk) h3
  have u3 : UpBelow g3 := Rc.grow.up uG
  have d3 : g3.drop = false := Rc.ext.2.2.1.trans dG
  have bG3 : g2.bo + 2 ≤ g3.bo := by have := Rc.ext.2.1; simpa using this
  have hap : ∀ e ∈ xc.laz.fork, e.1.1 ≠ g2.bo := fun e he => by
    have hm : e.1 ∈ entries xc.laz := by rw [entries_eq]; exact List.mem_append_right _ (fork_mem_entries he)
    have := (Rc.labs _ hm).1; simp only [sixGenL_bo] at this; omega
  have hcp' := hrest hbig
  rw [copyL_six_apart xc l0 l1 g2.bo (g2.bo + 1) g3 hap] at hcp'
  obtain ⟨⟨u, g4'⟩, hadd, e4⟩ := Option.map_eq_some_iff.mp hcp'
  simp only [Prod.mk.injEq] at e4
  obtain ⟨rfl, rfl⟩ := e4
  obtain ⟨A4, r4, bo4, _⟩ := addOps_nil hadd
  simp only [emitted_re, emitted_bo] at r4 bo4
  -- the states
  have E2 : Ext g2 (sixGenL g2 x0.th x1.th region) := ext_sixGenL _ _ _ _
  have E4 : Ext g3 g4' := (ext_emit g3 _).trans (ext_addOps_nil hadd)
  have E24 : Ext g2 g4' := E2.trans (Rc.ext.trans E4)
  have E14 : Ext g1 g4' := Ra.ext.trans E24
  have E04 : Ext g0 g4' := Rb.ext.trans E14
  have re01 := Rb.ext.1
  have re12 := Ra.ext.1
  have re2G : g2.re ≤ g3.re := by have := Rc.ext.1; simpa using this
  have h4k : ∀ k, k ≠ g3.bo → HoonMap.get g4'.blocks k = HoonMap.get g3.blocks k := fun k hk =>
    (A4 k).trans (get_emitted_ne hk)
  have h4o : HoonMap.get g4'.blocks g3.bo = some ⟨[], [], Termin.hop xc.th⟩ :=
    (A4 g3.bo).trans (emitted_get g3 _ d3)
  have hG3 : ∀ k, k < g2.bo + 2 → HoonMap.get g3.blocks k =
      HoonMap.get (sixGenL g2 x0.th x1.th region).blocks k := fun k hk => Rc.ext.2.2.2 k (by simpa using hk)
  have h4y : HoonMap.get g4'.blocks g2.bo = some ⟨[], [], Termin.hop x0.th⟩ := by
    rw [h4k _ (by omega), hG3 _ (by omega)]; exact sixGenL_get_y _ _ _ d2
  have h4n : HoonMap.get g4'.blocks (g2.bo + 1) = some ⟨[], [], Termin.hop x1.th⟩ := by
    rw [h4k _ (by omega), hG3 _ (by omega)]; exact sixGenL_get_n _ _ _ d2
  have h4y' : HoonMap.get g4'.blocks g2.bo = some ⟨[], [], Termin.hop x0U.th⟩ := by rw [h0th]; exact h4y
  have h4n' : HoonMap.get g4'.blocks (g2.bo + 1) = some ⟨[], [], Termin.hop x1U.th⟩ := by rw [h1th]; exact h4n
  have h42 : ∀ k, k < g2.bo → HoonMap.get g4'.blocks k = HoonMap.get g2.blocks k := E24.2.2.2
  have h41 : ∀ k, k < g1.bo → HoonMap.get g4'.blocks k = HoonMap.get g1.blocks k := E14.2.2.2
  -- the registers of the parts
  have raR : ∀ r, NMem x0U.laz.sure.ned r → g1.re ≤ r ∧ r < g2.re := fun r hr => (Ra.regs r hr).resolve_left (fun e => e)
  have rbR : ∀ r, NMem x1U.laz.sure.ned r → g0.re ≤ r ∧ r < g1.re := fun r hr => (Rb.regs r hr).resolve_left (fun e => e)
  -- the labels
  have lc : ∀ e ∈ entries xc.laz, g2.bo + 2 ≤ e.1 ∧ e.1 < g3.bo := fun e he => by
    have := Rc.labs e he; simp only [sixGenL_bo] at this; exact ⟨this.1, this.2.1⟩
  have la : ∀ e ∈ entries x0U.laz, g1.bo ≤ e.1 ∧ e.1 < g2.bo := fun e he =>
    ⟨(Ra.labs e he).1, (Ra.labs e he).2.1⟩
  have lb : ∀ e ∈ entries x1U.laz, g0.bo ≤ e.1 ∧ e.1 < g1.bo := fun e he =>
    ⟨(Rb.labs e he).1, (Rb.labs e he).2.1⟩
  have lc' := labels_bound (P := fun o => g2.bo + 2 ≤ o ∧ o < g3.bo) lc
  have la' := labels_bound (P := fun o => g1.bo ≤ o ∧ o < g2.bo) la
  have lb' := labels_bound (P := fun o => g0.bo ≤ o ∧ o < g1.bo) lb
  have en := entries_copy_six xc.laz (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
    g2.bo (g2.bo + 1) x0U.laz x1U.laz
  have memE : ∀ e, e ∈ entries (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
      (xc.laz.fork ++ [((g2.bo, x0U.laz), (g2.bo + 1, x1U.laz))]) xc.laz.bond) ↔
      e ∈ entries xc.laz ∨ e = (g2.bo, x0U.laz) ∨ e ∈ entries x0U.laz ∨ e = (g2.bo + 1, x1U.laz) ∨
        e ∈ entries x1U.laz := by
    intro e; rw [en]; simp only [List.mem_append, List.mem_cons]
    constructor
    · rintro (h | (h | h) | (h | h))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · rintro (h | h | h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl (Or.inl h))
      · exact Or.inr (Or.inl (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  have labAll : ∀ e ∈ entries (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
      (xc.laz.fork ++ [((g2.bo, x0U.laz), (g2.bo + 1, x1U.laz))]) xc.laz.bond),
      (g2.bo + 2 ≤ e.1 ∧ e.1 < g3.bo ∧ e ∈ entries xc.laz) ∨ e.1 = g2.bo ∨
      (g1.bo ≤ e.1 ∧ e.1 < g2.bo ∧ e ∈ entries x0U.laz) ∨ e.1 = g2.bo + 1 ∨
      (g0.bo ≤ e.1 ∧ e.1 < g1.bo ∧ e ∈ entries x1U.laz) := by
    intro e he
    rcases (memE e).mp he with h | h | h | h | h
    · exact Or.inl ⟨(lc e h).1, (lc e h).2, h⟩
    · exact Or.inr (Or.inl (by rw [h]))
    · exact Or.inr (Or.inr (Or.inl ⟨(la e h).1, (la e h).2, h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [h]))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨(lb e h).1, (lb e h).2, h⟩)))
  have hc43 : g4'.cond = g3.cond := by rw [(KC.addOps' _ _).keep _ _ _ hadd, emitted_cond]
  have cf34 : CondFresh g3 g4' := condFresh_of_eq E4.1 hc43
  have cfG : CondFresh g2 (sixGenL g2 x0.th x1.th region) :=
    condFresh_of_eq (by simp only [sixGenL_re]; omega) (by rw [sixGenL_cond])
  have cf24 : CondFresh g2 g4' := cfG.trans (Rc.cfr.trans cf34)
  have cf14 : CondFresh g1 g4' := Ra.cfr.trans cf24
  have hxca : xc.th.args = [] := by
    rcases Rc.ent with ⟨_, _, _, e⟩ | e
    · exact e
    · simp only [GoalJ] at e; rcases e with e | e <;> rw [e] <;> rfl
  -- what the program gives the parts
  have core : ∀ (cf : Map (Nat × List Nat)) (cc : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ)
      (gul : Noun) (t : Trace) (s0 s : Noun) (st : σ),
      (∀ st' : σ, AgreeUB lib O cc gul st' t cf ned g0 g4'
        (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
          (xc.laz.fork ++ [((g2.bo, x0U.laz), (g2.bo + 1, x1U.laz))]) xc.laz.bond) s0 s) →
      HoonMap.get cc.blocks g3.bo = some ⟨[], [], Termin.hop xc.th⟩ ∧
      (∀ st' : σ, AgreeUB lib O cc gul st' t cf ned (sixGenL g2 x0.th x1.th region) g3 xc.laz s0 s) ∧
      (∀ st' : σ, ∃ A, HoonMap.get cc.blocks g2.bo = some ⟨[], A, Termin.hop x0U.th⟩ ∧
        FillSem lib O cc gul st' t ned g4'.re x0U.laz.sure A s0 s) ∧
      (∀ st' : σ, AgreeUB lib O cc gul st' t cf ned g1 g2 x0U.laz s0 s) ∧
      (∀ st' : σ, ∃ A, HoonMap.get cc.blocks (g2.bo + 1) = some ⟨[], A, Termin.hop x1U.th⟩ ∧
        FillSem lib O cc gul st' t ned g4'.re x1U.laz.sure A s0 s) ∧
      (∀ st' : σ, AgreeUB lib O cc gul st' t cf ned g0 g1 x1U.laz s0 s) := by
    intro cf cc ned σ O gul t s0 s st ag
    have notLab : ∀ o, g0.bo ≤ o → o < g4'.bo → (g3.bo ≤ o ∨
        (g2.bo + 2 ≤ o ∧ o < g3.bo ∧ o ∉ (entries xc.laz).map Prod.fst) ∨
        (g1.bo ≤ o ∧ o < g2.bo ∧ o ∉ (entries x0U.laz).map Prod.fst) ∨
        (o < g1.bo ∧ o ∉ (entries x1U.laz).map Prod.fst)) →
        HoonMap.get cc.blocks o = (HoonMap.get g4'.blocks o).map (unproxyBlob cf) := by
      intro o h0 h1 hc'
      refine (ag st).1 o h0 h1 fun hm => ?_
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
      rcases labAll e he with ⟨x1', x2', x3'⟩ | x | ⟨x1', x2', x3'⟩ | x | ⟨x1', x2', x3'⟩
      · rcases hc' with y | ⟨_, _, y⟩ | y | y
        · omega
        · exact y (List.mem_map_of_mem x3')
        · omega
        · omega
      · rcases hc' with y | y | y | y <;> omega
      · rcases hc' with y | y | ⟨_, _, y⟩ | y
        · omega
        · omega
        · exact y (List.mem_map_of_mem x3')
        · omega
      · rcases hc' with y | y | y | y <;> omega
      · rcases hc' with y | y | y | ⟨_, y⟩
        · omega
        · omega
        · omega
        · exact y (List.mem_map_of_mem x3')
    have fork : ∀ (o : Nat) (x : NextL S) (st' : σ), (o, x.laz) ∈ entries
        (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
          (xc.laz.fork ++ [((g2.bo, x0U.laz), (g2.bo + 1, x1U.laz))]) xc.laz.bond) →
        HoonMap.get g4'.blocks o = some ⟨[], [], Termin.hop x.th⟩ → x.th.args = [] →
        ∃ A, HoonMap.get cc.blocks o = some ⟨[], A, Termin.hop x.th⟩ ∧
          FillSem lib O cc gul st' t ned g4'.re x.laz.sure A s0 s := by
      intro o x st' hm hb hxa
      obtain ⟨A, B, th, hg, hcb, hF⟩ := (ag st').2 _ hm
      rw [hb] at hg
      simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at hg
      obtain ⟨rfl, rfl⟩ := hg
      exact ⟨A, by rw [hcb]; simp [renJmp_nil _ hxa], hF⟩
    refine ⟨?_, fun st' => ⟨fun o h0 h1 hnl => ?_, fun e he => ?_⟩,
      fun st' => fork g2.bo x0U st' ((memE _).mpr (Or.inr (Or.inl rfl))) h4y' hx0a',
      fun st' => ⟨fun o h0 h1 hnl => ?_, fun e he => ?_⟩,
      fun st' => fork (g2.bo + 1) x1U st' ((memE _).mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) h4n' hx1a',
      fun st' => ⟨fun o h0 h1 hnl => ?_, fun e he => ?_⟩⟩
    · rw [notLab g3.bo (by omega) (by omega) (Or.inl (Nat.le_refl _)), h4o]
      simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, renFin, renJmp_nil _ hxca]
    · simp only [sixGenL_bo] at h0
      rw [notLab o (by omega) (by omega) (Or.inr (Or.inl ⟨h0, h1, hnl⟩)), h4k o (by omega)]
    · obtain ⟨A, B, th, hg, hcb, hF⟩ := (ag st').2 e ((memE e).mpr (Or.inl he))
      exact ⟨A, B, th, (h4k _ (by have := lc e he; omega)).symm.trans hg, hcb, hF.mono (by omega)⟩
    · rw [notLab o (by omega) (by omega) (Or.inr (Or.inr (Or.inl ⟨h0, h1, hnl⟩))), h42 o h1]
    · obtain ⟨A, B, th, hg, hcb, hF⟩ := (ag st').2 e ((memE e).mpr (Or.inr (Or.inr (Or.inl he))))
      exact ⟨A, B, th, (h42 _ (la e he).2).symm.trans hg, hcb, hF.mono (by omega)⟩
    · rw [notLab o (by omega) (by omega) (Or.inr (Or.inr (Or.inr ⟨h1, hnl⟩))), h41 o h1]
    · obtain ⟨A, B, th, hg, hcb, hF⟩ := (ag st').2 e ((memE e).mpr (Or.inr (Or.inr (Or.inr (Or.inr he)))))
      exact ⟨A, B, th, (h41 _ (lb e he).2).symm.trans hg, hcb, hF.mono (by omega)⟩
  refine ⟨⟨⟨mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
      (xc.laz.fork ++ [((g2.bo, x0U.laz), (g2.bo + 1, x1U.laz))]) xc.laz.bond, jmp0 g3.bo⟩, rfl, ?_, E04, ?_,
    Rb.cfr.trans cf14, by simp only [jmp0]; omega, by simp only [jmp0]; omega,
    Or.inl ⟨⟨[], [], Termin.hop xc.th⟩, h4o, rfl, rfl⟩, fun r hr => ?_, Rc.dist, ?_, ?_, ?_, fun s hs hfs => ?_,
    fun r hr => by rw [hc43]; exact Rc.ncond r hr, ?_, ?_, ?_⟩, ?_⟩
  · -- the walks
    refine walkEq_six _ xc.laz.fork xc.laz.bond (fun f hf => ?_) (fun f hf => ?_)
    · rcases hl01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact W0 f hf g2.bo
      · exact (walkLazy_wrap hf g2.bo x0.laz).trans (W0 f hf g2.bo)
    · rcases hl01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact W1 f hf (g2.bo + 1)
      · exact (walkLazy_wrap hf (g2.bo + 1) x1.laz).trans (W1 f hf (g2.bo + 1))
  · -- grow
    have GE := growU_emit (b := ⟨[], [], Termin.hop xc.th⟩) (jumpsBelow_hop Rc.lo Rc.hi) u3
    exact Rb.grow.trans (Ra.grow.trans (GU.trans
      (Rc.grow.trans (GE.trans (growU_addOps hadd (GE.up u3))))))
  · -- regs
    have := (Rc.regs r hr).resolve_left (fun e => e); simp only [sixGenL_re] at this
    exact Or.inr ⟨by omega, by omega⟩
  · -- eregs
    intro e he
    rcases (memE e).mp he with h | rfl | h | rfl | h
    · refine ⟨(Rc.eregs e h).1, fun r hr => ?_⟩
      have := (Rc.eregs e h).2 r hr
      have h1' := this.1.resolve_left (fun e => e); simp only [sixGenL_re] at h1'
      exact ⟨Or.inr (by omega), by omega⟩
    · exact ⟨Ra.dist, fun r hr => ⟨Or.inr (by have := raR r hr; omega), by have := raR r hr; omega⟩⟩
    · refine ⟨(Ra.eregs e h).1, fun r hr => ?_⟩
      have := (Ra.eregs e h).2 r hr
      have h1' := this.1.resolve_left (fun e => e)
      exact ⟨Or.inr (by omega), by omega⟩
    · exact ⟨Rb.dist, fun r hr => ⟨Or.inr (by have := rbR r hr; omega), by have := rbR r hr; omega⟩⟩
    · refine ⟨(Rb.eregs e h).1, fun r hr => ?_⟩
      have := (Rb.eregs e h).2 r hr
      have h1' := this.1.resolve_left (fun e => e)
      exact ⟨Or.inr (by omega), by omega⟩
  · -- labs
    intro e he
    rcases (memE e).mp he with h | rfl | h | rfl | h
    · obtain ⟨_, _, B, th, hth⟩ := Rc.labs e h
      have := lc e h
      exact ⟨by omega, by omega, B, th, (h4k _ (by omega)).trans hth⟩
    · exact ⟨by dsimp only; omega, by dsimp only; omega, [], x0U.th, h4y'⟩
    · obtain ⟨_, _, B, th, hth⟩ := Ra.labs e h
      have := la e h
      exact ⟨by omega, by omega, B, th, (h42 _ this.2).trans hth⟩
    · exact ⟨by dsimp only; omega, by dsimp only; omega, [], x1U.th, h4n'⟩
    · obtain ⟨l1, _, B, th, hth⟩ := Rb.labs e h
      have := lb e h
      exact ⟨l1, by omega, B, th, (h41 _ this.2).trans hth⟩
  · -- nodup
    rw [en, List.map_append, List.nodup_append, List.map_append, List.nodup_append]
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, List.mem_append]
    refine ⟨Rc.nodup, ⟨⟨fun hm => by have := la' _ hm; omega, Ra.nodup⟩,
      ⟨fun hm => by have := lb' _ hm; omega, Rb.nodup⟩, fun x hx y hy => ?_⟩, fun x hx y hy => ?_⟩
    · have hx' : g1.bo ≤ x ∧ x ≤ g2.bo := by
        rcases hx with e | e
        · omega
        · have := la' x e; omega
      rcases hy with e | e
      · omega
      · have := lb' y e; omega
    · have := lc' x hx
      rcases hy with (e | e) | (e | e)
      · omega
      · have := la' y e; omega
      · omega
      · have := lb' y e; omega
  · -- nec
    have fo' : ¬ FitsS xc.laz.sure s := fun f => hfs ⟨f.1, (looks_uni_empty _ _).mpr f.2⟩
    obtain ⟨N1, N2⟩ := Rc.nec s hs fo'
    refine ⟨fun gul n tm r hm => ?_, fun gul tm => ?_⟩
    · obtain ⟨n', hn', rb, hb, hcase⟩ := minkF_sixC hm
      have e2 : rb = Tone.two tm := by
        rcases N1 gul n' tm rb hb with e | ⟨p, _, hp⟩
        · exact e
        · exact hp.elim
      subst e2
      rcases hcase with ⟨_, e⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨p, e, _⟩
      · exact Or.inl e
      · cases e
      · cases e
      · cases e
    · obtain ⟨rb, hb, hbad⟩ := N2 gul tm
      have e2 : rb = Tone.two tm := by
        rcases hbad with e | ⟨p, _, hp⟩
        · exact e
        · exact hp.elim
      subst e2
      exact ⟨_, (mink_sixC_bwd (fc := fa) (fd := fb) hb).1 (fun _ e => by cases e), Or.inl rfl⟩
  · -- econd
    intro e he r hr
    rcases (memE e).mp he with h | rfl | h | rfl | h
    · rw [hc43]; exact Rc.econd e h r hr
    · rw [cf24.get_lt (raR r hr).2]; exact Ra.ncond r hr
    · rw [cf24.get_lt ((Ra.eregs e h).2 r hr).2]; exact Ra.econd e h r hr
    · rw [cf14.get_lt (rbR r hr).2]; exact Rb.ncond r hr
    · rw [cf14.get_lt ((Rb.eregs e h).2 r hr).2]; exact Rb.econd e h r hr
  · -- forward
    intro cf hcf cc ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    obtain ⟨hc3, agC, yesB, agA, nuhB, agB⟩ := core cf cc ned σ O gul t s0 s st ag
    have hcf3 : ∀ k, k < g3.re → HoonMap.get cf k = HoonMap.get g3.cond k := fun k hk =>
      (hcf k (by omega)).trans (by rw [hc43])
    have hcf2 : ∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g2.cond k := fun k hk =>
      (hcf k (by omega)).trans (cf24.get_lt hk)
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk =>
      (hcf k (by omega)).trans (cf14.get_lt hk)
    obtain ⟨n', hn', rb, hb, hcase⟩ := minkF_sixC hm
    have Gc := Rc.sem cf hcf3 cc ned σ Inv ν O n' gul hN hS (oracleFwd_le hF (Nat.le_of_lt hn')) st t tm s0 s rb
      hI htr hs hb agC (fun x hx => by have := hned x hx; omega) regs ⟨hh.1, (looks_uni_empty _ _).mp hh.2⟩ hn
    have e0 : goJ lib O cc gul st regs t (jmp0 g3.bo) = goJ lib O cc gul st regs t xc.th := by
      rw [goJ_jmp0 _ _ _ _ hc3, execBlob_hop]
    show ReturnsC lib O cc gul Inv ν st regs t (jmp0 g3.bo) r
    rcases hcase with ⟨hnz, hrr⟩ | ⟨rfl, ha⟩ | ⟨rfl, hb'⟩ | ⟨p, rfl, h0, h1, rfl⟩
    · rw [hrr]
      cases rb with
        | zero q => exact absurd rfl (hnz q)
        | one q => exact returnsC_step (Needs.le_refl _) e0 Gc
        | two q => exact returnsC_step (Needs.le_refl _) e0 Gc
    · obtain ⟨G0, -, -⟩ := Gc
      obtain ⟨st', regs', hI', hν, -, k2, e2⟩ := G0 rfl
      exact returnsC_step hν (e0.trans e2) (sixBlk_fwd Ra hN hS (oracleFwd_le hF (Nat.le_of_lt hn')) hcf2
        (by omega) hned hs yesB agA hI' (frames_mono hν htr)
        (HoldsN.agree ned (fun x hx => k2 x ⟨Or.inr hx, fun e => e⟩) hn) ha)
    · obtain ⟨-, G1, -⟩ := Gc
      obtain ⟨st', regs', hI', hν, -, k2, e2⟩ := G1 rfl
      exact returnsC_step hν (e0.trans e2) (sixBlk_fwd Rb hN hS (oracleFwd_le hF (Nat.le_of_lt hn')) hcf1
        (by omega) hned hs nuhB agB hI' (frames_mono hν htr)
        (HoldsN.agree ned (fun x hx => k2 x ⟨Or.inr hx, fun e => e⟩) hn) hb')
    · obtain ⟨-, -, G2⟩ := Gc
      exact returnsC_step (Needs.le_refl _) e0 (G2 h0 h1)
  · -- backward
    intro cf hcf cc ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨hc3, agC, yesB, agA, nuhB, agB⟩ := core cf cc ned σ O gul t s0 s st ag
    have hcf3 : ∀ k, k < g3.re → HoonMap.get cf k = HoonMap.get g3.cond k := fun k hk =>
      (hcf k (by omega)).trans (by rw [hc43])
    have hcf2 : ∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g2.cond k := fun k hk =>
      (hcf k (by omega)).trans (cf24.get_lt hk)
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk =>
      (hcf k (by omega)).trans (cf14.get_lt hk)
    have e0 : goJ lib O cc gul st regs t (jmp0 g3.bo) = goJ lib O cc gul st regs t xc.th := by
      rw [goJ_jmp0 _ _ _ _ hc3, execBlob_hop]
    obtain ⟨rb, hmb, Gc⟩ := Rc.semB cf hcf3 cc ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs agC
      (fun x hx => by have := hned x hx; omega) regs ⟨hh.1, (looks_uni_empty _ _).mp hh.2⟩ hn res
      (e0.symm.trans hres)
    have MB := mink_sixC_bwd (fc := fa) (fd := fb) hmb
    show ∃ r, Mink lib gul tm s (n4 (A 6) fc fa fb) r ∧ ReturnsC lib O cc gul Inv ν st regs t (jmp0 g3.bo) r
    cases rb with
    | zero p =>
      by_cases h0 : p = A 0
      · subst h0
        obtain ⟨G0, -, -⟩ := Gc
        obtain ⟨st', regs', hI', hν, -, k2, e2⟩ := G0 rfl
        obtain ⟨r, hr, G⟩ := sixBlk_bwd Ra hN hS hB hcf2 (by omega) hned hs yesB agA hI' (frames_mono hν htr)
          (HoldsN.agree ned (fun x hx => k2 x ⟨Or.inr hx, fun e => e⟩) hn) ((e0.trans e2).symm.trans hres)
        exact ⟨r, MB.2.1 r rfl hr, returnsC_step hν (e0.trans e2) G⟩
      · by_cases h1 : p = A 1
        · subst h1
          obtain ⟨-, G1, -⟩ := Gc
          obtain ⟨st', regs', hI', hν, -, k2, e2⟩ := G1 rfl
          obtain ⟨r, hr, G⟩ := sixBlk_bwd Rb hN hS hB hcf1 (by omega) hned hs nuhB agB hI' (frames_mono hν htr)
            (HoldsN.agree ned (fun x hx => k2 x ⟨Or.inr hx, fun e => e⟩) hn) ((e0.trans e2).symm.trans hres)
          exact ⟨r, MB.2.2.1 r rfl hr, returnsC_step hν (e0.trans e2) G⟩
        · obtain ⟨-, -, G2⟩ := Gc
          exact ⟨_, MB.2.2.2 p rfl h0 h1, returnsC_step (Needs.le_refl _) e0 (G2 h0 h1)⟩
    | one q => exact ⟨_, MB.1 (fun _ e => by cases e), returnsC_step (Needs.le_refl _) e0 Gc⟩
    | two q => exact ⟨_, MB.1 (fun _ e => by cases e), returnsC_step (Needs.le_refl _) e0 Gc⟩
  · -- the bound
    rw [entries_copy_six]; simp only [List.length_append, List.length_cons]
    have e0 : (entries l0).length ≤ ka + 1 := by
      rcases hl01 with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · omega
      · rw [entries_wrap]; simp only [List.length_cons]; omega
    have e1 : (entries l1).length ≤ kb + 1 := by
      rcases hl01 with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · omega
      · rw [entries_wrap]; simp only [List.length_cons]; omega
    omega

end Comp
end SkaModel
end Formalization
