import lemmas.Compiler.CompRunDirectC

/-!
# The direct call of the case `%2` of `+run`: the parts and the result

README Gaps 19.  The call `crDCall` under `mono` `|` (`comp_run_n2_call`)
took the runs of `p` and `q` as hypotheses (`hpq`).  Here they come from
`PartL` of `p` and `q`, as for the dropped call (`comp_run_n2_drop`):

* `km_crdBlockM`: the blocks of step `7` keep the counters' order, `drop`
  and the tags (`emit`, `+simple-next`, `+kerf`).
* `linv_need`: the goal `[%next (lazy-from-need sub-ned) _]` of `p` meets
  `LInv` when the registers of `sub-ned` are distinct and below the counter
  (`needOrdAllocRegs_spec`).
* `crd_hpq`: `hpq` from `PartL` (`q` through `ginv_bunt_j`, `p` through
  `tail_pgoal`, `CopyH` through `tail_copyH`).
* `res_n2_call`: what the call returns meets `GRes` (`tail_res`).
* `comp_run_n2_callM`: the call as `CompRunAtM` (every `x` with `NoSoft`
  and `CallNoun`), on every goal with `GInv`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

variable {ctx : Noun}

/-- **The blocks of step `7`** keep the counters' order, `drop` and the tags. -/
theorem km_crdBlockM (b : Bell) (subV : List Nat) (goal : CGoalL CSet) :
    KM (crdBlockM b subV goal : CM (TreapMap mugF) Nat) := by
  cases goal with
  | done => exact KM.emit' _
  | next laz th =>
    exact KM.bind' (km_simpleNextL _) fun nex => KM.bind' (km_kerf nex) fun r => by
      obtain ⟨out, pro⟩ := r; exact KM.emit' _
  | pick z o =>
    exact KM.bind' (km_simpleNextL _) fun nex => KM.bind' (km_kerf nex) fun r => by
      obtain ⟨out, pro⟩ := r; exact KM.emit' _

/-- **The goal of a need with fresh registers**: `[[ned ~] ~ ~]` meets `LInv`
when the registers of `ned` are distinct and below the counter. -/
theorem linv_need {kr kb : Nat} {ned : Need} (hn : NB kr ned) (hd : Distinct ned) :
    LInv kr kb (Lazy.ofSure (⟨ned, HoonSet.empty⟩ : Sure CSet)) :=
  ⟨⟨⟨fun y hy => absurd hy (HoonSet.mem_empty y), hn⟩, trivial, trivial⟩,
    by rw [lregs_ofSure]; exact (distinct_iff_nodup _).1 hd, lkeys_ofSure _, by simp [llabs_ofSure]⟩

/-- The goals of the call's two runs, at the state after the blocks: `q`'s
`[%next *need-lazy ~ call-block]` meets `GInv`, `p`'s need
`(lazy-from-need sub-ned)` meets `LInv`, and the counters moved up. -/
theorem crd_goals {nb : NeedOrd} {b : Bell} {goal : CGoalL CSet} {g g1 g2 : Gen (TreapMap mugF)} {subNed : Need}
    {cb : Nat} (hinv : GInv g goal) (e : needOrdAllocRegs nb g = some (subNed, g1))
    (eb : crdBlockM b (flattenNeed subNed) goal g1 = some (cb, g2)) :
    GInv g2 (CGoalL.next (Lazy.ofSure Sure.bunt) (jmp0 cb)) ∧
      LInv g2.re g2.bo (Lazy.ofSure (⟨subNed, HoonSet.empty⟩ : Sure CSet)) ∧
      g.re ≤ g2.re ∧ g.bo ≤ g2.bo ∧ ∀ r, NMem subNed r → g.re ≤ r := by
  obtain ⟨⟨k, hk⟩, hre, hdist, hmem⟩ := needOrdAllocRegs_spec nb g g1 subNed e
  have hd0 : g.drop = false := ginv_drop hinv
  subst hk
  obtain ⟨l2, b2, d2⟩ := km_drop (km_crdBlockM _ _ _) eb hd0
  refine ⟨ginv_bunt_j d2 (jmpIn_jmp0 _ _), linv_need (fun r hr => ?_) hdist, by simp at l2 hre ⊢; omega,
    by simpa using b2, fun r hr => (hmem r hr).1⟩
  have := (hmem r hr).2
  simp at l2 this
  omega

/-- **The runs of `p` and `q` of the call from `PartL`** (the hypothesis
`hpq` of `comp_run_n2_call`), at any `sup`. -/
theorem crd_hpq (env : CallEnv) (msup : Option Nomm) (p q : Nomm) {region : List Nat}
    (P : PartL env msup ctx p region) (Q : PartL env msup ctx q region) (b : Bell) (nb : NeedOrd)
    (goal : CGoalL CSet) (g : Gen (TreapMap mugF)) (hinv : GInv g goal) (x : GenRest) (hx : x.NoSoft)
    (sup : Noun) :
    ∀ subNed g1, needOrdAllocRegs nb g = some (subNed, g1) →
      (∀ cb g2, crdBlockM b (flattenNeed subNed) goal g1 = some (cb, g2) →
        RunAt env msup ctx x (A 1) sup q (CGoalL.next (Lazy.ofSure Sure.bunt) (jmp0 cb)) region g2) ∧
      (∀ cb g2 nexF g3 nexF' g4, crdBlockM b (flattenNeed subNed) goal g1 = some (cb, g2) →
        crdFq env msup q (jmp0 cb) region g2 = some (nexF, g3) → pastL noCode nexF p region g3 = some (nexF', g4) →
        RunAt env msup ctx x (A 1) sup p (CGoalL.next (Lazy.ofSure ⟨subNed, HoonSet.empty⟩) nexF'.th) region g4) ∧
      (∀ cb g2 nexF g3 nexF' g4 nexS g5, crdBlockM b (flattenNeed subNed) goal g1 = some (cb, g2) →
        crdFq env msup q (jmp0 cb) region g2 = some (nexF, g3) → pastL noCode nexF p region g3 = some (nexF', g4) →
        runLC env msup p (CGoalL.next (Lazy.ofSure ⟨subNed, HoonSet.empty⟩) nexF'.th) region g4 = some (nexS, g5) →
        CopyH g5.re nexS.laz nexF'.laz) := by
  intro subNed g1 e
  refine ⟨fun cb g2 eb => Q.link _ g2 (crd_goals hinv e eb).1 x _ _ hx,
    fun cb g2 nexF g3 nexF' g4 eb ef e3 => ?_, fun cb g2 nexF g3 nexF' g4 nexS g5 eb ef e3 e4 => ?_⟩
  · obtain ⟨hq2, hp2, -⟩ := crd_goals hinv e eb
    exact P.link _ _ (tail_pgoal hq2 hp2 (crd_fq_res Q.res hq2.2.1 hq2.2.2 ef) e3).1 x _ _ hx
  · obtain ⟨hq2, hp2, -⟩ := crd_goals hinv e eb
    have R2 := crd_fq_res Q.res hq2.2.1 hq2.2.2 ef
    have ap : (lregs (Lazy.ofSure (⟨subNed, HoonSet.empty⟩ : Sure CSet)) ++ lregs (Lazy.ofSure (Sure.bunt : Sure CSet))).Nodup := by
      rw [lregs_bunt, List.append_nil]; exact hp2.2.1
    exact (tail_copyH hq2 hp2 ap R2 e3 (P.res _ _ _ _ (tail_pgoal hq2 hp2 R2 e3).1 e4)).1

/-- **What the call returns** (`GRes`): a direct call with no key, not
dropped, no ring, `env.need b = some nb`, `sof` false, on every goal with
`GInv`. -/
theorem res_n2_call {env : CallEnv} {msup : Option Nomm} {p q : Nomm} {region : List Nat}
    (ihp : ResFor env msup p region) (ihq : ResFor env msup q region) (hpl : PlainOk p = true)
    {b : Bell} {nb : NeedOrd} {goal : CGoalL CSet} (hdr : crdDrop (env.pure b) goal = false)
    (hri : env.ring b = Option.none) (hnb : env.need b = some nb) (hsof : env.sof (made p msup) p q b nb = false)
    {g g' : Gen (TreapMap mugF)} {nex : NextL CSet} (hi : GInv g goal)
    (h : runLC env msup (Nomm.n2 p q (some (b, Option.none))) goal region g = some (nex, g')) :
    GRes g goal g' nex := by
  obtain ⟨hpc, -⟩ := hinted_plain env.cod hpl
  rw [crd_model_call env msup p q b nb goal region hdr hri hnb hsof hpc] at h
  obtain ⟨subNed, g1, e, h⟩ := bind_some h
  unfold crdCallM at h
  obtain ⟨cb, g2, eb, h⟩ := bind_some h
  unfold crdTailM at h
  simp only [crdArg] at h
  obtain ⟨nexF, g3, ef, h⟩ := bind_some h
  obtain ⟨nexF', g4, e3, h⟩ := bind_some h
  obtain ⟨nexS, g5, e4, e5⟩ := bind_some h
  obtain ⟨hq2, hp2, l2, b2, hm⟩ := crd_goals hi e eb
  have R2 := crd_fq_res ihq hq2.2.1 hq2.2.2 ef
  have P3 := tail_pgoal hq2 hp2 R2 e3
  have ap : (lregs (Lazy.ofSure (⟨subNed, HoonSet.empty⟩ : Sure CSet)) ++ lregs (Lazy.ofSure (Sure.bunt : Sure CSet))).Nodup := by
    rw [lregs_bunt, List.append_nil]; exact hp2.2.1
  obtain ⟨l, bb, i, s⟩ := tail_res hq2 hp2 ap R2 e3 (ihp _ _ _ _ P3.1 e4) e5
  refine ⟨Nat.le_trans l2 l, Nat.le_trans b2 bb, i, fun r hr => ?_⟩
  rcases s r hr with e' | e'
  · rw [lregs_bunt, List.append_nil, lregs_ofSure] at e'
    exact Or.inl (hm r ((mem_flat _ _).1 e'))
  · exact Or.inl (Nat.le_trans l2 e')

/-- **The case `%2` on a direct call that emits a block, as `CompRunAtM`**
(README Gaps 19): at `mono` `|` and `sup` the noun of `msup`, for every rest
`x` of the state with `NoSoft` and `CallNoun` (for some `sur`), on every goal
with `GInv`; `p` and `q` as `PartL`.  The callee `b` has no memo key, its
code entry has `pure` `env.pure b` (`CodePure`), the call is not dropped, no
ring, `env.need b = some nb`, `sof` false. -/
theorem comp_run_n2_callM (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm) {region : List Nat} (P : PartL env msup ctx p region)
    (Q : PartL env msup ctx q region) (b : Bell) (hcd : CodePure cod env b) (nb : NeedOrd) (goal : CGoalL CSet)
    (g : Gen (TreapMap mugF)) (hinv : GInv g goal) (hdr : crdDrop (env.pure b) goal = false)
    (hri : env.ring b = Option.none) (hnb : env.need b = some nb) (hsof : env.sof (made p msup) p q b nb = false) :
    CompRunAtM env msup ctx (fun x => ∃ sur, CallNoun msup ctx p q b nb sur x) (Nomm.n2 p q (some (b, Option.none)))
      goal region g := by
  intro x hx ⟨sur, hn⟩
  exact comp_run_n2_call h7 hcode env msup p q P.plain b hcd nb sur goal region g hinv hdr hri hnb hsof x hx hn
    (crd_hpq env msup p q P Q b nb goal g hinv x hx _)

end Compiler
end Formalization
