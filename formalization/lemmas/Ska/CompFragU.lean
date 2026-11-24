import lemmas.Ska.CompAboveX

/-!
# Proxy runs that compose: `RunOKV` and the fragment `FragU`

README Gaps 12.2.  `RunOKU` takes `AgreeU` by the run's own final `cond`.
A parent that runs a part which makes proxies and then runs more parts after
it ends with a `cond` that has more keys, all from the part's end on
(`CondFresh`).  `RunOKV` is `RunOKU` with its `sem` (`SemV`) taken against
every `cond` that agrees with the run's final one below the run's end, as
`CollRunU.sem` already is, so that the parent can pass its own final `cond`
down.

* `RunOKV.toU`: the case of the run's own `cond`.
* `RunOKP.toV`: a run that makes no proxy, from any state whose `cond` has
  its keys below `re` (`CondBelow`), meets `RunOKV` when its blocks mention
  registers from its start's `re` on (`AboveIn`) and below its end's
  (`BelowIn`), since unproxying leaves those registers alone.  So every run
  of `FragX` for `%done` and for `%pick` with jumps without arguments meets
  it (`okV_fragX`).
* `runOKV_seven4`: `[7 [4 p] q]` for `%done` from any state with `Clear`
  and `CondBelow`, not only `gen0` (`runOKU_seven4` generalized).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The relation -/

/-- **The `sem` of `RunOKU` against every later `cond`**: any `cf` that
agrees with the run's final `cond` below the run's end. -/
def SemV (lib : Lib) (nm : Nomm) (goal : CGoal S) (g0 g1 : Gen Map) (nex : NextL S) : Prop :=
  ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s0 s : Noun),
    AgreeU lib O c gul st t cf ned g0 g1 nex.laz s0 s → (∀ r, NMem ned r → g1.re ≤ r) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    GoalSem lib O c gul st (fun r => r < g0.re ∨ NMem ned r) regs t nex.th goal (pureEval nm s)

/-- **The relation for one run for `%done` or `%pick` that may make proxies
and composes**: the fields of `RunOKU` with the `sem` against every later
`cond` (`SemV`). -/
structure RunOKV (lib : Lib) (nm : Nomm) (goal : CGoal S) (g0 g1 : Gen Map) (nex : NextL S) : Prop where
  ext : Ext g0 g1
  grow : GrowU g0 g1
  cfr : CondFresh g0 g1
  lo : 1 ≤ nex.th.there
  hi : nex.th.there < g1.bo
  ent : Entry g1 goal nex.th
  regs : ∀ r, NMem nex.laz.sure.ned r → g0.re ≤ r ∧ r < g1.re
  dist : Distinct nex.laz.sure.ned
  eregs : ∀ e ∈ entries nex.laz, Distinct e.2.sure.ned ∧ ∀ r, NMem e.2.sure.ned r → g0.re ≤ r ∧ r < g1.re
  labs : ∀ e ∈ entries nex.laz, g0.bo ≤ e.1 ∧ e.1 < nex.th.there ∧
    ∃ th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩
  nodup : ((entries nex.laz).map Prod.fst).Nodup
  size : (entries nex.laz).length ≤ 2 * sixCount nm
  nec : ∀ s, ¬ FitsS nex.laz.sure s → pureEval nm s = none
  ncond : ∀ r, NMem nex.laz.sure.ned r → HoonMap.get g1.cond r = Option.none
  econd : ∀ e ∈ entries nex.laz, ∀ r, NMem e.2.sure.ned r → HoonMap.get g1.cond r = Option.none
  sem : SemV lib nm goal g0 g1 nex

/-- **`RunOKV` gives `RunOKU`**, the `sem` at the run's own `cond`. -/
theorem RunOKV.toU {lib : Lib} {nm : Nomm} {goal : CGoal S} {g0 g1 : Gen Map} {nex : NextL S}
    (R : RunOKV lib nm goal g0 g1 nex) : RunOKU lib nm goal g0 g1 nex :=
  ⟨R.ext, R.grow, R.cfr, R.lo, R.hi, R.ent, R.regs, R.dist, R.eregs, R.labs, R.nodup, R.size, R.nec, R.ncond,
    R.econd, fun c ned σ O st t gul s0 s ag hn regs hh h0 =>
      R.sem g1.cond (fun _ _ => rfl) c ned σ O st t gul s0 s ag hn regs hh h0⟩

/-- No key of `cond` from `re` on. -/
theorem condBelow_none {g : Gen Map} (h : CondBelow g) {x : Nat} (hx : g.re ≤ x) :
    HoonMap.get g.cond x = Option.none := by
  cases e : HoonMap.get g.cond x with
  | none => rfl
  | some _ => have := h x (by simp [e]); omega

/-- **A run that makes no proxy meets `RunOKV`** when its blocks mention
only registers allocated in it (`AboveIn` from its start's `re`, `BelowIn`)
and the keys of `cond` lie below its start's `re`. -/
theorem RunOKP.toV {lib : Lib} {nm : Nomm} {goal : CGoal S} {g0 g1 : Gen Map} {nex : NextL S}
    (R : RunOKP lib nm goal g0 g1 nex) (hb : BelowIn g0.bo g1) (ha : AboveIn g0.re g0.bo g1)
    (hcb : CondBelow g0) : RunOKV lib nm goal g0 g1 nex := by
  have nk : ∀ x, g0.re ≤ x → HoonMap.get g1.cond x = Option.none := fun x hx => by
    rw [R.cnd]; exact condBelow_none hcb hx
  refine ⟨R.ext, R.grow, condFresh_of_eq R.ext.1 R.cnd, R.lo, R.hi, R.ent, R.regs, R.dist, R.eregs, R.labs,
    R.nodup, R.size, R.nec, fun r hr => nk r (R.regs r hr).1, fun e he r hr => nk r ((R.eregs e he).2 r hr).1, ?_⟩
  intro cf hcf c ned σ O st t gul s0 s ag hned regs hh hn
  have u0 : ∀ x, x < g1.re → unproxy cf x = unproxy g1.cond x := unproxy_agree hcf
  have u1 : ∀ x, g0.re ≤ x → unproxy g1.cond x = id x := fun x hx => unproxy_none (nk x hx)
  have hlab : ∀ e ∈ entries nex.laz, g0.bo ≤ e.1 ∧ e.1 < g1.bo := fun e he =>
    ⟨(R.labs e he).1, Nat.lt_trans (R.labs e he).2.1 R.hi⟩
  refine R.sem c ned σ O st t gul s0 s ⟨fun o l u hnl => ?_, fun e he => ?_⟩ hned regs hh hn
  · rw [ag.1 o l u hnl]
    cases hg : HoonMap.get g1.blocks o with
    | none => rfl
    | some b =>
      simp only [Option.map_some]
      rw [unproxyBlob, renBlob_congr u0 (hb o b l u hg), renBlob_congr u1 (ha o b l u hg), renBlob_id]
  · obtain ⟨A, th, h1, h2, h3⟩ := ag.2 e he
    refine ⟨A, th, h1, ?_, h3⟩
    rw [h2, renJmp_congr u0 (hb e.1 _ (hlab e he).1 (hlab e he).2 h1).2.2,
      renJmp_congr u1 (ha e.1 _ (hlab e he).1 (hlab e he).2 h1).2.2, renJmp_id]

/-- **What the induction proves for `%done` and `%pick`**: every run meets
`RunOKV`, from a state with `Clear` and `CondBelow`. -/
abbrev OKV (lib : Lib) (goal : CGoal S) (nm : Nomm) : Prop :=
  ∀ {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}, NotNext goal → GJ g0.bo goal →
    sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    runL nm (CGoal.toL goal) region g0 = some (nex, g1) → RunOKV (Map := Map) lib nm goal g0 g1 nex

/-- **Every run of `FragX` for `%done`, and for `%pick` with jumps without
arguments, meets `RunOKV`.** -/
theorem okV_fragX (lib : Lib) {nm : Nomm} (hf : FragX (S := S) nm) :
    OKV (Map := Map) lib (CGoal.done : CGoal S) nm ∧
    ∀ z o : Jmp, z.args = [] → o.args = [] → OKV (Map := Map) lib (CGoal.pick z o : CGoal S) nm :=
  ⟨fun hg hj hc b0 d0 hu _ hcb h => ((runX_ok lib hf).1 hg hj hc b0 d0 hu h).toV
      (runX_below (goal := CGoal.done) hf d0 trivial hc h)
      (runX_above (goal := CGoal.done) hf d0 trivial trivial (Nat.le_refl _) hc h) hcb,
    fun z o hz ho => fun hg hj hc b0 d0 hu _ hcb h => ((runX_ok lib hf).2.2 z o hz ho hg hj hc b0 d0 hu h).toV
      (runX_below (goal := CGoal.pick z o) hf d0 ⟨jmpIn_nil hz, jmpIn_nil ho⟩ hc h)
      (runX_above (goal := CGoal.pick z o) hf d0 ⟨jmpIn_nil hz, jmpIn_nil ho⟩ ⟨jmpIn_nil hz, jmpIn_nil ho⟩
        (Nat.le_refl _) hc h) hcb⟩

/-! ## `[7 [4 p] q]` from any state -/

/-- **`[7 [4 p] q]` for `%done` meets `RunOKV` from any state** with
`Clear` and `CondBelow`, for every `q` in `FragX` (`runOKU_seven4`, which
starts from `gen0`, generalized).  The blocks of `q` mention only registers
allocated in `q`'s run (`runX_above`, `runX_below`), and no key of a later
`cond` lies there: below `q`'s start they are keys of the start's `cond`,
from it on `q` and the collapse made none below `q`'s end. -/
theorem runOKV_seven4 (lib : Lib) {p q : Nomm} (hp : NextOK (S := S) (Map := Map) lib p)
    (sp : OKNR (S := S) (Map := Map) lib p) (kp : KeepX S Map p) (ap : AboveX S Map p)
    (hq : FragX (S := S) q) (hcount : sixCount (Nomm.n7 (Nomm.n4 p) q) ≤ 255) {region : List Nat}
    {g0 g2 : Gen Map} {nex : NextL S} (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0)
    (hcl0 : Clear g0) (hcb0 : CondBelow g0)
    (h : runL (Nomm.n7 (Nomm.n4 p) q) (CGoalL.done : CGoalL S) region g0 = some (nex, g2)) :
    RunOKV (Map := Map) lib (Nomm.n7 (Nomm.n4 p) q) CGoal.done g0 g2 nex := by
  have hc : sixCount p ≤ 255 ∧ sixCount q ≤ 255 := by simp only [sixCount] at hcount; omega
  have p7 : ∀ s, pureEval (Nomm.n7 (Nomm.n4 p) q) s = (pureEval (Nomm.n4 p) s).bind (pureEval q) := fun _ => rfl
  rw [runL_n7] at h
  obtain ⟨nx, g1, h1, h2⟩ := bind_some h
  have Rq := (runX_ok (Map := Map) lib hq).1 trivial trivial hc.2 b0 d0 hu h1
  have Sq := SemPR.toG ((runX_semR (Map := Map) lib hq).1 trivial trivial trivial hc.2 b0 d0 hu hcl0 h1)
  have Bq : BelowIn g0.bo g1 := runX_below (goal := CGoal.done) hq d0 trivial hc.2 h1
  have Aq : AboveIn g0.re g0.bo g1 := runX_above (goal := CGoal.done) hq d0 trivial trivial (Nat.le_refl _) hc.2 h1
  obtain ⟨q1, q2, q3, q4⟩ := Rq.ext
  have nk1 : ∀ x, g0.re ≤ x → HoonMap.get g1.cond x = Option.none := fun x hx => by
    rw [Rq.cnd]; exact condBelow_none hcb0 hx
  have hcb1 : CondBelow g1 := (condFresh_of_eq q1 Rq.cnd).below hcb0
  have qlo := Rq.lo
  have qhi := Rq.hi
  obtain ⟨d, CR⟩ := collRun_n4 lib hp sp kp ap h2 hc.1 (by omega) (q3.trans d0) (Rq.grow.up hu)
    (hcl0.growU Rq.grow) Rq.lo Rq.hi (fun x hx => (Rq.regs x hx).2) (fun x hx => nk1 x (Rq.regs x hx).1)
    hcb1
    (List.nodup_cons.mpr ⟨fun hm => by
      obtain ⟨e, he, e1⟩ := List.mem_map.mp hm
      have := (Rq.labs e he).2.1; omega, Rq.nodup⟩)
    (fun e he => by obtain ⟨a, b, th, hb⟩ := Rq.labs e he; exact ⟨by omega, [], _, hb⟩)
    (fun e he x hx => ((Rq.eregs e he).2 x hx).2)
  have Cre := CR.re
  have Cbo := CR.bo
  have Cdl := CR.dlt
  refine ⟨⟨by omega, by omega, CR.drop.trans q3, fun o ho => (CR.keep o (by omega) (fun hm => ?_)).trans (q4 o ho)⟩,
    Rq.grow.trans CR.grow, (condFresh_of_eq q1 Rq.cnd).trans CR.pfor.1, CR.lo, CR.hi, Or.inl CR.ent,
    fun r hr => ⟨by have := (CR.regs r hr).1; omega, (CR.regs r hr).2⟩, CR.dist,
    fun e he => ⟨(CR.eregs e he).1, fun r hr => ⟨by have := ((CR.eregs e he).2 r hr).1; omega,
      ((CR.eregs e he).2 r hr).2⟩⟩,
    fun e he => ⟨by have := (CR.labs e he).1; omega, (CR.labs e he).2⟩, CR.nodup,
    by have := CR.size; simp only [sixCount] at this ⊢; omega,
    fun s hs' => by rw [p7, CR.nec s hs']; rfl, CR.ncond, CR.econd, ?_⟩
  · obtain ⟨e, he, e1⟩ := List.mem_map.mp hm
    have := (Rq.labs e he).1; omega
  intro cf hcf c ned σ O st t gul s0 s ag hned regs hh hn
  have agC : AgreeU lib O c gul st t cf ned g1 g2 nex.laz s0 s :=
    ⟨fun o l u hnl => ag.1 o (by omega) u hnl, ag.2⟩
  have Sp := CR.sem cf hcf c ned σ O st t gul s0 s agC (fun r hr => Or.inl (hned r hr)) regs hh hn
  have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk =>
    (hcf k (by omega)).trans (ProxyFor.get_lt CR.pfor hk)
  have u0 : ∀ x, x < g1.re → unproxy cf x = unproxy g1.cond x := unproxy_agree hcf1
  have u1 : ∀ x, g0.re ≤ x → unproxy g1.cond x = id x := fun x hx => unproxy_none (nk1 x hx)
  show GoalSem lib O c gul st _ regs t nex.th CGoal.done (pureEval (Nomm.n7 (Nomm.n4 p) q) s)
  cases ev : pureEval (Nomm.n4 p) s with
  | none =>
    rw [ev] at Sp
    have e7 : pureEval (Nomm.n7 (Nomm.n4 p) q) s = none := by rw [p7, ev]; rfl
    rw [e7]; exact goalSem_none _ Sp
  | some v =>
    rw [ev] at Sp
    have e7 : pureEval (Nomm.n7 (Nomm.n4 p) q) s = pureEval q v := by rw [p7, ev]; rfl
    rw [e7]
    obtain ⟨m, rfl⟩ : ∃ m, v = A m := by
      rw [pureEval_n4] at ev
      cases ep : pureEval p s with
      | none => rw [ep] at ev; cases ev
      | some x =>
        rw [ep] at ev
        cases x with
        | atom n => simp [incF] at ev; exact ⟨n + 1, ev.symm⟩
        | cell _ _ => simp [incF] at ev
    by_cases fit : FitsS nx.laz.sure (A m)
    · have hfa : ∀ v, FitsS nx.laz.sure (A v) := CR.dich.elim id (fun hn' => absurd fit (hn' m))
      have SpT := CR.semT hfa cf hcf c ned σ O st t gul s0 s agC
        (fun r hr => Or.inl (hned r hr)) regs hh hn
      rw [ev] at SpT
      obtain ⟨R, hR, kR, eR⟩ := SpT.1 ⟨trivial, looks_empty _⟩
      have hR' : SkaModel.read d R = some (A m) := hR
      have agQ : AgreeP lib O c gul st t (Need.pair ned (Need.this d)) g0 g1 nx.laz (C s0 (A m)) (A m) := by
        refine ⟨fun o l u hnl => ?_, fun e he => ?_⟩
        · have hn2 : o ∉ (entries nex.laz).map Prod.fst := fun hm => by
            obtain ⟨e', he', e1⟩ := List.mem_map.mp hm; have := (CR.labs e' he').1; omega
          rw [ag.1 o l (by omega) hn2, CR.keep o u hnl]
          cases hg : HoonMap.get g1.blocks o with
          | none => rfl
          | some b =>
            simp only [Option.map_some]
            rw [unproxyBlob, renBlob_congr u0 (Bq o b l u hg), renBlob_congr u1 (Aq o b l u hg), renBlob_id]
        · obtain ⟨l, lt, th, hb⟩ := Rq.labs e he
          obtain ⟨F, hF, hP⟩ := CR.front e he
          have hb2 := hF [] (Termin.hop th) hb
          rw [List.append_nil] at hb2
          have hn2 : e.1 ∉ (entries nex.laz).map Prod.fst := fun hm => by
            obtain ⟨e', he', e1⟩ := List.mem_map.mp hm; have := (CR.labs e' he').1; omega
          refine ⟨F.map (renPole (unproxy cf)), th, hb, ?_, ?_⟩
          · rw [ag.1 e.1 l (by omega) hn2, hb2]
            have hj := (Bq e.1 _ l (by omega) hb).2.2
            have hj' := (Aq e.1 _ l (by omega) hb).2.2
            simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, renFin]
            rw [renJmp_congr u0 hj, renJmp_congr u1 hj', renJmp_id]
          · exact collP_fillSem hP ((hcf d Cdl).trans CR.dkey)
              (fun x hx => by
                have hx1 := ((Rq.eregs e he).2 x hx)
                rw [hcf x (by omega), ProxyFor.get_lt CR.pfor hx1.2]; exact nk1 x hx1.1)
              (fun k hk => hcf k hk) lib O c gul st t ned g1.re s0 m
      have inQ : ∀ r, NMem (Need.pair ned (Need.this d)) r → InR (CGoal.done : CGoal S) g0 g1 nx.laz.sure.ned r := by
        intro r hr
        rcases hr with hr | hr
        · exact Or.inl (by have := hned r hr; omega)
        · have hr' : r = d := hr
          rw [hr']
          rcases CR.dreg with e | e
          · exact Or.inr (Or.inr e)
          · exact Or.inl e
      have hnR : HoldsN (Need.pair ned (Need.this d)) R (C s0 (A m)) :=
        ⟨HoldsN.agree ned (fun r hr => kR r (Or.inr hr)) hn, hR'⟩
      have Sq' := Sq c _ σ O st t gul _ _ agQ inQ R (CR.dhold hfa R m hR') hnR
      exact eR.trans Sq'
    · have cr := Sp.2 fit
      rw [Rq.nec (A m) fit]
      exact goalSem_crash _ cr

end Comp
end SkaModel
end Formalization
