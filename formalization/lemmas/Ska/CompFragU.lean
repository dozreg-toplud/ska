import lemmas.Ska.CompAboveX

/-!
# Proxy runs that compose: `RunOKV`

The fragment `FragU`, its joint induction and the top theorem are in
`CompFragUJ.lean` (since the tenth session, when `FragU` gained cons).

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
    (R : RunOKP lib nm goal g0 g1 nex) (hb : BelowIn g0.bo g1) (ha : AboveIn (g0.re ≤ ·) g0.bo g1)
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
      (runX_above (goal := CGoal.done) hf d0 trivial trivial (ple_le (Nat.le_refl _)) hc h) hcb,
    fun z o hz ho => fun hg hj hc b0 d0 hu _ hcb h => ((runX_ok lib hf).2.2 z o hz ho hg hj hc b0 d0 hu h).toV
      (runX_below (goal := CGoal.pick z o) hf d0 ⟨jmpIn_nil hz, jmpIn_nil ho⟩ hc h)
      (runX_above (goal := CGoal.pick z o) hf d0 ⟨jmpIn_nil hz, jmpIn_nil ho⟩ ⟨jmpIn_nil hz, jmpIn_nil ho⟩
        (ple_le (Nat.le_refl _)) hc h) hcb⟩

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
  have Aq : AboveIn (g0.re ≤ ·) g0.bo g1 :=
    runX_above (goal := CGoal.done) hq d0 trivial trivial (ple_le (Nat.le_refl _)) hc.2 h1
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

/-- **`[7 [4 p] q]` for `%pick` with jumps without arguments meets
`RunOKV` from any state** with `Clear` and `CondBelow`, for every `q` in
`FragX`: `runOKV_seven4` with `q` run for the `%pick`, the keep sets
composed through `goalSem_pre`. -/
theorem runOKV_seven4P (lib : Lib) {p q : Nomm} (hp : NextOK (S := S) (Map := Map) lib p)
    (sp : OKNR (S := S) (Map := Map) lib p) (kp : KeepX S Map p) (ap : AboveX S Map p)
    (hq : FragX (S := S) q) (hcount : sixCount (Nomm.n7 (Nomm.n4 p) q) ≤ 255) {region : List Nat}
    {g0 g2 : Gen Map} {nex : NextL S} {z o : Jmp} (hz : z.args = []) (ho : o.args = [])
    (hj : GJ g0.bo (CGoal.pick z o : CGoal S)) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0)
    (hcl0 : Clear g0) (hcb0 : CondBelow g0)
    (h : runL (Nomm.n7 (Nomm.n4 p) q) (CGoalL.pick z o : CGoalL S) region g0 = some (nex, g2)) :
    RunOKV (Map := Map) lib (Nomm.n7 (Nomm.n4 p) q) (CGoal.pick z o) g0 g2 nex := by
  have hc : sixCount p ≤ 255 ∧ sixCount q ≤ 255 := by simp only [sixCount] at hcount; omega
  have p7 : ∀ s, pureEval (Nomm.n7 (Nomm.n4 p) q) s = (pureEval (Nomm.n4 p) s).bind (pureEval q) := fun _ => rfl
  rw [runL_n7] at h
  obtain ⟨nx, g1, h1, h2⟩ := bind_some h
  have Rq := (runX_ok (Map := Map) lib hq).2.2 z o hz ho trivial hj hc.2 b0 d0 hu h1
  have Sq := SemPR.toG ((runX_semR (Map := Map) lib hq).2.2 z o hz ho trivial hj ⟨⟨hz, hj.1.2⟩, ho, hj.2.2⟩ hc.2
    b0 d0 hu hcl0 h1)
  have gin : GoalIn g0.re (CGoal.pick z o : CGoal S) := ⟨jmpIn_nil hz, jmpIn_nil ho⟩
  have Bq : BelowIn g0.bo g1 := runX_below (goal := CGoal.pick z o) hq d0 gin hc.2 h1
  have Aq : AboveIn (g0.re ≤ ·) g0.bo g1 :=
    runX_above (goal := CGoal.pick z o) hq d0 gin ⟨jmpIn_nil hz, jmpIn_nil ho⟩ (ple_le (Nat.le_refl _)) hc.2 h1
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
      have inQ : ∀ r, NMem (Need.pair ned (Need.this d)) r → InR (CGoal.pick z o : CGoal S) g0 g1 nx.laz.sure.ned r := by
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
      refine goalSem_pre (fun r hr => ?_) eR _ _ (goalSem_mono (fun r hr => ?_) _ _ Sq')
      · rcases hr with hr | hr
        · refine kR r (Or.inl ⟨by omega, fun hm' => ?_⟩)
          have := (Rq.regs r hm').1; omega
        · exact kR r (Or.inr hr)
      · rcases hr with hr | hr
        · exact Or.inl ⟨hr, fun h => h⟩
        · exact Or.inr (Or.inl hr)
    · have cr := Sp.2 fit
      rw [Rq.nec (A m) fit]
      exact goalSem_crash _ cr

/-! ## `%6` for `%done` and `%pick` -/

/-- A jump without arguments is not renamed. -/
theorem renJmp_nil (u : Nat → Nat) {j : Jmp} (h : j.args = []) : renJmp u j = j := by
  rcases j with ⟨args, there⟩
  simp only at h
  subst h
  rfl

/-- **`[6 c a b]` for `%done` or `%pick` with parts that make proxies**,
from `RunOKV` of the test for `%pick` and of the branches for the goal
(`sixP_ok` with `cond` growing by fresh proxies).  Each part's `sem` is
taken at the `cond` of the whole run's end through `CondFresh.get_lt`, and
the hops of the yes and no blocks and of the test's end pass no argument, so
unproxying leaves them alone. -/
theorem sixP_okV (lib : Lib) {goal : CGoal S} {c a b : Nomm} (hcp : c.pure = true)
    (ihc : ∀ z o : Jmp, z.args = [] → o.args = [] → OKV (Map := Map) lib (CGoal.pick z o : CGoal S) c)
    (iha : OKV (Map := Map) lib goal a) (ihb : OKV (Map := Map) lib goal b) :
    OKV (Map := Map) lib goal (Nomm.n6 c a b) := by
  intro region g0 g4 nex hg hj hcount b0 d0 hu hcl0 hcb0 h
  rw [runL_n6_body c a b hg] at h
  obtain ⟨x1, x0, xc, g1, g2, g3, h1, h2, hx0a, hx1a, h3, hrest⟩ := sixBody_apart hcp h
  simp only [sixCount] at hcount
  have Rb := ihb hg hj (by omega) b0 d0 hu hcl0 hcb0 h1
  have u1 : UpBelow g1 := Rb.grow.up hu
  have d1 : g1.drop = false := Rb.ext.2.2.1.trans d0
  have b01 : g0.bo ≤ g1.bo := Rb.ext.2.1
  have b1 : 1 ≤ g1.bo := Nat.le_trans b0 b01
  have cl1 : Clear g1 := hcl0.growU Rb.grow
  have cb1 : CondBelow g1 := Rb.cfr.below hcb0
  have Ra := iha hg (hj.mono b01) (by omega) b1 d1 u1 cl1 cb1 h2
  have cl2 : Clear g2 := cl1.growU Ra.grow
  have cb2 : CondBelow g2 := Ra.cfr.below cb1
  have u2 : UpBelow g2 := Ra.grow.up u1
  have d2 : g2.drop = false := Ra.ext.2.2.1.trans d1
  have b12 : g1.bo ≤ g2.bo := Ra.ext.2.1
  have GU : GrowU g2 (sixGenL g2 x0.th x1.th region) := (grow_sixGenL region (jumpsBelow_hop Ra.lo Ra.hi)
    (jumpsBelow_hop Rb.lo (by have := Rb.hi; omega))).toU u2
  have uG : UpBelow (sixGenL g2 x0.th x1.th region) := GU.up u2
  have hbig : lazyBig (mk (Sure.bunt : Sure S) [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))] []) = false := by
    apply lazyBig_entries
    rw [entries_six]; simp only [List.length_append, List.length_cons]
    have := Ra.size; have := Rb.size; simp only [lazyMax]; omega
  -- the test
  have dG : (sixGenL g2 x0.th x1.th region).drop = false := by simp [d2]
  have Rc := ihc (jmp0 g2.bo) (jmp0 (g2.bo + 1)) rfl rfl trivial
    ⟨⟨by simp only [jmp0]; omega, by simp only [jmp0, sixGenL_bo]; omega⟩,
      by simp only [jmp0]; omega, by simp only [jmp0, sixGenL_bo]; omega⟩ (by omega)
    (by simp only [sixGenL_bo]; omega) dG uG (cl2.growU GU)
    (fun k hk => by simp only [sixGenL_cond, sixGenL_re] at hk ⊢; exact cb2 k hk) h3
  have u3 : UpBelow g3 := Rc.grow.up uG
  have d3 : g3.drop = false := Rc.ext.2.2.1.trans dG
  have bG3 : g2.bo + 2 ≤ g3.bo := by have := Rc.ext.2.1; simpa using this
  have hap : ∀ e ∈ xc.laz.fork, e.1.1 ≠ g2.bo := fun e he => by
    have hm : e.1 ∈ entries xc.laz := by rw [entries_eq]; exact List.mem_append_right _ (fork_mem_entries he)
    have := (Rc.labs _ hm).1; simp only [sixGenL_bo] at this; omega
  have hcp := hrest hbig
  rw [copyL_six_apart xc x0.laz x1.laz g2.bo (g2.bo + 1) g3 hap] at hcp
  obtain ⟨⟨u, g4'⟩, hadd, e4⟩ := Option.map_eq_some_iff.mp hcp
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
  have h42 : ∀ k, k < g2.bo → HoonMap.get g4'.blocks k = HoonMap.get g2.blocks k := E24.2.2.2
  have h41 : ∀ k, k < g1.bo → HoonMap.get g4'.blocks k = HoonMap.get g1.blocks k := E14.2.2.2
  -- the labels
  have lc : ∀ e ∈ entries xc.laz, g2.bo + 2 ≤ e.1 ∧ e.1 < g3.bo := fun e he => by
    have := Rc.labs e he; have := Rc.hi; simp only [sixGenL_bo] at *; omega
  have la : ∀ e ∈ entries x0.laz, g1.bo ≤ e.1 ∧ e.1 < g2.bo := fun e he =>
    ⟨(Ra.labs e he).1, Nat.lt_trans (Ra.labs e he).2.1 Ra.hi⟩
  have lb : ∀ e ∈ entries x1.laz, g0.bo ≤ e.1 ∧ e.1 < g1.bo := fun e he =>
    ⟨(Rb.labs e he).1, Nat.lt_trans (Rb.labs e he).2.1 Rb.hi⟩
  have lc' := labels_bound (P := fun o => g2.bo + 2 ≤ o ∧ o < g3.bo) lc
  have la' := labels_bound (P := fun o => g1.bo ≤ o ∧ o < g2.bo) la
  have lb' := labels_bound (P := fun o => g0.bo ≤ o ∧ o < g1.bo) lb
  have en := entries_copy_six xc.laz (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
    g2.bo (g2.bo + 1) x0.laz x1.laz
  have memE : ∀ e, e ∈ entries (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
      (xc.laz.fork ++ [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))]) xc.laz.bond) ↔
      e ∈ entries xc.laz ∨ e = (g2.bo, x0.laz) ∨ e ∈ entries x0.laz ∨ e = (g2.bo + 1, x1.laz) ∨
        e ∈ entries x1.laz := by
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
      (xc.laz.fork ++ [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))]) xc.laz.bond),
      (g2.bo + 2 ≤ e.1 ∧ e.1 < g3.bo ∧ e ∈ entries xc.laz) ∨ e.1 = g2.bo ∨
      (g1.bo ≤ e.1 ∧ e.1 < g2.bo ∧ e ∈ entries x0.laz) ∨ e.1 = g2.bo + 1 ∨
      (g0.bo ≤ e.1 ∧ e.1 < g1.bo ∧ e ∈ entries x1.laz) := by
    intro e he
    rcases (memE e).mp he with h | h | h | h | h
    · exact Or.inl ⟨(lc e h).1, (lc e h).2, h⟩
    · exact Or.inr (Or.inl (by rw [h]))
    · exact Or.inr (Or.inr (Or.inl ⟨(la e h).1, (la e h).2, h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [h]))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨(lb e h).1, (lb e h).2, h⟩)))
  have reC : ∀ r, g2.re ≤ r → r < g3.re → g0.re ≤ r ∧ r < g4'.re := fun r h1 h2 => ⟨by omega, by omega⟩
  have reB : ∀ r, g1.re ≤ r → r < g2.re → g0.re ≤ r ∧ r < g4'.re := fun r h1 h2 => ⟨by omega, by omega⟩
  have reA : ∀ r, g0.re ≤ r → r < g1.re → g0.re ≤ r ∧ r < g4'.re := fun r h1 h2 => ⟨h1, by omega⟩
  have hc43 : g4'.cond = g3.cond := by rw [(KC.addOps' _ _).keep _ _ _ hadd, emitted_cond]
  have cf34 : CondFresh g3 g4' := condFresh_of_eq E4.1 hc43
  have cfG : CondFresh g2 (sixGenL g2 x0.th x1.th region) :=
    condFresh_of_eq (by simp only [sixGenL_re]; omega) (by rw [sixGenL_cond])
  have cf24 : CondFresh g2 g4' := cfG.trans (Rc.cfr.trans cf34)
  have cf14 : CondFresh g1 g4' := Ra.cfr.trans cf24
  refine ⟨E04, ?_, Rb.cfr.trans cf14, by simp only [jmp0]; omega, by simp only [jmp0]; omega,
    Or.inl ⟨⟨[], [], Termin.hop xc.th⟩, h4o, rfl, rfl⟩, fun r hr => ?_, Rc.dist, ?_, ?_, ?_, ?_, fun s hs => ?_,
    fun r hr => by rw [hc43]; exact Rc.ncond r hr, ?_, ?_⟩
  · -- grow
    have GE := growU_emit (b := ⟨[], [], Termin.hop xc.th⟩) (jumpsBelow_hop Rc.lo Rc.hi) u3
    exact Rb.grow.trans (Ra.grow.trans (GU.trans
      (Rc.grow.trans (GE.trans (growU_addOps hadd (GE.up u3))))))
  · -- regs
    have := Rc.regs r hr; simp only [sixGenL_re] at this; exact reC r this.1 this.2
  · -- eregs
    intro e he
    rcases (memE e).mp he with h | rfl | h | rfl | h
    · exact ⟨(Rc.eregs e h).1, fun r hr => by
        have := (Rc.eregs e h).2 r hr; simp only [sixGenL_re] at this; exact reC r this.1 this.2⟩
    · exact ⟨Ra.dist, fun r hr => reB r (Ra.regs r hr).1 (Ra.regs r hr).2⟩
    · exact ⟨(Ra.eregs e h).1, fun r hr => reB r ((Ra.eregs e h).2 r hr).1 ((Ra.eregs e h).2 r hr).2⟩
    · exact ⟨Rb.dist, fun r hr => reA r (Rb.regs r hr).1 (Rb.regs r hr).2⟩
    · exact ⟨(Rb.eregs e h).1, fun r hr => reA r ((Rb.eregs e h).2 r hr).1 ((Rb.eregs e h).2 r hr).2⟩
  · -- labs
    intro e he
    simp only [jmp0]
    rcases (memE e).mp he with h | rfl | h | rfl | h
    · obtain ⟨_, _, th, hth⟩ := Rc.labs e h
      have := lc e h
      exact ⟨by omega, by omega, th, (h4k _ (by omega)).trans hth⟩
    · exact ⟨by omega, by omega, x0.th, h4y⟩
    · obtain ⟨_, _, th, hth⟩ := Ra.labs e h
      have := la e h
      exact ⟨by omega, by omega, th, (h42 _ this.2).trans hth⟩
    · exact ⟨by omega, by omega, x1.th, h4n⟩
    · obtain ⟨l1, _, th, hth⟩ := Rb.labs e h
      have := lb e h
      exact ⟨l1, by omega, th, (h41 _ this.2).trans hth⟩
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
  · -- size
    rw [en]; simp only [List.length_append, List.length_cons, sixCount]
    have := Ra.size; have := Rb.size; have := Rc.size; omega
  · -- nec
    have fo' : ¬ FitsS xc.laz.sure s := fun f => hs ⟨f.1, (looks_uni_empty _ _).mpr f.2⟩
    rw [pureEval_n6, Rc.nec s fo']; rfl
  · -- econd
    intro e he r hr
    rcases (memE e).mp he with h | rfl | h | rfl | h
    · rw [hc43]; exact Rc.econd e h r hr
    · rw [cf24.get_lt (Ra.regs r hr).2]; exact Ra.ncond r hr
    · rw [cf24.get_lt ((Ra.eregs e h).2 r hr).2]; exact Ra.econd e h r hr
    · rw [cf14.get_lt (Rb.regs r hr).2]; exact Rb.ncond r hr
    · rw [cf14.get_lt ((Rb.eregs e h).2 r hr).2]; exact Rb.econd e h r hr
  · -- sem
    intro cf hcf cc ned σ O st t gul s0 s ag hned regs hh hn
    have hcf3 : ∀ k, k < g3.re → HoonMap.get cf k = HoonMap.get g3.cond k := fun k hk =>
      (hcf k (by omega)).trans (by rw [hc43])
    have hcfB : ∀ (gB : Gen Map), CondFresh gB g4' → ∀ k, k < gB.re → HoonMap.get cf k = HoonMap.get gB.cond k :=
      fun gB cfB k hk => (hcf k (Nat.lt_of_lt_of_le hk cfB.1)).trans (cfB.get_lt hk)
    have notLab : ∀ o, g0.bo ≤ o → o < g4'.bo → (g3.bo ≤ o ∨
        (g2.bo + 2 ≤ o ∧ o < g3.bo ∧ o ∉ (entries xc.laz).map Prod.fst) ∨
        (g1.bo ≤ o ∧ o < g2.bo ∧ o ∉ (entries x0.laz).map Prod.fst) ∨
        (o < g1.bo ∧ o ∉ (entries x1.laz).map Prod.fst)) →
        HoonMap.get cc.blocks o = (HoonMap.get g4'.blocks o).map (unproxyBlob cf) := by
      intro o h0 h1 hc'
      refine ag.1 o h0 h1 fun hm => ?_
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
    have hxca : xc.th.args = [] := by
      rcases Rc.ent with ⟨_, _, _, e⟩ | e
      · exact e
      · simp only [GoalJ] at e; rcases e with e | e <;> rw [e] <;> rfl
    have hc3 : HoonMap.get cc.blocks g3.bo = some ⟨[], [], Termin.hop xc.th⟩ := by
      rw [notLab g3.bo (by omega) (by omega) (Or.inl (Nat.le_refl _)), h4o]
      simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, renFin, renJmp_nil _ hxca]
    have hre4 : ∀ r, NMem ned r → g4'.re ≤ r := hned
    have agC : AgreeU lib O cc gul st t cf ned (sixGenL g2 x0.th x1.th region) g3 xc.laz s0 s := by
      refine ⟨fun o h0 h1 hnl => ?_, fun e he => ?_⟩
      · simp only [sixGenL_bo] at h0
        rw [notLab o (by omega) (by omega) (Or.inr (Or.inl ⟨h0, h1, hnl⟩)), h4k o (by omega)]
      · obtain ⟨A, th, hg, hcb, hF⟩ := ag.2 e ((memE e).mpr (Or.inl he))
        exact ⟨A, th, (h4k _ (by have := lc e he; omega)).symm.trans hg, hcb, hF.mono (by omega)⟩
    have agA : AgreeU lib O cc gul st t cf ned g1 g2 x0.laz s0 s := by
      refine ⟨fun o h0 h1 hnl => ?_, fun e he => ?_⟩
      · rw [notLab o (by omega) (by omega) (Or.inr (Or.inr (Or.inl ⟨h0, h1, hnl⟩))), h42 o h1]
      · obtain ⟨A, th, hg, hcb, hF⟩ := ag.2 e ((memE e).mpr (Or.inr (Or.inr (Or.inl he))))
        exact ⟨A, th, (h42 _ (la e he).2).symm.trans hg, hcb, hF.mono (by omega)⟩
    have agB : AgreeU lib O cc gul st t cf ned g0 g1 x1.laz s0 s := by
      refine ⟨fun o h0 h1 hnl => ?_, fun e he => ?_⟩
      · rw [notLab o (by omega) (by omega) (Or.inr (Or.inr (Or.inr ⟨h1, hnl⟩))), h41 o h1]
      · obtain ⟨A, th, hg, hcb, hF⟩ := ag.2 e ((memE e).mpr (Or.inr (Or.inr (Or.inr (Or.inr he)))))
        exact ⟨A, th, (h41 _ (lb e he).2).symm.trans hg, hcb, hF.mono (by omega)⟩
    -- a lazy block
    have lazyBlk : ∀ (o : Nat) (x : NextL S) (nm' : Nomm) (gA gB : Gen Map),
        (o, x.laz) ∈ entries (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
          (xc.laz.fork ++ [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))]) xc.laz.bond) →
        HoonMap.get g4'.blocks o = some ⟨[], [], Termin.hop x.th⟩ → x.th.args = [] →
        RunOKV (Map := Map) lib nm' goal gA gB x → CondFresh gB g4' →
        AgreeU lib O cc gul st t cf ned gA gB x.laz s0 s → gB.re ≤ g4'.re → g0.re ≤ gA.re →
        ∀ R2, HoldsN ned R2 s0 →
          GoalSem lib O cc gul st (fun r => r < g0.re ∨ NMem ned r) R2 t (jmp0 o) goal (pureEval nm' s) := by
      intro o x nm' gA gB hm hb hxa R cfB agX hre hlo R2 hR2
      obtain ⟨A, th, hg, hcb, hF⟩ := ag.2 _ hm
      rw [hb] at hg
      simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at hg
      subst hg
      rw [renJmp_nil _ hxa] at hcb
      have dj : ∀ y, NMem ned y → ¬ NMem x.laz.sure.ned y := fun y hy hy' => by
        have := hned y hy; have := (R.regs y hy').2; omega
      have e0 : goJ lib O cc gul st R2 t (jmp0 o) =
          execBlob lib O cc gul st R2 t ⟨[], A, Termin.hop x.th⟩ [] := goJ_jmp0 _ _ _ _ hcb
      by_cases f : FitsS x.laz.sure s
      · obtain ⟨R3, hh3, k3, e3⟩ := (fillSem_runK hF hR2 x.th).1 f
        have hn3 : HoldsN ned R3 s0 := HoldsN.agree ned (fun y hy => k3 y (Or.inl hy) (dj y hy)) hR2
        have S3 := R.sem cf (hcfB gB cfB) cc ned σ O st t gul s0 s agX (fun r hr => Nat.le_trans hre (hned r hr)) R3 hh3 hn3
        refine goalSem_pre (fun r hr => ?_) (e0.trans e3) goal _
          (goalSem_mono (fun r hr => hr.elim (fun h => Or.inl (by omega)) Or.inr) goal _ S3)
        rcases hr with hr | hr
        · exact k3 r (Or.inr (by omega)) (fun h => by have := (R.regs r h).1; omega)
        · exact k3 r (Or.inl hr) (dj r hr)
      · rw [R.nec s f]
        exact goalSem_none goal (e0.trans ((fillSem_runK hF hR2 x.th).2 f))
    have Hc := Rc.sem cf hcf3 cc ned σ O st t gul s0 s agC (fun r hr => by have := hned r hr; omega) regs
      ⟨hh.1, (looks_uni_empty _ _).mp hh.2⟩ hn
    have e0 : goJ lib O cc gul st regs t (jmp0 g3.bo) = goJ lib O cc gul st regs t xc.th := by
      rw [goJ_jmp0 _ _ _ _ hc3, execBlob_hop]
    have kk : ∀ R2 : Map (Option Noun), (∀ r, (r < (sixGenL g2 x0.th x1.th region).re ∨ NMem ned r) →
        SkaModel.read r R2 = SkaModel.read r regs) →
        ∀ r, (r < g0.re ∨ NMem ned r) → SkaModel.read r R2 = SkaModel.read r regs :=
      fun R2 k2 r hr => k2 r (hr.elim (fun h => Or.inl (by simp only [sixGenL_re]; omega)) Or.inr)
    show GoalSem lib O cc gul st (fun r => r < g0.re ∨ NMem ned r) regs t (jmp0 g3.bo) goal
      (pureEval (Nomm.n6 c a b) s)
    rw [pureEval_n6]
    cases ec : pureEval c s with
    | none => rw [ec] at Hc; exact goalSem_none goal (e0.trans Hc)
    | some v =>
      rw [ec] at Hc
      rcases v with ⟨_ | _ | k⟩ | ⟨x, y⟩
      · obtain ⟨R2, k2, e2⟩ := Hc
        exact goalSem_pre (kk R2 k2) (e0.trans e2) goal _
          (lazyBlk g2.bo x0 a g1 g2 ((memE _).mpr (Or.inr (Or.inl rfl))) h4y hx0a Ra cf24 agA (by omega) (by omega) R2
            (HoldsN.agree ned (fun x hx => k2 x (Or.inr hx)) hn))
      · obtain ⟨R2, k2, e2⟩ := Hc
        exact goalSem_pre (kk R2 k2) (e0.trans e2) goal _
          (lazyBlk (g2.bo + 1) x1 b g0 g1 ((memE _).mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) h4n hx1a Rb cf14 agB
            (by omega) (Nat.le_refl _) R2 (HoldsN.agree ned (fun x hx => k2 x (Or.inr hx)) hn))
      · exact goalSem_none goal (e0.trans Hc)
      · exact goalSem_none goal (e0.trans Hc)

/-! ## `[7 [4 p] q]` under a fork-free `%next` -/

/-- **The `sem` of `RunOKN` against every later `cond`.** -/
def SemNV (lib : Lib) (nm : Nomm) (sur : Sure S) (th : Jmp) (g0 g1 : Gen Map) (nex : NextL S) : Prop :=
  ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s0 s : Noun),
    AgreeU lib O c gul st t cf ned g0 g1 nex.laz s0 s → (∀ r, NMem ned r → g1.re ≤ r) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    GoalSem lib O c gul st (fun r => (r < g0.re ∨ NMem ned r) ∧ ¬ NMem sur.ned r) regs t nex.th
      (CGoal.next sur th) (pureEval nm s)

/-- **`RunOKN` for a run that may make proxies and composes**: `cond` grows
by fresh proxies, the result's needs are no keys of the final `cond`, and the
`sem` is taken against every later `cond` (`SemNV`). -/
structure RunOKNV (lib : Lib) (nm : Nomm) (sur : Sure S) (th : Jmp) (g0 g1 : Gen Map) (nex : NextL S) : Prop where
  ext : Ext g0 g1
  grow : GrowU g0 g1
  cfr : CondFresh g0 g1
  lo : 1 ≤ nex.th.there
  hi : nex.th.there < g1.bo
  ent : Entry g1 (CGoal.next sur th) nex.th
  regs : ∀ r, NMem nex.laz.sure.ned r → NMem sur.ned r ∨ (g0.re ≤ r ∧ r < g1.re)
  dist : Distinct nex.laz.sure.ned
  eregs : ∀ e ∈ entries nex.laz, Distinct e.2.sure.ned ∧ ∀ r, NMem e.2.sure.ned r → g0.re ≤ r ∧ r < g1.re
  labs : ∀ e ∈ entries nex.laz, g0.bo ≤ e.1 ∧ e.1 < nex.th.there ∧
    ∃ th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩
  nodup : ((entries nex.laz).map Prod.fst).Nodup
  size : (entries nex.laz).length ≤ 2 * sixCount nm
  nec : ∀ s, ¬ FitsS nex.laz.sure s → pureEval nm s = none ∨ ∃ p, pureEval nm s = some p ∧ ¬ FitsS sur p
  ncond : ∀ r, NMem nex.laz.sure.ned r → HoonMap.get g1.cond r = Option.none
  econd : ∀ e ∈ entries nex.laz, ∀ r, NMem e.2.sure.ned r → HoonMap.get g1.cond r = Option.none
  sem : SemNV lib nm sur th g0 g1 nex

/-- **`[7 [4 p] q]` under a fork-free `%next sur th` meets `RunOKNV`**, for
`q` in `FragX`, from a state with `Clear` and `CondBelow` in which no
register of the goal's need is a key of `cond` (`hkg`).  The blocks of `q`
mention the goal's registers and registers allocated in `q`'s run
(`runX_above` with the predicate "no key of the start's `cond`"), so
unproxying leaves them alone.  A parent meets `hkg` when the goal's
registers were allocated fresh after every key of `cond` it had then, and
the parts run since made proxies only from their own starts on
(`CondFresh`), as the head register of a cons is, whatever its tail makes. -/
theorem runOKNV_seven4 (lib : Lib) {p q : Nomm} (hp : NextOK (S := S) (Map := Map) lib p)
    (sp : OKNR (S := S) (Map := Map) lib p) (kp : KeepX S Map p) (ap : AboveX S Map p)
    (hq : FragX (S := S) q) (hcount : sixCount (Nomm.n7 (Nomm.n4 p) q) ≤ 255) {sur : Sure S} {th : Jmp}
    {region : List Nat} {g0 g2 : Gen Map} {nex : NextL S} (hj : GJ g0.bo (CGoal.next sur th)) (hth : th.args = [])
    (hok : GoalOK g0 (CGoal.next sur th)) (hcl : Clean sur.ned) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false)
    (hu : UpBelow g0) (hcl0 : Clear g0) (hcb0 : CondBelow g0)
    (hkg : ∀ r, NMem sur.ned r → HoonMap.get g0.cond r = Option.none)
    (h : runL (Nomm.n7 (Nomm.n4 p) q) (CGoalL.next (ofSure sur) th) region g0 = some (nex, g2)) :
    RunOKNV (Map := Map) lib (Nomm.n7 (Nomm.n4 p) q) sur th g0 g2 nex := by
  let P : Nat → Prop := fun r => HoonMap.get g0.cond r = Option.none
  have hm : GoalA P (CGoal.next sur th) := ⟨hkg, jmpIn_nil hth⟩
  have hmr : Ple P g0.re := fun r hr => condBelow_none hcb0 hr
  have hc : sixCount p ≤ 255 ∧ sixCount q ≤ 255 := by simp only [sixCount] at hcount; omega
  have p7 : ∀ s, pureEval (Nomm.n7 (Nomm.n4 p) q) s = (pureEval (Nomm.n4 p) s).bind (pureEval q) := fun _ => rfl
  rw [runL_n7] at h
  obtain ⟨nx, g1, h1, h2⟩ := bind_some h
  have Rq := (runX_ok (Map := Map) lib hq).2.1 hj hth hok hcl hc.2 b0 d0 hu h1
  have Sq := (runX_semR (Map := Map) lib hq).2.1 hj hth hok hcl hc.2 b0 d0 hu hcl0 h1
  have gin : GoalIn g0.re (CGoal.next sur th) := ⟨fun r hr => hok.2 r hr, jmpIn_nil hth⟩
  have Bq : BelowIn g0.bo g1 := runX_below (goal := CGoal.next sur th) hq d0 gin hc.2 h1
  have Aq : AboveIn P g0.bo g1 := runX_above (goal := CGoal.next sur th) hq d0 gin hm hmr hc.2 h1
  obtain ⟨q1, q2, q3, q4⟩ := Rq.ext
  have nk1 : ∀ x, P x → HoonMap.get g1.cond x = Option.none := fun x hx => by
    rw [Rq.cnd]; exact hx
  have hcb1 : CondBelow g1 := (condFresh_of_eq q1 Rq.cnd).below hcb0
  have qlo := Rq.lo
  have qhi := Rq.hi
  have hqr : ∀ x, NMem nx.laz.sure.ned x → P x ∧ x < g1.re := fun x hx => by
    rcases Rq.regs x hx with e | e
    · exact ⟨hm.1 x e, by have := hok.2 x e; omega⟩
    · exact ⟨hmr x e.1, e.2⟩
  obtain ⟨d, CR⟩ := collRun_n4 lib hp sp kp ap h2 hc.1 (by omega) (q3.trans d0) (Rq.grow.up hu)
    (hcl0.growU Rq.grow) Rq.lo Rq.hi (fun x hx => (hqr x hx).2) (fun x hx => nk1 x (hqr x hx).1)
    hcb1
    (List.nodup_cons.mpr ⟨fun hm' => by
      obtain ⟨e, he, e1⟩ := List.mem_map.mp hm'
      have := (Rq.labs e he).2.1; omega, Rq.nodup⟩)
    (fun e he => by obtain ⟨a, b, th, hb⟩ := Rq.labs e he; exact ⟨by omega, [], _, hb⟩)
    (fun e he x hx => ((Rq.eregs e he).2 x hx).2)
  have Cre := CR.re
  have Cbo := CR.bo
  have Cdl := CR.dlt
  refine ⟨⟨by omega, by omega, CR.drop.trans q3, fun o ho => (CR.keep o (by omega) (fun hm' => ?_)).trans (q4 o ho)⟩,
    Rq.grow.trans CR.grow, (condFresh_of_eq q1 Rq.cnd).trans CR.pfor.1, CR.lo, CR.hi, Or.inl CR.ent,
    fun r hr => Or.inr ⟨by have := (CR.regs r hr).1; omega, (CR.regs r hr).2⟩, CR.dist,
    fun e he => ⟨(CR.eregs e he).1, fun r hr => ⟨by have := ((CR.eregs e he).2 r hr).1; omega,
      ((CR.eregs e he).2 r hr).2⟩⟩,
    fun e he => ⟨by have := (CR.labs e he).1; omega, (CR.labs e he).2⟩, CR.nodup,
    by have := CR.size; simp only [sixCount] at this ⊢; omega,
    fun s hs' => Or.inl (by rw [p7, CR.nec s hs']; rfl), CR.ncond, CR.econd, ?_⟩
  · obtain ⟨e, he, e1⟩ := List.mem_map.mp hm'
    have := (Rq.labs e he).1; omega
  intro cf hcf c ned σ O st t gul s0 s ag hned regs hh hn
  have agC : AgreeU lib O c gul st t cf ned g1 g2 nex.laz s0 s :=
    ⟨fun o l u hnl => ag.1 o (by omega) u hnl, ag.2⟩
  have Sp := CR.sem cf hcf c ned σ O st t gul s0 s agC (fun r hr => Or.inl (hned r hr)) regs hh hn
  have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk =>
    (hcf k (by omega)).trans (ProxyFor.get_lt CR.pfor hk)
  have u0 : ∀ x, x < g1.re → unproxy cf x = unproxy g1.cond x := unproxy_agree hcf1
  have u1 : ∀ x, P x → unproxy g1.cond x = id x := fun x hx => unproxy_none (nk1 x hx)
  cases ev : pureEval (Nomm.n4 p) s with
  | none =>
    rw [ev] at Sp
    have e7 : pureEval (Nomm.n7 (Nomm.n4 p) q) s = none := by rw [p7, ev]; rfl
    rw [e7]; exact goalSem_none _ Sp
  | some v =>
    rw [ev] at Sp
    have e7 : pureEval (Nomm.n7 (Nomm.n4 p) q) s = pureEval q v := by rw [p7, ev]; rfl
    rw [e7]
    obtain ⟨m', rfl⟩ : ∃ m', v = A m' := by
      rw [pureEval_n4] at ev
      cases ep : pureEval p s with
      | none => rw [ep] at ev; cases ev
      | some x =>
        rw [ep] at ev
        cases x with
        | atom n => simp [incF] at ev; exact ⟨n + 1, ev.symm⟩
        | cell _ _ => simp [incF] at ev
    by_cases fit : FitsS nx.laz.sure (A m')
    · have hfa : ∀ v, FitsS nx.laz.sure (A v) := CR.dich.elim id (fun hn' => absurd fit (hn' m'))
      have SpT := CR.semT hfa cf hcf c ned σ O st t gul s0 s agC
        (fun r hr => Or.inl (hned r hr)) regs hh hn
      rw [ev] at SpT
      obtain ⟨R, hR, kR, eR⟩ := SpT.1 ⟨trivial, looks_empty _⟩
      have hR' : SkaModel.read d R = some (A m') := hR
      have agQ : AgreeP lib O c gul st t (Need.pair ned (Need.this d)) g0 g1 nx.laz (C s0 (A m')) (A m') := by
        refine ⟨fun o l u hnl => ?_, fun e he => ?_⟩
        · have hn2 : o ∉ (entries nex.laz).map Prod.fst := fun hm' => by
            obtain ⟨e', he', e1⟩ := List.mem_map.mp hm'; have := (CR.labs e' he').1; omega
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
          have hn2 : e.1 ∉ (entries nex.laz).map Prod.fst := fun hm' => by
            obtain ⟨e', he', e1⟩ := List.mem_map.mp hm'; have := (CR.labs e' he').1; omega
          refine ⟨F.map (renPole (unproxy cf)), th, hb, ?_, ?_⟩
          · rw [ag.1 e.1 l (by omega) hn2, hb2]
            have hj := (Bq e.1 _ l (by omega) hb).2.2
            have hj' := (Aq e.1 _ l (by omega) hb).2.2
            simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, renFin]
            rw [renJmp_congr u0 hj, renJmp_congr u1 hj', renJmp_id]
          · exact collP_fillSem hP ((hcf d Cdl).trans CR.dkey)
              (fun x hx => by
                have hx1 := ((Rq.eregs e he).2 x hx)
                rw [hcf x (by omega), ProxyFor.get_lt CR.pfor hx1.2]; exact nk1 x (hmr x hx1.1))
              (fun k hk => hcf k hk) lib O c gul st t ned g1.re s0 m'
      have inQ : ∀ r, NMem (Need.pair ned (Need.this d)) r →
          InR (CGoal.next sur th) g0 g1 nx.laz.sure.ned r := by
        intro r hr
        rcases hr with hr | hr
        · exact Or.inl (by have := hned r hr; omega)
        · have hr' : r = d := hr
          rw [hr']
          rcases CR.dreg with e | e
          · exact Or.inr (Or.inr e)
          · exact Or.inl e
      have hnR : HoldsN (Need.pair ned (Need.this d)) R (C s0 (A m')) :=
        ⟨HoldsN.agree ned (fun r hr => kR r (Or.inr hr)) hn, hR'⟩
      have Sq' := Sq c _ σ O st t gul _ _ agQ inQ R (CR.dhold hfa R m' hR') hnR
      refine goalSem_pre (fun r hr => ?_) eR _ _ (goalSem_mono (fun r hr => ?_) _ _ Sq')
      · rcases hr with ⟨hr | hr, hs⟩
        · refine kR r (Or.inl ⟨by omega, fun hm' => ?_⟩)
          rcases Rq.regs r hm' with e | e
          · exact hs e
          · omega
        · exact kR r (Or.inr hr)
      · rcases hr with ⟨hr | hr, hs⟩
        · exact Or.inl ⟨hr, hs⟩
        · exact Or.inr (Or.inl hr)
    · exact goalSem_crash_or (Rq.nec (A m') fit) (Sp.2 fit)

/-- **The first version of `runOKNV_seven4`**: a lower bound `m` of the
goal's registers with no key of `cond` from `m` on. -/
theorem runOKNV_seven4_le (lib : Lib) {p q : Nomm} (hp : NextOK (S := S) (Map := Map) lib p)
    (sp : OKNR (S := S) (Map := Map) lib p) (kp : KeepX S Map p) (ap : AboveX S Map p)
    (hq : FragX (S := S) q) (hcount : sixCount (Nomm.n7 (Nomm.n4 p) q) ≤ 255) {sur : Sure S} {th : Jmp}
    {region : List Nat} {g0 g2 : Gen Map} {nex : NextL S} (hj : GJ g0.bo (CGoal.next sur th)) (hth : th.args = [])
    (hok : GoalOK g0 (CGoal.next sur th)) (hcl : Clean sur.ned) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false)
    (hu : UpBelow g0) (hcl0 : Clear g0) (hcb0 : CondBelow g0) {m : Nat} (hm : GoalA (m ≤ ·) (CGoal.next sur th))
    (hkm : ∀ k, m ≤ k → HoonMap.get g0.cond k = Option.none)
    (h : runL (Nomm.n7 (Nomm.n4 p) q) (CGoalL.next (ofSure sur) th) region g0 = some (nex, g2)) :
    RunOKNV (Map := Map) lib (Nomm.n7 (Nomm.n4 p) q) sur th g0 g2 nex :=
  runOKNV_seven4 lib hp sp kp ap hq hcount hj hth hok hcl b0 d0 hu hcl0 hcb0 (fun r hr => hkm r (hm.1 r hr)) h

/-! ## The start state -/

theorem condBelow_gen0 : CondBelow (gen0 : Gen Map) := fun k hk => by
  simp [gen0, HoonMap.get_empty] at hk

end Comp
end SkaModel
end Formalization
