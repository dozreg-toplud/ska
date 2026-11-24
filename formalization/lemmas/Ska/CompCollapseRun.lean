import lemmas.Ska.CompCollapsePre
import lemmas.Ska.CompBelowX
import lemmas.Ska.CompRelX
import lemmas.Ska.CompEntryRel

/-!
# The run of `+collapse-lazy-atom` when the sure need is one register

README Gaps 12.2, the collapse case.  When the goal's sure need is
`this d` with looks at axis `1` only (as in
`[7 [4 [0 3]] [6 [5 [0 1] [1 6]] [0 1] [1 5]]]`, where `d` is the `rp` of the
`%5` of `q`), `+collapse-lazy-atom` takes `r = d` and `there = th.there`,
puts nothing at `th.there` (`+sure-require-look` of `this d` is `this d`
again), and walks the goal's entries with `collapseGate d th.there`
(`collapseL_this`): every entry gets ops that do what `CollP d` says for the
`cond` the walk ends with, `cond` grew only by proxies for `d`, and every
block other than the entries is kept, `th.there` included.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- **`+collapse-lazy-atom` when the sure need is `this d`**: it returns
`(d, th.there)`, keeps every block outside the goal's entries (`th.there`
included), and walks the entries with `CollP d` for the `cond` it ends
with, which grew only by proxies for `d`. -/
theorem collapseL_this {laz : Lazy S} {th : Jmp} {d : Nat} {g0 g2 : Gen Map} {a : Option (Nat × Nat)}
    (h : collapseLazyAtomL ⟨laz, th⟩ g0 = some (a, g2))
    (hs : laz.sure.ned = Need.this d) (hl : ∀ x ∈ HoonSet.toList laz.sure.lok, x = 1)
    (d0 : g0.drop = false)
    (hn : (th.there :: (entries laz).map Prod.fst).Nodup) :
    th.args = [] ∧ a = some (d, th.there) ∧ WalkOKD (ProxyFor d) (CollP (S := S) (Map := Map) d) g0 g2 (entries laz) := by
  unfold collapseLazyAtomL at h
  dsimp only at h
  by_cases ea : th.args ≠ []
  · rw [if_pos ea] at h; cases h
  rw [if_neg ea] at h
  have ea' : th.args = [] := by simpa using ea
  rcases laz with ⟨s, fk, bd⟩
  simp only [sure_mk] at hs hl
  have hne : noneEquivalentL (mk s fk bd) = false := by
    simp [noneEquivalentL, hs]
  rw [if_neg (by simp [hne])] at h
  obtain ⟨nedS, g1, h1, h⟩ := bind_some h
  have L := sureRequireLook_spec h1
  have eS : nedS = Need.this d := (L.same hl).trans hs
  subst eS
  obtain ⟨k1, hk1⟩ := L.gen
  have d1 : g1.drop = false := by rw [hk1]; exact d0
  simp only [sure_mk, fork_mk, bond_mk, bind_apply, pure_apply, Option.bind_some, get_apply, d1,
    Bool.false_eq_true, if_false] at h
  obtain ⟨⟨u, gW⟩, hW, hP⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.some.injEq, Prod.mk.injEq] at hP
  obtain ⟨rfl, rfl⟩ := hP
  refine ⟨ea', rfl, ?_⟩
  -- the walk: nothing at `th.there`, then the forks and the bonds
  unfold walkLazy at hW
  obtain ⟨u1, gA, hA, hr⟩ := bind_some hW
  obtain ⟨k2, hk2, hgA⟩ := collapseGate_self hl hA
  have W0 : WalkOKD (ProxyFor d) (CollP (S := S) (Map := Map) d) g0 gA [] := by
    have := WalkOKD.of_re (P := CollP (S := S) (Map := Map) d) (r := d) g0 k2 (Nat.le_trans L.le hk2)
    rw [hgA, hk1]; exact this
  have dA : gA.drop = false := by rw [hgA]; exact d1
  have ct : ∀ a b c : Gen Map, ProxyFor d a b → ProxyFor d b c → ProxyFor d a c := fun _ _ _ x y => ProxyFor.trans x y
  have cb : ∀ a b : Gen Map, ProxyFor d a b → ∀ k, k < a.re → HoonMap.get b.cond k = HoonMap.get a.cond k :=
    fun _ _ x _ hk => ProxyFor.get_lt x hk
  have hn' := (List.nodup_cons.mp hn).2
  simp only [entries, List.map_append] at hn' ⊢
  split at hr
  · rename_i hfb
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hfb
    obtain ⟨rfl, rfl⟩ := hfb
    have h' : some ((), _) = some ((), gW) := hr
    cases h'
    simpa [bondEntries, forkEntries] using W0
  · obtain ⟨u2, gB, h2, h3⟩ := bind_some hr
    have WF := walkForks_okD (ProxyFor.refl d) ct cb (collP_mono d) (collapseGate_ok d th.there) fk _ gB h2 dA
      (List.nodup_append.mp hn').2.1
    have WB := walkBonds_okD (ProxyFor.refl d) ct cb (collP_mono d) (collapseGate_ok d th.there) bd gB gW h3
      (WF.drop.trans dA) (List.nodup_append.mp hn').1
    have W := (W0.trans ct cb (collP_mono d) WF (fun x hx => absurd hx List.not_mem_nil)).trans ct cb
      (collP_mono d) WB (by
        intro x hx hm
        simp only [List.nil_append] at hx
        exact nodup_disj hn' x hm hx)
    exact W.congr fun e => by
      simp only [List.nil_append, List.mem_append]
      exact Or.comm

section Run
variable [HoonMapKeys Map]

/-- **The blocks a run of `p` for the goal `this a` emits mention only `a`
and registers from the run's start on.**  A hypothesis of `collRun_n4`: the
blocks of `p` must not mention the proxies the walk made below `a`.  The run
is one that `collRun_n4` makes: its jump has no arguments and goes below the
start, the state is not dropping, `UpBelow` and `CondBelow` hold, `a` is no
key of `cond`, and `p` has at most 255 `%6`. -/
def AboveX (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (p : Nomm) : Prop :=
  ∀ {a : Nat} {th : Jmp} {region : List Nat} {g g' : Gen Map} {nex : NextL S},
    runL p (CGoalL.next (ofSure (lazyReg a)) th) region g = some (nex, g') → a < g.re →
    th.args = [] → 1 ≤ th.there → th.there < g.bo → g.drop = false → UpBelow g → CondBelow g →
    HoonMap.get g.cond a = Option.none → sixCount p ≤ 255 →
    ∀ o b, g.bo ≤ o → o < g'.bo → HoonMap.get g'.blocks o = some b → BlobIn (a ≤ ·) b

/-- **What one run of `[4 p]` for a goal `%next laz th` with entries does**
(`collRun_n4`), with `d` the register the increment writes: the structural
facts of `RunOKE` with `ProxyFor d` in place of an unchanged `cond`, the
entries of the goal consumed with ops that do what `CollP d` says for the
run's final `cond` (`front`), fact (ii) for the result's needs (`ncond`,
`econd`), fact (i5) (`below`), and the relaxed `sem` against the blocks
unproxied by any `cond` that agrees with the run's below its end.  `d` is a
register of the goal's sure need or allocated in the run, below the run's
end, and no key of the final `cond` (`dreg`, `dlt`, `dkey`).  Either every atom fits the goal's sure need
or none does (`dich`); in the first case `d` holding an atom holds the sure
need (`dhold`), and the code leaves the product in `d` (`semT`, the `sem` for
the goal `this d`). -/
structure CollRunU (lib : Lib) (nm : Nomm) (laz : Lazy S) (th : Jmp) (d : Nat) (g0 g1 : Gen Map) (nex : NextL S) :
    Prop where
  re : g0.re ≤ g1.re
  bo : g0.bo ≤ g1.bo
  drop : g1.drop = g0.drop
  keep : ∀ o, o < g0.bo → o ∉ (entries laz).map Prod.fst → HoonMap.get g1.blocks o = HoonMap.get g0.blocks o
  grow : GrowU g0 g1
  pfor : ProxyFor d g0 g1
  lo : 1 ≤ nex.th.there
  hi : nex.th.there < g1.bo
  ent : Fresh g1 nex.th
  regs : ∀ r, NMem nex.laz.sure.ned r → g0.re ≤ r ∧ r < g1.re
  dist : Distinct nex.laz.sure.ned
  eregs : ∀ e ∈ entries nex.laz, Distinct e.2.sure.ned ∧ ∀ r, NMem e.2.sure.ned r → g0.re ≤ r ∧ r < g1.re
  labs : ∀ e ∈ entries nex.laz, g0.bo ≤ e.1 ∧ e.1 < nex.th.there ∧
    ∃ th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩
  nodup : ((entries nex.laz).map Prod.fst).Nodup
  size : (entries nex.laz).length ≤ 2 * sixCount nm
  front : ∀ e ∈ entries laz, ∃ F : List Pole,
    (∀ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩ → HoonMap.get g1.blocks e.1 = some ⟨[], F ++ B, fin⟩) ∧
    CollP (S := S) d g1.cond g0.re g1.re e.1 e.2.sure F
  ncond : ∀ r, NMem nex.laz.sure.ned r → HoonMap.get g1.cond r = Option.none
  econd : ∀ e ∈ entries nex.laz, ∀ r, NMem e.2.sure.ned r → HoonMap.get g1.cond r = Option.none
  below : BelowIn g0.bo g1
  nec : ∀ s, ¬ FitsS nex.laz.sure s → pureEval nm s = none
  sem : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s0 s : Noun),
    AgreeU lib O c gul st t cf ned g0 g1 nex.laz s0 s →
    (∀ r, NMem ned r → InR (CGoal.next laz.sure th) g0 g1 nex.laz.sure.ned r) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    GoalSem lib O c gul st (KeepI (CGoal.next laz.sure th) g0 ned) regs t nex.th (CGoal.next laz.sure th)
      (pureEval nm s)
  dreg : NMem laz.sure.ned d ∨ g0.re ≤ d
  dkey : HoonMap.get g1.cond d = Option.none
  dich : (∀ v, FitsS laz.sure (A v)) ∨ (∀ v, ¬ FitsS laz.sure (A v))
  dhold : (∀ v, FitsS laz.sure (A v)) → ∀ (R : Map (Option Noun)) v, SkaModel.read d R = some (A v) →
    HoldsS laz.sure R (A v)
  semT : (∀ v, FitsS laz.sure (A v)) → ∀ (cf : Map (Nat × List Nat)),
    (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s0 s : Noun),
    AgreeU lib O c gul st t cf ned g0 g1 nex.laz s0 s →
    (∀ r, NMem ned r → InR (CGoal.next laz.sure th) g0 g1 nex.laz.sure.ned r) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    GoalSem lib O c gul st (KeepI (CGoal.next laz.sure th) g0 ned) regs t nex.th
      (CGoal.next (⟨Need.this d, HoonSet.empty⟩ : Sure S) th) (pureEval nm s)
  dlt : d < g1.re

theorem fitsS_this_one {d : Nat} {lok : S} (hl : ∀ x ∈ HoonSet.toList lok, x = 1) (n : Noun) :
    FitsS (⟨Need.this d, lok⟩ : Sure S) n :=
  ⟨trivial, fun x hx => by rw [hl x hx]; simp⟩

/-- **`[4 p]` for a goal `%next laz th` with entries, for every shape of the
goal's sure need.**  `p` is any nomm whose runs for a fork-free goal meet
`RunOKN`, the relaxed `sem`, (i5) (`KeepX`) and mention no register below
their goal's (`AboveX`).  The sure need's registers are allocated before the
run and no keys of `cond`. -/
theorem collRun_n4 (lib : Lib) {p : Nomm} (hp : NextOK (S := S) (Map := Map) lib p)
    (sp : OKNR (S := S) (Map := Map) lib p) (kp : KeepX S Map p) (ap : AboveX S Map p)
    {laz : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (h : runL (Nomm.n4 p) (CGoalL.next laz th) region g0 = some (nex, g1))
    (hcount : sixCount p ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl0 : Clear g0)
    (h1 : 1 ≤ th.there) (h2 : th.there < g0.bo)
    (hnr : ∀ x, NMem laz.sure.ned x → x < g0.re)
    (hnc : ∀ x, NMem laz.sure.ned x → HoonMap.get g0.cond x = Option.none)
    (hcb : CondBelow g0) (hnd : (th.there :: (entries laz).map Prod.fst).Nodup)
    (hlab : ∀ e ∈ entries laz, e.1 < g0.bo ∧ ∃ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩)
    (hen : ∀ e ∈ entries laz, ∀ x, NMem e.2.sure.ned x → x < g0.re) :
    ∃ d, CollRunU lib (Nomm.n4 p) laz th d g0 g1 nex := by
  have e4 : (runL (Nomm.n4 p) (CGoalL.next laz th) region : CM Map (NextL S)) = (do
      let a ← collapseLazyAtomL ⟨laz, th⟩
      let (pro, th') ← collPick th a
      let arg ← re
      let o ← emit ⟨[], [Pole.inc arg pro], Termin.hop (jmp0 th')⟩
      runL p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region) := by
    conv => lhs; unfold runL
    rfl
  rw [e4] at h
  obtain ⟨a, gA, hc2, h⟩ := bind_some h
  obtain ⟨⟨d, th'⟩, g2, hm, h⟩ := bind_some h
  have P := collapsePre_spec hc2 hm d0 hcb hnr hnc hnd hlab hen
  refine ⟨d, ?_⟩
  simp only [bind_apply, pure_apply, Option.bind_some, re_apply, emit_apply] at h
  obtain ⟨g3, hg3⟩ : ∃ g3 : Gen Map, g3 = { g2 with re := g2.re + 1 } := ⟨_, rfl⟩
  obtain ⟨blk, hblk⟩ : ∃ blk : Blob, blk = ⟨[], [Pole.inc g2.re d], Termin.hop (jmp0 th')⟩ := ⟨_, rfl⟩
  obtain ⟨gE, hgE⟩ : ∃ gE : Gen Map, gE = g3.emitted blk := ⟨_, rfl⟩
  have hbo3 : g3.bo = g2.bo := by rw [hg3]
  have hre3 : g3.re = g2.re + 1 := by rw [hg3]
  have hcn3 : g3.cond = g2.cond := by rw [hg3]
  have hbl3 : g3.blocks = g2.blocks := by rw [hg3]
  have hdr3 : g3.drop = false := by rw [hg3]; exact P.drop.trans d0
  rw [← hg3, ← hblk, ← hgE] at h
  have hboE : gE.bo = g2.bo + 1 := by rw [hgE, emitted_bo, hbo3]
  have hreE : gE.re = g2.re + 1 := by rw [hgE, emitted_re, hre3]
  have hcnE : gE.cond = g2.cond := by rw [hgE, ← hcn3]; rfl
  have hdE : gE.drop = false := by rw [hgE, emitted_drop]; exact hdr3
  have hbE : HoonMap.get gE.blocks g2.bo = some blk := by rw [hgE, ← hbo3]; exact emitted_get g3 blk hdr3
  have oE : ∀ o, o ≠ g2.bo → HoonMap.get gE.blocks o = HoonMap.get g2.blocks o := fun o ho => by
    rw [hgE, ← hbl3]; simp [Gen.emitted, hdr3, HoonMap.get_put, hbo3, ho]
  have Pbo := P.bo1
  have Ple := P.le
  have Plt := P.rlt
  have hth' : 1 ≤ th' ∧ th' < g2.bo := by
    rcases P.shape with ⟨e, eb, -⟩ | ⟨e, eb, -⟩ <;> (rw [e]; omega)
  have G : Grow g0 gE := by
    have g23 : Grow g2 g3 := by rw [hg3]; exact grow_re g2
    have g3E : Grow g3 gE := by
      rw [hgE]; refine grow_emit ?_
      rw [hblk]; exact jumpsBelow_hop (j := jmp0 th') hth'.1 (by simp only [jmp0]; omega)
    exact P.grow.trans (g23.trans g3E)
  have GU : GrowU g0 gE := G.toU hu
  have Rp := hp (sur := lazyReg g2.re) (th := jmp0 g2.bo) ⟨by simp only [jmp0]; omega, by simp only [jmp0]; omega⟩ rfl
    (by exact ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; omega⟩) (by exact trivial)
    hcount (by omega) hdE (GU.up hu) h
  have Sp := sp (sur := lazyReg g2.re) (th := jmp0 g2.bo) ⟨by simp only [jmp0]; omega, by simp only [jmp0]; omega⟩ rfl
    (by exact ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; omega⟩) (by exact trivial)
    hcount (by omega) hdE (GU.up hu) (hcl0.growU GU) h
  have hbIn : BlobIn (· < g3.re) blk := by
    rw [hblk]
    refine blobIn_one (p := Pole.inc g2.re d) (f := Termin.hop (jmp0 th')) ?_ ?_
    · intro x hx
      simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
      omega
    · simp only [FinIn, JmpIn, jmp0]; intro x hx; simp at hx
  have Kp : KeepR g3 g1 nex (sixCount p) := keepX_tail (arg := g2.re) kp hdr3 hbIn
    (o := g2.bo) (by omega) hcount (by rw [emit_apply, hbo3, ← hgE]) h
  have cb2 : CondBelow g2 := P.pfor.1.below hcb
  have Ap := ap h (show g2.re < gE.re by omega) rfl (by simp only [jmp0]; omega) (by simp only [jmp0]; omega) hdE
    (GU.up hu) (fun x hx => by rw [hcnE] at hx; have := cb2 x hx; omega)
    (by
      rw [hcnE]
      cases e' : HoonMap.get g2.cond g2.re with
      | none => rfl
      | some _ => have := cb2 g2.re (by simp [e']); omega) hcount
  obtain ⟨Rre, Rbo, Rdr, Rold⟩ := Rp.ext
  have hcn1 : g1.cond = g2.cond := Rp.cnd.trans hcnE
  -- the final `cond` has no key from the end of the collapse on
  have nk1 : ∀ x, g2.re ≤ x → HoonMap.get g1.cond x = Option.none := fun x hx => by
    rw [hcn1]
    rcases P.pfor.1.2 x with e | ⟨_, l⟩
    · rw [e]
      cases e' : HoonMap.get g0.cond x with
      | none => rfl
      | some _ => have := hcb x (by simp [e']); omega
    · omega
  have hg1o : HoonMap.get g1.blocks g2.bo = some blk := (Rold _ (by omega)).trans hbE
  have keep1 : ∀ o, o < g0.bo → HoonMap.get g1.blocks o = HoonMap.get g2.blocks o := fun o ho =>
    (Rold o (by omega)).trans (oE o (by omega))
  have bel1 : BelowIn gE.bo g1 := Kp.keeps.bel gE.bo (fun o _ l u _ => absurd u (by omega))
  have semAll : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s0 s : Noun),
      AgreeU lib O c gul st t cf ned g0 g1 nex.laz s0 s →
      (∀ r, NMem ned r → InR (CGoal.next laz.sure th) g0 g1 nex.laz.sure.ned r) →
      ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
      GoalSem lib O c gul st (KeepI (CGoal.next laz.sure th) g0 ned) regs t nex.th (CGoal.next laz.sure th)
        (pureEval (Nomm.n4 p) s) ∧
      ((∀ v, FitsS laz.sure (A v)) → GoalSem lib O c gul st (KeepI (CGoal.next laz.sure th) g0 ned) regs t nex.th
        (CGoal.next (⟨Need.this d, HoonSet.empty⟩ : Sure S) th) (pureEval (Nomm.n4 p) s)) := by
    intro cf hcf c ned σ O st t gul s0 s ag hned regs hh hn
    have hu1 : ∀ x, x < g1.re → unproxy cf x = unproxy g1.cond x := unproxy_agree hcf
    have hu2 : ∀ x, g2.re ≤ x → unproxy g1.cond x = id x := fun x hx => unproxy_none (nk1 x hx)
    have pb : ∀ o b, gE.bo ≤ o → o < g1.bo → HoonMap.get g1.blocks o = some b → unproxyBlob cf b = b :=
      fun o b l u hb => by
        rw [unproxyBlob, renBlob_congr hu1 (bel1 o b l u hb), renBlob_congr hu2 (Ap o b l u hb), renBlob_id]
    have agP : AgreeP lib O c gul st t ned gE g1 nex.laz s0 s := by
      refine ⟨fun o l u hnl => ?_, fun e he => ?_⟩
      · rw [ag.1 o (by omega) u hnl]
        cases hg : HoonMap.get g1.blocks o with
        | none => rfl
        | some b => simp only [Option.map_some, pb o b l u hg]
      · obtain ⟨A, th'', hb1, hc1, hfs⟩ := ag.2 e he
        obtain ⟨l, lt, -⟩ := Rp.labs e he
        have hb := bel1 e.1 _ l (by have := Rp.hi; omega) hb1
        have ha := Ap e.1 _ l (by have := Rp.hi; omega) hb1
        refine ⟨A, th'', hb1, ?_, hfs⟩
        rw [hc1, renJmp_congr hu1 hb.2.2, renJmp_congr hu2 ha.2.2, renJmp_id]
    have inP : ∀ r, NMem ned r → InR (CGoal.next (lazyReg g2.re : Sure S) (jmp0 g2.bo)) gE g1 nex.laz.sure.ned r := by
      intro r hr
      show g1.re ≤ r ∨ (r < gE.re ∧ ¬ NMem (Need.this g2.re) r) ∨ NMem nex.laz.sure.ned r
      rcases hned r hr with e | ⟨e, _⟩ | e
      · exact Or.inl e
      · exact Or.inr (Or.inl ⟨by omega, fun hm => by simp only [NMem] at hm; omega⟩)
      · exact Or.inr (Or.inr e)
    have Hp := Sp c ned σ O st t gul s0 s agP inP regs hh hn
    have ud : unproxy cf d = d :=
      (hu1 d (by omega)).trans (unproxy_none (by rw [hcn1]; exact P.rkey))
    have ua : unproxy cf g2.re = g2.re := (hu1 _ (by omega)).trans (hu2 _ (Nat.le_refl _))
    have hco : HoonMap.get c.blocks g2.bo = some blk := by
      rw [ag.1 g2.bo (by omega) (by omega) (fun hm => ?_), hg1o]
      · simp [unproxyBlob, renBlob, hblk, renPole, renFin, renJmp, jmp0, ud, ua]
      · obtain ⟨e, he, e1⟩ := List.mem_map.mp hm; have := (Rp.labs e he).1; omega
    have nd : ∀ r, KeepI (CGoal.next laz.sure th) g0 ned r → r ≠ d ∧
        KeepI (CGoal.next (lazyReg g2.re : Sure S) (jmp0 g2.bo)) gE ned r := by
      intro r hr
      rcases hr with ⟨h1', h2'⟩ | h1'
      · refine ⟨fun e => ?_, Or.inl ⟨by omega, ?_⟩⟩
        · rcases P.rreg with hm' | hm'
          · exact h2' (by rw [e]; exact hm')
          · omega
        · show ¬ NMem (Need.this g2.re) r
          simp only [NMem]; omega
      · refine ⟨fun e => ?_, Or.inr h1'⟩
        rcases hned r h1' with e2 | ⟨e1, e2⟩ | e2
        · omega
        · rcases P.rreg with hm' | hm'
          · exact e2 (by rw [e]; exact hm')
          · omega
        · rcases Rp.regs r e2 with e' | e'
          · simp only [lazyReg, NMem] at e'; omega
          · omega
    rw [pureEval_n4]
    cases ev : pureEval p s with
    | none => rw [ev] at Hp; exact ⟨goalSem_none _ Hp, fun _ => goalSem_none _ Hp⟩
    | some x =>
      rw [ev] at Hp
      obtain ⟨R, hR, k, he⟩ := Hp.1 ⟨trivial, looks_empty x⟩
      have hj' := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) R t _ _ hco
      rw [hblk] at hj'
      cases x with
      | atom n =>
        rw [show [Pole.inc g2.re d] = [Pole.inc g2.re d] ++ [] from rfl, runs_inc hR, execBlob_hop] at hj'
        simp only [Option.bind_some, incF]
        have kk : ∀ r, KeepI (CGoal.next laz.sure th) g0 ned r →
            SkaModel.read r (store d (A (n + 1)) R) = SkaModel.read r regs := fun r hr => by
          obtain ⟨rd, kr⟩ := nd r hr
          rw [read_store_ne rd]; exact k r kr
        rcases P.shape with ⟨eth, -, hfa, hfit⟩ | ⟨eth, ebo, hnf, F, hF, hPF⟩
        · rw [eth] at hj'
          have gj : goJ lib O c gul st regs t nex.th = goJ lib O c gul st (store d (A (n + 1)) R) t th := by
            rw [he, hj', jmp0_of_args P.args]
          exact ⟨⟨fun _ => ⟨store d (A (n + 1)) R, (hfit _ _ (read_store_eq _ _ _)).1, kk, gj⟩,
              fun nf => absurd (hfa _) nf⟩,
            fun _ => ⟨fun _ => ⟨store d (A (n + 1)) R, read_store_eq _ _ _, kk, gj⟩,
              fun nf => absurd ⟨trivial, looks_empty _⟩ nf⟩⟩
        · rw [eth] at hj'
          refine ⟨⟨fun f => absurd f (hnf _), fun _ => ?_⟩, fun hf => absurd (hf (n + 1)) (hnf _)⟩
          have hcb0 : HoonMap.get c.blocks g0.bo =
              some ⟨[], F.map (renPole (unproxy cf)), Termin.bom Option.none⟩ := by
            rw [ag.1 g0.bo (Nat.le_refl _) (by omega) (fun hm => ?_), (Rold _ (by omega)).trans (oE _ (by omega)), hF]
            · simp [unproxyBlob, renBlob, renFin]
            · obtain ⟨e, he', e1⟩ := List.mem_map.mp hm; have := (Rp.labs e he').1; omega
          rw [he, hj', goJ_jmp0 _ _ _ _ hcb0]
          obtain ⟨S1, S2⟩ := hPF (unproxy cf) ud (fun x hx => by simp only [NMem] at hx; rw [hx]; exact ud)
            (fun x hx => by rw [hu1 x (by omega), hcn1]) lib σ O c gul st t (store d (A (n + 1)) R) (n + 1)
            (read_store_eq _ _ _)
          rw [← List.append_nil (F.map (renPole (unproxy cf)))]
          by_cases fT : FitsS (⟨Need.this d, laz.sure.lok⟩ : Sure S) (A (n + 1))
          · obtain ⟨R', hr', -, -⟩ := S1 fT
            rw [hr', execBlob_bom']
          · exact S2 fT [] _
      | cell u v =>
        simp only [Option.bind_some, incF]
        have cr : goJ lib O c gul st regs t nex.th = some (Tone.two t, st) := by
          rw [he, hj', show [Pole.inc g2.re d] = [Pole.inc g2.re d] ++ [] from rfl, crashes_inc hR]
        exact ⟨goalSem_crash _ cr, fun _ => goalSem_crash _ cr⟩
  refine ⟨by omega, by omega, Rdr.trans (hdE.trans d0.symm), fun o ho hn => (keep1 o ho).trans (P.other o ho hn),
    GU.trans Rp.grow, P.pfor.trans (ProxyFor.of_eq (by omega) hcn1), Rp.lo, Rp.hi, ?ent, ?hregs, Rp.dist, ?eregs,
    ?labs, Rp.nodup, by simpa only [sixCount] using Rp.size, ?front, ?ncond, ?econd, ?below, ?nec,
    fun cf hcf c ned σ O st t gul s0 s ag hned regs hh hn => (semAll cf hcf c ned σ O st t gul s0 s ag hned regs hh hn).1,
    P.rreg, by rw [hcn1]; exact P.rkey, ?dich, ?dhold,
    fun hf cf hcf c ned σ O st t gul s0 s ag hned regs hh hn =>
      (semAll cf hcf c ned σ O st t gul s0 s ag hned regs hh hn).2 hf, by omega⟩
  case ent =>
    rcases Rp.ent with f | e
    · exact f
    · simp only [GoalJ] at e
      rw [e]
      have fr : Fresh gE (jmp0 g2.bo) := by
        rw [hgE]; exact fresh_emitted (b := blk) hdr3 (by rw [hblk]) (by simp [jmp0, hbo3]) rfl
      exact fr.growU (by simp only [jmp0]; omega) Rp.grow
  case hregs =>
    intro r hr
    rcases Rp.regs r hr with e | e
    · simp only [lazyReg, NMem] at e; subst e; omega
    · omega
  case eregs =>
    intro e he
    exact ⟨(Rp.eregs e he).1, fun r hr => by have := (Rp.eregs e he).2 r hr; omega⟩
  case labs =>
    intro e he
    obtain ⟨x, y, z⟩ := Rp.labs e he
    exact ⟨by omega, y, z⟩
  case front =>
    intro e he
    obtain ⟨A, hA, hP⟩ := P.at_ e he
    have lt := (hlab e he).1
    refine ⟨A, fun B fin hb => (keep1 _ lt).trans (hA B fin hb), ?_⟩
    exact collP_mono d _ _ _ _ _ _ _ _ _ hP (fun k hk => by rw [hcn1]) (Nat.le_refl _) (by omega)
  case ncond =>
    intro r hr
    rcases Rp.regs r hr with e | e
    · simp only [lazyReg, NMem] at e; subst e; exact nk1 _ (Nat.le_refl _)
    · exact nk1 r (by omega)
  case econd =>
    intro e he r hr
    exact nk1 r (by have := (Rp.eregs e he).2 r hr; omega)
  case below =>
    have K3 : Keeps g0 g3 := by rw [hg3]; exact P.keeps.trans (keeps_reg g2 _ (Nat.le_succ _))
    exact Kp.keeps.bel g0.bo (K3.bel g0.bo (fun o _ l u _ => absurd u (by omega)))
  case nec =>
    intro s hs'
    rw [pureEval_n4]
    rcases Rp.nec s hs' with e | ⟨x, _, e⟩
    · rw [e]; rfl
    · exact absurd ⟨trivial, looks_empty x⟩ e
  case dich =>
    rcases P.shape with ⟨-, -, hf, -⟩ | ⟨-, -, hf, -⟩
    · exact Or.inl hf
    · exact Or.inr hf
  case dhold =>
    intro hf R v hR
    rcases P.shape with ⟨-, -, -, hfit⟩ | ⟨-, -, hnf, -⟩
    · exact hfit R v hR
    · exact absurd (hf v) (hnf v)

/-- **`[7 [4 p] q]` for `%done` from `gen0` meets `RunOKU`**, for every `q`
in `FragX`.  When every atom fits the sure need of `q`'s result, `q`'s
relaxed `sem` is taken at the widened input need `pair ned (this d)` holding
`[s0 v]`, with `d` the register the increment writes, which `InR` admits
since `d` is in the sure need of `q`'s result or allocated after `q`'s run,
and the lazy blocks of `q` are filled by the ops of the walk unproxied by
the final `cond` (`collP_fillSem`).  When no atom fits it, the code crashes
and so does `q` on the atom (`nec`). -/
theorem runOKU_seven4 (lib : Lib) {p q : Nomm} (hp : NextOK (S := S) (Map := Map) lib p)
    (sp : OKNR (S := S) (Map := Map) lib p) (kp : KeepX S Map p) (ap : AboveX S Map p)
    (hq : FragX (S := S) q) (hcount : sixCount (Nomm.n7 (Nomm.n4 p) q) ≤ 255) {region : List Nat}
    {g2 : Gen Map} {nex : NextL S}
    (h : runL (Nomm.n7 (Nomm.n4 p) q) (CGoalL.done : CGoalL S) region (gen0 : Gen Map) = some (nex, g2)) :
    RunOKU (Map := Map) lib (Nomm.n7 (Nomm.n4 p) q) CGoal.done gen0 g2 nex := by
  have hc : sixCount p ≤ 255 ∧ sixCount q ≤ 255 := by simp only [sixCount] at hcount; omega
  have p7 : ∀ s, pureEval (Nomm.n7 (Nomm.n4 p) q) s = (pureEval (Nomm.n4 p) s).bind (pureEval q) := fun _ => rfl
  rw [runL_n7] at h
  obtain ⟨nx, g1, h1, h2⟩ := bind_some h
  have Rq := (runX_ok (Map := Map) lib hq).1 trivial trivial hc.2 (by simp [gen0]) rfl upBelow_gen0 h1
  have Sq := SemPR.toG ((runX_semR (Map := Map) lib hq).1 trivial trivial trivial hc.2 (by simp [gen0]) rfl
    upBelow_gen0 clear_gen0 h1)
  have Bq : BelowIn (gen0 : Gen Map).bo g1 := runX_below (goal := CGoal.done) hq rfl trivial hc.2 h1
  have cq : ∀ k, HoonMap.get g1.cond k = Option.none := fun k => by rw [Rq.cnd]; exact gen0_cond_none k
  obtain ⟨q1, q2, q3, q4⟩ := Rq.ext
  have qlo := Rq.lo
  have qhi := Rq.hi
  obtain ⟨d, CR⟩ := collRun_n4 lib hp sp kp ap h2 hc.1 (by omega) (q3.trans rfl) (Rq.grow.up upBelow_gen0)
    (clear_gen0.growU Rq.grow) Rq.lo Rq.hi (fun x hx => (Rq.regs x hx).2) (fun x _ => cq x)
    (fun k hk => by simp [cq k] at hk)
    (List.nodup_cons.mpr ⟨fun hm => by
      obtain ⟨e, he, e1⟩ := List.mem_map.mp hm
      have := (Rq.labs e he).2.1; omega, Rq.nodup⟩)
    (fun e he => by obtain ⟨a, b, th, hb⟩ := Rq.labs e he; exact ⟨by omega, [], _, hb⟩)
    (fun e he x hx => ((Rq.eregs e he).2 x hx).2)
  have Cre := CR.re
  have Cbo := CR.bo
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
  intro c ned σ O st t gul s0 s ag hned regs hh hn
  have agC : AgreeU lib O c gul st t g2.cond ned g1 g2 nex.laz s0 s :=
    ⟨fun o l u hnl => ag.1 o (by omega) u hnl, ag.2⟩
  have Sp := CR.sem g2.cond (fun _ _ => rfl) c ned σ O st t gul s0 s agC (fun r hr => Or.inl (hned r hr)) regs hh hn
  have u1 : ∀ x, x < g1.re → unproxy g2.cond x = id x := fun x hx =>
    unproxy_none (by rw [ProxyFor.get_lt CR.pfor hx]; exact cq x)
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
      have SpT := CR.semT hfa g2.cond (fun _ _ => rfl) c ned σ O st t gul s0 s agC
        (fun r hr => Or.inl (hned r hr)) regs hh hn
      rw [ev] at SpT
      obtain ⟨R, hR, kR, eR⟩ := SpT.1 ⟨trivial, looks_empty _⟩
      have hR' : SkaModel.read d R = some (A m) := hR
      have agQ : AgreeP lib O c gul st t (Need.pair ned (Need.this d)) gen0 g1 nx.laz (C s0 (A m)) (A m) := by
        refine ⟨fun o l u hnl => ?_, fun e he => ?_⟩
        · have hn2 : o ∉ (entries nex.laz).map Prod.fst := fun hm => by
            obtain ⟨e', he', e1⟩ := List.mem_map.mp hm; have := (CR.labs e' he').1; omega
          rw [ag.1 o l (by omega) hn2, CR.keep o u hnl]
          cases hg : HoonMap.get g1.blocks o with
          | none => rfl
          | some b => simp only [Option.map_some, unproxyBlob, renBlob_congr u1 (Bq o b l u hg), renBlob_id]
        · obtain ⟨l, lt, th, hb⟩ := Rq.labs e he
          obtain ⟨F, hF, hP⟩ := CR.front e he
          have hb2 := hF [] (Termin.hop th) hb
          rw [List.append_nil] at hb2
          have hn2 : e.1 ∉ (entries nex.laz).map Prod.fst := fun hm => by
            obtain ⟨e', he', e1⟩ := List.mem_map.mp hm; have := (CR.labs e' he').1; omega
          refine ⟨F.map (renPole (unproxy g2.cond)), th, hb, ?_, ?_⟩
          · rw [ag.1 e.1 l (by omega) hn2, hb2]
            have hj := (Bq e.1 _ l (by omega) hb).2.2
            simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, renFin, renJmp_congr u1 hj, renJmp_id]
          · exact collP_fillSem hP CR.dkey
              (fun x hx => by rw [ProxyFor.get_lt CR.pfor ((Rq.eregs e he).2 x hx).2]; exact cq x)
              (fun k hk => rfl) lib O c gul st t ned g1.re s0 m
      have inQ : ∀ r, NMem (Need.pair ned (Need.this d)) r → InR (CGoal.done : CGoal S) gen0 g1 nx.laz.sure.ned r := by
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

/-- **`[0 axe]` meets `AboveX`** for `axe` at least `2`: for a goal `%next`
it emits no block. -/
theorem aboveX_n0 {axe : Nat} (ha : 2 ≤ axe) : AboveX S Map (Nomm.n0 axe) := by
  intro a th region g g' nex h _ _ _ _ _ _ _ _ _ o b l u hb
  rw [runL_n0_next ha] at h
  obtain ⟨_, _, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨-, rfl⟩ := e
  omega

/-- **`[1 k]` meets `AboveX`**: `+mede` emits one block, `[imm k a]` with a
hop to the goal's jump, which has no arguments. -/
theorem aboveX_n1 {k : Noun} : AboveX S Map (Nomm.n1 k) := by
  intro a th region g g' nex h _ ea _ _ d0 _ _ _ _ o b l u hb
  have e1 : (runL (Nomm.n1 k) (CGoalL.next (ofSure (lazyReg a : Sure S)) th) region : CM Map (NextL S)) = (do
      let o ← medeL th k (ofSure (lazyReg a : Sure S))
      pure ⟨ofSure Sure.bunt, jmp0 o⟩) := by
    conv => lhs; unfold runL
  rw [e1] at h
  obtain ⟨o', g1, h1, h2⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨-, rfl⟩ := h2
  unfold medeL at h1
  obtain ⟨o1, gE, hE, h1⟩ := bind_some h1
  rw [emit_apply] at hE
  simp only [Option.some.injEq, Prod.mk.injEq] at hE
  obtain ⟨rfl, rfl⟩ := hE
  have dE : (g.emitted ⟨[], [], Termin.hop th⟩).drop = false := d0
  simp only [bind_apply, get_apply, Option.bind_some, dE, Bool.false_eq_true, if_false] at h1
  obtain ⟨⟨u1, gW⟩, hW, h3⟩ := Option.bind_eq_some_iff.mp h1
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
  obtain ⟨-, rfl⟩ := h3
  unfold walkLazy at hW
  obtain ⟨u2, gA, hA, hr⟩ := bind_some hW
  have hr' : some ((), gA) = some (u1, gW) := hr
  simp only [Option.some.injEq, Prod.mk.injEq] at hr'
  obtain ⟨-, rfl⟩ := hr'
  obtain ⟨ned, gB, hB, hC⟩ := bind_some hA
  have L := sureRequireLook_spec hB
  have en : ned = Need.this a := L.same (fun x hx => absurd hx (HoonSet.mem_empty x))
  subst en
  obtain ⟨kk, hkk⟩ := L.gen
  have dB : gB.drop = false := by rw [hkk]; exact d0
  have hC' : addOps g.bo [Pole.imm k a] gB = some (u2, gA) := by unfold medeLoop at hC; exact hC
  obtain ⟨b0, hb0, rfl⟩ := addOps_spec hC' dB
  have hb0' : b0 = ⟨[], [], Termin.hop th⟩ := by
    rw [hkk] at hb0
    have := emitted_get g ⟨[], [], Termin.hop th⟩ d0
    rw [this] at hb0
    exact (Option.some.inj hb0).symm
  subst hb0'
  have hbo : gB.bo = g.bo + 1 := by rw [hkk]; rfl
  have eo : o = g.bo := by
    have u' : o < gB.bo := u
    omega
  subst eo
  simp only [HoonMap.get_put, if_true, Option.some.injEq] at hb
  subst hb
  refine ⟨fun x hx => absurd hx (List.not_mem_nil), ?_, ?_⟩
  · intro q hq x hx
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at hq
    subst hq
    simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
    omega
  · intro x hx
    rw [ea] at hx
    exact absurd hx (List.not_mem_nil)

/-- **`[4 p]` meets `AboveX` when `p` does**: the collapse of the goal
`this a` emits no block (every atom fits `this a`), the increment block
mentions the register `+collapse-lazy-atom` returns (`a` itself, or one
allocated in the run) and a fresh register, and the blocks of `p` lie above
that fresh register. -/
theorem aboveX_n4 {lib : Lib} {p : Nomm} (hp : NextOK (S := S) (Map := Map) lib p) (ap : AboveX S Map p) :
    AboveX S Map (Nomm.n4 p) := by
  intro a th region g g' nex h ha ea h1 h2 d0 hu hcb hka hcount o b l u hb
  have e4 : (runL (Nomm.n4 p) (CGoalL.next (ofSure (lazyReg a)) th) region : CM Map (NextL S)) = (do
      let x ← collapseLazyAtomL ⟨ofSure (lazyReg a : Sure S), th⟩
      let (pro, th') ← collPick th x
      let arg ← re
      let o ← emit ⟨[], [Pole.inc arg pro], Termin.hop (jmp0 th')⟩
      runL p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region) := by
    conv => lhs; unfold runL
    rfl
  rw [e4] at h
  obtain ⟨x, gA, hc2, h⟩ := bind_some h
  obtain ⟨⟨d, th'⟩, g2, hm, h⟩ := bind_some h
  have hne : ∀ y, NMem (ofSure (lazyReg a) : Lazy S).sure.ned y → y = a := fun y hy => hy
  have P := collapsePre_spec hc2 hm d0 hcb (fun y hy => by rw [hne y hy]; exact ha)
    (fun y hy => by rw [hne y hy]; exact hka) (by simp [entries_ofSure]) (by simp [entries_ofSure])
    (by simp [entries_ofSure])
  obtain ⟨eth, ebo⟩ : th' = th.there ∧ g2.bo = g.bo := by
    rcases P.shape with ⟨e1, e2, -⟩ | ⟨-, -, hnf, -⟩
    · exact ⟨e1, e2⟩
    · exact absurd ⟨trivial, looks_empty _⟩ (hnf 0)
  have hda : a ≤ d := by
    rcases P.rreg with e | e
    · exact Nat.le_of_eq (hne d e).symm
    · omega
  simp only [bind_apply, pure_apply, Option.bind_some, re_apply, emit_apply] at h
  obtain ⟨g3, hg3⟩ : ∃ g3 : Gen Map, g3 = { g2 with re := g2.re + 1 } := ⟨_, rfl⟩
  obtain ⟨blk, hblk⟩ : ∃ blk : Blob, blk = ⟨[], [Pole.inc g2.re d], Termin.hop (jmp0 th')⟩ := ⟨_, rfl⟩
  obtain ⟨gE, hgE⟩ : ∃ gE : Gen Map, gE = g3.emitted blk := ⟨_, rfl⟩
  have hbo3 : g3.bo = g2.bo := by rw [hg3]
  have hre3 : g3.re = g2.re + 1 := by rw [hg3]
  have hcn3 : g3.cond = g2.cond := by rw [hg3]
  have hdr3 : g3.drop = false := by rw [hg3]; exact P.drop.trans d0
  rw [← hg3, ← hblk, ← hgE] at h
  have hboE : gE.bo = g2.bo + 1 := by rw [hgE, emitted_bo, hbo3]
  have hreE : gE.re = g2.re + 1 := by rw [hgE, emitted_re, hre3]
  have hcnE : gE.cond = g2.cond := by rw [hgE, ← hcn3]; rfl
  have hdE : gE.drop = false := by rw [hgE, emitted_drop]; exact hdr3
  have hbE : HoonMap.get gE.blocks g2.bo = some blk := by rw [hgE, ← hbo3]; exact emitted_get g3 blk hdr3
  have Ple := P.le
  have G : Grow g gE := by
    have g23 : Grow g2 g3 := by rw [hg3]; exact grow_re g2
    have g3E : Grow g3 gE := by
      rw [hgE]; refine grow_emit ?_
      rw [hblk, eth]; exact jumpsBelow_hop (j := jmp0 th.there) h1 (by simp only [jmp0]; omega)
    exact P.grow.trans (g23.trans g3E)
  have GU : GrowU g gE := G.toU hu
  have Rp := hp (sur := lazyReg g2.re) (th := jmp0 g2.bo) ⟨by simp only [jmp0]; omega, by simp only [jmp0]; omega⟩ rfl
    (by exact ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; omega⟩) (by exact trivial)
    (by simpa only [sixCount] using hcount) (by omega) hdE (GU.up hu) h
  obtain ⟨Rre, Rbo, Rdr, Rold⟩ := Rp.ext
  have cb2 : CondBelow g2 := P.pfor.1.below hcb
  have Ap := ap h (show g2.re < gE.re by omega) rfl (by simp only [jmp0]; omega) (by simp only [jmp0]; omega) hdE
    (GU.up hu) (fun x hx => by rw [hcnE] at hx; have := cb2 x hx; omega)
    (by
      rw [hcnE]
      cases e' : HoonMap.get g2.cond g2.re with
      | none => rfl
      | some _ => have := cb2 g2.re (by simp [e']); omega) (by simpa only [sixCount] using hcount)
  by_cases hlo : o < gE.bo
  · have eo : o = g2.bo := by omega
    rw [eo, Rold _ (by omega), hbE] at hb
    cases hb
    rw [hblk, eth]
    refine blobIn_one (p := Pole.inc g2.re d) (f := Termin.hop (jmp0 th.there)) ?_ ?_
    · intro y hy
      simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hy
      omega
    · simp only [FinIn, JmpIn, jmp0]; intro y hy; simp at hy
  · exact (Ap o b (by omega) u hb).mono fun y hy => by omega

/-- **The final pass meets the contract on `[7 [4 p] q]`**, with `p` and `q`
in `FragX`, `p` meeting `AboveX` (every `[0 axe]` with `2 ≤ axe` does,
`aboveX_n0`), at most 255 `%6`, when nothing is baked and the bell's cape has
no `[| |]`.  The first theorem of the top whose runs make proxies. -/
theorem finishLF_bellContract74U {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {bl : Bell} {p q : Nomm} (hp : (Nomm.n7 (Nomm.n4 p) q).pure = true)
    (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol (Nomm.n7 (Nomm.n4 p) q))
    (hfp : FragX (S := S) p) (ap : AboveX S Map p) (hfq : FragX (S := S) q)
    (hcount : sixCount (Nomm.n7 (Nomm.n4 p) q) ≤ 255)
    {cape : Cape} {data : Noun} (hbl : bl.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) (Nomm.n7 (Nomm.n4 p) q) ord cape bake = some c') (N : Needs) :
    BellContract lib N bl false c' :=
  finishLF_bellContractU hok hp hA (fun h1 => runOKU_seven4 lib (runX_ok lib hfp).2.1 (runX_semR lib hfp).2.1
    (runX_keeps hfp) ap hfq hcount h1) hbl hn hbake h N

/-- The target `[7 [4 [0 3]] [6 [5 [0 1] [1 6]] [0 1] [1 5]]]` meets every
hypothesis of `finishLF_bellContract74U` on the formula: `[0 3]` and the
`%6` are in `FragX`, `[0 3]` meets `AboveX`, one `%6`. -/
example : FragX (S := S) (Nomm.n0 3) ∧ AboveX S Map (Nomm.n0 3) ∧
    FragX (S := S) (Nomm.n6 (Nomm.n5 (Nomm.n0 1) (Nomm.n1 (A 6))) (Nomm.n0 1) (Nomm.n1 (A 5))) ∧
    sixCount (Nomm.n7 (Nomm.n4 (Nomm.n0 3)) (Nomm.n6 (Nomm.n5 (Nomm.n0 1) (Nomm.n1 (A 6))) (Nomm.n0 1)
      (Nomm.n1 (A 5)))) ≤ 255 :=
  ⟨FragX.frag fun _ => trivial, aboveX_n0 (by decide),
    FragX.six (FragX.five (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial)) (FragX.frag fun _ => trivial)
      (FragX.frag fun _ => trivial),
    by decide⟩

/-- **The target `[7 [4 [0 3]] [6 [5 [0 1] [1 6]] [0 1] [1 5]]]` meets the
contract** with no hypothesis beyond the usual ones (the code table, the
annotation, nothing baked, a cape with no `[| |]`). -/
theorem finishLF_bellContract_target {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {bl : Bell}
    (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol
      (Nomm.n7 (Nomm.n4 (Nomm.n0 3)) (Nomm.n6 (Nomm.n5 (Nomm.n0 1) (Nomm.n1 (A 6))) (Nomm.n0 1) (Nomm.n1 (A 5)))))
    {cape : Cape} {data : Noun} (hbl : bl.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) (Nomm.n7 (Nomm.n4 (Nomm.n0 3))
      (Nomm.n6 (Nomm.n5 (Nomm.n0 1) (Nomm.n1 (A 6))) (Nomm.n0 1) (Nomm.n1 (A 5)))) ord cape bake = some c')
    (N : Needs) : BellContract lib N bl false c' :=
  finishLF_bellContract74U hok rfl hA (FragX.frag fun _ => trivial) (aboveX_n0 (by decide))
    (FragX.six (FragX.five (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial)) (FragX.frag fun _ => trivial)
      (FragX.frag fun _ => trivial)) (by decide) hbl hn hbake h N

/-- A second covered formula, `[7 [4 [4 [0 6]]] [6 [0 1] [0 1] [1 0]]]`: its
`p` is a chain of two `%4` over `[0 6]` (`aboveX_n4`). -/
example (lib : Lib) : FragX (S := S) (Nomm.n4 (Nomm.n4 (Nomm.n0 6))) ∧ AboveX S Map (Nomm.n4 (Nomm.n4 (Nomm.n0 6))) ∧
    FragX (S := S) (Nomm.n6 (Nomm.n0 1) (Nomm.n0 1) (Nomm.n1 (A 0))) ∧
    sixCount (Nomm.n7 (Nomm.n4 (Nomm.n4 (Nomm.n0 6))) (Nomm.n6 (Nomm.n0 1) (Nomm.n0 1) (Nomm.n1 (A 0)))) ≤ 255 :=
  ⟨FragX.four (FragX.four (FragX.frag fun _ => trivial)),
    aboveX_n4 (runX_ok (Map := Map) lib (FragX.four (S := S) (FragX.frag (S := S) (nm := Nomm.n0 6) fun _ => trivial))).2.1
      (aboveX_n4 (runX_ok (Map := Map) lib (FragX.frag (S := S) (nm := Nomm.n0 6) fun _ => trivial)).2.1
        (aboveX_n0 (by decide))),
    FragX.six (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial) (FragX.frag fun _ => trivial),
    by decide⟩

end Run
