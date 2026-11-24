import lemmas.Ska.CompCollapseGate
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

/-- A step that only allocates registers is a walk over no block. -/
theorem WalkOKD.of_re {P : Map (Nat × List Nat) → Nat → Nat → Nat → Sure S → List Pole → Prop} {r : Nat}
    (g : Gen Map) (k : Nat) (hk : g.re ≤ k) : WalkOKD (ProxyFor r) P g { g with re := k } [] :=
  ⟨rfl, rfl, hk, ProxyFor.of_eq hk rfl, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩

/-- The gate at the goal's own block, for the need `this d`: nothing. -/
theorem collapseGate_self {d o : Nat} {lok : S} {g g' : Gen Map}
    (hl : ∀ x ∈ HoonSet.toList lok, x = 1)
    (h : collapseGate (S := S) (Map := Map) d o o ⟨Need.this d, lok⟩ g = some ((), g')) :
    ∃ k, g.re ≤ k ∧ g' = { g with re := k } := by
  unfold collapseGate at h
  obtain ⟨ned, g1, h1, h2⟩ := bind_some h
  have L := sureRequireLook_spec h1
  have e : ned = Need.this d := L.same hl
  subst e
  obtain ⟨kk, rfl⟩ := L.gen
  simp only [if_true, pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨-, rfl⟩ := h2
  exact ⟨kk, L.le, rfl⟩

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
blocks of `p` must not mention the proxies the walk made below `a`. -/
def AboveX (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (p : Nomm) : Prop :=
  ∀ {a : Nat} {th : Jmp} {region : List Nat} {g g' : Gen Map} {nex : NextL S},
    runL p (CGoalL.next (ofSure (lazyReg a)) th) region g = some (nex, g') → a < g.re →
    ∀ o b, g.bo ≤ o → o < g'.bo → HoonMap.get g'.blocks o = some b → BlobIn (a ≤ ·) b

/-- **What one run of `[4 p]` for a goal `%next laz th` with entries does,
when the goal's sure need is `this d`** (`collRun_n4`): the structural facts
of `RunOKE` with `ProxyFor d` in place of an unchanged `cond`, the entries of
the goal consumed with ops that do what `CollP d` says for the run's final
`cond` (`front`), fact (ii) for the result's needs (`ncond`, `econd`), fact
(i5) (`below`), and the relaxed `sem` against the blocks unproxied by any
`cond` that agrees with the run's below its end. -/
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

theorem fitsS_this_one {d : Nat} {lok : S} (hl : ∀ x ∈ HoonSet.toList lok, x = 1) (n : Noun) :
    FitsS (⟨Need.this d, lok⟩ : Sure S) n :=
  ⟨trivial, fun x hx => by rw [hl x hx]; simp⟩

/-- **`[4 p]` for a goal `%next laz th` with entries whose sure need is
`this d`.**  `p` is any nomm whose runs for a fork-free goal meet `RunOKN`,
the relaxed `sem`, (i5) (`KeepX`) and mention no register below their goal's
(`AboveX`). -/
theorem collRun_n4 (lib : Lib) {p : Nomm} (hp : NextOK (S := S) (Map := Map) lib p)
    (sp : OKNR (S := S) (Map := Map) lib p) (kp : KeepX S Map p) (ap : AboveX S Map p)
    {laz : Lazy S} {th : Jmp} {d : Nat} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (h : runL (Nomm.n4 p) (CGoalL.next laz th) region g0 = some (nex, g1))
    (hs : laz.sure.ned = Need.this d) (hl : ∀ x ∈ HoonSet.toList laz.sure.lok, x = 1)
    (hcount : sixCount p ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl0 : Clear g0)
    (h1 : 1 ≤ th.there) (h2 : th.there < g0.bo) (hdre : d < g0.re) (hd0 : HoonMap.get g0.cond d = Option.none)
    (hcb : CondBelow g0) (hnd : (th.there :: (entries laz).map Prod.fst).Nodup)
    (hlab : ∀ e ∈ entries laz, e.1 < g0.bo ∧ ∃ B fin, HoonMap.get g0.blocks e.1 = some ⟨[], B, fin⟩) :
    CollRunU lib (Nomm.n4 p) laz th d g0 g1 nex := by
  have e4 : (runL (Nomm.n4 p) (CGoalL.next laz th) region : CM Map (NextL S)) = (do
      let a ← collapseLazyAtomL ⟨laz, th⟩
      let (pro, th') ← (match a with
        | some x => pure x
        | Option.none => do
            let r ← re
            if th.args = [] then pure (r, th.there) else fun _ => Option.none : CM Map (Nat × Nat))
      let arg ← re
      let o ← emit ⟨[], [Pole.inc arg pro], Termin.hop (jmp0 th')⟩
      runL p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region) := by
    conv => lhs; unfold runL
    rfl
  rw [e4] at h
  obtain ⟨a, g2, hc2, h⟩ := bind_some h
  obtain ⟨ea, rfl, W⟩ := collapseL_this hc2 hs hl d0 hnd
  simp only [bind_apply, pure_apply, Option.bind_some, re_apply, emit_apply] at h
  obtain ⟨g3, hg3⟩ : ∃ g3 : Gen Map, g3 = { g2 with re := g2.re + 1 } := ⟨_, rfl⟩
  obtain ⟨blk, hblk⟩ : ∃ blk : Blob, blk = ⟨[], [Pole.inc g2.re d], Termin.hop (jmp0 th.there)⟩ := ⟨_, rfl⟩
  obtain ⟨gE, hgE⟩ : ∃ gE : Gen Map, gE = g3.emitted blk := ⟨_, rfl⟩
  have hbo3 : g3.bo = g2.bo := by rw [hg3]
  have hre3 : g3.re = g2.re + 1 := by rw [hg3]
  have hcn3 : g3.cond = g2.cond := by rw [hg3]
  have hbl3 : g3.blocks = g2.blocks := by rw [hg3]
  have hdr3 : g3.drop = false := by rw [hg3]; exact W.drop.trans d0
  rw [← hg3, ← hblk, ← hgE] at h
  have hboE : gE.bo = g2.bo + 1 := by rw [hgE, emitted_bo, hbo3]
  have hreE : gE.re = g2.re + 1 := by rw [hgE, emitted_re, hre3]
  have hcnE : gE.cond = g2.cond := by rw [hgE, ← hcn3]; rfl
  have hdE : gE.drop = false := by rw [hgE, emitted_drop]; exact hdr3
  have hbE : HoonMap.get gE.blocks g2.bo = some blk := by rw [hgE, ← hbo3]; exact emitted_get g3 blk hdr3
  have oE : ∀ o, o ≠ g2.bo → HoonMap.get gE.blocks o = HoonMap.get g2.blocks o := fun o ho => by
    rw [hgE, ← hbl3]; simp [Gen.emitted, hdr3, HoonMap.get_put, hbo3, ho]
  have Wbo := W.bo
  have Wle := W.le
  -- the walk adds ops in front of the entries only
  have hgrow2 : Grow g0 g2 := by
    refine ⟨by omega, W.drop, fun kk b _ hb => ?_, fun kk b' hb' => ?_⟩
    · by_cases hm : kk ∈ (entries laz).map Prod.fst
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
        obtain ⟨B, fin, hB⟩ := (hlab e he).2
        obtain ⟨A, hA, _⟩ := W.at_ e he
        rw [hB] at hb; cases hb
        exact ⟨_, hA B fin hB, rfl, rfl⟩
      · exact ⟨b, (W.other kk hm).trans hb, rfl, rfl⟩
    · by_cases hm : kk ∈ (entries laz).map Prod.fst
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
        obtain ⟨B, fin, hB⟩ := (hlab e he).2
        obtain ⟨A, hA, _⟩ := W.at_ e he
        rw [hA B fin hB] at hb'; cases hb'
        exact Or.inl ⟨_, hB, rfl, rfl⟩
      · rw [W.other kk hm] at hb'
        exact Or.inl ⟨b', hb', rfl, rfl⟩
  have G : Grow g0 gE := by
    have g23 : Grow g2 g3 := by rw [hg3]; exact grow_re g2
    have g3E : Grow g3 gE := by
      rw [hgE]; refine grow_emit ?_
      rw [hblk]; exact jumpsBelow_hop (j := jmp0 th.there) h1 (by simp only [jmp0]; omega)
    exact hgrow2.trans (g23.trans g3E)
  have GU : GrowU g0 gE := G.toU hu
  have Rp := hp (sur := lazyReg g2.re) (th := jmp0 g2.bo) ⟨by simp only [jmp0]; omega, by simp only [jmp0]; omega⟩ rfl
    (by exact ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; omega⟩) (by exact trivial)
    hcount (by omega) hdE (GU.up hu) h
  have Sp := sp (sur := lazyReg g2.re) (th := jmp0 g2.bo) ⟨by simp only [jmp0]; omega, by simp only [jmp0]; omega⟩ rfl
    (by exact ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; omega⟩) (by exact trivial)
    hcount (by omega) hdE (GU.up hu) (hcl0.growU GU) h
  have hbIn : BlobIn (· < g3.re) blk := by
    rw [hblk]
    refine blobIn_one (p := Pole.inc g2.re d) (f := Termin.hop (jmp0 th.there)) ?_ ?_
    · intro x hx
      simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
      omega
    · simp only [FinIn, JmpIn, jmp0]; intro x hx; simp at hx
  have Kp : KeepR g3 g1 nex (sixCount p) := keepX_tail (arg := g2.re) kp hdr3 hbIn
    (o := g2.bo) (by omega) hcount (by rw [emit_apply, hbo3, ← hgE]) h
  have Ap := ap h (show g2.re < gE.re by omega)
  obtain ⟨Rre, Rbo, Rdr, Rold⟩ := Rp.ext
  have hcn1 : g1.cond = g2.cond := Rp.cnd.trans hcnE
  -- the final `cond` has no key from the walk's end on
  have nk1 : ∀ x, g2.re ≤ x → HoonMap.get g1.cond x = Option.none := fun x hx => by
    rw [hcn1]
    rcases W.cnd.1.2 x with e | ⟨_, l⟩
    · rw [e]
      cases e' : HoonMap.get g0.cond x with
      | none => rfl
      | some _ => have := hcb x (by simp [e']); omega
    · omega
  have hg1o : HoonMap.get g1.blocks g2.bo = some blk := (Rold _ (by omega)).trans hbE
  have keep1 : ∀ o, o < g0.bo → HoonMap.get g1.blocks o = HoonMap.get g2.blocks o := fun o ho =>
    (Rold o (by omega)).trans (oE o (by omega))
  have bel1 : BelowIn gE.bo g1 := Kp.keeps.bel gE.bo (fun o _ l u _ => absurd u (by omega))
  refine ⟨by omega, by omega, Rdr.trans (hdE.trans d0.symm), fun o ho hn => (keep1 o ho).trans (W.other o hn),
    GU.trans Rp.grow, W.cnd.trans (ProxyFor.of_eq (by omega) hcn1), Rp.lo, Rp.hi, ?ent, ?regs, Rp.dist, ?eregs,
    ?labs, Rp.nodup, by simpa only [sixCount] using Rp.size, ?front, ?ncond, ?econd, ?below, ?nec, ?sem⟩
  case ent =>
    rcases Rp.ent with f | e
    · exact f
    · simp only [GoalJ] at e
      rw [e]
      have fr : Fresh gE (jmp0 g2.bo) := by
        rw [hgE]; exact fresh_emitted (b := blk) hdr3 (by rw [hblk]) (by simp [jmp0, hbo3]) rfl
      exact fr.growU (by simp only [jmp0]; omega) Rp.grow
  case regs =>
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
    obtain ⟨A, hA, hP⟩ := W.at_ e he
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
    exact Kp.keeps.bel g0.bo (fun o _ l u _ => absurd u (by omega))
  case nec =>
    intro s hs'
    rw [pureEval_n4]
    rcases Rp.nec s hs' with e | ⟨x, _, e⟩
    · rw [e]; rfl
    · exact absurd ⟨trivial, looks_empty x⟩ e
  case sem =>
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
      · obtain ⟨A, th', hb1, hc1, hfs⟩ := ag.2 e he
        obtain ⟨l, lt, -⟩ := Rp.labs e he
        have hb := bel1 e.1 _ l (by have := Rp.hi; omega) hb1
        have ha := Ap e.1 _ l (by have := Rp.hi; omega) hb1
        refine ⟨A, th', hb1, ?_, hfs⟩
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
      (hu1 d (by omega)).trans (unproxy_none (by rw [hcn1, ProxyFor.get_lt W.cnd hdre]; exact hd0))
    have ua : unproxy cf g2.re = g2.re := (hu1 _ (by omega)).trans (hu2 _ (Nat.le_refl _))
    have hco : HoonMap.get c.blocks g2.bo = some blk := by
      rw [ag.1 g2.bo (by omega) (by omega) (fun hm => ?_), hg1o]
      · simp [unproxyBlob, renBlob, hblk, renPole, renFin, renJmp, jmp0, ud, ua]
      · obtain ⟨e, he, e1⟩ := List.mem_map.mp hm; have := (Rp.labs e he).1; omega
    have nd : ∀ r, KeepI (CGoal.next laz.sure th) g0 ned r → r ≠ d ∧
        KeepI (CGoal.next (lazyReg g2.re : Sure S) (jmp0 g2.bo)) gE ned r := by
      intro r hr
      rcases hr with ⟨h1', h2'⟩ | h1'
      · refine ⟨fun e => h2' (by rw [e]; show NMem laz.sure.ned d; rw [hs]; rfl), Or.inl ⟨by omega, ?_⟩⟩
        show ¬ NMem (Need.this g2.re) r
        simp only [NMem]; omega
      · refine ⟨fun e => ?_, Or.inr h1'⟩
        subst e
        rcases hned r h1' with e | ⟨_, e⟩ | e
        · omega
        · exact e (by show NMem laz.sure.ned r; rw [hs]; rfl)
        · rcases Rp.regs r e with e' | e'
          · simp only [lazyReg, NMem] at e'; omega
          · omega
    rw [pureEval_n4]
    cases ev : pureEval p s with
    | none => rw [ev] at Hp; exact goalSem_none _ Hp
    | some x =>
      rw [ev] at Hp
      obtain ⟨R, hR, k, he⟩ := Hp.1 ⟨trivial, looks_empty x⟩
      have hj' := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) R t _ _ hco
      rw [hblk] at hj'
      cases x with
      | atom n =>
        rw [show [Pole.inc g2.re d] = [Pole.inc g2.re d] ++ [] from rfl, runs_inc hR, execBlob_hop] at hj'
        simp only [Option.bind_some, incF]
        refine ⟨fun _ => ⟨store d (A (n + 1)) R, ?_, fun r hr => ?_, ?_⟩, fun nf => absurd ?_ nf⟩
        · rw [hs]; exact read_store_eq _ _ _
        · obtain ⟨rd, kr⟩ := nd r hr
          rw [read_store_ne rd]; exact k r kr
        · rw [he, hj', jmp0_of_args ea]
        · exact ⟨by rw [hs]; trivial, fun y hy => by rw [hl y hy]; simp⟩
      | cell u v =>
        simp only [Option.bind_some, incF]
        apply goalSem_crash
        rw [he, hj', show [Pole.inc g2.re d] = [Pole.inc g2.re d] ++ [] from rfl, crashes_inc hR]

/-- **`[7 [4 p] q]` for `%done` from `gen0` meets `RunOKU`**, when every run
of `q` for `%done` from `gen0` returns a sure need `this d` with looks at
axis `1` only.  `q`'s relaxed `sem` is taken at the widened input need
`pair ned (this d)` holding `[s0 v]`, which `InR` admits since `this d` is the
sure need of `q`'s result, and the lazy blocks of `q` are filled by the ops
of the walk unproxied by the final `cond` (`collP_fillSem`). -/
theorem runOKU_seven4 (lib : Lib) {p q : Nomm} (hp : NextOK (S := S) (Map := Map) lib p)
    (sp : OKNR (S := S) (Map := Map) lib p) (kp : KeepX S Map p) (ap : AboveX S Map p)
    (hq : FragX (S := S) q) (hcount : sixCount (Nomm.n7 (Nomm.n4 p) q) ≤ 255) {region : List Nat}
    {g2 : Gen Map} {nex : NextL S}
    (h : runL (Nomm.n7 (Nomm.n4 p) q) (CGoalL.done : CGoalL S) region (gen0 : Gen Map) = some (nex, g2))
    (hsq : ∀ {nx : NextL S} {g1 : Gen Map}, runL q (CGoalL.done : CGoalL S) region (gen0 : Gen Map) = some (nx, g1) →
      ∃ d, nx.laz.sure.ned = Need.this d ∧ ∀ x ∈ HoonSet.toList nx.laz.sure.lok, x = 1) :
    RunOKU (Map := Map) lib (Nomm.n7 (Nomm.n4 p) q) CGoal.done gen0 g2 nex := by
  have hc : sixCount p ≤ 255 ∧ sixCount q ≤ 255 := by simp only [sixCount] at hcount; omega
  have p7 : ∀ s, pureEval (Nomm.n7 (Nomm.n4 p) q) s = (pureEval (Nomm.n4 p) s).bind (pureEval q) := fun _ => rfl
  rw [runL_n7] at h
  obtain ⟨nx, g1, h1, h2⟩ := bind_some h
  obtain ⟨d, hs, hl⟩ := hsq h1
  have Rq := (runX_ok (Map := Map) lib hq).1 trivial trivial hc.2 (by simp [gen0]) rfl upBelow_gen0 h1
  have Sq := SemPR.toG ((runX_semR (Map := Map) lib hq).1 trivial trivial trivial hc.2 (by simp [gen0]) rfl
    upBelow_gen0 clear_gen0 h1)
  have Bq : BelowIn (gen0 : Gen Map).bo g1 := runX_below (goal := CGoal.done) hq rfl trivial hc.2 h1
  have cq : ∀ k, HoonMap.get g1.cond k = Option.none := fun k => by rw [Rq.cnd]; exact gen0_cond_none k
  obtain ⟨q1, q2, q3, q4⟩ := Rq.ext
  have qlo := Rq.lo
  have qhi := Rq.hi
  have dre : d < g1.re := (Rq.regs d (by rw [hs]; rfl)).2
  have CR := collRun_n4 lib hp sp kp ap h2 hs hl hc.1 (by omega) (q3.trans rfl) (Rq.grow.up upBelow_gen0)
    (clear_gen0.growU Rq.grow) Rq.lo Rq.hi dre (cq d) (fun k hk => by simp [cq k] at hk)
    (List.nodup_cons.mpr ⟨fun hm => by
      obtain ⟨e, he, e1⟩ := List.mem_map.mp hm
      have := (Rq.labs e he).2.1; omega, Rq.nodup⟩)
    (fun e he => by obtain ⟨a, b, th, hb⟩ := Rq.labs e he; exact ⟨by omega, [], _, hb⟩)
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
    have fit : FitsS nx.laz.sure (A m) := ⟨by rw [hs]; trivial, fun y hy => by rw [hl y hy]; simp⟩
    obtain ⟨R, hR, kR, eR⟩ := Sp.1 fit
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
        · exact collP_fillSem hP (by rw [ProxyFor.get_lt CR.pfor dre]; exact cq d)
            (fun x hx => by rw [ProxyFor.get_lt CR.pfor ((Rq.eregs e he).2 x hx).2]; exact cq x)
            (fun k hk => rfl) lib O c gul st t ned g1.re s0 m
    have inQ : ∀ r, NMem (Need.pair ned (Need.this d)) r → InR (CGoal.done : CGoal S) gen0 g1 nx.laz.sure.ned r := by
      intro r hr
      rcases hr with hr | hr
      · exact Or.inl (by have := hned r hr; omega)
      · exact Or.inr (Or.inr (by rw [hs]; exact hr))
    have hR' : SkaModel.read d R = some (A m) := by rw [hs] at hR; exact hR
    have hnR : HoldsN (Need.pair ned (Need.this d)) R (C s0 (A m)) :=
      ⟨HoldsN.agree ned (fun r hr => kR r (Or.inr hr)) hn, hR'⟩
    have Sq' := Sq c _ σ O st t gul _ _ agQ inQ R ⟨hR, fit.2⟩ hnR
    exact eR.trans Sq'

end Run
