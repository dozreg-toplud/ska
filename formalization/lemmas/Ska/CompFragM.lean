import lemmas.Ska.CompSevenN

/-!
# `%3`, `%4`, `%7` and `%6` nested in any order

`FragM`: the nomms built from the nomms of `Frag` by `[6 c a b]`, `[4 p]`,
`[3 p]` and `[7 p q]` (with `q` in `Frag`), in any order, in the tests of
`%6` too.  Every `%next` goal that a `%6` of such a nomm meets is fork-free:
`[4 p]` and `[3 p]` run `p` for the goal `%next` of one fresh register, and
`[7 p q]` runs `p` for the need of `q`, which has no forks as `q` has no
`%6`.  Every `%pick` goal has jumps without arguments (`jmp0` of the yes and
no blocks of a `%6`).

`runM_ok`: on `FragM` every run for `%done` and for such a `%pick` meets
`RunOKP`, and every run for a fork-free goal `%next` whose jump passes no
arguments meets `RunOKN`, by induction, with the parent cases for `%next`
(`runOKN_n4`, `runOKN_n3`, `runOKN_n7`, through `unaryN_ok`), for `%done`
(`runOKP_n4`, `runOKP_n3`, `runOKP_n7`) and for `%pick` (`runOKP_n4p`,
`runOKP_n3p`, `runOKP_n7g`, through `unaryG_ok`), and `sixP_ok`,
`sixNext_okN` for `%6`.  `finishLF_bellContractM` and `crash_iffM`: the top
theorems on `FragM`.

For example `[4 [6 [0 2] [3 [6 [0 6] [1 1] [0 7]]] [4 [0 3]]]]` and
`[6 [4 [6 [0 2] [1 0] [1 1]]] [0 2] [0 3]]` are in `FragM` and not in
`FragT`.  `[7 [6 [0 2] [1 1] [1 2]] [6 [0 2] [0 3] [0 1]]]`
is in neither: the run of `[6 [0 2] [1 1] [1 2]]` is for the need of the
second `%6`, which has forks.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## A unary case for a fork-free `%next` -/

/-- **A unary case for a fork-free goal `%next`**: the code of `p` for the
goal `%next` of the register `a`, into a block `o` that does for the goal
what `f` of `a` asks. -/
theorem unaryN_ok {lib : Lib} {nm p : Nomm} {sur : Sure S} {th : Jmp} {g0 g' g1 : Gen Map} {a o : Nat}
    {nexp : NextL S} {f : Noun → Option Noun} (hev : ∀ s, pureEval nm s = (pureEval p s).bind f)
    (hpre : Ext g0 g') (hgr : GrowU g0 g') (hcnd : g'.cond = g0.cond) (ha : g0.re ≤ a ∧ a < g'.re)
    (ho : o < g'.bo) (hfr : Fresh g' (jmp0 o)) (hp : RunOKN (Map := Map) lib p (lazyReg a) (jmp0 o) g' g1 nexp)
    (hsz : sixCount nm = sixCount p)
    (hblk : ∀ (c : Straight Map), Agree c g0 g' → ∀ (σ : Type) (O : Oracle σ) st regs t gul x,
      SkaModel.read a regs = some x →
      GoalSem lib O c gul st (Keep g0 g' (CGoal.next sur th)) regs t (jmp0 o) (CGoal.next sur th) (f x)) :
    RunOKN (Map := Map) lib nm sur th g0 g1 nexp := by
  refine ⟨hpre.trans hp.ext, hgr.trans hp.grow, hp.cnd.trans hcnd, hp.lo, hp.hi, ?_, fun r hr => ?_, hp.dist,
    fun e he => ?_, fun e he => ?_, hp.nodup, by rw [hsz]; exact hp.size, fun s hs => ?_, ?_⟩
  · rcases hp.ent with f | e
    · exact Or.inl f
    · simp only [GoalJ] at e
      rw [e]; exact Or.inl (hfr.growU ho hp.grow)
  · have := hp.ext.1; have := hpre.1
    rcases hp.regs r hr with h | h
    · simp only [lazyReg, NMem] at h; subst h; exact Or.inr ⟨ha.1, by omega⟩
    · exact Or.inr ⟨by omega, h.2⟩
  · exact ⟨(hp.eregs e he).1, fun r hr => by have := (hp.eregs e he).2 r hr; have := hpre.1; omega⟩
  · obtain ⟨x, y, z⟩ := hp.labs e he
    exact ⟨by have := hpre.2.1; omega, y, z⟩
  · left; rw [hev]
    rcases hp.nec s hs with h | ⟨x, _, h2⟩
    · rw [h]; rfl
    · exact absurd ⟨trivial, looks_empty x⟩ h2
  · intro c ned σ O st t gul s0 s ag hned regs hh hn
    have agP : AgreeP lib O c gul st t ned g' g1 nexp.laz s0 s :=
      ⟨fun o' h0 h1 hnl => ag.1 o' (Nat.le_trans hpre.2.1 h0) h1 hnl, ag.2⟩
    have Sp := hp.sem c ned σ O st t gul s0 s agP hned regs hh hn
    have agQ : Agree c g0 g' := fun o' h0 h1 => by
      rw [ag.1 o' h0 (Nat.lt_of_lt_of_le h1 hp.ext.2.1) (fun hm => ?_)]
      · exact hp.ext.2.2.2 o' h1
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
        have := (hp.labs e he).1; omega
    have l1 := hp.ext.1
    rw [hev]
    cases e : pureEval p s with
    | none => rw [e] at Sp; exact goalSem_none _ Sp
    | some x =>
      rw [e] at Sp
      obtain ⟨R, hR, k, he⟩ := Sp.1 ⟨trivial, looks_empty x⟩
      refine goalSem_pre (fun r hr => k r ⟨?_, ?_⟩) he _ _
        (goalSem_mono (fun r hr => ?_) _ _ (hblk c agQ σ O st R t gul x hR))
      · rcases hr.1 with h | h
        · exact Or.inl (by omega)
        · exact Or.inr h
      · simp only [lazyReg, NMem]
        intro ea; subst ea
        rcases hr.1 with h | h
        · omega
        · have := hned _ h; omega
      · simp only [Keep, GMem]
        refine ⟨?_, hr.2⟩
        rcases hr.1 with h | h
        · exact Or.inl h
        · have := hned r h; exact Or.inr (by omega)

/-! ## `[4 p]` and `[3 p]` under a fork-free `%next` -/

/-- **`[4 p]` for a fork-free `%next`**, from `RunOKN` of `p`. -/
theorem runOKN_n4 (lib : Lib) {p : Nomm} (hp : NextOK (S := S) (Map := Map) lib p) {sur : Sure S} {th : Jmp}
    {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} (hj : GJ g0.bo (CGoal.next sur th))
    (hcount : sixCount p ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0)
    (h : runL (Nomm.n4 p) (CGoalL.next (ofSure sur) th) region g0 = some (nex, g1)) :
    RunOKN (Map := Map) lib (Nomm.n4 p) sur th g0 g1 nex := by
  have e4 : (runL (Nomm.n4 p) (CGoalL.next (ofSure sur) th) region : CM Map (NextL S)) = (do
      let a ← collapseLazyAtomL ⟨ofSure sur, th⟩
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
  rw [e4, collapseLazyAtomL_mk] at h
  obtain ⟨a, g2, h2, h⟩ := bind_some h
  obtain ⟨E2, ea, hnone, hsome⟩ := collapse_ok h2
  have C := collapse_down h2 hj.1 hj.2 b0
  have c2 : g2.cond = g0.cond := (kc_collapseLazyAtom _).keep g0 a g2 h2
  obtain ⟨⟨pro, th'⟩, g3, h3, h⟩ := bind_some h
  have P : Ext g2 g3 ∧ g3.cond = g2.cond ∧ Grow g2 g3 ∧ (1 ≤ th' ∧ th' < g3.bo) ∧
      (NMem sur.ned pro ∨ (g0.re ≤ pro ∧ pro < g3.re)) ∧
      (g0.drop = false → ∀ (c : Straight Map), Agree c g0 g2 → ∀ (σ : Type) (O : Oracle σ) (st : σ) regs t gul n,
        SkaModel.read pro regs = some (A n) → ∀ {K : Nat → Prop},
        GoalSem lib O c gul st K regs t (jmp0 th') (CGoal.next sur th) (some (A n))) := by
    cases a with
    | some x =>
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
      obtain ⟨e1, rfl⟩ := h3
      subst e1
      obtain ⟨hm, _, hs⟩ := hsome pro th' rfl
      exact ⟨Ext.refl _, rfl, Grow.refl _, C.2 pro th' rfl, hm,
        fun hd c hc σ O st regs t gul n hr => hs hd c hc lib σ O st regs t gul n hr⟩
    | none =>
      obtain ⟨hn, hl⟩ := hnone rfl
      simp only [bind_apply, re_apply, Option.bind_some, ea, if_true, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h3
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h3
      refine ⟨ext_re _, rfl, grow_re _, ⟨hj.1, by have := C.1.bo; have := hj.2; show th.there < g2.bo; omega⟩,
        Or.inr ⟨E2.1, Nat.lt_succ_self _⟩, fun _ c _ σ O st regs t gul n hr => ?_⟩
      refine ⟨fun _ => ⟨regs, by rw [hn]; trivial, fun _ _ => rfl, by rw [jmp0_of_args ea]⟩, fun hf => ?_⟩
      exact absurd ⟨by rw [hn]; trivial, fun y hy => by rw [hl y hy]; simp⟩ hf
  simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
  have d3 : g3.drop = false := P.1.2.2.1.trans (E2.2.2.1.trans d0)
  have bo3 : g0.bo ≤ g3.bo := Nat.le_trans C.1.bo P.1.2.1
  have G : Grow g0 ({ g3 with re := g3.re + 1 }.emitted ⟨[], [Pole.inc g3.re pro], Termin.hop (jmp0 th')⟩) :=
    C.1.trans (P.2.2.1.trans ((grow_re _).trans (grow_emit (jumpsBelow_hop P.2.2.2.1.1 P.2.2.2.1.2))))
  have Rp := hp ⟨by simp only [jmp0]; omega, by simp only [jmp0, emitted_bo]; omega⟩ rfl
    (by exact ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; simp [emitted_re]⟩) (by exact trivial)
    hcount (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d3) ((G.toU hu).up hu) h
  refine unaryN_ok (pureEval_n4 p) (E2.trans (P.1.trans ((ext_re _).trans (ext_emit _ _)))) (G.toU hu)
    (P.2.1.trans c2) ⟨by have := E2.1; have := P.1.1; omega, by simp [emitted_re]⟩ (by simp [emitted_bo])
    (fresh_emitted (by simpa using d3) rfl rfl) Rp rfl ?_
  intro c hc σ O st regs t gul x hx
  have hb := emitted_get' (by simpa using d3) (hc _ bo3 (by simp [emitted_bo]))
  have hj' := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
  cases x with
  | atom n =>
    rw [show [Pole.inc _ _] = [Pole.inc _ _] ++ [] from rfl, runs_inc hx, execBlob_hop] at hj'
    refine GoalSem.transfer hj' (fun r ⟨h1, h2⟩ => read_store_ne (fun e => ?_) _ _)
      (P.2.2.2.2.2 d0 c (hc.left E2 (P.1.trans ((ext_re _).trans (ext_emit _ _)))) σ O st
        (store pro (A (n + 1)) regs) t gul (n + 1) (read_store_eq _ _ _))
    subst e
    rcases P.2.2.2.2.1 with hm | ⟨hm, hm'⟩
    · exact h2 hm
    · simp [emitted_re] at h1; omega
  | cell u v =>
    apply goalSem_crash
    rw [hj', show [Pole.inc _ _] = [Pole.inc _ _] ++ [] from rfl, crashes_inc hx]

/-- `[3 p]` for a fork-free `%next` that asks nothing of the product: the
code of `p` for the same goal. -/
theorem runOKN_n3_of_none {lib : Lib} {p : Nomm} {sur : Sure S} {th : Jmp} {g0 g1 : Gen Map} {nex : NextL S}
    (hn : sur.ned = Need.none) (hl : ∀ x ∈ HoonSet.toList sur.lok, x = 1)
    (hp : RunOKN (Map := Map) lib p sur th g0 g1 nex) : RunOKN (Map := Map) lib (Nomm.n3 p) sur th g0 g1 nex := by
  have hfit : ∀ v, FitsS sur v := fun v => ⟨by rw [hn]; trivial, fun y hy => by rw [hl y hy]; simp⟩
  refine ⟨hp.ext, hp.grow, hp.cnd, hp.lo, hp.hi, hp.ent, hp.regs, hp.dist, hp.eregs, hp.labs, hp.nodup,
    by simp only [sixCount]; exact hp.size, fun s hs => ?_, ?_⟩
  · left; rw [pureEval_n3]
    rcases hp.nec s hs with h | ⟨x, _, h2⟩
    · rw [h]; rfl
    · exact absurd (hfit x) h2
  · intro c ned σ O st t gul s0 s ag hned regs hh hn'
    have H := hp.sem c ned σ O st t gul s0 s ag hned regs hh hn'
    rw [pureEval_n3]
    cases e : pureEval p s with
    | none => rw [e] at H; exact goalSem_none _ H
    | some x =>
      rw [e] at H
      obtain ⟨regs', _, hk, he⟩ := H.1 (hfit x)
      exact ⟨fun _ => ⟨regs', by rw [hn]; trivial, hk, he⟩, fun hf => absurd (hfit _) hf⟩

/-- **`[3 p]` for a fork-free `%next`**, from `RunOKN` of `p`. -/
theorem runOKN_n3 (lib : Lib) {p : Nomm} (hp : NextOK (S := S) (Map := Map) lib p) {sur : Sure S} {th : Jmp}
    {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} (hj : GJ g0.bo (CGoal.next sur th)) (hth : th.args = [])
    (hok : GoalOK g0 (CGoal.next sur th)) (hcl : Clean sur.ned)
    (hcount : sixCount p ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0)
    (h : runL (Nomm.n3 p) (CGoalL.next (ofSure sur) th) region g0 = some (nex, g1)) :
    RunOKN (Map := Map) lib (Nomm.n3 p) sur th g0 g1 nex := by
  have e3 : (runL (Nomm.n3 p) (CGoalL.next (ofSure sur) th) region : CM Map (NextL S)) =
      if noneEquivalentL (ofSure sur) then runL p (CGoalL.next (ofSure sur) th) region else (do
        let a ← collapseLazyAtomL ⟨ofSure sur, th⟩
        match a with
        | Option.none => fun _ => Option.none
        | some (r, o) => do
            let (z, o') ← forl r o
            let r' ← re
            let oc ← emit ⟨[], [], Termin.clq r' (jmp0 z) (jmp0 o')⟩
            runL p (CGoalL.next (ofSure (lazyReg r')) (jmp0 oc)) region) := by
    conv => lhs; unfold runL
    rfl
  rw [e3, noneEquivalentL_ofSure] at h
  by_cases en : noneEquivalent sur = true
  · rw [if_pos en] at h
    have en' := en
    simp only [noneEquivalent, Bool.and_eq_true, decide_eq_true_eq, HoonSet.small_iff] at en'
    exact runOKN_n3_of_none en'.1 en'.2 (hp hj hth hok hcl hcount b0 d0 hu h)
  rw [if_neg en, collapseLazyAtomL_mk] at h
  obtain ⟨a, g2, h2, h⟩ := bind_some h
  obtain ⟨E2, ea, _, hsome⟩ := collapse_ok h2
  have C := collapse_down h2 hj.1 hj.2 b0
  have c2 : g2.cond = g0.cond := (kc_collapseLazyAtom _).keep g0 a g2 h2
  rcases a with _ | ⟨r, o⟩
  · cases h
  obtain ⟨hmr, _, hs⟩ := hsome r o rfl
  obtain ⟨⟨z, o'⟩, g3, h3, h⟩ := bind_some h
  have hr : r < g2.re := by
    rcases hmr with hm | ⟨_, h2⟩
    · exact Nat.lt_of_lt_of_le (hok.2 r hm) E2.1
    · exact h2
  obtain ⟨E3, er3, eb3, F⟩ := forl_ok h3 hr
  have Co := C.2 r o rfl
  have Fd := forl_down h3 Co.1 Co.2 (Nat.le_trans b0 C.1.bo)
  have c3 : g3.cond = g2.cond := (kc_forl r o).keep g2 _ g3 h3
  simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
  have Ep := (ext_re g3).trans (ext_emit { g3 with re := g3.re + 1 } ⟨[], [], Termin.clq g3.re (jmp0 z) (jmp0 o')⟩)
  have d2 : g2.drop = false := E2.2.2.1.trans d0
  have d3 : g3.drop = false := E3.2.2.1.trans d2
  have bo3 : g0.bo ≤ g3.bo := Nat.le_trans C.1.bo E3.2.1
  have G : Grow g0 ({ g3 with re := g3.re + 1 }.emitted ⟨[], [], Termin.clq g3.re (jmp0 z) (jmp0 o')⟩) :=
    C.1.trans (Fd.1.trans ((grow_re _).trans (grow_emit (jumpsBelow_two rfl Fd.2.1 Fd.2.2))))
  have Rp := hp ⟨by simp only [jmp0]; omega, by simp only [jmp0, emitted_bo]; omega⟩ rfl
    (by exact ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; simp [emitted_re]⟩) (by exact trivial)
    hcount (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d3) ((G.toU hu).up hu) h
  refine unaryN_ok (pureEval_n3 p) (E2.trans (E3.trans Ep)) (G.toU hu) (c3.trans c2)
    ⟨by have := E2.1; have := E3.1; omega, by simp [emitted_re]⟩ (by simp [emitted_bo])
    (fresh_emitted (by simpa using d3) rfl rfl) Rp rfl ?_
  intro c hc σ O st regs t gul x hx
  have hb := emitted_get' (by simpa using d3) (hc _ bo3 (by simp [emitted_bo]))
  have hj' := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
  rw [execBlob_clq, hx, Option.bind_some] at hj'
  have F' := F d2 c ((hc.right E2).left E3 Ep) lib σ O st regs t gul
  have hag2 : Agree c g0 g2 := hc.left E2 (E3.trans Ep)
  have keep : ∀ (v : Noun) (k : Nat) (rr : Nat), (k = g2.re ∨ k = g2.re + 1) → (rr < g0.re ∨ g3.re + 1 ≤ rr) →
      ¬ NMem sur.ned rr → SkaModel.read rr (store r v (store k v regs)) = SkaModel.read rr regs := by
    intro v k rr hk k1 k2
    have := er3
    have hne : rr ≠ r := fun e => by
      subst e
      rcases hmr with hm | ⟨hm, _⟩
      · exact k2 hm
      · omega
    rw [read_store_ne hne, read_store_ne (show rr ≠ k by have := E2.1; omega)]
  cases x with
  | cell u v =>
    exact GoalSem.transfer (hj'.trans F'.1)
      (fun rr ⟨k1, k2⟩ => keep (A 0) g2.re rr (Or.inl rfl) (by simpa [emitted_re] using k1) k2)
      (hs d0 c hag2 lib σ O st (store r (A 0) (store g2.re (A 0) regs)) t gul 0 (read_store_eq _ _ _))
  | atom n =>
    exact GoalSem.transfer (hj'.trans F'.2)
      (fun rr ⟨k1, k2⟩ => keep (A 1) (g2.re + 1) rr (Or.inr rfl) (by simpa [emitted_re] using k1) k2)
      (hs d0 c hag2 lib σ O st (store r (A 1) (store (g2.re + 1) (A 1) regs)) t gul 1 (read_store_eq _ _ _))

/-! ## `[7 p q]` under a fork-free `%next` -/

/-- **`[7 p q]` for a fork-free `%next`**, with `q` in `Frag` and `RunOKN`
of `p`: `q`'s need has no forks, so `p` runs for a fork-free goal. -/
theorem runOKN_n7 (lib : Lib) {p q : Nomm} {sur : Sure S} {th : Jmp} (hq : Frag q (CGoal.next sur th))
    (hp : NextOK (S := S) (Map := Map) lib p) {region : List Nat} {g0 g2 : Gen Map} {nex : NextL S}
    (hj : GJ g0.bo (CGoal.next sur th)) (hth : th.args = []) (hok : GoalOK g0 (CGoal.next sur th))
    (hcl : Clean sur.ned) (hcount : sixCount p ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0)
    (h : runL (Nomm.n7 p q) (CGoalL.next (ofSure sur) th) region g0 = some (nex, g2)) :
    RunOKN (Map := Map) lib (Nomm.n7 p q) sur th g0 g2 nex := by
  rw [runL_n7] at h
  obtain ⟨nx, g, h1, h2⟩ := bind_some h
  rw [show (CGoalL.next (ofSure sur) th : CGoalL S) = CGoal.toL (CGoal.next sur th) from rfl, runL_frag hq] at h1
  obtain ⟨⟨n, g'⟩, hr, e⟩ := Option.map_eq_some_iff.mp h1
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have Rq := run_ok lib q _ g0 g' n hq hok hcl hr
  have Dq := run_down (S := S) (Map := Map) q _ g0 g' n hj b0 d0 hr
  have dg : g'.drop = false := Rq.ext.2.2.1.trans d0
  have fa : n.th.args = [] := by
    rcases Dq.entry with ⟨_, _, _, fa⟩ | e
    · exact fa
    · simp only [GoalJ] at e; rw [e]; exact hth
  have hcl' : Clean n.laz.ned := run_clean q (CGoal.next sur th) g0 g' n hcl hr
  have hok' : GoalOK g' (CGoal.next n.laz n.th) := ⟨Rq.dist, fun r hr => by
    rcases Rq.regs r hr with h' | h'
    · exact Nat.lt_of_lt_of_le (hok.2 r h') Rq.ext.1
    · exact h'.2⟩
  have GQ : GrowU g0 g' := Dq.grow.toU hu
  have Rp := hp (sur := n.laz) (th := n.th) (region := region) (g0 := g') (g1 := g2) (nex := nex)
    ⟨Dq.lo, Dq.hi⟩ fa hok' hcl' hcount (Nat.le_trans b0 Dq.grow.bo) dg (GQ.up hu) h2
  have l1 := Rq.ext.1
  have l2 := Rp.ext.1
  refine ⟨Rq.ext.trans Rp.ext, GQ.trans Rp.grow, Rp.cnd.trans ((kc_run q _).keep g0 n g' hr),
    Rp.lo, Rp.hi, ?_, fun r hr => ?_, Rp.dist, fun e he => ?_, fun e he => ?_, Rp.nodup, ?_,
    fun s hs => ?_, ?_⟩
  · rcases Rp.ent with f | e
    · exact Or.inl f
    · simp only [GoalJ] at e
      rw [e]
      rcases Dq.entry with f' | e'
      · exact Or.inl (f'.growU Dq.hi Rp.grow)
      · exact Or.inr e'
  · rcases Rp.regs r hr with h' | h'
    · rcases Rq.regs r h' with h'' | h''
      · exact Or.inl h''
      · exact Or.inr ⟨h''.1, by omega⟩
    · exact Or.inr ⟨by omega, h'.2⟩
  · exact ⟨(Rp.eregs e he).1, fun r hr => by have := (Rp.eregs e he).2 r hr; omega⟩
  · obtain ⟨a, b, c⟩ := Rp.labs e he
    exact ⟨by have := Rq.ext.2.1; omega, b, c⟩
  · simp only [sixCount, sixCount_frag hq]; have := Rp.size; omega
  · rcases Rp.nec s hs with e | ⟨v, e, nf⟩
    · left; simp [pureEval, e]
    · rcases Rq.nec v nf with e' | ⟨w, e', x⟩
      · left; simp [pureEval, e, e']
      · right; exact ⟨w, by simp [pureEval, e, e'], x⟩
  · intro c ned σ O st t gul s0 s ag hned regs hh hn
    have agP : AgreeP lib O c gul st t ned g' g2 nex.laz s0 s :=
      ⟨fun o h0 h1 hnl => ag.1 o (Nat.le_trans Rq.ext.2.1 h0) h1 hnl, ag.2⟩
    have Sp := Rp.sem c ned σ O st t gul s0 s agP hned regs hh hn
    have agQ : Agree c g0 g' := fun o h0 h1 => by
      rw [ag.1 o h0 (Nat.lt_of_lt_of_le h1 Rp.ext.2.1) (fun hm => ?_)]
      · exact Rp.ext.2.2.2 o h1
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
        have := (Rp.labs e he).1; omega
    show GoalSem lib O c gul st _ regs t nex.th (CGoal.next sur th) (pureEval (Nomm.n7 p q) s)
    cases ev : pureEval p s with
    | none =>
      rw [ev] at Sp
      have e7 : pureEval (Nomm.n7 p q) s = none := by simp [pureEval, ev]
      rw [e7]; exact goalSem_none _ Sp
    | some v =>
      rw [ev] at Sp
      have e7 : pureEval (Nomm.n7 p q) s = pureEval q v := by simp [pureEval, ev]
      rw [e7]
      by_cases f : FitsS n.laz v
      · obtain ⟨R, hR, kR, e⟩ := Sp.1 f
        have Sq := Rq.sem d0 c agQ σ O st v R t gul ⟨hR, f.2⟩
        refine goalSem_pre (fun r hr => kR r ⟨?_, ?_⟩) e _ _ (goalSem_mono (fun r hr => ?_) _ _ Sq)
        · rcases hr.1 with h' | h'
          · exact Or.inl (by omega)
          · exact Or.inr h'
        · intro hm
          rcases Rq.regs r hm with h' | h'
          · exact hr.2 h'
          · rcases hr.1 with h'' | h''
            · omega
            · have := hned r h''; omega
        · simp only [Keep, GMem]
          refine ⟨?_, hr.2⟩
          rcases hr.1 with h' | h'
          · exact Or.inl h'
          · have := hned r h'; exact Or.inr (by omega)
      · rcases Rq.nec v f with e' | ⟨w, e', x⟩
        · rw [e']; exact goalSem_none _ (Sp.2 f)
        · rw [e']; exact ⟨fun fw => absurd fw x, fun _ => Sp.2 f⟩

/-! ## `[4 p]`, `[3 p]`, `[7 p q]` under `%done` or `%pick` -/

/-- **A unary case for `%done` or `%pick`**: the code of `p` for the goal
`%next` of the register `a`, into a block `o` that does for the goal what `f`
of `a` asks. -/
theorem unaryG_ok {lib : Lib} {nm p : Nomm} {goal : CGoal S} (hg : NotNext goal) {g0 g' g1 : Gen Map} {a o : Nat}
    {nexp : NextL S} {f : Noun → Option Noun} (hev : ∀ s, pureEval nm s = (pureEval p s).bind f)
    (hpre : Ext g0 g') (hgr : GrowU g0 g') (hcnd : g'.cond = g0.cond) (ha : g0.re ≤ a ∧ a < g'.re)
    (ho : o < g'.bo) (hfr : Fresh g' (jmp0 o)) (hp : RunOKN (Map := Map) lib p (lazyReg a) (jmp0 o) g' g1 nexp)
    (hsz : sixCount nm = sixCount p)
    (hblk : ∀ (c : Straight Map), Agree c g0 g' → ∀ (σ : Type) (O : Oracle σ) st regs t gul x,
      SkaModel.read a regs = some x → GoalSem lib O c gul st (Keep g0 g' goal) regs t (jmp0 o) goal (f x)) :
    RunOKP (Map := Map) lib nm goal g0 g1 nexp := by
  refine ⟨hpre.trans hp.ext, hgr.trans hp.grow, hp.cnd.trans hcnd, hp.lo, hp.hi, ?_, fun r hr => ?_, hp.dist,
    fun e he => ?_, fun e he => ?_, hp.nodup, by rw [hsz]; exact hp.size, fun s hs => ?_, ?_⟩
  · rcases hp.ent with f | e
    · exact Or.inl f
    · simp only [GoalJ] at e
      rw [e]; exact Or.inl (hfr.growU ho hp.grow)
  · have := hp.ext.1; have := hpre.1
    rcases hp.regs r hr with h | h
    · simp only [lazyReg, NMem] at h; subst h; exact ⟨ha.1, by omega⟩
    · exact ⟨by omega, h.2⟩
  · exact ⟨(hp.eregs e he).1, fun r hr => by have := (hp.eregs e he).2 r hr; have := hpre.1; omega⟩
  · obtain ⟨x, y, z⟩ := hp.labs e he
    exact ⟨by have := hpre.2.1; omega, y, z⟩
  · rw [hev]
    rcases hp.nec s hs with h | ⟨x, _, h2⟩
    · rw [h]; rfl
    · exact absurd ⟨trivial, looks_empty x⟩ h2
  · intro c ned σ O st t gul s0 s ag hned regs hh hn
    have agP : AgreeP lib O c gul st t ned g' g1 nexp.laz s0 s :=
      ⟨fun o' h0 h1 hnl => ag.1 o' (Nat.le_trans hpre.2.1 h0) h1 hnl, ag.2⟩
    have Sp := hp.sem c ned σ O st t gul s0 s agP hned regs hh hn
    have agQ : Agree c g0 g' := fun o' h0 h1 => by
      rw [ag.1 o' h0 (Nat.lt_of_lt_of_le h1 hp.ext.2.1) (fun hm => ?_)]
      · exact hp.ext.2.2.2 o' h1
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
        have := (hp.labs e he).1; omega
    have l1 := hp.ext.1
    rw [hev]
    cases e : pureEval p s with
    | none => rw [e] at Sp; exact goalSem_none _ Sp
    | some x =>
      rw [e] at Sp
      obtain ⟨R, hR, k, he⟩ := Sp.1 ⟨trivial, looks_empty x⟩
      refine goalSem_pre (fun r hr => k r ⟨?_, ?_⟩) he _ _
        (goalSem_mono (fun r hr => ?_) _ _ (hblk c agQ σ O st R t gul x hR))
      · rcases hr with h | h
        · exact Or.inl (by omega)
        · exact Or.inr h
      · simp only [lazyReg, NMem]
        intro ea; subst ea
        rcases hr with h | h
        · omega
        · have := hned _ h; omega
      · refine ⟨?_, notNext_gmem hg r⟩
        rcases hr with h | h
        · exact Or.inl h
        · have := hned r h; exact Or.inr (by omega)

/-- **`[4 p]` for `%pick`**, from `RunOKN` of `p`. -/
theorem runOKP_n4p (lib : Lib) {p : Nomm} (hp : NextOK (S := S) (Map := Map) lib p) {z o : Jmp} {region : List Nat}
    {g0 g1 : Gen Map} {nex : NextL S} (hj : GJ g0.bo (CGoal.pick z o : CGoal S)) (hcount : sixCount p ≤ 255)
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0)
    (h : runL (Nomm.n4 p) (CGoal.toL (CGoal.pick z o : CGoal S)) region g0 = some (nex, g1)) :
    RunOKP (Map := Map) lib (Nomm.n4 p) (CGoal.pick z o) g0 g1 nex := by
  have e4 : (runL (Nomm.n4 p) (CGoal.toL (CGoal.pick z o : CGoal S)) region : CM Map (NextL S)) = (do
      let pro ← re
      let arg ← re
      let o' ← emit ⟨[], [Pole.inc arg pro], Termin.brn pro z o⟩
      runL p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o')) region) := by
    conv => lhs; unfold runL
    rfl
  rw [e4] at h
  simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
  have G := (grow_reg g0 (g0.re + 1 + 1)).trans (grow_emit (b := ⟨[], [Pole.inc (g0.re + 1) g0.re],
    Termin.brn g0.re z o⟩) (jumpsBelow_two rfl hj.1 hj.2))
  have Rp := hp ⟨by simp only [jmp0]; omega, by simp only [jmp0, emitted_bo]; omega⟩ rfl
    (by exact ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; simp [emitted_re]⟩) (by exact trivial)
    hcount (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d0) ((G.toU hu).up hu) h
  refine unaryG_ok (goal := CGoal.pick z o) trivial (pureEval_n4 p)
    ((ext_re _).trans ((ext_re _).trans (ext_emit _ _))) (G.toU hu) rfl
    ⟨Nat.le_succ _, by simp [emitted_re]⟩ (by simp [emitted_bo]) (fresh_emitted (by simpa using d0) rfl rfl) Rp rfl ?_
  intro c hc σ O st regs t gul x hx
  have hb := emitted_get' (by simpa using d0) (hc _ (by simp) (by simp [emitted_bo]))
  have hj' := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
  cases x with
  | atom n =>
    rw [show [Pole.inc _ _] = [Pole.inc _ _] ++ [] from rfl, runs_inc hx, execBlob_brn, read_store_eq,
      Option.bind_some] at hj'
    rcases n with _ | n
    · simp only [incF]
      refine ⟨store g0.re (A (0 + 1)) regs, fun r ⟨h1, _⟩ =>
        read_store_ne (show r ≠ g0.re by simp [emitted_re] at h1; omega) _ _, ?_⟩
      rw [hj']; simp
    · simp only [incF]
      exact goalSem_pick_other (by simp) (by simp) (by rw [hj']; simp)
  | cell u v =>
    simp only [incF]
    apply goalSem_crash
    rw [hj', show [Pole.inc _ _] = [Pole.inc _ _] ++ [] from rfl, crashes_inc hx]

/-- **`[3 p]` for `%pick`**, from `RunOKN` of `p`. -/
theorem runOKP_n3p (lib : Lib) {p : Nomm} (hp : NextOK (S := S) (Map := Map) lib p) {z o : Jmp} {region : List Nat}
    {g0 g1 : Gen Map} {nex : NextL S} (hj : GJ g0.bo (CGoal.pick z o : CGoal S)) (hcount : sixCount p ≤ 255)
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0)
    (h : runL (Nomm.n3 p) (CGoal.toL (CGoal.pick z o : CGoal S)) region g0 = some (nex, g1)) :
    RunOKP (Map := Map) lib (Nomm.n3 p) (CGoal.pick z o) g0 g1 nex := by
  have e3 : (runL (Nomm.n3 p) (CGoal.toL (CGoal.pick z o : CGoal S)) region : CM Map (NextL S)) = (do
      let r ← re
      let oc ← emit ⟨[], [], Termin.clq r z o⟩
      runL p (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region) := by
    conv => lhs; unfold runL
    rfl
  rw [e3] at h
  simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
  have G := (grow_re g0).trans (grow_emit (b := ⟨[], [], Termin.clq g0.re z o⟩) (jumpsBelow_two rfl hj.1 hj.2))
  have Rp := hp ⟨by simp only [jmp0]; omega, by simp only [jmp0, emitted_bo]; omega⟩ rfl
    (by exact ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; simp [emitted_re]⟩) (by exact trivial)
    hcount (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d0) ((G.toU hu).up hu) h
  refine unaryG_ok (goal := CGoal.pick z o) trivial (pureEval_n3 p) ((ext_re _).trans (ext_emit _ _)) (G.toU hu)
    rfl ⟨Nat.le_refl _, by simp [emitted_re]⟩ (by simp [emitted_bo]) (fresh_emitted (by simpa using d0) rfl rfl)
    Rp rfl ?_
  intro c hc σ O st regs t gul x hx
  have hb := emitted_get' (by simpa using d0) (hc _ (by simp) (by simp [emitted_bo]))
  have hj' := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
  rw [execBlob_clq, hx, Option.bind_some] at hj'
  cases x with
  | atom n => exact ⟨regs, fun _ _ => rfl, by rw [hj']⟩
  | cell u v => exact ⟨regs, fun _ _ => rfl, by rw [hj']⟩

/-- **`[7 p q]` for `%done` or `%pick`**, with `q` in `Frag` and `RunOKN` of
`p`, when the goal's jumps pass no arguments. -/
theorem runOKP_n7g (lib : Lib) {p q : Nomm} {goal : CGoal S} (hg : NotNext goal) (hq : Frag q goal)
    (hp : NextOK (S := S) (Map := Map) lib p) (hargs : ∀ j, GoalJ goal j → j.args = []) {region : List Nat}
    {g0 g2 : Gen Map} {nex : NextL S} (hj : GJ g0.bo goal) (hcount : sixCount p ≤ 255) (b0 : 1 ≤ g0.bo)
    (d0 : g0.drop = false) (hu : UpBelow g0) (h : runL (Nomm.n7 p q) (CGoal.toL goal) region g0 = some (nex, g2)) :
    RunOKP (Map := Map) lib (Nomm.n7 p q) goal g0 g2 nex := by
  rw [runL_n7] at h
  obtain ⟨nx, g, h1, h2⟩ := bind_some h
  rw [runL_frag hq] at h1
  obtain ⟨⟨n, g'⟩, hr, e⟩ := Option.map_eq_some_iff.mp h1
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have hok : GoalOK g0 goal := by cases goal with | next => exact hg.elim | _ => trivial
  have hcl : GClean goal := by cases goal with | next => exact hg.elim | _ => trivial
  have Rq := run_ok lib q goal g0 g' n hq hok hcl hr
  have Dq := run_down (S := S) (Map := Map) q goal g0 g' n hj b0 d0 hr
  have dg : g'.drop = false := Rq.ext.2.2.1.trans d0
  have fa : n.th.args = [] := by
    rcases Dq.entry with ⟨_, _, _, fa⟩ | e
    · exact fa
    · exact hargs _ e
  have hcl' : Clean n.laz.ned := run_clean q goal g0 g' n hcl hr
  have hok' : GoalOK g' (CGoal.next n.laz n.th) := ⟨Rq.dist, fun r hr => by
    rcases Rq.regs r hr with h' | h'
    · exact (notNext_gmem hg r h').elim
    · exact h'.2⟩
  have GQ : GrowU g0 g' := Dq.grow.toU hu
  have Rp := hp (sur := n.laz) (th := n.th) (region := region) (g0 := g') (g1 := g2) (nex := nex)
    ⟨Dq.lo, Dq.hi⟩ fa hok' hcl' hcount (Nat.le_trans b0 Dq.grow.bo) dg (GQ.up hu) h2
  have l1 := Rq.ext.1
  have l2 := Rp.ext.1
  refine ⟨Rq.ext.trans Rp.ext, GQ.trans Rp.grow, Rp.cnd.trans ((kc_run q goal).keep g0 n g' hr),
    Rp.lo, Rp.hi, ?_, fun r hr => ?_, Rp.dist, fun e he => ?_, fun e he => ?_, Rp.nodup, ?_,
    fun s hs => ?_, ?_⟩
  · rcases Rp.ent with f | e
    · exact Or.inl f
    · simp only [GoalJ] at e
      rw [e]
      rcases Dq.entry with f' | e'
      · exact Or.inl (f'.growU Dq.hi Rp.grow)
      · exact Or.inr e'
  · rcases Rp.regs r hr with h' | h'
    · rcases Rq.regs r h' with h'' | h''
      · exact (notNext_gmem hg r h'').elim
      · exact ⟨h''.1, by omega⟩
    · exact ⟨by omega, h'.2⟩
  · exact ⟨(Rp.eregs e he).1, fun r hr => by have := (Rp.eregs e he).2 r hr; omega⟩
  · obtain ⟨a, b, c⟩ := Rp.labs e he
    exact ⟨by have := Rq.ext.2.1; omega, b, c⟩
  · simp only [sixCount, sixCount_frag hq]; have := Rp.size; omega
  · rcases Rp.nec s hs with e | ⟨v, e, nf⟩
    · simp [pureEval, e]
    · rcases Rq.nec v nf with e' | ⟨w, _, x⟩
      · simp [pureEval, e, e']
      · exact (notNext_gnot hg w x).elim
  · intro c ned σ O st t gul s0 s ag hned regs hh hn
    have agP : AgreeP lib O c gul st t ned g' g2 nex.laz s0 s :=
      ⟨fun o h0 h1 hnl => ag.1 o (Nat.le_trans Rq.ext.2.1 h0) h1 hnl, ag.2⟩
    have Sp := Rp.sem c ned σ O st t gul s0 s agP hned regs hh hn
    have agQ : Agree c g0 g' := fun o h0 h1 => by
      rw [ag.1 o h0 (Nat.lt_of_lt_of_le h1 Rp.ext.2.1) (fun hm => ?_)]
      · exact Rp.ext.2.2.2 o h1
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
        have := (Rp.labs e he).1; omega
    show GoalSem lib O c gul st _ regs t nex.th goal (pureEval (Nomm.n7 p q) s)
    cases ev : pureEval p s with
    | none =>
      rw [ev] at Sp
      have e7 : pureEval (Nomm.n7 p q) s = none := by simp [pureEval, ev]
      rw [e7]; exact goalSem_none _ Sp
    | some v =>
      rw [ev] at Sp
      have e7 : pureEval (Nomm.n7 p q) s = pureEval q v := by simp [pureEval, ev]
      rw [e7]
      by_cases f : FitsS n.laz v
      · obtain ⟨R, hR, kR, e⟩ := Sp.1 f
        have Sq := Rq.sem d0 c agQ σ O st v R t gul ⟨hR, f.2⟩
        refine goalSem_pre (fun r hr => kR r ⟨?_, ?_⟩) e _ _ (goalSem_mono (fun r hr => ?_) _ _ Sq)
        · rcases hr with h' | h'
          · exact Or.inl (by omega)
          · exact Or.inr h'
        · intro hm
          rcases Rq.regs r hm with h' | h'
          · exact notNext_gmem hg r h'
          · rcases hr with h'' | h''
            · omega
            · have := hned r h''; omega
        · refine ⟨?_, notNext_gmem hg r⟩
          rcases hr with h' | h'
          · exact Or.inl h'
          · have := hned r h'; exact Or.inr (by omega)
      · rcases Rq.nec v f with e' | ⟨w, _, x⟩
        · rw [e']; exact goalSem_none _ (Sp.2 f)
        · exact (notNext_gnot hg w x).elim

/-! ## The fragment -/

/-- **The fragment with `%3`, `%4`, `%7` and `%6` nested in any order**: the
nomms of `Frag` (for every goal), `[6 c a b]` with a test and branches in
`FragM`, `[4 p]` and `[3 p]` with `p` in `FragM`, and `[7 p q]` with `q` in
`Frag` and `p` in `FragM`. -/
inductive FragM : Nomm → Prop
  | frag {nm : Nomm} : (∀ goal : CGoal S, Frag nm goal) → FragM nm
  | six {c a b : Nomm} : FragM c → FragM a → FragM b → FragM (Nomm.n6 c a b)
  | four {p : Nomm} : FragM p → FragM (Nomm.n4 p)
  | three {p : Nomm} : FragM p → FragM (Nomm.n3 p)
  | seven {p q : Nomm} : (∀ goal : CGoal S, Frag q goal) → FragM p → FragM (Nomm.n7 p q)

theorem fragM_pure {nm : Nomm} (h : FragM (S := S) nm) : nm.pure = true := by
  induction h with
  | frag hf => exact (frag_pure_noSix _ _ (hf CGoal.done)).1
  | six _ _ _ ihc iha ihb => simp only [Nomm.pure, ihc, iha, ihb, Bool.and_self]
  | four _ ih => simpa only [Nomm.pure] using ih
  | three _ ih => simpa only [Nomm.pure] using ih
  | seven hq _ ih => simp only [Nomm.pure, ih, (frag_pure_noSix _ _ (hq CGoal.done)).1, Bool.and_self]

/-- **`runL` meets the relations on `FragM`**: `RunOKP` for `%done`,
`RunOKN` for every fork-free goal `%next` whose jump has no arguments, and
`RunOKP` for every `%pick` whose jumps have no arguments, when the nomm has
at most 255 `%6`. -/
theorem runM_ok (lib : Lib) {nm : Nomm} (hf : FragM (S := S) nm) :
    OKP (Map := Map) lib (CGoal.done : CGoal S) nm ∧ NextOK (S := S) (Map := Map) lib nm ∧
    ∀ z o : Jmp, z.args = [] → o.args = [] → OKP (Map := Map) lib (CGoal.pick z o : CGoal S) nm := by
  induction hf with
  | frag hf =>
    exact ⟨fun hg hj _ b0 d0 hu h => runOKP_frag lib (hf _) hg hj b0 d0 hu h,
      fun hj _ hok hcl _ b0 d0 hu h => runOKN_frag lib (hf _) hj b0 d0 hu hok hcl h,
      fun _ _ _ _ _ _ _ _ hg hj _ b0 d0 hu h => runOKP_frag lib (hf _) hg hj b0 d0 hu h⟩
  | @six c a b hc _ _ ihc iha ihb =>
    have hcp := fragM_pure hc
    exact ⟨sixP_ok lib hcp ihc.2.2 iha.1 ihb.1,
      fun hj hth hok hcl hcount b0 d0 hu h => sixNext_okN lib hcp
        (fun z o hz ho => ihc.2.2 z o hz ho trivial) iha.2.1 ihb.2.1 hj hth hok hcl hcount b0 d0 hu h,
      fun z o hz ho => sixP_ok lib hcp ihc.2.2 (iha.2.2 z o hz ho) (ihb.2.2 z o hz ho)⟩
  | four _ ih =>
    exact ⟨fun _ _ hcount b0 d0 hu h => runOKP_n4 lib ih.2.1 (by simpa only [sixCount] using hcount) b0 d0 hu h,
      fun hj _ _ _ hcount b0 d0 hu h => runOKN_n4 lib ih.2.1 hj (by simpa only [sixCount] using hcount) b0 d0 hu h,
      fun _ _ _ _ _ _ _ _ _ hj hcount b0 d0 hu h =>
        runOKP_n4p lib ih.2.1 hj (by simpa only [sixCount] using hcount) b0 d0 hu h⟩
  | three _ ih =>
    exact ⟨fun _ _ hcount b0 d0 hu h => runOKP_n3 lib ih.2.1 (by simpa only [sixCount] using hcount) b0 d0 hu h,
      fun hj hth hok hcl hcount b0 d0 hu h =>
        runOKN_n3 lib ih.2.1 hj hth hok hcl (by simpa only [sixCount] using hcount) b0 d0 hu h,
      fun _ _ _ _ _ _ _ _ _ hj hcount b0 d0 hu h =>
        runOKP_n3p lib ih.2.1 hj (by simpa only [sixCount] using hcount) b0 d0 hu h⟩
  | seven hq _ ih =>
    exact ⟨fun _ _ hcount b0 d0 hu h => runOKP_n7 lib (hq _) ih.2.1 (by simp only [sixCount] at hcount; omega)
        b0 d0 hu h,
      fun hj hth hok hcl hcount b0 d0 hu h => runOKN_n7 lib (hq _) ih.2.1 hj hth hok hcl
        (by simp only [sixCount] at hcount; omega) b0 d0 hu h,
      fun z o hz ho _ _ _ _ hg hj hcount b0 d0 hu h => runOKP_n7g lib hg (hq _) ih.2.1
        (fun j e => by simp only [GoalJ] at e; rcases e with rfl | rfl <;> assumption) hj
        (by simp only [sixCount] at hcount; omega) b0 d0 hu h⟩

/-- The example of the header: `[4 [6 [0 2] [3 [6 [0 6] [1 1] [0 7]]] [4 [0 3]]]]`
is in `FragM`. -/
example : FragM (S := S) (Nomm.n4 (Nomm.n6 (Nomm.n0 2) (Nomm.n3 (Nomm.n6 (Nomm.n0 6) (Nomm.n1 (A 1)) (Nomm.n0 7)))
    (Nomm.n4 (Nomm.n0 3)))) :=
  FragM.four (FragM.six (FragM.frag fun _ => trivial)
    (FragM.three (FragM.six (FragM.frag fun _ => trivial) (FragM.frag fun _ => trivial) (FragM.frag fun _ => trivial)))
    (FragM.frag fun goal => by cases goal <;> exact fun _ _ => trivial))

/-- A test that is an increment of a `%6`: `[6 [4 [6 [0 2] [1 0] [1 1]]] [0 2] [0 3]]`. -/
example : FragM (S := S) (Nomm.n6 (Nomm.n4 (Nomm.n6 (Nomm.n0 2) (Nomm.n1 (A 0)) (Nomm.n1 (A 1)))) (Nomm.n0 2)
    (Nomm.n0 3)) :=
  FragM.six (FragM.four (FragM.six (FragM.frag fun _ => trivial) (FragM.frag fun _ => trivial)
    (FragM.frag fun _ => trivial))) (FragM.frag fun _ => trivial) (FragM.frag fun _ => trivial)

/-- **The final pass meets the contract on `FragM`**, when the nomm has at
most 255 `%6`, nothing is baked and the bell's cape has no `[| |]`. -/
theorem finishLF_bellContractM {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {bl : Bell} {nm : Nomm} (hp : nm.pure = true) (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol nm)
    (hf : FragM (S := S) nm) (hcount : sixCount nm ≤ 255) {cape : Cape} {data : Noun}
    (hbl : bl.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) nm ord cape bake = some c') (N : Needs) : BellContract lib N bl false c' :=
  finishLF_bellContractR hok hp hA
    (fun h1 => (runM_ok lib hf).1 trivial trivial hcount (by simp [gen0]) rfl upBelow_gen0 h1) hbl hn hbake h N

/-- **The compiled code of a nomm of `FragM` crashes exactly when the nomm
does**, on every subject that has the axes the cape says it has. -/
theorem crash_iffM (lib : Lib) {nm : Nomm} (hf : FragM (S := S) nm) (hcount : sixCount nm ≤ 255)
    {ord : NeedOrd} {less : Cape} {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, []))
    {c' : Straight Map} (h : finishLF (S := S) nm ord less bake = some c') {σ : Type} (O : Oracle σ) (st : σ)
    (s : Noun) (args : List Noun) (t : Trace) (gul : Noun) (hP : CapeAxes less s)
    (hsp : SkaModel.split c'.need s = some args) :
    (execEntry lib O st c' args t gul = some (Tone.two t, st) ↔ pureEval nm s = none) ∧
    ∀ v, execEntry lib O st c' args t gul = some (Tone.zero v, st) ↔ pureEval nm s = some v :=
  crash_iffR lib (fun h1 => (runM_ok lib hf).1 trivial trivial hcount (by simp [gen0]) rfl upBelow_gen0 h1)
    hbake h O st s args t gul hP hsp

end Comp
end SkaModel
end Formalization
