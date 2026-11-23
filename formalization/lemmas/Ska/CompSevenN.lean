import lemmas.Ska.CompSixNextOK
import lemmas.Ska.CompNestFinalP

/-!
# `[7 p q]` under `%done` with `%6` in `p`

`runOKP_n7`: when `q` is in `Frag` for `%done` and `p` in `FragN`, the run
of `[7 p q]` for `%done` meets `RunOKP`.  `q`'s run returns a fork-free need
and a jump to a fresh block that takes no arguments (`Fresh`), so `p` runs
for a fork-free goal `%next` whose jump has no arguments, which is what
`runN_ok` asks.  The blocks of `p` may hop up (the fork blocks of its
`%6`), so the relation grows by `GrowU`.

`runOKP_n4`: `[4 p]` for `%done` with `p` in `FragN`, through `unaryP_ok`,
which a `[3 p]` for `%done` can use too.

`FragT`: the nomms of `FragP` for `%done`, `[7 p q]` with `q` in `Frag`
and `p` in `FragN`, and `[4 p]` with `p` in `FragN`.  `finishLF_bellContractT` and `crash_iffT`: the top
theorems on `FragT`.  For example `[7 [6 [0 2] [6 [0 3] [1 1] [1 2]] [0 3]]
[4 [0 1]]]`, a test whose yes branch is again a `%6`, under an increment.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

theorem Fresh.growU {g g' : Gen Map} {j : Jmp} (h : Fresh g j) (hl : j.there < g.bo) (hg : GrowU g g') :
    Fresh g' j := by
  obtain ⟨b, hb, hp, ha⟩ := h
  obtain ⟨b', hb', hp', _⟩ := hg.keep _ b hl hb
  exact ⟨b', hb', hp'.trans hp, ha⟩

theorem runL_n7 (p q : Nomm) (goal : CGoalL S) (region : List Nat) :
    (runL (Nomm.n7 p q) goal region : CM Map (NextL S)) =
      (runL q goal region >>= fun nx => runL p nx.goal region) := by
  cases goal
  all_goals (conv => lhs; unfold runL)

/-- **`[7 p q]` for `%done`**, from `RunOK` of `q` and `RunOKN` of `p`. -/
theorem runOKP_n7 (lib : Lib) {p q : Nomm} (hq : Frag q (CGoal.done : CGoal S)) (hp : FragN (S := S) p)
    {region : List Nat} {g0 g2 : Gen Map} {nex : NextL S} (hcount : sixCount p ≤ 255) (b0 : 1 ≤ g0.bo)
    (d0 : g0.drop = false) (hu : UpBelow g0)
    (h : runL (Nomm.n7 p q) (CGoal.toL (CGoal.done : CGoal S)) region g0 = some (nex, g2)) :
    RunOKP (Map := Map) lib (Nomm.n7 p q) CGoal.done g0 g2 nex := by
  rw [runL_n7] at h
  obtain ⟨nx, g, h1, h2⟩ := bind_some h
  rw [runL_frag hq] at h1
  obtain ⟨⟨n, g'⟩, hr, e⟩ := Option.map_eq_some_iff.mp h1
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have Rq := run_ok lib q CGoal.done g0 g' n hq trivial trivial hr
  have Dq := run_down (S := S) (Map := Map) q CGoal.done g0 g' n trivial b0 d0 hr
  have dg : g'.drop = false := Rq.ext.2.2.1.trans d0
  have fr : Fresh g' n.th := Dq.entry.elim id False.elim
  have fa : n.th.args = [] := by obtain ⟨_, _, _, fa⟩ := fr; exact fa
  have hcl : Clean n.laz.ned := run_clean q CGoal.done g0 g' n trivial hr
  have hok : GoalOK g' (CGoal.next n.laz n.th) := ⟨Rq.dist, fun r hr => by
    rcases Rq.regs r hr with h' | h'
    · exact h'.elim
    · exact h'.2⟩
  have GQ : GrowU g0 g' := Dq.grow.toU hu
  have Rp := runN_ok lib hp (sur := n.laz) (th := n.th) (region := region) (g0 := g') (g1 := g2) (nex := nex)
    ⟨Dq.lo, Dq.hi⟩ fa hok hcl hcount (Nat.le_trans b0 Dq.grow.bo) dg (GQ.up hu) h2
  refine ⟨Rq.ext.trans Rp.ext, GQ.trans Rp.grow, Rp.cnd.trans ((kc_run q CGoal.done).keep g0 n g' hr),
    Rp.lo, Rp.hi, ?_, fun r hr => ?_, Rp.dist, fun e he => ?_, fun e he => ?_, Rp.nodup, ?_,
    fun s hs => ?_, ?_⟩
  · rcases Rp.ent with f | e
    · exact Or.inl f
    · simp only [GoalJ] at e
      rw [e]; exact Or.inl (fr.growU Dq.hi Rp.grow)
  · have := Rp.ext.1; have := Rq.ext.1
    rcases Rp.regs r hr with h' | h'
    · rcases Rq.regs r h' with h'' | h''
      · exact h''.elim
      · exact ⟨h''.1, by omega⟩
    · exact ⟨by omega, h'.2⟩
  · exact ⟨(Rp.eregs e he).1, fun r hr => by have := (Rp.eregs e he).2 r hr; have := Rq.ext.1; omega⟩
  · obtain ⟨a, b, c⟩ := Rp.labs e he
    exact ⟨by have := Rq.ext.2.1; omega, b, c⟩
  · simp only [sixCount]; have := Rp.size; omega
  · rcases Rp.nec s hs with e | ⟨v, e, nf⟩
    · simp [pureEval, e]
    · rcases Rq.nec v nf with e' | ⟨w, _, x⟩
      · simp [pureEval, e, e']
      · exact x.elim
  · intro c ned σ O st t gul s0 s ag hned regs hh hn
    have agP : AgreeP lib O c gul st t ned g' g2 nex.laz s0 s :=
      ⟨fun o h0 h1 hnl => ag.1 o (Nat.le_trans Rq.ext.2.1 h0) h1 hnl, ag.2⟩
    have Sp := Rp.sem c ned σ O st t gul s0 s agP hned regs hh hn
    have agQ : Agree c g0 g' := fun o h0 h1 => by
      rw [ag.1 o h0 (Nat.lt_of_lt_of_le h1 Rp.ext.2.1) (fun hm => ?_)]
      · exact Rp.ext.2.2.2 o h1
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
        have := (Rp.labs e he).1; omega
    show goJ lib O c gul st regs t nex.th = some (toneOf t (pureEval (Nomm.n7 p q) s), st)
    cases ev : pureEval p s with
    | none =>
      rw [ev] at Sp
      have e7 : pureEval (Nomm.n7 p q) s = none := by simp [pureEval, ev]
      rw [e7]; exact Sp
    | some v =>
      rw [ev] at Sp
      have e7 : pureEval (Nomm.n7 p q) s = pureEval q v := by simp [pureEval, ev]
      rw [e7]
      by_cases f : FitsS n.laz v
      · obtain ⟨R, hR, _, e⟩ := Sp.1 f
        exact e.trans (Rq.sem d0 c agQ σ O st v R t gul ⟨hR, f.2⟩)
      · rcases Rq.nec v f with e' | ⟨w, _, x⟩
        · rw [e']; exact Sp.2 f
        · exact x.elim

/-! ## `[4 p]` under `%done` -/

/-- **A unary case for `%done`**: the code of `p` for the goal `%next` of the
register `a`, into a block `o` that does `f` to what `a` holds. -/
theorem unaryP_ok {lib : Lib} {nm p : Nomm} {g0 g' g1 : Gen Map} {a o : Nat} {nexp : NextL S}
    {f : Noun → Option Noun} (hev : ∀ s, pureEval nm s = (pureEval p s).bind f) (hpre : Ext g0 g')
    (hgr : GrowU g0 g') (hcnd : g'.cond = g0.cond) (ha : g0.re ≤ a ∧ a < g'.re) (ho : o < g'.bo)
    (hfr : Fresh g' (jmp0 o)) (hp : RunOKN (Map := Map) lib p (lazyReg a) (jmp0 o) g' g1 nexp)
    (hsz : sixCount nm = sixCount p)
    (hblk : ∀ (c : Straight Map), Agree c g0 g' → ∀ (σ : Type) (O : Oracle σ) st regs t gul x,
      SkaModel.read a regs = some x → goJ lib O c gul st regs t (jmp0 o) = some (toneOf t (f x), st)) :
    RunOKP (Map := Map) lib nm CGoal.done g0 g1 nexp := by
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
    show goJ lib O c gul st regs t nexp.th = some (toneOf t (pureEval nm s), st)
    rw [hev]
    cases e : pureEval p s with
    | none => rw [e] at Sp; exact Sp
    | some x =>
      rw [e] at Sp
      obtain ⟨R, hR, _, he⟩ := Sp.1 ⟨trivial, looks_empty x⟩
      exact he.trans (hblk c agQ σ O st R t gul x hR)

/-- **`[4 p]` for `%done`**, with `p` in `FragN`. -/
theorem runOKP_n4 (lib : Lib) {p : Nomm} (hp : FragN (S := S) p) {region : List Nat} {g0 g1 : Gen Map}
    {nex : NextL S} (hcount : sixCount p ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0)
    (h : runL (Nomm.n4 p) (CGoal.toL (CGoal.done : CGoal S)) region g0 = some (nex, g1)) :
    RunOKP (Map := Map) lib (Nomm.n4 p) CGoal.done g0 g1 nex := by
  have e4 : (runL (Nomm.n4 p) (CGoal.toL (CGoal.done : CGoal S)) region : CM Map (NextL S)) = (do
      let pro ← re
      let arg ← re
      let o ← emit ⟨[], [Pole.inc arg pro], Termin.don pro⟩
      runL p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region) := by
    conv => lhs; unfold runL
    rfl
  rw [e4] at h
  simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
  have Rp := runN_ok (Map := Map) lib hp ⟨by simp only [jmp0]; omega, by simp only [jmp0, emitted_bo]; omega⟩ rfl
    (by exact ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; simp [emitted_re]⟩) (by exact trivial)
    hcount
    (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d0)
    (((grow_reg g0 _).trans (grow_emit (jumpsBelow_nil rfl _))).toU hu |>.up hu) h
  refine unaryP_ok (pureEval_n4 p) ((ext_re _).trans ((ext_re _).trans (ext_emit _ _)))
    (((grow_reg g0 _).trans (grow_emit (jumpsBelow_nil rfl _))).toU hu) rfl
    ⟨Nat.le_succ _, by simp [emitted_re]⟩ (by simp [emitted_bo]) (fresh_emitted (by simpa using d0) rfl rfl) Rp rfl ?_
  intro c hc σ O st regs t gul x hx
  have hb := emitted_get' (by simpa using d0) (hc _ (by simp) (by simp [emitted_bo]))
  rw [goJ_jmp0 _ _ _ _ hb]
  cases x with
  | atom n =>
    rw [show [Pole.inc _ _] = [Pole.inc _ _] ++ [] from rfl, runs_inc hx]
    simp [incF, toneOf, execBlob_don', read_store_eq]
  | cell u v =>
    rw [show [Pole.inc _ _] = [Pole.inc _ _] ++ [] from rfl, crashes_inc hx]
    rfl

/-! ## The fragment of the top theorems -/

/-- **The fragment of the top theorems**: `FragP` for `%done`, `[7 p q]`
with `q` in `Frag` for `%done` and `p` in `FragN`, and `[4 p]` with `p` in
`FragN`. -/
inductive FragT : Nomm → Prop
  | nest {nm : Nomm} : FragP (S := S) CGoal.done nm → FragT nm
  | seven {p q : Nomm} : Frag q (CGoal.done : CGoal S) → FragN (S := S) p → FragT (Nomm.n7 p q)
  | four {p : Nomm} : FragN (S := S) p → FragT (Nomm.n4 p)

/-- **The run for `%done` from `gen0` meets `RunOKP` on `FragT`.** -/
theorem runT_ok (lib : Lib) {nm : Nomm} (hf : FragT (S := S) nm) (hcount : sixCount nm ≤ 255)
    {nex : NextL S} {g4 : Gen Map} (h : runL nm (CGoalL.done : CGoalL S) [] (gen0 : Gen Map) = some (nex, g4)) :
    RunOKP (Map := Map) lib nm CGoal.done gen0 g4 nex := by
  cases hf with
  | nest hf => exact runP_ok lib hf trivial trivial hcount (by simp [gen0]) rfl upBelow_gen0 h
  | seven hq hp =>
    exact runOKP_n7 lib hq hp (by simp only [sixCount] at hcount; omega) (by simp [gen0]) rfl upBelow_gen0 h
  | four hp =>
    exact runOKP_n4 lib hp (by simp only [sixCount] at hcount; omega) (by simp [gen0]) rfl upBelow_gen0 h

/-- **The final pass meets the contract on `FragT`**, when the nomm has at
most 255 `%6`, nothing is baked and the bell's cape has no `[| |]`. -/
theorem finishLF_bellContractT {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code)
    {bl : Bell} {nm : Nomm} (hp : nm.pure = true) (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol nm)
    (hf : FragT (S := S) nm) (hcount : sixCount nm ≤ 255) {cape : Cape} {data : Noun}
    (hbl : bl.less = Sock.mk cape data) (hn : CapeNorm cape) {ord : NeedOrd}
    {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, [])) {c' : Straight Map}
    (h : finishLF (S := S) nm ord cape bake = some c') (N : Needs) : BellContract lib N bl false c' :=
  finishLF_bellContractR hok hp hA (fun h1 => runT_ok lib hf hcount h1) hbl hn hbake h N

/-- **The compiled code of a nomm of `FragT` crashes exactly when the nomm
does**, on every subject that has the axes the cape says it has. -/
theorem crash_iffT (lib : Lib) {nm : Nomm} (hf : FragT (S := S) nm) (hcount : sixCount nm ≤ 255)
    {ord : NeedOrd} {less : Cape} {bake : Need → Need × List (Nat × Noun)} (hbake : ∀ ned, bake ned = (ned, []))
    {c' : Straight Map} (h : finishLF (S := S) nm ord less bake = some c') {σ : Type} (O : Oracle σ) (st : σ)
    (s : Noun) (args : List Noun) (t : Trace) (gul : Noun) (hP : CapeAxes less s)
    (hsp : SkaModel.split c'.need s = some args) :
    (execEntry lib O st c' args t gul = some (Tone.two t, st) ↔ pureEval nm s = none) ∧
    ∀ v, execEntry lib O st c' args t gul = some (Tone.zero v, st) ↔ pureEval nm s = some v :=
  crash_iffR lib (fun h1 => runT_ok lib hf hcount h1) hbake h O st s args t gul hP hsp

end Comp
end SkaModel
end Formalization
