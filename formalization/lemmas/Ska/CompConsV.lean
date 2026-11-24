import lemmas.Ska.CompConsNV

/-!
# Cons with proxy runs for `%done` and `%pick`

README Gaps 12.2 (eighth session).

* `clean_n4L`, `cleanA_seven4`: `[4 p]` runs `p` for one fresh register
  under every goal, entries or not, so the sure need of `[7 [4 p] q]` is that
  of `p`'s run for a clean need, for every `q` (`CleanA` of `[7 [4 p] q]`
  from `CleanA` of `p`).
* `unaryGV_ok`: `unaryG_ok` with a `RunOKNV` operand, giving `RunOKV`; the
  blocks before the operand's run are left alone by unproxying by
  hypothesis (`hfix`).
* `runOKV_consD`: cons for `%done` with `OKNV` parts (`runOKP_consD`).
* `SemGV`, `RunOKGV`: `RunOKNV` for any goal; `RunOKGV.toNV`,
  `RunOKGV.toV`.  `binaryGV_ok`: `binaryNV_ok` for any goal.
* `runOKV_consP`: cons for `%pick` with `OKNV` parts (`runOKP_consP`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Clean needs of `[7 [4 p] q]` -/

/-- **`[4 p]` under any `%next` returns the sure need of `p`'s run for one
fresh register**, so it is clean when `p`'s runs for clean needs are. -/
theorem clean_n4L {p : Nomm} (cp : CleanA S Map p) {laz : Lazy S} {th : Jmp} {region : List Nat}
    {g0 g1 : Gen Map} {nex : NextL S} (h : runL (Nomm.n4 p) (CGoalL.next laz th) region g0 = some (nex, g1)) :
    Clean nex.laz.sure.ned := by
  unfold runL at h
  obtain ⟨_, _, _, h⟩ := bind_some h
  obtain ⟨_, _, _, h⟩ := bind_some h
  obtain ⟨arg, _, _, h⟩ := bind_some h
  obtain ⟨o, _, _, h⟩ := bind_some h
  exact cp (goal := CGoal.next (lazyReg arg) (jmp0 o)) trivial h

/-- **`CleanA` of `[7 [4 p] q]` from `CleanA` of `p`**, for every `q`: the
run of `[4 p]` for the goal `q`'s run returns (with entries or not) runs `p`
for one fresh register. -/
theorem cleanA_seven4 {p : Nomm} (q : Nomm) (cp : CleanA S Map p) : CleanA S Map (Nomm.n7 (Nomm.n4 p) q) := by
  intro goal region g0 g1 nex _ h
  rw [runL_n7] at h
  obtain ⟨nx, g, _, h2⟩ := bind_some h
  exact clean_n4L cp h2

/-! ## One operand -/

/-- **One operand whose run may make proxies, for `%done` or `%pick`**
(`unaryG_ok` with a `RunOKNV` operand, giving `RunOKV`).  The operand's
`sem` is taken at the later `cond`; the blocks before the operand's run are
left alone by unproxying by hypothesis (`hfix`). -/
theorem unaryGV_ok {lib : Lib} {nm p : Nomm} {goal : CGoal S} (hg : NotNext goal) {g0 g' g1 : Gen Map} {a o : Nat}
    {nexp : NextL S} {f : Noun → Option Noun} (hev : ∀ s, pureEval nm s = (pureEval p s).bind f)
    (hpre : Ext g0 g') (hgr : GrowU g0 g') (hcnd : g'.cond = g0.cond) (ha : g0.re ≤ a ∧ a < g'.re)
    (ho : o < g'.bo) (hfr : Fresh g' (jmp0 o)) (hp : RunOKNV (Map := Map) lib p (lazyReg a) (jmp0 o) g' g1 nexp)
    (hsz : sixCount nm = sixCount p)
    (hfix : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g0.cond k) →
      ∀ k, g0.bo ≤ k → k < g'.bo → (HoonMap.get g'.blocks k).map (unproxyBlob cf) = HoonMap.get g'.blocks k)
    (hblk : ∀ (c : Straight Map), Agree c g0 g' → ∀ (σ : Type) (O : Oracle σ) st regs t gul x,
      SkaModel.read a regs = some x → GoalSem lib O c gul st (Keep g0 g' goal) regs t (jmp0 o) goal (f x)) :
    RunOKV (Map := Map) lib nm goal g0 g1 nexp := by
  refine ⟨hpre.trans hp.ext, hgr.trans hp.grow, (condFresh_of_eq hpre.1 hcnd).trans hp.cfr, hp.lo, hp.hi, ?_,
    fun r hr => ?_, hp.dist, fun e he => ?_, fun e he => ?_, hp.nodup, by rw [hsz]; exact hp.size, fun s hs => ?_,
    hp.ncond, hp.econd, ?_⟩
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
  · intro cf hcf c ned σ O st t gul s0 s ag hned regs hh hn
    have agP : AgreeU lib O c gul st t cf ned g' g1 nexp.laz s0 s :=
      ⟨fun o' h0 h1 hnl => ag.1 o' (Nat.le_trans hpre.2.1 h0) h1 hnl, ag.2⟩
    have Sp := hp.sem cf hcf c ned σ O st t gul s0 s agP hned regs hh hn
    have hcf0 : ∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g0.cond k := fun k hk =>
      (hcf k (Nat.lt_of_lt_of_le hk hp.ext.1)).trans ((hp.cfr.get_lt hk).trans (by rw [hcnd]))
    have agQ : Agree c g0 g' := fun o' h0 h1 => by
      rw [ag.1 o' h0 (Nat.lt_of_lt_of_le h1 hp.ext.2.1) (fun hm => ?_)]
      · rw [hp.ext.2.2.2 o' h1]; exact hfix cf hcf0 o' h0 h1
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

/-- **Cons for `%done` with parts that may make proxies** (`runOKP_consD`
with `OKNV` parts): the `%don` block of the result register, then cons under
a fork-free `%next` of that register (`okNV_cons`). -/
theorem runOKV_consD (lib : Lib) {p q : Nomm} (hp : OKNV (S := S) (Map := Map) lib p)
    (hq : OKNV (S := S) (Map := Map) lib q) (cp : CleanN S Map p) (cq : CleanN S Map q)
    (hpp : p.pure = true) (hqp : q.pure = true) : OKV (Map := Map) lib (CGoal.done : CGoal S) (Nomm.cons p q) := by
  intro region g0 g1 nex _ _ hcount b0 d0 hu hcl0 hcb h
  simp only [CGoal.toL] at h
  rw [runL_cons_done] at h
  simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
  have G : Grow g0 ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) :=
    (grow_re g0).trans (grow_emit (fun j hj => by simp [finJumps] at hj))
  have GU := G.toU hu
  have nk0 : HoonMap.get g0.cond g0.re = Option.none := condBelow_none hcb (Nat.le_refl _)
  have Hn := okNV_cons lib hp hq cp cq hpp hqp (sur := lazyReg g0.re) (th := jmp0 g0.bo)
    ⟨b0, by simp [jmp0, emitted_bo]⟩ rfl ⟨trivial, fun r hr => by
      simp only [lazyReg, NMem] at hr; simp [hr, emitted_re]⟩ trivial hcount (by simp [emitted_bo])
    (by simpa [emitted_drop] using d0) (GU.up hu) (hcl0.growU GU)
    ((condFresh_of_eq (g0 := g0) (g1 := { g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩)
      (by simp [emitted_re]) rfl).below hcb)
    (fun r hr => by simp only [lazyReg, NMem] at hr; subst hr; exact nk0) h
  refine unaryGV_ok (goal := CGoal.done) trivial (f := some) (fun s => by cases pureEval (Nomm.cons p q) s <;> rfl)
    ((ext_re _).trans (ext_emit _ _)) GU rfl ⟨Nat.le_refl _, by simp [emitted_re]⟩ (by simp [emitted_bo])
    (fresh_emitted (by simpa using d0) rfl rfl) Hn rfl ?_ ?_
  · intro cf hcf k h0 h1
    simp only [emitted_bo] at h1
    obtain rfl : k = g0.bo := by omega
    have e0 : HoonMap.get cf g0.re = Option.none := (hcf g0.re (by simp [emitted_re])).trans nk0
    rw [emitted_get _ _ (by simpa using d0)]
    simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, renFin, unproxy_none e0]
  · intro c hc σ O st regs t gul x hx
    have hb := emitted_get' (by simpa using d0) (hc _ (by simp) (by simp [emitted_bo]))
    show goJ lib O c gul st regs t (jmp0 _) = some (toneOf t (some x), st)
    rw [goJ_jmp0 _ _ _ _ hb, execBlob_don', hx]; rfl

/-! ## Two operands for any goal -/

/-- **The `sem` of `RunOKG` against every later `cond`.** -/
def SemGV (lib : Lib) (nm : Nomm) (goal : CGoal S) (g0 g1 : Gen Map) (nex : NextL S) : Prop :=
  ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s0 s : Noun),
    AgreeU lib O c gul st t cf ned g0 g1 nex.laz s0 s → (∀ r, NMem ned r → g1.re ≤ r) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    GoalSem lib O c gul st (fun r => (r < g0.re ∨ NMem ned r) ∧ ¬ GMem goal r) regs t nex.th goal (pureEval nm s)

/-- **`RunOKG` for a run that may make proxies and composes** (`RunOKNV`
for any goal): `cond` grows by fresh proxies, the result's needs are no keys
of the final `cond`, and the `sem` is taken against every later `cond`. -/
structure RunOKGV (lib : Lib) (nm : Nomm) (goal : CGoal S) (g0 g1 : Gen Map) (nex : NextL S) : Prop where
  ext : Ext g0 g1
  grow : GrowU g0 g1
  cfr : CondFresh g0 g1
  lo : 1 ≤ nex.th.there
  hi : nex.th.there < g1.bo
  ent : Entry g1 goal nex.th
  regs : ∀ r, NMem nex.laz.sure.ned r → GMem goal r ∨ (g0.re ≤ r ∧ r < g1.re)
  dist : Distinct nex.laz.sure.ned
  eregs : ∀ e ∈ entries nex.laz, Distinct e.2.sure.ned ∧ ∀ r, NMem e.2.sure.ned r → g0.re ≤ r ∧ r < g1.re
  labs : ∀ e ∈ entries nex.laz, g0.bo ≤ e.1 ∧ e.1 < nex.th.there ∧
    ∃ th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩
  nodup : ((entries nex.laz).map Prod.fst).Nodup
  size : (entries nex.laz).length ≤ 2 * sixCount nm
  nec : ∀ s, ¬ FitsS nex.laz.sure s → pureEval nm s = none ∨ ∃ p, pureEval nm s = some p ∧ GNot goal p
  ncond : ∀ r, NMem nex.laz.sure.ned r → HoonMap.get g1.cond r = Option.none
  econd : ∀ e ∈ entries nex.laz, ∀ r, NMem e.2.sure.ned r → HoonMap.get g1.cond r = Option.none
  sem : SemGV lib nm goal g0 g1 nex

theorem RunOKGV.toNV {lib : Lib} {nm : Nomm} {sur : Sure S} {th : Jmp} {g0 g1 : Gen Map} {nex : NextL S}
    (h : RunOKGV (Map := Map) lib nm (CGoal.next sur th) g0 g1 nex) : RunOKNV (Map := Map) lib nm sur th g0 g1 nex :=
  ⟨h.ext, h.grow, h.cfr, h.lo, h.hi, h.ent, h.regs, h.dist, h.eregs, h.labs, h.nodup, h.size, h.nec, h.ncond,
    h.econd, h.sem⟩

theorem RunOKGV.toV {lib : Lib} {nm : Nomm} {goal : CGoal S} (hg : NotNext goal) {g0 g1 : Gen Map} {nex : NextL S}
    (h : RunOKGV (Map := Map) lib nm goal g0 g1 nex) : RunOKV (Map := Map) lib nm goal g0 g1 nex := by
  refine ⟨h.ext, h.grow, h.cfr, h.lo, h.hi, h.ent, fun r hr => ?_, h.dist, h.eregs, h.labs, h.nodup, h.size,
    fun s hs => ?_, h.ncond, h.econd, fun cf hcf c ned σ O st t gul s0 s ag hned regs hh hn => ?_⟩
  · rcases h.regs r hr with a | a
    · exact (notNext_gmem hg r a).elim
    · exact a
  · rcases h.nec s hs with a | ⟨p, _, a⟩
    · exact a
    · exact (notNext_gnot hg p a).elim
  · exact goalSem_mono (fun r hr => ⟨hr, notNext_gmem hg r⟩) _ _
      (h.sem cf hcf c ned σ O st t gul s0 s ag hned regs hh hn)

/-- **Two operands whose runs may make proxies, for any goal**
(`binaryNV_ok` for any goal, as `binaryN_ok` is). -/
theorem binaryGV_ok {lib : Lib} {nm p q : Nomm} {goal : CGoal S} {g0 g' g1 g2 g3 : Gen Map}
    {lp lq : Sure S} {o : Nat} {nexq nexp nex : NextL S} {f : Noun → Noun → Option Noun}
    (hev : ∀ s, pureEval nm s = (pureEval p s).bind fun x => (pureEval q s).bind fun y => f x y)
    (hg : GoalOK g0 goal) (hpre : Ext g0 g') (hgr : GrowU g0 g') (hcnd : g'.cond = g0.cond)
    (hcb : CondBelow g0)
    (hlp : ∀ r, NMem lp.ned r → GMem goal r ∨ (g0.re ≤ r ∧ r < g'.re))
    (hlq : ∀ r, NMem lq.ned r → GMem goal r ∨ (g0.re ≤ r ∧ r < g'.re))
    (hpq : ∀ r, NMem lp.ned r → ¬ NMem lq.ned r)
    (hq : RunOKNV (Map := Map) lib q lq (jmp0 o) g' g1 nexq)
    (hp : RunOKNV (Map := Map) lib p lp nexq.th g1 g2 nexp)
    (cq : Clean nexq.laz.sure.ned) (cp : Clean nexp.laz.sure.ned)
    (hc : copyL nexp nexq.laz g2 = some (nex, g3))
    (hu : UpBelow g0) (d0 : g0.drop = false) (hsz : sixCount p + sixCount q ≤ sixCount nm)
    (hnot : ∀ x y, ¬ FitsS lp x ∨ ¬ FitsS lq y → f x y = none ∨ ∃ v, f x y = some v ∧ GNot goal v)
    (hfix : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g0.cond k) →
      ∀ k, g0.bo ≤ k → k < g'.bo → (HoonMap.get g'.blocks k).map (unproxyBlob cf) = HoonMap.get g'.blocks k)
    (hblk : ∀ (c : Straight Map), Agree c g0 g' →
      ∀ (σ : Type) (O : Oracle σ) st regs t gul x y, FitsS lp x → FitsS lq y → HoldsN lp.ned regs x →
        HoldsN lq.ned regs y →
          GoalSem lib O c gul st (Keep g0 g' goal) regs t (jmp0 o) goal (f x y)) :
    RunOKGV (Map := Map) lib nm goal g0 g3 nex := by
  -- the labels of the two runs are apart
  have lq' : ∀ e ∈ entries nexq.laz, g'.bo ≤ e.1 ∧ e.1 < g1.bo := fun e he =>
    ⟨(hq.labs e he).1, Nat.lt_trans (hq.labs e he).2.1 hq.hi⟩
  have lp' : ∀ e ∈ entries nexp.laz, g1.bo ≤ e.1 ∧ e.1 < g2.bo := fun e he =>
    ⟨(hp.labs e he).1, Nat.lt_trans (hp.labs e he).2.1 hp.hi⟩
  have apF : ∀ e ∈ nexp.laz.fork, ∀ e' ∈ nexq.laz.fork, e.1.1 ≠ e'.1.1 := fun e he e' he' => by
    have a := lp' e.1 (by rw [entries_eq]; exact List.mem_append_right _ (fork_mem_entries he))
    have b := lq' e'.1 (by rw [entries_eq]; exact List.mem_append_right _ (fork_mem_entries he'))
    omega
  have apB : ∀ e ∈ nexp.laz.bond, ∀ e' ∈ nexq.laz.bond, e.1 ≠ e'.1 := fun e he e' he' => by
    have a := lp' e (by rw [entries_eq]; exact List.mem_append_left _ (bond_mem_entries he))
    have b := lq' e' (by rw [entries_eq]; exact List.mem_append_left _ (bond_mem_entries he'))
    omega
  have kc3 := (kc_copyL _ _).keep _ _ _ hc
  obtain ⟨n, hcp, rfl⟩ := copyL_apart_some apF apB hc
  obtain ⟨EC, eth, bo3, CM, CS⟩ := copy_ok hcp
  have gm : ∀ r, GMem goal r → r < g0.re := fun r hr => by
    cases goal with
    | next laz th => exact hg.2 r hr
    | _ => exact hr.elim
  have lpl : ∀ r, NMem lp.ned r → r < g'.re := fun r hr => by
    rcases hlp r hr with h | ⟨_, h⟩
    · exact Nat.lt_of_lt_of_le (gm r h) hpre.1
    · exact h
  have lql : ∀ r, NMem lq.ned r → r < g'.re := fun r hr => by
    rcases hlq r hr with h | ⟨_, h⟩
    · exact Nat.lt_of_lt_of_le (gm r h) hpre.1
    · exact h
  have mp : ∀ r, NMem nexp.laz.sure.ned r → NMem lp.ned r ∨ (g1.re ≤ r ∧ r < g2.re) := hp.regs
  have mq : ∀ r, NMem nexq.laz.sure.ned r → NMem lq.ned r ∨ (g'.re ≤ r ∧ r < g1.re) := hq.regs
  have l0 := hpre.1
  have l1 := hq.ext.1
  have l2 := hp.ext.1
  have l3 := EC.1
  have lowP : ∀ r, NMem nexp.laz.sure.ned r → r < g2.re := fun r hr => by
    rcases mp r hr with a | ⟨_, a⟩
    · have := lpl r a; omega
    · exact a
  have lowQ : ∀ r, NMem nexq.laz.sure.ned r → r < g1.re := fun r hr => by
    rcases mq r hr with a | ⟨_, a⟩
    · have := lql r a; omega
    · exact a
  have P : CopyPre nexp.laz.sure.ned nexq.laz.sure.ned g2.re := by
    refine ⟨cp, cq, ⟨hp.dist, hq.dist, fun r h1 h2 => ?_⟩, fun r hr => ?_⟩
    · rcases mp r h1 with a | ⟨a, _⟩ <;> rcases mq r h2 with b | ⟨b, b'⟩
      · exact hpq r a b
      · have := lpl r a; omega
      · have := lql r b; omega
      · omega
    · rcases hr with h | h
      · exact lowP r h
      · have := lowQ r h; omega
  obtain ⟨CD, CF, CB⟩ := CS P
  have d2 : g2.drop = false := hp.ext.2.2.1.trans (hq.ext.2.2.1.trans (hpre.2.2.1.trans d0))
  have Dc := copy_down (goal := goal) hcp hp.lo hp.hi d2 (Nat.le_trans hp.lo (Nat.le_of_lt hp.hi))
  have u2 : UpBelow g2 := (hgr.trans (hq.grow.trans hp.grow)).up hu
  have Eq3 : Ext g1 g3 := hp.ext.trans EC
  have E'3 : Ext g' g3 := hq.ext.trans Eq3
  have bo01 := hpre.2.1
  have bo12 := hq.ext.2.1
  have bo23 := hp.ext.2.1
  have hp3 : Ext g2 g3 := EC
  have cb2 : CondBelow g2 := ((condFresh_of_eq hpre.1 hcnd).trans (hq.cfr.trans hp.cfr)).below hcb
  have nkq : ∀ r, NMem nexq.laz.sure.ned r → HoonMap.get g2.cond r = Option.none := fun r h => by
    rw [hp.cfr.get_lt (lowQ r h)]; exact hq.ncond r h
  have thq : nexq.th.args = [] := nextArgs_nil hq.ent rfl
  have thp : nexp.th.args = [] := nextArgs_nil hp.ent thq
  have AC : AboveIn (fun r => HoonMap.get g2.cond r = Option.none) g2.bo g3 :=
    (keepsA_copy (P := fun r => HoonMap.get g2.cond r = Option.none) (first := ⟨nexp.laz.sure, nexp.th⟩) d2 ⟨hp.ncond, jmpIn_nil thp⟩ nkq (fun r hr => condBelow_none cb2 hr) hcp).1.ab _
      (aboveIn_start _ g2)
  have BC : BelowIn g2.bo g3 :=
    (keeps_copy (first := ⟨nexp.laz.sure, nexp.th⟩) d2 ⟨fun r hr => lowP r hr, jmpIn_nil thp⟩ (fun r hr => by have := lowQ r hr; omega) hcp).1.bel _
      (belowIn_start g2)
  have fixC : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g3.re → HoonMap.get cf k = HoonMap.get g3.cond k) →
      ∀ k, g2.bo ≤ k → k < g3.bo → (HoonMap.get g3.blocks k).map (unproxyBlob cf) = HoonMap.get g3.blocks k := by
    intro cf hcf k h0 h1
    have u0 : ∀ x, x < g3.re → unproxy cf x = unproxy g3.cond x := unproxy_agree hcf
    have u1 : ∀ x, HoonMap.get g2.cond x = Option.none → unproxy g3.cond x = id x :=
      fun x hx => unproxy_none (by rw [kc3]; exact hx)
    cases hg : HoonMap.get g3.blocks k with
    | none => rfl
    | some b =>
      simp only [Option.map_some]
      rw [unproxyBlob, renBlob_congr u0 (BC k b h0 h1 hg), renBlob_congr u1 (AC k b h0 h1 hg), renBlob_id]
  -- the entries
  have memN : ∀ e, e ∈ entries (mk n.laz (nexp.laz.fork ++ nexq.laz.fork) (nexp.laz.bond ++ nexq.laz.bond)) ↔
      e ∈ entries nexp.laz ∨ e ∈ entries nexq.laz := fun e => by
    rw [(entries_side_perm _ _ _).mem_iff, List.mem_append]
  have labN : ∀ k, k ∈ (entries (mk n.laz (nexp.laz.fork ++ nexq.laz.fork)
      (nexp.laz.bond ++ nexq.laz.bond))).map Prod.fst → g'.bo ≤ k ∧ k < g2.bo := fun k hk => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
    rcases (memN e).mp he with a | a
    · have := lp' e a; omega
    · have := lq' e a; omega
  refine {
    ext := hpre.trans E'3
    grow := hgr.trans (hq.grow.trans (hp.grow.trans (Dc.grow.toU u2)))
    cfr := ((condFresh_of_eq hpre.1 hcnd).trans hq.cfr).trans (hp.cfr.trans (condFresh_of_eq EC.1 kc3))
    lo := Dc.lo
    hi := Dc.hi
    ent := Dc.entry
    regs := fun r hr => ?_
    dist := CD
    eregs := fun e he => ?_
    labs := fun e he => ?_
    nodup := ?_
    size := ?_
    nec := fun s hs => ?_
    ncond := fun r hr => ?_
    econd := fun e he r hr => ?_
    sem := fun cf hcf c ned σ O st t gul s0 s ag hned regs hh hn => ?_ }
  · rcases CM r hr with h | h | ⟨h, h'⟩
    · rcases mp r h with a | ⟨a, a'⟩
      · rcases hlp r a with b | ⟨b, b'⟩
        · exact Or.inl b
        · exact Or.inr ⟨b, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    · rcases mq r h with a | ⟨a, a'⟩
      · rcases hlq r a with b | ⟨b, b'⟩
        · exact Or.inl b
        · exact Or.inr ⟨b, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, h'⟩
  · rcases (memN e).mp he with a | a
    · exact ⟨(hp.eregs e a).1, fun r hr => by have := (hp.eregs e a).2 r hr; omega⟩
    · exact ⟨(hq.eregs e a).1, fun r hr => by have := (hq.eregs e a).2 r hr; omega⟩
  · show g0.bo ≤ e.1 ∧ e.1 < n.th.there ∧ _
    rw [eth]
    simp only [jmp0]
    rcases (memN e).mp he with a | a
    · obtain ⟨x, y, th, z⟩ := hp.labs e a
      have := hp.hi
      exact ⟨by omega, by omega, th, by rw [hp3.2.2.2 _ (by omega)]; exact z⟩
    · obtain ⟨x, y, th, z⟩ := hq.labs e a
      have := hq.hi
      exact ⟨by omega, by omega, th, by rw [Eq3.2.2.2 _ (by omega)]; exact z⟩
  · rw [((entries_side_perm _ _ _).map Prod.fst).nodup_iff, List.map_append, List.nodup_append]
    refine ⟨hp.nodup, hq.nodup, fun a ha b hb => ?_⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp hb
    have := lp' e he; have := lq' e' he'; omega
  · rw [(entries_side_perm _ _ _).length_eq, List.length_append]
    have := hp.size; have := hq.size; omega
  · rw [hev]
    have hn : ¬ FitsS nexp.laz.sure s ∨ ¬ FitsS nexq.laz.sure s := by
      by_cases a : FitsS nexp.laz.sure s
      · exact Or.inr fun b => hs ((CF s).mpr ⟨a, b⟩)
      · exact Or.inl a
    cases ep : pureEval p s with
    | none => exact Or.inl rfl
    | some x =>
      cases eq : pureEval q s with
      | none => exact Or.inl rfl
      | some y =>
        simp only [Option.bind_some]
        rcases hn with a | a
        · rcases hp.nec s a with e | ⟨x', e, hx⟩
          · rw [ep] at e; cases e
          · rw [ep] at e; cases e
            exact hnot x y (Or.inl hx)
        · rcases hq.nec s a with e | ⟨y', e, hy⟩
          · rw [eq] at e; cases e
          · rw [eq] at e; cases e
            exact hnot x y (Or.inr hy)
  · rw [kc3]
    rcases CM r hr with h | h | ⟨h, h'⟩
    · exact hp.ncond r h
    · rw [hp.cfr.get_lt (lowQ r h)]; exact hq.ncond r h
    · exact condBelow_none cb2 h
  · rw [kc3]
    rcases (memN e).mp he with a | a
    · exact hp.econd e a r hr
    · rw [hp.cfr.get_lt ((hq.eregs e a).2 r hr).2]; exact hq.econd e a r hr
  · -- the copy block
    have hcf2 : ∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g2.cond k := fun k hk =>
      (hcf k (by omega)).trans (by rw [kc3])
    have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk =>
      (hcf2 k (by omega)).trans (hp.cfr.get_lt hk)
    have hcf0 : ∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g0.cond k := fun k hk =>
      (hcf1 k (by omega)).trans ((hq.cfr.get_lt hk).trans (by rw [hcnd]))
    have agC : Agree c g2 g3 := fun k h0 h1 => by
      rw [ag.1 k (by omega) h1 (fun hm => by have := labN k hm; omega)]
      exact fixC cf hcf k h0 h1
    obtain ⟨R1, hs1, hs1', u1, e1⟩ := CB d2 c agC lib σ O st regs t gul s hh
    have hned2 : ∀ r, NMem ned r → g2.re ≤ r := fun r hr => by have := hned r hr; omega
    have hned1 : ∀ r, NMem ned r → g1.re ≤ r := fun r hr => by have := hned r hr; omega
    have hn1 : HoldsN ned R1 s0 := HoldsN.agree _ (fun r hr => u1 r (fun hm => by
      have := lowP r hm; have := hned r hr; omega) (fun hm => by have := lowQ r hm; have := hned r hr; omega)) hn
    have agP : AgreeU lib O c gul st t cf ned g1 g2 nexp.laz s0 s :=
      ag.part (by omega) hp3 (fun e he => (memN e).mpr (Or.inl he))
        (fun k h0 h1 hm => by
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
          rcases (memN e).mp he with a | a
          · exact List.mem_map_of_mem a
          · have := lq' e a; omega)
        (fun e he => (lp' e he).2)
    have Hp := hp.sem cf hcf2 c ned σ O st t gul s0 s agP hned2 R1 hs1 hn1
    have agQ0 : Agree c g0 g' := fun k h0 h1 => by
      rw [ag.1 k h0 (by omega) (fun hm => by have := labN k hm; omega), E'3.2.2.2 k h1]
      exact hfix cf hcf0 k h0 h1
    -- the kept registers
    have keep1 : ∀ r, (r < g0.re ∨ NMem ned r) → ¬ GMem goal r →
        SkaModel.read r R1 = SkaModel.read r regs := by
      intro r k1 k2
      refine u1 r (fun hm => ?_) (fun hm => ?_)
      · rcases mp r hm with a | ⟨a, a'⟩
        · rcases hlp r a with b | ⟨b, b'⟩
          · exact k2 b
          · rcases k1 with k1 | k1
            · omega
            · have := hned r k1; omega
        · rcases k1 with k1 | k1
          · omega
          · have := hned r k1; omega
      · rcases mq r hm with a | ⟨a, a'⟩
        · rcases hlq r a with b | ⟨b, b'⟩
          · exact k2 b
          · rcases k1 with k1 | k1
            · omega
            · have := hned r k1; omega
        · rcases k1 with k1 | k1
          · omega
          · have := hned r k1; omega
    rw [hev]
    cases ep : pureEval p s with
    | none =>
      rw [ep] at Hp
      exact goalSem_crash goal (by rw [eth] at e1 ⊢; exact e1.trans Hp)
    | some x =>
      rw [ep] at Hp
      simp only [Option.bind_some]
      by_cases fx : FitsS lp x
      · obtain ⟨R2, hl2, k2, e2⟩ := Hp.1 fx
        have hq2 : HoldsS nexq.laz.sure R2 s := by
          refine ⟨HoldsN.agree _ (fun r hr => k2 r ⟨Or.inl (lowQ r hr), ?_⟩) hs1'.1, hs1'.2⟩
          intro hm
          rcases mq r hr with a | ⟨a, _⟩
          · exact hpq r hm a
          · have := lpl r hm; omega
        have hn2 : HoldsN ned R2 s0 := HoldsN.agree _ (fun r hr => k2 r ⟨Or.inr hr, fun hm => by
          have := lpl r hm; have := hned r hr; omega⟩) hn1
        have agQ : AgreeU lib O c gul st t cf ned g' g1 nexq.laz s0 s :=
          ag.part bo01 Eq3 (fun e he => (memN e).mpr (Or.inr he))
            (fun k h0 h1 hm => by
              obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
              rcases (memN e).mp he with a | a
              · have := lp' e a; omega
              · exact List.mem_map_of_mem a)
            (fun e he => (lq' e he).2)
        have Hq := hq.sem cf hcf1 c ned σ O st t gul s0 s agQ hned1 R2 hq2 hn2
        cases eq : pureEval q s with
        | none =>
          rw [eq] at Hq
          exact goalSem_crash goal (by rw [eth] at e1 ⊢; exact e1.trans (e2.trans Hq))
        | some y =>
          rw [eq] at Hq
          simp only [Option.bind_some]
          by_cases fy : FitsS lq y
          · obtain ⟨R3, hq3, k3, e3⟩ := Hq.1 fy
            have hl3 : HoldsN lp.ned R3 x :=
              HoldsN.agree _ (fun r hr => k3 r ⟨Or.inl (lpl r hr), hpq r hr⟩) hl2
            have B := hblk c agQ0 σ O st R3 t gul x y fx fy hl3 hq3
            refine GoalSem.transfer (by rw [eth] at e1 ⊢; exact e1.trans (e2.trans e3)) (fun r hk => ?_)
              (GoalSem.mono (fun r ⟨k1, k2⟩ => ⟨k1.imp id (fun h => by have := hned r h; omega), k2⟩) B)
            obtain ⟨k1, k2'⟩ := hk
            have nlq : ¬ NMem lq.ned r := fun hm => by
              rcases hlq r hm with b | ⟨b, b'⟩
              · exact k2' b
              · rcases k1 with k1 | k1
                · omega
                · have := hned r k1; omega
            have nlp : ¬ NMem lp.ned r := fun hm => by
              rcases hlp r hm with b | ⟨b, b'⟩
              · exact k2' b
              · rcases k1 with k1 | k1
                · omega
                · have := hned r k1; omega
            rw [k3 r ⟨k1.imp (fun h => by omega) id, nlq⟩, k2 r ⟨k1.imp (fun h => by omega) id, nlp⟩,
              keep1 r k1 k2']
          · exact goalSem_crash_or (hnot x y (Or.inr fy))
              (by rw [eth] at e1 ⊢; exact e1.trans (e2.trans (Hq.2 fy)))
      · have hc2 := Hp.2 fx
        cases eq : pureEval q s with
        | none => exact goalSem_crash goal (by rw [eth] at e1 ⊢; exact e1.trans hc2)
        | some y =>
          simp only [Option.bind_some]
          exact goalSem_crash_or (hnot x y (Or.inl fx)) (by rw [eth] at e1 ⊢; exact e1.trans hc2)

/-- **Cons for `%pick` with parts that may make proxies**
(`runOKP_consP` with `OKNV` parts): a cell is no loobean, the code crashes
after both operands at the `[%bom ~]` block, which mentions no register. -/
theorem runOKV_consP (lib : Lib) {p q : Nomm} (hp : OKNV (S := S) (Map := Map) lib p)
    (hq : OKNV (S := S) (Map := Map) lib q) (cp : CleanN S Map p) (cq : CleanN S Map q)
    (hpp : p.pure = true) (z o : Jmp) :
    OKV (Map := Map) lib (CGoal.pick z o : CGoal S) (Nomm.cons p q) := by
  intro region g0 g1 nex _ hj hcount b0 d0 hu hcl0 hcb h
  simp only [CGoal.toL] at h
  rw [runL_cons_pick] at h
  obtain ⟨o', g2, h2, h⟩ := bind_some h
  rw [emit_apply] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  obtain ⟨nex2, g3, h3, h⟩ := bind_some h
  obtain ⟨nex2', g3', hp2, h⟩ := bind_some h
  rw [pastL_pure _ _ hpp, pure_apply] at hp2
  simp only [Option.some.injEq, Prod.mk.injEq] at hp2
  obtain ⟨rfl, rfl⟩ := hp2
  obtain ⟨nex1, g4, h4, h⟩ := bind_some h
  simp only [sixCount] at hcount
  have G : Grow g0 (g0.emitted ⟨[], [], Termin.bom Option.none⟩) := grow_emit (fun j hj => by simp [finJumps] at hj)
  have d2 : (g0.emitted ⟨[], [], Termin.bom Option.none⟩).drop = false := by simpa [emitted_drop] using d0
  have GU := G.toU hu
  have u2 := GU.up hu
  have cl2 : Clear (g0.emitted ⟨[], [], Termin.bom Option.none⟩) := hcl0.growU GU
  have cb2 : CondBelow (g0.emitted ⟨[], [], Termin.bom Option.none⟩) := hcb
  have Rq := hq (sur := Sure.bunt) (th := jmp0 g0.bo) ⟨b0, by simp [jmp0, emitted_bo]⟩ rfl
    ⟨trivial, fun r hr => hr.elim⟩ trivial (by omega) (by simp [emitted_bo]) d2 u2 cl2 cb2 (fun r hr => hr.elim) h3
  have Rp := hp (sur := Sure.bunt) (th := nex2.th) ⟨Rq.lo, Rq.hi⟩ (nextArgs_nil Rq.ent rfl)
    ⟨trivial, fun r hr => hr.elim⟩ trivial (by omega) (by have := Rq.lo; have := Rq.hi; omega)
    (Rq.ext.2.2.1.trans d2) (Rq.grow.up u2) (cl2.growU Rq.grow) (Rq.cfr.below cb2) (fun r hr => hr.elim) h4
  refine RunOKGV.toV (goal := CGoal.pick z o) trivial (binaryGV_ok (goal := CGoal.pick z o) (pureEval_cons p q)
    trivial (ext_emit _ _) GU rfl hcb
    (fun r hr => by exact hr.elim) (fun r hr => by exact hr.elim) (fun r hr => by exact hr.elim) Rq Rp
    (cq (sur := Sure.bunt) trivial h3) (cp (sur := Sure.bunt) trivial h4) h hu d0 (by simp only [sixCount]; omega)
    (fun x y hn => absurd (hn.elim (fun a => a (fitsS_bunt x)) (fun a => a (fitsS_bunt y))) id) ?_ ?_)
  · intro cf _ k h0 h1
    simp only [emitted_bo] at h1
    obtain rfl : k = g0.bo := by omega
    rw [emitted_get _ _ d0]
    simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, renFin]
  · intro c hc σ O st regs t gul x y _ _ _ _
    have hb := emitted_get' d0 (hc _ (by simp) (by simp [emitted_bo]))
    show goJ lib O c gul st regs t (jmp0 g0.bo) = some (Tone.two t, st)
    rw [goJ_jmp0 _ _ _ _ hb, execBlob_bom']

end Comp
end SkaModel
end Formalization
