import lemmas.Ska.CompIndirectOut
import lemmas.Ska.CompConsV

/-!
# A cons with the call in its head

README Gaps 12.14 (eighteenth session).  The cons `[[2 b c] d]` under a
fork-free `%next`: `+split` makes the `con` block, the tail `d` runs for the
tail of the need, then `+past` (the head is hinted, so a tail that needs
something has that need parked in a bond behind a new block `[hop]`, whose
ops `+kern` fills later), then the call runs for the head of the need into
that block, then `+copy`.  At run time the call runs first, then the block of
`+past` fills the tail's need from the subject at the oracle's new state,
then the tail, then the `con` block.

* `growU_tagged`: `+set-tag` changes the tags only.
* `pastL_hinted`: what `+past` does behind a hinted nomm (nothing, for a
  need that asks nothing, or the block and the bond).
* `entries_past`: the entries of the bond of `+past`.
* `TailNV`: `RunOKNV` with the entries' registers from a given bound on and
  their labels up to the jump, which the tail with its block of `+past`
  meets (`tailNV_past`), as does a `RunOKNV` (`TailNV.ofRun`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## `+set-tag` changes the tags only -/

theorem growU_tagged (g : Gen Map) (o : Nat) (region : List Nat) : GrowU g (g.tagged o region) :=
  ⟨by simp, by simp, fun _ b _ hb => ⟨b, by simpa using hb, rfl, rfl⟩,
    fun _ b' hb' => Or.inl ⟨b', by simpa using hb', rfl, rfl⟩⟩

/-! ## `+past` behind a hinted nomm -/

/-- **`+past` behind a hinted nomm** (a call): nothing when the need asks
nothing (no register, looks at the subject whole only, no fork), else a new
block `[hop th]` tagged with the region, and the need parked in a bond there. -/
theorem pastL_hinted {cod : Bell → Option Bool} {nex : NextL S} {nom : Nomm} (hh : hinted cod nom = some true)
    {region : List Nat} {g g' : Gen Map} {nex' : NextL S} (h : pastL cod nex nom region g = some (nex', g')) :
    (nex' = nex ∧ g' = g ∧ nex.laz.sure.ned = Need.none ∧ HoonSet.small nex.laz.sure.lok = true ∧
      nex.laz.fork = []) ∨
    (nex' = ⟨mk Sure.bunt [] ((g.bo, mk nex.laz.sure nex.laz.fork []) :: nex.laz.bond), jmp0 g.bo⟩ ∧
      g' = (g.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g.bo region) := by
  unfold pastL at h
  split at h
  · rename_i hc
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, rfl, hc.1, hc.2.1, List.isEmpty_iff.mp hc.2.2⟩
  · rw [hh] at h
    simp only at h
    obtain ⟨o, g1, h1, h⟩ := bind_some h
    rw [emit_apply] at h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨u, g2, h2, h⟩ := bind_some h
    rw [setTag_apply] at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨-, rfl⟩ := h2
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inr ⟨rfl, rfl⟩

/-- A need with no register that looks at the subject whole only holds of
every noun in every registers. -/
theorem looks_small {lok : S} (hs : HoonSet.small lok = true) (v : Noun) : Looks lok v := fun a ha => by
  rw [(HoonSet.small_iff _).mp hs a ha, slot?_one]
  rfl

theorem holdsS_trivial {s : Sure S} (hn : s.ned = Need.none) (hs : HoonSet.small s.lok = true)
    (regs : Map (Option Noun)) (v : Noun) : HoldsS s regs v := ⟨by rw [hn]; trivial, looks_small hs v⟩

theorem fitsS_trivial {s : Sure S} (hn : s.ned = Need.none) (hs : HoonSet.small s.lok = true) (v : Noun) :
    FitsS s v := ⟨by rw [hn]; trivial, looks_small hs v⟩

/-- The entries of the bond of `+past`. -/
theorem entries_past (s : Sure S) (l : Lazy S) (o : Nat) :
    (entries (mk s [] ((o, mk l.sure l.fork []) :: l.bond))).Perm ((o, mk l.sure l.fork []) :: entries l) := by
  rw [entries_eq l]
  simp only [entries, bondEntries, forkEntries, List.append_nil, List.cons_append, List.nil_append]
  exact List.Perm.cons _ (List.perm_append_comm)

/-! ## The tail of a cons behind a call -/

/-- **The relation of the tail of a cons behind a call**: `RunOKNV` but
with the entries' registers from `lo` on (the block of `+past` holds the
tail's need, whose registers the parent's `+split` allocated) and the
labels of the entries up to the jump (the block of `+past` is the jump). -/
structure TailNV (lib : Lib) (nm : Nomm) (bot : Nat) (sur : Sure S) (th : Jmp) (g0 g1 : Gen Map) (nex : NextL S) :
    Prop where
  ext : Ext g0 g1
  grow : GrowU g0 g1
  cfr : CondFresh g0 g1
  lo : 1 ≤ nex.th.there
  hi : nex.th.there < g1.bo
  ent : Entry g1 (CGoal.next sur th) nex.th
  regs : ∀ r, NMem nex.laz.sure.ned r → NMem sur.ned r ∨ (g0.re ≤ r ∧ r < g1.re)
  dist : Distinct nex.laz.sure.ned
  eregs : ∀ e ∈ entries nex.laz, Distinct e.2.sure.ned ∧
    ∀ r, NMem e.2.sure.ned r → (NMem sur.ned r ∨ bot ≤ r) ∧ r < g1.re
  labs : ∀ e ∈ entries nex.laz, g0.bo ≤ e.1 ∧ e.1 ≤ nex.th.there ∧
    ∃ th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩
  nodup : ((entries nex.laz).map Prod.fst).Nodup
  nec : ∀ s, ¬ FitsS nex.laz.sure s → pureEval nm s = none ∨ ∃ p, pureEval nm s = some p ∧ ¬ FitsS sur p
  ncond : ∀ r, NMem nex.laz.sure.ned r → HoonMap.get g1.cond r = Option.none
  econd : ∀ e ∈ entries nex.laz, ∀ r, NMem e.2.sure.ned r → HoonMap.get g1.cond r = Option.none
  sem : SemNV lib nm sur th g0 g1 nex

theorem TailNV.ofRun {lib : Lib} {nm : Nomm} {lo : Nat} {sur : Sure S} {th : Jmp} {g0 g1 : Gen Map}
    {nex : NextL S} (R : RunOKNV (Map := Map) lib nm sur th g0 g1 nex) (hlo : lo ≤ g0.re) :
    TailNV lib nm lo sur th g0 g1 nex :=
  ⟨R.ext, R.grow, R.cfr, R.lo, R.hi, R.ent, R.regs, R.dist,
    fun e he => ⟨(R.eregs e he).1, fun r hr => ⟨Or.inr (by have := ((R.eregs e he).2 r hr).1; omega),
      ((R.eregs e he).2 r hr).2⟩⟩,
    fun e he => ⟨(R.labs e he).1, Nat.le_of_lt (R.labs e he).2.1, (R.labs e he).2.2⟩,
    R.nodup, R.nec, R.ncond, R.econd, R.sem⟩

/-- **The tail with its block of `+past` meets `TailNV`**: the bond's
block fills the tail's need from the subject (`FillSem` of `AgreeU`), or
crashes where the subject does not fit it, which the tail's `nec` makes the
tail's crash or a value that does not fit the goal. -/
theorem tailNV_past {lib : Lib} {nm : Nomm} {lo : Nat} {sur : Sure S} {o : Nat} {g0 g1 : Gen Map}
    {nex : NextL S} (R : RunOKNV (Map := Map) lib nm sur (jmp0 o) g0 g1 nex) (hlo : lo ≤ g0.re)
    (hsur : ∀ r, NMem sur.ned r → r < g0.re) (d1 : g1.drop = false) (u1 : UpBelow g1)
    (region : List Nat) :
    TailNV lib nm lo sur (jmp0 o) g0 ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region)
      ⟨mk Sure.bunt [] ((g1.bo, mk nex.laz.sure nex.laz.fork []) :: nex.laz.bond), jmp0 g1.bo⟩ := by
  have hb : ∀ k, HoonMap.get ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region).blocks k =
      if k = g1.bo then some ⟨[], [], Termin.hop nex.th⟩ else HoonMap.get g1.blocks k := fun k => by
    simp only [tagged_blocks, Gen.emitted, d1, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]
  have E1 : Ext g1 ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region) :=
    (ext_emit g1 _).trans (ext_tagged _ _ _)
  have G1 : GrowU g1 ((g1.emitted ⟨[], [], Termin.hop nex.th⟩).tagged g1.bo region) :=
    (growU_emit (b := ⟨[], [], Termin.hop nex.th⟩) (fun j hj => by
      simp only [finJumps, List.mem_singleton] at hj; subst hj; exact ⟨R.lo, R.hi⟩) u1).trans (growU_tagged _ _ _)
  have mem : ∀ e, e ∈ entries (mk (Sure.bunt : Sure S) [] ((g1.bo, mk nex.laz.sure nex.laz.fork []) ::
      nex.laz.bond)) ↔ e = (g1.bo, mk nex.laz.sure nex.laz.fork []) ∨ e ∈ entries nex.laz := fun e => by
    rw [(entries_past _ _ _).mem_iff, List.mem_cons]
  have lt1 : ∀ e ∈ entries nex.laz, e.1 < g1.bo := fun e he => Nat.lt_trans (R.labs e he).2.1 R.hi
  have l01 := R.ext.1
  have thn : nex.th.args = [] := nextArgs_nil R.ent rfl
  refine ⟨R.ext.trans E1, R.grow.trans G1, R.cfr.trans (condFresh_of_eq (by simp [Gen.emitted]) (by
      rw [tagged_cond]; rfl)), by simp only [jmp0]; have := R.lo; have := R.hi; omega,
    by simp [jmp0, Gen.emitted], Or.inl ⟨⟨[], [], Termin.hop nex.th⟩, by rw [hb]; simp [jmp0], rfl, rfl⟩,
    fun r hr => by simp [Sure.bunt, NMem] at hr, trivial, fun e he => ?_, fun e he => ?_, ?_,
    fun s hs => absurd (fitsS_bunt s) hs, fun r hr => by simp [Sure.bunt, NMem] at hr, fun e he r hr => ?_, ?_⟩
  · rcases (mem e).mp he with rfl | a
    · refine ⟨R.dist, fun r hr => ?_⟩
      simp only [Gen.emitted, tagged_re]
      rcases R.regs r hr with b | ⟨b, b'⟩
      · exact ⟨Or.inl b, by have := hsur r b; omega⟩
      · exact ⟨Or.inr (by omega), by omega⟩
    · exact ⟨(R.eregs e a).1, fun r hr => by
        have := (R.eregs e a).2 r hr; simp only [Gen.emitted, tagged_re]; exact ⟨Or.inr (by omega), by omega⟩⟩
  · rcases (mem e).mp he with rfl | a
    · exact ⟨R.ext.2.1, by simp [jmp0], _, by rw [hb, if_pos rfl]⟩
    · obtain ⟨x, -, th', z⟩ := R.labs e a
      have := lt1 e a
      exact ⟨x, by simp only [jmp0]; omega, th', by rw [hb, if_neg (by omega)]; exact z⟩
  · rw [((entries_past _ _ _).map Prod.fst).nodup_iff, List.map_cons, List.nodup_cons]
    exact ⟨fun hm => by obtain ⟨e, he, e1⟩ := List.mem_map.mp hm; have := lt1 e he; omega, R.nodup⟩
  · rw [tagged_cond]
    rcases (mem e).mp he with rfl | a
    · exact R.ncond r hr
    · exact R.econd e a r hr
  -- the `sem`
  intro cf hcf c ned σ O st t gul s0 s ag hned regs _ hn
  obtain ⟨A, th', h1, h2, F⟩ := ag.2 _ ((mem _).mpr (Or.inl rfl))
  rw [hb, if_pos rfl] at h1
  cases h1
  rw [renJmp_nil _ thn] at h2
  have hcf1 : ∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k := fun k hk => by
    rw [hcf k (by simp [Gen.emitted]; omega), tagged_cond]; rfl
  have ag1 : AgreeU lib O c gul st t cf ned g0 g1 nex.laz s0 s :=
    ag.part (Nat.le_refl _) E1 (fun e he => (mem e).mpr (Or.inr he))
      (fun k _ h1' hm => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
        rcases (mem e).mp he with rfl | a
        · simp at h1'
        · exact List.mem_map_of_mem a) lt1
  have hned1 : ∀ r, NMem ned r → g1.re ≤ r := fun r hr => by have := hned r hr; simpa [Gen.emitted] using this
  obtain ⟨F1, F2⟩ := F regs hn
  by_cases fs : FitsS nex.laz.sure s
  · obtain ⟨R', hr, hh, hk⟩ := F1 fs
    have e1 := hr [] (Termin.hop nex.th)
    simp only [List.append_nil] at e1
    have hn' : HoldsN ned R' s0 := HoldsN.agree _ (fun x hx => hk x (Or.inl hx) (fun hm => by
      have := hned1 x hx
      rcases R.regs x hm with b | ⟨_, b⟩
      · have := hsur x b; omega
      · omega)) hn
    have G := R.sem cf hcf1 c ned σ O st t gul s0 s ag1 hned1 R' hh hn'
    refine GoalSem.transfer (by rw [goJ_jmp0 _ _ _ _ h2, e1, execBlob_hop]) (fun r hk' => ?_) G
    obtain ⟨k1, k2⟩ := hk'
    refine hk r (k1.elim (fun h => Or.inr (by rw [tagged_re]; simp only [Gen.emitted]; omega)) Or.inl)
      fun hm => ?_
    rcases R.regs r hm with b | ⟨b, _⟩
    · exact k2 b
    · rcases k1 with k1 | k1
      · omega
      · have := hned1 r k1; omega
  · have e2 := F2 fs [] (Termin.hop nex.th)
    simp only [List.append_nil] at e2
    have ec : goJ lib O c gul st regs t (jmp0 g1.bo) = some (Tone.two t, st) := by
      rw [goJ_jmp0 _ _ _ _ h2, e2]
    rcases R.nec s fs with e | ⟨v, ev, hv⟩
    · rw [e]; exact goalSem_crash _ ec
    · rw [ev]; exact goalSem_crash_or (Or.inr ⟨v, rfl, hv⟩) ec

/-! ## `+mink` on a cons, and returns -/

/-- **`+mink` on a cell formula whose head is a cell**: the head runs first
with one less fuel; its crash or block is the cons's, else the tail runs
(with the tone of a pure nomm, `Mq`). -/
theorem minkF_consC {lib : Lib} {P : Noun → Prop} {q : Nomm} {fh ft : Noun} (hfh : ∃ a b, fh = C a b)
    (Mq : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {r : Tone}, P s → minkF lib gul n tm s ft = some r →
      r = toneOf tm (pureEval q s))
    {s gul : Noun} {n : Nat} {tm : Trace} {r : Tone} (hs : P s) (h : minkF lib gul n tm s (C fh ft) = some r) :
    ∃ n' rh, n' < n ∧ minkF lib gul n' tm s fh = some rh ∧
      (((∀ p, rh ≠ Tone.zero p) ∧ r = rh) ∨ ∃ x, rh = Tone.zero x ∧
        ((pureEval q s = none ∧ r = Tone.two tm) ∨ ∃ y, pureEval q s = some y ∧ r = Tone.zero (C x y))) := by
  obtain ⟨a, b, rfl⟩ := hfh
  cases n with
  | zero => simp [minkF] at h
  | succ n' =>
    rw [minkF_succ_eq] at h
    simp only [minkStep] at h
    cases eh : minkF lib gul n' tm s (C a b) with
    | none => rw [eh] at h; simp [tbind] at h
    | some rh =>
      rw [eh] at h
      refine ⟨n', rh, Nat.lt_succ_self n', eh, ?_⟩
      cases rh with
      | zero x =>
        refine Or.inr ⟨x, rfl, ?_⟩
        simp only [tbind] at h
        cases et : minkF lib gul n' tm s ft with
        | none => rw [et] at h; simp [tbind] at h
        | some rt =>
          rw [et] at h
          have e := Mq hs et
          cases eq : pureEval q s with
          | none =>
            rw [eq] at e; subst e
            simp only [toneOf, tbind, Option.some.injEq] at h
            exact Or.inl ⟨rfl, h.symm⟩
          | some y =>
            rw [eq] at e; subst e
            simp only [toneOf, tbind, Option.some.injEq] at h
            exact Or.inr ⟨y, rfl, h.symm⟩
      | one p =>
        simp only [tbind, Option.some.injEq] at h
        exact Or.inl ⟨(fun _ e => by cases e), h.symm⟩
      | two t' =>
        simp only [tbind, Option.some.injEq] at h
        exact Or.inl ⟨(fun _ e => by cases e), h.symm⟩

section
variable {lib : Lib} {σ : Type} {Inv : σ → Prop} {ν : σ → Needs} {O : Oracle σ} {c : Straight Map} {gul : Noun}

/-- `OracleFwd` with a smaller bound. -/
theorem oracleFwd_le {n n' : Nat} (h : OracleFwd lib Inv ν O n) (hn : n' ≤ n) : OracleFwd lib Inv ν O n' :=
  ⟨fun st b m vals ti tm gul s j r hst hj => h.call st b m vals ti tm gul s j r hst (by omega),
   fun st u f gul j r hst hj => h.nok st u f gul j r hst (by omega)⟩

/-- A tone that is no product is returned, for every goal (the converse of
`goalSemCM_ret`). -/
theorem returnsC_of_goalSemCM {K : Nat → Prop} {st : σ} {regs : Map (Option Noun)} {t tm : Trace} {je : Jmp} :
    ∀ (goal : CGoal S) (r : Tone), (∀ p, r ≠ Tone.zero p) →
      GoalSemCM lib O c gul Inv ν K st regs t tm je goal r → ReturnsC lib O c gul Inv ν st regs t je r
  | CGoal.done, _, _, H => H
  | CGoal.next _ _, Tone.zero p, hn, _ => absurd rfl (hn p)
  | CGoal.next _ _, Tone.one _, _, H => H
  | CGoal.next _ _, Tone.two _, _, H => H
  | CGoal.pick _ _, Tone.zero p, hn, _ => absurd rfl (hn p)
  | CGoal.pick _ _, Tone.one _, _, H => H
  | CGoal.pick _ _, Tone.two _, _, H => H

end

/-! ## The composition -/

-- BEGIN consNC_ok
/-- **A cons whose head calls, under a fork-free `%next`** (`binaryGV_ok`
with the head's `RunOKNV` replaced by `RunOKNC` and the tail a `TailNV`
whose need fits every subject, as the tail behind its block of `+past` is):
the copy block, the head's `GoalSemCM` (the call moves the oracle's state),
the tail's `SemNV` at the new state (the program agrees with the run at
every state), then the `con` block.  `+mink` on the cell formula runs the
head first, so the head's crash or block is the cons's (`minkF_consC`).
Generated by `tools/gen/conscall.py` from `binaryGV_ok`. -/
theorem consNC_ok {lib : Lib} {P : Noun → Prop} {fh ft : Noun} {pp q : Nomm} {sur : Sure S} {th : Jmp}
    {g0 g' g1 g2 g3 : Gen Map} {lp lq : Sure S} {o : Nat} {nexq nexp nex : NextL S}
    (hfh : ∃ a b, fh = C a b)
    (Mq : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {r : Tone}, P s → minkF lib gul n tm s ft = some r →
      r = toneOf tm (pureEval q s))
    (hg : GoalOK g0 (CGoal.next sur th)) (hpre : Ext g0 g') (hgr : GrowU g0 g') (hcnd : g'.cond = g0.cond)
    (hcb : CondBelow g0)
    (hlp : ∀ r, NMem lp.ned r → GMem (CGoal.next sur th) r ∨ (g0.re ≤ r ∧ r < g'.re))
    (hlq : ∀ r, NMem lq.ned r → GMem (CGoal.next sur th) r ∨ (g0.re ≤ r ∧ r < g'.re))
    (hpq : ∀ r, NMem lp.ned r → ¬ NMem lq.ned r)
    (hq : TailNV lib q g0.re lq (jmp0 o) g' g1 nexq)
    (hp : RunOKNC lib P fh pp lp nexq.th g1 g2 nexp)
    (hqt : ∀ s, FitsS nexq.laz.sure s)
    (cq : Clean nexq.laz.sure.ned) (cp : Clean nexp.laz.sure.ned)
    (hc : copyL nexp nexq.laz g2 = some (nex, g3))
    (hu : UpBelow g0) (d0 : g0.drop = false)
    (hnot : ∀ x y, ¬ FitsS lp x ∨ ¬ FitsS lq y → ¬ FitsS sur (C x y))
    (hfix : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g0.cond k) →
      ∀ k, g0.bo ≤ k → k < g'.bo → (HoonMap.get g'.blocks k).map (unproxyBlob cf) = HoonMap.get g'.blocks k)
    (hblk : ∀ (c : Straight Map), Agree c g0 g' →
      ∀ (σ : Type) (O : Oracle σ) st regs t gul x y, FitsS lp x → FitsS lq y → HoldsN lp.ned regs x →
        HoldsN lq.ned regs y →
          GoalSem lib O c gul st (Keep g0 g' (CGoal.next sur th)) regs t (jmp0 o) (CGoal.next sur th)
            (some (C x y))) :
    RunOKNC lib P (C fh ft) (Nomm.cons pp q) sur th g0 g3 nex := by
  -- the labels of the two runs are apart
  have lq' : ∀ e ∈ entries nexq.laz, g'.bo ≤ e.1 ∧ e.1 < g1.bo := fun e he =>
    ⟨(hq.labs e he).1, Nat.lt_of_le_of_lt (hq.labs e he).2.1 hq.hi⟩
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
  have gm : ∀ r, GMem (CGoal.next sur th : CGoal S) r → r < g0.re := fun r hr => hg.2 r hr
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
  have Dc := copy_down (goal := CGoal.next sur th) hcp hp.lo hp.hi d2 (Nat.le_trans hp.lo (Nat.le_of_lt hp.hi))
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
    nec := fun s hs => ?_
    ncond := fun r hr => ?_
    econd := fun e he r hr => ?_
    sem := fun cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn => ?_ }
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
    · refine ⟨(hp.eregs e a).1, fun r hr => ⟨?_, by have := ((hp.eregs e a).2 r hr).2; omega⟩⟩
      rcases ((hp.eregs e a).2 r hr).1 with b | b
      · rcases hlp r b with b' | ⟨b', _⟩
        · exact Or.inl b'
        · exact Or.inr b'
      · exact Or.inr (by omega)
    · refine ⟨(hq.eregs e a).1, fun r hr => ⟨?_, by have := ((hq.eregs e a).2 r hr).2; omega⟩⟩
      rcases ((hq.eregs e a).2 r hr).1 with b | b
      · rcases hlq r b with b' | ⟨b', _⟩
        · exact Or.inl b'
        · exact Or.inr b'
      · exact Or.inr b
  · show g0.bo ≤ e.1 ∧ e.1 < n.th.there ∧ _
    rw [eth]
    simp only [jmp0]
    rcases (memN e).mp he with a | a
    · obtain ⟨x, y, th, z⟩ := hp.labs e a
      have := hp.hi
      exact ⟨by omega, by omega, th, by rw [hp3.2.2.2 _ (by omega)]; exact z⟩
    · obtain ⟨x, y, th, z⟩ := hq.labs e a
      have := hq.hi
      have := hq.lo
      exact ⟨by omega, by omega, th, by rw [Eq3.2.2.2 _ (by omega)]; exact z⟩
  · rw [((entries_side_perm _ _ _).map Prod.fst).nodup_iff, List.map_append, List.nodup_append]
    refine ⟨hp.nodup, hq.nodup, fun a ha b hb => ?_⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp hb
    have := lp' e he; have := lq' e' he'; omega
  · have a : ¬ FitsS nexp.laz.sure s := fun a => hs ((CF s).mpr ⟨a, hqt s⟩)
    rw [pureEval_cons, hp.nec s a]
    rfl
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
      rw [(ag st).1 k (by omega) h1 (fun hm => by have := labN k hm; omega)]
      exact fixC cf hcf k h0 h1
    obtain ⟨R1, hs1, hs1', u1, e1⟩ := CB d2 c agC lib σ O st regs t gul s hh
    have hned2 : ∀ r, NMem ned r → g2.re ≤ r := fun r hr => by have := hned r hr; omega
    have hned1 : ∀ r, NMem ned r → g1.re ≤ r := fun r hr => by have := hned r hr; omega
    have hn1 : HoldsN ned R1 s0 := HoldsN.agree _ (fun r hr => u1 r (fun hm => by
      have := lowP r hm; have := hned r hr; omega) (fun hm => by have := lowQ r hm; have := hned r hr; omega)) hn
    have agP : ∀ st' : σ, AgreeU lib O c gul st' t cf ned g1 g2 nexp.laz s0 s := fun st' =>
      (ag st').part (by omega) hp3 (fun e he => (memN e).mpr (Or.inl he))
        (fun k h0 h1 hm => by
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
          rcases (memN e).mp he with a | a
          · exact List.mem_map_of_mem a
          · have := lq' e a; omega)
        (fun e he => (lp' e he).2)
    have agQ : ∀ st' : σ, AgreeU lib O c gul st' t cf ned g' g1 nexq.laz s0 s := fun st' =>
      (ag st').part bo01 Eq3 (fun e he => (memN e).mpr (Or.inr he))
        (fun k h0 h1 hm => by
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
          rcases (memN e).mp he with a | a
          · have := lp' e a; omega
          · exact List.mem_map_of_mem a)
        (fun e he => (lq' e he).2)
    have agQ0 : Agree c g0 g' := fun k h0 h1 => by
      rw [(ag st).1 k h0 (by omega) (fun hm => by have := labN k hm; omega), E'3.2.2.2 k h1]
      exact hfix cf hcf0 k h0 h1
    -- the kept registers
    have nlpK : ∀ r, (r < g0.re ∨ NMem ned r) → ¬ NMem sur.ned r → ¬ NMem lp.ned r := fun r k1 k2 hm => by
      rcases hlp r hm with b | ⟨b, b'⟩
      · exact k2 b
      · rcases k1 with k1 | k1
        · omega
        · have := hned r k1; omega
    have keep1 : ∀ r, (r < g0.re ∨ NMem ned r) → ¬ NMem sur.ned r →
        SkaModel.read r R1 = SkaModel.read r regs := by
      intro r k1 k2
      refine u1 r (fun hm => ?_) (fun hm => ?_)
      · rcases mp r hm with a | ⟨a, a'⟩
        · exact nlpK r k1 k2 a
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
    -- the head runs first
    obtain ⟨n', rh, hn', hmh, hr⟩ := minkF_consC hfh Mq hs hm
    have Hp := hp.sem cf hcf2 c ned σ Inv ν O n' gul hS (oracleFwd_le hF (Nat.le_of_lt hn')) st t tm
      s0 s rh hI htr hs hmh agP hned2 R1 hs1 hn1
    rcases hr with ⟨hnz, rfl⟩ | ⟨x, rfl, hq'⟩
    · exact goalSemCM_ret _ _ hnz (returnsC_step (Needs.le_refl _) e1 (returnsC_of_goalSemCM _ _ hnz Hp))
    by_cases fx : FitsS lp x
    · obtain ⟨st', R2, hI', hν, hl2, k2, e2⟩ := Hp.1 fx
      have htr' := frames_mono hν htr
      have hq2 : HoldsS nexq.laz.sure R2 s := by
        refine ⟨HoldsN.agree _ (fun r hr => k2 r ⟨Or.inl (lowQ r hr), ?_⟩) hs1'.1, hs1'.2⟩
        intro hm
        rcases mq r hr with a | ⟨a, _⟩
        · exact hpq r hm a
        · have := lpl r hm; omega
      have hn2 : HoldsN ned R2 s0 := HoldsN.agree _ (fun r hr => k2 r ⟨Or.inr hr, fun hm => by
        have := lpl r hm; have := hned r hr; omega⟩) hn1
      have keep2 : ∀ r, (r < g0.re ∨ NMem ned r) ∧ ¬ NMem sur.ned r →
          SkaModel.read r R2 = SkaModel.read r regs := fun r hk => by
        obtain ⟨k1, k2'⟩ := hk
        rw [k2 r ⟨k1.imp (fun h => by omega) id, nlpK r k1 k2'⟩, keep1 r k1 k2']
      have Hq := hq.sem cf hcf1 c ned σ O st' t gul s0 s (agQ st') hned1 R2 hq2 hn2
      rcases hq' with ⟨eq, rfl⟩ | ⟨y, eq, rfl⟩
      · rw [eq] at Hq
        exact ⟨Tone.two t, st', hI', hν, e1.trans (e2.trans Hq), ToneRel.two htr'⟩
      rw [eq] at Hq
      by_cases fy : FitsS lq y
      · obtain ⟨R3, hq3, k3, e3⟩ := Hq.1 fy
        have hl3 : HoldsN lp.ned R3 x :=
          HoldsN.agree _ (fun r hr => k3 r ⟨Or.inl (lpl r hr), hpq r hr⟩) hl2
        have B := hblk c agQ0 σ O st' R3 t gul x y fx fy hl3 hq3
        have G : GoalSem lib O c gul st' (fun r => (r < g0.re ∨ NMem ned r) ∧ ¬ NMem sur.ned r) R2 t nexq.th
            (CGoal.next sur th) (some (C x y)) := by
          refine GoalSem.transfer e3 (fun r hk => ?_)
            (GoalSem.mono (fun r ⟨k1, k2⟩ => ⟨k1.imp id (fun h => by have := hned r h; omega), k2⟩) B)
          obtain ⟨k1, k2'⟩ := hk
          have nlq : ¬ NMem lq.ned r := fun hm => by
            rcases hlq r hm with b | ⟨b, b'⟩
            · exact k2' b
            · rcases k1 with k1 | k1
              · omega
              · have := hned r k1; omega
          exact k3 r ⟨k1.imp (fun h => by omega) id, nlq⟩
        exact goalSemCM_step hν keep2 (e1.trans e2) _ _ (goalSemC_of_goalSem hI' htr' _ _ G)
      · exact ⟨fun hf => absurd hf (hnot x y (Or.inr fy)),
          fun _ => ⟨Tone.two t, st', hI', hν, e1.trans (e2.trans (Hq.2 fy)), ToneRel.two htr'⟩⟩
    · have Rc := returnsC_step (Needs.le_refl _) e1 (Hp.2 fx)
      rcases hq' with ⟨_, rfl⟩ | ⟨y, _, rfl⟩
      · exact Rc
      · exact ⟨fun hf => absurd hf (hnot x y (Or.inl fx)), fun _ => Rc⟩
-- END consNC_ok

/-! ## The cons with the call in its head, from the run -/

/-- The sure need of the indirect call's run is clean (`+copy` of two clean
needs). -/
theorem indirect_clean {lib : Lib} {p q : Nomm} (up : UOK (S := S) (Map := Map) lib p)
    (uq : UOK (S := S) (Map := Map) lib q) {env : CallEnv} {sup : Option Nomm} {goal : CGoalL S}
    {region : List Nat} {g0 g' : Gen Map} {nex : NextL S}
    (h : runLC env sup (Nomm.n2 p q Option.none) goal region g0 = some (nex, g')) : Clean nex.laz.sure.ned := by
  obtain ⟨nex0, g1, out, pro, g2, o, g3, nexF, g4, nexF', g5, nexS, g6, h1, h2, h3, h4, h5, h6, h7⟩ :=
    runLC_n2_none h
  rw [runLC_eq env q (Nomm.noCall_of_pure q uq.pure)] at h4
  rw [pastL_pure _ _ up.pure, pure_apply] at h5
  simp only [Option.some.injEq, Prod.mk.injEq] at h5
  obtain ⟨rfl, rfl⟩ := h5
  rw [runLC_eq env p (Nomm.noCall_of_pure p up.pure)] at h6
  exact clean_copyL h7 (up.clean (goal := CGoal.next (lazyReg g2.re) _) trivial h6)
    (uq.clean (goal := CGoal.next (lazyReg (g2.re + 1)) _) trivial h4)

/-- **The cons `[[2 b c] d]` under a fork-free `%next sur th` meets
`RunOKNC`** for the cell formula `[fh ft]`, with `b`, `c`, `d` meeting `UOK`,
`fh` a formula with `MinkN2` (so any `Annot` of `[2 b c]` but the bare ones)
and `ft` one whose `+mink` is `d`'s value (`Mq`), from any state with the
hypotheses of `OKNV`.  The run (`consNV_body`'s steps) is `+split`, the tail
`d`, `+past` behind the call (`pastL_hinted`: nothing, or the block of
`tailNV_past`), the call (`indirect_runN`), `+copy`; `consNC_ok` composes. -/
theorem consCH_runN (lib : Lib) {b c d : Nomm} (ub : UOK (S := S) (Map := Map) lib b)
    (uc : UOK (S := S) (Map := Map) lib c) (ud : UOK (S := S) (Map := Map) lib d)
    {P : Noun → Prop} {fh ft : Noun} (M : MinkN2 lib P fh b c) (hfh : ∃ x y, fh = C x y)
    (Mq : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {r : Tone}, P s → minkF lib gul n tm s ft = some r →
      r = toneOf tm (pureEval d s))
    (hcount : sixCount b + sixCount c + sixCount d ≤ 255) {env : CallEnv} {sup : Option Nomm}
    {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (hj : GJ g0.bo (CGoal.next sur th)) (hth : th.args = []) (hok : GoalOK g0 (CGoal.next sur th))
    (hcl : Clean sur.ned) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false)
    (hu : UpBelow g0) (hcl0 : Clear g0) (hcb : CondBelow g0)
    (hkg : ∀ r, NMem sur.ned r → HoonMap.get g0.cond r = Option.none)
    (h : runLC env sup (Nomm.cons (Nomm.n2 b c Option.none) d) (CGoalL.next (ofSure sur) th) region g0 =
      some (nex, g1)) :
    RunOKNC lib P (C fh ft) (Nomm.cons (Nomm.cons b c) d) sur th g0 g1 nex := by
  have e : (runLC env sup (Nomm.cons (Nomm.n2 b c Option.none) d) (CGoalL.next (ofSure sur) th) region :
      CM Map (NextL S)) = (do
        let (hed, tel, o) ← splitL ⟨ofSure sur, th⟩
        let nexh ← pastL env.cod ⟨hed, jmp0 o⟩ d region
        let nex2 ← runLC env sup d (CGoalL.next tel nexh.th) region
        let nex2 ← pastL env.cod nex2 (Nomm.n2 b c Option.none) region
        let nex1 ← runLC env sup (Nomm.n2 b c Option.none) (CGoalL.next nexh.laz nex2.th) region
        copyL nex1 nex2.laz) := rfl
  rw [e] at h
  obtain ⟨⟨hed', tel', o⟩, g2x, h2, h⟩ := bind_some h
  rw [splitL_mk, map_apply] at h2
  obtain ⟨⟨⟨hed, tel, o'⟩, g2⟩, hs2, e2⟩ := Option.map_eq_some_iff.mp h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := e2
  clear h2
  simp only at h
  obtain ⟨nexh, g2', hph, h⟩ := bind_some h
  rw [pastL_mk _ _ _ ud.pure, pure_apply] at hph
  simp only [Option.some.injEq, Prod.mk.injEq] at hph
  obtain ⟨rfl, rfl⟩ := hph
  obtain ⟨nex2, g3, h3, h⟩ := bind_some h
  rw [runLC_eq env d (Nomm.noCall_of_pure d ud.pure)] at h3
  obtain ⟨nex2', g3', hp2, h⟩ := bind_some h
  obtain ⟨nex1, g4, h4, hcp⟩ := bind_some h
  obtain ⟨eo, E2, _, Mh, Mt, SP⟩ := split_ok hs2
  obtain ⟨Dh, Dt, Dht, F, B⟩ := SP hok.1 hok.2
  obtain ⟨G2, eo', lt2, _⟩ := split_down hs2 hj.1 hj.2 d0
  simp only at eo'
  subst eo
  have CS := clean_split hs2 hcl
  simp only at CS
  have c2 : g2.cond = g0.cond := (kc_split _).keep _ _ _ hs2
  have d2 : g2.drop = false := E2.2.2.1.trans d0
  have u2 : UpBelow g2 := (G2.toU hu).up hu
  have lt2' : ∀ (n : Need), (∀ y, NMem n y → NMem sur.ned y ∨ (g0.re ≤ y ∧ y < g2.re)) →
      ∀ y, NMem n y → y < g2.re := fun n M y hy => by
    rcases M y hy with a | ⟨_, a⟩
    · exact Nat.lt_of_lt_of_le (hok.2 y a) E2.1
    · exact a
  have G2U : GrowU g0 g2 := G2.toU hu
  have cl2 : Clear g2 := hcl0.growU G2U
  have cf2 : CondFresh g0 g2 := condFresh_of_eq E2.1 c2
  have cb2 : CondBelow g2 := cf2.below hcb
  have nk2 : ∀ (n : Need), (∀ y, NMem n y → NMem sur.ned y ∨ (g0.re ≤ y ∧ y < g2.re)) →
      ∀ y, NMem n y → HoonMap.get g2.cond y = Option.none := fun n M y hy => by
    rw [c2]
    rcases M y hy with a | ⟨a, _⟩
    · exact hkg y a
    · exact condBelow_none hcb a
  have Rq := ud.next (sur := tel) (th := jmp0 g0.bo) ⟨b0, by simp only [jmp0]; omega⟩ rfl ⟨Dt, lt2' _ Mt⟩ CS.2
    (by omega) (by omega) d2 u2 cl2 cb2 (nk2 _ Mt) h3
  have d3 : g3.drop = false := Rq.ext.2.2.1.trans d2
  have u3 : UpBelow g3 := Rq.grow.up u2
  have AS : AboveIn (fun r => HoonMap.get g0.cond r = Option.none) g0.bo g2 :=
    (keepsA_split (P := fun r => HoonMap.get g0.cond r = Option.none) d0 hkg (jmpIn_nil hth)
      (fun r hr => condBelow_none hcb hr) hs2).1.ab _ (aboveIn_start _ g0)
  have BS : BelowIn g0.bo g2 :=
    (keeps_split d0 (fun r hr => hok.2 r hr) (jmpIn_nil hth) hs2).1.bel _ (belowIn_start g0)
  have hfix : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g2.re → HoonMap.get cf k = HoonMap.get g0.cond k) →
      ∀ k, g0.bo ≤ k → k < g2.bo → (HoonMap.get g2.blocks k).map (unproxyBlob cf) = HoonMap.get g2.blocks k := by
    intro cf hcf k h0 h1
    have u0 : ∀ x, x < g2.re → unproxy cf x = unproxy g0.cond x := unproxy_agree (fun k hk => hcf k hk)
    have u1 : ∀ x, HoonMap.get g0.cond x = Option.none → unproxy g0.cond x = id x := fun x hx => unproxy_none hx
    cases hg : HoonMap.get g2.blocks k with
    | none => rfl
    | some b =>
      simp only [Option.map_some]
      rw [unproxyBlob, renBlob_congr u0 (BS k b h0 h1 hg), renBlob_congr u1 (AS k b h0 h1 hg), renBlob_id]
  have hblk : ∀ (c : Straight Map), Agree c g0 g2 →
      ∀ (σ : Type) (O : Oracle σ) st regs t gul x y, FitsS hed x → FitsS tel y → HoldsN hed.ned regs x →
        HoldsN tel.ned regs y →
          GoalSem lib O c gul st (Keep g0 g2 (CGoal.next sur th)) regs t (jmp0 g0.bo) (CGoal.next sur th)
            (some (C x y)) := by
    intro c hc σ O st regs t gul x y fx fy hx hy
    refine ⟨fun _ => ?_, fun hn => absurd ((F x y).mpr ⟨fx, fy⟩) hn⟩
    obtain ⟨R', hl, u, e⟩ := B d0 c hc lib σ O st t regs x y gul hx hy
    exact ⟨R', hl, fun r ⟨_, k⟩ => u r k, e⟩
  have hnot : ∀ x y, ¬ FitsS hed x ∨ ¬ FitsS tel y → ¬ FitsS sur (C x y) := fun x y hn hf => by
    rcases hn with a | a
    · exact a ((F x y).mp hf).1
    · exact a ((F x y).mp hf).2
  have hkp : ∀ y, NMem hed.ned y → HoonMap.get g3.cond y = Option.none := fun y hy => by
    rw [Rq.cfr.get_lt (lt2' _ Mh y hy)]; exact nk2 _ Mh y hy
  rcases pastL_hinted (show hinted env.cod (Nomm.n2 b c Option.none) = some true from rfl) hp2 with
    ⟨x1, x2, en, es, _⟩ | ⟨x1, x2⟩
  · -- the tail's need asks nothing: no block of `+past`
    subst nex2' g3'
    have Rp := indirect_runN lib ub uc M (by omega) (sur := hed) (th := nex2.th) ⟨Rq.lo, Rq.hi⟩
      (nextArgs_nil Rq.ent rfl) ⟨Dh, fun y hy => Nat.lt_of_lt_of_le (lt2' _ Mh y hy) Rq.ext.1⟩
      (by have := Rq.lo; have := Rq.hi; omega) d3 u3 (cl2.growU Rq.grow) (Rq.cfr.below cb2) hkp h4
    exact consNC_ok hfh Mq hok E2 G2U c2 hcb Mh Mt Dht (TailNV.ofRun Rq E2.1) Rp
      (fun s => fitsS_trivial en es s) (by rw [en]; trivial) (indirect_clean ub uc h4) hcp hu d0 hnot hfix hblk
  · -- the tail's need parked behind the block of `+past`
    subst nex2' g3'
    have T := tailNV_past Rq E2.1 (lt2' _ Mt) d3 u3 region
    have G3 : GrowU g3 ((g3.emitted ⟨[], [], Termin.hop nex2.th⟩).tagged g3.bo region) :=
      (growU_emit (b := ⟨[], [], Termin.hop nex2.th⟩) (fun j hj => by
        simp only [finJumps, List.mem_singleton] at hj; subst hj; exact ⟨Rq.lo, Rq.hi⟩) u3).trans
        (growU_tagged _ _ _)
    have Rp := indirect_runN lib ub uc M (by omega) (sur := hed) (th := jmp0 g3.bo)
      ⟨by have := Rq.lo; have := Rq.hi; simp only [jmp0]; omega, by simp [jmp0, Gen.emitted]⟩ rfl
      ⟨Dh, fun y hy => by have := lt2' _ Mh y hy; have := Rq.ext.1; simp [Gen.emitted]; omega⟩
      (by simp [Gen.emitted]) (by simp [Gen.emitted, d3]) (G3.up u3) ((cl2.growU Rq.grow).growU G3)
      (fun k hk => by
        rw [tagged_cond] at hk
        have := (Rq.cfr.below cb2) k hk
        simp [Gen.emitted]; omega)
      (fun y hy => by rw [tagged_cond]; exact hkp y hy) h4
    exact consNC_ok hfh Mq hok E2 G2U c2 hcb Mh Mt Dht T Rp (fun s => fitsS_bunt s) trivial
      (indirect_clean ub uc h4) hcp hu d0 hnot hfix hblk

end Comp
end SkaModel
end Formalization
