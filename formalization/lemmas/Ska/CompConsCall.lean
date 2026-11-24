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
  eregs : ∀ e ∈ entries nex.laz, Distinct e.2.sure.ned ∧ ∀ r, NMem e.2.sure.ned r → bot ≤ r ∧ r < g1.re
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
    fun e he => ⟨(R.eregs e he).1, fun r hr => ⟨by have := ((R.eregs e he).2 r hr).1; omega,
      ((R.eregs e he).2 r hr).2⟩⟩,
    fun e he => ⟨(R.labs e he).1, Nat.le_of_lt (R.labs e he).2.1, (R.labs e he).2.2⟩,
    R.nodup, R.nec, R.ncond, R.econd, R.sem⟩

/-- **The tail with its block of `+past` meets `TailNV`**: the bond's
block fills the tail's need from the subject (`FillSem` of `AgreeU`), or
crashes where the subject does not fit it, which the tail's `nec` makes the
tail's crash or a value that does not fit the goal. -/
theorem tailNV_past {lib : Lib} {nm : Nomm} {lo : Nat} {sur : Sure S} {o : Nat} {g0 g1 : Gen Map}
    {nex : NextL S} (R : RunOKNV (Map := Map) lib nm sur (jmp0 o) g0 g1 nex) (hlo : lo ≤ g0.re)
    (hsur : ∀ r, NMem sur.ned r → lo ≤ r ∧ r < g0.re) (d1 : g1.drop = false) (u1 : UpBelow g1)
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
      rcases R.regs r hr with b | ⟨_, b⟩
      · have := hsur r b; omega
      · omega
    · exact ⟨(R.eregs e a).1, fun r hr => by
        have := (R.eregs e a).2 r hr; simp only [Gen.emitted, tagged_re]; omega⟩
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

end Comp
end SkaModel
end Formalization
