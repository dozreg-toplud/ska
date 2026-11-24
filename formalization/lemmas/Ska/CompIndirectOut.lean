import lemmas.Ska.CompIndirectNext
import lemmas.Ska.CompIndirectFwd

/-!
# The block `out` of `+kerf` under a fork-free `%next`

README Gaps 12.13 (seventeenth session).  Under a goal `%next (ofSure sur)
th` the case `%2` of `runLC` makes the block `out = [hop th]` and `+kern`
puts in front of it the ops of `+kern-need` from the product register
`pro`.  The lazy need has no entries, so `+kern` walks the block `out` only,
takes `pro` itself as its source and makes no proxy.

* `runs_keep`: ops of `+kern-need` (moves, `cel`, `hed`, `tal`: `KOp`)
  change no register they do not write (`Runs` is an equation of the
  interpreter, so the registers after the ops are read through a `%don`).
  `KernSemS` only keeps the registers below the ops' fresh registers; a
  parent needs more, the registers of `ned` (the subject whole, which the
  lazy blocks read) lie above every register of the run.
* `kernLoop_kop`: the ops of `+kern-need` are `KOp`.
* `outGoal_next_of_fill`: a block `[ops; hop th]` whose ops fill `sur` from
  `pro` and keep `K` meets `OutGoal` for `%next sur th`.
* `kerf_ofSure`: what `+kerf` makes for a fork-free `%next`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Ops that change only what they write -/

/-- The ops of `+kern-need`. -/
def KOp : Pole → Prop
  | Pole.mov _ _ => True
  | Pole.hed _ _ => True
  | Pole.tal _ _ => True
  | Pole.cel _ => True
  | _ => False

section
variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun}

theorem kop_exec {p : Pole} (hp : KOp p) (st : σ) (R : Map (Option Noun)) (t : Trace) :
    execPole lib O gul st p R t =
      (localPole lib gul p R t).map fun (ton, regs', trace') => (ton, regs', trace', st) := by
  cases p <;> first | rfl | exact hp.elim

theorem kop_local {p : Pole} (hp : KOp p) (R : Map (Option Noun)) (t : Trace) :
    (∃ R1, localPole lib gul p R t = some (Tone.zero (A 0), R1, t)) ∨
    localPole lib gul p R t = some (Tone.two t, R, t) ∨ localPole lib gul p R t = Option.none := by
  cases p with
  | mov s d =>
    cases e : move s d R with
    | none => exact Or.inr (Or.inr (by simp [localPole, e]))
    | some R1 => exact Or.inl ⟨R1, by simp [localPole, e]⟩
  | hed s d =>
    cases e : SkaModel.read s R with
    | none => exact Or.inr (Or.inr (by simp [localPole, e]))
    | some v =>
      cases v with
      | atom a => exact Or.inr (Or.inr (by simp [localPole, e]))
      | cell x y => exact Or.inl ⟨store d x R, by simp [localPole, e]⟩
  | tal s d =>
    cases e : SkaModel.read s R with
    | none => exact Or.inr (Or.inr (by simp [localPole, e]))
    | some v =>
      cases v with
      | atom a => exact Or.inr (Or.inr (by simp [localPole, e]))
      | cell x y => exact Or.inl ⟨store d y R, by simp [localPole, e]⟩
  | cel s =>
    cases e : SkaModel.read s R with
    | none => exact Or.inr (Or.inr (by simp [localPole, e]))
    | some v =>
      cases v with
      | atom a => exact Or.inr (Or.inl (by simp [localPole, e]))
      | cell x y => exact Or.inl ⟨R, by simp [localPole, e]⟩
  | _ => exact hp.elim

theorem execBlob_imm_don (st : σ) (R : Map (Option Noun)) (t : Trace) (n : Noun) (x : Nat) :
    execBlob lib O c gul st R t ⟨[], [Pole.imm n x], Termin.don x⟩ [] = some (Tone.zero n, st) := by
  rw [execBlob_cons]
  simp [execPole, localPole, execBlob_don', read_store_eq]

/-- The code after some ops cannot be the same whatever follows them. -/
theorem execBlob_not_const {st : σ} {R : Map (Option Noun)} {t : Trace} {X : Option (Tone × σ)}
    (h : ∀ (rest : List Pole) (fin : Termin), execBlob lib O c gul st R t ⟨[], rest, fin⟩ [] = X) : False := by
  have h0 := h [Pole.imm (A 0) 0] (Termin.don 0)
  have h1 := h [Pole.imm (A 1) 0] (Termin.don 0)
  rw [execBlob_imm_don] at h0 h1
  rw [← h0] at h1
  simp at h1

/-- **Ops of `+kern-need` keep every register they do not write.** -/
theorem runs_keep {st : σ} {t : Trace} : ∀ (A : List Pole) (R R' : Map (Option Noun)), (∀ p ∈ A, KOp p) →
    Runs lib O c gul st t A R R' → ∀ x, (∀ p ∈ A, x ∉ poleWr p) → SkaModel.read x R' = SkaModel.read x R
  | [], R, R', _, h, x, _ => by
    have e := h [] (Termin.don x)
    simp only [List.nil_append, execBlob_don'] at e
    cases h1 : SkaModel.read x R <;> cases h2 : SkaModel.read x R' <;> simp_all
  | p :: A, R, R', hk, h, x, hw => by
    have hp : KOp p := hk p List.mem_cons_self
    rcases kop_local (lib := lib) (gul := gul) hp R t with ⟨R1, e⟩ | e | e
    · have R1' : Runs lib O c gul st t A R1 R' := fun rest fin => by
        have := h rest fin
        rw [List.cons_append, execBlob_cons, kop_exec hp, e] at this
        exact this
      have k1 := runs_keep A R1 R' (fun q hq => hk q (List.mem_cons_of_mem _ hq)) R1' x
        (fun q hq => hw q (List.mem_cons_of_mem _ hq))
      have k2 := localPole_frame lib gul e x (hw p List.mem_cons_self)
      rw [k1]; unfold SkaModel.read; rw [k2]
    · exact (execBlob_not_const (X := some (Tone.two t, st)) fun rest fin => by
        rw [← h rest fin, List.cons_append, execBlob_cons, kop_exec hp, e]; rfl).elim
    · exact (execBlob_not_const (X := Option.none) fun rest fin => by
        rw [← h rest fin, List.cons_append, execBlob_cons, kop_exec hp, e]; rfl).elim

end

/-! ## The ops of `+kern-need` are `KOp` -/

theorem kernBoth_kop {r d : Nat} {kh kt : Nat → List Pole → CM Map (List Pole)}
    (sh : ∀ r' acc (g g' : Gen Map) ops, kh r' acc g = some (ops, g') → (∀ p ∈ acc, KOp p) → ∀ p ∈ ops, KOp p)
    (st : ∀ r' acc (g g' : Gen Map) ops, kt r' acc g = some (ops, g') → (∀ p ∈ acc, KOp p) → ∀ p ∈ ops, KOp p)
    {acc : List Pole} {g g' : Gen Map} {ops : List Pole} (hk : kernBoth r d kh kt acc g = some (ops, g'))
    (ha : ∀ p ∈ acc, KOp p) : ∀ p ∈ ops, KOp p := by
  unfold kernBoth at hk
  obtain ⟨rt, g1, h1, hk⟩ := bind_some hk
  obtain ⟨o1, g2, h2, hk⟩ := bind_some hk
  have A2 := st _ _ _ _ _ h2 ha
  obtain ⟨rh, g3, h3, hk⟩ := bind_some hk
  obtain ⟨o2, g4, h4, hk⟩ := bind_some hk
  have A2' : ∀ p ∈ (if o1 ≠ acc then Pole.tal d rt :: o1 else o1), KOp p := by
    split
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · trivial
      · exact A2 p hp
    · exact A2
  have A4 := sh _ _ _ _ _ h4 A2'
  by_cases e : r = d
  · rw [if_pos e] at hk; cases hk
  rw [if_neg e] at hk
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  intro p hp
  simp only [List.mem_cons] at hp
  rcases hp with rfl | rfl | hp
  · trivial
  · trivial
  · by_cases e2 : o2 ≠ (if o1 ≠ acc then Pole.tal d rt :: o1 else o1)
    · rw [if_pos e2] at hp
      rcases List.mem_cons.mp hp with rfl | hp
      · trivial
      · exact A4 p hp
    · rw [if_neg e2] at hp; exact A4 p hp

theorem kernLoop_kop : ∀ (tgt : Need) (r : Nat) (acc : List Pole) (g g' : Gen Map) (ops : List Pole),
    kernLoop r tgt acc g = some (ops, g') → (∀ p ∈ acc, KOp p) → ∀ p ∈ ops, KOp p := by
  intro tgt
  induction tgt with
  | none =>
    intro r acc g g' ops h ha
    simp only [kernLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ha
  | this d =>
    intro r acc g g' ops h ha
    simp only [kernLoop] at h
    by_cases e : r = d
    · rw [if_pos e] at h; cases h
    rw [if_neg e] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · trivial
    · exact ha p hp
  | pair p q ihp ihq =>
    intro r acc g g' ops h ha
    simp only [kernLoop] at h
    obtain ⟨rn, g1, _, h⟩ := bind_some h
    exact kernBoth_kop (fun r' acc g g' ops h => ihp r' acc g g' ops h)
      (fun r' acc g g' ops h => ihq r' acc g g' ops h) h ha
  | both d h t ihh iht =>
    intro r acc g g' ops hk ha
    simp only [kernLoop] at hk
    exact kernBoth_kop (fun r' acc g g' ops h' => ihh r' acc g g' ops h')
      (fun r' acc g g' ops h' => iht r' acc g g' ops h') hk ha

theorem poleWr_sub {p : Pole} {r : Nat} (h : r ∈ poleWr p) : r ∈ poleRegs p := by
  cases p <;> simp_all [poleWr, poleRegs]

/-! ## What `+kerf` makes for a fork-free `%next` -/

/-- **`+kerf` under a fork-free `%next sur th`**: the block `out` is the
next label, the product register `pro` the next register, `+kern` makes no
proxy (the lazy need has no entries and `out` is its own block), and the
block `out` is `[A; hop th]` with `A` the ops of `+kern-need`, which mention
`pro`, the registers of `sur` and fresh registers only, and fill `sur`
from `pro`. -/
theorem kerf_ofSure {sur : Sure S} {th : Jmp} {g g' : Gen Map} {out pro : Nat}
    (h : kerf (⟨ofSure sur, th⟩ : NextL S) g = some ((out, pro), g')) (hd : g.drop = false) :
    out = g.bo ∧ pro = g.re ∧ g'.bo = g.bo + 1 ∧ g'.drop = g.drop ∧ g'.cond = g.cond ∧ g'.tags = g.tags ∧
    g.re + 1 ≤ g'.re ∧ ∃ A : List Pole,
      (∀ k, HoonMap.get g'.blocks k = if k = g.bo then some ⟨[], A, Termin.hop th⟩ else HoonMap.get g.blocks k) ∧
      (∀ p ∈ A, KOp p) ∧ RegsIn (fun x => x = g.re ∨ NMem sur.ned x ∨ (g.re + 1 ≤ x ∧ x < g'.re)) A ∧
      (Distinct sur.ned → (∀ x, NMem sur.ned x → x < g.re) → KernSemS (Map := Map) sur g.re (g.re + 1) A) := by
  unfold kerf at h
  obtain ⟨o', ge, he, h⟩ := bind_some h
  rw [emit_apply] at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨r, g4, h3, h4⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
  rw [kern_eq] at h3
  obtain ⟨r', g1, h1, h3⟩ := bind_some h3
  rw [re_apply] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  obtain ⟨gg, g2, h2, h3⟩ := bind_some h3
  rw [get_apply] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  have hde : (g.emitted ⟨[], [], Termin.hop th⟩).drop = false := hd
  simp only at h3
  rw [if_neg (show ¬ ((g.emitted ⟨[], [], Termin.hop th⟩).drop = true) by simp [hde])] at h3
  obtain ⟨u, g3, h5, h6⟩ := bind_some h3
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h6
  obtain ⟨e6, rfl⟩ := h6
  subst e6
  simp only [ofSure, walkLazy] at h5
  obtain ⟨u1, g5, h7, h8⟩ := bind_some h5
  simp only [List.isEmpty_nil, Bool.and_self, ↓reduceIte, pure_apply, Option.some.injEq,
    Prod.mk.injEq] at h8
  obtain ⟨-, rfl⟩ := h8
  -- the gate at `out`
  unfold kernGate at h7
  obtain ⟨ned, g6, h9, h7⟩ := bind_some h7
  have L := sureRequireLook_spec h9
  obtain ⟨kk, e1⟩ := L.gen
  subst e1
  have lk : g.re + 1 ≤ kk := L.le
  have eb : ∀ k, HoonMap.get (g.emitted ⟨[], [], Termin.hop th⟩).blocks k =
      if k = g.bo then some ⟨[], [], Termin.hop th⟩ else HoonMap.get g.blocks k := fun k => by
    simp only [Gen.emitted, hd, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]
  by_cases en : ned = Need.none
  · rw [if_pos en] at h7
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h7
    obtain ⟨-, rfl⟩ := h7
    subst en
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, lk, [], fun k => eb k, fun _ h => absurd h List.not_mem_nil,
      RegsIn.nil _, fun _ _ => ?_⟩
    intro lib σ O c gul st t R v _
    exact ⟨fun _ => ⟨R, Runs.nil R, holdsS_of_sure L trivial, fun _ _ _ => rfl⟩,
      fun nf => absurd ((fits_sure L v).mp trivial) nf⟩
  rw [if_neg en] at h7
  obtain ⟨src, g7, hs, h7⟩ := bind_some h7
  simp only [↓reduceIte, pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  rw [show noSoft g.bo = false from rfl] at h7
  simp only [Bool.false_eq_true, ↓reduceIte] at h7
  obtain ⟨ops, g8, h10, h11⟩ := bind_some h7
  obtain ⟨Ak, hA, K⟩ := kernLoop_spec ned _ [] _ g8 ops h10
  simp only [List.append_nil] at hA
  rw [hA] at h10 h11
  have kop := kernLoop_kop ned _ [] _ g8 Ak h10 (fun _ h => absurd h List.not_mem_nil)
  obtain ⟨n, rfl⟩ := K.gen
  have l3 : kk ≤ n := K.le
  have RI := kernLoop_lt (fun x => x = g.re ∨ NMem sur.ned x ∨ (g.re + 1 ≤ x ∧ x < n)) ned g.re [] _ _ Ak h10
    (Or.inl rfl) (fun x hx => by
      rcases L.mem x hx with h' | ⟨a, b⟩
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr ⟨a, by simp only at b; omega⟩))
    (fun x a b => Or.inr (Or.inr ⟨by simp only at a; omega, b⟩)) (RegsIn.nil _)
  obtain ⟨b, hb, rfl⟩ := addOps_spec h11 hde
  have hb' : b = ⟨[], [], Termin.hop th⟩ := by
    have := hb; simp only [eb, ↓reduceIte] at this
    exact (Option.some.inj this).symm
  subst hb'
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp only; omega, Ak, fun k => ?_, kop, RI, ?_⟩
  · simp only [HoonMap.get_put, List.append_nil]
    by_cases ek : k = g.bo
    · simp [ek]
    · rw [if_neg ek, if_neg ek, eb, if_neg ek]
  intro dist hlt
  have dn : Distinct ned := L.dist dist (fun x hx => by have := hlt x hx; simp only [Gen.emitted]; omega)
  have lt2 : ∀ x, NMem ned x → x < kk := fun x hx => by
    rcases L.mem x hx with h' | ⟨_, b⟩
    · have := hlt x h'; omega
    · simp only at b; omega
  have KS := K.sem dn lt2
  intro lib σ O c gul st t R v hR
  obtain ⟨S1, S2⟩ := KS lib σ O c gul st t R v hR
  refine ⟨fun f => ?_, fun nf => S2 fun f => nf ((fits_sure L v).mp f)⟩
  obtain ⟨R', hr', hh, hk⟩ := S1 ((fits_sure L v).mpr f)
  exact ⟨R', hr', holdsS_of_sure L hh, fun x hx hn => hk x (by simp only; omega) fun hm => by
    rcases L.mem x hm with h' | ⟨a, _⟩
    · exact hn h'
    · simp only [Gen.emitted] at a; omega⟩

/-! ## `OutGoal` of a block that fills the need -/

/-- **A block `[ops; hop th]` whose ops fill `sur` from `pro` and keep the
registers of `K` meets `OutGoal` for `%next sur th`.** -/
theorem outGoal_next_of_fill {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun}
    {Inv : σ → Prop} {ν : σ → Needs} {K : Nat → Prop} {pro out : Nat} {sur : Sure S} {th : Jmp}
    {A : List Pole} (hb : HoonMap.get c.blocks out = some ⟨[], A, Termin.hop th⟩)
    (hfill : ∀ (st : σ) (t : Trace) (R : Map (Option Noun)) (v : Noun), SkaModel.read pro R = some v →
      (FitsS sur v → ∃ R', Runs lib O c gul st t A R R' ∧ HoldsS sur R' v ∧
        ∀ x, K x → SkaModel.read x R' = SkaModel.read x R) ∧
      (¬ FitsS sur v → Crashes lib O c gul st t A R)) :
    OutGoal lib O c gul Inv ν K pro out (CGoal.next sur th) := by
  intro st regs ti tm p hI htr hp
  obtain ⟨F1, F2⟩ := hfill st ti regs p hp
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · obtain ⟨R', hr, hh, hk⟩ := F1 hf
    refine ⟨st, R', hI, Needs.le_refl _, hh.1, hk, ?_⟩
    have e1 := hr [] (Termin.hop th)
    simp only [List.append_nil] at e1
    rw [goJ_jmp0 _ _ _ _ hb, e1, execBlob_hop]
  · have e2 := F2 hf [] (Termin.hop th)
    simp only [List.append_nil] at e2
    exact ⟨Tone.two ti, st, hI, Needs.le_refl _, by rw [goJ_jmp0 _ _ _ _ hb, e2], ToneRel.two htr⟩

/-- **`OutGoal` of the block of `+kerf` under a fork-free `%next sur th`**,
in every program whose block at `out` is the one `+kerf` made, unproxied by
a `cond` that has none of the block's registers as keys.  The registers
kept (`K`) are below the product register or from the end of `+kerf` on,
and not in `sur`: the ops keep the first by `KernSemS` and the second
because they do not write them (`runs_keep`). -/
theorem outGoal_kerf {sur : Sure S} {th : Jmp} {g g' : Gen Map} {out pro : Nat}
    (h : kerf (⟨ofSure sur, th⟩ : NextL S) g = some ((out, pro), g')) (hd : g.drop = false)
    (hth : th.args = []) (hdist : Distinct sur.ned) (hlt : ∀ x, NMem sur.ned x → x < g.re)
    {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {Inv : σ → Prop} {ν : σ → Needs}
    {cf : Map (Nat × List Nat)}
    (hc : HoonMap.get c.blocks out = (HoonMap.get g'.blocks out).map (unproxyBlob cf))
    (hcf : ∀ x, (x = g.re ∨ NMem sur.ned x ∨ (g.re + 1 ≤ x ∧ x < g'.re)) → HoonMap.get cf x = Option.none)
    {K : Nat → Prop} (hK : ∀ x, K x → ¬ NMem sur.ned x ∧ (x < g.re ∨ g'.re ≤ x)) :
    OutGoal lib O c gul Inv ν K pro out (CGoal.next sur th) := by
  obtain ⟨rfl, rfl, -, -, -, -, l1, Ak, hblk, kop, RI, KS⟩ := kerf_ofSure h hd
  have hb : HoonMap.get c.blocks g.bo = some ⟨[], Ak, Termin.hop th⟩ := by
    rw [hc, hblk, if_pos rfl]
    simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, renFin, renJmp_nil _ hth,
      renOps_fix (fun x hx => unproxy_none (hcf x hx)) RI]
  refine outGoal_next_of_fill hb fun st t R v hR => ?_
  obtain ⟨S1, S2⟩ := KS hdist hlt lib σ O c gul st t R v hR
  refine ⟨fun f => ?_, S2⟩
  obtain ⟨R', hr, hh, hk⟩ := S1 f
  refine ⟨R', hr, hh, fun x hx => ?_⟩
  obtain ⟨hn, hx | hx⟩ := hK x hx
  · exact hk x (by omega) hn
  · exact runs_keep Ak R R' kop hr x fun p hp hw => by
      rcases RI p hp x (poleWr_sub hw) with e | e | ⟨_, e⟩
      · omega
      · exact hn e
      · omega

/-! ## The blocks before the runs, from any state -/

/-- **The blocks of the indirect call before its two runs, under a
fork-free `%next sur th`, from any state** (`indirect_prefix` from `gen0`
for `%done`): `+simple-next` is the identity, `+kerf` makes the block
`out = bo` and takes `pro = re`, and the `%nok` block at `bo + 1` reads the
subject and the formula from two fresh registers above `+kerf`'s and hops to
`out`.  The state after them grows from the start (`GrowU`) and keeps its
`cond`. -/
theorem indirect_prefixN {sur : Sure S} {th : Jmp} {g0 g1 g2 g3 : Gen Map} {nex0 : NextL S}
    {out pro o : Nat}
    (h1 : simpleNextL (CGoalL.next (ofSure sur) th) g0 = some (nex0, g1))
    (h2 : kerf nex0 g1 = some ((out, pro), g2))
    (h3 : emit ⟨[], [Pole.nok g2.re (g2.re + 1) pro], Termin.hop (jmp0 out)⟩
        { { g2 with re := g2.re + 1 } with re := g2.re + 1 + 1 } = some (o, g3))
    (hd : g0.drop = false) (hu : UpBelow g0) (hcb : CondBelow g0) (b0 : 1 ≤ g0.bo)
    (hj : GJ g0.bo (CGoal.next sur th)) :
    g1 = g0 ∧ nex0 = ⟨ofSure sur, th⟩ ∧ out = g0.bo ∧ pro = g0.re ∧ o = g0.bo + 1 ∧ g0.re + 1 ≤ g2.re ∧
    g3.re = g2.re + 2 ∧ g3.bo = g0.bo + 2 ∧ g3.drop = false ∧ g3.cond = g0.cond ∧
    HoonMap.get g3.blocks (g0.bo + 1) = some ⟨[], [Pole.nok g2.re (g2.re + 1) g0.re], Termin.hop (jmp0 g0.bo)⟩ ∧
    HoonMap.get g3.blocks g0.bo = HoonMap.get g2.blocks g0.bo ∧ (∀ k, k < g0.bo →
      HoonMap.get g3.blocks k = HoonMap.get g0.blocks k) ∧
    kerf (⟨ofSure sur, th⟩ : NextL S) g0 = some ((out, pro), g2) ∧
    GrowU g0 g3 ∧ UpBelow g3 ∧ CondBelow g3 := by
  simp only [simpleNextL, pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  have K := kerf_ofSure h2 hd
  obtain ⟨rfl, rfl, bo2, dr2, cd2, -, l2, Ak, hblk, -, -, -⟩ := K
  rw [emit_apply] at h3
  simp only [Option.some.injEq, Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  have d2 : g2.drop = false := dr2.trans hd
  have eb3 : ∀ k, HoonMap.get ({ { g2 with re := g2.re + 1 } with re := g2.re + 1 + 1 }.emitted
      ⟨[], [Pole.nok g2.re (g2.re + 1) g0.re], Termin.hop (jmp0 g0.bo)⟩).blocks k =
      if k = g0.bo + 1 then some ⟨[], [Pole.nok g2.re (g2.re + 1) g0.re], Termin.hop (jmp0 g0.bo)⟩ else
      if k = g0.bo then some ⟨[], Ak, Termin.hop th⟩ else HoonMap.get g0.blocks k := fun k => by
    simp only [Gen.emitted, d2, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put, bo2, hblk]
  have thl : th.there < g0.bo := hj.2
  have up0 : ∀ t, ¬ UpAt ({ { g2 with re := g2.re + 1 } with re := g2.re + 1 + 1 }.emitted
      ⟨[], [Pole.nok g2.re (g2.re + 1) g0.re], Termin.hop (jmp0 g0.bo)⟩).blocks g0.bo t := by
    rintro t ⟨b, j, hb, hf, ht, hlt⟩
    rw [eb3, if_neg (by omega), if_pos rfl] at hb
    cases hb; simp only [Termin.hop.injEq] at hf; subst hf; omega
  have G : GrowU g0 ({ { g2 with re := g2.re + 1 } with re := g2.re + 1 + 1 }.emitted
      ⟨[], [Pole.nok g2.re (g2.re + 1) g0.re], Termin.hop (jmp0 g0.bo)⟩) := by
    refine ⟨by simp only [Gen.emitted]; omega, by simp only [Gen.emitted]; exact dr2, fun k b hk hb => ?_,
      fun k b' hb' => ?_⟩
    · exact ⟨b, by rw [eb3, if_neg (by omega), if_neg (by omega)]; exact hb, rfl, rfl⟩
    · rw [eb3] at hb'
      by_cases e1 : k = g0.bo + 1
      · rw [if_pos e1] at hb'; cases hb'
        refine Or.inr ⟨by omega, by simp only [Gen.emitted]; omega, fun j hj' => ?_⟩
        simp only [finJumps, List.mem_singleton] at hj'; subst hj'
        exact ⟨by simp [jmp0]; omega, Or.inl ⟨by simp [jmp0]; omega, fun t ht => absurd ht (up0 t)⟩⟩
      rw [if_neg e1] at hb'
      by_cases e0 : k = g0.bo
      · rw [if_pos e0] at hb'; cases hb'
        refine Or.inr ⟨by omega, by simp only [Gen.emitted]; omega, fun j hj' => ?_⟩
        simp only [finJumps, List.mem_singleton] at hj'; subst hj'
        refine ⟨hj.1, Or.inl ⟨by omega, fun t ht => ?_⟩⟩
        have ht' : UpAt g0.blocks j.there t := by
          obtain ⟨b, j', hb, hf, ht, hlt⟩ := ht
          rw [eb3, if_neg (by omega), if_neg (by omega)] at hb
          exact ⟨b, j', hb, hf, ht, hlt⟩
        have := hu _ _ ht'; omega
      · rw [if_neg e0] at hb'
        exact Or.inl ⟨b', hb', rfl, rfl⟩
  refine ⟨rfl, rfl, rfl, rfl, by omega, l2, rfl, by simp only [Gen.emitted]; omega, by simp only [Gen.emitted]; exact d2,
    by simp only [Gen.emitted]; exact cd2, by rw [eb3, if_pos rfl], ?_, fun k hk => ?_, h2, G, G.up hu, ?_⟩
  · rw [eb3, if_neg (by omega), if_pos rfl, hblk, if_pos rfl]
  · rw [eb3, if_neg (by omega), if_neg (by omega)]
  · intro k hk
    simp only [Gen.emitted, cd2] at hk ⊢
    have := hcb k hk; omega

/-! ## The run relation of the indirect call under a fork-free `%next` -/

/-- **The `sem` of a run that calls, under a fork-free `%next`**: `SemNV`
with the oracle's state moving, for `+mink`'s tone `r` on a formula `f`
that the nomm stands for on the subjects of `P` (`GoalSemCM` in place of
`GoalSem`, at every later `cond`). -/
def SemNC (lib : Lib) (P : Noun → Prop) (f : Noun) (sur : Sure S) (th : Jmp) (g0 g1 : Gen Map) (nex : NextL S) :
    Prop :=
  ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
    ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) (n : Nat)
      (gul : Noun), OracleSteps Inv ν O → OracleFwd lib Inv ν O n →
    ∀ (st : σ) (t tm : Trace) (s0 s : Noun) (r : Tone), Inv st → Forall2 (FrameRel lib (ν st)) t tm → P s →
    minkF lib gul n tm s f = some r →
    AgreeU lib O c gul st t cf ned g0 g1 nex.laz s0 s → (∀ x, NMem ned x → g1.re ≤ x) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    GoalSemCM lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ NMem sur.ned x) st regs t tm nex.th
      (CGoal.next sur th) r

/-- **`RunOKNV` for a run that calls**: the structural fields of `RunOKNV`,
`nec` on the pure part `pq` (where the subject does not fit the need, `pq`
crashes, and so does `+mink` by `MinkN2`), and `SemNC`. -/
structure RunOKNC (lib : Lib) (P : Noun → Prop) (f : Noun) (pq : Nomm) (sur : Sure S) (th : Jmp)
    (g0 g1 : Gen Map) (nex : NextL S) : Prop where
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
  size : (entries nex.laz).length ≤ 2 * sixCount pq
  nec : ∀ s, ¬ FitsS nex.laz.sure s → pureEval pq s = none
  ncond : ∀ r, NMem nex.laz.sure.ned r → HoonMap.get g1.cond r = Option.none
  econd : ∀ e ∈ entries nex.laz, ∀ r, NMem e.2.sure.ned r → HoonMap.get g1.cond r = Option.none
  sem : SemNC lib P f sur th g0 g1 nex

/-- **The indirect call `[2 p q]` under a fork-free `%next sur th` meets
`RunOKNC`**, from any state with the hypotheses of `OKNV`, for `p`, `q`
meeting `UOK` and any formula with `MinkN2` (so any `Annot` of `[2 p q]`
but the bare ones): `indirect_prefixN`, `indirect_mid` for the runs of `p`
and `q`, `indirect_semG` with `outGoal_kerf` for the block of `+kerf`. -/
theorem indirect_runS (lib : Lib) {p q : Nomm} (up : UOK (S := S) (Map := Map) lib p)
    (uq : UOK (S := S) (Map := Map) lib q) {P : Noun → Prop} {f : Noun} (M : MinkN2 lib P f p q)
    (hcount : sixCount p + sixCount q ≤ 255) {env : CallEnv} {sup : Option Nomm}
    {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g' : Gen Map} {nex : NextL S}
    (hj : GJ g0.bo (CGoal.next sur th)) (hth : th.args = []) (hok : GoalOK g0 (CGoal.next sur th))
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (hkg : ∀ r, NMem sur.ned r → HoonMap.get g0.cond r = Option.none)
    {out pro o : Nat} {g2 g3 g4 g5 g6 : Gen Map} {nexF nexF' nexS : NextL S}
    (h2 : kerf (⟨ofSure sur, th⟩ : NextL S) g0 = some ((out, pro), g2))
    (h3 : emit ⟨[], [Pole.nok g2.re (g2.re + 1) pro], Termin.hop (jmp0 out)⟩
        { { g2 with re := g2.re + 1 } with re := g2.re + 1 + 1 } = some (o, g3))
    (h4 : runLC env sup q (CGoalL.next (ofSure (lazyReg (g2.re + 1))) (jmp0 o)) region g3 = some (nexF, g4))
    (h5 : pastL env.cod nexF p region g4 = some (nexF', g5))
    (h6 : runLC env sup p (CGoalL.next (ofSure (lazyReg g2.re)) nexF'.th) region g5 = some (nexS, g6))
    (h7 : copyL nexS nexF'.laz g6 = some (nex, g')) :
    RunOKNC lib P f (Nomm.cons p q) sur th g0 g' nex := by
  have h1 : simpleNextL (CGoalL.next (ofSure sur) th) g0 = some (⟨ofSure sur, th⟩, g0) := rfl
  obtain ⟨-, -, rfl, rfl, rfl, l2, r3, b3, d3, cn3, k3o, k3out, k3lo, hk2, G3, u3, cb3⟩ :=
    indirect_prefixN h1 h2 h3 d0 hu hcb b0 hj
  have pp := up.pure
  have qp := uq.pure
  rw [runLC_eq env q (Nomm.noCall_of_pure q qp)] at h4
  rw [pastL_pure _ _ pp, pure_apply] at h5
  simp only [Option.some.injEq, Prod.mk.injEq] at h5
  obtain ⟨rfl, rfl⟩ := h5
  rw [runLC_eq env p (Nomm.noCall_of_pure p pp)] at h6
  have nk : ∀ x, g0.re ≤ x → HoonMap.get g0.cond x = Option.none := fun x hx => condBelow_none hcb hx
  have Rm := indirect_mid (a := g2.re) (b := g2.re + 1) (o := g0.bo + 1) lib up uq (by omega)
    (by omega) (by omega) (by omega) (by omega) hcount d3 u3 (hcl.growU G3) cb3
    (by rw [cn3]; exact nk _ (by omega)) (by rw [cn3]; exact nk _ (by omega)) h4 h6 h7
  have E3 : Ext g0 g3 := ⟨by omega, by omega, by rw [d3, d0], k3lo⟩
  have CF3 : CondFresh g0 g3 := ⟨by omega, fun k => Or.inl (by rw [cn3])⟩
  -- the keys of every later `cond` below `g3.re` are the start's
  have cf3 : ∀ k, k < g3.re → HoonMap.get g'.cond k = HoonMap.get g0.cond k := fun k hk => by
    rw [Rm.cfr.get_lt hk, cn3]
  refine ⟨E3.trans Rm.ext, G3.trans Rm.grow, CF3.trans Rm.cfr, Rm.lo, Rm.hi, ?_, fun r hr => ?_, Rm.dist,
    fun e he => ⟨(Rm.eregs e he).1, fun r hr => ⟨by have := ((Rm.eregs e he).2 r hr).1; omega,
      ((Rm.eregs e he).2 r hr).2⟩⟩,
    fun e he => ⟨by have := (Rm.labs e he).1; omega, (Rm.labs e he).2⟩, Rm.nodup, Rm.size, fun s hs => ?_,
    Rm.ncond, Rm.econd, ?_⟩
  · rcases Rm.ent with fr | e
    · exact Or.inl fr
    · simp only [GoalJ] at e
      rw [e]
      exact Or.inl ⟨_, by rw [Rm.ext.2.2.2 _ (by show g0.bo + 1 < g3.bo; omega)]; exact k3o, rfl, rfl⟩
  · rcases Rm.regs r hr with e | ⟨a, b⟩
    · simp only [pairSure, NMem] at e
      exact Or.inr ⟨by omega, by have := Rm.ext.1; omega⟩
    · exact Or.inr ⟨by omega, b⟩
  · rcases Rm.nec s hs with e | ⟨v, ev, hv⟩
    · exact e
    · exfalso
      apply hv
      rw [pureEval_cons] at ev
      obtain ⟨x, -, ev⟩ := Option.bind_eq_some_iff.mp ev
      obtain ⟨y, -, ev⟩ := Option.bind_eq_some_iff.mp ev
      cases ev
      exact ⟨⟨trivial, trivial⟩, looks_empty _⟩
  -- the `sem`
  intro cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
  have hcf6 : ∀ x, x < g3.re → HoonMap.get cf x = HoonMap.get g0.cond x := fun x hx => by
    rw [hcf x (by have := Rm.ext.1; omega), cf3 x hx]
  have ag3 : AgreeU lib O c gul st t cf ned g3 g' nex.laz s0 s :=
    AgreeU.part ag (by omega) (Ext.refl g') (fun e he => he) (fun k _ _ hk => hk)
      (fun e he => Nat.lt_trans (Rm.labs e he).2.1 Rm.hi)
  have G := Rm.sem cf (fun k hk => hcf k hk) c ned σ O st t gul s0 s ag3 hned regs hh hn
  have nlab : ∀ k, k < g3.bo → k ∉ (entries nex.laz).map Prod.fst := fun k hk hm => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
    have := (Rm.labs e he).1; omega
  have hbo : HoonMap.get c.blocks (g0.bo + 1) =
      some ⟨[], [Pole.nok g2.re (g2.re + 1) g0.re], Termin.hop (jmp0 g0.bo)⟩ := by
    rw [ag.1 (g0.bo + 1) (by omega) (by have := Rm.ext.2.1; omega) (nlab _ (by omega)),
      Rm.ext.2.2.2 _ (by omega), k3o]
    simp only [Option.map_some, unproxyBlob, renBlob, List.map_nil, List.map_cons, renPole, renFin,
      renJmp_nil _ (show (jmp0 g0.bo).args = [] from rfl)]
    rw [unproxy_none (by rw [hcf6 _ (by omega)]; exact nk _ (by omega)),
      unproxy_none (by rw [hcf6 _ (by omega)]; exact nk _ (by omega)),
      unproxy_none (by rw [hcf6 _ (by omega)]; exact nk _ (Nat.le_refl _))]
  have Hout := outGoal_kerf (Inv := Inv) (ν := ν) (lib := lib) (O := O) (gul := gul)
    (K := fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ NMem sur.ned x) hk2 d0 hth hok.1 hok.2
    (cf := cf) (c := c)
    (by rw [ag.1 g0.bo (Nat.le_refl _) (by have := Rm.ext.2.1; omega) (nlab _ (by omega)),
      Rm.ext.2.2.2 _ (by omega), k3out])
    (fun x hx => by
      rcases hx with e | e | ⟨a, b⟩
      · rw [hcf6 _ (by omega)]; exact nk _ (by omega)
      · rw [hcf6 _ (by have := hok.2 x e; omega)]; exact hkg x e
      · rw [hcf6 _ (by omega)]; exact nk _ (by omega))
    (fun x hx => ⟨hx.2, by
      rcases hx.1 with e | e
      · exact Or.inl e
      · exact Or.inr (by have := hned x e; have := Rm.ext.1; omega)⟩)
  refine indirect_semG M hS hF hbo (K' := fun x => (x < g3.re ∨ NMem ned x) ∧ ¬ NMem (pairSure g2.re (g2.re + 1) : Sure S).ned x)
    (fun x hx => ⟨⟨by
      rcases hx.1 with e | e
      · exact Or.inl (by omega)
      · exact Or.inr e, fun hm => by
      simp only [pairSure, NMem] at hm
      rcases hx.1 with e | e
      · omega
      · have := hned x e; have := Rm.ext.1; omega⟩, fun e => by
      subst e
      rcases hx.1 with e | e
      · omega
      · have := hned _ e; have := Rm.ext.1; omega⟩) Hout hI htr hs hm G

/-- **The indirect call `[2 p q]` under a fork-free `%next sur th` meets
`RunOKNC`** (`indirect_runS` after `runLC_n2_none`). -/
theorem indirect_runN (lib : Lib) {p q : Nomm} (up : UOK (S := S) (Map := Map) lib p)
    (uq : UOK (S := S) (Map := Map) lib q) {P : Noun → Prop} {f : Noun} (M : MinkN2 lib P f p q)
    (hcount : sixCount p + sixCount q ≤ 255) {env : CallEnv} {sup : Option Nomm}
    {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g' : Gen Map} {nex : NextL S}
    (hj : GJ g0.bo (CGoal.next sur th)) (hth : th.args = []) (hok : GoalOK g0 (CGoal.next sur th))
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (hkg : ∀ r, NMem sur.ned r → HoonMap.get g0.cond r = Option.none)
    (h : runLC env sup (Nomm.n2 p q Option.none) (CGoalL.next (ofSure sur) th) region g0 = some (nex, g')) :
    RunOKNC lib P f (Nomm.cons p q) sur th g0 g' nex := by
  obtain ⟨nex0, g1, out, pro, g2, o, g3, nexF, g4, nexF', g5, nexS, g6, h1, h2, h3, h4, h5, h6, h7⟩ :=
    runLC_n2_none h
  simp only [simpleNextL, pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  exact indirect_runS lib up uq M hcount hj hth hok b0 d0 hu hcl hcb hkg h2 h3 h4 h5 h6 h7

/-- **The indirect call `[2 p q]` under `%done`, from any state**:
`+simple-next` makes the block `[don re]` at `bo` (kept to the end), and the
rest of the run is the one under the fork-free `%next (lazy-from-reg re)`
into it, from the state after that block, which meets `RunOKNC`
(`indirect_runS`); `outGoal_done` turns its goal into `%done`. -/
theorem indirect_runD (lib : Lib) {p q : Nomm} (up : UOK (S := S) (Map := Map) lib p)
    (uq : UOK (S := S) (Map := Map) lib q) {P : Noun → Prop} {f : Noun} (M : MinkN2 lib P f p q)
    (hcount : sixCount p + sixCount q ≤ 255) {env : CallEnv} {sup : Option Nomm}
    {region : List Nat} {g0 g' : Gen Map} {nex : NextL S}
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (h : runLC env sup (Nomm.n2 p q Option.none) CGoalL.done region g0 = some (nex, g')) :
    HoonMap.get g'.blocks g0.bo = some ⟨[], [], Termin.don g0.re⟩ ∧
    RunOKNC lib P f (Nomm.cons p q) (lazyReg g0.re) (jmp0 g0.bo)
      ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) g' nex := by
  obtain ⟨nex0, g1, out, pro, g2, o, g3, nexF, g4, nexF', g5, nexS, g6, h1, h2, h3, h4, h5, h6, h7⟩ :=
    runLC_n2_none h
  simp only [simpleNextL] at h1
  obtain ⟨r, ga, ha, h1⟩ := bind_some h1
  rw [re_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨od, gb, hb, h1⟩ := bind_some h1
  rw [emit_apply] at hb
  simp only [Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  have G1 : GrowU ({ g0 with re := g0.re + 1 } : Gen Map) ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) :=
    growU_emit (g := { g0 with re := g0.re + 1 }) (b := ⟨[], [], Termin.don g0.re⟩)
      (fun j hj => by simp [finJumps] at hj) hu
  have R := indirect_runS (sur := lazyReg g0.re) (th := jmp0 g0.bo) lib up uq M hcount
    ⟨b0, by simp only [jmp0, Gen.emitted]; omega⟩ rfl
    ⟨trivial, fun x hx => by simp only [lazyReg, NMem] at hx; subst hx; simp only [Gen.emitted]; omega⟩
    (by simp only [Gen.emitted]; omega) (by simp only [Gen.emitted]; exact d0) (G1.up hu)
    (Clear.growU (g := ({ g0 with re := g0.re + 1 } : Gen Map)) hcl G1)
    (fun k hk => by have := hcb k hk; simp only [Gen.emitted] at this ⊢; omega)
    (fun x hx => by
      simp only [lazyReg, NMem] at hx; subst hx
      exact condBelow_none hcb (Nat.le_refl _)) h2 h3 h4 h5 h6 h7
  refine ⟨?_, R⟩
  rw [R.ext.2.2.2 _ (by simp only [Gen.emitted]; omega)]
  simp only [Gen.emitted, d0, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]

/-! ## `OutGoal` for `%done` and `%pick` -/

/-- **`OutGoal` for `%done`** from `OutGoal` for `%next (lazy-from-reg r)`
into a block `[don r]`, which `+simple-next` makes for `%done`. -/
theorem outGoal_done {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun}
    {Inv : σ → Prop} {ν : σ → Needs} {K : Nat → Prop} {pro out r b : Nat}
    (hb : HoonMap.get c.blocks b = some ⟨[], [], Termin.don r⟩)
    (H : OutGoal lib O c gul Inv ν K pro out (CGoal.next (lazyReg r : Sure S) (jmp0 b))) :
    OutGoal lib O c gul Inv ν K pro out (CGoal.done : CGoal S) := by
  intro st regs ti tm p hI htr hp
  obtain ⟨st', regs', hI', hle, hh, -, e⟩ := (H st regs ti tm p hI htr hp).1 (fitsS_lazyReg r p)
  refine ⟨Tone.zero p, st', hI', hle, ?_, ToneRel.zero p⟩
  rw [e, goJ_jmp0 _ _ _ _ hb, execBlob_don']
  have hr : SkaModel.read r regs' = some p := hh
  rw [hr]; rfl

/-- **`OutGoal` for `%pick z o`** from `OutGoal` for `%next (lazy-from-reg
r)` into a block `[brn r z o]`, which `+simple-next` makes for `%pick`. -/
theorem outGoal_pick {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun}
    {Inv : σ → Prop} {ν : σ → Needs} {K : Nat → Prop} {pro out r b : Nat} {z o : Jmp}
    (hb : HoonMap.get c.blocks b = some ⟨[], [], Termin.brn r z o⟩)
    (H : OutGoal lib O c gul Inv ν K pro out (CGoal.next (lazyReg r : Sure S) (jmp0 b))) :
    OutGoal lib O c gul Inv ν K pro out (CGoal.pick z o : CGoal S) := by
  intro st regs ti tm p hI htr hp
  obtain ⟨st', regs', hI', hle, hh, hk, e⟩ := (H st regs ti tm p hI htr hp).1 (fitsS_lazyReg r p)
  have hr : SkaModel.read r regs' = some p := hh
  have E : goJ lib O c gul st regs ti (jmp0 out) =
      if p = A 0 then goJ lib O c gul st' regs' ti z
      else if p = A 1 then goJ lib O c gul st' regs' ti o else some (Tone.two ti, st') := by
    rw [e, goJ_jmp0 _ _ _ _ hb, execBlob_brn, hr]; rfl
  refine ⟨fun e0 => ⟨st', regs', hI', hle, trivial, hk, by rw [E, if_pos e0]⟩,
    fun e1 => ⟨st', regs', hI', hle, trivial, hk, by
      rw [E, if_neg (by rw [e1]; exact fun h => by cases h), if_pos e1]⟩,
    fun e0 e1 => ⟨Tone.two ti, st', hI', hle, by rw [E, if_neg e0, if_neg e1],
      ToneRel.two (frames_mono hle htr)⟩⟩

end Comp
end SkaModel
end Formalization
