import lemmas.Ska.CompIndirectNext

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

end Comp
end SkaModel
end Formalization
