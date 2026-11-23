import lemmas.Ska.CompSixNextCond

/-!
# `+fork-need` and the join it makes

`+fork-need` makes two needs `n0`, `n1` of the shape of `ned` from fresh
registers (`NCopy`), a join block `barg` whose parameters are the registers
of `ned` and which hops to the goal's block, and the blocks `o0` and `o1`,
which hop to `barg` passing the registers of `n0` and of `n1`
(`forkNeed_spec`).  Every argument is `some r`, so `+eval-pass` poisons
nothing: entering `o0` with `n0` holding a noun enters the goal's block with
`ned` holding it and every other register unchanged (`goJ_fork`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Needs of the same shape -/

/-- `n` has the shape of `ned`, with other registers. -/
def NCopy : Need → Need → Prop
  | Need.none, Need.none => True
  | Need.this _, Need.this _ => True
  | Need.pair p q, Need.pair p' q' => NCopy p p' ∧ NCopy q q'
  | Need.both _ p q, Need.both _ p' q' => NCopy p p' ∧ NCopy q q'
  | _, _ => False

theorem NCopy.length : ∀ {ned n : Need}, NCopy ned n → (flattenNeed n).length = (flattenNeed ned).length
  | Need.none, Need.none, _ => rfl
  | Need.this _, Need.this _, _ => rfl
  | Need.pair _ _, Need.pair _ _, h => by simp [flattenNeed, h.1.length, h.2.length]
  | Need.both _ _ _, Need.both _ _ _, h => by simp [flattenNeed, h.1.length, h.2.length]

theorem NCopy.fits : ∀ {ned n : Need}, NCopy ned n → ∀ v, (Fits n v ↔ Fits ned v)
  | Need.none, Need.none, _, _ => Iff.rfl
  | Need.this _, Need.this _, _, _ => Iff.rfl
  | Need.pair _ _, Need.pair _ _, h, Noun.cell a b => by simp only [Fits, h.1.fits a, h.2.fits b]
  | Need.pair _ _, Need.pair _ _, _, Noun.atom _ => Iff.rfl
  | Need.both _ _ _, Need.both _ _ _, h, Noun.cell a b => by simp only [Fits, h.1.fits a, h.2.fits b]
  | Need.both _ _ _, Need.both _ _ _, _, Noun.atom _ => Iff.rfl

theorem NCopy.clean : ∀ {ned n : Need}, NCopy ned n → Clean ned → Clean n
  | Need.none, Need.none, _, _ => trivial
  | Need.this _, Need.this _, _, _ => trivial
  | Need.pair p q, Need.pair p' q', h, hc => by
    refine ⟨fun ⟨e1, e2⟩ => hc.1 ⟨?_, ?_⟩, h.1.clean hc.2.1, h.2.clean hc.2.2⟩
    · subst e1; cases p <;> simp_all [NCopy]
    · subst e2; cases q <;> simp_all [NCopy]
  | Need.both _ _ _, Need.both _ _ _, h, hc => ⟨h.1.clean hc.1, h.2.clean hc.2⟩

/-! ## The loop of `+fork-need` -/

/-- **The loop of `+fork-need`**: two needs of the shape of `ned`, from
distinct fresh registers. -/
theorem forkNeedGo_spec : ∀ (ned : Need) (g g' : Gen Map) (n0 n1 : Need),
    (forkNeedGo ned : CM Map (Need × Need)) g = some ((n0, n1), g') →
    (∃ k, g' = { g with re := g.re + k }) ∧ NCopy ned n0 ∧ NCopy ned n1 ∧
    Distinct n0 ∧ Distinct n1 ∧ (∀ x, NMem n0 x → ¬ NMem n1 x) ∧
    (∀ x, NMem n0 x ∨ NMem n1 x → g.re ≤ x ∧ x < g'.re)
  | Need.none, g, g', n0, n1, h => by
    simp only [forkNeedGo, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact ⟨⟨0, by simp⟩, trivial, trivial, trivial, trivial, fun _ h => h.elim, fun _ h => by
      rcases h with h | h <;> exact h.elim⟩
  | Need.this _, g, g', n0, n1, h => by
    simp only [forkNeedGo, bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    refine ⟨⟨2, rfl⟩, trivial, trivial, trivial, trivial, fun x h0 h1 => ?_, fun x h => ?_⟩
    · simp only [NMem] at h0 h1; omega
    · simp only [NMem] at h ⊢; omega
  | Need.pair p q, g, g', n0, n1, h => by
    simp only [forkNeedGo] at h
    obtain ⟨⟨h0, h1⟩, g1, hp, h⟩ := bind_some h
    obtain ⟨⟨t0, t1⟩, g2, hq, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    obtain ⟨⟨k1, e1⟩, cp0, cp1, dp0, dp1, jp, rp⟩ := forkNeedGo_spec p g g1 h0 h1 hp
    obtain ⟨⟨k2, e2⟩, cq0, cq1, dq0, dq1, jq, rq⟩ := forkNeedGo_spec q g1 g2 t0 t1 hq
    have r1 : g1.re = g.re + k1 := by rw [e1]
    have r2 : g2.re = g1.re + k2 := by rw [e2]
    refine ⟨⟨k1 + k2, by rw [e2, e1]; simp [Nat.add_assoc]⟩, ⟨cp0, cq0⟩, ⟨cp1, cq1⟩,
      ⟨dp0, dq0, fun x a b => ?_⟩, ⟨dp1, dq1, fun x a b => ?_⟩, fun x a b => ?_, fun x a => ?_⟩
    · have := rp x (Or.inl a); have := rq x (Or.inl b); omega
    · have := rp x (Or.inr a); have := rq x (Or.inr b); omega
    · rcases a with a | a <;> rcases b with b | b
      · exact jp x a b
      · have := rp x (Or.inl a); have := rq x (Or.inr b); omega
      · have := rq x (Or.inl a); have := rp x (Or.inr b); omega
      · exact jq x a b
    · rcases a with (a | a) | (a | a)
      · have := rp x (Or.inl a); omega
      · have := rq x (Or.inl a); omega
      · have := rp x (Or.inr a); omega
      · have := rq x (Or.inr a); omega
  | Need.both _ p q, g, g', n0, n1, h => by
    simp only [forkNeedGo] at h
    obtain ⟨r0, ga, ha, h⟩ := bind_some h
    obtain ⟨r1, gb, hb, h⟩ := bind_some h
    simp only [re_apply, Option.some.injEq, Prod.mk.injEq] at ha hb
    obtain ⟨rfl, rfl⟩ := ha
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨⟨h0, h1⟩, g1, hp, h⟩ := bind_some h
    obtain ⟨⟨t0, t1⟩, g2, hq, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    obtain ⟨⟨k1, e1⟩, cp0, cp1, dp0, dp1, jp, rp⟩ := forkNeedGo_spec p _ g1 h0 h1 hp
    obtain ⟨⟨k2, e2⟩, cq0, cq1, dq0, dq1, jq, rq⟩ := forkNeedGo_spec q g1 g2 t0 t1 hq
    simp only at rp
    have r1 : g1.re = g.re + 1 + 1 + k1 := by rw [e1]
    have r2 : g2.re = g1.re + k2 := by rw [e2]
    refine ⟨⟨2 + k1 + k2, by rw [e2, e1]; simp; omega⟩, ⟨cp0, cq0⟩, ⟨cp1, cq1⟩,
      ⟨dp0, dq0, fun x a b => ?_, fun a => ?_, fun a => ?_⟩,
      ⟨dp1, dq1, fun x a b => ?_, fun a => ?_, fun a => ?_⟩, fun x a b => ?_, fun x a => ?_⟩
    · have := rp x (Or.inl a); have := rq x (Or.inl b); omega
    · have := rp _ (Or.inl a); omega
    · have := rq _ (Or.inl a); omega
    · have := rp x (Or.inr a); have := rq x (Or.inr b); omega
    · have := rp _ (Or.inr a); omega
    · have := rq _ (Or.inr a); omega
    · simp only [NMem] at a b
      rcases a with a | a | a <;> rcases b with b | b | b
      · omega
      · have := rp x (Or.inr b); omega
      · have := rq x (Or.inr b); omega
      · have := rp x (Or.inl a); omega
      · exact jp x a b
      · have := rp x (Or.inl a); have := rq x (Or.inr b); omega
      · have := rq x (Or.inl a); omega
      · have := rq x (Or.inl a); have := rp x (Or.inr b); omega
      · exact jq x a b
    · simp only [NMem] at a
      rcases a with (a | a | a) | (a | a | a)
      · omega
      · have := rp x (Or.inl a); omega
      · have := rq x (Or.inl a); omega
      · omega
      · have := rp x (Or.inr a); omega
      · have := rq x (Or.inr a); omega

/-! ## `+eval-pass` of a copy -/

theorem evalPassLoop_append : ∀ (a : List (Option Nat)) (p : List Nat) (a' : List (Option Nat)) (p' : List Nat),
    a.length = p.length → ∀ R : Map (Option Noun),
    evalPassLoop (a ++ a') (p ++ p') R = (evalPassLoop a p R).bind (evalPassLoop a' p')
  | [], [], _, _, _, R => by simp [evalPassLoop]
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h
  | x :: a, y :: p, a', p', h, R => by
    simp only [List.cons_append, evalPassLoop, Option.bind_assoc]
    congr 1; funext R1
    exact evalPassLoop_append a p a' p' (by simpa using h) R1

/-- **The moves of a join from a copy**: the registers of `ned` get what
those of `n` hold, and no other register changes. -/
theorem evalPassLoop_copy : ∀ (ned n : Need), NCopy ned n → ∀ (R : Map (Option Noun)) (v : Noun), HoldsN n R v →
    Distinct ned → (∀ x, NMem n x → ¬ NMem ned x) →
    ∃ R', evalPassLoop ((flattenNeed n).map some) (flattenNeed ned) R = some R' ∧ HoldsN ned R' v ∧
      ∀ x, ¬ NMem ned x → SkaModel.read x R' = SkaModel.read x R
  | Need.none, Need.none, _, R, _, _, _, _ => ⟨R, by simp [flattenNeed, evalPassLoop], trivial, fun _ _ => rfl⟩
  | Need.this r, Need.this r', _, R, v, hh, _, _ => by
    refine ⟨store r v R, ?_, read_store_eq r v R, fun x hx => read_store_ne hx v R⟩
    simp only [HoldsN] at hh
    simp [flattenNeed, evalPassLoop, move_of_read hh]
  | Need.pair p q, Need.pair p' q', hc, R, Noun.cell a b, hh, hd, hj => by
    obtain ⟨R1, e1, h1, k1⟩ := evalPassLoop_copy p p' hc.1 R a hh.1 hd.1 (fun x hx hn => hj x (Or.inl hx) (Or.inl hn))
    have hq1 : HoldsN q' R1 b := HoldsN.agree q' (fun x hx => k1 x fun hn => hj x (Or.inr hx) (Or.inl hn)) hh.2
    obtain ⟨R2, e2, h2, k2⟩ := evalPassLoop_copy q q' hc.2 R1 b hq1 hd.2.1 (fun x hx hn => hj x (Or.inr hx) (Or.inr hn))
    refine ⟨R2, ?_, ⟨HoldsN.agree p (fun x hx => k2 x (hd.2.2 x hx)) h1, h2⟩, fun x hx => ?_⟩
    · simp only [flattenNeed, List.map_append]
      rw [evalPassLoop_append _ _ _ _ (by simp [hc.1.length]), e1, Option.bind_some, e2]
    · rw [k2 x (fun h => hx (Or.inr h)), k1 x (fun h => hx (Or.inl h))]
  | Need.pair _ _, Need.pair _ _, _, _, Noun.atom _, hh, _, _ => hh.elim
  | Need.both r p q, Need.both r' p' q', hc, R, Noun.cell a b, hh, hd, hj => by
    have hr : ¬ NMem (Need.both r p q) r' := hj r' (Or.inl rfl)
    let R0 := store r (C a b) R
    have k0 : ∀ x, x ≠ r → SkaModel.read x R0 = SkaModel.read x R := fun x hx => read_store_ne hx _ R
    have hp0 : HoldsN p' R0 a := HoldsN.agree p' (fun x hx => k0 x fun e => hj x (Or.inr (Or.inl hx))
      (Or.inl e)) hh.2.1
    obtain ⟨R1, e1, h1, k1⟩ := evalPassLoop_copy p p' hc.1 R0 a hp0 hd.1
      (fun x hx hn => hj x (Or.inr (Or.inl hx)) (Or.inr (Or.inl hn)))
    have hq1 : HoldsN q' R1 b := HoldsN.agree q' (fun x hx => by
      rw [k1 x fun hn => hj x (Or.inr (Or.inr hx)) (Or.inr (Or.inl hn))]
      exact k0 x fun e => hj x (Or.inr (Or.inr hx)) (Or.inl e)) hh.2.2
    obtain ⟨R2, e2, h2, k2⟩ := evalPassLoop_copy q q' hc.2 R1 b hq1 hd.2.1
      (fun x hx hn => hj x (Or.inr (Or.inr hx)) (Or.inr (Or.inr hn)))
    refine ⟨R2, ?_, ⟨?_, HoldsN.agree p (fun x hx => k2 x (hd.2.2.1 x hx)) h1, h2⟩, fun x hx => ?_⟩
    · simp only [flattenNeed, List.map_cons, List.map_append, evalPassLoop]
      rw [move_of_read hh.1]
      simp only [Option.bind_some]
      rw [evalPassLoop_append _ _ _ _ (by simp [hc.1.length]), e1, Option.bind_some, e2]
    · rw [k2 r hd.2.2.2.2, k1 r hd.2.2.2.1]; exact read_store_eq _ _ _
    · simp only [NMem, not_or] at hx
      rw [k2 x hx.2.2, k1 x hx.2.1]; exact k0 x hx.1
  | Need.both _ _ _, Need.both _ _ _, _, _, Noun.atom _, hh, _, _ => hh.elim

theorem mem_flatten : ∀ (n : Need) (x : Nat), x ∈ flattenNeed n ↔ NMem n x
  | Need.none, x => by simp [flattenNeed, NMem]
  | Need.this r, x => by simp [flattenNeed, NMem]
  | Need.pair p q, x => by simp [flattenNeed, NMem, mem_flatten p x, mem_flatten q x]
  | Need.both r p q, x => by simp [flattenNeed, NMem, mem_flatten p x, mem_flatten q x]

/-! ## `+fork-sure` -/

/-- **`+fork-sure` with three fresh labels**: `o0` and `o1` taken before,
the join at the next label. -/
theorem forkSure_spec {sur : Sure S} {o : Nat} {g g' : Gen Map} {s0 s1 : Sure S}
    (h : forkSure sur o g.bo (g.bo + 1) { g with bo := g.bo + 2 } = some ((s0, s1), g')) (hd : g.drop = false) :
    s0.lok = sur.lok ∧ s1.lok = sur.lok ∧ NCopy sur.ned s0.ned ∧ NCopy sur.ned s1.ned ∧
    Distinct s0.ned ∧ Distinct s1.ned ∧ (∀ x, NMem s0.ned x → ¬ NMem s1.ned x) ∧
    (∀ x, NMem s0.ned x ∨ NMem s1.ned x → g.re ≤ x ∧ x < g'.re) ∧
    g.re ≤ g'.re ∧ g'.bo = g.bo + 3 ∧ g'.drop = g.drop ∧ g'.cond = g.cond ∧ g'.id = g.id ∧
    HoonMap.get g'.blocks g.bo = some ⟨[], [], Termin.hop ⟨(flattenNeed s0.ned).map some, g.bo + 2⟩⟩ ∧
    HoonMap.get g'.blocks (g.bo + 1) = some ⟨[], [], Termin.hop ⟨(flattenNeed s1.ned).map some, g.bo + 2⟩⟩ ∧
    HoonMap.get g'.blocks (g.bo + 2) = some ⟨flattenNeed sur.ned, [], Termin.hop (jmp0 o)⟩ ∧
    ∀ k, k < g.bo → HoonMap.get g'.blocks k = HoonMap.get g.blocks k := by
  unfold forkSure at h
  obtain ⟨⟨n0, n1⟩, gK, hK, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  unfold forkNeed at hK
  obtain ⟨⟨m0, m1⟩, gN, hN, h⟩ := bind_some hK
  obtain ⟨⟨k, eN⟩, c0, c1, d0, d1, j01, r01⟩ := forkNeedGo_spec _ _ _ _ _ hN
  subst eN
  simp only [bind_apply, emit_apply, Option.bind_some, pure_apply] at h
  simp only [emir, Gen.emitted, hd, Bool.false_eq_true, if_false, Option.bind_some, pure_apply,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  simp only at r01
  refine ⟨rfl, rfl, c0, c1, d0, d1, j01, r01, by simp, by simp, hd.symm, rfl, rfl, ?_, ?_, ?_, fun k' hk' => ?_⟩
  · simp [HoonMap.get_put]
  · simp [HoonMap.get_put]
  · simp [HoonMap.get_put]
  · simp [HoonMap.get_put, show k' ≠ g.bo + 1 by omega, show k' ≠ g.bo by omega, show k' ≠ g.bo + 2 by omega]

/-! ## The join -/

section Join
variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ}

/-- **Entering a fork block with a copy of the need held** enters the
goal's block with the need held and the other registers unchanged. -/
theorem goJ_fork {o0 barg : Nat} {ned n : Need} {th : Jmp} (hth : th.args = [])
    (h0 : HoonMap.get c.blocks o0 = some ⟨[], [], Termin.hop ⟨(flattenNeed n).map some, barg⟩⟩)
    (hb : HoonMap.get c.blocks barg = some ⟨flattenNeed ned, [], Termin.hop (jmp0 th.there)⟩)
    (hc : NCopy ned n) (hd : Distinct ned) (hj : ∀ x, NMem n x → ¬ NMem ned x)
    {R : Map (Option Noun)} {v : Noun} (hh : HoldsN n R v) (t : Trace) :
    ∃ R', HoldsN ned R' v ∧ (∀ x, ¬ NMem ned x → SkaModel.read x R' = SkaModel.read x R) ∧
      goJ lib O c gul st R t (jmp0 o0) = goJ lib O c gul st R' t th := by
  obtain ⟨R', e, h', k⟩ := evalPassLoop_copy ned n hc R v hh hd hj
  rcases th with ⟨targs, there⟩
  simp only at hth
  subst hth
  have ep : evalPass ((flattenNeed n).map some) (flattenNeed ned) R = some R' := by
    unfold evalPass
    rw [if_pos, e]
    simp only [List.all_map, List.all_eq_true, Function.comp_apply]
    intro x hx
    rw [Bool.not_eq_true', Bool.eq_false_iff]
    intro hm
    exact hj x ((mem_flatten n x).mp hx) ((mem_flatten ned x).mp (by simpa using hm))
  refine ⟨R', h', k, ?_⟩
  rw [goJ_jmp0 _ _ _ _ h0, execBlob_hop]
  simp only [goJ, hb, Option.bind_some]
  rw [execBlob]
  split
  · rw [ep]
    exact execBlob_hop _ _ _
  · rename_i hn
    simp only [ne_eq, not_or, Decidable.not_not] at hn
    rw [hn.1] at ep
    simp only [evalPass, List.all_nil, if_true, evalPassLoop, hn.2] at ep
    cases ep
    rfl

end Join

/-! ## `+sect` when the branches made no proxy -/

/-- `g'` is `g` with the same blocks at every label. -/
def SameBlocks (g g' : Gen Map) : Prop :=
  g'.re = g.re ∧ g'.bo = g.bo ∧ g'.id = g.id ∧ g'.drop = g.drop ∧ g'.tags = g.tags ∧ g'.cond = g.cond ∧
    ∀ k, HoonMap.get g'.blocks k = HoonMap.get g.blocks k

theorem SameBlocks.trans {g0 g1 g2 : Gen Map} (a : SameBlocks g0 g1) (b : SameBlocks g1 g2) : SameBlocks g0 g2 :=
  ⟨b.1.trans a.1, b.2.1.trans a.2.1, b.2.2.1.trans a.2.2.1, b.2.2.2.1.trans a.2.2.2.1,
    b.2.2.2.2.1.trans a.2.2.2.2.1, b.2.2.2.2.2.1.trans a.2.2.2.2.2.1,
    fun k => (b.2.2.2.2.2.2 k).trans (a.2.2.2.2.2.2 k)⟩

theorem lensHop_self {b : Blob} {t : Jmp} (h : b.fin = Termin.hop t) : lensHop t.args b = some b := by
  rcases b with ⟨p, bd, f⟩
  simp only at h; subst h; simp [lensHop]

theorem jabBlock_same {o : Nat} {f : Blob → Option Blob} {g g' : Gen Map}
    (hf : ∀ b, HoonMap.get g.blocks o = some b → f b = some b) (h : jabBlock o f g = some ((), g')) :
    SameBlocks g g' := by
  unfold jabBlock at h
  obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
  rw [hf b hb] at h
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun k => ?_⟩
  by_cases e : k = o
  · subst e; simp [HoonMap.get_put, hb]
  · simp [HoonMap.get_put, e]

/-- **The threading of `+sect` puts every block back** when the branches
made no proxy. -/
theorem sectThread_same {rid o0 o1 : Nat} {cnd : Map (Nat × List Nat)} {g g' : Gen Map} {u : Unit}
    (hc : g.cond = cnd) (h : sectThread rid o0 o1 cnd cnd g = some (u, g')) : SameBlocks g g' := by
  subst hc
  unfold sectThread at h
  simp only [keys_difM_self, List.foldlM_nil] at h
  obtain ⟨b0, hb0, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b1, hb1, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · rename_i t0 t1 e0 e1
    split at h
    · cases h
    · obtain ⟨bt, hbt, h⟩ := Option.bind_eq_some_iff.mp h
      simp only [bind_apply, pure_apply, Option.bind_some] at h
      obtain ⟨⟨_, gA⟩, hA, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨_, gB⟩, hB, hC⟩ := Option.bind_eq_some_iff.mp h
      have kA := jabBlock_same (fun b hb => by rw [hbt] at hb; cases hb; rfl) hA
      have kB := jabBlock_same (fun b hb => by
        rw [kA.2.2.2.2.2.2, hb0] at hb; cases hb; exact lensHop_self e0) hB
      have kC := jabBlock_same (fun b hb => by
        rw [kB.2.2.2.2.2.2, kA.2.2.2.2.2.2, hb1] at hb; cases hb; exact lensHop_self e1) hC
      cases u
      exact kA.trans (kB.trans kC)
  · cases h

end Comp
end SkaModel
end Formalization
