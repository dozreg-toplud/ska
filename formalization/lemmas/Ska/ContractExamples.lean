import lemmas.Ska.Contract
import lemmas.Ska.MinkTrace

/-!
# The contract holds of code like the compiler's

Two pieces of IR, proved to satisfy both halves of the contract, as evidence
that the contract can be met by code of the kind `+comp` emits:

* `tail_fwd`, `tail_bwd`: the formula `[2 [0 1] 1 g]`, compiled to a tail
  call `[%jmp g' ~[0]]` of a bell `g'` with formula `g` that the subject fits,
  whose need is `[%this ~]`.  This exercises the call oracle and the needs.
* `nok_fwd`, `nok_bwd`: the formula `[2 b c]`, compiled to three indirect
  calls, `%nok`, of `b`, `c` and then of their products.  This exercises the
  indirect call oracle, its empty trace and its crash traces on top of the
  caller's.
-/

set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel

open Nock

section
variable {Map : Type → Type} [HoonMap Map]

theorem read_store (r r' : Nat) (v : Noun) (regs : Map (Option Noun)) :
    SkaModel.read r (store r' v regs) = if r = r' then some v else SkaModel.read r regs := by
  by_cases h : r = r'
  · subst h; simp [read_store_self]
  · simp [read_store_other h, h]

theorem read_put (r r' : Nat) (v : Noun) (regs : Map (Option Noun)) :
    SkaModel.read r (HoonMap.put regs r' (some v)) = if r = r' then some v else SkaModel.read r regs :=
  read_store r r' v regs

/-- A function of one block, entered with the whole subject in register 0. -/
def oneBlock (b : Blob) : Straight Map := ⟨NeedOrd.this, 1, HoonMap.put HoonMap.empty 0 b⟩

theorem execEntry_oneBlock (lib : Lib) {σ : Type} (O : Oracle σ) (st : σ) (b : Blob)
    (s : Noun) (t : Trace) (gul : Noun) :
    execEntry lib O st (oneBlock (Map := Map) b) [s] t gul =
      execBlob lib O (oneBlock (Map := Map) b) gul st (HoonMap.put HoonMap.empty 0 (some s)) t b [] := by
  simp [execEntry, oneBlock, HoonMap.get_put, regsOf, regsFrom]

theorem execBlob_body {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun}
    {st : σ} {regs : Map (Option Noun)} {t : Trace} (p : Pole) (rest : List Pole) (fin : Termin) :
    execBlob lib O c gul st regs t ⟨[], p :: rest, fin⟩ [] =
      (execPole lib O gul st p regs t).bind fun (ton, regs', t', st') =>
        match ton with
        | Tone.zero _ => execBlob lib O c gul st' regs' t' ⟨[], rest, fin⟩ []
        | _ => some (ton, st') := by
  rw [execBlob]; rfl

theorem minkF_slot1 (lib : Lib) (gul : Noun) (m : Nat) (t : Trace) (s : Noun) :
    minkF lib gul (m + 1) t s (slot 1) = some (Tone.zero s) := by
  simp [minkF_succ_eq, minkStep]

theorem minkF_quote (lib : Lib) (gul : Noun) (m : Nat) (t : Trace) (s g : Noun) :
    minkF lib gul (m + 1) t s (quote g) = some (Tone.zero g) := rfl

/-! ## A tail call -/

/-- The code: jump to `g'` with the subject. -/
def tailCode (g' : Bell) : Straight Map := oneBlock ⟨[], [], Termin.jmp g' [0]⟩

theorem tail_run (lib : Lib) {σ : Type} (O : Oracle σ) (st : σ) (g' : Bell) (s : Noun)
    (t : Trace) (gul : Noun) :
    execEntry lib O st (tailCode (Map := Map) g') [s] t gul = O.call st g' false [s] t gul := by
  rw [tailCode, execEntry_oneBlock, execBlob]
  simp [read, HoonMap.get_put]

theorem tail_fwd (lib : Lib) (N : Needs) (g : Noun) (g' : Bell) (s : Noun)
    (hN : N g' false = some NeedOrd.this) (hfit : Fits g'.less s) (hfol : g'.fol = g) :
    ContractFwd lib N s (n3 (A 2) (slot 1) (quote g)) [s] (tailCode (Map := Map) g') := by
  intro σ Inv ν O n gul ti tm r hle _ hO hmink st hI htr
  rw [tail_run]
  -- `+mink` takes two steps to reach `g`
  match n, hmink with
  | m + 2, hmink =>
    rw [minkF_succ_eq] at hmink
    simp only [minkStep, minkF_slot1, minkF_quote, tbind_zero] at hmink
    have hargs : argsFor (ν st) g' false s = some [s] := by
      simp [argsFor, hle st hI _ _ _ hN, split]
    rw [← hfol] at hmink
    exact hO.call st g' false [s] ti tm gul s (m + 1) r hI (by omega) hfit hargs htr hmink
  | 1, hmink =>
    rw [minkF_succ_eq] at hmink
    simp [minkStep, minkF] at hmink
  | 0, hmink => simp [minkF] at hmink

theorem tail_bwd (lib : Lib) (N : Needs) (g : Noun) (g' : Bell) (s : Noun)
    (hN : N g' false = some NeedOrd.this) (hfit : Fits g'.less s) (hfol : g'.fol = g) :
    ContractBwd lib N s (n3 (A 2) (slot 1) (quote g)) [s] (tailCode (Map := Map) g') := by
  intro σ Inv ν O gul ti tm hle _ hO st ton st' hI htr hrun
  rw [tail_run] at hrun
  have hargs : argsFor (ν st) g' false s = some [s] := by
    simp [argsFor, hle st hI _ _ _ hN, split]
  obtain ⟨r, ⟨k, hk⟩, hrel⟩ := hO.call st g' false [s] ti gul ton st' hI hrun s tm hfit hargs htr
  refine ⟨r, ⟨k + 2, ?_⟩, hrel⟩
  rw [minkF_succ_eq]
  simp only [minkStep, minkF_slot1, minkF_quote, tbind_zero]
  rw [← hfol]
  exact minkF_le lib gul (Nat.le_succ k) _ _ _ _ hk

/-! ## Indirect calls -/

section
variable {σ : Type} {lib : Lib} {Inv : σ → Prop} {ν : σ → Needs} {O : Oracle σ}

theorem execPole_imm (gul : Noun) (st : σ) (n : Noun) (d : Nat) (regs : Map (Option Noun)) (t : Trace) :
    execPole lib O gul st (Pole.imm n d) regs t = some (Tone.zero (A 0), store d n regs, t, st) :=
  rfl

/-- The outcome of an indirect call against `+mink`'s: the product stored,
or a tone that stands for `+mink`'s, which ends the block. -/
def NokOut (lib : Lib) (N : Needs) (d : Nat) (regs : Map (Option Noun)) (ton : Tone) (regs' : Map (Option Noun))
    (r : Tone) : Prop :=
  (∃ p, r = Tone.zero p ∧ ton = Tone.zero (A 0) ∧ regs' = store d p regs) ∨
    ((∀ p, r ≠ Tone.zero p) ∧ (∀ p, ton ≠ Tone.zero p) ∧ ToneRel lib N ton r)

theorem nokOut_of_rel {N : Needs} {d : Nat} {regs : Map (Option Noun)} {ti tm : Trace} {ton0 r0 : Tone}
    (hrel : ToneRel lib N ton0 r0) (htr : Forall2 (FrameRel lib N) ti tm) :
    NokOut lib N d regs (match ton0 with
        | Tone.zero _ => Tone.zero (A 0)
        | Tone.one b => Tone.one b
        | Tone.two tr => Tone.two (tr ++ ti))
      (match ton0 with
        | Tone.zero p => store d p regs
        | _ => regs) (r0.app tm) := by
  cases hrel with
  | zero p => exact Or.inl ⟨p, rfl, rfl, rfl⟩
  | one p =>
    exact Or.inr ⟨fun _ h => Tone.noConfusion h, fun _ h => Tone.noConfusion h, ToneRel.one p⟩
  | two hl =>
    exact Or.inr ⟨fun _ h => Tone.noConfusion h, fun _ h => Tone.noConfusion h,
      ToneRel.two (Forall2.append hl htr)⟩

theorem nok_step_fwd {n : Nat} (hO : OracleFwd lib Inv ν O n) (hS : OracleSteps Inv ν O)
    {gul : Noun} {st : σ} {regs : Map (Option Noun)} {ti tm : Trace} {u f d : Nat} {x y : Noun} {j : Nat}
    {r : Tone} (hI : Inv st) (htr : Forall2 (FrameRel lib (ν st)) ti tm)
    (hu : read u regs = some x) (hf : read f regs = some y) (hj : j < n)
    (hm : minkF lib gul j tm x y = some r) :
    ∃ ton regs' st', execPole lib O gul st (Pole.nok u f d) regs ti = some (ton, regs', ti, st') ∧
      Inv st' ∧ ν st ≤ ν st' ∧ NokOut lib (ν st') d regs ton regs' r := by
  rw [minkF_trace] at hm
  obtain ⟨r0, hm0, rfl⟩ := Option.map_eq_some_iff.mp hm
  obtain ⟨ton0, st', hn, hrel⟩ := hO.nok st x y gul j r0 hI hj hm0
  obtain ⟨hI', hle⟩ := hS.nok st x y gul ton0 st' hI hn
  refine ⟨_, _, st', ?_, hI', hle, nokOut_of_rel hrel (htr.imp fun _ _ => FrameRel.mono hle)⟩
  simp only [execPole, hu, hf, hn, Option.bind_some]
  cases ton0 <;> rfl

theorem nok_step_bwd (hO : OracleBwd lib Inv ν O) (hS : OracleSteps Inv ν O)
    {gul : Noun} {st st' : σ} {regs regs' : Map (Option Noun)} {ti tm t' : Trace} {u f d : Nat}
    {x y : Noun} {ton : Tone} (hI : Inv st) (htr : Forall2 (FrameRel lib (ν st)) ti tm)
    (hu : read u regs = some x) (hf : read f regs = some y)
    (h : execPole lib O gul st (Pole.nok u f d) regs ti = some (ton, regs', t', st')) :
    Inv st' ∧ ν st ≤ ν st' ∧ t' = ti ∧ ∃ r, Mink lib gul tm x y r ∧
      NokOut lib (ν st') d regs ton regs' r := by
  simp only [execPole, hu, hf, Option.bind_some, Option.bind_eq_some_iff] at h
  obtain ⟨⟨ton0, st1⟩, hn, h⟩ := h
  obtain ⟨hI', hle⟩ := hS.nok st x y gul ton0 st1 hI hn
  obtain ⟨r0, ⟨k, hk⟩, hrel⟩ := hO.nok st x y gul ton0 st1 hI hn
  have hout := nokOut_of_rel (d := d) (regs := regs) hrel (htr.imp fun _ _ => FrameRel.mono hle)
  have hmt : Mink lib gul tm x y (r0.app tm) := ⟨k, by rw [minkF_trace, hk]; rfl⟩
  cases ton0 <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h <;> exact ⟨hI', hle, rfl, _, hmt, hout⟩

end

/-- The code of `[2 b c]`: `b` and `c` by indirect calls, then their
products by a third. -/
def nokCode (b c : Noun) : Straight Map :=
  oneBlock ⟨[], [Pole.imm b 1, Pole.nok 0 1 2, Pole.imm c 3, Pole.nok 0 3 4, Pole.nok 2 4 5],
    Termin.don 5⟩

theorem tbind_nonzero {x : Tone} (h : ∀ p, x ≠ Tone.zero p) (k : Noun → Option Tone) :
    tbind (some x) k = some x := by
  cases x with
  | zero p => exact absurd rfl (h p)
  | one _ => rfl
  | two _ => rfl

theorem nok_fwd (lib : Lib) (N : Needs) (s b c : Noun) :
    ContractFwd lib N s (n3 (A 2) b c) [s] (nokCode (Map := Map) b c) := by
  intro σ Inv ν O n gul ti tm r _ hS hO hmink st hI htr
  match n, hmink with
  | 0, hmink => simp [minkF] at hmink
  | m + 1, hmink =>
  rw [minkF_succ_eq] at hmink
  simp only [minkStep] at hmink
  rw [nokCode, execEntry_oneBlock, execBlob_body, execPole_imm, Option.bind_some]
  simp only
  rw [execBlob_body]
  cases hb : minkF lib gul m tm s b with
  | none => rw [hb] at hmink; simp at hmink
  | some rb =>
  rw [hb] at hmink
  obtain ⟨ton1, regs2, st1, hp1, hI1, hle1, hout1⟩ := nok_step_fwd (u := 0) (f := 1) (d := 2) (x := s) (y := b)
    (regs := (store 1 b (HoonMap.put HoonMap.empty 0 (some s)) : Map (Option Noun))) hO hS hI htr
    (by simp [read_store, read_put]) (by simp [read_store, read_put])
    (Nat.lt_succ_self m) hb
  rw [hp1, Option.bind_some]
  simp only
  rcases hout1 with ⟨s', rfl, rfl, rfl⟩ | ⟨hr1, ht1, hrel1⟩
  · simp only [tbind_zero] at hmink
    simp only
    rw [execBlob_body, execPole_imm, Option.bind_some]
    simp only
    rw [execBlob_body]
    have htr1 := htr.imp fun _ _ => FrameRel.mono hle1
    cases hc : minkF lib gul m tm s c with
    | none => rw [hc] at hmink; simp at hmink
    | some rc =>
    rw [hc] at hmink
    obtain ⟨ton2, regs4, st2, hp2, hI2, hle2, hout2⟩ := nok_step_fwd (u := 0) (f := 3) (d := 4) (x := s) (y := c)
      (regs := (store 3 c (store 2 s' (store 1 b (HoonMap.put HoonMap.empty 0 (some s)))) : Map (Option Noun))) hO hS hI1 htr1
      (by simp [read_store, read_put]) (by simp [read_store, read_put])
      (Nat.lt_succ_self m) hc
    rw [hp2, Option.bind_some]
    simp only
    rcases hout2 with ⟨f', rfl, rfl, rfl⟩ | ⟨hr2, ht2, hrel2⟩
    · simp only [tbind_zero] at hmink
      simp only
      rw [execBlob_body]
      have htr2 := htr1.imp fun _ _ => FrameRel.mono hle2
      obtain ⟨ton3, regs5, st3, hp3, hI3, hle3, hout3⟩ := nok_step_fwd (u := 2) (f := 4) (d := 5) (x := s') (y := f')
        (regs := (store 4 f' (store 3 c (store 2 s' (store 1 b (HoonMap.put HoonMap.empty 0 (some s))))) : Map (Option Noun)))
        hO hS hI2 htr2
        (by simp [read_store, read_put]) (by simp [read_store, read_put])
        (Nat.lt_succ_self m) hmink
      rw [hp3, Option.bind_some]
      simp only
      rcases hout3 with ⟨p, rfl, rfl, rfl⟩ | ⟨hr3, ht3, hrel3⟩
      · refine ⟨Tone.zero p, st3, ?_, ToneRel.zero p⟩
        simp only
        rw [execBlob]
        simp [read_store, read_put]
      · cases ton3 with
        | zero p => exact absurd rfl (ht3 p)
        | one _ => exact ⟨_, st3, rfl, hrel3⟩
        | two _ => exact ⟨_, st3, rfl, hrel3⟩
    · rw [tbind_nonzero hr2] at hmink
      cases hmink
      cases ton2 with
        | zero p => exact absurd rfl (ht2 p)
        | one _ => exact ⟨_, st2, rfl, hrel2⟩
        | two _ => exact ⟨_, st2, rfl, hrel2⟩
  · rw [tbind_nonzero hr1] at hmink
    cases hmink
    cases ton1 with
        | zero p => exact absurd rfl (ht1 p)
        | one _ => exact ⟨_, st1, rfl, hrel1⟩
        | two _ => exact ⟨_, st1, rfl, hrel1⟩


theorem nonzero_cont {σ : Type} {t : Tone} {k : Option (Tone × σ)}
    {st st' : σ} {ton : Tone}
    (h : (match t with | Tone.zero _ => k | _ => some (t, st)) = some (ton, st'))
    (ht : ∀ p, t ≠ Tone.zero p) : ton = t ∧ st' = st := by
  cases t with
  | zero p => exact absurd rfl (ht p)
  | one _ => simp only [Option.some.injEq, Prod.mk.injEq] at h; exact ⟨h.1.symm, h.2.symm⟩
  | two _ => simp only [Option.some.injEq, Prod.mk.injEq] at h; exact ⟨h.1.symm, h.2.symm⟩

theorem nok_bwd (lib : Lib) (N : Needs) (s b c : Noun) :
    ContractBwd lib N s (n3 (A 2) b c) [s] (nokCode (Map := Map) b c) := by
  intro σ Inv ν O gul ti tm _ hS hO st ton st' hI htr hrun
  rw [nokCode, execEntry_oneBlock, execBlob_body, execPole_imm, Option.bind_some] at hrun
  simp only at hrun
  rw [execBlob_body] at hrun
  obtain ⟨⟨t1, regs2, tr2, st1⟩, hp1, hrun1⟩ := Option.bind_eq_some_iff.mp hrun
  clear hrun
  obtain ⟨hI1, hle1, rfl, r1, ⟨k1, hk1⟩, hout1⟩ := nok_step_bwd (u := 0) (f := 1) (x := s) (y := b)
    (regs := (store 1 b (HoonMap.put HoonMap.empty 0 (some s)) : Map (Option Noun))) hO hS hI htr
    (by simp [read_store, read_put]) (by simp [read_store, read_put]) hp1
  simp only at hrun1
  rcases hout1 with ⟨s', rfl, rfl, rfl⟩ | ⟨hr1, ht1, hrel1⟩
  · simp only at hrun1
    rw [execBlob_body, execPole_imm, Option.bind_some] at hrun1
    simp only at hrun1
    rw [execBlob_body] at hrun1
    have htr1 := htr.imp fun _ _ => FrameRel.mono hle1
    obtain ⟨⟨t2, regs4, tr4, st2⟩, hp2, hrun2⟩ := Option.bind_eq_some_iff.mp hrun1
    clear hrun1
    obtain ⟨hI2, hle2, rfl, r2, ⟨k2, hk2⟩, hout2⟩ := nok_step_bwd (u := 0) (f := 3) (x := s) (y := c)
      (regs := (store 3 c (store 2 s' (store 1 b (HoonMap.put HoonMap.empty 0 (some s)))) : Map (Option Noun)))
      hO hS hI1 htr1 (by simp [read_store, read_put]) (by simp [read_store, read_put]) hp2
    simp only at hrun2
    rcases hout2 with ⟨f', rfl, rfl, rfl⟩ | ⟨hr2, ht2, hrel2⟩
    · simp only at hrun2
      rw [execBlob_body] at hrun2
      have htr2 := htr1.imp fun _ _ => FrameRel.mono hle2
      obtain ⟨⟨t3, regs5, tr5, st3⟩, hp3, hrun3⟩ := Option.bind_eq_some_iff.mp hrun2
      clear hrun2
      obtain ⟨hI3, hle3, rfl, r3, ⟨k3, hk3⟩, hout3⟩ := nok_step_bwd (u := 2) (f := 4) (x := s')
        (y := f')
        (regs := (store 4 f' (store 3 c (store 2 s' (store 1 b (HoonMap.put HoonMap.empty 0 (some s)))))
          : Map (Option Noun)))
        hO hS hI2 htr2 (by simp [read_store, read_put]) (by simp [read_store, read_put]) hp3
      simp only at hrun3
      have hm : ∀ K, k1 ≤ K → k2 ≤ K → k3 ≤ K → minkF lib gul (K + 1) tm s (n3 (A 2) b c) =
          minkF lib gul K tm s' f' := by
        intro K h1 h2 h3
        rw [minkF_succ_eq]
        simp only [minkStep]
        rw [minkF_le lib gul h1 _ _ _ _ hk1, tbind_zero, minkF_le lib gul h2 _ _ _ _ hk2,
          tbind_zero]
      rcases hout3 with ⟨p, rfl, rfl, rfl⟩ | ⟨hr3, ht3, hrel3⟩
      · simp only at hrun3
        rw [execBlob] at hrun3
        simp [read_store, read_put] at hrun3
        obtain ⟨rfl, rfl⟩ := hrun3
        refine ⟨Tone.zero p, ⟨max k1 (max k2 k3) + 1, ?_⟩, ToneRel.zero p⟩
        rw [hm _ (by omega) (by omega) (by omega)]
        exact minkF_le lib gul (by omega) _ _ _ _ hk3
      · obtain ⟨rfl, rfl⟩ := nonzero_cont hrun3 ht3
        refine ⟨r3, ⟨max k1 (max k2 k3) + 1, ?_⟩, hrel3⟩
        rw [hm _ (by omega) (by omega) (by omega)]
        exact minkF_le lib gul (by omega) _ _ _ _ hk3
    · obtain ⟨rfl, rfl⟩ := nonzero_cont hrun2 ht2
      refine ⟨r2, ⟨max k1 k2 + 1, ?_⟩, hrel2⟩
      rw [minkF_succ_eq]
      simp only [minkStep]
      rw [minkF_le lib gul (Nat.le_max_left _ _) _ _ _ _ hk1, tbind_zero,
        minkF_le lib gul (Nat.le_max_right _ _) _ _ _ _ hk2, tbind_nonzero hr2]
  · obtain ⟨rfl, rfl⟩ := nonzero_cont hrun1 ht1
    refine ⟨r1, ⟨k1 + 1, ?_⟩, hrel1⟩
    rw [minkF_succ_eq]
    simp only [minkStep]
    rw [hk1, tbind_nonzero hr1]

end

end SkaModel
end Formalization
