import lemmas.Ska.CompIndirectTop
import lemmas.Ska.CompCallStep

/-!
# The first call theorem: the indirect call `[2 b c]`, forward

README Gaps 12.11 (fifteenth session).  `indirectTop_fwd`: the whole-subject
code of the nomm `[2 p q]` of the formula `[2 b c]` (`Annot.indirect`), with
`p` and `q` in `FragU`, meets the forward half of the contract on the subject
whole, against any needs.  The proof: `runLC_n2_none` takes the run apart,
`indirect_prefix` computes the blocks before the two runs, `indirect_mid`
composes the runs of `p` and `q` (`RunOKNV` of the cons `[p q]` for the goal
`%next [[2 3] ~]` into the `%nok` block), and `finishTop_gen` gives the
entry with the property `fwdPhi`: from the run's jump, the code goes on at
the `%nok` block with the products of `p` and `q` in `2` and `3` (`goJ_nok`),
the oracle's `nok` answers as `+mink` on the product subject and formula
with one less fuel (`OracleFwd.nok`, `minkF_trace` for the caller's trace
below a crash's), the product goes to `1`, is moved to `0` and returned.

`IndirectTopFwd` (`CompIndirect.lean`) asks this for every `Annot` of the
nomm `[2 p q]`, and is false as stated: `Annot.bare` gives that nomm with
`p` the subject and `q` the formula `f` itself (`[11 %bare g]`), whose code
makes one `nok` of `f` on the subject, which `+mink` runs with all `n` of
its fuel, outside the bound `j < n` of `OracleFwd`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- What the code does from a point, for the forward contract on `[s f]`
against the needs `N`. -/
def fwdPhi (lib : Lib) (N : Needs) (P : Noun → Prop) (f : Noun) :
    (σ : Type) → Oracle σ → σ → Trace → Noun → Noun → Option (Tone × σ) → Prop :=
  fun σ O st t gul s x => ∀ (Inv : σ → Prop) (ν : σ → Needs) (n : Nat) (tm : Trace) (r : Tone),
    P s → (∀ st, Inv st → N ≤ ν st) → OracleSteps Inv ν O → OracleFwd lib Inv ν O n →
    minkF lib gul n tm s f = some r → Inv st → Forall2 (FrameRel lib (ν st)) t tm →
    ∃ ton st', x = some (ton, st') ∧ ToneRel lib (ν st') ton r

/-- **`+mink` on `[2 b c]` with pure parts**: the subject and the formula
are the parts' values, and the product formula runs with one less fuel; a
part with no value is a crash with the caller's trace. -/
theorem minkF_n2_pure {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {P : Noun → Prop}
    {b c : Noun} {p q : Nomm} (hp : p.pure = true) (hq : q.pure = true) (hAp : Annot lib code P b p)
    (hAq : Annot lib code P c q) {s : Noun} (hs : P s) {gul : Noun} {n : Nat} {tm : Trace} {r : Tone}
    (h : minkF lib gul n tm s (n3 (A 2) b c) = some r) :
    (∃ n' x y, n = n' + 1 ∧ pureEval p s = some x ∧ pureEval q s = some y ∧ minkF lib gul n' tm x y = some r) ∨
      (((pureEval p s).bind fun x => (pureEval q s).bind fun y => some (C x y)) = Option.none ∧ r = Tone.two tm) := by
  cases n with
  | zero => simp [minkF] at h
  | succ n' =>
    rw [minkF_succ_eq] at h
    simp only [minkStep] at h
    have h1 : ∀ y, minkF lib gul n' tm s b = some y → y = toneOf tm (pureEval p s) := fun y hy =>
      (mink_pure hok hp hAp hs gul tm y).mp ⟨n', hy⟩
    rcases tbind_toneOf_inv h1 h with ⟨x, ex, h⟩ | ⟨ex, er⟩
    · have h2 : ∀ y, minkF lib gul n' tm s c = some y → y = toneOf tm (pureEval q s) := fun y hy =>
        (mink_pure hok hq hAq hs gul tm y).mp ⟨n', hy⟩
      rcases tbind_toneOf_inv h2 h with ⟨y, ey, h⟩ | ⟨ey, er⟩
      · exact Or.inl ⟨n', x, y, rfl, ex, ey, h⟩
      · exact Or.inr ⟨by rw [ex, ey]; rfl, er⟩
    · exact Or.inr ⟨by rw [ex]; rfl, er⟩

/-- **The code of the indirect call from the run's jump meets `fwdPhi`**,
on every program that agrees with the run's blocks. -/
theorem indirect_sem {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {P : Noun → Prop}
    {fb fc : Noun} {p q : Nomm} (hp : p.pure = true) (hq : q.pure = true) (hAp : Annot lib code P fb p)
    (hAq : Annot lib code P fc q) (N : Needs) {g3 g6 : Gen Map} {nex : NextL S}
    (Rm : RunOKNV lib (Nomm.cons p q) (pairSure 2 3 : Sure S) (jmp0 3) g3 g6 nex)
    (hre : g3.re = 4) (hbo : g3.bo = 4) (hcn : ∀ k, HoonMap.get g3.cond k = Option.none)
    (hb1 : HoonMap.get g3.blocks 1 = some ⟨[], [], Termin.don 0⟩)
    (hb2 : HoonMap.get g3.blocks 2 = some ⟨[], [Pole.mov 1 0], Termin.hop (jmp0 1)⟩)
    (hb3 : HoonMap.get g3.blocks 3 = some ⟨[], [Pole.nok 2 3 1], Termin.hop (jmp0 2)⟩) :
    ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g6.re → HoonMap.get cf k = HoonMap.get g6.cond k) →
      ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s : Noun),
      AgreeU lib O c gul st t cf ned gen0 g6 nex.laz s s → (∀ r, NMem ned r → g6.re ≤ r) →
      ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s →
      fwdPhi lib N P (n3 (A 2) fb fc) σ O st t gul s (goJ lib O c gul st regs t nex.th) := by
  intro cf hcf c ned σ O st t gul s ag hned regs hh hn Inv ν n tm r hs hN hS hF hm hI htr
  -- the blocks 1, 2, 3 of the program
  have u : ∀ k, k < 4 → unproxy cf k = k := fun k hk => unproxy_none (by
    rw [hcf k (by have := Rm.ext.1; omega)]
    rcases Rm.cfr.2 k with e | ⟨l, _⟩
    · rw [e]; exact hcn k
    · omega)
  have cb : ∀ k blk, 1 ≤ k → k < 4 → HoonMap.get g3.blocks k = some blk →
      HoonMap.get c.blocks k = some (unproxyBlob cf blk) := fun k blk k1 k4 hk => by
    rw [ag.1 k (by simp [gen0]; omega) (by have := Rm.ext.2.1; omega) (fun hm => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
      have := (Rm.labs e he).1; omega), Rm.ext.2.2.2 k (by omega), hk]; rfl
  have c1 := cb 1 _ (by omega) (by omega) hb1
  have c2 := cb 2 _ (by omega) (by omega) hb2
  have c3 := cb 3 _ (by omega) (by omega) hb3
  simp only [unproxyBlob, renBlob, List.map_cons, List.map_nil, renPole, renFin, renJmp, jmp0,
    u 0 (by omega), u 1 (by omega), u 2 (by omega), u 3 (by omega)] at c1 c2 c3
  -- the runs of the two parts
  have ag' : AgreeU lib O c gul st t cf ned g3 g6 nex.laz s s :=
    ⟨fun o' l u' hnl => ag.1 o' (by simp [gen0]; omega) u' hnl, ag.2⟩
  have G := Rm.sem cf hcf c ned σ O st t gul s s ag' hned regs hh hn
  rw [pureEval_cons] at G
  rcases minkF_n2_pure hok hp hq hAp hAq hs hm with ⟨n', x, y, rfl, ex, ey, hm'⟩ | ⟨en, er⟩
  · rw [ex, ey] at G
    simp only [Option.bind_some] at G
    obtain ⟨regs', ⟨h2, h3⟩, -, e⟩ := G.1 ⟨⟨trivial, trivial⟩, looks_empty _⟩
    rw [e, goJ_nok (o := 3) (out := 2) c3 st regs' t h2 h3]
    rw [minkF_trace] at hm'
    obtain ⟨r0, h0, rfl⟩ := Option.map_eq_some_iff.mp hm'
    obtain ⟨ton, st', hO, hrel⟩ := hF.nok st x y gul n' r0 hI (Nat.lt_succ_self n') h0
    obtain ⟨_, hν⟩ := hS.nok st x y gul ton st' hI hO
    rw [hO, Option.bind_some]
    cases hrel with
    | zero p' =>
      refine ⟨Tone.zero p', st', ?_, ToneRel.zero p'⟩
      show goJ lib O c gul st' (SkaModel.store 1 p' regs') t (jmp0 2) = some (Tone.zero p', st')
      rw [goJ_jmp0 _ _ _ _ c2, execBlob_cons]
      rw [execPole_local lib O gul st' _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]
      have hm1 : SkaModel.move 1 0 (SkaModel.store 1 p' regs') =
          some (HoonMap.put (SkaModel.store 1 p' regs') 0 (some p')) := by
        simp [SkaModel.move, SkaModel.store, HoonMap.get_put]
      simp only [localPole, hm1, Option.bind_some, Option.map_some]
      rw [execBlob_hop]
      simp [goJ, c1, execBlob_don', SkaModel.read, HoonMap.get_put]
    | one p' => exact ⟨Tone.one p', st', rfl, ToneRel.one p'⟩
    | two hl => exact ⟨_, st', rfl, ToneRel.two (Forall2.append hl (frames_mono hν htr))⟩
  · rw [en] at G
    exact ⟨Tone.two t, st, G, by rw [er]; exact ToneRel.two htr⟩

/-- **The first call theorem** (forward): the whole-subject code of the
nomm `[2 p q]` of the formula `[2 b c]`, with `p` and `q` in `FragU` and at
most 255 `%6` in all, has the input need `this` and meets the forward half
of the contract on the subject whole, on every subject that fits the bell,
against any needs. -/
theorem indirectTop_fwd {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {bl : Bell}
    {fb fc : Noun} {p q : Nomm} (hfol : bl.fol = n3 (A 2) fb fc)
    (hAp : Annot lib code (SkaModel.Fits bl.less) fb p) (hAq : Annot lib code (SkaModel.Fits bl.less) fc q)
    (hp : FragU (S := S) p) (hq : FragU (S := S) q) (hcount : sixCount p + sixCount q ≤ 255)
    {env : CallEnv} {c : Straight Map} (h : finishLUC (S := S) env (Nomm.n2 p q Option.none) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ ∀ s, SkaModel.Fits bl.less s → ContractFwd lib N s bl.fol [s] c := by
  unfold finishLUC at h
  obtain ⟨⟨nex, gE⟩, hrun, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨⟨o', sub⟩, g8⟩, hk, hts⟩ := Option.bind_eq_some_iff.mp h
  simp only at hts
  obtain ⟨nex0, g1, out, pro, g2, o, g3, nexF, g4, nexF', g5, nexS, g6, h1, h2, h3, h4, h5, h6, h7⟩ :=
    runLC_n2_none hrun
  obtain ⟨rfl, rfl, rfl, e2, r3, b3, d3, cn3, k1, k2, k3, G3, cl3, k0⟩ := indirect_prefix h1 h2 h3
  have pp := fragU_pure hp
  have qp := fragU_pure hq
  rw [runLC_eq env q (Nomm.noCall_of_pure q qp), e2] at h4
  rw [pastL_pure _ _ pp, pure_apply] at h5
  simp only [Option.some.injEq, Prod.mk.injEq] at h5
  obtain ⟨rfl, rfl⟩ := h5
  rw [runLC_eq env p (Nomm.noCall_of_pure p pp), e2] at h6
  have u3 : UpBelow g3 := G3.up upBelow_gen0
  have cb3 : CondBelow g3 := fun k hk => by rw [cn3 k] at hk; simp at hk
  have Rm := indirect_mid (a := 2) (b := 3) (o := 3) lib (runU_uok lib hp) (runU_uok lib hq) (by decide)
    (by omega) (by omega) (by decide) (by omega) hcount d3 u3 cl3 cb3 (cn3 2) (cn3 3) h4 h6 h7
  have T : TopS gE nex :=
    { ext := Ext.trans ⟨Nat.zero_le _, by show 1 ≤ g3.bo; omega, by rw [d3]; rfl, fun o ho => by
        have : o = 0 := by show o = 0; simp [gen0] at ho; omega
        subst this; rw [k0]; exact (HoonMap.get_empty 0).symm⟩ Rm.ext
      grow := G3.trans Rm.grow
      cfr := CondFresh.trans ⟨Nat.zero_le _, fun k => Or.inl (by rw [cn3 k]; exact (HoonMap.get_empty k).symm)⟩
        Rm.cfr
      lo := Rm.lo
      hi := Rm.hi
      args := nextArgs_nil Rm.ent rfl
      regs := fun r hr => ⟨Nat.zero_le _, by
        rcases Rm.regs r hr with e | ⟨_, e⟩
        · simp only [pairSure, NMem] at e; have := Rm.ext.1; omega
        · exact e⟩
      dist := Rm.dist
      eregs := fun e he => ⟨(Rm.eregs e he).1, fun r hr => ⟨Nat.zero_le _, ((Rm.eregs e he).2 r hr).2⟩⟩
      labs := fun e he => ⟨by have := (Rm.labs e he).1; show 1 ≤ e.1; omega, (Rm.labs e he).2⟩
      nodup := Rm.nodup
      ncond := Rm.ncond
      econd := Rm.econd }
  have F := finishTop_gen lib T (fwdPhi lib N (SkaModel.Fits bl.less) (n3 (A 2) fb fc))
    (indirect_sem hok pp qp hAp hAq N Rm r3 b3 cn3 k1 k2 k3)
    (fun σ O st t gul s hfs Inv ν n tm r hs _ _ _ hm _ htr => by
      rcases Rm.nec s hfs with e | ⟨v, ev, hv⟩
      · rcases minkF_n2_pure hok pp qp hAp hAq hs hm with ⟨n', x, y, rfl, ex, ey, _⟩ | ⟨_, er⟩
        · rw [pureEval_cons, ex, ey] at e; simp at e
        · exact ⟨Tone.two t, st, rfl, by rw [er]; exact ToneRel.two htr⟩
      · exfalso
        apply hv
        rw [pureEval_cons] at ev
        obtain ⟨x, -, ev⟩ := Option.bind_eq_some_iff.mp ev
        obtain ⟨y, -, ev⟩ := Option.bind_eq_some_iff.mp ev
        cases ev
        exact ⟨⟨trivial, trivial⟩, looks_empty _⟩)
    hk hts
  refine ⟨F.1, fun s hs σ Inv ν O n gul ti tm r hN hS hF hm st hI htr => ?_⟩
  rw [hfol] at hm
  exact F.2 σ O st s ti gul Inv ν n tm r hs hN hS hF hm hI htr

end Comp
end SkaModel
end Formalization
