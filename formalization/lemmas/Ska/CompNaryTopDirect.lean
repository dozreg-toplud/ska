import lemmas.Ska.CompNaryTopClose
import lemmas.Ska.CompDirectMTailP

/-!
# The n-ary direct call under `%done`

README Gaps 18.15 (c), its `%jmp` half.  In the n-ary code (`runLC`, `mono`
`|`, the case `callL`), a direct call `[2 p q b]` under `%done` allocates the
callee's argument registers `sub` (`+need-ord-alloc-regs` of `bNed`), emits
`[jmp b sub]`, and runs `p` under `%next (ofSure sub) (jmp0 that block)`: `p`
is computed straight into the registers of the split, so on a product of `p`
that does not split by `bNed` the code crashes before the call, where
`+mink` runs the callee.  `SplitsLess b bNed` (every noun that fits the
bell's sock splits by `bNed`) makes that case empty, since the products of
`p` fit the bell (`Annot.direct`): it is a hypothesis on the bell and its
need alone, in place of `CalleeNec`.

* `jmpN_run`: the block `[jmp b sub]` under `%done` meets `RunOKGB` with the
  result `[ofSure sub, jmp0 block]`, for `[2 [0 1] [1 b.fol]]` on subjects
  that fit the bell (`tailStep_fwd`, `tailStep_bwd`; `nec` from
  `SplitsLess` and `fits_of_split`).
* `runLC_tailN`, `tailN_done`: the whole case meets `DoneOK`, with `p` any
  member of track C's class (`LOKS false`), read as `[7 p [2 [0 1] [1
  b.fol]]]` (`minkC7_direct`, `runOKGB_sevenL`), as `tailP_done` does for
  the whole-subject code.
* `finishLFC_contractTailN`, `finishLFC_bellContractTailN`: the n-ary
  contract of a bell whose nomm is such a call, and `tableOK_tailN` the table
  of a bell `[2 p [1 k] b']` calling a member of `CallTreeA` with its four
  entries.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-- **Every noun that fits the bell splits by the need**: a hypothesis on a
bell and its n-ary need only. -/
def SplitsLess (b : Bell) (bNed : NeedOrd) : Prop :=
  ∀ s, SkaModel.Fits b.less s → ∃ vs, SkaModel.split bNed s = some vs

section
variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The block `[jmp b sub]` under `%done` meets `RunOKGB`** with the result
`[ofSure sub, jmp0 block]`, for the tail formula `[2 [0 1] [1 b.fol]]` on
subjects that fit the bell and split by its need. -/
theorem jmpN_run (lib : Lib) {N : Needs} {P : Noun → Prop} {b : Bell} {bNed : NeedOrd}
    (hNf : N b false = some bNed) (hfit : ∀ s, P s → SkaModel.Fits b.less s)
    (hspl : ∀ s, P s → ∃ vs, SkaModel.split bNed s = some vs)
    {g0 gA : Gen Map} {sub : Need}
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcb : CondBelow g0)
    (ha : needOrdAllocRegs bNed g0 = some (sub, gA)) :
    RunOKGB lib N P (tailFol b.fol) (CGoal.done : CGoal S) g0 (gA.emitted ⟨[], [], Termin.jmp b (flattenNeed sub)⟩)
      ⟨ofSure ⟨sub, HoonSet.empty⟩, jmp0 gA.bo⟩ := by
  have hsub := fits_of_split bNed g0 gA sub ha
  obtain ⟨⟨kA, rfl⟩, la, dA, ma⟩ := needOrdAllocRegs_spec bNed _ _ _ ha
  simp only at la ma ⊢
  have qb : ∀ x, HoonMap.get (({ g0 with re := kA } : Gen Map).emitted ⟨[], [], Termin.jmp b (flattenNeed sub)⟩).blocks x =
      if x = g0.bo then some ⟨[], [], Termin.jmp b (flattenNeed sub)⟩ else HoonMap.get g0.blocks x := by
    intro x; simp [Gen.emitted, d0, HoonMap.get_put]
  have GQ : Grow g0 (({ g0 with re := kA } : Gen Map).emitted ⟨[], [], Termin.jmp b (flattenNeed sub)⟩) :=
    (grow_reg g0 kA).trans (grow_emit (fun j hj => by simp [finJumps] at hj))
  have e0 : entries (ofSure ⟨sub, HoonSet.empty⟩ : Lazy S) = [] := entries_ofSure _
  have hl : ∀ x, x < g0.bo → HoonMap.get (({ g0 with re := kA } : Gen Map).emitted
      ⟨[], [], Termin.jmp b (flattenNeed sub)⟩).blocks x = HoonMap.get g0.blocks x := by
    intro x hx; rw [qb, if_neg (by omega)]
  have ofs : (ofSure (⟨sub, HoonSet.empty⟩ : Sure S)).sure = ⟨sub, HoonSet.empty⟩ := by simp [ofSure, sure_mk]
  -- the block of the code, unproxied
  have blocks : ∀ (cf : Map (Nat × List Nat)), (∀ x, x < kA → HoonMap.get cf x = HoonMap.get g0.cond x) →
      ∀ (c : Straight Map), (∀ o, g0.bo ≤ o → o < g0.bo + 1 →
        HoonMap.get c.blocks o = (HoonMap.get (({ g0 with re := kA } : Gen Map).emitted
          ⟨[], [], Termin.jmp b (flattenNeed sub)⟩).blocks o).map (unproxyBlob cf)) →
      HoonMap.get c.blocks g0.bo = some ⟨[], [], Termin.jmp b (flattenNeed sub)⟩ := by
    intro cf hcf c ag
    have hs : ∀ x, NMem sub x → unproxy cf x = x := fun x hx =>
      unproxy_none (by rw [hcf x (ma x hx).2]; exact condBelow_none hcb (ma x hx).1)
    rw [ag _ (Nat.le_refl _) (by omega), qb, if_pos rfl]
    simp only [Option.map_some, unproxyBlob, renBlob, renFin, List.map_nil]
    rw [List.map_congr_left (g := id) (fun x hx => hs x ((mem_flatten sub x).mp hx)), List.map_id]
  refine ⟨⟨by simp only [Gen.emitted]; omega, by simp only [Gen.emitted]; omega, by simp only [Gen.emitted], hl⟩,
    GQ.toU hu, condFresh_of_eq (by simp only [Gen.emitted]; omega) rfl,
    (by simp only [jmp0]; omega), (by simp only [jmp0, Gen.emitted]; omega),
    Or.inl ⟨_, (by simp only [jmp0]; rw [qb, if_pos rfl]), rfl, rfl⟩,
    fun r hr => Or.inr (by rw [ofs] at hr; have := ma r hr; simp only [Gen.emitted]; omega), (by rw [ofs]; exact dA),
    fun e he => (by rw [e0] at he; cases he), fun e he => (by rw [e0] at he; cases he), (by rw [e0]; simp),
    fun s hs hf => absurd (by
      rw [ofs]
      obtain ⟨vs, hv⟩ := hspl s hs
      exact ⟨hsub s vs hv, looks_empty _⟩) hf,
    fun r hr => (by rw [ofs] at hr; exact condBelow_none hcb (ma r hr).1),
    fun e he => (by rw [e0] at he; cases he), ?_, ?_⟩
  · -- forward
    intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    have Bo := blocks cf (fun x hx => hcf x (by simp only [Gen.emitted]; omega)) c
      (fun o h1 h2 => (ag st).1 o h1 (by simp only [Gen.emitted]; omega) (by rw [e0]; simp))
    have hold : HoldsN sub regs s := by have := hh.1; rwa [ofs] at this
    obtain ⟨j, hj, hm'⟩ := minkF_tail hm
    exact tailStep_fwd hS hF hNf ha Bo hI (hN st hI) hold (hfit s hs) htr hj hm'
  · -- backward
    intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    have Bo := blocks cf (fun x hx => hcf x (by simp only [Gen.emitted]; omega)) c
      (fun o h1 h2 => (ag st).1 o h1 (by simp only [Gen.emitted]; omega) (by rw [e0]; simp))
    have hold : HoldsN sub regs s := by have := hh.1; rwa [ofs] at this
    obtain ⟨r, hmk, R⟩ := tailStep_bwd hS hB hNf ha Bo hI (hN st hI) hold (hfit s hs) htr hres
    exact ⟨r, mink_tail_bwd hmk, R⟩

/-- **The run of the n-ary direct call under `%done`, `q` skipped**: the
callee's registers, the block `[jmp b sub]`, `p` under `%next (ofSure sub)`,
`+copy` into the need that asks nothing. -/
theorem runLC_tailN {env : CallEnv} {sup : Option Nomm} {p q : Nomm} {b : Bell} {bNed : NeedOrd}
    {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (hring : env.ring b = Option.none) (hned : env.need b = some bNed)
    (hsof : env.sof (made p sup) p q b bNed = false) (hq : safeFolFol q = true)
    (h : runLC env sup (Nomm.n2 p q (some (b, Option.none))) CGoalL.done region g0 = some (nex, g1)) :
    ∃ sub gA nexS g5, needOrdAllocRegs bNed g0 = some (sub, gA) ∧
      runLC env sup p (CGoalL.next (ofSure ⟨sub, HoonSet.empty⟩) (jmp0 gA.bo)) region
        (gA.emitted ⟨[], [], Termin.jmp b (flattenNeed sub)⟩) = some (nexS, g5) ∧
      copyL nexS (ofSure Sure.bunt) g5 = some (nex, g1) := by
  simp only [runLC, callL, hring, hned, hsof, Bool.false_eq_true, if_false, hq, if_true] at h
  obtain ⟨sub, gA, ha, h⟩ := bind_some h
  obtain ⟨o, g3, hc, h⟩ := bind_some h
  rw [emit_apply] at hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [pure_apply, bind_apply, Option.bind_some] at h
  rw [pastL_bunt] at h
  simp only [pure_apply, Option.bind_some] at h
  obtain ⟨⟨nexS, g5⟩, hp, hc⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨sub, gA, nexS, g5, ha, hp, hc⟩

/-- **The n-ary direct call `[2 p q b]` under `%done` meets `DoneOK`**, from
any state of a compile: `p` meets `LOKS false` (any member of track C's
class, indirect calls included), `q` is skipped and returns the callee's
formula on every subject, the products of `p` fit the bell, the need read is
`N b false`, the call is not soft, and every noun that fits the bell splits
by its need (`SplitsLess`). -/
theorem tailN_done (lib : Lib) {N : Needs} {env : CallEnv} {P : Noun → Prop} {p q : Nomm} {fb fq : Noun}
    {b : Bell} {bNed : NeedOrd} (hring : env.ring b = Option.none) (hned : env.need b = some bNed)
    (hsof : ∀ m, env.sof m p q b bNed = false) (hNf : N b false = some bNed) (hspl : SplitsLess b bNed)
    (Sp : LOKS (S := S) (Map := Map) false lib N env P fb p) (hcount : sixCount p ≤ 255)
    (hq : safeFolFol q = true)
    (hAp : ∀ x gul y, P x → Mink lib gul [] x fb (Tone.zero y) → SkaModel.Fits b.less y)
    (hq1 : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {rc : Tone}, P s → minkF lib gul n tm s fq = some rc →
      rc = Tone.zero b.fol)
    (hq2 : ∀ {s gul : Noun} {tm : Trace}, P s → Mink lib gul tm s fq (Tone.zero b.fol))
    {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (hr : runLC env sup (Nomm.n2 p q (some (b, Option.none))) CGoalL.done region g0 = some (nex, g1)) :
    DoneOK lib N P (n3 (A 2) fb fq) g0 g1 nex := by
  obtain ⟨sub, gA, nexS, g5, ha, hp, hc⟩ := runLC_tailN hring hned (hsof _) hq hr
  have hfit : ∀ s, Img lib P fb s → SkaModel.Fits b.less s := fun s ⟨x, gul, hx, hm⟩ => hAp x gul s hx hm
  have Rq := jmpN_run (S := S) lib (P := Img lib P fb) hNf hfit (fun s hs => hspl s (hfit s hs)) b0 d0 hu hcb ha
  have cl := needOrdAllocRegs_clean bNed g0 gA sub ha
  obtain ⟨⟨kA, rfl⟩, la, dA, ma⟩ := needOrdAllocRegs_spec bNed _ _ _ ha
  simp only at la ma hp Rq
  have ofs : (ofSure (⟨sub, HoonSet.empty⟩ : Sure S)).sure = ⟨sub, HoonSet.empty⟩ := by simp [ofSure, sure_mk]
  have e3 : entries (ofSure ⟨sub, HoonSet.empty⟩ : Lazy S) = [] := entries_ofSure _
  have dT := Rq.ext.2.2.1.trans d0
  obtain ⟨⟨Qh, Rp⟩, hne, -, hfl, hec⟩ := Sp.run (sup := sup) (region := region)
    (L := ofSure ⟨sub, HoonSet.empty⟩) (th := jmp0 g0.bo) hcount (by have := Rq.ext.2.1; omega) dT (Rq.grow.up hu)
    (Clear.growU hcl Rq.grow) (Rq.cfr.below hcb) Rq.lo Rq.hi rfl (by rw [e3]; simp) (by rw [ofs]; exact dA)
    (fun x hx => by
      rw [ofs] at hx
      exact ⟨by have := (ma x hx).2; simp only [Gen.emitted]; omega, Rq.ncond _ (by rw [ofs]; exact hx)⟩)
    (fun e he => by rw [e3] at he; cases he) (by rw [e3]; simp) (fun e he => by rw [e3] at he; cases he)
    (flat_ofSure _) (by rw [ofs]; exact cl) (fun e he => by rw [e3] at he; cases he) hp
  have cS := Sp.clean (L := ofSure ⟨sub, HoonSet.empty⟩) (by rw [ofs]; exact cl) hp
  have d5 : g5.drop = false := Rp.drop.trans dT
  have Rp' := Rp.toRunOKLB.copyBunt (Rq.grow.up hu) d5 rfl (fun e he => by rw [e3] at he; cases he) hc
  have R := runOKGB_sevenL (minkC7_direct lib P fb fq b.fol hq1 hq2) Rq Rp' (fun r hr => hr.elim)
  have labS : ∀ e ∈ entries nexS.laz, e.1 < g5.bo := fun e he => by
    rcases (Rp.labs e he).1 with h | h
    · rw [e3] at h; cases h
    · exact h.2
  obtain ⟨rfl, -, -, -, -, -⟩ := copyL_bunt d5 hc
  rcases nexS with ⟨⟨s1, f1, b1⟩, th1⟩
  exact ⟨R, fun hm => by
    obtain ⟨e, he, ee⟩ := List.mem_map.mp hm
    have := labS e he; simp only [jmp0] at ee; omega, ⟨hfl.1, hfl.2⟩, cS, hec⟩

/-- **The n-ary contract of a direct call at the top**: the n-ary code
(`finishLFC`) of `[2 p q b]` with `p` in track C's class, on every subject of
`P` with the cape's axes, entered with its split. -/
theorem finishLFC_contractTailN (lib : Lib) {N : Needs} {env : CallEnv} {P : Noun → Prop} {p q : Nomm} {fb fq : Noun}
    {b : Bell} {bNed : NeedOrd} (hring : env.ring b = Option.none) (hned : env.need b = some bNed)
    (hsof : ∀ m, env.sof m p q b bNed = false) (hNf : N b false = some bNed) (hspl : SplitsLess b bNed)
    (Sp : LOKS (S := S) (Map := Map) false lib N env P fb p) (hcount : sixCount p ≤ 255)
    (hq : safeFolFol q = true)
    (hAp : ∀ x gul y, P x → Mink lib gul [] x fb (Tone.zero y) → SkaModel.Fits b.less y)
    (hq1 : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {rc : Tone}, P s → minkF lib gul n tm s fq = some rc →
      rc = Tone.zero b.fol)
    (hq2 : ∀ {s gul : Noun} {tm : Trace}, P s → Mink lib gul tm s fq (Tone.zero b.fol))
    {ord : NeedOrd} {less : Cape} {c : Straight Map}
    (h : finishLFC (S := S) env (Nomm.n2 p q (some (b, Option.none))) ord less (fun ned => (ned, [])) = some c) :
    ∀ s, P s → CapeAxes less s → ∀ args, SkaModel.split c.need s = some args →
      ContractFwd lib N s (n3 (A 2) fb fq) args c ∧ ContractBwd lib N s (n3 (A 2) fb fq) args c :=
  finishLFC_contractGB lib N (fun hr => tailN_done lib hring hned hsof hNf hspl Sp hcount hq hAp hq1 hq2
    (by simp [gen0]) rfl upBelow_gen0 clear_gen0 condBelow_gen0 hr) (fun _ => rfl) h

end

end Comp
end SkaModel
end Formalization
