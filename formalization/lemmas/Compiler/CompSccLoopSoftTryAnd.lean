import lemmas.Compiler.CompSccLoopSoftTryLat
import lemmas.Compiler.CompSccLoopSoftTryCons
import lemmas.Compiler.CompSccLoopSoftTryFree
import lemmas.Compiler.CompSccLoopSoftTryLast

/-! # The try path of `+soft-emit`, composed (README Gaps 21.22)

The pushes of `seTryPath` (`tp0`, `CompSccLoopSoftTryCut.lean`) composed: `tl_lat`, `tl_flag`,
`tl_tom` (`CompSccLoopSoftTryLat.lean`), `tc_push` (`+soft-cons`), `tz_mean`, `tz_pes`, `tz_fail`
(`CompSccLoopSoftTryPes.lean`), `tf_def`, `tf_test` (`+soft-free`), `tw_last` (the tries last).

* `taTail fuel`: the tail of `softEmit` after `?~ tries` (`softEmit` has `fuel = fun _ => 100000`,
  `ta_tail_eq`), the fuel of `+soft-free` a function of the state;
* `TaFlag`: the `|` side of `+soft-free` (`tpYNN0`, `+:(flag(gen gen) fail)`) is `softFlag`, a named
  hypothesis (not linked here);
* `TaNone fuel`: where the model's `+soft-free` is `none`, the pill's test crashes too (true where
  the `none` is a missing block, `+got:by`; false where the fuel runs out first, see `tf_trap`);
* **`ta_and`**: the pill on `tp0` is `taTail fuel` under `TaFlag` and `TaNone fuel`. -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- **The tail of `softEmit`** after `?~ tries` (line 5363), the fuel of `+soft-free` given by
`fuel` at the state where it runs. -/
def taTail (fuel : Gen (TreapMap mugF) → Nat) (o : Nat) (s : SoftCall) (ops : List Pole)
    (tops : List (Nat × Nat × Need)) (hed : Blob) (ht : Jmp) : CM (TreapMap mugF) Unit := do
  let tries := softTriesP tops
  let (_, lt) ← hopOf s.last
  let tom := (tops.map fun t => (t.1, t.2.1)).reverse
  let (kon, rub) ← softConsM tom s.ned 1 s.b.less
  if s.rin.isSome then crashM else
  let pes ← softPesM s rub
  let fail ← emitCold ⟨[], kon, Termin.hop (jmp0 pes)⟩
  let dfn := softDefs tries
  let g ← get
  match softFreeF g.blocks s.last dfn (fuel g) [o] [] with
  | none => crashM
  | some false => do
    let _ ← softFlag s ops tries ht lt fail
    pure ()
  | some true => do
    let first ← tries.foldlM (fun nxt (_, r, n) => monoTryCall n nxt r fail) lt.there
    emir s.head ⟨[], ops, hed.fin⟩
    emir s.last ⟨[], [], Termin.hop (jmp0 first)⟩

/-- **`softEmit` through `taTail`** with the fuel `100000`. -/
theorem ta_tail_eq (o : Nat) (s : SoftCall) :
    (softEmit o s : CM (TreapMap mugF) Unit) =
      (if s.req = [] then pure () else do
      let (opsC, topsC) ← softCutsM (softAxes s.ned 1 []) s.sur s.b.less s.req ([], [])
      let ops := opsC ++ softMoves topsC
      let tries := softTriesP topsC
      let (hed, ht) ← hopOf s.head
      if tries = [] then emir s.head ⟨[], ops, hed.fin⟩ else
      taTail (fun _ => 100000) o s ops topsC hed ht) := by
  rfl

/-- `hopOf` keeps the state, and its block ends in the jump. -/
theorem ta_hopOf {o : Nat} {g g' : Gen (TreapMap mugF)} {b : Blob} {t : Jmp}
    (h : hopOf o g = some ((b, t), g')) : g = g' ∧ b.fin = Termin.hop t := by
  unfold hopOf at h
  cases e : HoonMap.get g.blocks o with
  | none => simp [e] at h
  | some b0 =>
    simp only [e, Option.bind_some] at h
    by_cases h1 : b0.par = [] ∧ b0.body = []
    · simp only [h1, and_self, if_true] at h
      cases hf : b0.fin with
      | hop t0 =>
        rw [hf] at h
        by_cases h2 : t0.args = []
        · simp only [h2, if_true, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
          exact ⟨rfl, hf⟩
        · simp [h2] at h
      | _ => rw [hf] at h; simp at h
    · simp [h1] at h

/-- **The `|` side of `+soft-free`** (the named hypothesis): `+:(flag(gen gen) fail)` (`tpYNN0`) on
the subject after `def`, with the gate `flag` pushed on `[lat tpS0]` at any earlier `gen`, is
`softFlag`. -/
def TaFlag (ctx : Noun) (x : GenRest) (o : Nat) (s : SoftCall) (hed lat : Blob) (ht lt : Jmp)
    (ops : List Pole) (tries : List (Nat × Nat × Need)) (CUT AXS : Noun) : Prop :=
  hed.fin = Termin.hop ht → lat.fin = Termin.hop lt →
  ∀ (DEF : Noun) (FAIL PES : Nat) (kon : List Pole) (rub : Nat) (TOM : Noun) (g0 g : Gen (TreapMap mugF)),
    SawRel DEF (softDefs tries) →
    nock (twSub DEF FAIL PES kon rub TOM
        (tpFlagN (C lat.toNoun (tpS0 hed.toNoun (listNoun seTopN tries) (listNoun Pole.toNoun ops) CUT AXS
          o s g0 x ctx)))
        lat.toNoun hed.toNoun (listNoun seTopN tries) (listNoun Pole.toNoun ops) CUT AXS o s g x ctx) tpYNN0
      = (softFlag s ops tries ht lt FAIL g).map fun q => genNoun q.2 x

/-- **The model's `+soft-free` is `none` only where the pill's test crashes** (the named
hypothesis): true for a fuel the walk does not run out of. -/
def TaNone (fuel : Gen (TreapMap mugF) → Nat) (ctx : Noun) (x : GenRest) (o : Nat) (s : SoftCall)
    (hed lat : Blob) (ops : List Pole) (tries : List (Nat × Nat × Need)) (CUT AXS : Noun) : Prop :=
  ∀ (DEF : Noun) (FAIL PES : Nat) (kon : List Pole) (rub : Nat) (TOM FLAG : Noun) (g : Gen (TreapMap mugF)),
    SawRel DEF (softDefs tries) →
    softFreeF g.blocks s.last (softDefs tries) (fuel g) [o] [] = none →
    nock (C DEF (tfS FAIL PES kon rub TOM FLAG lat.toNoun hed.toNoun (listNoun seTopN tries)
        (listNoun Pole.toNoun ops) CUT AXS o s g x ctx)) tpYN9 = none

/-- **The try path of `+soft-emit`** (`seTryPath`, `tp0`): on the subject `tpS0` with `hed` the head
block of the bond, `tries` the `softTriesP` of `tops`, `ops` and `cut`, the pill gives the `gen` of
`taTail fuel`, under the `|` side `TaFlag` and `TaNone fuel`. -/
theorem ta_and {ctx : Noun} (hc : CompIn ctx) (hl : slot? 255 ctx = some lib)
    (h15 : slot? 15 ctx = some compTypes) (x : GenRest) (fuel : Gen (TreapMap mugF) → Nat) (o : Nat)
    (s : SoftCall) (hk : s.kin = 0 ∨ s.kin = 1) (hr : s.rin = none) (hed : Blob) (ht : Jmp)
    (ops cops : List Pole) (tops : List (Nat × Nat × Need)) (AXS : Noun) (g : Gen (TreapMap mugF))
    (hflag : ∀ lat lt, TaFlag ctx x o s hed lat ht lt ops (softTriesP tops) (seCutN (cops, tops)) AXS)
    (hnone : ∀ lat, TaNone fuel ctx x o s hed lat ops (softTriesP tops) (seCutN (cops, tops)) AXS)
    (hhf : hed.fin = Termin.hop ht) :
    nock (tpS0 hed.toNoun (listNoun seTopN (softTriesP tops)) (listNoun Pole.toNoun ops) (seCutN (cops, tops))
        AXS o s g x ctx) tp0
      = (taTail fuel o s ops tops hed ht g).map fun p => genNoun p.2 x := by
  obtain ⟨TOM, hT, htom⟩ := tl_tom ctx hc g x o s hed.toNoun (listNoun seTopN (softTriesP tops))
    (listNoun Pole.toNoun ops) AXS cops tops
  rw [tl_lat ctx hc g x o s]
  cases hL : hopOf s.last g with
  | none => simp [taTail, hL, bind, StateT.bind]
  | some p =>
    obtain ⟨⟨lat, lt⟩, g0⟩ := p
    obtain ⟨rfl, hlf⟩ := ta_hopOf hL
    simp only [Option.bind_some]
    rw [tl_flag, htom, tc_push x hc hl hT]
    cases hS : softConsM ((tops.map fun t => (t.1, t.2.1)).reverse) s.ned 1 s.b.less g with
    | none => simp [taTail, hL, hS, bind, StateT.bind]
    | some q =>
      obtain ⟨⟨kon, rub⟩, g1⟩ := q
      simp only [Option.bind_some]
      have hm := tz_mean kon rub TOM (tpFlagN (C lat.toNoun (tpS0 hed.toNoun (listNoun seTopN (softTriesP tops))
        (listNoun Pole.toNoun ops) (seCutN (cops, tops)) AXS o s g x ctx))) lat.toNoun hed.toNoun
        (listNoun seTopN (softTriesP tops)) (listNoun Pole.toNoun ops) (seCutN (cops, tops)) AXS o s g1 x ctx hk
      simp only [tzS] at hm
      rw [hm]
      have hp := tz_pes hc kon rub TOM (tpFlagN (C lat.toNoun (tpS0 hed.toNoun (listNoun seTopN (softTriesP tops))
        (listNoun Pole.toNoun ops) (seCutN (cops, tops)) AXS o s g x ctx))) lat.toNoun hed.toNoun
        (listNoun seTopN (softTriesP tops)) (listNoun Pole.toNoun ops) (seCutN (cops, tops)) AXS o s x hr hk g1
      simp only [tzS] at hp
      rw [hp]
      cases hP : (softPesM s rub g1 : Option (Nat × Gen (TreapMap mugF))) with
      | none => simp [taTail, hL, hS, hP, hr, bind, StateT.bind]
      | some q2 =>
        obtain ⟨pes, g2⟩ := q2
        simp only [Option.bind_some]
        have hf := tz_fail hc kon rub pes TOM (tpFlagN (C lat.toNoun (tpS0 hed.toNoun
          (listNoun seTopN (softTriesP tops)) (listNoun Pole.toNoun ops) (seCutN (cops, tops)) AXS o s g x ctx)))
          lat.toNoun hed.toNoun (listNoun seTopN (softTriesP tops)) (listNoun Pole.toNoun ops) (seCutN (cops, tops))
          AXS o s g2 x
        simp only [tzS] at hf
        rw [hf]
        cases hE : (emitCold ⟨[], kon, Termin.hop (jmp0 pes)⟩ g2 : Option (Nat × Gen (TreapMap mugF))) with
        | none => simp [taTail, hL, hS, hP, hE, hr, bind, StateT.bind]
        | some q3 =>
          obtain ⟨fail, g3⟩ := q3
          simp only [Option.bind_some]
          obtain ⟨DEF, hD, hdef⟩ := tf_def hc fail pes kon rub TOM (tpFlagN (C lat.toNoun (tpS0 hed.toNoun
            (listNoun seTopN (softTriesP tops)) (listNoun Pole.toNoun ops) (seCutN (cops, tops)) AXS o s g x ctx)))
            lat.toNoun hed.toNoun (listNoun Pole.toNoun ops) (seCutN (cops, tops)) AXS o s g3 x (softTriesP tops)
          simp only [tfS, tzS] at hdef
          rw [hdef]
          cases hF : softFreeF g3.blocks s.last (softDefs (softTriesP tops)) (fuel g3) [o] [] with
          | none =>
            have hn := hnone lat DEF fail pes kon rub TOM (tpFlagN (C lat.toNoun (tpS0 hed.toNoun
              (listNoun seTopN (softTriesP tops)) (listNoun Pole.toNoun ops) (seCutN (cops, tops)) AXS o s g x ctx)))
              g3 hD hF
            simp only [tfS, tzS] at hn
            rw [hn]
            simp [taTail, hL, hS, hP, hE, hF, hr, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
              crashM]
          | some b =>
            have ht' := tf_test hc h15 fail pes kon rub TOM (tpFlagN (C lat.toNoun (tpS0 hed.toNoun
              (listNoun seTopN (softTriesP tops)) (listNoun Pole.toNoun ops) (seCutN (cops, tops)) AXS o s g x ctx)))
              lat.toNoun hed.toNoun (listNoun seTopN (softTriesP tops)) (listNoun Pole.toNoun ops) (seCutN (cops, tops))
              AXS o s g3 x hD (fuel g3) b hF
            simp only [tfS, tzS] at ht'
            rw [ht']
            cases b with
            | true =>
              have hw := tw_last hc x DEF fail pes kon rub TOM (tpFlagN (C lat.toNoun (tpS0 hed.toNoun
                (listNoun seTopN (softTriesP tops)) (listNoun Pole.toNoun ops) (seCutN (cops, tops)) AXS o s g x ctx)))
                (seCutN (cops, tops)) AXS o s hed lat lt hlf ops (softTriesP tops) g3
              simp only [twSub, tzS] at hw
              simp only [if_true]
              rw [hw]
              simp [taTail, hL, hS, hP, hE, hF, hr, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get]
            | false =>
              have hw := hflag lat lt hhf hlf DEF fail pes kon rub TOM g g3 hD
              simp only [twSub, tzS] at hw
              simp only [Bool.false_eq_true, if_false]
              rw [hw]
              simp [taTail, hL, hS, hP, hE, hF, hr, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
                pure, StateT.pure]
              cases (softFlag s ops (softTriesP tops) ht lt fail g3 : Option (Nat × Gen (TreapMap mugF))) <;> rfl

end Compiler
end Formalization
