import lemmas.Compiler.PokeLinkHot
import lemmas.Compiler.CompCopyLib

/-!
# The `%jets` branch of the pill's `+poke` on `[%jets ~]` (track P, README Gaps 23)

The branch (`bJets`, 298 cells) is `=/ hot (malt p.ovo)`, the test
`&(=(hot jets-hot.state) =(~ pend.jets.long-ska.state))`, `[[%drop ~] ..poke]`
when it holds, and the settling path (`jRest`: `+ska-cole-settle`,
`+hot-stale`, `+del-bells`, the edits) when it does not.  Here:

* `mold_jets_nil`: the mold `ovum` returns `[%jets ~]` on `[%jets ~]` (run
  by the kernel through `evalFuel`); `ipokeB_jets_nil`: so does the
  validation push of the inner `+poke`;
* `ipokeR_jets`: the dispatch sends a `%jets` to `bJets`; `bJets_eq`: the
  branch cut at its `malt` call, its test and its settling path;
* **`pokeN_jets_idle`**: on every encoded state with `jets-hot = ~` and
  `pend = ~`, the pill's poke of `[%jets ~]` returns `[%drop ~]` and the core
  unchanged;
* **`jetsIdle_keeps`**: so such a poke keeps `PGood7`, `long` and
  `jets-hot = ~` (the state itself), the `[%jets ~]`, `pend = ~` case of
  `OtherKeeps9`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.PokeM FinMap

/-! ## Validation of `[%jets ~]` -/

/-- **The mold `ovum` on `[%jets ~]`** returns it (the list mold on `~`). -/
theorem mold_jets_nil : slamAt vcore 685 (C (A Tag.jets) (A 0)) = some (C (A Tag.jets) (A 0)) := by
  rw [slamAt_mold]
  exact nock_of_evalFuel (fuel := 400) (by kernel_rfl)

/-- `+validate-ovum` on a `%jets` is the mold, on every context. -/
theorem vovum_jets (c tl : Noun) :
    nock (C vovumBat (C (C (A Tag.jets) tl) c)) vovumBat = slamAt c 685 (C (A Tag.jets) tl) := by
  nock_open vovumBat
  simp [nock_exec, Tag.jets, slamAt]

/-- The validation push of the inner `+poke` on `[%jets ~]` returns it. -/
theorem ipokeB_jets_nil {cr : Noun} (h15 : slot? 15 cr = some vcore) :
    nock (C ipokeBat (C (C (A Tag.jets) (A 0)) cr)) ipokeB = some (C (A Tag.jets) (A 0)) := by
  unfold ipokeB
  simp only [nock_exec, h15, vcore_ovum, gateArm_run, vovum_jets, mold_jets_nil]

/-- The dispatch sends a `%jets` to the `%jets` branch. -/
theorem ipokeR_jets (tl ib ovo cr : Noun) :
    nock (C (C (A Tag.jets) tl) (C ib (C ovo cr))) ipokeR = nock (C (C (A Tag.jets) tl) (C ib (C ovo cr))) bJets := by
  rw [ipokeR_eq]
  simp [nock_exec, pick_eqCode, Tag.jets]

/-! ## The branch, cut -/

/-- `=/ hot (malt p.ovo)`: `+malt` (arm `382` of layer 2) on `p` of the ovum. -/
def jMaltF : Noun :=
  C (A 8) (C (C (A 9) (C (A 382) (C (A 0) (A 16777215)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 13)))
    (C (A 0) (A 2)))))))

/-- `&(=(hot jets-hot.state) =(~ pend.jets.long-ska.state))`. -/
def jTestF : Noun :=
  C (A 6) (C (C (A 5) (C (C (A 0) (A 2)) (C (A 0) (A 2038)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0))
    (C (A 0) (A 65182)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))

/-- `[[%drop ~] ..poke]`. -/
def jThenF : Noun := C (C (A 1) (C (A Tag.drop) (A 0))) (C (A 0) (A 31))

/-- The settling path (`+ska-cole-settle`, `+hot-stale`, the edits), kept whole. -/
noncomputable def jRest : Noun := (slot? 63 bJets).getD (A 0)

theorem bJets_eq : bJets = C (A 8) (C jMaltF (C (A 6) (C jTestF (C jThenF jRest)))) := by
  kernel_rfl

/-- The battery of the gate `+malt` builds. -/
def maltBatH : Noun :=
  C (A 8) (C (C (A 9) (C (A 766) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14)))
    (C (A 0) (A 2)))))))

/-- `+malt` of `~` is `~`, as the branch calls it on a core with layer 2 at
its axis `2097151`. -/
theorem jMalt_nil {cr : Noun} (hl : slot? 2097151 cr = some layer2) (ib ovo : Noun) :
    nock (C (C (A Tag.jets) (A 0)) (C ib (C ovo cr))) jMaltF = some (A 0) := by
  have hg := malt_gate [] (A 0) rfl
  simp only [List.map_nil, listN, appendN] at hg
  have h16 : slot? 16777215 (C (C (A Tag.jets) (A 0)) (C ib (C ovo cr))) = some layer2 := by
    simpa only [nock_exec] using hl
  have hma : maltArm = gateArm maltBatH := rfl
  unfold jMaltF
  rw [nock_op8, nock_op9, nock_op0, h16]
  simp only [Option.bind_some, malt_at, hma, gateArm_run, nock_exec]
  unfold maltBatH
  exact hg

/-! ## On encoded states -/

/-- **The pill's `[%jets ~]` on a state with `jets-hot = ~` and `pend = ~`**:
`[%drop ~]`, and the core unchanged. -/
theorem pokeN_jets_idle (fl : Flags) (st : PSt) (hh : st.hot = A 0) {r1 r2 r3 r4 cole : Noun}
    (hj : st.jets = C r1 (C r2 (C r3 (C r4 (C (A 0) cole))))) :
    pokeN (enc fl st) (C (A Tag.jets) (A 0)) = some (C (C (A Tag.drop) (A 0)) (enc fl st)) := by
  rw [pokeN_eq (enc_slot2 fl st), nock_eight ipokeBat_eq, ipokeB_jets_nil (enc_slot15 fl st), Option.bind_some,
    ipokeR_jets, bJets_eq]
  have hm := jMalt_nil (enc_hoon fl st) ipokeBat (C (A Tag.jets) (A 0))
  have hs : ∀ x, slot? 2038 (C x (C (C (A Tag.jets) (A 0)) (C ipokeBat (C (C (A Tag.jets) (A 0)) (enc fl st))))) =
      some st.hot := fun x => by simp [enc, stNoun, nock_exec]
  simp only [nock_exec, hm, Option.bind_some, jTestF, jThenF, hs, hh, Nock.pick, eqCode]
  simp [Nock.pick, nock_exec, hj, eqCode_self]

variable {Cls : Straight (TreapMap mugF) → Prop}

/-- **The `[%jets ~]`, `pend = ~` case of `OtherKeeps9`**: the poke returns the
state itself. -/
theorem jetsIdle_keeps (fl : Flags) (st : PSt) (hg : PGood7 Cls st) (hh : st.hot = A 0)
    {r1 r2 r3 r4 cole : Noun} (hj : st.jets = C r1 (C r2 (C r3 (C r4 (C (A 0) cole))))) {p c' : Noun}
    (h : pokeN (enc fl st) (C (A Tag.jets) (A 0)) = some (C p c')) :
    ∃ st', PGood7 Cls st' ∧ st'.long = st.long ∧ st'.hot = A 0 ∧ enc fl st' = c' := by
  rw [pokeN_jets_idle fl st hh hj] at h
  simp only [Option.some.injEq, Noun.cell.injEq] at h
  exact ⟨st, hg, rfl, hh, h.2⟩

/-! ## `OtherKeeps9` from its open cases -/

/-- **Open (P)**: `[%jets ~]` with `pend` not empty keeps `PGood7`, `long`
and `jets-hot = ~` (`jRest`: `+ska-cole-settle` with the empty key set,
then `+hot-stale` of `(hot-diff ~ ~)`, which drops nothing (`hotempty.hoon`,
`%drop0`), and the edit of `jets-hot` to `(malt ~) = ~`). -/
def JetsSettle9 (fl : Flags) (Cls : Straight (TreapMap mugF) → Prop) : Prop :=
  ∀ (st : PSt) r1 r2 r3 r4 pd cole p c', PGood7 Cls st → st.hot = A 0 →
    st.jets = C r1 (C r2 (C r3 (C r4 (C pd cole)))) → pd ≠ A 0 →
    pokeN (enc fl st) (C (A Tag.jets) (A 0)) = some (C p c') →
    ∃ st', PGood7 Cls st' ∧ st'.long = st.long ∧ st'.hot = A 0 ∧ enc fl st' = c'

/-- **Open (P)**: the pill crashes on `[%jets a]` for an atom `a ≠ 0` (the
list mold of `+validate-ovum` on an atom other than `~`; checked on the real
compiler: `tools/hoon/hotatom.hoon` crashes on `[%jets 5]`). -/
def JetsAtom9 (fl : Flags) : Prop :=
  ∀ (st : PSt) (a : Nat), a ≠ 0 → pokeN (enc fl st) (C (A Tag.jets) (A a)) = none

/-- **Open (P)**: the pokes whose head is neither `%jets` nor a `%full`
(`%dire`, `%fast`, and the heads `+validate-ovum` crashes on) keep `PGood7`,
`long` and `jets-hot = ~`. -/
def NonJets9 (fl : Flags) (Cls : Straight (TreapMap mugF) → Prop) : Prop :=
  ∀ (st : PSt) ovo p c', PGood7 Cls st → st.hot = A 0 → pokeN (enc fl st) ovo = some (C p c') →
    (∀ tl, ovo ≠ C (A Tag.jets) tl) → (∀ s f, ovo ≠ (Ovum.full s f).toNoun) →
    ∃ st', PGood7 Cls st' ∧ st'.long = st.long ∧ st'.hot = A 0 ∧ enc fl st' = c'

/-- **`OtherKeeps9` from its three open cases**: the `[%jets ~]` case with
`pend` empty is `jetsIdle_keeps`, a `%jets` whose list is a cell is `Hot`. -/
theorem otherKeeps9_of {fl : Flags} (hS : JetsSettle9 fl Cls) (hA : JetsAtom9 fl) (hO : NonJets9 fl Cls) :
    OtherKeeps9 fl Cls := by
  intro st ovo p c' hg hh hp hH hf
  by_cases ej : ∃ tl, ovo = C (A Tag.jets) tl
  · obtain ⟨tl, rfl⟩ := ej
    rcases tl with a | ⟨x, y⟩
    · by_cases ha : a = 0
      · subst ha
        obtain ⟨r1, r2, r3, r4, pd, ca, bk, hj, -⟩ := hg.good6.good5.good4.good3.good2.good.maps
        by_cases hpd : pd = A 0
        · subst hpd
          exact jetsIdle_keeps fl st hg hh hj hp
        · exact hS st r1 r2 r3 r4 pd (C ca bk) p c' hg hh hj hpd hp
      · rw [hA st a ha] at hp; cases hp
    · exact absurd ⟨x, y, rfl⟩ hH
  · exact hO st ovo p c' hg hh hp (fun tl e => ej ⟨tl, e⟩) hf

end Compiler
end Formalization
