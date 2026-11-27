import lemmas.Compiler.CompSofArms
import lemmas.Compiler.CompSccSix
import lemmas.Ska.PokeEnc

/-!
# `SfTable` and `SofBell` from facts of the analysis (README Gaps 19, item (f))

`cu_gate_dir_code` takes two facts of the code table, `SfTable (nommOf CODE)`
and `SofBell CODE b` per callee.  Both follow from one fact per entry of
`code.long-ska`, `CodeAna CODE`, in the shape a link of `+ska-poke` (track P's
`SkaLink`) delivers about the state noun:

* the head of the entry is the noun of a nomm that `+fol-loop` returns
  (`FolMade`, so `Bake.NoAx0` by `folMade_noAx0`: the axis half of `SfTable`);
* every callee on the nomm's product path (`sfBells`) has an entry (the calls
  of the analysis are closed: `+ska-poke` puts an entry for every bell it
  calls);
* the bell's `less` is not `%void` (`member` asserts `?>  ?=(^ less.b)` on
  every bell it compiles).

`nommOf_eq` reads the nomm of an entry (by `nomm_toNoun_inj`), `sfTable_code`
and `sofBell_code` are the two reductions, and **`cu_gate_dir_ana`** is
`cu_gate_dir_code` with `CodeAna CODE` in place of both.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

/-- **The facts of the analysis on `code.long-ska`**, per entry. -/
def CodeAna (CODE : Noun) : Prop :=
  ∀ (b : Bell) (V : Noun), getF mugF b.toNoun CODE = some (C (A 0) V) →
    ∃ m : Nomm, slot? 2 V = some m.toNoun ∧ FolMade m ∧
      (∀ b' ∈ sfBells m, ∃ V', getF mugF b'.toNoun CODE = some (C (A 0) V')) ∧ b.less ≠ Sock.void

/-- The nomm of an entry is the one `nommOf` chooses. -/
theorem nommOf_eq {CODE : Noun} {b : Bell} {m : Nomm} {V : Noun}
    (hg : getF mugF b.toNoun CODE = some (C (A 0) V)) (hv : slot? 2 V = some m.toNoun) :
    nommOf CODE b = some m := by
  obtain ⟨m', hm'⟩ := nommOf_some hg hv
  obtain ⟨V', hg', hv'⟩ := codeNomms_nommOf CODE b m' hm'
  rw [hg] at hg'
  have eV : V = V' := by simpa using hg'
  subst eV
  rw [hv] at hv'
  have em : m.toNoun = m'.toNoun := by simpa using hv'
  rw [hm', nomm_toNoun_inj em]

/-- `nommOf` returns only on entries. -/
theorem nommOf_entry {CODE : Noun} {b : Bell} {m : Nomm} (h : nommOf CODE b = some m) :
    ∃ V, getF mugF b.toNoun CODE = some (C (A 0) V) ∧ slot? 2 V = some m.toNoun :=
  codeNomms_nommOf CODE b m h

/-- **`SfTable` of the code table from `CodeAna`**: the axis half by
`folMade_noAx0` and `sfTable_of`, the entries of the callees from the
closed calls. -/
theorem sfTable_code {CODE : Noun} (h : CodeAna CODE) : SfTable (nommOf CODE) := by
  apply sfTable_of
  intro b m hm
  obtain ⟨V, hg, hv⟩ := nommOf_entry hm
  obtain ⟨m', hv', hf, hc, -⟩ := h b V hg
  have e : m' = m := nomm_toNoun_inj (Option.some.inj (hv'.symm.trans hv))
  subst e
  refine ⟨folMade_noAx0 hf, fun b' mem => ?_⟩
  obtain ⟨V', hg'⟩ := hc b' mem
  obtain ⟨m'', hv''⟩ : ∃ m'' : Nomm, slot? 2 V' = some m''.toNoun := by
    obtain ⟨m'', h2, -⟩ := h b' V' hg'
    exact ⟨m'', h2⟩
  exact ⟨m'', nommOf_eq hg' hv''⟩

/-- **`SofBell` of a bell with an entry, from `CodeAna`.** -/
theorem sofBell_code {CODE : Noun} (h : CodeAna CODE) {b : Bell} {V : Noun}
    (hg : getF mugF b.toNoun CODE = some (C (A 0) V)) : SofBell CODE b := by
  obtain ⟨m, hv, -, -, hl⟩ := h b V hg
  exact ⟨⟨m, nommOf_eq hg hv⟩, hl⟩

/-- An entry from `codeOf`. -/
theorem entry_of_codeOf {CODE : Noun} {b : Bell} {c : Bool} (h : codeOf CODE b = some c) :
    ∃ V, getF mugF b.toNoun CODE = some (C (A 0) V) := by
  unfold codeOf at h
  split at h
  · rename_i V e
    exact ⟨V, e⟩
  · cases h

/-- **The gate of `+compile-unary` on `DirOk` with direct calls, from the
facts of the analysis** (README Gaps 19): `cu_gate_dir_code` with
`CodeAna CODE` for `SfTable (nommOf CODE)` and the `SofBell` of every callee
(each callee has an entry by `CodeNoRing`). -/
theorem cu_gate_dir_ana (FUNC SCC CODE LSR JH CACHE NM CA V COLE : Noun) (env : CallEnv) (n : Nomm)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun)
    (hcl : slot? 190 LSR = some COLE) (hcr : CodeNoRing CODE COLE n)
    (hn : DirOk n = true) (he : EnvFrom env CODE COLE)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuCsi = some (C NM CA))
    (hneed : CsiNeeds env SCC NM CA n) (hsure : CsiSures env CA n) (hana : CodeAna CODE) :
    nock (C cuGB (C (cuSam FUNC SCC CODE LSR JH CACHE) compK)) cuGB
      = (finishLUCM (S := CSet) (Map := TreapMap mugF) env n).map fun st => C (C st.toNoun NM) CA :=
  cu_gate_dir_code FUNC SCC CODE LSR JH CACHE NM CA V COLE env n hgot hv hcl hcr hn he hcsi hneed hsure
    (sfTable_code hana) (fun b mem => by
      obtain ⟨c, hc⟩ := (hcr b mem).1
      obtain ⟨V', hg⟩ := entry_of_codeOf hc
      exact sofBell_code hana hg)

end Compiler
end Formalization
