import lemmas.Compiler.PokeLinkJet

/-!
# The image of `enc` after a `%full` poke, and the flags (P1, option (b))

`SkaLink fl A ska` asks the core `+ska-poke` returns to be `enc fl` of the
model's new state, flags included: the flags `[pure total]` the SCC loop of
`+ska-poke` writes with `+eval-finalized` for each new bell must be
`fl newTable b`.  Here that part is split off as ONE named hypothesis on the
product of the pill's `+ska-poke`:

* `SkaLinkU fl A ska`: `SkaLink` up to the flags (the new core is `enc fl'`
  of the model's new state for SOME flags `fl'`);
* `SkaFlags fl A ska`: in that product the flags of every bell of the new
  table are `fl`'s (`fl' newTable b = fl newTable b` for each key `b`);
* `skaLink_of_flags`: `SkaLinkU` and `SkaFlags` give `SkaLink`
  (`enc_flags_congr`: `enc` reads the flags of the table's keys only);
* `full_step_enc`: the `poke` case of `PokeReachEnc` for a `%full` ovum: from
  an encoded state, with the links and the two facts of the model at the
  state that `pokeModel_fullG` takes, the core the pill returns is `enc fl`
  of the model's new state.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeM

/-- `codeNoun` reads the flags of the table's keys only. -/
theorem codeNoun_congr {fl fl' : Flags} {code : FinMap Bell (VarEntry FinMap)}
    (h : ∀ b, code.1 b ≠ none → fl code b = fl' code b) : codeNoun fl code = codeNoun fl' code := by
  unfold codeNoun
  congr 1
  apply Subtype.ext
  funext k
  simp only [FinMap.mapK]
  cases e : code.1 k with
  | none => rfl
  | some v => simp [h k (by simp [e])]

/-- `enc` reads the flags of the table's keys only. -/
theorem enc_flags_congr {fl fl' : Flags} (st : PSt)
    (h : ∀ b, st.long.code.1 b ≠ none → fl st.long.code b = fl' st.long.code b) : enc fl st = enc fl' st := by
  simp only [enc, stNoun, longNoun, codeNoun_congr h]

section Ska

variable (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))

/-- **`SkaLink` up to the flags**: the pill's `+ska-poke` returns exactly
when the model's does, with its root bell and `new`, and a core that is the
model's new state under SOME flags. -/
def SkaLinkU (ska : Noun → Noun → Noun → Option (Noun × Noun × Noun)) : Prop :=
  ∀ (st : PSt) s f, ∃ fl' : Flags, ska (enc fl st) s f = (Ar.skaPoke s f st.long st.jets st.hot).map fun r =>
    (r.1.toNoun, r.2.2.2, enc fl' { st with long := r.2.1, jets := r.2.2.1 })

/-- **P1, the flags (option (b))**: in the core the pill's `+ska-poke`
returns, the flags of every bell of the new table are `fl` of the new table.
What the SCC loop of `+ska-poke` with `+eval-finalized` must give for it:
the flags it writes for each new bell are `fl newTable b`, and `fl` does not
change on the old bells when the table grows (the loop writes new bells
only, so an old bell keeps the flags `fl oldTable b` of the state it came
from). -/
def SkaFlags (ska : Noun → Noun → Noun → Option (Noun × Noun × Noun)) : Prop :=
  ∀ (st : PSt) s f r (fl' : Flags), Ar.skaPoke s f st.long st.jets st.hot = some r →
    ska (enc fl st) s f = some (r.1.toNoun, r.2.2.2, enc fl' { st with long := r.2.1, jets := r.2.2.1 }) →
    ∀ b, r.2.1.code.1 b ≠ none → fl' r.2.1.code b = fl r.2.1.code b

/-- **`SkaLink` from the link up to the flags and the flags.** -/
theorem skaLink_of_flags {ska : Noun → Noun → Noun → Option (Noun × Noun × Noun)}
    (hU : SkaLinkU fl Ar ska) (hF : SkaFlags fl Ar ska) : SkaLink fl Ar ska := by
  intro st s f
  obtain ⟨fl', h⟩ := hU st s f
  rw [h]
  cases e : Ar.skaPoke s f st.long st.jets st.hot with
  | none => rfl
  | some r =>
    have hp : ska (enc fl st) s f = some (r.1.toNoun, r.2.2.2, enc fl' { st with long := r.2.1, jets := r.2.2.1 }) := by
      rw [h, e]; rfl
    have hc := hF st s f r fl' e hp
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and]
    exact enc_flags_congr { st with long := r.2.1, jets := r.2.2.1 } hc

/-! ## The `poke` case of `PokeReachEnc` for `%full` -/

/-- **A `%full` poke from an encoded state returns an encoded state**, the
model's: under the hypotheses of `pokeModel_fullG` at the state. -/
theorem full_step_enc {Cls : Straight (TreapMap mugF) → Prop} (hJA : Ar.jetRoot = jetRootP)
    (hS : SkaLink fl Ar skaP) (hC : SccLink fl Ar sccP)
    (hM : MonoLink fl Ar monoP) (hO : OptLinkOn Cls Ar optP)
    (hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none) (st : PSt) (s f : Noun)
    (hG : ∀ r, Ar.skaPoke s f st.long st.jets st.hot = some r → JetsGood r.2.2.1 st.hot)
    (hIn : OptInAt Ar Cls st s f) {p c' : Noun}
    (hp : pokeN (enc fl st) (Ovum.full s f).toNoun = some (C p c')) :
    ∃ st' pr, pokeS Ar st (Ovum.full s f) = some (pr, st') ∧ enc fl st' = c' ∧ pr.toNoun = p := by
  rw [pokeModel_fullG fl Ar hJA hS hC hM hO hAt st s f hG hIn, liftPoke_enc_fl] at hp
  cases e : pokeS Ar st (Ovum.full s f) with
  | none => rw [e] at hp; cases hp
  | some q =>
    rw [e] at hp
    simp only [Option.map_some, Option.some.injEq, Noun.cell.injEq] at hp
    exact ⟨q.2, q.1, rfl, hp.2, hp.1⟩

/-- **The same with `SkaLink` split** into the link up to the flags and the
flags (P1). -/
theorem full_step_enc_flags {Cls : Straight (TreapMap mugF) → Prop} (hJA : Ar.jetRoot = jetRootP)
    (hU : SkaLinkU fl Ar skaP) (hF : SkaFlags fl Ar skaP) (hC : SccLink fl Ar sccP)
    (hM : MonoLink fl Ar monoP) (hO : OptLinkOn Cls Ar optP)
    (hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none) (st : PSt) (s f : Noun)
    (hG : ∀ r, Ar.skaPoke s f st.long st.jets st.hot = some r → JetsGood r.2.2.1 st.hot)
    (hIn : OptInAt Ar Cls st s f) {p c' : Noun}
    (hp : pokeN (enc fl st) (Ovum.full s f).toNoun = some (C p c')) :
    ∃ st' pr, pokeS Ar st (Ovum.full s f) = some (pr, st') ∧ enc fl st' = c' ∧ pr.toNoun = p :=
  full_step_enc fl Ar hJA (skaLink_of_flags fl Ar hU hF) hC hM hO hAt st s f hG hIn hp

end Ska

end Compiler
end Formalization
