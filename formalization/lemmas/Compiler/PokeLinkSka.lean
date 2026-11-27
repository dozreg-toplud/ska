import lemmas.Compiler.PokeLinkReach
import lemmas.Compiler.RegisterFastShape

/-!
# The link of `+ska-poke` in the `%full` branch, up to its baking half `spRest`

`skaRaw` (`Compiler/PokeLinkFull.lean`) slams arm `20` of `ana` (axis `511`
of the core) on `[[& s] f]`, `long-ska` and `~(key by jets-hot)`.  Here:

* `skaRaw_eq`: on an encoded core it is the gate `+ska-poke` (`spBat`) on
  that sample, once `~(key by jets-hot)` (`keyRaw`) returns;
* `skaRaw_iff`: with `ska_poke_iff` and `ska_poke_ana_iff_pill` (the
  analysis half, linked): on a state whose jets noun has the shape
  `[r1 r2 r3 r4 jRest]`, the call returns `y` exactly when, at some fuel,
  `+ska-callgraph` returns `gr`, `Ana.skaPoke` returns `r` (on the
  registrations `[r1 r2 r3 r4 ~]`) and the baking half `spRest` returns `y`
  on `spAfter` of them;
* `SpRestAt fl Ar st s f key`: the link of `spRest` at a state (open, the
  baking half: `+bake-graph`, `new-code`, the SCC loop with
  `+eval-finalized`, the writes of `seek` and `calls`, `+ska-cole-update`),
  stated as what `SkaLink` needs at that state;
* `skaP_at`: `SkaLink`'s equation at a state from the shape, `keyRaw`, and
  `SpRestAt` (`enc_edit58`: writing `long-ska` into an encoded core);
* `pokeN_fullAt2`: `pokeN_fullAt` with the equation of `+ska-poke` at the
  state in place of `SkaLink`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeM

/-- `~(key by jets-hot)` of a core: arm `188` of the door `by` on axis `118`. -/
def keyRaw (cr : Noun) : Option Noun := (slot? 2097151 cr).bind fun hc => byArmO hc (slot? 118 cr) 188

theorem corLib_ana : slot? 63 corLib = some ana := by kernel_rfl

theorem enc_ana (fl : Flags) (st : PSt) : slot? 511 (enc fl st) = some ana := by
  have h : slot? 511 (enc fl st) = slot? 63 corLib := by simp [enc, nock_exec]
  rw [h, corLib_ana]

theorem enc_long (fl : Flags) (st : PSt) : slot? 58 (enc fl st) = some (longNoun fl st.jets st.long) := by
  simp [enc, stNoun, nock_exec]

/-- Writing `long-ska` into an encoded core. -/
theorem enc_edit58 (fl : Flags) (st : PSt) (j : Noun) (L : LongB FinMap) :
    edit? 58 (longNoun fl j L) (enc fl st) = some (enc fl { st with long := L, jets := j }) := by
  simp [enc, stNoun, nock_exec]

/-- **The call of `+ska-poke` on an encoded core** is the gate on its
sample, once `~(key by jets-hot)` returns. -/
theorem skaRaw_eq (fl : Flags) (st : PSt) (s f : Noun) :
    skaRaw (enc fl st) s f = (keyRaw (enc fl st)).bind fun key =>
      nock (C spBat (C (C (C (C (A 0) s) f) (C (longNoun fl st.jets st.long) key)) ana)) spBat := by
  unfold skaRaw keyRaw
  rw [enc_ana, enc_long, enc_hoon, enc_hot]
  simp only [Option.bind_some]
  generalize byArmO layer2 (some st.hot) 188 = K
  cases K <;> simp [gateAt, sp_at, slamG, nock_exec]

/-- The rest of `long-ska` after `memo`: `[code calls vars seek]`. -/
noncomputable def lonRestNoun (fl : Flags) (L : LongB FinMap) : Noun :=
  C (codeNoun fl L.code) (C (L.code.toNoun fun e => FinMap.setNoun e.calls)
    (C (L.vars.toNoun FinMap.setNoun) (L.code.toNoun fun e => e.seek.toNoun)))

theorem longNoun_split (fl : Flags) (j : Noun) (L : LongB FinMap) :
    longNoun fl j L = C j (C (memoNoun L.memo) (lonRestNoun fl L)) := rfl

/-- **The analysis half of `+ska-poke` on an encoded state** (linked:
`ska_poke_iff`, `ska_poke_ana_iff_pill`): on a state whose jets noun is
`[r1 r2 r3 r4 jRest]` and whose `~(key by jets-hot)` returns `key`, the call
returns `y` exactly when, at some fuel, `+ska-callgraph` and `Ana.skaPoke`
return `gr` and `r` on the registrations `[r1 r2 r3 r4 ~]`, and the baking
half `spRest` returns `y` on `spAfter` of them. -/
theorem skaRaw_iff (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP)
    (fl : Flags) (st : PSt) (s f : Noun) (r1 r2 r3 r4 jRest key : Noun)
    (hj : st.jets = C r1 (C r2 (C r3 (C r4 jRest)))) (hk : keyRaw (enc fl st) = some key) (y : Noun) :
    skaRaw (enc fl st) s f = some y ↔
      ∃ n gr r, Ana.skaCallgraph env n (Sock.mk Cape.yes s, f) st.long.memo (C r1 (C r2 (C r3 (C r4 (A 0))))) = some gr ∧
        Ana.skaPoke env n (Sock.mk Cape.yes s, f) st.long.memo (C r1 (C r2 (C r3 (C r4 (A 0))))) = some r ∧
        nock (spAfter (fun x : Noun => x) (Sock.mk Cape.yes s, f) r1 r2 r3 r4 jRest (lonRestNoun fl st.long) key gr r)
          spRest = some y := by
  rw [skaRaw_eq, hk, Option.bind_some, ska_poke_iff]
  have e : spTrap (C (C (C (A 0) s) f) (C (longNoun fl st.jets st.long) key)) =
      spT0 ana (Sock.mk Cape.yes s, f) r1 r2 r3 r4 jRest (memoNoun st.long.memo) (lonRestNoun fl st.long) key := by
    rw [longNoun_split, hj]; rfl
  rw [e]
  exact ska_poke_ana_iff_pill env hhe hth hsoft hrf (Sock.mk Cape.yes s, f) st.long.memo _ r1 r2 r3 r4 jRest
    (lonRestNoun fl st.long) key rfl y

section At

variable (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))

/-- **The link of the baking half `spRest` at a state** (open): what the
analysis half leaves (the graph `gr` and `r` of `Ana.skaPoke` at some fuel)
runs through `spRest` to `[[func new] long-ska']` exactly when the model's
`+ska-poke` returns, with `func` its root bell, `new` its registrations and
`long-ska'` the noun of its new jets and table (flags `fl`). -/
def SpRestAt (env : Env Noun) (st : PSt) (s f : Noun) (r1 r2 r3 r4 jRest key : Noun) : Prop :=
  ∀ y, (∃ n gr r, Ana.skaCallgraph env n (Sock.mk Cape.yes s, f) st.long.memo (C r1 (C r2 (C r3 (C r4 (A 0))))) = some gr ∧
        Ana.skaPoke env n (Sock.mk Cape.yes s, f) st.long.memo (C r1 (C r2 (C r3 (C r4 (A 0))))) = some r ∧
        nock (spAfter (fun x : Noun => x) (Sock.mk Cape.yes s, f) r1 r2 r3 r4 jRest (lonRestNoun fl st.long) key gr r)
          spRest = some y) ↔
      ∃ res, Ar.skaPoke s f st.long st.jets st.hot = some res ∧
        y = C (C res.1.toNoun res.2.2.2) (longNoun fl res.2.2.1 res.2.1)

/-- The equation of `SkaLink` at one state. -/
def SkaLinkAt (st : PSt) (s f : Noun) : Prop :=
  skaP (enc fl st) s f = (Ar.skaPoke s f st.long st.jets st.hot).map fun r =>
    (r.1.toNoun, r.2.2.2, enc fl { st with long := r.2.1, jets := r.2.2.1 })

/-- **`SkaLink`'s equation at a state** from the analysis half (proved) and
the link of the baking half there. -/
theorem skaLinkAt_of (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP)
    (st : PSt) (s f : Noun) (r1 r2 r3 r4 jRest key : Noun)
    (hj : st.jets = C r1 (C r2 (C r3 (C r4 jRest)))) (hk : keyRaw (enc fl st) = some key)
    (hR : SpRestAt fl Ar env st s f r1 r2 r3 r4 jRest key) : SkaLinkAt fl Ar st s f := by
  have hI := fun y => (skaRaw_iff env hhe hth hsoft hrf fl st s f r1 r2 r3 r4 jRest key hj hk y).trans (hR y)
  unfold SkaLinkAt skaP
  cases e : Ar.skaPoke s f st.long st.jets st.hot with
  | none =>
    cases e2 : skaRaw (enc fl st) s f with
    | none => rfl
    | some y =>
      obtain ⟨res, h1, -⟩ := (hI y).1 e2
      rw [e] at h1; cases h1
  | some res =>
    have h2 := (hI _).2 ⟨res, e, rfl⟩
    rw [h2]
    simp [enc_edit58]

/-- `SkaLink` gives the equation at every state. -/
theorem skaLinkAt_of_link (h : SkaLink fl Ar skaP) (st : PSt) (s f : Noun) : SkaLinkAt fl Ar st s f := h st s f

/-- **`pokeN_fullAt` with the equation of `+ska-poke` at the state only.** -/
theorem pokeN_fullAt2 {Cls : Straight (TreapMap mugF) → Prop}
    (hC : SccLink fl Ar sccP) (hM : MonoLink fl Ar monoP) (hO : OptLinkOn Cls Ar optP) (st : PSt) (s f₁ f₂ : Noun)
    (hS : SkaLinkAt fl Ar st s (C f₁ f₂))
    (hJ : ∀ r, Ar.skaPoke s (C f₁ f₂) st.long st.jets st.hot = some r →
      jrP (enc fl { st with long := r.2.1, jets := r.2.2.1 }) r.1.toNoun =
        some ((Ar.jetRoot r.2.2.1 st.hot r.1).map Straight.toNoun))
    (hIn : OptInAt Ar Cls st s (C f₁ f₂)) :
    pokeN (enc fl st) (Ovum.full s (C f₁ f₂)).toNoun =
      (liftPoke (enc fl) (pokeS Ar) (enc fl st) (Ovum.full s (C f₁ f₂))).map fun r => C r.1.toNoun r.2 := by
  rw [fullBranchIs fl st s f₁ f₂, liftPoke_enc_fl]
  unfold pillFull
  rw [hS]
  simp only [pokeS]
  cases e1 : Ar.skaPoke s (C f₁ f₂) st.long st.jets st.hot with
  | none => rfl
  | some r =>
    simp only [Option.map_some, Option.bind_some]
    rw [hJ r e1]
    simp only [Option.bind_some]
    cases e2 : Ar.jetRoot r.2.2.1 st.hot r.1 with
    | some out => simp [Prod.toNoun]
    | none =>
      simp only [Option.map_none]
      unfold compileStep
      rw [hC]
      cases e3 : Ar.sccOf r.1 r.2.1 st.cache.sccs with
      | none => rfl
      | some q =>
        simp only [Option.map_some, Option.bind_some, if_true]
        rw [hM]
        cases e4 : compiledMono Ar { st with long := r.2.1, jets := r.2.2.1, cache := { st.cache with sccs := q.2 } } r.1 q.1 with
        | none => rfl
        | some p =>
          simp only [Option.map_some, Option.bind_some]
          rw [hO p.1 (hIn r q p e1 e2 e3 e4)]
          simp [Prod.toNoun]

end At

end Compiler
end Formalization
